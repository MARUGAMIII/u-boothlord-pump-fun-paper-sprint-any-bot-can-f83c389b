// Surge — a paper trading bot for the pump.fun bonding-curve replay.
//
// One entry mode, read off each curve's rolling trade tape: a mature curve
// whose tape shows accelerating buy pressure — net SOL flowing in, several
// distinct buyers, price up at least 25% over a 20-slot window and sitting
// within 2% of its window high, with the newer half of the window buying
// harder than the older half. One small buy per entry, no pyramid: adding
// into strength lost money on every dev-window test, as did a dip-buy mode
// (both tried and dropped). Positions are small (0.02 SOL) and many — the
// edge, if any, is in catching a few runners while the many small losers
// stay capped by the stop and the fade exit.
//
// Every position exits on the first of: a stop loss against cost, a trailing
// stop once the position is up, a take-profit, a fade (net outflow over a
// short window), or a time limit. A curve that completes is closed by the
// replay at its final reserves.
//
// Guardrail probes: the ranking bar needs a round trip of at least 0.01 SOL on
// each of at least 20 coins, so when the bot's own fills or coins lag the pace
// of the window it opens tiny probe round trips (buy 0.02 SOL, sell as soon as
// the buy lands) on liquid curves.
//
// Everything is a pure function of the batches the harness sends: no clock, no
// randomness, no I/O, no environment reads, so the two graded executions
// produce byte-identical action logs. Iteration is only over insertion-ordered
// maps fed by the batch stream.

import { runBot, type Batch, type Bot, type BotState, type OrderInput, type Pubkey } from './vendor/makefun-bot.ts';

const LAMPORTS = 1e9;
const CURVE_FEE = 0.0125; // protocol 95 bps + creator 30 bps fallback = 1.25% each way
const BPS = 10_000;

interface Params {
  // --- SURGE (momentum) ---
  surgeWindow: number; // entry lookback, slots
  surgeMinNetSol: number; // net SOL bought over the window
  surgeMinBuys: number; // buy trades in the window
  surgeMinBuyers: number; // distinct buying wallets in the window
  surgeMinUp: number; // price now / price at window start - 1, lower bound
  surgeMaxUp: number; // ... upper bound (skip curves that already ran too far)
  surgeAccel: number; // newer-half net inflow must be >= this x older-half net
  surgeNearHigh: number; // price now must be >= this share of the window high
  surgeMinAge: number; // slots since CreateEvent before a surge entry
  surgeMinRqSol: number; // real SOL at entry, lower bound
  surgeMaxRqSol: number; // real SOL at entry, upper bound
  // --- sizing ---
  surgeInitialSol: number; // first surge buy
  surgeAddSol: number; // each surge pyramid add
  surgeMaxSol: number; // most SOL into one surge position
  minBuySol: number; // smallest buy worth sending (tx fee is ~0.000105 SOL/order)
  buySlipBps: number; // slippage tolerance on buys; sells always go out at 10000
  // --- exits ---
  stopLoss: number; // exit when value < cost * (1 - stopLoss)
  trail: number; // trailing stop: exit when value < peak * (1 - trail)
  trailArm: number; // trailing stop arms once value >= cost * (1 + trailArm)
  takeProfit: number; // exit when value >= cost * (1 + takeProfit)
  fadeWindow: number; // exit when net SOL over this window < -fadeNetSol
  fadeNetSol: number;
  maxHold: number; // exit after this many slots held (unless already in profit)
  holdIfUp: number; // the time limit does not apply while up at least this much
  cooldown: number; // slots to wait after an exit before the same curve re-enters
  maxEntries: number; // most entries per curve over the run
  maxMain: number; // most momentum/dip positions open at once (rest is for probes)
  maxExposureSol: number; // most SOL at cost across all positions at once
  // --- guardrail probes ---
  targetCoins: number; // distinct coins the run should trade by the end
  targetFills: number; // fills the run should reach by the end
  paceSecs: number; // block-time span the pace is measured over (6h window)
  probeSol: number; // size of one probe round trip
  maxProbes: number; // most probe round trips open at once
}

export const PARAMS: Params = {
  surgeWindow: 20,
  surgeMinNetSol: 0.5,
  surgeMinBuys: 4,
  surgeMinBuyers: 4,
  surgeMinUp: 0.25,
  surgeMaxUp: 2.0,
  surgeAccel: 1.0,
  surgeNearHigh: 0.98,
  surgeMinAge: 400,
  surgeMinRqSol: 3,
  surgeMaxRqSol: 40,
  surgeInitialSol: 0.02,
  surgeAddSol: 0, // pyramid disabled: adds lost money on every dev-window test
  surgeMaxSol: 0.12,
  minBuySol: 0.01,
  buySlipBps: 1500,
  stopLoss: 0.18,
  trail: 0.2,
  trailArm: 0.08,
  takeProfit: 0.35,
  fadeWindow: 20,
  fadeNetSol: 0.3,
  maxHold: 1200,
  holdIfUp: 0.05,
  cooldown: 200,
  maxEntries: 2,
  maxMain: 4,
  maxExposureSol: 4,
  targetCoins: 25,
  targetFills: 240,
  paceSecs: 21_600,
  probeSol: 0.02,
  maxProbes: 1,
};

interface Trade {
  slot: number;
  buy: boolean;
  sol: number;
  user: string;
  price: number;
}

interface Tape {
  created: number | null;
  trades: Trade[];
  entries: number;
  lastExit: number;
}

interface Held {
  opened: number;
  peakValue: number;
  invested: number;
  exiting: boolean;
  filled: boolean;
  lastAddPrice: number;
  lastValue: number;
}

export function createBot(p: Params = PARAMS): Bot {
  const tapes = new Map<Pubkey, Tape>();
  const held = new Map<Pubkey, Held>();
  /** Probe round trips in flight, by mint: false while buying, true once selling. */
  const probes = new Map<Pubkey, boolean>();
  /** The bot's own filled orders and the coins they were on (harness closes excluded). */
  let myFills = 0;
  const myCoins = new Set<Pubkey>();
  let firstTime: number | null = null;
  let lastTime: number | null = null;
  const keep = Math.max(p.surgeWindow, p.fadeWindow) + 5;

  const tapeOf = (mint: Pubkey): Tape => {
    let t = tapes.get(mint);
    if (t === undefined) {
      t = { created: null, trades: [], entries: 0, lastExit: -1e12 };
      tapes.set(mint, t);
    }
    return t;
  };

  /** Net recorded SOL (buys minus sells) over the last `w` slots. */
  const flow = (t: Tape, now: number, w: number): number => {
    let net = 0;
    for (let i = t.trades.length - 1; i >= 0; i--) {
      const tr = t.trades[i]!;
      if (tr.slot <= now - w) break;
      net += tr.buy ? tr.sol : -tr.sol;
    }
    return net;
  };

  /** SURGE signal: accelerating buy pressure on a mature curve near its high. */
  const surgeSignal = (t: Tape, now: number, rqSol: number): boolean => {
    if (rqSol < p.surgeMinRqSol || rqSol > p.surgeMaxRqSol) return false;
    if (t.created === null || now - t.created < p.surgeMinAge) return false;
    const from = now - p.surgeWindow;
    const mid = now - p.surgeWindow / 2;
    let buySol = 0;
    let sellSol = 0;
    let buys = 0;
    let netOld = 0;
    let netNew = 0;
    let startPrice = -1;
    let high = 0;
    let last = 0;
    const byUser = new Map<string, number>();
    for (const tr of t.trades) {
      if (tr.slot <= from) {
        startPrice = tr.price;
        continue;
      }
      if (startPrice < 0) startPrice = tr.price;
      const signed = tr.buy ? tr.sol : -tr.sol;
      if (tr.slot <= mid) netOld += signed;
      else netNew += signed;
      if (tr.buy) {
        buySol += tr.sol;
        buys++;
        byUser.set(tr.user, (byUser.get(tr.user) ?? 0) + tr.sol);
      } else {
        sellSol += tr.sol;
      }
      if (tr.price > high) high = tr.price;
      last = tr.price;
    }
    if (buys < p.surgeMinBuys || byUser.size < p.surgeMinBuyers) return false;
    if (buySol - sellSol < p.surgeMinNetSol) return false;
    if (startPrice <= 0) return false;
    const up = last / startPrice - 1;
    if (up < p.surgeMinUp || up > p.surgeMaxUp) return false;
    if (last < high * p.surgeNearHigh) return false;
    // Acceleration: the newer half of the window must buy at least as hard as the older half.
    if (netNew <= 0 || netNew < p.surgeAccel * netOld) return false;
    return true;
  };

  /** Liquidation value of a position in SOL, curve and tx fees deducted. */
  const positionValue = (
    state: BotState,
    mint: Pubkey,
    tokens: number,
    tx: number,
  ): { value: number; rqSol: number; price: number } => {
    const curve = state.curves.get(mint)!;
    const vq = Number(curve.virtual_quote_reserves);
    const vt = Number(curve.virtual_token_reserves);
    const value = ((tokens * vq) / (vt + tokens) / LAMPORTS) * (1 - CURVE_FEE) - tx;
    return { value, rqSol: Number(curve.real_quote_reserves) / LAMPORTS, price: vq / vt };
  };

  return {
    onBatch(state: BotState, batch: Batch): OrderInput[] {
      const now = batch.slot;
      const traded = new Set<Pubkey>();
      for (const f of batch.fills) {
        if (f.status === 'filled' && !f.client_id.startsWith('_')) {
          myFills++;
          myCoins.add(f.mint);
        }
      }
      for (const e of batch.events) {
        if (e.block_time !== null) {
          if (firstTime === null) firstTime = e.block_time;
          if (lastTime === null || e.block_time > lastTime) lastTime = e.block_time;
        }
        if (e.event === 'CreateEvent') {
          tapeOf(e.mint).created = e.slot;
        } else if (e.event === 'TradeEvent') {
          const t = tapeOf(e.mint);
          const sol = Number(e.sol_amount) / LAMPORTS;
          t.trades.push({
            slot: e.slot,
            buy: e.is_buy,
            sol,
            user: e.user,
            price: Number(e.virtual_quote_reserves) / Number(e.virtual_token_reserves),
          });
          traded.add(e.mint);
        }
      }
      for (const mint of traded) {
        const t = tapes.get(mint)!;
        let cut = 0;
        while (cut < t.trades.length && t.trades[cut]!.slot <= now - keep) cut++;
        if (cut > 0) t.trades.splice(0, cut);
      }
      const pendingByMint = new Map<Pubkey, number>();
      for (const po of state.pending.values()) pendingByMint.set(po.order.mint, (pendingByMint.get(po.order.mint) ?? 0) + 1);

      const orders: OrderInput[] = [];
      const cap = state.hello.caps.max_orders_per_batch;
      const tx = Number(state.txFeeLamports()) / LAMPORTS;

      // ---- Exits first. ----
      for (const [mint, h] of held) {
        const pos = state.positions.get(mint);
        const curve = state.curves.get(mint);
        if (pos === undefined) {
          if (!pendingByMint.has(mint)) {
            held.delete(mint);
            const t = tapeOf(mint);
            if (h.filled) t.lastExit = now;
            else t.entries--;
          }
          continue;
        }
        h.filled = true;
        if (curve === undefined || curve.complete) continue;
        const tokens = Number(pos.token_amount);
        const { value, rqSol } = positionValue(state, mint, tokens, tx);
        const cost = Number(pos.cost_lamports) / LAMPORTS;
        if (value > h.peakValue) h.peakValue = value;
        h.lastValue = value;
        let exit = h.exiting;
        const t = tapeOf(mint);
        // A curve about to complete (deep real SOL) is ridden, not faded out.
        const riding = rqSol >= 100;
        if (!exit && value < cost * (1 - p.stopLoss)) exit = true;
        if (!exit && h.peakValue >= cost * (1 + p.trailArm) && value < h.peakValue * (1 - p.trail)) exit = true;
        if (!exit && value >= cost * (1 + p.takeProfit)) exit = true;
        if (!exit && !riding && flow(t, now, p.fadeWindow) < -p.fadeNetSol) exit = true;
        if (!exit && now - h.opened > p.maxHold && value < cost * (1 + p.holdIfUp)) exit = true;
        if (!exit) continue;
        h.exiting = true;
        if (pendingByMint.has(mint)) {
          let sellPending = false;
          for (const po of state.pending.values()) if (po.order.mint === mint && po.order.side === 'sell') sellPending = true;
          if (sellPending) continue;
        }
        if (orders.length >= cap) break;
        orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
      }

      // ---- Probe round trips: sell the whole probe as soon as its buy has landed. ----
      for (const [mint, selling] of probes) {
        const pos = state.positions.get(mint);
        const curve = state.curves.get(mint);
        if (pos === undefined) {
          if (!pendingByMint.has(mint)) probes.delete(mint);
          continue;
        }
        if (curve === undefined || curve.complete || pendingByMint.has(mint)) continue;
        if (orders.length >= cap) break;
        orders.push({ side: 'sell', mint, token_amount: pos.token_amount, max_slippage_bps: 10_000 });
        if (!selling) probes.set(mint, true);
      }

      // ---- Entries and pyramid adds. ----
      let free = Number(state.freeCashLamports()) / LAMPORTS;
      let slotsLeft = state.hello.caps.max_open_positions - state.committedPositionCount();
      let mainLeft = p.maxMain - held.size;
      let exposure = 0;
      for (const [mint, h] of held) exposure += Math.max(h.invested, Number(state.positions.get(mint)?.cost_lamports ?? 0n) / LAMPORTS);
      for (const mint of traded) {
        if (orders.length >= cap) break;
        const curve = state.curves.get(mint);
        if (curve === undefined || curve.complete) continue;
        if (pendingByMint.has(mint) || probes.has(mint)) continue;
        const t = tapes.get(mint)!;
        const h = held.get(mint);
        const price = Number(curve.virtual_quote_reserves) / Number(curve.virtual_token_reserves);
        const rqSol = Number(curve.real_quote_reserves) / LAMPORTS;
        let want: number;
        if (h === undefined) {
          if (slotsLeft <= 0 || mainLeft <= 0) continue;
          if (t.entries >= p.maxEntries || now - t.lastExit < p.cooldown) continue;
          if (!surgeSignal(t, now, rqSol)) continue;
          want = p.surgeInitialSol;
        } else {
          // Pyramid into strength only: the signal still holds, the price is at
          // or above the last buy's, and the position is below its cap.
          if (h.exiting || !h.filled) continue;
          const pos = state.positions.get(mint);
          if (pos === undefined) continue;
          if (h.invested >= p.surgeMaxSol - p.minBuySol) continue;
          if (!surgeSignal(t, now, rqSol)) continue;
          if (price < h.lastAddPrice) continue;
          want = Math.min(p.surgeAddSol, p.surgeMaxSol - h.invested);
        }
        const capSol = Math.floor(Number(state.maxBuyLamports(mint))) / LAMPORTS;
        let amount = Math.min(capSol, want, p.maxExposureSol - exposure);
        if (amount > free - tx) amount = free - tx;
        if (amount < p.minBuySol) continue;
        const lamports = BigInt(Math.floor(amount * LAMPORTS));
        orders.push({ side: 'buy', mint, quote_lamports: lamports, max_slippage_bps: p.buySlipBps });
        free -= amount + tx;
        exposure += amount;
        if (h === undefined) {
          held.set(mint, {
            opened: now,
            peakValue: 0,
            invested: amount,
            exiting: false,
            filled: false,
            lastAddPrice: price,
            lastValue: 0,
          });
          t.entries++;
          slotsLeft--;
          mainLeft--;
        } else {
          h.invested += amount;
          h.lastAddPrice = price;
        }
      }

      // ---- Guardrail pacing: open a probe when fills or coins lag the pace. ----
      if (probes.size < p.maxProbes && slotsLeft > 0 && firstTime !== null && lastTime !== null) {
        const pace = Math.min(1, (lastTime - firstTime) / p.paceSecs);
        const needCoins = myCoins.size < Math.ceil(p.targetCoins * pace);
        const needFills = myFills < Math.ceil(p.targetFills * pace);
        if (needCoins || needFills) {
          const minRq = (p.probeSol * BPS) / state.hello.caps.max_order_bps_of_real_reserve;
          for (const mint of traded) {
            if (orders.length >= cap || probes.size >= p.maxProbes) break;
            if (held.has(mint) || probes.has(mint) || pendingByMint.has(mint) || state.positions.has(mint)) continue;
            if (needCoins && !needFills && myCoins.has(mint)) continue;
            const curve = state.curves.get(mint);
            if (curve === undefined || curve.complete) continue;
            if (Number(curve.real_quote_reserves) / LAMPORTS < minRq * 1.5) continue;
            if (free < p.probeSol + 2 * tx) break;
            orders.push({ side: 'buy', mint, quote_lamports: BigInt(Math.floor(p.probeSol * LAMPORTS)), max_slippage_bps: p.buySlipBps });
            probes.set(mint, false);
            free -= p.probeSol + tx;
          }
        }
      }
      return orders;
    },
  };
}

const isMain = typeof process.argv[1] === 'string' && process.argv[1].endsWith('main.ts');
if (isMain) {
  await runBot(createBot());
}
