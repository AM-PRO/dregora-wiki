// Anvil plan optimizer, shared by the page, its Web Worker and the tests.
// A plan is a tree: {item: true} | {b: bookIndex} | {l, r} | {up: itemSide}. The item is always the leftmost leaf.
// Cost rules come from Anvil Patch (REMOVE_REPAIR_SCALING), see README.
// {up} is the Upgraded Potentials book put on the item (SME EnchantmentUpgradedPotentials.onAnvilUpdateEvent):
// fixed cost, cut penalty, once per item, and only on an item that already carries an enchantment.

function OptimizerCore() {
  const BOOK_MULT = [1, 1, 2, 4];

  // Vanilla EntityPlayer.xpBarCap, summed to get the points held at a given level.
  const barCap = (l) => (l >= 30 ? 112 + (l - 30) * 9 : l >= 15 ? 37 + (l - 15) * 5 : 7 + l * 2);
  const xpCache = [0];
  function xpAt(lvl) {
    while (xpCache.length <= lvl) { const l = xpCache.length - 1; xpCache.push(xpCache[l] + barCap(l)); }
    return xpCache[lvl];
  }
  const costFn = (objective) => (objective === "xp" ? xpAt : (c) => c);
  const UP_COST = 10;
  const upPen = (pen) => Math.max(0, Math.floor(pen / 4) - 20);

  // Walks a plan, writes step/pen on merge nodes and returns totals.
  function evalTree(node, vals, p0, f) {
    if (node.item) return { pen: p0, cost: 0, val: 0, levels: 0 };
    if (node.b !== undefined) return { pen: 0, cost: 0, val: vals[node.b], levels: 0 };
    if (node.up) {
      const I = evalTree(node.up, vals, p0, f);
      node.step = UP_COST;
      node.pen = upPen(I.pen);
      return { pen: node.pen, cost: I.cost + f(UP_COST), val: I.val, levels: I.levels + UP_COST };
    }
    const L = evalTree(node.l, vals, p0, f), R = evalTree(node.r, vals, p0, f);
    const step = L.pen + R.pen + R.val;
    node.step = step;
    node.pen = 2 * Math.max(L.pen, R.pen) + 1;
    return { pen: node.pen, cost: L.cost + R.cost + f(step), val: L.val + R.val, levels: L.levels + R.levels + step };
  }

  // Only a book's cost value matters, so books with equal values are interchangeable.
  // The exact search runs over multisets of value classes instead of subsets of books.
  function classesOf(vals) {
    const classes = [...new Set(vals)].sort((a, b) => a - b);
    const members = classes.map((v) => vals.map((x, i) => (x === v ? i : -1)).filter((i) => i >= 0));
    return { classes, members, m: members.map((x) => x.length) };
  }

  // Number of (state, sub-multiset) pairs visited by the exact search; the Upgraded Potentials states add about half.
  function exactWork(vals, up) {
    return classesOf(vals).m.reduce((w, k) => w * ((k + 1) * (k + 2)) / 2, 1) * (up ? 1.5 : 1);
  }

  function addPareto(list, c) {
    for (const x of list) if (x.pen <= c.pen && x.cost <= c.cost) return;
    for (let i = list.length - 1; i >= 0; i--) if (c.pen <= list[i].pen && c.cost <= list[i].cost) list.splice(i, 1);
    list.push(c);
  }

  // item[s]: Pareto front (penalty, cost) of the item once it got the books of multiset s.
  // itemU[s]: the same with the Upgraded Potentials book applied somewhere along the way (only when `up` is set).
  function exactPlan(vals, p0, objective, onProgress, up) {
    const f = costFn(objective);
    const { classes, members, m } = classesOf(vals);
    const d = classes.length;
    const base = [];
    let S = 1;
    for (let i = 0; i < d; i++) { base.push(S); S *= m[i] + 1; }
    const val = new Float64Array(S), count = new Int32Array(S);
    const digits = (s, out) => { for (let i = 0; i < d; i++) { out[i] = Math.floor(s / base[i]) % (m[i] + 1); } return out; };
    const dg = new Int32Array(d);
    for (let s = 0; s < S; s++) {
      digits(s, dg);
      let v = 0, c = 0;
      for (let i = 0; i < d; i++) { v += dg[i] * classes[i]; c += dg[i]; }
      val[s] = v; count[s] = c;
    }
    const book = new Array(S), item = new Array(S), itemU = new Array(S);
    item[0] = [{ pen: p0, cost: 0 }];
    // A penalty means the item went through the anvil already, so it carries an enchantment and can take the book now.
    itemU[0] = up && p0 > 0 ? [{ pen: upPen(p0), cost: f(UP_COST), up: true }] : [];
    const cs = new Int32Array(d), as = new Int32Array(d);
    const total = S * 2;
    let done = 0, lastReport = Date.now();
    // Sub-multisets have smaller mixed-radix indices, so increasing index order is a valid DP order.
    for (let s = 1; s < S; s++) {
      digits(s, cs);
      const bl = [], il = [], ul = [];
      if (count[s] === 1) bl.push({ pen: 0, cost: 0 });
      // A runs over every sub-multiset of s from s down to 0 (odometer in mixed radix).
      // First pass builds book[s]; the second needs it, since the item can take all of s as one book.
      book[s] = bl;
      for (const pass of [0, 1]) {
        if (pass === 0 && count[s] === 1) continue;
        as.set(cs);
        let A = s;
        while (true) {
          const B = s - A;
          if (B > 0) {
            const vb = val[B];
            if (pass === 1) {
              for (const x of item[A]) for (const b of book[B]) {
                const step = x.pen + b.pen + vb;
                addPareto(il, { pen: 2 * Math.max(x.pen, b.pen) + 1, cost: x.cost + b.cost + f(step), A, x, b });
              }
              if (up) for (const x of itemU[A]) for (const b of book[B]) {
                const step = x.pen + b.pen + vb;
                addPareto(ul, { pen: 2 * Math.max(x.pen, b.pen) + 1, cost: x.cost + b.cost + f(step), A, x, b });
              }
            } else if (A > 0) {
              for (const a of book[A]) for (const b of book[B]) {
                const step = a.pen + b.pen + vb;
                addPareto(bl, { pen: 2 * Math.max(a.pen, b.pen) + 1, cost: a.cost + b.cost + f(step), A, a, b });
              }
            }
          }
          if (A === 0) break;
          let i = 0;
          while (as[i] === 0) { as[i] = cs[i]; A += cs[i] * base[i]; i++; }
          as[i]--; A -= base[i];
        }
      }
      item[s] = il;
      if (up) for (const x of il) addPareto(ul, { pen: upPen(x.pen), cost: x.cost + f(UP_COST), up: true, x });
      itemU[s] = ul;
      done += 2;
      if (onProgress && (s & 1023) === 0 && Date.now() - lastReport > 150) { lastReport = Date.now(); onProgress(done / total); }
    }
    let best = null, bestU = false;
    const consider = (list, u) => {
      for (const c of list) if (!best || c.cost < best.cost || (c.cost === best.cost && c.pen < best.pen)) { best = c; bestU = u; }
    };
    consider(item[S - 1], false);
    consider(itemU[S - 1], true);

    const pool = members.map((x) => x.slice());
    const bookTree = (s, e) => {
      if (count[s] === 1) { digits(s, dg); for (let i = 0; i < d; i++) if (dg[i]) return { b: pool[i].pop() }; }
      return { l: bookTree(e.A, e.a), r: bookTree(s - e.A, e.b) };
    };
    const itemTree = (s, e) => (s === 0 ? { item: true } : { l: itemTree(e.A, e.x), r: bookTree(s - e.A, e.b) });
    const itemUTree = (s, e) => (e.up
      ? { up: s === 0 ? { item: true } : itemTree(s, e.x) }
      : { l: itemUTree(e.A, e.x), r: bookTree(s - e.A, e.b) });
    return { tree: (bestU ? itemUTree : itemTree)(S - 1, best), cost: best.cost };
  }

  // ---------- Simulated annealing for selections too large for the exact search ----------
  // A plan is stored as a chain of book trees applied to the item in order, plus u: the number of chain books
  // applied before the Upgraded Potentials book (-1 = not used, 0 only on an item that has a penalty already).
  function rng(seed) {
    let s = seed >>> 0 || 1;
    return () => { s ^= s << 13; s ^= s >>> 17; s ^= s << 5; return (s >>> 0) / 4294967296; };
  }
  const clone = (n) => (n.b !== undefined ? { b: n.b } : { l: clone(n.l), r: clone(n.r) });
  const toTree = (chain, u) => {
    let acc = u === 0 ? { up: { item: true } } : { item: true };
    chain.forEach((t, i) => { acc = { l: acc, r: t }; if (i + 1 === u) acc = { up: acc }; });
    return acc;
  };

  function chainCost(chain, u, vals, p0, f) {
    let pen = p0, cost = 0;
    const rec = (n) => {
      if (n.b !== undefined) return [0, 0, vals[n.b]];
      const L = rec(n.l), R = rec(n.r), step = L[0] + R[0] + R[2];
      cost += f(step);
      return [2 * Math.max(L[0], R[0]) + 1, 0, L[2] + R[2]];
    };
    if (u === 0) { cost += f(UP_COST); pen = upPen(pen); }
    chain.forEach((t, i) => {
      const [bp, , bv] = rec(t);
      cost += f(pen + bp + bv);
      pen = 2 * Math.max(pen, bp) + 1;
      if (i + 1 === u) { cost += f(UP_COST); pen = upPen(pen); }
    });
    return cost;
  }

  function nodesOf(chain) {
    const out = [];
    chain.forEach((t, ci) => {
      const rec = (n, p) => { out.push({ n, p, ci }); if (n.b === undefined) { rec(n.l, n); rec(n.r, n); } };
      rec(t, null);
    });
    return out;
  }
  const replace = (target, src) => { for (const k of Object.keys(target)) delete target[k]; Object.assign(target, src); };

  function mutate(chain, rand) {
    const c = chain.map(clone);
    const nodes = nodesOf(c);
    const pick = (arr) => arr[Math.floor(rand() * arr.length)];
    const kind = rand();
    if (kind < 0.3) {
      const leaves = nodes.filter((x) => x.n.b !== undefined);
      const a = pick(leaves).n, b = pick(leaves).n;
      [a.b, b.b] = [b.b, a.b];
    } else if (kind < 0.4) {
      const inner = nodes.filter((x) => x.n.b === undefined);
      if (inner.length) { const n = pick(inner).n; [n.l, n.r] = [n.r, n.l]; }
    } else if (kind < 0.5) {
      if (c.length > 1) { const i = Math.floor(rand() * c.length), j = Math.floor(rand() * c.length); [c[i], c[j]] = [c[j], c[i]]; }
    } else {
      // Move a subtree: detach it, then put it in a new chain slot or next to another node.
      const e = pick(nodes);
      const moved = clone(e.n);
      if (!e.p) c.splice(e.ci, 1);
      else replace(e.p, clone(e.p.l === e.n ? e.p.r : e.p.l));
      const rest = nodesOf(c);
      if (!rest.length || rand() < 0.3) c.splice(Math.floor(rand() * (c.length + 1)), 0, moved);
      else {
        const x = pick(rest).n, copy = clone(x);
        replace(x, rand() < 0.5 ? { l: copy, r: moved } : { l: moved, r: copy });
      }
    }
    return c;
  }

  // Start: books sorted by value, merged pairwise into one balanced book (big values on the left).
  function initialChain(vals) {
    let level = vals.map((v, i) => i).sort((a, b) => vals[b] - vals[a]).map((i) => ({ b: i }));
    while (level.length > 1) {
      const next = [];
      for (let i = 0; i < level.length; i += 2) next.push(i + 1 < level.length ? { l: level[i], r: level[i + 1] } : level[i]);
      level = next;
    }
    return level;
  }

  function annealPlan(vals, p0, objective, timeMs, seed, onImprove, up) {
    const f = costFn(objective);
    const rand = rng(seed || 12345);
    const uMin = p0 > 0 ? 0 : 1;
    // Keeps the book where it was when the chain changes length, within the valid range.
    const fitU = (u, n) => (u < 0 ? -1 : Math.max(uMin, Math.min(u, n)));
    let best = initialChain(vals), bestU = -1, bestCost = chainCost(best, -1, vals, p0, f);
    if (up) for (let u = uMin; u <= best.length; u++) {
      const c = chainCost(best, u, vals, p0, f);
      if (c < bestCost) { bestU = u; bestCost = c; }
    }
    const end = Date.now() + timeMs;
    const avg = vals.reduce((a, b) => a + b, 0) / vals.length || 1;
    while (Date.now() < end) {
      // One restart: cool from about one book value down to near zero.
      let cur = best.map(clone), curU = bestU, curCost = bestCost;
      const iters = 4000 + vals.length * 400;
      for (let k = 0; k < iters; k++) {
        const T = avg * 2 * Math.pow(0.002, k / iters);
        let cand = cur, candU;
        if (up && rand() < 0.15) {
          // Move the Upgraded Potentials book along the chain, or take it out now and then.
          candU = rand() < 0.1 ? -1 : uMin + Math.floor(rand() * (cur.length - uMin + 1));
        } else {
          cand = mutate(cur, rand);
          candU = fitU(curU, cand.length);
        }
        const cc = chainCost(cand, candU, vals, p0, f);
        if (cc <= curCost || rand() < Math.exp((curCost - cc) / T)) {
          cur = cand; curU = candU; curCost = cc;
          if (cc < bestCost) { best = cand.map(clone); bestU = candU; bestCost = cc; if (onImprove) onImprove(toTree(best, bestU), bestCost); }
        }
      }
    }
    return { tree: toTree(best, bestU), cost: bestCost };
  }

  return { BOOK_MULT, UP_COST, xpAt, costFn, upPen, evalTree, exactWork, exactPlan, annealPlan };
}

// Worker entry: posts a quick approximate plan when the exact search is long, then the exact plan if it is tractable.
// Without the Upgraded Potentials book, a quick search also posts the plan it would allow, to show what it would save.
function OptimizerWorker() {
  const C = OptimizerCore();
  const FAST_WORK = 2e6, EXACT_MAX_WORK = 1.5e8;
  self.onmessage = (ev) => {
    const { vals, p0, objective, up } = ev.data;
    const work = C.exactWork(vals, up);
    if (work <= FAST_WORK) {
      const r = C.exactPlan(vals, p0, objective, null, up);
      self.postMessage({ type: "plan", exact: true, final: true, tree: r.tree });
      if (!up && C.exactWork(vals, true) <= FAST_WORK) self.postMessage({ type: "upPlan", tree: C.exactPlan(vals, p0, objective, null, true).tree });
      return;
    }
    const exactPossible = work <= EXACT_MAX_WORK;
    let lastPost = 0;
    const post = (tree, final) => self.postMessage({ type: "plan", exact: false, final, exactPending: exactPossible && !final, tree });
    const a = C.annealPlan(vals, p0, objective, exactPossible ? 600 : 4000, 1, (tree) => {
      if (Date.now() - lastPost > 300) { lastPost = Date.now(); post(tree, false); }
    }, up);
    post(a.tree, !exactPossible);
    if (!exactPossible) return;
    const r = C.exactPlan(vals, p0, objective, (p) => self.postMessage({ type: "progress", p }), up);
    self.postMessage({ type: "plan", exact: true, final: true, tree: r.tree });
  };
}

if (typeof module !== "undefined") module.exports = { OptimizerCore };
