"""Exact toy check of Lemma Y (proofs/bands.md, Sec. 10), end to end, with mixed segment lengths.

Model (Secs. 2 and 4 of bands.md on a toy): one K0 x K0 tile; inner sets grouped by segment signature, each good class
(the zone segment 0 holds at least z0 outer levels) placed WHOLE on one integer diagonal (cells (r, r + delta)) in
random order. Row label j = r 3^n' + sum_{rank >= z0} u 3^(rank - z0), column label k = c 3^n' + sum_{rank >= z0}
v 3^(rank - z0) + sigma0, key = (k - j, zone row digits, zone column digits), and W is a union of random key fibres.
For every w in W and every order-d leaf (T, terms) of w, the representative (the lexicographically smallest member
in W) is found by listing ALL members of the leaf. Rule Y (non-zone segments, the window equation of Lemma Y) and
Rule Z per element (zone segment) are applied to every element, with no condition (a). Checks:
 (0) every movable element's target is a position in W with the same key and a lexicographically smaller set;
 (1) for every w: #{leaves whose representative is w} <= R^Y(w) = #{(T, terms) with no movable element};
 (2) R^Y(w) = [z^d] prod_{p in Q} (1 + 9 b_p z) for every w, with b_p from the rule (the generating function);
 (3) the mechanism is exercised: moves with windows of two or more outer levels, across Z levels, across T levels.
Must-fail controls, in the same run: (A) the naive window "key kept iff d_a = t", which ignores the rank shift;
(B) targets allowed in the segment below; (C) Rule Y inside the zone segment (changes x, y). A control fails if it
produces a target outside W or a violation of (1).
Pure Python. The six cases take about 1 minute of CPU; with no argument (or several cases) they run in parallel, one
process each, and print in case order (about 15 s on six cores). `python check_bands_y.py 0` runs case 0 alone (about
2 s, tests/test_bands_y.py). The checks are explicit (SystemExit).
"""
import sys as _sys
# For uniformity with the other mechanical checks, refuse python -O (the checks here do not use assert).
if not __debug__:
    _sys.exit("refusing to run under python -O")
import itertools, multiprocessing, os, random, sys
from math import comb
from operator import itemgetter

def die(m):
    print("CHECK FAILED:", m, flush=True); raise SystemExit(1)

def run(L, mu, segs, z0, d, frac, seed, K0=None):
    rng = random.Random(seed)
    assert sum(segs) == L
    segof = []
    for s, l in enumerate(segs): segof += [s] * l
    nout = L - mu; npr = nout - z0
    Qs = list(itertools.combinations(range(L), mu))
    sig = lambda Q: tuple(sum(1 for q in Q if segof[q] == s) for s in range(len(segs)))
    good = lambda Q: segs[0] - sig(Q)[0] >= z0
    classes = {}
    for Q in Qs:
        if good(Q): classes.setdefault(sig(Q), []).append(Q)
    cl = list(classes.values()); rng.shuffle(cl)
    K0 = K0 or max(len(c) for c in cl) + 2
    cap = {dl: K0 - dl for dl in range(K0)}; used = {dl: 0 for dl in range(K0)}
    cell = {}
    for c in cl:
        opts = [dl for dl in range(K0) if cap[dl] - used[dl] >= len(c)]
        if not opts: die("packing")
        dl = rng.choice(opts)
        for Q in c:
            r = used[dl]; cell[Q] = (r, r + dl); used[dl] += 1
    sigma0 = rng.randrange(3 ** npr)
    parts = {}
    def key(Q, s):
        if s not in parts:                          # the parts of the labels that do not depend on Q
            parts[s] = (sum((s[i] // 3) * 3 ** (i - z0) for i in range(z0, nout)),
                        sum((s[i] % 3) * 3 ** (i - z0) for i in range(z0, nout)),
                        tuple(x // 3 for x in s[:z0]), tuple(x % 3 for x in s[:z0]))
        rows, cols, zr, zc = parts[s]
        r, c = cell[Q]
        j = r * 3 ** npr + rows
        k = c * 3 ** npr + cols + sigma0
        return (k - j, zr, zc)
    fib = {}
    for Q in cell:
        for s in itertools.product(range(9), repeat=nout):
            fib.setdefault(key(Q, s), []).append((Q, s))
    ks = sorted(fib); rng.shuffle(ks)
    W = set(); Wk = {Q: {} for Q in cell}          # Wk[Q][s] = the key of (Q, s), for every (Q, s) in W
    for kk in ks[:max(1, int(frac * len(ks)))]:
        W.update(fib[kk])
        for Q, s in fib[kk]: Wk[Q][s] = kk
    Wl = sorted(W)

    belows = {}; tmemo = {}
    def targets(Q, s, p, mode):
        """For element p of Q: the target level p' for each term t (pair 0..8), None where p is not movable. It depends
        on s only through the digits of the outer levels below p that the window can reach (memoised on those)."""
        if (Q, p, mode) not in belows:
            O = [l for l in range(L) if l not in Q]
            sp = segof[p]
            lowseg = sp - 1 if mode == "B" else sp
            belows[Q, p, mode] = O, [i for i, o in enumerate(O) if o < p and lowseg <= segof[o] <= sp]
        O, below = belows[Q, p, mode]
        dig = tuple(s[i] for i in below)
        if (Q, p, mode, dig) in tmemo: return tmemo[Q, p, mode, dig]
        if not below: tab = [None] * 9
        elif segof[p] == 0 and mode != "C":
            tab = [O[below[-1]] if dig[-1] == t else None for t in range(9)]
        else:
            if any(i < z0 for i in below) and mode == "Y":
                die("non-zone window below z0 (good-signature condition broken)")
            dd = [(x % 3) - (x // 3) for x in dig]
            N = len(below)
            # target below[a], window below[a..N-1] (m = N - 1 - a): the window value must equal tdiff 3^m
            val = [dd[a] if mode == "A" else dd[a] + 2 * sum(dd[a + jj] * 3 ** (jj - 1) for jj in range(1, N - a))
                   for a in range(N)]
            scale = [1 if mode == "A" else 3 ** (N - 1 - a) for a in range(N)]
            tgt = {td: next((O[below[a]] for a in range(N) if val[a] == td * scale[a]), None) for td in range(-2, 3)}
            tab = [tgt[(t % 3) - (t // 3)] for t in range(9)]
        tmemo[Q, p, mode, dig] = tab
        return tab

    def getter(idx):
        """x -> tuple(x[i] for i in idx), as one C call."""
        idx = tuple(idx)
        return itemgetter(*idx) if len(idx) > 1 else (lambda x: tuple(x[i] for i in idx))

    plans = {}
    def plan(Q):
        """Per T, what the leaves of (Q, s) share for every s and every mode."""
        if Q not in plans:
            O = [l for l in range(L) if l not in Q]
            plans[Q] = pl = []
            for T in itertools.combinations(Q, d):
                Z = tuple(q for q in Q if q not in T)
                F = sorted(O + list(T))
                # a leaf is the digit tuple s + tt (the outer digits of w, then the terms); F[i] sits at pos[i] in it
                pos = [len(O) + T.index(l) if l in T else O.index(l) for l in F]
                def member(Tp):
                    """(Q2, getter of the digits s2 from s + tt) of the member of the leaf with deleted set Tp."""
                    return tuple(sorted(Z + Tp)), getter([pos[i] for i, l in enumerate(F) if l not in Tp])
                cands = []
                for Tp in itertools.combinations(F, d):
                    Q2, g = member(Tp)
                    if Q2 in cell: cands.append((Tp, Wk[Q2], g))
                info = {}
                for p in T:
                    for pp in O:
                        Tp = tuple(sorted(set(T) - {p} | {pp}))
                        Q2, g = member(Tp)
                        between = range(pp + 1, p)
                        info[p, pp] = (Wk[Q2] if Q2 in cell and Tp < T else None, g,
                                       sum(1 for l in between if l not in Q) >= 1,
                                       any(l in Z for l in between), any(l in T for l in between))
                pl.append((T, tuple(Q.index(p) for p in T), cands, info))
        return plans[Q]

    # The leaf data (the representative of every leaf of every w) does not depend on the mode: it is computed once and
    # the four modes are evaluated on it; the statistics are kept per mode.
    modes = ("Y", "A", "B", "C")
    outside = [0] * 4; viol = [0] * 4; sumR = [0] * 4; gf_bad = [0] * 4; sumRep = 0
    cnt = [{"window>=2": 0, "crosses Z level": 0, "crosses T level": 0, "moves": 0} for _ in modes]
    for (Q, s) in Wl:
        kw = Wk[Q][s]
        tabs = [[targets(Q, s, p, mode) for p in Q] for mode in modes]      # tabs[mode][index of p in Q][t]
        rep_w = 0; R = [0] * 4
        for T, tq, cands, info in plan(Q):
            for tt in itertools.product(range(9), repeat=d):
                cat = s + tt
                # representative: lex-min deleted set among members in W
                rep = None
                for Tp, Wq2, g in cands:
                    if g(cat) in Wq2: rep = Tp; break
                if rep == T: rep_w += 1
                for mi in range(4):
                    anym = False
                    for i, ip in enumerate(tq):
                        pp = tabs[mi][ip][tt[i]]
                        if pp is None: continue
                        anym = True
                        Wq2, g, win2, zl, tl = info[T[i], pp]
                        if Wq2 is None or Wq2.get(g(cat)) != kw: outside[mi] += 1
                        c = cnt[mi]
                        c["moves"] += 1; c["window>=2"] += win2; c["crosses Z level"] += zl; c["crosses T level"] += tl
                    if not anym: R[mi] += 1
        sumRep += rep_w
        for mi in range(4):
            if rep_w > R[mi]: viol[mi] += 1
            # (2): R must be the coefficient of z^d in prod_p (1 + 9 b_p z), 9 b_p = #terms with p not movable
            cf = [1]
            for ip in range(mu):
                nb = tabs[mi][ip].count(None)
                cf = [(cf[k] if k < len(cf) else 0) + (nb * cf[k - 1] if k else 0) for k in range(len(cf) + 1)]
            if cf[d] != R[mi]: gf_bad[mi] += 1
            sumR[mi] += R[mi]
    res = {mode: (outside[mi], viol[mi], sumR[mi], sumRep, cnt[mi], gf_bad[mi]) for mi, mode in enumerate(modes)}
    return len(W), res

def report(case):
    """Run one case: its printed line, and whether every check holds (the three controls must fail)."""
    (L, mu, segs, z0, d, frac, seed) = case
    nW, res = run(L, mu, segs, z0, d, frac, seed)
    o, v, sR, sRep, cnt, gfb = res["Y"]
    ok = o == 0 and v == 0 and gfb == 0 and sRep <= sR and cnt["window>=2"] > 0 \
        and (mu - d < 1 or cnt["crosses Z level"] > 0) and (d < 2 or cnt["crosses T level"] > 0)
    line = (f"L={L} mu={mu} segs={segs} z0={z0} d={d} seed={seed} |W|={nW}: Y: targets bad={o} per-w viol={v} "
            f"|Leaves|={sRep} <= sumR_Y={sR} GF mismatches={gfb} {cnt} {'OK' if ok else 'FAIL'}")
    for mname in ("A", "B", "C"):
        o2, v2, sR2, sRep2, _, _ = res[mname]
        failed = o2 > 0 or v2 > 0
        line += f" | control {mname}: bad targets={o2} per-w viol={v2} {'fails as required' if failed else 'DID NOT FAIL'}"
        ok &= failed
    return line, ok

def report_in_worker(case):
    try: return report(case)
    except SystemExit: return None                  # die() has printed its message; the parent exits

def reports(cases):
    """The report of each case, in the order of the cases. Several cases run in parallel, one process each."""
    if len(cases) == 1:
        yield report(cases[0]); return
    with multiprocessing.Pool(min(len(cases), os.cpu_count() or 1)) as pool:
        for r in pool.imap(report_in_worker, cases):        # imap keeps the order
            if r is None: raise SystemExit(1)
            yield r

if __name__ == "__main__":
    cases = [(6, 2, (3, 3), 1, 1, 0.3, 1), (6, 2, (3, 3), 1, 2, 0.3, 2), (7, 3, (3, 4), 1, 1, 0.3, 3),
             (7, 2, (3, 4), 1, 1, 0.15, 4), (7, 3, (4, 3), 1, 2, 0.08, 5), (7, 2, (2, 5), 1, 1, 0.15, 6)]
    if len(sys.argv) > 1: cases = [cases[int(i)] for i in sys.argv[1].split(',')]
    allok = True
    for line, ok in reports(cases):
        print(line, flush=True); allok &= ok
    print("ALL OK" if allok else "PROBLEM")
    if not allok: raise SystemExit(1)
