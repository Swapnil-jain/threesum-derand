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
Pure Python. The six cases take about 20 minutes on one core; `python check_bands_y.py 0` runs case 0 alone (about
2 minutes, tests/test_bands_y.py). The checks are explicit (SystemExit).
"""
import sys as _sys
# For uniformity with the other mechanical checks, refuse python -O (the checks here do not use assert).
if not __debug__:
    _sys.exit("refusing to run under python -O")
import itertools, random, sys
from math import comb

def die(m):
    print("CHECK FAILED:", m); raise SystemExit(1)

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
    def key(Q, s):
        r, c = cell[Q]
        j = r * 3 ** npr + sum((s[i] // 3) * 3 ** (i - z0) for i in range(z0, nout))
        k = c * 3 ** npr + sum((s[i] % 3) * 3 ** (i - z0) for i in range(z0, nout)) + sigma0
        return (k - j, tuple(x // 3 for x in s[:z0]), tuple(x % 3 for x in s[:z0]))
    fib = {}
    for Q in cell:
        for s in itertools.product(range(9), repeat=nout):
            fib.setdefault(key(Q, s), []).append((Q, s))
    ks = sorted(fib); rng.shuffle(ks)
    W = set()
    for kk in ks[:max(1, int(frac * len(ks)))]: W.update(fib[kk])
    Wl = sorted(W)

    def movable(Q, s, p, t, mode):
        """Return target level p' for element p with term t (pair 0..8), or None."""
        O = [l for l in range(L) if l not in Q]
        sp = segof[p]
        lowseg = sp - 1 if mode == "B" else sp
        below = [i for i, o in enumerate(O) if o < p and lowseg <= segof[o] <= sp]
        if not below: return None
        zone = segof[p] == 0 and mode != "C"
        if zone:
            i = below[-1]
            return O[i] if s[i] == t else None
        if any(i < z0 for i in below) and mode == "Y":
            die("non-zone window below z0 (good-signature condition broken)")
        dd = [(s[i] % 3) - (s[i] // 3) for i in below]
        tdiff = (t % 3) - (t // 3)
        N = len(below)
        for a in range(N):                 # target below[a], window below[a..N-1]
            m = N - 1 - a
            if mode == "A":
                ok = dd[a] == tdiff
            else:
                ok = dd[a] + 2 * sum(dd[a + jj] * 3 ** (jj - 1) for jj in range(1, m + 1)) == tdiff * 3 ** m
            if ok: return O[below[a]]
        return None

    res = {}
    for mode in ("Y", "A", "B", "C"):
        outside = 0; viol = 0; sumR = 0; sumRep = 0; gf_bad = 0
        cnt = {"window>=2": 0, "crosses Z level": 0, "crosses T level": 0, "moves": 0}
        for (Q, s) in Wl:
            O = [l for l in range(L) if l not in Q]
            rep_w = 0; R = 0
            for T in itertools.combinations(Q, d):
                Z = tuple(q for q in Q if q not in T)
                F = sorted(O + list(T))
                for tt in itertools.product(range(9), repeat=d):
                    tm = dict(zip(T, tt))
                    full = tuple(tm[l] if l in tm else s[O.index(l)] for l in F)
                    # representative: lex-min deleted set among members in W
                    rep = None
                    for Tp in itertools.combinations(F, d):
                        Q2 = tuple(sorted(Z + Tp))
                        if Q2 not in cell: continue
                        s2 = tuple(full[i] for i, l in enumerate(F) if l not in Tp)
                        if (Q2, s2) in W: rep = Tp; break
                    if rep == T: rep_w += 1
                    anym = False
                    for p in T:
                        pp = movable(Q, s, p, tm[p], mode)
                        if pp is None: continue
                        anym = True; cnt["moves"] += 1
                        Tp = tuple(sorted(set(T) - {p} | {pp}))
                        Q2 = tuple(sorted(Z + Tp))
                        s2 = tuple(full[i] for i, l in enumerate(F) if l not in Tp)
                        if Q2 not in cell or (Q2, s2) not in W or not Tp < T or key(Q2, s2) != key(Q, s):
                            outside += 1
                        between = [l for l in range(pp + 1, p)]
                        if sum(1 for l in between if l not in Q) >= 1: cnt["window>=2"] += 1
                        if any(l in Z for l in between): cnt["crosses Z level"] += 1
                        if any(l in T for l in between): cnt["crosses T level"] += 1
                    if not anym: R += 1
            if rep_w > R: viol += 1
            # (2): R must be the coefficient of z^d in prod_p (1 + 9 b_p z), 9 b_p = #terms with p not movable
            cf = [1]
            for p in Q:
                nb = sum(1 for t in range(9) if movable(Q, s, p, t, mode) is None)
                cf = [(cf[k] if k < len(cf) else 0) + (nb * cf[k - 1] if k else 0) for k in range(len(cf) + 1)]
            if cf[d] != R: gf_bad += 1
            sumR += R; sumRep += rep_w
        res[mode] = (outside, viol, sumR, sumRep, cnt, gf_bad)
    return len(W), res

if __name__ == "__main__":
    cases = [(6, 2, (3, 3), 1, 1, 0.3, 1), (6, 2, (3, 3), 1, 2, 0.3, 2), (7, 3, (3, 4), 1, 1, 0.3, 3),
             (7, 2, (3, 4), 1, 1, 0.15, 4), (7, 3, (4, 3), 1, 2, 0.08, 5), (7, 2, (2, 5), 1, 1, 0.15, 6)]
    if len(sys.argv) > 1: cases = [cases[int(i)] for i in sys.argv[1].split(',')]
    allok = True
    for (L, mu, segs, z0, d, frac, seed) in cases:
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
        print(line, flush=True); allok &= ok
    print("ALL OK" if allok else "PROBLEM")
    if not allok: raise SystemExit(1)
