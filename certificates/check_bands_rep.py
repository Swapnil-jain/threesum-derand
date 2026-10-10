"""Mechanical check of Lemmas 2.1 and 2.2 of proofs/bands.md (the canonical representative and its generating
function) on one tile, by brute force over every leaf. Exact integers and fractions; standard library only.

Setting: L levels, inner sets of size mu, a K0 x K0 grid of block products (cell (r, c) carries the inner set
Q(r, c)), row and column strings over the outer levels indexed by rank (rank 0 = lowest outer level), a zone of the
ranks below z0, and integer labels j = r 3^n' + sum_{rank >= z0} digit 3^(rank - z0). A key fibre is the set of
positions with one key (column label - row label, row zone digits, column zone digits); W is a union of fibres.
Asserted: |Leaves_d(W)| <= sum_{w in W} R_d(w), where R_d(w) counts the order-d leaves of w with no movable element,
and, for adjacent moves, R_d(w) = [z^d] prod_G P_G(z) exactly. A move of p in T needs (a) p lowest in T within its
gap, (b) a target p' in the stretch below the gap (adjacent moves: the outer level just below), (c) rank(p') >= z0,
(d) Q - p + p' in a used cell on the same diagonal c - r, (e) the moved member in the same key fibre.
Runs: random grids and segment grids, adjacent and stretch moves, d = 1, 2; and segment grids fine enough that whole
signature classes sit on one diagonal, where moves are actually used (the bound is asserted strictly below the
trivial count, and the stretch bound at most the adjacent one).
Negative controls, each of which must violate the inequality somewhere: dropping (d), dropping (e), and a W that is
not a union of fibres. Logic only, not asymptotics. Usage: python check_bands_rep.py
"""
import sys as _sys
# These checks rely on assert and on the exit status, and python -O strips asserts; refuse to run there.
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assert statements")
import itertools, random, sys
from fractions import Fraction

def run(L, mu, z0, K0, grid_mode, d, nfib, seed, control=None, stretch=False, seglen=None):
    rnd = random.Random(seed)
    Qs = list(itertools.combinations(range(L), mu))
    if grid_mode == "segments":
        # signature classes for segments; place whole classes on diagonals greedily, then random filler
        if seglen: segs = [range(a, min(a + seglen, L)) for a in range(0, L, seglen)]
        else: segs = [range(0, 3), range(3, L)] if L > 3 else [range(L)]
        def sig(Q): return tuple(sum(1 for l in Q if l in s) for s in segs)
        classes = {}
        for Q in Qs: classes.setdefault(sig(Q), []).append(Q)
        cells = {}
        diag_cells = {dl: [(r, r + dl) for r in range(K0) if 0 <= r + dl < K0] for dl in range(-K0 + 1, K0)}
        used = set()
        order = sorted(classes.values(), key=len)
        for dl in sorted(diag_cells, key=lambda x: abs(x)):
            free = list(diag_cells[dl])
            for cl in order:
                if len(cl) <= len(free) and not (set(cl) & used):
                    for Q in cl: cells[free.pop(0)] = Q
                    used |= set(cl)
            rest = [Q for Q in Qs if Q not in used]
            rnd.shuffle(rest)
            for cell in free:
                Q = rest.pop(); cells[cell] = Q; used.add(Q)
    else:
        pick = rnd.sample(Qs, K0 * K0)
        cells = {(r, c): pick[r * K0 + c] for r in range(K0) for c in range(K0)}
    where = {Q: cell for cell, Q in cells.items()}
    n0 = L - mu; npr = n0 - z0
    def lab(g, s):  # integer label of group g with string s (tuple over ranks)
        return g * 3 ** npr + sum(s[k] * 3 ** (k - z0) for k in range(z0, n0))
    def fkey(r, c, s, t):
        return (lab(c, t) - lab(r, s), s[:z0], t[:z0])
    strings = list(itertools.product(range(3), repeat=n0))
    allpos = [(r, c, s, t) for (r, c) in cells for s in strings for t in strings]
    keys = {}
    for p in allpos: keys.setdefault(fkey(*p), []).append(p)
    if control == "nonfibre":
        W = set(rnd.sample(allpos, nfib * 40))
    else:
        W = set()
        for k in rnd.sample(sorted(keys), nfib): W |= set(keys[k])
    def leaves_of(w):
        r, c, s, t = w; Q = cells[(r, c)]
        outer = [l for l in range(L) if l not in Q]
        sym = {l: 3 * s[k] + t[k] for k, l in enumerate(outer)}
        for T in itertools.combinations(Q, d):
            for xs in itertools.product(range(9), repeat=d):
                lf = [9] * L
                for l in outer: lf[l] = sym[l]
                for p, x in zip(T, xs): lf[p] = x
                yield T, xs, tuple(lf)
    def movable(w, T, xs, p, x):
        if stretch: return movable_stretch(w, T, xs, p, x)
        r, c, s, t = w; Q = cells[(r, c)]
        outer = [l for l in range(L) if l not in Q]
        below = [l for l in outer if l < p]
        if not below: return False
        l = below[-1]
        if any(l < q < p for q in T): return False
        rk = outer.index(l)
        if rk < z0: return False
        dl = t[rk] - s[rk]; dx = x % 3 - x // 3
        if control != "drop_e" and dx != dl: return False   # (e) for adjacent moves: same key iff j_p - i_p = d_l
        if control == "drop_d": return True                 # control: skip (d)
        Q2 = tuple(sorted(set(Q) - {p} | {l}))
        if Q2 not in where: return False
        r2, c2 = where[Q2]
        return c2 - r2 == c - r
    def movable_stretch(w, T, xs, p, x):
        """Stretch moves (Lemma 3.3): p lowest in its gap, p' any outer level above the previous inner level and below
        p, with rank >= z0, Q - p + p' on the same diagonal, and the moved member in the same key fibre."""
        r, c, s, t = w; Q = cells[(r, c)]
        outer = [l for l in range(L) if l not in Q]
        below = [l for l in outer if l < p]
        if not below or any(below[-1] < q < p for q in T): return False
        prevQ = max([q for q in Q if q < below[-1]] + [-1])
        sym = {l: (s[k], t[k]) for k, l in enumerate(outer)}
        sym[p] = (x // 3, x % 3)
        for q, xx in zip(T, xs): sym[q] = (xx // 3, xx % 3)
        Fl = sorted(outer + list(T))
        def member(Tset):
            Q2 = tuple(sorted(set(Q) - set(T) | set(Tset)))
            if Q2 not in where: return None
            rest = [l for l in Fl if l not in Tset]
            s2 = tuple(sym[l][0] for l in rest); t2 = tuple(sym[l][1] for l in rest)
            return where[Q2], s2, t2
        k0 = fkey(r, c, s, t)
        for pp in [l for l in outer if prevQ < l < p and outer.index(l) >= z0]:
            m = member(set(T) - {p} | {pp})
            if m is None: continue
            (r2, c2), s2, t2 = m
            if c2 - r2 == c - r and fkey(r2, c2, s2, t2) == k0: return True
        return False
    need = set(); bound = 0; gf_ok = True
    for w in W:
        cnt = 0
        for T, xs, lf in leaves_of(w):
            need.add(lf)
            if not any(movable(w, T, xs, p, x) for p, x in zip(T, xs)): cnt += 1
        bound += cnt
        # generating-function form, exact coefficient
        r, c, s, t = w; Q = cells[(r, c)]
        outer = [l for l in range(L) if l not in Q]
        poly = [Fraction(1)]
        Qs_sorted = sorted(Q); gaps = []
        for q in Qs_sorted:
            if gaps and not any(gaps[-1][-1] < l < q for l in outer): gaps[-1].append(q)
            else: gaps.append([q])
        for G in gaps:
            PG = [Fraction(0)] * (len(G) + 1); PG[0] = Fraction(1)
            for idx, p in enumerate(G):
                # weight of 'p lowest in T cap G' = 9 b_p, upper elements free (9 each)
                bp = Fraction(sum(1 for x in range(9) if not movable(w, (p,), (x,), p, x)), 9)
                above = len(G) - idx - 1
                for e in range(above + 1):
                    from math import comb
                    PG[1 + e] += 9 * bp * comb(above, e) * 9 ** e
            new = [Fraction(0)] * (len(poly) + len(PG) - 1)
            for i, a in enumerate(poly):
                for j, b in enumerate(PG): new[i + j] += a * b
            poly = new
        gf = poly[d] if d < len(poly) else 0
        if gf != cnt and not stretch: gf_ok = False
    return len(W), len(need), bound, gf_ok

if __name__ == "__main__":
    ok = True
    print("Lemma 2.1: |Leaves_d(W)| <= sum_w R_d(w); Lemma 2.2: R_d(w) = [z^d] prod_G P_G(z) (adjacent moves)")
    for (L, mu, z0, K0) in [(6, 2, 1, 3), (7, 3, 1, 5)]:
        for d in (1, 2):
            for gm in ("segments", "random"):
                for seed in range(2):
                    nW, nl, bd, g = run(L, mu, z0, K0, gm, d, 6, seed)
                    good = nl <= bd and g
                    ok &= good
                    print(f"  L={L} mu={mu} z0={z0} K0={K0} d={d} {gm:8s} seed {seed}: |W|={nW} leaves={nl} "
                          f"bound={bd} trivial={nW * (mu if d == 1 else mu*(mu-1)//2) * 9**d} gf={'ok' if g else 'MISMATCH'} {'OK' if good else 'FAIL'}")
    print("stretch moves (Lemma 3.3): leaves <= stretch bound <= adjacent bound")
    for (L, mu, z0, K0) in [(6, 2, 1, 3), (7, 3, 1, 5)]:
        for d in (1, 2):
            for seed in range(2):
                nW, nl, bd, g = run(L, mu, z0, K0, "segments", d, 6, seed, stretch=True)
                nW2, nl2, bd2, g2 = run(L, mu, z0, K0, "segments", d, 6, seed)
                good = nl <= bd <= bd2; ok &= good
                print(f"  L={L} mu={mu} K0={K0} d={d} seed {seed}: leaves={nl} stretch bound={bd} adjacent bound={bd2} {'OK' if good else 'FAIL'}")
    print("segment grids whose whole classes sit on diagonals, so moves are used (bound < trivial asserted)")
    MOVE_CASES = [(6, 2, 0, 3, 3), (6, 3, 1, 4, 3), (6, 3, 0, 4, 3), (7, 3, 1, 5, 3)]
    for (L, mu, z0, K0, sl) in MOVE_CASES:
        for d in (1, 2):
            nW, nl, bd, g = run(L, mu, z0, K0, "segments", d, 10, 0, seglen=sl)
            nWs, nls, bds, gs = run(L, mu, z0, K0, "segments", d, 10, 0, stretch=True, seglen=sl)
            triv = nW * (mu if d == 1 else mu * (mu - 1) // 2) * 9 ** d
            good = g and nl <= bd < triv and nls == nl and nl <= bds <= bd
            ok &= good
            print(f"  L={L} mu={mu} z0={z0} K0={K0} seglen={sl} d={d}: |W|={nW} leaves={nl} adjacent bound={bd} "
                  f"stretch bound={bds} trivial={triv} moves used={bd < triv} {'OK' if good else 'FAIL'}")
    print("negative controls on the move-exercising segment grids (each must violate in at least one run)")
    for control in ("drop_d", "drop_e"):
        failed = False
        for (L, mu, z0, K0, sl) in MOVE_CASES:
            for seed in range(2):
                nW, nl, bd, g = run(L, mu, z0, K0, "segments", 1, 10, seed, control, seglen=sl)
                if nl > bd: failed = True
                print(f"  control {control} L={L} mu={mu} z0={z0} seed {seed}: leaves={nl} bound={bd} "
                      f"{'violated' if nl > bd else 'holds'}")
        ok &= failed
        print(f"  control {control} on segment grids violated somewhere: {failed}")
    print("negative controls on random grids (each must violate in at least one run)")
    for control in ("drop_d", "nonfibre", "drop_e"):
        failed = False
        for seed in range(6):
            nW, nl, bd, g = run(7, 3, 1, 5, "random", 1, 6, seed, control)
            if nl > bd: failed = True
            print(f"  control {control} seed {seed}: leaves={nl} bound={bd} {'violated' if nl > bd else 'holds'}")
        ok &= failed
    assert ok, "a check failed or a control did not fail"
    print("ALL OK")
