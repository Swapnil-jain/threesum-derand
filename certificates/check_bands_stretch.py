"""Mechanical check of Lemma 3.3 of proofs/bands.md (the blocking law of stretch moves). Exact fractions; standard
library only.

One inner set Q of size mu in [L], segments of lam levels, no zone. The row string u and the key kappa are uniform
over [0, 3^n0) (n0 = L - mu), v = (u + kappa) mod 3^n0. A move p -> p' (p the lowest element of T in its gap, p' an
outer level of the stretch below the gap: above the previous inner level and inside p's segment) is available iff the
moved member has the same integer key. R_d counts the (T, terms) with no available move. Asserted, exactly:
  E_{u, kappa} R_d = [z^d] prod_G (1 + b(len_G) ((1 + 9z)^|G| - 1)),  b(0) = 1, b(1) = 62/81, b(2) = 538/729, ...
and the same with adjacent moves only and b = 62/81 for every len >= 1. Control: the two counts must differ somewhere
(stretch moves are really used). Usage: python check_bands_stretch.py
"""
import sys as _sys
# These checks rely on assert and on the exit status, and python -O strips asserts; refuse to run there.
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assert statements")
import itertools, sys
from fractions import Fraction as F
from math import comb
PI = {-2: 1, -1: 2, 0: 3, 1: 2, 2: 1}
def bstretch(n):
    if n == 0: return F(1)
    tot = F(0)
    for ds in itertools.product(range(-2, 3), repeat=n):
        w = 1
        for x in ds: w *= PI[x]
        for x in range(-2, 3):
            t = list(ds) + [x]; tv = sum(c * 3 ** i for i, c in enumerate(ds))
            if all(sum(c * 3 ** i for i, c in enumerate(t[:pp] + t[pp + 1:])) != tv for pp in range(n)):
                tot += w * PI[x]
    return tot / F(9) ** (n + 1)
def run(L, mu, lam, Q, d, adjacent_only=False):
    n0 = L - mu; outer = [l for l in range(L) if l not in Q]
    rank = {l: i for i, l in enumerate(outer)}
    tot = 0
    for u in range(3 ** n0):
        ud = [(u // 3 ** i) % 3 for i in range(n0)]
        for kap in range(3 ** n0):
            v = (u + kap) % 3 ** n0; vd = [(v // 3 ** i) % 3 for i in range(n0)]
            dig = {l: (ud[rank[l]], vd[rank[l]]) for l in outer}
            for T in itertools.combinations(Q, d):
                for xs in itertools.product(range(9), repeat=d):
                    sym = dict(dig); sym.update({p: (x // 3, x % 3) for p, x in zip(T, xs)})
                    F_ = sorted(outer + list(T))
                    def keyof(Tset):
                        rest = [l for l in F_ if l not in Tset]
                        return sum((sym[l][1] - sym[l][0]) * 3 ** i for i, l in enumerate(rest))
                    k0 = keyof(set(T)); blocked = True
                    for p in T:
                        below = [l for l in F_ if l < p]
                        if not below or below[-1] in T: continue        # not lowest in its gap
                        prevQ = max([q for q in Q if q < below[-1]] + [-1])
                        stretch = [l for l in outer if prevQ < l < p and l // lam == p // lam]
                        if adjacent_only: stretch = [l for l in stretch if l == below[-1]]
                        if any(keyof(set(T) - {p} | {pp}) == k0 for pp in stretch): blocked = False; break
                    tot += blocked
    return F(tot, 9 ** n0)
def predict(L, mu, lam, Q, d, B):
    poly = [F(1)]
    S = sorted(Q); gaps = []
    for q in S:
        if gaps and gaps[-1][-1] == q - 1: gaps[-1].append(q)
        else: gaps.append([q])
    for G in gaps:
        g0 = G[0]
        if g0 % lam == 0: ln = 0
        else:
            prevQ = max([q for q in Q if q < g0] + [-1])
            ln = len([l for l in range(max(prevQ + 1, (g0 // lam) * lam), g0)])
        b = B[ln]; k = len(G)
        PG = [F(0)] * (k + 1); PG[0] = 1
        for e in range(1, k + 1): PG[e] += b * comb(k, e) * 9 ** e
        new = [F(0)] * (len(poly) + k)
        for i, a in enumerate(poly):
            for j, c in enumerate(PG): new[i + j] += a * c
        poly = new
    return poly[d] if d < len(poly) else F(0)
if __name__ == "__main__":
    B = [bstretch(n) for n in range(6)]
    print("b(len):", [str(x) for x in B])
    ok = True; ctrl = False
    for (L, mu, lam, Q, d) in [(6, 2, 6, (3, 5), 1), (6, 2, 3, (2, 4), 1), (6, 2, 6, (4, 5), 1), (6, 2, 6, (3, 5), 2),
                               (7, 2, 7, (4, 6), 1), (7, 2, 7, (0, 5), 2), (6, 1, 6, (5,), 1)]:
        got = run(L, mu, lam, Q, d); pred = predict(L, mu, lam, Q, d, B)
        adj = run(L, mu, lam, Q, d, True); padj = predict(L, mu, lam, Q, d, [F(1)] + [F(62, 81)] * 5)
        ok &= got == pred and adj == padj
        ctrl |= got != adj
        print(f"L={L} mu={mu} lam={lam} Q={Q} d={d}: E R_d = {got} predicted {pred} {'OK' if got == pred else 'FAIL'}; "
              f"adjacent-only {adj} predicted {padj} {'OK' if adj == padj else 'FAIL'}")
    print("control (stretch moves change the count somewhere):", ctrl)
    ok &= ctrl
    assert ok, "a check failed or the control did not fail"
    print("ALL OK")
