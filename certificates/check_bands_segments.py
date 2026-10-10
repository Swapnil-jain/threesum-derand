"""Mechanical check of Lemma 4.1 of proofs/bands.md: over one signature class, the average of prod_G P_G with the
true gaps of Q (which may cross segment boundaries) equals prod_s A(lam, n_s; y, b), the product of per-segment
averages in which a run at a segment's first level gets no move. Exact fractions; standard library only.
A move of p to the outer level just below its gap is available iff that level exists and lies in p's segment.
Negative control: letting cross-boundary gaps move must break the equality. Usage: python check_bands_segments.py
"""
import sys as _sys
# These checks rely on assert and on the exit status, and python -O strips asserts; refuse to run there.
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assert statements")
import itertools, sys
from fractions import Fraction as F
from math import comb
def gaps_of(Q, L):
    out = []
    for q in sorted(Q):
        if out and out[-1][-1] == q - 1: out[-1].append(q)
        else: out.append([q])
    return out
def true_prod(Q, L, lam, y, b, control=False):
    pr = F(1)
    for G in gaps_of(Q, L):
        l = G[0] - 1                      # outer level just below the gap (or -1: none)
        PG = F(1)
        for idx, p in enumerate(G):
            ok = l >= 0 and (control or l // lam == p // lam)
            PG += y * (b if ok else 1) * (1 + y) ** (len(G) - idx - 1)
        pr *= PG
    return pr
def A(lam, n, y, b):
    tot = F(0)
    for S in itertools.combinations(range(lam), n):
        pr = F(1)
        for G in gaps_of(S, lam):
            k = len(G)
            pr *= (1 + b * ((1 + y) ** k - 1)) if G[0] != 0 else (1 + y) ** k
        tot += pr
    return tot / comb(lam, n)
if __name__ == "__main__":
    ok = True; ctrl = False
    for (L, lam, mu) in [(8, 4, 3), (12, 4, 4), (12, 3, 5), (10, 5, 4)]:
        y = F(2, 7); b = F(2, 3)
        segs = L // lam
        classes = {}
        for Q in itertools.combinations(range(L), mu):
            classes.setdefault(tuple(sum(1 for q in Q if q // lam == s) for s in range(segs)), []).append(Q)
        for sig, Qs in classes.items():
            avg = sum(true_prod(Q, L, lam, y, b) for Q in Qs) / len(Qs)
            pred = F(1)
            for n in sig: pred *= A(lam, n, y, b)
            ok &= avg == pred
            ctrl |= sum(true_prod(Q, L, lam, y, b, True) for Q in Qs) / len(Qs) != pred
        print(f"L={L} lam={lam} mu={mu}: {len(classes)} classes, equality {'holds' if ok else 'FAILS'}")
    print("control differs somewhere:", ctrl)
    ok &= ctrl
    assert ok, "a check failed or the control did not fail"
    print("ALL OK")
