"""Certificate for the hash-free route L1 (proofs/l1.md): deterministic integer all-edges Exact Triangle, (min,+),
APSP and 3SUM by bit halving + Fredman's trick + Matousek's blocks + Alon-Naor witnesses.

Per halving level the work is (exponents of n; D = n^eps the thin inner dimension, d = n^delta the colour-block size):
  queries      (n/d) sum|P| D^q          -> saving delta - eps*q
  boxes        32 (n/d) d n^2 D^-gamma   -> eps*gamma
  encodings    (n/d) d n D^E             -> 1 - eps*E          (also the tile-fit condition N >= D^E)
  same block   n^2 d s, s = 2nd/D        -> eps - 2*delta      (Matousek same-block pairs)
  inner dim    (n/d) d n D               -> 1 - eps
  bookkeeping  n^3/d (pivot sums, Alon-Naor goodness checks) -> delta
  lists/sort   (n/d) 32 n d^2            -> 1 - delta
3SUM has the same savings relative to 2. The levels (O(log n)) and the Alon-Naor phases (polylog) cost n^{o(1)}.
Side conditions: c > 10, 0 < theta < 0.9, eps > 0, 0 < delta <= eps, eps <= 1 + delta, and the paper's Cor. tradeoff
condition eps*gamma < 1 - eps*E on the whole ball. The ds^2 term (saving 2 eps - 3 delta) is implied by the same-block
term since delta <= eps. Printing: savings DOWN and exponents UP from the exact arb endpoints; the O(n^e) line gives
the 5-digit e strictly above the upper endpoint, which absorbs the n^{o(1)} factor.
Usage: python certify_L1.py
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from certify import A, gamma, q, E, bmin, arb, down, up, o_exp


def cert(name, c, th, eps, de, boxes, enc):
    fc, fth, fe, fd = map(Fr, (c, th, eps, de))
    side = {"c>10": fc > 10, "0<theta<0.9": 0 < fth < Fr(9, 10), "eps>0": fe > 0,
            "0<delta<=eps": 0 < fd <= fe, "eps<=1+delta": fe <= 1 + fd}
    c, th, eps, de = A(c), A(th), A(eps), A(de)
    g, e = gamma(c, th, boxes), E(c, enc)
    side["Cor. tradeoff eps*gamma < 1-eps*E"] = bool(eps*g < 1 - eps*e)
    terms = {"queries": de - eps*q(th), "boxes": eps*g, "encodings": 1 - eps*e,
             "same block": eps - 2*de, "inner dim": 1 - eps, "bookkeeping": de, "lists": 1 - de}
    S = bmin(*terms.values())
    ok = all(side.values()) and all(t > 0 for t in terms.values())
    lo = arb(S.lower())
    print(f"{name}: {'CERTIFIED' if ok else 'FAILED'}  S >= {down(lo)}")
    for k, v in side.items():
        if not v: print("   failed side:", k)
    print(f"   deterministic 3SUM <= n^({up(2-lo)}+o(1)) = O(n^{o_exp(2-lo)})")
    print(f"   deterministic all-edges ET, (min,+), APSP <= n^({up(3-lo)}+o(1)) = O(n^{o_exp(3-lo)})")
    print("   terms: " + "  ".join(f"{k}>={down(v, 7)}" for k, v in terms.items()))
    # Corollaries: Convolution-3SUM by the linear reduction to 3SUM; (min,+)-convolution by BCD14 (sqrt n
    # (min,+) products of sqrt n x sqrt n matrices, so 2 - S/2).
    print(f"   deterministic Convolution-3SUM <= n^({up(2-lo, 6)}+o(1)) = O(n^{o_exp(2-lo)})")
    print(f"   deterministic (min,+)-convolution <= n^({up(2-lo/2, 6)}+o(1)) = O(n^{o_exp(2-lo/2)})")
    return ok


if __name__ == "__main__":
    assert cert("exact count + pruned encoding (after ImprovedExponents secs. 3-4)", "20.276", "0.10457", "0.05961", "0.027966", "exact", "pruned")
    assert cert("paper lemmas", "21.178", "0.10488", "0.05620", "0.026384", "rho", "full")
