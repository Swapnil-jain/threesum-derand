"""Certificate for the derandomised route (proofs/derandomisation.md).

The route solves 3SUM and all-edges Exact Triangle through thin products at density a = 1/2 with no halving, so the
saving is that of one thin product,
    sigma = min(eps*gamma, eps*(1/2 - q), 1 - eps*E)          (boxes, queries, encodings),
and deterministic 3SUM runs in n^{2 - sigma + o(1)}, deterministic all-edges Exact Triangle in n^{3 - sigma + o(1)}.
c and theta are rational, as the exact count needs. Side conditions (all on the whole arb ball): c > 10, 0 < theta < 0.9, eps > 0, every term positive, encodings strictly
cheaper than boxes (eps < R_c(gamma), the paper's Cor. tradeoff), dense instance building 1 + eps < 2 - sigma, and the
per-slot bookkeeping sigma < eps/2.
The points are fixed exact rationals (found by a float optimiser, then eps lowered by a factor 1 - 1e-6 so the strict
conditions hold with room); the optimiser is not part of the certificate. Printing uses directed rounding from the exact arb endpoints: savings DOWN, exponents UP.
Usage: python derand_cert.py
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from certify import A, gamma, q, E, bmin, down, up, o_exp

# Theorem A of proofs/derandomisation.md is stated for rational c and theta (the exact-count tier needs m to be a
# multiple of their denominators), so the certified points are hard-coded exact rationals, never floats.
POINTS = [
    # name, c, theta, eps, box count, encoding
    ("exact count + pruned encoding (after ImprovedExponents secs. 3-4)",
     "2127327/100000", "111731/1000000", "5684608/100000000", "exact", "pruned"),
    ("paper lemmas", "2221832/100000", "112064/1000000", "5351255/100000000", "rho", "full"),
    ("paper point (21, 1/9, 1/18), paper lemmas", "21", "1/9", "1/18", "rho", "full"),
]


def cert(name, c, th, eps, bk, ek):
    side = {"c>10": Fr(c) > 10, "0<theta<0.9": 0 < Fr(th) < Fr(9, 10), "eps>0": Fr(eps) > 0}
    c_q, th_q, eps_q = c, th, eps
    c, th, eps = A(c), A(th), A(eps)
    t1, t2, t3 = eps*gamma(c, th, bk), eps*(A("1/2")-q(th)), 1-eps*E(c, ek)
    s = bmin(t1, t2, t3)
    side.update({"terms > 0": t1 > 0 and t2 > 0 and t3 > 0, "encodings < boxes (eps < R_c)": t3 > t1,
                 "building 1+eps < 2-sigma": 1 + eps < 2 - s, "bookkeeping sigma < eps/2": s < eps/2})
    ok = all(bool(v) for v in side.values())
    print(f"{name}: {'CERTIFIED' if ok else 'FAILED'}  sigma >= {down(s, 12)}")
    print(f"   certified point (exact rationals): c = {c_q}, theta = {th_q}, eps = {eps_q}")
    for k, v in side.items():
        if not v: print("   failed:", k)
    print(f"   deterministic 3SUM <= n^({up(2-s)}+o(1)) = O(n^{o_exp(2-s, 6)})")
    print(f"   deterministic all-edges Exact Triangle, (min,+), APSP <= n^({up(3-s)}+o(1)) = O(n^{o_exp(3-s, 6)})")
    return ok, s


def corollaries(s):
    """Corollaries of the best saving (README, Corollaries): Convolution-3SUM by the linear reduction to 3SUM, and
    Zero/Min/Max-Weight k-Clique by the paper's Nesetril-Poljak folding to Exact Triangle on n^{floor(k/3)} vertices."""
    print(f"   deterministic Convolution-3SUM <= n^({up(2-s, 6)}+o(1)) = O(n^{o_exp(2-s, 6)})")
    for k in range(3, 10):
        print(f"   deterministic Zero/Min/Max-Weight {k}-Clique <= n^({up(k - s*(k//3), 6)}+o(1))"
              f" = O(n^{o_exp(k - s*(k//3), 6)})")


if __name__ == "__main__":
    res = [cert(*p) for p in POINTS]
    assert all(ok for ok, _ in res)
    print("Corollaries (exact count + pruned encoding):")
    corollaries(res[0][1])
