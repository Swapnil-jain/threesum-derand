"""Certificate for Theorem A' (folded residue instances; proofs/stacked.md) and its k-Clique corollary.

The folded route changes only the Exact Triangle instances of Theorem 1 (Lemma 3.2 of proofs/derandomisation.md),
so its saving is that of Theorem 1's all-edges Exact Triangle route,
    sigma = min(eps*gamma, eps*(1/2 - q))                         (boxes, queries),
under the Theorem O hypothesis of the folded instances, eps*(E + gamma - 1/4) < 1 (it was eps*(E + gamma) < 1), and
the side conditions 2 + eps < 3 - sigma (writing the instances) and sigma < eps/2 (per-slot sums). Then deterministic
all-edges Exact Triangle, (min,+) and APSP run in n^{3 - sigma + o(1)}. Both oracle tiers are certified ("paper
lemmas": gamma_rho, E_full; "exact count + pruned encoding": gamma_exact, E_pruned).
Corollaries (proofs/stacked.md, Sec. 3): Zero-, Min- and Max-Weight k-Clique in n^{k - floor(k/3) sigma + o(1)} by the
paper's Nesetril-Poljak folding; and Convolution-3SUM through Exact Triangle on n^{1/2} vertices, 2 - sigma/2, which is
printed only to show that it is worse than the direct reduction to 3SUM.
The points are fixed exact rationals (found by a float optimiser, then eps taken just below the arb lower bound of
1/(E - 1/4 + gamma)); the optimiser is not part of the certificate. Controls: without the fold the same formula at
Theorem 1's point gives back Theorem 1's saving; at the folded points eps*E > 1, so the unfolded Lemma 3.2 does not
apply there; and eps 1% above the bound must FAIL. Printing uses directed rounding: savings DOWN, exponents UP.
Usage: python stacked_cert.py
"""
import sys as _sys
# The final verdict uses assert, which python -O strips; refuse to run there rather than pass silently.
if not __debug__:
    _sys.exit("refusing to run under python -O: the certificate's checks are assert statements")
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from flint import arb
from certify import A, gamma, q, E, bmin, down, up, o_exp, exact

TIERS = {"exact": ("exact", "pruned", "exact count + pruned encoding (after ImprovedExponents secs. 3-4)"),
         "paper": ("rho", "full", "paper lemmas")}
# name, tier, c, theta, eps, folded?, expected verdict
POINTS = [
    ("folded", "exact", "2105675159/100000000", "11196129/100000000", "72821473/1250000000", True, True),
    ("folded", "paper", "220136043/10000000", "5613801/50000000", "54758043/1000000000", True, True),
    ("control: unfolded, at Theorem 1's point (must give Theorem 1's saving)", "exact", "2127327/100000",
     "111731/1000000", "568461449/10000000000", False, True),
    ("control: folded, eps 1% too large (must FAIL)", "exact", "2105675159/100000000", "11196129/100000000",
     "73549687730/1250000000000", True, False),
]


def cert(name, tier, c, th, eps, folded):
    bk, ek, tname = TIERS[tier]
    side = {"c>10": Fr(c) > 10, "0<theta<0.9": 0 < Fr(th) < Fr(9, 10), "eps>0": Fr(eps) > 0}
    C, TH, EPS = A(c), A(th), A(eps)
    g, qq, e = gamma(C, TH, bk), q(TH), E(C, ek)
    t1, t2 = EPS * g, EPS * (A("1/2") - qq)
    s = bmin(t1, t2)
    shift = A("1/4") if folded else A(0)
    cond = "eps(E+gamma-1/4) < 1" if folded else "eps(E+gamma) < 1"
    side.update({"terms > 0": t1 > 0 and t2 > 0, cond: EPS * (e - shift + g) < 1,
                 "building 2+eps < 3-sigma": 2 + EPS < 3 - s, "bookkeeping sigma < eps/2": s < EPS / 2})
    ok = all(bool(v) for v in side.values())
    print(f"{name}, {tname}: {'CERTIFIED' if ok else 'FAILED'}  sigma >= {down(s, 12)}")
    print(f"   certified point (exact rationals): c = {c}, theta = {th}, eps = {eps}")
    for k, v in side.items():
        if not v:
            print("   failed:", k)
    if folded:
        # eps*E > 1 means 1 - eps*E < 0: the unfolded instances (encoding term 1 - eps*E) are not available here.
        print(f"   unfolded encoding term 1 - eps*E <= {up(1 - EPS * e, 6)} (negative: only the folded Lemma 3.2' applies)")
    print(f"   deterministic all-edges Exact Triangle, (min,+), APSP <= n^({up(3 - s)}+o(1)) = O(n^{o_exp(3 - s, 6)})")
    return ok, s


def corollaries(s, tier):
    s_lo = exact(s.lower())
    s6 = Fr(int(s_lo * 10**6), 10**6)                 # the saving rounded DOWN to 6 dp, strictly below sigma
    assert s6 < s_lo
    print(f"   deterministic Zero/Min/Max-Weight k-Clique: O(n^(k - {float(s6):.6f} floor(k/3))) for every k >= 3")
    for k in range(3, 13):
        print(f"     k = {k:2d}: <= n^({up(k - (k // 3) * s, 6)}+o(1)) = O(n^{o_exp(k - (k // 3) * s, 6)})")
    direct = "1.995790 (Theorem 3)" if tier == "exact" else "1.996291 (Theorem 1, paper lemmas)"
    print(f"   Convolution-3SUM through Exact Triangle on n^(1/2) vertices: 2 - sigma/2 <= {up(A(2) - s / 2, 6)}, "
          f"worse than the direct reduction to 3SUM, {direct}")


def theorem1_sigma():
    """Theorem 1's saving at its certified point (derand_cert.py, exact count + pruned encoding), as a ball."""
    c, th, eps = A("2127327/100000"), A("111731/1000000"), A("5684608/100000000")
    return bmin(eps * gamma(c, th, "exact"), eps * (A("1/2") - q(th)), 1 - eps * E(c, "pruned"))


if __name__ == "__main__":
    verdicts, sig = [], {}
    for name, tier, c, th, eps, folded, expect in POINTS:
        ok, s = cert(name, tier, c, th, eps, folded)
        if not expect:
            print("   (negative control: it must FAIL)", "OK" if not ok else "WRONG")
        verdicts.append(ok == expect)
        if name == "folded":
            sig[tier] = s
            print("Corollaries at this point:")
            corollaries(s, tier)
    s_best = arb(sig["exact"].lower())
    s1 = theorem1_sigma()
    print("Comparisons, exact count + pruned encoding, ratios rounded DOWN (our lower bound over the other's upper end):")
    print(f"   APSP over Theorem 1 (sigma <= {up(s1, 12)}): x{down(s_best / arb(s1.upper()), 4)}")
    print(f"   APSP over the paper's deterministic APSP (eps'/3 = 0.00175/3): x{down(s_best / (A('0.00175') / 3), 3)}")
    print(f"   Exact Triangle over the paper's deterministic Exact Triangle (eps' = 0.00175): "
          f"x{down(s_best / A('0.00175'), 3)}")
    assert all(verdicts), "a point did not give its expected verdict"
    print("ALL OK")
