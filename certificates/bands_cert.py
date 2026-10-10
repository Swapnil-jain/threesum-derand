"""Certificate for Theorem 3, the band (leaf-sharing) gain for deterministic 3SUM (proofs/bands.md).

The route is Theorem 1's 3SUM route with each thin product evaluated by the paper's pruned recursion, charged by the
canonical-representative bound of proofs/bands.md. Exponents (natural logs, D = 4^mu = n^eps, lam = 8 levels per
segment, n_s ~ Bin(lam, 1/c), zeta = log_3(2)/(c - 1), z in (0, 1] a free parameter of the bound):
  gamma  = [c H(1/c) - c H((1-th)/c) - th ln 9]/ln 4                     exact leaf count (boxes)
  E      = [(c/2) H(1/c) + (c-1) ln 3]/ln 4                               pruned encodings
  q_eff  = [-th ln z + zeta ln(1 + 9z) + (1 - zeta)(c/lam) E ln A(lam, n_s; 9z, b)]/ln 4      shared queries
  q_fill = [(c/lam) E ln C(lam, n_s) - (c/2) H(1/c) + H(th) + th ln 9]/ln 4                     filler cells
  sigma  = min(eps gamma, eps (1/2 - q*), 1 - eps E),   q* = max(q_eff, q_fill)
A(lam, n; y, b) is the average, over the n-subsets S of a segment of lam levels, of the product over the runs G of S of
(1 + y)^|G| if G starts at the segment's first level and 1 + b_G ((1 + y)^|G| - 1) otherwise; it is computed exactly
in rationals. b_G is the blocking law of the tier: 22/27 (worst keys, Lemma 3.1), 62/81 (shifted keys, Lemma 3.2), or
b(len_G) for stretch moves (Lemma 3.3, len_G = outer levels between G and the previous inner level of the segment).
Side conditions (proofs/bands.md, Sec. 5 and 7), each checked on the whole arb ball, rationals exactly:
  c > 10, 0 < theta < 9/10, eps > 0, 0 < z <= 1; gamma > 0; the three terms positive; eps (E + gamma) < 1;
  q* < 1/2; q_fill < q_eff; sigma < eps/2; 1 + eps < 2 - sigma; eps (E + q(theta) - 1/2) + sigma < 1 (partial band
  rows); e_pre < 2 - sigma (the input-independent layout, e_pre = eps c (ln 9/lam + H(1/c))/ln 4).
The points are fixed exact rationals (found by a float optimiser, which is not part of the certificate). Two controls
must FAIL, and b = 1 (no sharing) must give back Theorem 1's saving: it is compared with Theorem 1's formula at the
same point, up to the rounding of z. Printing uses directed rounding from the exact
arb endpoints: savings DOWN, exponents UP. Usage: python bands_cert.py
"""
import sys as _sys
# The final verdict uses assert, which python -O strips; refuse to run there rather than pass silently.
if not __debug__:
    _sys.exit("refusing to run under python -O: the certificate's checks are assert statements")
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as Fr
from itertools import combinations
from math import comb
from flint import arb
from certify import A, gamma, q, E, bmin, down, up, o_exp, L4, L9, H

LAM = 8
# Blocking law of stretch moves (Lemma 3.3): b(len) for a stretch of len outer levels, exact for len <= 5
# (check_bands_stretch.py enumerates them); b is nonincreasing in len, so b(5) bounds every longer stretch.
B_STRETCH = [Fr(1), Fr(62, 81), Fr(538, 729), Fr(4834, 6561), Fr(43498, 59049), Fr(391474, 531441)]

# name, c, theta, eps, z, blocking law, expected verdict
POINTS = [
    ("(C) shifted keys, stretch moves", "1052341/50000", "1836/15625", "28717589/500000000", "94241/5000000",
     "stretch", True),
    ("(S) shifted keys, adjacent moves", "65833/3125", "23379/200000", "28691779/500000000", "36571/2000000",
     "62/81", True),
    ("(W) worst keys, adjacent moves", "2111519/100000", "115663/1000000", "28628097/500000000", "17187/1000000",
     "22/27", True),
    ("control b = 1, no sharing (must give Theorem 1's saving)", "1063663/50000", "111731/1000000",
     "14211513/250000000", "139761/10000000", "1", True),
    ("control eps 1% too large (must FAIL)", "1052341/50000", "1836/15625", "2900476489/50000000000",
     "94241/5000000", "stretch", False),
    ("control z = 2 (must FAIL)", "1052341/50000", "1836/15625", "28717589/500000000", "2", "stretch", False),
]


def seg_average(lam, n, y, law):
    """A(lam, n; y, b): exact rational average over the n-subsets of [lam] (Lemma 4.1)."""
    total = Fr(0)
    for S in combinations(range(lam), n):
        prod, i = Fr(1), 0
        while i < n:
            j = i
            while j + 1 < n and S[j + 1] == S[j] + 1:
                j += 1
            size = j - i + 1
            if S[i] == 0:                       # a run at the segment's first level has no move inside the segment
                prod *= (1 + y) ** size
            else:
                if law == "stretch":
                    stretch = S[i] - (S[i - 1] + 1 if i > 0 else 0)
                    b = B_STRETCH[min(stretch, 5)]
                else:
                    b = law
                prod *= 1 + b * ((1 + y) ** size - 1)
            i = j + 1
        total += prod
    return total / comb(lam, n)


def cert(name, c, th, eps, z, law, zone=None):
    """Certify one point and print its claims. zone=None is Theorem C (no moves in zone segments, zone term
    zeta ln(1 + 9z)). zone = 8/9 is Theorem C' (Rule Z, proofs/bands.md Sec. 9): the zone segments contribute
    zeta (c/lam) E ln A(lam, n_s; 9z, 8/9) instead. bands3_cert.py uses the second form."""
    fc, fth, feps, fz = Fr(c), Fr(th), Fr(eps), Fr(z)
    law = law if law == "stretch" else Fr(law)
    side = {"c>10": fc > 10, "0<theta<9/10": 0 < fth < Fr(9, 10), "eps>0": feps > 0, "0<z<=1": 0 < fz <= 1}
    C, TH, EPS, Z = A(c), A(th), A(eps), A(z)
    y, p = 9 * fz, 1 / fc
    pmf = [comb(LAM, k) * p ** k * (1 - p) ** (LAM - k) for k in range(LAM + 1)]          # exact rationals
    e_lnA = sum(A(pmf[k]) * A(seg_average(LAM, k, y, law)).log() for k in range(LAM + 1))
    e_lnC = sum(A(pmf[k]) * arb(comb(LAM, k)).log() for k in range(LAM + 1))
    zeta = (arb(2).log() / arb(3).log()) / (C - 1)
    if zone is None:
        zone_term = zeta * A(1 + y).log()
    else:
        zone_term = zeta * (C / LAM) * sum(A(pmf[k]) * A(seg_average(LAM, k, y, Fr(zone))).log()
                                           for k in range(LAM + 1))
    q_eff = (-TH * Z.log() + zone_term + (1 - zeta) * (C / LAM) * e_lnA) / L4
    q_fill = (C / LAM * e_lnC - C / 2 * H(1 / C) + H(TH) + TH * L9) / L4
    # q* = max(q_eff, q_fill) as a ball; q_fill < q_eff is itself required below, so this is q_eff when it passes.
    q_star = arb(max(q_eff.lower(), q_fill.lower())).union(arb(max(q_eff.upper(), q_fill.upper())))
    g, e = gamma(C, TH, "exact"), E(C, "pruned")
    t1, t2, t3 = EPS * g, EPS * (A("1/2") - q_star), 1 - EPS * e
    s = bmin(t1, t2, t3)
    e9 = EPS * C * L9 / (LAM * L4)
    eK = EPS * C * H(1 / C) / L4
    side.update({
        "gamma>0": g > 0, "terms > 0": t1 > 0 and t2 > 0 and t3 > 0, "eps(E+gamma) < 1": t3 > t1,
        "q* < 1/2": q_star < A("1/2"), "q_fill < q_eff": q_fill < q_eff,
        "sigma < eps/2": s < EPS / 2, "1+eps < 2-sigma": 1 + EPS < 2 - s,
        "partial band rows: eps(E+q-1/2)+sigma < 1": EPS * (e + q(TH) - A("1/2")) + s < 1,
        "layout: e_pre < 2-sigma": e9 + eK < 2 - s})
    ok = all(bool(v) for v in side.values())
    print(f"{name}: {'CERTIFIED' if ok else 'FAILED'}  sigma >= {down(s, 10)}")
    print(f"   certified point (exact rationals): c = {c}, theta = {th}, eps = {eps}, z = {z}, lam = {LAM}, "
          f"b = {law}" + ("" if zone is None else f", zone b = {zone}"))
    for k, v in side.items():
        if not v:
            print("   failed:", k)
    print(f"   q_eff <= {up(q_eff, 9)}  q_fill <= {up(q_fill, 9)}  gamma >= {down(g, 9)}  E <= {up(e, 6)}")
    print(f"   layout precomputation: e9 <= {up(e9, 6)}  eK <= {up(eK, 6)}  e_pre <= {up(e9 + eK, 6)}")
    print(f"   deterministic 3SUM <= n^({up(2 - s)}+o(1)) = O(n^{o_exp(2 - s, 6)})")
    return ok, s


def theorem1_sigma():
    """Theorem 1's saving at its certified point (derand_cert.py, exact count + pruned encoding), as a ball."""
    c, th, eps = A("2127327/100000"), A("111731/1000000"), A("5684608/100000000")
    return bmin(eps * gamma(c, th, "exact"), eps * (A("1/2") - q(th)), 1 - eps * E(c, "pruned"))


if __name__ == "__main__":
    verdicts, sig = [], {}
    for name, c, th, eps, z, law, expect in POINTS:
        ok, s = cert(name, c, th, eps, z, law)
        if not expect:
            print("   (negative control: it must FAIL)", "OK" if not ok else "WRONG")
        verdicts.append(ok == expect)
        sig[name] = s
    s_best = arb(sig[POINTS[0][0]].lower())                     # tier (C): its certified lower end
    s1 = theorem1_sigma()
    # The b = 1 control is compared with Theorem 1's formula, so that it can fail. At b = 1 every run factor is
    # (1 + y)^|G|, so A(lam, n; y, 1) = (1 + y)^n exactly and q_eff is Theorem 1's -theta ln z + ln(1 + 9z) at this z;
    # Theorem 1 uses the optimal z, so its saving at the same (c, theta, eps) is at least ours and above it only by
    # the rounding of z. Certifying the point alone (CERTIFIED above) did not compare anything.
    _, c0, th0, eps0, z0, _, _ = POINTS[3]
    y0 = 9 * Fr(z0)
    exact_b1 = all(seg_average(LAM, k, y0, Fr(1)) == (1 + y0) ** k for k in range(LAM + 1))
    C0, TH0, EPS0 = A(c0), A(th0), A(eps0)
    s_thm1 = bmin(EPS0 * gamma(C0, TH0, "exact"), EPS0 * (A("1/2") - q(TH0)), 1 - EPS0 * E(C0, "pruned"))
    gap = s_thm1 - sig[POINTS[3][0]]
    b1_ok = exact_b1 and bool(gap > -A("1e-15")) and bool(gap < A("1e-10"))
    print(f"control b = 1 against Theorem 1's formula at the same point: A(lam, n; y, 1) = (1 + y)^n exactly: {exact_b1};"
          f" Theorem 1's saving there minus ours <= {up(gap, 15)} (must lie in [0, 1e-10]): {'OK' if b1_ok else 'WRONG'}")
    verdicts.append(b1_ok)
    print("Comparisons, tier (C), ratios rounded DOWN (our lower bound over the other saving's upper end):")
    print(f"   over Theorem 1 (sigma <= {up(s1, 12)}): x{down(s_best / arb(s1.upper()), 4)}")
    print(f"   over the paper's deterministic 3SUM (eps'/2 = 0.000875): x{down(s_best / A('0.000875'), 3)}")
    print(f"   deterministic Convolution-3SUM (linear-time reduction to 3SUM) <= n^({up(2 - s_best)}+o(1))"
          f" = O(n^{o_exp(2 - s_best, 6)})")
    assert all(verdicts), "a point did not give its expected verdict"
    print("ALL OK")
