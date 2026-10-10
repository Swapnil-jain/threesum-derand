"""Certificate for Theorem C', the zone-move improvement of Theorem 3 (proofs/bands.md, Sec. 9).

Theorem C' is Theorem C with Rule Z in the zone segments: a zone gap blocks with law 8/9 for every key (Lemma Z)
instead of 1. The only change to the exponents is the zone term of q_eff:
  q_eff = [-th ln z + (c/lam) E_{n_s} ((1 - zeta) ln A(lam, n_s; 9z, b) + zeta ln A(lam, n_s; 9z, 8/9))]/ln 4,
with A, b, gamma, E, q_fill, sigma and every side condition exactly as in bands_cert.py, whose cert() does the work
(zone = 8/9). With zone law 1, A(lam, n; y, 1) = (1 + y)^n and E n_s = lam/c, so the zone term is Theorem C's
zeta ln(1 + 9z); two controls check that reduction numerically, at Theorem 1's control point and at tier (C) of
Corollary D. Two further controls must FAIL. Printing uses directed rounding from the exact arb endpoints: savings
DOWN, exponents UP. Usage: python bands3_cert.py
"""
import sys as _sys
# The final verdict uses assert, which python -O strips; refuse to run there rather than pass silently.
if not __debug__:
    _sys.exit("refusing to run under python -O: the certificate's checks are assert statements")
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from flint import arb
from certify import A, down, up, o_exp
from bands_cert import cert, theorem1_sigma

ZONE = "8/9"   # Lemma Z: exactly one of the nine terms is zone-movable, for every key

# name, c, theta, eps, z, blocking law, zone law (None: Theorem C, no zone moves), expected verdict.
# The (C), (S), (W) points were found by a float optimiser, which is not part of the certificate.
POINTS = [
    ("(C) shifted keys, stretch moves, zone moves", "10514903/500000", "58807/500000", "574807987/10000000000",
     "23671/1250000", "stretch", ZONE, True),
    ("(S) shifted keys, adjacent moves, zone moves", "5262491/250000", "58501/500000", "574279737/10000000000",
     "91849/5000000", "62/81", ZONE, True),
    ("(W) worst keys, adjacent moves, zone moves", "5274867/250000", "57881/500000", "572980907/10000000000",
     "172629/10000000", "22/27", ZONE, True),
    ("control zone law 1 at Corollary D's (C) point (must give 0.0042108435)", "1052341/50000", "1836/15625",
     "28717589/500000000", "94241/5000000", "stretch", "1", True),
    ("control b = 1, zone law 1 (must give Theorem 1's saving)", "1063663/50000", "111731/1000000",
     "14211513/250000000", "139761/10000000", "1", "1", True),
    ("control eps 1% too large (must FAIL)", "10514903/500000", "58807/500000", "145139/2500000", "23671/1250000",
     "stretch", ZONE, False),
    ("control z = 2 (must FAIL)", "10514903/500000", "58807/500000", "574807987/10000000000", "2", "stretch", ZONE,
     False),
]

# Each reduction control must reproduce the saving bands_cert.py prints for the same point, to ten digits.
REDUCTION = {POINTS[3][0]: "0.0042108435", POINTS[4][0]: "0.0039992877"}

if __name__ == "__main__":
    verdicts, sig = [], {}
    for name, c, th, eps, z, law, zone, expect in POINTS:
        ok, s = cert(name, c, th, eps, z, law, zone)
        if not expect:
            print("   (negative control: it must FAIL)", "OK" if not ok else "WRONG")
        verdicts.append(ok == expect)
        sig[name] = s
    for name, printed in REDUCTION.items():
        same = down(sig[name], 10) == printed
        print(f"{name}: sigma >= {down(sig[name], 10)}, bands_cert.py prints {printed}:", "OK" if same else "WRONG")
        verdicts.append(same)
    s_best = arb(sig[POINTS[0][0]].lower())                     # tier (C): its certified lower end
    s_c = sig[POINTS[3][0]]
    s1 = theorem1_sigma()
    print("Comparisons, tier (C), ratios rounded DOWN (our lower bound over the other saving's upper end):")
    print(f"   over Theorem C (sigma <= {up(s_c, 12)}): x{down(s_best / arb(s_c.upper()), 5)}")
    print(f"   over Theorem 1 (sigma <= {up(s1, 12)}): x{down(s_best / arb(s1.upper()), 4)}")
    print(f"   over the paper's deterministic 3SUM (eps'/2 = 0.000875): x{down(s_best / A('0.000875'), 3)}")
    print(f"   deterministic Convolution-3SUM (linear-time reduction to 3SUM) <= n^({up(2 - s_best)}+o(1))"
          f" = O(n^{o_exp(2 - s_best, 6)})")
    assert all(verdicts), "a point did not give its expected verdict"
    print("ALL OK")
