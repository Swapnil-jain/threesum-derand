# Corrections

Corrections from an independent re-review of the proofs and certificates. None of them changes a theorem, an
exponent (3SUM 1.995782, all-edges Exact Triangle, (min,+) and APSP 2.995943, k-Clique) or a Lean statement.

## 2026-10-11

- **`stacked_cert.py`, a stale figure (found by Romain Hedouin).** Its Convolution-3SUM line compared against the
  version 2 exponent 1.995790 instead of the current 1.995782 (Theorem 3). The script, `stacked_cert.out` and
  `tests/test_certificates.py` now print 1.995782. Only the printed comparison changes; the certified sigma does not.
- **`check_bands_y.py`, faster (contributed by Romain Hedouin).** The six cases now take about 1 minute of CPU instead
  of about 20 minutes: the leaf data is computed once for the four modes, the targets are memoised, and the cases
  run in parallel. The checks and the three must-fail controls are unchanged.

## 2026-10-10

- **`bands_cert.py`, the b = 1 control.** It was described as "b = 1 gives Theorem A's saving", but the script only
  certified the point and never compared the value with anything, so it could not fail. It now checks that
  A(lam, n; y, 1) = (1 + y)^n exactly, and that Theorem A's formula at the same (c, theta, eps) exceeds the b = 1
  saving by between 0 and 1e-10 (the gap is at most 5e-15, from the rounding of z). `bands_cert.out` gains one line;
  every other printed value is unchanged. `proofs/bands.md` Sec. 0 says so.
- **`check_bands_buckets.py`.** Two of its checks were weaker than described. "The chosen F(p) is at most the mean"
  holds by definition for the minimising prime, so it tests nothing; the bound of Lemma 6.2 on the mean is not tested.
  And the progression instances are cut to n elements, so in 28 of the 40 of them some window prime has no heavy
  residue: they do not force heavy residues for every prime. The proof does not use either check. The script's
  comments and the table in `proofs/bands.md` Sec. 8 now say this; its output is unchanged.
- **`check_derand_controls.py`, the second control (the plain count N as the all-edges potential).** Every pair that
  survives it has an exact zero, because under N a zero slot never leaves. So it shows that N keeps the positive
  pairs, not that the halving fails. The third control (bad primes) runs on 3SUM only, at one size.
  `proofs/derandomisation.md` Sec. 5 now says so; the output is unchanged.
- **`proofs/l1.md` Sec. 6.** It said `certify_L1.py` "encodes every term". The ds^2 term (n^3 d^3 / D^2, saving
  2 eps - 3 delta) is not encoded. It is implied by the same-block term (saving eps - 2 delta), because delta <= eps
  is a checked side condition, as the table in that section already notes. The saving S = 0.003677999 is unchanged.
