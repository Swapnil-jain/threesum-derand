"""Tests for Theorem 3, the band (leaf-sharing) gain (proofs/bands.md).

- Each script of the band gain is run once; its claimed lines must appear, every expected control must fail, and its
  output must equal the saved .out file next to it.
- An independent recomputation of the three certified savings, with other algorithms than bands_cert.py: the segment
  averages A(lambda, n; y, b) by a dynamic program over the levels of a segment (not by enumerating subsets), b(len) by
  a separate enumeration of the stretch condition, and the exponents in double precision. Each certified lower bound
  must lie below the recomputed value and within 1e-9 of it.
- Every script refuses to run under python -O, which would strip its assert statements.
"""
import math, pathlib, subprocess, sys, unittest
from fractions import Fraction as Fr
from functools import lru_cache
from itertools import product
from math import comb

CERTS = pathlib.Path(__file__).resolve().parents[1] / "certificates"
SCRIPTS = ["bands_cert.py", "check_bands_rep.py", "check_bands_carry.py", "check_bands_stretch.py",
           "check_bands_segments.py", "check_bands_buckets.py"]
_cache = {}


def run(script, *flags):
    key = (script, flags)
    if key not in _cache:
        r = subprocess.run([sys.executable, *flags, str(CERTS / script)], capture_output=True, text=True, cwd=CERTS)
        if not flags:
            sys.stdout.write(f"\n--- {script} ---\n{r.stdout}")
            if r.returncode != 0:
                sys.stdout.write(r.stderr)
        _cache[key] = r
    return _cache[key]


class Claims(unittest.TestCase):
    def check(self, script, *lines):
        r = run(script)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("ALL OK", r.stdout)
        for line in lines:
            self.assertIn(line, r.stdout)
        return r.stdout

    def test_certificate(self):
        out = self.check("bands_cert.py",
                         "(C) shifted keys, stretch moves: CERTIFIED  sigma >= 0.0042108435",
                         "deterministic 3SUM <= n^(1.995789157+o(1)) = O(n^1.995790)",
                         "(S) shifted keys, adjacent moves: CERTIFIED  sigma >= 0.0041883974",
                         "deterministic 3SUM <= n^(1.995811603+o(1)) = O(n^1.995812)",
                         "(W) worst keys, adjacent moves: CERTIFIED  sigma >= 0.0041432182",
                         "deterministic 3SUM <= n^(1.995856782+o(1)) = O(n^1.995857)",
                         "control b = 1, no sharing (must give Theorem 1's saving): CERTIFIED  sigma >= 0.0039992877",
                         "layout precomputation: e9 <= 0.239494  eK <= 0.166660  e_pre <= 0.406153",
                         "over Theorem 1 (sigma <= 0.003999289714): x1.0528",
                         "over the paper's deterministic 3SUM (eps'/2 = 0.000875): x4.812",
                         "deterministic Convolution-3SUM (linear-time reduction to 3SUM) <= n^(1.995789157+o(1))"
                         " = O(n^1.995790)")
        # Exactly the two controls fail, each for its own reason, and each is reported as the expected failure.
        self.assertEqual(out.count(": FAILED"), 2)
        self.assertEqual(out.count("(negative control: it must FAIL) OK"), 2)
        self.assertNotIn("WRONG", out)
        self.assertIn("failed: eps(E+gamma) < 1", out)
        self.assertIn("failed: 0<z<=1", out)

    def test_representative_lemma(self):
        out = self.check("check_bands_rep.py",
                         "control drop_d on segment grids violated somewhere: True",
                         "control drop_e on segment grids violated somewhere: True")
        self.assertNotIn("FAIL\n", out)
        self.assertNotIn("MISMATCH", out)
        self.assertEqual(out.count("moves used=True OK"), 8)
        for control in ("drop_d", "nonfibre", "drop_e"):
            self.assertIn(f"control {control} seed", out)

    def test_carry_laws(self):
        self.check("check_bands_carry.py",
                   "control (W with 62/81) fails somewhere: True ; control (fixed worst kappa above average): True")

    def test_stretch_law(self):
        out = self.check("check_bands_stretch.py",
                         "b(len): ['1', '62/81', '538/729', '4834/6561', '43498/59049', '391474/531441']",
                         "control (stretch moves change the count somewhere): True")
        self.assertEqual(out.count("OK; adjacent-only"), 7)

    def test_segments(self):
        out = self.check("check_bands_segments.py", "control differs somewhere: True")
        self.assertEqual(out.count("equality holds"), 4)

    def test_buckets(self):
        self.check("check_bands_buckets.py",
                   "instances 160, yes 124",
                   "answers and solution partition: OK; light buckets <= tau s: True; chosen F(p) <= mean: True; "
                   "shrink inequality: True",
                   "control (drop child 2): 12 instances",
                   "chosen F(p) above the mean at 292 nodes, no-progress nodes (recursion would not terminate) 98")

    def test_saved_outputs(self):
        for script in SCRIPTS:
            with self.subTest(script=script):
                saved = (CERTS / script.replace(".py", ".out")).read_text()
                self.assertEqual(run(script).stdout, saved)

    def test_refuses_optimised_mode(self):
        for script in SCRIPTS:
            with self.subTest(script=script):
                r = run(script, "-O")
                self.assertNotEqual(r.returncode, 0)
                self.assertIn("refusing to run under python -O", r.stderr)


# ---------- independent recomputation ----------
PI = {e: Fr(3 - abs(e), 9) for e in range(-2, 3)}


def b_len_independent(n):
    """P(no stretch position works), stretch digits d_0..d_{n-1} iid pi, inserted difference x ~ pi. Moving to
    position i keeps the key iff sum_{r >= i} d_r 3^r == sum_{i <= r < n-1} d_{r+1} 3^r + x 3^(n-1)."""
    if n == 0:
        return Fr(1)
    blocked = Fr(0)
    for ds in product(range(-2, 3), repeat=n):
        w = math.prod(PI[d] for d in ds)
        for x in range(-2, 3):
            hit = any(sum(ds[r] * 3 ** r for r in range(i, n)) ==
                      sum(ds[r + 1] * 3 ** r for r in range(i, n - 1)) + x * 3 ** (n - 1) for i in range(n))
            if not hit:
                blocked += w * PI[x]
    return blocked


B_LEN = [b_len_independent(n) for n in range(6)]


def seg_average_dp(lam, n, y, law):
    """A(lam, n; y, b) by a left-to-right dynamic program over the levels (state: levels left to choose, start and
    length of the open run, end of the previous run)."""
    def factor(start, size, prev_end):
        if start == 0:
            return (1 + y) ** size
        b = B_LEN[min(start - (prev_end + 1), 5)] if law == "stretch" else law
        return 1 + b * ((1 + y) ** size - 1)

    @lru_cache(None)
    def go(pos, left, start, size, prev_end):
        if pos == lam:
            return Fr(0) if left else (factor(start, size, prev_end) if size else Fr(1))
        total = Fr(0)
        if left:                                       # level pos is in S
            total += go(pos + 1, left - 1, start if size else pos, size + 1, prev_end)
        if size:                                       # level pos is outside S: close the open run
            total += factor(start, size, prev_end) * go(pos + 1, left, -1, 0, start + size - 1)
        else:
            total += go(pos + 1, left, -1, 0, prev_end)
        return total
    return go(0, n, -1, 0, -1) / comb(lam, n)


def sigma_float(c, th, eps, z, law, lam=8):
    c, th, eps, zf = (float(Fr(v)) for v in (c, th, eps, z))
    law = law if law == "stretch" else Fr(law)
    H = lambda x: -x * math.log(x) - (1 - x) * math.log(1 - x)
    p = 1 / c
    pmf = [comb(lam, k) * p ** k * (1 - p) ** (lam - k) for k in range(lam + 1)]
    y = 9 * Fr(z)
    e_lnA = sum(pmf[k] * math.log(seg_average_dp(lam, k, y, law)) for k in range(lam + 1))
    e_lnC = sum(pmf[k] * math.log(comb(lam, k)) for k in range(lam + 1))
    zeta = (math.log(2) / math.log(3)) / (c - 1)
    L4 = math.log(4)
    q_eff = (-th * math.log(zf) + zeta * math.log(1 + 9 * zf) + (1 - zeta) * (c / lam) * e_lnA) / L4
    q_fill = ((c / lam) * e_lnC - (c / 2) * H(1 / c) + H(th) + th * math.log(9)) / L4
    g = (c * H(1 / c) - c * H((1 - th) / c) - th * math.log(9)) / L4
    E = ((c / 2) * H(1 / c) + (c - 1) * math.log(3)) / L4
    return min(eps * g, eps * (0.5 - max(q_eff, q_fill)), 1 - eps * E)


class Independent(unittest.TestCase):
    def test_b_len(self):
        self.assertEqual([str(b) for b in B_LEN], ["1", "62/81", "538/729", "4834/6561", "43498/59049", "391474/531441"])
        self.assertTrue(all(B_LEN[i + 1] <= B_LEN[i] for i in range(5)))

    def test_shifted_law_is_one_minus_collision(self):
        self.assertEqual(sum(PI[e] * Fr(6 + abs(e), 9) for e in PI), Fr(62, 81))

    def test_savings(self):
        cases = [  # point, certified lower bound printed by bands_cert.py
            (("1052341/50000", "1836/15625", "28717589/500000000", "94241/5000000", "stretch"), 0.0042108435),
            (("65833/3125", "23379/200000", "28691779/500000000", "36571/2000000", "62/81"), 0.0041883974),
            (("2111519/100000", "115663/1000000", "28628097/500000000", "17187/1000000", "22/27"), 0.0041432182),
            (("1063663/50000", "111731/1000000", "14211513/250000000", "139761/10000000", "1"), 0.0039992877),
        ]
        for point, certified in cases:
            with self.subTest(law=point[-1]):
                s = sigma_float(*point)
                self.assertLessEqual(certified, s)
                self.assertLess(s - certified, 1e-9)


if __name__ == "__main__":
    unittest.main()
