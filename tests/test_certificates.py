"""Runs every certificate once and checks the values it prints against the claims of README.md (the band-gain scripts
of Theorem 3 are in test_bands.py).

Each script is run as a subprocess with the same interpreter, its output is echoed, and the claimed lines must appear
verbatim. A script that prints FAILED anywhere, or exits non-zero, fails the test.
"""
import pathlib, subprocess, sys, unittest

CERTS = pathlib.Path(__file__).resolve().parents[1] / "certificates"
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
        self.assertNotIn("FAILED", r.stdout)
        self.check_lines(script, *lines)

    def check_lines(self, script, *lines):
        r = run(script)
        self.assertEqual(r.returncode, 0, r.stderr)
        for line in lines:
            self.assertIn(line, r.stdout)

    def test_folded_route(self):
        # Theorem A' (proofs/stacked.md). The one FAILED line is the control with eps 1% too large.
        r = run("stacked_cert.py")
        self.assertEqual(r.returncode, 0, r.stderr)
        for line in ("folded, exact count + pruned encoding (after ImprovedExponents secs. 3-4): CERTIFIED  sigma >= 0.004057248470",
                     "certified point (exact rationals): c = 2105675159/100000000, theta = 11196129/100000000, eps = 72821473/1250000000",
                     "deterministic all-edges Exact Triangle, (min,+), APSP <= n^(2.995942752+o(1)) = O(n^2.995943)",
                     "folded, paper lemmas: CERTIFIED  sigma >= 0.003760515625",
                     "deterministic all-edges Exact Triangle, (min,+), APSP <= n^(2.996239485+o(1)) = O(n^2.996240)",
                     "unfolded encoding term 1 - eps*E <= -0.010507",
                     "control: unfolded, at Theorem 1's point (must give Theorem 1's saving), exact count + pruned encoding (after ImprovedExponents secs. 3-4): CERTIFIED  sigma >= 0.003999294279",
                     "failed: eps(E+gamma-1/4) < 1",
                     "(negative control: it must FAIL) OK",
                     "APSP over Theorem 1 (sigma <= 0.003999289714): x1.0144",
                     "APSP over the paper's deterministic APSP (eps'/3 = 0.00175/3): x6.955",
                     "Exact Triangle over the paper's deterministic Exact Triangle (eps' = 0.00175): x2.318",
                     "ALL OK"):
            self.assertIn(line, r.stdout)
        self.assertEqual(r.stdout.count(": FAILED"), 1)
        self.assertNotIn("WRONG", r.stdout)

    def test_kclique_corollary(self):
        self.check_lines("stacked_cert.py",
                         "deterministic Zero/Min/Max-Weight k-Clique: O(n^(k - 0.004057 floor(k/3))) for every k >= 3",
                         "k =  6: <= n^(5.991886+o(1)) = O(n^5.991886)",
                         "k =  9: <= n^(8.987829+o(1)) = O(n^8.987829)",
                         "k = 12: <= n^(11.983772+o(1)) = O(n^11.983772)",
                         "deterministic Zero/Min/Max-Weight k-Clique: O(n^(k - 0.003760 floor(k/3))) for every k >= 3",
                         "Convolution-3SUM through Exact Triangle on n^(1/2) vertices: 2 - sigma/2 <= 1.997972, worse than "
                         "the direct reduction to 3SUM, 1.995790 (Theorem 3)")

    def test_folded_mechanical(self):
        self.check("check_stacked.py",
                   "Lemma 3.2' folded instance: 24746 slots checked, mismatches 0",
                   "negative controls (must be > 0): no x*M0 shift 4478, wrong sign of y 16697")

    def test_folded_saved_outputs_and_guards(self):
        for script in ("stacked_cert.py", "check_stacked.py"):
            with self.subTest(script=script):
                self.assertEqual(run(script).stdout, (CERTS / script.replace(".py", ".out")).read_text())
                r = run(script, "-O")
                self.assertNotEqual(r.returncode, 0)
                self.assertIn("refusing to run under python -O", r.stderr)

    def test_derandomised_route(self):
        self.check("derand_cert.py",
                   "exact count + pruned encoding (after ImprovedExponents secs. 3-4): CERTIFIED  sigma >= 0.003999289713",
                   "certified point (exact rationals): c = 2127327/100000, theta = 111731/1000000, eps = 5684608/100000000",
                   "deterministic 3SUM <= n^(1.996000711+o(1)) = O(n^1.996001)",
                   "deterministic all-edges Exact Triangle, (min,+), APSP <= n^(2.996000711+o(1)) = O(n^2.996001)",
                   "paper lemmas: CERTIFIED  sigma >= 0.003709895012",
                   "certified point (exact rationals): c = 2221832/100000, theta = 112064/1000000, eps = 5351255/100000000",
                   "deterministic 3SUM <= n^(1.996290105+o(1)) = O(n^1.996291)")

    def test_corollaries(self):
        self.check("derand_cert.py",
                   "deterministic Convolution-3SUM <= n^(1.996001+o(1)) = O(n^1.996001)",
                   "deterministic Zero/Min/Max-Weight 6-Clique <= n^(5.992002+o(1))",
                   "deterministic Zero/Min/Max-Weight 9-Clique <= n^(8.988003+o(1))")
        self.check("certify_L1.py",
                   "deterministic Convolution-3SUM <= n^(1.996323+o(1)) = O(n^1.99633)",
                   "deterministic (min,+)-convolution <= n^(1.998162+o(1)) = O(n^1.99817)")

    def test_derand_mechanical(self):
        self.check("check_derand.py",
                   "3SUM: instances 300, yes 147 mismatches 0",
                   "all-edges ET: instances 120, positive pairs 163 mismatches 0",
                   "Lemma 4.1 exhaustive v,t<70, tau<150 mismatches 0",
                   "(min,+) via all-edges ET: instances 150, mismatches 0")

    def test_derand_stress(self):
        # The stress run asserts the halving lemmas on every chain (Lemma 2.5: |S_l minus Z| <= |S_{l-1}|/4;
        # Lemma 3.5: |S'_l| <= |S'_{l-1}|/2, S'_L empty, no zero-free slot in T). A violated assertion makes the
        # script exit non-zero, which check() rejects; the source check guards against the asserts being removed.
        self.check("check_derand.py",
                   "stress 3SUM (primes in [20,200), U=1e5, inputs multiples of 667): instances 120, yes 78 mismatches 0",
                   "stress all-edges ET: instances 60, positive pairs 119 mismatches 0")
        src = (CERTS / "check_derand.py").read_text()
        self.assertIn("assert viol == 0          # Lemma 2.5 on every chain", src)
        self.assertIn("assert viol == 0 and zf == 0 and not Sp   # Lemma 3.5 on every chain, S'_L empty, Lemma 3.6", src)

    def test_derand_controls_fail(self):
        # Each control replaces one ingredient of the proof by a wrong one; the run must show the failure.
        self.check("check_derand_controls.py",
                   "control 4.1 without v+t=tau-1: 900 mismatches",
                   "survivors nonempty in 33 of 40",
                   "control bad primes (3SUM stress): 373 halving violations, 30 wrong answers of 120")

    def test_l1_route(self):
        self.check("certify_L1.py",
                   "exact count + pruned encoding (after ImprovedExponents secs. 3-4): CERTIFIED  S >= 0.003677999",
                   "deterministic 3SUM <= n^(1.996322001+o(1)) = O(n^1.99633)",
                   "deterministic all-edges ET, (min,+), APSP <= n^(2.996322001+o(1)) = O(n^2.99633)",
                   "paper lemmas: CERTIFIED  S >= 0.003431999",
                   "deterministic 3SUM <= n^(1.996568001+o(1)) = O(n^1.99657)",
                   "deterministic all-edges ET, (min,+), APSP <= n^(2.996568001+o(1)) = O(n^2.99657)")

    def test_las_vegas_route(self):
        self.check("certify_levers.py",
                   "route A, exact count + pruned encoding (after ImprovedExponents secs. 3-4): CERTIFIED sigma(1/2) >= 0.003999291",
                   "<= n^(2.996000709+o(1)) = O(n^2.99601)",
                   "s_ET >= 0.002095234  APSP <= 2.997904766")

    def test_paper_route(self):
        self.check("certify.py",
                   "paper_point: CERTIFIED  boxes=rho enc=full  s_ET >= 0.001777777  3SUM <= 1.999111112",
                   "exact_count_free_density_pruned_encoding: CERTIFIED  boxes=exact enc=pruned  s_ET >= 0.002095234  3SUM <= 1.998952383")

    def test_negative_to_exact_triangle(self):
        self.check("check_negtri.py",
                   "dyadic identity, all v, t < 2^7, tau in [-4, 260]: mismatches 0",
                   "full reduction, fixed shift tau = 2h - w_ab: 33227 instances, mismatches 0",
                   "OK: fixed reduction exact on every instance; old shift rejected")


if __name__ == "__main__":
    unittest.main()
