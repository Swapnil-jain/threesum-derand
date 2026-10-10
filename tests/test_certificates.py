"""Runs every certificate once and checks the values it prints against the claims of README.md.

Each script is run as a subprocess with the same interpreter, its output is echoed, and the claimed lines must appear
verbatim. A script that prints FAILED anywhere, or exits non-zero, fails the test.
"""
import pathlib, subprocess, sys, unittest

CERTS = pathlib.Path(__file__).resolve().parents[1] / "certificates"
_cache = {}


def run(script):
    if script not in _cache:
        r = subprocess.run([sys.executable, str(CERTS / script)], capture_output=True, text=True, cwd=CERTS)
        sys.stdout.write(f"\n--- {script} ---\n{r.stdout}")
        if r.returncode != 0:
            sys.stdout.write(r.stderr)
        _cache[script] = r
    return _cache[script]


class Claims(unittest.TestCase):
    def check(self, script, *lines):
        r = run(script)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertNotIn("FAILED", r.stdout)
        for line in lines:
            self.assertIn(line, r.stdout)

    def test_derandomised_route(self):
        self.check("derand_cert.py",
                   "exact count + pruned encodings: CERTIFIED  sigma >= 0.003999289713",
                   "deterministic 3SUM <= n^(1.996000711+o(1)) = O(n^1.996001)",
                   "deterministic all-edges Exact Triangle, (min,+), APSP <= n^(2.996000711+o(1)) = O(n^2.996001)",
                   "paper lemmas only: CERTIFIED  sigma >= 0.003709895012",
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
        self.check("check_derand_controls.py",
                   "control 4.1 without v+t=tau-1: 900 mismatches",
                   "survivors nonempty in 33 of 40")

    def test_l1_route(self):
        self.check("certify_L1.py",
                   "exact count + pruned encodings: CERTIFIED  S >= 0.003677999",
                   "deterministic 3SUM <= n^(1.996322001+o(1)) = O(n^1.99633)",
                   "deterministic all-edges ET, (min,+), APSP <= n^(2.996322001+o(1)) = O(n^2.99633)",
                   "paper lemmas only: CERTIFIED  S >= 0.003431999",
                   "deterministic 3SUM <= n^(1.996568001+o(1)) = O(n^1.99657)",
                   "deterministic all-edges ET, (min,+), APSP <= n^(2.996568001+o(1)) = O(n^2.99657)")

    def test_las_vegas_route(self):
        self.check("certify_levers.py",
                   "route A, exact count + pruned encodings: CERTIFIED sigma(1/2) >= 0.003999291",
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
