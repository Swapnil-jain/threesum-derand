"""Tests for Theorem C'', the per-element window moves of Lemma Y with mixed segment lengths (proofs/bands.md, Sec. 10).

- bands4_cert.py is run once; its claimed lines must appear, all four must-fail controls must fail (the diagonal-fit
  control by that condition alone), the no-sharing control must give Theorem 1's saving, and its output must equal
  the saved bands4_cert.out. It refuses python -O.
- bands4_poly.py is run once; its output must equal the saved bands4_poly.json (about 3 minutes).
- check_bands_y.py is run on its case 0; the printed line must equal the first line of the saved check_bands_y.out.
- An independent construction of the polynomials A_Y and A_ZY: for every subset, digit string, element, term and
  target, the moved member's segment string is built (outer levels minus the target plus p, with digit t at p) and its
  integer value is compared with w's; no window formula is used. Every entry must equal bands4_poly.json.
- An independent recomputation of the two certified savings in double precision from those polynomials.
"""
import itertools, json, math, pathlib, subprocess, sys, unittest
from fractions import Fraction as Fr
from math import comb

import numpy as np

CERTS = pathlib.Path(__file__).resolve().parents[1] / "certificates"
_cache = {}


def run(script, *args, flags=()):
    key = (script, args, flags)
    if key not in _cache:
        r = subprocess.run([sys.executable, *flags, str(CERTS / script), *args], capture_output=True, text=True,
                           cwd=CERTS)
        if not flags and script != "bands4_poly.py":
            sys.stdout.write(f"\n--- {script} {' '.join(args)} ---\n{r.stdout}")
            if r.returncode != 0:
                sys.stdout.write(r.stderr)
        _cache[key] = r
    return _cache[key]


class Claims(unittest.TestCase):
    def test_certificate(self):
        r = run("bands4_cert.py")
        self.assertEqual(r.returncode, 0, r.stderr)
        out = r.stdout
        for line in ("(C) Lemma Y, segment lengths 8 and 9 (7/10, 3/10): CERTIFIED",
                     "sigma >= 0.0042181468   3SUM exponent <= 1.995781854   e_pre <= 0.400985",
                     "(C) Lemma Y, segment length 8: CERTIFIED",
                     "sigma >= 0.0042165295   3SUM exponent <= 1.995783471   e_pre <= 0.406309",
                     "class fits a diagonal: ln(class)/mu <= 1.979195 vs ln(K0)/mu >= 2.010567",
                     "sigma >= 0.0039992840, in (0.0039992, 0.0039994): OK",
                     "Both Lemma Y points beat Theorem C' tier (C): OK",
                     "over Theorem 1 (sigma <= 0.003999289714): x1.0547",
                     "over the paper's deterministic 3SUM (eps'/2 = 0.000875): x4.820",
                     "deterministic 3SUM <= n^(1.995781854+o(1)) = O(n^1.995782)",
                     "deterministic Convolution-3SUM (linear-time reduction to 3SUM) <= n^(1.995781854+o(1))"
                     " = O(n^1.995782)",
                     "ALL OK"):
            self.assertIn(line, out)
        self.assertEqual(out.count(": FAILED"), 4)
        self.assertEqual(out.count("(negative control: it must FAIL) OK"), 4)
        self.assertNotIn("WRONG", out)
        block = out.split("class too big for a diagonal (must FAIL): FAILED")[1].split("\n(")[0]
        self.assertEqual([l.strip() for l in block.splitlines() if "failed:" in l], ["failed: class fits a diagonal"])

    def test_saved_output(self):
        self.assertEqual(run("bands4_cert.py").stdout, (CERTS / "bands4_cert.out").read_text())

    def test_refuses_optimised_mode(self):
        for script in ("bands4_cert.py", "bands4_poly.py", "check_bands_y.py"):
            with self.subTest(script=script):
                r = run(script, flags=("-O",))
                self.assertNotEqual(r.returncode, 0)
                self.assertIn("refusing to run under python -O", r.stderr)

    def test_polynomials_reproduce(self):
        r = run("bands4_poly.py")
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("ALL OK", r.stderr)
        self.assertEqual(json.loads(r.stdout), json.loads((CERTS / "bands4_poly.json").read_text()))

    def test_toy_case0(self):
        r = run("check_bands_y.py", "0")
        self.assertEqual(r.returncode, 0, r.stderr)
        first = (CERTS / "check_bands_y.out").read_text().splitlines()[0]
        self.assertEqual(r.stdout.splitlines()[0], first)
        self.assertIn("GF mismatches=0", first)
        self.assertEqual(first.count("fails as required"), 3)


PIN = np.array([1, 2, 3, 2, 1], dtype=np.int64)     # 9 pi(d), d = -2..2


def built_poly(lam, n, law):
    """A_Y (law "Y") or A_ZY (law "ZY") by building every moved member's segment string."""
    if n == 0:
        return [Fr(1)]
    K = lam - n
    D = (np.array(list(itertools.product(range(-2, 3), repeat=K)), dtype=np.int64) if K
         else np.zeros((1, 0), dtype=np.int64))
    wt = np.prod(PIN[D + 2], axis=1) if K else np.ones(1, dtype=np.int64)
    val = D @ (3 ** np.arange(K, dtype=np.int64)) if K else np.zeros(1, dtype=np.int64)
    tot = [Fr(0)] * (n + 1)
    for S in itertools.combinations(range(lam), n):
        O = [l for l in range(lam) if l not in S]
        cols = []
        for p in S:
            below = [i for i, o in enumerate(O) if o < p]
            if law == "ZY":
                cols.append(np.full(D.shape[0], 8 if below else 9, dtype=np.int64))
                continue
            keeps = np.zeros((D.shape[0], 5), dtype=bool)
            for a in below:
                outer2 = sorted([o for o in O if o != O[a]] + [p])
                for ti, t in enumerate(range(-2, 3)):
                    nv = np.zeros(D.shape[0], dtype=np.int64)
                    for r, o in enumerate(outer2):
                        nv = nv + (t if o == p else D[:, O.index(o)]) * 3 ** r
                    keeps[:, ti] |= nv == val
            cols.append(((~keeps) * PIN[None, :]).sum(axis=1))
        M = np.stack(cols, axis=1)
        groups = {}
        for row, w in zip(map(tuple, M.tolist()), wt.tolist()):
            groups[row] = groups.get(row, 0) + w
        for row, w in groups.items():
            cf = [Fr(1)]
            for b9 in row:
                cf = [(cf[k] if k < len(cf) else 0) + (Fr(b9, 9) * cf[k - 1] if k else 0) for k in range(len(cf) + 1)]
            for k in range(n + 1):
                tot[k] += Fr(w, 9 ** K) * cf[k]
    return [x / comb(lam, n) for x in tot]


_POLY = {}


def polys():
    if not _POLY:
        for lam in (8, 9):
            for n in range(lam + 1):
                for law in ("Y", "ZY"):
                    _POLY[f"{law},{lam},{n}"] = built_poly(lam, n, law)
    return _POLY


def sigma_float(c, th, eps, z, pattern):
    c, th, eps, zf = (float(Fr(v)) for v in (c, th, eps, z))
    H = lambda x: -x * math.log(x) - (1 - x) * math.log(1 - x)
    P = polys()
    ev = lambda cf, y: sum(float(a) * y ** k for k, a in enumerate(cf))
    zeta = (math.log(2) / math.log(3)) / (c - 1)
    Lbar = sum(l * float(Fr(w)) for l, w in pattern.items())
    SA = SC = 0.0
    for l, w in pattern.items():
        w = float(Fr(w)); pm = [comb(l, k) * (1 / c) ** k * (1 - 1 / c) ** (l - k) for k in range(l + 1)]
        SA += w * sum(pm[k] * ((1 - zeta) * math.log(ev(P[f"Y,{l},{k}"], 9 * zf))
                               + zeta * math.log(ev(P[f"ZY,{l},{k}"], 9 * zf))) for k in range(l + 1))
        SC += w * sum(pm[k] * math.log(comb(l, k)) for k in range(l + 1))
    L4 = math.log(4)
    q_eff = (-th * math.log(zf) + (c / Lbar) * SA) / L4
    q_fill = ((c / Lbar) * SC - (c / 2) * H(1 / c) + H(th) + th * math.log(9)) / L4
    g = (c * H(1 / c) - c * H((1 - th) / c) - th * math.log(9)) / L4
    E = ((c / 2) * H(1 / c) + (c - 1) * math.log(3)) / L4
    return min(eps * g, eps * (0.5 - max(q_eff, q_fill)), 1 - eps * E)


class Independent(unittest.TestCase):
    def test_polynomials(self):
        saved = {k: [Fr(x) for x in v] for k, v in json.loads((CERTS / "bands4_poly.json").read_text()).items()}
        mine = polys()
        self.assertEqual(set(saved), set(mine))
        for k in sorted(saved):
            with self.subTest(entry=k):
                self.assertEqual(mine[k], saved[k])

    def test_savings(self):
        cases = [  # point, pattern, certified lower bound printed by bands4_cert.py
            (("4203319/200000", "3679/31250", "115032221/2000000000", "190589/10000000"), {8: "7/10", 9: "3/10"},
             0.0042181468),
            (("21018799/1000000", "1176831/10000000", "143775683/2500000000", "190173/10000000"), {8: "1"},
             0.0042165295),
        ]
        for point, pattern, certified in cases:
            with self.subTest(pattern=pattern):
                s = sigma_float(*point, pattern)
                self.assertLessEqual(certified, s)
                self.assertLess(s - certified, 1e-9)


if __name__ == "__main__":
    unittest.main()
