"""Tests for Theorem C', the zone moves of Rule Z (proofs/bands.md, Sec. 9).

- bands3_cert.py is run once; its claimed lines must appear, both must-fail controls must fail, both reduction
  controls must reproduce bands_cert.py, and its output must equal the saved bands3_cert.out. It refuses python -O.
- An independent recomputation of the three certified savings (the dynamic program of test_bands.py for every
  segment average, zone averages included, and double precision for the exponents).
- An independent toy check of Lemma Z. Leaves are built directly as (Z, terms on F) and their union is counted as a
  set. Inner sets are packed by signature class onto integer diagonals of the grid, in random order, and W is a union
  of random key fibres. Rule Z is applied in every segment, which is stronger than the zone-only use. Every Rule-Z
  target must be a member of the same leaf with the same row and column strings, a lexicographically smaller set,
  and must lie in W; R_d(w) must equal the coefficient of the 8/9 generating function for every w; and |Leaves_d| <=
  sum_w R_d(w). Must-fail control: one class split across the two pieces of a wrapped diagonal sends Rule-Z targets
  outside W, so the integer-diagonal packing of Sec. 4 is what makes the lemma hold. About 80 seconds.
"""
import itertools, math, pathlib, random, subprocess, sys, unittest
from collections import defaultdict
from fractions import Fraction as Fr
from math import comb

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from test_bands import seg_average_dp  # noqa: E402  (the segment-average dynamic program, shared)

CERTS = pathlib.Path(__file__).resolve().parents[1] / "certificates"
SCRIPT = "bands3_cert.py"
_cache = {}


def run(*flags):
    if flags not in _cache:
        r = subprocess.run([sys.executable, *flags, str(CERTS / SCRIPT)], capture_output=True, text=True, cwd=CERTS)
        if not flags:
            sys.stdout.write(f"\n--- {SCRIPT} ---\n{r.stdout}")
            if r.returncode != 0:
                sys.stdout.write(r.stderr)
        _cache[flags] = r
    return _cache[flags]


class Claims(unittest.TestCase):
    def test_certificate(self):
        r = run()
        self.assertEqual(r.returncode, 0, r.stderr)
        out = r.stdout
        for line in ("(C) shifted keys, stretch moves, zone moves: CERTIFIED  sigma >= 0.0042143770",
                     "deterministic 3SUM <= n^(1.995785623+o(1)) = O(n^1.995786)",
                     "(S) shifted keys, adjacent moves, zone moves: CERTIFIED  sigma >= 0.0041917719",
                     "deterministic 3SUM <= n^(1.995808229+o(1)) = O(n^1.995809)",
                     "(W) worst keys, adjacent moves, zone moves: CERTIFIED  sigma >= 0.0041463659",
                     "deterministic 3SUM <= n^(1.995853635+o(1)) = O(n^1.995854)",
                     "layout precomputation: e9 <= 0.239490  eK <= 0.166758  e_pre <= 0.406248",
                     "bands_cert.py prints 0.0042108435: OK",
                     "bands_cert.py prints 0.0039992877: OK",
                     "over Theorem 1 (sigma <= 0.003999289714): x1.0537",
                     "over the paper's deterministic 3SUM (eps'/2 = 0.000875): x4.816",
                     "deterministic Convolution-3SUM (linear-time reduction to 3SUM) <= n^(1.995785623+o(1))"
                     " = O(n^1.995786)",
                     "ALL OK"):
            self.assertIn(line, out)
        self.assertEqual(out.count(": FAILED"), 2)
        self.assertEqual(out.count("(negative control: it must FAIL) OK"), 2)
        self.assertNotIn("WRONG", out)
        self.assertIn("failed: eps(E+gamma) < 1", out)
        self.assertIn("failed: 0<z<=1", out)

    def test_saved_output(self):
        self.assertEqual(run().stdout, (CERTS / "bands3_cert.out").read_text())

    def test_refuses_optimised_mode(self):
        r = run("-O")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("refusing to run under python -O", r.stderr)


def sigma_float_zone(c, th, eps, z, law, zone=Fr(8, 9), lam=8):
    c, th, eps, zf = (float(Fr(v)) for v in (c, th, eps, z))
    law = law if law == "stretch" else Fr(law)
    H = lambda x: -x * math.log(x) - (1 - x) * math.log(1 - x)
    p = 1 / c
    pmf = [comb(lam, k) * p ** k * (1 - p) ** (lam - k) for k in range(lam + 1)]
    y = 9 * Fr(z)
    e_lnA = sum(pmf[k] * math.log(seg_average_dp(lam, k, y, law)) for k in range(lam + 1))
    e_lnZ = sum(pmf[k] * math.log(seg_average_dp(lam, k, y, zone)) for k in range(lam + 1))
    e_lnC = sum(pmf[k] * math.log(comb(lam, k)) for k in range(lam + 1))
    zeta = (math.log(2) / math.log(3)) / (c - 1)
    L4 = math.log(4)
    q_eff = (-th * math.log(zf) + (c / lam) * ((1 - zeta) * e_lnA + zeta * e_lnZ)) / L4
    q_fill = ((c / lam) * e_lnC - (c / 2) * H(1 / c) + H(th) + th * math.log(9)) / L4
    g = (c * H(1 / c) - c * H((1 - th) / c) - th * math.log(9)) / L4
    E = ((c / 2) * H(1 / c) + (c - 1) * math.log(3)) / L4
    return min(eps * g, eps * (0.5 - max(q_eff, q_fill)), 1 - eps * E)


class Independent(unittest.TestCase):
    def test_savings(self):
        cases = [  # point, certified lower bound printed by bands3_cert.py
            (("10514903/500000", "58807/500000", "574807987/10000000000", "23671/1250000", "stretch"), 0.0042143770),
            (("5262491/250000", "58501/500000", "574279737/10000000000", "91849/5000000", "62/81"), 0.0041917719),
            (("5274867/250000", "57881/500000", "572980907/10000000000", "172629/10000000", "22/27"), 0.0041463659),
        ]
        for point, certified in cases:
            with self.subTest(law=point[-1]):
                s = sigma_float_zone(*point)
                self.assertLessEqual(certified, s)
                self.assertLess(s - certified, 1e-9)

    def test_zone_law_one_is_theorem_c(self):
        # With zone law 1 the formula is Theorem C's: Corollary D's (C) saving comes back.
        s = sigma_float_zone("1052341/50000", "1836/15625", "28717589/500000000", "94241/5000000", "stretch", Fr(1))
        self.assertLessEqual(0.0042108435, s)
        self.assertLess(s - 0.0042108435, 1e-9)


# ---------- toy check of Lemma Z ----------
def zone_toy(L, mu, lam, z0, d, K0, seed, split=False):
    """One toy instance: L levels, inner sets of size mu, segments of lam levels, a zone of z0 ranks, order d, a
    K0 x K0 grid. With split=True the largest class is put on a wrapped diagonal instead (the control)."""
    rng = random.Random(seed)
    seg = lambda l: l // lam
    sets = list(itertools.combinations(range(L), mu))
    cls = defaultdict(list)
    for Q in sets:
        cls[tuple(sum(1 for q in Q if seg(q) == s) for s in range(L // lam))].append(Q)
    # place each class whole on one integer diagonal (cells (r, r + delta)), in random order along it
    cell = {}
    free = {dl: [(r, r + dl) for r in range(K0) if 0 <= r + dl < K0] for dl in range(-K0 + 1, K0)}
    for ci, C in enumerate(sorted(cls.values(), key=len, reverse=True)):
        C = C[:]
        rng.shuffle(C)
        if split and ci == 0:   # control: the class goes on a WRAPPED diagonal, across both of its pieces
            dl = 1
            cand = [(r, (r + dl) % K0) for r in range(K0)]
            cand = [x for x in cand if x not in cell.values()]
            if len(cand) < len(C):
                return None
            for Q, rc in zip(C, cand[-len(C):]):
                cell[Q] = rc
            continue
        for dl in sorted(free, key=lambda t: (abs(t) <= 1 and split, abs(t))):
            av = [x for x in free[dl] if x not in cell.values()]
            if len(av) >= len(C):
                rng.shuffle(av)
                for Q, rc in zip(C, av):
                    cell[Q] = rc
                break
        else:
            raise AssertionError("packing failed")
    no = L - mu
    npr = no - z0

    def key(Q, rs, cs):
        r, c = cell[Q]
        j = r * 3 ** npr + sum(rs[t] * 3 ** (t - z0) for t in range(z0, no))
        k = c * 3 ** npr + sum(cs[t] * 3 ** (t - z0) for t in range(z0, no))
        return (k - j, rs[:z0], cs[:z0])
    strings = list(itertools.product(range(3), repeat=no))
    keys = {key(Q, rs, cs) for Q in cell for rs in strings for cs in strings}
    Wk = {kk for kk in keys if rng.random() < 0.5}
    W = {(Q, rs, cs) for Q in cell for rs in strings for cs in strings if key(Q, rs, cs) in Wk}

    def leaf(w, T, terms):        # a leaf is (Z, the terms on F as a sorted tuple level -> (i, j))
        Q, rs, cs = w
        out = [l for l in range(L) if l not in Q]
        f = {l: (rs[t], cs[t]) for t, l in enumerate(out)}
        for p, tm in zip(T, terms):
            f[p] = tm
        return (tuple(q for q in Q if q not in T), tuple(sorted(f.items())))

    def member(lf, Tp):
        Z, f = lf
        f = dict(f)
        Q = tuple(sorted(Z + tuple(Tp)))
        if Q not in cell:
            return None
        out = [l for l in range(L) if l not in Q]
        return (Q, tuple(f[l][0] for l in out), tuple(f[l][1] for l in out))
    leaves = set()
    sumR = outside = notmember = gf_bad = 0
    T9 = list(itertools.product(range(3), repeat=2))
    for w in W:
        Q, rs, cs = w
        out = [l for l in range(L) if l not in Q]
        dig = {l: (rs[t], cs[t]) for t, l in enumerate(out)}
        Rw = 0
        for T in itertools.combinations(Q, d):
            for terms in itertools.product(T9, repeat=d):
                lf = leaf(w, T, terms)
                leaves.add(lf)
                assert member(lf, T) == w
                movable = False
                for idx, p in enumerate(T):
                    lo = p
                    while lo - 1 in Q:
                        lo -= 1                                   # the gap G of p starts at lo
                    if any(lo <= t < p for t in T):
                        continue                                  # p is not the lowest element of T in G
                    lg = lo - 1
                    if lg < 0 or seg(lg) != seg(p):
                        continue                                  # l_G must be in p's segment
                    if terms[idx] != dig[lg]:
                        continue                                  # Rule Z: the term equals w's digit pair at l_G
                    Tp = tuple(sorted(set(T) - {p} | {lg}))
                    w2 = member(lf, Tp)
                    if w2 is None:
                        notmember += 1
                        continue
                    if w2 not in W:
                        outside += 1
                    assert w2[1] == rs and w2[2] == cs            # the strings are unchanged
                    assert Tp < T                                 # and the set is lexicographically smaller
                    movable = True
                if not movable:
                    Rw += 1
        # generating function: per gap 1 + (8/9)((1 + 9z)^|G| - 1) if l_G is in the same segment, else (1 + 9z)^|G|;
        # the part of a gap above a segment boundary never moves (its target would leave the class)
        poly = [1]
        runs = []
        for q in sorted(Q):
            if runs and runs[-1][-1] == q - 1:
                runs[-1].append(q)
            else:
                runs.append([q])
        for G in runs:
            g0 = [q for q in G if seg(q) == seg(G[0])]
            can = G[0] - 1 >= 0 and seg(G[0] - 1) == seg(G[0])
            P = [0] * (len(G) + 1)
            P[0] = 1
            for pi, p in enumerate(G):
                above = len(G) - pi - 1
                blocked = 8 if (can and p in g0) else 9           # blocked terms out of 9
                for a in range(above + 1):
                    P[1 + a] += blocked * comb(above, a) * 9 ** a
            new = [0] * (len(poly) + len(P) - 1)
            for x, u in enumerate(poly):
                for y, v in enumerate(P):
                    new[x + y] += u * v
            poly = new
        if Rw != poly[d]:
            gf_bad += 1
        sumR += Rw
    return dict(W=len(W), leaves=len(leaves), sumR=sumR, outside=outside, notmember=notmember, gfbad=gf_bad)


class ZoneToy(unittest.TestCase):
    def test_lemma_z(self):
        for (L, mu, lam, z0, d, K0, seed) in [(6, 2, 3, 1, 1, 10, 1), (6, 2, 3, 1, 1, 10, 2), (7, 3, 7, 2, 1, 40, 3),
                                              (6, 2, 6, 0, 2, 16, 3)]:
            with self.subTest(case=(L, mu, lam, z0, d, K0, seed)):
                r = zone_toy(L, mu, lam, z0, d, K0, seed)
                sys.stdout.write(f"\nzone toy {(L, mu, lam, z0, d, K0, seed)}: {r}")
                self.assertEqual(r["outside"], 0)
                self.assertEqual(r["gfbad"], 0)
                self.assertLessEqual(r["leaves"], r["sumR"])

    def test_wrapped_diagonal_control(self):
        r = zone_toy(6, 2, 3, 1, 1, 12, 1, split=True)
        sys.stdout.write(f"\nzone toy control, wrapped-diagonal split: {r}\n")
        self.assertIsNotNone(r)
        self.assertGreater(r["outside"], 0)   # must fail: targets leave W


if __name__ == "__main__":
    unittest.main()
