"""Generate ThreesumLean/Bands4Points.lean: kernel checks of certificates/bands4_cert.py (Theorem C'', tier (C)).

Derived from gen_bands3.py and reusing gen_bands2.py's Tier (casts, proof scripts of the positive theorem and the
controls). The changes are the ones Theorem C'' makes (proofs/bands.md, Sec. 10):
  * the class averages are the exact Lemma Y polynomials A_Y(lam, n; y) and A_ZY(lam, n; y) (Bands4Defs.lean,
    tables copied from certificates/bands4_poly.json; the copy is compared entry by entry before anything is
    written);
  * every per-segment term is the w-weighted mix over the pattern, divided by Lbar, so the bounds lemma sandwiches
    the A_Y and A_ZY values and the binomials for each length in the pattern;
  * the theorems state CertBands4 at the points of bands4_cert.py (POINTS) with bands4_cert.out's claims.
Each point gets the positive theorem and four negative controls (next s0, next exponent, next O-line, perturbed
eps). One more control (CONTROLS) refutes CertBands4 by `class_fits` alone, at a point of bands4_cert.py where a
class does not fit a diagonal but q_fill < q_eff still holds. Every point is first cross-checked against
certificates/bands4_cert.out (parameters, printed saving, exponent and e_pre); any mismatch aborts.
Usage: python gen_bands4.py
"""
import json, os, re, sys
from fractions import Fraction as F
from math import comb
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(os.path.dirname(HERE), "certificates"))
import gen_bands2 as g2
from gen_bands2 import R, LN, L2, L3, L4, L9, H, lit, outward, log_rat_lines, lean_q, floor_dec, ceil_dec, lo_of, hi_of, pmq
import gen
import bands4_cert

CERTS = os.path.join(os.path.dirname(HERE), "certificates")
DEFS = os.path.join(HERE, "ThreesumLean", "Bands4Defs.lean")
LAWS = {"Y": "coefY", "ZY": "coefZY"}

# claims: bands4_cert.out's saving (rounded down) and exponent (rounded up); the O-line is the exponent rounded up to 6 places
POINTS = {
    "C": {"key": bands4_cert.HEADLINE,
          "claims": {"s0": "0.0042181468", "b": "1.995781854", "o": "1.995782"},
          "doc": "Tier (C) with Lemma Y and segment lengths 8 and 9 mixed 7/10 : 3/10. The headline O(n^1.995782)."},
    "C8": {"key": bands4_cert.LENGTH8,
           "claims": {"s0": "0.0042165295", "b": "1.995783471", "o": "1.995784"},
           "doc": "Tier (C) with Lemma Y, every segment of length 8."},
}
# points refuted by `class_fits` alone (bands4_cert.out must list "failed: class fits a diagonal" and no other failure);
# the claims are the headline's, which these points cannot certify
CONTROLS = {
    "Fit9": {"key": "control: length 9, theta = 1/50, class too big for a diagonal (must FAIL)", "claims": POINTS["C"]["claims"],
             "doc": "Every segment of length 9 at th = 1/50: q_fill < q_eff holds, but a class does not fit a diagonal."},
}
# the order of the bounds in b4<point>_num; "cl" and "k0" are the two sides of `class_fits`
QKEYS = ("g", "E", "q", "qe", "qf", "pre", "cl", "k0")


def poly(cf, y):
    v = F(0)
    for a in reversed(cf): v = a + y * v
    return v


def load_tables():
    """bands4_poly.json, and the same tables parsed back out of Bands4Defs.lean; they must agree exactly."""
    J = json.load(open(os.path.join(CERTS, "bands4_poly.json")))
    T = {k: [F(x) for x in v] for k, v in J.items()}
    src = open(DEFS).read()
    for law, nm in (("Y", "tabY"), ("ZY", "tabZY")):
        m = re.search(r"def " + nm + r" : List \(List \(List ℚ\)\) := \[(.*?)\]\]\]", src, re.S)
        body = m.group(1)
        blocks = body.split("],\n    [")
        assert len(blocks) == 2, nm
        for i, lam in enumerate((8, 9)):
            rows = re.findall(r"\[([^\[\]]*)\]", blocks[i] + "]")
            if len(rows) != lam + 1:
                raise SystemExit(f"STOP: {nm} lam={lam} has {len(rows)} rows")
            for n, r in enumerate(rows):
                got = [F(x.strip()) for x in r.split(",")]
                if got != T[f"{law},{lam},{n}"]:
                    raise SystemExit(f"STOP: Bands4Defs {nm} differs from bands4_poly.json at lam={lam} n={n}")
    return T


TAB = load_tables()


def pat_lit(pat):
    return "([" + ", ".join(f"({l}, {lit(w)})" for l, w in pat) + "] : List (ℕ × ℚ))"


class Tier4(g2.Tier):
    def __init__(self, name, spec, pt):
        self.name, self.spec = name, spec
        self.c, self.th, self.eps, self.z = (F(pt[k]) for k in ("c", "theta", "eps", "z"))
        if (pt["law"], pt["zone_law"]) != ("Y", "ZY"):
            raise SystemExit(f"STOP: point {name} law {pt['law']}/{pt['zone_law']} is not Y/ZY")
        self.pat = sorted((int(l), F(w)) for l, w in pt["pattern"].items())
        assert sum(w for _, w in self.pat) == 1 and all(w > 0 and l in (8, 9) for l, w in self.pat)
        self.bf = None
        c, th, eps, z = (R(x) for x in (self.c, self.th, self.eps, self.z))
        y = 9 * self.z
        self.Lbar = sum(l * w for l, w in self.pat)
        LB = R(self.Lbar)
        self.zeta = (L2 / L3) / (c - 1)
        self.pm, self.AY, self.AZ = {}, {}, {}
        SA, SC, S9 = R(0), R(0), R(0)
        for l, w in self.pat:
            self.pm[l] = [pmq(l, n, self.c) for n in range(l + 1)]
            self.AY[l] = [poly(TAB[f"Y,{l},{n}"], y) for n in range(l + 1)]
            self.AZ[l] = [poly(TAB[f"ZY,{l},{n}"], y) for n in range(l + 1)]
            EA = sum(R(self.pm[l][n]) * LN(R(self.AY[l][n])) for n in range(l + 1))
            EZ = sum(R(self.pm[l][n]) * LN(R(self.AZ[l][n])) for n in range(l + 1))
            ECl = sum(R(self.pm[l][n]) * LN(g2.arb(comb(l, n))) for n in range(l + 1))
            SA += R(w) * ((1 - self.zeta) * EA + self.zeta * EZ); SC += R(w) * ECl; S9 += R(w) * LN(g2.arb(l + 1))
        self.qe = (-th * LN(z) + (c / LB) * SA) / L4
        self.qf = (c / LB * SC - c / 2 * H(1 / c) + H(th) + th * L9) / L4
        self.g = (c * H(1 / c) - c * H((1 - th) / c) - th * L9) / L4
        self.E = (c * H(1 / c) / 2 + (c - 1) * LN(g2.arb(3))) / L4
        self.q = (H(th) + th * L9) / L4
        self.pre = eps * c * (S9 / LB + H(1 / c)) / L4
        self.cl = c / LB * SC
        self.k0 = c / 2 * H(1 / c)
        assert hi_of(self.qf) < lo_of(self.qe), "q_fill must be below q_eff"

    def fits(self):
        """True / False when the arb balls decide `class_fits`, None when they overlap."""
        if hi_of(self.cl) < lo_of(self.k0): return True
        if hi_of(self.k0) < lo_of(self.cl): return False
        return None

    def num_lemma(self, keys=QKEYS, tag="num"):
        """The bounds lemma b4<point>_<tag> on the quantities `keys`. Without "qe" the segment polynomials are not
        needed, and their bounds are left out."""
        C, TH, EPS, Z = self.lits()
        cq, thq, zq, epsq = (f"({x} : ℚ)" for x in (C, TH, Z, EPS))
        PAT = pat_lit(self.pat)
        Q = {}
        Q["g"] = (f"gammaExact (({cq} : ℚ) : ℝ) (({thq} : ℚ) : ℝ)", outward(self.g))
        Q["E"] = (f"Epruned (({cq} : ℚ) : ℝ)", outward(self.E))
        Q["q"] = (f"qExp (({thq} : ℚ) : ℝ)", outward(self.q))
        Q["qe"] = (f"qEff4 {PAT} coefY coefZY {cq} {thq} {zq}", outward(self.qe))
        Q["qf"] = (f"qFill4 {PAT} {cq} {thq}", outward(self.qf))
        Q["pre"] = (f"ePre4 {PAT} {cq} {epsq}", outward(self.pre))
        Q["cl"] = (f"lnClass4 {PAT} {cq}", outward(self.cl))
        Q["k0"] = (f"lnK0 {cq}", outward(self.k0))
        assert tuple(Q) == QKEYS
        Q = {k: Q[k] for k in keys}
        polys = "qe" in keys
        self.Q = Q
        stmt = " ∧\n    ".join(f"({lean_q(lo)} : ℝ) ≤ {e} ∧ {e} ≤ ({lean_q(hi)} : ℝ)" for e, (lo, hi) in Q.values())
        what = "every exponent" if keys == QKEYS else "both sides of `class_fits`"
        out = f"/-- Bounds on {what} of point {self.name} (certificates/bands4_cert.py). -/\ntheorem b4{self.name}_{tag} :\n    {stmt} := by\n"
        out += self.cast_lines([self.eps])
        # the pattern: weights, mean length and the ln(lam + 1) arguments as real literals
        simp_extra = []
        for i, (l, w) in enumerate(self.pat):
            out += f"  have ew{i} : ((({lit(w)} : ℚ)) : ℝ) = {lit(w)} := by norm_num\n"
            out += f"  have el{i} : (((({l} + 1 : ℕ) : ℚ)) : ℝ) = {l + 1} := by norm_num\n"
            simp_extra += [f"ew{i}", f"el{i}"]
        out += (f"  have elb : ((lbar {PAT} : ℚ) : ℝ) = {lit(self.Lbar)} := by\n"
                f"    rw [show lbar {PAT} = ({lit(self.Lbar)} : ℚ) by decide +kernel]; norm_num\n")
        simp_extra.append("elb")
        P = gen.Point()
        P.H(f"1 / {C}", 1 / self.c); P.H(f"(1 - {TH}) / {C}", (1 - self.th) / self.c); P.H(TH, self.th)
        for a in (9, 4, 3, 2): P.atom(str(a), a)
        P.atom(Z, self.z)
        for l, _ in self.pat:
            P.atom(str(l + 1), l + 1)
            for n in range(l + 1): P.atom(str(comb(l, n)), comb(l, n))
        for i, (e, x) in enumerate(P.atoms.items()):
            out += gen.atom_lines(f"a{i}", e, x)
        out += "  have hL4 : (0 : ℝ) < log 4 := by linarith\n  have hL3 : (0 : ℝ) < log 3 := by linarith\n"
        if polys:
            zl, zh = floor_dec(lo_of(self.zeta), 38) - F(1, 10 ** 38), ceil_dec(hi_of(self.zeta), 38) + F(1, 10 ** 38)
            out += (f"  have hz : ({lean_q(zl)} : ℝ) ≤ zetaB {C} ∧ zetaB {C} ≤ ({lean_q(zh)} : ℝ) := by\n"
                    f"    unfold zetaB\n    constructor\n"
                    f"    · rw [le_div_iff₀ (by norm_num), le_div_iff₀ hL3]; linarith\n"
                    f"    · rw [div_le_iff₀ (by norm_num), div_le_iff₀ hL3]; linarith\n")
        yq = f"(9 * {zq})"
        for l, _ in self.pat:
            hps = ", ".join(f"hp{l}_{n}" for n in range(l + 1))
            for n in range(l + 1):
                p = self.pm[l][n]
                out += (f"  have hc{l}_{n} : (((Nat.choose {l} {n} : ℕ) : ℚ) : ℝ) = {comb(l, n)} := by\n"
                        f"    rw [show Nat.choose {l} {n} = {comb(l, n)} by decide]; norm_num\n")
                out += (f"  have hp{l}_{n} : ((pmq {l} {n} {cq} : ℚ) : ℝ) = ({lean_q(p)} : ℝ) := by\n"
                        f"    rw [show pmq {l} {n} {cq} = ({lean_q(p)} : ℚ) by decide +kernel]; norm_num\n")
            for tag, law, vals in ((("A", "Y", self.AY[l]), ("Z", "ZY", self.AZ[l])) if polys else ()):
                cf = LAWS[law]
                lo_s, hi_s = F(0), F(0)
                for n in range(l + 1):
                    ln_, lo, hi = log_rat_lines(f"{tag}{l}_{n}", f"polyEval ({cf} {l} {n}) {yq}", vals[n]); out += ln_
                    lo_s += self.pm[l][n] * lo; hi_s += self.pm[l][n] * hi
                lo_s, hi_s = floor_dec(lo_s, 35) - F(1, 10 ** 35), ceil_dec(hi_s, 35) + F(1, 10 ** 35)
                assert lo_s > 0
                ex = f"EAl {cf} {l} {cq} {yq}"
                out += (f"  have h{tag}{l} : ({lean_q(lo_s)} : ℝ) ≤ {ex} ∧ {ex} ≤ ({lean_q(hi_s)} : ℝ) := by\n"
                        f"    simp only [EAl, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]\n"
                        f"    rw [{hps}]; constructor <;> linarith\n")
            cll, clh = F(0), F(0)
            for n in range(l + 1):
                lc = LN(g2.arb(comb(l, n))); cll += self.pm[l][n] * lo_of(lc); clh += self.pm[l][n] * hi_of(lc)
            cll, clh = floor_dec(cll, 35) - F(1, 10 ** 35), ceil_dec(clh, 35) + F(1, 10 ** 35)
            out += (f"  have hECl{l} : ({lean_q(cll)} : ℝ) ≤ ECl {l} {cq} ∧ ECl {l} {cq} ≤ ({lean_q(clh)} : ℝ) := by\n"
                    f"    simp only [ECl, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]\n"
                    f"    rw [{hps}, {', '.join(f'hc{l}_{n}' for n in range(l + 1))}]; constructor <;> linarith\n")
            # the products (1 - zeta) EA_Y and zeta EA_ZY, both factors nonnegative
            if not polys: continue
            out += (f"  have hP1_{l} := mul_mem (x := 1 - zetaB {C}) (xl := 1 - {lean_q(zh)}) (xh := 1 - {lean_q(zl)}) "
                    f"⟨by linarith, by linarith⟩ hA{l} (by norm_num) (by norm_num)\n")
            out += f"  have hP2_{l} := mul_mem hz hZ{l} (by norm_num) (by norm_num)\n"
        pieces = []
        lists = "List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero"
        UNF = {"g": "gammaExact H", "E": "Epruned H", "q": "qExp H", "qe": "qEff4 segSum",
               "qf": "qFill4 lnClass4 lnK0 segSum H", "pre": "ePre4 segSum H", "cl": "lnClass4 segSum", "k0": "lnK0 H"}
        for key in keys:
            e, (lo, hi) = Q[key]
            simp = f"    simp only [{lists}, ec, eth, ez, eeps0, {', '.join(simp_extra)}, Nat.cast_ofNat]\n"
            out += (f"  have Q{key} : ({lean_q(lo)} : ℝ) ≤ {e} ∧ {e} ≤ ({lean_q(hi)} : ℝ) := by\n"
                    f"    unfold {UNF[key]}\n{simp}    constructor\n")
            # the two sides of class_fits are not divided by ln 4
            out += ("    · linarith\n    · linarith\n" if key in ("cl", "k0") else
                    "    · rw [le_div_iff₀ hL4]; linarith\n    · rw [div_le_iff₀ hL4]; linarith\n")
            pieces += [f"Q{key}.1", f"Q{key}.2"]
        out += "  exact ⟨" + ", ".join(pieces) + "⟩\n"
        return out

    def obtain(self, keys=QKEYS, tag="num"):
        names = [f"{k}{s}" for k in keys for s in "lh"]
        return f"  obtain ⟨{', '.join(names)}⟩ := b4{self.name}_{tag}\n"

    def fit_control(self, claims, doc):
        """A point where `class_fits` fails: its own bounds lemma on the two sides, then CertBands4 refuted."""
        assert self.fits() is False, (self.name, "class_fits must fail")
        out = self.num_lemma(("cl", "k0"), "fit") + "\n"
        out += (f"/-- {doc} -/\ntheorem bands4_{self.name}_fails_class_fits : ¬ ({self.ty(claims)}) := by\n"
                + self.obtain(("cl", "k0"), "fit") + "  intro h\n  have := h.class_fits\n  linarith\n")
        return out

    def ty(self, claims, eps=None):
        C, TH, EPS, Z = self.lits(eps)
        return (f"CertBands4 {pat_lit(self.pat)} coefY coefZY {C} {TH} {EPS} {Z} ({lean_q(F(claims['s0']))}) "
                f"({lean_q(F(claims['b']))}) ({lean_q(F(claims['o']))})")

    # gen_bands2's proof scripts with the CertBands4 structure; the pattern check is closed by kernel evaluation
    def positive(self, claims, doc):
        assert self.fits() is True, (self.name, "class_fits must hold")
        out = super().positive(claims, doc).replace("CertBands2.mk'", "CertBands4.mk'").replace(
            f"theorem bands2_{self.name}", f"theorem bands4_{self.name}")
        assert "    | (right; right; linarith)\n" in out
        return out.replace("    | (right; right; linarith)\n", "    | (right; right; linarith)\n    | (decide +kernel)\n")

    def negative(self, tag, claims, doc, eps=None):
        return super().negative(tag, claims, doc, eps).replace(
            f"theorem bands2_{self.name}", f"theorem bands4_{self.name}")


def cert_lines():
    """bands4_cert.out, per point name: parameters, pattern, law and the printed saving / exponent / e_pre."""
    txt = open(os.path.join(CERTS, "bands4_cert.out")).read()
    res = {}
    for m in re.finditer(r"^(.+?): (?:CERTIFIED|FAILED) at c=(\S+), th=(\S+), eps=(\S+), z=(\S+), pattern=(\{.*?\}), law=(\S+)/(\S+)\n"
                         r"(?:.*\n)*?   sigma >= (\S+)   3SUM exponent <= (\S+)   e_pre <= (\S+)", txt, re.M):
        res[m.group(1)] = m.groups()[1:]
    return res


def failures(key):
    """The "failed:" lines bands4_cert.out prints under point `key`."""
    txt = open(os.path.join(CERTS, "bands4_cert.out")).read()
    m = re.search(r"^" + re.escape(key) + r": FAILED at .*\n((?:   failed: .*\n)*)", txt, re.M)
    if not m: raise SystemExit(f"STOP: bands4_cert.out has no FAILED block for {key}")
    return [x.split("failed: ", 1)[1] for x in m.group(1).splitlines()]


def same_point(T, pt, printed):
    c, th, eps, z, pat, law, zlaw = printed[:7]
    patp = sorted((int(k), F(v)) for k, v in eval(pat, {"__builtins__": {}}).items())
    if (F(c), F(th), F(eps), F(z), patp, law, zlaw) != (T.c, T.th, T.eps, T.z, T.pat, pt["law"], pt["zone_law"]):
        raise SystemExit(f"STOP: point {T.name} differs from bands4_cert.out")


def cross_check(T, spec, pt, printed):
    c, th, eps, z, pat, law, zlaw, s0, ex, pre = printed
    patp = sorted((int(k), F(v)) for k, v in eval(pat, {"__builtins__": {}}).items())
    want = (F(c), F(th), F(eps), F(z), patp, law, zlaw)
    got = (T.c, T.th, T.eps, T.z, T.pat, pt["law"], pt["zone_law"])
    if want != got:
        raise SystemExit(f"STOP: point {T.name} differs from bands4_cert.out: {want} vs {got}")
    lo, hi, _ = T.sigma()
    if not (floor_dec(lo, 10) == F(s0) and ceil_dec(2 - lo, 9) == F(ex) and ceil_dec(hi_of(T.pre), 6) == F(pre)):
        raise SystemExit(f"STOP: point {T.name} values differ from bands4_cert.out: sigma in [{float(lo)}, {float(hi)}], "
                         f"printed {s0} {ex} {pre}")
    cl = spec["claims"]
    if (F(cl["s0"]), F(cl["b"])) != (F(s0), F(ex)):
        raise SystemExit(f"STOP: point {T.name} claims {cl} are not bands4_cert.out's {s0} {ex}")
    if not (2 - F(s0) < F(cl["o"]) and F(cl["o"]) - g2.ulp(cl["o"]) < 2 - F(s0)):
        raise SystemExit(f"STOP: point {T.name} O-line {cl['o']} is not the exponent rounded up to 6 places")


HEADER = g2.HEADER.replace("import ThreesumLean.Bands2Defs", "import ThreesumLean.Bands4Defs").replace(
    "# Kernel checks of the Theorem 3 certificate (generated by gen_bands2.py; do not edit)",
    "# Kernel checks of the Theorem C'' certificate (generated by gen_bands4.py; do not edit)").replace(
    "Tiers W, S, C of Theorem C in proofs/bands.md at the exact rational points of certificates/bands_cert.py (`POINTS`).\n"
    "Each positive theorem states `CertBands2` (every side condition of bands_cert.py, the saving, the 3SUM exponent and\n"
    "the strict `O(n^e)` line). Each `*_fails_*` theorem is a negative control, proved false.",
    "Tier (C) of Theorem C'' in proofs/bands.md (Lemma Y, segment lengths 8 and 9) at the exact rational points of\n"
    "certificates/bands4_cert.py (`POINTS`). Each positive theorem states `CertBands4` (every side condition of\n"
    "bands4_cert.py, the saving, the 3SUM exponent and the strict `O(n^e)` line). Each `*_fails_*` theorem is a\n"
    "negative control, proved false.")
assert "Bands4Defs" in HEADER and "CertBands4" in HEADER and "gen_bands4" in HEADER


def run():
    pts = bands4_cert.POINTS
    printed = cert_lines()
    out = HEADER
    for name, spec in POINTS.items():
        T = Tier4(name, spec, pts[spec["key"]])
        cross_check(T, spec, pts[spec["key"]], printed[spec["key"]])
        cl = spec["claims"]
        out += T.num_lemma() + "\n" + T.positive(cl, spec["doc"]) + "\n"
        nx = {k: (v if k != "s0" else f"{F(cl['s0']) + g2.ulp(cl['s0'])}") for k, v in cl.items()}
        out += T.negative("next_s0", nx, f"Next grid point: s0 + {lean_q(g2.ulp(cl['s0']))} must fail.") + "\n"
        nb = dict(cl); nb["b"] = str(F(cl["b"]) - g2.ulp(cl["b"]))
        out += T.negative("next_b", nb, f"Next grid point: exponent - {lean_q(g2.ulp(cl['b']))} must fail.") + "\n"
        no = dict(cl); no["o"] = str(F(cl["o"]) - g2.ulp(cl["o"]))
        out += T.negative("next_o", no, f"The O(n^e) line one unit lower ({F(cl['o']) - g2.ulp(cl['o'])}) must fail.") + "\n"
        pe = None
        for units in (1, 10, 100, 1000):
            for sgn in (1, -1):
                cand = T.eps + sgn * F(units, T.eps.denominator)
                if pe is None and T.sigma(cand)[1] < F(cl["s0"]): pe, pu = cand, sgn * units
            if pe is not None: break
        out += T.negative("perturbed_eps", cl, f"Perturbed parameter: eps = {pe} (numerator {pu:+d}) must fail.", eps=pe) + "\n"
        lo, hi, _ = T.sigma()
        print(name, "sigma in", float(lo), float(hi), "qe", float(lo_of(T.qe)), "qf", float(lo_of(T.qf)),
              "e_pre", float(hi_of(T.pre)), "margin s0", float(lo - F(cl["s0"])), "exponent <=", ceil_dec(2 - lo, 9),
              "fit margin", float(lo_of(T.k0) - hi_of(T.cl)))
    for name, spec in CONTROLS.items():
        pt = pts[spec["key"]]
        T = Tier4(name, spec, pt)
        same_point(T, pt, printed[spec["key"]])
        if failures(spec["key"]) != ["class fits a diagonal"]:
            raise SystemExit(f"STOP: control {name} must fail class_fits only, bands4_cert.out says {failures(spec['key'])}")
        out += T.fit_control(spec["claims"], spec["doc"]) + "\n"
        print(name, "class_fits fails by", float(lo_of(T.cl) - hi_of(T.k0)))
    out += "end TS\n"
    open(os.path.join(HERE, "ThreesumLean", "Bands4Points.lean"), "w").write(out)


if __name__ == "__main__":
    run()
