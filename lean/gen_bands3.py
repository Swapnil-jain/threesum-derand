"""Generate ThreesumLean/Bands3Points.lean: kernel checks of certificates/bands3_cert.py (Theorem C') at tiers W, S, C.

Derived from gen_bands2.py, whose Tier class it reuses. The only changes are the ones Theorem C' makes:
  * q_eff takes the zone term (c/lam) zeta sum_n Bin(n) ln A(lam, n; 9z, 8/9) (Lemma Z) instead of zeta ln(1 + 9z),
    so the bounds lemma also sandwiches the nine zone averages A(8, n; 9z, 8/9);
  * the theorems state CertBands3 (Bands3Defs.lean) at the points of bands3_cert.py (POINTS) with bands3_cert.out's
    claims.
Each tier gets the positive theorem and the four negative controls of gen_bands2.py (next s0, next exponent, next
O-line, perturbed eps). Before writing, every point is cross-checked against certificates/bands3_cert.out
(parameters, printed saving, exponent and e_pre); any mismatch aborts. Usage: python gen_bands3.py
"""
import os, re, sys
from fractions import Fraction as F
from math import comb
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(os.path.dirname(HERE), "certificates"))
import gen_bands2 as g2
from gen_bands2 import R, LN, L4, LAM, Aq, lit, qlit, outward, log_rat_lines, lean_q, floor_dec, ceil_dec, lo_of, hi_of
import gen
import bands3_cert

CERTS = os.path.join(os.path.dirname(HERE), "certificates")
ZONE_B = F(8, 9)

# claims: bands3_cert.out's saving (rounded down) and exponent (rounded up); the O-line is the exponent rounded up to 6 places
TIERS = {
    "W": {"key": "(W) worst keys, adjacent moves, zone moves", "bf": "bW", "law": lambda l: F(22, 27),
          "claims": {"s0": "0.0041463659", "b": "1.995853635", "o": "1.995854"},
          "doc": "Tier (W): worst keys, adjacent moves, b = 22/27, zone law 8/9 (Lemma Z)."},
    "S": {"key": "(S) shifted keys, adjacent moves, zone moves", "bf": "bSh", "law": lambda l: F(62, 81),
          "claims": {"s0": "0.0041917719", "b": "1.995808229", "o": "1.995809"},
          "doc": "Tier (S): shifted keys, adjacent moves, b = 62/81, zone law 8/9 (Lemma Z)."},
    "C": {"key": "(C) shifted keys, stretch moves, zone moves", "bf": "bS", "law": lambda l: g2.BSTRETCH[min(l, 5)],
          "claims": {"s0": "0.0042143770", "b": "1.995785623", "o": "1.995786"},
          "doc": "Tier (C): shifted keys, stretch moves, b(len), zone law 8/9 (Lemma Z). The headline O(n^1.995786)."},
}


class Tier3(g2.Tier):
    def __init__(self, name, spec, pt):
        super().__init__(name, spec, pt)
        assert F(pt["zone_b"]) == ZONE_B and pt["lam"] == LAM and pt["b"] in (str(spec["law"](0)), "stretch")
        c, th, z = R(self.c), R(self.th), R(self.z)
        y = 9 * self.z
        self.AZ = [Aq(LAM, n, y, lambda l: ZONE_B) for n in range(LAM + 1)]
        self.EZ = sum(R(self.pm[n]) * LN(R(self.AZ[n])) for n in range(LAM + 1))
        # the bands3 q_eff replaces bands2's (set by the parent constructor)
        self.qe = (-th * LN(z) + (c / LAM) * ((1 - self.zeta) * self.EA + self.zeta * self.EZ)) / L4
        assert hi_of(self.qf) < lo_of(self.qe), "q_fill must be below q_eff"

    def num_lemma(self):
        """The bounds lemma b3<tier>_num (gen_bands2's, with the zone sum in q_eff)."""
        C, TH, EPS, Z = self.lits()
        cq, thq, zq, epsq = (f"({x} : ℚ)" for x in (C, TH, Z, EPS))
        bf = self.bf
        Q = {}
        Q["g"] = (f"gammaExact (({cq} : ℚ) : ℝ) (({thq} : ℚ) : ℝ)", outward(self.g))
        Q["E"] = (f"Epruned (({cq} : ℚ) : ℝ)", outward(self.E))
        Q["q"] = (f"qExp (({thq} : ℚ) : ℝ)", outward(self.q))
        Q["qe"] = (f"qEff3 {LAM} {bf} {cq} {thq} {zq}", outward(self.qe))
        Q["qf"] = (f"qFill {LAM} {cq} {thq}", outward(self.qf))
        Q["pre"] = (f"ePre {LAM} {cq} {epsq}", outward(self.pre))
        self.Q = Q
        stmt = " ∧\n    ".join(f"({lean_q(lo)} : ℝ) ≤ {e} ∧ {e} ≤ ({lean_q(hi)} : ℝ)" for e, (lo, hi) in Q.values())
        out = f"/-- Bounds on every exponent of tier {self.name} (certificates/bands3_cert.py). -/\ntheorem b3{self.name}_num :\n    {stmt} := by\n"
        out += self.cast_lines([self.eps])
        P = gen.Point()
        P.H(f"1 / {C}", 1 / self.c); P.H(f"(1 - {TH}) / {C}", (1 - self.th) / self.c); P.H(TH, self.th)
        for a in (9, 4, 3, 2): P.atom(str(a), a)
        P.atom(Z, self.z)
        for n in range(LAM + 1): P.atom(str(comb(LAM, n)), comb(LAM, n))
        for i, (e, x) in enumerate(P.atoms.items()):
            out += gen.atom_lines(f"a{i}", e, x)
        out += "  have hL4 : (0 : ℝ) < log 4 := by linarith\n  have hL3 : (0 : ℝ) < log 3 := by linarith\n"
        yq = f"(9 * {zq})"
        hps = ", ".join(f"hp{n}" for n in range(LAM + 1))
        for n in range(LAM + 1):
            p = self.pm[n]
            out += (f"  have hc{n} : (((Nat.choose {LAM} {n} : ℕ) : ℚ) : ℝ) = {comb(LAM, n)} := by\n"
                    f"    rw [show Nat.choose {LAM} {n} = {comb(LAM, n)} by decide]; norm_num\n")
            out += (f"  have hp{n} : ((pmq {LAM} {n} {cq} : ℚ) : ℝ) = ({lean_q(p)} : ℝ) := by\n"
                    f"    rw [show pmq {LAM} {n} {cq} = ({lean_q(p)} : ℚ) by decide +kernel]; norm_num\n")

        def sandwich(tag, bfl, vals):
            """log_rat_mem for every A(8, n; 9z, law) and the Bin-weighted sum EA, rounded outward to 35 places."""
            nonlocal out
            lo_s, hi_s = F(0), F(0)
            for n in range(LAM + 1):
                ln_, lo, hi = log_rat_lines(f"{tag}{n}", f"Aq {LAM} {n} {yq} {bfl}", vals[n]); out += ln_
                lo_s += self.pm[n] * lo; hi_s += self.pm[n] * hi
            lo_s, hi_s = floor_dec(lo_s, 35) - F(1, 10 ** 35), ceil_dec(hi_s, 35) + F(1, 10 ** 35)
            assert lo_s > 0
            out += (f"  have h{tag} : ({lean_q(lo_s)} : ℝ) ≤ EA {LAM} {cq} {yq} {bfl} ∧ EA {LAM} {cq} {yq} {bfl} ≤ ({lean_q(hi_s)} : ℝ) := by\n"
                    f"    simp only [EA, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]\n"
                    f"    rw [{hps}]; constructor <;> linarith\n")
        sandwich("A", bf, self.A)
        sandwich("Z", "bZ", self.AZ)
        cll, clh = F(0), F(0)
        for n in range(LAM + 1):
            lc = LN(g2.arb(comb(LAM, n))); cll += self.pm[n] * lo_of(lc); clh += self.pm[n] * hi_of(lc)
        cll, clh = floor_dec(cll, 35) - F(1, 10 ** 35), ceil_dec(clh, 35) + F(1, 10 ** 35)
        out += (f"  have hECl : ({lean_q(cll)} : ℝ) ≤ ECl {LAM} {cq} ∧ ECl {LAM} {cq} ≤ ({lean_q(clh)} : ℝ) := by\n"
                f"    simp only [ECl, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]\n"
                f"    rw [{hps}, {', '.join(f'hc{n}' for n in range(LAM + 1))}]; constructor <;> linarith\n")
        zl, zh = floor_dec(lo_of(self.zeta), 38) - F(1, 10 ** 38), ceil_dec(hi_of(self.zeta), 38) + F(1, 10 ** 38)
        out += (f"  have hz : ({lean_q(zl)} : ℝ) ≤ zetaB {C} ∧ zetaB {C} ≤ ({lean_q(zh)} : ℝ) := by\n"
                f"    unfold zetaB\n    constructor\n"
                f"    · rw [le_div_iff₀ (by norm_num), le_div_iff₀ hL3]; linarith\n"
                f"    · rw [div_le_iff₀ (by norm_num), div_le_iff₀ hL3]; linarith\n")
        # the products (1 - zeta) EA and zeta EZ, both factors nonnegative
        out += (f"  have hP1 := mul_mem (x := 1 - zetaB {C}) (xl := 1 - {lean_q(zh)}) (xh := 1 - {lean_q(zl)}) "
                f"⟨by linarith, by linarith⟩ hA (by norm_num) (by norm_num)\n")
        out += f"  have hP2 := mul_mem hz hZ (by norm_num) (by norm_num)\n"
        pieces = []
        for key, unfold in (("g", "gammaExact H"), ("E", "Epruned H"), ("q", "qExp H"), ("qe", "qEff3"), ("qf", "qFill H"),
                            ("pre", "ePre H")):
            e, (lo, hi) = Q[key]
            simp = "    simp only [ec, eth, ez, eeps0, Nat.cast_ofNat]\n"
            out += (f"  have Q{key} : ({lean_q(lo)} : ℝ) ≤ {e} ∧ {e} ≤ ({lean_q(hi)} : ℝ) := by\n"
                    f"    unfold {unfold}\n{simp}    constructor\n"
                    f"    · rw [le_div_iff₀ hL4]; linarith\n    · rw [div_le_iff₀ hL4]; linarith\n")
            pieces += [f"Q{key}.1", f"Q{key}.2"]
        out += "  exact ⟨" + ", ".join(pieces) + "⟩\n"
        return out

    def obtain(self):
        return super().obtain().replace(f"b2{self.name}_num", f"b3{self.name}_num")

    def ty(self, claims, eps=None):
        return super().ty(claims, eps).replace("CertBands2", "CertBands3", 1)

    # gen_bands2's proof scripts, with the bands3 structure and theorem names (the tactics are identical)
    def positive(self, claims, doc):
        return super().positive(claims, doc).replace("CertBands2.mk'", "CertBands3.mk'").replace(
            f"theorem bands2_{self.name}", f"theorem bands3_{self.name}")

    def negative(self, tag, claims, doc, eps=None):
        return super().negative(tag, claims, doc, eps).replace(
            f"theorem bands2_{self.name}", f"theorem bands3_{self.name}")


def cert_lines():
    """bands3_cert.out, parsed per tier: parameters and printed saving / exponent / e_pre."""
    txt = open(os.path.join(CERTS, "bands3_cert.out")).read()
    res = {}
    for m in re.finditer(r"^\((\w)\) [^\n]*, zone moves: CERTIFIED  sigma >= (\S+)\n"
                         r"   certified point \(exact rationals\): c = (\S+), theta = (\S+), eps = (\S+), z = (\S+), "
                         r"lam = (\d+), b = (\S+), zone b = (\S+)\n"
                         r"(?:.*\n)*?   layout precomputation: .* e_pre <= (\S+)\n"
                         r"   deterministic 3SUM <= n\^\((\S+)\+o\(1\)\)", txt, re.M):
        t, s0, c, th, eps, z, lam, b, zb, pre, ex = m.groups()
        res[t] = (c, th, eps, z, lam, b, zb, s0, ex, pre)
    return res


def cross_check(T, spec, pt, printed):
    c, th, eps, z, lam, b, zb, s0, ex, pre = printed
    want = (F(c), F(th), F(eps), F(z), int(lam), F(zb))
    got = (T.c, T.th, T.eps, T.z, pt["lam"], F(pt["zone_b"]))
    if want != got or b != pt["b"]:
        raise SystemExit(f"STOP: tier {T.name} point differs from bands3_cert.out: {want} {b} vs {got} {pt['b']}")
    lo, hi, _ = T.sigma()
    if not (floor_dec(lo, 10) == F(s0) and ceil_dec(2 - lo, 9) == F(ex) and ceil_dec(hi_of(T.pre), 6) == F(pre)):
        raise SystemExit(f"STOP: tier {T.name} values differ from bands3_cert.out: sigma in [{float(lo)}, {float(hi)}], "
                         f"printed {s0} {ex} {pre}")
    cl = spec["claims"]
    if (F(cl["s0"]), F(cl["b"])) != (F(s0), F(ex)):
        raise SystemExit(f"STOP: tier {T.name} claims {cl} are not bands3_cert.out's {s0} {ex}")


HEADER = g2.HEADER.replace("import ThreesumLean.Bands2Defs", "import ThreesumLean.Bands3Defs").replace(
    "# Kernel checks of the Theorem 3 certificate (generated by gen_bands2.py; do not edit)",
    "# Kernel checks of the Theorem C' certificate (generated by gen_bands3.py; do not edit)").replace(
    "Tiers W, S, C of Theorem C in proofs/bands.md at the exact rational points of certificates/bands_cert.py (`POINTS`).\n"
    "Each positive theorem states `CertBands2` (every side condition of bands_cert.py,",
    "Tiers W, S, C of Theorem C' in proofs/bands.md at the exact rational points of certificates/bands3_cert.py\n"
    "(`POINTS`). Each positive theorem states `CertBands3` (every side condition of bands3_cert.py,").replace(
    "bands3_cert.py, the saving, the 3SUM exponent and\nthe strict `O(n^e)` line)",
    "bands3_cert.py, the saving, the 3SUM\nexponent and the strict `O(n^e)` line)")
assert "Bands3Defs" in HEADER and "CertBands3" in HEADER and "gen_bands3" in HEADER


def run():
    pts = {name: {"c": c, "theta": th, "eps": eps, "z": z, "lam": LAM, "b": law, "zone_b": zone}
           for name, c, th, eps, z, law, zone, _ok in bands3_cert.POINTS}
    printed = cert_lines()
    out = HEADER
    for name, spec in TIERS.items():
        T = Tier3(name, spec, pts[spec["key"]])
        cross_check(T, spec, pts[spec["key"]], printed[name])
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
              "e_pre", float(hi_of(T.pre)), "margin s0", float(lo - F(cl["s0"])), "exponent <=", ceil_dec(2 - lo, 9))
    out += "end TS\n"
    open(os.path.join(HERE, "ThreesumLean", "Bands3Points.lean"), "w").write(out)


if __name__ == "__main__":
    run()
