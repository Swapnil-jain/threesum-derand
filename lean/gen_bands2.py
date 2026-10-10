"""Generate ThreesumLean/Bands2Points.lean (kernel checks of certificates/bands_cert.py, Theorem 3, at tiers W, S, C)
and Bands2Stretch.lean with its leaves Bands2Leaves1-3.lean (the stretch law b(len) for len <= 7).

For each tier it emits
  * `<tier>_num`: rigorous bounds on gamma, E, q(th), q_eff, q_fill and e_pre, derived from series bounds on every
    log atom (log_mem) and, for the class averages A(8, n; 9z, b) and the binomials C(8, n), from log_rat_mem
    (A is a kernel-evaluated rational, sandwiched between 40-digit decimals);
  * the positive theorem: CertBands2 with every bands_cert.py side condition, the printed saving, the 3SUM exponent and
    the strict O(n^e) line;
  * negative controls proved false: the saving at the next grid point, the exponent at the next grid point down,
    the O(n^e) line one unit lower, and eps moved by one unit in its numerator.
The exact rational points and the stretch table are read from certificates/bands_cert.py (POINTS, B_STRETCH).
arb (python-flint) is used only to choose the rational bounds; Lean checks them. Usage: python gen_bands2.py
"""
import math, os, sys
from fractions import Fraction as F
from itertools import combinations
from math import comb
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(os.path.dirname(HERE), "certificates"))
from flint import arb, ctx, fmpq
import gen
import bands_cert
from gen import atom_lines, lean_q, lo_of, hi_of, floor_dec, ceil_dec, Param
ctx.prec = 400

LAM = 8
A_DIGITS = 40          # decimals of the sandwich xl <= A <= xh
Q_DIGITS = 30          # derived quantities are rounded outward to this many decimals
BSTRETCH = bands_cert.B_STRETCH  # b(len) for len <= 5, the table Bands2Stretch.lean checks against the enumeration

def R(x):
    x = F(x); return arb(fmpq(x.numerator, x.denominator))
LN = lambda x: x.log()
def H(x): return -x * LN(x) - (1 - x) * LN(1 - x)
L2, L3, L4, L9 = LN(arb(2)), LN(arb(3)), LN(arb(4)), LN(arb(9))

# --- exact replicas of the Lean definitions (Bands2Defs.lean) -------------------------------------------------
def runs(S):
    if not S: return []
    r = runs(S[1:]); x = S[0]
    if not r: return [(x, 1)]
    s, k = r[0]
    return [(x, k + 1)] + r[1:] if x + 1 == s else [(x, 1)] + r
def run_factors(y, bf, e, rs):
    if not rs: return F(1)
    (s, k), rest = rs[0], rs[1:]
    f = (1 + y) ** k if s == 0 else 1 + bf(s - e) * ((1 + y) ** k - 1)
    return f * run_factors(y, bf, s + k, rest)
def Aq(lam, n, y, bf):
    return sum(run_factors(y, bf, 0, runs(list(S))) for S in combinations(range(lam), n)) / comb(lam, n)
def pmq(lam, n, c): return comb(lam, n) * (1 / c) ** n * (1 - 1 / c) ** (lam - n)

TIERS = {
    "W": {"key": "(W) worst keys, adjacent moves", "bf": "bW", "law": lambda l: F(22, 27),
          "claims": {"s0": "0.0041432182", "b": "1.995856782", "o": "1.995857"},
          "doc": "Tier (W): worst keys, adjacent moves, b = 22/27 (Lemma 3.1). Needs neither Lemma 3.3 nor 3.4."},
    "S": {"key": "(S) shifted keys, adjacent moves", "bf": "bSh", "law": lambda l: F(62, 81),
          "claims": {"s0": "0.0041883974", "b": "1.995811603", "o": "1.995812"},
          "doc": "Tier (S): shifted keys, adjacent moves, b = 62/81 (Lemmas 3.2, 3.4)."},
    "C": {"key": "(C) shifted keys, stretch moves", "bf": "bS", "law": lambda l: BSTRETCH[min(l, 5)],
          "claims": {"s0": "0.0042108435", "b": "1.995789157", "o": "1.995790"},
          "doc": "Tier (C): shifted keys, stretch moves, b(len) (Lemmas 3.2 to 3.4). The headline O(n^1.995790)."},
}

def lit(x):
    """A rational as a parenthesised Lean literal (numerator/denominator)."""
    x = F(x); return f"({x.numerator}/{x.denominator})" if x.denominator != 1 else f"({x.numerator})"
def qlit(x): return f"({lit(x)} : ℚ)"

def outward(v, d=Q_DIGITS):
    return floor_dec(lo_of(v), d) - F(1, 10 ** d), ceil_dec(hi_of(v), d) + F(1, 10 ** d)

def log_rat_lines(name, xexpr, x):
    """log_rat_mem for log((xexpr : ℚ) : ℝ) with x its exact value: sandwich by A_DIGITS decimals."""
    xl, xh = floor_dec(x, A_DIGITS), ceil_dec(x, A_DIGITS)
    out = []
    bounds = []
    for v in (xl, xh):
        k = round(math.log2(v)); t = 1 - v / F(2) ** k
        assert abs(t) < F(1, 2)
        S, Rr = gen.lsum(t, gen.N_SERIES), gen.lrem(t, gen.N_SERIES)
        lo = floor_dec(-S - Rr + min(k * gen.L2LO, k * gen.L2HI), gen.ATOM_DIGITS)
        hi = ceil_dec(-S + Rr + max(k * gen.L2LO, k * gen.L2HI), gen.ATOM_DIGITS)
        bounds.append((v, k, lo, hi))
    (_, k1, lo1, hi1), (_, k2, lo2, hi2) = bounds
    line = (f"  obtain ⟨{name}l, {name}h⟩ := log_rat_mem ({xexpr}) {qlit(xl)} {qlit(xh)} ({lean_q(lo1)}) ({lean_q(hi2)}) "
            f"({lean_q(lo2)}) ({lean_q(hi1)}) ({k1}) ({k2}) {gen.N_SERIES}\n"
            f"    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)\n")
    # sanity: the log bounds must enclose arb's log x
    lx = LN(R(x)); assert lo1 <= lo_of(lx) and hi_of(lx) <= hi2
    return line, lo1, hi2

class Tier:
    def __init__(self, name, spec, pt):
        self.name, self.spec = name, spec
        self.c, self.th, self.eps, self.z = (F(pt[k]) for k in ("c", "theta", "eps", "z"))
        self.bf, self.law = spec["bf"], spec["law"]
        c, th, eps, z = (R(x) for x in (self.c, self.th, self.eps, self.z))
        y = 9 * self.z
        self.A = [Aq(LAM, n, y, self.law) for n in range(LAM + 1)]
        self.pm = [pmq(LAM, n, self.c) for n in range(LAM + 1)]
        self.EA = sum(R(self.pm[n]) * LN(R(self.A[n])) for n in range(LAM + 1))
        self.ECl = sum(R(self.pm[n]) * LN(arb(comb(LAM, n))) for n in range(LAM + 1))
        self.zeta = (L2 / L3) / (c - 1)
        self.qe = (-th * LN(z) + (1 - self.zeta) * (c / LAM) * self.EA + self.zeta * LN(1 + 9 * z)) / L4
        self.qf = (c / LAM * self.ECl - c / 2 * H(1 / c) + H(th) + th * L9) / L4
        self.g = (c * H(1 / c) - c * H((1 - th) / c) - th * L9) / L4
        self.E = (c * H(1 / c) / 2 + (c - 1) * LN(arb(3))) / L4
        self.q = (H(th) + th * L9) / L4
        self.pre = eps * c * (L9 / LAM + H(1 / c)) / L4
        assert hi_of(self.qf) < lo_of(self.qe), "q_fill must be below q_eff"

    def terms(self, eps):
        e = R(eps); return [e * self.g, e * (R(F(1, 2)) - self.qe), 1 - e * self.E]

    # Lean literals of the parameters
    def lits(self, eps=None):
        eps = self.eps if eps is None else eps
        return lit(self.c), lit(self.th), lit(eps), lit(self.z)

    def cast_lines(self, eps_list):
        out = ""
        vals = [("ec", self.c), ("eth", self.th), ("ez", self.z)] + [(f"eeps{i}", e) for i, e in enumerate(eps_list)]
        for nm, v in vals:
            out += f"  have {nm} : ((({lit(v)} : ℚ)) : ℝ) = {lit(v)} := by norm_num\n"
        return out

    def num_lemma(self):
        """The bounds lemma <tier>_num."""
        C, TH, EPS, Z = self.lits()
        cq, thq, zq, epsq = (f"({x} : ℚ)" for x in (C, TH, Z, EPS))
        bf = self.bf
        Q = {}
        Q["g"] = (f"gammaExact (({cq} : ℚ) : ℝ) (({thq} : ℚ) : ℝ)", outward(self.g))
        Q["E"] = (f"Epruned (({cq} : ℚ) : ℝ)", outward(self.E))
        Q["q"] = (f"qExp (({thq} : ℚ) : ℝ)", outward(self.q))
        Q["qe"] = (f"qEff {LAM} {bf} {cq} {thq} {zq}", outward(self.qe))
        Q["qf"] = (f"qFill {LAM} {cq} {thq}", outward(self.qf))
        Q["pre"] = (f"ePre {LAM} {cq} {epsq}", outward(self.pre))
        self.Q = Q
        stmt = " ∧\n    ".join(f"({lean_q(lo)} : ℝ) ≤ {e} ∧ {e} ≤ ({lean_q(hi)} : ℝ)" for e, (lo, hi) in Q.values())
        out = f"/-- Bounds on every exponent of tier {self.name} (certificates/bands_cert.py). -/\ntheorem b2{self.name}_num :\n    {stmt} := by\n"
        out += self.cast_lines([self.eps])
        # log atoms (real literal expressions)
        P = gen.Point()
        P.H(f"1 / {C}", 1 / self.c); P.H(f"(1 - {TH}) / {C}", (1 - self.th) / self.c); P.H(TH, self.th)
        for a in (9, 4, 3, 2): P.atom(str(a), a)
        P.atom(Z, self.z); P.atom(f"1 + 9 * {Z}", 1 + 9 * self.z)
        for n in range(LAM + 1): P.atom(str(comb(LAM, n)), comb(LAM, n))
        for i, (e, x) in enumerate(P.atoms.items()):
            out += atom_lines(f"a{i}", e, x)
        out += "  have hL4 : (0 : ℝ) < log 4 := by linarith\n  have hL3 : (0 : ℝ) < log 3 := by linarith\n"
        # class averages and binomials
        yq = f"(9 * {zq})"
        eal, eah = F(0), F(0); cll, clh = F(0), F(0)
        for n in range(LAM + 1):
            ln_, lo, hi = log_rat_lines(f"A{n}", f"Aq {LAM} {n} {yq} {bf}", self.A[n]); out += ln_
            p = self.pm[n]; eal += p * lo; eah += p * hi
            out += (f"  have hc{n} : (((Nat.choose {LAM} {n} : ℕ) : ℚ) : ℝ) = {comb(LAM, n)} := by\n"
                    f"    rw [show Nat.choose {LAM} {n} = {comb(LAM, n)} by decide]; norm_num\n")
            out += (f"  have hp{n} : ((pmq {LAM} {n} {cq} : ℚ) : ℝ) = ({lean_q(p)} : ℝ) := by\n"
                    f"    rw [show pmq {LAM} {n} {cq} = ({lean_q(p)} : ℚ) by decide +kernel]; norm_num\n")
        for n in range(LAM + 1):
            lc = LN(arb(comb(LAM, n))); cll += self.pm[n] * lo_of(lc); clh += self.pm[n] * hi_of(lc)
        eal, eah = floor_dec(eal, 35) - F(1, 10 ** 35), ceil_dec(eah, 35) + F(1, 10 ** 35)
        cll, clh = floor_dec(cll, 35) - F(1, 10 ** 35), ceil_dec(clh, 35) + F(1, 10 ** 35)
        assert eal > 0
        hps = ", ".join(f"hp{n}" for n in range(LAM + 1))
        out += (f"  have hEA : ({lean_q(eal)} : ℝ) ≤ EA {LAM} {cq} {yq} {bf} ∧ EA {LAM} {cq} {yq} {bf} ≤ ({lean_q(eah)} : ℝ) := by\n"
                f"    simp only [EA, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]\n"
                f"    rw [{hps}]; constructor <;> linarith\n")
        out += (f"  have hECl : ({lean_q(cll)} : ℝ) ≤ ECl {LAM} {cq} ∧ ECl {LAM} {cq} ≤ ({lean_q(clh)} : ℝ) := by\n"
                f"    simp only [ECl, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]\n"
                f"    rw [{hps}, {', '.join(f'hc{n}' for n in range(LAM + 1))}]; constructor <;> linarith\n")
        zl, zh = floor_dec(lo_of(self.zeta), 38) - F(1, 10 ** 38), ceil_dec(hi_of(self.zeta), 38) + F(1, 10 ** 38)
        out += (f"  have hz : ({lean_q(zl)} : ℝ) ≤ zetaB {C} ∧ zetaB {C} ≤ ({lean_q(zh)} : ℝ) := by\n"
                f"    unfold zetaB\n    constructor\n"
                f"    · rw [le_div_iff₀ (by norm_num), le_div_iff₀ hL3]; linarith\n"
                f"    · rw [div_le_iff₀ (by norm_num), div_le_iff₀ hL3]; linarith\n")
        out += (f"  have hP1 := mul_mem (x := 1 - zetaB {C}) (xl := 1 - {lean_q(zh)}) (xh := 1 - {lean_q(zl)}) "
                f"⟨by linarith, by linarith⟩ hEA (by norm_num) (by norm_num)\n")
        out += f"  have hP2 := mul_mem hz ⟨a{list(P.atoms).index(f'1 + 9 * {Z}')}l, a{list(P.atoms).index(f'1 + 9 * {Z}')}h⟩ (by norm_num) (by norm_num)\n"
        # the six quantities
        pieces = []
        for key, unfold in (("g", "gammaExact H"), ("E", "Epruned H"), ("q", "qExp H"), ("qe", "qEff"), ("qf", "qFill H"),
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
        names = []
        for k in ("g", "E", "q", "qe", "qf", "pre"): names += [f"{k}l", f"{k}h"]
        return f"  obtain ⟨{', '.join(names)}⟩ := b2{self.name}_num\n"

    def ty(self, claims, eps=None):
        C, TH, EPS, Z = self.lits(eps)
        return (f"CertBands2 {LAM} {self.bf} {C} {TH} {EPS} {Z} ({lean_q(F(claims['s0']))}) "
                f"({lean_q(F(claims['b']))}) ({lean_q(F(claims['o']))})")

    def sigma(self, eps=None):
        ts = self.terms(self.eps if eps is None else eps)
        return min(lo_of(t) for t in ts), min(hi_of(t) for t in ts), ts

    def positive(self, claims, doc):
        lo, hi, ts = self.sigma()
        s0, b, o = F(claims["s0"]), F(claims["b"]), F(claims["o"])
        assert lo >= s0 and 2 - s0 <= b and 2 - s0 < o, (self.name, float(lo), claims)
        j = min(range(3), key=lambda i: hi_of(ts[i]))
        U = ceil_dec(hi_of(ts[j]), Q_DIGITS) + F(1, 10 ** Q_DIGITS)
        e = self.eps
        assert U < e / 2 and 1 + e < 2 - U and hi_of(R(e) * (self.E + self.q - R(F(1, 2)))) + U < 1 and hi_of(self.pre) < 2 - U
        out = f"/-- {doc} -/\ntheorem bands2_{self.name} : {self.ty(claims)} := by\n" + self.obtain()
        out += self.cast_lines([self.eps])
        out += f"  apply CertBands2.mk' (U := ({lean_q(U)} : ℝ))\n"
        out += "  all_goals try simp only [ec, eth, ez, eeps0] at *\n"
        out += ("  all_goals first\n    | (norm_num; done)\n    | linarith\n"
                "    | (intro t ht; simp only [b2Terms, List.mem_cons, List.mem_nil_iff, or_false] at ht\n"
                "       rcases ht with rfl | rfl | rfl <;> linarith)\n"
                "    | (left; linarith)\n    | (right; left; linarith)\n    | (right; right; linarith)\n")
        return out

    def negative(self, tag, claims, doc, eps=None):
        lo, hi, ts = self.sigma(eps)
        s0, b, o = F(claims["s0"]), F(claims["b"]), F(claims["o"])
        need = max(s0, 2 - b)
        # some claimed lower bound on sigma must exceed an upper bound of the binding term
        assert hi < need or hi <= 2 - o, (self.name, tag, float(hi), float(need))
        e = self.eps if eps is None else eps
        out = f"/-- {doc} -/\ntheorem bands2_{self.name}_fails_{tag} : ¬ ({self.ty(claims, e)}) := by\n" + self.obtain()
        out += self.cast_lines([e])
        out += ("  intro h\n  have hl := h.lower\n  have hu := h.upper\n"
                "  simp only [ec, eth, ez, eeps0] at hl hu\n"
                "  obtain ⟨hl1, hl2, hl3⟩ := hl\n  obtain ⟨hu1, hu2, hu3⟩ := hu\n  linarith\n")
        return out

HEADER = """import ThreesumLean.Bands2Defs

/-!
# Kernel checks of the Theorem 3 certificate (generated by gen_bands2.py; do not edit)

Tiers W, S, C of Theorem C in proofs/bands.md at the exact rational points of certificates/bands_cert.py (`POINTS`).
Each positive theorem states `CertBands2` (every side condition of bands_cert.py, the saving, the 3SUM exponent and
the strict `O(n^e)` line). Each `*_fails_*` theorem is a negative control, proved false.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

open Real

namespace TS

"""

def ulp(s):
    return F(1, 10 ** len(s.split(".")[1]))

def run():
    pts = {name: {"c": c, "theta": th, "eps": eps, "z": z} for name, c, th, eps, z, _law, _ok in bands_cert.POINTS}
    out = HEADER
    for name, spec in TIERS.items():
        T = Tier(name, spec, pts[spec["key"]])
        cl = spec["claims"]
        out += T.num_lemma() + "\n" + T.positive(cl, spec["doc"]) + "\n"
        nx = dict(cl); nx["s0"] = str(F(cl["s0"]) + ulp(cl["s0"]))
        nx = {k: (v if k != "s0" else f"{F(cl['s0']) + ulp(cl['s0'])}") for k, v in cl.items()}
        out += T.negative("next_s0", nx, f"Next grid point: s0 + {lean_q(ulp(cl['s0']))} must fail.") + "\n"
        nb = dict(cl); nb["b"] = str(F(cl["b"]) - ulp(cl["b"]))
        out += T.negative("next_b", nb, f"Next grid point: exponent - {lean_q(ulp(cl['b']))} must fail.") + "\n"
        no = dict(cl); no["o"] = str(F(cl["o"]) - ulp(cl["o"]))
        out += T.negative("next_o", no, f"The O(n^e) line one unit lower ({F(cl['o']) - ulp(cl['o'])}) must fail.") + "\n"
        pe = None
        for units in (1, 10, 100, 1000):
            for sgn in (1, -1):
                cand = T.eps + sgn * F(units, T.eps.denominator)
                if pe is None and T.sigma(cand)[1] < F(cl["s0"]): pe, pu = cand, sgn * units
            if pe is not None: break
        out += T.negative("perturbed_eps", cl, f"Perturbed parameter: eps = {pe} (numerator {pu:+d}) must fail.", eps=pe) + "\n"
        lo, hi, _ = T.sigma()
        print(name, "sigma in", float(lo), float(hi), "qe", float(lo_of(T.qe)), "qf", float(lo_of(T.qf)),
              "e_pre", float(hi_of(T.pre)), "margin s0", float(lo - F(cl["s0"])))
    out += "end TS\n"
    open(os.path.join(HERE, "ThreesumLean", "Bands2Points.lean"), "w").write(out)


# --- Bands2Stretch.lean: the stretch law b(len) for len <= 7 as kernel computations -------------------------------
def gen_stretch():
    sys.path.insert(0, os.path.join(HERE))
    D = [-2, -1, 0, 1, 2]
    def wt(d): return 3 - abs(d)
    def dval(l):
        v = 0
        for a in reversed(l): v = a + 3 * v
        return v
    def blocked(ds, x):
        t = ds + [x]; tv = dval(ds)
        return all(dval(t[:p] + t[p + 1:]) != tv for p in range(len(ds)))
    def bcount(k, ds, w):
        if k == 0: return w * sum(wt(x) for x in D if blocked(ds, x))
        return sum(bcount(k - 1, [d] + ds, wt(d) * w) for d in D)
    def L(l): return "[" + ", ".join(str(x) for x in l) + "]"
    def nm(k, l): return f"bc{k}_" + ("nil" if not l else "_".join(("m%d" % -x) if x < 0 else str(x) for x in l))
    LEAF = 4
    out = ['''import ThreesumLean.Bands2Defs

/-!
# The stretch law b(len), len <= 7, by kernel computation (generated by gen_bands2.py; do not edit)

`bnum len = 9^(len + 1) b(len)` (Bands2Defs.lean, the enumeration of certificates/check_bands_stretch.py). Each
kernel `decide` is one `bcount 4` leaf (a few seconds, under 2 GB); larger values are assembled with `bcount_succ'`.
Proofs are elaborated one at a time (`Elab.async false`) so that leaf memory peaks do not add up.
-/

set_option Elab.async false
set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace TS
''']
    for n in range(LEAF + 1):
        out.append(f"theorem bnum_{n} : bnum {n} = {bcount(n, [], 1)} := by decide +kernel\n")
    def node(k, l):
        if k == LEAF:
            out.append(f"theorem {nm(k, l)} : bcount {k} {L(l)} 1 = {bcount(k, l, 1)} := by decide +kernel\n")
            return
        for d in D: node(k - 1, [d] + l)
        kids = ", ".join(nm(k - 1, [d] + l) for d in D)
        out.append(f"theorem {nm(k, l)} : bcount {k} {L(l)} 1 = {bcount(k, l, 1)} := by\n"
                   f"  (rw [show bcount {k} {L(l)} 1 = bcount ({k - 1} + 1) {L(l)} 1 from rfl, bcount_succ', {kids}]) <;> norm_num\n")
    for n in (5, 6, 7):
        node(n, [])
        out.append(f"theorem bnum_{n} : bnum {n} = {bcount(n, [], 1)} := by\n"
                   f"  rw [show bnum {n} = bcount {n} [] 1 from rfl, {nm(n, [])}]\n")
    out.append('''/-- The table bands_cert.py uses (`B_STRETCH`) is the enumeration, for every `len <= 5`. -/
theorem bS_eq : ∀ len < 6, bS len = (bnum len : ℚ) / 9 ^ (len + 1) := by
  intro len h
  interval_cases len
  · rw [bnum_0]; decide +kernel
  · rw [bnum_1]; decide +kernel
  · rw [bnum_2]; decide +kernel
  · rw [bnum_3]; decide +kernel
  · rw [bnum_4]; decide +kernel
  · rw [bnum_5]; decide +kernel

/-- Longer stretches block less: `b(6), b(7) <= b(5)`. With `lam = 8` a stretch has at most 7 outer levels, so
bands_cert.py's `B_STRETCH[min(len, 5)]` bounds every stretch that occurs. -/
theorem bS_long : (bnum 6 : ℚ) / 9 ^ 7 ≤ bS 6 ∧ (bnum 7 : ℚ) / 9 ^ 8 ≤ bS 7 := by
  rw [bnum_6, bnum_7]; decide +kernel

/-- Negative control: the table entry b(5) is not b(4) (the law really changes with the stretch length). -/
theorem bS_five_ne_four : bS 5 ≠ (bnum 4 : ℚ) / 9 ^ 5 := by
  rw [bnum_4]; decide +kernel

end TS
''')
    # kernel leaves go to NLEAF module files that lake builds in parallel; the assembly stays in Bands2Stretch
    NLEAF = 3
    leaves = [x for x in out[1:] if x.rstrip().endswith(":= by decide +kernel") and "bcount" in x or x.startswith("theorem bnum_") and x.rstrip().endswith("decide +kernel")]
    rest = [x for x in out[1:] if x not in leaves]
    for i in range(NLEAF):
        hdr = (f"import ThreesumLean.Bands2Defs\n\n/-! Kernel leaves of Bands2Stretch.lean, part {i + 1} of {NLEAF} "
               f"(generated by gen_bands2.py; do not edit). Each is one `bcount 4` evaluation. -/\n\n"
               f"set_option Elab.async false\nset_option maxRecDepth 100000\n\nnamespace TS\n")
        open(os.path.join(HERE, "ThreesumLean", f"Bands2Leaves{i + 1}.lean"), "w").write(
            "\n".join([hdr] + leaves[i::NLEAF] + ["end TS\n"]))
    head = out[0].replace("import ThreesumLean.Bands2Defs\n", "".join(f"import ThreesumLean.Bands2Leaves{i + 1}\n" for i in range(NLEAF)))
    open(os.path.join(HERE, "ThreesumLean", "Bands2Stretch.lean"), "w").write("\n".join([head] + rest))

if __name__ == "__main__":
    gen_stretch()
    run()
