"""Generate ThreesumLean/Points.lean: kernel checks of every arb certificate at its rational point.

For each point it emits
  * rigorous bounds on every log atom (log_mem: a series bound checked by `decide +kernel`),
  * bounds on gamma, q, E (and log 7 / log 2, c H(1/c) / ln 4) derived from the atoms by linarith,
  * the positive theorem: the full certificate structure of ThreesumLean/Certs.lean with the printed claims,
  * negative controls that must FAIL, proved in Lean as negations: the next grid point of the saving, the next
    grid point (down) of the first exponent, a perturbed parameter, and any printed value that is false (none now:
    the scripts round every bound in the safe direction).
arb (python-flint) is used only to choose the rational bounds; Lean checks them. Usage: python gen.py
"""
import math, os, sys
from fractions import Fraction as F
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "certificates"))
from flint import arb, ctx
import certify
from certify import A, gamma as agamma, q as aq, E as aE
ctx.prec = 400

N_SERIES = 110        # series terms per atom: |t| <= 0.415 gives a tail below 1e-42
ATOM_DIGITS = 44      # atom bounds are rounded outward to this many decimals
Q_DIGITS = 34         # derived quantities (gamma, q, E, ...) are rounded outward to this many decimals
L2 = F(693147180559945309417232121458176568075500134, 10 ** 45)
L2LO, L2HI = L2 - F(1, 10 ** 42), L2 + F(1, 10 ** 42)

def lsum(t, n):
    s = F(0)
    for i in range(n):
        s += t ** (i + 1) / (i + 1)
    return s

def lrem(t, n):
    return abs(t) ** (n + 1) / (1 - abs(t))

def lean_q(x):
    x = F(x)
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"

def ex(a):
    m, e = a.man_exp(); return F(int(m)) * F(2) ** int(e)

def lo_of(a): return ex(a.lower())
def hi_of(a): return ex(a.upper())

def floor_dec(x, d): return F(math.floor(x * 10 ** d), 10 ** d)
def ceil_dec(x, d): return F(math.ceil(x * 10 ** d), 10 ** d)

class Param:
    """A parameter given by its decimal string; renders as the unreduced Lean fraction, e.g. 21.178 -> 21178/1000."""
    def __init__(self, s):
        self.s = s; self.v = F(s)
        if "/" in s: self.lean = "(" + s.replace("/", "/") + ")"
        elif "." in s:
            ip, fp = s.split("."); self.lean = f"({int(ip + fp)}/{10 ** len(fp)})"
        else: self.lean = f"({s})"
        self.digits = len(s.split(".")[1]) if "." in s else None

def atom_lines(name, expr, x):
    """log_mem for log(expr), expr = x (a positive rational)."""
    k = round(math.log2(x))
    t = 1 - x / F(2) ** k
    assert abs(t) < F(1, 2), (expr, x)
    S, R = lsum(t, N_SERIES), lrem(t, N_SERIES)
    lo = -S - R + min(k * L2LO, k * L2HI)
    hi = -S + R + max(k * L2LO, k * L2HI)
    lo, hi = floor_dec(lo, ATOM_DIGITS), ceil_dec(hi, ATOM_DIGITS)
    L, Hh = lean_q(lo), lean_q(hi)
    return (f"  obtain ⟨{name}l, {name}h⟩ := log_mem ({expr}) ({lean_q(x)}) ({L}) ({Hh}) ({k}) {N_SERIES} ({L}) ({Hh})\n"
            f"    (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)\n")

class Point:
    """Collects the atoms and derived quantities that one theorem needs."""
    def __init__(self):
        self.atoms = {}; self.qs = []
    def atom(self, expr, x):
        if expr not in self.atoms: self.atoms[expr] = F(x)
    def H(self, expr, x):
        self.atom(expr, x); self.atom(f"1 - ({expr})", 1 - x)
    def quantity(self, term, unfold, L, val):
        self.qs.append((term, unfold, L, val))
    def lines(self):
        out = ""
        for i, (e, x) in enumerate(self.atoms.items()):
            out += atom_lines(f"a{i}", e, x)
        out += "  have hL4 : (0 : ℝ) < log 4 := by linarith\n" if "4" in self.atoms else ""
        out += "  have hL2 : (0 : ℝ) < log 2 := by linarith\n" if "2" in self.atoms else ""
        for i, (term, unfold, L, val) in enumerate(self.qs):
            lo, hi = floor_dec(lo_of(val), Q_DIGITS) - F(1, 10 ** Q_DIGITS), ceil_dec(hi_of(val), Q_DIGITS) + F(1, 10 ** Q_DIGITS)
            u = f"    unfold {unfold}\n" if unfold else ""
            out += (f"  have q{i} : ({lean_q(lo)} : ℝ) ≤ {term} ∧ {term} ≤ ({lean_q(hi)} : ℝ) := by\n{u}"
                    f"    constructor\n    · rw [le_div_iff₀ {L}]; linarith\n    · rw [div_le_iff₀ {L}]; linarith\n")
            out += f"  obtain ⟨q{i}l, q{i}h⟩ := q{i}\n"
        return out

def need_gamma(P, c, th, kind):
    if kind == "rho":
        P.atom(f"({c.lean} - 1) / 9", (c.v - 1) / 9); P.atom("4", 4)
        P.quantity(f"gammaRho {c.lean} {th.lean}", "gammaRho", "hL4", agamma(A(c.s), A(th.s), "rho"))
        return f"(gammaRho {c.lean} {th.lean})"
    P.H(f"1 / {c.lean}", 1 / c.v); P.H(f"(1 - {th.lean}) / {c.lean}", (1 - th.v) / c.v)
    P.atom("9", 9); P.atom("4", 4)
    P.quantity(f"gammaExact {c.lean} {th.lean}", "gammaExact H", "hL4", agamma(A(c.s), A(th.s), "exact"))
    return f"(gammaExact {c.lean} {th.lean})"

def need_q(P, th):
    P.H(th.lean, th.v); P.atom("9", 9); P.atom("4", 4)
    P.quantity(f"qExp {th.lean}", "qExp H", "hL4", aq(A(th.s)))

def need_E(P, c, kind):
    P.H(f"1 / {c.lean}", 1 / c.v); P.atom("3", 3); P.atom("4", 4)
    if kind == "full":
        P.atom("10", 10)
        P.quantity(f"Efull {c.lean}", "Efull H", "hL4", aE(A(c.s), "full")); return f"(Efull {c.lean})"
    P.quantity(f"Epruned {c.lean}", "Epruned H", "hL4", aE(A(c.s), "pruned")); return f"(Epruned {c.lean})"

def bmin(xs): return min(lo_of(x) for x in xs), min(hi_of(x) for x in xs)

# ---------------------------------------------------------------------------------------------------------------
# Certificate kinds. Each returns (lean type string, Point, list of term arb values, S interval (lo, hi), mk' info)

def kind_l1(p, claims):
    c, th, eps, de = (Param(p[k]) for k in ("c", "th", "eps", "de"))
    P = Point(); g = need_gamma(P, c, th, p["boxes"]); need_q(P, th); E = need_E(P, c, p["enc"])
    ac, ath, aeps, ade = A(c.s), A(th.s), A(eps.s), A(de.s)
    gg, ee = agamma(ac, ath, p["boxes"]), aE(ac, p["enc"])
    terms = [ade - aeps * aq(ath), aeps * gg, 1 - aeps * ee, aeps - 2 * ade, 1 - aeps, ade, 1 - ade]
    cl = [claims[k] for k in ("s0", "b3", "bA", "o3", "oA")]
    ty = f"CertL1 {c.lean} {th.lean} {eps.lean} {de.lean} {g} {E} " + " ".join(f"({x})" for x in map(lean_q, cl))
    return ty, P, terms, bmin(terms)

def kind_derand(p, claims):
    c, th, eps = (Param(p[k]) for k in ("c", "th", "eps"))
    P = Point(); g = need_gamma(P, c, th, p["boxes"]); need_q(P, th); E = need_E(P, c, p["enc"])
    ac, ath, aeps = A(c.s), A(th.s), A(eps.s)
    terms = [aeps * agamma(ac, ath, p["boxes"]), aeps * (A("1/2") - aq(ath)), 1 - aeps * aE(ac, p["enc"])]
    cl = [claims[k] for k in ("s0", "b3", "bA", "o3", "oA")]
    ty = f"CertDerand {c.lean} {th.lean} {eps.lean} {g} {E} " + " ".join(f"({x})" for x in map(lean_q, cl))
    return ty, P, terms, bmin(terms)

def kind_et(p, claims):
    c, th, a, eps = (Param(p[k]) for k in ("c", "th", "a", "eps"))
    P = Point(); g = need_gamma(P, c, th, p["boxes"]); need_q(P, th); E = need_E(P, c, p["enc"])
    P.atom("7", 7); P.atom("2", 2)
    ac, ath, aa, aeps = A(c.s), A(th.s), A(a.s), A(eps.s)
    eta = Param(p["eta"]); eta_lean, aeta = eta.lean, A(eta.s)
    ee = aE(ac, p["enc"])
    P.quantity("log 7 / log 2", None, "hL2", certify.L7_2)
    lop = [aeps * agamma(ac, ath, p["boxes"]), aeps * (aa - aq(ath)), 1 - aeps * ee]
    k = aeps * aeta
    # s = min(sigma - k, k): as a list of 'terms' for the generator, term j < 3 means lop[j] - k, j = 3 means k
    terms = [t - k for t in lop] + [k]
    cl = [claims[x] for x in ("s0", "b3", "bA")]
    ty = f"CertET {c.lean} {th.lean} {a.lean} {eps.lean} {eta_lean} {g} {E} " + " ".join(f"({x})" for x in map(lean_q, cl))
    return ty, P, terms, bmin(terms)

KINDS = {"l1": kind_l1, "derand": kind_derand, "et": kind_et}
LISTS = {"l1": ("l1Terms", 7), "derand": ("sigTerms", 3), "et": ("etTerms", 3)}
MK = {"l1": "CertL1.mk'", "derand": "CertDerand.mk'", "et": "CertET.mk'"}
# which claim value each 'lower' component bounds S by: S >= f(claim)
LOWER = {"l1": [("s0", lambda v: v), ("b3", lambda v: 2 - v), ("bA", lambda v: 3 - v)],
         "et": [("s0", lambda v: v), ("b3", lambda v: 2 * (2 - v)), ("bA", lambda v: 3 * (3 - v))]}
LOWER["derand"] = LOWER["l1"]
def implied(kind, key, v):
    """Lower bound on S that claim `key = v` asserts, and whether it is strict (the O(n^e) lines)."""
    if kind == "et":
        return {"s0": v, "b3": 2 * (2 - v), "bA": 3 * (3 - v)}[key], False
    return {"s0": v, "b3": 2 - v, "bA": 3 - v, "o3": 2 - v, "oA": 3 - v}[key], key in ("o3", "oA")

def directed(kind, key, v, S):
    """The printed value rounded in the safe direction at the same number of digits."""
    d = len(str(v).split(".")[1])
    if key == "s0": return lean_dec(floor_dec(S[0], d), d)
    need, strict = implied(kind, key, F(0))
    m = need - implied(kind, key, F(1))[0]          # implied(v) = need - m v, so v >= (need - S)/m
    x = (need - S[0]) / m
    r = ceil_dec(x, d)
    if strict and r == x: r += F(1, 10 ** d)
    return lean_dec(r, d)

def lean_dec(x, d):
    k = int(x * 10 ** d); return f"{k // 10 ** d}.{k % 10 ** d:0{d}d}"

def holds(kind, claims, S):
    """Exact check against the arb enclosure of S: True (holds), False (fails), None (undecided)."""
    res = {}
    for k, v in claims.items():
        need, strict = implied(kind, k, F(v))
        lo, hi = S
        if (lo > need) or (lo >= need and not strict): res[k] = True
        elif (hi < need) or (hi <= need and strict): res[k] = False
        else: res[k] = None
    return res

def list_name(kind, p):
    return LISTS[kind][0]

def side_tactics(kind, n, lst):
    mem = "rcases ht with " + " | ".join(["rfl"] * n)
    return (f"  all_goals first\n    | (norm_num; done)\n    | linarith\n"
            f"    | (intro t ht; simp only [{lst}, List.mem_cons, List.mem_nil_iff, or_false] at ht\n"
            f"       {mem} <;> linarith)\n")

def positive(name, kind, p, claims, doc):
    ty, P, terms, S = KINDS[kind](p, claims)
    out = f"/-- {doc} -/\ntheorem {name} : {ty} := by\n" + P.lines()
    n = LISTS[kind][1]
    out += f"  apply {MK[kind]}\n"
    out += side_tactics(kind, n, list_name(kind, p))
    return out

def negative(name, kind, p, claims, key, doc):
    """¬ certificate, refuting claim `key` through the binding term."""
    ty, P, terms, S = KINDS[kind](p, claims)
    need, _ = implied(kind, key, F(claims[key]))
    j = min(range(len(terms)), key=lambda i: hi_of(terms[i]))
    assert hi_of(terms[j]) < need, (name, key, float(hi_of(terms[j])), float(need))
    comp = [x for x, _ in LOWER[kind]].index(key)
    lower, hpick = f"{MK[kind][:-4]}.lower", ["h.1", "h.2.1", "h.2.2"][comp]
    intro = "  intro h\n"
    out = f"/-- {doc} -/\ntheorem {name} : ¬ ({ty}) := by\n" + P.lines() + intro
    out += f"  replace h := {lower} h\n"
    if kind == "et":
        step = "sET_le_k" if j == 3 else f"(sET_le_term {j} (by simp [etTerms]))"
        out += f"  have hm := {hpick}.trans {step}\n"
        if j < 3:
            succ = "List.getElem_cons_succ, " if j > 0 else ""
            out += f"  simp only [etTerms, {succ}List.getElem_cons_zero] at hm\n"
    else:
        lst = list_name(kind, p)
        out += f"  have hm := {hpick}.trans (minl_le_get _ {j} (by simp [{lst}]))\n"
        succ = "List.getElem_cons_succ, " if j > 0 else ""
        out += f"  simp only [{lst}, {succ}List.getElem_cons_zero] at hm\n"
    out += "  linarith\n"
    return out

def ulp_str(v):
    s = str(v); return F(1, 10 ** len(s.split(".")[1])) if "." in s else F(1)

def perturb(kind, p, claims):
    """One parameter moved by one unit in its last printed digit (up to 1000 units) so that the claimed saving
    fails; the move that lowers S most is taken. Returns (param name, new string, units)."""
    _, _, _, S0 = KINDS[kind](p, claims)
    need, _ = implied(kind, "s0", F(claims["s0"]))
    for units in (1, 10, 100, 1000):
        best = None
        for k in p:
            if k in ("boxes", "enc"): continue
            par = Param(p[k]); u = F(1, 10 ** par.digits) if par.digits else F(1, 10 ** 6)
            for sgn in (1, -1):
                v = par.v + sgn * units * u
                if v <= 0: continue
                d = par.digits or 9
                s = f"{v.numerator / v.denominator:.{d}f}" if par.digits else lean_q(v)
                if F(s) != v: s = lean_q(v)
                q = dict(p); q[k] = s
                _, _, terms, S = KINDS[kind](q, claims)
                if S[1] < need and (best is None or S[1] < best[0]): best = (S[1], k, s)
        if best: return best[1], best[2], units
    raise RuntimeError("no perturbation fails")

HEADER = """import ThreesumLean.Certs

/-!
# Kernel checks of the arb certificates (generated by gen.py; do not edit)

Every positive theorem states a full certificate structure (ThreesumLean/Certs.lean) at the script's rational point
with the printed claims. Every `*_fails_*` theorem is a negative control: the same statement at the next grid point,
or at a perturbed parameter, or with a printed value that is false, and Lean proves it is false.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

open Real

namespace TS

"""

def run(specs):
    out, report = HEADER, []
    for sp in specs:
        name, kind, p, claims, doc = sp["name"], sp["kind"], sp["p"], sp["claims"], sp["doc"]
        _, _, _, S = KINDS[kind](p, claims)
        h = holds(kind, claims, S)
        bad = [k for k, v in h.items() if v is False]   # undecided by arb (exact ties): Lean decides
        fixed = {k: (directed(kind, k, claims[k], S) if k in bad else claims[k]) for k in claims}
        for k in bad: report.append((name, k, claims[k], "fails", "->", fixed[k]))
        out += positive(name, kind, p, fixed, doc + (" Printed values replaced by directed rounding: " + ", ".join(bad) + "." if bad else "")) + "\n"
        for k in bad:
            if h[k] is False:
                out += negative(f"{name}_fails_printed_{k}", kind, p, claims, k,
                                f"The printed value {k} = {claims[k]} is false (nearest rounding in the wrong direction).") + "\n"
        # next grid point of the saving, and of the first exponent claim
        s0 = F(fixed["s0"]); u = ulp_str(fixed["s0"])
        g = dict(fixed); g["s0"] = lean_q(s0 + u)
        if holds(kind, g, S)["s0"] is False:
            out += negative(f"{name}_fails_next_s0", kind, p, g, "s0", f"Next grid point: s0 + {lean_q(u)} must fail.") + "\n"
        else: report.append((name, "next s0 grid point still holds (bound not tight)", g["s0"]))
        ek = [k for k in fixed if k != "s0" and not k.startswith("o")][0]
        g = dict(fixed); ue = ulp_str(fixed[ek]); g[ek] = lean_q(F(fixed[ek]) - ue)
        if holds(kind, g, S)[ek] is False:
            out += negative(f"{name}_fails_next_{ek}", kind, p, g, ek, f"Next grid point: {ek} - {lean_q(ue)} must fail.") + "\n"
        else: report.append((name, f"next {ek} grid point still holds (bound not tight)", g[ek]))
        k, s, units = perturb(kind, p, fixed)
        q = dict(p); q[k] = s
        out += negative(f"{name}_fails_perturbed", kind, q, fixed, "s0",
                        f"Perturbed parameter: {k} = {s} ({units} unit(s) in the last digit) must fail.") + "\n"
        report.append((name, "perturbed", f"{k}={s}", units))
    out += "end TS\n"
    open(os.path.join(HERE, "ThreesumLean", "Points.lean"), "w").write(out)
    for r in report: print(*r)

if __name__ == "__main__":
    from specs import SPECS
    run(SPECS)
