"""Certificate for Theorem C'', the per-element window moves of Lemma Y with a mix of segment lengths
(proofs/bands.md, Sec. 10). Tier (C) only.

Theorem C'' is Theorem C' with two changes: every element of T is tested on its own against every outer level below
it in its segment (Lemma Y; in zone segments, Rule Z for every element), and the segments have lengths 8 and 9 in a
fixed periodic pattern. With pattern = {lam: w} (w the fraction of segments of length lam), Lbar = sum w lam,
n ~ Bin(lam, 1/c), zeta = log_3(2)/(c - 1) and y = 9z:
  q_eff  = [-th ln z + (c/Lbar) sum_lam w_lam E((1 - zeta) ln A_Y(lam, n; y) + zeta ln A_ZY(lam, n; y))]/ln 4
  q_fill = [(c/Lbar) sum_lam w_lam E ln C(lam, n) - (c/2) H(1/c) + H(th) + th ln 9]/ln 4
  e_pre  = eps c (sum_lam w_lam ln(lam + 1)/Lbar + H(1/c))/ln 4
gamma, E, sigma and every other side condition are those of Theorem C (bands_cert.py), plus the packing condition
"a class fits a diagonal": a class must sit whole on one integer diagonal, so ln(class size)/mu < ln K0/mu, i.e.
  (c/Lbar) sum_lam w_lam E ln C(lam, n)  <  (c/2) H(1/c).
It does not follow from q_fill < q_eff (that would need H(th) + th ln 9 >= q_eff ln 4), so it is checked on its own,
with a control that fails it alone. A_Y and A_ZY are the exact fractions of bands4_poly.json (bands4_poly.py).

arb, 200 bits, at exact rational points; savings rounded DOWN, exponents UP. Every check is an explicit test that
sets the verdict, and the final verdict is an assert. The points were found by a float optimiser, which is not part of
the certificate. Usage: python bands4_cert.py
"""
import sys as _sys
# The final verdict uses assert, which python -O strips; refuse to run there rather than pass silently.
if not __debug__:
    _sys.exit("refusing to run under python -O: the certificate's checks are assert statements")
import contextlib, io, json, os, sys
from fractions import Fraction as Fr
from math import comb
import flint
from flint import arb, fmpq
flint.ctx.prec = 200
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)


def R(x):
    x = Fr(x); return arb(fmpq(x.numerator, x.denominator))
LN4, LN9, LN3, LN2 = arb(4).log(), arb(9).log(), arb(3).log(), arb(2).log()
def H(x): return -x * x.log() - (1 - x) * (1 - x).log()
def to_fr(a):
    m, e = a.man_exp(); return Fr(int(m)) * (Fr(2) ** int(e))
def fmt(s, k):
    sign = "-" if s < 0 else ""; s = abs(s); return f"{sign}{s // 10 ** k}.{s % 10 ** k:0{k}d}"
def dec_down(a, k):
    f = to_fr(a.lower()); return fmt((f.numerator * 10 ** k) // f.denominator, k)
def dec_up(a, k):
    f = to_fr(a.upper()); return fmt(-((-f.numerator * 10 ** k) // f.denominator), k)
def o_line(a, k=6):
    """Smallest k-digit decimal strictly above the upper end of a, so n^{a + o(1)} = O(n^{that})."""
    f = to_fr(a.upper()); return fmt((f.numerator * 10 ** k) // f.denominator + 1, k)
def bmin(*xs):
    lo = min(to_fr(x.lower()) for x in xs); hi = min(to_fr(x.upper()) for x in xs)
    return R(lo).union(R(hi))

POLY = {k: [Fr(x) for x in v] for k, v in json.load(open(os.path.join(HERE, "bands4_poly.json"))).items()}

MIX = {"8": "7/10", "9": "3/10"}
C_MIX = {"c": "4203319/200000", "theta": "3679/31250", "eps": "115032221/2000000000", "z": "190589/10000000"}
# name -> point; law Y / zone law ZY are Lemma Y and Rule Z per element; ONE is no sharing, (1 + y)^n (a control).
POINTS = {
    "(C) Lemma Y, segment lengths 8 and 9 (7/10, 3/10)": dict(C_MIX, pattern=MIX, law="Y", zone_law="ZY"),
    "(C) Lemma Y, segment length 8": {"c": "21018799/1000000", "theta": "1176831/10000000",
        "eps": "143775683/2500000000", "z": "190173/10000000", "pattern": {"8": "1"}, "law": "Y", "zone_law": "ZY"},
    "control: no sharing, length 8 (must give Theorem 1's saving)": {"c": "1329579/62500", "theta": "111731/1000000",
        "eps": "56846/1000000", "z": "139761/10000000", "pattern": {"8": "1"}, "law": "ONE", "zone_law": "ONE"},
    "control: eps 1% too large (must FAIL)": dict(C_MIX, eps=str(Fr(C_MIX["eps"]) * Fr(101, 100)), pattern=MIX,
        law="Y", zone_law="ZY", expect="fail"),
    "control: z = 2 (must FAIL)": dict(C_MIX, z="2", pattern=MIX, law="Y", zone_law="ZY", expect="fail"),
    "control: 2/5 of the segments of length 9, filler condition (must FAIL)": dict(C_MIX,
        pattern={"8": "3/5", "9": "2/5"}, law="Y", zone_law="ZY", expect="fail"),
    # fails only "class fits a diagonal": small theta keeps q_fill < q_eff, so that condition is not implied by it
    "control: length 9, theta = 1/50, class too big for a diagonal (must FAIL)": dict(C_MIX, theta="1/50",
        pattern={"9": "1"}, law="Y", zone_law="ZY", expect="fail"),
}
HEADLINE = "(C) Lemma Y, segment lengths 8 and 9 (7/10, 3/10)"
LENGTH8 = "(C) Lemma Y, segment length 8"
CONTROL = "control: no sharing, length 8 (must give Theorem 1's saving)"


def seg_poly(law, lam, n, y):
    if law == "ONE":
        cf = [Fr(comb(n, k)) for k in range(n + 1)]
    else:
        cf = POLY[f"{law},{lam},{n}"]
    return sum(cf[k] * y ** k for k in range(len(cf)))


def certify(name, P):
    c, th, eps, z = (Fr(P[k]) for k in ("c", "theta", "eps", "z"))
    pat = {int(l): Fr(w) for l, w in P["pattern"].items()}
    law, zlaw = P["law"], P["zone_law"]
    chk = {"c>10": c > 10, "0<th<9/10": 0 < th < Fr(9, 10), "eps>0": eps > 0, "0<z<=1": 0 < z <= 1,
           "pattern weights sum to 1": sum(pat.values()) == 1 and all(w > 0 for w in pat.values()),
           "lengths in {8, 9}": set(pat) <= {8, 9}}
    C, TH, EPS, Z = R(c), R(th), R(eps), R(z)
    y = 9 * z; p = 1 / c
    Lbar = sum(w * l for l, w in pat.items())
    zeta = (LN2 / LN3) / (C - 1)
    S_A = arb(0); S_Cl = arb(0); S_9 = arb(0)
    for l, w in pat.items():
        pm = [comb(l, n) * p ** n * (1 - p) ** (l - n) for n in range(l + 1)]
        EA = sum(R(pm[n]) * R(seg_poly(law, l, n, y)).log() for n in range(l + 1))
        EZ = sum(R(pm[n]) * R(seg_poly(zlaw, l, n, y)).log() for n in range(l + 1))
        ECl = sum(R(pm[n]) * arb(comb(l, n)).log() for n in range(l + 1))
        S_A += R(w) * ((1 - zeta) * EA + zeta * EZ); S_Cl += R(w) * ECl; S_9 += R(w) * arb(l + 1).log()
    LB = R(Lbar)
    qe = (-TH * Z.log() + (C / LB) * S_A) / LN4
    qfill = (C / LB * S_Cl - C / 2 * H(1 / C) + H(TH) + TH * LN9) / LN4
    qs = -bmin(-qe, -qfill)
    # class fits a diagonal: arb "<" holds only if the whole left ball lies below the whole right ball (safe side)
    lnclass, lnK0 = C / LB * S_Cl, C / 2 * H(1 / C)
    g = (C * H(1 / C) - C * H((1 - TH) / C) - TH * LN9) / LN4
    e = (C / 2 * H(1 / C) + (C - 1) * LN3) / LN4
    qth = (H(TH) + TH * LN9) / LN4
    t1, t2, t3 = EPS * g, EPS * (R(Fr(1, 2)) - qs), 1 - EPS * e
    sig = bmin(t1, t2, t3)
    epre = EPS * C * (S_9 / LB + H(1 / C)) / LN4
    chk.update({"gamma>0": g > 0, "terms>0": t1 > 0 and t2 > 0 and t3 > 0, "eps(E+gamma)<1": EPS * (e + g) < 1,
                "q*<1/2": qs < R(Fr(1, 2)), "q_fill<q_eff": qfill < qe, "sigma<eps/2": sig < EPS / 2,
                "1+eps<2-sigma": 1 + EPS < 2 - sig, "partial bands": EPS * (e + qth - R(Fr(1, 2))) + sig < 1,
                "e_pre<2-sigma": epre < 2 - sig, "class fits a diagonal": lnclass < lnK0})
    ok = all(bool(v) for v in chk.values())
    print(f"{name}: {'CERTIFIED' if ok else 'FAILED'} at c={c}, th={th}, eps={eps}, z={z}, pattern={P['pattern']}, "
          f"law={law}/{zlaw}")
    for k, v in chk.items():
        if not bool(v): print("   failed:", k)
    print(f"   gamma={g.str(8)} q_eff={qe.str(8)} q_fill={qfill.str(8)} E={e.str(8)}")
    print(f"   class fits a diagonal: ln(class)/mu <= {dec_up(lnclass, 6)} vs ln(K0)/mu >= {dec_down(lnK0, 6)}")
    print(f"   sigma >= {dec_down(sig, 10)}   3SUM exponent <= {dec_up(2 - sig, 9)}   e_pre <= {dec_up(epre, 6)}")
    return ok, sig


def theorem_c_prime_sigma():
    """Theorem C' (bands3_cert.py) at its tier (C) point, as a ball; its own printing is suppressed."""
    import bands3_cert
    from bands_cert import cert
    name, c, th, eps, z, law, zone, _ = bands3_cert.POINTS[0]
    with contextlib.redirect_stdout(io.StringIO()):
        ok, s = cert(name, c, th, eps, z, law, zone)
    return ok, s


if __name__ == "__main__":
    verdicts, res = [], {}
    for name, v in POINTS.items():
        ok, s = certify(name, v); res[name] = s
        if v.get("expect") == "fail":
            print("   (negative control: it must FAIL)", "OK" if not ok else "WRONG"); verdicts.append(not ok)
        else:
            verdicts.append(ok)
    # the no-sharing control must give Theorem 1's saving 0.0039992...
    ctl = res[CONTROL]
    same = ctl > R(Fr(39992, 10 ** 7)) and ctl < R(Fr(39994, 10 ** 7))
    print(f"{CONTROL}: sigma >= {dec_down(ctl, 10)}, in (0.0039992, 0.0039994):", "OK" if same else "WRONG")
    verdicts.append(bool(same))
    from bands_cert import theorem1_sigma
    okc, s_c = theorem_c_prime_sigma()
    verdicts.append(okc)
    s_best = R(to_fr(res[HEADLINE].lower()))                     # the headline: its certified lower end
    s1 = theorem1_sigma()
    beats = all(bool(res[k] > R(to_fr(s_c.upper()))) for k in (HEADLINE, LENGTH8))
    print("Both Lemma Y points beat Theorem C' tier (C):", "OK" if beats else "WRONG")
    verdicts.append(beats)
    print("Comparisons, headline point, ratios rounded DOWN (our lower bound over the other saving's upper end):")
    print(f"   over Theorem C' (sigma <= {dec_up(s_c, 12)}): x{dec_down(s_best / R(to_fr(s_c.upper())), 5)}")
    print(f"   over Theorem 1 (sigma <= {dec_up(s1, 12)}): x{dec_down(s_best / R(to_fr(s1.upper())), 4)}")
    print(f"   over the paper's deterministic 3SUM (eps'/2 = 0.000875): x{dec_down(s_best / R(Fr(875, 10 ** 6)), 3)}")
    print(f"   deterministic 3SUM <= n^({dec_up(2 - s_best, 9)}+o(1)) = O(n^{o_line(2 - s_best)})")
    print(f"   deterministic Convolution-3SUM (linear-time reduction to 3SUM) <= n^({dec_up(2 - s_best, 9)}+o(1))"
          f" = O(n^{o_line(2 - s_best)})")
    assert all(verdicts), "a point did not give its expected verdict"
    print("ALL OK")
