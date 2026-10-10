"""Shared arb (ball arithmetic) closed forms, and the certificate of the paper's own Exact Triangle route.

Closed forms (all logs natural, D = 4^m = N^eps; proofs/derandomisation.md, Appendix A):
  gamma_rho(c,th)   = th ln((c-1)/9)/ln4                                  box saving, the paper's Cor. tradeoff
  gamma_exact(c,th) = [c H(1/c) - c H((1-th)/c) - th ln9]/ln4             box saving, exact box count
  q(th)             = [H(th) + th ln9]/ln4                                query exponent, the paper's Cor. tradeoff
  E_full(c)         = [c ln10 - (c/2) H(1/c) - (c-1) ln3]/ln4             encoding exponent, the paper's eq. (Rc)
  E_pruned(c)       = [(c/2) H(1/c) + (c-1) ln3]/ln4                      encoding exponent, pruned encoding
  sigma(a) = min(eps*gamma, eps*(a-q), 1 - eps*E)   saving of one thin product with |W| <= N^2/D^a
Run as a script, this certifies the paper's route (Thm 17 -> Thm 21) at the points of params.json:
  s_ET = min(sigma - eps*eta, eps*eta) with 2a-1 <= eta <= a;  3SUM <= 2 - s_ET/2,  APSP <= 3 - s_ET/3.
That route keeps half of sigma; it is printed for comparison only (its re-tune was public first, see NOTICE).
A point is accepted only if every side condition holds on the whole ball. Usage: python certify.py [params.json]
"""
import json, math, os, sys
from fractions import Fraction as Fr
from flint import arb, ctx, fmpq
ctx.prec = 200
HERE = os.path.dirname(os.path.abspath(__file__))


def A(x):
    """Exact rational ball from a decimal or fraction string."""
    q = Fr(x); return arb(fmpq(q.numerator, q.denominator))


LN = lambda x: x.log()
def H(x): return -x*LN(x) - (1-x)*LN(1-x)
L4 = LN(A(4)); L9 = LN(A(9)); L3 = LN(A(3)); L10 = LN(A(10)); L7_2 = LN(A(7))/LN(A(2))
def gamma(c, th, kind):
    if kind == "rho": return th*LN((c-1)/9)/L4
    return (c*H(1/c) - c*H((1-th)/c) - th*L9)/L4
def q(th): return (H(th) + th*L9)/L4
def E(c, kind):
    if kind == "full": return (c*L10 - c*H(1/c)/2 - (c-1)*L3)/L4
    return (c*H(1/c)/2 + (c-1)*L3)/L4


# Directed rounding for printed bounds: savings (lower bounds) are rounded DOWN and exponents (upper bounds) UP.
# arb.str rounds to nearest, which can print an upper bound below its true value, so it is never used for a bound.
def exact(x):
    """Exact rational value of a radius-zero arb, such as an endpoint from .lower() or .upper()."""
    m, e = x.man_exp(); return Fr(int(m)) * Fr(2) ** int(e)
def _fmt(k, d):
    s = "-" if k < 0 else ""; k = abs(k); return f"{s}{k // 10**d}.{k % 10**d:0{d}d}"
def down(x, d=9):
    return _fmt(math.floor(exact(x.lower()) * 10**d), d)
def up(x, d=9):
    return _fmt(math.ceil(exact(x.upper()) * 10**d), d)
def o_exp(x, d=5):
    """Smallest d-digit decimal STRICTLY above the upper endpoint of x, so n^{x+o(1)} = O(n^{that})."""
    k = math.floor(exact(x.upper()) * 10**d) + 1
    return _fmt(k, d)
def bmin(*xs):
    """Ball enclosing the minimum: [min of the lower ends, min of the upper ends]."""
    lo = min(x.lower() for x in xs); hi = min(x.upper() for x in xs)
    return arb(lo).union(arb(hi))


def certify(name, P):
    c, th, a, eps, eta = (A(P[k]) for k in ("c", "theta", "a", "eps", "eta"))
    # Rational side conditions are checked in exact fractions (a decimal is not an exact binary ball).
    fc, fth, fa, feps, feta = (Fr(P[k]) for k in ("c", "theta", "a", "eps", "eta"))
    checks = {"c>10": fc > 10, "0<theta<0.9": 0 < fth < Fr(9, 10), "eps>0": feps > 0,
              "eta>=2a-1 (g>=1)": feta >= 2*fa-1, "eta<=a (g<=piece)": feta <= fa, "a<=1": fa <= 1}
    g, qq, e = gamma(c, th, P["boxes"]), q(th), E(c, P["enc"])
    t_box, t_qry, t_enc = eps*g, eps*(a-qq), 1-eps*e
    checks["all three terms > 0"] = (t_box > 0) and (t_qry > 0) and (t_enc > 0)
    sig = bmin(t_box, t_qry, t_enc)
    s = bmin(sig-eps*eta, eps*eta)
    checks["choice of p: log2(7)+3a*eps < 3-s"] = (L7_2 + 3*a*eps) < 3 - s
    checks["building: 2+eps(2-2a+eta) < 3-s"] = (2 + eps*(2-2*a+eta)) < 3 - s
    ok = all(bool(v) for v in checks.values())
    s_lo = arb(s.lower())
    print(f"{name}: {'CERTIFIED' if ok else 'FAILED'}  boxes={P['boxes']} enc={P['enc']}  "
          f"s_ET >= {down(s_lo)}  3SUM <= {up(2-s_lo/2)}  APSP <= {up(3-s_lo/3)}")
    for k, v in checks.items():
        if not v: print("   failed:", k)
    return ok, s_lo


if __name__ == "__main__":
    Ps = json.load(open(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, "params.json")))
    print("The paper's route (Thm 17 single prime, then Thm 21), re-tuned. Comparison only: it keeps half the saving.")
    res = {k: certify(k, v) for k, v in Ps.items()}
    assert all(ok for ok, _ in res.values())
