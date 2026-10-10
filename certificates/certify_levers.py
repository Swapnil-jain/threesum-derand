"""Certificate for route A (proofs/derandomisation.md, Appendix B): Las Vegas all-edges Exact Triangle with integer
weights, by L independent random primes and a scan only when all L accept. Saving sigma(1/2) = min(eps*gamma,
eps*(1/2 - q), 1 - eps*E) of one thin product with |W| <= n^2/sqrt D, so Las Vegas all-edges ET, and APSP through
the reduction of Appendix C, in n^{3 - sigma(1/2) + o(1)} expected time.
The last line is the deterministic comparison route: all-edges ET by the paper's Thm 17 (single prime, which halves
the saving), then Appendix C. Its s_ET is re-derived from certify.py at the best point of params.json.
Printing uses directed rounding: savings DOWN, exponents UP. Usage: python certify_levers.py
"""
import contextlib, io, json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fractions import Fraction as Fr
from certify import A, gamma, q, E, bmin, arb, certify, down, up, o_exp


def route_A(name, c, th, eps, boxes, enc):
    C, T, e = A(c), A(th), A(eps)
    assert Fr(c) > 10 and 0 < Fr(th) < Fr(9, 10) and Fr(eps) > 0
    tb, tq, te = e*gamma(C, T, boxes), e*(A("1/2") - q(T)), 1 - e*E(C, enc)
    assert tb > 0 and tq > 0 and te > 0
    s = bmin(tb, tq, te); lo = arb(s.lower())
    assert 2 + e < 3 - s          # building n D per instance, n polylog instances
    print(f"{name}: CERTIFIED sigma(1/2) >= {down(lo)}  Las Vegas all-edges ET and APSP (integer weights) "
          f"<= n^({up(3-lo)}+o(1)) = O(n^{o_exp(3-lo)})")
    return lo


if __name__ == "__main__":
    route_A("route A, exact count + pruned encodings", "21.27326", "0.111731", "0.0568461", "exact", "pruned")
    route_A("route A, exact count", "20.78856", "0.112251", "0.0572427", "exact", "full")
    route_A("route A, paper lemmas", "22.21828", "0.112064", "0.0535127", "rho", "full")
    P = json.load(open(os.path.join(HERE, "params.json")))["exact_count_free_density_pruned_encoding"]
    with contextlib.redirect_stdout(io.StringIO()):
        ok, s4 = certify("x", P)
    assert ok
    print(f"comparison, deterministic APSP via Thm 17 all-edges ET + Appendix C: s_ET >= {down(s4)}  APSP <= {up(3 - s4)}")
