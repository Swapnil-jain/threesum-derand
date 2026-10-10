"""Mechanical check of Lemmas 3.1 and 3.2 of proofs/bands.md (blocking laws for integer keys), exhaustive over every
key and row string for n' <= 6 digits. Exact fractions; standard library only.

For a key kappa in [0, 3^n) and a row string u uniform in [0, 3^n), v = (u + kappa) mod 3^n and d_p = v_p - u_p in
{-2..2}, b(d) = (6 + |d|)/9. For a set S of digit positions and weights X_p >= 0:
  Lemma 3.1 (worst keys):   E_u prod_{p in S} (1 + b(d_p) X_p) <= prod (1 + (22/27) X_p), equal at kappa = 11...1 (base 3);
  Lemma 3.2 (shifted keys): the average of the same over all kappa equals prod (1 + (62/81) X_p).
Negative controls: 62/81 in place of 22/27 must fail for some kappa; a fixed worst kappa must exceed the average.
Usage: python check_bands_carry.py
"""
import sys as _sys
# These checks rely on assert and on the exit status, and python -O strips asserts; refuse to run there.
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assert statements")
import itertools, random, sys
from fractions import Fraction as F
def b(d): return F(6 + abs(d), 9)
def digits(x, n): return [(x // 3 ** p) % 3 for p in range(n)]
def E(kappa, n, S, X):
    tot = F(0)
    for u in range(3 ** n):
        du = digits(u, n); dv = digits((u + kappa) % 3 ** n, n)
        pr = F(1)
        for p in S: pr *= 1 + b(dv[p] - du[p]) * X[p]
        tot += pr
    return tot / 3 ** n
if __name__ == "__main__":
    rnd = random.Random(7); ok = True; ctrlW = False; ctrlT = False
    for n in range(1, 7):
        for trial in range(3):
            S = sorted(rnd.sample(range(n), rnd.randint(1, n)))
            X = {p: F(rnd.randint(1, 30), rnd.randint(1, 7)) for p in S}
            bw = 1; bt = 1; bt_bad = 1
            for p in S: bw *= 1 + F(22, 27) * X[p]; bt *= 1 + F(62, 81) * X[p]
            vals = [E(k, n, S, X) for k in range(3 ** n)]
            mx = max(vals)
            ones = sum(3 ** p for p in range(n))
            ok &= mx <= bw
            avg = sum(vals) / len(vals)
            ok &= avg == bt
            ctrlW |= mx > bt
            ctrlT |= mx > avg
            print(f"n={n} S={S}: max_kappa E = {float(mx):.6g} <= worst bound {float(bw):.6g} "
                  f"(kappa=1..1: {float(E(ones, n, S, X)):.6g}); avg over kappa {float(avg):.6g} == typical {float(bt):.6g}: {avg == bt}")
    print("control (W with 62/81) fails somewhere:", ctrlW, "; control (fixed worst kappa above average):", ctrlT)
    ok &= ctrlW and ctrlT
    assert ok, "a check failed or a control did not fail"
    print("ALL OK")
