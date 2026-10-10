"""Exact segment polynomials of Lemma Y and Rule Z per element (proofs/bands.md, Sec. 10), for bands4_cert.py.

A_Y(lam, n; y)  = average over the n-subsets S of a segment of lam levels and over the digit differences d ~ pi^K on
                  its K = lam - n outer levels (pi = (1, 2, 3, 2, 1)/9 on {-2, ..., 2}, Lemma 3.2) of
                  prod_{p in S} (1 + y b_p), where b_p = P_{t ~ pi}[no outer level p' of the segment below p keeps
                  the key]. With the outer levels below p numbered o_0 < ... < o_{N-1}, the target p' = o_a keeps the
                  key iff d_a + 2 sum_{j=1}^{m} d_{a+j} 3^{j-1} = t 3^m, m = N - 1 - a (Lemma Y).
A_ZY(lam, n; y) = the same average with b_p = 8/9 if p has an outer level below it in the segment, else 1 (zone
                  segments: Rule Z applied to every element).
The fast implementation works in integers (numpy int64, overflow checked) and writes exact fractions. A second,
independent implementation (pure Python, Fraction) tests every target by building the moved member's segment string
and comparing integer values, and must agree on every entry with lam = 8, n <= 3 and lam = 9, n = 4, 5. The checks
are explicit (SystemExit). About 3 minutes on a laptop.
Usage: python bands4_poly.py > bands4_poly.json   (progress and the verdict go to stderr)
"""
import sys as _sys
# For uniformity with the other new scripts, refuse python -O (the checks here do not use assert).
if not __debug__:
    _sys.exit("refusing to run under python -O")
import itertools, json, sys
from fractions import Fraction as Fr
from math import comb
import numpy as np

PIN = [1, 2, 3, 2, 1]                       # 9 * pi(d), d = -2..2


def req(c, msg):
    if not c:
        sys.stderr.write("CHECK FAILED: " + msg + "\n"); raise SystemExit(1)


def blocked_num(D, N):
    """9 * b for an element with N outer levels below it, per digit row of D (int matrix, columns = outer levels)."""
    ok = np.zeros((D.shape[0], 5), dtype=bool)
    for a in range(N):
        m = N - 1 - a
        lhs = D[:, a].copy()
        for j in range(1, m + 1):
            lhs = lhs + 2 * D[:, a + j] * 3 ** (j - 1)
        for ti, t in enumerate(range(-2, 3)):
            ok[:, ti] |= (lhs == t * 3 ** m)
    return ((~ok) * np.array(PIN)[None, :]).sum(axis=1)


def A_Y(lam, n):
    if n == 0:
        return [Fr(1)]
    K = lam - n
    if K:
        D = np.array(list(itertools.product(range(-2, 3), repeat=K)), dtype=np.int64)
        w = np.prod(np.array(PIN)[D + 2], axis=1)
    else:
        D = np.zeros((1, 0), dtype=np.int64); w = np.ones(1, dtype=np.int64)
    bn = {N: (blocked_num(D, N) if N else np.full(D.shape[0], 9, dtype=np.int64)) for N in range(K + 1)}
    tot = [0] * (n + 1)
    for S in itertools.combinations(range(lam), n):
        Np = [sum(1 for o in range(lam) if o not in S and o < p) for p in S]
        e = np.zeros((D.shape[0], n + 1), dtype=np.int64); e[:, 0] = 1
        for N in Np:
            new = e.copy(); new[:, 1:] += e[:, :-1] * bn[N][:, None]; e = new
        for k in range(n + 1):
            s = int((w * e[:, k]).sum())
            req(s < 2 ** 62, "int64 overflow risk")
            tot[k] += s
    den = comb(lam, n) * 9 ** K
    return [Fr(tot[k], den * 9 ** k) for k in range(n + 1)]


def A_ZY(lam, n):
    tot = [Fr(0)] * (n + 1)
    for S in itertools.combinations(range(lam), n):
        cf = [Fr(1)]
        for p in S:
            N = sum(1 for o in range(lam) if o not in S and o < p)
            b = Fr(8, 9) if N else Fr(1)
            cf = [(cf[k] if k < len(cf) else 0) + (b * cf[k - 1] if k >= 1 else 0) for k in range(len(cf) + 1)]
        tot = [tot[k] + cf[k] for k in range(n + 1)]
    return [x / comb(lam, n) for x in tot]


def A_Y_slow(lam, n):
    """Independent: enumerate S, digits and the term vector directly, test every target by integer values."""
    PI = {d: Fr(PIN[d + 2], 9) for d in range(-2, 3)}
    tot = [Fr(0)] * (n + 1)
    for S in itertools.combinations(range(lam), n):
        O = [l for l in range(lam) if l not in S]
        for dig in itertools.product(range(-2, 3), repeat=len(O)):
            wt = Fr(1)
            for x in dig: wt *= PI[x]
            dd = dict(zip(O, dig))
            val = sum(dig[i] * 3 ** i for i in range(len(O)))           # value of w's segment string
            bs = []
            for p in S:
                blk = Fr(0)
                for t in range(-2, 3):
                    moved = False
                    for pp in [o for o in O if o < p]:
                        outer2 = sorted([o for o in O if o != pp] + [p])
                        sym = [t if o == p else dd[o] for o in outer2]
                        if sum(sym[i] * 3 ** i for i in range(len(sym))) == val: moved = True; break
                    if not moved: blk += PI[t]
                bs.append(blk)
            cf = [Fr(1)]
            for b in bs:
                cf = [(cf[k] if k < len(cf) else 0) + (b * cf[k - 1] if k >= 1 else 0) for k in range(len(cf) + 1)]
            tot = [tot[k] + wt * cf[k] for k in range(n + 1)]
    return [x / comb(lam, n) for x in tot]


if __name__ == "__main__":
    out = {}
    for lam in (8, 9):
        for n in range(lam + 1):
            ay = A_Y(lam, n); az = A_ZY(lam, n)
            req(ay[0] == 1 and az[0] == 1, "constant term")
            # sanity: 0 <= coefficient <= C(n, k) (b in [0, 1])
            req(all(0 <= ay[k] <= comb(n, k) for k in range(n + 1)), "coefficient range")
            out[f"Y,{lam},{n}"] = [str(x) for x in ay]
            out[f"ZY,{lam},{n}"] = [str(x) for x in az]
            sys.stderr.write(f"lam={lam} n={n} done\n")
    for lam, ns in ((8, (0, 1, 2, 3)), (9, (4, 5))):
        for n in ns:
            req([str(x) for x in A_Y_slow(lam, n)] == out[f"Y,{lam},{n}"], f"slow != fast at lam={lam} n={n}")
    # One element alone: its law is the stretch law b(len) of Lemma 3.3, len = the outer levels below it, so the
    # linear coefficient of A_Y(8, 1) lies between avg_{i<6} b(i) (b(6), b(7) >= 0) and avg_{i<8} b(min(i, 5)).
    BST = [Fr(1), Fr(62, 81), Fr(538, 729), Fr(4834, 6561), Fr(43498, 59049), Fr(391474, 531441)]
    req(Fr(out["Y,8,1"][1]) <= sum(BST[min(i, 5)] for i in range(8)) / 8, "one-element law above the stretch law of Lemma 3.3")
    req(Fr(out["Y,8,1"][1]) >= sum(BST[min(i, 5)] for i in range(6)) / 8, "one-element law implausibly small")
    sys.stderr.write("ALL OK\n")
    json.dump(out, sys.stdout, indent=0)
