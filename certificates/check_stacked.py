"""Mechanical check of Lemma 3.2' of proofs/stacked.md (the folded residue instance) against brute force. Standard
library only (the product is formed sparsely, entry by entry over the inner index).

For a piece C_k and a modulus M, the M residue instances of Lemma 3.2 of proofs/derandomisation.md are folded into one
square product: rows (x, a), x in {0..M0}, columns (y, b), y in {0..M0 - 1}, M0 = ceil(sqrt M), inner index (c, z) in
C_k x Z_M, with
    X[(x,a),(c,z)] = [z = w(c,a) + x*M0 (mod M)],   Y[(c,z),(y,b)] = [z = -w(b,c) + y (mod M)].
For a pair (a, b) let r = w(a,b) mod M, x = ceil(r/M0), y = x*M0 - r. Asserted: (XY)[(x,a),(y,b)] = N_M(a,b,k), the
number of c in C_k with M | w(a,b) + w(b,c) + w(c,a), on every slot of random instances (planted zero triangles,
pieces of every size, moduli 1, 2, squares, non-squares and 667 = 23*29); (x, y) inside the matrix; the n^2 wanted
positions distinct. Negative controls, which must give mismatches: no x*M0 shift, and y = r - x*M0 (wrong sign).
Logic only: the cost of the fold is the paper proof in proofs/stacked.md. Usage: python check_stacked.py
"""
import sys as _sys
# These checks rely on assert, which python -O strips; refuse to run there rather than pass silently.
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assert statements")
import math, random, sys

def folded(w_ab, w_bc, w_ca, piece, M, variant="proof"):
    n = len(w_ab); M0 = math.isqrt(M - 1) + 1 if M > 1 else 1   # ceil(sqrt M); M0^2 >= M
    assert M0 * M0 >= M and (M0 - 1) ** 2 < M
    # Sparse 0/1 matrices: Xrows[row] = inner indices with a 1, Ycols[inner] = columns with a 1.
    Xrows, Ycols = {}, {}
    for ci, c in enumerate(piece):
        for x in range(M0 + 1):
            shift = 0 if variant == "no_shift" else x * M0
            for a in range(n):
                Xrows.setdefault(x * n + a, []).append(ci * M + (w_ca[c][a] + shift) % M)
        for y in range(M0):
            for b in range(n):
                Ycols.setdefault(ci * M + (-w_bc[b][c] + y) % M, []).append(y * n + b)
    P = {}
    for row, inner in Xrows.items():
        for u in inner:
            for col in Ycols.get(u, ()):
                P[(row, col)] = P.get((row, col), 0) + 1
    out, seen = {}, set()
    for a in range(n):
        for b in range(n):
            r = w_ab[a][b] % M
            x = -(-r // M0)                          # ceil(r / M0) <= M0 because r <= M - 1 <= M0^2 - 1
            y = (r - x * M0) if variant == "wrong_sign" else x * M0 - r
            if variant == "proof":
                assert 0 <= x <= M0 and 0 <= y < M0 and (x * M0 - y) == r
            if not (0 <= x <= M0 and 0 <= y < M0):
                out[(a, b)] = None; continue
            pos = (x * n + a, y * n + b)
            if variant == "proof":
                assert pos not in seen
            seen.add(pos); out[(a, b)] = P.get(pos, 0)
    return out

def brute(w_ab, w_bc, w_ca, piece, M, a, b):
    return sum(1 for c in piece if (w_ab[a][b] + w_bc[b][c] + w_ca[c][a]) % M == 0)

def run(trials, rng):
    bad = {"proof": 0, "no_shift": 0, "wrong_sign": 0}; slots = 0
    moduli = [1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 16, 23 * 29, 25, 30, 31, 47, 49, 64, 97]
    for _ in range(trials):
        n = rng.randint(2, 7); U = rng.choice([3, 20, 1000])
        rnd = lambda: [[rng.randint(-U, U) for _ in range(n)] for _ in range(n)]
        w_ab, w_bc, w_ca = rnd(), rnd(), rnd()
        if rng.random() < 0.3:                       # plant zero triangles
            for _ in range(n):
                a, b, c = rng.randrange(n), rng.randrange(n), rng.randrange(n)
                w_ab[a][b] = -(w_bc[b][c] + w_ca[c][a])
        s = rng.randint(1, n); pieces = [list(range(i, min(n, i + s))) for i in range(0, n, s)]
        M = rng.choice(moduli)
        for piece in pieces:
            for variant in bad:
                got = folded(w_ab, w_bc, w_ca, piece, M, variant)
                for (a, b), v in got.items():
                    if v != brute(w_ab, w_bc, w_ca, piece, M, a, b): bad[variant] += 1
                    if variant == "proof": slots += 1
    return bad, slots

if __name__ == "__main__":
    trials = int(sys.argv[1]) if len(sys.argv) > 1 else 400
    bad, slots = run(trials, random.Random(2026))
    print(f"Lemma 3.2' folded instance: {slots} slots checked, mismatches {bad['proof']}")
    print(f"negative controls (must be > 0): no x*M0 shift {bad['no_shift']}, wrong sign of y {bad['wrong_sign']}")
    assert bad["proof"] == 0 and bad["no_shift"] > 0 and bad["wrong_sign"] > 0
    print("OK")
