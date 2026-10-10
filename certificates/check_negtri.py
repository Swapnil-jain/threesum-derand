"""Checks for Appendix C of proofs/derandomisation.md: Negative Triangle -> all-edges Exact Triangle on the same three parts.

Part 1, the dyadic identity, exhaustive: for integers v, t >= 0 and tau,
  v + t < tau  <=>  v + t = tau - 1, or some k >= 0 has
  floor(v/2^k) + floor(t/2^k) in {floor(tau/2^k) - 2, floor(tau/2^k) - 3}.
Part 2, the FULL reduction end to end. reduce_negtri() builds the ET instances from (w_ab, w_bc, w_ca), including
the weight shift; an exact all-edges ET solver is run on each instance and the answers are ORed per edge (a, b).
That is compared with brute-force all-edges negative-triangle detection on exhaustive and random instances, with
the boundary sums S = -2, -1, 0 present. Part 1 alone cannot catch a wrong shift: the shift is outside the identity.
Negative control: the old shift tau = 2h - w_ab - 1 must FAIL part 2 (it detects S <= -2, so S = -1 is missed).
Usage: python check_negtri.py   (pure Python, a few seconds)"""
import sys as _sys
# These checks rely on assert, which python -O strips; refuse to run there rather than pass silently.
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assert statements")
import itertools, random

def rhs(v, t, tau, K):
    if v + t == tau - 1: return True
    return any(((v >> k) + (t >> k)) in ((tau >> k) - 2, (tau >> k) - 3) for k in range(K))

def check_identity(B=7):
    bad = 0
    for v in range(1 << B):
        for t in range(1 << B):
            for tau in range(-4, (2 << B) + 5):
                K = max(v, t, abs(tau), 1).bit_length() + 3
                if (v + t < tau) != (rhs(v, t, tau, K) if tau >= 0 else False): bad += 1
    return bad

def reduce_negtri(wab, wbc, wca, h=None, old_shift=False):
    """Appendix C. wab[a][b], wbc[b][c], wca[c][a] integers. Returns ET instances (x_ab, y_bc, z_ca) such that edge
    (a, b) lies in a negative triangle iff it lies in a zero triangle (x + y + z = 0) of at least one instance.
    The shift h must satisfy h >= max |w|, so v, t >= 0 and tau >= h >= 0."""
    W = max(abs(x) for M in (wab, wbc, wca) for row in M for x in row)
    h = W if h is None else h
    assert h >= W
    v = [[x + h for x in row] for row in wbc]
    t = [[x + h for x in row] for row in wca]
    # v + t = S - w_ab + 2h, so v + t < tau  <=>  S < tau + w_ab - 2h. The fix is tau = 2h - w_ab (S < 0).
    # The old tau = 2h - w_ab - 1 tests S < -1, i.e. S <= -2, and silently misses S = -1.
    tau = [[2 * h - x - (1 if old_shift else 0) for x in row] for row in wab]
    # f(k) = -2 once 2^k exceeds every v, t, tau (all <= 3h), so k < bitlength(3h) suffices (see the proof).
    K = (3 * h).bit_length()
    inst = [([[1 - x for x in row] for row in tau], v, t)]                   # v + t = tau - 1
    for k in range(K):
        vk = [[x >> k for x in row] for row in v]
        tk = [[x >> k for x in row] for row in t]
        for j in (2, 3):                                                      # v' + t' = tau_k - j
            inst.append(([[j - (x >> k) for x in row] for row in tau], vk, tk))
    return inst

def all_edges_et(x, y, z):
    nA, nB, nC = len(x), len(y), len(z)
    return [[any(x[a][b] + y[b][c] + z[c][a] == 0 for c in range(nC)) for b in range(nB)] for a in range(nA)]

def all_edges_neg(wab, wbc, wca):
    nA, nB, nC = len(wab), len(wbc), len(wca)
    return [[any(wab[a][b] + wbc[b][c] + wca[c][a] < 0 for c in range(nC)) for b in range(nB)] for a in range(nA)]

def via_reduction(wab, wbc, wca, **kw):
    out = None
    for x, y, z in reduce_negtri(wab, wbc, wca, **kw):
        r = all_edges_et(x, y, z)
        out = r if out is None else [[p or q for p, q in zip(ro, rr)] for ro, rr in zip(out, r)]
    return out

def mat(vals, r, c): return [list(vals[i * c:(i + 1) * c]) for i in range(r)]

def instances(rng):
    """Yields (wab, wbc, wca, h). Exhaustive 1x1x1 over [-9, 9]^3 (every S in [-27, 27]); exhaustive 2x2x1 over
    [-1, 1]^8; exhaustive 2x1x1 over [-3, 3]^5; then random 3x3x3 .. 5x5x5 with mixed weight scales and
    shifts h > W."""
    for w in itertools.product(range(-9, 10), repeat=3):
        yield [[w[0]]], [[w[1]]], [[w[2]]], None
    for w in itertools.product(range(-1, 2), repeat=8):              # A=2, B=2, C=1: ab 4, bc 2, ca 2
        yield mat(w[:4], 2, 2), mat(w[4:6], 2, 1), mat(w[6:], 1, 2), None
    for w in itertools.product(range(-3, 4), repeat=5):              # A=2, B=1, C=1: ab 2, bc 1, ca 2
        yield mat(w[:2], 2, 1), mat(w[2:3], 1, 1), mat(w[3:], 1, 2), None
    for _ in range(3000):
        nA, nB, nC = (rng.randint(1, 5) for _ in range(3))
        R = rng.choice((2, 5, 40, 1000))
        g = lambda r, c: [[rng.randint(-R, R) for _ in range(c)] for _ in range(r)]
        wab, wbc, wca = g(nA, nB), g(nB, nC), g(nC, nA)
        W = max(abs(x) for M in (wab, wbc, wca) for row in M for x in row)
        yield wab, wbc, wca, rng.choice((None, W + rng.randint(0, 50)))

def check_reduction(old_shift=False, seed=1):
    rng = random.Random(seed)
    n = bad = 0; seen = set(); first = None
    for wab, wbc, wca, h in instances(rng):
        n += 1
        for a, row in enumerate(wab):
            for b in range(len(row)):
                seen.update(min(wab[a][b] + wbc[b][c] + wca[c][a], 1) for c in range(len(wca)) if
                            -2 <= wab[a][b] + wbc[b][c] + wca[c][a] <= 0)
        if via_reduction(wab, wbc, wca, h=h, old_shift=old_shift) != all_edges_neg(wab, wbc, wca):
            bad += 1; first = first or (wab, wbc, wca, h)
    assert {-2, -1, 0} <= seen, "boundary sums S = -2, -1, 0 must all occur"
    return n, bad, first

if __name__ == "__main__":
    print("dyadic identity, all v, t < 2^7, tau in [-4, 260]: mismatches", check_identity())
    n, bad, _ = check_reduction()
    print(f"full reduction, fixed shift tau = 2h - w_ab: {n} instances, mismatches {bad}")
    n, bad_old, ex = check_reduction(old_shift=True)
    print(f"negative control, old shift tau = 2h - w_ab - 1: {n} instances, mismatches {bad_old}, first {ex}")
    assert bad == 0 and bad_old > 0
    print("OK: fixed reduction exact on every instance; old shift rejected")
