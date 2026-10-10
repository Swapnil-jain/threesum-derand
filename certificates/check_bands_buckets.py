"""Mechanical check of Section 6 of proofs/bands.md (deterministic residue buckets with heavy-bucket recursion)
against brute force. Standard library only.

Node (A', B', C'): if min(|B'|, |C'|) <= cut, solve directly. Otherwise take the prime p in [g, 2g) minimising
F(p) = (Coll_B(p) + X(p))/|B'| + (Coll_C(p) + X(p))/|C'|, Coll_S = #{(u, v) in S^2 : u = v mod p},
X = #{(b, c) in B' x C' : b = c mod p}. Buckets are residues mod p; a bucket is heavy if it holds more than tau s
elements of B' or of C'. The light instance (A', B'_L, C'_L) is answered through the buckets alone (queries
(a, j) with k = (a + j) mod p; this stands in for the chains and the oracle), and the children are (A', B'_H, C') and
(A', B'_L, C'_H). Asserted: the answer and the set of solutions match brute force, each solution is found at exactly
one node (Lemma 6.1), light buckets hold at most tau s elements, and the shrink inequality of Lemma 6.2 holds. The
check "the chosen F(p) is at most the mean over the primes" is printed too, but the chosen prime is the minimiser, so it
holds by definition; Lemma 6.2's bound on the mean itself is not tested here.
Negative controls: (i) dropping the second child must miss solutions; (ii) the worst prime in place of the best one
must put F(p) above the mean and stall the recursion (no progress, so no termination).
Usage: python check_bands_buckets.py
"""
import sys as _sys
# These checks rely on assert and on the exit status, and python -O strips asserts; refuse to run there.
if not __debug__:
    _sys.exit("refusing to run under python -O: the checks are assert statements")
import random, sys, bisect
def primes_in(lo, hi):
    return [p for p in range(max(2, lo), hi) if all(p % q for q in range(2, int(p ** 0.5) + 1))]
def brute(A, B, C):
    Cs = set(C); return {(a, b, a + b) for a in A for b in B if a + b in Cs}
def coll(S, p):
    cnt = {}
    for v in S: cnt[v % p] = cnt.get(v % p, 0) + 1
    return cnt
STATS = {"nodes": 0, "maxdepth": 0, "shrink_ok": True, "light_ok": True, "mean_ok": True}
def solve(A, B, C, g, tau_s, cut, depth=0, drop_child2=False, worst=False, found=None):
    STATS["nodes"] += 1; STATS["maxdepth"] = max(STATS["maxdepth"], depth)
    assert depth <= 60, "recursion did not terminate"
    if min(len(B), len(C)) <= cut:
        sols = brute(A, B, C)
        for s in sols: found[s] = found.get(s, 0) + 1
        return bool(sols)
    best = None; vals = []
    for p in primes_in(g, 2 * g):
        cb, cc = coll(B, p), coll(C, p)
        CB = sum(x * x for x in cb.values()); CC = sum(x * x for x in cc.values())
        X = sum(cb[r] * cc.get(r, 0) for r in cb)
        Fp = (CB + X) / len(B) + (CC + X) / len(C)
        vals.append(Fp)
        if best is None or (Fp > best[0] if worst else Fp < best[0]): best = (Fp, p, cb, cc, CB, CC, X)
    Fp, p, cb, cc, CB, CC, X = best
    if not worst and Fp > sum(vals) / len(vals) + 1e-9: STATS["mean_ok"] = False
    heavy = {r for r in set(cb) | set(cc) if cb.get(r, 0) > tau_s or cc.get(r, 0) > tau_s}
    BH = [b for b in B if b % p in heavy]; BL = [b for b in B if b % p not in heavy]
    CH = [c for c in C if c % p in heavy]; CL = [c for c in C if c % p not in heavy]
    if len(BH) > (CB + X) / tau_s or len(CH) > (CC + X) / tau_s: STATS["shrink_ok"] = False
    # light instance through the bucket structure only
    bk = {}; ck = {}
    for b in BL: bk.setdefault(b % p, []).append(b)
    for c in CL: ck.setdefault(c % p, set()).add(c)
    if any(len(v) > tau_s for v in bk.values()) or any(len(v) > tau_s for v in ck.values()): STATS["light_ok"] = False
    res = False
    for a in A:
        for j, bl in bk.items():
            k = (a + j) % p
            for b in bl:
                if a + b in ck.get(k, ()):
                    found[(a, b, a + b)] = found.get((a, b, a + b), 0) + 1; res = True
    r1 = solve(A, BH, C, g, tau_s, cut, depth + 1, drop_child2, worst, found) if BH else False
    r2 = False
    if not drop_child2 and CH:
        r2 = solve(A, BL, CH, g, tau_s, cut, depth + 1, drop_child2, worst, found)
    return res or r1 or r2
def instance(kind, n, rnd):
    """Values bounded by U = g^2, so a nonzero difference has at most two prime factors in [g, 2g), as in the proof
    (few window primes divide any difference)."""
    g = max(3, 3 * n // 4); U = g * g; P = primes_in(g, 2 * g)
    if kind == "random":
        return [rnd.randint(-U, U) for _ in range(3 * n)], g
    if kind == "sparse":     # more buckets (s = 1), larger U = g^2: many no-instances
        g = 3 * n; U = 20 * g * g
        return [rnd.randint(-U, U) for _ in range(3 * n)], g
    if kind == "aps":        # B and C built from one AP per window prime. The lists are cut to n elements, so the
                             # later primes' APs are dropped: in 28 of the 40 instances some prime has no heavy bucket.
        out = [rnd.randint(-U, U) for _ in range(n)]
        for part in range(2):
            vals = []
            for p in P:
                v0 = rnd.randint(-U // 2, U // 2); vals += [v0 + p * t for t in range(6)]
            out += (vals + [rnd.randint(-U, U) for _ in range(n)])[:n]
        return out, g
    if kind == "cluster":    # everything in a short window
        return [rnd.randint(0, 3 * g) for _ in range(3 * n)], g
if __name__ == "__main__":
    rnd = random.Random(11); ok = True; miss = 0; tot_yes = 0
    for kind in ("random", "sparse", "aps", "cluster"):
        for it in range(40):
            n = rnd.randint(20, 60)
            vals, g = instance(kind, n, rnd)
            A = sorted(set(vals[:n])); B = sorted(set(vals[n:2 * n])); C = sorted(set(vals[2 * n:]))
            # plant a solution half the time, using a heavy-block element of C when there is one
            if it % 2 == 0 and kind != "sparse" and A and B: C = sorted(set(C) | {A[0] + B[-1]})
            if it % 4 == 1 and kind != "sparse": A = sorted(set(A) | {C[len(C) // 2] - B[0]})
            truth = brute(A, B, C)
            s = 4; tau_s = s; cut = 3
            found = {}
            got = solve(A, B, C, g, tau_s, cut, found=found)
            ok &= got == bool(truth) and set(found) == truth and all(v == 1 for v in found.values())
            tot_yes += bool(truth)
            f2 = {}
            if solve(A, B, C, g, tau_s, cut, drop_child2=True, found=f2) != bool(truth) or set(f2) != truth: miss += 1
    print(f"instances 160, yes {tot_yes}, nodes {STATS['nodes']}, max depth {STATS['maxdepth']}")
    print(f"answers and solution partition: {'OK' if ok else 'FAIL'}; light buckets <= tau s: {STATS['light_ok']}; "
          f"chosen F(p) <= mean: {STATS['mean_ok']}; shrink inequality: {STATS['shrink_ok']}")
    ok &= STATS["light_ok"] and STATS["mean_ok"] and STATS["shrink_ok"]
    print(f"control (drop child 2): {miss} instances with missed or wrong solution sets (must be > 0)")
    ok &= miss > 0
    # Control (ii): take the WORST prime (argmax F) on the same instances. The answers stay correct (Lemma 6.1 does
    # not depend on the choice of p), but the step 'F(p) <= mean' of Lemma 6.2 fails, and with it the shrink bound
    # |B'_H| <= mean_F |B'| / (tau s) that the depth bound uses: the worst prime can leave a child as large as its
    # parent, so the recursion makes no progress (such nodes are counted and finished by brute force).
    W = {"nodes": 0, "above_mean": 0, "shrink_vs_mean_broken": 0, "stalled": 0, "answers_ok": True}
    def solve_w(A, B, C, g, tau_s, cut, depth=0):
        W["nodes"] += 1
        if min(len(B), len(C)) <= cut: return brute(A, B, C)
        vals = []
        for p in primes_in(g, 2 * g):
            cb, cc = coll(B, p), coll(C, p)
            CB = sum(x * x for x in cb.values()); CC = sum(x * x for x in cc.values())
            X = sum(cb[r] * cc.get(r, 0) for r in cb)
            vals.append(((CB + X) / len(B) + (CC + X) / len(C), p, cb, cc))
        mean = sum(v[0] for v in vals) / len(vals)
        Fp, p, cb, cc = max(vals, key=lambda v: v[0])
        if Fp > mean + 1e-9: W["above_mean"] += 1
        heavy = {r for r in set(cb) | set(cc) if cb.get(r, 0) > tau_s or cc.get(r, 0) > tau_s}
        BH = [b for b in B if b % p in heavy]; BL = [b for b in B if b % p not in heavy]
        CH = [c for c in C if c % p in heavy]; CL = [c for c in C if c % p not in heavy]
        if len(BH) > mean * len(B) / tau_s or len(CH) > mean * len(C) / tau_s: W["shrink_vs_mean_broken"] += 1
        if len(BH) == len(B) or len(CH) == len(C):
            # no progress: the recursion would never terminate; count it and finish this node by brute force
            W["stalled"] += 1; return brute(A, B, C)
        sols = brute(A, BL, CL)
        if BH: sols |= solve_w(A, BH, C, g, tau_s, cut, depth + 1)
        if CH: sols |= solve_w(A, BL, CH, g, tau_s, cut, depth + 1)
        return sols
    rnd = random.Random(11)
    for kind in ("random", "sparse", "aps", "cluster"):
        for it in range(40):
            n = rnd.randint(20, 60)
            vals, g = instance(kind, n, rnd)
            A = sorted(set(vals[:n])); B = sorted(set(vals[n:2 * n])); C = sorted(set(vals[2 * n:]))
            if it % 2 == 0 and kind != "sparse" and A and B: C = sorted(set(C) | {A[0] + B[-1]})
            if it % 4 == 1 and kind != "sparse": A = sorted(set(A) | {C[len(C) // 2] - B[0]})
            if solve_w(A, B, C, g, 4, 3) != brute(A, B, C): W["answers_ok"] = False
    print(f"control (ii) worst prime: nodes {W['nodes']}, chosen F(p) above the mean at {W['above_mean']} nodes, "
          f"no-progress nodes (recursion would not terminate) {W['stalled']} (both must be > 0); "
          f"mean-based shrink bound broken at {W['shrink_vs_mean_broken']} nodes (informational: at these sizes the "
          f"mean exceeds tau s, so that bound is vacuous); "
          f"answers still correct: {W['answers_ok']}")
    ok &= W["above_mean"] > 0 and W["stalled"] > 0 and W["answers_ok"]
    assert ok, "a check failed or a control did not fail"
    print("ALL OK")
