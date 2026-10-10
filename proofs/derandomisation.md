# Deterministic 3SUM, all-edges Exact Triangle and APSP at the full thin-product saving

Base result: Alman and Vassilevska Williams, arXiv 2610.06783 ("the paper", AVW). Certificate:
`certificates/derand_cert.py` (arb, 200 bits, directed rounding, exact rational parameters). Mechanical check on
small instances: `certificates/check_derand.py` and `check_derand_controls.py` (Sec. 5).

**Review status.** A sketch of Sections 2 and 3 was checked step by step by one adversarial review, which found no
gap. This complete write-up, including Section 4, then had a second adversarial review. Verdict: **the proof is
correct; no gap that touches the theorem or the exponents.** It asked for one qualifier (c and theta rational) and four
textual fixes (the chain index range in Lemma 2.3, the bound on P_t in Lemma 3.1, the family count in Lemma 3.7, and
the tier names), and it found the mechanical check of the chains too weak; the fixes and its stronger stress test
are applied here.

## 0. Statement

*Model.* Word RAM with words of Theta(log n) bits; every input number is an integer of absolute value at most n^nu,
for a constant nu >= 1 (the paper's setting). Every algorithm below is deterministic, and its time bound holds for
every input.

*Oracle tiers.* Two versions of the oracle (Sec. 1, Theorem O) are used, named by what they rest on:
- "paper lemmas": the paper's Corollary `cor:tradeoff` alone;
- "exact count + pruned encoding (after ImprovedExponents secs. 3-4)": the same proof with the exact leaf count and
  the pruned encodings (Appendix A).

*Saving.* For an oracle tier tau and **rational** constants c > 10, 0 < theta < 0.9, eps > 0, let
gamma = gamma_tau(c, theta), q = q(theta), E = E_tau(c) (Sec. 1, Theorem O) and

    sigma = min( eps*gamma, eps*(1/2 - q) ),   subject to   eps*(E + gamma) < 1.

(The constraint says the encoding term 1 - eps E is larger than eps gamma, so the minimum is the same as
min(eps gamma, eps(1/2 - q), 1 - eps E).) Rationality is needed for the exact-count tier (its proof takes m a
multiple of the denominators of c and theta); for the paper-lemma tier it is harmless. For irrational values the
statement holds with every sigma' < sigma, by approximating (c, theta) by rationals.

**Theorem A.** For every constant nu >= 1, either oracle tier tau, and all rational (c, theta) and eps admissible as
above, on the word RAM above:
- (a) 3SUM (sets A, B, C of at most n integers in [-n^nu, n^nu]; is there a + b = c with a in A, b in B, c in C?)
  is solved deterministically in time n^{2 - sigma + o(1)};
- (b) all-edges Exact Triangle (complete tripartite graph on A, B, C with n vertices each and integer weights in
  [-n^nu, n^nu]; for every (a, b) in A x B, is there c in C with w(a,b) + w(b,c) + w(c,a) = 0?) is solved
  deterministically in time n^{3 - sigma + o(1)};
- (c) the (min,+)-product of two n x n matrices with integer entries in
  [-n^nu, n^nu], and APSP on directed n-vertex graphs with integer weights in [-n^nu, n^nu] and no negative cycle, are
  solved deterministically in time n^{3 - sigma + o(1)}.

**Corollary B (values; exponents rounded up from the exact arb endpoints).** The parameters are exact rationals
(c = 2221832/100000 etc. in `derand_cert.py`), so Theorem A applies to them as stated.

| oracle tier | (c, theta, eps), exact decimals | sigma >= | 3SUM | all-edges ET, (min,+), APSP |
|---|---|---|---|---|
| paper lemmas (Cor. `cor:tradeoff` only) | (22.21832, 0.112064, 0.05351255) | 0.003709895012 | O(n^{1.996291}) | O(n^{2.996291}) |
| exact count + pruned encoding (after ImprovedExponents secs. 3-4; Appendix A) | (21.27327, 0.111731, 0.05684608) | 0.003999289713 | O(n^{1.996001}) | O(n^{2.996001}) |

Nine-digit upper ends: 1.996290105 / 2.996290105 (paper lemmas) and 1.996000711 / 2.996000711 (exact count + pruned
encoding). The n^{o(1)} is absorbed
because each printed exponent is strictly above 2 - sigma (resp. 3 - sigma). The paper's bounds in this model:
3SUM 1.9992, Exact Triangle 2.9983, APSP 2.99942 (its Theorem `thm:3sumapsp`).

The one-set version of 3SUM (a + b + c = 0) reduces to the three-set version in the standard way; that reduction is
not re-proved here.

*Credit.* The reductions are KPP16's (3SUM to offline Set Disjointness, with an AND over O(log n) hashes) and the
paper's (Theorem 17 instances; its conclusion footnote says that KPP16 keeps all of the saving and that APSP can go
through the all-edges version). The interval groups are FKP24 Lemma 3.3, the sets are FKP24's proof of Theorem 1.3,
the prime-at-a-time moduli are FKP24 Lemma 3.2, and counting false positives with the oracle is the paper's footnote
to Theorem 17. The (min,+) to all-edges Exact Triangle chain is VW10/VW18 (simultaneous binary search) plus VW13
(comparisons as equalities); it is also published, Lean-checked, in ImprovedExponents (2026-10-07, Prop.
`minplus-math` and Thm `pairs` of its paper). The exact count + pruned encoding oracle tier is ImprovedExponents' as
well (its Sections 3 and 4: exact leaf count and pruned encodings; Appendix A here).

The chains of Sec. 2 are a known technique applied in a new setting. They follow Chan and Lewenstein's deterministic construction of a pseudo-perfect family (CL15, proof of the
FFT Lemma): hashes made of small primes chosen one at a time, each by averaging over the elements that no earlier hash
has handled; the pattern goes back to greedy covering by conditional expectations (Schmidt and Siegel 1990; AN96
Sec. 4), and Fischer (STOC 2026) uses it recently for a deterministic Exact Triangle subroutine. The authors' footnote
to Theorem 17 suggests choosing the modulus prime by prime with oracle counts. **New here, in Sec. 2:** the per-prime
criterion, which counts the 3-term false positives (pseudo-solutions) of the surviving queries with the #Lop oracle;
this lets the construction replace KPP16's AND without losing any of the saving. **New in Sec. 3:** the all-edges
weight H. Its ingredient, that a nonzero |S| <= 3U is detected by the first t primes because their product exceeds
3U (a Chinese-remainder zero test), is folklore. KPP16 wrote that "it would be surprising if our
construction could be efficiently derandomized"; FKP24 derandomised it with a smaller saving.

## 1. The oracle: wanted entries of a thin product

Notation. H(x) = -x ln x - (1-x) ln(1-x). For c > 10, 0 < theta < 0.9:
- q(theta) = (H(theta) + theta ln 9)/ln 4;
- paper lemmas: gamma = theta ln((c-1)/9)/ln 4, E = (c ln 10 - (c/2) H(1/c) - (c-1) ln 3)/ln 4;
- exact count + pruned encoding: gamma = (c H(1/c) - c H((1-theta)/c) - theta ln 9)/ln 4, E = ((c/2) H(1/c) + (c-1) ln 3)/ln 4.

**Theorem O.** Fix an oracle tier, c, theta, and eps0 with 0 < eps0 < 1/(E + gamma). There is a deterministic algorithm that,
given X in Z^{N x D} and Y in Z^{D x N} with entries of absolute value N^{O(1)}, 2 <= D <= N^{eps0}, and a set W of
positions of an N x N matrix, outputs (XY)[I,J] for all (I,J) in W in time O((N^2 D^{-gamma} + |W| D^q) log^2 D).

*Source.* Paper lemmas: this restates the paper's Corollary `cor:tradeoff` (preprocessing O(N^2 log^2 D / D^gamma), then
O(D^q log D) per entry), since R_c(gamma) = ln 4/(c ln 10 - (c/2)H(1/c) - (c-1) ln 3 + gamma ln 4) = 1/(E + gamma).
Exact count + pruned encoding: the same proof (the paper's Theorem `thm:singletech`) with the two replacements of
Appendix A: (i) the geometric bound on the leaves of order >= t is replaced by the exact count
sum_{d >= t} beta_d <= poly(m) C D^{-gamma} with this tier's gamma (C = K N0^2 outputs per tile; c and theta rational
and m a multiple of their denominators, which changes D by a constant factor; this is why Theorem A takes c and
theta rational); (ii) encodings are computed only for the leaves with at most m symbols P0, at cost
N sqrt(K) N0 = N D^E with this tier's E instead of N 10^L/(sqrt(K) N0). The encoding term
N D^E polylog is at most N^2 D^{-gamma}, because D^{E + gamma} <= N^{eps0 (E + gamma)} and eps0 (E + gamma) < 1
leaves a polynomial margin that absorbs the polylog for large D (for bounded D the claim is trivial). The tile fits
(N >= D^E) for the same reason. The entries need not be 0/1: `thm:singletech` takes integer entries of absolute value
N^{O(1)} directly.

**Corollary O' (the KPP16 shape).** Let eps < eps0 < 1/(E + gamma). Let N = n^{1+o(1)}, D = n^{eps + o(1)} and
|W| <= C N^2/sqrt(D) for a constant C. For n large the hypotheses of Theorem O hold, and the time is
n^{2 - sigma + o(1)}.
*Proof.* log D / log N -> eps < eps0, so D <= N^{eps0} for large n. N^2 D^{-gamma} = n^{2 - eps gamma + o(1)},
|W| D^q <= C N^2 D^{q - 1/2} = n^{2 - eps(1/2 - q) + o(1)}, and log^2 D = n^{o(1)}. ∎

*Admissibility of the certified points.* They are exact rationals, and `derand_cert.py` checks c > 10, 0 < theta < 0.9, eps > 0, the three terms
eps gamma, eps(1/2 - q), 1 - eps E positive, 1 - eps E > eps gamma (so an eps0 strictly between eps and 1/(E + gamma)
exists), and the cost side conditions 1 + eps < 2 - sigma and sigma < eps/2 used below.

## 2. Deterministic 3SUM

Input A, B, C, each of at most n integers in [-U, U], U = n^nu, n >= 3. Write k(a,b,c) = a + b - c, so |k| <= 3U.

*Parameters.* delta = (log2 n)^{-1/2}. P = the primes in [n^delta, 2 n^delta). lambda = 2(nu + 1) ln n.
r = ceil(eps/delta). s = the largest integer with 4 s^2 lambda^r <= n^{delta r}. g = ceil(3n/s).
D_max = (2 n^delta)^r. M_max = ceil(sqrt(D_max)).

**Lemma 2.1 (sizes).** As n -> infinity: n^delta -> infinity, |P| >= n^delta/(2 delta ln n) for large n;
r, |P|, 2^r and lambda^r are n^{o(1)}; s = n^{eps/2 + o(1)}, g = n^{1 - eps/2 + o(1)}, D_max = n^{eps + o(1)}.
*Proof.* n^delta = 2^{sqrt(log2 n)}. The prime number theorem gives pi(2x) - pi(x) ~ x/ln x, so
|P| >= n^delta/(2 ln n^delta) for large n. r <= eps sqrt(log2 n) + 1, so 2^r = n^{o(1)} and
lambda^r = exp(r ln lambda) = exp(O(sqrt(log n) log log n)) = n^{o(1)}; |P| <= 2 n^delta = n^{o(1)}.
n^{delta r} lies in [n^eps, n^{eps + delta}), which is n^{eps + o(1)}; the rest follows. ∎

**Lemma 2.2 (one prime).** Let k != 0 be an integer with |k| <= 3U and let m' >= 1 divide k. Then, for n large, at
most rho |P| primes p in P satisfy m' p | k, where rho := 2 ln(3U)/n^delta <= lambda n^{-delta}.
*Proof.* m' p | k iff p | k/m', and k/m' is a nonzero integer of absolute value at most 3U. If k' primes >= n^delta
divide it, their product is at most 3U, so k' <= ln(3U)/(delta ln n). Divide by |P| >= n^delta/(2 delta ln n).
Finally ln(3U) <= (nu + 1) ln n for n >= 3. ∎

*Step 1 (interval groups; FKP24 Lemma 3.3, adapted).* Let V = A ∪ B ∪ C as a set of distinct values, |V| <= 3n,
sorted. Cut V into g consecutive blocks V_1 < ... < V_g of at most ceil(|V|/g) <= s values each
(max V_i < min V_{i+1}). Put A_i = A ∩ V_i, B_j = B ∩ V_j, C_k = C ∩ V_k, each of size at most s. Call (i,j,k)
trivial if min V_i + min V_j > max V_k or max V_i + max V_j < min V_k, and let R be the set of nontrivial triples.

**Lemma 2.3.** (i) Every solution a + b = c with a in A_i, b in B_j, c in C_k has (i,j,k) in R.
(ii) |R| <= (2g+1)^2. (iii) R is computed in O(n log n + g^2 log g + |R|) time.
*Proof.* (i) min V_i + min V_j <= a + b = c <= max V_k, and max V_i + max V_j >= a + b = c >= min V_k.
(ii) Order triples by (i,j,k) < (i',j',k') iff i < i', j < j', k > k' (the third coordinate reversed). If both are
nontrivial, then 0 <= max V_i + max V_j - min V_k < min V_{i'} + min V_{j'} - max V_{k'} <= 0, using
max V_i < min V_{i'}, max V_j < min V_{j'} and max V_{k'} < min V_k; a contradiction, so each chain of this order
contains at most one nontrivial triple. The (2g - 1)^2 chains {(i, i + u, v - i) : i}, u in {1-g..g-1},
v in {2..2g}, cover [g]^3 ((i,j,k) lies on the chain u = j - i, v = k + i, and i, j, k in [g] put u and v in these
ranges; FKP24 states v in {-g..g}, which misses most triples), and they are chains for the order above. So
|R| <= (2g - 1)^2 <= (2g + 1)^2. (FKP24 states the order with k increasing; its own chains decrease in k, and the
step above needs the reversed order.) (iii) Sort; for each (i,j) the nontrivial k form a contiguous range (both
conditions are monotone in k), found by binary search. ∎

*Queries.* Q = {(a, i, j, k) : (i,j,k) in R, a in A_i}, |Q| <= (2g+1)^2 s <= 9 g^2 s. For a modulus m and
q = (a,i,j,k) in Q let N_m(q) = #{(b, c) in B_j x C_k : m | a + b - c}.

**Lemma 2.4 (one thin product gives N_m on all of Q).** For any m <= D_max, the numbers N_m(q), q in Q, are computed
in time n^{2 - sigma + o(1)} + O(n^{1 + eps + o(1)}) for n large.
*Proof.* Let M0 = ceil(sqrt(m)) <= M_max. Rows (j, x), j in [g], x in {0..M0}; columns (k, y), y in {0..M0 - 1};
inner index u in Z_m; pad with zeros to N = g(M_max + 1) rows and columns and to D_max inner indices. Set
X[(j,x), u] = #{b in B_j : (b + x M0) mod m = u} and Y[u, (k,y)] = #{c in C_k : (c + y) mod m = u}. Then
(XY)[(j,x),(k,y)] = #{(b,c) : b + x M0 ≡ c + y (mod m)}. For q = (a,i,j,k) let r = a mod m in [0, m),
x = ceil(r/M0) <= M0 (as r <= m - 1 <= M0^2 - 1) and y = x M0 - r in [0, M0). Then b + x M0 ≡ c + y iff
a + b ≡ c (mod m), so N_m(q) = (XY)[(j,x(q)),(k,y(q))]. Let W be the set of these positions, |W| <= |Q| <= 9 g^2 s.
Entries are at most s <= N. Sizes: N = g(M_max + 1) = n^{1 + o(1)} (M_max/s = n^{o(1)} by Lemma 2.1),
D_max = n^{eps + o(1)}, and N^2/sqrt(D_max) >= g^2 sqrt(D_max) >= g^2 s, because
D_max >= n^{delta r} >= 4 s^2 lambda^r >= s^2. So |W| <= 9 N^2/sqrt(D_max), and Corollary O' applies. Writing X, Y
densely costs O(N D_max) = n^{1 + eps + o(1)}; computing the positions costs O(|Q|). ∎

*Step 2 (chains).* Let L = ceil(log2(|Q| + 1)) <= 3 log2 n + 5 and S_0 = Q. For l = 1..L:
- m' := 1. For j = 1..r: for every p in P compute Phi(p) = sum over q in S_{l-1} of N_{m'p}(q) (one solve of
  Lemma 2.4 per p); let p_j minimise Phi (ties: smallest p); m' := m' p_j.
- m_l := m', and S_l := {q in S_{l-1} : N_{m_l}(q) >= 1}.

Output YES iff S_L is nonempty. Every modulus used is a product of at most r primes below 2 n^delta, so at most D_max.

**Lemma 2.5 (halving in no-instances).** If the instance has no solution, |S_l| <= |S_{l-1}|/2 for every l.
*Proof.* Fix l and write S = S_{l-1}; let m'_0 = 1 and m'_j = m'_{j-1} p_j. For q in S, every pair counted in
N_{m'_{j-1}}(q) has k = a + b - c != 0 and m'_{j-1} | k, so by Lemma 2.2 at most a rho fraction of the p in P keep
it in N_{m'_{j-1} p}(q). Summing over the pairs and over q in S, the average over p in P of Phi(p) is at most
rho sum_{q in S} N_{m'_{j-1}}(q). The chosen p_j attains the minimum, which is at most the average. By induction
over j, sum_{q in S} N_{m_l}(q) <= rho^r sum_{q in S} N_1(q) <= rho^r s^2 |S|, and
rho^r s^2 <= s^2 lambda^r / n^{delta r} <= 1/4. Every q in S_l has N_{m_l}(q) >= 1, so |S_l| <= |S|/4. ∎

**Lemma 2.6 (correctness).** The output is YES iff the instance has a solution.
*Proof.* If a + b = c, then by Lemma 2.3(i) some q = (a,i,j,k) in Q counts (b, c), and m | 0 for every m, so
N_{m_l}(q) >= 1 for every l and q lies in every S_l. If there is no solution, Lemma 2.5 gives
|S_L| <= |Q| 2^{-L} < 1. ∎

**Lemma 2.7 (time).** n^{2 - sigma + o(1)}.
*Proof.* Step 1: O(n log n + g^2 log g) = n^{2 - eps + o(1)}. Step 2: L r |P| = O(log n) · O(sqrt(log n)) · n^{o(1)}
= n^{o(1)} solves of Lemma 2.4, each n^{2 - sigma + o(1)} + n^{1 + eps + o(1)}, and 1 + eps < 2 - sigma (checked).
The sums over S_{l-1} cost O(|Q|) per solve. The primes of P are found by a sieve up to 2 n^delta = n^{o(1)}. All
numbers are n^{O(1)} (counts at most n^2, sums at most n^5, moduli at most D_max <= n), so O(1) words each. ∎

This proves Theorem A(a). The run is the same on yes- and no-instances (no early exit is needed), and no step uses
randomness: the only choices are the minimisers p_j, which are computed.

*Remarks.* (1) Why the AND survives: Lemma 2.5 bounds the counts only on the survivors S_{l-1}, so chain l works on
what the earlier chains left. Unlike FKP24's single modulus (FKP24 Lemma 3.2, the paper's Theorem 17), which
controls only a total over all queries, the chains keep the AND; those routes lose a constant fraction of sigma.
(2) Prime-at-a-time is essential: choosing each m_l among all primes near sqrt(D_max) would cost n^{eps/2} solves per
choice (+0.028 in the exponent with the exact count + pruned encoding tier).

## 3. Deterministic all-edges Exact Triangle

Input: parts A, B, C of n vertices, weights w in [-U, U], U = n^nu; S(a,b,c) = w(a,b) + w(b,c) + w(c,a), |S| <= 3U.

*The weight.* Let P_1 < ... < P_t be the first t primes, t minimal with P_1 ··· P_t > 3U. For an integer S with
|S| <= 3U put h(S) = #{i : P_i does not divide S}.

**Lemma 3.1.** h(0) = 0, and 1 <= h(S) <= t for S != 0. Moreover t <= log2(3U) + 1 and P_t = O(log n).
*Proof.* Every P_i divides 0. If S != 0 and every P_i divided S, then P_1 ··· P_t would divide S and exceed |S|. The
product of the first t primes is at least 2^t, so t <= log2(3U) + 1. For P_t: by Chebyshev's bound
theta(x) = sum_{p <= x} ln p >= x/2 for x >= x_0, the primes up to x0' = max(x_0, 2 ln(3U) + 1) have product above
3U, so by minimality of t, P_t <= x0' = O(log U) = O(log n). (The bound P_t = O(t log t) from the prime number
theorem would only give O(log n log log n).) Only P_t < n^delta is used below. ∎

*Parameters.* delta, P, lambda as in Sec. 2 (Lemma 2.2 holds verbatim for k = S(a,b,c)). r = ceil(eps/(2 delta)).
s = the largest integer with 2 s t lambda^r <= n^{delta r}. m_max = (2 n^delta)^r. D_max = s m_max P_t.
Pieces: C = C_1 ∪ ... ∪ C_h, |C_k| <= s, h = ceil(n/s). Slots: Q = A x B x [h], |Q| <= n^3. As in Lemma 2.1:
s = n^{eps/2 + o(1)}, m_max = n^{eps/2 + o(1)}, m_max/s = n^{o(1)}, D_max = n^{eps + o(1)}, and P_t < n^delta for
large n, so gcd(P_i, p) = 1 for every p in P.

For a modulus M and a slot q = (a, b, k):
N_M(q) = #{c in C_k : M | S(a,b,c)} and H_M(q) = sum over c in C_k with M | S(a,b,c) of h(S(a,b,c)).

**Lemma 3.2 (one family gives N_M on all slots).** For M <= m_max P_t, the numbers N_M(q), q in Q, are computed in
time n^{3 - sigma + o(1)} for n large.
*Proof (the paper's Theorem 17 instances, without hashing to a prime).* For each residue rho in Z_M and piece k form
the instance with middle part C_k x Z_M (size s M <= D_max, padded to D_max), query set
W_rho = {(a,b) : w(a,b) ≡ rho (mod M)}, and edges a ~ (c, z) iff z ≡ w(c,a) + rho, (c, z) ~ b iff z ≡ -w(b,c)
(mod M). The common neighbours of (a,b) in W_rho are the c in C_k with w(c,a) + w(a,b) ≡ -w(b,c) (mod M), so the
integer product gives N_M(a,b,k) exactly. There are M h instances, each an instance of Theorem O with N = n,
D = D_max <= n^{eps0} (large n). Their total time is
M h · O(n^2 D_max^{-gamma} log^2 D_max) + sum over rho, k of |W_rho| D_max^q log^2 D_max
<= n^{o(1)} (M/s) n^3 D_max^{-gamma} + n^{o(1)} h n^2 D_max^q = n^{3 - eps gamma + o(1)} + n^{3 - eps(1/2 - q) + o(1)},
using M/s <= m_max P_t/s = n^{o(1)} and h = n^{1 - eps/2 + o(1)}. Writing the instances costs
O(M h n D_max) = n^{2 + eps + o(1)}, below n^{3 - sigma} since 1 + eps < 2 - sigma. ∎

**Lemma 3.3 (H from N).** If gcd(M, P_i) = 1 for all i, then H_M(q) = sum_i (N_M(q) - N_{M P_i}(q)).
*Proof.* H_M(q) = sum_i #{c : M | S, P_i does not divide S}, and for coprime M, P_i: (M | S and P_i | S) iff
M P_i | S. ∎ So H_M on all slots costs t + 1 = O(log n) families of Lemma 3.2.

**Lemma 3.4 (one prime, weighted; every instance).** For every slot q and modulus M', the average over p in P of
H_{M'p}(q) is at most rho H_{M'}(q).
*Proof.* A c with S(a,b,c) = 0 contributes h(0) = 0 to both sides. A c with S != 0 and M' | S stays in H_{M'p}(q) for
at most a rho fraction of the p (Lemma 2.2), always with the same weight h(S) >= 0. ∎

*Algorithm.* L = ceil(log2(|Q| + 1)) <= 3 log2 n + 1 and S'_0 = Q. For l = 1..L:
- M' := 1. For j = 1..r: for every p in P compute Psi(p) = sum over q in S'_{l-1} of H_{M'p}(q) (Lemma 3.3 with
  M = M'p, coprime to every P_i); let p_j minimise Psi; M' := M' p_j.
- m_l := M'. Compute N_{m_l} and H_{m_l} on all slots, and S'_l := {q in S'_{l-1} : H_{m_l}(q) >= 1}.

Output: for each (a, b), YES iff some k has N_{m_l}(a,b,k) >= 1 for every l = 1..L. Every modulus used is at most
m_max, and every M P_i at most m_max P_t, as Lemma 3.2 needs.

**Lemma 3.5 (the weighted survivors halve, in every instance).** |S'_l| <= |S'_{l-1}|/2, so S'_L is empty.
*Proof.* By Lemma 3.4 and the greedy choice, as in Lemma 2.5: sum over S'_{l-1} of H_{m_l} is at most
rho^r sum over S'_{l-1} of H_1 <= rho^r s t |S'_{l-1}| (H_1(q) <= |C_k| t), which is at most
(s t lambda^r / n^{delta r}) |S'_{l-1}| <= |S'_{l-1}|/2. Every survivor has H_{m_l} >= 1. Then |S'_L| <= |Q| 2^{-L} < 1. ∎

**Lemma 3.6 (exact all-edges output).** Let T = {q : N_{m_l}(q) >= 1 for all l}. Then q is in T iff C_k contains a c
with S(a,b,c) = 0. Hence the output is the all-edges answer.
*Proof.* If S(a,b,c) = 0 for some c in C_k, every modulus divides 0, so q is in T. Conversely let q contain no zero
triangle and suppose q is in T. By induction q is in S'_l for every l: q is in S'_0; if q is in S'_{l-1}, then
N_{m_l}(q) >= 1 gives a c in C_k with m_l | S(a,b,c) != 0, so H_{m_l}(q) >= h(S) >= 1 (Lemma 3.1) and q is in S'_l.
This contradicts S'_L = ∅ (Lemma 3.5). Finally (a,b) lies in a zero triangle iff the piece of its third vertex gives
a slot in T. ∎

**Lemma 3.7 (time).** n^{3 - sigma + o(1)}.
*Proof.* The greedy choices take L r |P| (t + 1) families (t + 1 per value of H, Lemma 3.3), and computing N_{m_l}
and H_{m_l} on all slots takes t + 2 more per chain, so L r |P| (t + 1) + L (t + 2) = n^{o(1)} families of Lemma 3.2,
each n^{3 - sigma + o(1)}. Sums over the slots cost
O(|Q|) = O(n^3/s) = n^{3 - eps/2 + o(1)} per family, and sigma < eps/2 (checked). ∎

This proves Theorem A(b), with no scans and no witness search. The plain count N_M cannot serve as the potential,
because a slot with a zero triangle never leaves it; H vanishes exactly on zero sums, so the survivors of H halve in
every instance, and the zero slots are recovered from N.

## 4. Deterministic (min,+)-product and APSP from all-edges Exact Triangle (Theorem A(c))

Let T_AE(n, U) be the time of Theorem A(b) for weights in [-U, U]; for U = n^{O(1)} it is n^{3 - sigma + o(1)}.

**Lemma 4.1 (comparisons as equalities; VW13 Theorem 3.3 style; ImprovedExponents Lemma F, Lean
`add_lt_iff_shiftDiff`).** For integers v, t, tau >= 0, with
x_k = floor(x/2^k): v + t < tau iff v + t = tau - 1, or v_k + t_k in {tau_k - 2, tau_k - 3} for some
k < bitlength(max(v,t,tau)).
*Proof.* Soundness: v_k + t_k <= tau_k - 2 gives v + t <= (v_k + t_k + 2) 2^k - 2 <= tau_k 2^k - 2 <= tau - 2.
Completeness: let f(k) = tau_k - 2 - v_k - t_k. If v + t < tau then f(0) >= -1; f(0) = -1 is the first case, and
f(0) in {0, 1} is k = 0. If f(k) >= 2, then floor(f(k)/2) - 1 <= f(k+1) <= f(k)/2, so f(k+1) lies in [0, f(k)), and
the sequence lands in {0, 1} before 2^k exceeds max(v, t, tau), where f = -2. ∎
(Appendix C gives the same reduction with an explicit shift, checked end to end by `check_negtri.py`.)

**Lemma 4.2 (all-pairs negative triangle with thresholds).** Given n x n integer matrices A, B with entries in
[-V, V] and thresholds tau(i,j) in [-2V - 1, 2V + 1], all n^2 answers "is there k with A(i,k) + B(k,j) < tau(i,j)?"
are computed with 2K + 1 all-edges Exact Triangle calls on the same n + n + n vertices, K = bitlength(4V + 1) =
O(log V), weights in [-4V - 2, 4V + 2], plus O(n^2 log V) time.
*Proof.* Put v(i,k) = A(i,k) + V and t(k,j) = B(k,j) + V, both in [0, 2V], and u(i,j) = max(tau(i,j) + 2V, 0) in
[0, 4V + 1]. Since v + t >= 0, A + B < tau iff v + t < u. Apply Lemma 4.1 to (v, t, u) for each triple (all three are
below 2^K): the instance for (k', j') in {0..K-1} x {2, 3} has weights w(i,k) = v_{k'}(i,k), w(k,j) = t_{k'}(k,j),
w(i,j) = j' - u_{k'}(i,j), and the k'-free instance has w(i,j) = 1 - u(i,j), w(i,k) = v, w(k,j) = t. A triple is a
zero triangle of one of them iff v + t < u. The equivalence holds triple by triple, so (i,j) is positive iff it is
positive in at least one of the 2K + 1 all-edges answers. ∎

**Lemma 4.3 ((min,+) by simultaneous binary search; VW10 full version, proof of Theorem 3.2, with the pairs oracle
of Lemma 4.2 in place of its Lemma 3.2, which is where VW lose T(n^{1/3}) n^2).** For n x n integer
matrices with entries in [-V, V], C = A * B (C(i,j) = min_k A(i,k) + B(k,j), in [-2V, 2V]) is computed with
ceil(log2(4V + 1)) calls of Lemma 4.2 on the same n vertices, plus O(n^2 log V) time.
*Proof.* Keep lo(i,j) <= C(i,j) <= hi(i,j), initially -2V and 2V. A round asks, with tau = floor((lo + hi)/2) + 1 (in
[-2V + 1, 2V + 1]), for all pairs at once, whether C(i,j) < tau, and sets hi = tau - 1 or lo = tau. Each round halves
every interval, so after ceil(log2(4V + 1)) rounds lo = hi = C. ∎ Entries +infinity are replaced by Lambda = 4V' + 1
for the bound V' on finite entries; any sum using Lambda exceeds 2V', so results above 2V' are read as +infinity.

**Lemma 4.4 (APSP).** APSP on n vertices with weights in [-n^nu, n^nu] and no negative cycle takes ceil(log2 n)
(min,+) squarings of the matrix with 0 on the diagonal, with finite entries bounded by n^{nu + 1} throughout
(shortest walks of at most n - 1 edges are shortest paths when no cycle is negative); this is the paper's Theorem
`thm:knownred`(b) setting (standard repeated squaring).

*Total.* APSP is O(log n) (min,+) products, each O(log n) rounds of 2K + 1 = O(log n) all-edges ET calls on n vertices
with weights n^{nu + O(1)}: O(log^3 n) T_AE(n, n^{nu + O(1)}) + n^{2 + o(1)} = n^{3 - sigma + o(1)}. The loss is
polylogarithmic, so the exponent 3 - sigma is kept in full. This completes the chain APSP -> (min,+) -> all-pairs
negative triangle (the search of VW10 Theorem 3.2) -> all-edges ET (Lemma 4.1); the same chain is Lean-checked in
ImprovedExponents (`minPlus_allEdges`, `apsp_allEdges`).

## 5. Mechanical check (small instances; logic, not asymptotics)

`check_derand.py` runs the three constructions as written (interval groups, the residue sets of Lemma 2.4 with the
(x, y) decoding asserted, survivor-restricted greedy chains, the weight H through Lemma 3.3 with the identity asserted,
Lemmas 4.1-4.3) against brute force, in two runs.

*Basic run*, chain primes in [20, 40): 3SUM on 300 instances (147 yes), all-edges ET on 120 instances (163 positive
pairs, S'_L empty asserted every time), Lemma 4.1 exhaustively for v, t < 70, tau < 150, and the (min,+) product on
150 instances, all with 0 mismatches. Here two chain primes already exceed 3U, so the modulus test is soon exact and
the greedy choice is barely exercised.

*Stress run*, which exercises it: chain primes in [20, 200), U = 10^5, every input a multiple of 667 = 23 · 29 (or
667 · 31), so the smallest chain primes divide every k and the greedy minimum must avoid them; every chain modulus is
asserted below 0.35 · 3U. It asserts the corrected chain cover of Lemma 2.3(ii), Lemma 2.5 on every chain
(|S_l minus Z| <= |S_{l-1}|/4, Z the queries with a solution; this is the lemma itself on no-instances), Lemma 3.3 at
every chosen modulus, Lemma 3.5 on every chain (|S'_l| <= |S'_{l-1}|/2), S'_L empty, and no zero-free slot in T
(Lemma 3.6): 3SUM on 120 instances (78 yes) and all-edges ET on 60 instances (119 positive pairs), 0 mismatches.

`check_derand_controls.py` gives three negative controls, each of which must fail: Lemma 4.1 without the case
v + t = tau - 1 (900 mismatches); the plain count N as the all-edges potential, which leaves survivors in 33 of 40
instances; and, on the stress instances, choosing each chain prime as the worst of the three smallest primes instead
of the greedy minimum, which gives 373 halving violations and 30 wrong answers out of 120.

## Appendix A. The exact count and pruned encodings

These two improvements to the paper's data structure were found by us independently, but they were published first
(with a Lean formalisation) in github.com/qawbecrdtey/ImprovedExponents (2026-10-07, its Sections 3 and 4); see NOTICE. They are short
arguments on the paper's construction (notation of AVW Sec. 4: D = 4^m, L = cm, t = theta m, N0 = 3^{L-m},
K = C(L, m), Cm = K N0^2 outputs per tile, alpha_d = C(m, d) 9^d, beta_d = C(L, m - d) 9^{L - m + d}).
Take c and theta rational and m a multiple of their denominators, so L and t are integers.

*Exact boxes.* The paper bounds the box work per tile, O(L(m + 1) sum_{d >= t} beta_d), by beta_d <= rho^d Cm with
rho = 9m/(L - m + 1). The ratio beta_{d+1}/beta_d = 9(m - d)/(L - m + d + 1) is at most rho and decreases in d, so
sum_{d >= t} beta_d <= beta_t / (1 - rho), and beta_0 = Cm. With C(L, k) <= e^{L H(k/L)} and
C(L, m) >= e^{L H(m/L)}/(L + 1),

  beta_t / beta_0 = C(L, m - t) 9^t / C(L, m) <= (L + 1) exp(m [c H((1 - theta)/c) - c H(1/c) + theta ln 9])
                  = (L + 1) D^{-gamma_exact},

with gamma_exact(c, theta) = [c H(1/c) - c H((1 - theta)/c) - theta ln 9] / ln 4. The polynomial factor is D^{o(1)}.

*Pruned encoding.* A query reads only leaves of order below t, and a box contains only leaves of order at least t,
and every leaf of order d >= 0 has at most m symbols P0 (AVW `lem:boxes`). So a leaf that has more than m symbols P0
is never needed. Run Yates' algorithm level by level and drop an intermediate entry as soon as its processed prefix
has more than m symbols P0. After k levels at most A(k) 7^{L-k} entries remain, A(k) = sum_{j <= m} C(k, j) 9^{k-j}
(the processed prefixes, 10 options per level of which one is P0, and 7 input positions per unprocessed level).
Since A(k + 1) >= 9 A(k), the stage sizes grow by a factor at least 9/7 per level, so the total work is O(A(L)), and
A(L) = sum_d beta_d <= Cm/(1 - rho). Over the 4N/(sqrt K N0) bands the encodings cost
O(N/(sqrt K N0) · L · K N0^2) = O(L N sqrt K N0) instead of N 10^L / (sqrt K N0), that is D^{E_pruned} with
E_pruned(c) = [(c/2) H(1/c) + (c - 1) ln 3] / ln 4, and the tile fit N >= sqrt K N0 is the same condition.

## Appendix B. Remark: Las Vegas all-edges Exact Triangle by independent primes

Integer weights only (it hashes). Fix pieces of size s = floor(sqrt D / (6 K ln sqrt D)) with
K = floor(log(3 n^nu) / log(sqrt D / 2)) = O(nu/eps). Draw L = ceil(3 log2 n) primes p_1, ..., p_L independently and
uniformly from [sqrt D/2, sqrt D). For each l build the instances of Lemma 3.2 with modulus p_l (middle part
C_k x Z_{p_l}, size <= s p_l <= D, |W| <= n^2/sqrt D). Scan slot (a, b, k) only if all L instances containing it
accept it, and stop a pair's scans once its zero triangle is found.
- *Zero error.* A zero triangle is 0 mod every p_l, so all L instances accept its slot. Every report is verified.
- *False triggers.* For a slot with no zero, each nonzero S has at most K prime factors in the range, and the range
  holds at least sqrt D/(3 ln sqrt D) primes, so one prime accepts it with probability at most
  s K 3 ln sqrt D / sqrt D <= 1/2, over the prime only (worst case over inputs). Independence gives at most 2^{-L}
  <= n^{-3}, so the expected failed-scan cost is at most (n^3/s) n^{-3} s = O(1).
- *Cost.* L · 2 sqrt D · ceil(n/s) = O(n K log^2 n) instances, each n^{2 - sigma + o(1)}; building O(nD) each; reading
  and ANDing the L answers per slot n^3 polylog/sqrt D (below n^{3 - sigma} since sigma < eps/2); successful scans
  at most n^2 s. Total: expected n^{3 - sigma + o(1)} (`certify_levers.py`: O(n^{2.99601}) with the exact count +
  pruned encoding tier), and APSP through Sec. 4 (Lemmas 4.2-4.4).

Credit: this is KPP16's amplification (an AND over independent hashes) applied to the paper's Theorem 17 instances,
a known technique in a new setting. The Monte Carlo version of this exponent already follows from VX20 (Theorem 3.4
with Proposition 3.8, at alpha = beta = 1, gamma = eps, rho = eps/2) and the paper's thin-product theorem; CX24 (footnote 6) sketches the Las
Vegas upgrade of its own random-prime reduction. The new content is only the Las Vegas variant on Theorem 17's thin
instances. Theorem A(b) supersedes it for integers.

## Appendix C. Negative Triangle to all-edges Exact Triangle on the same vertices

The same reduction as Lemmas 4.1-4.2 (VW13, Theorem 3.3), written with the shift tau = 2h - w_ab, the form that
`check_negtri.py` tests end to end; it preserves edges.

Input: integer weights on the three parts, S(a, b, c) = w_ab + w_bc + w_ca, W = max |w|. Goal: for every edge (a, b),
decide whether some c has S(a, b, c) < 0.
- *Shift.* Take h >= W and put v_bc = w_bc + h, t_ca = w_ca + h, tau_ab = 2h - w_ab. Then v, t >= 0, tau >= h >= 0,
  v, t, tau <= 3h, and v + t - tau = S. So v + t < tau iff S < 0. (The shift tau = 2h - w_ab - 1 would test S <= -2
  and miss S = -1: w = (0, 0, -1), h = 1 gives v + t = 1 = tau. `check_negtri.py` keeps this as a negative control.)
- *Identity.* Write x_k = floor(x / 2^k). For integers v, t, tau >= 0:
  v + t < tau iff v + t = tau - 1, or some k >= 0 has v_k + t_k in {tau_k - 2, tau_k - 3}.
- *Soundness.* If v_k + t_k <= tau_k - 2, then v <= (v_k + 1) 2^k - 1 and t <= (t_k + 1) 2^k - 1, so
  v + t <= (v_k + t_k + 2) 2^k - 2 <= tau_k 2^k - 2 <= tau - 2.
- *Completeness.* Assume v + t <= tau - 1 and let f(k) = tau_k - 2 - v_k - t_k. Then f(0) >= -1. If f(0) = -1, then
  v + t = tau - 1; if f(0) is 0 or 1, take k = 0. Otherwise f(0) >= 2. From x/2 - 1/2 <= floor(x/2) <= x/2,
  f(k + 1) <= f(k)/2 and f(k + 1) >= (f(k) - 3)/2, so f(k + 1) >= floor(f(k)/2) - 1 >= 0 while f(k) >= 2, and f
  strictly decreases there. A strictly decreasing sequence of non-negative integers leaves [2, inf), and when it does
  it is 0 or 1. Once 2^k > 3h, f(k) = -2, so the hit occurs at some k < bitlength(3h).
- *Instances.* For k < K = bitlength(3h) and j in {2, 3}: x_ab = j - tau_k(a, b), y_bc = v_k(b, c), z_ca = t_k(c, a),
  so x + y + z = 0 iff v_k + t_k = tau_k - j; plus x_ab = 1 - tau_ab, y = v, z = t. That is 2K + 1 = O(log W)
  Exact Triangle instances on the same parts with weights at most 3h + 3.
- *All-edges.* The equivalence holds for each triple (a, b, c), so (a, b) is in a negative triangle iff it is in a
  zero triangle of some instance: OR the 2K + 1 all-edges answers.

`check_negtri.py` tests the identity exhaustively (all v, t < 2^7, tau in [-4, 260]) and the whole reduction (shift,
instances, exact all-edges ET, OR) against brute force on 33,227 instances, exhaustive 1x1x1 over [-9, 9]^3,
2x2x1 over [-1, 1]^8 and 2x1x1 over [-3, 3]^5, plus random instances up to 5x5x5, with the boundary sums
S = -2, -1, 0 asserted present; the shift tau = 2h - w_ab - 1 must fail, and does.
