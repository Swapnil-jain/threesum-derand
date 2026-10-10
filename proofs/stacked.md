# Folded residue instances: deterministic all-edges Exact Triangle, (min,+) and APSP in O(n^2.995943)

Base result: Alman and Vassilevska Williams, arXiv 2610.06783 ("the paper", AVW). Base route: Theorem A of
`proofs/derandomisation.md` ("Theorem A"), whose notation is used throughout. This note replaces one lemma of it,
Lemma 3.2, and so improves Theorem A(b) and A(c). Certificate: `certificates/stacked_cert.py` (arb, 200 bits, exact
rational points, directed rounding). Mechanical check: `certificates/check_stacked.py`. Lean: `lean/ThreesumLean/
Stacked.lean` and `KClique.lean` check the arithmetic of the certificate (`lean/README.md`).

**Review status.** One internal adversarial review found Lemma 3.2', the way it invokes Theorem O, and the certificate
all correct. It re-checked the decoding of Lemma 3.2' exhaustively for every modulus M <= 5000 and every residue,
recomputed both savings independently, and re-ran the certificate and the mechanical check. The k-Clique corollary (Sec.
3) composes Theorem A' with the paper's own reduction and was not reviewed separately.

## 1. Statement

**Theorem A' (Theorem 1' of the README).** In the model of Theorem A, for either oracle tier and all rational c > 10, 0
< theta < 0.9 and eps > 0 with

    eps (E + gamma - 1/4) < 1,     2 + eps < 3 - sigma,     sigma < eps/2,     where sigma = min(eps gamma, eps (1/2 - q)),

all-edges Exact Triangle, the (min,+)-product and APSP (integer weights in [-n^nu, n^nu], no negative cycle) are solved
deterministically in time n^{3 - sigma + o(1)}. Compared with Theorem A(b), (c), only the first condition differs: it
reads eps (E + gamma) < 1 there.

**Corollary B' (values; exponents rounded up from the exact arb endpoints).** `stacked_cert.py`:

| oracle tier | (c, theta, eps), exact | sigma >= | all-edges ET, (min,+), APSP |
|---|---|---|---|
| paper lemmas | (220136043/10^7, 5613801/(5*10^7), 54758043/10^9) | 0.003760515625 | O(n^{2.996240}) |
| exact count + pruned encoding (after ImprovedExponents secs. 3-4) | (2105675159/10^8, 11196129/10^8, 72821473/(125*10^7)) | 0.004057248470 | O(n^{2.995943}) |

Nine-digit upper ends: 2.996239485 and 2.995942752; Theorem A gives 2.996290105 and 2.996000711.

*The unfolded lemma does not hold at these points.* At both certified points eps E > 1 (the unfolded encoding term
1 - eps E is at most -0.0105 and -0.0099), so Lemma 3.2 of Theorem A cannot be used there, and these exponents rest on
Lemma 3.2' alone. Theorem O itself does not need eps E < 1: its tile fit follows from D <= N^{eps0}.

*3SUM.* Lemma 3.2 belongs to the Exact Triangle route. The 3SUM route of Theorem A already makes one square product
per modulus (its Lemma 2.4), so Theorem A' leaves 3SUM unchanged; 3SUM improves through Theorem C instead
(`proofs/bands.md`).

## 2. Lemma 3.2' (folded instances)

Notation of Theorem A, Sec. 3: pieces C_1, ..., C_h of size at most s, h = ceil(n/s), s = n^{eps/2 + o(1)},
m_max = n^{eps/2 + o(1)}, m_max/s = n^{o(1)}, P_t = O(log n), and N_M(a, b, k) = #{c in C_k : M | S(a, b, c)}.

**Lemma 3.2'.** Under the conditions of Theorem A' and for n large, all the numbers N_M(q), q in Q, can be computed in
time n^{3 - sigma + o(1)}, for each modulus 1 <= M <= m_max P_t.

*Construction.* For a modulus M and a piece C_k, set M0 = ceil(sqrt M) (then M0^2 >= M), D_M = s M and N_M = (M0 + 1) n.
Rows are indexed by (x, a), x in {0, ..., M0}, a in A, and columns by (y, b), y in {0, ..., M0 - 1}, b in B, with zero
columns added up to N_M. The inner index runs over (c, z) in C_k x Z_M, with zeros added up to D_M. Put

    X[(x, a), (c, z)] = [z = w(c, a) + x M0 (mod M)],        Y[(c, z), (y, b)] = [z = -w(b, c) + y (mod M)].

For a pair (a, b) let r = w(a, b) mod M, in [0, M), and x = ceil(r/M0), y = x M0 - r. The wanted set W_k has one
position ((x, a), (y, b)) per pair, so |W_k| <= n^2.

*Correctness.* Since r <= M - 1 <= M0^2 - 1, x <= M0, and y = x M0 - r lies in [0, M0), so every position is inside the
matrix; distinct pairs give distinct positions, because a position names a and b. The entry at the position of (a, b)
counts the c in C_k with w(c, a) + x M0 = -w(b, c) + y (mod M), that is, with w(c, a) + w(b, c) + r = 0 (mod M); each c
contributes at most once, since it fixes z. As r = w(a, b) (mod M), the entry is #{c in C_k : M | S(a, b, c)} =
N_M(a, b, k). In other words, the M residue instances of piece k in Theorem A's Lemma 3.2 (the paper's Theorem 17
instances) share their right matrix up to a shift of the columns, and the decoding x M0 + y of Theorem A's Lemma 2.4
stacks all M of them into one square product.

*Theorem O applies.* Write u = log M/log n and v = log s/log n, so 0 <= u <= u_max = eps/2 + o(1) and v = eps/2 + o(1).
Since log(M0 + 1) >= (1/2) log M, log D_M/log N_M <= (v + u)/(1 + u/2) + o(1). The right side grows with u (the sign of
its derivative is that of 1 - v/2, which is positive), so over the whole range of M it is at most eps/(1 + eps/4) +
o(1). Now eps (E + gamma - 1/4) < 1 is equivalent to eps/(1 + eps/4) < 1/(E + gamma). Fix any eps0 strictly between
these two numbers; then for n large D_M <= N_M^{eps0} for every M at once, and also D_M >= s >= 2. The entries are 0 or
1. So Theorem O applies as stated to every folded instance, in either tier, and its hidden constant depends only on c,
theta and eps0.

*Time.* For each piece Theorem O costs O((N_M^2 D_M^{-gamma} + |W_k| D_M^q) log^2 D_M). Using (M0 + 1)^2 <= (sqrt M +
2)^2 <= 9M:
- boxes: h · 9 M n^2 (s M)^{-gamma} = 9 h n^2 s^{-gamma} M^{1 - gamma}, increasing in M; at M <= m_max P_t = s n^{o(1)}
  this is n^{o(1)} (n/s) n^2 s^{1 - 2 gamma} = n^{3 - eps gamma + o(1)}, the same as the M h separate instances;
- queries: h n^2 (s M)^q <= (n/s) n^2 (s^2 n^{o(1)})^q = n^{3 - eps (1/2 - q) + o(1)}, also the same;
- writing X and Y: h N_M D_M <= n^{o(1)} (n/s) s^{1/2} n s^2 = n^{2 + 3 eps/4 + o(1)}, below n^{3 - sigma} because
  2 + eps < 3 - sigma; computing the positions: O(n^3/s) = n^{3 - eps/2 + o(1)}, below n^{3 - sigma} because
  sigma < eps/2.

With log^2 D_M = n^{o(1)} the total is n^{3 - sigma + o(1)}. ∎ The whole gain is in the encodings, which Theorem O
counts inside N^2 D^{-gamma} and its tile fit: one folded product pays them on a side of sqrt(M) n rather than M
products of side n.

*Proof of Theorem A'.* Lemmas 3.3 to 3.7 of Theorem A use Lemma 3.2 only through its output, the exact numbers N_M(q)
for M <= m_max P_t, and its time bound. Lemma 3.2' has the same output under the conditions of Theorem A', so Lemmas 3.3
to 3.7 and Section 4 of Theorem A hold unchanged, which gives all-edges Exact Triangle, (min,+) and APSP. Corollary O'
serves only the 3SUM route, and no other lemma of the Exact Triangle route refers to D_max or to the shape of the old
instances. ∎

*Mechanical check (`check_stacked.py`; logic only).* The script forms X and Y exactly as above, multiplies them, and
checks each wanted entry against a brute-force count of the c in C_k with M | S(a, b, c): 24746 slots of random
instances with n <= 7, pieces of every size, planted zero triangles, and moduli 1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 16, 25,
30, 31, 47, 49, 64, 97 and 667 = 23 · 29 (x = M0 occurs at the squares), with 0 mismatches; positions in range and
distinct are asserted. The negative controls must give mismatches: without the shift x M0 (4478) and with y = r - x M0
(16697).

## 3. Corollaries

Theorem A'(b) gives deterministic all-edges Exact Triangle, and so Exact Triangle detection, in n^{3 - sigma + o(1)}
with sigma >= 0.004057248470 (exact count + pruned encoding) or 0.003760515625 (paper lemmas).

**Corollary E (k-Clique).** For every k >= 3, deterministic Zero-, Min- and Max-Weight k-Clique on n vertices with
integer weights in [-n^nu, n^nu] run in time n^{k - floor(k/3) sigma + o(1)}, so in O(n^{k - 0.004057 floor(k/3)})
(O(n^{k - 0.003760 floor(k/3)}) with the paper lemmas alone).
*Proof.* The paper's Corollary `cor:kclique` applies the Nešetřil-Poljak reduction: n^{k - 3 floor(k/3)} Exact Triangle
instances on N = n^{floor(k/3)} vertices per part, with weights at most N^{O(nu)}; Min- and Max-Weight go through VW13
(Theorem 3.3) with O(log^2 n) calls. With Theorem A'(b) in place of the paper's Exact Triangle algorithm each instance
costs N^{3 - sigma + o(1)} = n^{3 floor(k/3) - floor(k/3) sigma + o(1)}, and the reduction is deterministic. The
printed saving 0.004057 is strictly below sigma, so the n^{o(1)} is absorbed. ∎

Certified exponents (`stacked_cert.py`, rounded up), against the paper's k - 0.0017 floor(k/3) behind its Exact
Triangle bound 2.9983:

| k | 3 | 4 | 5 | 6 | 9 | 12 |
|---|---|---|---|---|---|---|
| exact count + pruned encoding | 2.995943 | 3.995943 | 4.995943 | 5.991886 | 8.987829 | 11.983772 |
| paper lemmas | 2.996240 | 3.996240 | 4.996240 | 5.992479 | 8.988719 | 11.984958 |

*Convolution-3SUM* gains nothing from the fold. It reduces to 3SUM deterministically in linear time, so Theorem C
gives O(n^{1.995790}); going
through Exact Triangle on n^{1/2} vertices would give only 2 - sigma/2 <= 1.997972 (`stacked_cert.py` prints both).

## Credits

- The residue instances are the paper's Theorem 17 instances, as used in Theorem A's Lemma 3.2. The decoding
  x M0 + y is FKP24's set construction, already used in Theorem A's Lemma 2.4. The exact count + pruned encoding
  tier is ImprovedExponents' (its Sections 3 and 4).
- The k-Clique corollary is the paper's `cor:kclique` (Nešetřil and Poljak 1985; VW13 for Min and Max), applied to
  Theorem A'.
- **New here:** folding the M residue instances of one Exact Triangle piece into one square product, and the
  resulting condition eps (E + gamma - 1/4) < 1. We found it in neither the paper, ImprovedExponents nor FKP24.
