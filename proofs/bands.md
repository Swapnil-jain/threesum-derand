# Deterministic 3SUM in O(n^1.995782): shared leaves in the pruned recursion

Base result: Alman and Vassilevska Williams, arXiv 2610.06783 ("the paper", AVW). Base route: Theorem A of
`proofs/derandomisation.md` ("Theorem A"; its Sections 1 and 2 and Appendix A are used throughout). Certificate:
`certificates/bands_cert.py` for Theorem C, `certificates/bands3_cert.py` for Theorem C' (Sec. 9) and
`certificates/bands4_cert.py` for Theorem C'' (Sec. 10, with the exact polynomials of `bands4_poly.py`) (arb, 200 bits,
exact rational points, directed rounding). Mechanical checks on small cases: `certificates/check_bands_*.py` and
`tests/test_bands_zone.py` (Secs. 8 to 10).

**Review status.** One internal adversarial review checked every lemma below. It re-derived the generating function of
Lemma 2.2 and the blocking laws of Sec. 3, recomputed every certified value with an independent implementation
(agreement to ten digits or more), and confirmed all three tiers of Corollary D, the stretch tier (C) with the fewest
independent checks of the three. It asked for three changes to this material, all applied here: state the cost of
computing the layout (Sec. 4), add check grids on which the moves are really used and run the worst-prime control (Sec.
8), and credit the open lead of ImprovedExponents (Credits). A second internal adversarial review checked Sec. 9 (Lemma
Z and Theorem C'), confirmed it, ran its own toy check of Lemma Z with a control that must fail, and recomputed the
three tiers of Corollary D' with an independent implementation. A third internal adversarial review checked Sec. 10
(Lemma Y, the mixed segment lengths and Theorem C''), confirmed it, built its own segment polynomials by constructing
every moved member's string (they agree exactly with `bands4_poly.json`), recomputed both points of Corollary D'' in
arb, and ran its own end-to-end toy check with mixed segment lengths and three controls that must fail (now
`check_bands_y.py`). It asked for the condition that a class fits a diagonal, now part of Theorem C'' and of the
certificate, and for the limits at the end of Sec. 10 to be stated with their scope, as they are here.

## 0. Statement

*Model.* As in Theorem A: word RAM with words of Theta(log n) bits, every input an integer of absolute value at most
n^nu for a constant nu >= 1. Every algorithm is deterministic, and every time bound holds for every input.

*Parameters.* Rational c > 10, 0 < theta < 9/10, eps > 0 and 0 < z <= 1; segment length lambda = 8; and one of three
blocking laws b (Sec. 3): 22/27 ("worst keys"), 62/81 ("shifted keys") or b(len) ("stretch moves"). Write H(x) =
-x ln x - (1 - x) ln(1 - x), and let gamma and E be the exact-count and pruned-encoding values of Theorem O:

    gamma = [c H(1/c) - c H((1 - theta)/c) - theta ln 9]/ln 4,      E = [(c/2) H(1/c) + (c - 1) ln 3]/ln 4,
    q(theta) = [H(theta) + theta ln 9]/ln 4.

Let n_s be a Binomial(lambda, 1/c) variable, zeta = log_3(2)/(c - 1), and let A(lambda, n; y) be the average over the
n-subsets of a segment defined in Lemma 4.1. Define

    q_eff  = [ -theta ln z + zeta ln(1 + 9z) + (1 - zeta)(c/lambda) E ln A(lambda, n_s; 9z) ] / ln 4,
    q_fill = [ (c/lambda) E ln C(lambda, n_s) - (c/2) H(1/c) + H(theta) + theta ln 9 ] / ln 4,
    q* = max(q_eff, q_fill),       sigma = min( eps gamma, eps (1/2 - q*), 1 - eps E ).

**Theorem C (Theorem 3 of the README without zone moves; Sec. 9 improves it to Theorem C').** Suppose the parameters
satisfy: gamma > 0; the three terms of sigma are positive; eps (E + gamma) < 1; q_fill < q_eff < 1/2; sigma < eps/2;
1 + eps < 2 - sigma; eps (E + q(theta) - 1/2) + sigma < 1; and e_pre < 2 - sigma, where e_pre = eps c (ln 9/lambda +
H(1/c))/ln 4. Then 3SUM (sets A, B, C of at most n integers in [-n^nu, n^nu]; is there a + b = c with a in A, b in B,
c in C?) is solved deterministically in time n^{2 - sigma + o(1)}.

**Corollary D (values; exponents rounded up from the exact arb endpoints).** `bands_cert.py` checks every condition
of Theorem C on the whole arb ball at these exact rational points:

| tier | blocking law | (c, theta, eps, z), exact | sigma >= | 3SUM |
|---|---|---|---|---|
| (W) worst keys, adjacent moves | 22/27 (Lemma 3.1) | (2111519/100000, 115663/1000000, 28628097/500000000, 17187/1000000) | 0.0041432182 | O(n^{1.995857}) |
| (S) shifted keys, adjacent moves | 62/81 (Lemmas 3.2, 3.4) | (65833/3125, 23379/200000, 28691779/500000000, 36571/2000000) | 0.0041883974 | O(n^{1.995812}) |
| (C) shifted keys, stretch moves | b(len) (Lemmas 3.3, 3.4) | (1052341/50000, 1836/15625, 28717589/500000000, 94241/5000000) | 0.0042108435 | O(n^{1.995790}) |

Nine-digit upper ends: 1.995856782, 1.995811603 and 1.995789157. Theorem A gives 1.996000711. With b = 1 (no sharing)
the same formula gives 0.0039992877, Theorem A's saving, at a point that `bands_cert.py` also certifies (a control).
Tier (W) uses neither Lemma 3.3 nor Lemma 3.4 and is the simplest to check. Convolution-3SUM reduces to 3SUM in linear
time, so it is solved deterministically in O(n^{1.995790}) as well.

*Zone moves.* Sec. 9 adds one move in the zone segments, where Theorem C allows none (Rule Z, Lemma Z). It changes
only the zone term of q_eff and improves every tier: Theorem C' and Corollary D' give deterministic 3SUM in
O(n^{1.995786}) (tier (C), upper end 1.995785623), O(n^{1.995809}) (S) and O(n^{1.995854}) (W).

*Window moves per element.* Sec. 10 drops condition (a) and the stretch limit: every element of T is tested on its own
against every outer level below it in its segment (Lemma Y), and the segments have lengths 8 and 9 in a fixed mix.
Theorem C'' and Corollary D'' give deterministic 3SUM in O(n^{1.995782}) (tier (C), upper end 1.995781854).

*Scope.* Theorem C improves 3SUM only. All-edges Exact Triangle and APSP do not gain from it: their query sets (the
sets W_rho of Theorem A's Lemma 3.2) are not unions of translates in the sense of Sec. 2. Their improvement in this
release is a different one (`proofs/stacked.md`).

## Credits

- The pruned recursion and its cost (the paper's Section 2, `lem:prune`), the leaf structure it rests on
  (`sec:whatit`), the tiling (`sec:tiling`), shared encodings (`sec:encoders`), and the bound
  sum_d min(|U| alpha_d, beta_d) that we tighten (`lem:count`) are the paper's. We do not change the recursion; we
  bound the same union of leaves more tightly.
- The exact leaf count and the pruned encodings (the values gamma and E above) are ImprovedExponents'
  (github.com/qawbecrdtey/ImprovedExponents, 2026-10-07, its Sections 3 and 4; Appendix A of `derandomisation.md`). Its
  notes on limits show that a random wanted set gives no saving over the worst-case leaf count, and they name structured
  (Hankel or anti-diagonal) wanted sets as an open lead, not pursued there. This note follows that lead: the suggestion
  to look for a gain in the structure of the wanted set is theirs.
- The 3SUM route is Theorem A's (KPP16's AND, chosen by Chan and Lewenstein's prime-at-a-time averaging with the
  per-prime criterion of Theorem A; FKP24's residue sets in Lemma 2.4). The residue buckets of Sec. 6 replace FKP24's
  interval groups. Choosing a hash prime deterministically by counting collisions goes back to Fredman, Komlós and
  Szemerédi (JACM 1984). The shift of Lemma 3.4 is chosen by the method of conditional expectations (Erdős and
  Selfridge 1973; Spencer 1987; Raghavan 1988). The typical-signature bound uses Hoeffding's inequality (1963).
- **New here:** the canonical-representative bound for shared leaves and its generating function (Lemmas 2.1, 2.2),
  the blocking laws of integer keys (Lemmas 3.1 to 3.3) and the choice of the shift (Lemma 3.4), the layout by
  segment signatures (Sec. 4), the deterministic residue buckets with heavy-bucket recursion (Sec. 6), and the zone
  moves of Rule Z (Sec. 9).

## 1. Where the saving comes from

*Notation (the paper's Section 2; Appendix A of `derandomisation.md`, where mu is written m).* One run of the paper's
recursion has L = c mu levels. Each level of an output string carries an output variable: z_0 at the mu levels of its
inner set Q, and some z_{ij}, i, j in {0, 1, 2}, at each of the L - mu outer levels, where i is a row digit and j a
column digit. D = 4^mu is the inner dimension, N0 = 3^{L - mu}, K = C(L, mu), and a tile computes K0^2 <= K block
products of shape N0 x D x N0, one per inner set. A leaf of the recursion picks one of ten terms at each level: P_0 or
one of the nine P_{ij}. Its *order* is mu minus its number of P_0 symbols.

*Leaves and members.* Let tau be a leaf of order d with P_0 exactly on the set Z (|Z| = mu - d), and let F = [L] \ Z.
For every d-subset T' of F, tau contributes to exactly one output string with inner set Z ∪ T': the one whose outer
variables are the z_{ij} read off tau's terms on F \ T'. Call these C(L - mu + d, d) strings the *members* of tau.
Read from the other side, the order-d leaves of an output string w with inner set Q are given by a d-subset T of Q and
a term P_{i_p j_p} at each p in T (P_0 on Q \ T, and w's terms off Q): alpha_d = C(mu, d) 9^d leaves. In all there are
beta_d = C(L, mu - d) 9^{L - mu + d} leaves of order d.

*The cost of a solve.* Given a set U of wanted output strings in a tile, the paper's pruned recursion visits exactly
the leaves that contribute to some string of U, the union Leaves(U), and the sets it passes down have total size at
most (L + 1)|Leaves(U)| (`lem:prune`). So a tile costs O(L^2 |Leaves(U)|) once the encodings are known. Write
Leaves_d(U) for the leaves of order d. The paper charges |Leaves_d(U)| <= min(|U| alpha_d, beta_d), that is, every
string pays for all of its own leaves at low orders. Theorem A uses the paper's box data structure (Theorem O), which
prepares its boxes before the wanted set is known and so cannot do better. Theorem A's route, however, knows its
wanted set before every solve (Lemma 2.4 lists all its positions), so the pruned recursion can be used in its place.
We then charge:
- orders d >= t = theta mu: beta_d, the exact count of all leaves of that order (this gives the same gamma);
- orders d < t: sum over w in U of R_d(w), where R_d(w) counts only the leaves of w of which w is the canonical
  member (Lemma 2.1). When U is closed under the moves of Sec. 2, this is smaller than alpha_d per string;
- the encodings: the pruned encodings of Appendix A, unchanged (a needed leaf still has at most mu symbols P_0).

## 2. Canonical representatives

*Layout.* A tile is a K0 x K0 grid of block products. Cell (r, c) carries an inner set Q(r, c); different cells carry
different sets, and the grid is the same in every tile (the paper allows any grid with K0^2 <= K). The rows of one row
block are shared by the K0 cells of that block, which have different inner sets, so we index a row's string by
**rank**: its digit of rank k sits, in each cell, at the k-th lowest outer level of that cell's inner set (rank 0 is
the lowest). The ranks below a fixed z0 form the *zone*. They hold the index x of Theorem A's Lemma 2.4 on rows and y
on columns; 3^{z0} >= M_max + 1. Put n' = L - mu - z0. Row blocks are grouped in bands of K0, and the row in band beta,
row block r, with high digits u_k (ranks k >= z0) has the integer label

    j = (beta K0 + r) 3^{n'} + sum_{k >= z0} u_k 3^{k - z0};

column labels k are formed the same way from column bands, blocks c and high digits v_k. A *position* is a pair (row,
column) in one cell, that is, one output string. Its *key* is (k - j, x, y). A *key fibre* is the set of all positions,
over all tiles, with one key, and a set W of positions is *fibre-closed* if it is a union of key fibres.

*Moves.* Fix a position w with cell Q and an order-d leaf tau of w, given by (T, terms). For p in T let G be its *gap*,
the maximal run of consecutive levels of Q containing p, and let l_G be the outer level just below G. The *stretch* of
G is the run of consecutive outer levels that ends at l_G, cut at the next level of Q below and at the boundary of p's
segment (Sec. 4). We say p *can move* to an outer level p' < p if:
- (a) p is the lowest element of T in G;
- (b) p' lies in the stretch of G (an *adjacent* move is the case p' = l_G);
- (c) rank(p') >= z0;
- (d) Q - p + p' is the inner set of a cell of the grid on the same diagonal c - r as Q;
- (e) the member w' = w(T - p + p') of tau has the same key as w.

**Lemma 2.1 (canonical representative).** If W is fibre-closed, then for every tile and every order d,

    |Leaves_d(W_tile)| <= sum over w in W_tile of R_d(w),    R_d(w) = #{(T, terms) of order d : no p in T can move}.

*Proof.* Every leaf in Leaves_d(W_tile) has a member in W. Among its members in W, call the one whose sorted d-set is
lexicographically smallest its *representative*; distinct d-sets give distinct members, so the representative is
unique, and |Leaves_d(W_tile)| is the sum over w of the number of leaves whose representative is w. A leaf is
determined by w together with (T, terms), so it is enough to show: if some p in T can move to p', then w is not the
representative. The level p' is outer for w, so p' lies in F and T - p + p' is a d-subset of F; hence w' is a member
of tau. Its inner set is Z ∪ (T - p + p') = Q - p + p', which by (d) is a cell of the grid on the same diagonal, in the
same tile. Its outer levels are those of w with p' replaced by p. No level of T lies strictly between p' and p: the
levels of G below p are in Q \ T by (a), and the stretch is outer by (b). So no outer level of w' changes rank below
p', which by (c) leaves the zone digits x and y as they are; with (e), w' has the same key as w and lies in W, because W
is fibre-closed. Finally the sorted d-set of w' is that of w with p replaced by the smaller p' in the same place, so it
is lexicographically smaller. ∎

*Adjacent moves.* When p' = l_G, the levels between l_G and p are in Z, so l_G in w and p in w' have the same rank.
The strings of w' agree with those of w except at that rank, where w' carries (i_p, j_p) in place of w's digits there.
The cell of w' is on the same diagonal, so the cell parts of the labels cancel as before, and (e) holds if and only if
j_p - i_p = d_{l_G} as integers, where d_l is the column digit minus the row digit of w at the rank of l.

**Lemma 2.2 (generating function).** Fix w. For p in a gap G, let b_p be the fraction of the nine terms at p for
which p, as the lowest element of T in G, cannot move (b_p = 1 if no move is available). Then b_p depends only on w
and p, and

    R_d(w) = [z^d] prod over the gaps G of P_G(z),     P_G(z) = 1 + sum over p in G of 9 b_p z (1 + 9z)^{#(G above p)}.

If b_p = b for every p in G, then P_G(z) = 1 + b((1 + 9z)^{|G|} - 1). In particular R_d(w) <= z^{-d} prod_G P_G(z) for
every z > 0.
*Proof.* Whether p can move is decided by (a) to (e). Given (a), the levels of G below p carry P_0 whatever T is, and
the stretch below G holds no level of Q. So the moved member depends only on w, p and the term at p, and so does b_p.
By (a), only the lowest element of T in each gap can move. A pair (T, terms) with no movable element is therefore a
free choice, gap by gap, of S = T ∩ G and its terms such that, if S is nonempty, its lowest element p cannot move.
Grouping the nonempty S by p gives 9 b_p z for p and a factor 1 + 9z for each level of G above p. The coefficients
are nonnegative, which gives the last bound. ∎

For adjacent moves, b_p = b on all of a gap that lies inside one segment, because the target l_G is the same for
every p in G. A gap that crosses into the next segment has b_p = 1 on its upper part (a move from there would leave
the segment); Lemma 4.1 accounts for this.

## 3. Blocking laws

For an adjacent move the term (i_p, j_p) is one of nine, and j_p - i_p takes the values -2, ..., 2 with probabilities
pi(e) = (3 - |e|)/9. So the fraction of terms that cannot move is b(e) = 1 - pi(e) = (6 + |e|)/9 when d_{l_G} = e:
2/3, 7/9 or 8/9. It remains to average b over the positions of a fibre.

Fix a fibre with key kappa and one band row of it: all row blocks r and all high digits u, read as an integer in
[0, 3^{n'}). Let kappa_lo be the residue of the first coordinate of kappa modulo 3^{n'}. Over the band row, u is
uniform, the column digits are those of v = (u + kappa_lo) mod 3^{n'}, and the digit differences d_k = v_k - u_k
form a carry chain.

**Lemma 3.1 (worst keys).** For every kappa_lo, every set S of digit positions and all weights X_k >= 0,

    E_u prod over k in S of (1 + b(d_k) X_k)  <=  prod over k in S of (1 + (22/27) X_k).

*Proof.* Let s = kappa_k + carry, the carry coming from the positions below k, so s is in {0, 1, 2, 3}. If s is 0 or 3,
then v_k = u_k, d_k = 0 and b = 2/3. If s = 1, the three values of u_k give d_k = 1, 1, -2, and if s = 2 they give
d_k = 2, -1, -1; in both cases b averages to 22/27. The digit u_k is uniform and independent of the lower digits,
which fix the carry, so conditioning on them bounds the factor of the top position of S by 1 + (22/27) X_k in
expectation. Induction on |S|, removing the top position each time, gives the bound. ∎ The bound is attained at
kappa_lo = 11...1 in base 3.

**Lemma 3.2 (shifted keys).** If kappa_lo is replaced by (kappa_lo + sigma_0) mod 3^{n'} with sigma_0 uniform, the
d_k are independent with law pi, and

    E prod over k in S of (1 + b(d_k) X_k) = prod over k in S of (1 + (62/81) X_k),     62/81 = 1 - sum_e pi(e)^2.

*Proof.* With sigma_0 uniform, the key digit at each position is uniform given everything below it. So, whatever the
incoming carry, (u_k, v_k) is uniform over the nine pairs and independent of the lower positions; the outgoing carry
is a function of those lower positions and (u_k, v_k), so the argument repeats upward. ∎

**Lemma 3.3 (stretch moves).** Under independent pi digits (Lemma 3.2), the probability that the lowest element of
T ∩ G cannot move anywhere in a stretch of len outer levels is b(len), with b(0) = 1, b(1) = 62/81,
b(2) = 538/729, b(3) = 4834/6561, b(4) = 43498/59049, b(5) = 391474/531441, and b(len) <= b(5) for len >= 5.
Different gaps have disjoint stretches, so their factors are independent.
*Proof.* Moving p to the stretch level of position i (from the bottom) deletes that level's digit pair and inserts
p's term at the top of the stretch; the levels in between move down one rank. So w' has the same key if and only if
the integer spelled by the digit differences of the stretch from position i up equals the one spelled after the
deletion and insertion. The event depends only on the stretch digits from i up and on j_p - i_p. Hence b(len) is the
probability, over pi^len for the stretch and pi for the term, that no position works; the values above are exact
enumerations. A longer stretch contains a shifted copy of the candidates of a shorter one, so b is nonincreasing. ∎

**Lemma 3.4 (choosing the shift).** Tiers (S) and (C) give the column labels a shift sigma_0 in [0, 3^{n'}) chosen
deterministically: digit by digit from rank z0 up, each digit minimising the conditional expectation of the
potential Psi of Sec. 5 (a sum, over key, band row and cell, of E_u prod_G P_G). The value reached is at most
E_{sigma_0} Psi, and the choice costs n^{2 - eps/2 + o(1)} time.
*Proof.* When a prefix of sigma_0 is fixed and the rest is uniform, the digits above the prefix are independent with
law pi and independent of those below (the argument of Lemma 3.2). So the conditional expectation of each term of Psi
is a product over positions, computed by a dynamic program whose state is the carry of kappa + sigma_0, the carry of
u + key, and the digits of the current stretch: O(5^lambda) = O(1) states per position. Taking the digit with the
smallest conditional expectation never increases it, which is the method of conditional expectations. Psi has at
most 6 n g_pad/3^{n'} <= n^{2 - eps/2 + o(1)} terms (Sec. 5), each costing poly(L) per digit. A shift keeps W
fibre-closed: every key moves by sigma_0. ∎

## 4. The layout: segment signatures

Cut [L] into S = L/lambda segments of lambda = 8 consecutive levels, with mu a multiple of 8 and of the denominators
of c and theta. The *signature* of an inner set Q is (n_1, ..., n_S), n_s = |Q ∩ segment s|, and its *class* is the
set of all inner sets with that signature, of size prod_s C(lambda, n_s). A move of Sec. 2 never leaves p's segment, so
Q - p + p' has the signature of Q. Hence, if every class that is used is placed whole on one diagonal, condition (d)
holds for every move.

*Zone segments.* Let eta = mu^{-1/4}, l0 = (1 + eta) z0 c/(c - 1) and s0 = ceil(l0/lambda). Segments s < s0 are *zone
segments*. Theorem C uses no moves there and sets b = 1 (Sec. 9 adds Rule Z there). The good signatures below have
rank(s0 lambda) >= z0, so every stretch in a later segment has rank at least z0 and (c) holds: the outer levels below
s0 lambda number at least s0 lambda (1 - 1/c) - S^{2/3} >= (1 + eta) z0 - S^{2/3} >= z0, as eta z0 = Theta(mu^{3/4})
exceeds S^{2/3} = Theta(mu^{2/3}) for large mu.

**Lemma 4.1 (the class average factorises).** For a class with counts (n_s),

    average over Q in the class of prod_G P_G(z) = prod_{s < s0} (1 + 9z)^{n_s} * prod_{s >= s0} A(lambda, n_s; 9z),

where A(lambda, n; y) is the average over the n-subsets S of [lambda] of the product over the runs G of S of
(1 + y)^{|G|} if G starts at the segment's first level, and 1 + b_G((1 + y)^{|G|} - 1) otherwise, with b_G the
blocking law of the tier (for stretch moves, b(len_G) with len_G the stretch inside the segment).
*Proof.* The sets Q ∩ segment s are independent uniform n_s-subsets over the class. A gap G that crosses from segment
s into s + 1 splits into G_1 (in s) and G_2 (in s + 1, starting at its first level). Its upper elements never move, so
expanding P_G gives (1 + y)^{|G_2|}(1 + b((1 + y)^{|G_1|} - 1)), which is the product of the two per-segment factors.
In zone segments every factor is (1 + y)^{|G|}. For integer keys, b_G is first replaced by its average over the band
row (Lemma 3.1, or 3.2 and 3.3 under the shift), which is valid because the product is linear in each factor. ∎

*Good signatures.* Let X_1, ..., X_S be independent Binomial(lambda, 1/c) variables. The signature of a uniform
mu-subset of [L] has the law of (X_s) conditioned on sum_s X_s = mu, and P(sum_s X_s = mu) >= 1/(L + 1), since mu = L/c
is the mode of Binomial(L, 1/c). Take f1(n) = ln C(lambda, n), f2(n) = ln A(lambda, n; 9z), and n itself on the zone
segments. Each is bounded by a constant R, so by Hoeffding's inequality the chance that one of the sums exceeds its mean
by more than S^{2/3} is at most 2 exp(-2 S^{1/3}/R^2) without the conditioning, and at most (L + 1) times that with it.
A signature is *good* if sum_s f1(n_s) <= S E f1 + S^{2/3}, sum_{s >= s0} f2(n_s) <= (S - s0) E f2 + S^{2/3}, and sum_{s
< s0} n_s <= s0 lambda/c + S^{2/3}. For large mu the good classes hold at least K/2 inner sets, and, since s0/S -> zeta,

    the largest good class has at most exp(mu (c/lambda) E f1 + o(mu)) sets, and
    the largest class average of prod_G P_G over good classes is at most exp(mu Lambda(z) + o(mu)),
    Lambda(z) = zeta ln(1 + 9z) + (1 - zeta)(c/lambda) E_{n ~ Bin(lambda, 1/c)} ln A(lambda, n; 9z).

*Packing.* Let the supply be the number of sets in good classes, maxclass the size of the largest good class, and
K0 = floor(sqrt(supply/2)), so K0^2 >= K/4 - O(sqrt K) and the tile loses only a constant factor. Fill the integer
diagonals one at a time: while the free length of the diagonal is at least maxclass, place a whole unused good
class on it; then fill the rest with *filler* sets taken from classes that are not placed on any good cell. At most
K0^2 <= supply/2 sets are ever placed, so an unused good class is always available. Each integer diagonal has fewer
than maxclass filler cells, so each *wrapped* diagonal {(r, (r + delta) mod K0)}, which is two integer diagonals, has at
most 2 maxclass filler cells, and its good cells come in whole classes.

*Cost of the layout.* It depends only on n, not on the input. Enumerate the (lambda + 1)^S = 9^S signatures, with the
class size and the three goodness sums of each in poly(L) time; then pack greedily and list each inner set once, in
poly(L) time per set, for at most K <= exp(L H(1/c)) sets. With S = c mu/lambda and D = 4^mu = n^eps,

    9^S = n^{e9},  e9 = eps c ln 9/(lambda ln 4);      K <= n^{eK},  eK = eps c H(1/c)/ln 4,

so the time is n^{max(e9, eK) + o(1)}, and even the product bound n^{e_pre}, e_pre = e9 + eK, is far below n^{2 -
sigma}. `bands_cert.py` checks e_pre < 2 - sigma and prints e9, eK and e_pre rounded up:

| tier | e9 | eK | e_pre |
|---|---|---|---|
| (W) | 0.239523 | 0.166278 | 0.405800 |
| (S) | 0.239503 | 0.166550 | 0.406053 |
| (C) | 0.239494 | 0.166660 | 0.406153 |

## 5. One solve

*The wanted set.* In a light instance (Sec. 6) the queries are q = (a, j) with a in A' and j in [0, p), and
k = (a + j) mod p. Their positions are ((j, x(a)), (k + sigma_0, y(a))), with x and y as in Theorem A's Lemma 2.4 and
sigma_0 = 0 in tier (W). They lie in the fibres with keys kappa in {i_a + sigma_0, i_a - p + sigma_0}, i_a = a mod p.
Let W' be the union of these fibres over the padded label ranges [0, g_pad) of rows and columns (padding rows are
zero). W' is a union of fibres, has |W'| <= 2|A'| g_pad, and includes all the positions Lemma 2.4 needs. The tiles,
bands and cells are those of Secs. 2 and 4, with g_pad/(K0 3^{n'}) >= n^{1 - eps E - o(1)} bands.

*The bound per position.* Fix a fibre and one full band row of it (all r in [K0] and all u). Its positions lie in the
cells (r, (r + kappa_hi + e) mod K0), with e in {0, 1} without the shift (one carry, from u + kappa_lo) and in
{0, 1, 2} with it (a second carry, from kappa_lo + sigma_0); kappa_hi is the quotient of the first coordinate of kappa
by 3^{n'}. Bound R_d by alpha_d on filler cells and by z^{-d} prod_G P_G (Lemma 2.2) on good cells. Sum the good-cell
bound over every e and every u. Over r each cell of a wrapped diagonal appears once, and the terms are nonnegative, so
this over-count is safe and makes u uniform. Then average over u (Lemma 3.1; or keep E_u inside the potential Psi and
apply Lemma 3.4), and apply Lemma 4.1 class by class:

    sum over the band row of R_d <= 3^{n'} [ 3 K0 z^{-d} max_good avg prod_G P_G + 6 maxclass alpha_d ].

The band row has K0 3^{n'} positions, so per position R_d <= 3 z^{-d} e^{mu Lambda(z) + o(mu)} + 6 alpha_d maxclass/K0.
At most four band rows of a fibre are partial (the two ends of the label range, and the shift); each of their
positions is charged alpha_d.

*Exponents.* With D = 4^mu and t = theta mu, every d < t has z^{-d} <= z^{-t} (as z <= 1) and alpha_d <= alpha_t (as
theta < 9/10), so summing over d < t gives the per-position costs D^{q_eff + o(1)} for good cells and D^{q_fill + o(1)}
for filler cells, with q_eff and q_fill as in Sec. 0 (maxclass from Sec. 4 and K0 = e^{mu (c/2) H(1/c) + o(mu)}). Over
all tiles, the pruned recursion then costs, for each solve,

    n^{o(1)} [ N^2 D^{-gamma} + |W'| D^{q*} + n K0 3^{n'} D^{q(theta)} + N D^E ]:

orders d >= t at sum_{d >= t} beta_d per tile (the exact count); orders d < t by Lemma 2.1 summed over the fibres;
the partial band rows, at most four per fibre and at most 2n fibres; and the pruned encodings. With N = n^{1 + o(1)},
|W'| <= n^{2 - eps/2 + o(1)} and K0 3^{n'} = D^{E - 1/2 + o(1)}, this is n^{2 - sigma + o(1)} provided
eps (E + gamma) < 1, q* < 1/2 and eps (E + q(theta) - 1/2) + sigma < 1, all conditions of Theorem C.

## 6. Deterministic residue buckets with heavy-bucket recursion

Theorem A groups the inputs into intervals (FKP24). The block triples that can hold a solution then form a
staircase, which has no translation structure. Here the buckets are residues modulo a prime p, so a + b = c forces
k = (i + j) mod p exactly, and the wanted set of Sec. 5 is fibre-closed.

*Parameters.* As in Theorem A's Lemma 2.1, except tau = 2^{ceil(sqrt(log2 n))} and s the largest integer with
4 (tau s)^2 lambda^r <= n^{delta r} (lambda here is Theorem A's lambda = 2(nu + 1) ln n). Put g = ceil(3n/s), let P_w be
the primes in [g, 2g), and let omega be the largest number of primes of P_w that divide one nonzero integer of
absolute value at most 2U; omega <= ln(2U)/ln g = O(1).

*A node (A', B', C').* If min(|B'|, |C'|) <= n^{1 - sigma}, solve it directly in O(n^{2 - sigma} log n) time. Otherwise,
for every p in P_w compute Coll_B(p) = #{(b, b') in B'^2 : b = b' mod p}, Coll_C(p) likewise, and
X(p) = #{(b, c) in B' x C' : b = c mod p}, in O(n + p) time each, n^{2 - eps/2 + o(1)} in all, and take the p that
minimises F(p) = (Coll_B(p) + X(p))/|B'| + (Coll_C(p) + X(p))/|C'|. Call a residue *heavy* if more than tau s elements
of B', or of C', lie in it. Solve the light instance (A', B'_L, C'_L) by Theorem A's Section 2, with buckets in place
of interval groups and Lemma 2.4 evaluated as in Sec. 5. Its counts satisfy N_1(q) <= (tau s)^2, so Lemma 2.5 halves
as before, by the choice of s. Then recurse on (A', B'_H, C') and on (A', B'_L, C'_H).

**Lemma 6.1.** Every solution lies in exactly one light instance or one directly solved node.
*Proof.* At a node, a solution with b and c both light is in the light instance; one with b heavy is in the first
child; one with b light and c heavy is in the second. The three cases are disjoint, and induction finishes it. ∎

**Lemma 6.2.** mean over p in P_w of F(p) <= 4 + 2 omega (|B'| + |C'|)/|P_w|, and |B'_H| <= F(p)|B'|/(tau s),
|C'_H| <= F(p)|C'|/(tau s).
*Proof.* Coll_B(p) = |B'| + sum over b != b' of [p | b - b'], and each nonzero difference is divisible by at most omega
primes of P_w, so its average over p is at most |B'| + omega |B'|^2/|P_w|. Likewise X(p) <= min(|B'|, |C'|) + sum over b
!= c of [p | b - c]. Dividing and adding gives the mean. For the second claim, the elements of B' in residues holding
more than tau s elements of B' number at most Coll_B/(tau s), and those in residues holding more than tau s elements of
C' number at most sum_r |B'_r||C'_r|/(tau s) = X/(tau s); the same holds for C'. ∎

Since the chosen p is at most the mean and |P_w| >= g/(2 ln g), each child shrinks the set it recurses on by a factor
phi <= (4 + 3 omega s ln g)/(tau s) <= 4 omega ln g/tau = n^{-Omega(1/sqrt(log n))} for large n, and the other set does
not grow. So the depth is O(sqrt(log n)), the tree has 2^{O(sqrt(log n))} = n^{o(1)} nodes, and a node pays for one
light instance (n^{o(1)} solves of Sec. 5, as in Theorem A's Lemma 2.7) plus n^{2 - eps/2 + o(1)}. As sigma < eps/2, the
total is n^{2 - sigma + o(1)}.

## 7. Proof of Theorem C

Compute the layout of Sec. 4 (n^{e_pre + o(1)} time, below n^{2 - sigma}) and run the recursion of Sec. 6. Correctness:
by Lemma 6.1 every solution lies in exactly one light instance or directly solved node, and each light instance is
decided correctly by Theorem A's Lemmas 2.5 and 2.6 (with s replaced by tau s), since the pruned recursion returns the
exact entries (`lem:prune`). Time: n^{o(1)} nodes, each with n^{o(1)} solves of n^{2 - sigma + o(1)} (Sec. 5) and
n^{2 - eps/2 + o(1)} further work, with the shift of Lemma 3.4 in tiers (S) and (C). The choice of every prime and of
sigma_0 is computed, so no step uses randomness. ∎

## 8. Mechanical checks (small cases; logic, not asymptotics)

| script | what it checks | negative controls (each must fail) |
|---|---|---|
| `check_bands_rep.py` | Lemma 2.1 by brute force over every leaf, on random and segment grids, adjacent and stretch moves, d = 1, 2; Lemma 2.2's coefficient exactly for adjacent moves; grids fine enough that whole classes sit on one diagonal, where the bound is asserted strictly below the trivial count | dropping (d), dropping (e), and a W that is not fibre-closed |
| `check_bands_carry.py` | Lemmas 3.1 and 3.2, exhaustive over every key for n' <= 6 digits, with the 22/27 bound attained | 62/81 in place of 22/27; a fixed worst key above the average |
| `check_bands_stretch.py` | Lemma 3.3: the values b(len), and the exact average of R_d over all (u, kappa) against the generating function, on seven shapes | the stretch count must differ from the adjacent one |
| `check_bands_segments.py` | Lemma 4.1 as an exact equality, on four shapes | letting cross-segment gaps move |
| `check_bands_buckets.py` | Sec. 6 against brute force on 160 instances (random, sparse, per-prime progressions that force heavy residues, clusters): answers, the solution partition of Lemma 6.1, light buckets, F(p) at most the mean, the shrink bound | dropping the second child misses solutions; the worst prime puts F(p) above the mean and stalls the recursion |
| `bands_cert.py` | Corollary D, every condition of Theorem C on the whole ball, b = 1 gives Theorem A's saving | eps 1% too large; z = 2 |
| `bands3_cert.py` | Corollary D' (Sec. 9), every condition of Theorem C' on the whole ball; zone law 1 gives back Corollary D's (C) value and Theorem A's saving | eps 1% too large; z = 2 |
| `tests/test_bands_zone.py` | Lemma Z by brute force over every leaf on toy grids (Sec. 9) | one class split across a wrapped diagonal |
| `bands4_poly.py` | the exact polynomials A_Y and A_ZY of Sec. 10 for lengths 8 and 9, cross-checked by a second implementation that builds every moved member's string | (a cross-check, not a control) |
| `bands4_cert.py` | Corollary D'' (Sec. 10), every condition of Theorem C'' on the whole ball, including the diagonal fit; no sharing gives Theorem A's saving | eps 1% too large; z = 2; 2/5 of the segments of length 9; length 9 at theta = 1/50 (fails the diagonal fit only) |
| `check_bands_y.py` | Lemma Y end to end on toy tiles with mixed segment lengths (Sec. 10) | a naive window that ignores the rank shift; targets in the segment below; Rule Y inside the zone |

The saved outputs are the `.out` files next to each script. `tests/test_bands.py` checks the printed values,
compares every run with its saved output, and recomputes the three savings by an independent method (a dynamic
program over the levels of a segment in place of the subset enumeration of `bands_cert.py`, and a separate
enumeration of b(len)).

## 9. Zone moves: Rule Z and Theorem C'

Theorem C allows no move in the zone segments, because a move there changes the zone digits x and y of the key
(condition (c)). One kind of move changes no digit at all: the move whose new term equals the digit pair it replaces.
It changes the cell and nothing else, its blocking law is 8/9 for every key, and every fibre-closed W is already closed
under it.

*Rule Z.* Let w be a position with cell Q, tau an order-d leaf of w given by (T, terms), and p in T in a zone segment
s, with p the lowest element of T in its gap G. Let l_G be the outer level just below G, and suppose that l_G lies in
segment s. Call p *zone-movable* if the term (i_p, j_p) of tau at p equals (u, v), the row and column digits of w at
rank(l_G). A gap that starts at the first level of its segment, and the part of a gap above a segment boundary, get no
zone move.

**Lemma Z (zone moves).** Lemma 2.1 stays true when, in zone segments, the elements that can move are the
zone-movable ones, while the other segments keep the moves of Sec. 2. So, for fibre-closed W and every tile and order
d, |Leaves_d(W_tile)| <= sum over w in W_tile of R_d(w), where R_d(w) counts the (T, terms) of order d in which no
element can move by these rules.
*Proof.* Let w' = w(T - p + l_G). The level l_G is outer for w, so it lies in F, and w' is a member of tau. The levels
strictly between l_G and p lie in G, which is inside Q and inside Q' = Q - p + l_G, so they are inner for both w and
w'. So the outer levels of w' are those of w with l_G replaced by p, at the same rank, and no outer level lies between
them. Every rank is unchanged, and w' carries tau's term at p, which is (i_p, j_p) = (u, v), the pair w carries at
rank(l_G). So w' has exactly the row string and the column string of w, zone digits x and y included. The levels l_G
and p are in the same segment s, so Q' has the signature of Q. Its class is placed whole on one integer diagonal of the
grid (Sec. 4, *Packing*: whole classes fill integer diagonals, and only the filler count is per wrapped diagonal), so
Q' is the inner set of a good cell (r', c') of the same tile with c' - r' = c - r. The row label of w' is
j' = j + (r' - r) 3^{n'} and its column label is k' = k + (c' - c) 3^{n'}; the shift sigma_0 of tiers (S) and (C) is
added to both k and k'. So k' - j' = k - j, x and y are unchanged, the key is the same, j' and k' stay in the band, and
w' lies in W because W is fibre-closed. The sorted set T - p + l_G is the sorted set of T with p replaced by the smaller
l_G, so it is lexicographically smaller, and w is not the representative of tau. The rest is the proof of Lemma 2.1
unchanged: each needed leaf is counted once, at its representative, and R_d has only to exclude the (T, terms) with
some element that can move. ∎

Rule Z needs neither (c) nor (e): no digit of the key changes. Nor does it depend on the key: exactly one of the nine
terms at p is zone-movable, whatever w is, so b_p = 8/9 for every position, in all three tiers. In the zone segments
Rule Z replaces Theorem C's "no moves", which only enlarges the set of moves; restricting moves would only enlarge R_d.
In a non-zone segment a Rule-Z target is already an adjacent move of Sec. 2 (j_p - i_p = v - u = d_{l_G}), so the gain
is exactly the zone.

*Generating function and class average.* Lemma 2.2 applies verbatim with b_p = 8/9: in a zone segment the per-gap
factor is 1 + (8/9)((1 + 9z)^{|G|} - 1) when l_G lies in the segment, and (1 + 9z)^{|G|} when G starts at the
segment's first level. The factor is deterministic, so it passes unchanged through the induction of Lemma 3.1, the
shift law of Lemma 3.2 and the conditional expectations of Lemma 3.4 (in the potential Psi it is a constant factor of
each term). In Lemma 4.1 the segments are independent under the class law, so the zone segments contribute
prod_{s < s0} A(lambda, n_s; 9z, 8/9) in place of prod_{s < s0} (1 + 9z)^{n_s}, where A(lambda, n; y, 8/9) is the
average of Lemma 4.1 with b_G = 8/9 for every run.

*Good signatures.* Add one condition to the three of Sec. 4: sum_{s < s0} f4(n_s) <= s0 E f4 + S^{2/3}, with
f4(n) = ln A(lambda, n; 9z, 8/9). Its range is in [0, lambda ln(1 + 9z)], so Hoeffding's inequality under the
conditioned law gives the same failure bound (L + 1) 2 exp(-2 S^{1/3}/R^2) as for the other sums, and the good classes
still hold at least K/2 inner sets for large mu. The zone condition on sum_{s < s0} n_s is kept, so rank(s0 lambda) >=
z0 still holds for the moves of the non-zone segments. The layout cost of Sec. 4 adds one poly(L) sum per signature,
so e_pre is unchanged. With s0/S -> zeta, the largest class average of prod_G P_G over good classes is at most
exp(mu Lambda'(z) + o(mu)),

    Lambda'(z) = (c/lambda) [ zeta E ln A(lambda, n_s; 9z, 8/9) + (1 - zeta) E ln A(lambda, n_s; 9z) ],   n_s ~ Bin(lambda, 1/c).

With zone law 1 in place of 8/9, A(lambda, n; y, 1) = (1 + y)^n and E n_s = lambda/c, so Lambda' becomes the
Lambda(z) of Sec. 4.

**Theorem C'.** Theorem C holds with q_eff replaced by

    q_eff' = [ -theta ln z + (c/lambda) E( (1 - zeta) ln A(lambda, n_s; 9z) + zeta ln A(lambda, n_s; 9z, 8/9) ) ] / ln 4

in q*, sigma and every condition. Every other quantity and condition is unchanged.
*Proof.* Sec. 5 with Lambda' in place of Lambda: on good cells R_d <= 3 z^{-d} e^{mu Lambda'(z) + o(mu)} per position,
and the filler cells, partial band rows, exact count and encodings are charged as before. Secs. 6 and 7 are unchanged.
∎

**Corollary D' (values; exponents rounded up from the exact arb endpoints).** `bands3_cert.py` checks every condition
of Theorem C' on the whole arb ball at these exact rational points (lambda = 8, zone law 8/9):

| tier | blocking law | (c, theta, eps, z), exact | sigma >= | 3SUM |
|---|---|---|---|---|
| (W) worst keys, adjacent moves | 22/27 | (5274867/250000, 57881/500000, 572980907/10000000000, 172629/10000000) | 0.0041463659 | O(n^{1.995854}) |
| (S) shifted keys, adjacent moves | 62/81 | (5262491/250000, 58501/500000, 574279737/10000000000, 91849/5000000) | 0.0041917719 | O(n^{1.995809}) |
| (C) shifted keys, stretch moves | b(len) | (10514903/500000, 58807/500000, 574807987/10000000000, 23671/1250000) | 0.0042143770 | O(n^{1.995786}) |

Nine-digit upper ends: 1.995853635, 1.995808229 and 1.995785623 (Corollary D: 1.995856782, 1.995811603, 1.995789157).
The layout costs are e_pre <= 0.405887, 0.406145 and 0.406248. With zone law 1, the formula gives back Corollary D's
tier (C) saving 0.0042108435 at its point, and Theorem A's saving 0.0039992877 with b = 1 (two controls of
`bands3_cert.py`). So deterministic 3SUM, and Convolution-3SUM, are solved in O(n^{1.995786}).

*Toy check of Lemma Z* (`tests/test_bands_zone.py`, exact). Leaves are built directly as (Z, terms on F), their union
is a set, inner sets are packed by signature class onto integer diagonals in random order, W is a union of random key
fibres, and Rule Z is applied in every segment (stronger than its use in the zone only). On four toy runs
(L, mu, lambda, z0, d) = (6, 2, 3, 1, 1) twice, (7, 3, 7, 2, 1) and (6, 2, 6, 0, 2): no Rule-Z target lies outside W,
every target is a member of the same leaf with the same strings and a lexicographically smaller set, R_d(w) equals the
coefficient of the 8/9 generating function for every w, and |Leaves_d| <= sum R_d. Control (must fail): one class
split across the two pieces of a wrapped diagonal sends 3416 targets outside W, so the integer-diagonal packing of Sec.
4 is what the lemma uses.

## 10. Window moves per element (Lemma Y), mixed segment lengths, and Theorem C''

Theorem C' moves only the lowest element of T in its gap (condition (a)), and only inside the stretch of the gap. Both
restrictions can go. Every element p of T can be tested on its own, against every outer level below it in its
segment, across the levels of Q (in Z or in T) that lie in between. Those levels are inner for w and for the moved
member, so they carry no digit, and the key test is still a window equation on w's own digits. This section proves
that (Lemma Y), and then lets the segments have lengths 8 and 9 in a fixed pattern. Only tier (C) (shifted keys) is
claimed; tiers (S) and (W) are unchanged.

*Notation.* Fix a good cell Q, a position w in it and an order-d leaf tau of w, given by (T, terms). For p in T in
segment s, let o_1 < ... < o_N be the outer levels of w in segment s below p, d_i the digit difference of w at the
rank of o_i (column digit minus row digit), and t = j_p - i_p.

*Rule Y.* In a non-zone segment, p is *Y-movable* if for some a <= N the member w' = w(T - p + o_a) has the key of w.
In a zone segment, p is Y-movable if N >= 1 and (i_p, j_p) = (u, v), the digit pair of w at the rank of o_N (Rule Z for
every element, with no condition (a)).

**Lemma Y.** Let W be fibre-closed. In a non-zone segment, w' = w(T - p + o_a) has the key of w if and only if

    d_a + 2 sum_{j=1}^{m} d_{a+j} 3^{j-1} = t 3^m,     m = N - a.

If some p in T is Y-movable, w is not the representative of tau in W. Hence |Leaves_d(W_tile)| <= sum over w of
R^Y_d(w), with

    R^Y_d(w) = [z^d] prod_{p in Q} (1 + 9 b_p z),

where b_p is the fraction of the nine terms at p for which p is not Y-movable (b_p = 1 if N = 0).
*Proof.* The level o_a is outer for w, so it lies in F, T' = T - p + o_a is a d-subset of F, and w' is a member of
tau. The levels p and o_a are in the same segment, so Q' = Q - p + o_a has the signature of Q. Its class sits whole on
one integer diagonal (Sec. 4), so Q' is the inner set of a cell of the same tile with c' - r' = c - r. The outer
levels of w' are those of w with o_a replaced by p. Every level outside segment s keeps its rank, and segment s keeps
its number of outer levels, so the digits outside segment s do not change. In a non-zone segment every window rank is
at least z0 (good signatures, Sec. 4), so x and y do not change. Inside segment s, the levels strictly between o_a and
p that are not outer lie in Q (in Z or in T). They are inner for w and for w' (only p leaves Q', only o_a enters it),
so they carry no digit. The outer levels of w' in segment s, in order, are o_1, ..., o_{a-1}, o_{a+1}, ..., o_N, p,
and then the levels above p. So the digit sequence of w' differs from that of w only at the ranks of o_a, ..., o_N,
where it reads d_{a+1}, ..., d_N, t. With rho the rank of o_a, the change in the integer of digit differences is

    3^{rho - z0} [ sum_{i < m} d_{a+1+i} 3^i + t 3^m - sum_{i <= m} d_{a+i} 3^i ],

which is 0 if and only if the displayed equation holds. Then k' - j' = k - j (the cell parts cancel as in Lemma 2.1,
and sigma_0 is added to both), x and y are unchanged, and w' is in W. In a zone segment, every level strictly between
o_N and p is in Q, so p takes the rank of o_N in w'. It carries (i_p, j_p) = (u, v), so both strings are unchanged
and the key is unchanged, as in Lemma Z. In both cases the sorted T' is the sorted T with p replaced by o_a < p, and
o_a is not in T, so T' is lexicographically smaller and w is not the representative. Whether p is Y-movable depends
only on w and on the term at p. So the number of (T, terms) with no Y-movable element is
sum_{|T| = d} prod_{p in T} 9 b_p = [z^d] prod_{p in Q} (1 + 9 b_p z). ∎

Condition (a) was used in Sec. 2 only to make b_p a function of w and p, and for the lexicographic step. Neither
needs it here. Rule Y contains the stretch moves of Sec. 2 (the case where o_a, ..., o_N is the stretch of p's gap and
p is the lowest element of T in it) and the zone moves of Sec. 9, so R^Y_d(w) <= R_d(w) of Theorem C' for every w. The
bound is one injection (each needed leaf to its representative), so nothing is counted twice.

*Class average.* b_p depends only on Q ∩ segment s and on w's digits at the outer levels of segment s. Under the
shifted law (Lemma 3.2) the digits at ranks >= z0 are independent with law pi, and under the class law the sets
Q ∩ segment s are independent uniform n_s-subsets, so

    average over the class of E_u prod_{p in Q} (1 + y b_p) = prod_{s < s0} A_ZY(lambda_s, n_s; y) prod_{s >= s0} A_Y(lambda_s, n_s; y),

where A_Y(lambda, n; y) is the exact joint average over the n-subsets of a segment of length lambda and over its digits
(the window factors are correlated inside a segment, so it is not a product of per-gap factors), and A_ZY is the same
average with b_p = 8/9 when N >= 1. Both are polynomials in y with rational coefficients; `certificates/bands4_poly.py`
computes them exactly for lambda = 8, 9 and cross-checks them with a second implementation that builds each moved
member's string and compares integer values. For the shift of Lemma 3.4 the dynamic program carries the two carries
and the digits of the current segment, at most 5^9 = O(1) states. The good-signature conditions use f2(n) = ln A_Y
and f4(n) = ln A_ZY, both in [0, lambda ln(1 + 9z)], so Hoeffding's inequality gives the same failure bound as in Sec.
4. Everything else (filler cells, partial band rows, the exact count, the encodings) is as in Secs. 4 and 5.

*Mixed segment lengths.* Fix a period of 10 segments, 7 of length 8 and 3 of length 9 (83 levels), and repeat it; L
is a multiple of 83 and of the denominators of c and theta, which costs o(1) in the exponent. Signatures and classes
are defined per segment as before, a class has size prod_s C(lambda_s, n_s), and every move of Lemma Y stays in its
segment, so segments of different lengths do not interact. The levels are still i.i.d. Bernoulli(1/c), so the
signature law is that of independent Bin(lambda_s, 1/c) counts conditioned on their sum being mu, and P(sum = mu) >=
1/(L + 1) as before. The zone segments are the first s0 segments; they have the period's mix up to O(1) segments. With
w_l the fraction of segments of length l and Lbar = sum_l w_l l, the class average per key level is

    Lambda''(z) = (c/Lbar) sum_l w_l E_{n ~ Bin(l, 1/c)} [ (1 - zeta) ln A_Y(l, n; 9z) + zeta ln A_ZY(l, n; 9z) ].

The signatures number prod_s (lambda_s + 1), so e9 = eps c (sum_l w_l ln(l + 1)/Lbar)/ln 4.

*A class fits a diagonal.* The packing of Sec. 4 places each good class whole on one integer diagonal, which needs
ln(maxclass) < ln K0, that is

    (c/Lbar) sum_l w_l E ln C(l, n)  <  (c/2) H(1/c).

It holds at both points of Corollary D'' (by about 0.065 and 0.031 per key level), but it does not follow from
q_fill < q_eff in general (that would need H(theta) + theta ln 9 >= q_eff ln 4), so Theorem C'' lists it as a condition
of its own.

**Theorem C''.** Let the segment pattern be (w_8, w_9) with w_8 + w_9 = 1, and define

    q_eff''  = [ -theta ln z + Lambda''(z) ] / ln 4,
    q_fill'' = [ (c/Lbar) sum_l w_l E ln C(l, n) - (c/2) H(1/c) + H(theta) + theta ln 9 ] / ln 4,
    e_pre''  = eps c ( sum_l w_l ln(l + 1)/Lbar + H(1/c) ) / ln 4.

If the conditions of Theorem C hold with q_eff'', q_fill'' and e_pre'' in place of q_eff, q_fill and e_pre, and a class
fits a diagonal, then 3SUM is solved deterministically in time n^{2 - sigma + o(1)} (tier (C), shifted keys).
*Proof.* Sec. 5 with Lemma Y and Lambda'' in place of Lemma 2.1 and Lambda: on good cells R^Y_d <= 3 z^{-d}
e^{mu Lambda''(z) + o(mu)} per position, and the rest is charged as before. Secs. 6 and 7 are unchanged. ∎

**Corollary D'' (values; exponents rounded up from the exact arb endpoints).** `bands4_cert.py` checks every condition
of Theorem C'', including the diagonal fit, on the whole arb ball at these exact rational points:

| tier (C), Lemma Y | pattern (w_8, w_9) | (c, theta, eps, z), exact | sigma >= | 3SUM |
|---|---|---|---|---|
| segment length 8 | (1, 0) | (21018799/1000000, 1176831/10000000, 143775683/2500000000, 190173/10000000) | 0.0042165295 | O(n^{1.995784}) |
| lengths 8 and 9 | (7/10, 3/10) | (4203319/200000, 3679/31250, 115032221/2000000000, 190589/10000000) | 0.0042181468 | O(n^{1.995782}) |

Nine-digit upper ends: 1.995783471 and 1.995781854 (Corollary D', tier (C): 1.995785623). The layout costs are
e_pre <= 0.406309 and 0.400985. At the mixed point the binding term is eps (1/2 - q_eff''), with eps gamma and
1 - eps E within 2e-8 of it, and q_fill'' is within 1.3e-3 of q_eff'': the filler condition is what limits the share of
segments of length 9. So deterministic 3SUM, and Convolution-3SUM, are solved in O(n^{1.995782}).
Controls of `bands4_cert.py`: with no sharing (A = (1 + y)^n) the formula gives Theorem A's saving 0.0039992840 at its
point; and four points must fail: eps 1% too large, z = 2, a pattern with 2/5 of the segments of length 9 (q_fill'' >
q_eff''), and length 9 alone at theta = 1/50, which fails the diagonal fit and no other condition.

*Toy check of Lemma Y* (`certificates/check_bands_y.py`, exact). One tile per run, classes packed whole on integer
diagonals in random order, real row and column labels with the shift sigma_0, and W a union of random key fibres. For
every w in W and every order-d leaf of w, the representative is found by listing all members of the leaf. Six runs,
(L, mu, segment lengths, z0, d) = (6, 2, (3, 3), 1, 1), (6, 2, (3, 3), 1, 2), (7, 3, (3, 4), 1, 1), (7, 2, (3, 4), 1,
1), (7, 3, (4, 3), 1, 2) and (7, 2, (2, 5), 1, 1), so mixed segment lengths included: no Y target lies outside W, the
number of leaves represented by w is at most R^Y_d(w) for every w, and R^Y_d(w) equals the coefficient of the
generating function for every w. The moves are exercised: 4185 to 123091 moves per run with windows of two or more
outer levels, moves across Z levels, and, at d = 2, 60192 and 65736 moves across T levels. Three controls must fail,
and fail in every run: (A) the naive window "the key is kept iff d_a = t", which ignores the rank shift (8577 to
374947 targets outside W); (B) targets in the segment below (41673 to 424440); (C) Rule Y inside the zone (16617 to
201366).

*Limits of this accounting.* (i) In a zone segment, a downward single swap inside the segment that keeps w's fibre
must keep the row and the column string, so all its window digit pairs must equal the term at p, and every target
needs the same term: b_p >= 8/9 for every key whenever the window lies at ranks < z0, which Rule Z attains. Zone
elements whose window reaches ranks >= z0 (in the top zone segment) have ordinary Y moves; they are an o(1) fraction.
(ii) For adjacent moves and any injective labelling of the row and column strings (input-dependent labellings
included), with keys that are label differences, a move fixes the rest of the member, so the three values of i_p give
three row labels, the three values of j_p give three column labels, and at most one j_p per i_p keeps the key: b >=
2/3 per adjacent move [proof]. In the per-element accounting of this section, b_p = 2/3 for every element with an
outer level below it gives a saving of about 0.004304, or about 0.004296 if the zone keeps law 8/9 [float optimum of
the formula of Theorem C''], less than 1e-4 above Corollary D''. This bounds adjacent-move accounting only.
