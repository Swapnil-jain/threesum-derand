# Deterministic 3SUM in O(n^1.995782)

**Swapnil Jain. A short paper with its artefacts.**

Alman and Vassilevska Williams (arXiv 2610.06783; below "the paper", AVW) gave the first truly subquadratic 3SUM and
truly subcubic APSP algorithms. Their deterministic bounds are O(n^1.9992) for 3SUM and O(n^2.99942) for APSP. Their
conclusion notes that two routes would keep more of their saving: KPP16's reduction for 3SUM, which is randomised,
and the all-edges version of Exact Triangle for APSP. We make both deterministic, and they keep the whole saving.

**Version 3** improves deterministic 3SUM to O(n^1.995782): every element of a shared leaf may now move on its own,
to any free level below it in its segment, and the segments have lengths 8 and 9 in a fixed mix (Theorem C'' of
Theorem 3). The 3SUM saving grows by 5.4% over version 1 (from 0.0039993 to 0.0042181, both rounded against us) and
is 4.82 times the paper's 0.000875. All-edges Exact Triangle, (min,+), APSP and k-Clique are unchanged from version 2.

**Version 2** adds three results: deterministic 3SUM in O(n^1.995786), by bounding the leaves that the wanted entries
share in the paper's pruned recursion (Theorem 3); deterministic all-edges Exact Triangle, (min,+) and APSP in
O(n^2.995943), by folding the residue instances of one Exact Triangle piece into one square product (Theorem 1');
and, from the latter, deterministic Zero-, Min- and Max-Weight k-Clique in O(n^{k - 0.004057 floor(k/3)}). The 3SUM
saving grows by 5.3% over version 1 (from 0.0039993 to 0.0042143, both rounded against us) and is 4.8 times the
paper's 0.000875.

**Working on this problem?** Read [docs/CLOSED_IDEAS.md](docs/CLOSED_IDEAS.md) first: it lists the routes we tried
that do not improve the saving, with the reason for each, so effort is not duplicated. Contributions are welcome.

## Credits

The method and every lemma used here are Alman and Vassilevska Williams's (arXiv 2610.06783). This release composes
their thin-product theorem with known reductions. In detail:

- **The derandomisation technique is known.** Hashes made of small primes chosen one at a time, each by averaging
  over the elements no earlier hash has handled, are Chan and Lewenstein's deterministic pseudo-perfect
  pseudo-additive family (STOC 2015). The pattern goes back to greedy covering by conditional expectations
  (Schmidt and Siegel 1990; Alon and Naor 1996, Sec. 4), and Fischer (STOC 2026) used it recently. The paper's own
  footnote to its Theorem 17 suggests choosing the modulus prime by prime with oracle counts.
  **Ours:** the per-prime criterion counts the 3-term false positives (pseudo-solutions) of the surviving queries with
  the counting oracle, which replaces KPP16's AND of random hashes without losing any of the saving; and the
  all-edges weight H, whose zero test by small primes (Chinese remaindering) is folklore.
- **ImprovedExponents** (github.com/qawbecrdtey/ImprovedExponents, 2026-10-07): the exact leaf count and the pruned
  encodings behind every figure labelled "exact count + pruned encoding (after ImprovedExponents secs. 3-4)",
  including 1.996001. We found them independently, but they were public first, with a Lean
  formalisation. With the paper's lemmas alone our bound is
  1.996291.
- **ImprovedExponents** also showed that a random wanted set gives no saving over the worst-case leaf count, and named
  structured (Hankel or anti-diagonal) wanted sets as an open lead. Theorem 3 follows that lead; the suggestion to
  look for a gain in the structure of the wanted set is theirs. The pruned recursion whose leaves Theorem 3 counts,
  and the count it tightens, are the paper's. **Ours (Theorem 3):** the canonical-representative bound on shared
  leaves, the blocking laws of integer keys and the choice of the shift, the layout by segment signatures, the zone
  moves of Rule Z, the per-element window moves of Lemma Y with mixed segment lengths, and the deterministic residue
  buckets. **Ours (Theorem 1'):** folding the residue instances of an Exact Triangle piece into one square product.
- Kopelowitz, Pettie and Porat 2016 (KPP16): 3SUM to offline Set Disjointness and the AND over hashes.
- Chan and Xu 2024 (CX24): the deterministic hash-free bit halving and Fredman reduction (route L1), and the
  random-prime false-positive bound.
- Fischer, Kaliciak and Polak 2024 (FKP24): interval groups, the residue sets, and prime-at-a-time moduli.
- Alon and Naor 1996: deterministic witnesses (route L1). Zwick 2002 is the precedent for using them beyond Boolean
  products.
- Vassilevska Williams and Williams (VW10, VW13, VW18): the (min,+) to Negative Triangle search and the
  negative-to-zero triangle reduction.
- Vassilevska Williams and Xu 2020 (VX20): the Monte Carlo Exact Triangle reduction behind the Las Vegas remark.
- Björklund, Husfeldt, Kaski and Koivisto 2010 (BHKK10): trimmed Möbius inversion, the idea behind pruning the
  encodings.
- Chan, Vassilevska Williams and Xu 2022 (CVX22): the randomised witness and predecessor steps that route L1 makes
  deterministic.
- Fredman, Komlós and Szemerédi 1984 (choosing a hash prime by counting collisions; Theorem 3's buckets), the method
  of conditional expectations (Erdős and Selfridge 1973, Spencer 1987, Raghavan 1988; Theorem 3's shift), and
  Hoeffding 1963 (Theorem 3's typical signatures).
- Fredman 1976 (Fredman's trick), Matoušek 1991 (dominance products), Schönhage 1981 and Coppersmith 1982 (the
  identity and its recursion, as used by the paper), Nešetřil and Poljak 1985 (k-Clique folding), and Bremner et al.
  2014 (BCD14, (min,+)-convolution via (min,+) products).

`NOTICE` has the full list and states exactly what is new.

## 1. The problem

**3SUM.** Given three sets A, B, C of n integers, each of absolute value at most n^nu for a constant nu, decide
whether a + b = c for some a in A, b in B, c in C. Sorting gives O(n^2) time. The 3SUM hypothesis said that
n^{2 - o(1)} time is needed, until the paper.

**Exact Triangle and APSP.** In a complete tripartite graph with integer edge weights, *all-edges Exact Triangle*
asks, for every edge (a, b), whether some c closes a triangle of total weight zero. The (min,+) product and APSP
(all-pairs shortest paths, integer weights, no negative cycle) reduce to it. The textbook time is n^3.

The paper reduces all of these to evaluating a thin integer matrix product X (N x D) Y (D x N), D = N^eps, on a
sparse set W of wanted entries. It evaluates that product faster than N^2 by Schönhage's identity, recursed as in
Coppersmith's algorithm. One such product with |W| <= N^2/sqrt D costs N^{2 - sigma + o(1)}, where

    sigma = min(eps gamma, eps (1/2 - q), 1 - eps E)        (boxes, queries, encodings)

and gamma, q, E are explicit functions of the recursion parameters c and theta (`certificates/certify.py`).
The paper's deterministic reductions keep only part of sigma. Exact Triangle to the thin product keeps half, because
one deterministic prime decides every scan. 3SUM and APSP then keep a half and a third of that.

## 2. Results

Model throughout: word RAM with Theta(log n)-bit words, integer inputs in [-n^nu, n^nu] for a constant nu >= 1.
Running times are worst case. Exponents are upper bounds rounded **up** from exact arb endpoints, and each O(n^e)
has e strictly above the certified value, so it absorbs every n^{o(1)} factor. Savings are rounded **down**.

**Theorem 1 (derandomised route; `proofs/derandomisation.md`).** On the word RAM with Theta(log n)-bit words and
integer inputs in [-n^nu, n^nu] (nu >= 1 constant), there are deterministic algorithms with worst-case running times:
3SUM in O(n^{1.996001}); all-edges Exact Triangle, (min,+)-product and APSP (no negative cycles) in O(n^{2.996001}).
More generally n^{2 - sigma + o(1)} and n^{3 - sigma + o(1)} with sigma = min(eps gamma, eps(1/2 - q)) for rational
c > 10, 0 < theta < 0.9 and 0 < eps < 1/(E + gamma). Using only the lemmas of Alman and Vassilevska Williams
(cor:tradeoff), the exponents are 1.996291 and 2.996291; the 1.996001 / 2.996001 figures also use the exact leaf
count and pruned encodings of ImprovedExponents. Credit: KPP16 (Set Disjointness shape), FKP24 (interval groups,
prime-at-a-time moduli), the paper (Thm 17 instances, counting false positives with the oracle), VW10/VW18 and VW13
(the (min,+) chain), ImprovedExponents (the oracle tier and the Lean-checked all-edges APSP chain). New: the
survivor-restricted greedy chains and the weight H.

The certified savings are sigma >= 0.003709895012 (paper lemmas) and sigma >= 0.003999289713 (exact count + pruned
encoding (after ImprovedExponents secs. 3-4)), at exact rational points. The survivor-restricted greedy chains are new
only in their criterion; the construction itself is known (Credits). The 3SUM algorithm is a decision algorithm; a
solution costs O(log n) more decisions, and we claim no listing version.

**Theorem 1' (folded residue instances; `proofs/stacked.md`).** Same model. Deterministic all-edges Exact Triangle,
(min,+)-product and APSP (no negative cycles) in O(n^{2.995943}) (sigma >= 0.004057248470, exact count + pruned
encoding), and O(n^{2.996240}) with the paper's lemmas only (sigma >= 0.003760515625). The M residue instances of one
Exact Triangle piece share their right matrix up to a column shift, so the decoding x M0 + y of the 3SUM route stacks
them into one square product, which pays the encodings once on a side sqrt(M) n. Only the Theorem O hypothesis of
these instances changes, from eps (E + gamma) < 1 to eps (E + gamma - 1/4) < 1; every other lemma of Theorem 1 is
unchanged. 3SUM is not affected by this step.

**Theorem 2 (hash-free route L1; `proofs/l1.md`).** Deterministic all-edges Exact Triangle, (min,+) product and APSP
in O(n^2.99633), and 3SUM in O(n^1.99633) (S >= 0.003677999). With the paper's lemmas only: O(n^2.99657) and
O(n^1.99657) (S >= 0.003431999). It uses no hashing at all, so it is an independent second route.

**Theorem 3 (shared leaves in the pruned recursion, the band gain; `proofs/bands.md`, Theorem C'').** Same model.
Deterministic 3SUM in O(n^{1.995782}) (sigma >= 0.0042181468, upper end 1.995781854), with window moves per element
(Lemma Y) and segments of lengths 8 and 9 mixed 7/10 : 3/10; with segments of length 8 only, O(n^{1.995784})
(sigma >= 0.0042165295). Without Lemma Y (Theorem C' of `bands.md`), O(n^{1.995786}) (sigma >= 0.0042143770), and
two simpler tiers give O(n^{1.995809}) (shifted keys with adjacent moves only, sigma >= 0.0041917719) and
O(n^{1.995854}) (worst keys, no shift, sigma >= 0.0041463659). Without the zone moves of Rule Z either (Theorem C of
`bands.md`) the three tiers give O(n^{1.995790}), O(n^{1.995812}) and O(n^{1.995857}). Theorem 1 knows its wanted
entries before each thin product, so it can use the paper's pruned recursion, whose cost is the number of leaves it
reaches, in place of the box data structure. With residue buckets in place of interval groups, the wanted set is a union of translates (key fibres), and
a leaf shared by several wanted entries is charged only to its lexicographically first one. The fraction of leaves
that survive this charging is a carry-chain law in the keys: 22/27 per gap in the worst case, 62/81 under a
deterministically chosen shift, and less with moves along whole stretches. In the low levels that carry Theorem 1's
decoding digits, a move whose new term equals the old digit pair changes nothing but the cell, so a gap there blocks
with law 8/9 for every key (Lemma Z). Finally, every element of a leaf's d-set can be tested on its own against every
free level below it in its segment, across the levels of the inner set in between, which carry no digit (Lemma Y);
this gives exact per-segment polynomials in place of the per-gap factors. The tiers use the exact count + pruned
encoding values of gamma and E. Exact Triangle and APSP do not gain from this step, as their wanted sets have no
translation structure.

**Remark (Las Vegas).** For integer weights, Las Vegas all-edges Exact Triangle and APSP run in O(n^2.99601) by an
AND over independent random primes (`derandomisation.md`, Appendix B). This is KPP16's amplification on the paper's
instances, and the Monte Carlo exponent already follows from VX20 with the paper's theorem. Theorem 1 supersedes it.

### Against the paper, model by model

delta is the saving below the trivial exponent (2 for 3SUM, 3 otherwise). For the paper, delta is the exact value
behind its printed bound: eps'/2 = 0.000875 behind 1.9992 for 3SUM, eps'/3 = 0.000583 behind 2.99942 for APSP, and
eps' = 0.00175 behind 2.9983 for Exact Triangle. Ratios are rounded down.

| model / problem | paper | ours | delta (paper) | delta (ours) | ratio |
|---|---|---|---|---|---|
| deterministic 3SUM | 1.9992 | **1.995782** (Theorem 3, Lemma Y, lengths 8 and 9) | 0.000875 | 0.0042181 | x4.82 |
| | | 1.995784 (Theorem 3, Lemma Y, length 8) | | 0.0042165 | x4.81 |
| | | 1.995786 (Theorem 3 without Lemma Y) | | 0.0042143 | x4.81 |
| | | 1.995809 (Theorem 3, shifted keys, adjacent moves) | | 0.0041917 | x4.79 |
| | | 1.995854 (Theorem 3, worst keys) | | 0.0041463 | x4.73 |
| | | 1.995790 (Theorem 3 without zone moves) | | 0.0042108 | x4.81 |
| | | 1.996001 (Theorem 1, version 1) | | 0.0039992 | x4.57 |
| | | 1.996291 (Theorem 1, paper lemmas) | | 0.0037098 | x4.23 |
| | | 1.99633 (Theorem 2) | | 0.0036779 | x4.20 |
| deterministic Exact Triangle | 2.9983 (decision) | **2.995943** (Theorem 1', all-edges) | 0.00175 | 0.0040572 | x2.31 |
| | | 2.996001 (Theorem 1, all-edges, version 1) | | 0.0039992 | x2.28 |
| | | 2.99633 (Theorem 2, all-edges) | | 0.0036779 | x2.10 |
| deterministic (min,+) / APSP | 2.99942 | **2.995943** (Theorem 1') | 0.000583 | 0.0040572 | x6.95 |
| | | 2.996240 (Theorem 1', paper lemmas) | | 0.0037605 | x6.44 |
| | | 2.996001 (Theorem 1, version 1) | | 0.0039992 | x6.85 |
| | | 2.996291 (Theorem 1, paper lemmas) | | 0.0037098 | x6.35 |
| | | 2.99633 (Theorem 2) | | 0.0036779 | x6.30 |
| Las Vegas APSP / ET, integer weights | 2.998 (real RAM, `thm:real`) | 2.99601 (remark) | 0.002 | 0.0039992 | x1.99 |

Against version 1 of this repository, the saving grows by 5.4% for 3SUM (0.0039993 to 0.0042181, Theorem 3) and by
1.4% for all-edges Exact Triangle, (min,+) and APSP (0.0039993 to 0.0040572, Theorem 1'); `bands4_cert.py` and
`stacked_cert.py` print these ratios, rounded down from the certified endpoints (x1.0547 and x1.0144).

The deterministic 3SUM bound is also below the paper's Las Vegas bound (1.998) and its randomised footnote figure
(1.9965). ImprovedExponents improves the paper's own deterministic route to 1.99896 for 3SUM and 2.99791 for APSP.

### Corollaries (deterministic, same model)

Each applies a cited reduction to the theorems above; `certificates/bands4_cert.py`, `stacked_cert.py`,
`derand_cert.py` and `certify_L1.py` print them.

| problem | bound | route |
|---|---|---|
| Convolution-3SUM | O(n^1.995782) (Theorem 3); O(n^1.996001) (Theorem 1); O(n^1.99633) (Theorem 2) | linear-time reduction to 3SUM, x_i = a_i (2n + 1) + i |
| Zero-, Min- and Max-Weight k-Clique | O(n^{k - 0.004057 floor(k/3)}) for every k >= 3, e.g. O(n^5.991886) for k = 6 and O(n^8.987829) for k = 9 (Theorem 1'; version 1: n^{k - 0.0039992 floor(k/3)}) | the paper's Nešetřil-Poljak folding to Exact Triangle on n^{floor(k/3)} vertices, on Theorem 1'; Min/Max via VW13 as in the paper (`proofs/stacked.md`, Corollary E) |
| (min,+)-convolution | n^{1.998162 + o(1)} = O(n^1.99817) | Theorem 2 and BCD14 (sqrt n (min,+) products of sqrt n x sqrt n matrices) |

## 3. The method in one page

**Where the paper loses.** Its Theorem 17 hashes all weights modulo one prime p ~ sqrt D and scans every pair that
the thin product reports. The false-positive scans times the number of instances is a fixed quantity, so balancing
them keeps sigma/2. KPP16 avoid the balance for 3SUM with an AND over O(log n) independent hashes: a query counts as
positive only if every hash accepts it, so false positives die with probability 1 - 1/poly. That needs randomness.

**Theorem 1: the AND, chosen deterministically.** Group A, B, C into intervals (FKP24), so that only O(g^2) group
triples can hold a solution. For a modulus m, the number of pseudo-solutions a + b ≡ c (mod m) of every query (a,
group pair) is one entry of a thin product with D = m (FKP24's sets), so the oracle returns all of them at once.
Build a chain modulus one small prime at a time (primes near n^{1/sqrt(log n)}), choosing each prime to minimise the
total pseudo-solution count over the queries that **survived the earlier chains**. A nonzero a + b - c has few prime
factors, so averaging over the primes contracts the count by a factor n^{-Omega(1/sqrt(log n))}. The minimum is at
most the average, so every chain halves the survivors in a no-instance, while a true solution survives every chain.
After O(log n) chains the survivors are empty iff there is no solution. Each chain is n^{o(1)} thin products at
density 1/2, so 3SUM costs n^{2 - sigma + o(1)} with no loss.

**All-edges Exact Triangle without scans.** A true zero triangle is counted under every modulus, so plain counts never
halve. Weight every match S by h(S), the number of the first t primes (product > 3U) that do not divide S. Then
h(0) = 0 and h(S) >= 1 otherwise, and the weighted count is a difference of t + 1 plain counts. The weighted survivors
halve in every instance, and a slot that passes every plain count but drops out of the weighted ones must contain a
zero. This gives exact all-edges output in n^{3 - sigma + o(1)}. The (min,+) product and APSP follow on the same
vertices by parallel binary search and the dyadic negative-to-zero reduction (VW10, VW13).

**Theorem 2: no hashing at all.** Chan and Xu's bit-halving recursion keeps, for every pair and block of d vertices,
a pivot whose weight sum is known up to a constant window. At the next level the near-witnesses are counted exactly
with Fredman's trick as comparison counts, which the paper's Matoušek-style lemma turns into thin products. Witnesses
are found deterministically by Alon and Naor's dilution with the counting oracle. Queries, same-block pairs and boxes
bind together (`certify_L1.py`).

**Theorem 1': fold the residue instances.** For a modulus M, Theorem 1 builds M separate Exact Triangle instances per
piece of C, one per residue of w(a, b), each of side n. Their right matrices are the same up to a shift of the column
index, so one square product of side about sqrt(M) n, with rows (x, a) and columns (y, b), reads every count at the
position given by r = w(a, b) mod M = x M0 - y. Boxes and queries cost what they cost before; the encodings are paid
once on the larger side instead of M times, which relaxes the condition on eps to eps (E + gamma - 1/4) < 1.

**Theorem 3: charge each shared leaf once.** The paper's pruned recursion visits the union of the leaves of the wanted
entries, but the paper bounds that union by charging every entry for all its leaves of low order. Theorem 1's 3SUM
route knows its wanted set before each product, so the pruned recursion can replace the box data structure there.
With residue buckets (a prime chosen by collision counts, heavy residues recursed on) the wanted set is a union of
key fibres. A leaf of order d has many members; it is charged only to the member whose d-set is lexicographically
smallest, and an entry is charged for a leaf only when no element of the leaf's d-set can move to a lower free level
inside the same fibre. Placing whole classes of inner sets (by their counts per segment of 8 levels) on single
diagonals of the tile makes every such move available, and the fraction of blocked moves follows from the carry chain
of the key (Lemmas 3.1 to 3.3 of `bands.md`). In the zone, where the levels hold the decoding digits x and y, a move
is allowed only when the new term equals the old digit pair; the key is then unchanged, and one term in nine moves
for every key (Lemma Z, Sec. 9 of `bands.md`). Last, the lowest-element and stretch restrictions go: every element
of the d-set is tested on its own against every free level below it in its segment. The levels of the inner set in
between carry no digit, so the key test is one window equation on the entry's own digits (Lemma Y, Sec. 10), and the
class average of a segment becomes an exact polynomial, computed for segment lengths 8 and 9. A fixed mix of the two
lengths (7 of 10 segments of length 8) keeps every class small enough to fit whole on one diagonal and the filler
cells cheap enough, and gives O(n^1.995782).

## 4. Status: what is proved, certified, Lean-checked, sketched

| item | status |
|---|---|
| Theorem 1 (`derandomisation.md`) | Full written proof. Two internal adversarial reviews: the first checked a sketch step by step; the second checked the full text, including the APSP chain, and found it correct (its qualifier, four textual fixes and stronger stress test are applied) |
| Theorem 1', folded residue instances (`stacked.md`) | Full written proof; one internal adversarial review, which re-checked the decoding exhaustively for every modulus up to 5000 and found no gap |
| Theorem 3, shared leaves (`bands.md`) | Full written proof; one internal adversarial review confirmed all three tiers of Theorem C (the stretch tier with the fewest independent checks) and recomputed every value independently; its requested changes are applied. A second internal adversarial review confirmed Lemma Z and Theorem C' (Sec. 9), with its own toy check and an independent recomputation of the three tiers. A third internal adversarial review confirmed Lemma Y and Theorem C'' (Sec. 10) with its own segment polynomials, its own arb recomputation and an end-to-end toy check with mixed segment lengths; its requested changes are applied (the condition that a class fits a diagonal, and the scope of the limits stated in Sec. 10) |
| Theorem 2, L1 (`l1.md`) | Full written proof; one internal adversarial review, after two fixes (3SUM window [-7, 8]; Alon-Naor bias 2^{-7c-1} for 3SUM) |
| Corollaries | Compositions of Theorems 1, 1', 2 and 3 with the cited reductions; not separately reviewed |
| Remark, Las Vegas route (Appendix B) | Proof; one internal adversarial review |
| Exact count and pruned encodings (Appendix A) | Short arguments on the paper's construction; reviewed once; public earlier, Lean-checked, in ImprovedExponents |
| All saving values | arb ball arithmetic (200 bits) at fixed rational points, every side condition checked on the whole ball (`certificates/`) |
| Negative triangle to Exact Triangle (Appendix C) | Proof; exhaustive and end-to-end checks against brute force with a negative control (`check_negtri.py`) |
| Theorem 3's lemmas on small cases | Mechanical checks against brute force or exact enumeration: the canonical-representative bound on every leaf (including grids where the moves are used), the carry and stretch laws exhaustively, the class average exactly, and the residue buckets with their recursion; each has negative controls that must fail (`check_bands_*.py`). `tests/test_bands.py` also recomputes the three savings by an independent method. `tests/test_bands_zone.py` checks Lemma Z on toy grids by brute force over every leaf (no Rule-Z target leaves W, R_d equals the 8/9 generating function), with a wrapped-diagonal control that must fail, and recomputes the savings of Theorem C'. `check_bands_y.py` checks Lemma Y end to end on toy tiles with mixed segment lengths (every target in W with the same key, the representative bound for every entry, the generating function), with three controls that must fail (a naive window that ignores the rank shift, targets in the segment below, Rule Y inside the zone). `tests/test_bands_y.py` recomputes the Lemma Y polynomials and the two savings independently |
| Lemma 3.2' on small instances | The folded product against a direct count on 24746 slots, with two negative controls (`check_stacked.py`) |
| Theorem 1's constructions on small instances | Mechanical check against brute force, including a stress run that exercises the greedy choice and asserts the halving lemmas on every chain, with three negative controls that must fail (`check_derand.py`, `check_derand_controls.py`) |
| Lean (`lean/`) | Lean 4 kernel checks (Mathlib, standard axioms only, no `sorry` or `native_decide`) of the arithmetic of every certificate point in `derand_cert.py`, `certify_L1.py` and `certify.py`: each side condition, the saving and the 3SUM and APSP exponents (with the O(n^e) lines), at the exact rational point, with negative controls. Also the finite integer lemmas of Theorem 2 and Appendix C (bit-halving windows, Fredman's identity, the unique-witness test, the Alon-Naor bias, the negative-to-zero reduction). `Stacked.lean` and `KClique.lean` check the same for `stacked_cert.py` (Theorem 1') and its k-Clique corollary. Not in Lean: the reductions and cost accounting, which are the paper proofs above, and `certify_levers.py` |
| Lean for Theorem 3 | Lean-checked (`lean/`, `Bands2*.lean`, `Bands3*.lean` and `Bands4*.lean`; standard axioms only, no `sorry` or `native_decide`): the arithmetic of both points of `bands4_cert.py` (Theorem C'', O(n^1.995782) and O(n^1.995784)), from the exact Lemma Y polynomials, with each side condition including the diagonal fit, and of all three tiers of `bands3_cert.py` (Theorem C') and of `bands_cert.py` (Theorem C) at their exact rational points, with each side condition, the saving, the 3SUM exponent and the O(n^e) line (O(n^1.995854), O(n^1.995809), O(n^1.995786); without zone moves O(n^1.995857), O(n^1.995812), O(n^1.995790)), and four negative controls per tier or point (and one more for the diagonal fit). Also the 22/27 and 62/81 digit laws, the 8/9 zone law and the stretch law b(len) for len <= 7, by kernel computation. Not in Lean: the reductions and cost accounting (`bands.md`), the probabilistic content of Lemmas 3.1 to 3.3, Lemma Y, and that the polynomial tables are the averages they claim to be (`bands4_poly.py` computes them two independent ways) |
| The paper's theorems | Assumed as published (its main theorems are Lean-formalised in anthropics/formal-math) |

The mechanical checks test logic on small instances, not asymptotics. The arb certificates and their Lean versions
check arithmetic, not the reductions.

## 5. Reproduce

Requires Python 3.9 or newer, `python-flint` and `numpy` (`pip install -r requirements.txt`; tested with 0.6.0 and
2.0.2; numpy is used only by `bands4_poly.py` and `tests/test_bands_y.py`).

```sh
make              # all certificates, the mechanical checks and the tests on their printed values (about 9 min)
make certificates # the certificates and checks alone, printing every claim
make lean         # the Lean 4 kernel checks (lean/README.md; elan with Lean v4.34.1, Mathlib cache; about 13 min on 3 cores, plus about 35 min on 2 cores for Theorem 3, about 7 min for Theorem C' and about 7 min for Theorem C'')
```

| script | prints |
|---|---|
| `certificates/derand_cert.py` | Theorem 1 savings and exponents (both tiers and the paper's point), Convolution-3SUM and k-Clique |
| `certificates/certify_L1.py` | Theorem 2 savings, all seven cost terms, exponents, Convolution-3SUM and (min,+)-convolution |
| `certificates/certify_levers.py` | the Las Vegas remark, and the paper's single-prime route with Appendix C for comparison |
| `certificates/certify.py` | the shared closed forms, and the paper's Theorem 17 route re-tuned (comparison only) |
| `certificates/check_negtri.py` | Appendix C: identity, full reduction against brute force, negative control |
| `certificates/check_derand.py`, `check_derand_controls.py` | Theorem 1's constructions against brute force (basic and stress runs), and three controls that must fail |
| `certificates/stacked_cert.py` | Theorem 1' savings and exponents (both tiers), the k-Clique exponents for k = 3..12, Convolution-3SUM through Exact Triangle, the controls, and the ratios to version 1 and the paper |
| `certificates/check_stacked.py` | Lemma 3.2' against a direct count, and two controls that must fail |
| `certificates/bands_cert.py` | Theorem 3 savings and exponents (three tiers), the layout cost, the b = 1 control (Theorem 1's saving), two controls that must fail, Convolution-3SUM and the ratios to version 1 and the paper |
| `certificates/bands3_cert.py` | Theorem 3 with zone moves (Theorem C'): savings and exponents (three tiers), the layout cost, two controls that reduce to `bands_cert.py` (zone law 1), two controls that must fail, Convolution-3SUM and the ratios to Theorem C, version 1 and the paper |
| `certificates/bands4_poly.py` | the exact Lemma Y and Rule Z segment polynomials for lengths 8 and 9, by two independent implementations (saved in `bands4_poly.json`) |
| `certificates/bands4_cert.py` | Theorem 3 with Lemma Y and mixed segment lengths (Theorem C''): savings and exponents at both points, the diagonal fit, the no-sharing control (Theorem 1's saving), four controls that must fail, Convolution-3SUM and the ratios to Theorem C', version 1 and the paper |
| `certificates/check_bands_y.py` | Lemma Y end to end on toy tiles with mixed segment lengths, with three controls that must fail (about 20 min; one case in about 2 min) |
| `certificates/check_bands_rep.py`, `check_bands_carry.py`, `check_bands_stretch.py`, `check_bands_segments.py`, `check_bands_buckets.py` | Lemmas 2.1-2.2, 3.1-3.2, 3.3, 4.1 and Sec. 6 of `bands.md` against brute force or exact enumeration, each with negative controls |

The new scripts keep their output in a `.out` file next to them. `tests/test_certificates.py`, `tests/test_bands.py`,
`tests/test_bands_zone.py` and `tests/test_bands_y.py` run each script once and check its printed values against this
README (and the new scripts' output against the saved `.out` files); `test_bands.py`, `test_bands_zone.py` and
`test_bands_y.py` also recompute Theorem 3's savings independently, and `test_bands_zone.py` checks Lemma Z on toy
grids. `test_bands_y.py` runs case 0 of `check_bands_y.py` and compares it with the saved output. The mechanical checks and the new
certificates refuse to run under `python -O`, which would strip their `assert` statements.

## Further notes

- [docs/CLOSED_IDEAS.md](docs/CLOSED_IDEAS.md): approaches we tried that do not improve the saving, each with its reason and model.

## Attribution

Author: **Swapnil Jain**. Research, implementation and drafting were done with assistance from Claude (Anthropic).
AI assistance is not independent review. Licensed under Apache-2.0.
