# Closed ideas

This file lists approaches to faster 3SUM and APSP, built on the thin-product method of Alman and Vassilevska
Williams (arXiv 2610.06783, "AVW"), that we tried and found do not improve the saving. Each row has a stated reason.
We list it so that other researchers and automated searches do not spend time on these routes again.

**Contributing.** Please check this list before starting on a route, so effort is not duplicated. If you find a
mistake in a closure, an idea that escapes a stated hypothesis, or a closed route of your own, open an issue or a
pull request with the argument or certificate. New closures and corrections are welcome and will be credited.

**Scope.** A closure holds only inside its stated model or hypotheses: the cost model of the thin product as AVW
charge it, a stated class of identities, tests or reductions, or one route. Nothing here is a lower bound for 3SUM or
APSP in general. The hypotheses of a closure show where an escape would have to break the model. An idea that
breaks a stated hypothesis is not covered by the row.

**Status labels.** [proof]: a complete argument. [cert]: interval-arithmetic or exact computer certificate, upper
bounds rounded up. [exp]: a decisive experiment. [arg]: a short argument, convincing but not written as a full proof.
"Internally reviewed" means an adversarial check by a separate review pass of our own. It is not independent peer
review. For the no-go theorems we give only the statement and model here. Their proofs are in preparation for a
later paper.

**Notation.** The thin product multiplies X (N x D) by Y (D x N), D = N^eps, on a wanted set W with
|W| <= N^2 D^{-a}. The saving sigma is defined as in the README. For a zero test, a *slot* holds J candidate pairs and
the test decides whether any pair is an exact match. An *identity* is a bilinear identity of the AVW kind,
<a,1,b> + <1,D0,1> with one outer term per output ("one-term-per-output"), Schönhage's <3,1,3> + <1,4,1> being the
one AVW use.

## 1. Identities

| idea | why it fails | status | credit |
|---|---|---|---|
| Plug in better omega or alpha (rectangular matrix multiplication bounds) | omega enters only through the choice of the hashing prime, which is far from binding; alpha-type bounds give N^{2+o(1)} for the full product | [proof] | Le Gall–Urrutia, Vassilevska Williams–Xu–Xu–Zhou, Alman et al., Uznański (2610.10494) |
| A bigger exact one-term-per-output identity with one inner output (e = 1) | Statement: an exact identity of rank ab + 1 for <a,1,b> + <1,D0,1> whose error terms are the harmless ones AVW allow has D0 <= max(1, (a-1)(b-1)), so Schönhage's identity is optimal. Model: exact decompositions over any field, also over Z/p^k. Proof in preparation | [proof], internally reviewed | asserted without proof as a remark by Kassabov, Landsberg, Souza and Speegle (KLSS, 2608.27434); char-p variant suggested by jacklightChen and rohanarun |
| Other shapes (a, b) inside Schönhage's family | (3,3) is best; every other shape is well below it | [exp] | found first by ImprovedExponents (shape table) |
| Several terms per outer output, or several private terms per inner output | t terms per output multiply the query cost by t^{L-m}; two or more private inner terms give no saving at any D0 | [proof] / [exp] | |
| Identities with several inner outputs (e >= 2), any field | Statement: dimension bounds on D0, e1, e2 for every exact one-term-per-output identity in which every outer term feeds every inner output; under the AVW cost, extended to e >= 2, every such identity has sigma <= 0.0053, against 0.0040 for Schönhage. The targets (5,5) with e = 9 and (6,6) with e = 16 are impossible. Model: AVW's cost, with the e-dependence an argued extension (AVW treat e = 1). Proof in preparation | [proof] + [cert], internally reviewed | |
| Conjecture "for e >= 2 the maximum is D0 = a + b - 2 - e" | Refuted: (5,5) with inner <1,8,2> is an exact identity above it | [exp] (exact) | |
| "The asymptotic sum inequality plus flattenings caps sigma at about 0.0105 unless omega improves" | Refuted as a uniform cap: the profile <2,1,3> + <2,2,3>, D0 = 2 passes both filters with implied omega >= 2.45 and model saving >= 0.0119. That profile is itself unrealisable: an exact Koszul flattening gives border rank >= 14 > 12 | [cert] + [exp] (exact), internally reviewed | Schönhage (asymptotic sum inequality); Landsberg–Ottaviani (Koszul flattenings) |
| Use the threshold eps* as a lever for 3SUM | d sigma / d eps* = 0 at the optimum; any gain there is a reduction of the encoding term. eps* is also sharp for AVW's theorem as stated, since that theorem is uniform over q > 0 | [proof] | AVW |
| Different switching thresholds at different recursion levels, one identity | Levels are exchangeable, so the optimal region is the uniform one: gain 0 | [proof] | |
| Ring changes: labels in Z[x]/(x^p - 1), random weights over F_q, word packing | The polynomial ring loses a factor p^{1+gamma}; F_q weights change nothing; packing gives log factors | [proof] / [arg] | |

## 2. Hashing and reductions on the deterministic route

| idea | why it fails | status | credit |
|---|---|---|---|
| False-positive floor for modular tests | Statement: one random gapped-interval no-instance has few zero counts under every modulus m <= s^2/J at once (s the interval-group size), so every sound schedule of modular tests pays at least a constant fraction of one solve at modulus about s^2, and the density a <= 1/2 is forced. Model: queries (a, B, C) answered by counts of a + b - c = 0 mod m (or through a homomorphism into a finite abelian group), adaptive and composite moduli allowed, each test charged a full-grid thin product, fixed interval partition, a query discarded by one zero count; values up to n^nu with nu >= 5 (or nu > 3 with a wider gap). Proof in preparation | [proof], internally reviewed | builds on KPP16 and FKP24 |
| Any other data-independent label instead of a modulus (almost-linear, Bohr, multiply-shift, rounding, window products, random or few-bit data-dependent hashes) | Statement: on the same kind of instance, every label test whose count reads c only through a label lambda(c) and is correct on true sums has zero fraction at most min(1, 138/J, 2exp(-(J/51)^{1/3})), simultaneously for exponentially large families chosen after seeing the input; a collision lambda(c) = lambda(a + b) is a pseudo-solution. Same model as above. Proof in preparation | [proof], internally reviewed | |
| Data-dependent partitions of B and C before hashing | Any partitions (adaptive, even exponential-time) whose test kernels have lcm <= s^2/J leave almost all FKP24 incidences unexcluded; a short corollary of the floor above by divisibility | [proof], internally reviewed | FKP24 (interval groups) |
| Fully data-dependent labels | Any floor for them would be a 3SUM lower bound: on a no-instance a two-label map is correct and makes every count zero | [proof] (elementary), internally reviewed | |
| Structure theorems for approximate homomorphisms as the closer | Almost-linear hashes into Z_D are Bohr hashes up to constant error, but the label-test floor above does not need this | [proof], internally reviewed (folklore) | Hyers–Ulam stability |
| AND of hashes at false-positive density a > 1/2 | Every query then has a false positive in every round; a = 1/2 is optimal for this shape, the derandomised one included | [proof], internally reviewed | KPP16 |
| "No hash family can help" | Refuted by amplification: an AND over independent hashes kills false positives | [proof] | KPP16 |
| FKP24's derandomisation as published | Keeps about sigma/1000 once the hashing-lemma and residual-scan terms are counted; at best sigma/9 when re-tuned. Refutes an earlier "sigma/7" estimate | [proof], internally reviewed | FKP24 |
| Enumerate candidate primes per chain; small-bias sample spaces as black boxes | n^{eps/2} solves add about +0.028 to the exponent, far above the saving | [arg] | |
| Collision-only hashing | Controls only the first moment of false positives, so it cannot replace the AND | [arg] | Chan–He; Chan–Lewenstein |
| Almost-linear hashing with balanced buckets | No longer needed: exact modular hashing with interval groups removes the off-by-one and heavy-bucket cases; packing gives log factors | [arg] | Baran–Demaine–Pătraşcu; Dietzfelbinger |
| Share work across chains or candidate primes (CRT sub-encodings, shrinking later chains) | The number of solves is n^{o(1)}, so sharing moves sigma by 0; CRT does not compose pair counts (counterexample); the first chain is binding; chains ending below modulus s^2 keep a 1 - e^{-s^2/m} fraction of queries | [proof] + [exp] | |
| Cheaper binding solve: composite modulus, residue pre-splitting of the queries | A composite modulus has no CRT factorisation of the counts, and equivariance is already used; a residue split is a smaller block size with the same saving | [proof] | |
| Unequal interval-group sizes for A, B, C | The total size constraint makes the density exponent minimal at the symmetric choice, i.e. a = 1/2 | [arg] | |
| Monte Carlo instead of Las Vegas | No gain: every route here is already zero-error | [proof], internally reviewed | |
| KPP16 on the real RAM | It needs hashing, which the real RAM does not provide | [arg] | KPP16 |
| "VX20's Exact Triangle reduction keeps only half of sigma" | Refuted: at the thin-product parameters it keeps all of sigma(1/2), Monte Carlo | [proof], internally reviewed | Vassilevska Williams–Xu |
| Route an auxiliary step back through the fast primitive (self-call on queries or false positives) | Circular: the query is a 2SUM and the batch is a block 3SUM of the same size | [arg] | suggested by eumemic |

## 3. Zero tests (paying per decision)

| idea | why it fails | status | credit |
|---|---|---|---|
| Oblivious analytic decoders (power sums or other real-analytic functions fixed in advance) | Statement: deciding a slot needs k >= J calls. Model: each call returns a sum of separable real-analytic functions over the slot, chosen before any answer. Proof in preparation | [proof] | |
| Adaptive tests with yes/no answers | Statement: k >= (1 - 2 eps - o(1)) sqrt(J / ln 2) calls, adaptive, randomised, two-sided error eps; counts capped at c need sqrt(J / ((c + 1) ln J)). Proof in preparation | [proof] | |
| Certified separable counts: hash buckets, residue classes, CRT trees, adaptive value-space refinement, colour searches, Prony inside buckets, any mixture | Statement: calls plus direct checks number at least sqrt(J / (6.24 b + 9.24)) for b-bit answers, and at least 2 sqrt(J) for covers fixed in advance. Model: each call returns sum_u f_u(x_u) g_u(y_u), and a "no match" answer must name, for each unchecked position, calls whose supports cover the diagonal. Bucket-Prony meets it up to logs. Proof in preparation | [proof] | Prony; bucket hashing |
| Use a sublinear zero test to raise the density a | At J^{1/2} calls per slot the instance terms reproduce exactly the a = 1/2 budget (J = s^2/D), so the lever gives 0 in the models above | [proof] | |
| Count divisors (few prime factors, inclusion–exclusion over divisors) | A threshold test needs more than J w primes, so it costs more than J; joint counts need rank above 3R | [proof] | |
| Additive energy or Plünnecke bounds on the matched sums | The differences are adversarial, so no doubling bound applies | [arg] | Plünnecke |
| Batch the failed checks with fast matrix multiplication | The batch is itself an Exact Triangle on a dense triple set | [arg] | |
| Cancel false positives in bulk by segments (runs across numerical scales) | Statement: under any label test, a discarded query needs at least as many segments as there are b with a label pseudo-solution, at least 0.158 min(s, J) in expectation, so the per-query cost exponent is >= 1/2 and the gain is 0. Model: disjoint one-dimensional segments with a single b, unit cost each. Proof in preparation | [proof], internally reviewed | Chi–Duan–Xie–Zhang (CDXZ); JPSX (2605.07150) |

## 4. Encodings and tiles

| idea | why it fails | status | credit |
|---|---|---|---|
| Make the encoding term free on one instance | The encoding exponent E is the tile side, not the table size: on Schönhage's profile sigma rises by at most x1.00403 | [cert] | |
| Share tiles across instances (any sharing that keeps boxes and queries) | A tile still has at least (sqrt M)^{L-m} columns: at most x1.09187 on Schönhage's profile | [cert] | |
| Schönhage's profile, any parameters (c, theta) | sigma <= 0.0039993 | [cert] | first by ImprovedExponents |
| Combination of outputs instead of tiling (plain, bootstrapped, laser or Coppersmith–Winograd style) | gamma becomes (gamma - mu)/(1 + mu), which is worse; a bootstrap pays one operation per entry. Refutes an earlier x1.16 estimate | [proof] in the cost model | Coppersmith–Winograd |
| Four Russians, word packing of the encodings | Polylogarithmic factors only | [arg] | |
| Reuse sub-tables across levels; sparser slot families | By Kruskal–Katona this equals a smaller c; a random fraction loses | [arg] | Kruskal–Katona |
| Asymmetric blocks on one square instance | AM-GM forces the symmetric choice | [proof] | |
| Count encodings modulo the inputs | Only order-0 leaves are inputs; the maximum is unchanged (x1.00) | [exp] | suggested by icekylinx |
| Merge leaves with equal response to drop encodings | Shrinks the table, not the tile side: at most x1.004 | [proof] | suggested by eumemic |
| Concave consolidation or majorization of charged pieces (contiguous blocks, shrunk frames, terminal elimination) | The only fixed per-piece charge is the encodings, so the tile-sharing cap applies | [proof] | suggested by rohanarun, djsmanchanda, SovereignSteak, GamingPuzzled, icekylinx |
| One paid completion across several stages | A tile has at least (sqrt M)^{L-m} columns whatever is shared, so the tile-sharing cap applies | [proof] | suggested by jacobalansussman, hcg890 |
| Batch residual leaves into full boxes ("banks", bin filling) | The cost is already the per-order minimum of box and query cost; bin fill is tile fit, x1.004 | [proof] | suggested by evmckinney9, rohanarun, maxime-fleury |
| Absorb a charged term into a free offset (gauges, merged exteriors) | The charged terms are additive leaf counts; no free offset removes one | [arg] | suggested by eumemic, icekylinx |
| Copy inputs to remove a doubled charge | The best routes have no halving to remove | [arg] | suggested by icekylinx |
| Exact min-cut choice of the box/query split per leaf class | The cost is separable per order, so the threshold rule is already optimal | [proof] | suggested by Th0rgal |

## 5. Layouts and folding

| idea | why it fails | status | credit |
|---|---|---|---|
| Fold the families of instances (chains, candidate primes, interval groups) into one squarer product | There are n^{o(1)} solves, so folding moves sigma by 0; the interval groups are already one product | [proof] | |
| Run k disjoint instances in lockstep as one block-diagonal instance | Cross-block boxes are wasted by a factor k; this reduces to tile sharing | [proof] | suggested by ikeboy, DanieleCorso |
| Chunk the inner dimension, chunk below one group per piece, or add an outer bilinear algorithm on top | Each loses by construction; the optimum is at no chunking | [proof] / [exp] | |
| Stop the recursion early and finish with an outside procedure | Reduces to the chunking case above | [proof] | suggested by icekylinx |
| Inner sets of different sizes | A smaller inner set needs combination, which loses (section 4) | [proof] | |

## 6. Reductions and literature ideas

| idea | why it fails | status | credit |
|---|---|---|---|
| Use Chan–Xu's exact labels as thin instances | The inner dimension becomes n times the size of a block, so the product is not thin; reducing mod p brings back the single-prime false positives | [proof] | Chan–Xu (CX24) |
| Oblivious isolating families for witness finding | A family of size up to d/4 is defeated; Alon–Naor's adaptivity is essential. Refutes "polylog isolating subsets suffice" | [proof], internally reviewed | Alon–Naor |
| Avoid the same-block brute force of the hash-free route by counting only wanted pairs | An adversarial two-scale instance puts at least 1/4 of the same-block work on wanted pairs, so per-incidence methods cannot beat brute force | [proof] + [exp] | Matoušek; Chan–Xu |
| Count same-block incidences in bulk (recursive Matoušek inside blocks) | Priced as thin products, every depth and choice of scales gives a saving at most that of the outer level | [proof] | Matoušek |
| Subpolynomial shavings (Williams; Chan; Grønlund–Pettie; Chan 2020; Pant–Williams 2606.27727) | n^{o(1)} or log factors only | [lit] | as named |
| Kane–Lovett–Moran decision trees | A statement about query complexity, with no running time | [lit] | Kane–Lovett–Moran |
| Sparse matrix multiplication bounds | Give no exponent lever at these densities | [lit] | |
| Same-week follow-ups 2610.10153 (real to integer), 2610.10354 (low-rank 3SUM), 2610.10282 | Lossy or for structured inputs; no exponent lever for the general problem | [lit] | as named |

## 7. Other paradigms

Every route below lands on one of the n^2 endpoints of the thin-product accounting.

| idea | why it fails | status | credit |
|---|---|---|---|
| Reduce to a dense product of another shape (square or fat) and price it by omega | For local encodings (each entry a function of O(1) inputs), label indicators need a label universe of about s^2 per bucket pair, which blows naive work up by D^{1/2}; Fourier encodings make D >= N g^3; exact labels are not thin; power-sum encodings fall to the oblivious zero-test bound | [arg] | |
| Split by popularity (higher-order Balog–Szemerédi–Gowers) and send only the pseudorandom part to the thin product | The pseudorandom part is exactly where the hashing floors are proved, so it keeps sigma(1/2) and the split gains 0 | [arg] | Fischer–Jin–Xu (FJX); Balog–Szemerédi–Gowers |
| Dense/sparse recursion with a cheap pruning test | A test with lcm <= s^2 prunes almost nothing on the floor instance; at s^2 it is the thin product itself; scale-by-scale pruning is the segment case | [arg] | |
| Algebra over F_p: power sums, resultants, modular composition | Counting zeros mod p by power sums is the DFT over Z_p with its n^3/p false positives; an indicator polynomial needs degree >= U - 1; resultants need an n^2-dimensional algebra; Kedlaya–Umans evaluation outputs n^2 values | [proof] / [arg] | Kedlaya–Umans |
| Polynomial method (Razborov–Smolensky) for 3XOR or 3SUM | Membership in a set of size n has probabilistic degree about log n, giving n^{2.755} monomials already at c = 3 | [arg] | Razborov–Smolensky; Abboud–Williams–Yu; Dietzfelbinger–Schlag–Walzer (3XOR) |
| Offline function inversion (3SUM-indexing structures) | Offline preprocessing must cover all n^2 pairs | [arg] | Fiat–Naor; Hellman; Golovnev et al. |
| Block-Toeplitz structure (displacement rank) of the hashed product | The Fourier form is again a thin product with the same D^{1/2} blow-up, and the block correlations form a rank-one polynomial matrix with no inner sum for fast multiplication | [arg] | |

## 8. Shared leaves in the pruned recursion (Theorem 3)

Terms as in `proofs/bands.md`: a leaf shared by several wanted entries is charged to its representative, and an entry
is charged only when no element of the leaf's d-set can move to a lower free level inside the same key fibre; b is
the fraction of the nine terms at an element that cannot move.

| idea | why it fails | status | credit |
|---|---|---|---|
| More single swaps in the zone segments (the levels that hold the decoding digits x and y) than Rule Z allows | Keeping x and y fixes the row and the column string, so every window digit pair must equal the new term and every target needs the same term: at most one of the nine terms moves, b >= 8/9 for every key, which Rule Z already attains. Model: downward single swaps inside one segment that land in the entry's own fibre, windows at ranks below z0 (the elements of the top zone segment whose window reaches higher ranks are an o(1) fraction) | [proof], internally reviewed | |
| Relabel the row and column strings (any injective labelling, input-dependent allowed) or bucket by input-dependent additive maps, so that fewer adjacent moves are blocked | With a key that is a label difference, an adjacent move fixes the rest of the entry, so the three row terms give three row labels, the three column terms give three column labels, and at most one column term per row term keeps the key: b >= 2/3 per adjacent move. In the per-element accounting of Theorem C'' this caps the saving at about 0.004296 to 0.004304, less than 1e-4 above 0.0042181. Model: adjacent moves (to the nearest free level below), difference keys | [proof] (the law) + [float] (the cap value), internally reviewed | |
