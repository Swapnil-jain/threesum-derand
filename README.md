# Deterministic 3SUM in O(n^1.996001)

**Swapnil Jain. A short paper with its artefacts.**

Alman and Vassilevska Williams (arXiv 2610.06783; below "the paper", AVW) gave the first truly subquadratic 3SUM and
truly subcubic APSP algorithms. Their deterministic bounds are O(n^1.9992) for 3SUM and O(n^2.99942) for APSP. Their
conclusion notes that two routes would keep more of their saving: KPP16's reduction for 3SUM, which is randomised,
and the all-edges version of Exact Triangle for APSP. We make both deterministic, and they keep the whole saving.

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
  encodings behind every figure labelled "exact count + pruned encodings", including 1.996001. We found them
  independently, but they were public first, with a Lean formalisation. With the paper's lemmas alone our bound is
  1.996291.
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

**Theorem 1 (derandomised route; `proofs/derandomisation.md`).** There are deterministic algorithms that
- decide 3SUM in **O(n^1.996001)**;
- solve all-edges Exact Triangle, the (min,+) product and APSP (no negative cycles) in **O(n^2.996001)**.

More generally the times are n^{2 - sigma + o(1)} and n^{3 - sigma + o(1)} with sigma = min(eps gamma, eps(1/2 - q)),
for rational c > 10, 0 < theta < 0.9 and 0 < eps < 1/(E + gamma). Using only the paper's lemmas (its Cor.
`cor:tradeoff`), the exponents are 1.996291 and 2.996291 (sigma >= 0.003709895012). The figures 1.996001 / 2.996001
(sigma >= 0.003999289713) also use ImprovedExponents' exact leaf count and pruned encodings. The 3SUM algorithm is a
decision algorithm; a solution costs O(log n) more decisions, and we claim no listing or All-Numbers version.

**Theorem 2 (hash-free route L1; `proofs/l1.md`).** Deterministic all-edges Exact Triangle, (min,+) product and APSP
in O(n^2.99633), and 3SUM in O(n^1.99633) (S >= 0.003677999). With the paper's lemmas only: O(n^2.99657) and
O(n^1.99657) (S >= 0.003431999). It uses no hashing at all, so it is an independent second route.

**Remark (Las Vegas).** For integer weights, Las Vegas all-edges Exact Triangle and APSP run in O(n^2.99601) by an
AND over independent random primes (`derandomisation.md`, Appendix B). This is KPP16's amplification on the paper's
instances, and the Monte Carlo exponent already follows from VX20 with the paper's theorem. Theorem 1 supersedes it.

### Against the paper, model by model

delta is the saving below the trivial exponent (2 for 3SUM, 3 otherwise). For the paper, delta is the exact value
behind its printed bound: eps'/2 = 0.000875 behind 1.9992 for 3SUM, eps'/3 = 0.000583 behind 2.99942 for APSP, and
eps' = 0.00175 behind 2.9983 for Exact Triangle. Ratios are rounded down.

| model / problem | paper | ours | delta (paper) | delta (ours) | ratio |
|---|---|---|---|---|---|
| deterministic 3SUM | 1.9992 | **1.996001** (Theorem 1) | 0.000875 | 0.0039992 | x4.57 |
| | | 1.996291 (Theorem 1, paper lemmas only) | | 0.0037098 | x4.23 |
| | | 1.99633 (Theorem 2) | | 0.0036779 | x4.20 |
| deterministic Exact Triangle | 2.9983 (decision) | **2.996001** (Theorem 1, all-edges) | 0.00175 | 0.0039992 | x2.28 |
| | | 2.99633 (Theorem 2, all-edges) | | 0.0036779 | x2.10 |
| deterministic (min,+) / APSP | 2.99942 | **2.996001** (Theorem 1) | 0.000583 | 0.0039992 | x6.85 |
| | | 2.996291 (Theorem 1, paper lemmas only) | | 0.0037098 | x6.35 |
| | | 2.99633 (Theorem 2) | | 0.0036779 | x6.30 |
| Las Vegas APSP / ET, integer weights | 2.998 (real RAM, `thm:real`) | 2.99601 (remark) | 0.002 | 0.0039992 | x1.99 |

The deterministic 3SUM bound is also below the paper's Las Vegas bound (1.998) and its randomised footnote figure
(1.9965). ImprovedExponents improves the paper's own deterministic route to 1.99896 for 3SUM and 2.99791 for APSP.

### Corollaries (deterministic, same model)

Each applies a cited reduction to the theorems above; `certificates/derand_cert.py` and `certify_L1.py` print them.

| problem | bound | route |
|---|---|---|
| Convolution-3SUM | O(n^1.996001) (Theorem 1); O(n^1.99633) (Theorem 2) | linear-time reduction to 3SUM, x_i = a_i (2n + 1) + i |
| Zero-, Min- and Max-Weight k-Clique | n^{k - 0.0039992 floor(k/3)}, e.g. O(n^5.992002) for k = 6 | the paper's Nešetřil-Poljak folding to Exact Triangle on n^{floor(k/3)} vertices, on Theorem 1; Min/Max via VW13 as in the paper |
| (min,+)-convolution | n^{1.998162 + o(1)} = O(n^1.99817) | Theorem 2 and BCD14 (sqrt n (min,+) products of sqrt n x sqrt n matrices) |

Future work, unverified: deterministic 3XOR and All-Numbers 3SUM at the Theorem 1 exponent look reachable by the same
chains. We have sketches only and claim nothing.

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
with Fredman's trick as comparison counts, which the paper's Matousek-style lemma turns into thin products. Witnesses
are found deterministically by Alon and Naor's dilution with the counting oracle. Queries, same-block pairs and boxes
bind together (`certify_L1.py`).

## 4. Status: what is proved, certified, Lean-checked, sketched

| item | status |
|---|---|
| Theorem 1 (`derandomisation.md`) | Full written proof. Two adversarial reviews: the first checked a sketch step by step; the second checked the full text, including the APSP chain, and found it correct (its qualifier and four textual fixes are applied) |
| Theorem 2, L1 (`l1.md`) | Full written proof; one adversarial review, after two fixes (3SUM window [-7, 8]; Alon-Naor bias 2^{-7c-1} for 3SUM) |
| Corollaries | Compositions of Theorems 1 and 2 with the cited reductions; not separately reviewed |
| Remark, Las Vegas route (Appendix B) | Proof; one adversarial review |
| Exact count and pruned encodings (Appendix A) | Short arguments on the paper's construction; reviewed once; public earlier, Lean-checked, in ImprovedExponents |
| All saving values | arb ball arithmetic (200 bits) at fixed rational points, every side condition checked on the whole ball (`certificates/`) |
| Negative triangle to Exact Triangle (Appendix C) | Proof; exhaustive and end-to-end checks against brute force with a negative control (`check_negtri.py`) |
| Theorem 1's constructions on small instances | Mechanical check against brute force, with two negative controls (`check_derand.py`, `check_derand_controls.py`) |
| Lean | **Pending.** A Lean 4 kernel check of the certificates is being built and is not included yet |
| The paper's theorems | Assumed as published (its main theorems are Lean-formalised in anthropics/formal-math) |
| 3XOR, All-Numbers 3SUM | Sketches only, unverified; not claimed |

The mechanical checks test logic on small instances, not asymptotics. The arb certificates check arithmetic, not the
reductions. Nothing here is formalised in Lean yet.

## 5. Reproduce

Requires Python 3.9 or newer and `python-flint` (`pip install -r requirements.txt`; tested with 0.6.0).

```sh
make              # all certificates, the mechanical checks and the tests on their printed values (about 15 s)
make certificates # the certificates and checks alone, printing every claim
```

| script | prints |
|---|---|
| `certificates/derand_cert.py` | Theorem 1 savings and exponents (both tiers and the paper's point), Convolution-3SUM and k-Clique |
| `certificates/certify_L1.py` | Theorem 2 savings, all seven cost terms, exponents, Convolution-3SUM and (min,+)-convolution |
| `certificates/certify_levers.py` | the Las Vegas remark, and the paper's single-prime route with Appendix C for comparison |
| `certificates/certify.py` | the shared closed forms, and the paper's Theorem 17 route re-tuned (comparison only) |
| `certificates/check_negtri.py` | Appendix C: identity, full reduction against brute force, negative control |
| `certificates/check_derand.py`, `check_derand_controls.py` | Theorem 1's constructions against brute force, and two controls that must fail |

`tests/test_certificates.py` runs each script once and checks its printed values against this README.

## Attribution

Author: **Swapnil Jain**. Research, implementation and drafting were done with assistance from Claude (Anthropic).
AI assistance is not independent review. Licensed under Apache-2.0.
