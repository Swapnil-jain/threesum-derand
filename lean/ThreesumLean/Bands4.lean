import ThreesumLean.Bands4Points

/-!
# Theorem C'' headlines (proofs/bands.md, Sec. 10; certificates/bands4_cert.py)

(C, Lemma Y, lengths 8 and 9 mixed 7/10 : 3/10) 3SUM <= 1.995781854, O(n^1.995782);
(C, Lemma Y, length 8 only) 3SUM <= 1.995783471, O(n^1.995784).
-/

namespace TS

/-- bands4_poly.py's sanity check of the Lemma Y table, rechecked by the kernel: with one key in a segment of length
8, the linear coefficient of `A_Y(8, 1; y)` lies between the stretch-law averages `sum_{i<6} b(i)/8` and
`sum_{i<8} b(min(i, 5))/8` of Lemma 3.3. -/
theorem coefY_one_vs_stretch :
    (coefY 8 1).getD 1 0 ≤ ((List.range 8).map fun i => bS i).sum / 8 ∧
      ((List.range 6).map fun i => bS i).sum / 8 ≤ (coefY 8 1).getD 1 0 := by
  decide +kernel

/-- The headline: the certificate at the 7/10 : 3/10 mix, with the table's upper sanity bound. -/
theorem bands4_C_full :
    CertBands4 ([(8, (7/10)), (9, (3/10))] : List (ℕ × ℚ)) coefY coefZY (4203319/200000) (3679/31250)
      (115032221/2000000000) (190589/10000000) (10545367/2500000000) (997890927/500000000) (997891/500000) ∧
      (coefY 8 1).getD 1 0 ≤ ((List.range 8).map fun i => bS i).sum / 8 :=
  ⟨bands4_C, coefY_one_vs_stretch.1⟩

/-- The length-8-only point. -/
theorem bands4_C8_full :
    CertBands4 ([(8, (1))] : List (ℕ × ℚ)) coefY coefZY (21018799/1000000) (1176831/10000000)
      (143775683/2500000000) (190173/10000000) (8433059/2000000000) (1995783471/1000000000) (249473/125000) :=
  bands4_C8

end TS
