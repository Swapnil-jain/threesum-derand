import ThreesumLean.Bands2Points
import ThreesumLean.Bands2Stretch

/-!
# Theorem 3 headlines: each tier's certificate together with the finite facts behind its blocking law

(W) 3SUM <= 1.995856782, O(n^1.995857); (S) <= 1.995811603, O(n^1.995812); (C) <= 1.995789157, O(n^1.995790).
-/

namespace TS

/-- Tier (W): the certificate, and `22/27` bounds the one-digit average for every carry sum (Lemma 3.1). -/
theorem bands2_W_full :
    CertBands2 8 bW (2111519/100000) (115663/1000000) (28628097/500000000) (17187/1000000) (20716091/5000000000)
      (997928391/500000000) (1995857/1000000) ∧ ∀ s < 4, worstAvg s ≤ bW 0 :=
  ⟨bands2_W, worstAvg_le⟩

/-- Tier (S): the certificate, and the shifted law is exactly `62/81` (Lemma 3.2). -/
theorem bands2_S_full :
    CertBands2 8 bSh (65833/3125) (23379/200000) (28691779/500000000) (36571/2000000) (20941987/5000000000)
      (1995811603/1000000000) (498953/250000) ∧ shiftAvg = bSh 0 :=
  ⟨bands2_S, shiftAvg_eq⟩

/-- Tier (C): the certificate, the `b(len)` table is the enumeration for `len <= 5`, and `b(6), b(7) <= b(5)`. -/
theorem bands2_C_full :
    CertBands2 8 bS (1052341/50000) (1836/15625) (28717589/500000000) (94241/5000000) (8421687/2000000000)
      (1995789157/1000000000) (199579/100000) ∧ (∀ len < 6, bS len = (bnum len : ℚ) / 9 ^ (len + 1)) ∧
      ((bnum 6 : ℚ) / 9 ^ 7 ≤ bS 6 ∧ (bnum 7 : ℚ) / 9 ^ 8 ≤ bS 7) :=
  ⟨bands2_C, bS_eq, bS_long⟩

end TS
