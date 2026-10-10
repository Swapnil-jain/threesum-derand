import ThreesumLean.Bands3Points
import ThreesumLean.Bands2Stretch

/-!
# Theorem C' headlines: each tier's certificate together with the finite facts behind its blocking laws

(W) 3SUM <= 1.995853635, O(n^1.995854); (S) <= 1.995808229, O(n^1.995809); (C) <= 1.995785623, O(n^1.995786).
The zone law `8/9` (Lemma Z) is the same in every tier; the non-zone laws are Theorem C's.
-/

namespace TS

/-- Tier (W): the certificate, `22/27` bounds the one-digit average for every carry sum (Lemma 3.1), and the zone
law is `8/9` for every digit pair. -/
theorem bands3_W_full :
    CertBands3 8 bW (5274867/250000) (57881/500000) (572980907/10000000000) (172629/10000000)
      (41463659/10000000000) (399170727/200000000) (997927/500000) ∧ (∀ s < 4, worstAvg s ≤ bW 0) ∧
      (∀ u < 3, ∀ v < 3, zoneAvg u v = bZ 0) :=
  ⟨bands3_W, worstAvg_le, zoneAvg_eq⟩

/-- Tier (S): the certificate, the shifted law is exactly `62/81` (Lemma 3.2), and the zone law is `8/9`. -/
theorem bands3_S_full :
    CertBands3 8 bSh (5262491/250000) (58501/500000) (574279737/10000000000) (91849/5000000)
      (41917719/10000000000) (1995808229/1000000000) (1995809/1000000) ∧ shiftAvg = bSh 0 ∧
      (∀ u < 3, ∀ v < 3, zoneAvg u v = bZ 0) :=
  ⟨bands3_S, shiftAvg_eq, zoneAvg_eq⟩

/-- Tier (C): the certificate, the `b(len)` table is the enumeration for `len <= 5`, `b(6), b(7) <= b(5)`, and the
zone law is `8/9`. -/
theorem bands3_C_full :
    CertBands3 8 bS (10514903/500000) (58807/500000) (574807987/10000000000) (23671/1250000)
      (4214377/1000000000) (1995785623/1000000000) (997893/500000) ∧
      (∀ len < 6, bS len = (bnum len : ℚ) / 9 ^ (len + 1)) ∧
      ((bnum 6 : ℚ) / 9 ^ 7 ≤ bS 6 ∧ (bnum 7 : ℚ) / 9 ^ 8 ≤ bS 7) ∧ (∀ u < 3, ∀ v < 3, zoneAvg u v = bZ 0) :=
  ⟨bands3_C, bS_eq, bS_long, zoneAvg_eq⟩

end TS
