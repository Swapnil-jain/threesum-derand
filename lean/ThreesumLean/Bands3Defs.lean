import ThreesumLean.Bands2Defs

/-!
# Theorem C': zone moves (certificates/bands3_cert.py)

Theorem C' is Theorem C with one change (Lemma Z, proofs/bands.md Sec. 9): in a zone segment the move whose term
equals the digit pair of `w` at the level below the gap keeps the key, so a zone gap blocks with probability `8/9`
for every key instead of `1`. The zone segments then contribute `zeta (c/lam) sum_n Bin(n) ln A(lam, n; 9z, 8/9)` to
`q_eff` in place of Theorem C's `zeta ln(1 + 9z)`. Everything else (the class averages `Aq`, the laws `bW`, `bSh`,
`bS`, the other exponents and the side conditions) is reused from Bands2Defs.lean unchanged.

What is NOT checked here: Lemma Z itself and the class-average argument (paper proofs, proofs/bands.md Sec. 9).
-/

open Real Finset

namespace TS

/-! ## The zone law (Lemma Z) -/

/-- The zone blocking law of Lemma Z: `8/9`, the same for every key and every gap. -/
def bZ (_ : ℕ) : ℚ := 8 / 9

/-- Lemma Z, finite part: for the digit pair `(u, v)` of `w`, exactly one of the 9 terms `(i, j)` is movable, so
the fraction of blocked terms is `8/9`. -/
def zoneAvg (u v : ℕ) : ℚ :=
  ((List.range 3).flatMap fun i => (List.range 3).map fun j => if i = u ∧ j = v then (0 : ℚ) else 1).sum / 9

theorem zoneAvg_eq : ∀ u < 3, ∀ v < 3, zoneAvg u v = bZ 0 := by decide +kernel

/-! ## The exponents of bands3_cert.py -/

/-- `q_eff = [-th ln z + (c/lam) sum_n Bin(n) ((1 - zeta) ln A(lam, n; 9z, b) + zeta ln A(lam, n; 9z, 8/9))]/ln 4`.
Since both `EA` sums share the weights `Bin(n)`, the per-`n` mix in bands3_cert.py equals this mix of the two sums. -/
noncomputable def qEff3 (lam : ℕ) (bf : ℕ → ℚ) (c th z : ℚ) : ℝ :=
  (-(th : ℝ) * log z + ((c : ℝ) / lam) *
      ((1 - zetaB c) * EA lam c (9 * z) bf + zetaB c * EA lam c (9 * z) bZ)) / log 4

/-- `q* = max(q_eff, q_fill)`; `q_fill` is Theorem C's. -/
noncomputable def qStar3 (lam : ℕ) (bf : ℕ → ℚ) (c th z : ℚ) : ℝ := max (qEff3 lam bf c th z) (qFill lam c th)

/-- `sigma = min(eps gamma, eps (1/2 - q*), 1 - eps E)`, Theorem C's terms with the zone-move `q*`. -/
noncomputable def sigB3 (lam : ℕ) (bf : ℕ → ℚ) (c th eps z : ℚ) : ℝ :=
  minl (b2Terms eps (gammaExact c th) (Epruned c) (qStar3 lam bf c th z))

/-- bands3_cert.py: every side condition at `(c, theta, eps, z, lam, b)` with zone law `8/9`, then `sigma >= s0`, the
3SUM exponent `2 - sigma <= b` and the `O(n^o)` line `2 - sigma < o`. The fields are those of `CertBands2`. -/
structure CertBands3 (lam : ℕ) (bf : ℕ → ℚ) (c th eps z : ℚ) (s0 b o : ℝ) : Prop where
  c_gt : 10 < c
  th_pos : 0 < th
  th_lt : th < 9 / 10
  eps_pos : 0 < eps
  z_pos : 0 < z
  z_le : z ≤ 1
  gamma_pos : 0 < gammaExact c th
  terms_pos : ∀ t ∈ b2Terms eps (gammaExact c th) (Epruned c) (qStar3 lam bf c th z), 0 < t
  enc_box : (eps : ℝ) * (Epruned c + gammaExact c th) < 1
  qstar_lt : qStar3 lam bf c th z < 1 / 2
  fill_lt : qFill lam c th < qEff3 lam bf c th z
  sig_lt : sigB3 lam bf c th eps z < eps / 2
  writing : 1 + (eps : ℝ) < 2 - sigB3 lam bf c th eps z
  partial_bands : (eps : ℝ) * (Epruned c + qExp th - 1 / 2) + sigB3 lam bf c th eps z < 1
  precompute : ePre lam c eps < 2 - sigB3 lam bf c th eps z
  saving : s0 ≤ sigB3 lam bf c th eps z
  exponent : 2 - sigB3 lam bf c th eps z ≤ b
  exponent_O : 2 - sigB3 lam bf c th eps z < o

lemma sigB3_eq {lam : ℕ} {bf : ℕ → ℚ} {c th eps z : ℚ} (h : qFill lam c th < qEff3 lam bf c th z) :
    sigB3 lam bf c th eps z = minl (b2Terms eps (gammaExact c th) (Epruned c) (qEff3 lam bf c th z)) := by
  unfold sigB3 qStar3; rw [max_eq_left h.le]

/-- Build the certificate from a lower bound `s0` on every term and an upper bound `U` on one of them. -/
lemma CertBands3.mk' {lam : ℕ} {bf : ℕ → ℚ} {c th eps z : ℚ} {s0 b o U : ℝ}
    (h1 : 10 < c) (h2 : 0 < th) (h3 : th < 9 / 10) (h4 : 0 < eps) (h5 : 0 < z) (h6 : z ≤ 1)
    (hg : 0 < gammaExact c th) (hfill : qFill lam c th < qEff3 lam bf c th z)
    (hlow : ∀ t ∈ b2Terms eps (gammaExact c th) (Epruned c) (qEff3 lam bf c th z), s0 ≤ t) (hs0 : 0 < s0)
    (henc : (eps : ℝ) * (Epruned c + gammaExact c th) < 1) (hq : qEff3 lam bf c th z < 1 / 2)
    (hU : (eps : ℝ) * gammaExact c th ≤ U ∨ (eps : ℝ) * (1 / 2 - qEff3 lam bf c th z) ≤ U ∨
      1 - (eps : ℝ) * Epruned c ≤ U)
    (hsU : U < eps / 2) (hwU : 1 + (eps : ℝ) < 2 - U)
    (hpU : (eps : ℝ) * (Epruned c + qExp th - 1 / 2) + U < 1) (hpre : ePre lam c eps < 2 - U)
    (hb : 2 - s0 ≤ b) (ho : 2 - s0 < o) : CertBands3 lam bf c th eps z s0 b o := by
  have hS := sigB3_eq (eps := eps) hfill
  have hqs : qStar3 lam bf c th z = qEff3 lam bf c th z := max_eq_left hfill.le
  have hlo : s0 ≤ sigB3 lam bf c th eps z := hS ▸ le_minl (by simp [b2Terms]) hlow
  have hup : sigB3 lam bf c th eps z ≤ U := by
    rw [hS]
    rcases hU with h | h | h
    · exact (minl_le (by simp [b2Terms])).trans h
    · exact (minl_le (by simp [b2Terms])).trans h
    · exact (minl_le (by simp [b2Terms])).trans h
  refine ⟨h1, h2, h3, h4, h5, h6, hg, ?_, henc, hqs ▸ hq, hfill, by linarith, by linarith, by linarith,
    by linarith, hlo, by linarith, by linarith⟩
  rw [hqs]; intro t ht; linarith [hlow t ht]

/-- The claimed bounds, which the negative controls refute. -/
lemma CertBands3.lower {lam : ℕ} {bf : ℕ → ℚ} {c th eps z : ℚ} {s0 b o : ℝ}
    (h : CertBands3 lam bf c th eps z s0 b o) :
    s0 ≤ sigB3 lam bf c th eps z ∧ 2 - b ≤ sigB3 lam bf c th eps z ∧ 2 - o < sigB3 lam bf c th eps z :=
  ⟨h.saving, by linarith [h.exponent], by linarith [h.exponent_O]⟩

/-- Each term bounds `sigma` from above (`q* >= q_eff` and `eps > 0` for the middle one). -/
lemma CertBands3.upper {lam : ℕ} {bf : ℕ → ℚ} {c th eps z : ℚ} {s0 b o : ℝ}
    (h : CertBands3 lam bf c th eps z s0 b o) :
    sigB3 lam bf c th eps z ≤ (eps : ℝ) * gammaExact c th ∧
      sigB3 lam bf c th eps z ≤ (eps : ℝ) * (1 / 2 - qEff3 lam bf c th z) ∧
      sigB3 lam bf c th eps z ≤ 1 - (eps : ℝ) * Epruned c := by
  have he : (0 : ℝ) ≤ eps := by exact_mod_cast h.eps_pos.le
  have hq : qEff3 lam bf c th z ≤ qStar3 lam bf c th z := le_max_left _ _
  unfold sigB3
  refine ⟨minl_le_get _ 0 (by simp [b2Terms]), (minl_le_get _ 1 (by simp [b2Terms])).trans ?_,
    minl_le_get _ 2 (by simp [b2Terms])⟩
  exact mul_le_mul_of_nonneg_left (by linarith) he

end TS
