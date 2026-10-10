import Mathlib

/-!
# The finite and integer lemmas behind L1 (proofs/l1.md) and Appendix C (check_negtri.py)

All statements are over `ℤ` with Lean's `/` (Euclidean division, which is the floor for a positive divisor) or
over `ℚ`/`ℝ`. Most are proved for all integers, not only on a finite range. Where the claim was checked
exhaustively in Python, the exhaustive version is also closed by `decide +kernel`. Negative controls are stated as
negations.
-/

open Finset

namespace TS

/-! ## Floors -/

lemma floor_half (x : ℤ) : ⌊(x : ℚ) / 2⌋ = x / 2 := by
  rw [Int.floor_eq_iff]
  have h1 : 2 * (x / 2) ≤ x := by omega
  have h2 : x < 2 * (x / 2) + 2 := by omega
  have h1' : 2 * ((x / 2 : ℤ) : ℚ) ≤ (x : ℚ) := by exact_mod_cast h1
  have h2' : (x : ℚ) < 2 * ((x / 2 : ℤ) : ℚ) + 2 := by exact_mod_cast h2
  constructor <;> linarith

/-- Halving step: `floor(floor(x/2^l)/2) = floor(x/2^(l+1))`. -/
theorem halving_iterate (x : ℤ) (l : ℕ) : x / 2 ^ l / 2 = x / 2 ^ (l + 1) := by
  rw [Int.ediv_ediv_of_nonneg (by positivity), pow_succ]

/-- Halving step: `floor(x/2)` lies in `[x/2 - 1/2, x/2]`. -/
theorem floor_half_mem (x : ℤ) :
    (x : ℚ) / 2 - 1 / 2 ≤ ((x / 2 : ℤ) : ℚ) ∧ ((x / 2 : ℤ) : ℚ) ≤ (x : ℚ) / 2 := by
  have h1 : x - 1 ≤ 2 * (x / 2) := by omega
  have h2 : 2 * (x / 2) ≤ x := by omega
  have h1' : (x : ℚ) - 1 ≤ 2 * ((x / 2 : ℤ) : ℚ) := by exact_mod_cast h1
  have h2' : 2 * ((x / 2 : ℤ) : ℚ) ≤ (x : ℚ) := by exact_mod_cast h2
  constructor <;> linarith

/-! ## Exact Triangle window (proofs/l1.md, Sec. 2): `S = x + y + z`, each term halved by floor -/

/-- `S_l/2 - 3/2 ≤ S_{l+1} ≤ S_l/2`, for all integers. -/
theorem et_window (x y z : ℤ) :
    ((x + y + z : ℤ) : ℚ) / 2 - 3 / 2 ≤ ((x / 2 + y / 2 + z / 2 : ℤ) : ℚ) ∧
      ((x / 2 + y / 2 + z / 2 : ℤ) : ℚ) ≤ ((x + y + z : ℤ) : ℚ) / 2 := by
  have h1 : x + y + z - 3 ≤ 2 * (x / 2 + y / 2 + z / 2) := by omega
  have h2 : 2 * (x / 2 + y / 2 + z / 2) ≤ x + y + z := by omega
  have h1' : ((x + y + z : ℤ) : ℚ) - 3 ≤ 2 * ((x / 2 + y / 2 + z / 2 : ℤ) : ℚ) := by exact_mod_cast h1
  have h2' : 2 * ((x / 2 + y / 2 + z / 2 : ℤ) : ℚ) ≤ ((x + y + z : ℤ) : ℚ) := by exact_mod_cast h2
  constructor <;> linarith

/-- The same window with the floors written as `⌊x/2⌋`. -/
theorem et_window_floor (x y z : ℤ) :
    ((x + y + z : ℤ) : ℚ) / 2 - 3 / 2 ≤ ((⌊(x : ℚ) / 2⌋ + ⌊(y : ℚ) / 2⌋ + ⌊(z : ℚ) / 2⌋ : ℤ) : ℚ) ∧
      ((⌊(x : ℚ) / 2⌋ + ⌊(y : ℚ) / 2⌋ + ⌊(z : ℚ) / 2⌋ : ℤ) : ℚ) ≤ ((x + y + z : ℤ) : ℚ) / 2 := by
  rw [floor_half, floor_half, floor_half]; exact et_window x y z

/-- `|S_l| ≤ 3` implies `S_{l+1} ∈ [-3, 3/2]`. -/
theorem et_window_near (x y z : ℤ) (h : |x + y + z| ≤ 3) :
    (-3 : ℚ) ≤ ((x / 2 + y / 2 + z / 2 : ℤ) : ℚ) ∧ ((x / 2 + y / 2 + z / 2 : ℤ) : ℚ) ≤ 3 / 2 := by
  have h' := abs_le.mp h
  have h1 : -3 ≤ x / 2 + y / 2 + z / 2 := by omega
  have h2 : 2 * (x / 2 + y / 2 + z / 2) ≤ 3 := by omega
  have h1' : (-3 : ℚ) ≤ ((x / 2 + y / 2 + z / 2 : ℤ) : ℚ) := by exact_mod_cast h1
  have h2' : 2 * ((x / 2 + y / 2 + z / 2 : ℤ) : ℚ) ≤ 3 := by exact_mod_cast h2
  constructor <;> linarith

/-- `S_l ∈ [2 S_{l+1}, 2 S_{l+1} + 3]`, and `|S_{l+1}| ≤ 3` puts it in `[-6, 9]`. -/
theorem et_recover (x y z : ℤ) :
    2 * (x / 2 + y / 2 + z / 2) ≤ x + y + z ∧ x + y + z ≤ 2 * (x / 2 + y / 2 + z / 2) + 3 ∧
      (|x / 2 + y / 2 + z / 2| ≤ 3 → -6 ≤ x + y + z ∧ x + y + z ≤ 9) := by
  refine ⟨by omega, by omega, fun h => ?_⟩
  have := abs_le.mp h; omega

/-! ## 3SUM window (`a + b = c` form): `S = x + y - z` -/

/-- `S_l/2 - 1 ≤ S_{l+1} ≤ S_l/2 + 1/2`. -/
theorem sum3_window (x y z : ℤ) :
    ((x + y - z : ℤ) : ℚ) / 2 - 1 ≤ ((x / 2 + y / 2 - z / 2 : ℤ) : ℚ) ∧
      ((x / 2 + y / 2 - z / 2 : ℤ) : ℚ) ≤ ((x + y - z : ℤ) : ℚ) / 2 + 1 / 2 := by
  have h1 : x + y - z - 2 ≤ 2 * (x / 2 + y / 2 - z / 2) := by omega
  have h2 : 2 * (x / 2 + y / 2 - z / 2) ≤ x + y - z + 1 := by omega
  have h1' : ((x + y - z : ℤ) : ℚ) - 2 ≤ 2 * ((x / 2 + y / 2 - z / 2 : ℤ) : ℚ) := by exact_mod_cast h1
  have h2' : 2 * ((x / 2 + y / 2 - z / 2 : ℤ) : ℚ) ≤ ((x + y - z : ℤ) : ℚ) + 1 := by exact_mod_cast h2
  constructor <;> linarith

/-- `|S_l| ≤ 3` implies `S_{l+1} ∈ [-5/2, 2]`. -/
theorem sum3_window_near (x y z : ℤ) (h : |x + y - z| ≤ 3) :
    (-5 / 2 : ℚ) ≤ ((x / 2 + y / 2 - z / 2 : ℤ) : ℚ) ∧ ((x / 2 + y / 2 - z / 2 : ℤ) : ℚ) ≤ 2 := by
  have h' := abs_le.mp h
  have h1 : -5 ≤ 2 * (x / 2 + y / 2 - z / 2) := by omega
  have h2 : x / 2 + y / 2 - z / 2 ≤ 2 := by omega
  have h1' : (-5 : ℚ) ≤ 2 * ((x / 2 + y / 2 - z / 2 : ℤ) : ℚ) := by exact_mod_cast h1
  have h2' : ((x / 2 + y / 2 - z / 2 : ℤ) : ℚ) ≤ 2 := by exact_mod_cast h2
  constructor <;> linarith

/-- `S_l ∈ [2 S_{l+1} - 1, 2 S_{l+1} + 2]`, and `|S_{l+1}| ≤ 3` puts it in `[-7, 8]`. -/
theorem sum3_recover (x y z : ℤ) :
    2 * (x / 2 + y / 2 - z / 2) - 1 ≤ x + y - z ∧ x + y - z ≤ 2 * (x / 2 + y / 2 - z / 2) + 2 ∧
      (|x / 2 + y / 2 - z / 2| ≤ 3 → -7 ≤ x + y - z ∧ x + y - z ≤ 8) := by
  refine ⟨by omega, by omega, fun h => ?_⟩
  have := abs_le.mp h; omega

/-- Negative control: the ET window `[-6, 9]` is not valid for 3SUM (`x = y = -2`, `z = 3`). -/
theorem sum3_window_not_et :
    ¬ ∀ x y z : ℤ, |x / 2 + y / 2 - z / 2| ≤ 3 → -6 ≤ x + y - z ∧ x + y - z ≤ 9 := by
  intro h; have := h (-2) (-2) 3 (by decide); omega

/-- Negative control: the ET window's lower end cannot be raised to `S_l/2 - 1` (`x = y = z = 1`). -/
theorem et_window_tight :
    ¬ ∀ x y z : ℤ, ((x + y + z : ℤ) : ℚ) / 2 - 1 ≤ ((x / 2 + y / 2 + z / 2 : ℤ) : ℚ) := by
  intro h; have := h 1 1 1; norm_num at this

/-! ## Base level, scaling, Fredman, (min,+) -/

/-- Base level: `|x| < d` (in particular `x = 4w`, `d = 2^L`) gives `floor(x/d) ∈ {-1, 0}`. -/
theorem base_level (x d : ℤ) (hd : 0 < d) (hx : |x| < d) : x / d = -1 ∨ x / d = 0 := by
  have h := abs_lt.mp hx
  have h1 : x / d < 1 := by
    rw [Int.ediv_lt_iff_lt_mul hd]; linarith
  have h2 : -1 ≤ x / d := by
    rw [Int.le_ediv_iff_mul_le hd]; linarith
  omega

/-- Base level sums: three values in `{-1, 0}` sum to `[-3, 0]` (ET) and `x + y - z` lies in `[-2, 1]` (3SUM). -/
theorem base_level_sums (x y z : ℤ) (hx : x = -1 ∨ x = 0) (hy : y = -1 ∨ y = 0) (hz : z = -1 ∨ z = 0) :
    (-3 ≤ x + y + z ∧ x + y + z ≤ 0) ∧ (-2 ≤ x + y - z ∧ x + y - z ≤ 1) := by omega

/-- Scaling: after multiplying every weight by 4, `S = 0` iff `|S| ≤ 3`. -/
theorem scale_by_four (S : ℤ) : 4 * S = 0 ↔ |4 * S| ≤ 3 := by
  rw [abs_le]; omega

/-- Fredman identity: with `w_ab = delta - w_ak - w_bk`,
`S(c') ≤ t` iff `w_ac' - w_ak ≤ (t - delta) + w_bk - w_bc'`. -/
theorem fredman (wab wak wbk wac wbc delta t : ℤ) (h : wab = delta - wak - wbk) :
    wab + wbc + wac ≤ t ↔ wac - wak ≤ (t - delta) + wbk - wbc := by omega

/-- (min,+) step: for every `c` the level values satisfy the ET window, `piv` minimises level `l + 1`, then
`j* = S_l(piv) - min S_l` is in `{0, 1, 2, 3}`. -/
theorem minplus_step {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (x y z : ι → ℤ) (piv : ι) (hp : piv ∈ s)
    (hmin : ∀ c ∈ s, x piv / 2 + y piv / 2 + z piv / 2 ≤ x c / 2 + y c / 2 + z c / 2) :
    0 ≤ (x piv + y piv + z piv) - s.inf' hs (fun c => x c + y c + z c) ∧
      (x piv + y piv + z piv) - s.inf' hs (fun c => x c + y c + z c) ≤ 3 := by
  have hle : s.inf' hs (fun c => x c + y c + z c) ≤ x piv + y piv + z piv := Finset.inf'_le _ hp
  have hge : 2 * (x piv / 2 + y piv / 2 + z piv / 2) ≤ s.inf' hs (fun c => x c + y c + z c) := by
    apply Finset.le_inf'
    intro c hc
    have := hmin c hc
    omega
  have hpv : x piv + y piv + z piv ≤ 2 * (x piv / 2 + y piv / 2 + z piv / 2) + 3 := by omega
  constructor <;> omega

/-! ## Unique-witness test and the Claim-7 bias -/

/-- Unique-witness test: for a nonempty multiset of indices below `2^b`, every bit-class count is `0` or the
total iff all indices are equal. Proved for every `b` and every multiset. -/
theorem unique_witness (b : ℕ) (W : Multiset ℕ) (hb : ∀ x ∈ W, x < 2 ^ b) :
    (∀ j < b, (W.filter (fun x => x.testBit j = true)).card = 0 ∨
        (W.filter (fun x => x.testBit j = true)).card = W.card) ↔ ∀ x ∈ W, ∀ y ∈ W, x = y := by
  constructor
  · intro h x hx y hy
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < b
    · rcases h i hi with h0 | hc
      · have hn := Multiset.card_eq_zero.mp h0
        have fx : x.testBit i ≠ true := fun hx' => by
          have : x ∈ W.filter (fun x => x.testBit i = true) := Multiset.mem_filter.mpr ⟨hx, hx'⟩
          rw [hn] at this; simp at this
        have fy : y.testBit i ≠ true := fun hy' => by
          have : y ∈ W.filter (fun x => x.testBit i = true) := Multiset.mem_filter.mpr ⟨hy, hy'⟩
          rw [hn] at this; simp at this
        simp only [ne_eq, Bool.not_eq_true] at fx fy; rw [fx, fy]
      · have he : W.filter (fun x => x.testBit i = true) = W :=
          Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _) hc.ge
        have hall := Multiset.filter_eq_self.mp he
        rw [hall x hx, hall y hy]
    · push Not at hi
      rw [Nat.testBit_eq_false_of_lt ((hb x hx).trans_le (Nat.pow_le_pow_right (by norm_num) hi)),
        Nat.testBit_eq_false_of_lt ((hb y hy).trans_le (Nat.pow_le_pow_right (by norm_num) hi))]
  · intro h j _
    by_cases hW : W = 0
    · left; simp [hW]
    obtain ⟨x0, hx0⟩ := Multiset.exists_mem_of_ne_zero hW
    by_cases hbit : x0.testBit j = true
    · right; congr 1
      exact Multiset.filter_eq_self.mpr fun a ha => (h a ha x0 hx0) ▸ hbit
    · left; rw [Multiset.card_eq_zero]
      exact Multiset.filter_eq_nil.mpr fun a ha hab => hbit ((h a ha x0 hx0) ▸ hab)

/-- Claim-7 bias bound: for `v ≤ 7c` and `eps' = 2^{-7c-1}`, `2^{-v} - eps' > 0`. -/
theorem claim7_bias (c v : ℕ) (hv : v ≤ 7 * c) : (0 : ℝ) < (1 / 2) ^ v - (1 / 2) ^ (7 * c + 1) := by
  have : ((1 : ℝ) / 2) ^ (7 * c + 1) < (1 / 2) ^ v :=
    pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
  linarith

/-! ## Negative Triangle to all-edges Exact Triangle (proofs/derandomisation.md, Appendix C) -/

/-- Soundness of one dyadic level: `v_k + t_k ≤ tau_k - 2` gives `v + t < tau`. -/
lemma a2_sound (v t tau d : ℤ) (hd : 0 < d) (h : v / d + t / d + 2 ≤ tau / d) : v + t < tau := by
  have hv := Int.lt_ediv_add_one_mul_self v hd
  have ht := Int.lt_ediv_add_one_mul_self t hd
  have hu := Int.ediv_mul_le tau hd.ne'
  have : (v / d + t / d + 2) * d ≤ tau / d * d := mul_le_mul_of_nonneg_right h hd.le
  nlinarith

/-- `f(k) = tau_k - 2 - v_k - t_k`. -/
def fA2 (v t tau : ℤ) (k : ℕ) : ℤ := tau / 2 ^ k - 2 - v / 2 ^ k - t / 2 ^ k

/-- Completeness: from `f(k) ≥ 0` the sequence reaches `{0, 1}` before level `K`, where every value is below `2^K`. -/
lemma a2_hit (v t tau : ℤ) (K : ℕ) (hv : 0 ≤ v) (ht : 0 ≤ t) (htau : 0 ≤ tau) (hvK : v < 2 ^ K)
    (htK : t < 2 ^ K) (htauK : tau < 2 ^ K) :
    ∀ n k, k + n = K → 0 ≤ fA2 v t tau k → ∃ k' < K, fA2 v t tau k' = 0 ∨ fA2 v t tau k' = 1 := by
  intro n
  induction n with
  | zero =>
    intro k hk h0
    simp only [add_zero] at hk; subst hk
    simp only [fA2, Int.ediv_eq_zero_of_lt hv hvK, Int.ediv_eq_zero_of_lt ht htK,
      Int.ediv_eq_zero_of_lt htau htauK] at h0
    omega
  | succ n ih =>
    intro k hk h0
    by_cases h01 : fA2 v t tau k = 0 ∨ fA2 v t tau k = 1
    · exact ⟨k, by omega, h01⟩
    · apply ih (k + 1) (by omega)
      simp only [fA2] at h0 h01 ⊢
      rw [← halving_iterate, ← halving_iterate, ← halving_iterate]
      omega

/-- The dyadic identity, for all integers `v, t, tau ≥ 0` below `2^K`:
`v + t < tau` iff `v + t = tau - 1` or some `k < K` has `v_k + t_k ∈ {tau_k - 2, tau_k - 3}`. -/
theorem a2_identity (v t tau : ℤ) (K : ℕ) (hv : 0 ≤ v) (ht : 0 ≤ t) (htau : 0 ≤ tau) (hvK : v < 2 ^ K)
    (htK : t < 2 ^ K) (htauK : tau < 2 ^ K) :
    v + t < tau ↔ v + t = tau - 1 ∨ ∃ k < K, v / 2 ^ k + t / 2 ^ k = tau / 2 ^ k - 2 ∨
      v / 2 ^ k + t / 2 ^ k = tau / 2 ^ k - 3 := by
  constructor
  · intro h
    by_cases h1 : v + t = tau - 1
    · exact Or.inl h1
    · right
      have h0 : 0 ≤ fA2 v t tau 0 := by simp [fA2]; omega
      obtain ⟨k, hk, hf⟩ := a2_hit v t tau K hv ht htau hvK htK htauK K 0 (by omega) h0
      exact ⟨k, hk, by simp only [fA2] at hf; omega⟩
  · rintro (h | ⟨k, -, h | h⟩)
    · omega
    · exact a2_sound v t tau (2 ^ k) (by positivity) (by omega)
    · exact a2_sound v t tau (2 ^ k) (by positivity) (by omega)

/-- Appendix C per triple, with the fixed shift `tau = 2h - w_ab`, `v = w_bc + h`, `t = w_ca + h`, `3h < 2^K`:
`S < 0` iff the k-free instance `x = 1 - tau` or one of the instances `x = j - tau_k`, `y = v_k`, `z = t_k`
(`k < K`, `j ∈ {2, 3}`) has `x + y + z = 0`. This is the full reduction of check_negtri.py, for all weights. -/
theorem a2_reduction (wab wbc wca h : ℤ) (K : ℕ) (hab : |wab| ≤ h) (hbc : |wbc| ≤ h) (hca : |wca| ≤ h)
    (hK : 3 * h < 2 ^ K) :
    wab + wbc + wca < 0 ↔ (1 - (2 * h - wab)) + (wbc + h) + (wca + h) = 0 ∨
      ∃ k < K, ∃ j ∈ ({2, 3} : Finset ℤ),
        (j - (2 * h - wab) / 2 ^ k) + (wbc + h) / 2 ^ k + (wca + h) / 2 ^ k = 0 := by
  have a := abs_le.mp hab; have b := abs_le.mp hbc; have c := abs_le.mp hca
  have hid := a2_identity (wbc + h) (wca + h) (2 * h - wab) K (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith)
  have e : wab + wbc + wca < 0 ↔ (wbc + h) + (wca + h) < 2 * h - wab := by constructor <;> intro <;> linarith
  rw [e, hid]
  simp only [Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, exists_eq_left]
  constructor
  · rintro (h1 | ⟨k, hk, h2 | h3⟩)
    · left; linarith
    · right; exact ⟨k, hk, Or.inl (by linarith)⟩
    · right; exact ⟨k, hk, Or.inr (by linarith)⟩
  · rintro (h1 | ⟨k, hk, h2 | h3⟩)
    · left; linarith
    · right; exact ⟨k, hk, Or.inl (by linarith)⟩
    · right; exact ⟨k, hk, Or.inr (by linarith)⟩

/-- Negative control: the old shift `tau = 2h - w_ab - 1` fails at `w = (0, 0, -1)`, `h = 1`: the triangle is
negative (`S = -1`) but no instance has a zero. -/
theorem a2_old_shift_fails :
    ¬ ∀ (wab wbc wca h : ℤ) (K : ℕ), |wab| ≤ h → |wbc| ≤ h → |wca| ≤ h → 3 * h < 2 ^ K →
      (wab + wbc + wca < 0 ↔ (1 - (2 * h - wab - 1)) + (wbc + h) + (wca + h) = 0 ∨
        ∃ k < K, ∃ j ∈ ({2, 3} : Finset ℤ),
          (j - (2 * h - wab - 1) / 2 ^ k) + (wbc + h) / 2 ^ k + (wca + h) / 2 ^ k = 0) := by
  intro hall
  have := (hall 0 0 (-1) 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp (by norm_num)
  revert this; decide

/-! ### The exhaustive check of check_negtri.py, as a kernel computation -/

def a2rhs (v t tau K : ℕ) : Bool :=
  v + t + 1 == tau || (List.range K).any fun k =>
    v / 2 ^ k + t / 2 ^ k + 2 == tau / 2 ^ k || v / 2 ^ k + t / 2 ^ k + 3 == tau / 2 ^ k

/-- The same test with only the offset 2 (a deliberately wrong identity, for the negative control). -/
def a2rhsBad (v t tau K : ℕ) : Bool :=
  v + t + 1 == tau || (List.range K).any fun k => v / 2 ^ k + t / 2 ^ k + 2 == tau / 2 ^ k

/-- `check_identity(B)` of check_negtri.py with `K = bitlength(max(v, t, tau, 1)) + 3`; negative `tau` makes both
sides false (`v + t ≥ 0`), so only `tau ≥ 0` is enumerated. -/
def a2check (rhs : ℕ → ℕ → ℕ → ℕ → Bool) (B : ℕ) : Bool :=
  (List.range (2 ^ B)).all fun v => (List.range (2 ^ B)).all fun t =>
    (List.range (2 ^ (B + 1) + 5)).all fun tau =>
      (decide (v + t < tau)) == rhs v t tau (Nat.log2 (max (max v t) (max tau 1)) + 1 + 3)

theorem a2_exhaustive_B4 : a2check a2rhs 4 = true := by decide +kernel

theorem a2_exhaustive_wrong_identity_fails : a2check a2rhsBad 4 = false := by decide +kernel

end TS
