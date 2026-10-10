import Mathlib

/-!
# Shared definitions for the 3SUM certificates

Rigorous rational bounds on `Real.log`, the closed forms of `certify.py`, and `minl`, the minimum of a list
of savings (`bmin` in the Python scripts).

Log bounds. For `|t| < 1`, Mathlib's `Real.abs_log_sub_add_sum_range_le` gives
`|∑_{i<n} t^(i+1)/(i+1) + log (1 - t)| ≤ |t|^(n+1) / (1 - |t|)`. A positive rational `x` is written as
`x = 2^k * (1 - t)` with `|t| < 1`, and `log 2 = -log (1 - 1/2)` is bounded by the same series. The partial sums
are computed in `ℚ` and compared by `decide +kernel`. No analytic fact is assumed: everything is proved from Mathlib.
-/

open Real Finset

namespace TS

/-- `∑_{i<n} t^(i+1)/(i+1)` in `ℚ`, by recursion so that the kernel can evaluate it. -/
def lsum (t : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => lsum t n + t ^ (n + 1) / ((n : ℚ) + 1)

/-- The tail bound `|t|^(n+1) / (1 - |t|)`. -/
def lrem (t : ℚ) (n : ℕ) : ℚ := |t| ^ (n + 1) / (1 - |t|)

lemma lsum_cast (t : ℚ) (n : ℕ) :
    ((lsum t n : ℚ) : ℝ) = ∑ i ∈ range n, (t : ℝ) ^ (i + 1) / ((i : ℝ) + 1) := by
  induction n with
  | zero => simp [lsum]
  | succ n ih => rw [sum_range_succ, ← ih]; simp only [lsum]; push_cast; ring

lemma log_one_sub_mem (t : ℚ) (n : ℕ) (ht : |t| < 1) :
    -((lsum t n : ℚ) : ℝ) - ((lrem t n : ℚ) : ℝ) ≤ log (1 - (t : ℝ)) ∧
      log (1 - (t : ℝ)) ≤ -((lsum t n : ℚ) : ℝ) + ((lrem t n : ℚ) : ℝ) := by
  have ht' : |(t : ℝ)| < 1 := by rw [← Rat.cast_abs]; exact_mod_cast ht
  have h := Real.abs_log_sub_add_sum_range_le ht' n
  rw [← lsum_cast] at h
  have hr : ((lrem t n : ℚ) : ℝ) = |(t : ℝ)| ^ (n + 1) / (1 - |(t : ℝ)|) := by
    simp [lrem, Rat.cast_abs]
  rw [← hr] at h
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

/-- Rational bounds on `log 2`, from the series at `t = 1/2` with 150 terms (checked below). -/
def L2lo : ℚ := 693147180559945309417232121458176568075500134 / 10 ^ 45 - 1 / 10 ^ 42
def L2hi : ℚ := 693147180559945309417232121458176568075500134 / 10 ^ 45 + 1 / 10 ^ 42

lemma log_two_mem : (L2lo : ℝ) ≤ log 2 ∧ log 2 ≤ (L2hi : ℝ) := by
  have h := log_one_sub_mem (1 / 2) 150 (by norm_num [abs_of_pos])
  have e : log (2 : ℝ) = -log (1 - (((1 / 2 : ℚ)) : ℝ)) := by
    rw [show (1 : ℝ) - (((1 / 2 : ℚ)) : ℝ) = 2⁻¹ by norm_num, Real.log_inv, neg_neg]
  have c1 : L2lo ≤ lsum (1 / 2) 150 - lrem (1 / 2) 150 := by decide +kernel
  have c2 : lsum (1 / 2) 150 + lrem (1 / 2) 150 ≤ L2hi := by decide +kernel
  have c1' : (L2lo : ℝ) ≤ ((lsum (1 / 2) 150 : ℚ) : ℝ) - ((lrem (1 / 2) 150 : ℚ) : ℝ) := by
    exact_mod_cast c1
  have c2' : ((lsum (1 / 2) 150 : ℚ) : ℝ) + ((lrem (1 / 2) 150 : ℚ) : ℝ) ≤ (L2hi : ℝ) := by
    exact_mod_cast c2
  rw [e]; constructor <;> linarith [h.1, h.2]

lemma kmul_mem (k : ℤ) (a b l : ℝ) (ha : a ≤ l) (hb : l ≤ b) :
    min ((k : ℝ) * a) ((k : ℝ) * b) ≤ (k : ℝ) * l ∧ (k : ℝ) * l ≤ max ((k : ℝ) * a) ((k : ℝ) * b) := by
  rcases le_total 0 (k : ℝ) with hk | hk
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left ha hk),
      (mul_le_mul_of_nonneg_left hb hk).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hb hk),
      (mul_le_mul_of_nonpos_left ha hk).trans (le_max_left _ _)⟩

/-- The kernel-checked condition behind `log_mem`: `x > 0`, `t = 1 - x/2^k` has `|t| < 1`, and the series
bound of `log x = log (1 - t) + k log 2` lies inside `[lo, hi]`. -/
def logOK (x : ℚ) (k : ℤ) (n : ℕ) (lo hi : ℚ) : Bool :=
  decide (0 < x) && decide (|1 - x / 2 ^ k| < 1) &&
  decide (lo ≤ -(lsum (1 - x / 2 ^ k) n) - lrem (1 - x / 2 ^ k) n + min (k * L2lo) (k * L2hi)) &&
  decide (-(lsum (1 - x / 2 ^ k) n) + lrem (1 - x / 2 ^ k) n + max (k * L2lo) (k * L2hi) ≤ hi)

/-- Rigorous bounds `loR ≤ log e ≤ hiR` for a real expression `e` equal to the rational `x`. -/
theorem log_mem (e : ℝ) (x lo hi : ℚ) (k : ℤ) (n : ℕ) (loR hiR : ℝ) (he : e = x) (hlo : loR = lo)
    (hhi : hiR = hi) (h : logOK x k n lo hi = true) : loR ≤ log e ∧ log e ≤ hiR := by
  simp only [logOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hx, ht⟩, h1⟩, h2⟩ := h
  have hb := log_one_sub_mem (1 - x / 2 ^ k) n ht
  have hy : (1 - (((1 - x / 2 ^ k : ℚ)) : ℝ)) = (x : ℝ) / 2 ^ k := by push_cast; ring
  rw [hy] at hb
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hlog : log (x : ℝ) = log ((x : ℝ) / 2 ^ k) + (k : ℝ) * log 2 := by
    rw [Real.log_div hxpos.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow]; ring
  obtain ⟨l2a, l2b⟩ := log_two_mem
  have hk := kmul_mem k _ _ _ l2a l2b
  have h1' : ((lo : ℚ) : ℝ) ≤ ((-(lsum (1 - x / 2 ^ k) n) - lrem (1 - x / 2 ^ k) n
      + min (k * L2lo) (k * L2hi) : ℚ) : ℝ) := by exact_mod_cast h1
  have h2' : ((-(lsum (1 - x / 2 ^ k) n) + lrem (1 - x / 2 ^ k) n
      + max (k * L2lo) (k * L2hi) : ℚ) : ℝ) ≤ ((hi : ℚ) : ℝ) := by exact_mod_cast h2
  push_cast at h1' h2'
  subst he hlo hhi
  rw [hlog]; constructor <;> linarith [hb.1, hb.2, hk.1, hk.2]

/-! ## The closed forms of `certify.py` (all logs natural) -/

/-- Binary entropy in nats, `H(x) = -x ln x - (1-x) ln (1-x)`. -/
noncomputable def H (x : ℝ) : ℝ := -x * log x - (1 - x) * log (1 - x)
/-- `gamma_rho(c, th) = th ln((c-1)/9) / ln 4` (paper, Cor. 4.6). -/
noncomputable def gammaRho (c th : ℝ) : ℝ := th * log ((c - 1) / 9) / log 4
/-- `gamma_exact(c, th) = [c H(1/c) - c H((1-th)/c) - th ln 9] / ln 4`. -/
noncomputable def gammaExact (c th : ℝ) : ℝ := (c * H (1 / c) - c * H ((1 - th) / c) - th * log 9) / log 4
/-- `q(th) = [H(th) + th ln 9] / ln 4`. -/
noncomputable def qExp (th : ℝ) : ℝ := (H th + th * log 9) / log 4
/-- `E_full(c) = [c ln 10 - (c/2) H(1/c) - (c-1) ln 3] / ln 4`. -/
noncomputable def Efull (c : ℝ) : ℝ := (c * log 10 - c * H (1 / c) / 2 - (c - 1) * log 3) / log 4
/-- `E_pruned(c) = [(c/2) H(1/c) + (c-1) ln 3] / ln 4`. -/
noncomputable def Epruned (c : ℝ) : ℝ := (c * H (1 / c) / 2 + (c - 1) * log 3) / log 4

/-! ## Minimum of a list of savings -/

/-- `minl [t₁, …, tₖ] = min t₁ (min t₂ … tₖ)`; the empty list is never used. -/
noncomputable def minl : List ℝ → ℝ
  | [] => 0
  | [x] => x
  | x :: y :: ys => min x (minl (y :: ys))

lemma le_minl {s : ℝ} : ∀ {l : List ℝ}, l ≠ [] → (∀ t ∈ l, s ≤ t) → s ≤ minl l
  | [], h, _ => absurd rfl h
  | [x], _, h => by simpa [minl] using h
  | x :: y :: ys, _, h => by
      simp only [minl]
      exact le_min (h x (by simp)) (le_minl (by simp) (fun t ht => h t (by simp [ht])))

lemma minl_le : ∀ {l : List ℝ} {t : ℝ}, t ∈ l → minl l ≤ t
  | [], _, h => absurd h (by simp)
  | [x], t, h => by simp at h; simp [minl, h]
  | x :: y :: ys, t, h => by
      simp only [minl]
      rcases List.mem_cons.mp h with rfl | h
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (minl_le h)

end TS
