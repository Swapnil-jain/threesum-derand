import ThreesumLean.Certs

/-!
# Theorem 3 (shared leaves): definitions of the certificate of certificates/bands_cert.py

Everything bands_cert.py uses that the rest of the library lacks, written as computable rational functions so that
the kernel can evaluate them, plus the certificate structure itself.

* The blocking laws of proofs/bands.md, Sec. 3, as finite computations: the worst-key average `22/27` (Lemma 3.1,
  one digit for every carry sum `s`), the shifted-key average `62/81` (Lemma 3.2), and the stretch law `b(len)`
  (Lemma 3.3) by the same enumeration as certificates/check_bands_stretch.py. The kernel checks that the table
  bands_cert.py uses (`B_STRETCH`) is exactly this enumeration for `len <= 5`, and that `b(6), b(7) <= b(5)` (with
  `lam = 8` a stretch holds at most 7 outer levels, so bands_cert.py's `B_STRETCH[min(len, 5)]` is an upper bound for
  every stretch that occurs). These kernel computations are in Bands2Stretch.lean.
* `Aq lam n y bf`: bands_cert.py's `seg_average`, the average over the `n`-subsets of `[lam]` of the product over
  runs.
* `qEff`, `qFill`, `qStar`, `sigB`: the exponents of bands_cert.py, with every `ln A` and `ln C(lam, n)` term.
* `CertBands2`: one field per check in bands_cert.py, plus the printed saving, the exponent and the strict `O(n^e)`
  line.

What is NOT checked here: that these quantities are the costs of the algorithm (proofs/bands.md, a paper proof,
reviewed once), and the probabilistic content of Lemmas 3.1 to 3.3 beyond the finite computations listed above.
-/

open Real Finset

namespace TS

/-! ## Blocking laws (proofs/bands.md, Sec. 3) -/

/-- `b(d) = 1 - pi(d) = (6 + |d|)/9`: the probability that an adjacent move with key digit `d` is blocked. -/
def bAdj (d : ℤ) : ℚ := ((6 + d.natAbs : ℕ) : ℚ) / 9

/-- Lemma 3.1, one digit: with carry sum `s = kappa_p + carry` the row digit `u` is uniform on `{0, 1, 2}` and the
column digit is `(u + s) mod 3`. The average of `b` over `u`. -/
def worstAvg (s : ℕ) : ℚ := ((List.range 3).map fun u => bAdj ((((u + s) % 3 : ℕ) : ℤ) - (u : ℤ))).sum / 3

/-- The worst-key law: for every carry sum `s in {0..3}` the average is at most `22/27`. -/
theorem worstAvg_le : ∀ s < 4, worstAvg s ≤ 22 / 27 := by decide +kernel

/-- The bound is attained (`s = 1` and `s = 2`), so `22/27` cannot be lowered. -/
theorem worstAvg_tight : worstAvg 1 = 22 / 27 ∧ worstAvg 2 = 22 / 27 := by decide +kernel

/-- Negative control: `62/81` is NOT a worst-key bound. -/
theorem worstAvg_not_62_81 : ¬ (∀ s < 4, worstAvg s ≤ 62 / 81) := by decide +kernel

/-- Lemma 3.2: a uniform pair `(u, v)` of digits; the average of `b(v - u)`. -/
def shiftAvg : ℚ := ((List.range 3).flatMap fun u => (List.range 3).map fun v => bAdj ((v : ℤ) - (u : ℤ))).sum / 9

theorem shiftAvg_eq : shiftAvg = 62 / 81 := by decide +kernel

/-- `62/81 = 1 - sum_e pi(e)^2` with `pi = (1, 2, 3, 2, 1)/9`. -/
theorem shift_eq_one_sub_sq :
    1 - ((List.range 5).map fun i => (((3 - ((i : ℤ) - 2).natAbs : ℕ) : ℚ) / 9) ^ 2).sum = 62 / 81 := by
  decide +kernel

/-- The integer spelled by a digit string, lowest digit first. -/
def dval : List ℤ → ℤ
  | [] => 0
  | a :: as => a + 3 * dval as

/-- `9 pi(d) = 3 - |d|`. -/
def wt (d : ℤ) : ℕ := 3 - d.natAbs

/-- Lemma 3.3: with stretch digits `ds` and the symbol `x` at the moved position on top, every move into the
stretch (deleting position `pp < len` instead of the top) changes the key. -/
def blocked (ds : List ℤ) (x : ℤ) : Bool :=
  (List.range ds.length).all fun pp => dval ((ds ++ [x]).eraseIdx pp) != dval ds

/-- The pi-weighted count of blocked `(ds, x)` over all completions of the partial string `ds` by `k` more
digits (prefix weight `w`). Written as a recursion, not a list of all strings, to keep kernel memory small. -/
def bcount : ℕ → List ℤ → ℕ → ℕ
  | 0, ds, w => w * (([-2, -1, 0, 1, 2].filter (blocked ds)).map wt).sum
  | k + 1, ds, w => bcount k (-2 :: ds) w + bcount k (-1 :: ds) (2 * w) + bcount k (0 :: ds) (3 * w) +
      bcount k (1 :: ds) (2 * w) + bcount k (2 :: ds) w

/-- `9^(len + 1) b(len)`: the pi-weighted number of blocked `(ds, x)` (`bstretch` in
certificates/check_bands_stretch.py). -/
def bnum (n : ℕ) : ℕ := bcount n [] 1

/-- bands_cert.py's `B_STRETCH[min(len, 5)]`. -/
def bS (len : ℕ) : ℚ :=
  [1, 62 / 81, 538 / 729, 4834 / 6561, 43498 / 59049, 391474 / 531441].getD (min len 5) 1

/-- Weights factor out of `bcount`. -/
theorem bcount_mul (k : ℕ) : ∀ (ds : List ℤ) (w v : ℕ), bcount k ds (w * v) = w * bcount k ds v := by
  induction k with
  | zero => intro ds w v; simp only [bcount]; ring
  | succ k ih =>
    intro ds w v
    simp only [bcount]
    rw [show 2 * (w * v) = w * (2 * v) by ring, show 3 * (w * v) = w * (3 * v) by ring]
    simp only [ih]; ring

theorem bcount_w (k : ℕ) (ds : List ℤ) (w : ℕ) : bcount k ds w = w * bcount k ds 1 := by
  rw [← bcount_mul, mul_one]

/-- One level of `bcount`, with the weights pulled out. -/
theorem bcount_succ' (k : ℕ) (ds : List ℤ) (w : ℕ) :
    bcount (k + 1) ds w = w * (bcount k (-2 :: ds) 1 + 2 * bcount k (-1 :: ds) 1 + 3 * bcount k (0 :: ds) 1 +
      2 * bcount k (1 :: ds) 1 + bcount k (2 :: ds) 1) := by
  simp only [bcount]
  rw [bcount_w k (-2 :: ds) w, bcount_w k (-1 :: ds) (2 * w), bcount_w k (0 :: ds) (3 * w),
    bcount_w k (1 :: ds) (2 * w), bcount_w k (2 :: ds) w]
  ring

/-- The constant laws of tiers (W) and (S). -/
def bW (_ : ℕ) : ℚ := 22 / 27
def bSh (_ : ℕ) : ℚ := 62 / 81

/-! ## The class average `A(lam, n; y, b)` -/

/-- Maximal runs `(start, length)` of an increasing list. -/
def runs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: xs =>
    match runs xs with
    | [] => [(x, 1)]
    | (s, k) :: rest => if x + 1 = s then (x, k + 1) :: rest else (x, 1) :: (s, k) :: rest

/-- Product over runs: `(1 + y)^k` for a run at the segment's first level, else `1 + b((1 + y)^k - 1)` with
`b = bf(len)`, `len` = the gap below the run (`e` = one past the previous run, initially 0). -/
def runFactors (y : ℚ) (bf : ℕ → ℚ) : ℕ → List (ℕ × ℕ) → ℚ
  | _, [] => 1
  | e, (s, k) :: rest =>
    (if s = 0 then (1 + y) ^ k else 1 + bf (s - e) * ((1 + y) ^ k - 1)) * runFactors y bf (s + k) rest

/-- bands_cert.py `seg_average(lam, n, y, law)`: the average over the `n`-subsets of `[lam]`. -/
def Aq (lam n : ℕ) (y : ℚ) (bf : ℕ → ℚ) : ℚ :=
  (((List.range lam).sublistsLen n).map fun S => runFactors y bf 0 (runs S)).sum / (lam.choose n : ℚ)

/-- The binomial law `Bin(lam, 1/c)` at `n`. -/
def pmq (lam n : ℕ) (c : ℚ) : ℚ := (lam.choose n : ℚ) * (1 / c) ^ n * (1 - 1 / c) ^ (lam - n)

/-! ## The exponents of bands_cert.py (natural logs) -/

/-- `zeta = log_3(2)/(c - 1)`, the zone fraction. -/
noncomputable def zetaB (c : ℝ) : ℝ := (log 2 / log 3) / (c - 1)

/-- `sum_n Bin(n) ln A(lam, n; y, b)`. -/
noncomputable def EA (lam : ℕ) (c y : ℚ) (bf : ℕ → ℚ) : ℝ :=
  ∑ n ∈ range (lam + 1), (pmq lam n c : ℝ) * log (Aq lam n y bf : ℝ)

/-- `sum_n Bin(n) ln C(lam, n)`. -/
noncomputable def ECl (lam : ℕ) (c : ℚ) : ℝ :=
  ∑ n ∈ range (lam + 1), (pmq lam n c : ℝ) * log (((lam.choose n : ℕ) : ℚ) : ℝ)

/-- `q_eff = [-th ln z + (1 - zeta)(c/lam) sum_n Bin(n) ln A(lam, n; 9z, b) + zeta ln(1 + 9z)]/ln 4`. -/
noncomputable def qEff (lam : ℕ) (bf : ℕ → ℚ) (c th z : ℚ) : ℝ :=
  (-(th : ℝ) * log z + (1 - zetaB c) * ((c : ℝ) / lam) * EA lam c (9 * z) bf + zetaB c * log (1 + 9 * (z : ℝ)))
    / log 4

/-- `q_fill = [(c/lam) sum_n Bin(n) ln C(lam, n) - (c/2) H(1/c) + H(th) + th ln 9]/ln 4`. -/
noncomputable def qFill (lam : ℕ) (c th : ℚ) : ℝ :=
  ((c : ℝ) / lam * ECl lam c - (c : ℝ) / 2 * H (1 / c) + H th + th * log 9) / log 4

/-- `q* = max(q_eff, q_fill)`. -/
noncomputable def qStar (lam : ℕ) (bf : ℕ → ℚ) (c th z : ℚ) : ℝ := max (qEff lam bf c th z) (qFill lam c th)

/-- The three terms `eps gamma`, `eps (1/2 - q*)`, `1 - eps E`. -/
noncomputable def b2Terms (eps g E qs : ℝ) : List ℝ := [eps * g, eps * (1 / 2 - qs), 1 - eps * E]

/-- `sigma = min(eps gamma, eps (1/2 - q*), 1 - eps E)` with exact boxes and pruned encodings. -/
noncomputable def sigB (lam : ℕ) (bf : ℕ → ℚ) (c th eps z : ℚ) : ℝ :=
  minl (b2Terms eps (gammaExact c th) (Epruned c) (qStar lam bf c th z))

/-- The layout precomputation exponent `e_pre = eps c (ln 9/lam + H(1/c))/ln 4` (proofs/bands.md, Sec. 4). -/
noncomputable def ePre (lam : ℕ) (c eps : ℚ) : ℝ := (eps : ℝ) * c * (log 9 / lam + H (1 / c)) / log 4

/-- bands_cert.py: every side condition at `(c, theta, eps, z, lam, b)`, then `sigma >= s0`, the 3SUM exponent
`2 - sigma <= b` and the `O(n^o)` line `2 - sigma < o`. -/
structure CertBands2 (lam : ℕ) (bf : ℕ → ℚ) (c th eps z : ℚ) (s0 b o : ℝ) : Prop where
  c_gt : 10 < c
  th_pos : 0 < th
  th_lt : th < 9 / 10
  eps_pos : 0 < eps
  z_pos : 0 < z
  z_le : z ≤ 1
  gamma_pos : 0 < gammaExact c th
  terms_pos : ∀ t ∈ b2Terms eps (gammaExact c th) (Epruned c) (qStar lam bf c th z), 0 < t
  enc_box : (eps : ℝ) * (Epruned c + gammaExact c th) < 1
  qstar_lt : qStar lam bf c th z < 1 / 2
  fill_lt : qFill lam c th < qEff lam bf c th z
  sig_lt : sigB lam bf c th eps z < eps / 2
  writing : 1 + (eps : ℝ) < 2 - sigB lam bf c th eps z
  partial_bands : (eps : ℝ) * (Epruned c + qExp th - 1 / 2) + sigB lam bf c th eps z < 1
  precompute : ePre lam c eps < 2 - sigB lam bf c th eps z
  saving : s0 ≤ sigB lam bf c th eps z
  exponent : 2 - sigB lam bf c th eps z ≤ b
  exponent_O : 2 - sigB lam bf c th eps z < o

lemma sigB_eq {lam : ℕ} {bf : ℕ → ℚ} {c th eps z : ℚ} (h : qFill lam c th < qEff lam bf c th z) :
    sigB lam bf c th eps z = minl (b2Terms eps (gammaExact c th) (Epruned c) (qEff lam bf c th z)) := by
  unfold sigB qStar; rw [max_eq_left h.le]

/-- Build the certificate from a lower bound `s0` on every term and an upper bound `U` on one of them. -/
lemma CertBands2.mk' {lam : ℕ} {bf : ℕ → ℚ} {c th eps z : ℚ} {s0 b o U : ℝ}
    (h1 : 10 < c) (h2 : 0 < th) (h3 : th < 9 / 10) (h4 : 0 < eps) (h5 : 0 < z) (h6 : z ≤ 1)
    (hg : 0 < gammaExact c th) (hfill : qFill lam c th < qEff lam bf c th z)
    (hlow : ∀ t ∈ b2Terms eps (gammaExact c th) (Epruned c) (qEff lam bf c th z), s0 ≤ t) (hs0 : 0 < s0)
    (henc : (eps : ℝ) * (Epruned c + gammaExact c th) < 1) (hq : qEff lam bf c th z < 1 / 2)
    (hU : (eps : ℝ) * gammaExact c th ≤ U ∨ (eps : ℝ) * (1 / 2 - qEff lam bf c th z) ≤ U ∨
      1 - (eps : ℝ) * Epruned c ≤ U)
    (hsU : U < eps / 2) (hwU : 1 + (eps : ℝ) < 2 - U)
    (hpU : (eps : ℝ) * (Epruned c + qExp th - 1 / 2) + U < 1) (hpre : ePre lam c eps < 2 - U)
    (hb : 2 - s0 ≤ b) (ho : 2 - s0 < o) : CertBands2 lam bf c th eps z s0 b o := by
  have hS := sigB_eq (eps := eps) hfill
  have hqs : qStar lam bf c th z = qEff lam bf c th z := max_eq_left hfill.le
  have hlo : s0 ≤ sigB lam bf c th eps z := hS ▸ le_minl (by simp [b2Terms]) hlow
  have hup : sigB lam bf c th eps z ≤ U := by
    rw [hS]
    rcases hU with h | h | h
    · exact (minl_le (by simp [b2Terms])).trans h
    · exact (minl_le (by simp [b2Terms])).trans h
    · exact (minl_le (by simp [b2Terms])).trans h
  refine ⟨h1, h2, h3, h4, h5, h6, hg, ?_, henc, hqs ▸ hq, hfill, by linarith, by linarith, by linarith,
    by linarith, hlo, by linarith, by linarith⟩
  rw [hqs]; intro t ht; linarith [hlow t ht]

/-- The claimed bounds, which the negative controls refute. -/
lemma CertBands2.lower {lam : ℕ} {bf : ℕ → ℚ} {c th eps z : ℚ} {s0 b o : ℝ}
    (h : CertBands2 lam bf c th eps z s0 b o) :
    s0 ≤ sigB lam bf c th eps z ∧ 2 - b ≤ sigB lam bf c th eps z ∧ 2 - o < sigB lam bf c th eps z :=
  ⟨h.saving, by linarith [h.exponent], by linarith [h.exponent_O]⟩

/-- Each term bounds `sigma` from above (`q* >= q_eff` and `eps > 0` for the middle one). -/
lemma CertBands2.upper {lam : ℕ} {bf : ℕ → ℚ} {c th eps z : ℚ} {s0 b o : ℝ}
    (h : CertBands2 lam bf c th eps z s0 b o) :
    sigB lam bf c th eps z ≤ (eps : ℝ) * gammaExact c th ∧
      sigB lam bf c th eps z ≤ (eps : ℝ) * (1 / 2 - qEff lam bf c th z) ∧
      sigB lam bf c th eps z ≤ 1 - (eps : ℝ) * Epruned c := by
  have he : (0 : ℝ) ≤ eps := by exact_mod_cast h.eps_pos.le
  have hq : qEff lam bf c th z ≤ qStar lam bf c th z := le_max_left _ _
  unfold sigB
  refine ⟨minl_le_get _ 0 (by simp [b2Terms]), (minl_le_get _ 1 (by simp [b2Terms])).trans ?_,
    minl_le_get _ 2 (by simp [b2Terms])⟩
  exact mul_le_mul_of_nonneg_left (by linarith) he

/-- Product bounds for nonnegative intervals. -/
lemma mul_mem {x y xl xh yl yh : ℝ} (hx : xl ≤ x ∧ x ≤ xh) (hy : yl ≤ y ∧ y ≤ yh) (hxl : 0 ≤ xl)
    (hyl : 0 ≤ yl) : xl * yl ≤ x * y ∧ x * y ≤ xh * yh :=
  ⟨mul_le_mul hx.1 hy.1 hyl (hxl.trans hx.1),
    mul_le_mul hx.2 hy.2 (hyl.trans hy.1) ((hxl.trans hx.1).trans hx.2)⟩

/-- Log bounds for a rational `x` (possibly with a huge numerator) through simpler rationals `xl <= x <= xh`. -/
theorem log_rat_mem (x xl xh lo hi lo' hi' : ℚ) (k1 k2 : ℤ) (n : ℕ) (hl : xl ≤ x) (hh : x ≤ xh)
    (h1 : logOK xl k1 n lo hi' = true) (h2 : logOK xh k2 n lo' hi = true) :
    (lo : ℝ) ≤ log (x : ℝ) ∧ log (x : ℝ) ≤ (hi : ℝ) := by
  obtain ⟨a, -⟩ := log_mem (xl : ℝ) xl lo hi' k1 n (lo : ℝ) (hi' : ℝ) rfl rfl rfl h1
  obtain ⟨-, b⟩ := log_mem (xh : ℝ) xh lo' hi k2 n (lo' : ℝ) (hi : ℝ) rfl rfl rfl h2
  have hxl : (0 : ℚ) < xl := by
    simp only [logOK, Bool.and_eq_true, decide_eq_true_eq] at h1; exact h1.1.1.1
  have hxl' : (0 : ℝ) < xl := by exact_mod_cast hxl
  have hl' : (xl : ℝ) ≤ x := by exact_mod_cast hl
  have hh' : (x : ℝ) ≤ xh := by exact_mod_cast hh
  exact ⟨a.trans (Real.log_le_log hxl' hl'), (Real.log_le_log (hxl'.trans_le hl') hh').trans b⟩

end TS
