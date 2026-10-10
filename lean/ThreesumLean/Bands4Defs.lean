import ThreesumLean.Bands2Defs

/-!
# Theorem C'': window moves per element (Lemma Y) and mixed segment lengths (certificates/bands4_cert.py)

Theorem C'' keeps Theorem C' and changes two things (proofs/bands.md, Sec. 10):
* Lemma Y: every element of a segment's key set is tested on its own against all outer levels of the segment below
  it, so the class average of a segment of length `lam` with `n` keys is a polynomial `A_Y(lam, n; y)` in `y = 9z`;
  in zone segments Rule Z applies to every element, giving `A_ZY(lam, n; y)`. The exact coefficients come from
  certificates/bands4_poly.py (saved in bands4_poly.json) and are written here as data (`tabY`, `tabZY`).
* Segment lengths are mixed: a fraction `w_lam` of the segments has length `lam` (`pat`, the pattern), with mean
  length `Lbar = sum w lam`. Every per-segment term of Theorem C' is replaced by its `w`-weighted mix over `pat`,
  divided by `Lbar` instead of `lam`.
gamma, E, the three sigma terms and every side condition are Theorem C's (Bands2Defs.lean), unchanged, plus one
packing condition: a class must fit whole on one integer diagonal, `ln(class)/mu < ln K0/mu`. It does not follow
from `q_fill < q_eff` in general, so it is its own field.

What is NOT checked here: Lemma Y and Rule Z per element (paper proofs, proofs/bands.md Sec. 10), and that the tables
are the averages they claim to be (bands4_poly.py computes them two independent ways). Lean checks every arithmetic
step from these tables to the exponent.
-/

open Real Finset

namespace TS

/-! ## The segment polynomials -/

/-- A polynomial from its coefficients, lowest degree first (Horner). -/
def polyEval : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: as, y => a + y * polyEval as y

/-- bands4_poly.json `Y,lam,n` for lam = 8, 9 (outer index lam - 8, inner index n): coefficients, lowest first. -/
def tabY : List (List (List ℚ)) := [
    [
      [1],
      [1, 266318371/344373768],
      [1, 52135346/33480783, 734123713/1205308188],
      [1, 2504935/1062882, 20774525/11160261, 169664725/344373768],
      [1, 939316/295245, 10149586/2657205, 343267348/167403915, 1251187097/3013270470],
      [1, 106295/26244, 390343/59049, 1924777/354294, 75248183/33480783, 128909677/344373768],
      [1, 3650/729, 138245/13122, 703802/59049, 4061681/531441, 88139354/33480783, 50941897/133923132],
      [1, 1001/162, 1337/81, 648025/26244, 439411/19683, 12956741/1062882, 5931173/1594323, 168469955/344373768],
      [1, 8, 28, 56, 70, 56, 28, 8, 1]],
    [
      [1],
      [1, 2682249157/3486784401],
      [1, 266318371/172186884, 8376237911/13947137604],
      [1, 26067673/11160261, 734123713/401769396, 15577515197/32543321076],
      [1, 5009870/1594323, 41549050/11160261, 169664725/86093442, 19193570591/48814981614],
      [1, 234829/59049, 10149586/1594323, 171633674/33480783, 1251187097/602654094, 2358728131/6973568802],
      [1, 21259/4374, 390343/39366, 1924777/177147, 75248183/11160261, 128909677/57395628, 3402673325/10847773692],
      [1, 12775/2187, 193543/13122, 2463307/118098, 28431767/1594323, 44069677/4782969, 50941897/19131876, 4628753197/13947137604],
      [1, 572/81, 5348/243, 259210/6561, 878822/19683, 51826964/1594323, 23724692/1594323, 168469955/43046721, 58440077/129140163],
      [1, 9, 36, 84, 126, 126, 84, 36, 9, 1]]]

/-- bands4_poly.json `ZY,lam,n` for lam = 8, 9 (outer index lam - 8, inner index n): coefficients, lowest first. -/
def tabZY : List (List (List ℚ)) := [
    [
      [1],
      [1, 65/72],
      [1, 38/21, 619/756],
      [1, 49/18, 467/189, 30529/40824],
      [1, 164/45, 2018/405, 77284/25515, 317249/459270],
      [1, 55/12, 227/27, 11249/1458, 54227/15309, 717419/1102248],
      [1, 50/9, 695/54, 11602/729, 72689/6561, 567206/137781, 9492289/14880348],
      [1, 119/18, 1519/81, 86275/2916, 183967/6561, 1885079/118098, 2685817/531441, 26269505/38263752],
      [1, 8, 28, 56, 70, 56, 28, 8, 1]],
    [
      [1],
      [1, 73/81],
      [1, 65/36, 2377/2916],
      [1, 19/7, 619/252, 45385/61236],
      [1, 98/27, 934/189, 30529/10206, 561481/826686],
      [1, 41/9, 2018/243, 38642/5103, 317249/91854, 4690249/7440174],
      [1, 11/2, 227/18, 11249/729, 54227/5103, 717419/183708, 26710345/44641044],
      [1, 175/27, 973/54, 40607/1458, 508823/19683, 283603/19683, 9492289/2125764, 102207817/172186884],
      [1, 68/9, 6076/243, 34510/729, 367934/6561, 7540316/177147, 10743268/531441, 26269505/4782969, 253202761/387420489],
      [1, 9, 36, 84, 126, 126, 84, 36, 9, 1]]]

/-- The Lemma Y coefficients of `A_Y(lam, n; y)` (non-zone segments). Empty (the zero polynomial) off the table. -/
def coefY (lam n : ℕ) : List ℚ := (tabY.getD (lam - 8) []).getD n []

/-- The Rule Z per element coefficients of `A_ZY(lam, n; y)` (zone segments). -/
def coefZY (lam n : ℕ) : List ℚ := (tabZY.getD (lam - 8) []).getD n []

/-! ## The segment pattern -/

/-- bands4_cert.py's pattern checks: the weights are positive and sum to 1, and every length is 8 or 9 (the lengths the
tables cover). -/
def PatOK (pat : List (ℕ × ℚ)) : Prop :=
  (pat.map Prod.snd).sum = 1 ∧ ∀ p ∈ pat, 0 < p.2 ∧ (p.1 = 8 ∨ p.1 = 9)

instance (pat : List (ℕ × ℚ)) : Decidable (PatOK pat) := by unfold PatOK; infer_instance

/-- The mean segment length `Lbar = sum w lam`. -/
def lbar (pat : List (ℕ × ℚ)) : ℚ := (pat.map fun p => (p.1 : ℚ) * p.2).sum

/-- The `w`-weighted mix `sum_{(lam, w) in pat} w f(lam)`. -/
noncomputable def segSum (pat : List (ℕ × ℚ)) (f : ℕ → ℝ) : ℝ := (pat.map fun p => (p.2 : ℝ) * f p.1).sum

/-! ## The exponents of bands4_cert.py -/

/-- `sum_n Bin(lam, 1/c)(n) ln A(lam, n; y)` for the polynomial table `coef`. -/
noncomputable def EAl (coef : ℕ → ℕ → List ℚ) (lam : ℕ) (c y : ℚ) : ℝ :=
  ∑ n ∈ range (lam + 1), (pmq lam n c : ℝ) * log (polyEval (coef lam n) y : ℝ)

/-- `q_eff = [-th ln z + (c/Lbar) sum_lam w_lam ((1 - zeta) EA_Y(lam) + zeta EA_ZY(lam))]/ln 4`, `y = 9z`. -/
noncomputable def qEff4 (pat : List (ℕ × ℚ)) (cA cZ : ℕ → ℕ → List ℚ) (c th z : ℚ) : ℝ :=
  (-(th : ℝ) * log z + ((c : ℝ) / (lbar pat : ℝ)) *
      segSum pat (fun l => (1 - zetaB c) * EAl cA l c (9 * z) + zetaB c * EAl cZ l c (9 * z))) / log 4

/-- `ln(class)/mu = (c/Lbar) sum_lam w_lam sum_n Bin(n) ln C(lam, n)`: the log size of a good-signature class per
key level. -/
noncomputable def lnClass4 (pat : List (ℕ × ℚ)) (c : ℚ) : ℝ :=
  (c : ℝ) / (lbar pat : ℝ) * segSum pat (fun l => ECl l c)

/-- `ln(K0)/mu = (c/2) H(1/c)`: the log capacity of one integer diagonal per key level. -/
noncomputable def lnK0 (c : ℚ) : ℝ := (c : ℝ) / 2 * H (1 / c)

/-- `q_fill = [ln(class)/mu - ln(K0)/mu + H(th) + th ln 9]/ln 4`. -/
noncomputable def qFill4 (pat : List (ℕ × ℚ)) (c th : ℚ) : ℝ :=
  (lnClass4 pat c - lnK0 c + H th + th * log 9) / log 4

/-- `q* = max(q_eff, q_fill)`. -/
noncomputable def qStar4 (pat : List (ℕ × ℚ)) (cA cZ : ℕ → ℕ → List ℚ) (c th z : ℚ) : ℝ :=
  max (qEff4 pat cA cZ c th z) (qFill4 pat c th)

/-- `sigma = min(eps gamma, eps (1/2 - q*), 1 - eps E)`, Theorem C's terms with the Lemma Y `q*`. -/
noncomputable def sigB4 (pat : List (ℕ × ℚ)) (cA cZ : ℕ → ℕ → List ℚ) (c th eps z : ℚ) : ℝ :=
  minl (b2Terms eps (gammaExact c th) (Epruned c) (qStar4 pat cA cZ c th z))

/-- The layout precomputation exponent `e_pre = eps c (sum_lam w_lam ln(lam + 1)/Lbar + H(1/c))/ln 4`. -/
noncomputable def ePre4 (pat : List (ℕ × ℚ)) (c eps : ℚ) : ℝ :=
  (eps : ℝ) * c * (segSum pat (fun l => log (((l + 1 : ℕ) : ℚ) : ℝ)) / (lbar pat : ℝ) + H (1 / c)) / log 4

/-- bands4_cert.py: every side condition at `(c, theta, eps, z, pattern, law)`, then `sigma >= s0`, the 3SUM exponent
`2 - sigma <= b` and the `O(n^o)` line `2 - sigma < o`. The fields are those of `CertBands3` plus the pattern
checks and `class_fits`. -/
structure CertBands4 (pat : List (ℕ × ℚ)) (cA cZ : ℕ → ℕ → List ℚ) (c th eps z : ℚ) (s0 b o : ℝ) : Prop where
  c_gt : 10 < c
  th_pos : 0 < th
  th_lt : th < 9 / 10
  eps_pos : 0 < eps
  z_pos : 0 < z
  z_le : z ≤ 1
  pat_ok : PatOK pat
  gamma_pos : 0 < gammaExact c th
  terms_pos : ∀ t ∈ b2Terms eps (gammaExact c th) (Epruned c) (qStar4 pat cA cZ c th z), 0 < t
  enc_box : (eps : ℝ) * (Epruned c + gammaExact c th) < 1
  qstar_lt : qStar4 pat cA cZ c th z < 1 / 2
  fill_lt : qFill4 pat c th < qEff4 pat cA cZ c th z
  /-- A class fits whole on one diagonal (the packing of proofs/bands.md, Sec. 4). Not implied by `fill_lt`: that would need
  `H(th) + th ln 9 >= q_eff ln 4`, which fails for small `th` (see the `class_fits` control in Bands4Points). -/
  class_fits : lnClass4 pat c < lnK0 c
  sig_lt : sigB4 pat cA cZ c th eps z < eps / 2
  writing : 1 + (eps : ℝ) < 2 - sigB4 pat cA cZ c th eps z
  partial_bands : (eps : ℝ) * (Epruned c + qExp th - 1 / 2) + sigB4 pat cA cZ c th eps z < 1
  precompute : ePre4 pat c eps < 2 - sigB4 pat cA cZ c th eps z
  saving : s0 ≤ sigB4 pat cA cZ c th eps z
  exponent : 2 - sigB4 pat cA cZ c th eps z ≤ b
  exponent_O : 2 - sigB4 pat cA cZ c th eps z < o

lemma sigB4_eq {pat : List (ℕ × ℚ)} {cA cZ : ℕ → ℕ → List ℚ} {c th eps z : ℚ}
    (h : qFill4 pat c th < qEff4 pat cA cZ c th z) :
    sigB4 pat cA cZ c th eps z = minl (b2Terms eps (gammaExact c th) (Epruned c) (qEff4 pat cA cZ c th z)) := by
  unfold sigB4 qStar4; rw [max_eq_left h.le]

/-- Build the certificate from a lower bound `s0` on every term and an upper bound `U` on one of them. -/
lemma CertBands4.mk' {pat : List (ℕ × ℚ)} {cA cZ : ℕ → ℕ → List ℚ} {c th eps z : ℚ} {s0 b o U : ℝ}
    (h1 : 10 < c) (h2 : 0 < th) (h3 : th < 9 / 10) (h4 : 0 < eps) (h5 : 0 < z) (h6 : z ≤ 1)
    (hpat : PatOK pat) (hg : 0 < gammaExact c th) (hfill : qFill4 pat c th < qEff4 pat cA cZ c th z)
    (hfit : lnClass4 pat c < lnK0 c)
    (hlow : ∀ t ∈ b2Terms eps (gammaExact c th) (Epruned c) (qEff4 pat cA cZ c th z), s0 ≤ t) (hs0 : 0 < s0)
    (henc : (eps : ℝ) * (Epruned c + gammaExact c th) < 1) (hq : qEff4 pat cA cZ c th z < 1 / 2)
    (hU : (eps : ℝ) * gammaExact c th ≤ U ∨ (eps : ℝ) * (1 / 2 - qEff4 pat cA cZ c th z) ≤ U ∨
      1 - (eps : ℝ) * Epruned c ≤ U)
    (hsU : U < eps / 2) (hwU : 1 + (eps : ℝ) < 2 - U)
    (hpU : (eps : ℝ) * (Epruned c + qExp th - 1 / 2) + U < 1) (hpre : ePre4 pat c eps < 2 - U)
    (hb : 2 - s0 ≤ b) (ho : 2 - s0 < o) : CertBands4 pat cA cZ c th eps z s0 b o := by
  have hS := sigB4_eq (eps := eps) hfill
  have hqs : qStar4 pat cA cZ c th z = qEff4 pat cA cZ c th z := max_eq_left hfill.le
  have hlo : s0 ≤ sigB4 pat cA cZ c th eps z := hS ▸ le_minl (by simp [b2Terms]) hlow
  have hup : sigB4 pat cA cZ c th eps z ≤ U := by
    rw [hS]
    rcases hU with h | h | h
    · exact (minl_le (by simp [b2Terms])).trans h
    · exact (minl_le (by simp [b2Terms])).trans h
    · exact (minl_le (by simp [b2Terms])).trans h
  refine ⟨h1, h2, h3, h4, h5, h6, hpat, hg, ?_, henc, hqs ▸ hq, hfill, hfit, by linarith, by linarith, by linarith,
    by linarith, hlo, by linarith, by linarith⟩
  rw [hqs]; intro t ht; linarith [hlow t ht]

/-- The claimed bounds, which the negative controls refute. -/
lemma CertBands4.lower {pat : List (ℕ × ℚ)} {cA cZ : ℕ → ℕ → List ℚ} {c th eps z : ℚ} {s0 b o : ℝ}
    (h : CertBands4 pat cA cZ c th eps z s0 b o) :
    s0 ≤ sigB4 pat cA cZ c th eps z ∧ 2 - b ≤ sigB4 pat cA cZ c th eps z ∧ 2 - o < sigB4 pat cA cZ c th eps z :=
  ⟨h.saving, by linarith [h.exponent], by linarith [h.exponent_O]⟩

/-- Each term bounds `sigma` from above (`q* >= q_eff` and `eps > 0` for the middle one). -/
lemma CertBands4.upper {pat : List (ℕ × ℚ)} {cA cZ : ℕ → ℕ → List ℚ} {c th eps z : ℚ} {s0 b o : ℝ}
    (h : CertBands4 pat cA cZ c th eps z s0 b o) :
    sigB4 pat cA cZ c th eps z ≤ (eps : ℝ) * gammaExact c th ∧
      sigB4 pat cA cZ c th eps z ≤ (eps : ℝ) * (1 / 2 - qEff4 pat cA cZ c th z) ∧
      sigB4 pat cA cZ c th eps z ≤ 1 - (eps : ℝ) * Epruned c := by
  have he : (0 : ℝ) ≤ eps := by exact_mod_cast h.eps_pos.le
  have hq : qEff4 pat cA cZ c th z ≤ qStar4 pat cA cZ c th z := le_max_left _ _
  unfold sigB4
  refine ⟨minl_le_get _ 0 (by simp [b2Terms]), (minl_le_get _ 1 (by simp [b2Terms])).trans ?_,
    minl_le_get _ 2 (by simp [b2Terms])⟩
  exact mul_le_mul_of_nonneg_left (by linarith) he

end TS
