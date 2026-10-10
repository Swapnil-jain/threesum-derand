import ThreesumLean.Basic

/-!
# The certificate statements

One structure per script. Each field is one check that the script makes, written in the script's own form,
plus the printed claims (saving lower bound, exponent upper bounds). A theorem `CertX args` therefore states the full
certificate at that rational point. The `mk'` lemmas build a certificate from lower bounds on each saving term;
the `lower` lemmas extract the claimed bounds, which the negative controls refute.
-/

open Real

namespace TS

lemma minl_le_get (l : List ℝ) (i : ℕ) (h : i < l.length) : minl l ≤ l[i] :=
  minl_le (List.getElem_mem h)

/-! ## certify.py: the paper's route, Exact Triangle saving `s_ET` (the six points of params.json) -/

/-- The three Lop terms: boxes `eps*gamma`, queries `eps*(a - q)`, encodings `1 - eps*E`. -/
noncomputable def etTerms (th a eps g E : ℝ) : List ℝ := [eps * g, eps * (a - qExp th), 1 - eps * E]

/-- `s_ET = min(sigma - eps*eta, eps*eta)` with `sigma` the minimum of the three Lop terms. -/
noncomputable def sET (th a eps eta g E : ℝ) : ℝ := min (minl (etTerms th a eps g E) - eps * eta) (eps * eta)

/-- certify.py: every side condition, then `s_ET >= s0`, `3SUM <= 2 - s/2 <= b3`, `APSP <= 3 - s/3 <= bA`. -/
structure CertET (c th a eps eta g E s0 b3 bA : ℝ) : Prop where
  c_gt : 10 < c
  th_pos : 0 < th
  th_lt : th < 9 / 10
  eps_pos : 0 < eps
  eta_ge : 2 * a - 1 ≤ eta
  eta_le : eta ≤ a
  a_le : a ≤ 1
  terms_pos : ∀ t ∈ etTerms th a eps g E, 0 < t
  choice_p : log 7 / log 2 + 3 * a * eps < 3 - sET th a eps eta g E
  building : 2 + eps * (2 - 2 * a + eta) < 3 - sET th a eps eta g E
  saving : s0 ≤ sET th a eps eta g E
  sum3 : 2 - sET th a eps eta g E / 2 ≤ b3
  apsp : 3 - sET th a eps eta g E / 3 ≤ bA

lemma CertET.mk' {c th a eps eta g E s0 b3 bA : ℝ} (h1 : 10 < c) (h2 : 0 < th) (h3 : th < 9 / 10)
    (h4 : 0 < eps) (h5 : 2 * a - 1 ≤ eta) (h6 : eta ≤ a) (h7 : a ≤ 1)
    (hlow : ∀ t ∈ etTerms th a eps g E, s0 + eps * eta ≤ t) (hk : s0 ≤ eps * eta) (hs0 : 0 < s0)
    (hp : log 7 / log 2 + 3 * a * eps < 3 - eps * eta) (hb : 2 + eps * (2 - 2 * a + eta) < 3 - eps * eta)
    (hb3 : 2 - s0 / 2 ≤ b3) (hbA : 3 - s0 / 3 ≤ bA) : CertET c th a eps eta g E s0 b3 bA := by
  have hS : s0 ≤ sET th a eps eta g E :=
    le_min (le_sub_iff_add_le.mpr (le_minl (by simp [etTerms]) hlow)) hk
  have hu : sET th a eps eta g E ≤ eps * eta := min_le_right _ _
  exact ⟨h1, h2, h3, h4, h5, h6, h7, fun t ht => by linarith [hlow t ht], by linarith, by linarith, hS,
    by linarith, by linarith⟩

lemma CertET.lower {c th a eps eta g E s0 b3 bA : ℝ} (h : CertET c th a eps eta g E s0 b3 bA) :
    s0 ≤ sET th a eps eta g E ∧ 2 * (2 - b3) ≤ sET th a eps eta g E ∧ 3 * (3 - bA) ≤ sET th a eps eta g E :=
  ⟨h.saving, by linarith [h.sum3], by linarith [h.apsp]⟩

lemma sET_le_term {th a eps eta g E : ℝ} (j : ℕ) (hj : j < (etTerms th a eps g E).length) :
    sET th a eps eta g E ≤ (etTerms th a eps g E)[j] - eps * eta :=
  (min_le_left _ _).trans (sub_le_sub_right (minl_le_get _ j hj) _)

lemma sET_le_k {th a eps eta g E : ℝ} : sET th a eps eta g E ≤ eps * eta := min_le_right _ _

/-! ## derand_cert.py: the saving `sigma = sigma(1/2)` of one thin product -/

/-- `sigma = min(eps*gamma, eps*(1/2 - q), 1 - eps*E)`. -/
noncomputable def sigTerms (th eps g E : ℝ) : List ℝ := [eps * g, eps * (1 / 2 - qExp th), 1 - eps * E]

/-- derand_cert.py: every side condition (encodings cheaper than boxes, dense instance building, per-slot
bookkeeping), `sigma >= s0`, det 3SUM `2 - sigma <= b3`, det all-edges ET/(min,+)/APSP `3 - sigma <= bA`, and the
O(n^e) lines `2 - sigma < o3`, `3 - sigma < oA`. -/
structure CertDerand (c th eps g E s0 b3 bA o3 oA : ℝ) : Prop where
  c_gt : 10 < c
  th_pos : 0 < th
  th_lt : th < 9 / 10
  eps_pos : 0 < eps
  terms_pos : ∀ t ∈ sigTerms th eps g E, 0 < t
  enc_lt_box : eps * g < 1 - eps * E
  building : 1 + eps < 2 - minl (sigTerms th eps g E)
  bookkeeping : minl (sigTerms th eps g E) < eps / 2
  saving : s0 ≤ minl (sigTerms th eps g E)
  sum3 : 2 - minl (sigTerms th eps g E) ≤ b3
  apsp : 3 - minl (sigTerms th eps g E) ≤ bA
  sum3_O : 2 - minl (sigTerms th eps g E) < o3
  apsp_O : 3 - minl (sigTerms th eps g E) < oA

lemma CertDerand.mk' {c th eps g E s0 b3 bA o3 oA : ℝ} (h1 : 10 < c) (h2 : 0 < th) (h3 : th < 9 / 10)
    (h4 : 0 < eps) (ht : eps * g < 1 - eps * E) (hbuild : 1 + eps + eps * g < 2) (hq : 0 < eps * qExp th)
    (hlow : ∀ t ∈ sigTerms th eps g E, s0 ≤ t) (hs0 : 0 < s0) (hb3 : 2 - s0 ≤ b3) (hbA : 3 - s0 ≤ bA)
    (ho3 : 2 - s0 < o3) (hoA : 3 - s0 < oA) : CertDerand c th eps g E s0 b3 bA o3 oA := by
  have hS := le_minl (by simp [sigTerms]) hlow
  have hU1 : minl (sigTerms th eps g E) ≤ eps * g := minl_le_get _ 0 (by simp [sigTerms])
  have hU2 : minl (sigTerms th eps g E) ≤ eps * (1 / 2 - qExp th) := minl_le_get _ 1 (by simp [sigTerms])
  exact ⟨h1, h2, h3, h4, fun t ht => by linarith [hlow t ht], ht, by linarith, by linarith, hS, by linarith,
    by linarith, by linarith, by linarith⟩

lemma CertDerand.lower {c th eps g E s0 b3 bA o3 oA : ℝ} (h : CertDerand c th eps g E s0 b3 bA o3 oA) :
    s0 ≤ minl (sigTerms th eps g E) ∧ 2 - b3 ≤ minl (sigTerms th eps g E) ∧
      3 - bA ≤ minl (sigTerms th eps g E) := ⟨h.saving, by linarith [h.sum3], by linarith [h.apsp]⟩

/-! ## certify_L1.py: the hash-free route L1 by bit halving -/

noncomputable def l1Terms (th eps de g E : ℝ) : List ℝ :=
  [de - eps * qExp th, eps * g, 1 - eps * E, eps - 2 * de, 1 - eps, de, 1 - de]

/-- certify_L1.py: side conditions (with the Cor. tradeoff check), all seven terms positive, `S >= s0`,
det 3SUM `2 - S <= b3`, det ET/(min,+)/APSP `3 - S <= bA`, and the O(n^e) lines `2 - S < o3`, `3 - S < oA`. -/
structure CertL1 (c th eps de g E s0 b3 bA o3 oA : ℝ) : Prop where
  c_gt : 10 < c
  th_pos : 0 < th
  th_lt : th < 9 / 10
  eps_pos : 0 < eps
  de_pos : 0 < de
  de_le : de ≤ eps
  eps_le : eps ≤ 1 + de
  tradeoff : eps * g < 1 - eps * E
  terms_pos : ∀ t ∈ l1Terms th eps de g E, 0 < t
  saving : s0 ≤ minl (l1Terms th eps de g E)
  sum3 : 2 - minl (l1Terms th eps de g E) ≤ b3
  apsp : 3 - minl (l1Terms th eps de g E) ≤ bA
  sum3_O : 2 - minl (l1Terms th eps de g E) < o3
  apsp_O : 3 - minl (l1Terms th eps de g E) < oA

lemma CertL1.mk' {c th eps de g E s0 b3 bA o3 oA : ℝ} (h1 : 10 < c) (h2 : 0 < th) (h3 : th < 9 / 10)
    (h4 : 0 < eps) (h5 : 0 < de) (h6 : de ≤ eps) (h7 : eps ≤ 1 + de) (ht : eps * g < 1 - eps * E)
    (hlow : ∀ t ∈ l1Terms th eps de g E, s0 ≤ t) (hs0 : 0 < s0) (hb3 : 2 - s0 ≤ b3) (hbA : 3 - s0 ≤ bA)
    (ho3 : 2 - s0 < o3) (hoA : 3 - s0 < oA) : CertL1 c th eps de g E s0 b3 bA o3 oA := by
  have hS := le_minl (by simp [l1Terms]) hlow
  exact ⟨h1, h2, h3, h4, h5, h6, h7, ht, fun t ht => by linarith [hlow t ht], hS, by linarith, by linarith,
    by linarith, by linarith⟩

lemma CertL1.lower {c th eps de g E s0 b3 bA o3 oA : ℝ} (h : CertL1 c th eps de g E s0 b3 bA o3 oA) :
    s0 ≤ minl (l1Terms th eps de g E) ∧ 2 - b3 ≤ minl (l1Terms th eps de g E) ∧
      3 - bA ≤ minl (l1Terms th eps de g E) := ⟨h.saving, by linarith [h.sum3], by linarith [h.apsp]⟩

end TS
