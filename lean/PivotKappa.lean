import HairbrushLogLoss

/-! One explicit density-independent kappa simultaneously satisfies the
physical legal-sample exclusion and marked-direction half-cap tests. -/
namespace KakeyaFormal.PivotKappa
open HairbrushScales HairbrushLogLoss
noncomputable section

/-- The two radii are multiplied so that a single choice meets both tests
and has a direct polynomial logarithmic lower bound. -/
def choice (width B K alpha beta : ℝ) : ℝ :=
  concentrationRadius (8*B) alpha*concentrationRadius K beta/(100*(2*width+1))

def loss (alpha beta b q : ℝ) : ℝ := b/alpha+q/beta

theorem choice_pos {width B K alpha beta : ℝ} (hw : 0 ≤ width)
    (hB : 0 < B) (hK : 0 < K) : 0 < choice width B K alpha beta := by
  have hR₁ := concentrationRadius_pos (alpha := alpha) (by positivity : 0 < 8*B)
  have hR₂ := concentrationRadius_pos (alpha := beta) hK
  unfold choice
  positivity

theorem choice_le_hundredth {width B K alpha beta : ℝ} (hw : 0 ≤ width)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (ha : 0 < alpha) (hb : 0 < beta) :
    choice width B K alpha beta ≤ 1/100 := by
  have hR₁ := concentrationRadius_pos (alpha := alpha) (by linarith : 0 < 8*B)
  have hR₂ := concentrationRadius_pos (alpha := beta) (by linarith : 0 < K)
  have hR₁1 := concentrationRadius_le_one (by linarith : 1/2 ≤ 8*B) ha
  have hR₂1 := concentrationRadius_le_one (by linarith : 1/2 ≤ K) hb
  unfold choice
  apply (div_le_iff₀ (by positivity : 0 < 100*(2*width+1))).mpr
  nlinarith

/-- The actual physical test radius is bounded by the two-ends radius chosen
with constant8B, independently of the angular radius. -/
theorem physical_radius_le {width B K alpha beta : ℝ} (hw : 0 ≤ width)
    (hB : 0 < B) (hK : 1 ≤ K) (hb : 0 < beta) :
    (2*width+1)*choice width B K alpha beta ≤ concentrationRadius (8*B) alpha := by
  have hR₁ := concentrationRadius_pos (alpha := alpha) (by positivity : 0 < 8*B)
  have hR₂1 := concentrationRadius_le_one (by linarith : 1/2 ≤ K) hb
  have hD : 2*width+1 ≠ 0 := by positivity
  have hid : (2*width+1)*choice width B K alpha beta =
      concentrationRadius (8*B) alpha*concentrationRadius K beta/100 := by
    unfold choice
    field_simp
  rw [hid]
  exact (div_le_iff₀ (by norm_num : (0:ℝ) < 100)).mpr (by nlinarith)

theorem physical_radius_le_one {width B K alpha beta : ℝ} (hw : 0 ≤ width)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (ha : 0 < alpha) (hb : 0 < beta) :
    (2*width+1)*choice width B K alpha beta ≤ 1 :=
  (physical_radius_le hw (by linarith) hK hb).trans
    (concentrationRadius_le_one (by linarith : 1/2 ≤ 8*B) ha)

/-- Twice the same kappa is below the marked broadness radius. -/
theorem angular_radius_le {width B K alpha beta : ℝ} (hw : 0 ≤ width)
    (hB : 1 ≤ B) (hK : 0 < K) (ha : 0 < alpha) :
    2*choice width B K alpha beta ≤ concentrationRadius K beta := by
  have hR₂ := concentrationRadius_pos (alpha := beta) hK
  have hR₁1 := concentrationRadius_le_one (by linarith : 1/2 ≤ 8*B) ha
  have hD : 0 < 100*(2*width+1) := by positivity
  have hd : 2*concentrationRadius (8*B) alpha ≤ 100*(2*width+1) := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hd hR₂.le
  unfold choice
  rw [← mul_div_assoc]
  exact (div_le_iff₀ hD).mpr (by nlinarith)

/-- The precise1/16 legal-sample interval exclusion follows from the physical
two-ends coefficient, with no cardinality or density assumption. -/
theorem legal_two_ends {width B K alpha beta : ℝ} (hw : 0 ≤ width)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (ha : 0 < alpha) (hb : 0 < beta) :
    B*((2*width+1)*choice width B K alpha beta)^alpha ≤ 1/16 := by
  have hk := choice_pos (alpha := alpha) (beta := beta) hw (by linarith : 0 < B) (by linarith : 0 < K)
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (2*width+1)*choice width B K alpha beta)
    (physical_radius_le hw (by linarith) hK hb) ha.le
  have hm := mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ B)
  have hf := concentrationRadius_factor (by linarith : 0 < 8*B) ha
  nlinarith

/-- The marked angular half-cap condition uses the same kappa. -/
theorem broad_half_cap {width B K alpha beta : ℝ} (hw : 0 ≤ width)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (ha : 0 < alpha) (hb : 0 < beta) :
    K*(2*choice width B K alpha beta)^beta ≤ 1/2 := by
  have hk := choice_pos (alpha := alpha) (beta := beta) hw (by linarith : 0 < B) (by linarith : 0 < K)
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 2*choice width B K alpha beta)
    (angular_radius_le hw hB (by linarith) ha) hb.le
  exact (mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ K)).trans_eq
    (concentrationRadius_factor (by linarith : 0 < K) hb)

/-- All required geometric and concentration properties belong to the same
explicit choice, so callers need no further existential radius selection. -/
theorem admissible {width B K alpha beta : ℝ} (hw : 0 ≤ width)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (ha : 0 < alpha) (hb : 0 < beta) :
    0 < choice width B K alpha beta ∧ choice width B K alpha beta ≤ 1/100 ∧
      (2*width+1)*choice width B K alpha beta ≤ 1 ∧
      B*((2*width+1)*choice width B K alpha beta)^alpha ≤ 1/16 ∧
      K*(2*choice width B K alpha beta)^beta ≤ 1/2 :=
  ⟨choice_pos hw (by linarith) (by linarith),choice_le_hundredth hw hB hK ha hb,
    physical_radius_le_one hw hB hK ha hb,legal_two_ends hw hB hK ha hb,broad_half_cap hw hB hK ha hb⟩

/-- The exact physical two-ends coefficient and radius scale inversely under
the common homothety, preserving the legal1/16 bound. -/
theorem normalized_legal_two_ends {width B K alpha beta R : ℝ} (hw : 0 ≤ width)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (ha : 0 < alpha) (hb : 0 < beta) (hR : 0 < R) :
    (B*R^alpha)*((2*width+1)*(choice width B K alpha beta/R))^alpha ≤ 1/16 := by
  have hk := choice_pos (alpha := alpha) (beta := beta) hw (by linarith : 0 < B) (by linarith : 0 < K)
  have hid : (B*R^alpha)*((2*width+1)*(choice width B K alpha beta/R))^alpha =
      B*((2*width+1)*choice width B K alpha beta)^alpha := by
    rw [mul_assoc,← Real.mul_rpow hR.le (by positivity : 0 ≤ (2*width+1)*(choice width B K alpha beta/R))]
    congr 2
    field_simp
  rw [hid]
  exact legal_two_ends hw hB hK ha hb

/-- Polynomial logarithmic budgets for both original coefficients give an
explicit lower bound with fixed prefactor and no shading-density dependence. -/
theorem choice_log_lower {width B K B₀ K₀ alpha beta L b q : ℝ}
    (hw : 0 ≤ width) (hB : 0 < B) (hK : 0 < K) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 < beta) (hL : 0 < L)
    (hBB : B ≤ B₀*L^b) (hKK : K ≤ K₀*L^q) :
    choice width B₀ K₀ alpha beta*L^(-loss alpha beta b q) ≤ choice width B K alpha beta := by
  have hBB' : 8*B ≤ (8*B₀)*L^b :=
    (mul_le_mul_of_nonneg_left hBB (by norm_num : (0:ℝ) ≤ 8)).trans_eq (by ring)
  have hr₁ := radius_log_lower (by positivity : 0 < 8*B) (by positivity : 0 < 8*B₀) ha hL hBB'
  have hr₂ := radius_log_lower hK hK₀ hb hL hKK
  have hR₁ := concentrationRadius_pos (alpha := alpha) (by positivity : 0 < 8*B)
  have hR₂₀ := concentrationRadius_pos (alpha := beta) hK₀
  have hm := mul_le_mul hr₁ hr₂ (by positivity) hR₁.le
  have hid : (concentrationRadius (8*B₀) alpha*L^(-b/alpha))*
      (concentrationRadius K₀ beta*L^(-q/beta)) =
      (concentrationRadius (8*B₀) alpha*concentrationRadius K₀ beta)*L^(-loss alpha beta b q) := by
    rw [show (concentrationRadius (8*B₀) alpha*L^(-b/alpha))*(concentrationRadius K₀ beta*L^(-q/beta)) =
      (concentrationRadius (8*B₀) alpha*concentrationRadius K₀ beta)*(L^(-b/alpha)*L^(-q/beta)) by ring,
      ← Real.rpow_add hL]
    unfold loss
    congr 2
    ring
  rw [hid] at hm
  have hh := div_le_div_of_nonneg_right hm (by positivity : 0 ≤ 100*(2*width+1))
  unfold choice
  exact (by ring : (concentrationRadius (8*B₀) alpha*concentrationRadius K₀ beta/(100*(2*width+1)))*
      L^(-loss alpha beta b q) =
      (concentrationRadius (8*B₀) alpha*concentrationRadius K₀ beta)*L^(-loss alpha beta b q)/(100*(2*width+1))).trans_le hh

theorem loss_nonneg {alpha beta b q : ℝ} (ha : 0 < alpha) (hb : 0 < beta)
    (hb₀ : 0 ≤ b) (hq : 0 ≤ q) : 0 ≤ loss alpha beta b q := by
  unfold loss
  positivity

/-- The common legal-sample homothety preserves the same logarithmic exponent;
only its fixed geometric scale enters the positive prefactor. -/
theorem normalized_choice_log_lower {width B K B₀ K₀ alpha beta L b q R : ℝ}
    (hw : 0 ≤ width) (hB : 0 < B) (hK : 0 < K) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 < beta) (hL : 0 < L) (hR : 0 < R)
    (hBB : B ≤ B₀*L^b) (hKK : K ≤ K₀*L^q) :
    (choice width B₀ K₀ alpha beta/R)*L^(-loss alpha beta b q) ≤ choice width B K alpha beta/R := by
  have hh := div_le_div_of_nonneg_right (choice_log_lower hw hB hK hB₀ hK₀ ha hb hL hBB hKK) hR.le
  exact (by ring : (choice width B₀ K₀ alpha beta/R)*L^(-loss alpha beta b q) =
    choice width B₀ K₀ alpha beta*L^(-loss alpha beta b q)/R).trans_le hh

/-- A transparent scalar scale test implies delta≤kappa. The scale test is
kept explicit; the theorem does not silently assume N exceeds a cutoff. -/
theorem scale_admissible {width B K B₀ K₀ alpha beta L b q δ : ℝ}
    (hw : 0 ≤ width) (hB : 0 < B) (hK : 0 < K) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 < beta) (hL : 0 < L)
    (hBB : B ≤ B₀*L^b) (hKK : K ≤ K₀*L^q)
    (hscale : δ ≤ choice width B₀ K₀ alpha beta*L^(-loss alpha beta b q)) :
    δ ≤ choice width B K alpha beta :=
  hscale.trans (choice_log_lower hw hB hK hB₀ hK₀ ha hb hL hBB hKK)

end
end KakeyaFormal.PivotKappa

#print axioms KakeyaFormal.PivotKappa.legal_two_ends
#print axioms KakeyaFormal.PivotKappa.broad_half_cap
#print axioms KakeyaFormal.PivotKappa.choice_log_lower
