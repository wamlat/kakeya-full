import MarkedSubsetSamples

/-! A minimum-based legal pivot scale, distinct from the frozen product choice.
It is maximal for the three explicit scalar tests, and a literal manuscript-form
c*min(theta,1/100,(c/B)^(1/alpha)) satisfies the tests after doubling B. -/
namespace KakeyaFormal.MinPivotKappa
open HairbrushScales
noncomputable section

/-- Largest radius satisfying the fixed cap, angular, and physical exclusion
radius constraints simultaneously. B is the actual post-recovery coefficient. -/
def optimal (width B alpha theta : ℝ) : ℝ :=
  min (1/100) (min (theta/2) (concentrationRadius (8*B) alpha/(2*width+1)))

theorem optimal_pos {width B alpha theta : ℝ}
    (hw : 0 ≤ width) (hB : 0 < B) (htheta : 0 < theta) :
    0 < optimal width B alpha theta := by
  have hr := concentrationRadius_pos (alpha := alpha) (by positivity : 0 < 8*B)
  unfold optimal
  positivity

theorem optimal_constraints {width B alpha theta : ℝ} (hw : 0 ≤ width) :
    optimal width B alpha theta ≤ 1/100 ∧
    2*optimal width B alpha theta ≤ theta ∧
    (2*width+1)*optimal width B alpha theta ≤ concentrationRadius (8*B) alpha := by
  have hsmall := min_le_left (1/100:ℝ) (min (theta/2) (concentrationRadius (8*B) alpha/(2*width+1)))
  have hsecond := min_le_right (1/100:ℝ) (min (theta/2) (concentrationRadius (8*B) alpha/(2*width+1)))
  have hang := hsecond.trans (min_le_left _ _)
  have hphys := hsecond.trans (min_le_right _ _)
  refine ⟨hsmall,by change optimal width B alpha theta ≤ theta/2 at hang; linarith,?_⟩
  change optimal width B alpha theta ≤ concentrationRadius (8*B) alpha/(2*width+1) at hphys
  exact (by simpa only [mul_comm] using (le_div_iff₀ (by linarith : 0 < 2*width+1)).mp hphys)

theorem physical_factor {B alpha : ℝ} (hB : 0 < B) (ha : 0 < alpha) :
    B*(concentrationRadius (8*B) alpha)^alpha = 1/16 := by
  have hh := concentrationRadius_factor (by positivity : 0 < 8*B) ha
  nlinarith

/-- The power test is exactly equivalent to the explicit concentration-radius
constraint, so maximality does not assume its own desired conclusion. -/
theorem physical_test_iff {B alpha x : ℝ} (hB : 0 < B) (ha : 0 < alpha) (hx : 0 ≤ x) :
    B*x^alpha ≤ 1/16 ↔ x ≤ concentrationRadius (8*B) alpha := by
  have hr := concentrationRadius_pos (alpha := alpha) (by positivity : 0 < 8*B)
  have hf := physical_factor hB ha
  constructor
  · intro hh
    apply (Real.rpow_le_rpow_iff hx hr.le ha).mp
    nlinarith
  · intro hh
    have hp := Real.rpow_le_rpow hx hh ha.le
    nlinarith

/-- Maximality among all nonnegative radii meeting the three actual scalar
requirements; no asymptotic comparison is substituted. -/
theorem maximal {width B alpha theta kappa : ℝ}
    (hw : 0 ≤ width) (hB : 0 < B) (ha : 0 < alpha) (hk : 0 ≤ kappa)
    (hsmall : kappa ≤ 1/100) (hang : 2*kappa ≤ theta)
    (hlegal : B*((2*width+1)*kappa)^alpha ≤ 1/16) :
    kappa ≤ optimal width B alpha theta := by
  have hphys := (physical_test_iff hB ha (by positivity : 0 ≤ (2*width+1)*kappa)).mp hlegal
  apply le_min hsmall
  apply le_min (by linarith)
  exact (le_div_iff₀ (by linarith : 0 < 2*width+1)).mpr (by simpa only [mul_comm] using hphys)

theorem optimal_admissible {width B alpha theta : ℝ}
    (hw : 0 ≤ width) (hB : 1 ≤ B) (ha : 0 < alpha) (htheta : 0 < theta) :
    0 < optimal width B alpha theta ∧ optimal width B alpha theta ≤ 1/100 ∧
      2*optimal width B alpha theta ≤ theta ∧
      (2*width+1)*optimal width B alpha theta ≤ 1 ∧
      B*((2*width+1)*optimal width B alpha theta)^alpha ≤ 1/16 := by
  have hk := optimal_pos (alpha := alpha) hw (by linarith : 0 < B) htheta
  obtain ⟨hsmall,hang,hphys⟩ := optimal_constraints (B := B) (alpha := alpha) (theta := theta) hw
  refine ⟨hk,hsmall,hang,hphys.trans (concentrationRadius_le_one (by linarith : 1/2 ≤ 8*B) ha),?_⟩
  exact (physical_test_iff (by linarith : 0 < B) ha (by positivity)).mpr hphys

/-- Every scale cutoff proved using the frozen product choice is also a valid
cutoff for this larger minimum choice, at the same fixed-radius hypotheses. -/
theorem product_le_optimal {width B alpha theta : ℝ}
    (hw : 0 ≤ width) (hB : 1 ≤ B) (ha : 0 < alpha)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) :
    PivotKappa.choice width B theta⁻¹ alpha 1 ≤ optimal width B alpha theta := by
  obtain ⟨hk,hsmall,hang,_,hlegal⟩ := MarkedSubsetSamples.fixed_radius_choice hw hB ha htheta htheta1
  exact maximal hw (by linarith) ha hk.le hsmall hang hlegal

/-- Fixed geometric constant, used both outside and inside the literal
manuscript minimum. -/
def sourceConstant (width : ℝ) : ℝ := 1/(100*(2*width+1))

def sourceChoice (width B alpha theta : ℝ) : ℝ :=
  sourceConstant width * min theta (min (1/100) ((sourceConstant width/B)^(1/alpha)))

theorem sourceConstant_bounds {width : ℝ} (hw : 0 ≤ width) :
    0 < sourceConstant width ∧ sourceConstant width ≤ 1/100 ∧
      (2*width+1)*sourceConstant width = 1/100 := by
  have hD : 0 < 2*width+1 := by linarith
  refine ⟨by unfold sourceConstant; positivity,?_,?_⟩
  · unfold sourceConstant
    apply (div_le_iff₀ (by positivity : 0 < 100*(2*width+1))).mpr
    nlinarith
  · unfold sourceConstant
    field_simp

theorem sourceChoice_pos {width B alpha theta : ℝ}
    (hw : 0 ≤ width) (hB : 0 < B) (htheta : 0 < theta) :
    0 < sourceChoice width B alpha theta := by
  have hc := (sourceConstant_bounds hw).1
  unfold sourceChoice
  positivity

/-- The minimum's two geometric constraints need no all-radius angular
broadness assumption; a single marked-cap radius theta suffices. -/
theorem source_geometric_constraints {width B alpha theta : ℝ}
    (hw : 0 ≤ width) (htheta : 0 < theta) :
    sourceChoice width B alpha theta ≤ 1/100 ∧
      2*sourceChoice width B alpha theta ≤ theta := by
  obtain ⟨hc,hc1,_⟩ := sourceConstant_bounds hw
  have hs : min theta (min (1/100:ℝ) ((sourceConstant width/B)^(1/alpha))) ≤ 1/100 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have ht := min_le_left theta (min (1/100:ℝ) ((sourceConstant width/B)^(1/alpha)))
  have hs' := mul_le_mul_of_nonneg_left hs hc.le
  have ht' := mul_le_mul_of_nonneg_left ht hc.le
  change sourceChoice width B alpha theta ≤ sourceConstant width*(1/100) at hs'
  change sourceChoice width B alpha theta ≤ sourceConstant width*theta at ht'
  constructor <;> nlinarith

/-- The literal minimum choice allows the factor-two two-ends deterioration
explicitly used after original pruning in the manuscript. -/
theorem source_legal_two_ends {width B alpha theta : ℝ}
    (hw : 0 ≤ width) (hB : 0 < B) (ha : 0 < alpha) (htheta : 0 < theta) :
    (2*B)*((2*width+1)*sourceChoice width B alpha theta)^alpha ≤ 1/16 := by
  obtain ⟨hc,hc1,hcD⟩ := sourceConstant_bounds hw
  let r := (sourceConstant width/B)^(1/alpha)
  have hr : 0 < r := by dsimp [r]; positivity
  have hk := sourceChoice_pos (alpha := alpha) hw hB htheta
  have hraw : sourceChoice width B alpha theta ≤ sourceConstant width*r :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) hc.le
  have hphys : (2*width+1)*sourceChoice width B alpha theta ≤ r := by
    have hh := mul_le_mul_of_nonneg_left hraw (by linarith : 0 ≤ 2*width+1)
    rw [← mul_assoc,hcD] at hh
    linarith
  have hpower : r^alpha = sourceConstant width/B := by
    dsimp [r]
    rw [← Real.rpow_mul (div_nonneg hc.le hB.le),div_mul_cancel₀ 1 ha.ne',Real.rpow_one]
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ (2*width+1)*sourceChoice width B alpha theta)
    hphys ha.le
  rw [hpower] at hp
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2*B)
  have he : (2*B)*(sourceConstant width/B) = 2*sourceConstant width := by field_simp
  rw [he] at hm
  linarith

/-- A literal manuscript-form minimum is below the maximal admissible minimum
for the actual doubled coefficient, with no B- or theta-dependent comparison loss. -/
theorem source_le_optimal {width B alpha theta : ℝ}
    (hw : 0 ≤ width) (hB : 0 < B) (ha : 0 < alpha) (htheta : 0 < theta) :
    sourceChoice width B alpha theta ≤ optimal width (2*B) alpha theta := by
  obtain ⟨hsmall,hang⟩ := source_geometric_constraints (B := B) (alpha := alpha) hw htheta
  exact maximal hw (by positivity) ha (sourceChoice_pos hw hB htheta).le hsmall hang
    (source_legal_two_ends hw hB ha htheta)

/-- The exact source-form scale satisfies all geometric and exclusion tests
with the actual doubled two-ends coefficient. -/
theorem source_admissible {width B alpha theta : ℝ}
    (hw : 0 ≤ width) (hB : 1 ≤ B) (ha : 0 < alpha) (htheta : 0 < theta) :
    0 < sourceChoice width B alpha theta ∧ sourceChoice width B alpha theta ≤ 1/100 ∧
      2*sourceChoice width B alpha theta ≤ theta ∧
      (2*width+1)*sourceChoice width B alpha theta ≤ 1 ∧
      (2*B)*((2*width+1)*sourceChoice width B alpha theta)^alpha ≤ 1/16 := by
  obtain ⟨hsmall,hang⟩ := source_geometric_constraints (B := B) (alpha := alpha) hw htheta
  have hopt := optimal_admissible hw (by linarith : 1 ≤ 2*B) ha htheta
  have hle := source_le_optimal hw (by linarith : 0 < B) ha htheta
  exact ⟨sourceChoice_pos hw (by linarith) htheta,hsmall,hang,
    (mul_le_mul_of_nonneg_left hle (by linarith : 0 ≤ 2*width+1)).trans hopt.2.2.2.1,
    source_legal_two_ends hw (by linarith) ha htheta⟩

/-- Existing product-scale logarithmic lower bounds also hold for the maximal
admissible minimum; this does not identify the two parameter dependencies. -/
theorem optimal_log_lower {width B B₀ K₀ alpha theta L b q : ℝ}
    (hw : 0 ≤ width) (hB : 1 ≤ B) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (htheta : 0 < theta) (htheta1 : theta ≤ 1) (hL : 0 < L)
    (hBB : B ≤ B₀*L^b) (hKK : theta⁻¹ ≤ K₀*L^q) :
    PivotKappa.choice width B₀ K₀ alpha 1*L^(-PivotKappa.loss alpha 1 b q) ≤
      optimal width B alpha theta :=
  (PivotKappa.choice_log_lower hw (by linarith) (by positivity) hB₀ hK₀ ha
    (by norm_num) hL hBB hKK).trans (product_le_optimal hw hB ha htheta htheta1)

/-- An explicit admissible one-parameter family exposes the different orders
of the two choices. Here B is original and the product uses the actual 2B. -/
theorem product_example {t : ℝ} (ht : 0 < t) :
    PivotKappa.choice (1/2) (2*t) t 1 1 = 1/(12800*t^2) := by
  norm_num [PivotKappa.choice, concentrationRadius, Real.rpow_neg_one]
  field_simp
  ring

theorem source_example {t : ℝ} (ht : 1 ≤ t) :
    sourceChoice (1/2) t 1 (1/t) = 1/(40000*t) := by
  have ht0 : 0 < t := by linarith
  have hsmall : (1/200:ℝ)/t ≤ 1/100 := (div_le_iff₀ ht0).mpr (by linarith)
  have htheta : (1/200:ℝ)/t ≤ 1/t := div_le_div_of_nonneg_right (by norm_num) ht0.le
  have hc : sourceConstant (1/2) = 1/200 := by norm_num [sourceConstant]
  unfold sourceChoice
  rw [hc]
  norm_num only [div_one,Real.rpow_one]
  rw [min_eq_right hsmall,min_eq_right htheta]
  field_simp
  ring

/-- There is no positive constant, uniform in B and theta, that bounds the
frozen product choice below by the literal source minimum. -/
theorem no_uniform_product_lower :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t →
      c*sourceChoice (1/2) t 1 (1/t) ≤ PivotKappa.choice (1/2) (2*t) t 1 1 := by
  rintro ⟨c,hc,hall⟩
  let t : ℝ := 1+4/c
  have ht : 1 ≤ t := by
    have hp : 0 ≤ 4/c := by positivity
    dsimp [t]
    linarith
  have ht0 : 0 < t := by linarith
  have hct : c*t = c+4 := by dsimp [t]; field_simp
  have hh := hall t ht
  rw [product_example ht0,source_example ht] at hh
  have hmul := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ 12800*t^2)
  have hleft : c*(1/(40000*t))*(12800*t^2) = (8/25:ℝ)*(c*t) := by
    field_simp
    ring
  have hright : (1/(12800*t^2))*(12800*t^2) = 1 := by field_simp
  rw [hleft,hright,hct] at hmul
  linarith

end
end KakeyaFormal.MinPivotKappa
