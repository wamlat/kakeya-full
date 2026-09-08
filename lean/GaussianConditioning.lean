import GaussianPerpendicular

/-! Uniform perpendicular small balls with the first Gaussian vector varying.
The actual product law and Fubini give a section estimate over every measurable
first-vector event. No conditional Gaussian law or collision bound is assumed. -/
namespace KakeyaFormal.GaussianConditioning
open MeasureTheory ProbabilityTheory EuclideanSplit GaussianMatrix
open scoped ENNReal RealInnerProductSpace
noncomputable section

/-- A Borel unit direction at every vector, with a harmless fixed value at zero. -/
def unitDirection {n : ℕ} (x : Space (n+1)) : Space (n+1) :=
  if x=0 then axisUnit n else ‖x‖⁻¹ • x

theorem unitDirection_norm {n : ℕ} (x : Space (n+1)) : ‖unitDirection x‖=1 := by
  by_cases hx : x=0
  · simp [unitDirection,hx]
  · simp only [unitDirection,if_neg hx,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

theorem unitDirection_measurable (n : ℕ) : Measurable (unitDirection (n := n)) := by
  unfold unitDirection
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_id.norm.inv.smul measurable_id)

/-- The actual orthogonal remainder perpendicular to the first vector when it
is nonzero. At zero the same formula uses the fixed unit direction above. -/
def perpendicular {n : ℕ} (x y : Space (n+1)) : Space (n+1) :=
  y-⟪unitDirection x,y⟫ • unitDirection x

theorem perpendicular_eq {n : ℕ} (x y : Space (n+1)) (hx : x≠0) :
    perpendicular x y=y-⟪‖x‖⁻¹ • x,y⟫ • (‖x‖⁻¹ • x) := by
  simp [perpendicular,unitDirection,hx]

theorem perpendicular_measurable (n : ℕ) :
    Measurable (fun p : Space (n+1) × Space (n+1) => perpendicular p.1 p.2) := by
  unfold perpendicular
  exact measurable_snd.sub (((unitDirection_measurable n).comp measurable_fst).inner (𝕜 := ℝ)
    measurable_snd |>.smul ((unitDirection_measurable n).comp measurable_fst))

theorem section_bound (x : Space 5) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space 5) {y | ‖perpendicular x y‖ ≤ r} ≤
      min 1 (ENNReal.ofReal (16*r^4)) :=
  GaussianPerpendicular.orthogonal_component_small_ball (unitDirection x)
    (unitDirection_norm x) hr

/-- Actual Fubini estimate over every measurable first-vector event. This is
the precise probabilistic content of fixing the first projected vector. -/
theorem product_section_bound (B : Set (Space 5)) (hB : MeasurableSet B)
    {r : ℝ} (hr : 0 ≤ r) :
    ((stdGaussian (Space 5)).prod (stdGaussian (Space 5)))
      {p | p.1∈B ∧ ‖perpendicular p.1 p.2‖ ≤ r} ≤
      stdGaussian (Space 5) B * min 1 (ENNReal.ofReal (16*r^4)) := by
  have hs : MeasurableSet {p : Space 5 × Space 5 | p.1∈B ∧
      ‖perpendicular p.1 p.2‖ ≤ r} :=
    (hB.preimage measurable_fst).inter
      (measurableSet_le (perpendicular_measurable 4).norm measurable_const)
  rw [Measure.prod_apply hs]
  calc
    _ ≤ ∫⁻ x, B.indicator (fun _ => min 1 (ENNReal.ofReal (16*r^4))) x
        ∂stdGaussian (Space 5) := by
      apply lintegral_mono
      intro x
      by_cases hx : x∈B
      · simpa [hx] using section_bound x hr
      · simp [hx]
    _ = _ := by rw [lintegral_indicator hB,setLIntegral_const,mul_comm]

/-- The estimate for the ACTUAL images of two orthogonal unit input vectors
under the original standard Gaussian five-by-seven matrix. -/
theorem matrix_section_bound (v w : Space 7) (hv : ‖v‖=1) (hw : ‖w‖=1)
    (horth : ⟪v,w⟫=0) (B : Set (Space 5)) (hB : MeasurableSet B)
    {r : ℝ} (hr : 0 ≤ r) :
    law 5 7 {ω | projection v ω∈B ∧
      ‖perpendicular (projection v ω) (projection w ω)‖ ≤ r} ≤
      stdGaussian (Space 5) B * min 1 (ENNReal.ofReal (16*r^4)) := by
  have hs : MeasurableSet {p : Space 5 × Space 5 | p.1∈B ∧
      ‖perpendicular p.1 p.2‖ ≤ r} :=
    (hB.preimage measurable_fst).inter
      (measurableSet_le (perpendicular_measurable 4).norm measurable_const)
  have hh := product_section_bound B hB hr
  rw [← orthogonal_joint_law v w hv hw horth,
    Measure.map_apply (by fun_prop) hs] at hh
  exact hh

/-- Uniform small-ball probability without restricting the first image. -/
theorem matrix_small_ball (v w : Space 7) (hv : ‖v‖=1) (hw : ‖w‖=1)
    (horth : ⟪v,w⟫=0) {r : ℝ} (hr : 0 ≤ r) :
    law 5 7 {ω | ‖perpendicular (projection v ω) (projection w ω)‖ ≤ r} ≤
      min 1 (ENNReal.ofReal (16*r^4)) := by
  simpa using matrix_section_bound v w hv hw horth Set.univ MeasurableSet.univ hr

end
end KakeyaFormal.GaussianConditioning
