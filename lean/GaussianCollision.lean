import GaussianCollisionGeometry
import GaussianLinearOperator

/-! Actual truncated collision probability for a standard Gaussian 5×7 map.
The constant depends only on the fixed operator-norm cutoff. The Gaussian law,
the orthogonal input pair and the perpendicular small ball are all constructed
in the imported, standard-only modules. -/
namespace KakeyaFormal.GaussianCollision
open MeasureTheory ProbabilityTheory GaussianMatrix GaussianConditioning
open GaussianCollisionGeometry GaussianLinearOperator ProjectiveAngleComparison
open scoped ENNReal RealInnerProductSpace
noncomputable section

/-- Projected directions are compared only when the actual images are nonzero. -/
def collisionEvent (K δ : ℝ) (v w : Space 7) : Set (Sample 5 7) :=
  {ω | ‖operator ω‖ ≤ K ∧ projection v ω≠0 ∧ projection w ω≠0 ∧
    angle (unitDirection (projection v ω)) (unitDirection (projection w ω)) ≤ δ}

theorem collisionEvent_measurable (K δ : ℝ) (v w : Space 7) :
    MeasurableSet (collisionEvent K δ v w) := by
  have hp (z : Space 7) : Measurable (fun ω : Sample 5 7 => unitDirection (projection z ω)) :=
    (unitDirection_measurable 4).comp (projection z).measurable
  unfold collisionEvent angle
  exact (measurableSet_le (operator_measurable 5 7).norm measurable_const).inter
    (((projection v).measurable (measurableSet_singleton 0)).compl.inter
      (((projection w).measurable (measurableSet_singleton 0)).compl.inter
        (measurableSet_le (Real.continuous_arccos.measurable.comp
          ((hp v).inner (𝕜 := ℝ) (hp w)).abs) measurable_const)))

/-- The direct sine-denominator bound, with the literal codimension-four power. -/
theorem collision_probability_sine {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (v w : Space 7) (hv : ‖v‖=1) (hw : ‖w‖=1) (hangle : 0 < angle v w) :
    law 5 7 (collisionEvent K δ v w) ≤
      min 1 (ENNReal.ofReal (16*(K*δ/Real.sin (angle v w))^4)) := by
  obtain ⟨u,hu,huorth,hcontain⟩ := collision_containment (n := 4) v w hv hw hangle
  have hsub : collisionEvent K δ v w ⊆
      {ω | ‖perpendicular (projection v ω) (projection u ω)‖ ≤
        K*δ/Real.sin (angle v w)} := by
    intro ω hω
    change ‖perpendicular (projection v ω) (projection u ω)‖ ≤
      K*δ/Real.sin (angle v w)
    have hh := hcontain (operator ω) hδ hω.1
      (by simpa only [operator_apply] using hω.2.2.1)
      (by simpa only [operator_apply] using hω.2.2.2)
    simpa only [operator_apply] using hh
  exact (measure_mono hsub).trans (matrix_small_ball v u hv hu huorth
    (div_nonneg (mul_nonneg hK hδ) (sin_angle_nonneg v w)))

def collisionConstant (K : ℝ) : ℝ := max 1 (16*(Real.pi*K/2)^4)

theorem collisionConstant_ge_one (K : ℝ) : 1 ≤ collisionConstant K := le_max_left _ _

theorem collisionConstant_pos (K : ℝ) : 0 < collisionConstant K :=
  lt_of_lt_of_le zero_lt_one (collisionConstant_ge_one K)

theorem sine_radius_le {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (v w : Space 7) (hangle : 0 < angle v w) :
    K*δ/Real.sin (angle v w) ≤ (Real.pi*K/2)*(δ/angle v w) := by
  have hh := div_le_div_of_nonneg_left (mul_nonneg hK hδ)
    (mul_pos (div_pos (by norm_num : (0:ℝ)<2) Real.pi_pos) hangle)
    (sine_angle_bounds v w).1
  calc
    _ ≤ K*δ/((2/Real.pi)*angle v w) := hh
    _ = _ := by field_simp

/-- Source (2.3), for the actual original Gaussian matrix and actual projected
unoriented angular collision. C_K is chosen before all input directions and
collision radii. No surviving-family, collision, or projection-law premise is
used. The nonzero-output tests merely make projected directions well defined. -/
theorem collision_probability {K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ)
    (v w : Space 7) (hv : ‖v‖=1) (hw : ‖w‖=1) (hangle : 0 < angle v w) :
    law 5 7 (collisionEvent K δ v w) ≤
      ENNReal.ofReal (collisionConstant K) *
        min 1 (ENNReal.ofReal ((δ/angle v w)^4)) := by
  have hr0 : 0 ≤ K*δ/Real.sin (angle v w) :=
    div_nonneg (mul_nonneg hK hδ) (sin_angle_nonneg v w)
  have ht0 : 0 ≤ δ/angle v w := div_nonneg hδ hangle.le
  have hpow : 16*(K*δ/Real.sin (angle v w))^4 ≤
      collisionConstant K*(δ/angle v w)^4 := by
    calc
      _ ≤ 16*((Real.pi*K/2)*(δ/angle v w))^4 := by
        gcongr
        exact sine_radius_le hK hδ v w hangle
      _ = (16*(Real.pi*K/2)^4)*(δ/angle v w)^4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg ht0 _)
  have hp := collision_probability_sine hK hδ v w hv hw hangle
  rw [mul_min,mul_one]
  refine le_min ?_ ?_
  · exact (hp.trans (min_le_left _ _)).trans
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal (collisionConstant_ge_one K)))
  · apply (hp.trans (min_le_right _ _)).trans
    rw [← ENNReal.ofReal_mul (collisionConstant_pos K).le]
    exact ENNReal.ofReal_le_ofReal hpow

end
end KakeyaFormal.GaussianCollision
