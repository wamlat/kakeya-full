import TwoEndsPivot
import TwoEndsGlobalization
import MaximalShading

/-! The actual six-dimensional diagonal estimate for unrestricted shadings.
Both pivot inputs are proved fractional seeds; the all-angle reduction and
actual geometric removal of two ends are proved. No published-result axiom
is needed. The measurable and tube-volume conversions are the existing
proved adapters. Bounded positions are explicitly distinguished below from
the separate literal position-unrestricted maximal predicate. -/
namespace KakeyaFormal.SixDimensionalUnrestricted
open MeasureTheory Finset
noncomputable section

/-- The actual unrestricted finite-grid estimate with D=p=33/8.
No full two ends, marked shading, broadness, sampling, or analytic input is
supplied. Its constant is uniform in every actual configuration parameter. -/
theorem discrete : DiscreteEstimate 6 5 (33/8) (33/8) := by
  have h := TwoEndsGlobalization.remove_two_ends (k:=5) TwoEndsPivot.six_dimensional
    (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- Arbitrary measurable shadings, obtained by the actual occupancy adapter. -/
theorem measurable : MeasurableEstimate 6 5 (33/8) (33/8) :=
  discrete.to_measurable (by norm_num) (by norm_num) le_rfl

/-- The exact sum of actual tube volumes, with exponent6−33/8=15/8. -/
theorem measurable_volume : VolumeMeasurableEstimate 6 5 (33/8) (33/8) :=
  measurable.volume_form

/-- The full ambient cap condition is automatically supplied by direction
separation. This theorem has no input cap coefficient or cap condition. -/
theorem bounded_maximal : MaximalShading.BoundedEstimate 6 (33/8) :=
  MaximalShading.bounded_maximal_of_volume (k:=5) measurable_volume

/-- The manuscript's first-step implication in the existing exact measurable
real-cap predicate. The conclusion is stronger: its base seed is already proved. -/
theorem measurable_first_step (_base : MeasurableEstimate 6 5 4 4) :
    MeasurableEstimate 6 5 (33/8) (33/8) := measurable

/-- The same first-step implication in the actual tube-volume predicate. -/
theorem volume_first_step (_base : VolumeMeasurableEstimate 6 5 4 4) :
    VolumeMeasurableEstimate 6 5 (33/8) (33/8) := measurable_volume

/-- The cap-free first-step implication under an explicit fixed bounded
position normalization; no base estimate is required by the proof. -/
theorem bounded_first_step (_base : MaximalShading.BoundedEstimate 6 4) :
    MaximalShading.BoundedEstimate 6 (33/8) := bounded_maximal

/-- Display the manuscript's precise power in the actual volume form.
All configuration data vary after the positive constant is chosen. -/
theorem volume_lower (geom : MeasurableNormalization) (eps : ℝ) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : MeasurableConfiguration 6 geom 5,
      c*F.A⁻¹*F.δ^((15:ℝ)/8+eps)*F.lam^((33:ℝ)/8)*
        (∑ i, (volume : Measure (Space 6)).real ((F.family.tube i).carrier F.δ)) ≤
          (volume : Measure (Space 6)).real F.unionSet := by
  have h := measurable_volume geom eps heps
  norm_num at h
  exact h

end
end KakeyaFormal.SixDimensionalUnrestricted
