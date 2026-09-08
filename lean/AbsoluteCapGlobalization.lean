import AbsoluteCapEstimates
import TwoEndsGlobalization
import MeasurableEstimate

/-! The weaker absolute-cap input of Proposition8.1, including 0<C<1.
Only actual whole-tube thinning and the proved geometric two-ends removal are
used. The hypothesis is not silently strengthened to uniform inverse-cap control. -/
namespace KakeyaFormal
noncomputable section

/-- The existing C>=1 globalization also covers smaller density exponents:
first weaken the actual normalized density power to one. Since D>=1, this
leaves max(D,C) unchanged. No change to original shadings is involved. -/
theorem TwoEndsDiscreteEstimate.remove_two_ends_all_density {k : ℕ} {m D C : ℝ}
    (h : TwoEndsDiscreteEstimate (k+1) m D C) (hm : 0 ≤ m) (hD : 1 ≤ D) :
    DiscreteEstimate (k+1) m D (max D C) := by
  by_cases hC : 1 ≤ C
  · exact TwoEndsGlobalization.remove_two_ends h hm hD hC
  · have hC1 : C ≤ 1 := le_of_not_ge hC
    have hh := TwoEndsGlobalization.remove_two_ends (h.weaken_density hC1) hm hD (by norm_num)
    simpa only [max_eq_left hD,max_eq_left (hC1.trans hD)] using hh

/-- Literal absolute-cap hypothesis implies the full unrestricted linear
inverse-cap conclusion. This includes the entire source range 1<D<m,C>0;
the stated assumptions are slightly broader because the same proof allows it. -/
theorem AbsoluteTwoEndsDiscreteEstimate.globalize {k : ℕ} {m D C : ℝ}
    (h : AbsoluteTwoEndsDiscreteEstimate (k+1) m D C) (hm : 0 ≤ m) (hD : 1 ≤ D) :
    DiscreteEstimate (k+1) m D (max D C) :=
  (h.to_two_ends hm).remove_two_ends_all_density hm hD

/-- Actual measurable tube shadings, with original tube-volume normalization,
follow from the same weaker absolute-cap two-ends premise. -/
theorem AbsoluteTwoEndsDiscreteEstimate.globalize_measurable {k : ℕ} {m D C : ℝ}
    (h : AbsoluteTwoEndsDiscreteEstimate (k+1) m D C) (hm : 0 ≤ m) (hD : 1 ≤ D) :
    VolumeMeasurableEstimate (k+1) m D (max D C) :=
  (h.globalize hm hD).to_measurable_volume (by omega) hD (le_max_left _ _)

end
end KakeyaFormal
