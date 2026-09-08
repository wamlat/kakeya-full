import FamilyLocalization
import ScaleChoice
import MeasurableEstimate

/-! Actual common-radius and common-density localization for finite measurable
families. Both classes are selected, and their cardinality losses and logarithmic
depths are explicit. This module does not silently identify different spatial
localization centers with one common origin. -/
namespace KakeyaFormal.CommonDensityLocalization
open MeasureTheory Set Finset
open KakeyaFormal.Localization KakeyaFormal.OccupancySelection
open scoped BigOperators ENNReal
noncomputable section

variable {I X : Type*} [Fintype I] [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

structure Selection (μ : Measure X) (Y : I → Set X) (δ alpha base upper : ℝ) where
  radiusDepth : ℕ
  radiusIndex : Fin (radiusDepth+1)
  densityDepth : ℕ
  densityIndex : Fin (densityDepth+1)
  centers : I → X
  selected : Finset I
  selected_nonempty : selected.Nonempty
  radius_depth_bound : (radiusDepth:ℝ) ≤ Real.log (1/δ)/Real.log 2
  density_depth_bound : (densityDepth:ℝ)+1 ≤
    Real.log (upper / ((radius radiusDepth radiusIndex.val)^alpha*base))/Real.log 2+2
  radius_lower : δ ≤ radius radiusDepth radiusIndex.val
  radius_upper : radius radiusDepth radiusIndex.val ≤ 1
  count_lower : (Fintype.card I:ℝ)/((radiusDepth+1:ℕ)*(densityDepth+1:ℕ)) ≤ selected.card
  localized_measurable : ∀ i ∈ selected,
    MeasurableSet (Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val))
  original_mass_fraction : ∀ i ∈ selected,
    (radius radiusDepth radiusIndex.val)^alpha*μ.real (Y i) ≤
      μ.real (Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val))
  density_range : ∀ i ∈ selected,
    ((radius radiusDepth radiusIndex.val)^alpha*base)*(2:ℝ)^densityIndex.val ≤
      μ.real (Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val)) ∧
    μ.real (Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val)) <
      2*(((radius radiusDepth radiusIndex.val)^alpha*base)*(2:ℝ)^densityIndex.val)
  two_ends : ∀ i ∈ selected, ∀ y : X, ∀ r : ℝ, δ ≤ r → r ≤ radius radiusDepth radiusIndex.val →
    μ.real ((Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val)) ∩ Metric.closedBall y r) ≤
      (4:ℝ)^alpha*(r/(radius radiusDepth radiusIndex.val))^alpha*
        μ.real (Y i ∩ Metric.closedBall (centers i) (radius radiusDepth radiusIndex.val))

/-- Both common classes and the actual surviving family are constructed. The
second selection uses cardinality, preserving the intended two class-count loss. -/
theorem exists_selection (μ : Measure X) (Y : I → Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (hfinite : ∀ i, μ (Y i) ≠ ∞)
    {δ alpha base upper : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ alpha)
    (hbase : 0 < base) (hI : 0 < Fintype.card I)
    (hlower : ∀ i, base ≤ μ.real (Y i)) (hupper : ∀ i, μ.real (Y i) ≤ upper)
    (x₀ : I → X) (hcover : ∀ i, Y i ⊆ Metric.closedBall (x₀ i) 1) :
    Nonempty (Selection μ Y δ alpha base upper) := by
  classical
  obtain ⟨J,j,x,S,hj,hJ,hret,hδrho,hrho1,hlocal⟩ := FamilyLocalization.measurable_family_localization
    μ Y hY hfinite (fun _ => 1) hδ hδ1 ha x₀ hcover
  let rho := radius J j
  let Z := fun i => Y i ∩ Metric.closedBall (x i) rho
  let b := rho^alpha*base
  have hrho : 0 < rho := hδ.trans_le hδrho
  have hb : 0 < b := mul_pos (Real.rpow_pos_of_pos hrho alpha) hbase
  have hretS : (Fintype.card I:ℝ)/(J+1:ℕ) ≤ (S.card:ℝ) := by
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_one] using hret
  have hS : S.Nonempty := Finset.card_pos.mp (by
    have hh := (div_pos (by exact_mod_cast hI) (by positivity : (0:ℝ)<(J+1:ℕ))).trans_le hretS
    exact_mod_cast hh)
  have hlowerZ (i : I) (hi : i ∈ S) : b ≤ μ.real (Z i) :=
    (mul_le_mul_of_nonneg_left (hlower i) (Real.rpow_nonneg hrho.le alpha)).trans (hlocal i hi).2.1
  have hupperZ (i : I) : μ.real (Z i) ≤ upper :=
    (measureReal_mono Set.inter_subset_left (hfinite i)).trans (hupper i)
  obtain ⟨i₀,hi₀⟩ := hS
  obtain ⟨D,hD,hDlog⟩ := ScaleChoice.dyadic_class_budget hb ((hlowerZ i₀ hi₀).trans (hupperZ i₀))
  obtain ⟨ell,hell,R,hRS,hrange,hRmass⟩ := weighted_dyadic_selection S
    (fun i => μ.real (Z i)) (fun _ => 1) hb D hlowerZ
    (fun i _ => (hupperZ i).trans (by simpa only [mul_comm] using hD))
  have hretR : (S.card:ℝ)/(D+1:ℕ) ≤ (R.card:ℝ) := by
    simpa only [sum_const,nsmul_eq_mul,mul_one] using hRmass
  have htotal : (Fintype.card I:ℝ)/((J+1:ℕ)*(D+1:ℕ)) ≤ (R.card:ℝ) := by
    have hh := (div_le_div_of_nonneg_right hretS (by positivity : (0:ℝ)≤(D+1:ℕ))).trans hretR
    simpa only [div_div] using hh
  have hRne : R.Nonempty := Finset.card_pos.mp (by
    have hh := (div_pos (by exact_mod_cast hI) (by positivity : (0:ℝ)<(J+1:ℕ)*(D+1:ℕ))).trans_le htotal
    exact_mod_cast hh)
  exact ⟨{
    radiusDepth := J
    radiusIndex := ⟨j,by omega⟩
    densityDepth := D
    densityIndex := ⟨ell,by omega⟩
    centers := x
    selected := R
    selected_nonempty := hRne
    radius_depth_bound := hJ
    density_depth_bound := hDlog
    radius_lower := hδrho
    radius_upper := hrho1
    count_lower := htotal
    localized_measurable := fun i hi => (hlocal i (hRS hi)).1
    original_mass_fraction := fun i hi => (hlocal i (hRS hi)).2.1
    density_range := hrange
    two_ends := fun i hi => (hlocal i (hRS hi)).2.2
  }⟩

omit [BorelSpace X] in
/-- The common localized density is at least the radius-to-alpha fraction of
the original lower density. This follows from the constructed dyadic index. -/
theorem Selection.common_mass_lower {μ : Measure X} {Y : I → Set X} {δ alpha base upper : ℝ}
    (s : Selection μ Y δ alpha base upper) (hδ : 0 < δ) (hbase : 0 ≤ base) :
    (radius s.radiusDepth s.radiusIndex.val)^alpha*base ≤
      ((radius s.radiusDepth s.radiusIndex.val)^alpha*base)*(2:ℝ)^s.densityIndex.val := by
  have hpow : (1:ℝ) ≤ (2:ℝ)^s.densityIndex.val := one_le_pow₀ (by norm_num)
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (Real.rpow_nonneg (hδ.le.trans s.radius_lower) alpha) hbase)

omit [BorelSpace X] in
/-- The second class budget is logarithmic in the original mass ratio and the
mesh scale; no hidden dependence on the selected radius remains. -/
theorem Selection.density_depth_log_bound {μ : Measure X} {Y : I → Set X}
    {δ alpha base upper : ℝ} (s : Selection μ Y δ alpha base upper)
    (hδ : 0 < δ) (ha : 0 ≤ alpha) (hbase : 0 < base) (hupper : 0 < upper) :
    (s.densityDepth:ℝ)+1 ≤ Real.log (upper/base)/Real.log 2 +
      alpha*(Real.log (1/δ)/Real.log 2)+2 := by
  have hrho : 0 < radius s.radiusDepth s.radiusIndex.val := hδ.trans_le s.radius_lower
  have hlog := Real.log_le_log hδ s.radius_lower
  have hmult := mul_le_mul_of_nonneg_left hlog ha
  have hcompare : Real.log (upper/((radius s.radiusDepth s.radiusIndex.val)^alpha*base)) ≤
      Real.log (upper/base)+alpha*Real.log (1/δ) := by
    rw [Real.log_div hupper.ne' (mul_pos (Real.rpow_pos_of_pos hrho alpha) hbase).ne',
      Real.log_mul (Real.rpow_pos_of_pos hrho alpha).ne' hbase.ne',Real.log_rpow hrho,
      Real.log_div hupper.ne' hbase.ne',one_div,Real.log_inv]
    nlinarith
  have hh := div_le_div_of_nonneg_right hcompare (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  rw [add_div,mul_div_assoc] at hh
  exact s.density_depth_bound.trans (by linarith)

end
end KakeyaFormal.CommonDensityLocalization

-- Kernel dependency audit.
#print axioms KakeyaFormal.CommonDensityLocalization.exists_selection
#print axioms KakeyaFormal.CommonDensityLocalization.Selection.common_mass_lower
#print axioms KakeyaFormal.CommonDensityLocalization.Selection.density_depth_log_bound
