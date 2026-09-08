import IndicatorWitnessCover
import SphereCapMeasure
import MainMaximal

/-! The actual restricted weak estimate derived from the proved maximal
shading assertion. Finite direction witnesses and sphere-cap measure are
constructed, not supplied as premises. -/
namespace KakeyaFormal.IndicatorRestrictedWeak
open MeasureTheory Finset KakeyaOperator
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 800000

def tubeLowerConstant (n : ℕ) : ℝ :=
  TubeVolume.unitBallVolume n / (2:ℝ)^(n+1)

theorem tubeLowerConstant_pos (n : ℕ) : 0 < tubeLowerConstant n := by
  have h := TubeVolume.unitBallVolume_pos n
  unfold tubeLowerConstant
  positivity

/-- The real finite-input version, with its uniform constant chosen before
the scale, level, test set, and actual supremum witnesses. -/
theorem real_bound {n : ℕ} {a : ℝ} (hn : 0 < n)
    (h : MaximalShading.Estimate n a) {eps : ℝ} (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ {δ lam : ℝ}, 0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 →
      ∀ E : Set (Space n), MeasurableSet E → (volume : Measure (Space n)) E ≠ ∞ →
        (sphereMeasure n).real (indicatorLevel δ E lam) ≤
          C*δ^(-((n:ℝ)-a+eps))*lam^(-a)*(volume : Measure (Space n)).real E := by
  obtain ⟨c,hc,hestimate⟩ := h (1/2) (by norm_num) eps heps
  let L := tubeLowerConstant n
  let B := SphereCapMeasure.capConstant n
  have hL : 0 < L := tubeLowerConstant_pos n
  have hB : 0 < B := SphereCapMeasure.capConstant_pos hn
  refine ⟨B/(c*L),by positivity,?_⟩
  intro δ lam hδ hδ1 hlam hlam1 E hE hEfinite
  obtain ⟨W⟩ := IndicatorWitnessCover.construct (lam:=lam) hδ E hE
  have hsep : W.family.Separated ((1/2)*δ) := by
    convert W.separated using 1; ring
  have hs := hestimate W.family W.shading hδ hδ1 hlam hlam1 W.shading_measurable
    W.shading_subset (fun i => (W.strict_mass i).le) hsep
  have hEbound := measureReal_mono W.union_subset hEfinite
  have htotal := hs.trans hEbound
  have htube (i : Fin W.M) : L*δ^((n:ℝ)-1) ≤
      (volume : Measure (Space n)).real ((W.family.tube i).carrier δ) := by
    have ht := TubeVolume.carrier_volume_lower (W.family.tube i) hδ
    simpa only [L,tubeLowerConstant,mul_div_assoc,SphereCapMeasure.scale_power hδ] using ht
  have hsum : L*(δ^((n:ℝ)-1)*(W.M:ℝ)) ≤
      ∑ i, (volume : Measure (Space n)).real ((W.family.tube i).carrier δ) := by
    have ht := sum_le_sum (s:=univ) (fun i _ => htube i)
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc,mul_comm,mul_left_comm] using ht
  have hcover := SphereCapMeasure.indexed_cover_upper W.direction (indicatorLevel δ E lam)
    hδ hδ1 (fun v hv => by
      obtain ⟨i,hi⟩ := W.covers v hv
      exact ⟨i,hi.le⟩)
  let z := c*δ^((n:ℝ)-a+eps)*lam^a
  have hz : 0 < z := by dsimp [z]; positivity
  have hprod : z*(L*(δ^((n:ℝ)-1)*(W.M:ℝ))) ≤
      (volume : Measure (Space n)).real E :=
    (mul_le_mul_of_nonneg_left hsum hz.le).trans htotal
  have hscaled := mul_le_mul_of_nonneg_left hcover (mul_pos hz hL).le
  have hprod' := mul_le_mul_of_nonneg_left hprod hB.le
  have hfinal : (sphereMeasure n).real (indicatorLevel δ E lam) ≤
      (B/(z*L))*(volume : Measure (Space n)).real E := by
    have hcross : (sphereMeasure n).real (indicatorLevel δ E lam)*(z*L) ≤
        B*(volume : Measure (Space n)).real E := by
      calc
        _ = (z*L)*(sphereMeasure n).real (indicatorLevel δ E lam) := mul_comm _ _
        _ ≤ (z*L)*(SphereCapMeasure.capConstant n*δ^((n:ℝ)-1)*(W.M:ℝ)) := hscaled
        _ = B*(z*(L*(δ^((n:ℝ)-1)*(W.M:ℝ)))) := by dsimp [B]; ring
        _ ≤ _ := hprod'
    have hh := (le_div_iff₀ (mul_pos hz hL)).mpr hcross
    simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  convert hfinal using 1
  dsimp only [z]
  rw [Real.rpow_neg hδ.le,Real.rpow_neg hlam.le]
  field_simp

end
end KakeyaFormal.IndicatorRestrictedWeak
