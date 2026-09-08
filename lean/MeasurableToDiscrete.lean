import GridMarked
import MeasurableEstimate

/-! The converse measurable-to-discrete implication, using actual whole-cell
shadings and one common width-normalizing map. Together with the forward
conversion this gives equivalence of the concrete estimate predicates. -/
namespace KakeyaFormal.MeasurableToDiscrete
open MeasureTheory WidthNormalization GridShadingMeasure GridMarked TubeVolume
open scoped BigOperators
noncomputable section

/-- Width normalization does not enlarge bounded original tube bases. -/
theorem normalized_base_bound {k : ℕ} (T : UnitTube k) {W R : ℝ}
    (hW : 1 ≤ W) (hR : 0 ≤ R) (hbase : ‖T.base‖ ≤ R) :
    ‖(normalizedTube T W).base‖ ≤ R := by
  have hW0 : 0 < W := by linarith
  change ‖W⁻¹ • (T.axisPoint 0-0)‖ ≤ R
  simp only [UnitTube.axisPoint,zero_smul,add_zero,sub_zero,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hW0)]
  have hh := mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hW0.le)
  have hdiv : R/W ≤ R := div_le_self hR hW
  exact hh.trans (by simpa only [div_eq_mul_inv,mul_comm] using hdiv)

/-- A fixed normalization of the density parameter satisfies the actual
relative-to-tube-volume shading condition, uniformly over all grid data. -/
theorem realized_relative_density {k M : ℕ} (F : TubeFamily k M) {δ W C D lam : ℝ}
    (hδ : 0 < δ) (hW : 0 < W) (hD : 0 < D)
    (hlam : 0 ≤ lam) (hscale : C*W^k ≤ D)
    (hvol : ∀ i, (volume : Measure (Space k)).real ((normalizedTube (F.tube i) W).carrier δ) ≤ C*δ^k/δ)
    (hdense : ∀ i, lam/δ ≤ ((F.shade i).card:ℝ)) :
    ∀ i, (lam/D)*(volume : Measure (Space k)).real ((normalizedTube (F.tube i) W).carrier δ) ≤
      (volume : Measure (Space k)).real (shading F δ W i) := by
  intro i
  have hcoef : C/D ≤ 1/W^k := (div_le_div_iff₀ hD (pow_pos hW k)).mpr (by simpa only [one_mul] using hscale)
  have hfirst := mul_le_mul_of_nonneg_left (hvol i) (div_nonneg hlam hD.le)
  have hsecond := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ δ^k*(lam/δ))
  have hthird := mul_le_mul_of_nonneg_left (hdense i) (by positivity : 0 ≤ δ^k/W^k)
  have hsecond' : (lam/D)*(C*δ^k/δ) ≤ (δ^k/W^k)*(lam/δ) := by
    simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,one_mul,mul_one] using hsecond
  have hh := hfirst.trans (hsecond'.trans hthird)
  change _ ≤ (volume : Measure (Space k)).real (normalizedSet W (cellUnion δ (F.shade i)))
  rw [grid_mass _ hδ hW]
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

/-- Exact cancellation of the common physical cell volume; both sides arise
from the same spatial homothety, so no comparison of unrelated unions is used. -/
theorem conversion_identity {δ W D lam c A m d eps p N : ℝ} (k : ℕ)
    (hδ : 0 < δ) (hW : 0 < W) (hD : 0 < D) (hlam : 0 ≤ lam) :
    (δ^k/W^k)*((c*W^k/D^p)*A⁻¹*δ^(m-d+eps)*lam^p*N) =
      c*A⁻¹*δ^((k:ℝ)+m-d+eps)*(lam/D)^p*N := by
  rw [Real.div_rpow hlam hD.le]
  have hpow : δ^((k:ℝ)+m-d+eps) = δ^k*δ^(m-d+eps) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hδ]
    congr 1
    ring
  rw [hpow]
  have hWpow := (pow_pos hW k).ne'
  field_simp

end
end KakeyaFormal.MeasurableToDiscrete

namespace KakeyaFormal
open MeasureTheory WidthNormalization GridMarked TubeVolume MeasurableToDiscrete
noncomputable section

/-- The uniform concrete measurable estimate implies the uniform concrete grid
estimate in every integer ambient dimension, with fixed geometry-dependent loss. -/
theorem MeasurableEstimate.to_discrete {k : ℕ} {m d p : ℝ}
    (hbase : MeasurableEstimate k m d p) : DiscreteEstimate k m d p := by
  intro geom eps heps
  let W := widthFactor k geom.width
  let C := 3*(2:ℝ)^k*unitBallVolume k
  let D := max 1 (C*W^k)
  have hW1 : 1 ≤ W := widthFactor_ge_one _ _
  have hW : 0 < W := widthFactor_pos _ _
  have hD1 : 1 ≤ D := le_max_left _ _
  have hD : 0 < D := zero_lt_one.trans_le hD1
  let g : MeasurableNormalization := {
    separation := geom.separation
    radius := geom.radius
    separation_pos := geom.separation_pos
    radius_pos := geom.radius_pos
  }
  obtain ⟨c,hc,hestimate⟩ := hbase g eps heps
  refine ⟨c*W^k/D^p,by positivity,?_⟩
  intro F
  have hmass := realized_relative_density F.family F.scale_pos hW hD F.density_pos.le
    (le_max_right _ _) (fun i => carrier_volume_upper _ F.scale_pos F.scale_le_one)
    (fun i => (F.comparable i).1)
  let H : MeasurableConfiguration k g m := {
    M := F.M
    δ := F.δ
    lam := F.lam/D
    A := F.A
    family := GridMarked.family F.family W
    shading := GridMarked.shading F.family F.δ W
    scale_pos := F.scale_pos
    scale_le_one := F.scale_le_one
    density_pos := div_pos F.density_pos hD
    density_le_one := (div_le_one hD).mpr (F.density_le_one.trans hD1)
    cap_ge_one := F.cap_ge_one
    shading_measurable := shading_measurable F.family hW
    shading_subset := fun i => grid_carrier F.family F.scale_pos F.admissible i
    shading_mass := hmass
    separated := separated F.family W _ F.separated
    bounded := fun i => normalized_base_bound (F.family.tube i) hW1 geom.radius_pos.le (F.bounded i)
    cap_bound := cap_bound F.family W _ _ _ F.cap_bound
  }
  have hh := hestimate H
  change c*F.A⁻¹*F.δ^((k:ℝ)+m-d+eps)*(F.lam/D)^p*F.M ≤
    (volume : Measure (Space k)).real (⋃ i, normalizedSet W (GridShadingMeasure.cellUnion F.δ (F.family.shade i))) at hh
  rw [grid_union_mass F.family F.scale_pos hW] at hh
  have hfactor : 0 < F.δ^k/W^k := by positivity [F.scale_pos]
  apply (mul_le_mul_iff_left₀ hfactor).mp
  conv_lhs => rw [mul_comm]
  conv_rhs => rw [mul_comm]
  rw [conversion_identity k F.scale_pos hW hD F.density_pos.le]
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh

/-- Equivalence of the actual discrete and measurable formulations in the
range where the previously proved forward conversion applies. -/
theorem discrete_iff_measurable {k : ℕ} {m d p : ℝ} (hk : 0 < k) (hd : 1 ≤ d) (hp : d ≤ p) :
    DiscreteEstimate k m d p ↔ MeasurableEstimate k m d p :=
  ⟨fun h => h.to_measurable hk hd hp,fun h => h.to_discrete⟩

end
end KakeyaFormal
