import AngularSpatialSampling
import LocalAngularCoarse

/-! The coarse and bounded normalized-scale branches on the SAME actual old
spatial-box shadings. Their population estimate follows from original cap
geometry, and the union lower bound comes from an actual full shading. -/
namespace KakeyaFormal.AngularBoxCoarse
open Finset AngularSeedPieces AngularRestrictedRefinement AngularSpatialSampling
open WidthNormalization SpatialMarkedPartition
noncomputable section

variable {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
variable {P : Pieces F δ beta} {g : Fin M}

/-- Common width normalization decreases the dimensionless finite density. -/
theorem physical_density_le (V : Refinement P lam B alpha g) (width : ℝ) :
    physicalDensity V width ≤ V.density :=
  div_le_self V.density_pos.le (one_le_pow₀ (widthFactor_ge_one _ _))

/-- A density upper bound of TWO is what the actual refinement supplies. -/
theorem original_density_le_two (V : Refinement P lam B alpha g) (hlam : lam ≤ 1) :
    V.density ≤ 2 := by linarith [V.density_upper]

/-- Decreasing to the physical density weakens the actual box target. This
comparison introduces no geometric or counting assumption. -/
theorem density_target_le (V : Refinement P lam B alpha g) (width : ℝ)
    {c A deltaNew m D C eps : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hnew : 0 < deltaNew) (hC : 0 ≤ C) (q : Cell k) :
    c*A⁻¹*deltaNew^(m-D+eps)*(physicalDensity V width)^C*
      ((indices (SpatialGridPopulation.refinedLabel V width) q).card:ℝ) ≤
    c*A⁻¹*deltaNew^(m-D+eps)*V.density^C*
      ((indices (SpatialGridPopulation.refinedLabel V width) q).card:ℝ) := by
  have hh := Real.rpow_le_rpow (physicalDensity_pos V width).le (physical_density_le V width) hC
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hh (by positivity)) (Nat.cast_nonneg _)

/-- Section 7's coarse angular branch, with one constant before every actual
family, angular refinement, simultaneous Package and good spatial box. -/
theorem coarse {k : ℕ} {m D C eps : ℝ}
    (width R B alpha beta : ℝ) (hR : 0 ≤ R)
    (hm : 0 ≤ m) (hD : D < m+1) (hmn : m+1 ≤ ((k+1:ℕ):ℝ)+1)
    (hC : 1 ≤ C) (heps : 0 ≤ eps) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} {F : TubeFamily (k+2) M} {δ lam A : ℝ}
      (P : Pieces F δ beta) (g : Fin M) (V : Refinement P lam B alpha g)
      (_U : Package V width R m A) (q : ↥(boxes V width)),
      g ∈ P.groups → 0 < δ → lam ≤ 1 → 1 ≤ A →
      F.Separated δ → F.Bounded R → F.CapBound δ m A →
      δ^(1/(2*(((k+1:ℕ):ℝ)+1))) ≤ δ/P.tau →
      c*A⁻¹*(δ/P.tau)^(m-D+eps)*(physicalDensity V width)^C*
        ((indices (SpatialGridPopulation.refinedLabel V width) q.val).card:ℝ) ≤
          ((SpatialGridPopulation.refinedCells V width q.val).card:ℝ) := by
  let c := (2:ℝ)^(1-C)/LocalAngularCoarse.populationCoefficient (k+1) 3 m
  have hc : 0 < c := div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (LocalAngularCoarse.populationCoefficient_pos _ _ _)
  refine ⟨c,hc,?_⟩
  intro M F δ lam A P g V _U q hg hδ hlam hA hsep hbounded hcap hcoarse
  obtain ⟨_hs,hcbox,hl⟩ := box_geometry V hg hR hsep hbounded hcap q.val (width:=width)
  have hsub : ∀ i, (boxFamily V width q.val).shade i ⊆ SpatialGridPopulation.refinedCells V width q.val := by
    intro i
    rw [← box_cells_eq V width q.val]
    exact (boxFamily V width q.val).shade_subset_union i
  have hh := LocalAngularCoarse.coarse_family_bound (boxFamily V width q.val)
    (F.tube g).direction (SpatialGridPopulation.refinedCells V width q.val)
    (F.tube g).unit_direction hδ P.lower_scale P.upper_scale hm hD hmn hC heps V.density_pos
    (by norm_num : (0:ℝ)<2) (original_density_le_two V hlam) (zero_lt_one.trans_le hA)
    hcbox hl (box_comparable V width q.val) hsub hcoarse
  exact (density_target_le V width hc.le (zero_le_one.trans hA)
    (div_pos hδ (hδ.trans_le P.lower_scale)) (zero_le_one.trans hC) q.val).trans hh

/-- Every normalized mesh above a fixed positive cutoff is handled by the
same original box shadings. This covers the complement of the small-scale
threshold in the high-density theorem, without an analytic estimate premise. -/
theorem bounded_scale {k : ℕ} {m D C eps : ℝ}
    (width R B alpha beta delta0 : ℝ) (hR : 0 ≤ R)
    (hm : 0 ≤ m) (hC : 1 ≤ C) (hdelta0 : 0 < delta0) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} {F : TubeFamily (k+2) M} {δ lam A : ℝ}
      (P : Pieces F δ beta) (g : Fin M) (V : Refinement P lam B alpha g)
      (_U : Package V width R m A) (q : ↥(boxes V width)),
      g ∈ P.groups → 0 < δ → lam ≤ 1 → 1 ≤ A →
      F.Separated δ → F.Bounded R → F.CapBound δ m A → delta0 ≤ δ/P.tau →
      c*A⁻¹*(δ/P.tau)^(m-D+eps)*(physicalDensity V width)^C*
        ((indices (SpatialGridPopulation.refinedLabel V width) q.val).card:ℝ) ≤
          ((SpatialGridPopulation.refinedCells V width q.val).card:ℝ) := by
  let c := (2:ℝ)^(1-C)/(LocalAngularCoarse.populationCoefficient (k+1) 3 m*
    max 1 (delta0^(-D+eps)))
  have hmax : 0 < max 1 (delta0^(-D+eps)) := zero_lt_one.trans_le (le_max_left _ _)
  have hc : 0 < c := div_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (mul_pos (LocalAngularCoarse.populationCoefficient_pos _ _ _) hmax)
  refine ⟨c,hc,?_⟩
  intro M F δ lam A P g V _U q hg hδ hlam hA hsep hbounded hcap hscale
  obtain ⟨_hs,hcbox,hl⟩ := box_geometry V hg hR hsep hbounded hcap q.val (width:=width)
  have hsub : ∀ i, (boxFamily V width q.val).shade i ⊆ SpatialGridPopulation.refinedCells V width q.val := by
    intro i
    rw [← box_cells_eq V width q.val]
    exact (boxFamily V width q.val).shade_subset_union i
  have hh := LocalAngularCoarse.bounded_scale_family_bound (D:=D) (eps:=eps) (boxFamily V width q.val)
    (F.tube g).direction (SpatialGridPopulation.refinedCells V width q.val)
    (F.tube g).unit_direction hδ P.lower_scale P.upper_scale hm hC V.density_pos
    (by norm_num : (0:ℝ)<2) (original_density_le_two V hlam) (zero_lt_one.trans_le hA)
    hcbox hl (box_comparable V width q.val) hsub hdelta0 hscale
  exact (density_target_le V width hc.le (zero_le_one.trans hA)
    (div_pos hδ (hδ.trans_le P.lower_scale)) (zero_le_one.trans hC) q.val).trans hh

end
end KakeyaFormal.AngularBoxCoarse
