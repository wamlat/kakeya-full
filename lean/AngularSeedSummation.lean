import AngularSeedRealization

/-! Actual measurable union summation for the constructed angular groups.
The pointwise overlap is proved from the finite assignment, and every group
lies in the same common image of the original shading union. -/
namespace KakeyaFormal.AngularSeedSummation
open AngularSeedPieces AngularSeedRealization AngularGroupRestriction
open WidthNormalization GridShadingMeasure MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Classical

def groupUnion {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) : Set (Space (k+1)) := ⋃ i, Ref P width g i

theorem groupUnion_measurable {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) : MeasurableSet (groupUnion P width g) :=
  MeasurableSet.iUnion (ref_measurable P width g)

theorem groupUnion_finite {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) :
    (volume : Measure (Space (k+1))) (groupUnion P width g) ≠ ∞ :=
  measure_ne_top_of_subset (ref_union_subset P width g)
    (normalized_finite (widthFactor_pos _ _) (cellUnion_finite _ _))

/-- Use the original finite group index space, with empty sets for discarded
groups. This changes neither the retained sum nor any pointwise overlap. -/
def retainedUnion {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width lam : ℝ) (g : Fin M) : Set (Space (k+1)) :=
  if g ∈ P.keptGroups lam then groupUnion P width g else ∅

theorem retainedUnion_measurable {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width lam : ℝ) (g : Fin M) : MeasurableSet (retainedUnion P width lam g) := by
  unfold retainedUnion
  split_ifs
  · exact groupUnion_measurable P width g
  · exact MeasurableSet.empty

theorem retainedUnion_finite {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width lam : ℝ) (g : Fin M) :
    (volume : Measure (Space (k+1))) (retainedUnion P width lam g) ≠ ∞ := by
  unfold retainedUnion
  split_ifs
  · exact groupUnion_finite P width g
  · simp

theorem retainedUnion_overlap {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width lam : ℝ) (hδ : 0 < δ) (x : Space (k+1)) :
    (MeasurableEnergy.overlapCount (retainedUnion P width lam) x:ℝ) ≤ 2*P.tau^(-beta) := by
  have heq : Finset.univ.filter (fun g => x ∈ retainedUnion P width lam g) =
      (P.keptGroups lam).filter (fun g => ∃ i, x ∈ Ref P width g i) := by
    ext g
    by_cases hg : g ∈ P.keptGroups lam <;> simp [retainedUnion,groupUnion,hg]
  simpa only [MeasurableEnergy.overlapCount,heq] using kept_group_overlap P width hδ x

/-- The actual selected union stays in a single common image of the original
whole-grid union, independently of its number of angular groups. -/
theorem retainedUnion_subset {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width lam : ℝ) :
    (⋃ g, retainedUnion P width lam g) ⊆
      normalizedSet (widthFactor (k+1) width) (cellUnion δ F.unionCells) := by
  intro x hx
  obtain ⟨g,hg⟩ := Set.mem_iUnion.mp hx
  by_cases hkeep : g ∈ P.keptGroups lam
  · exact ref_union_subset P width g (by simpa [retainedUnion,hkeep,groupUnion] using hg)
  · simp [retainedUnion,hkeep] at hg

/-- The quantitative volume summation has exactly the angular overlap loss and
exactly the shared width-normalization factor. -/
theorem group_volume_sum {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width lam : ℝ) (hδ : 0 < δ) :
    (∑ g ∈ P.keptGroups lam, (volume : Measure (Space (k+1))).real (groupUnion P width g)) ≤
      (2*P.tau^(-beta))*(δ^(k+1)*(F.unionCells.card:ℝ)/(widthFactor (k+1) width)^(k+1)) := by
  have hover := MeasurableEnergy.finite_union_overlap (μ := (volume : Measure (Space (k+1))))
    (retainedUnion P width lam) (retainedUnion_measurable P width lam)
    (retainedUnion_finite P width lam) (retainedUnion_overlap P width lam hδ)
  have hsum : (∑ g, (volume : Measure (Space (k+1))).real (retainedUnion P width lam g)) =
      ∑ g ∈ P.keptGroups lam, (volume : Measure (Space (k+1))).real (groupUnion P width g) := by
    simp only [retainedUnion,apply_ite,measureReal_empty,Finset.sum_ite,Finset.sum_const_zero,add_zero]
    congr 1
    ext g
    simp
  rw [hsum] at hover
  have hvol := measureReal_mono (retainedUnion_subset P width lam)
    (normalized_finite (widthFactor_pos _ _) (cellUnion_finite _ _))
  rw [grid_mass _ hδ (widthFactor_pos _ _)] at hvol
  exact hover.trans (mul_le_mul_of_nonneg_left hvol (by
    have htau : 0 < P.tau := hδ.trans_le P.lower_scale
    positivity))

/-- The angular gain of the single-group estimate offsets the angular group
overlap whenever the chosen broadness exponent is at most the seed exponent. -/
theorem angular_gain_absorbs_overlap {δ tau beta s : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (hbs : beta ≤ s) :
    δ^s ≤ tau^beta*(δ/tau)^s := by
  rw [Real.div_rpow hδ.le htau.le,← mul_div_assoc]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos htau s)).mpr
  have hh : tau^s ≤ tau^beta := Real.rpow_le_rpow_of_exponent_ge htau htau1 hbs
  have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hδ s).le
  nlinarith

end
end KakeyaFormal.AngularSeedSummation
