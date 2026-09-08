import ActualGroupedGeometry
import SelectedLiftWitness

/-! The literal original slab label survives finite grouping and high-cell
restriction. Legal energy positions follow from selected centered cells and
the actual integral shift, rather than an assumed energy comparison. -/
namespace KakeyaFormal.GroupedSlabPositions
open Finset ActualGroupedIncidence SelectedLiftWitness SlabNormalization
open scoped BigOperators
noncomputable section
open Classical

variable {I C : Type*} [Fintype I] {k : ℕ}
    (base : I → Cell k × ℕ) (color : I → C)
    (trimmed shading : I → Finset (Cell (k+1))) {δ : ℝ}
    (hsub : ∀ i, shading i ⊆ (trimmed i).image (shiftCell δ (base i).2))
    (hslab : ∀ i z, z ∈ trimmed i →
      ((base i).2 : ℝ) ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) < ((base i).2 : ℝ)+1)

include hsub hslab

/-- Every actual normalized incidence occupies the same legal original slab
selected for its own original output index. -/
theorem incidence_position_legal
    (r : GroupedCumulative.Record (k := k+1) (population base color))
    (hr : r ∈ incidences base color shading) : LegalPosition δ (position base color r) := by
  have hz := (mem_incidences base color shading r).mp hr
  obtain ⟨z,hztrim,hzeq⟩ := mem_image.mp (hsub (indexEquiv base color r.1) hz)
  rw [position_original base color r,← hzeq]
  exact shifted_position_legal _ _ (hslab _ _ hztrim)

/-- Every subset returned by grouped high-cell pruning inherits actual legal
positions, with no slab-count factor. -/
theorem restricted_position_legal
    (T : Finset (GroupedCumulative.Record (k := k+1) (population base color)))
    (hT : T ⊆ incidences base color shading) :
    ∀ r ∈ T, LegalPosition δ (position base color r) :=
  fun r hr => incidence_position_legal base color trimmed shading hsub hslab r (hT hr)

/-- The actual grouped degree energy equals the energy at original pivot and
unshifted lifted-cell labels, for every actual retained incidence restriction. -/
theorem restricted_energy_equals_original
    (T : Finset (GroupedCumulative.Record (k := k+1) (population base color)))
    (hT : T ⊆ incidences base color shading) :
    (∑ q ∈ T.image (fun r => originalPosition δ (position base color r)),
      ((T.filter (fun r => originalPosition δ (position base color r)=q)).card : ℝ)^2) =
      ∑ p ∈ T.image (position base color),
        (GroupedIncidence.degree T (position base color) p : ℝ)^2 := by
  have hh := grouped_energy_equals_original T (position base color)
    (restricted_position_legal base color trimmed shading hsub hslab T hT)
  unfold GroupedIncidence.degree
  convert hh using 1
  congr! 10

end
end KakeyaFormal.GroupedSlabPositions
