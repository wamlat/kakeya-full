import LebesgueRepresentatives
import MeasurableAngularSpatialLengths

/-! The literal angular/spatial decomposition for completed-Lebesgue-measurable
shadings. Actual Borel subsets preserve all original mass and stay in the same
original carriers; the final Pieces record is indexed by the original input.
The retained sets and their broadness/overlap hold pointwise everywhere. -/
namespace KakeyaFormal.LebesgueAngularSpatial
open MeasureTheory Set MeasurableAngularSpatial
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- Replace only the input reference of an already constructed angular piece.
Every selected set, group, index, scale and assignment is literally unchanged. -/
def restoreInput {k M : ℕ} {F : TubeFamily (k+1) M}
    {Y Z : Fin M → Set (Space (k+1))} {δ beta : ℝ}
    (P : MeasurableAngularPieces.Pieces F Z δ beta)
    (hsub : ∀ i, Z i ⊆ Y i)
    (hmass : (∑ i,volume.real (Z i)) = ∑ i,volume.real (Y i)) :
    MeasurableAngularPieces.Pieces F Y δ beta where
  J := P.J
  tau := P.tau
  groups := P.groups
  assign := P.assign
  shading := P.shading
  depth := P.depth
  lower_scale := P.lower_scale
  upper_scale := P.upper_scale
  assign_mem := P.assign_mem
  measurable := P.measurable
  finite := P.finite
  subset := fun g i => (P.subset g i).trans (hsub i)
  unique := P.unique
  local_cap := P.local_cap
  retained := by rw [← hmass]; exact P.retained
  broad := P.broad
  overlap := P.overlap

/-- No mass, geometric or cap oracle is supplied. This constructs the full
variable-axis Lemma 3.2 output from completed-measurable original shadings,
including actual subsets and entire-carrier containment in each spatial box. -/
theorem construct {k M : ℕ} (F : TubeFamily (k+1) M)
    (Y : Fin M → Set (Space (k+1))) (length : Fin M → ℝ)
    {δ beta width upperLength : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) (hb1 : beta ≤ 1)
    (hw : 0 ≤ width) (hL : ∀ i, length i ≤ upperLength)
    (hY : ∀ i, NullMeasurableSet (Y i) volume)
    (hcarrier : ∀ i, Y i ⊆ SamplingGeometry.lengthCarrier (F.tube i) (length i) (width*δ)) :
    Nonempty (MeasurableAngularSpatialLengths.Decomposition F Y length δ beta width upperLength) := by
  obtain ⟨O⟩ := LebesgueRepresentatives.construct volume Y Y hY hY (fun _ => Subset.rfl)
  obtain ⟨U⟩ := MeasurableAngularSpatialLengths.construct F O.full length hδ hδ1 hb hb1 hw hL
    O.full_measurable (fun i => (O.full_subset i).trans (hcarrier i))
  let P := restoreInput U.angular O.full_subset O.full_total_real
  refine ⟨{
    angular := P
    retained := ?_
    overlap := U.overlap
    broad := U.broad
    containing_box := U.containing_box
    containing_tube := U.containing_tube }⟩
  rw [← O.full_total_real]
  exact U.retained

end
end KakeyaFormal.LebesgueAngularSpatial
