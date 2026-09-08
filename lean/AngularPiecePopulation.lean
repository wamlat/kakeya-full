import TransformedGridSupport
import AngularSeedRealization
import SamplingDichotomy

/-! Returning actual transformed angular-piece support to original cell counts.
Only original restricted piece unions enter the overlap sum; no overlap of
sampled target cubes or their pullbacks is asserted. -/
namespace KakeyaFormal.AngularPiecePopulation
open Finset AngularSeedPieces AngularGroupRestriction AngularSeedRealization
open GridShadingMeasure TransformedGridSupport SpatialAngular WidthNormalization
open MeasureTheory
open scoped BigOperators
noncomputable section
open Classical

/-- Exact original group union; compression adds no cells. -/
theorem family_union_subset {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (g : Fin M) : (P.family g).unionCells ⊆ F.unionCells := by
  intro z hz
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
  exact F.shade_subset_union _ (P.subset g (index (P.shading g) i) hi)

/-- Double-count actual old-cell group occurrences to obtain the source overlap
sum. The pointwise overlap used here is derived by the angular construction. -/
theorem sum_old_unions {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam : ℝ}
    (P : Pieces F δ beta) :
    (∑ g ∈ P.keptGroups lam, (((P.family g).unionCells).card:ℝ)) ≤
      2*P.tau^(-beta)*(F.unionCells.card:ℝ) := by
  let groups := P.keptGroups lam
  let row (z : Cell (k+1)) := groups.filter (fun g => z ∈ (P.family g).unionCells)
  have hf (g : Fin M) : F.unionCells.filter (fun z => g ∈ row z) =
      if g ∈ groups then (P.family g).unionCells else ∅ := by
    ext z
    by_cases hg : g ∈ groups
    · simp only [row,mem_filter,hg,true_and]
      exact and_iff_right_of_imp (fun hz => family_union_subset P g hz)
    · simp [row,hg]
  have hdc := AngularAssignment.sum_row_cards F.unionCells row
  simp_rw [hf] at hdc
  have hid : (∑ g ∈ groups, (((P.family g).unionCells).card:ℝ)) =
      ∑ z ∈ F.unionCells, ((row z).card:ℝ) := by
    have hn : (∑ z ∈ F.unionCells, (row z).card) =
        ∑ g ∈ groups, (P.family g).unionCells.card := by simpa [apply_ite] using hdc
    exact_mod_cast hn.symm
  rw [show P.keptGroups lam = groups from rfl,hid]
  calc
    _ ≤ ∑ _z ∈ F.unionCells, 2*P.tau^(-beta) := by
      apply sum_le_sum
      intro z _
      simpa only [row,groups,TubeFamily.unionCells,mem_biUnion,mem_univ,true_and] using
        P.kept_overlap (lam:=lam) z
    _ = _ := by simp [mul_comm]

/-- The full transformed union of the actual references is contained in the
common map of the original restricted piece union. -/
theorem transformed_ref_subset {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) (u : Space (k+1)) (q : Cell k)
    (i : Fin (active (P.shading g)).card) :
    normalizeBox u P.tau q '' Ref P width g i ⊆
      (pieceMap u P.tau (widthFactor (k+1) width) q) '' cellUnion δ (P.family g).unionCells := by
  rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
  exact ⟨x,cellUnion_mono δ ((P.family g).shade_subset_union i) hx,rfl⟩

/-- Actual positive sampling support of restrictions of the transformed
references is controlled by the old piece count. No geometric count is an input. -/
theorem piece_positive_count {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta width R newWidth : ℝ}
    (P : Pieces F δ beta) (hδ : 0 < δ) (g : Fin M) (u : Space (k+1)) (q : Cell k)
    (tube : Fin (active (P.shading g)).card → UnitTube (k+1))
    (Y : Fin (active (P.shading g)).card → Set (Space (k+1)))
    (hY : ∀ i, Y i ⊆ normalizeBox u P.tau q '' Ref P width g i) :
    (SamplingSupport.support tube Y (δ/P.tau) newWidth R).card ≤
      (P.family g).unionCells.card*(2*(k+1)+3)^(k+1) :=
  positive_support_card u hδ (hδ.trans_le P.lower_scale) P.upper_scale (widthFactor_ge_one _ _)
    q (P.family g).unionCells tube Y (fun i => (hY i).trans (transformed_ref_subset P width g u q i))

/-- Sum of all newly available populations is bounded using ONLY the old
restricted piece unions and their verified overlap. Maps may differ by group. -/
theorem sum_piece_positive_counts {k M : ℕ} {F : TubeFamily (k+1) M}
    {δ beta width R newWidth lam : ℝ} (P : Pieces F δ beta) (hδ : 0 < δ)
    (u : Fin M → Space (k+1)) (q : Fin M → Cell k)
    (tube : ∀ g, Fin (active (P.shading g)).card → UnitTube (k+1))
    (Y : ∀ g, Fin (active (P.shading g)).card → Set (Space (k+1)))
    (hY : ∀ g ∈ P.keptGroups lam, ∀ i,
      Y g i ⊆ normalizeBox (u g) P.tau (q g) '' Ref P width g i) :
    (∑ g ∈ P.keptGroups lam, ((SamplingSupport.support (tube g) (Y g) (δ/P.tau) newWidth R).card:ℝ)) ≤
      (((2*(k+1)+3)^(k+1):ℕ):ℝ)*(2*P.tau^(-beta)*(F.unionCells.card:ℝ)) := by
  have hbound : (∑ g ∈ P.keptGroups lam,
      ((SamplingSupport.support (tube g) (Y g) (δ/P.tau) newWidth R).card:ℝ)) ≤
      ∑ g ∈ P.keptGroups lam, (((P.family g).unionCells.card*(2*(k+1)+3)^(k+1):ℕ):ℝ) := by
    apply sum_le_sum
    intro g hg
    exact_mod_cast piece_positive_count (newWidth:=newWidth) (R:=R) P hδ g (u g) (q g)
      (tube g) (Y g) (hY g hg)
  simp only [Nat.cast_mul,← sum_mul] at hbound
  exact hbound.trans (by
    have hh := mul_le_mul_of_nonneg_right (sum_old_unions (lam:=lam) P)
      (Nat.cast_nonneg ((2*(k+1)+3)^(k+1)))
    simpa only [mul_comm] using hh)

end
end KakeyaFormal.AngularPiecePopulation

#print axioms KakeyaFormal.AngularPiecePopulation.sum_old_unions
#print axioms KakeyaFormal.AngularPiecePopulation.sum_piece_positive_counts
