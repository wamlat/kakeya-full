import AngularRestrictedRefinement
import GridMarked

/-! Exact measurable full/marked realization of the refined angular references.
Every full set is an original Ref set on an injectively selected tube index;
marks are actual subsets, so all original restricted-union comparisons apply. -/
namespace KakeyaFormal.AngularRestrictedMeasurable
open AngularSeedPieces AngularGroupRestriction AngularSeedRealization AngularRestrictedRefinement
open WidthNormalization GridShadingMeasure GridCells MeasureTheory DensityBroadnessRecovery
open scoped BigOperators ENNReal
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
variable {P : Pieces F δ beta} {g : Fin M}

def family (V : Refinement P lam B alpha g) (width : ℝ) : TubeFamily (k+1) V.N :=
  GridMarked.family V.family (widthFactor (k+1) width)

def Full (V : Refinement P lam B alpha g) (width : ℝ) (i : Fin V.N) : Set (Space (k+1)) :=
  normalizedSet (widthFactor (k+1) width) (cellUnion δ (V.family.shade i))

def Marks (V : Refinement P lam B alpha g) (width : ℝ) (i : Fin V.N) : Set (Space (k+1)) :=
  normalizedSet (widthFactor (k+1) width) (cellUnion δ (V.marks i))

/-- Full sets are exactly the old actual references of the selected indices. -/
theorem full_eq_ref (V : Refinement P lam B alpha g) (width : ℝ) (i : Fin V.N) :
    Full V width i = Ref P width g (V.index i) := by
  unfold Full Ref
  rw [(V.full_exact i).2]

theorem marks_subset_full (V : Refinement P lam B alpha g) (width : ℝ) (i : Fin V.N) :
    Marks V width i ⊆ Full V width i :=
  Set.image_mono (cellUnion_mono δ (V.marks_subset i))

theorem marks_subset_ref (V : Refinement P lam B alpha g) (width : ℝ) (i : Fin V.N) :
    Marks V width i ⊆ Ref P width g (V.index i) := by
  rw [← full_eq_ref]
  exact marks_subset_full V width i

theorem measurable (V : Refinement P lam B alpha g) (width : ℝ) :
    (∀ i, MeasurableSet (Full V width i)) ∧ (∀ i, MeasurableSet (Marks V width i)) :=
  ⟨fun _ => normalized_measurable (widthFactor_pos _ _) (cellUnion_measurable _ _),
    fun _ => normalized_measurable (widthFactor_pos _ _) (cellUnion_measurable _ _)⟩

theorem finite (V : Refinement P lam B alpha g) (width : ℝ) :
    (∀ i, (volume : Measure (Space (k+1))) (Full V width i) ≠ ∞) ∧
    (∀ i, (volume : Measure (Space (k+1))) (Marks V width i) ≠ ∞) :=
  ⟨fun _ => normalized_finite (widthFactor_pos _ _) (cellUnion_finite _ _),
    fun _ => normalized_finite (widthFactor_pos _ _) (cellUnion_finite _ _)⟩

/-- The original physical unit-width carriers still contain the actual refined
full sets, and the unchanged direction is on the same selected reference index. -/
theorem carrier (V : Refinement P lam B alpha g) {width : ℝ} (hδ : 0 < δ)
    (hadm : F.Admissible width δ) (i : Fin V.N) :
    Full V width i ⊆ ((family V width).tube i).carrier δ := by
  have hh := AngularSeedRealization.full_carrier P hδ hadm g (V.index i)
  have hsub := AngularSeedRealization.ref_subset_full P width g (V.index i)
  rw [full_eq_ref]
  have heq : (family V width).tube i = (AngularSeedRealization.family P width g).tube (V.index i) := by
    change normalizedTube (V.family.tube i) _ = normalizedTube ((P.family g).tube (V.index i)) _
    rw [(V.full_exact i).1]
  rw [heq]
  exact hsub.trans hh

/-- Comparable density has the exact same common physical volume factor. -/
theorem full_density (V : Refinement P lam B alpha g) (width : ℝ) (hδ : 0 < δ) (i : Fin V.N) :
    (V.density/(widthFactor (k+1) width)^(k+1))*δ^k ≤
      (volume : Measure (Space (k+1))).real (Full V width i) ∧
    (volume : Measure (Space (k+1))).real (Full V width i) ≤
      2*(V.density/(widthFactor (k+1) width)^(k+1))*δ^k := by
  rw [Full,grid_mass _ hδ (widthFactor_pos _ _)]
  have hlo := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (V.comparable i).1 (pow_pos hδ (k+1)).le)
    (pow_pos (widthFactor_pos (k+1) width) (k+1)).le
  have hhi := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (V.comparable i).2 (pow_pos hδ (k+1)).le)
    (pow_pos (widthFactor_pos (k+1) width) (k+1)).le
  constructor
  · calc
      _ = δ^(k+1)*(V.density/δ)/(widthFactor (k+1) width)^(k+1) := by
        rw [pow_succ δ]
        field_simp
      _ ≤ _ := hlo
  · calc
      _ ≤ δ^(k+1)*(2*V.density/δ)/(widthFactor (k+1) width)^(k+1) := hhi
      _ = _ := by
        rw [pow_succ δ]
        field_simp

/-- Exact marked fraction after both genuine tube selections and the marked
cell filters. No independent thinning of marked incidences is performed. -/
theorem marked_fraction (V : Refinement P lam B alpha g) (width : ℝ) (hδ : 0 < δ) :
    (∑ i, (volume : Measure (Space (k+1))).real (Full V width i))/(4*(V.depth+1:ℕ)) ≤
      ∑ i, (volume : Measure (Space (k+1))).real (Marks V width i) := by
  simp only [Full,Marks,grid_mass _ hδ (widthFactor_pos _ _),← Finset.sum_div,← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left V.marked_fraction
    (div_nonneg (pow_pos hδ (k+1)).le (pow_pos (widthFactor_pos (k+1) width) (k+1)).le)
  convert hh using 1 <;> first | rfl | ring

/-- The inherited power broadness is on the literal final marked row. -/
theorem marked_broad (V : Refinement P lam B alpha g) (width : ℝ) (hδ : 0 < δ) :
    ∀ x, AngularDecomposition.Broad (family V width)
      (Finset.univ.filter (fun i => x ∈ Marks V width i)) δ beta P.tau
      ((broadCoefficient k beta*(8/P.eta))*(2*(V.depth+1:ℕ))) := by
  intro x
  have hh := V.broad (label δ (MeasurableRescaling.inverse (widthFactor (k+1) width) 0 x))
  simpa only [Marks,grid_membership _ hδ (widthFactor_pos _ _),row,AngularDecomposition.Broad,
    AngularDecomposition.cap,family,GridMarked.family,normalized_direction] using hh

/-- Two ends is inherited from original full shadings through the proved
proportional density ratio, while the result stays inside the exact Ref set. -/
theorem two_ends (V : Refinement P lam B alpha g) (width : ℝ) (hδ : 0 < δ)
    (hB : 1 ≤ B) (ha : 0 ≤ alpha) :
    ∀ i x r, δ ≤ r →
      (volume : Measure (Space (k+1))).real (Full V width i ∩ Metric.closedBall x r) ≤
        (((B*(4/P.eta))*(1+((k+1:ℕ):ℝ)/2)^alpha)*(widthFactor (k+1) width)^alpha)*
          r^alpha*(volume : Measure (Space (k+1))).real (Full V width i) := by
  have hr : 1 ≤ 4/P.eta := (le_div_iff₀ P.eta_pos).mpr (by linarith [P.eta_le_one])
  have hBB : 1 ≤ B*(4/P.eta) := by nlinarith
  intro i x r hrδ
  have hold := GridShadingMeasure.two_ends (V.family.shade i) hδ hBB ha (V.two_ends i)
  exact normalized_two_ends (widthFactor_pos _ _) hδ _ hold x r
    ((div_le_self hδ.le (widthFactor_ge_one _ _)).trans hrδ)

/-- The resulting full union is in the SAME restricted original group union
that appears in AngularPiecePopulation's verified overlap sum. -/
theorem full_union_subset (V : Refinement P lam B alpha g) (width : ℝ) :
    (⋃ i, Full V width i) ⊆ normalizedSet (widthFactor (k+1) width)
      (cellUnion δ (P.family g).unionCells) := by
  rintro x ⟨_,⟨i,rfl⟩,hi⟩
  exact Set.image_mono (cellUnion_mono δ
    ((V.family.shade_subset_union i).trans V.union_subset)) hi

end
end KakeyaFormal.AngularRestrictedMeasurable

#print axioms KakeyaFormal.AngularRestrictedMeasurable.full_eq_ref
#print axioms KakeyaFormal.AngularRestrictedMeasurable.marked_fraction
#print axioms KakeyaFormal.AngularRestrictedMeasurable.marked_broad
#print axioms KakeyaFormal.AngularRestrictedMeasurable.two_ends
