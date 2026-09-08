import AngularSeedPieces
import WidthNormalization

/-! Exact measurable realization of actual angular groups using one common
homothety. Full original shadings supply two ends; selected group shadings
supply angular broadness. No newly occupied grid cells are inserted. -/
namespace KakeyaFormal.AngularSeedRealization
open AngularSeedPieces AngularGroupRestriction AngularGroupPruning
open WidthNormalization GridShadingMeasure MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Classical

/-- Actual common-width-normalized tubes with the participating group index set. -/
def family {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) :
    TubeFamily (k+1) (active (P.shading g)).card where
  tube i := normalizedTube ((P.family g).tube i) (widthFactor (k+1) width)
  shade i := (P.family g).shade i

/-- Full original shadings, on the exact participating indices. -/
def Full {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M)
    (i : Fin (active (P.shading g)).card) : Set (Space (k+1)) :=
  normalizedSet (widthFactor (k+1) width)
    (cellUnion δ (F.shade (index (P.shading g) i)))

/-- Actual selected references, with the same map as every full shading. -/
def Ref {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M)
    (i : Fin (active (P.shading g)).card) : Set (Space (k+1)) :=
  normalizedSet (widthFactor (k+1) width) (cellUnion δ ((P.family g).shade i))

/-- Exact density in physical unit-width carriers. -/
def physicalDensity (k : ℕ) (width lam : ℝ) : ℝ := lam/(widthFactor (k+1) width)^(k+1)

/-- The fixed physical two-ends coefficient, independent of both scales. -/
def endsConstant (k : ℕ) (width B alpha : ℝ) : ℝ :=
  (B*(1+((k+1:ℕ):ℝ)/2)^alpha)*(widthFactor (k+1) width)^alpha

theorem physicalDensity_pos (k : ℕ) (width : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    0 < physicalDensity k width lam := div_pos hlam (pow_pos (widthFactor_pos _ _) _)

theorem physicalDensity_le_one (k : ℕ) (width : ℝ) {lam : ℝ} (hlam : lam ≤ 1) :
    physicalDensity k width lam ≤ 1 := by
  exact (div_le_one (pow_pos (widthFactor_pos _ _) _)).mpr
    (hlam.trans (one_le_pow₀ (widthFactor_ge_one _ _)))

theorem full_measurable {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) (i : Fin (active (P.shading g)).card) :
    MeasurableSet (Full P width g i) :=
  normalized_measurable (widthFactor_pos _ _) (cellUnion_measurable _ _)

theorem ref_measurable {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) (i : Fin (active (P.shading g)).card) :
    MeasurableSet (Ref P width g i) :=
  normalized_measurable (widthFactor_pos _ _) (cellUnion_measurable _ _)

theorem ref_finite {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) (i : Fin (active (P.shading g)).card) :
    (volume : Measure (Space (k+1))) (Ref P width g i) ≠ ∞ :=
  normalized_finite (widthFactor_pos _ _) (cellUnion_finite _ _)

theorem ref_subset_full {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) (i : Fin (active (P.shading g)).card) :
    Ref P width g i ⊆ Full P width g i :=
  Set.image_mono (cellUnion_mono δ (P.subset g (index (P.shading g) i)))

theorem full_carrier {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta width : ℝ}
    (P : Pieces F δ beta) (hδ : 0 < δ) (hadm : F.Admissible width δ)
    (g : Fin M) (i : Fin (active (P.shading g)).card) :
    Full P width g i ⊆ ((family P width g).tube i).carrier δ :=
  grid_carrier F hδ hadm (index (P.shading g) i)

theorem family_local {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) {g : Fin M} (hg : g ∈ P.groups) :
    ∀ i, projectiveDistance ((family P width g).tube i).direction (F.tube g).direction ≤ 3*P.tau :=
  P.family_cap hg

theorem family_separated {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) (hsep : F.Separated δ) :
    (family P width g).Separated δ :=
  AngularGroupRestriction.family_separated F (P.shading g) hsep

theorem family_cap_bound {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta m A : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) (hcap : F.CapBound δ m A) :
    (family P width g).CapBound δ m A :=
  AngularGroupRestriction.family_cap_bound F (P.shading g) hcap

/-- The full original comparable upper density becomes its exact common-map
physical upper density; there is no per-group loss in this bound. -/
theorem full_mass_upper {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (hδ : 0 < δ) (hcomp : F.Comparable δ lam)
    (g : Fin M) (i : Fin (active (P.shading g)).card) :
    (volume : Measure (Space (k+1))).real (Full P width g i) ≤
      2*physicalDensity k width lam*δ^k := by
  rw [Full,grid_mass _ hδ (widthFactor_pos _ _)]
  calc
    _ ≤ δ^(k+1)*(2*lam/δ)/(widthFactor (k+1) width)^(k+1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hcomp _).2 (pow_pos hδ _).le)
        (pow_pos (widthFactor_pos _ _) _).le
    _ = _ := by
      unfold physicalDensity
      rw [pow_succ δ]
      field_simp

/-- Exact total group incidence mass under the common measurable map. -/
theorem ref_mass {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (hδ : 0 < δ) (g : Fin M) :
    (∑ i, (volume : Measure (Space (k+1))).real (Ref P width g i)) =
      δ^(k+1)*mass (P.shading g)/(widthFactor (k+1) width)^(k+1) := by
  simp only [Ref,grid_mass _ hδ (widthFactor_pos _ _),← Finset.sum_div,← Finset.mul_sum]
  rw [P.family_mass]

/-- The actual pruning threshold supplies the exact positive mass premise
required by the measurable angular-box theorem. -/
theorem kept_ref_mass_lower {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (hδ : 0 < δ) {g : Fin M}
    (hg : g ∈ P.keptGroups lam) :
    P.eta*physicalDensity k width lam*δ^k*((active (P.shading g)).card:ℝ) ≤
      ∑ i, (volume : Measure (Space (k+1))).real (Ref P width g i) := by
  have hm := (kept_spec P.groups P.shading (P.eta*(lam/δ)) hg).2
  rw [ref_mass P width hδ g]
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hm (pow_pos hδ (k+1)).le)
    (pow_pos (widthFactor_pos (k+1) width) (k+1)).le
  calc
    _ = δ^(k+1)*(P.eta*(lam/δ)*((active (P.shading g)).card:ℝ))/(widthFactor (k+1) width)^(k+1) := by
      unfold physicalDensity
      rw [pow_succ δ]
      field_simp
    _ ≤ _ := hh

/-- All points of the exact references retain finite angular broadness. -/
theorem ref_broad {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (hδ : 0 < δ) {g : Fin M} (hg : g ∈ P.groups) :
    ∀ x, AngularDecomposition.Broad (family P width g)
      (Finset.univ.filter (fun i => x ∈ Ref P width g i))
      δ beta P.tau ((4:ℝ)^beta*(4*angularConstant k)) := by
  intro x
  have hb := AngularGroupRestriction.family_broad F (P.shading g) (fun z => P.broad z g hg)
    (GridCells.label δ (MeasurableRescaling.inverse (widthFactor (k+1) width) 0 x))
  simpa only [Ref,grid_membership _ hδ (widthFactor_pos _ _),AngularDecomposition.Broad,
    AngularDecomposition.cap,family,normalized_direction,Pieces.family] using hb

/-- Every physical ball test for the full shadings is inherited from the
original full finite shading, not from a selected low-density subset. -/
theorem full_two_ends {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta B alpha : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (hδ : 0 < δ) (hB : 1 ≤ B) (ha : 0 ≤ alpha)
    (hends : ∀ i, ∀ x : Space (k+1), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ)) :
    ∀ g (i : Fin (active (P.shading g)).card) x r, δ ≤ r →
      (volume : Measure (Space (k+1))).real (Full P width g i ∩ Metric.closedBall x r) ≤
        endsConstant k width B alpha*r^alpha*(volume : Measure (Space (k+1))).real (Full P width g i) := by
  intro g i x r hr
  have hold := GridShadingMeasure.two_ends (F.shade (index (P.shading g) i)) hδ hB ha (hends _)
  exact normalized_two_ends (widthFactor_pos _ _) hδ _ hold x r
    ((div_le_self hδ.le (widthFactor_ge_one _ _)).trans hr)

/-- Exact measurable overlap of all retained groups, including every boundary
point, is controlled by the original finite group overlap. -/
theorem kept_group_overlap {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (hδ : 0 < δ) (x : Space (k+1)) :
    (((P.keptGroups lam).filter (fun g => ∃ i, x ∈ Ref P width g i)).card:ℝ) ≤ 2*P.tau^(-beta) := by
  simpa only [Ref,grid_membership _ hδ (widthFactor_pos _ _)] using
    (P.kept_overlap (lam := lam) (GridCells.label δ (MeasurableRescaling.inverse (widthFactor (k+1) width) 0 x)))

/-- Every selected measurable group union lies in one and the same transformed
original union, so groupwise estimates compare to the requested original set. -/
theorem ref_union_subset {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (width : ℝ) (g : Fin M) :
    (⋃ i, Ref P width g i) ⊆
      normalizedSet (widthFactor (k+1) width) (cellUnion δ F.unionCells) := by
  rintro x ⟨_,⟨i,rfl⟩,hi⟩
  exact Set.image_mono (cellUnion_mono δ
    ((P.subset g (index (P.shading g) i)).trans (F.shade_subset_union _))) hi

end
end KakeyaFormal.AngularSeedRealization
