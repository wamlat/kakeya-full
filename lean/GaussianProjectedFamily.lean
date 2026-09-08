import GaussianProjectedSelection
import ProjectedGridFamily

/-! The complete actual projected family obtained from the original Gaussian
selection. An injective original-index restriction precedes one common grid
projection; no output geometry, retained population or fiber bound is assumed. -/
namespace KakeyaFormal.GaussianProjectedFamily
open GaussianMatrix GaussianLinearOperator GaussianConditioning GaussianProjectedSelection
open ProjectedGrid SamplingGeometry
noncomputable section
open Classical

def indexMap {M : ℕ} (S : Finset (Fin M)) (i : Fin S.card) : Fin M :=
  (S.equivFin.symm i).val

theorem indexMap_injective {M : ℕ} (S : Finset (Fin M)) : Function.Injective (indexMap S) :=
  Subtype.val_injective.comp S.equivFin.symm.injective

theorem indexMap_mem {M : ℕ} (S : Finset (Fin M)) (i : Fin S.card) : indexMap S i∈S :=
  (S.equivFin.symm i).property

def restrictedFamily {n M : ℕ} (F : TubeFamily n M) (S : Finset (Fin M)) : TubeFamily n S.card where
  tube i := F.tube (indexMap S i)
  shade i := F.shade (indexMap S i)

theorem restricted_union {n M : ℕ} (F : TubeFamily n M) (S : Finset (Fin M)) :
    (restrictedFamily F S).unionCells=S.biUnion F.shade := by
  ext z
  simp only [TubeFamily.unionCells,restrictedFamily,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨indexMap S i,indexMap_mem S i,hi⟩
  · rintro ⟨i,hi,hz⟩
    refine ⟨S.equivFin ⟨i,hi⟩,?_⟩
    simpa only [indexMap,Equiv.symm_apply_apply] using hz

theorem restricted_union_subset {n M : ℕ} (F : TubeFamily n M) (S : Finset (Fin M)) :
    (restrictedFamily F S).unionCells ⊆ F.unionCells := by
  rw [restricted_union]
  intro z hz
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩

/-- Literal lengths of the images of the selected original unit segments. -/
def lengths {M : ℕ} (F : TubeFamily 7 M) (S : Finset (Fin M)) (ω : Sample 5 7)
    (i : Fin S.card) : ℝ := ‖operator ω (F.tube (indexMap S i)).direction‖

/-- Every field describes the actual original-index restriction and the same
common rounded projection. Physical lengths are separate from unit directions. -/
structure Output {M : ℕ} (F : TubeFamily 7 M) (δ A width R : ℝ) where
  omega : Sample 5 7
  selected : Finset (Fin M)
  family : TubeFamily 5 selected.card
  operator_bound : ‖operator omega‖ ≤ 20
  tube_geometry : ∀ i, (family.tube i).base=operator omega (F.tube (indexMap selected i)).base ∧
    (family.tube i).direction=‖operator omega (F.tube (indexMap selected i)).direction‖⁻¹ •
      operator omega (F.tube (indexMap selected i)).direction
  image_rows : ∀ i, family.shade i=(F.shade (indexMap selected i)).image (labelMap (operator omega) δ)
  length_bounds : ∀ i, (1/4:ℝ) ≤ lengths F selected omega i ∧ lengths F selected omega i ≤ 20
  carrier : ∀ i q, q∈family.shade i → cellCenter δ q ∈
    lengthCarrier (family.tube i) (lengths F selected omega i) ((20*width+(5:ℝ)/2)*δ)
  separated : family.Separated ((2/Real.pi)*δ)
  union_image : family.unionCells=(selected.biUnion F.shade).image (labelMap (operator omega) δ)
  union_card_le : family.unionCells.card ≤ F.unionCells.card
  row_bounds : ∀ i,
    ((F.shade (indexMap selected i)).card:ℝ)/(fiberConstant 7 5 (1/4) 20 width:ℝ) ≤
        ((family.shade i).card:ℝ) ∧
      ((family.shade i).card:ℝ) ≤ (F.shade (indexMap selected i)).card
  bounded : family.Bounded (20*R)
  population : retainedConstant*(M:ℝ)/(A*Real.log (2/δ)) ≤ (selected.card:ℝ)

/-- Original cap-four, separation and ordinary tube/grid geometry construct
the actual lower-dimensional finite family and every quantitative field above.
Constants are fixed before all original configurations; M=0 is included. -/
theorem construct {M : ℕ} (F : TubeFamily 7 M) {δ A width R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    (hsep : F.Separated δ) (hcap : F.CapBound δ 4 A)
    (hadm : F.Admissible width δ) (hbounded : F.Bounded R) :
    Nonempty (Output F δ A width R) := by
  obtain ⟨ω,S,hK,hgood,_hangle,hchord,hpop⟩ := exists_projection F hδ hδ1 hA hsep hcap
  let P := operator ω
  let G := restrictedFamily F S
  have hg : ∀ i, (1/4:ℝ) ≤ ‖P (G.tube i).direction‖ :=
    fun i => hgood (indexMap S i) (indexMap_mem S i)
  have hd : ∀ i, ‖P (G.tube i).direction‖ ≠ 0 := fun i =>
    (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) (hg i)).ne'
  have hGa : G.Admissible width δ := fun i z hz => hadm (indexMap S i) z hz
  have hGb : G.Bounded R := fun i => hbounded (indexMap S i)
  let H := ProjectedGridFamily.family P G δ hd
  have hHdir (i : Fin S.card) : (H.tube i).direction=
      unitDirection (P (F.tube (indexMap S i)).direction) := by
    change ‖P (G.tube i).direction‖⁻¹ • P (G.tube i).direction=
      unitDirection (P (G.tube i).direction)
    rw [unitDirection,if_neg (norm_ne_zero_iff.mp (hd i))]
  have hHs : H.Separated ((2/Real.pi)*δ) := by
    intro i j hij
    rw [hHdir i,hHdir j]
    exact hchord (indexMap S i) (indexMap_mem S i) (indexMap S j) (indexMap_mem S j)
      (fun h => hij (indexMap_injective S h))
  have hHu : H.unionCells=(S.biUnion F.shade).image (labelMap P δ) := by
    rw [ProjectedGridFamily.union_image,restricted_union]
  refine ⟨{
    omega := ω
    selected := S
    family := H
    operator_bound := hK
    tube_geometry := fun _ => ⟨rfl,rfl⟩
    image_rows := fun _ => rfl
    length_bounds := ProjectedGridFamily.length_bounds P G hK hg
    carrier := ProjectedGridFamily.family_carrier P G hd hδ hK hGa
    separated := hHs
    union_image := hHu
    union_card_le := (ProjectedGridFamily.union_card_le P G δ hd).trans
      (Finset.card_le_card (restricted_union_subset F S))
    row_bounds := ProjectedGridFamily.row_card_bounds P G hd hδ (by norm_num) hK hg hGa
    bounded := ProjectedGridFamily.bounded P G δ hd hK hGb
    population := hpop
  }⟩

/-- Optional original comparable-density input gives the precise fixed
projected density interval. No strict factor-two normalization is claimed. -/
theorem density_bounds {M : ℕ} {F : TubeFamily 7 M} {δ A width R lam : ℝ}
    (U : Output F δ A width R) (hcomp : F.Comparable δ lam) :
    ∀ i, lam/((fiberConstant 7 5 (1/4) 20 width:ℝ)*δ) ≤ ((U.family.shade i).card:ℝ) ∧
      ((U.family.shade i).card:ℝ) ≤ 2*lam/δ := by
  intro i
  have hh := div_le_div_of_nonneg_right (hcomp (indexMap U.selected i)).1
    (Nat.cast_nonneg (fiberConstant 7 5 (1/4) 20 width))
  refine ⟨?_,(U.row_bounds i).2.trans (hcomp _).2⟩
  apply (le_trans _ (U.row_bounds i).1)
  simpa only [div_div,mul_comm] using hh

end
end KakeyaFormal.GaussianProjectedFamily
