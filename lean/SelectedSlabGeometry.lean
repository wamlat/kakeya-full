import SlabNormalization
import PrunedGraphLift

/-! A common residue-color type and genuine geometric input families for all
original pivot/slab groups. No cap, separation, or large-radius spatial estimate
is assumed: these are derived from the actual pruned union and legal lifts. -/
namespace KakeyaFormal.SelectedSlabGeometry
open Finset PivotWitnesses PivotOutputCount SelectedFiberLift SlabNormalization
open LiftGraph PrunedGraphLift Coarsening BallPruning
open scoped BigOperators
noncomputable section
open Classical

/-- This modulus is fixed by the pivot rounding error, before any group data. -/
def colorModulus (C : ℝ) : ℕ := Nat.ceil (2*C+1)

def residueColor {I : Type*} {k : ℕ} (C : ℝ) (label : I → Cell k)
    (i : I) : Fin k → ZMod (colorModulus C) := fun l => (label i l : ZMod (colorModulus C))

theorem color_modulus_bounds {C : ℝ} (hC : 0 ≤ C) :
    0 < colorModulus C ∧ (colorModulus C : ℝ) ≤ 2*C+2 ∧
      2*C+1 ≤ (colorModulus C : ℝ) := by
  have hlo : 2*C+1 ≤ (colorModulus C : ℝ) := Nat.le_ceil _
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ 2*C+1 by positivity)
  refine ⟨?_,?_,hlo⟩
  · have hp : (0 : ℝ) < colorModulus C := by linarith
    exact_mod_cast hp
  · dsimp [colorModulus]
    linarith

/-- The explicit same color is used in every pivot/slab group. The original
label map need only be injective within the current fixed-pivot group. -/
theorem common_color_separation {I : Type*} {k : ℕ}
    (v : I → Space k) (label : I → Cell k) (pivot : Space k)
    {δ V C : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hinj : Function.Injective label) (hv : ∀ i, ‖v i‖ ≤ V)
    (hres : ∀ i, ‖v i-(pivot-cellCenter δ (label i))‖ ≤ C*δ) :
    ∀ i j, i ≠ j → residueColor C label i = residueColor C label j →
      δ/(2*(1+V)^2) ≤ projectiveDistance (graphDirection (v i)) (graphDirection (v j)) := by
  intro i j hij hc
  have hgrid := modular_grid_separation label hinj hδ hij hc
  have hresdist := residual_label_distance pivot (cellCenter δ (label i))
    (cellCenter δ (label j)) (v i) (v j) (hres i) (hres j)
  have hinverse := graphDirection_inverse (v i) (v j) hV (hv i) (hv j)
  have hQδ := mul_le_mul_of_nonneg_left (color_modulus_bounds hC).2.2 hδ.le
  apply (div_le_iff₀ (by positivity : 0 < 2*(1+V)^2)).mpr
  nlinarith

theorem common_color_count {k : ℕ} {C : ℝ} (hC : 0 ≤ C) :
    let _ : NeZero (colorModulus C) := ⟨(color_modulus_bounds hC).1.ne'⟩
    (Fintype.card (Fin k → ZMod (colorModulus C)) : ℝ) ≤ (2*C+2)^k := by
  let _ : NeZero (colorModulus C) := ⟨(color_modulus_bounds hC).1.ne'⟩
  exact color_count_bound (color_modulus_bounds hC).1 (color_modulus_bounds hC).2.1

/-- A common normalization for all legal selected groups with vertex radius R.
The direction separation is exactly delta/8 because the reference slopes have
norm at most one. No kappa or slab index occurs in the normalization. -/
def geometry (k : ℕ) (R : ℝ) : Normalization where
  width := 3*(((k : ℝ)+1)/2)+2
  separation := 1/8
  radius := max 1 (R+6+3*(((k : ℝ)+1)/2))
  width_pos := by positivity
  separation_pos := by norm_num
  radius_pos := zero_lt_one.trans_le (le_max_left _ _)

def capCoefficient (k : ℕ) (baseWidth baseRadius d L pairWidth : ℝ) : ℝ :=
  (spatialConstant k baseWidth baseRadius d*L)*(16+2*(pairWidth+(k : ℝ)/2))^d

theorem cap_coefficient_ge_one {k : ℕ} {baseWidth baseRadius d L pairWidth : ℝ}
    (hd : 0 ≤ d) (hL : 1 ≤ L) (hw : 0 ≤ pairWidth) :
    1 ≤ capCoefficient k baseWidth baseRadius d L pairWidth := by
  have hh := lifted_cap_coefficient_ge_one (k := k) (width := baseWidth) (R := baseRadius)
    (V := (1:ℝ)) (C := pairWidth+(k : ℝ)/2) hd hL (by norm_num) (by positivity)
  norm_num at hh
  exact hh

/-- Actual legal selected lifts in one original pivot/slab group yield the same
fixed geometry, real-d cap coefficient and finite color palette in every group.
The small-radius premise is the literal output of spatial pruning. Its required
all-radius extension is proved inside this theorem from the original tubes. -/
theorem selected_group_geometry {k M N J : ℕ} {kap δ pairWidth R L d baseWidth baseRadius : ℝ}
    (F : TubeFamily k M) (E : Finset (Cell k))
    (angles : Fin N → Angle k kap) (fc sc : Fin N → Cell k → ℝ)
    (reference : ∀ i, LabeledPair (angles i) δ pairWidth (fc i) (sc i))
    (raw : ∀ i, Finset (LabeledPair (angles i) δ pairWidth (fc i) (sc i)))
    (S : Fin N → Finset (Cell (k+1))) (group : Cell k × ℕ) (label : Fin N → Cell k)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) (hw : 0 ≤ pairWidth)
    (hbaseWidth : 0 ≤ baseWidth) (hL : 1 ≤ L) (hd : 0 ≤ d)
    (hadm : F.Admissible baseWidth δ) (hbounded : F.Bounded baseRadius)
    (hsmall : ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((ballCells (PrunedIncidence.family F E δ L d J).unionCells δ x r).card : ℝ) ≤
        (coverConstant k 1*(2:ℝ)^d*L)*(r/δ)^d)
    (hinj : Function.Injective label)
    (hlabels : ∀ i, label i ∈ (PrunedIncidence.family F E δ L d J).unionCells)
    (hne : ∀ i, (S i).Nonempty) (hvertex : ∀ i, ‖(angles i).vertex‖ ≤ R)
    (hsub : ∀ i, S i ⊆ liftedCells (reference i) (raw i))
    (hslab : ∀ i z, z ∈ S i → (group.2 : ℝ) ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) < (group.2 : ℝ)+1)
    (hpivot : ∀ i, (reference i).pivotLabel = group.1)
    (hintermediate : ∀ i, dist (cellCenter δ (label i))
      ((angles i).vertex+(angles i).intermediate • (angles i).first) ≤ pairWidth*δ) :
    let C := pairWidth+(k : ℝ)/2
    ∃ G : TubeFamily (k+1) N,
      (∀ i, (G.tube i).direction = graphDirection ((reference i).endpoints.coefficient • (angles i).second)) ∧
      (∀ i, G.shade i ⊆ (S i).image (shiftCell δ group.2)) ∧
      (∀ i, ((S i).card : ℝ)/3 ≤ ((G.shade i).card : ℝ)) ∧
      G.Admissible (geometry k R).width δ ∧
      G.Bounded (geometry k R).radius ∧
      G.CapBound δ d (capCoefficient k baseWidth baseRadius d L pairWidth) ∧
      (∀ i j, i ≠ j → residueColor C label i = residueColor C label j →
        (geometry k R).separation*δ ≤ projectiveDistance (G.tube i).direction (G.tube j).direction) ∧
      G.unionCells ⊆ (univ.biUnion S).image (shiftCell δ group.2) ∧
      G.unionCells.card ≤ (univ.biUnion S).card ∧
      (∀ i, (G.shade i).Nonempty) ∧
      (∀ i, ‖(reference i).endpoints.coefficient • (angles i).second-
        (cellCenter δ group.1-cellCenter δ (label i))‖ ≤ C*δ) := by
  intro C
  obtain ⟨G,hdir,hshade,hcard,hGadm,hGbound,hU,hUcard,hres⟩ :=
    normalize_selected_group angles fc sc reference raw S group label hδ hδ1 hk hne hvertex
      hsub hslab hpivot hintermediate
  let v := fun i => (reference i).endpoints.coefficient • (angles i).second
  have hv (i) : ‖v i‖ ≤ 1 := reference_slope_bound (reference i) hk
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hball := pruned_all_ball_bound F E hδ hδ1 hbaseWidth hL0 hd hadm hbounded hsmall
  have hcap := lifted_family_cap_bound G v label (cellCenter δ group.1)
    (PrunedIncidence.family F E δ L d J).unionCells hinj hlabels hδ
    (by norm_num : (0:ℝ) ≤ 1) hC
    (mul_nonneg (spatialConstant_nonneg k hbaseWidth) hL0) hv hres hdir hball
  have hcolor := common_color_separation v label (cellCenter δ group.1) hδ
    (by norm_num : (0:ℝ) ≤ 1) hC hinj hv hres
  refine ⟨G,hdir,hshade,hcard,hGadm,fun i => (hGbound i).trans (le_max_right _ _),?_,?_,hU,hUcard,?_,hres⟩
  · norm_num at hcap
    exact hcap
  · intro i j hij hc
    have hh := hcolor i j hij hc
    norm_num at hh
    simpa only [hdir,geometry,div_eq_mul_inv,mul_comm,one_mul] using hh
  · intro i
    apply card_pos.mp
    have hSi : (0:ℝ) < (S i).card := by exact_mod_cast card_pos.mpr (hne i)
    have hGi : (0:ℝ) < (G.shade i).card := (div_pos hSi (by norm_num)).trans_le (hcard i)
    exact_mod_cast hGi

end
end KakeyaFormal.SelectedSlabGeometry

#print axioms KakeyaFormal.SelectedSlabGeometry.common_color_separation
#print axioms KakeyaFormal.SelectedSlabGeometry.common_color_count
#print axioms KakeyaFormal.SelectedSlabGeometry.cap_coefficient_ge_one
#print axioms KakeyaFormal.SelectedSlabGeometry.selected_group_geometry
