import DiscreteMeasurable
import AngularDecomposition

/-! Actual tube density selection, whole-cell marking, pointwise broadness
recovery, and two-ends inheritance after arbitrary finite shading deletion. -/
namespace KakeyaFormal.DensityBroadnessRecovery
open Finset AngularDecomposition
open scoped BigOperators
noncomputable section
open Classical

/-- Actual incident original tube indices at a cell. -/
def row {k M : ℕ} (O : Fin M → Finset (Cell k)) (S : Finset (Fin M)) (z : Cell k) :
    Finset (Fin M) := S.filter fun i => z ∈ O i

def cells {k M : ℕ} (O : Fin M → Finset (Cell k)) : Finset (Cell k) := univ.biUnion O

def good {k M : ℕ} (O : Fin M → Finset (Cell k)) (δ eta lam : ℝ) : Finset (Fin M) :=
  univ.filter fun i => eta*lam/2 ≤ δ*((O i).card : ℝ)

def marked {k M : ℕ} (O : Fin M → Finset (Cell k)) (δ eta lam : ℝ) : Finset (Cell k) :=
  (cells O).filter fun z => (eta/8)*((row O univ z).card : ℝ) ≤
    ((row O (good O δ eta lam) z).card : ℝ)

/-- Exact finite incidence double counting for an arbitrary set of tube rows. -/
theorem incidence_sum {k M : ℕ} (O : Fin M → Finset (Cell k)) (S : Finset (Fin M))
    (U : Finset (Cell k)) (hU : ∀ i ∈ S, O i ⊆ U) :
    (∑ z ∈ U, (row O S z).card) = ∑ i ∈ S, (O i).card := by
  have hid (i : Fin M) (hi : i ∈ S) : U.filter (fun z => z ∈ O i) = O i := by
    ext z
    simp only [mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨hU i hi h,h⟩⟩
  calc
    _ = ∑ i ∈ S, (U.filter (fun z => z ∈ O i)).card := by
      simpa only [row,bipartiteAbove,bipartiteBelow] using
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := U) (t := S) (fun z i => z ∈ O i))
    _ = _ := sum_congr rfl fun i hi => congrArg card (hid i hi)

/-- Selecting tubes above half the retained average preserves the stated mass
and tube count, even though the original outputs may have empty shadings. -/
theorem good_mass_and_count {k M : ℕ} (O : Fin M → Finset (Cell k))
    {δ eta lam : ℝ} (heta : 0 < eta) (hlam : 0 < lam)
    (hupper : ∀ i, δ*((O i).card : ℝ) ≤ 2*lam)
    (hmass : eta*lam*M ≤ δ*∑ i, ((O i).card : ℝ)) :
    eta*lam*(M : ℝ)/2 ≤ δ*∑ i ∈ good O δ eta lam, ((O i).card : ℝ) ∧
      eta*(M : ℝ)/4 ≤ ((good O δ eta lam).card : ℝ) := by
  let a := eta*lam/2
  have hbad : (∑ i ∈ (univ : Finset (Fin M)).filter (fun i => ¬a ≤ δ*((O i).card : ℝ)),
      δ*((O i).card : ℝ)) ≤ a*(M : ℝ) := by
    calc
      _ ≤ ∑ _i ∈ (univ : Finset (Fin M)).filter (fun i => ¬a ≤ δ*((O i).card : ℝ)), a :=
        sum_le_sum fun i hi => (lt_of_not_ge (mem_filter.mp hi).2).le
      _ = a*(((univ : Finset (Fin M)).filter (fun i => ¬a ≤ δ*((O i).card : ℝ))).card : ℝ) := by simp [mul_comm]
      _ ≤ a*(M : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast (show ((univ : Finset (Fin M)).filter (fun i => ¬a ≤ δ*((O i).card : ℝ))).card ≤ M by simpa using card_filter_le (univ : Finset (Fin M)) (fun i => ¬a ≤ δ*((O i).card : ℝ)))) (by dsimp [a]; positivity)
  have hsplit := sum_filter_add_sum_filter_not (s := (univ : Finset (Fin M)))
    (fun i => a ≤ δ*((O i).card : ℝ)) (fun i => δ*((O i).card : ℝ))
  have hgood : eta*lam*(M : ℝ)/2 ≤ δ*∑ i ∈ good O δ eta lam, ((O i).card : ℝ) := by
    simp only [← mul_sum] at hsplit
    change (δ*∑ i ∈ good O δ eta lam, ((O i).card : ℝ)) + _ = _ at hsplit
    rw [← mul_sum] at hbad
    dsimp [a] at hbad hsplit
    linarith
  refine ⟨hgood,?_⟩
  have hgupper : δ*∑ i ∈ good O δ eta lam, ((O i).card : ℝ) ≤
      2*lam*((good O δ eta lam).card : ℝ) := by
    rw [mul_sum]
    exact (sum_le_sum (fun i _ => hupper i)).trans_eq (by simp [mul_comm])
  apply (mul_le_mul_iff_left₀ hlam).mp
  nlinarith [hgood.trans hgupper]

/-- Cell marking preserves at least half the incidence on the selected tubes.
The removed good mass is controlled by the actual pre-selection multiplicity. -/
theorem marked_mass {k M : ℕ} (O : Fin M → Finset (Cell k))
    {δ eta lam : ℝ} (hδ : 0 < δ) (heta : 0 < eta) (hlam : 0 < lam)
    (hupper : ∀ i, δ*((O i).card : ℝ) ≤ 2*lam)
    (hmass : eta*lam*M ≤ δ*∑ i, ((O i).card : ℝ)) :
    (∑ i ∈ good O δ eta lam, ((O i).card : ℝ))/2 ≤
      ∑ z ∈ marked O δ eta lam, ((row O (good O δ eta lam) z).card : ℝ) := by
  let U := cells O
  let S := good O δ eta lam
  have hU (i : Fin M) : O i ⊆ U := fun _ h => mem_biUnion.mpr ⟨i,mem_univ _,h⟩
  have hfull : (∑ z ∈ U, ((row O univ z).card : ℝ)) = ∑ i, ((O i).card : ℝ) := by
    exact_mod_cast incidence_sum O univ U (fun i _ => hU i)
  have hgood : (∑ z ∈ U, ((row O S z).card : ℝ)) = ∑ i ∈ S, ((O i).card : ℝ) := by
    exact_mod_cast incidence_sum O S U (fun i _ => hU i)
  have hbad : (∑ z ∈ U.filter (fun z => ¬(eta/8)*((row O univ z).card : ℝ) ≤ ((row O S z).card : ℝ)),
      ((row O S z).card : ℝ)) ≤ (eta/8)*∑ i, ((O i).card : ℝ) := by
    calc
      _ ≤ ∑ z ∈ U.filter (fun z => ¬(eta/8)*((row O univ z).card : ℝ) ≤ ((row O S z).card : ℝ)),
          (eta/8)*((row O univ z).card : ℝ) :=
        sum_le_sum fun z hz => (lt_of_not_ge (mem_filter.mp hz).2).le
      _ ≤ ∑ z ∈ U, (eta/8)*((row O univ z).card : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ = _ := by rw [← mul_sum,hfull]
  have hsplit := sum_filter_add_sum_filter_not (s := U)
    (fun z => (eta/8)*((row O univ z).card : ℝ) ≤ ((row O S z).card : ℝ))
    (fun z => ((row O S z).card : ℝ))
  rw [hgood] at hsplit
  change (∑ z ∈ marked O δ eta lam, ((row O S z).card : ℝ)) + _ = _ at hsplit
  have htotal : δ*∑ i, ((O i).card : ℝ) ≤ 2*lam*M := by
    rw [mul_sum]
    exact (sum_le_sum (fun i _ => hupper i)).trans_eq (by simp [mul_comm])
  have hgoodlower := (good_mass_and_count O heta hlam hupper hmass).1
  have hbδ := mul_le_mul_of_nonneg_left hbad hδ.le
  have htotδ := mul_le_mul_of_nonneg_left htotal (show 0 ≤ eta/8 by positivity)
  apply (mul_le_mul_iff_left₀ hδ).mp
  dsimp [S] at hsplit hgoodlower ⊢
  nlinarith



def selectedIndex {k M : ℕ} (O : Fin M → Finset (Cell k)) (δ eta lam : ℝ) :
    Fin (good O δ eta lam).card → Fin M := fun i => ((good O δ eta lam).equivFin.symm i).val

def selectedFamily {k M : ℕ} (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    (δ eta lam : ℝ) : TubeFamily k (good O δ eta lam).card :=
  ⟨fun i => F.tube (selectedIndex O δ eta lam i),fun i => O (selectedIndex O δ eta lam i)⟩

theorem selectedIndex_injective {k M : ℕ} (O : Fin M → Finset (Cell k)) (δ eta lam : ℝ) :
    Function.Injective (selectedIndex O δ eta lam) :=
  Subtype.val_injective.comp (good O δ eta lam).equivFin.symm.injective

theorem selectedIndex_mem {k M : ℕ} (O : Fin M → Finset (Cell k)) (δ eta lam : ℝ)
    (i : Fin (good O δ eta lam).card) : selectedIndex O δ eta lam i ∈ good O δ eta lam :=
  ((good O δ eta lam).equivFin.symm i).property

theorem selected_row_image {k M : ℕ} (O : Fin M → Finset (Cell k)) (δ eta lam : ℝ) (z : Cell k) :
    (row (fun i => O (selectedIndex O δ eta lam i)) univ z).image (selectedIndex O δ eta lam) =
      row O (good O δ eta lam) z := by
  ext i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact mem_filter.mpr ⟨selectedIndex_mem O δ eta lam j,(mem_filter.mp hj).2⟩
  · intro hi
    have hg := (mem_filter.mp hi).1
    let j := (good O δ eta lam).equivFin ⟨i,hg⟩
    have hj : selectedIndex O δ eta lam j = i := by simp [selectedIndex,j]
    exact mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,by simpa only [hj] using (mem_filter.mp hi).2⟩,hj⟩

theorem selected_row_card {k M : ℕ} (O : Fin M → Finset (Cell k)) (δ eta lam : ℝ) (z : Cell k) :
    (row (fun i => O (selectedIndex O δ eta lam i)) univ z).card =
      (row O (good O δ eta lam) z).card := by
  rw [← selected_row_image O δ eta lam z,card_image_of_injective _ (selectedIndex_injective O δ eta lam)]

/-- Broadness transfers to the actual reindexed retained directions on every
marked cell, with exactly the reciprocal proportional loss 8/eta. -/
theorem selected_broad {k M : ℕ} (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    {δ eta lam beta tau K : ℝ} (hδ : 0 ≤ δ) (heta : 0 < eta) (htau : 0 < tau) (hK : 0 ≤ K)
    (hbroad : ∀ z ∈ cells O, Broad F (row O univ z) δ beta tau K)
    {z : Cell k} (hz : z ∈ marked O δ eta lam) :
    Broad (selectedFamily F O δ eta lam)
      (row (fun i => O (selectedIndex O δ eta lam i)) univ z) δ beta tau (K*(8/eta)) := by
  have hmark := (mem_filter.mp hz).2
  have hpop : ((row O univ z).card : ℝ) ≤ (8/eta)*((row O (good O δ eta lam) z).card : ℝ) := by
    calc
      _ ≤ (8*((row O (good O δ eta lam) z).card : ℝ))/eta := (le_div_iff₀ heta).mpr (by nlinarith)
      _ = _ := by ring
  have hsub : row O (good O δ eta lam) z ⊆ row O univ z := filter_subset_filter _ (subset_univ _)
  have hbr := broad_proportional_subset F hsub hδ htau hK hpop (hbroad z (mem_filter.mp hz).1)
  intro center r hr
  have hid : (cap (selectedFamily F O δ eta lam)
      (row (fun i => O (selectedIndex O δ eta lam i)) univ z) center r).image (selectedIndex O δ eta lam) =
        cap F (row O (good O δ eta lam) z) center r := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨selectedIndex_mem O δ eta lam j,
        (mem_filter.mp (mem_filter.mp hj).1).2⟩,(mem_filter.mp hj).2⟩
    · intro hi
      obtain ⟨j,hj,he⟩ := mem_image.mp (by rw [selected_row_image]; exact (mem_filter.mp hi).1 :
        i ∈ (row (fun i => O (selectedIndex O δ eta lam i)) univ z).image (selectedIndex O δ eta lam))
      exact mem_image.mpr ⟨j,mem_filter.mpr ⟨hj,by simpa only [selectedFamily,he] using (mem_filter.mp hi).2⟩,he⟩
  have hcard := congrArg card hid
  rw [card_image_of_injective _ (selectedIndex_injective O δ eta lam)] at hcard
  rw [hcard,selected_row_card]
  exact hbr center r hr


/-- Actual proportional retention gives the cardinality ratio needed to inherit
two-ends estimates from the original tube shading. -/
theorem original_card_ratio {k M : ℕ} (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    {δ eta lam : ℝ} (hδ : 0 < δ) (heta : 0 < eta)
    (hupper : ∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam)
    (i : Fin (good O δ eta lam).card) :
    ((F.shade (selectedIndex O δ eta lam i)).card : ℝ) ≤
      (4/eta)*((O (selectedIndex O δ eta lam i)).card : ℝ) := by
  have hlo := (mem_filter.mp (selectedIndex_mem O δ eta lam i)).2
  have hhi := hupper (selectedIndex O δ eta lam i)
  have hm := mul_le_mul_of_nonneg_left hhi heta.le
  have hmul : ((F.shade (selectedIndex O δ eta lam i)).card : ℝ)*eta ≤
      4*((O (selectedIndex O δ eta lam i)).card : ℝ) := by
    apply (mul_le_mul_iff_left₀ hδ).mp
    nlinarith
  calc
    _ ≤ (4*((O (selectedIndex O δ eta lam i)).card : ℝ))/eta := (le_div_iff₀ heta).mpr hmul
    _ = _ := by ring

/-- Original finite physical-ball two-ends bounds pass to the actual selected
full shadings with the explicit factor 4/eta. -/
theorem selected_two_ends {k M : ℕ} (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    {δ eta lam alpha B : ℝ} (hδ : 0 < δ) (heta : 0 < eta) (hB : 0 ≤ B)
    (hsub : ∀ i, O i ⊆ F.shade i)
    (hupper : ∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun q => dist (cellCenter δ q) x ≤ r)).card : ℝ) ≤
        B*r^alpha*((F.shade i).card : ℝ)) :
    ∀ i x r, δ ≤ r → r ≤ 1 →
      (((O (selectedIndex O δ eta lam i)).filter (fun q => dist (cellCenter δ q) x ≤ r)).card : ℝ) ≤
        (B*(4/eta))*r^alpha*((O (selectedIndex O δ eta lam i)).card : ℝ) := by
  intro i x r hr hr1
  have hc : (((O (selectedIndex O δ eta lam i)).filter (fun q => dist (cellCenter δ q) x ≤ r)).card : ℝ) ≤
      (((F.shade (selectedIndex O δ eta lam i)).filter (fun q => dist (cellCenter δ q) x ≤ r)).card : ℝ) := by
    exact_mod_cast card_le_card (filter_subset_filter _ (hsub _))
  have hh := mul_le_mul_of_nonneg_left (original_card_ratio F O hδ heta hupper i)
    (mul_nonneg hB (Real.rpow_nonneg (hδ.le.trans hr) alpha))
  exact (hc.trans (hends _ x r hr hr1)).trans (by convert hh using 1; ring)

/-- Reindexing preserves the exact full incidence mass and marked multiplicity. -/
theorem selected_mass {k M : ℕ} (O : Fin M → Finset (Cell k)) (δ eta lam : ℝ) :
    (∑ i, ((O (selectedIndex O δ eta lam i)).card : ℝ)) =
      ∑ i ∈ good O δ eta lam, ((O i).card : ℝ) := by
  let e : {i // i ∈ good O δ eta lam} ≃ Fin (good O δ eta lam).card := (good O δ eta lam).equivFin
  have hh := e.symm.sum_comp (fun i : {i // i ∈ good O δ eta lam} => ((O i.val).card : ℝ))
  exact hh.trans (Finset.sum_subtype (good O δ eta lam) (fun _ => Iff.rfl) (fun i => ((O i).card : ℝ))).symm


/-- Every marked cell genuinely meets a retained full shading. -/
theorem marked_subset_union {k M : ℕ} (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    {δ eta lam : ℝ} (heta : 0 < eta) :
    marked O δ eta lam ⊆ (selectedFamily F O δ eta lam).unionCells := by
  intro z hz
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp (mem_filter.mp hz).1
  have hrow : 0 < ((row O univ z).card : ℝ) := by
    exact_mod_cast card_pos.mpr (show (row O univ z).Nonempty from ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩)
  have hgood : 0 < ((row O (good O δ eta lam) z).card : ℝ) :=
    (mul_pos (by positivity : 0 < eta/8) hrow).trans_le (mem_filter.mp hz).2
  rw [← selected_row_card O δ eta lam z] at hgood
  obtain ⟨j,hj⟩ := card_pos.mp (show 0 < (row (fun i => O (selectedIndex O δ eta lam i)) univ z).card by exact_mod_cast hgood)
  exact mem_biUnion.mpr ⟨j,mem_univ _,(mem_filter.mp hj).2⟩

/-- Marked incidence is exactly the sum of the actual marked shading cardinalities. -/
theorem marked_shading_mass {k M : ℕ} (O : Fin M → Finset (Cell k)) (δ eta lam : ℝ) :
    (∑ i, ((O (selectedIndex O δ eta lam i) ∩ marked O δ eta lam).card : ℝ)) =
      ∑ z ∈ marked O δ eta lam,
        ((row (fun i => O (selectedIndex O δ eta lam i)) univ z).card : ℝ) := by
  have hh := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := (univ : Finset (Fin (good O δ eta lam).card))) (t := marked O δ eta lam)
    (fun i z => z ∈ O (selectedIndex O δ eta lam i))
  have hid (i : Fin (good O δ eta lam).card) :
      (marked O δ eta lam).filter (fun z => z ∈ O (selectedIndex O δ eta lam i)) =
        O (selectedIndex O δ eta lam i) ∩ marked O δ eta lam := by ext z; simp [and_comm]
  simp only [bipartiteAbove,bipartiteBelow,hid] at hh
  exact_mod_cast hh

/-- Complete constructive density, marking and broadness recovery. The full
selected shading is retained separately from its marked subset; only total
marked incidence is required, not a per-tube marked density. -/
theorem recover {k M : ℕ} (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    {δ eta lam beta tau K alpha B : ℝ}
    (hδ : 0 < δ) (heta : 0 < eta) (hlam : 0 < lam) (htau : 0 < tau)
    (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hsub : ∀ i, O i ⊆ F.shade i)
    (hupper : ∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam)
    (hmass : eta*lam*M ≤ δ*∑ i, ((O i).card : ℝ))
    (hbroad : ∀ z ∈ cells O, Broad F (row O univ z) δ beta tau K)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun q => dist (cellCenter δ q) x ≤ r)).card : ℝ) ≤
        B*r^alpha*((F.shade i).card : ℝ)) :
    let N := (good O δ eta lam).card
    let e := selectedIndex O δ eta lam
    let G := selectedFamily F O δ eta lam
    let Z := marked O δ eta lam
    Function.Injective e ∧ eta*(M : ℝ)/4 ≤ (N : ℝ) ∧
    (∀ i, G.tube i = F.tube (e i) ∧ G.shade i ⊆ F.shade (e i) ∧
      eta*lam/2 ≤ δ*((G.shade i).card : ℝ) ∧ δ*((G.shade i).card : ℝ) ≤ 2*lam) ∧
    eta*lam*(M : ℝ)/2 ≤ δ*∑ i, ((G.shade i).card : ℝ) ∧
    Z ⊆ G.unionCells ∧
    (∑ i, ((G.shade i).card : ℝ))/2 ≤ ∑ i, ((G.shade i ∩ Z).card : ℝ) ∧
    (∀ z ∈ Z, Broad G (row G.shade univ z) δ beta tau (K*(8/eta))) ∧
    (∀ i x r, δ ≤ r → r ≤ 1 →
      (((G.shade i).filter (fun q => dist (cellCenter δ q) x ≤ r)).card : ℝ) ≤
        (B*(4/eta))*r^alpha*((G.shade i).card : ℝ)) := by
  intro N e G Z
  have hOupper (i : Fin M) : δ*((O i).card : ℝ) ≤ 2*lam :=
    (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card (hsub i)) hδ.le).trans (hupper i)
  obtain ⟨hgoodmass,hN⟩ := good_mass_and_count O heta hlam hOupper hmass
  refine ⟨selectedIndex_injective O δ eta lam,hN,?_,?_,marked_subset_union F O heta,?_,?_,?_⟩
  · intro i
    exact ⟨rfl,hsub _,(mem_filter.mp (selectedIndex_mem O δ eta lam i)).2,hOupper _⟩
  · change eta*lam*(M : ℝ)/2 ≤ δ*∑ i, ((O (selectedIndex O δ eta lam i)).card : ℝ)
    rw [selected_mass]
    exact hgoodmass
  · change (∑ i, ((O (selectedIndex O δ eta lam i)).card : ℝ))/2 ≤
      ∑ i, ((O (selectedIndex O δ eta lam i) ∩ marked O δ eta lam).card : ℝ)
    rw [selected_mass,marked_shading_mass]
    simp_rw [selected_row_card]
    exact marked_mass O hδ heta hlam hOupper hmass
  · intro z hz
    exact selected_broad F O hδ.le heta htau hK hbroad hz
  · exact selected_two_ends F O hδ heta hB hsub hupper hends

/-- The recovery's injective tube restriction preserves all remaining geometric
hypotheses for direct downstream use. -/
theorem selected_geometry {k M : ℕ} (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    (δ eta lam : ℝ) {width sep R m A : ℝ}
    (hsub : ∀ i, O i ⊆ F.shade i)
    (hadm : F.Admissible width δ) (hsep : F.Separated sep)
    (hbounded : F.Bounded R) (hcap : F.CapBound δ m A) :
    (selectedFamily F O δ eta lam).Admissible width δ ∧
    (selectedFamily F O δ eta lam).Separated sep ∧
    (selectedFamily F O δ eta lam).Bounded R ∧
    (selectedFamily F O δ eta lam).CapBound δ m A := by
  refine ⟨?_,DiscreteMeasurable.injective_tube_restriction F (selectedFamily F O δ eta lam)
    (selectedIndex O δ eta lam) (selectedIndex_injective O δ eta lam) (fun _ => rfl) hsep hbounded hcap⟩
  intro i q hq
  exact hadm _ q (hsub _ hq)

end
end KakeyaFormal.DensityBroadnessRecovery

#print axioms KakeyaFormal.DensityBroadnessRecovery.marked_mass
#print axioms KakeyaFormal.DensityBroadnessRecovery.recover
#print axioms KakeyaFormal.DensityBroadnessRecovery.selected_geometry
