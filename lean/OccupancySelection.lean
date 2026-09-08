import Finite
import MeasurableOccupancy

/-!
Actual finite dyadic-class selection and integer trimming for Section 8.1.
Class labels and selected subsets are constructed from the weights. The analytic
Kakeya estimate, Euclidean cell-count bound, and logarithmic asymptotics remain
outside this module.
-/
namespace KakeyaFormal.OccupancySelection
open Finset
open scoped BigOperators
noncomputable section

/-- A finite dyadic cover of an arbitrary positive real interval, including
its top endpoint. No discretization or positive lower integer bound is assumed. -/
theorem dyadic_cover {lo x : ℝ} (hlo : 0 < lo) (hx : lo ≤ x) (J : ℕ)
    (htop : x ≤ lo * (2 : ℝ) ^ J) :
    ∃ j ≤ J, lo * (2 : ℝ) ^ j ≤ x ∧ x < 2 * (lo * (2 : ℝ) ^ j) := by
  have hex : ∃ j : ℕ, j ≤ J ∧ x < lo * (2 : ℝ) ^ (j + 1) := by
    refine ⟨J, le_rfl, ?_⟩
    rw [pow_succ]
    nlinarith [mul_pos hlo (pow_pos (by norm_num : (0 : ℝ) < 2) J)]
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  refine ⟨j, hj.1, ?_, ?_⟩
  · by_cases hz : j = 0
    · simpa [hz] using hx
    · have hprev := Nat.find_min hex (show j - 1 < j by dsimp [j] at hz ⊢; omega)
      have hnot : ¬ x < lo * (2 : ℝ) ^ ((j - 1) + 1) := by
        intro hh
        exact hprev ⟨by omega, hh⟩
      have hid : j - 1 + 1 = j := by omega
      simpa [hid] using le_of_not_gt hnot
  · have hh := hj.2
    rw [pow_succ] at hh
    nlinarith

/-- Weighted pigeonhole on a supplied finite classification; the selected
fiber is produced, and its loss is exactly the number of classes. -/
theorem weighted_class_selection {Q : Type*} (S : Finset Q) (f : Q → ℝ)
    {B : ℕ} (hB : 0 < B) (label : Q → Fin B) :
    ∃ j : Fin B, (∑ q ∈ S, f q) / B ≤ ∑ q ∈ S with label q = j, f q := by
  classical
  let _ : NeZero B := ⟨hB.ne'⟩
  have hn : ((univ : Finset (Fin B)).card : ℝ) * ((∑ q ∈ S, f q) / B) = ∑ q ∈ S, f q := by
    simp only [card_univ, Fintype.card_fin]
    field_simp
  obtain ⟨j, hj, hmass⟩ := exists_le_sum_fiber_of_maps_to_of_nsmul_le_sum
    (s := S) (t := (univ : Finset (Fin B))) (f := label) (w := f)
    (fun _ _ => mem_univ _) univ_nonempty (b := (∑ q ∈ S, f q) / B)
    (by simpa only [nsmul_eq_mul] using hn.le)
  exact ⟨j, hmass⟩

/-- Construct a dyadic occupancy or tube-mass class from the actual real
weights `w`; select it by a possibly different incidence mass `f`. -/
theorem weighted_dyadic_selection {Q : Type*} (S : Finset Q) (w f : Q → ℝ)
    {lo : ℝ} (hlo : 0 < lo) (J : ℕ)
    (hlower : ∀ q ∈ S, lo ≤ w q)
    (hupper : ∀ q ∈ S, w q ≤ lo * (2 : ℝ) ^ J) :
    ∃ j ≤ J, ∃ R : Finset Q, R ⊆ S ∧
      (∀ q ∈ R, lo * (2 : ℝ) ^ j ≤ w q ∧ w q < 2 * (lo * (2 : ℝ) ^ j)) ∧
      (∑ q ∈ S, f q) / (J + 1 : ℕ) ≤ ∑ q ∈ R, f q := by
  classical
  have hex (q : Q) (hq : q ∈ S) := dyadic_cover hlo (hlower q hq) J (hupper q hq)
  let label : Q → Fin (J + 1) := fun q =>
    if hq : q ∈ S then ⟨Classical.choose (hex q hq), by have := (Classical.choose_spec (hex q hq)).1; omega⟩
    else ⟨0, by omega⟩
  have hlabel (q : Q) (hq : q ∈ S) :
      lo * (2 : ℝ) ^ (label q).val ≤ w q ∧
      w q < 2 * (lo * (2 : ℝ) ^ (label q).val) := by
    simpa only [label, dif_pos hq] using (Classical.choose_spec (hex q hq)).2
  obtain ⟨j, hj⟩ := weighted_class_selection S f (by omega : 0 < J + 1) label
  refine ⟨j.val, by omega, S.filter (fun q => label q = j), filter_subset _ _, ?_, hj⟩
  intro q hq
  obtain ⟨hqS, hqj⟩ := mem_filter.mp hq
  simpa [hqj] using hlabel q hqS

/-- Actual threshold pruning of tube masses: removing masses below total/(2M)
loses at most half the total. This is a selection theorem, not an assumed bound. -/
theorem half_mass_pruning {T : Type*} [Fintype T] (a : T → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hT : 0 < Fintype.card T) :
    let good := (univ : Finset T).filter (fun t => (∑ u, a u) / (2 * (Fintype.card T : ℝ)) ≤ a t)
    (∑ t, a t) / 2 ≤ ∑ t ∈ good, a t := by
  classical
  intro good
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset T)
    (fun t => (∑ u, a u) / (2 * (Fintype.card T : ℝ)) ≤ a t) a
  have hbad : (∑ t ∈ univ with ¬ (∑ u, a u) / (2 * (Fintype.card T : ℝ)) ≤ a t, a t) ≤
      (∑ t, a t) / 2 := by
    calc
      (∑ t ∈ univ with ¬ (∑ u, a u) / (2 * (Fintype.card T : ℝ)) ≤ a t, a t) ≤
          ∑ _t : T, (∑ u, a u) / (2 * (Fintype.card T : ℝ)) := by
        rw [sum_filter]
        apply sum_le_sum
        intro t ht
        split_ifs with h
        · exact div_nonneg (sum_nonneg (fun u _ => ha u)) (by positivity)
        · exact (lt_of_not_ge h).le
      _ = _ := by simp; field_simp
  change (∑ t, a t) / 2 ≤ ∑ t ∈ univ with (∑ u, a u) / (2 * (Fintype.card T : ℝ)) ≤ a t, a t
  linarith


/-- Construct a comparable tube-mass class after actual threshold pruning.
The number retained and their mass range are quantitative consequences. -/
theorem tube_mass_class {T : Type*} [Fintype T] (a : T → ℝ)
    (ha : ∀ t, 0 ≤ a t) (hT : 0 < Fintype.card T) (hpositive : 0 < ∑ t, a t)
    {upper : ℝ} (hupper : ∀ t, a t ≤ upper) (J : ℕ)
    (hclasses : upper ≤ ((∑ t, a t) / (2 * (Fintype.card T : ℝ))) * (2 : ℝ) ^ J) :
    ∃ j ≤ J, ∃ selected : Finset T, selected.Nonempty ∧
      (∀ t ∈ selected,
        ((∑ u, a u) / (2 * (Fintype.card T : ℝ))) * (2 : ℝ) ^ j ≤ a t ∧
        a t < 2 * (((∑ u, a u) / (2 * (Fintype.card T : ℝ))) * (2 : ℝ) ^ j)) ∧
      (∑ t, a t) ≤ 2 * (J + 1 : ℕ) * (∑ t ∈ selected, a t) ∧
      (∑ t, a t) ≤ 2 * (J + 1 : ℕ) * upper * (selected.card : ℝ) := by
  classical
  let lo := (∑ u, a u) / (2 * (Fintype.card T : ℝ))
  have hlo : 0 < lo := div_pos hpositive (by exact_mod_cast (show 0 < 2 * Fintype.card T by omega))
  let good := (univ : Finset T).filter (fun t => lo ≤ a t)
  have hhalf : (∑ t, a t) / 2 ≤ ∑ t ∈ good, a t := half_mass_pruning a ha hT
  obtain ⟨j,hj,selected,hsub,hrange,hmass⟩ := weighted_dyadic_selection good a a hlo J
    (fun t ht => (mem_filter.mp ht).2)
    (fun t _ => (hupper t).trans hclasses)
  have hJ : (0 : ℝ) < (J + 1 : ℕ) := by positivity
  have hmult := (div_le_iff₀ hJ).mp hmass
  have hret : (∑ t, a t) ≤ 2 * (J + 1 : ℕ) * (∑ t ∈ selected, a t) := by nlinarith
  have hnonempty : selected.Nonempty := by
    by_contra h
    have he : selected = ∅ := not_nonempty_iff_eq_empty.mp h
    simp only [he, sum_empty, mul_zero] at hret
    linarith
  have hcount : (∑ t ∈ selected, a t) ≤ upper * (selected.card : ℝ) := by
    calc
      (∑ t ∈ selected, a t) ≤ ∑ _t ∈ selected, upper := sum_le_sum (fun t _ => hupper t)
      _ = _ := by simp [mul_comm]
  refine ⟨j,hj,selected,hnonempty,hrange,hret,?_⟩
  have hh := mul_le_mul_of_nonneg_left hcount (by positivity : (0 : ℝ) ≤ 2 * (J + 1 : ℕ))
  nlinarith

/-- Every selected tube is actually trimmed to the same positive integer
cardinality, chosen as the minimum available cardinality. No integer trimming
or comparable count hypothesis is assumed. -/
theorem uniform_integer_trim {T Q : Type*} (selected : Finset T) (hne : selected.Nonempty)
    (cells : T → Finset Q) {lower : ℝ} (hlower : 0 < lower)
    (hcount : ∀ t ∈ selected, lower ≤ (cells t).card) :
    ∃ K : ℕ, 0 < K ∧ lower ≤ (K : ℝ) ∧ ∃ Y : T → Finset Q,
      (∀ t ∈ selected, Y t ⊆ cells t ∧ (Y t).card = K) ∧
      (∀ t, t ∉ selected → Y t = ∅) := by
  classical
  obtain ⟨t₀,ht₀,hmin⟩ := selected.exists_min_image (fun t => (cells t).card) hne
  let K := (cells t₀).card
  have hKlower : lower ≤ (K : ℝ) := hcount t₀ ht₀
  have hK : 0 < K := by exact_mod_cast (show (0 : ℝ) < K from hlower.trans_le hKlower)
  have hex (t : T) (ht : t ∈ selected) : ∃ s ⊆ cells t, s.card = K :=
    exists_subset_card_eq (hmin t ht)
  let Y : T → Finset Q := fun t => if ht : t ∈ selected then Classical.choose (hex t ht) else ∅
  refine ⟨K,hK,hKlower,Y,?_,?_⟩
  · intro t ht
    simpa only [Y, dif_pos ht] using Classical.choose_spec (hex t ht)
  · intro t ht
    simp only [Y, dif_neg ht]

open MeasureTheory Set KakeyaFormal.Occupancy

/-- A dyadic occupancy class is selected by the actual measurable tube-incidence
mass. Its lower occupancy controls ambient union volume, and its upper occupancy
will control the number of positive incidences per tube. -/
theorem measurable_occupancy_class {X T : Type*} [MeasurableSpace X] [Fintype T]
    {Q : ℕ} {μ : Measure X} (C : CellSystem μ Q) (U : Set X)
    (hU : MeasurableSet U) (hcover : U ⊆ C.covered) (Y : T → Set X)
    (hY : ∀ t, MeasurableSet (Y t)) (S : Finset (Fin Q))
    {V lo : ℝ} (hV : 0 < V) (hlo : 0 < lo) (hvol : ∀ q, μ.real (C.cell q) = V)
    (J : ℕ) (htop : 1 ≤ lo * (2 : ℝ) ^ J)
    (hlower : ∀ q ∈ S, lo ≤ C.cellMass U q / V) :
    ∃ j ≤ J, ∃ R : Finset (Fin Q), R ⊆ S ∧
      (∀ q ∈ R, (lo * (2 : ℝ) ^ j) * V ≤ C.cellMass U q ∧
        C.cellMass U q < 2 * ((lo * (2 : ℝ) ^ j) * V)) ∧
      (∑ t, μ.real (Y t ∩ ⋃ q ∈ S, C.cell q)) / (J + 1 : ℕ) ≤
        ∑ t, μ.real (Y t ∩ ⋃ q ∈ R, C.cell q) ∧
      ((lo * (2 : ℝ) ^ j) * V) * (R.card : ℝ) ≤ μ.real U := by
  classical
  obtain ⟨j,hj,R,hRS,hocc,hmass⟩ := weighted_dyadic_selection S
    (fun q => C.cellMass U q / V) (fun q => ∑ t, C.cellMass (Y t) q) hlo J hlower
    (fun q _ => ((C.normalized_occupancy U q hV (hvol q)).2).trans htop)
  have hcell (q : Fin Q) (hq : q ∈ R) :
      (lo * (2 : ℝ) ^ j) * V ≤ C.cellMass U q ∧
      C.cellMass U q < 2 * ((lo * (2 : ℝ) ^ j) * V) := by
    have hh := hocc q hq
    constructor
    · exact (le_div_iff₀ hV).mp hh.1
    · have hlt := (div_lt_iff₀ hV).mp hh.2
      nlinarith
  refine ⟨j,hj,R,hRS,hcell,?_, C.occupancy_union_lower hU hcover R (fun q hq => (hcell q hq).1)⟩
  simp_rw [C.class_mass _ (hY _)]
  rw [sum_comm, sum_comm (s := (univ : Finset T)) (t := R)]
  exact hmass

/-- After selecting an occupancy class, construct a tube-mass class and equal
integer shadings directly from positive-measure cell incidences. -/
theorem measurable_tube_class_and_trim {X T : Type*} [MeasurableSpace X] [Fintype T]
    {Q : ℕ} {μ : Measure X} (C : CellSystem μ Q) (U : Set X) (Y : T → Set X)
    (hY : ∀ t, MeasurableSet (Y t)) (hYU : ∀ t, Y t ⊆ U)
    (R : Finset (Fin Q)) {v upper : ℝ} (hv : 0 < v)
    (hocc : ∀ q ∈ R, C.cellMass U q ≤ 2 * v)
    (hT : 0 < Fintype.card T)
    (hpositive : 0 < ∑ t, μ.real (Y t ∩ ⋃ q ∈ R, C.cell q))
    (hupper : ∀ t, μ.real (Y t ∩ ⋃ q ∈ R, C.cell q) ≤ upper)
    (J : ℕ)
    (hclasses : upper ≤ ((∑ t, μ.real (Y t ∩ ⋃ q ∈ R, C.cell q)) /
      (2 * (Fintype.card T : ℝ))) * (2 : ℝ) ^ J) :
    ∃ selected : Finset T, selected.Nonempty ∧ ∃ j ≤ J, ∃ K : ℕ, 0 < K ∧
      ((∑ t, μ.real (Y t ∩ ⋃ q ∈ R, C.cell q)) / (2 * (Fintype.card T : ℝ))) /
        (2 * v) ≤ (K : ℝ) ∧
      (∑ t, μ.real (Y t ∩ ⋃ q ∈ R, C.cell q)) ≤
        2 * (J + 1 : ℕ) * upper * (selected.card : ℝ) ∧
      (∀ t ∈ selected,
        ((∑ u, μ.real (Y u ∩ ⋃ q ∈ R, C.cell q)) / (2 * (Fintype.card T : ℝ))) *
          (2 : ℝ) ^ j ≤ μ.real (Y t ∩ ⋃ q ∈ R, C.cell q) ∧
        μ.real (Y t ∩ ⋃ q ∈ R, C.cell q) <
          2 * (((∑ u, μ.real (Y u ∩ ⋃ q ∈ R, C.cell q)) / (2 * (Fintype.card T : ℝ))) *
            (2 : ℝ) ^ j)) ∧
      ∃ Z : T → Finset (Fin Q),
        (∀ t ∈ selected, Z t ⊆ C.positiveCells (Y t) R ∧ (Z t).card = K) ∧
        (∀ t, t ∉ selected → Z t = ∅) := by
  classical
  let a : T → ℝ := fun t => μ.real (Y t ∩ ⋃ q ∈ R, C.cell q)
  let lo := (∑ t, a t) / (2 * (Fintype.card T : ℝ))
  have hlo : 0 < lo := div_pos hpositive (by exact_mod_cast (show 0 < 2 * Fintype.card T by omega))
  obtain ⟨j,hj,selected,hne,hrange,hmass,hcount⟩ := tube_mass_class a
    (fun _ => measureReal_nonneg) hT hpositive hupper J hclasses
  have hcard (t : T) (ht : t ∈ selected) : lo / (2 * v) ≤ (C.positiveCells (Y t) R).card := by
    have hscale : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hlow : lo ≤ a t := by
      have hh := (hrange t ht).1
      have hm := mul_le_mul_of_nonneg_left hscale hlo.le
      nlinarith
    have hmass := C.occupied_count_from_mass (hY t) (hYU t) R hocc
    apply (div_le_iff₀ (by positivity : 0 < 2 * v)).mpr
    dsimp [a] at hlow
    nlinarith
  obtain ⟨K,hK,hKlower,Z,hZ,hzero⟩ := uniform_integer_trim selected hne
    (fun t => C.positiveCells (Y t) R) (div_pos hlo (by positivity)) hcard
  exact ⟨selected,hne,j,hj,K,hK,hKlower,hcount,hrange,Z,hZ,hzero⟩


section Combined
variable {X T : Type*} [MeasurableSpace X] [Fintype T]
variable {Q : ℕ} {μ : Measure X}

def restrictedMass (C : CellSystem μ Q) (Y : T → Set X) (S : Finset (Fin Q)) (t : T) : ℝ :=
  μ.real (Y t ∩ ⋃ q ∈ S, C.cell q)
def incidenceMass (C : CellSystem μ Q) (Y : T → Set X) (S : Finset (Fin Q)) : ℝ :=
  ∑ t, restrictedMass C Y S t

/-- The surviving cell family is an actual occupancy threshold filter. -/
def highOccupancyCells (C : CellSystem μ Q) (U : Set X) (lo V : ℝ) : Finset (Fin Q) := by
  classical
  exact univ.filter (fun q => lo ≤ C.cellMass U q / V)

/-- Removing the actual low-occupancy filter loses at most `lo * V * K`
from each measurable shading with at most K positive cell incidences. -/
theorem low_occupancy_pruning (C : CellSystem μ Q) (U Y : Set X)
    (hY : MeasurableSet Y) (hYU : Y ⊆ U) (hcover : U ⊆ C.covered)
    {lo V K : ℝ} (hlo : 0 ≤ lo) (hV : 0 < V)
    (hcount : ((C.positiveCells Y univ).card : ℝ) ≤ K) :
    μ.real Y - lo * V * K ≤ μ.real (Y ∩ ⋃ q ∈ highOccupancyCells C U lo V, C.cell q) := by
  classical
  let bad := univ.filter (fun q => ¬ lo ≤ C.cellMass U q / V)
  have hbadupper (q : Fin Q) (hq : q ∈ bad) : C.cellMass U q ≤ lo * V := by
    exact ((div_lt_iff₀ hV).mp (lt_of_not_ge (mem_filter.mp hq).2)).le
  have hbadsub : C.positiveCells Y bad ⊆ C.positiveCells Y univ := by
    intro q hq
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hq).2⟩
  have hbadcount : ((C.positiveCells Y bad).card : ℝ) ≤ K :=
    (show ((C.positiveCells Y bad).card : ℝ) ≤ (C.positiveCells Y univ).card by
      exact_mod_cast Finset.card_le_card hbadsub).trans hcount
  have hloss := C.low_occupancy_loss hY hYU bad (mul_nonneg hlo hV.le) hbadupper hbadcount
  have hsplit := sum_filter_add_sum_filter_not (univ : Finset (Fin Q))
    (fun q => lo ≤ C.cellMass U q / V) (C.cellMass Y)
  rw [C.class_mass bad hY] at hloss
  rw [C.class_mass _ hY, C.mass_decomposition hY (hYU.trans hcover)]
  change (∑ q, C.cellMass Y q) - lo * V * K ≤
    ∑ q ∈ univ with lo ≤ C.cellMass U q / V, C.cellMass Y q
  linarith

/-- The full output of common occupancy-class selection, tube-mass-class
selection, and equal integer trimming. Density is not assumed to be at most one:
the integer count may exceed N by a geometric normalization constant. -/
structure CommonIntegerSelection (C : CellSystem μ Q) (U : Set X) (Y : T → Set X)
    (S : Finset (Fin Q)) (V lo upper : ℝ) (Jocc Jtube : ℕ) where
  occupancyIndex : Fin (Jocc + 1)
  cells : Finset (Fin Q)
  cells_subset : cells ⊆ S
  occupancy_range : ∀ q ∈ cells,
    ((lo * (2 : ℝ) ^ occupancyIndex.val) * V) ≤ C.cellMass U q ∧
    C.cellMass U q < 2 * ((lo * (2 : ℝ) ^ occupancyIndex.val) * V)
  selected : Finset T
  selected_nonempty : selected.Nonempty
  tubeIndex : Fin (Jtube + 1)
  tube_mass_range : ∀ t ∈ selected,
    (incidenceMass C Y cells / (2 * (Fintype.card T : ℝ))) * (2 : ℝ) ^ tubeIndex.val ≤
      restrictedMass C Y cells t ∧
    restrictedMass C Y cells t <
      2 * ((incidenceMass C Y cells / (2 * (Fintype.card T : ℝ))) * (2 : ℝ) ^ tubeIndex.val)
  count : ℕ
  count_positive : 0 < count
  count_lower : ((incidenceMass C Y S / (Jocc + 1 : ℕ)) / (2 * (Fintype.card T : ℝ))) /
    (2 * ((lo * (2 : ℝ) ^ occupancyIndex.val) * V)) ≤ (count : ℝ)
  tube_count_lower : incidenceMass C Y S ≤
    2 * (Jocc + 1 : ℕ) * (Jtube + 1 : ℕ) * upper * (selected.card : ℝ)
  shades : T → Finset (Fin Q)
  shades_subset : ∀ t ∈ selected, shades t ⊆ C.positiveCells (Y t) cells
  shades_card : ∀ t ∈ selected, (shades t).card = count
  shades_zero : ∀ t, t ∉ selected → shades t = ∅
  union_volume : ((lo * (2 : ℝ) ^ occupancyIndex.val) * V) *
    ((selected.biUnion shades).card : ℝ) ≤ μ.real U

/-- End-to-end measurable finite selection: neither common class nor equal
integer shading is assumed. The two explicit class counts determine all losses. -/
theorem exists_common_integer_selection (C : CellSystem μ Q) (U : Set X)
    (hU : MeasurableSet U) (hcover : U ⊆ C.covered) (Y : T → Set X)
    (hY : ∀ t, MeasurableSet (Y t)) (hYU : ∀ t, Y t ⊆ U)
    (S : Finset (Fin Q)) {V lo upper : ℝ} (hV : 0 < V) (hlo : 0 < lo)
    (hvol : ∀ q, μ.real (C.cell q) = V) (Jocc Jtube : ℕ)
    (htop : 1 ≤ lo * (2 : ℝ) ^ Jocc)
    (hlower : ∀ q ∈ S, lo ≤ C.cellMass U q / V)
    (hT : 0 < Fintype.card T) (hpositive : 0 < incidenceMass C Y S)
    (hupper : ∀ t, restrictedMass C Y S t ≤ upper)
    (hclasses : upper ≤ ((incidenceMass C Y S / (Jocc + 1 : ℕ)) /
      (2 * (Fintype.card T : ℝ))) * (2 : ℝ) ^ Jtube) :
    Nonempty (CommonIntegerSelection C U Y S V lo upper Jocc Jtube) := by
  classical
  obtain ⟨j,hj,R,hRS,hocc,hret,hvolume⟩ := measurable_occupancy_class C U hU hcover Y hY
    S hV hlo hvol Jocc htop hlower
  let v := (lo * (2 : ℝ) ^ j) * V
  have hv : 0 < v := mul_pos (mul_pos hlo (pow_pos (by norm_num) j)) hV
  have hret' : incidenceMass C Y S / (Jocc + 1 : ℕ) ≤ incidenceMass C Y R := hret
  have hRpositive : 0 < incidenceMass C Y R :=
    (div_pos hpositive (by positivity : (0 : ℝ) < (Jocc + 1 : ℕ))).trans_le hret'
  have hRupper (t : T) : restrictedMass C Y R t ≤ upper := by
    apply le_trans ?_ (hupper t)
    dsimp [restrictedMass]
    rw [C.class_mass R (hY t), C.class_mass S (hY t)]
    exact sum_le_sum_of_subset_of_nonneg hRS (fun q _ _ => C.cellMass_nonneg (Y t) q)
  have hRclasses : upper ≤ (incidenceMass C Y R / (2 * (Fintype.card T : ℝ))) * (2 : ℝ) ^ Jtube := by
    have hd := div_le_div_of_nonneg_right hret' (by positivity : (0 : ℝ) ≤ 2 * (Fintype.card T : ℝ))
    exact hclasses.trans (mul_le_mul_of_nonneg_right hd (by positivity))
  obtain ⟨selected,hne,k,hk,K,hK,hKlower,hcount,hrange,Z,hZ,hzero⟩ :=
    measurable_tube_class_and_trim C U Y hY hYU R hv
      (fun q hq => (hocc q hq).2.le) hT hRpositive hRupper Jtube hRclasses
  have hd := div_le_div_of_nonneg_right hret' (by positivity : (0 : ℝ) ≤ 2 * (Fintype.card T : ℝ))
  have hKlower' : ((incidenceMass C Y S / (Jocc + 1 : ℕ)) / (2 * (Fintype.card T : ℝ))) /
      (2 * v) ≤ (K : ℝ) :=
    (div_le_div_of_nonneg_right hd (by positivity : (0 : ℝ) ≤ 2 * v)).trans hKlower
  have hcount' : incidenceMass C Y S ≤
      2 * (Jocc + 1 : ℕ) * (Jtube + 1 : ℕ) * upper * (selected.card : ℝ) := by
    have hw := (div_le_iff₀ (by positivity : (0 : ℝ) < (Jocc + 1 : ℕ))).mp hret'
    have hcountR : incidenceMass C Y R ≤ 2 * (Jtube + 1 : ℕ) * upper * (selected.card : ℝ) := hcount
    have hm := mul_le_mul_of_nonneg_left hcountR (by positivity : (0 : ℝ) ≤ (Jocc + 1 : ℕ))
    nlinarith
  have hunion : selected.biUnion Z ⊆ R := by
    intro q hq
    obtain ⟨t,ht,hqt⟩ := mem_biUnion.mp hq
    have hc := (hZ t ht).1 hqt
    exact (mem_filter.mp hc).1
  have hunionvol : v * ((selected.biUnion Z).card : ℝ) ≤ μ.real U :=
    C.occupancy_union_lower hU hcover (selected.biUnion Z) (fun q hq => (hocc q (hunion hq)).1)
  exact ⟨{
    occupancyIndex := ⟨j, by omega⟩
    cells := R
    cells_subset := hRS
    occupancy_range := hocc
    selected := selected
    selected_nonempty := hne
    tubeIndex := ⟨k, by omega⟩
    tube_mass_range := hrange
    count := K
    count_positive := hK
    count_lower := hKlower'
    tube_count_lower := hcount'
    shades := Z
    shades_subset := fun t ht => (hZ t ht).1
    shades_card := fun t ht => (hZ t ht).2
    shades_zero := hzero
    union_volume := hunionvol
  }⟩

/-- Section 8.1's finite measurable assembly, including actual low-occupancy
removal. A uniform cell-incidence count K and the explicit cutoff budget imply
that every original tube keeps at least half its required mass before class
selection. The class hypotheses are quantitative, not hidden good-class inputs. -/
theorem high_occupancy_integer_selection (C : CellSystem μ Q) (U : Set X)
    (hU : MeasurableSet U) (hcover : U ⊆ C.covered) (Y : T → Set X)
    (hY : ∀ t, MeasurableSet (Y t)) (hYU : ∀ t, Y t ⊆ U)
    {V lo base upper K : ℝ} (hV : 0 < V) (hlo : 0 < lo) (hbase : 0 < base)
    (hvol : ∀ q, μ.real (C.cell q) = V)
    (hT : 0 < Fintype.card T) (hmass : ∀ t, base ≤ μ.real (Y t))
    (hupper : ∀ t, μ.real (Y t) ≤ upper)
    (hcount : ∀ t, ((C.positiveCells (Y t) univ).card : ℝ) ≤ K)
    (hcutoff : lo * V * K ≤ base / 2) (Jocc Jtube : ℕ)
    (htop : 1 ≤ lo * (2 : ℝ) ^ Jocc)
    (hclasses : upper ≤ (base / (4 * (Jocc + 1 : ℕ))) * (2 : ℝ) ^ Jtube) :
    (∀ t, base / 2 ≤ restrictedMass C Y (highOccupancyCells C U lo V) t) ∧
    (Fintype.card T : ℝ) * base / 2 ≤ incidenceMass C Y (highOccupancyCells C U lo V) ∧
    Nonempty (CommonIntegerSelection C U Y (highOccupancyCells C U lo V)
      V lo upper Jocc Jtube) := by
  classical
  let S := highOccupancyCells C U lo V
  have hret (t : T) : base / 2 ≤ restrictedMass C Y S t := by
    have hh := low_occupancy_pruning C U (Y t) (hY t) (hYU t) hcover hlo.le hV (hcount t)
    change μ.real (Y t) - lo * V * K ≤ restrictedMass C Y S t at hh
    linarith [hmass t]
  have htotal : (Fintype.card T : ℝ) * base / 2 ≤ incidenceMass C Y S := by
    have hh := sum_le_sum (fun t (_ : t ∈ (univ : Finset T)) => hret t)
    simpa only [sum_const, card_univ, nsmul_eq_mul, incidenceMass, mul_div_assoc] using hh
  have hpositive : 0 < incidenceMass C Y S :=
    (div_pos (mul_pos (by exact_mod_cast hT) hbase) (by norm_num)).trans_le htotal
  have hrestricted (t : T) : restrictedMass C Y S t ≤ upper := by
    apply le_trans ?_ (hupper t)
    exact measureReal_mono Set.inter_subset_left
      (measure_ne_top_of_subset ((hYU t).trans hcover) C.covered_finite)
  have hclass : upper ≤ ((incidenceMass C Y S / (Jocc + 1 : ℕ)) /
      (2 * (Fintype.card T : ℝ))) * (2 : ℝ) ^ Jtube := by
    have hM : (0 : ℝ) < Fintype.card T := by exact_mod_cast hT
    have hB : (0 : ℝ) < (Jocc + 1 : ℕ) := by positivity
    have hbase' : base / (4 * (Jocc + 1 : ℕ)) ≤
        (incidenceMass C Y S / (Jocc + 1 : ℕ)) / (2 * (Fintype.card T : ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (Fintype.card T : ℝ))).mpr
      apply (le_div_iff₀ hB).mpr
      field_simp
      nlinarith
    exact hclasses.trans (mul_le_mul_of_nonneg_right hbase' (by positivity))
  exact ⟨hret, htotal, exists_common_integer_selection C U hU hcover Y hY hYU S hV hlo
    hvol Jocc Jtube htop (fun q hq => (mem_filter.mp hq).2) hT hpositive hrestricted hclass⟩

/-- Positive cutoff and tube mass parameters always admit finite dyadic class
budgets. This existence statement makes no logarithmic asymptotic claim. -/
theorem finite_class_budgets {lo base upper : ℝ} (hlo : 0 < lo) (hbase : 0 < base) :
    ∃ Jocc Jtube : ℕ, 1 ≤ lo * (2 : ℝ) ^ Jocc ∧
      upper ≤ (base / (4 * (Jocc + 1 : ℕ))) * (2 : ℝ) ^ Jtube := by
  obtain ⟨Jocc,hJ⟩ := pow_unbounded_of_one_lt (1 / lo) (by norm_num : (1 : ℝ) < 2)
  have htop : 1 ≤ lo * (2 : ℝ) ^ Jocc := by
    have hh := (div_lt_iff₀ hlo).mp hJ
    nlinarith
  have hb : 0 < base / (4 * (Jocc + 1 : ℕ)) := div_pos hbase (by positivity)
  obtain ⟨Jtube,hT⟩ := pow_unbounded_of_one_lt (upper / (base / (4 * (Jocc + 1 : ℕ))))
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨Jocc,Jtube,htop,?_⟩
  have hh := (div_lt_iff₀ hb).mp hT
  nlinarith

end Combined

/-- Optional normalization: trim further to at most N cells, preserving an
explicit clamped lower bound. This never silently identifies K/N with a density
at most one when the original common count K may exceed N. -/
theorem uniform_integer_trim_capped {T Q : Type*} (selected : Finset T) (hne : selected.Nonempty)
    (cells : T → Finset Q) {lower : ℝ} (hlower : 0 < lower)
    (hcount : ∀ t ∈ selected, lower ≤ (cells t).card) (N : ℕ) (hN : 0 < N) :
    ∃ K : ℕ, 0 < K ∧ K ≤ N ∧ min lower (N : ℝ) ≤ (K : ℝ) ∧
      ∃ Y : T → Finset Q, (∀ t ∈ selected, Y t ⊆ cells t ∧ (Y t).card = K) ∧
        (∀ t, t ∉ selected → Y t = ∅) := by
  classical
  obtain ⟨K,hK,hKlower,Z,hZ,hzero⟩ := uniform_integer_trim selected hne cells hlower hcount
  let K' := min K N
  have hK' : 0 < K' := lt_min hK hN
  have hK'lower : min lower (N : ℝ) ≤ (K' : ℝ) := by
    dsimp [K']
    rw [Nat.cast_min]
    exact min_le_min hKlower le_rfl
  have hex (t : T) (ht : t ∈ selected) : ∃ s ⊆ cells t, s.card = K' := by
    have hbound : K' ≤ (cells t).card :=
      (min_le_left K N).trans (by rw [← (hZ t ht).2]; exact card_le_card (hZ t ht).1)
    exact exists_subset_card_eq hbound
  let Y : T → Finset Q := fun t => if ht : t ∈ selected then Classical.choose (hex t ht) else ∅
  refine ⟨K',hK',min_le_right _ _,hK'lower,Y,?_,?_⟩
  · intro t ht
    simpa only [Y, dif_pos ht] using Classical.choose_spec (hex t ht)
  · intro t ht
    simp only [Y, dif_neg ht]

theorem capped_density_bounds {K N : ℕ} (hK : 0 < K) (hKN : K ≤ N) :
    0 < (K : ℝ) / N ∧ (K : ℝ) / N ≤ 1 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hK.trans_le hKN
  constructor
  · exact div_pos (by exact_mod_cast hK) hN
  · exact (div_le_one hN).mpr (by exact_mod_cast hKN)

end
end KakeyaFormal.OccupancySelection

-- Kernel dependency audit: only Lean standard logical axioms are expected.
#print axioms KakeyaFormal.OccupancySelection.dyadic_cover
#print axioms KakeyaFormal.OccupancySelection.weighted_class_selection
#print axioms KakeyaFormal.OccupancySelection.weighted_dyadic_selection
#print axioms KakeyaFormal.OccupancySelection.half_mass_pruning
#print axioms KakeyaFormal.OccupancySelection.tube_mass_class
#print axioms KakeyaFormal.OccupancySelection.uniform_integer_trim
#print axioms KakeyaFormal.OccupancySelection.measurable_occupancy_class
#print axioms KakeyaFormal.OccupancySelection.measurable_tube_class_and_trim
#print axioms KakeyaFormal.OccupancySelection.low_occupancy_pruning
#print axioms KakeyaFormal.OccupancySelection.exists_common_integer_selection
#print axioms KakeyaFormal.OccupancySelection.high_occupancy_integer_selection
#print axioms KakeyaFormal.OccupancySelection.finite_class_budgets
#print axioms KakeyaFormal.OccupancySelection.uniform_integer_trim_capped
#print axioms KakeyaFormal.OccupancySelection.capped_density_bounds
