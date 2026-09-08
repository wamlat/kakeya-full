import Mathlib

/-! Measure-theoretic occupancy identities for actual finite measurable cell
partitions. These statements prove the count/volume and density conversions;
selection of a common dyadic occupancy and tube-density class remains separate. -/

open MeasureTheory Set
open scoped ENNReal
namespace KakeyaFormal.Occupancy

variable {X : Type*} [MeasurableSpace X] {Q : ℕ} {μ : Measure X}

structure CellSystem (μ : Measure X) (Q : ℕ) where
  cell : Fin Q → Set X
  measurable : ∀ q, MeasurableSet (cell q)
  disjoint : Pairwise (fun q r => Disjoint (cell q) (cell r))
  finite : ∀ q, μ (cell q) ≠ ∞

namespace CellSystem

noncomputable def covered (C : CellSystem μ Q) : Set X := ⋃ q, C.cell q

noncomputable def cellMass (C : CellSystem μ Q) (Y : Set X) (q : Fin Q) : ℝ :=
  μ.real (Y ∩ C.cell q)

theorem covered_finite (C : CellSystem μ Q) : μ C.covered ≠ ∞ := by
  simpa only [covered, Set.biUnion_univ] using
    measure_biUnion_ne_top (μ := μ) (s := Set.univ) (f := C.cell)
      (Set.toFinite _) (fun q _ => C.finite q)

theorem cellMass_nonneg (C : CellSystem μ Q) (Y : Set X) (q : Fin Q) :
    0 ≤ C.cellMass Y q := measureReal_nonneg

theorem cellMass_mono (C : CellSystem μ Q) {Y Z : Set X} (h : Y ⊆ Z) (q : Fin Q) :
    C.cellMass Y q ≤ C.cellMass Z q :=
  measureReal_mono (Set.inter_subset_inter_left _ h)
    (measure_ne_top_of_subset Set.inter_subset_right (C.finite q))

theorem cellMass_le_volume (C : CellSystem μ Q) (Y : Set X) (q : Fin Q) :
    C.cellMass Y q ≤ μ.real (C.cell q) :=
  measureReal_mono Set.inter_subset_right (C.finite q)

/-- Exact decomposition, with all measure finiteness and measurability checked. -/
theorem mass_decomposition (C : CellSystem μ Q) {Y : Set X}
    (hY : MeasurableSet Y) (hcover : Y ⊆ C.covered) :
    μ.real Y = ∑ q, C.cellMass Y q := by
  have heq : (⋃ q ∈ (Finset.univ : Finset (Fin Q)), Y ∩ C.cell q) = Y := by
    ext x
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left, Set.mem_inter_iff]
    constructor
    · rintro ⟨q,hx,_⟩
      exact hx
    · intro hx
      obtain ⟨q,hq⟩ := Set.mem_iUnion.mp (hcover hx)
      exact ⟨q,hx,hq⟩
  have hdec := measureReal_biUnion_finset (μ := μ)
    (s := Finset.univ) (f := fun q => Y ∩ C.cell q)
    (fun q _ r _ hqr => (C.disjoint hqr).mono Set.inter_subset_right Set.inter_subset_right)
    (fun q _ => hY.inter (C.measurable q))
    (fun q _ => measure_ne_top_of_subset Set.inter_subset_right (C.finite q))
  simpa only [heq, cellMass] using hdec

/-- Restricting a shading to selected cells exactly restricts its finite mass sum. -/
theorem class_mass (C : CellSystem μ Q) (S : Finset (Fin Q)) {Y : Set X}
    (hY : MeasurableSet Y) :
    μ.real (Y ∩ ⋃ q ∈ S, C.cell q) = ∑ q ∈ S, C.cellMass Y q := by
  have heq : (Y ∩ ⋃ q ∈ S, C.cell q) = ⋃ q ∈ S, Y ∩ C.cell q := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    aesop
  have hdec := measureReal_biUnion_finset (μ := μ)
    (s := S) (f := fun q => Y ∩ C.cell q)
    (fun q _ r _ hqr => (C.disjoint hqr).mono Set.inter_subset_right Set.inter_subset_right)
    (fun q _ => hY.inter (C.measurable q))
    (fun q _ => measure_ne_top_of_subset Set.inter_subset_right (C.finite q))
  simpa only [heq, cellMass] using hdec

/-- A lower occupancy in every selected cell turns union count into actual volume. -/
theorem occupancy_union_lower (C : CellSystem μ Q) {Y : Set X}
    (hY : MeasurableSet Y) (hcover : Y ⊆ C.covered)
    (S : Finset (Fin Q)) {v : ℝ} (hlower : ∀ q ∈ S, v ≤ C.cellMass Y q) :
    v * (S.card : ℝ) ≤ μ.real Y := by
  have hsum : v * (S.card : ℝ) ≤ ∑ q ∈ S, C.cellMass Y q := by
    calc
      _ = ∑ _q ∈ S, v := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hlower
  rw [← C.class_mass S hY] at hsum
  exact hsum.trans (measureReal_mono Set.inter_subset_left
    (measure_ne_top_of_subset hcover C.covered_finite))

noncomputable def positiveCells (C : CellSystem μ Q) (Y : Set X)
    (S : Finset (Fin Q)) : Finset (Fin Q) := by
  classical
  exact S.filter (fun q => 0 < C.cellMass Y q)

/-- Zero-volume incidences contribute exactly zero, even when the sets are nonempty. -/
theorem sum_positiveCells (C : CellSystem μ Q) (Y : Set X) (S : Finset (Fin Q)) :
    (∑ q ∈ C.positiveCells Y S, C.cellMass Y q) = ∑ q ∈ S, C.cellMass Y q := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq hnot
  have hn : ¬ 0 < C.cellMass Y q := by
    intro hp
    exact hnot (Finset.mem_filter.mpr ⟨hq,hp⟩)
  exact le_antisymm (le_of_not_gt hn) (C.cellMass_nonneg Y q)

/-- Filling positive incidences with whole cells yields the required density lower
bound from the upper occupancy of the ambient union. -/
theorem occupied_count_from_mass (C : CellSystem μ Q) {Y U : Set X}
    (hY : MeasurableSet Y) (hYU : Y ⊆ U) (S : Finset (Fin Q)) {v : ℝ}
    (hupper : ∀ q ∈ S, C.cellMass U q ≤ v) :
    μ.real (Y ∩ ⋃ q ∈ S, C.cell q) ≤ v * ((C.positiveCells Y S).card : ℝ) := by
  classical
  rw [C.class_mass S hY, ← C.sum_positiveCells Y S]
  calc
    _ ≤ ∑ _q ∈ C.positiveCells Y S, v := by
      apply Finset.sum_le_sum
      intro q hq
      exact (C.cellMass_mono hYU q).trans (hupper q (Finset.mem_filter.mp hq).1)
    _ = _ := by simp [mul_comm]

/-- Uniform cell volume bounds every normalized occupancy between zero and one. -/
theorem normalized_occupancy (C : CellSystem μ Q) (U : Set X) (q : Fin Q)
    {V : ℝ} (hV : 0 < V) (hvol : μ.real (C.cell q) = V) :
    0 ≤ C.cellMass U q / V ∧ C.cellMass U q / V ≤ 1 := by
  refine ⟨div_nonneg (C.cellMass_nonneg U q) hV.le, ?_⟩
  apply (div_le_one hV).mpr
  rw [← hvol]
  exact C.cellMass_le_volume U q

/-- Low-occupancy cells remove at most threshold times the number of actually
positive incidences. A geometric tube-count theorem can be substituted for K. -/
theorem low_occupancy_loss (C : CellSystem μ Q) {Y U : Set X}
    (hY : MeasurableSet Y) (hYU : Y ⊆ U) (S : Finset (Fin Q))
    {v K : ℝ} (hv : 0 ≤ v)
    (hupper : ∀ q ∈ S, C.cellMass U q ≤ v)
    (hcount : ((C.positiveCells Y S).card : ℝ) ≤ K) :
    μ.real (Y ∩ ⋃ q ∈ S, C.cell q) ≤ v*K :=
  (C.occupied_count_from_mass hY hYU S hupper).trans
    (mul_le_mul_of_nonneg_left hcount hv)

end CellSystem
end KakeyaFormal.Occupancy
