import Mathlib

/-!
# Arbitrary finite-arity laminar selection and finite thinning

This file constructs actual subsets respecting all capacities in a finite rooted
partition. Internal nodes may have any finite number of children; their supports
must be pairwise disjoint. Nothing assumes the desired integral rounding.
The direction-space geometry needed to construct such a partition is separate.
-/
namespace KakeyaVerification.CapSelection

inductive CapacityTree (α : Type*) where
  | leaf (points : Finset α) (capacity : ℕ)
  | node (arity : ℕ) (children : Fin arity → CapacityTree α) (capacity : ℕ)

variable {α : Type*} [DecidableEq α]

namespace CapacityTree

def support : CapacityTree α → Finset α
  | .leaf points _ => points
  | .node _ children _ => Finset.univ.biUnion fun i => (children i).support

def rank : CapacityTree α → ℕ
  | .leaf points capacity => min capacity points.card
  | .node _ children capacity => min capacity (∑ i, (children i).rank)

def Partitioned : CapacityTree α → Prop
  | .leaf _ _ => True
  | .node _ children _ =>
      (∀ i, (children i).Partitioned) ∧
      (Pairwise fun i j => Disjoint (children i).support (children j).support)

def Admissible : CapacityTree α → Finset α → Prop
  | .leaf _ capacity, selected => selected.card ≤ capacity
  | .node _ children capacity, selected =>
      selected.card ≤ capacity ∧
      ∀ i, (children i).Admissible (selected ∩ (children i).support)

def Feasible (weight : α → ℝ) : CapacityTree α → Prop
  | .leaf points capacity => ∑ x ∈ points, weight x ≤ (capacity : ℝ)
  | .node _ children capacity =>
      (∑ x ∈ Finset.univ.biUnion (fun i => (children i).support), weight x)
        ≤ (capacity : ℝ) ∧
      ∀ i, (children i).Feasible weight

/-- All upper capacities survive deleting selected elements. -/
theorem admissible_mono (tree : CapacityTree α) {small large : Finset α}
    (hsub : small ⊆ large) (hlarge : tree.Admissible large) :
    tree.Admissible small := by
  induction tree generalizing small large with
  | leaf points capacity => exact (Finset.card_le_card hsub).trans hlarge
  | node arity children capacity ih =>
    exact ⟨(Finset.card_le_card hsub).trans hlarge.1,
      fun i => ih i (Finset.inter_subset_inter hsub (by rfl)) (hlarge.2 i)⟩

/-- The union of disjoint component selections restricts to precisely its component. -/
theorem union_inter_component {ι : Type*} [Fintype ι] [DecidableEq ι]
    (parts selected : ι → Finset α)
    (hparts : Pairwise fun i j => Disjoint (parts i) (parts j))
    (hsub : ∀ i, selected i ⊆ parts i) (i : ι) :
    (Finset.univ.biUnion selected) ∩ parts i = selected i := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨j, hxj⟩, hxi⟩
    by_cases hji : j = i
    · simpa [hji] using hxj
    · exact False.elim ((Finset.disjoint_left.mp (hparts hji)) (hsub j hxj) hxi)
  · intro hxi
    exact ⟨⟨i, hxi⟩, hsub i hxi⟩

/-- Actual finite-set construction for a partition tree of arbitrary finite arity. -/
theorem attainsRank (tree : CapacityTree α) (htree : tree.Partitioned) :
    ∃ selected ⊆ tree.support, tree.Admissible selected ∧ selected.card = tree.rank := by
  classical
  induction tree with
  | leaf points capacity =>
    obtain ⟨selected, hsub, hcard⟩ :=
      Finset.exists_subset_card_eq (s := points) (Nat.min_le_right capacity points.card)
    exact ⟨selected, hsub, by simp [Admissible, hcard],
      hcard⟩
  | node arity children capacity ih =>
    choose selections hsub hadm hcard using (fun i => ih i (htree.1 i))
    have hd : Pairwise fun i j => Disjoint (selections i) (selections j) := by
      intro i j hij
      exact (htree.2 hij).mono (hsub i) (hsub j)
    have hUcard : (Finset.univ.biUnion selections).card = ∑ i, (children i).rank := by
      rw [Finset.card_biUnion]
      · exact Finset.sum_congr rfl (fun i _ => hcard i)
      · intro i _ j _ hij
        exact hd hij
    have hbound : min capacity (∑ i, (children i).rank) ≤
        (Finset.univ.biUnion selections).card := by
      rw [hUcard]
      exact Nat.min_le_right _ _
    obtain ⟨selected, hsel, hselcard⟩ := Finset.exists_subset_card_eq hbound
    refine ⟨selected, ?_, ?_, hselcard⟩
    · exact hsel.trans (Finset.biUnion_mono fun i _ => hsub i)
    · constructor
      · rw [hselcard]
        exact Nat.min_le_left _ _
      · intro i
        apply (children i).admissible_mono _ (hadm i)
        have hinter := Finset.inter_subset_inter hsel (by rfl :
          (children i).support ⊆ (children i).support)
        rwa [union_inter_component (fun i => (children i).support) selections htree.2 hsub i]
          at hinter

/-- Every feasible fractional mass is at most the attainable integer rank. -/
theorem mass_le_rank (tree : CapacityTree α) (htree : tree.Partitioned)
    (weight : α → ℝ) (hupper : ∀ x ∈ tree.support, weight x ≤ 1)
    (hfeas : tree.Feasible weight) :
    (∑ x ∈ tree.support, weight x) ≤ (tree.rank : ℝ) := by
  induction tree with
  | leaf points capacity =>
    have hcard : (∑ x ∈ points, weight x) ≤ (points.card : ℝ) := by
      calc
        _ ≤ ∑ _x ∈ points, (1:ℝ) := Finset.sum_le_sum hupper
        _ = _ := by simp
    simpa [support, rank, Nat.cast_min] using le_min hfeas hcard
  | node arity children capacity ih =>
    have hsum : (∑ x ∈ Finset.univ.biUnion (fun i => (children i).support), weight x) ≤
        ((∑ i, (children i).rank : ℕ) : ℝ) := by
      rw [Finset.sum_biUnion]
      · rw [Nat.cast_sum]
        apply Finset.sum_le_sum
        intro i _
        apply ih i (htree.1 i) _ (hfeas.2 i)
        intro x hx
        exact hupper x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
      · intro i _ j _ hij
        exact htree.2 hij
    simpa [support, rank, Nat.cast_min] using le_min hfeas.1 hsum

/-- Integer rounding for a genuinely arbitrary finite rooted partition. -/
theorem fractionalSelection (tree : CapacityTree α) (htree : tree.Partitioned)
    (weight : α → ℝ) (hweight : ∀ x ∈ tree.support, 0 ≤ weight x ∧ weight x ≤ 1)
    (hfeas : tree.Feasible weight) :
    ∃ selected ⊆ tree.support, tree.Admissible selected ∧
      (∑ x ∈ tree.support, weight x) ≤ (selected.card : ℝ) := by
  obtain ⟨selected, hsub, hadm, hcard⟩ := tree.attainsRank htree
  refine ⟨selected, hsub, hadm, ?_⟩
  rw [hcard]
  exact tree.mass_le_rank htree weight (fun x hx => (hweight x hx).2) hfeas

def capacity : CapacityTree α → ℕ
  | .leaf _ cap => cap
  | .node _ _ cap => cap

/-- A constrained block actually occurring in the hierarchy. -/
inductive Occurs : CapacityTree α → Finset α → ℕ → Prop
  | self (tree : CapacityTree α) : Occurs tree tree.support tree.capacity
  | child {arity : ℕ} {children : Fin arity → CapacityTree α} {cap : ℕ}
      (i : Fin arity) {block : Finset α} {bound : ℕ}
      (h : Occurs (children i) block bound) : Occurs (.node arity children cap) block bound

theorem occurs_subset {tree : CapacityTree α} {block : Finset α} {bound : ℕ}
    (h : tree.Occurs block bound) : block ⊆ tree.support := by
  induction h with
  | self tree => rfl
  | @child arity children cap i block bound h ih =>
    exact ih.trans (Finset.subset_biUnion_of_mem (fun j => (children j).support)
      (Finset.mem_univ i))

theorem admissible_card (tree : CapacityTree α) {selected : Finset α}
    (h : tree.Admissible selected) : selected.card ≤ tree.capacity := by
  cases tree with
  | leaf points cap => exact h
  | node arity children cap => exact h.1

/-- Every descendant's capacity is a concrete cardinality bound on the selected set. -/
theorem all_capacities {tree : CapacityTree α} {selected block : Finset α} {bound : ℕ}
    (h : tree.Occurs block bound) (hsel : selected ⊆ tree.support)
    (hadm : tree.Admissible selected) : (selected ∩ block).card ≤ bound := by
  induction h generalizing selected with
  | self tree =>
    rw [Finset.inter_eq_left.mpr hsel]
    exact tree.admissible_card hadm
  | @child arity children cap i block bound h ih =>
    have hb : block ⊆ (children i).support := occurs_subset h
    have hr := ih (Finset.inter_subset_right : selected ∩ (children i).support ⊆ _)
      (hadm.2 i)
    simpa only [Finset.inter_assoc, Finset.inter_eq_right.mpr hb] using hr

/-- Feasibility of constant fractional weights follows from exactly the stated
cardinality/capacity inequalities on every hierarchy block. -/
theorem uniform_feasible (tree : CapacityTree α) (rho : ℝ)
    (hbounds : ∀ block bound, tree.Occurs block bound →
      rho * (block.card : ℝ) ≤ (bound : ℝ)) :
    tree.Feasible (fun _ => rho) := by
  induction tree with
  | leaf points cap =>
    have h := hbounds points cap (.self (.leaf points cap))
    simpa [Feasible, mul_comm] using h
  | node arity children cap ih =>
    constructor
    · have h := hbounds _ _ (.self (.node arity children cap))
      simpa [support, capacity, mul_comm] using h
    · intro i
      exact ih i (fun block bound h => hbounds block bound (.child i h))

/-- Proportional retention with every hierarchy capacity enforced. -/
theorem uniformSelection (tree : CapacityTree α) (htree : tree.Partitioned)
    (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    (hbounds : ∀ block bound, tree.Occurs block bound →
      rho * (block.card : ℝ) ≤ (bound : ℝ)) :
    ∃ selected ⊆ tree.support,
      rho * (tree.support.card : ℝ) ≤ (selected.card : ℝ) ∧
      tree.Admissible selected ∧
      ∀ block bound, tree.Occurs block bound → (selected ∩ block).card ≤ bound := by
  obtain ⟨selected, hsub, hadm, hmass⟩ := tree.fractionalSelection htree (fun _ => rho)
    (fun _ _ => ⟨hrho, hrho1⟩) (tree.uniform_feasible rho hbounds)
  exact ⟨selected, hsub, by simpa [mul_comm] using hmass, hadm,
    fun _ _ h => all_capacities h hsub hadm⟩

/-- The inverse cap coefficient is lost exactly once. No repeated rounding is used. -/
theorem inverseCoefficientSelection (tree : CapacityTree α) (htree : tree.Partitioned)
    (A : ℝ) (hA : 1 ≤ A)
    (hbounds : ∀ block bound, tree.Occurs block bound →
      (block.card : ℝ) ≤ A * (bound : ℝ)) :
    ∃ selected ⊆ tree.support,
      (tree.support.card : ℝ) / A ≤ (selected.card : ℝ) ∧
      tree.Admissible selected ∧
      ∀ block bound, tree.Occurs block bound → (selected ∩ block).card ≤ bound := by
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hAinv : 1/A ≤ (1:ℝ) := (div_le_one hApos).mpr hA
  obtain ⟨selected, hsub, hmass, hadm, hall⟩ :=
    tree.uniformSelection htree (1/A) (le_of_lt (one_div_pos.mpr hApos)) hAinv
      (fun block bound h => by
        rw [one_div, ← div_eq_inv_mul]
        exact (div_le_iff₀ hApos).mpr (by simpa [mul_comm] using hbounds block bound h))
  exact ⟨selected, hsub, by simpa [one_div, div_eq_mul_inv, mul_comm] using hmass, hadm, hall⟩

/-- Capacity-one terminal cells contain at most one selected original element. -/
theorem terminal_unique {tree : CapacityTree α} {selected cell : Finset α}
    (hcell : tree.Occurs cell 1) (hsub : selected ⊆ tree.support)
    (hadm : tree.Admissible selected) {x y : α}
    (hx : x ∈ selected) (hxc : x ∈ cell) (hy : y ∈ selected) (hyc : y ∈ cell) : x = y :=
  Finset.card_le_one.mp (all_capacities hcell hsub hadm) x
    (Finset.mem_inter.mpr ⟨hx, hxc⟩) y (Finset.mem_inter.mpr ⟨hy, hyc⟩)


/-- Taking one finite color class costs at most the number of colors and preserves
all hierarchy capacities, because it only deletes elements. -/
theorem monochromaticSelection (tree : CapacityTree α)
    {selected : Finset α} (hsub : selected ⊆ tree.support)
    (hadm : tree.Admissible selected) {β : Type*} [Fintype β] [DecidableEq β]
    [Nonempty β] (color : α → β) :
    ∃ c : β, ∃ kept ⊆ selected,
      (selected.card : ℝ) / (Fintype.card β : ℝ) ≤ (kept.card : ℝ) ∧
      tree.Admissible kept ∧
      (∀ x ∈ kept, color x = c) ∧
      ∀ block bound, tree.Occurs block bound → (kept ∩ block).card ≤ bound := by
  have hn : (0:ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast Fintype.card_pos
  have hb : (Finset.univ : Finset β).card •
      ((selected.card : ℝ) / (Fintype.card β : ℝ)) ≤ (selected.card : ℝ) := by
    simp only [Finset.card_univ, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (ne_of_gt hn)]
  obtain ⟨c, _, hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := selected) (t := Finset.univ) (f := color)
    (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty hb
  let kept := selected.filter (fun x => color x = c)
  have hk : kept ⊆ selected := Finset.filter_subset _ _
  have ha : tree.Admissible kept := tree.admissible_mono hk hadm
  exact ⟨c, kept, hk, hc, ha, fun _ hx => (Finset.mem_filter.mp hx).2,
    fun _ _ h => all_capacities h (hk.trans hsub) ha⟩


/-- Combined finite thinning: one inverse-coefficient loss and one color loss. -/
theorem inverseCoefficientColorSelection (tree : CapacityTree α) (htree : tree.Partitioned)
    (A : ℝ) (hA : 1 ≤ A)
    (hbounds : ∀ block bound, tree.Occurs block bound →
      (block.card : ℝ) ≤ A * (bound : ℝ))
    {β : Type*} [Fintype β] [DecidableEq β] [Nonempty β] (color : α → β) :
    ∃ c : β, ∃ kept ⊆ tree.support,
      (tree.support.card : ℝ) / (A * (Fintype.card β : ℝ)) ≤ (kept.card : ℝ) ∧
      tree.Admissible kept ∧
      (∀ x ∈ kept, color x = c) ∧
      ∀ block bound, tree.Occurs block bound → (kept ∩ block).card ≤ bound := by
  obtain ⟨selected, hsub, hmass, hadm, _⟩ := tree.inverseCoefficientSelection htree A hA hbounds
  obtain ⟨c, kept, hk, hkmass, hkad, hc, hall⟩ :=
    tree.monochromaticSelection hsub hadm color
  have hn : (0:ℝ) < (Fintype.card β : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨c, kept, hk.trans hsub, ?_, hkad, hc, hall⟩
  calc
    _ = ((tree.support.card : ℝ) / A) / (Fintype.card β : ℝ) := by rw [div_div]
    _ ≤ (selected.card : ℝ) / (Fintype.card β : ℝ) := div_le_div_of_nonneg_right hmass hn.le
    _ ≤ _ := hkmass

/-- The capacity-one constraints for actual fibers make the cell map injective. -/
theorem terminal_fibers_injective (tree : CapacityTree α) {ι : Type*} [DecidableEq ι]
    (cell : α → ι)
    (hterminal : ∀ x ∈ tree.support,
      tree.Occurs (tree.support.filter (fun y => cell y = cell x)) 1)
    {selected : Finset α} (hsub : selected ⊆ tree.support) (hadm : tree.Admissible selected) :
    Set.InjOn cell (selected : Set α) := by
  intro x hx y hy hxy
  exact terminal_unique (hterminal x (hsub hx)) hsub hadm hx
    (Finset.mem_filter.mpr ⟨hsub hx, rfl⟩) hy
    (Finset.mem_filter.mpr ⟨hsub hy, hxy.symm⟩)

/-- Equal residues modulo three force distinct lattice coordinates to differ by at least three. -/
theorem coordinate_gap_of_same_residue {a b : ℤ} (hne : a ≠ b)
    (hc : (a : ZMod 3) = (b : ZMod 3)) : (3:ℤ) ≤ |a-b| := by
  have hdvd : (3:ℤ) ∣ a-b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a-b) 3).mp
    push_cast
    exact sub_eq_zero.mpr hc
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by
    intro hz
    have hab : a-b = 0 := by simpa [hz] using hk
    exact hne (sub_eq_zero.mp hab)
  rw [hk, abs_mul]
  norm_num
  nlinarith [Int.one_le_abs hk0]

omit [DecidableEq α] in
/-- A concrete modular coloring separates distinct occupied lattice cells. -/
theorem lattice_color_separates {dimension : ℕ} (cell : α → Fin dimension → ℤ)
    {selected : Finset α} (hinj : Set.InjOn cell (selected : Set α))
    {color : Fin dimension → ZMod 3}
    (hcolor : ∀ x ∈ selected, (fun i => (cell x i : ZMod 3)) = color)
    {x y : α} (hx : x ∈ selected) (hy : y ∈ selected) (hxy : x ≠ y) :
    ∃ i : Fin dimension, (3:ℤ) ≤ |cell x i - cell y i| := by
  classical
  have hfn : cell x ≠ cell y := fun h => hxy (hinj hx hy h)
  have hnall : ¬ ∀ i, cell x i = cell y i := fun h => hfn (funext h)
  obtain ⟨i, hi⟩ := not_forall.mp hnall
  refine ⟨i, coordinate_gap_of_same_residue hi ?_⟩
  exact congrFun ((hcolor x hx).trans (hcolor y hy).symm) i

/-- Finite direction-cell thinning with quantitative retention, all hierarchy
capacities, and actual lattice-index separation. Geometric charts and cap-to-cell
covering estimates are deliberately absent from the hypotheses and conclusion. -/
theorem latticeCellSelection (tree : CapacityTree α) (htree : tree.Partitioned)
    (A : ℝ) (hA : 1 ≤ A)
    (hbounds : ∀ block bound, tree.Occurs block bound →
      (block.card : ℝ) ≤ A * (bound : ℝ))
    {dimension : ℕ} (cell : α → Fin dimension → ℤ)
    (hterminal : ∀ x ∈ tree.support,
      tree.Occurs (tree.support.filter (fun y => cell y = cell x)) 1) :
    ∃ kept ⊆ tree.support,
      (tree.support.card : ℝ) / (A * (3:ℝ)^dimension) ≤ (kept.card : ℝ) ∧
      tree.Admissible kept ∧
      (∀ block bound, tree.Occurs block bound → (kept ∩ block).card ≤ bound) ∧
      ∀ x ∈ kept, ∀ y ∈ kept, x ≠ y →
        ∃ i : Fin dimension, (3:ℤ) ≤ |cell x i - cell y i| := by
  classical
  obtain ⟨color, kept, hk, hmass, hadm, hc, hall⟩ :=
    tree.inverseCoefficientColorSelection htree A hA hbounds
      (fun x i => (cell x i : ZMod 3))
  refine ⟨kept, hk, ?_, hadm, hall, ?_⟩
  · simpa [Fintype.card_fun, ZMod.card] using hmass
  · intro x hx y hy hxy
    exact lattice_color_separates cell (tree.terminal_fibers_injective cell hterminal hk hadm)
      hc hx hy hxy


/-- A query (for example a direction cap) covered by hierarchy blocks inherits the
sum of their capacities. This gives a finite bridge from dyadic blocks to cap bounds. -/
theorem covered_query_capacity (tree : CapacityTree α)
    {selected query : Finset α} (hsub : selected ⊆ tree.support)
    (hadm : tree.Admissible selected) {ι : Type*} [DecidableEq ι]
    (cover : Finset ι) (block : ι → Finset α) (bound : ι → ℕ)
    (hcover : query ⊆ cover.biUnion block)
    (hblocks : ∀ i ∈ cover, tree.Occurs (block i) (bound i)) :
    (selected ∩ query).card ≤ ∑ i ∈ cover, bound i := by
  have hs : selected ∩ query ⊆ cover.biUnion (fun i => selected ∩ block i) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp (hcover (Finset.mem_inter.mp hx).2)
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hx).1, hxi⟩⟩
  calc
    _ ≤ (cover.biUnion (fun i => selected ∩ block i)).card := Finset.card_le_card hs
    _ ≤ ∑ i ∈ cover, (selected ∩ block i).card := Finset.card_biUnion_le
    _ ≤ _ := Finset.sum_le_sum (fun i hi => all_capacities (hblocks i hi) hsub hadm)

/-- If a cap meets at most K covering blocks, each with capacity B, its selected
population is at most K*B. Overlap between covering blocks is harmless. -/
theorem covered_query_uniform_bound (tree : CapacityTree α)
    {selected query : Finset α} (hsub : selected ⊆ tree.support)
    (hadm : tree.Admissible selected) {ι : Type*} [DecidableEq ι]
    (cover : Finset ι) (block : ι → Finset α) {K B : ℕ}
    (hcount : cover.card ≤ K) (hcover : query ⊆ cover.biUnion block)
    (hblocks : ∀ i ∈ cover, tree.Occurs (block i) B) :
    (selected ∩ query).card ≤ K * B := by
  have h := tree.covered_query_capacity hsub hadm cover block (fun _ => B) hcover hblocks
  simpa using h.trans (by simpa using Nat.mul_le_mul_right B hcount)


end CapacityTree
end KakeyaVerification.CapSelection
