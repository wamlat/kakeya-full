import Mathlib

/-!
# Constructive finite laminar capacity selection

A finite rooted partition is represented by a binary `CapacityTree`. Leaves hold
actual finite sets of elements; `Partitioned` requires disjoint child supports.
`Admissible` imposes each capacity on the elements selected below that node.
No integrality/rounding theorem is assumed: `attainsRank` constructs a finite
selection by induction and arbitrary finite-set truncation.

Any finite-arity rooted partition can be encoded by grouping siblings in binary
nodes and giving inserted grouping nodes capacity equal to their support size.
This encoding equivalence is explanatory here; it is not itself formalized.
The theorem `fractionalSelection` is the complete binary-tree version of the
combined manuscript's Lemma 4.2 (physical PDF pp. 14–15).
-/

namespace KakeyaVerification.Laminar

inductive CapacityTree (α : Type*) where
  | leaf (points : Finset α) (capacity : ℕ)
  | branch (left right : CapacityTree α) (capacity : ℕ)

variable {α : Type*} [DecidableEq α]

namespace CapacityTree

def support : CapacityTree α → Finset α
  | .leaf points _ => points
  | .branch left right _ => left.support ∪ right.support

def rank : CapacityTree α → ℕ
  | .leaf points capacity => min capacity points.card
  | .branch left right capacity => min capacity (left.rank + right.rank)

def Partitioned : CapacityTree α → Prop
  | .leaf _ _ => True
  | .branch left right _ =>
      left.Partitioned ∧ right.Partitioned ∧ Disjoint left.support right.support

def Admissible : CapacityTree α → Finset α → Prop
  | .leaf _ capacity, selected => selected.card ≤ capacity
  | .branch left right capacity, selected =>
      selected.card ≤ capacity ∧
      left.Admissible (selected ∩ left.support) ∧
      right.Admissible (selected ∩ right.support)

def Feasible (weight : α → ℝ) : CapacityTree α → Prop
  | .leaf points capacity => ∑ x ∈ points, weight x ≤ (capacity : ℝ)
  | .branch left right capacity =>
      (∑ x ∈ left.support ∪ right.support, weight x) ≤ (capacity : ℝ) ∧
      left.Feasible weight ∧ right.Feasible weight

/-- Deletion preserves every upper capacity, including all descendant capacities. -/
theorem admissible_mono (tree : CapacityTree α) {small large : Finset α}
    (hsub : small ⊆ large) (hlarge : tree.Admissible large) :
    tree.Admissible small := by
  induction tree generalizing small large with
  | leaf points capacity =>
      exact le_trans (Finset.card_le_card hsub) hlarge
  | branch left right capacity ihLeft ihRight =>
      obtain ⟨hcap, hleft, hright⟩ := hlarge
      exact ⟨le_trans (Finset.card_le_card hsub) hcap,
        ihLeft (Finset.inter_subset_inter hsub (by rfl)) hleft,
        ihRight (Finset.inter_subset_inter hsub (by rfl)) hright⟩

/-- The recursively computed integer capacity is attained by an actual subset. -/
theorem attainsRank (tree : CapacityTree α) (htree : tree.Partitioned) :
    ∃ selected ⊆ tree.support,
      tree.Admissible selected ∧ selected.card = tree.rank := by
  induction tree with
  | leaf points capacity =>
      obtain ⟨selected, hsub, hcard⟩ :=
        Finset.exists_subset_card_eq (s := points) (Nat.min_le_right capacity points.card)
      refine ⟨selected, hsub, ?_, hcard⟩
      change selected.card ≤ capacity
      rw [hcard]
      exact Nat.min_le_left capacity points.card
  | branch left right capacity ihLeft ihRight =>
      obtain ⟨htleft, htright, hdisj⟩ := htree
      obtain ⟨jl, hjl, hal, hcl⟩ := ihLeft htleft
      obtain ⟨jr, hjr, har, hcr⟩ := ihRight htright
      have hdj : Disjoint jl jr := hdisj.mono hjl hjr
      have hunionCard : (jl ∪ jr).card = left.rank + right.rank := by
        rw [Finset.card_union_of_disjoint hdj, hcl, hcr]
      have hleftInter : (jl ∪ jr) ∩ left.support = jl := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨h | h, hx⟩
          · exact h
          · exact False.elim ((Finset.disjoint_left.mp hdisj) hx (hjr h))
        · intro h
          exact ⟨Or.inl h, hjl h⟩
      have hrightInter : (jl ∪ jr) ∩ right.support = jr := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        constructor
        · rintro ⟨h | h, hx⟩
          · exact False.elim ((Finset.disjoint_left.mp hdisj) (hjl h) hx)
          · exact h
        · intro h
          exact ⟨Or.inr h, hjr h⟩
      have hsmall : min capacity (left.rank + right.rank) ≤ (jl ∪ jr).card := by
        rw [hunionCard]
        exact Nat.min_le_right _ _
      obtain ⟨selected, hsub, hcard⟩ := Finset.exists_subset_card_eq hsmall
      refine ⟨selected, ?_, ?_, hcard⟩
      · exact hsub.trans (Finset.union_subset_union hjl hjr)
      · refine ⟨?_, ?_, ?_⟩
        · rw [hcard]
          exact Nat.min_le_left _ _
        · apply left.admissible_mono _ hal
          have h := Finset.inter_subset_inter hsub (by rfl : left.support ⊆ left.support)
          rwa [hleftInter] at h
        · apply right.admissible_mono _ har
          have h := Finset.inter_subset_inter hsub (by rfl : right.support ⊆ right.support)
          rwa [hrightInter] at h

/-- A feasible fractional mass never exceeds the recursively computed integer rank. -/
theorem mass_le_rank (tree : CapacityTree α) (htree : tree.Partitioned)
    (weight : α → ℝ) (hupper : ∀ x ∈ tree.support, weight x ≤ 1)
    (hfeas : tree.Feasible weight) :
    (∑ x ∈ tree.support, weight x) ≤ (tree.rank : ℝ) := by
  induction tree with
  | leaf points capacity =>
      have hcard : (∑ x ∈ points, weight x) ≤ (points.card : ℝ) := by
        calc
          (∑ x ∈ points, weight x) ≤ ∑ _x ∈ points, (1 : ℝ) := by
            exact Finset.sum_le_sum hupper
          _ = (points.card : ℝ) := by simp
      simpa [support, rank, Nat.cast_min] using le_min hfeas hcard
  | branch left right capacity ihLeft ihRight =>
      obtain ⟨htleft, htright, hdisj⟩ := htree
      obtain ⟨hcap, hfl, hfr⟩ := hfeas
      have hwl : ∀ x ∈ left.support, weight x ≤ 1 := by
        intro x hx
        exact hupper x (Finset.mem_union_left _ hx)
      have hwr : ∀ x ∈ right.support, weight x ≤ 1 := by
        intro x hx
        exact hupper x (Finset.mem_union_right _ hx)
      have hsum : (∑ x ∈ left.support ∪ right.support, weight x) ≤
          ((left.rank + right.rank : ℕ) : ℝ) := by
        rw [Finset.sum_union hdisj, Nat.cast_add]
        exact add_le_add (ihLeft htleft hwl hfl) (ihRight htright hwr hfr)
      simpa [support, rank, Nat.cast_min] using le_min hcap hsum

/-- Lemma 4.2 for a binary finite rooted partition, with actual selected elements. -/
theorem fractionalSelection (tree : CapacityTree α) (htree : tree.Partitioned)
    (weight : α → ℝ)
    (hweight : ∀ x ∈ tree.support, 0 ≤ weight x ∧ weight x ≤ 1)
    (hfeas : tree.Feasible weight) :
    ∃ selected ⊆ tree.support, tree.Admissible selected ∧
      (∑ x ∈ tree.support, weight x) ≤ (selected.card : ℝ) := by
  obtain ⟨selected, hsub, hadm, hcard⟩ := tree.attainsRank htree
  refine ⟨selected, hsub, hadm, ?_⟩
  rw [hcard]
  exact tree.mass_le_rank htree weight (fun x hx => (hweight x hx).2) hfeas

end CapacityTree
end KakeyaVerification.Laminar

#print axioms KakeyaVerification.Laminar.CapacityTree.attainsRank
#print axioms KakeyaVerification.Laminar.CapacityTree.fractionalSelection
