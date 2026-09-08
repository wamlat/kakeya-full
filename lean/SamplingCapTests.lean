import SamplingApplication
import ProjectiveGeometry

/-! Actual finite angular tests for the coupled sampling construction.
The tests are centered at the original tube directions. Every nonempty cap
of radius theta on an actual row is contained in one test of radius 2 theta.
Thus there are exactly M tests, with no spherical-net or covering premise. -/
namespace KakeyaFormal.SamplingCapTests
open Finset ProjectiveGeometry KakeyaSamplingApplication
open scoped BigOperators
noncomputable section
open Classical

def cap {k M : ℕ} (F : TubeFamily k M) (theta : ℝ) : Fin M → Fin M → Bool :=
  fun a i => decide (projectiveDistance (F.tube a).direction (F.tube i).direction < 2*theta)

/-- The center is an actual member of the row being tested. -/
theorem cap_containment {k M : ℕ} (F : TubeFamily k M) (theta : ℝ)
    (S : Finset (Fin M)) (v : Space k)
    (hne : (S.filter (fun i => projectiveDistance v (F.tube i).direction < theta)).Nonempty) :
    ∃ a ∈ S, S.filter (fun i => projectiveDistance v (F.tube i).direction < theta) ⊆
      S.filter (fun i => cap F theta a i = true) := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨haS, ha⟩ := mem_filter.mp ha
  refine ⟨a, haS, ?_⟩
  intro i hi
  obtain ⟨hiS, hi⟩ := mem_filter.mp hi
  refine mem_filter.mpr ⟨hiS, ?_⟩
  simp only [cap, decide_eq_true_eq]
  have htri := projective_triangle (F.tube a).direction v (F.tube i).direction
  rw [projective_symm (F.tube a).direction v] at htri
  linarith

/-- The finite tests imply every original-center angular count, including empty rows. -/
theorem all_caps {k M : ℕ} (F : TubeFamily k M) (theta : ℝ)
    (S : Finset (Fin M))
    (hcap : ∀ a, ((S.filter (fun i => cap F theta a i = true)).card : ℝ) ≤
      (S.card : ℝ)/10) :
    ∀ v : Space k,
      ((S.filter (fun i => projectiveDistance v (F.tube i).direction < theta)).card : ℝ) ≤
        (S.card : ℝ)/10 := by
  intro v
  by_cases hne : (S.filter (fun i => projectiveDistance v (F.tube i).direction < theta)).Nonempty
  · obtain ⟨a, _, ha⟩ := cap_containment F theta S v hne
    exact (Nat.cast_le.mpr (card_le_card ha)).trans (hcap a)
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp only [card_empty, Nat.cast_zero]
    positivity

def row {M : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (high : Finset C) (omega : Outcome (Fin M) C) (c : C) : Finset (Fin M) :=
  univ.filter (fun i => c ∈ markedShading high omega i)

theorem row_card {M : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (high : Finset C) (omega : Outcome (Fin M) C) {c : C} (hc : c ∈ high) :
    ((row high omega c).card : ℝ) = markedCellCount omega c := by
  simp [row, markedShading, hc, markedCellCount, KakeyaSampling.markedBit]

theorem row_cap_card {k M : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (F : TubeFamily k M) (theta : ℝ) (high : Finset C)
    (omega : Outcome (Fin M) C) {c : C} (hc : c ∈ high) (a : Fin M) :
    (((row high omega c).filter (fun i => cap F theta a i = true)).card : ℝ) =
      markedCapCount omega (cap F theta) c a := by
  simp only [row, markedShading, mem_filter, mem_univ, true_and, hc,
    filter_filter, markedCapCount, KakeyaSampling.markedBit]
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hm : (omega (i,c)).val = 2 <;> cases cap F theta a i <;> simp [hm]

/-- The actual sampled marked shadings are broad at every cell and every cap center.
The only angular input is the simultaneous outcome's finite original-direction tests. -/
theorem sampled_broadness {k M : ℕ} {C B : Type*}
    [Fintype C] [DecidableEq C] [Fintype B]
    (F : TubeFamily k M) (theta : ℝ) (p q : Fin M → C → ℝ)
    (high : Finset C) (ball : B → C → Bool) (cutoff : Fin M → B → ℝ)
    (omega : Outcome (Fin M) C)
    (hgood : SampleGood p q high ball (cap F theta) cutoff omega) :
    ∀ (c : C) (v : Space k),
      (((row high omega c).filter (fun i =>
        projectiveDistance v (F.tube i).direction < theta)).card : ℝ) ≤
          ((row high omega c).card : ℝ)/10 := by
  intro c v
  by_cases hc : c ∈ high
  · apply all_caps F theta (row high omega c) _ v
    intro a
    rw [row_cap_card F theta high omega hc a, row_card high omega hc]
    exact hgood.angular c hc a
  · have hrow : row high omega c = ∅ := by
      simp [row, markedShading, hc]
    simp [hrow]

end
end KakeyaFormal.SamplingCapTests
