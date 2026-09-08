import ProjectiveSphereNet
import SamplingRawMeans

/-!
# Actual whole-sphere net tests for raw marked sampling

The angular test centers are the actual full-sphere net, not original tube
indices. Closed original caps are contained in open doubled net caps. Their
raw means follow by integrating the original measurable marked broadness over
the actual grid cells. This module does not assert a sampling probability bound.
-/
namespace KakeyaFormal.SphereNetCapTests
open Finset ProjectiveGeometry ProjectiveSphereNet SamplingMeans SamplingSupport
  KakeyaSamplingApplication MeasureTheory
open scoped BigOperators
noncomputable section
open Classical

/-- The concrete finite family of doubled-radius angular masks. -/
def cap {k M : ℕ} {theta : ℝ} (N : Net k theta) (F : TubeFamily (k+1) M) :
    Fin N.points.card → Fin M → Bool :=
  fun a i => decide (projectiveDistance (N.center a) (F.tube i).direction < 2*theta)

/-- Every closed original cap, including an empty one and one centered away
from all original tube directions, is contained in one of the same net tests. -/
theorem cap_containment {k M : ℕ} {theta : ℝ} (N : Net k theta)
    (F : TubeFamily (k+1) M) (S : Finset (Fin M)) (v : Space (k+1)) (hv : ‖v‖ = 1) :
    ∃ a : Fin N.points.card,
      S.filter (fun i => projectiveDistance v (F.tube i).direction ≤ theta) ⊆
        S.filter (fun i => cap N F a i = true) := by
  obtain ⟨a, ha⟩ := N.center_double_cap v hv
  refine ⟨a, ?_⟩
  intro i hi
  obtain ⟨hiS, hi⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨hiS, by simpa only [cap, decide_eq_true_eq] using ha _ hi⟩

/-- Finite net-test bounds transfer to every original unit cap center. -/
theorem all_closed_caps {k M : ℕ} {theta R : ℝ} (N : Net k theta)
    (F : TubeFamily (k+1) M) (S : Finset (Fin M))
    (hcap : ∀ a, ((S.filter (fun i => cap N F a i = true)).card : ℝ) ≤ R) :
    ∀ v : Space (k+1), ‖v‖ = 1 →
      ((S.filter (fun i => projectiveDistance v (F.tube i).direction ≤ theta)).card : ℝ) ≤ R := by
  intro v hv
  obtain ⟨a, ha⟩ := cap_containment N F S v hv
  exact (Nat.cast_le.mpr (card_le_card ha)).trans (hcap a)

/-- This equality refers to the actual outcome's original marked row. -/
theorem row_cap_card {k M : ℕ} {theta : ℝ} {C : Type*}
    [Fintype C] [DecidableEq C] (N : Net k theta) (F : TubeFamily (k+1) M)
    (high : Finset C) (omega : Outcome (Fin M) C) {c : C} (hc : c ∈ high)
    (a : Fin N.points.card) :
    (((SamplingCapTests.row high omega c).filter (fun i => cap N F a i = true)).card : ℝ) =
      markedCapCount omega (cap N F) c a := by
  simp only [SamplingCapTests.row, markedShading, mem_filter, mem_univ, true_and, hc,
    filter_filter, markedCapCount, KakeyaSampling.markedBit]
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hm : (omega (i,c)).val = 2 <;> cases cap N F a i <;> simp [hm]

/-- A simultaneous good outcome for these actual net tests is broad at every
original cell and every unit cap center, with no change to the output marks. -/
theorem sampled_closed_broadness {k M : ℕ} {theta : ℝ} {C B : Type*}
    [Fintype C] [DecidableEq C] [Fintype B]
    (N : Net k theta) (F : TubeFamily (k+1) M)
    (p q : Fin M → C → ℝ) (high : Finset C) (ball : B → C → Bool)
    (cutoff : Fin M → B → ℝ) (omega : Outcome (Fin M) C)
    (hgood : SampleGood p q high ball (cap N F) cutoff omega) :
    ∀ (c : C) (v : Space (k+1)), ‖v‖ = 1 →
      (((SamplingCapTests.row high omega c).filter (fun i =>
        projectiveDistance v (F.tube i).direction ≤ theta)).card : ℝ) ≤
          ((SamplingCapTests.row high omega c).card : ℝ)/10 := by
  intro c v hv
  by_cases hc : c ∈ high
  · apply all_closed_caps N F (SamplingCapTests.row high omega c) _ v hv
    intro a
    rw [row_cap_card N F high omega hc a, SamplingCapTests.row_card high omega hc]
    exact hgood.angular c hc a
  · have hrow : SamplingCapTests.row high omega c = ∅ := by
      simp [SamplingCapTests.row, markedShading, hc]
    simp [hrow]

/-- Integrating a tested marked-row inequality gives the actual raw cell mean.
No global finiteness of the marked sets is required: each grid cell is finite. -/
theorem cap_mean_le {k M : ℕ} {theta C δ : ℝ} (N : Net k theta)
    (F : TubeFamily (k+1) M) (G : Fin M → Set (Space (k+1)))
    (hδ : 0 < δ) (z : Cell (k+1)) (hG : ∀ i, MeasurableSet (G i))
    (hpoint : ∀ᵐ x ∂(volume : Measure (Space (k+1))), ∀ a : Fin N.points.card,
      ((univ.filter (fun i => x ∈ G i ∧
        projectiveDistance (N.center a) (F.tube i).direction < 2*theta)).card : ℝ) ≤
          C*((univ.filter (fun i => x ∈ G i)).card : ℝ)) (a : Fin N.points.card) :
    (∑ i, if cap N F a i then weight (G i) δ z else 0) ≤
      C*∑ i, weight (G i) δ z := by
  let indices := univ.filter (fun i => cap N F a i = true)
  have hpoint' : ∀ᵐ x ∂(volume : Measure (Space (k+1))),
      ((indices.filter (fun i => x ∈ G i)).card : ℝ) ≤
        C*((univ.filter (fun i => x ∈ G i)).card : ℝ) := by
    filter_upwards [hpoint] with x hx
    have he : indices.filter (fun i => x ∈ G i) = univ.filter (fun i => x ∈ G i ∧
        projectiveDistance (N.center a) (F.tube i).direction < 2*theta) := by
      ext i
      simp [indices, cap, and_comm]
    rw [he]
    exact hx a
  have hh := cell_incidence_weight_le G indices hδ z hG hpoint'
  simpa only [indices, sum_filter, Bool.coe_iff_coe] using hh

/-- Source broadness, only almost everywhere and only between delta and one,
supplies the doubled net-test mean with its original coefficient. -/
theorem cap_mean_from_bounded_radii {k M : ℕ} {theta K beta δ : ℝ} (N : Net k theta)
    (F : TubeFamily (k+1) M) (G : Fin M → Set (Space (k+1)))
    (hδ : 0 < δ) (htest : δ ≤ 2*theta) (htest1 : 2*theta ≤ 1) (z : Cell (k+1))
    (hG : ∀ i, MeasurableSet (G i))
    (hbroad : ∀ᵐ x ∂(volume : Measure (Space (k+1))), ∀ v : Space (k+1), ‖v‖ = 1 →
      ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ((univ.filter (fun i => x ∈ G i ∧ projectiveDistance (F.tube i).direction v ≤ r)).card : ℝ) ≤
          K*r^beta*((univ.filter (fun i => x ∈ G i)).card : ℝ)) (a : Fin N.points.card) :
    (∑ i, if cap N F a i then weight (G i) δ z else 0) ≤
      K*(2*theta)^beta*∑ i, weight (G i) δ z := by
  apply cap_mean_le N F G hδ z hG _ a
  filter_upwards [hbroad] with x hx
  intro a
  have hh := hx (N.center a) (N.center_unit a) (2*theta) htest htest1
  apply le_trans _ hh
  apply Nat.cast_le.mpr
  apply card_le_card
  intro i hi
  obtain ⟨_, hi, hcap⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨mem_univ _, hi, by rw [projective_symm]; exact hcap.le⟩

/-- The actual geometric means give the factor-1000 premise for the finite
coupled sampling theorem, now using full-sphere rather than original-direction tests. -/
theorem capMean_admissible {k M : ℕ} {theta K beta δ : ℝ} (N : Net k theta)
    (F : TubeFamily (k+1) M) (G : Fin M → Set (Space (k+1))) (S : Finset (Cell (k+1)))
    (hδ : 0 < δ) (htest : δ ≤ 2*theta) (htest1 : 2*theta ≤ 1)
    (hcoef : 1000*(K*(2*theta)^beta) ≤ 1) (hG : ∀ i, MeasurableSet (G i))
    (hbroad : ∀ᵐ x ∂(volume : Measure (Space (k+1))), ∀ v : Space (k+1), ‖v‖ = 1 →
      ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ((univ.filter (fun i => x ∈ G i ∧ projectiveDistance (F.tube i).direction v ≤ r)).card : ℝ) ≤
          K*r^beta*((univ.filter (fun i => x ∈ G i)).card : ℝ))
    (z : ↥S) (a : Fin N.points.card) :
    1000*capMean (weights G δ S) (cap N F) z a ≤ markedMean (weights G δ S) z := by
  have hh := cap_mean_from_bounded_radii N F G hδ htest htest1 z.val hG hbroad a
  have hn : 0 ≤ ∑ i, weight (G i) δ z.val :=
    sum_nonneg (fun i _ => weight_nonneg (G i) hδ z.val)
  have hmul := mul_le_mul_of_nonneg_right hcoef hn
  change 1000*(∑ i, if cap N F a i then weight (G i) δ z.val else 0) ≤
    ∑ i, weight (G i) δ z.val
  nlinarith

/-- The exact original theta choice discharges the numerical cap budget for
any actual finite cell support, with no density-ratio normalization. -/
theorem source_cap_test {k M : ℕ} {K beta δ : ℝ}
    (N : Net k (SamplingTheta.choice K beta))
    (F : TubeFamily (k+1) M) (G : Fin M → Set (Space (k+1))) (S : Finset (Cell (k+1)))
    (hδ : 0 < δ) (hK : 0 < K) (hbeta : 0 < beta)
    (htest : δ ≤ 2*SamplingTheta.choice K beta) (hG : ∀ i, MeasurableSet (G i))
    (hbroad : ∀ᵐ x ∂(volume : Measure (Space (k+1))), ∀ v : Space (k+1), ‖v‖ = 1 →
      ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        ((univ.filter (fun i => x ∈ G i ∧ projectiveDistance (F.tube i).direction v ≤ r)).card : ℝ) ≤
          K*r^beta*((univ.filter (fun i => x ∈ G i)).card : ℝ))
    (z : ↥S) (a : Fin N.points.card) :
    1000*capMean (weights G δ S) (cap N F) z a ≤ markedMean (weights G δ S) z := by
  apply capMean_admissible N F G S hδ htest
    (by linarith [SamplingTheta.choice_le_hundredth K beta]) _ hG hbroad z a
  simpa only [mul_assoc] using SamplingTheta.cap_budget hK hbeta

/-- Direct connection to the existing original raw measurable sampling Input.
The support and raw probabilities are exactly its original ones. -/
theorem input_cap_test {k M : ℕ} {F : TubeFamily (k+1) M}
    {Full G : Fin M → Set (Space (k+1))} {δ width R lam c₀ C₀ xi B alpha K beta : ℝ}
    (h : SamplingNormalizedMeans.Input F Full G δ width R lam c₀ C₀ xi B alpha K beta)
    (N : Net k (SamplingTheta.choice K beta))
    (htest : δ ≤ 2*SamplingTheta.choice K beta)
    (z : ↥(support F.tube Full δ width R)) (a : Fin N.points.card) :
    1000*capMean (SamplingNormalizedMeans.rawMarked F Full G δ width R) (cap N F) z a ≤
      markedMean (SamplingNormalizedMeans.rawMarked F Full G δ width R) z := by
  exact source_cap_test N F G _ h.scale_pos h.broadness_constant h.broadness_exponent
    htest h.marked_measurable h.broadness z a

end
end KakeyaFormal.SphereNetCapTests
