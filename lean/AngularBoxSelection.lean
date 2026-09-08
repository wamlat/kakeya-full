import MeasurableDensityRecovery
import SeparationColoring
import AnisotropicTransport

/-! Actual maximal-mass separation color, retaining all original reference
indices for the subsequent measurable broadness recovery. -/
namespace KakeyaFormal.AngularBoxSelection
open MeasureTheory SeparationColoring MeasurableDensityRecovery
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- Keep the actual output on one color and use the empty set elsewhere. -/
def colorOutput {X : Type*} {M P : ℕ} (O : Fin M → Set X)
    (color : Fin M → Fin P) (c : Fin P) : Fin M → Set X :=
  fun i => if color i = c then O i else ∅

theorem colorOutput_subset {X : Type*} {M P : ℕ} (O : Fin M → Set X)
    (color : Fin M → Fin P) (c : Fin P) (i : Fin M) : colorOutput O color c i ⊆ O i := by
  by_cases h : color i = c <;> simp [colorOutput,h]

theorem colorOutput_measurable {X : Type*} [MeasurableSpace X] {M P : ℕ}
    (O : Fin M → Set X) (color : Fin M → Fin P) (c : Fin P)
    (hO : ∀ i, MeasurableSet (O i)) : ∀ i, MeasurableSet (colorOutput O color c i) := by
  intro i
  by_cases h : color i = c <;> simp [colorOutput,h,hO]

theorem colorOutput_mass {X : Type*} [MeasurableSpace X] (ν : Measure X) {M P : ℕ}
    (O : Fin M → Set X) (color : Fin M → Fin P) (c : Fin P) :
    (∑ i, ν.real (colorOutput O color c i)) = ∑ i ∈ colorClass color c, ν.real (O i) := by
  simp only [colorOutput,colorClass,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : color i = c <;> simp [h]

/-- Finite maximization constructs a color retaining at least the average
actual mass. No equal per-tube mass or occupancy assumption is required. -/
theorem exists_mass_color {X : Type*} [MeasurableSpace X] (ν : Measure X) {M P : ℕ}
    (hP : 0 < P) (O : Fin M → Set X) (color : Fin M → Fin P) :
    ∃ c : Fin P, (∑ i, ν.real (O i))/(P:ℝ) ≤ ∑ i, ν.real (colorOutput O color c i) := by
  let : Nonempty (Fin P) := ⟨⟨0,hP⟩⟩
  obtain ⟨c,_,hc⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin P))
    (fun c => ∑ i ∈ colorClass color c, ν.real (O i)) Finset.univ_nonempty
  refine ⟨c,?_⟩
  have hh := Finset.sum_le_sum hc
  rw [color_weight_sum] at hh
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  rw [colorOutput_mass]
  exact (div_le_iff₀ (Nat.cast_pos.mpr hP)).mpr (by simpa only [mul_comm] using hh)

/-- Positive density forces every good output to belong to the chosen color. -/
theorem selectedIndex_color {X : Type*} [MeasurableSpace X] (ν : Measure X) {M P : ℕ}
    (O : Fin M → Set X) (color : Fin M → Fin P) (c : Fin P) {eta lam : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam)
    (i : Fin (good ν (colorOutput O color c) eta lam).card) :
    color (selectedIndex ν (colorOutput O color c) eta lam i) = c := by
  by_contra h
  have hm := selected_mass_lower (ν := ν) (colorOutput O color c) eta lam i
  simp only [selected,colorOutput,if_neg h,measureReal_empty] at hm
  have hp : 0 < eta*lam/2 := by positivity
  linarith

/-- Recovery of a positive-density family from one separation color inherits
the exact target separation, even though the reference family used all colors. -/
theorem recovered_separated {k M P : ℕ} (F : TubeFamily k M) (ν : Measure (Space k))
    (O : Fin M → Set (Space k)) (color : Fin M → Fin P) (c : Fin P) {eta lam δ : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam)
    (hcolor : ∀ i j, color i = color j → i ≠ j →
      δ ≤ projectiveDistance (F.tube i).direction (F.tube j).direction) :
    (selectedFamily F ν (colorOutput O color c) eta lam).Separated δ := by
  intro i j hij
  apply hcolor
  · exact (selectedIndex_color ν O color c heta hlam i).trans
      (selectedIndex_color ν O color c heta hlam j).symm
  · exact fun he => hij (selectedIndex_injective ν (colorOutput O color c) eta lam he)

/-- Literal finite angular broadness at unit angular scale is exactly the
measurable hairbrush pointwise broadness condition, with no exceptional points. -/
theorem pointwiseBroad_of_angular {k M : ℕ} (F : TubeFamily k M)
    (Y : Fin M → Set (Space k)) {δ beta K : ℝ}
    (h : ∀ x, AngularDecomposition.Broad F (Finset.univ.filter (fun i => x ∈ Y i)) δ beta 1 K) :
    HairbrushKernel.PointwiseBroad F Y (⋃ i, Y i) δ beta K := by
  intro x _ center t ht
  have hh := h x center t ht
  simpa only [AngularDecomposition.cap,Finset.filter_filter,div_one,
    MeasurableEnergy.overlapCount] using hh

end
end KakeyaFormal.AngularBoxSelection

#print axioms KakeyaFormal.AngularBoxSelection.exists_mass_color
#print axioms KakeyaFormal.AngularBoxSelection.recovered_separated
