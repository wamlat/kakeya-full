import GaussianGoodDirections
import GaussianCollisionExpectation

/-! One actual Gaussian matrix simultaneously has bounded norm, retains at
least half the original directions and has the stated ordered-collision bound.
No joint independence of the original directions is used. -/
namespace KakeyaFormal.GaussianRealization
open MeasureTheory ProbabilityTheory GaussianMatrix GaussianLinearOperator
open GaussianGoodDirections GaussianCollisionExpectation
open scoped ENNReal
noncomputable section

def budget (M : ℕ) (δ A : ℝ) : ℝ :=
  expectationCoefficient 20*A*(M:ℝ)*Real.log (2/δ)

theorem budget_pos {M : ℕ} {δ A : ℝ} (hM : 0 < M)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A) : 0 < budget M δ A := by
  have hlog : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  exact mul_pos (mul_pos (mul_pos (expectationCoefficient_pos 20)
    (by linarith)) (by exact_mod_cast hM)) hlog

def excessive {M : ℕ} (F : TubeFamily 7 M) (δ A : ℝ) : Set (Sample 5 7) :=
  {ω | ENNReal.ofReal (4*budget M δ A) ≤ collisionCount F 20 δ ω}

theorem excessive_measurable {M : ℕ} (F : TubeFamily 7 M) (δ A : ℝ) :
    MeasurableSet (excessive F δ A) :=
  measurableSet_le measurable_const (count_measurable F 20 δ)

/-- Markov applied to the literal finite ordered-pair count. -/
theorem excessive_probability {M : ℕ} (F : TubeFamily 7 M) {δ A : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    (hsep : F.Separated δ) (hcap : F.CapBound δ 4 A) :
    (law 5 7).real (excessive F δ A) ≤ 1/4 := by
  have hQ := budget_pos hM hδ hδ1 hA
  have he := expected_count_bound F (by norm_num : (0:ℝ) ≤ 20) hδ hδ1
    (by linarith : 0 ≤ A) hsep hcap
  have hm := mul_meas_ge_le_lintegral (μ:=law 5 7) (count_measurable F 20 δ)
    (ENNReal.ofReal (4*budget M δ A))
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hm.trans he)
  change (ENNReal.ofReal (4*budget M δ A) * law 5 7 (excessive F δ A)).toReal ≤
    (ENNReal.ofReal (budget M δ A)).toReal at ht
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal hQ.le] at ht
  change 4*budget M δ A*(law 5 7).real (excessive F δ A) ≤ budget M δ A at ht
  nlinarith

def simultaneousEvent {M : ℕ} (F : TubeFamily 7 M) (δ A : ℝ) : Set (Sample 5 7) :=
  goodEvent (fun i => (F.tube i).direction) ∩
    {ω | collisionCount F 20 δ ω ≤ ENNReal.ofReal (4*budget M δ A)}

theorem simultaneousEvent_measurable {M : ℕ} (F : TubeFamily 7 M) (δ A : ℝ) :
    MeasurableSet (simultaneousEvent F δ A) :=
  (goodEvent_measurable _).inter (measurableSet_le (count_measurable F 20 δ) measurable_const)

/-- All three properties hold on one event of probability at least 3/5. -/
theorem simultaneous_probability {M : ℕ} (F : TubeFamily 7 M) {δ A : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    (hsep : F.Separated δ) (hcap : F.CapBound δ 4 A) :
    (3/5:ℝ) ≤ (law 5 7).real (simultaneousEvent F δ A) := by
  have hg := good_probability (fun i => (F.tube i).direction) (fun i => (F.tube i).unit_direction)
  have hb := excessive_probability F hM hδ hδ1 hA hsep hcap
  have hcover : goodEvent (fun i => (F.tube i).direction) ⊆
      simultaneousEvent F δ A ∪ excessive F δ A := by
    intro ω hω
    by_cases hh : collisionCount F 20 δ ω ≤ ENNReal.ofReal (4*budget M δ A)
    · exact Or.inl ⟨hω,hh⟩
    · exact Or.inr (le_of_not_ge hh)
  have hu := (measureReal_mono hcover (measure_ne_top (law 5 7) _)).trans
    (measureReal_union_le (μ:=law 5 7) _ _)
  linarith

/-- The output refers to the actual original good-index set and actual
ordered distinct-pair count. The empty original family is included. -/
theorem exists_matrix {M : ℕ} (F : TubeFamily 7 M) {δ A : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    (hsep : F.Separated δ) (hcap : F.CapBound δ 4 A) :
    ∃ ω : Sample 5 7, ‖operator ω‖ ≤ 20 ∧
      (M:ℝ)/2 ≤ ((goodIndices (fun i => (F.tube i).direction) (1/4) ω).card:ℝ) ∧
      (∀ i ∈ goodIndices (fun i => (F.tube i).direction) (1/4) ω,
        (1/4:ℝ) ≤ ‖operator ω (F.tube i).direction‖) ∧
      ((orderedCollisions F 20 δ ω).card:ℝ) ≤ 4*budget M δ A := by
  by_cases hM : 0 < M
  · have hne : (simultaneousEvent F δ A).Nonempty := by
      by_contra hh
      have hp := simultaneous_probability F hM hδ hδ1 hA hsep hcap
      rw [Set.not_nonempty_iff_eq_empty.mp hh,measureReal_empty] at hp
      norm_num at hp
    obtain ⟨ω,hω⟩ := hne
    refine ⟨ω,hω.1.1,hω.1.2,?_,?_⟩
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
    · have hQ := budget_pos hM hδ hδ1 hA
      have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hω.2
      simpa only [collisionCount,ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*budget M δ A)] using ht
  · have hz : M=0 := Nat.eq_zero_of_not_pos hM
    obtain ⟨ω,hω,hcount,hgood⟩ := exists_good_matrix (fun i => (F.tube i).direction)
      (fun i => (F.tube i).unit_direction)
    refine ⟨ω,hω,hcount,hgood,?_⟩
    subst M
    simp [orderedCollisions,budget]

end
end KakeyaFormal.GaussianRealization
