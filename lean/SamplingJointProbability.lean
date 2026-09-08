import SamplingGeometricFailure
import SphereNetFailure

/-! The two separate source failure budgets give a probability greater than
three quarters on the same actual product law. Positive-weight outcomes in
this event satisfy every field of the actual finite sampling conclusion. -/
namespace KakeyaFormal.SamplingJointProbability
open KakeyaSampling KakeyaSamplingApplication Finset
open scoped BigOperators
noncomputable section
open Classical

/-- Zero-weight outcomes do not reduce the complement probability. -/
theorem positive_avoidance_identity {Ω : Type*} [Fintype Ω]
    (D : FiniteLaw Ω) (E F : Ω → Prop) :
    D.probability (fun ω => 0 < D.weight ω ∧ ¬E ω ∧ ¬F ω) +
      D.probability (fun ω => E ω ∨ F ω) = 1 := by
  simp only [FiniteLaw.probability, ←sum_add_distrib, ←D.total]
  apply sum_congr rfl
  intro ω _
  by_cases hE : E ω
  · simp [hE]
  by_cases hF : F ω
  · simp [hF]
  by_cases hw : 0 < D.weight ω
  · simp [hE,hF,hw]
  have hz : D.weight ω = 0 := le_antisymm (le_of_not_gt hw) (D.nonneg ω)
  simp [hE,hF,hz]

/-- Union bounding the same-law failures preserves the strict source fraction. -/
theorem positive_avoidance_probability {Ω : Type*} [Fintype Ω]
    (D : FiniteLaw Ω) (E F : Ω → Prop)
    (hE : D.probability E < 1/8) (hF : D.probability F < 1/8) :
    3/4 < D.probability (fun ω => 0 < D.weight ω ∧ ¬E ω ∧ ¬F ω) := by
  have hid := positive_avoidance_identity D E F
  have hu := D.probability_union E F
  linarith

variable {T C B A : Type*} [Fintype T] [Fintype C]
  [DecidableEq T] [DecidableEq C]

/-- Every positive-weight outcome avoiding the source events supplies actual
full and marked shadings, including support and quarter-total marked mass. -/
theorem sampleGood_of_avoiding (p q : T → C → ℝ)
    (hq : ∀ t c, 0 ≤ q t c) (hqp : ∀ t c, q t c ≤ p t c) (hp : ∀ t c, p t c ≤ 1)
    (high : Finset C) (ball : B → C → Bool) (cap : A → T → Bool) (cutoff : T → B → ℝ)
    (hhigh : (∑ c, markedMean q c)/2 ≤ ∑ c ∈ high, markedMean q c)
    (ω : Outcome T C) (hpositive : 0 < (SamplingGeometricFailure.law p q hq hqp hp).weight ω)
    (hgeo : ¬SamplingGeometricFailure.geometricFailure p ball cutoff ω)
    (hang : ¬SphereNetFailure.angularFailure q high cap ω) :
    SampleGood p q high ball cap cutoff ω := by
  have hdensity (t : T) : fullMean p t/2 < fullTubeCount ω t ∧
      fullTubeCount ω t < 2*fullMean p t := by
    have hh : ¬SamplingGeometricFailure.bad p ball cutoff (Sum.inl t) ω :=
      fun hb => hgeo ⟨Sum.inl t,hb⟩
    simpa only [SamplingGeometricFailure.bad,not_or,not_le] using hh
  have hballs (t : T) (b : B) : fullBallCount ω ball t b < cutoff t b := by
    have hh : ¬SamplingGeometricFailure.bad p ball cutoff (Sum.inr (t,b)) ω :=
      fun hb => hgeo ⟨Sum.inr (t,b),hb⟩
    simpa only [SamplingGeometricFailure.bad,not_le] using hh
  have hcells (c : C) (hc : c ∈ high) : markedMean q c/2 < markedCellCount ω c := by
    exact lt_of_not_ge (fun hh => hang ⟨c,hc,Or.inl hh⟩)
  have hcaps (c : C) (hc : c ∈ high) (a : A) : markedCapCount ω cap c a < markedMean q c/20 := by
    exact lt_of_not_ge (fun hh => hang ⟨c,hc,Or.inr ⟨a,hh⟩⟩)
  have hsupport := coupled_positive_support (flatten p) (flatten q)
    (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2) ω hpositive
  constructor
  · intro t
    rw [←fullTubeCount_eq_card]
    exact ⟨(hdensity t).1.le,(hdensity t).2.le⟩
  · intro t b
    exact (hballs t b).le
  · intro c hc
    exact (hcells c hc).le
  · intro c hc a
    have hl := hcells c hc
    have hu := hcaps c hc a
    linarith
  · rw [marked_total_identity]
    have hs : (∑ c ∈ high, markedMean q c)/2 ≤ ∑ c ∈ high, markedCellCount ω c := by
      rw [sum_div]
      exact sum_le_sum (fun c hc => (hcells c hc).le)
    linarith
  · simp_rw [←fullTubeCount_eq_card]
    rw [mul_sum]
    exact sum_le_sum (fun t _ => (hdensity t).2.le)
  · exact markedShading_subset high ω
  · intro t c hc
    have hval : (ω (t,c)).val ≠ 0 := (mem_filter.mp hc).2
    exact (hsupport (t,c)).1 (by simp [fullBit,hval])
  · intro t c hc
    have hval : (ω (t,c)).val = 2 := (mem_filter.mp hc).2.2
    exact (hsupport (t,c)).2 (by simp [markedBit,hval])

/-- A probability statement about the actual full sampling conclusion. The
two probability premises are discharged by the separate source wrappers. -/
theorem sampleGood_probability (p q : T → C → ℝ)
    (hq : ∀ t c, 0 ≤ q t c) (hqp : ∀ t c, q t c ≤ p t c) (hp : ∀ t c, p t c ≤ 1)
    (high : Finset C) (ball : B → C → Bool) (cap : A → T → Bool) (cutoff : T → B → ℝ)
    (hhigh : (∑ c, markedMean q c)/2 ≤ ∑ c ∈ high, markedMean q c)
    (hgeo : (SamplingGeometricFailure.law p q hq hqp hp).probability
      (SamplingGeometricFailure.geometricFailure p ball cutoff) < 1/8)
    (hang : (SphereNetFailure.law p q hq hqp hp).probability
      (SphereNetFailure.angularFailure q high cap) < 1/8) :
    3/4 < (SamplingGeometricFailure.law p q hq hqp hp).probability
      (fun ω => 0 < (SamplingGeometricFailure.law p q hq hqp hp).weight ω ∧
        SampleGood p q high ball cap cutoff ω) := by
  have hprob := positive_avoidance_probability (SamplingGeometricFailure.law p q hq hqp hp)
    (SamplingGeometricFailure.geometricFailure p ball cutoff)
    (SphereNetFailure.angularFailure q high cap) hgeo hang
  apply hprob.trans_le
  apply FiniteLaw.probability_mono
  intro ω hω
  exact ⟨hω.1,sampleGood_of_avoiding p q hq hqp hp high ball cap cutoff hhigh ω hω.1 hω.2.1 hω.2.2⟩

end
end KakeyaFormal.SamplingJointProbability
