import SamplingSourceGeometricFailure
import SamplingJointProbability

/-! The literal Section 6 low/high alternative and joint probability, using
the actual original raw probabilities and an actual whole-sphere theta-net.
Both separate one-eighth failure budgets are proved from physical input data.
The same outcome provides the full source density band and all SampleGood
fields; no probability, mean, test-count, or high-mass premise is supplied. -/
namespace KakeyaFormal.SamplingSourceProbability
open Finset KakeyaSampling KakeyaSamplingApplication SamplingLengthInput
  SamplingMeasurableAssembly SphereNetSourceFailure
open scoped BigOperators
noncomputable section
open Classical

/-- A positive event probability yields an actual member of the event. -/
theorem exists_of_probability_pos {Ω : Type*} [Fintype Ω]
    (D : FiniteLaw Ω) (E : Ω → Prop) (hp : 0 < D.probability E) : ∃ ω, E ω := by
  by_contra hh
  have hn : ∀ ω, ¬E ω := not_exists.mp hh
  have hz : D.probability E = 0 := by simp [FiniteLaw.probability,hn]
  linarith

/-- This event refers to actual raw full and marked rows on the original
support and to the cap masks of the supplied constructed whole-sphere net. -/
def goodEvent {k M : ℕ} (F : TubeFamily (k+1) M)
    (Full G : Fin M → Set (Space (k+1))) (δ width R L B alpha theta : ℝ)
    (J : ℕ) (net : ProjectiveSphereNet.Net k theta) :
    Outcome (Fin M) ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L)) → Prop :=
  SampleGood (SamplingLengthInput.rawFull Full δ width R L)
    (SamplingLengthInput.rawMarked Full G δ width R L) (highCells Full G δ width R L)
    (SamplingBallTests.mask δ) (SphereNetCapTests.cap net F)
    (ballCutoff (J:=J) (SamplingLengthInput.rawFull Full δ width R L) B alpha)

/-- Original physical hypotheses alone give the low-cell conclusion or a
probability greater than three quarters for a positive-weight full sampling
realization. The displayed angular test count and both failure budgets are
kept alongside that probability, with one uniform scale cutoff. -/
theorem source_sampling (k : ℕ) (width R L sep c₀ K₀ beta logPower s alpha : ℝ)
    (hw : 0 ≤ width) (hsep₀ : 0 < sep) (hc₀ : 0 < c₀) (hK₀ : 0 < K₀)
    (hbeta : 0 < beta) (hlog : 0 ≤ logPower)
    (hs : 0 < s) (hs1 : s < 1) (ha : 0 ≤ alpha) (hgap : alpha < 1-s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {M : ℕ} (F : TubeFamily (k+1) M) (length : Fin M → ℝ)
        (Full G : Fin M → Set (Space (k+1))) {δ lam C₀ xi B K : ℝ},
        ∀ h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta,
          F.Separated (sep*δ) → δ ≤ δ₀ → δ^s ≤ lam →
          K ≤ K₀*(Real.log (2/δ))^logPower →
          SamplingLengthAssembly.LowResult F Full G δ width R L ∨
          ∃ (J : ℕ) (net : ProjectiveSphereNet.Net k (SamplingTheta.choice K beta)),
            δ ≤ Localization.radius J 0 ∧ Localization.radius J 0 < 2*δ ∧
            (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
            δ ≤ 2*SamplingTheta.choice K beta ∧ 2*SamplingTheta.choice K beta ≤ 1 ∧
            ((highCells Full G δ width R L).card:ℝ)*(1+(net.points.card:ℝ)) ≤
              (1/δ)^(((k+1:ℕ):ℝ)+2) ∧
            (rawLaw h).probability
              (SamplingGeometricFailure.geometricFailure (SamplingLengthInput.rawFull Full δ width R L)
                (SamplingBallTests.mask δ)
                (ballCutoff (J:=J) (SamplingLengthInput.rawFull Full δ width R L) B alpha)) < 1/8 ∧
            (rawLaw h).probability
              (SphereNetFailure.angularFailure (SamplingLengthInput.rawMarked Full G δ width R L)
                (highCells Full G δ width R L) (SphereNetCapTests.cap net F)) ≤
              (1/δ)^(((k+1:ℕ):ℝ)+2)*Real.exp (-(highCoefficient k*Real.log (2/δ))/8) ∧
            (1/δ)^(((k+1:ℕ):ℝ)+2)*Real.exp (-(highCoefficient k*Real.log (2/δ))/8) < 1/8 ∧
            3/4 < (rawLaw h).probability (fun ω => 0 < (rawLaw h).weight ω ∧
              goodEvent F Full G δ width R L B alpha (SamplingTheta.choice K beta) J net ω) ∧
            ∃ ω, 0 < (rawLaw h).weight ω ∧
              goodEvent F Full G δ width R L B alpha (SamplingTheta.choice K beta) J net ω := by
  obtain ⟨δg,hδg,hδg1,hgeo⟩ := SamplingSourceGeometricFailure.source_geometric_failure
    k width R L sep c₀ s alpha hw hsep₀ hc₀ hs hs1 ha hgap
  obtain ⟨δa,hδa,hδa1,hang⟩ := source_angular_failure
    k width R L K₀ beta logPower hw hK₀ hbeta hlog
  refine ⟨min δg δa,lt_min hδg hδa,(min_le_left _ _).trans hδg1,?_⟩
  intro M F length Full G δ lam C₀ xi B K h hsep hscale hlam hK
  let p := SamplingLengthInput.rawFull Full δ width R L
  let q := SamplingLengthInput.rawMarked Full G δ width R L
  have hq : ∀ i z, 0 ≤ q i z := fun i z => (h.probabilities i z).1
  have hcut := threshold_pos (n:=k) h.scale_pos h.scale_le_one
  rcases KakeyaSamplingDichotomy.marked_dichotomy q hq hcut with hlo | hhigh
  · apply Or.inl
    simpa only [SamplingLengthAssembly.LowResult,←h.marked_mean_eq] using hlo
  · apply Or.inr
    obtain ⟨J,hbottom,hbottom2,hdepth,hg⟩ := hgeo F length Full G h hsep
      (hscale.trans (min_le_left _ _)) hlam
    obtain ⟨net,htbottom,htupper,htests,haProb,haSmall⟩ := hang F length Full G h
      (hscale.trans (min_le_right _ _)) hK
    have hprob := SamplingJointProbability.sampleGood_probability p q hq
      (fun i z => (h.probabilities i z).2.1) (fun i z => (h.probabilities i z).2.2)
      (highCells Full G δ width R L) (SamplingBallTests.mask δ) (SphereNetCapTests.cap net F)
      (ballCutoff (J:=J) p B alpha) hhigh hg (haProb.trans_lt haSmall)
    have hprob' : 3/4 < (rawLaw h).probability (fun ω => 0 < (rawLaw h).weight ω ∧
        goodEvent F Full G δ width R L B alpha (SamplingTheta.choice K beta) J net ω) := hprob
    have hex := exists_of_probability_pos (rawLaw h) _
      ((by norm_num : (0:ℝ)<3/4).trans hprob')
    exact ⟨J,net,hbottom,hbottom2,hdepth,htbottom,htupper,htests,hg,haProb,haSmall,hprob',hex⟩

end
end KakeyaFormal.SamplingSourceProbability
