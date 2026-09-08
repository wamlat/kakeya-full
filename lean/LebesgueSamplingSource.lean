import LebesgueSampling

/-! Literal source probability and physical sample for completed-measurable
original shadings. The finite data are exactly the original cell support and
raw arrays, so equality of data transports the SAME laws, tests and outcomes. -/
namespace KakeyaFormal.LebesgueSamplingSource
open Finset MeasureTheory KakeyaSamplingApplication LebesgueSampling
  SamplingLengthInput SamplingMeasurableAssembly
open scoped BigOperators
noncomputable section
open Classical

namespace Data
variable {n M : ℕ}

def high (D : LebesgueSampling.Data n M) (δ : ℝ) : Finset ↥D.cells :=
  KakeyaSamplingDichotomy.high (markedMean D.marked) (threshold n δ)

def Low (D : LebesgueSampling.Data n M) (δ : ℝ) : Prop :=
  (∑ z, markedMean D.marked z)/2 ≤
      ∑ z ∈ KakeyaSamplingDichotomy.low (markedMean D.marked) (threshold n δ), markedMean D.marked z ∧
    (∑ z, markedMean D.marked z)/(2*threshold n δ) ≤
      ((KakeyaSamplingDichotomy.low (markedMean D.marked) (threshold n δ)).card:ℝ)

def good (D : LebesgueSampling.Data n M) (F : TubeFamily (n+1) M)
    (δ B alpha theta : ℝ) (J : ℕ) (net : ProjectiveSphereNet.Net n theta) :
    Outcome (Fin M) ↥D.cells → Prop :=
  SampleGood D.full D.marked (high D δ) (SamplingBallTests.mask δ) (SphereNetCapTests.cap net F)
    (ballCutoff (J:=J) D.full B alpha)

/-- Every source test, budget and outcome refers to one concrete raw Data. -/
def Result (D : LebesgueSampling.Data n M) (F : TubeFamily (n+1) M)
    (δ B alpha K beta : ℝ) : Prop :=
  Low D δ ∨ ∃ (J : ℕ) (net : ProjectiveSphereNet.Net n (SamplingTheta.choice K beta)),
    δ ≤ Localization.radius J 0 ∧ Localization.radius J 0 < 2*δ ∧
    (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
    δ ≤ 2*SamplingTheta.choice K beta ∧ 2*SamplingTheta.choice K beta ≤ 1 ∧
    ((high D δ).card:ℝ)*(1+(net.points.card:ℝ)) ≤ (1/δ)^(((n+1:ℕ):ℝ)+2) ∧
    D.law.probability (SamplingGeometricFailure.geometricFailure D.full
      (SamplingBallTests.mask δ) (ballCutoff (J:=J) D.full B alpha)) < 1/8 ∧
    D.law.probability (SphereNetFailure.angularFailure D.marked (high D δ)
      (SphereNetCapTests.cap net F)) ≤
        (1/δ)^(((n+1:ℕ):ℝ)+2)*Real.exp (-(highCoefficient n*Real.log (2/δ))/8) ∧
    (1/δ)^(((n+1:ℕ):ℝ)+2)*Real.exp (-(highCoefficient n*Real.log (2/δ))/8) < 1/8 ∧
    3/4 < D.law.probability (fun ω => 0 < D.law.weight ω ∧
      good D F δ B alpha (SamplingTheta.choice K beta) J net ω) ∧
    ∃ ω, 0 < D.law.weight ω ∧ good D F δ B alpha (SamplingTheta.choice K beta) J net ω

end Data

/-- Full source range for arbitrary Lebesgue-measurable original shadings.
The threshold is uniform before every family and all varying physical data. -/
theorem source_sampling (k : ℕ) (width R L sep c₀ K₀ beta logPower s alpha : ℝ)
    (hw : 0 ≤ width) (hsep₀ : 0 < sep) (hc₀ : 0 < c₀) (hK₀ : 0 < K₀)
    (hbeta : 0 < beta) (hlog : 0 ≤ logPower)
    (hs : 0 < s) (hs1 : s < 1) (ha : 0 ≤ alpha) (hgap : alpha < 1-s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {M : ℕ} (F : TubeFamily (k+1) M) (length : Fin M → ℝ)
        (Full G : Fin M → Set (Space (k+1))) {δ lam C₀ xi B K : ℝ},
        ∀ h : LebesgueSampling.Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta,
          F.Separated (sep*δ) → δ ≤ δ₀ → δ^s ≤ lam →
          K ≤ K₀*(Real.log (2/δ))^logPower → Data.Result (data h) F δ B alpha K beta := by
  obtain ⟨δ₀,hδ₀,hδ₀1,hsource⟩ := SamplingSourceProbability.source_sampling
    k width R L sep c₀ K₀ beta logPower s alpha hw hsep₀ hc₀ hK₀ hbeta hlog hs hs1 ha hgap
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro M F length Full G δ lam C₀ xi B K h hsep hscale hlam hK
  obtain ⟨O⟩ := h.representatives
  let hb := h.to_borel O
  have H := hsource F length O.full O.marks hb hsep hscale hlam hK
  have H' : Data.Result (borelData hb) F δ B alpha K beta := by
    rcases H with hlo | hhi
    · apply Or.inl
      dsimp only [Data.Low, borelData]
      dsimp only [SamplingLengthAssembly.LowResult] at hlo
      rw [←hb.marked_mean_eq] at hlo
      convert hlo using 1 <;> apply Iff.of_eq <;> congr 6
    · exact Or.inr hhi
  rw [show borelData hb = data h from data_eq h O] at H'
  exact H'

/-- Exactly the same original-grid outcome is packaged as an actual geometric
sample, retaining the source positive probability and literal original Wg in
the low alternative. No Borel representative occurs in this public output. -/
theorem source_realization (k : ℕ) (width R L sep c₀ K₀ beta logPower s alpha : ℝ)
    (hw : 0 ≤ width) (hsep₀ : 0 < sep) (hc₀ : 0 < c₀) (hK₀ : 0 < K₀)
    (hbeta : 0 < beta) (hlog : 0 ≤ logPower)
    (hs : 0 < s) (hs1 : s < 1) (ha : 0 ≤ alpha) (hgap : alpha < 1-s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {M : ℕ} (F : TubeFamily (k+1) M) (length : Fin M → ℝ)
        (Full G : Fin M → Set (Space (k+1))) {δ lam C₀ xi B K : ℝ},
        ∀ h : LebesgueSampling.Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta,
          F.Separated (sep*δ) → δ ≤ δ₀ → δ^s ≤ lam →
          K ≤ K₀*(Real.log (2/δ))^logPower →
          SamplingLengthAssembly.LowResult F Full G δ width R L ∨
          ∃ (net : ProjectiveSphereNet.Net k (SamplingTheta.choice K beta))
            (O : SphereNetSampleRealization.Output F Full G δ width R L B alpha
              (SamplingTheta.choice K beta) net),
            0 < (data h).law.weight O.omega ∧
            3/4 < (data h).law.probability (fun ω => 0 < (data h).law.weight ω ∧
              SamplingSourceProbability.goodEvent F Full G δ width R L B alpha
                (SamplingTheta.choice K beta) O.depth net ω) := by
  obtain ⟨δ₀,hδ₀,hδ₀1,hsource⟩ := source_sampling
    k width R L sep c₀ K₀ beta logPower s alpha hw hsep₀ hc₀ hK₀ hbeta hlog hs hs1 ha hgap
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro M F length Full G δ lam C₀ xi B K h hsep hscale hlam hK
  rcases hsource F length Full G h hsep hscale hlam hK with hlo | hhi
  · apply Or.inl
    change Data.Low (data h) δ at hlo
    dsimp only [Data.Low] at hlo
    rw [h.marked_mean_eq] at hlo
    exact hlo
  · obtain ⟨J,net,hbottom,hbottom2,hdepth,_,_,_,_,_,_,hprob,ω,hpositive,hgood⟩ := hhi
    let O : SphereNetSampleRealization.Output F Full G δ width R L B alpha
        (SamplingTheta.choice K beta) net :=
      SphereNetSampleRealization.of_sample net J hbottom hbottom2 hdepth ω hgood
    exact Or.inr ⟨net,O,hpositive,hprob⟩

end
end KakeyaFormal.LebesgueSamplingSource
