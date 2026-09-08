import SamplingSourceProbability
import SphereNetSampleRealization

/-! The same source-net-tested positive-probability outcome is made into an
actual original-grid geometric configuration. Its density, marked mass, all-ball
two ends, all-center closed-cap broadness and original support are established
by SphereNetSampleRealization.Output, without choosing another outcome. -/
namespace KakeyaFormal.SamplingSourceRealization
open SamplingLengthInput SamplingSourceProbability SphereNetSourceFailure
noncomputable section
open Classical

/-- Complete original source low/high sampling route, including the actual
net, literal probability greater than three quarters, and that same outcome's
original-tube geometric realization. All constants precede actual input data. -/
theorem source_realization (k : ℕ) (width R L sep c₀ K₀ beta logPower s alpha : ℝ)
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
          ∃ (net : ProjectiveSphereNet.Net k (SamplingTheta.choice K beta))
            (O : SphereNetSampleRealization.Output F Full G δ width R L B alpha
              (SamplingTheta.choice K beta) net),
            0 < (rawLaw h).weight O.omega ∧
            3/4 < (rawLaw h).probability (fun ω => 0 < (rawLaw h).weight ω ∧
              goodEvent F Full G δ width R L B alpha (SamplingTheta.choice K beta) O.depth net ω) := by
  obtain ⟨δ₀,hδ₀,hδ₀1,hsource⟩ := source_sampling
    k width R L sep c₀ K₀ beta logPower s alpha hw hsep₀ hc₀ hK₀ hbeta hlog hs hs1 ha hgap
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro M F length Full G δ lam C₀ xi B K h hsep hscale hlam hK
  rcases hsource F length Full G h hsep hscale hlam hK with hlo | hhi
  · exact Or.inl hlo
  · obtain ⟨J,net,hbottom,hbottom2,hdepth,_,_,_,_,_,_,hprob,ω,hpositive,hgood⟩ := hhi
    let O := SphereNetSampleRealization.of_sample net J hbottom hbottom2 hdepth ω hgood
    exact Or.inr ⟨net,O,hpositive,hprob⟩

end
end KakeyaFormal.SamplingSourceRealization
