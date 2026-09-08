import SamplingNormalizedMeans
import SamplingExactDensity
import SamplingDichotomy
import ProjectiveGeometry

/-! Actual measurable-to-discrete sampling, with all finite test families and
expectation inputs constructed from the original geometry. The small-scale
threshold is fixed before the measurable configuration, density, and outcome. -/
namespace KakeyaFormal.SamplingMeasurableAssembly
open Finset SamplingNormalizedMeans SamplingSupport KakeyaSamplingApplication
open scoped BigOperators
noncomputable section
open Classical

/-- The dimension-only high-cell coefficient from the finite union bound. -/
def highCoefficient (n : ℕ) : ℝ := 64*(((n+1:ℕ):ℝ)+4)
def threshold (n : ℕ) (δ : ℝ) : ℝ := highCoefficient n*Real.log (2/δ)

def supportRadius (n : ℕ) (width R : ℝ) : ℝ :=
  PrunedGraphLift.regionRadius (width+((n+1:ℕ):ℝ)/2) R

def gridConstant (n : ℕ) (width R : ℝ) : ℝ :=
  (5:ℝ)^(n+1)*(1+supportRadius n width R)^(n+1)

theorem gridConstant_pos {n : ℕ} {width R : ℝ} (hw : 0 ≤ width) :
    0 < gridConstant n width R := by
  have hr : 0 < supportRadius n width R :=
    PrunedGraphLift.regionRadius_pos (by positivity)
  unfold gridConstant
  positivity

theorem threshold_pos {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < threshold n δ := by
  have ht : 1 < 2/δ := (lt_div_iff₀ hδ).mpr (by linarith)
  exact mul_pos (by unfold highCoefficient; positivity) (Real.log_pos ht)

/-- Literal physical-ball cutoff; its coefficient is uniform in alpha≤1/4. -/
def ballCutoff {n M J : ℕ} {E : Finset (Cell (n+1))}
    (p : Fin M → ↥E → ℝ) (B alpha : ℝ) (i : Fin M)
    (t : SamplingBallTests.Test E J) : ℝ :=
  ballCoefficient n*B*(SamplingBallTests.testRadius t)^alpha*fullMean p i

/-- One actual outcome supplies every finite ball/cap test and the narrow
per-tube density band. No expectation or probability budget is a field. -/
def HighResult {n M : ℕ} (F : TubeFamily (n+1) M)
    (Full G : Fin M → Set (Space (n+1))) (δ width R c₀ lam B alpha theta : ℝ) : Prop :=
  let E := support F.tube Full δ width R
  let p := full F Full δ width R c₀ lam
  let q := marked F Full G δ width R c₀ lam
  let high := KakeyaSamplingDichotomy.high (markedMean q) (threshold n δ)
  ∃ J : ℕ, δ ≤ Localization.radius J 0 ∧ Localization.radius J 0 < 2*δ ∧
    (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
    ∃ ω : Outcome (Fin M) ↥E,
      SampleGood p q high (SamplingBallTests.mask δ) (SamplingCapTests.cap F theta)
        (ballCutoff (J:=J) p B alpha) ω ∧
      ∀ i, (2/3:ℝ)*fullMean p i ≤ (fullShading ω i).card ∧
        ((fullShading ω i).card:ℝ) ≤ (4/3:ℝ)*fullMean p i

/-- The actual low/high alternative of Section 6, after row equalization.
All support/test counts follow from bounded original carriers and separated
original directions; all expected masses follow from physical shading data.
The existential scale cutoff precedes every original family and shading. -/
theorem construct (n : ℕ) (width R c₀ C₀ K₀ beta logPower : ℝ)
    (hw : 0 ≤ width) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hK₀ : 0 < K₀)
    (hbeta : 0 < beta) (hlog : 0 ≤ logPower) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {M : ℕ} (F : TubeFamily (n+1) M) (Full G : Fin M → Set (Space (n+1)))
      {δ lam xi B alpha K : ℝ},
      Input F Full G δ width R lam c₀ C₀ xi B alpha K beta →
      F.Separated δ → δ ≤ δ₀ → (1/δ)^(-(1:ℝ)/3) ≤ lam → alpha ≤ 1/4 →
      K ≤ K₀*(Real.log (2/δ))^logPower →
      let theta := SamplingTheta.choice (ratio c₀ C₀*K) beta
      let q := marked F Full G δ width R c₀ lam
      0 < theta ∧ δ ≤ 2*theta ∧ 2*theta ≤ 1 ∧
      SamplingTheta.choice (ratio c₀ C₀*K₀) beta*(Real.log (2/δ))^(-logPower/beta) ≤ theta ∧
      (((1/ratio c₀ C₀)*(xi*lam*(M:ℝ)/δ))/(2*threshold n δ) ≤
        ((KakeyaSamplingDichotomy.low (markedMean q) (threshold n δ)).card:ℝ) ∨
       HighResult F Full G δ width R c₀ lam B alpha theta) := by
  have hgrid := gridConstant_pos (n:=n) (R:=R) hw
  have heq : 0 < equalizer c₀ := lt_min hc₀ zero_lt_one
  obtain ⟨N₀,hN₀,hsample⟩ := SamplingExactDensity.source_sampling_narrow (n+1)
    (CT:=ProjectiveGeometry.packingConstant n)
    (CB:=gridConstant n width R) (CE:=gridConstant n width R)
    (cf:=equalizer c₀) (cb:=ballCoefficient n*equalizer c₀)
    (zero_le_one.trans (ProjectiveGeometry.packingConstant_ge_one n))
    hgrid.le hgrid.le heq (mul_pos (ballCoefficient_pos n) heq)
  obtain ⟨δa,hδa,hδa1,hangular⟩ := uniform_angular_tests c₀ C₀ K₀ beta logPower
    hc₀ hC₀ hK₀ hbeta hlog
  refine ⟨min δa (1/N₀),lt_min hδa (one_div_pos.mpr (zero_lt_one.trans_le hN₀)),
    (min_le_left _ _).trans hδa1,?_⟩
  intro M F Full G δ lam xi B alpha K h hsep hscale hlam ha hK theta q
  obtain ⟨htheta,hbottomTheta,hupperTheta,hlowerTheta,hcap⟩ :=
    hangular F Full G h (hscale.trans (min_le_left _ _)) hK
  refine ⟨htheta,hbottomTheta,hupperTheta,hlowerTheta,?_⟩
  have hq : ∀ i z, 0 ≤ q i z := fun i z => (h.normalized_probabilities i z).1
  have hcut := threshold_pos (n:=n) h.scale_pos h.scale_le_one
  rcases KakeyaSamplingDichotomy.marked_dichotomy q hq hcut with hlo | hhigh
  · apply Or.inl
    have hm := h.normalized_marked_mass
    have hr : 1/ratio c₀ C₀ = equalizer c₀/C₀ := by unfold ratio; field_simp
    rw [← hr] at hm
    exact (div_le_div_of_nonneg_right hm (by positivity)).trans hlo.2
  · apply Or.inr
    let E := support F.tube Full δ width R
    let p := full F Full δ width R c₀ lam
    have hbnd : ∀ z ∈ E, ‖cellCenter δ z‖ ≤ supportRadius n width R :=
      SamplingSupport.support_bounded F.tube Full h.scale_le_one hw h.bounded h.full_subset
    have hrad : 0 ≤ supportRadius n width R :=
      (PrunedGraphLift.regionRadius_pos (by positivity : 0 ≤ width+((n+1:ℕ):ℝ)/2)).le
    obtain ⟨J,hbottom,hbottom2,hdepth,hradtest,hcounttest,_⟩ :=
      SamplingBallTests.construct E h.scale_pos h.scale_le_one hrad hbnd
    have hN : N₀ ≤ 1/δ := by
      have hh := hscale.trans (min_le_right δa (1/N₀))
      exact (le_div_iff₀ h.scale_pos).mpr
        (by have hh' := (le_div_iff₀ (zero_lt_one.trans_le hN₀)).mp hh; nlinarith)
    have hT : (Fintype.card (Fin M):ℝ) ≤ ProjectiveGeometry.packingConstant n*
        (1/δ)^(((n+1:ℕ):ℝ)-1) := by
      simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Real.rpow_natCast]
        using ProjectiveGeometry.separated_total_tube_count F h.scale_pos h.scale_le_one hsep
    have hBalls : (Fintype.card (SamplingBallTests.Test E J):ℝ) ≤ gridConstant n width R*
        (1/δ)^((n+1:ℕ):ℝ)*(Real.log (1/δ)/Real.log 2+1) := by
      simpa only [gridConstant,supportRadius,Real.rpow_natCast] using hcounttest
    have hE := SamplingSupport.support_card F.tube Full h.scale_pos h.scale_le_one hw
      h.bounded h.full_subset
    have hHighCount : ((KakeyaSamplingDichotomy.high (markedMean q) (threshold n δ)).card:ℝ) ≤
        gridConstant n width R*(1/δ)^((n+1:ℕ):ℝ) := by
      have hc : ((KakeyaSamplingDichotomy.high (markedMean q) (threshold n δ)).card:ℝ) ≤ E.card := by
        have hh := Finset.card_le_univ (KakeyaSamplingDichotomy.high (markedMean q) (threshold n δ))
        simpa only [Fintype.card_coe,Nat.cast_le,E] using (Nat.cast_le (α:=ℝ)).mpr hh
      exact hc.trans (by simpa only [E,gridConstant,supportRadius,Real.rpow_natCast] using hE)
    have hpmean : ∀ i, fullMean p i = commonMean c₀ lam δ := h.normalized_full_mean
    have hfull : ∀ i, equalizer c₀*lam*(1/δ) ≤ fullMean p i := by
      intro i
      rw [hpmean]
      exact le_of_eq (by unfold commonMean; ring)
    have hballCutoff : ∀ i t, (ballCoefficient n*equalizer c₀)*B*
        (SamplingBallTests.testRadius t)^alpha*lam*(1/δ) ≤ ballCutoff (J:=J) p B alpha i t := by
      intro i t
      unfold ballCutoff
      rw [hpmean]
      exact le_of_eq (by unfold commonMean; ring)
    have hballMean : ∀ i t, 4*ballMean p (SamplingBallTests.mask δ) i t ≤
        ballCutoff (J:=J) p B alpha i t := by
      intro i t
      simpa only [ballCutoff,hpmean] using h.normalized_ball_test (by linarith : alpha ≤ 1) hbottom i t
    obtain ⟨ω,hgood,hnarrow⟩ := hsample (1/δ) hN (Fin M) ↥E (SamplingBallTests.Test E J) (Fin M)
      p q (KakeyaSamplingDichotomy.high (markedMean q) (threshold n δ))
      (SamplingBallTests.mask δ) (SamplingCapTests.cap F theta)
      (ballCutoff (J:=J) p B alpha) SamplingBallTests.testRadius lam B alpha
      hq (fun i z => (h.normalized_probabilities i z).2.1)
      (fun i z => (h.normalized_probabilities i z).2.2)
      hT hBalls hHighCount le_rfl hlam h.two_ends_constant h.two_ends_exponent ha
      (fun t => by rw [one_div_one_div]; linarith [(hradtest t).1,h.scale_pos])
      hfull hballCutoff
      (fun z hz => by
        have hz' := (mem_filter.mp hz).2
        simpa only [threshold,highCoefficient,mul_one_div] using hz')
      hballMean (fun z _ a => hcap z a) hhigh
    exact ⟨J,hbottom,hbottom2,hdepth,ω,hgood,hnarrow⟩

end
end KakeyaFormal.SamplingMeasurableAssembly
