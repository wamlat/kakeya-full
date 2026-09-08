import SamplingParameterRange
import SamplingRawMeans
import SamplingMeasurableAssembly

/-! Actual source sampling with raw cell probabilities and arbitrary fixed
0<s<1, 0≤alpha<1-s. No expected-value or outcome oracle is a hypothesis. -/
namespace KakeyaFormal.SamplingRawAssembly
open Finset SamplingNormalizedMeans SamplingSupport KakeyaSamplingApplication SamplingMeasurableAssembly
open scoped BigOperators
noncomputable section
open Classical

/-- One actual outcome supplies every finite ball/cap test and the narrow
per-tube density band. No expectation or probability budget is a field. -/
def HighResult {n M : ℕ} (F : TubeFamily (n+1) M)
    (Full G : Fin M → Set (Space (n+1))) (δ width R B alpha theta : ℝ) : Prop :=
  let E := support F.tube Full δ width R
  let p := rawFull F Full δ width R
  let q := rawMarked F Full G δ width R
  let high := KakeyaSamplingDichotomy.high (markedMean q) (threshold n δ)
  ∃ J : ℕ, δ ≤ Localization.radius J 0 ∧ Localization.radius J 0 < 2*δ ∧
    (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
    ∃ ω : Outcome (Fin M) ↥E,
      SampleGood p q high (SamplingBallTests.mask δ) (SamplingCapTests.cap F theta)
        (ballCutoff (J:=J) p B alpha) ω ∧
      ∀ i, (2/3:ℝ)*fullMean p i ≤ (fullShading ω i).card ∧
        ((fullShading ω i).card:ℝ) ≤ (4/3:ℝ)*fullMean p i

/-- The low alternative retains the exact original total marked mass, as
well as the actual positivity and threshold of each counted cell. -/
def LowResult {n M : ℕ} (F : TubeFamily (n+1) M)
    (Full G : Fin M → Set (Space (n+1))) (δ width R : ℝ) : Prop :=
  let q := rawMarked F Full G δ width R
  let W := (∑ i, (MeasureTheory.volume : MeasureTheory.Measure (Space (n+1))).real (G i))/δ^(n+1)
  W/2 ≤ ∑ z ∈ KakeyaSamplingDichotomy.low (markedMean q) (threshold n δ), markedMean q z ∧
    W/(2*threshold n δ) ≤
      ((KakeyaSamplingDichotomy.low (markedMean q) (threshold n δ)).card:ℝ)

/-- The actual low/high alternative of Section 6 with its original raw probabilities.
All support/test counts follow from bounded original carriers and separated
original directions; all expected masses follow from physical shading data.
The existential scale cutoff precedes every original family and shading. -/
theorem construct (n : ℕ) (width R c₀ C₀ K₀ beta logPower s alpha : ℝ)
    (hw : 0 ≤ width) (hc₀ : 0 < c₀) (hK₀ : 0 < K₀)
    (hbeta : 0 < beta) (hlog : 0 ≤ logPower)
    (hs : 0 < s) (hs1 : s < 1) (ha : 0 ≤ alpha) (hgap : alpha < 1-s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {M : ℕ} (F : TubeFamily (n+1) M) (Full G : Fin M → Set (Space (n+1)))
      {δ lam xi B K : ℝ},
      Input F Full G δ width R lam c₀ C₀ xi B alpha K beta →
      F.Separated δ → δ ≤ δ₀ → (1/δ)^(-s) ≤ lam →
      K ≤ K₀*(Real.log (2/δ))^logPower →
      let theta := SamplingTheta.choice K beta
      let q := rawMarked F Full G δ width R
      0 < theta ∧ δ ≤ 2*theta ∧ 2*theta ≤ 1 ∧
      SamplingTheta.choice K₀ beta*(Real.log (2/δ))^(-logPower/beta) ≤ theta ∧
      ((LowResult F Full G δ width R ∧
       (xi*lam*(M:ℝ)/δ)/(2*threshold n δ) ≤
        ((KakeyaSamplingDichotomy.low (markedMean q) (threshold n δ)).card:ℝ)) ∨
       HighResult F Full G δ width R B alpha theta) := by
  have hgrid := gridConstant_pos (n:=n) (R:=R) hw
  obtain ⟨N₀,hN₀,hsample⟩ := SamplingParameterRange.source_sampling_narrow (n+1) s alpha hs hs1 ha hgap
    (CT:=ProjectiveGeometry.packingConstant n)
    (CB:=gridConstant n width R) (CE:=gridConstant n width R)
    (cf:=c₀) (cb:=ballCoefficient n*c₀)
    (zero_le_one.trans (ProjectiveGeometry.packingConstant_ge_one n))
    hgrid.le hgrid.le hc₀ (mul_pos (ballCoefficient_pos n) hc₀)
  obtain ⟨δa,hδa,hδa1,hangular⟩ := SamplingTheta.uniform_small_scales hK₀ hbeta hlog
  refine ⟨min δa (1/N₀),lt_min hδa (one_div_pos.mpr (zero_lt_one.trans_le hN₀)),
    (min_le_left _ _).trans hδa1,?_⟩
  intro M F Full G δ lam xi B K h hsep hscale hlam hK theta q
  obtain ⟨htheta,hbottomTheta,hupperTheta,_,hlowerTheta⟩ :=
    hangular δ K h.scale_pos (hscale.trans (min_le_left _ _)) h.broadness_constant hK
  have hcap := SamplingRawMeans.cap_test h hbottomTheta
  refine ⟨htheta,hbottomTheta,hupperTheta,hlowerTheta,?_⟩
  have hq : ∀ i z, 0 ≤ q i z := fun i z => (h.raw_probabilities i z).1
  have hcut := threshold_pos (n:=n) h.scale_pos h.scale_le_one
  rcases KakeyaSamplingDichotomy.marked_dichotomy q hq hcut with hlo | hhigh
  · apply Or.inl
    refine ⟨?_,?_⟩
    · simpa only [LowResult,← SamplingRawMeans.marked_mean_eq h] using hlo
    have hm := SamplingRawMeans.marked_mean_lower h
    exact (div_le_div_of_nonneg_right hm (by positivity)).trans hlo.2
  · apply Or.inr
    let E := support F.tube Full δ width R
    let p := rawFull F Full δ width R
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
    have hfull : ∀ i, c₀*lam*(1/δ) ≤ fullMean p i := by
      intro i
      simpa only [div_eq_mul_inv,mul_one,one_mul] using (SamplingRawMeans.full_mean_bounds h i).1
    have hballCutoff : ∀ i t, (ballCoefficient n*c₀)*B*
        (SamplingBallTests.testRadius t)^alpha*lam*(1/δ) ≤ ballCutoff (J:=J) p B alpha i t := by
      intro i t
      have hrad0 : 0 ≤ SamplingBallTests.testRadius t := by
        linarith [(hradtest t).1,h.scale_pos]
      have hcoef : 0 ≤ ballCoefficient n*B*(SamplingBallTests.testRadius t)^alpha :=
        mul_nonneg (mul_nonneg (ballCoefficient_pos n).le (zero_le_one.trans h.two_ends_constant))
          (Real.rpow_nonneg hrad0 _)
      have hh := mul_le_mul_of_nonneg_left (hfull i) hcoef
      exact (by ring : (ballCoefficient n*c₀)*B*(SamplingBallTests.testRadius t)^alpha*lam*(1/δ) =
        (ballCoefficient n*B*(SamplingBallTests.testRadius t)^alpha)*(c₀*lam*(1/δ))).trans_le hh
    have hballMean : ∀ i t, 4*ballMean p (SamplingBallTests.mask δ) i t ≤
        ballCutoff (J:=J) p B alpha i t := by
      intro i t
      exact SamplingRawMeans.ball_test h (by linarith : alpha ≤ 1) hbottom i t
    obtain ⟨ω,hgood,hnarrow⟩ := hsample (1/δ) hN (Fin M) ↥E (SamplingBallTests.Test E J) (Fin M)
      p q (KakeyaSamplingDichotomy.high (markedMean q) (threshold n δ))
      (SamplingBallTests.mask δ) (SamplingCapTests.cap F theta)
      (ballCutoff (J:=J) p B alpha) SamplingBallTests.testRadius lam B
      hq (fun i z => (h.raw_probabilities i z).2.1)
      (fun i z => (h.raw_probabilities i z).2.2)
      hT hBalls hHighCount le_rfl hlam h.two_ends_constant
      (fun t => by rw [one_div_one_div]; linarith [(hradtest t).1,h.scale_pos])
      hfull hballCutoff
      (fun z hz => by
        have hz' := (mem_filter.mp hz).2
        simpa only [threshold,highCoefficient,mul_one_div] using hz')
      hballMean (fun z _ a => hcap z a) hhigh
    exact ⟨J,hbottom,hbottom2,hdepth,ω,hgood,hnarrow⟩

end
end KakeyaFormal.SamplingRawAssembly
