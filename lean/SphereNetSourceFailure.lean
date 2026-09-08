import SphereNetFailure
import SamplingLengthAssembly

/-!
# Literal angular failure budget on original measurable source data

Actual bounded-variable-length carriers construct the original cell support,
raw probabilities, high cells and full-sphere net tests. All geometric means and
test counts are discharged, giving the source (6.19) probability bound with a
uniform cutoff. The density and ball events are not part of this theorem.
-/
namespace KakeyaFormal.SphereNetSourceFailure
open Finset MeasureTheory ProjectiveSphereNet SphereNetFailure SamplingLengthInput
  KakeyaSamplingApplication SamplingMeasurableAssembly
open scoped BigOperators
noncomputable section
open Classical

/-- The actual raw product law from the original source input. -/
def rawLaw {k M : ℕ} {F : TubeFamily (k+1) M} {length : Fin M → ℝ}
    {Full G : Fin M → Set (Space (k+1))} {δ width R L lam c₀ C₀ xi B alpha K beta : ℝ}
    (h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta) :
    KakeyaSampling.FiniteLaw (Outcome (Fin M)
      ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L))) :=
  SphereNetFailure.law (SamplingLengthInput.rawFull Full δ width R L)
    (SamplingLengthInput.rawMarked Full G δ width R L)
    (fun i z => (h.probabilities i z).1) (fun i z => (h.probabilities i z).2.1)
    (fun i z => (h.probabilities i z).2.2)

/-- Actual expected marked multiplicity defines the same source high cells. -/
def highCells {k M : ℕ} (Full G : Fin M → Set (Space (k+1))) (δ width R L : ℝ) :
    Finset ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L)) :=
  KakeyaSamplingDichotomy.high (markedMean (SamplingLengthInput.rawMarked Full G δ width R L))
    (threshold k δ)

/-- All constants and the scale cutoff precede every original family, shading,
density, broadness constant, and actual constructed net. This is the complete
source angular display (6.19), including both high-cell and cap-test failures. -/
theorem source_angular_failure (k : ℕ) (width R L K₀ beta logPower : ℝ)
    (hw : 0 ≤ width) (hK₀ : 0 < K₀) (hbeta : 0 < beta) (hlog : 0 ≤ logPower) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {M : ℕ} (F : TubeFamily (k+1) M) (length : Fin M → ℝ)
        (Full G : Fin M → Set (Space (k+1))) {δ lam c₀ C₀ xi B alpha K : ℝ},
        ∀ h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta,
          δ ≤ δ₀ → K ≤ K₀*(Real.log (2/δ))^logPower →
          ∃ net : Net k (SamplingTheta.choice K beta),
            δ ≤ 2*SamplingTheta.choice K beta ∧ 2*SamplingTheta.choice K beta ≤ 1 ∧
            ((highCells Full G δ width R L).card : ℝ)*(1+(net.points.card : ℝ)) ≤
              (1/δ)^(((k+1 : ℕ) : ℝ)+2) ∧
            (rawLaw h).probability
              (angularFailure (SamplingLengthInput.rawMarked Full G δ width R L)
                (highCells Full G δ width R L) (SphereNetCapTests.cap net F)) ≤
              (1/δ)^(((k+1 : ℕ) : ℝ)+2)*Real.exp (-(highCoefficient k*Real.log (2/δ))/8) ∧
            (1/δ)^(((k+1 : ℕ) : ℝ)+2)*Real.exp (-(highCoefficient k*Real.log (2/δ))/8) < 1/8 := by
  let P := SamplingLengthAssembly.gridConstant k width R L
  have hpoint : 0 < pointRadius width R L := pointRadius_pos hw
  have hP : 0 < P := by dsimp [P, SamplingLengthAssembly.gridConstant]; positivity
  let theta₀ := SamplingTheta.choice K₀ beta
  have htheta₀ : 0 < theta₀ := SamplingTheta.choice_pos hK₀
  obtain ⟨N₁, hN₁, hcount⟩ := SphereNetFailure.test_count_threshold k
    (one_div_pos.mpr htheta₀) (div_nonneg hlog hbeta.le) hP.le
  let N₀ := max 16 N₁
  have hN₀ : 0 < N₀ := lt_of_lt_of_le (by norm_num : (0:ℝ)<16) (le_max_left _ _)
  obtain ⟨δa, hδa, hδa1, hangular⟩ := SamplingTheta.uniform_small_scales hK₀ hbeta hlog
  refine ⟨min δa (1/N₀), lt_min hδa (one_div_pos.mpr hN₀),
    (min_le_left _ _).trans hδa1, ?_⟩
  intro M F length Full G δ lam c₀ C₀ xi B alpha K h hsmall hK
  obtain ⟨htheta, hbottom, hupper, _, hlower⟩ := hangular δ K h.scale_pos
    (hsmall.trans (min_le_left _ _)) h.broadness_constant hK
  obtain ⟨net⟩ := ProjectiveSphereNet.exists_net htheta (by linarith)
  have hN : N₀ ≤ 1/δ := by
    have hh := hsmall.trans (min_le_right _ _)
    exact (le_div_iff₀ h.scale_pos).mpr
      (by have hh' := (le_div_iff₀ hN₀).mp hh; nlinarith)
  have hN16 : 16 ≤ 1/δ := (le_max_left _ _).trans hN
  have hN1 : 1 ≤ 1/δ := by linarith
  have hLp : 0 < Real.log (2/δ) := by
    apply Real.log_pos
    have he : 2/δ = 2*(1/δ) := by ring
    rw [he]
    linarith
  have hinv : 1/SamplingTheta.choice K beta ≤
      (1/theta₀)*(Real.log (2*(1/δ)))^(logPower/beta) := by
    have hlo : theta₀*(Real.log (2/δ))^(-(logPower/beta)) ≤ SamplingTheta.choice K beta := by
      simpa only [neg_div] using hlower
    have hh := one_div_le_one_div_of_le
      (mul_pos htheta₀ (Real.rpow_pos_of_pos hLp _)) hlo
    calc
      _ ≤ 1/(theta₀*(Real.log (2/δ))^(-(logPower/beta))) := hh
      _ = _ := by rw [one_div, mul_inv_rev, Real.rpow_neg hLp.le, inv_inv]; simp only [mul_one_div]; ring
  let E := SamplingBoundedSupport.support Full δ (pointRadius width R L)
  have hbnd : ∀ z ∈ E, ‖cellCenter δ z‖ ≤ pointRadius width R L+((k+1 : ℕ) : ℝ)/2 :=
    SamplingBoundedSupport.support_bounded Full h.scale_pos h.scale_le_one h.full_bounded
  have hrad : 0 ≤ pointRadius width R L+((k+1 : ℕ) : ℝ)/2 := by positivity
  have hE := SamplingBallTests.support_card E h.scale_pos h.scale_le_one hrad hbnd
  have hHighCount : ((highCells Full G δ width R L).card : ℝ) ≤
      P*(1/δ)^((k+1 : ℕ) : ℝ) := by
    have hc : ((highCells Full G δ width R L).card : ℝ) ≤ (E.card : ℝ) := by
      have hh := Finset.card_le_univ (highCells Full G δ width R L)
      simpa only [Fintype.card_coe, E] using (Nat.cast_le (α := ℝ)).mpr hh
    exact hc.trans (by simpa only [P, SamplingLengthAssembly.gridConstant, Real.rpow_natCast] using hE)
  have htests := hcount ((le_max_right _ _).trans hN) net hinv (highCells Full G δ width R L) hHighCount
  have hmean : ∀ z ∈ highCells Full G δ width R L,
      highCoefficient k*Real.log (2/δ) ≤
        markedMean (SamplingLengthInput.rawMarked Full G δ width R L) z := by
    intro z hz
    exact (mem_filter.mp hz).2
  have hcap : ∀ z ∈ highCells Full G δ width R L, ∀ a,
      1000*capMean (SamplingLengthInput.rawMarked Full G δ width R L)
        (SphereNetCapTests.cap net F) z a ≤
          markedMean (SamplingLengthInput.rawMarked Full G δ width R L) z := by
    intro z _ a
    exact SphereNetCapTests.source_cap_test net F G _ h.scale_pos h.broadness_constant hbeta
      hbottom h.marked_measurable h.broadness z a
  have hprob := SphereNetFailure.probability_le
    (SamplingLengthInput.rawFull Full δ width R L) (SamplingLengthInput.rawMarked Full G δ width R L)
    (fun i z => (h.probabilities i z).1) (fun i z => (h.probabilities i z).2.1)
    (fun i z => (h.probabilities i z).2.2) (highCells Full G δ width R L)
    (SphereNetCapTests.cap net F) hmean hcap
  simp only [Fintype.card_fin] at hprob
  refine ⟨net, hbottom, hupper, htests, ?_, ?_⟩
  · exact hprob.trans (mul_le_mul_of_nonneg_right htests (Real.exp_pos _).le)
  · simpa only [highCoefficient, mul_one_div] using SphereNetFailure.source_tail k hN16

end
end KakeyaFormal.SphereNetSourceFailure
