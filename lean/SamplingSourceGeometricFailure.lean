import SamplingGeometricFailure
import SphereNetSourceFailure

/-! The separate source one-eighth density and full-ball failure budget,
derived from actual original bounded-length measurable shadings. The law is
literally the raw law used by SphereNetSourceFailure, without equalization or
a change of support. The density tails are mu/2 and 2mu, not a narrower band. -/
namespace KakeyaFormal.SamplingSourceGeometricFailure
open Finset SamplingLengthInput SamplingLengthAssembly SamplingMeasurableAssembly SamplingNormalizedMeans
  KakeyaSamplingApplication
noncomputable section
open Classical

/-- Both event modules use the identical coupled raw product law. -/
theorem law_eq_rawLaw {k M : ℕ} {F : TubeFamily (k+1) M} {length : Fin M → ℝ}
    {Full G : Fin M → Set (Space (k+1))} {δ width R L lam c₀ C₀ xi B alpha K beta : ℝ}
    (h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta) :
    SamplingGeometricFailure.law (rawFull Full δ width R L) (rawMarked Full G δ width R L)
      (fun i z => (h.probabilities i z).1) (fun i z => (h.probabilities i z).2.1)
      (fun i z => (h.probabilities i z).2.2) = SphereNetSourceFailure.rawLaw h := rfl

/-- All fixed geometric and positive-gap parameters precede the scale cutoff.
Actual counts, full means, ball means and the test depth are derived internally.
The original full and marked probabilities remain unchanged throughout. -/
theorem source_geometric_failure (k : ℕ) (width R L sep c₀ s alpha : ℝ)
    (hw : 0 ≤ width) (hsep₀ : 0 < sep) (hc₀ : 0 < c₀)
    (hs : 0 < s) (hs1 : s < 1) (ha : 0 ≤ alpha) (hgap : alpha < 1-s) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {M : ℕ} (F : TubeFamily (k+1) M) (length : Fin M → ℝ)
        (Full G : Fin M → Set (Space (k+1))) {δ lam C₀ xi B K beta : ℝ},
        ∀ h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta,
          F.Separated (sep*δ) → δ ≤ δ₀ → δ^s ≤ lam →
          ∃ J : ℕ, δ ≤ Localization.radius J 0 ∧ Localization.radius J 0 < 2*δ ∧
            (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
            (SphereNetSourceFailure.rawLaw h).probability
              (SamplingGeometricFailure.geometricFailure (rawFull Full δ width R L)
                (SamplingBallTests.mask δ)
                (ballCutoff (J:=J) (rawFull Full δ width R L) B alpha)) < 1/8 := by
  have hpoint := pointRadius_pos (R:=R) (L:=L) hw
  have hgrid : 0 < SamplingLengthAssembly.gridConstant k width R L := by
    unfold SamplingLengthAssembly.gridConstant
    positivity
  have htcoef : 0 < directionCoefficient k sep := by
    have hp := ProjectiveGeometry.packingConstant_ge_one k
    unfold directionCoefficient
    positivity
  obtain ⟨N₀,hN₀,hsmall⟩ := SamplingGeometricFailure.uniform_threshold
    (CT:=directionCoefficient k sep)
    (CB:=directionCoefficient k sep*SamplingLengthAssembly.gridConstant k width R L*(1/Real.log 2+1))
    (cf:=c₀) (cb:=ballCoefficient k*c₀) (eta:=1-s) (phi:=1-s-alpha)
    (u:=((k+1:ℕ):ℝ)-1) (v:=2*((k+1:ℕ):ℝ))
    hc₀ (mul_pos (ballCoefficient_pos k) hc₀) (by linarith) (by linarith)
  have hN₀pos : 0 < N₀ := zero_lt_one.trans_le hN₀
  refine ⟨min 1 (min (1/N₀) (1/sep)),
    lt_min zero_lt_one (lt_min (one_div_pos.mpr hN₀pos) (one_div_pos.mpr hsep₀)),
    min_le_left _ _,?_⟩
  intro M F length Full G δ lam C₀ xi B K beta h hsep hscale hlam
  let E := SamplingBoundedSupport.support Full δ (pointRadius width R L)
  let p := rawFull Full δ width R L
  let q := rawMarked Full G δ width R L
  have hbnd : ∀ z ∈ E, ‖cellCenter δ z‖ ≤ pointRadius width R L+((k+1:ℕ):ℝ)/2 :=
    SamplingBoundedSupport.support_bounded Full h.scale_pos h.scale_le_one h.full_bounded
  have hrad : 0 ≤ pointRadius width R L+((k+1:ℕ):ℝ)/2 := by positivity
  obtain ⟨J,hbottom,hbottom2,hdepth,hradtest,hcounttest,_⟩ :=
    SamplingBallTests.construct E h.scale_pos h.scale_le_one hrad hbnd
  have hN : N₀ ≤ 1/δ := by
    have hh := (hscale.trans (min_le_right _ _)).trans (min_le_left _ _)
    exact (le_div_iff₀ h.scale_pos).mpr
      (by have hh' := (le_div_iff₀ hN₀pos).mp hh; nlinarith)
  have hN1 : 1 ≤ 1/δ := hN₀.trans hN
  have hdeltaSep : δ ≤ 1/sep := (hscale.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hlamN : (1/δ)^(-s) ≤ lam := by
    simpa only [one_div,Real.inv_rpow h.scale_pos.le,Real.rpow_neg h.scale_pos.le,inv_inv] using hlam
  have hT : (Fintype.card (Fin M):ℝ) ≤ directionCoefficient k sep*
      (1/δ)^(((k+1:ℕ):ℝ)-1) := by
    have hh := tube_count F h.scale_pos hsep₀ hdeltaSep hsep
    simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,add_sub_cancel_right,Real.rpow_natCast] using hh
  have hBalls : (Fintype.card (SamplingBallTests.Test E J):ℝ) ≤ SamplingLengthAssembly.gridConstant k width R L*
      (1/δ)^((k+1:ℕ):ℝ)*(Real.log (1/δ)/Real.log 2+1) := by
    simpa only [SamplingLengthAssembly.gridConstant,Real.rpow_natCast] using hcounttest
  have hcounts := (SamplingThreshold.source_counts (k+1) hN1 htcoef.le hgrid.le
    (by norm_num : (0:ℝ)≤0) (Nat.cast_nonneg _) (by norm_num : (0:ℝ)≤0)
    hT hBalls (by simp : (0:ℝ)≤0*(1/δ)^((k+1:ℕ):ℝ)) (Nat.cast_nonneg (Fintype.card (Fin M)))).1
  have hfull : ∀ i, c₀*lam*(1/δ) ≤ fullMean p i := by
    intro i
    simpa only [div_eq_mul_inv,mul_one,one_mul] using (h.full_mean_bounds i).1
  have hfullPower : ∀ i, c₀*(1/δ)^(1-s) ≤ fullMean p i := by
    intro i
    have hh := mul_le_mul_of_nonneg_left
      (SamplingParameterRange.full_mean_power hN1 hlamN) hc₀.le
    have hh' : c₀*(1/δ)^(1-s) ≤ c₀*lam*(1/δ) := by simpa only [mul_assoc] using hh
    exact hh'.trans (hfull i)
  have hballCutoff : ∀ i (t : SamplingBallTests.Test E J),
      (ballCoefficient k*c₀)*(1/δ)^(1-s-alpha) ≤ ballCutoff p B alpha i t := by
    intro i t
    have hr0 : 0 ≤ SamplingBallTests.testRadius t := by linarith [(hradtest t).1,h.scale_pos]
    have hcoef : 0 ≤ ballCoefficient k*B*(SamplingBallTests.testRadius t)^alpha :=
      mul_nonneg (mul_nonneg (ballCoefficient_pos k).le (zero_le_one.trans h.two_ends_constant))
        (Real.rpow_nonneg hr0 _)
    have hh := mul_le_mul_of_nonneg_left (hfull i) hcoef
    have hp := mul_le_mul_of_nonneg_left
      (SamplingParameterRange.source_mean_powers (r:=SamplingBallTests.testRadius t)
        hN1 hlamN h.two_ends_constant
        (by rw [one_div_one_div]; linarith [(hradtest t).1,h.scale_pos]) ha).2
      (mul_pos (ballCoefficient_pos k) hc₀).le
    calc
      _ ≤ (ballCoefficient k*c₀)*(B*(SamplingBallTests.testRadius t)^alpha*lam*(1/δ)) := hp
      _ = (ballCoefficient k*B*(SamplingBallTests.testRadius t)^alpha)*(c₀*lam*(1/δ)) := by ring
      _ ≤ ballCutoff p B alpha i t := hh
  have hballMean : ∀ i (t : SamplingBallTests.Test E J),
      4*ballMean p (SamplingBallTests.mask δ) i t ≤ ballCutoff p B alpha i t := by
    intro i t
    exact h.ball_test (by linarith : alpha ≤ 1) hbottom i t
  have hprob := SamplingGeometricFailure.probability_le p q
    (fun i z => (h.probabilities i z).1) (fun i z => (h.probabilities i z).2.1)
    (fun i z => (h.probabilities i z).2.2) (SamplingBallTests.mask δ)
    (ballCutoff (J:=J) p B alpha) hballMean
  have hbudget := SamplingGeometricFailure.budget_le_uniform p
    (ballCutoff (J:=J) p B alpha) hT hcounts hfullPower hballCutoff
  refine ⟨J,hbottom,hbottom2,hdepth,?_⟩
  exact (hprob.trans hbudget).trans_lt (hsmall (1/δ) hN)

end
end KakeyaFormal.SamplingSourceGeometricFailure
