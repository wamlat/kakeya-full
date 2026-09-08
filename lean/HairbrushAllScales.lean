import HairbrushCoarse

/-!
# An actual all-scale fractional-cap broad hairbrush kernel

Fine scales use the complete geometric hairbrush. Coarse scales use actual full
projective packing and integrated multiplicity. A common density-independent
radius prefactor absorbs both cases, with a concrete dimension-only logarithm.
-/
namespace KakeyaFormal.HairbrushAllScales
open MeasureTheory
open scoped ENNReal
open KakeyaFormal.ProjectiveGeometry KakeyaFormal.MeasurableEnergy
open KakeyaFormal.HairbrushSelection KakeyaFormal.HairbrushBroad
open KakeyaFormal.HairbrushFractional KakeyaFormal.HairbrushScales KakeyaFormal.HairbrushCoarse
noncomputable section

def allScaleConstant (k : ℕ) : ℝ := coarseConstant k+Real.sqrt (fractionalConstant k)

theorem allScaleConstant_pos (k : ℕ) : 0 < allScaleConstant k := by
  have h := coarseConstant_pos k
  unfold allScaleConstant
  positivity

/-- An all-scale real-cap broad hairbrush estimate with explicit original data.
The weaker common radius power d−1 (rather than (d−1)/2 at fine scales) only
changes logarithmic losses when the two chosen radii are logarithmic. The
physical scale power (m−1)/2 and density power3/2 are unchanged. -/
theorem all_scale_real_cap_hairbrush {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) (G : Set (Space (k+2)))
    {δ theta r lam B alpha m A upper : ℝ} (hM : 0 < M)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlamu : lam ≤ upper)
    (hm : 1 ≤ m) (hA : 1 ≤ A) (hu : 0 < upper) (hsep : F.Separated δ)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hG : MeasurableSet G)
    (hgood : (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 ≤ markedMass (ν := volume) Y G)
    (hbroad : δ ≤ theta → ∀ x ∈ G, ∀ i, x ∈ Y i →
      (nearCount F.tube Y i theta x:ℝ) ≤ MeasurableEnergy.multiplicity Y x/2)
    (hmass : ∀ i, lam*δ^(k+1) ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hsmall : B*r^alpha ≤ 1/2) (hcap : F.CapBound δ m A)
    (hupper : ∀ i, (volume : Measure (Space (k+2))).real (Y i) ≤ upper*δ^(k+1)) :
    (r*theta)^(k+1)*markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)/
        (allScaleConstant k*Real.sqrt (A*upper)*(hairbrushLog k δ)^((5:ℝ)/2)) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  let L := hairbrushLog k δ
  have hL : 0 < L := hairbrushLog_pos hδ hδ1
  have hJL := multiplicityDepth_log_bound (k := k) hδ hδ1
  have hL1 : 1 ≤ L := by
    have hJ : (0:ℝ) ≤ multiplicityDepth k δ := Nat.cast_nonneg _
    change (multiplicityDepth k δ:ℝ)+1 ≤ L at hJL
    linarith
  have hApos : 0 < A := by linarith
  have hW : 0 ≤ markedMass (ν := volume) Y G := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hC := allScaleConstant_pos k
  have hco := coarseConstant_pos k
  have hfr := fractionalConstant_pos k
  have hD : 0 < allScaleConstant k*Real.sqrt (A*upper)*L^((5:ℝ)/2) := by positivity
  by_cases hscale : 88*δ ≤ r*theta
  · have h := real_cap_hairbrush_linear F Y G (multiplicityDepth k δ) hM hδ htheta htheta1 hr hr1 hscale
      hlam hL hJL (hairbrushLog_covers_row hδ hδ1) (multiplicityDepth_covers F hδ hδ1 hsep)
      hsep hY hsub hG hgood
      (hbroad (by nlinarith [mul_le_mul_of_nonneg_right hr1 htheta.le]))
      hmass hends hsmall hApos hu hcap hupper
    have hrt1 : r*theta ≤ 1 := (mul_le_mul_of_nonneg_left htheta1 hr.le).trans (by simpa using hr1)
    have hpow : (r*theta)^(k+1) ≤ (r*theta)^((k+1:ℕ)/2:ℝ) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_ge (by positivity) hrt1
      have hk : (0:ℝ) ≤ (k+1:ℕ) := Nat.cast_nonneg _
      linarith
    have hnum := mul_le_mul_of_nonneg_right hpow
      (by positivity : 0 ≤ markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2))
    have hroot : Real.sqrt (fractionalConstant k*A*upper) =
        Real.sqrt (fractionalConstant k)*Real.sqrt (A*upper) := by
      rw [mul_assoc,Real.sqrt_mul hfr.le]
    have hden : Real.sqrt (fractionalConstant k*A*upper)*L^((5:ℝ)/2) ≤
        allScaleConstant k*Real.sqrt (A*upper)*L^((5:ℝ)/2) := by
      rw [hroot]
      have hh : Real.sqrt (fractionalConstant k) ≤ allScaleConstant k := by
        unfold allScaleConstant
        linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg _)) (by positivity)
    have hfirst := div_le_div_of_nonneg_right hnum hD.le
    have hsecond := div_le_div_of_nonneg_left
      (by positivity : 0 ≤ (r*theta)^((k+1:ℕ)/2:ℝ)*(markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)))
      (by positivity : 0 < Real.sqrt (fractionalConstant k*A*upper)*L^((5:ℝ)/2)) hden
    have hid₁ : (r*theta)^((k+1:ℕ)/2:ℝ)*(markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)) =
        markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)*(r*theta)^((k+1:ℕ)/2:ℝ) := by ring
    rw [hid₁] at hsecond
    have hid₂ : (r*theta)^(k+1)*(markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)) =
        (r*theta)^(k+1)*markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2) := by ring
    rw [hid₂] at hfirst
    have hid₃ : (r*theta)^((k+1:ℕ)/2:ℝ)*(markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)) =
        markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)*(r*theta)^((k+1:ℕ)/2:ℝ) := by ring
    rw [hid₃] at hfirst
    exact hfirst.trans (hsecond.trans h)

  · have h := coarse_hairbrush_union_lower F Y G hδ hδ1 hr htheta (le_of_lt (lt_of_not_ge hscale)) hsep hY hsub
    have hfactor := fractional_factor_le_one hlam hlam1 hlamu hδ hδ1 hm hA hu hL1
    have hcoeff : (r*theta)^(k+1)*markedMass (ν := volume) Y G/allScaleConstant k ≤
        (r*theta)^(k+1)*markedMass (ν := volume) Y G/coarseConstant k := by
      apply div_le_div_of_nonneg_left (by positivity) hco
      unfold allScaleConstant
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left hfactor
      (by positivity : 0 ≤ (r*theta)^(k+1)*markedMass (ν := volume) Y G/allScaleConstant k)
    rw [mul_one] at hmul
    have hid : ((r*theta)^(k+1)*markedMass (ν := volume) Y G/allScaleConstant k)*
        (lam^((3:ℝ)/2)*δ^((m-1)/2)/(Real.sqrt (A*upper)*L^((5:ℝ)/2))) =
      (r*theta)^(k+1)*markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)/
        (allScaleConstant k*Real.sqrt (A*upper)*L^((5:ℝ)/2)) := by ring
    rw [hid] at hmul
    exact hmul.trans (hcoeff.trans h)

end
end KakeyaFormal.HairbrushAllScales

#print axioms KakeyaFormal.HairbrushAllScales.all_scale_real_cap_hairbrush
