import HairbrushBroad

/-!
# Actual real-cap linearization of the broad hairbrush

The same real cap exponent m controls the total original tube count through an
actual finite radius-one cap cover. It is combined with the proved measurable
broad hairbrush, retaining m in the physical exponent (m−1)/2.
-/
namespace KakeyaFormal.HairbrushFractional
open MeasureTheory
open scoped ENNReal
open KakeyaFormal.HairbrushBroad KakeyaFormal.HairbrushSelection
open KakeyaFormal.MeasurableEnergy KakeyaFormal.ProjectiveGeometry
noncomputable section

/-- Actual upper shading density and actual real direction caps bound the marked
incidence mass with the same real m. -/
theorem marked_mass_cap_upper {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) (G : Set (Space (k+2))) {δ m A upper : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A) (hu : 0 ≤ upper)
    (hcap : F.CapBound δ m A)
    (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hmass : ∀ i, (volume : Measure (Space (k+2))).real (Y i) ≤ upper*δ^(k+1)) :
    markedMass (ν := volume) Y G ≤ packingConstant (k+1)*A*upper*δ^(k+1)*δ^(-m) := by
  have htotal := CapCover.cap_bound_total_count_scale F hδ hδ1 hA hcap
  have hterm (i : Fin M) : (volume : Measure (Space (k+2))).real (Y i ∩ G) ≤ upper*δ^(k+1) :=
    (measureReal_mono Set.inter_subset_left
      (measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite (F.tube i) δ))).trans (hmass i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) => hterm i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
  have hm := mul_le_mul_of_nonneg_right htotal (by positivity : 0 ≤ upper*δ^(k+1))
  have hid : (packingConstant (k+1)*A*δ^(-m))*(upper*δ^(k+1)) =
      packingConstant (k+1)*A*upper*δ^(k+1)*δ^(-m) := by ring
  exact hs.trans (hm.trans_eq hid)

/-- Dimensional constant after the actual real-cap total-count bound. -/
def fractionalConstant (k : ℕ) : ℝ := broadConstant k*packingConstant (k+1)

theorem fractionalConstant_pos (k : ℕ) : 0 < fractionalConstant k := by
  exact mul_pos (broadConstant_pos k) (lt_of_lt_of_le (by norm_num) (packingConstant_ge_one (k+1)))

/-- The exact scale identity in the real-m linearization. -/
theorem fractional_scale_identity {δ m : ℝ} (hδ : 0 < δ) (k : ℕ) :
    δ^(k+1)*δ^(-m)*δ^(m-1) = δ^k := by
  rw [← Real.rpow_natCast δ (k+1),← Real.rpow_natCast δ k,
    ← Real.rpow_add hδ,← Real.rpow_add hδ]
  congr 1
  push_cast
  ring

/-- The fine-scale real-cap hairbrush (4.16), in squared form. No cap-cover
cardinality, broad hairbrush bound, stem selection or support estimate is an
assumption; all are applied to the actual original tube family. -/
theorem real_cap_hairbrush_squared {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) (G : Set (Space (k+2)))
    {δ theta r lam L B alpha m A upper : ℝ} (J : ℕ) (hM : 0 < M)
    (hδ : 0 < δ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hscale : 88*δ ≤ r*theta)
    (hlam : 0 ≤ lam) (hL : 0 < L) (hJL : (J:ℝ)+1 ≤ L)
    (hlogL : Real.logb 2 (2/δ)+2 ≤ L) (htop : (M:ℝ) ≤ (2:ℝ)^J)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (F.tube i).direction (F.tube j).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hG : MeasurableSet G)
    (hgood : (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 ≤ markedMass (ν := volume) Y G)
    (hbroad : ∀ x ∈ G, ∀ i, x ∈ Y i →
      (nearCount F.tube Y i theta x:ℝ) ≤ MeasurableEnergy.multiplicity Y x/2)
    (hmass : ∀ i, lam*δ^(k+1) ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hsmall : B*r^alpha ≤ 1/2) (hA : 0 < A) (hu : 0 < upper)
    (hcap : F.CapBound δ m A)
    (hupper : ∀ i, (volume : Measure (Space (k+2))).real (Y i) ≤ upper*δ^(k+1)) :
    (markedMass (ν := volume) Y G)^2*lam^3*δ^(m-1)*(r*theta)^(k+1)/
        (fractionalConstant k*A*upper*L^5) ≤
      ((volume : Measure (Space (k+2))).real (⋃ i, Y i))^2 := by
  have : Nonempty (Fin M) := Fin.pos_iff_nonempty.mp hM
  have hδ1 : δ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left htheta1 hr.le]
  have hcore := broad_hairbrush_squared F.tube Y G J hδ htheta htheta1 hr hr1 hscale
    hlam hL hJL hlogL (by simpa only [Fintype.card_fin] using htop)
    hdir hY hsub hG hgood hbroad hmass hends hsmall
  have hmax := marked_mass_cap_upper F Y G hδ hδ1 hA.le hu.le hcap hsub hupper
  have hW : 0 ≤ markedMass (ν := volume) Y G := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hmul := mul_le_mul_of_nonneg_left hmax
    (by positivity : 0 ≤ markedMass (ν := volume) Y G*lam^3*δ^(m-1)*(r*theta)^(k+1))
  have hid : (markedMass (ν := volume) Y G*lam^3*δ^(m-1)*(r*theta)^(k+1)) *
      (packingConstant (k+1)*A*upper*δ^(k+1)*δ^(-m)) =
      (packingConstant (k+1)*A*upper) *
        (markedMass (ν := volume) Y G*lam^3*δ^k*(r*theta)^(k+1)) := by
    calc
      _ = (packingConstant (k+1)*A*upper)*markedMass (ν := volume) Y G*lam^3*
          (r*theta)^(k+1)*(δ^(k+1)*δ^(-m)*δ^(m-1)) := by ring
      _ = _ := by rw [fractional_scale_identity hδ k]; ring
  rw [hid] at hmul
  have hC := broadConstant_pos k
  have hP := packingConstant_ge_one (k+1)
  have hB := (div_le_iff₀ (by positivity : 0 < broadConstant k*L^5)).mp hcore
  have hh := hmul.trans (mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ packingConstant (k+1)*A*upper))
  apply (div_le_iff₀ (by have hc := fractionalConstant_pos k; positivity : 0 < fractionalConstant k*A*upper*L^5)).mpr
  dsimp [fractionalConstant]
  nlinarith [hh]

/-- Exact half-power square identity used to recover the stated unsquared
physical scale and density exponents. -/
theorem half_power_square {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x^(a/2))^2 = x^a := by
  rw [← Real.rpow_mul_natCast hx]
  congr 1
  norm_num

/-- Algebraic square-root extraction from the proved geometric squared estimate.
The explicit exponents are the manuscript's λ^(3/2), δ^((m−1)/2), and L^(-5/2). -/
theorem fractional_square_root {k : ℕ} {W lam δ r theta L A upper E m : ℝ}
    (hW : 0 ≤ W) (hlam : 0 ≤ lam) (hδ : 0 < δ) (hr : 0 < r) (htheta : 0 < theta)
    (hL : 0 < L) (hA : 0 < A) (hu : 0 < upper) (hE : 0 ≤ E)
    (hsq : W^2*lam^3*δ^(m-1)*(r*theta)^(k+1)/(fractionalConstant k*A*upper*L^5) ≤ E^2) :
    W*lam^((3:ℝ)/2)*δ^((m-1)/2)*(r*theta)^((k+1:ℕ)/2:ℝ)/
        (Real.sqrt (fractionalConstant k*A*upper)*L^((5:ℝ)/2)) ≤ E := by
  have hC := fractionalConstant_pos k
  have hden : 0 < Real.sqrt (fractionalConstant k*A*upper)*L^((5:ℝ)/2) := by positivity
  have hlamPow : (lam^((3:ℝ)/2))^2 = lam^3 := by simpa using half_power_square hlam 3
  have hδpow := half_power_square hδ.le (m-1)
  have hrt : ((r*theta)^((k+1:ℕ)/2:ℝ))^2 = (r*theta)^(k+1) := by
    simpa only [Real.rpow_natCast] using half_power_square (by positivity : 0 ≤ r*theta) (k+1:ℕ)
  have hLpow : (L^((5:ℝ)/2))^2 = L^5 := by simpa using half_power_square hL.le 5
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ fractionalConstant k*A*upper)
  have hlhs : (W*lam^((3:ℝ)/2)*δ^((m-1)/2)*(r*theta)^((k+1:ℕ)/2:ℝ))^2 =
      W^2*lam^3*δ^(m-1)*(r*theta)^(k+1) := by simp only [mul_pow,hlamPow,hδpow,hrt]
  have hrhs : (E*(Real.sqrt (fractionalConstant k*A*upper)*L^((5:ℝ)/2)))^2 =
      E^2*(fractionalConstant k*A*upper*L^5) := by simp only [mul_pow,hroot,hLpow]
  have hh := (div_le_iff₀ (by positivity : 0 < fractionalConstant k*A*upper*L^5)).mp hsq
  apply (div_le_iff₀ hden).mpr
  have hleft : 0 ≤ W*lam^((3:ℝ)/2)*δ^((m-1)/2)*(r*theta)^((k+1:ℕ)/2:ℝ) := by positivity
  have hright : 0 ≤ E*(Real.sqrt (fractionalConstant k*A*upper)*L^((5:ℝ)/2)) := by positivity
  nlinarith

/-- Equation (4.16) for an actual real-cap tube family and actual measurable
shadings, with the displayed physical exponents and an explicit dimensional
constant. The full geometric and measure-theoretic proof is invoked internally. -/
theorem real_cap_hairbrush_linear {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) (G : Set (Space (k+2)))
    {δ theta r lam L B alpha m A upper : ℝ} (J : ℕ) (hM : 0 < M)
    (hδ : 0 < δ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hscale : 88*δ ≤ r*theta)
    (hlam : 0 ≤ lam) (hL : 0 < L) (hJL : (J:ℝ)+1 ≤ L)
    (hlogL : Real.logb 2 (2/δ)+2 ≤ L) (htop : (M:ℝ) ≤ (2:ℝ)^J)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (F.tube i).direction (F.tube j).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hG : MeasurableSet G)
    (hgood : (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 ≤ markedMass (ν := volume) Y G)
    (hbroad : ∀ x ∈ G, ∀ i, x ∈ Y i →
      (nearCount F.tube Y i theta x:ℝ) ≤ MeasurableEnergy.multiplicity Y x/2)
    (hmass : ∀ i, lam*δ^(k+1) ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hsmall : B*r^alpha ≤ 1/2) (hA : 0 < A) (hu : 0 < upper)
    (hcap : F.CapBound δ m A)
    (hupper : ∀ i, (volume : Measure (Space (k+2))).real (Y i) ≤ upper*δ^(k+1)) :
    markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)*(r*theta)^((k+1:ℕ)/2:ℝ)/
        (Real.sqrt (fractionalConstant k*A*upper)*L^((5:ℝ)/2)) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  have hsq := real_cap_hairbrush_squared F Y G J hM hδ htheta htheta1 hr hr1 hscale
    hlam hL hJL hlogL htop hdir hY hsub hG hgood hbroad hmass hends hsmall hA hu hcap hupper
  have hW : 0 ≤ markedMass (ν := volume) Y G := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  exact fractional_square_root hW hlam hδ hr htheta hL hA hu measureReal_nonneg hsq

end
end KakeyaFormal.HairbrushFractional

#print axioms KakeyaFormal.HairbrushFractional.real_cap_hairbrush_squared

#print axioms KakeyaFormal.HairbrushFractional.real_cap_hairbrush_linear
