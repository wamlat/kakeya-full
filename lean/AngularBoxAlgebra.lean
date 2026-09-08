import AngularBoxHairbrush

/-! Exact density and angular-scale powers of the constructed one-box estimate. -/
namespace KakeyaFormal.AngularBoxAlgebra
open MeasureTheory AngularBoxRecovery AngularBoxHairbrush HairbrushScales HairbrushAllScales
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- The selected lower density and common upper density combine to exactly
the quadratic density factor, with the explicit retention constant. -/
theorem density_factor_identity {e lam A : ℝ} (he : 0 < e) (hlam : 0 < lam) (hA : 0 < A) :
    e*lam*(e*lam/2)^((3:ℝ)/2)/(4*Real.sqrt (A*(2*lam))) =
      e^((5:ℝ)/2)*lam^2/(16*Real.sqrt A) := by
  have hpow (x : ℝ) (hx : 0 < x) : x^((3:ℝ)/2) = x*Real.sqrt x := by
    rw [show (3:ℝ)/2 = 1+1/2 by norm_num,Real.rpow_add hx,Real.rpow_one,Real.sqrt_eq_rpow]
  have hepow : e^((5:ℝ)/2) = e^2*Real.sqrt e := by
    rw [show (5:ℝ)/2 = 2+1/2 by norm_num,Real.rpow_add he,Real.rpow_two,Real.sqrt_eq_rpow]
  rw [hpow _ (by positivity),hepow,Real.sqrt_div (by positivity),Real.sqrt_mul he.le,
    Real.sqrt_mul hA.le,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hsA := Real.sqrt_ne_zero'.mpr hA
  have hsl := Real.sqrt_ne_zero'.mpr hlam
  have hs2 : Real.sqrt (2:ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hsq2 : (Real.sqrt (2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

/-- All non-scale losses in the one-box estimate. It is independent of
shading density, physical scale, angular scale and original family size. -/
def densityConstant (k : ℕ) (angular eta alpha beta B K m A : ℝ) : ℝ :=
  (concentrationRadius (endsCoefficient k angular B eta) alpha*
    concentrationRadius (broadCoefficient k angular beta K eta) beta)^(k+1)*
    (retention k angular eta)^((5:ℝ)/2)/
    (16*allScaleConstant k*Real.sqrt (capCoefficient k angular m A))

theorem densityConstant_pos (k : ℕ) {angular eta alpha beta B K m A : ℝ}
    (ha : 0 ≤ angular) (heta : 0 < eta) (hB : 0 < B) (hK : 0 < K) (hA : 0 < A) :
    0 < densityConstant k angular eta alpha beta B K m A := by
  have he := retention_pos k (angular := angular) heta
  have hAng : 0 < angularLoss angular := lt_of_lt_of_le (by norm_num) (angularLoss_ge_one ha)
  have hPc : 0 < ProjectiveGeometry.packingConstant (k+1) := lt_of_lt_of_le (by norm_num) (ProjectiveGeometry.packingConstant_ge_one _)
  have hCap : 0 < capCoefficient k angular m A := by unfold capCoefficient; positivity
  have hEnds : 0 < endsCoefficient k angular B eta := by unfold endsCoefficient; positivity
  have hBroad : 0 < broadCoefficient k angular beta K eta := by unfold broadCoefficient; positivity
  have hR₁ := concentrationRadius_pos (alpha := alpha) hEnds
  have hR₂ := concentrationRadius_pos (alpha := beta) hBroad
  have hC := allScaleConstant_pos k
  unfold densityConstant
  positivity

/-- Exact quadratic density normal form of the actual constructed bound. -/
theorem boxLowerBound_density_identity (k M : ℕ) {angular eta lam alpha beta B K m A δ tau : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam) (hCap : 0 < capCoefficient k angular m A) :
    boxLowerBound k M angular eta lam alpha beta B K m A δ tau =
      densityConstant k angular eta alpha beta B K m A*lam^2*(M:ℝ)*δ^(k+1)*(δ/tau)^((m-1)/2)/
        (hairbrushLog k (δ/tau))^((5:ℝ)/2) := by
  have hd := density_factor_identity (retention_pos k (angular := angular) heta) hlam hCap
  let R := (concentrationRadius (endsCoefficient k angular B eta) alpha*
    concentrationRadius (broadCoefficient k angular beta K eta) beta)^(k+1)
  have hfactor : boxLowerBound k M angular eta lam alpha beta B K m A δ tau =
      (R*(M:ℝ)*δ^(k+1)*(δ/tau)^((m-1)/2)/
        (allScaleConstant k*(hairbrushLog k (δ/tau))^((5:ℝ)/2)))*
      (retention k angular eta*lam*(retention k angular eta*lam/2)^((3:ℝ)/2)/
        (4*Real.sqrt (capCoefficient k angular m A*(2*lam)))) := by
    unfold boxLowerBound
    dsimp only [R]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hfactor,hd]
  unfold densityConstant
  dsimp only [R]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- The angular gain and physical scale exponent are explicit real powers. -/
theorem physical_angular_power (k : ℕ) {δ tau m : ℝ} (hδ : 0 < δ) (htau : 0 < tau) :
    δ^(k+1)*(δ/tau)^((m-1)/2) = δ^((k:ℝ)+1+(m-1)/2)*tau^(-(m-1)/2) := by
  rw [Real.div_rpow hδ.le htau.le,← Real.rpow_natCast,← mul_div_assoc,← Real.rpow_add hδ]
  rw [show (-(m-1)/2:ℝ) = -((m-1)/2) by ring,Real.rpow_neg htau.le]
  simp only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv]

/-- The constructed one-box theorem in quadratic-density form. The positive
constant contains no lambda, delta, tau or family-size dependence. -/
theorem single_box_quadratic_density {k M : ℕ} (F : TubeFamily (k+2) M)
    (Full Ref : Fin M → Set (Space (k+2))) (u : Space (k+2)) (q : Cell (k+1))
    {δ tau angular eta lam alpha beta B K m A : ℝ}
    (hM : 0 < M) (hu : ‖u‖ = 1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (heta : 0 < eta) (heta1 : eta ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hB : 1 ≤ B) (halpha : 0 < alpha) (hK : 1 ≤ K) (hbeta : 0 < beta)
    (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hFull : ∀ i, MeasurableSet (Full i)) (hRef : ∀ i, MeasurableSet (Ref i))
    (hRefFull : ∀ i, Ref i ⊆ Full i) (hsub : ∀ i, Full i ⊆ (F.tube i).carrier δ)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hupper : ∀ i, (volume : Measure (Space (k+2))).real (Full i) ≤ 2*lam*δ^(k+1))
    (hmass : eta*lam*δ^(k+1)*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+2))).real (Ref i))
    (hbroad : ∀ x, AngularDecomposition.Broad F (Finset.univ.filter (fun i => x ∈ Ref i)) δ beta tau K)
    (hends : ∀ i p r, δ ≤ r → r ≤ 1 → (volume : Measure (Space (k+2))).real (Full i ∩ Metric.closedBall p r) ≤
      B*r^alpha*(volume : Measure (Space (k+2))).real (Full i)) :
    densityConstant k angular eta alpha beta B K m A*lam^2*(M:ℝ)*δ^(k+1)*(δ/tau)^((m-1)/2)/
      (hairbrushLog k (δ/tau))^((5:ℝ)/2) ≤ (volume : Measure (Space (k+2))).real (⋃ i, Ref i) := by
  have h := single_box_hairbrush F Full Ref u q hM hu hδ hδtau htau1 ha heta heta1 hlam hlam1
    hB halpha hK hbeta hm hA hFull hRef hRefFull hsub hlocal hsep hcap hupper hmass hbroad hends
  have hCap : 0 < capCoefficient k angular m A :=
    lt_of_lt_of_le (by norm_num) (capCoefficient_ge_one k ha (by linarith) hA)
  rwa [boxLowerBound_density_identity k M heta hlam hCap] at h

end
end KakeyaFormal.AngularBoxAlgebra

#print axioms KakeyaFormal.AngularBoxAlgebra.boxLowerBound_density_identity
#print axioms KakeyaFormal.AngularBoxAlgebra.single_box_quadratic_density
