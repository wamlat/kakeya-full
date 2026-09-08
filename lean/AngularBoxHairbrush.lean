import AngularBoxRecovery

/-! A direct actual-union hairbrush bound for one angular box, including
the anisotropic tau gain. Every intermediate family and mark is constructed. -/
namespace KakeyaFormal.AngularBoxHairbrush
open MeasureTheory AngularBoxRecovery HairbrushKernel HairbrushSelection
open HairbrushScales HairbrushAllScales ProjectiveGeometry
open scoped ENNReal BigOperators
noncomputable section
open Classical

theorem angularLoss_ge_one {angular : ℝ} (ha : 0 ≤ angular) : 1 ≤ angularLoss angular := by
  unfold angularLoss
  nlinarith [sq_nonneg angular]

theorem capCoefficient_ge_one (k : ℕ) {angular m A : ℝ} (ha : 0 ≤ angular)
    (hm : 0 ≤ m) (hA : 1 ≤ A) : 1 ≤ capCoefficient k angular m A := by
  have hp := packingConstant_ge_one (k+1)
  have ha' := Real.one_le_rpow (angularLoss_ge_one ha) hm
  have hpA : 1 ≤ packingConstant (k+1)*A := by nlinarith
  unfold capCoefficient
  nlinarith

theorem endsCoefficient_ge_one (k : ℕ) {angular B eta : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hB : 1 ≤ B) :
    1 ≤ endsCoefficient k angular B eta := by
  have he := retention_pos k (angular := angular) heta
  have he1 := (retention_le k (angular := angular) heta.le).trans heta1
  have hd : 1 ≤ 4/retention k angular eta := (le_div_iff₀ he).mpr (by linarith)
  unfold endsCoefficient
  nlinarith

theorem broadCoefficient_ge_one (k : ℕ) {angular beta K eta : ℝ}
    (ha : 0 ≤ angular) (hb : 0 ≤ beta) (heta : 0 < eta) (heta1 : eta ≤ 1) (hK : 1 ≤ K) :
    1 ≤ broadCoefficient k angular beta K eta := by
  have he := retention_pos k (angular := angular) heta
  have he1 := (retention_le k (angular := angular) heta.le).trans heta1
  have hd : 1 ≤ 8/retention k angular eta := (le_div_iff₀ he).mpr (by linarith)
  have hp := Real.one_le_rpow (angularLoss_ge_one ha) hb
  have hkp : 1 ≤ K*(angularLoss angular)^beta := by nlinarith
  unfold broadCoefficient
  nlinarith

/-- Explicit one-box expression. All losses except the displayed scale and
logarithm are fixed by dimension and the original quantitative hypotheses. -/
def boxLowerBound (k M : ℕ) (angular eta lam alpha beta B K m A δ tau : ℝ) : ℝ :=
  (concentrationRadius (endsCoefficient k angular B eta) alpha*
    concentrationRadius (broadCoefficient k angular beta K eta) beta)^(k+1)*
    (retention k angular eta*lam*(M:ℝ)/4)*δ^(k+1)*
    (retention k angular eta*lam/2)^((3:ℝ)/2)*(δ/tau)^((m-1)/2)/
    (allScaleConstant k*Real.sqrt (capCoefficient k angular m A*(2*lam))*
      (hairbrushLog k (δ/tau))^((5:ℝ)/2))

/-- The usual physical-ball tests up to radius one imply every larger-radius
test by finite measure monotonicity and the nonnegative exponent. -/
theorem two_ends_all_radii {k : ℕ} (Full : Set (Space k)) {δ B alpha : ℝ}
    (hfin : volume Full ≠ ∞) (hB : 1 ≤ B) (ha : 0 ≤ alpha)
    (hends : ∀ p r, δ ≤ r → r ≤ 1 → (volume : Measure (Space k)).real (Full ∩ Metric.closedBall p r) ≤
      B*r^alpha*(volume : Measure (Space k)).real Full) :
    ∀ p r, δ ≤ r → (volume : Measure (Space k)).real (Full ∩ Metric.closedBall p r) ≤
      B*r^alpha*(volume : Measure (Space k)).real Full := by
  intro p r hr
  by_cases hr1 : r ≤ 1
  · exact hends p r hr hr1
  · have hp := Real.one_le_rpow (le_of_lt (lt_of_not_ge hr1)) ha
    have hcoef : 1 ≤ B*r^alpha := by nlinarith
    exact (measureReal_mono Set.inter_subset_left hfin).trans
      (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hcoef
        (show 0 ≤ (volume : Measure (Space k)).real Full from measureReal_nonneg)))

/-- The stronger fractional hairbrush estimate for one actual angular box.
The target is the original reference union, with the explicit angular gain
`(delta/tau)^((m-1)/2)`. No segment choice, color, marked mass or hairbrush
energy bound occurs among the inputs. -/
theorem single_box_hairbrush {k M : ℕ} (F : TubeFamily (k+2) M)
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
    boxLowerBound k M angular eta lam alpha beta B K m A δ tau ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Ref i) := by
  have htau : 0 < tau := hδ.trans_le hδtau
  let d := δ/tau
  have hd : 0 < d := div_pos hδ htau
  have hd1 : d ≤ 1 := (div_le_one htau).mpr hδtau
  let e := retention k angular eta
  have he : 0 < e := retention_pos k heta
  have he1 : e ≤ 1 := (retention_le k heta.le).trans heta1
  have helam : e*lam ≤ 1 := (mul_le_mul he1 hlam1 hlam.le (by norm_num)).trans_eq (by ring)
  have hBl := endsCoefficient_ge_one k (angular := angular) heta heta1 hB
  have hKl := broadCoefficient_ge_one k ha hbeta.le heta heta1 hK
  have hAl := capCoefficient_ge_one k ha (by linarith : 0 ≤ m) hA
  have hendsAll (i) := two_ends_all_radii (Full i)
    (measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite _ _)) hB halpha.le (hends i)
  obtain ⟨N,H,Y,G,hN,hHsep,hHcap,hYi,hG,hgood,hYbroad,hYends,hGmass,hUnion⟩ :=
    single_box_recovery F Full Ref u q hM hu hδ hδtau htau1 ha heta hlam
      (by linarith : 0 ≤ B) (by linarith : 0 ≤ K) (by linarith : 0 ≤ m) (by linarith : 0 ≤ A)
      hFull hRef hRefFull hsub hlocal hsep hcap hupper hmass hbroad hendsAll
  have hk := chosen_radius_hairbrush H Y G hN hd hd1 hBl halpha hKl hbeta
    (by positivity : 0 ≤ e*lam/2) (by linarith : e*lam/2 ≤ 1)
    (by nlinarith : e*lam/2 ≤ 2*lam) hm hAl (by positivity : 0 < 2*lam) hHsep
    (fun i => (hYi i).1) (fun i => (hYi i).2.1) hG hgood hYbroad
    (fun i => (hYi i).2.2.1) hYends hHcap (fun i => (hYi i).2.2.2)
  let R := (concentrationRadius (endsCoefficient k angular B eta) alpha*
    concentrationRadius (broadCoefficient k angular beta K eta) beta)^(k+1)
  let D := allScaleConstant k*Real.sqrt (capCoefficient k angular m A*(2*lam))*
    (hairbrushLog k d)^((5:ℝ)/2)
  have hR : 0 ≤ R := by
    have hbpos : 0 < endsCoefficient k angular B eta := by linarith
    have hkpos : 0 < broadCoefficient k angular beta K eta := by linarith
    have hr₁ := concentrationRadius_pos (alpha := alpha) hbpos
    have hr₂ := concentrationRadius_pos (alpha := beta) hkpos
    dsimp [R]
    positivity
  have hD : 0 < D := by
    have hC := allScaleConstant_pos k
    have hL := hairbrushLog_pos (k := k) hd hd1
    have hApos : 0 < capCoefficient k angular m A := by linarith
    dsimp [D]
    positivity
  have hnum := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGmass hR)
      (Real.rpow_nonneg (by positivity : 0 ≤ e*lam/2) ((3:ℝ)/2)))
    (Real.rpow_nonneg hd.le ((m-1)/2))
  have hsmall : R*(e*lam*d^(k+1)*(M:ℝ)/4)*(e*lam/2)^((3:ℝ)/2)*d^((m-1)/2)/D ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Ref i)/tau^(k+1) :=
    ((div_le_div_of_nonneg_right hnum hD.le).trans hk).trans hUnion
  have hmul := (le_div_iff₀ (pow_pos htau (k+1))).mp hsmall
  have hid : (R*(e*lam*d^(k+1)*(M:ℝ)/4)*(e*lam/2)^((3:ℝ)/2)*d^((m-1)/2)/D)*tau^(k+1) =
      boxLowerBound k M angular eta lam alpha beta B K m A δ tau := by
    dsimp only [boxLowerBound,R,D,e,d]
    rw [div_pow]
    field_simp
  rwa [hid] at hmul

end
end KakeyaFormal.AngularBoxHairbrush

#print axioms KakeyaFormal.AngularBoxHairbrush.single_box_hairbrush
