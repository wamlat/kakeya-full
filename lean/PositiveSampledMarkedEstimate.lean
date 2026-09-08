import SamplingPivotInterface
import PositiveMarkedPivotEstimate

/-! Positive-base-density extension (p>0), reusing the constructed geometry.
 The original marked pivot estimate applied to the actual compatible sampled
family. The estimate constant precedes all families, probability arrays and
outcomes; original scale and density parameters are retained in the conclusion. -/
namespace KakeyaFormal.PositiveSampledMarkedEstimate
open Finset KakeyaSamplingApplication SamplingRealization SamplingPivotInterface
open scoped BigOperators
noncomputable section
open Classical

theorem construct {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 0 ≤ m) (hpExp : 0 < pExp) (hd : 0 ≤ d) (hqExp : 2 ≤ qExp)
    (width baseRadius eps : ℝ) (hw : 0 ≤ width) (heps : 0 < eps)
    (cEq R C B₀ K₀ xi₀ alpha bLog qLog xLog : ℝ)
    (hcEq : 0 < cEq) (hcEq1 : cEq ≤ 1) (hR : 1 ≤ R) (hC : 1 ≤ C)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hxi₀ : 0 < xi₀)
    (ha : 0 < alpha) (hbLog : 0 ≤ bLog) (hqLog : 0 ≤ qLog) (hxLog : 0 ≤ xLog) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M J : ℕ} (F : TubeFamily (k+2) M)
      (Y : Fin M → Set (Space (k+2))) (E : Finset (Cell (k+2)))
      {δ A lam xi B theta : ℝ},
      0 < δ → δ ≤ 1 → 1 ≤ A → 0 < lam → lam ≤ 1 → 0 < xi → xi ≤ 1 →
      0 < M → 1 ≤ B → 0 < theta → theta ≤ 1 →
      B ≤ B₀*(Real.log (2/δ))^bLog → theta⁻¹ ≤ K₀*(Real.log (2/δ))^qLog →
      xi₀*(Real.log (2/δ))^(-xLog) ≤ xi →
      Localization.radius J 0 ≤ 2*δ →
      (∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) →
      F.Separated δ → F.Bounded baseRadius → F.CapBound δ m A →
      ∀ (p q : Fin M → ↥E → ℝ), (∀ i z, 0 ≤ p i z) →
      (∀ i z, p i z ≤ SamplingSupport.weight (Y i) δ z.val) →
      ∀ (high : Finset ↥E) (omega : Outcome (Fin M) ↥E),
      SampleGood p q high (SamplingBallTests.mask (J:=J) δ) (SamplingCapTests.cap F theta)
        (fun i t => C*B*(SamplingBallTests.testRadius t)^alpha*fullMean p i) omega →
      (∀ i, (2/3:ℝ)*(cEq*lam/δ) ≤ (fullShading omega i).card ∧
        ((fullShading omega i).card:ℝ) ≤ (4/3:ℝ)*(cEq*lam/δ)) →
      (1/R)*(xi*lam*(M:ℝ)/δ) ≤ ∑ z, markedMean q z →
      c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤ (E.card:ℝ) := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hf : 0 < twoEndsFactor C alpha := by unfold twoEndsFactor; positivity
  have hwidth : (1:ℝ)/12 ≤ width+((k+2:ℕ):ℝ)/2 := by
    have hk := Nat.cast_nonneg (α:=ℝ) k
    push_cast
    linarith
  obtain ⟨cCore,hcCore,hcore⟩ := PositiveMarkedPivotEstimate.all_scales hbase hlift hm hpExp hd hqExp
    (width+((k+2:ℕ):ℝ)/2) baseRadius hwidth eps heps
    (twoEndsFactor C alpha*B₀) K₀ (xi₀/(8*R)) alpha bLog qLog xLog
    (mul_pos hf hB₀) hK₀ (div_pos hxi₀ (by positivity)) ha hbLog hqLog hxLog
  let gamma : ℝ := (2/3:ℝ)*cEq
  have hgamma : 0 < gamma := by dsimp [gamma]; positivity
  refine ⟨cCore*gamma^(KakeyaScalar.pivotDensity pExp qExp),by positivity,?_⟩
  intro M J F Y E δ A lam xi B theta hδ hδ1 hA hlam hlam1 hxi hxi1 hM hB
    htheta htheta1 hBbudget hthetaBudget hxiBudget hbottom hY hsep hbounded hcap
    p q hp hpweight high omega hgood hband hmarked
  obtain ⟨H,hlamNew,hxiNew,hxiNewBudget⟩ := SamplingPivotInterface.construct F Y E
    hδ hδ1 hA hlam hlam1 hxi hxi1 hcEq hcEq1 hR hC hM hB ha.le htheta htheta1
    hBbudget hthetaBudget hxiBudget hbottom hY hsep hbounded hcap
    p q hp hpweight high omega hgood hband hmarked
  have hh := hcore (full F.tube E omega) E (marks E high omega) H hlamNew hxiNew hxiNewBudget
  change cCore*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
    (gamma*lam)^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤ (E.card:ℝ) at hh
  rw [Real.mul_rpow hgamma.le hlam.le] at hh
  convert hh using 1
  ring

end
end KakeyaFormal.PositiveSampledMarkedEstimate
