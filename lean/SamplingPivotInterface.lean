import SamplingRealization
import OriginalPivotSlabs
import SamplingRowNormalization

/-! The actual sampled outcome supplies the marked pivot's literal geometric
input record. A narrow common-mean density band is used explicitly; there is no
post-sampling tube binning or unproved preservation of angular broadness. -/
namespace KakeyaFormal.SamplingPivotInterface
open Finset KakeyaSamplingApplication SamplingRealization
open scoped BigOperators
noncomputable section
open Classical

def density (cEq lam : ℝ) : ℝ := (2/3:ℝ)*cEq*lam
def markedFraction (R xi : ℝ) : ℝ := xi/(8*R)
def twoEndsFactor (C alpha : ℝ) : ℝ := 2*(4:ℝ)^alpha*C

/-- The safe fixed marked fraction lies below the actual quarter-mass bound. -/
theorem marked_mass {M : ℕ} {δ cEq lam xi R W : ℝ}
    (hδ : 0 < δ) (hc1 : cEq ≤ 1)
    (hlam : 0 < lam) (hxi : 0 < xi) (hR : 1 ≤ R)
    (hW : (1/R)*(xi*lam*(M:ℝ)/δ) ≤ W) :
    markedFraction R xi*density cEq lam*(M:ℝ)/δ ≤ W/4 := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hmass0 : 0 ≤ xi*lam*(M:ℝ)/δ := by positivity
  have hcsmall : cEq/12 ≤ (1:ℝ)/4 := by linarith
  have hcoef := mul_le_mul_of_nonneg_right hcsmall
    (show 0 ≤ (1/R)*(xi*lam*(M:ℝ)/δ) by positivity)
  have hid : markedFraction R xi*density cEq lam*(M:ℝ)/δ =
      (cEq/12)*((1/R)*(xi*lam*(M:ℝ)/δ)) := by
    unfold markedFraction density
    ring
  rw [hid]
  exact hcoef.trans (by linarith)

/-- The same original tube family, the same finite support and the same coupled
outcome instantiate every geometric hypothesis of the marked pivot. The only
extra density information is the sharper band proved by narrow concentration. -/
theorem construct {n M J : ℕ} (F : TubeFamily n M)
    (Y : Fin M → Set (Space n)) (E : Finset (Cell n))
    {δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ b qLog cEq R C xi₀ xLog : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ δ₀) (hA : 1 ≤ A)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (hc : 0 < cEq) (hc1 : cEq ≤ 1) (hR : 1 ≤ R) (hC : 1 ≤ C)
    (hM : 0 < M) (hB : 1 ≤ B) (ha : 0 ≤ alpha)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hBbudget : B ≤ B₀*(Real.log (2/δ))^b)
    (hthetaBudget : theta⁻¹ ≤ K₀*(Real.log (2/δ))^qLog)
    (hxiBudget : xi₀*(Real.log (2/δ))^(-xLog) ≤ xi)
    (hbottom : Localization.radius J 0 ≤ 2*δ)
    (hY : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ))
    (hsep : F.Separated δ) (hbounded : F.Bounded baseRadius) (hcap : F.CapBound δ m A)
    (p q : Fin M → ↥E → ℝ) (hp : ∀ i c, 0 ≤ p i c)
    (hpweight : ∀ i c, p i c ≤ SamplingSupport.weight (Y i) δ c.val)
    (high : Finset ↥E) (omega : Outcome (Fin M) ↥E)
    (hgood : SampleGood p q high (SamplingBallTests.mask (J:=J) δ)
      (SamplingCapTests.cap F theta)
      (fun i t => C*B*(SamplingBallTests.testRadius t)^alpha*fullMean p i) omega)
    (hband : ∀ i, (2/3:ℝ)*(cEq*lam/δ) ≤ (fullShading omega i).card ∧
      ((fullShading omega i).card:ℝ) ≤ (4/3:ℝ)*(cEq*lam/δ))
    (hmarked : (1/R)*(xi*lam*(M:ℝ)/δ) ≤ ∑ c, markedMean q c) :
    OriginalPivotSlabs.Hypotheses (full F.tube E omega) E (marks E high omega)
      δ₀ δ A (density cEq lam) (markedFraction R xi) (twoEndsFactor C alpha*B) theta
      (width+(n:ℝ)/2) baseRadius m alpha (twoEndsFactor C alpha*B₀) K₀ b qLog ∧
      density cEq lam ≤ 1 ∧ markedFraction R xi ≤ 1 ∧
      (xi₀/(8*R))*(Real.log (2/δ))^(-xLog) ≤ markedFraction R xi := by
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hfactor1 : 1 ≤ twoEndsFactor C alpha := by
    have hpow := Real.one_le_rpow (show (1:ℝ) ≤ 4 by norm_num) ha
    unfold twoEndsFactor
    nlinarith
  have hfactor : 0 < twoEndsFactor C alpha := zero_lt_one.trans_le hfactor1
  have hcomparable := SamplingRowNormalization.comparable_of_narrow
    (full F.tube E omega) hc hc1 hlam hlam1 (by simpa only [full,unlabel_card] using hband)
  have hfrac : 0 < markedFraction R xi := div_pos hxi (by positivity)
  have hfrac1 : markedFraction R xi ≤ 1 := by
    unfold markedFraction
    apply (div_le_one (by positivity : 0 < 8*R)).mpr
    linarith
  have hsupport := support_and_marks F.tube E high omega
  have hmarkedLower := (marked_mass hδ hc1 hlam hxi hR hmarked).trans hgood.marked_mass
  have hmarkedOriginal : markedFraction R xi*density cEq lam*(M:ℝ)/δ ≤
      ∑ i, ((marks E high omega i).card:ℝ) := by
    simpa only [marks,unlabel_card] using hmarkedLower
  refine ⟨?_,hcomparable.2.1,hfrac1,?_⟩
  · constructor
    · exact hδ
    · exact hδsmall
    · exact hA
    · exact hcomparable.1
    · exact hfrac
    · exact hM
    · nlinarith
    · exact htheta
    · exact htheta1
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hBbudget hfactor.le
    · exact hthetaBudget
    · intro i; exact unlabel_subset E _
    · exact admissible F.tube Y E hδ hY p q hpweight high (SamplingBallTests.mask δ)
        (SamplingCapTests.cap F theta) _ omega hgood
    · exact hsep
    · exact hbounded
    · exact hcap
    · exact hcomparable.2.2
    · exact hsupport.2
    · exact hmarkedOriginal
    · intro z _ v _
      have hh := broadness F E theta p q high (SamplingBallTests.mask δ) _ omega hgood z v
      have hrow : TransverseAngles.incident
          (MarkedSubsetSamples.markedFamily (full F.tube E omega) (marks E high omega)) z =
          univ.filter (fun i => z ∈ marks E high omega i) := rfl
      rw [hrow]
      have hfilter : (univ.filter (fun i => z ∈ marks E high omega i)).filter
          (fun i => projectiveDistance ((full F.tube E omega).tube i).direction v < theta) =
          (univ.filter (fun i => z ∈ marks E high omega i)).filter
            (fun i => projectiveDistance v (F.tube i).direction < theta) := by
        apply filter_congr
        intro i _
        exact (congrArg (fun d => d < theta)
          (ProjectiveGeometry.projective_symm (F.tube i).direction v)).to_iff
      rw [hfilter]
      exact hh
    · exact two_ends F.tube E hδ hbottom hC0.le (zero_le_one.trans hB) ha p q hp high
        (SamplingCapTests.cap F theta) omega hgood
  · have hh := div_le_div_of_nonneg_right hxiBudget (by positivity : 0 ≤ 8*R)
    simpa only [markedFraction,mul_div_right_comm] using hh

end
end KakeyaFormal.SamplingPivotInterface
