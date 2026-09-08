import LocalizedSeedNormalization
import AngularSeedEstimate

/-! Direct application of the proved uniform two-ends seed to the actual
coarse-thinned common dilation, with exact radius/density arithmetic. -/
namespace KakeyaFormal.LocalizedSeedApplication
open LocalizedSeedNormalization LocalizedDirectionThinning LocalizedGridTubes AngularSeedEstimate
noncomputable section
open Classical

/-- Exact scale accounting, including the one original inverse cap loss. -/
theorem scale_identity {c C K T A s δ rho m x M : ℝ}
    (hδ : 0 < δ) (hrho : 0 < rho) (hK : 0 < K) :
    c*C⁻¹*(s/(K*rho))^2*((M*rho^m)/(T*A))*(δ/(K*rho))^x =
      (c*C⁻¹/(T*K^(2+x)))*A⁻¹*δ^x*s^2*rho^(m-2-x)*M := by
  have hKpow : K^(2+x) = K^2*K^x := by rw [Real.rpow_add hK,Real.rpow_two]
  have hrhopow : rho^m = rho^2*rho^x*rho^(m-2-x) := by
    rw [← Real.rpow_two,← Real.rpow_add hrho,← Real.rpow_add hrho]
    congr 1
    ring
  rw [Real.div_rpow hδ.le (mul_pos hK hrho).le,Real.mul_rpow hK.le hrho.le,div_pow,mul_pow,hKpow,hrhopow]
  have hKx : K^x ≠ 0 := (Real.rpow_pos_of_pos hK x).ne'
  have hrx : rho^x ≠ 0 := (Real.rpow_pos_of_pos hrho x).ne'
  field_simp

/-- The normalized two-ends coefficient is a fixed number independent of the
original radius, density, scale and cap constant. -/
def endsConstant (k : ℕ) (width alpha : ℝ) : ℝ :=
  (4:ℝ)^alpha*(dilationConstant (k+2) width)^alpha

theorem endsConstant_ge_one (k : ℕ) (width : ℝ) {alpha : ℝ} (ha : 0 ≤ alpha) :
    1 ≤ endsConstant k width alpha :=
  one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by norm_num) ha)
    (Real.one_le_rpow (dilationConstant_ge_one _ _) ha)

/-- Uniform local seed on every actual finite localized family. No analytic
input is supplied: direction selection and unit normalization are constructed,
and the previously proved two-ends seed is applied to them. -/
theorem localized_seed (k : ℕ) {width alpha beta m eps : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hbetaS : beta ≤ (m-1)/2)
    (hm : 1 ≤ m) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ δ rho s A : ℝ,
      0 < M → 0 < δ → δ ≤ rho → rho ≤ 1 → 0 < s → 1 ≤ A →
      F.Admissible width δ → F.Comparable δ s → F.CapBound δ m A →
      ∀ centers : Fin M → Space (k+2),
      (∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho) →
      (∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ rho →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          (4:ℝ)^alpha*(r/rho)^alpha*((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^((m-3)/2+eps)*s^2*rho^((m-1)/2)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hseed⟩ := two_ends_seed k (width := localWidth width) (b := 0)
    halpha hbeta hbetaS (endsConstant_ge_one k width halpha.le) (by norm_num) hm heps
  let K := dilationConstant (k+2) width
  let T := retentionConstant (k+1) m
  let C := capConstant (k+1) m
  let x := (m-3)/2+eps
  have hK : 0 < K := dilationConstant_pos _ _
  have hT : 0 < T := retentionConstant_pos _ _
  have hC : 0 < C := zero_lt_one.trans_le (capConstant_ge_one _ _)
  refine ⟨c*C⁻¹/(T*K^(2+x)),by positivity,?_⟩
  intro M F δ rho s A hM hδ hδrho hrho1 hs hA hadm hcomp hcap centers hball hends
  have hrho := hδ.trans_le hδrho
  have hL : 0 < K*rho := mul_pos hK hrho
  obtain ⟨hscale,hscale1,hdensity,hdensity1,N,hN,e,he,G,hcount,hGadm,hGcomp,hGsep,hGcap,hcards,hU,hGends⟩ :=
    normalize_localized_family F hM hδ hδrho hrho1 hs halpha.le
      (Real.one_le_rpow (by norm_num) halpha.le) (by linarith : 0 ≤ m) hA centers hadm hcomp hcap hball hends
  have hGbound := hseed N G (δ/(K*rho)) (s/(K*rho)) (endsConstant k width alpha) C
    hscale hscale1 hdensity hdensity1 (endsConstant_ge_one k width halpha.le) (capConstant_ge_one _ _)
    (by simp) hGadm hGcomp hGsep hGcap (fun i y r hr _ => hGends i y r hr)
  have hfac : 0 ≤ c*C⁻¹*(s/(K*rho))^2*(δ/(K*rho))^x := by positivity
  have hpop := mul_le_mul_of_nonneg_left hcount hfac
  have hmain : (c*C⁻¹/(T*K^(2+x)))*A⁻¹*δ^x*s^2*rho^(m-2-x)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
    calc
      _ = c*C⁻¹*(s/(K*rho))^2*(((M:ℝ)*rho^m)/(T*A))*(δ/(K*rho))^x :=
        (scale_identity hδ hrho hK).symm
      _ ≤ c*C⁻¹*(s/(K*rho))^2*(N:ℝ)*(δ/(K*rho))^x := by nlinarith [hpop]
      _ ≤ (G.unionCells.card:ℝ) := hGbound
      _ ≤ _ := Nat.cast_le.mpr hU
  have hpow : rho^((m-1)/2) ≤ rho^(m-2-x) := by
    apply Real.rpow_le_rpow_of_exponent_ge hrho hrho1
    dsimp [x]
    linarith
  have hcoef : 0 ≤ (c*C⁻¹/(T*K^(2+x)))*A⁻¹*δ^x*s^2*(M:ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left hpow hcoef
  calc
    _ = ((c*C⁻¹/(T*K^(2+x)))*A⁻¹*δ^x*s^2*(M:ℝ))*rho^((m-1)/2) := by ring
    _ ≤ _ := hh
    _ = (c*C⁻¹/(T*K^(2+x)))*A⁻¹*δ^x*s^2*rho^(m-2-x)*(M:ℝ) := by ring
    _ ≤ _ := hmain

end
end KakeyaFormal.LocalizedSeedApplication
