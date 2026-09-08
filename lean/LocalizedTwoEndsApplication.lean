import LocalizedGroupedNormalization
import TwoEndsGlobalizationAlgebra

/-! Apply a concrete uniform two-ends estimate to every actual spatial group.
All groups, shared origins, legal densities, cap thinning and population/union
summations are constructed internally. The conclusion is the localized
old-cell estimate used in Proposition 8.1. -/
namespace KakeyaFormal.LocalizedTwoEndsApplication
open Finset LocalizedCellPartition LocalizedGroupedNormalization
open LocalizedSeedNormalization LocalizedDirectionThinning
noncomputable section
open Classical

/-- Exact arbitrary real-density scaling, with one original inverse cap loss. -/
theorem scale_identity {c C K T A s δ rho m x p M : ℝ}
    (hδ : 0 < δ) (hrho : 0 < rho) (hs : 0 < s) (hK : 0 < K) :
    c*C⁻¹*(s/(K*rho))^p*((M*rho^m)/(T*A))*(δ/(K*rho))^x =
      (c*C⁻¹/(T*K^(p+x)))*A⁻¹*δ^x*s^p*rho^(m-p-x)*M := by
  have hKpow : K^(p+x) = K^p*K^x := Real.rpow_add hK _ _
  have hrhopow : rho^m = rho^p*rho^x*rho^(m-p-x) := by
    rw [← Real.rpow_add hrho,← Real.rpow_add hrho]
    congr 1
    ring
  rw [Real.div_rpow hs.le (mul_pos hK hrho).le,
    Real.div_rpow hδ.le (mul_pos hK hrho).le,
    Real.mul_rpow hK.le hrho.le,Real.mul_rpow hK.le hrho.le,hKpow,hrhopow]
  have hKp := (Real.rpow_pos_of_pos hK p).ne'
  have hKx := (Real.rpow_pos_of_pos hK x).ne'
  have hrp := (Real.rpow_pos_of_pos hrho p).ne'
  have hrx := (Real.rpow_pos_of_pos hrho x).ne'
  field_simp

/-- Uniform original localized estimate. The estimate constant and its fixed
normalized geometry/two-ends data precede every actual family and scale. -/
theorem localized_bound (k : ℕ) {width alpha B m D C eta : ℝ}
    (hestimate : TwoEndsDiscreteEstimate (k+1) m D C)
    (halpha : 0 < alpha) (hB : 1 ≤ B) (hm : 0 ≤ m) (hC : 0 ≤ C)
    (heta : 0 < eta) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∀ F : TubeFamily (k+1) M, ∀ δ rho s A : ℝ,
      0 < M → 0 < δ → δ ≤ rho → rho ≤ 1 → 0 < s → 1 ≤ A →
      F.Admissible width δ → F.Comparable δ s → F.CapBound δ m A →
      ∀ centers : Fin M → Space (k+1),
      (∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho) →
      (∀ i x r, δ ≤ r → r ≤ rho →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          B*(r/rho)^alpha*((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^(m-D+eta)*s^C*rho^(D-C)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let K := dilationConstant (k+1) width
  let T := retentionConstant k m
  let Q := capConstant k m
  let J : ℝ := binCount (k+1)
  let x := m-D+eta
  have hK : 0 < K := dilationConstant_pos _ _
  have hT : 0 < T := retentionConstant_pos _ _
  have hQ : 0 < Q := zero_lt_one.trans_le (capConstant_ge_one _ _)
  have hJ : 0 < J := Nat.cast_pos.mpr (binCount_pos _)
  obtain ⟨c,hc,hbound⟩ := hestimate (geometry (k+1) width)
    ((2*J*B)*K^alpha) alpha eta (normalized_ends_ge_one hB halpha.le) halpha heta
  let a := c*Q⁻¹/(T*K^(C+x))
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨a/J^C,by positivity,?_⟩
  intro M F δ rho s A hM hδ hδrho hrho1 hs hA hadm hcomp hcap centers hball hends
  have hrho := hδ.trans_le hδrho
  have hAp : 0 < A := zero_lt_one.trans_le hA
  obtain ⟨P⟩ := LocalizedCellPartition.construct F hM hδ hrho hs hcomp centers hball
  obtain ⟨O,hpop,hunion⟩ := construct_partition P hδ hδrho hrho1 hB halpha.le hm hA
    centers hadm hcap hball hends
  have hsP : 0 < P.density := mul_pos hδ (Nat.cast_pos.mpr P.commonCard_pos)
  have hlocal (q : ↥P.bins) :
      c*Q⁻¹*(δ/(K*rho))^x*(P.density/(K*rho))^C*((O q).configuration.M:ℝ) ≤
        ((O q).configuration.family.unionCells.card:ℝ) := by
    have hh := hbound (O q).configuration (O q).full_two_ends
    simpa only [(O q).scale_eq,(O q).density_eq,(O q).cap_eq] using hh
  have hsum : c*Q⁻¹*(δ/(K*rho))^x*(P.density/(K*rho))^C*
      (∑ q : ↥P.bins, ((O q).configuration.M:ℝ)) ≤ (F.unionCells.card:ℝ) := by
    calc
      _ = ∑ q : ↥P.bins, c*Q⁻¹*(δ/(K*rho))^x*(P.density/(K*rho))^C*
          ((O q).configuration.M:ℝ) := mul_sum _ _ _
      _ ≤ ∑ q : ↥P.bins, ((O q).configuration.family.unionCells.card:ℝ) :=
        sum_le_sum (fun q _ => hlocal q)
      _ ≤ _ := by exact_mod_cast hunion
  have hfactor : 0 ≤ c*Q⁻¹*(δ/(K*rho))^x*(P.density/(K*rho))^C := by positivity
  have hmain : a*A⁻¹*δ^x*P.density^C*rho^(m-C-x)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
    calc
      _ = c*Q⁻¹*(P.density/(K*rho))^C*(((M:ℝ)*rho^m)/(T*A))*(δ/(K*rho))^x :=
        (scale_identity hδ hrho hsP hK).symm
      _ = (c*Q⁻¹*(δ/(K*rho))^x*(P.density/(K*rho))^C)*
          (((M:ℝ)*rho^m)/(T*A)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpop hfactor
      _ ≤ _ := hsum
  have hdensity : s^C/J^C ≤ P.density^C := by
    rw [← Real.div_rpow hs.le hJ.le]
    exact Real.rpow_le_rpow (div_pos hs hJ).le P.density_lower hC
  have hscale : rho^(D-C) ≤ rho^(m-C-x) := by
    apply Real.rpow_le_rpow_of_exponent_ge hrho hrho1
    dsimp [x]
    linarith
  calc
    _ = (a*A⁻¹*δ^x)*(s^C/J^C)*rho^(D-C)*(M:ℝ) := by ring
    _ ≤ (a*A⁻¹*δ^x)*P.density^C*rho^(m-C-x)*(M:ℝ) := by
      gcongr
    _ ≤ _ := hmain

end
end KakeyaFormal.LocalizedTwoEndsApplication
