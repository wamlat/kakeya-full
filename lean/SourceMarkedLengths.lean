import MarkedLengthInput
import MarkedLengthAlgebra
import SourceMarkedNormalization

/-! Source marked pivot with arbitrary fixed bounded original axis lengths,
fixed row-density multiples and fixed separation. The actual common dilation
and common grid refinement preserve every original marked incidence. -/
namespace KakeyaFormal.SourceMarkedLengths
open Finset MarkedLengthNormalization MarkedNormalizationAlgebra
noncomputable section
open Classical

/-- The geometric factor for both normalization steps is kept inside the
source minimum's concentration power as well as in its outside factor. -/
def kappa (n : ℕ) (lengthUpper a b sep width B alpha theta : ℝ) : ℝ :=
  MarkedNormalizationKappa.choice
    (MarkedGridNormalization.newWidth n (MarkedGridNormalization.depth a b sep) width)
    (MarkedGridPadding.endsFactor n (MarkedGridNormalization.depth a b sep)*dilation lengthUpper)
    B alpha theta

theorem source_fourth {k : ℕ} {m d d' p q : ℝ}
    (hbase : SourceAnalyticInputs.Base (k+2) m d p)
    (hlift : SourceAnalyticInputs.Lifted (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (lengthUpper width R a b sep : ℝ) (hw : 0 ≤ width)
    (ha : 0 < a) (hb : 0 < b) (hsep : 0 < sep)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) (lengths : Fin M → ℝ)
      {δ A lam xi B theta alpha : ℝ},
      (∀ i, lengths i ≤ lengthUpper) →
      MarkedLengthInput.Input F E marks lengths δ A lam xi B theta width R m alpha a b sep →
      0 < alpha → alpha ≤ 1 →
      T ≤ (1/δ)*(kappa (k+2) lengthUpper a b sep width B alpha theta)^20 →
      c*A⁻¹*(kappa (k+2) lengthUpper a b sep width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
        xi^(p+3)*(Real.log (2/δ))^(-(p+4))*δ^(-2*m-3-d'+3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)*δ^m)^3 ≤ (E.card:ℝ)^4 := by
  let W := dilation lengthUpper
  have hW : 1 ≤ W := dilation_ge_one _
  have hW0 : 0 < W := dilation_pos _
  obtain ⟨T,c,hT,hc,hbound⟩ := SourceMarkedNormalization.source_fourth
    hbase hlift hm hp hd hq width (R/W) a b sep hw ha hb hsep eps heps heps1
  let cfactor := transportFactor 0 W 1 1 (p+3) (p+4)
    (-2*m-3-d'+3*eps) (p+2*q+4+2*eps) m
  have hf : 0 < cfactor := transportFactor_pos 0 hW (by norm_num) (by norm_num)
  refine ⟨T,c*cfactor,hT,mul_pos hc hf,?_⟩
  intro M F E marks lengths δ A lam xi B theta alpha hL h halpha halpha1 hcut
  let kap := kappa (k+2) lengthUpper a b sep width B alpha theta
  let kapNew := SourceMarkedNormalization.kappa (k+2) a b sep width (B*W) alpha theta
  let C := MarkedGridPadding.endsFactor (k+2) (MarkedGridNormalization.depth a b sep)
  let widthNew := MarkedGridNormalization.newWidth (k+2) (MarkedGridNormalization.depth a b sep) width
  have hC : 1 ≤ C := MarkedGridPadding.endsFactor_ge_one _ _
  have hCW : 1 ≤ C*W := by nlinarith
  have hwn : 0 ≤ widthNew := (by norm_num : (0:ℝ)≤1/12).trans
    (SourceMarkedNormalization.newWidth_lower (by omega) _ hw)
  have hB0 : 0 < B := zero_lt_one.trans_le h.ends_ge_one
  have hkap : 0 < kap := MarkedNormalizationKappa.choice_pos (alpha:=alpha) hwn hCW hB0 h.theta_pos
  have hle : kap ≤ kapNew :=
    MarkedLengthAlgebra.choice_le_rescaled hwn hC hW hB0 h.theta_pos
  have hcutNew : T ≤ (1/(δ/W))*kapNew^20 :=
    MarkedLengthAlgebra.rescaled_cutoff h.scale_pos hW hkap.le hle hcut
  have hi := MarkedLengthInput.bounded_lengths hL hm hsep.le halpha.le halpha1 h
  have hh := hbound (normalizedFamily F W) E marks hi halpha halpha1 hcutNew
  change c*A⁻¹*kapNew^(5*((k+1:ℕ):ℝ)+6*q+12)*xi^(p+3)*
    (Real.log (2/(δ/W)))^(-(p+4))*(δ/W)^(-2*m-3-d'+3*eps)*
    (lam/W)^(p+2*q+4+2*eps)*((M:ℝ)*(δ/W)^m)^3 ≤ (E.card:ℝ)^4 at hh
  have hH : 0 ≤ 5*((k+1:ℕ):ℝ)+6*q+12 := by positivity
  have hA0 : 0 < A := zero_lt_one.trans_le h.cap_ge_one
  have hδp := h.scale_pos
  have hlamp := h.density_pos
  have hxip := h.fraction_pos
  have hδn : 0 < δ/W := div_pos hδp hW0
  have hlog : 0 ≤ Real.log (2/(δ/W)) := by
    apply Real.log_nonneg
    apply (one_le_div hδn).mpr
    linarith [hi.scale_le_one]
  have hnorm : c*A⁻¹*kap^(5*((k+1:ℕ):ℝ)+6*q+12)*(xi/1)^(p+3)*
      (Real.log (2/(δ/W)))^(-(p+4))*(δ/W)^(-2*m-3-d'+3*eps)*
      (lam/W)^(p+2*q+4+2*eps)*((M:ℝ)*(δ/W)^m)^3 ≤
      (W^0*(E.card:ℝ))^4 := by
    simp only [div_one,pow_zero,one_mul]
    apply le_trans ?_ hh
    gcongr
  have hnu : (1/W)*lam ≤ lam/W := le_of_eq (by ring)
  exact transport_fourth 0 hc.le hA0 hkap h.fraction_pos h.scale_pos h.scale_le_one
    h.density_pos (Nat.cast_nonneg M) hW (by norm_num) (by norm_num)
    (by linarith : 0 ≤ p+4) (by linarith : 0 ≤ p+2*q+4+2*eps) hnu hnorm

/-- Literal N,S notation for all fixed original length/width/separation/row
normalizations. The constant remains uniform in B,theta,alpha and all data. -/
theorem source_notation {k : ℕ} {m d d' p q : ℝ}
    (hbase : SourceAnalyticInputs.Base (k+2) m d p)
    (hlift : SourceAnalyticInputs.Lifted (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (lengthUpper width R a b sep A₀ : ℝ) (hw : 0 ≤ width)
    (ha : 0 < a) (hb : 0 < b) (hsep : 0 < sep) (hA₀ : 1 ≤ A₀)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (marks : Fin M → Finset (Cell (k+2)))
      (lengths : Fin M → ℝ) {N lam xi B theta alpha : ℝ},
      2 ≤ N → (∀ i, lengths i ≤ lengthUpper) →
      MarkedLengthInput.Input F F.unionCells marks lengths (1/N) A₀ lam xi B theta width R m alpha a b sep →
      0 < alpha → alpha ≤ 1 →
      T ≤ N*(kappa (k+2) lengthUpper a b sep width B alpha theta)^20 →
      c*(kappa (k+2) lengthUpper a b sep width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
        xi^(p+3)*(Real.log (2*N))^(-(p+4))*N^(2*m+3+d'-3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)/N^m)^3 ≤ (F.unionCells.card:ℝ)^4 := by
  obtain ⟨T,c,hT,hc,hbound⟩ := source_fourth hbase hlift hm hp hd hq
    lengthUpper width R a b sep hw ha hb hsep eps heps heps1
  refine ⟨T,c*A₀⁻¹,hT,by positivity,?_⟩
  intro M F marks lengths N lam xi B theta alpha hN hL h halpha halpha1 hcut
  have hN0 : 0 < N := by linarith
  have hcut' : T ≤ (1/(1/N))*(kappa (k+2) lengthUpper a b sep width B alpha theta)^20 := by
    simpa only [one_div,inv_inv] using hcut
  have hh := hbound F F.unionCells marks lengths hL h halpha halpha1 hcut'
  have hlog : 2/(1/N)=2*N := by field_simp
  have hpower : (1/N)^(-2*m-3-d'+3*eps)=N^(2*m+3+d'-3*eps) := by
    rw [one_div,Real.inv_rpow hN0.le,← Real.rpow_neg hN0.le]
    congr 1
    ring
  have hpop : (M:ℝ)*(1/N)^m=(M:ℝ)/N^m := by
    rw [one_div,Real.inv_rpow hN0.le,div_eq_mul_inv]
  rwa [hlog,hpower,hpop] at hh

end
end KakeyaFormal.SourceMarkedLengths
