import MarkedNormalizationAlgebra
import SourceMarkedPivotFullRange
import SourceAnalyticInputs

/-! Literal marked pivot input normalization: arbitrary fixed positive density
multiples and fixed positive direction separation, exact original marked
broadness, source minimum radius, and original occupied-cell conclusion. -/
namespace KakeyaFormal.SourceMarkedNormalization
open Finset MarkedGridRefinement MarkedGridPadding MarkedGridNormalization
open MarkedNormalizationAlgebra
noncomputable section
open Classical

/-- The only adjustment of the source minimum is a fixed geometric constant,
used in BOTH its outside factor and its 1/alpha-power numerator. -/
def kappa (n : ℕ) (a b sep width B alpha theta : ℝ) : ℝ :=
  MarkedNormalizationKappa.choice (newWidth n (depth a b sep) width)
    (endsFactor n (depth a b sep)) B alpha theta

theorem newWidth_lower {n : ℕ} (hn : 1 ≤ n) (j : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    (1:ℝ)/12 ≤ newWidth n j width := by
  have hq : (1:ℝ) ≤ factor j := by exact_mod_cast factor_pos j
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  unfold newWidth
  nlinarith

/-- Original-scale bound from the actual normalized construction. The two
analytic inputs are only the source N>=2 absolute-cap base and paired-error
cumulative lifted estimates. T and c precede B,theta,alpha and all configurations. -/
theorem source_fourth {k : ℕ} {m d d' p q : ℝ}
    (hbase : SourceAnalyticInputs.Base (k+2) m d p)
    (hlift : SourceAnalyticInputs.Lifted (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width R a b sep : ℝ) (hw : 0 ≤ width) (ha : 0 < a) (hb : 0 < b) (hsep : 0 < sep)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta alpha : ℝ},
      Input F E marks δ A lam xi B theta width R m alpha a b sep →
      0 < alpha → alpha ≤ 1 →
      T ≤ (1/δ)*(kappa (k+2) a b sep width B alpha theta)^20 →
      c*A⁻¹*(kappa (k+2) a b sep width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
        xi^(p+3)*(Real.log (2/δ))^(-(p+4))*δ^(-2*m-3-d'+3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)*δ^m)^3 ≤ (E.card:ℝ)^4 := by
  let j := depth a b sep
  let Q : ℝ := factor j
  let W := newWidth (k+2) j width
  let C := endsFactor (k+2) j
  have hQ : 1 ≤ Q := by dsimp [Q]; exact_mod_cast factor_pos j
  have hQ0 : 0 < Q := by linarith
  have hW : (1:ℝ)/12 ≤ W := newWidth_lower (by omega) j hw
  have hW0 : 0 ≤ W := by linarith
  have hC : 1 ≤ C := endsFactor_ge_one (k+2) j
  obtain ⟨craw,hcraw,hraw⟩ := SourceMarkedPivotFullRange.admissible_fourth
    (hbase.to_discrete hm) hlift.to_discrete hm hp hd hq W R hW eps heps heps1
  let cnat := craw*(3/Real.log 2)^(-(p+4))
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hcnat : 0 < cnat := by dsimp [cnat]; positivity
  let cfactor := transportFactor (k+2) Q b (2*max 1 b) (p+3) (p+4)
    (-2*m-3-d'+3*eps) (p+2*q+4+2*eps) m
  have hcfactor : 0 < cfactor := transportFactor_pos (k+2) hQ hb (by positivity)
  let T := PivotGeometryScale.geometryConstant (k+2) W*(1+2*W)^20
  have hT : 0 < T := by
    have hh := zero_lt_one.trans_le (PivotGeometryScale.constant_bounds (k+2) W).1
    dsimp [T]
    positivity
  refine ⟨T,cnat*cfactor,hT,mul_pos hcnat hcfactor,?_⟩
  intro M F E marks δ A lam xi B theta alpha h halpha halpha1 hscale
  obtain ⟨U⟩ := MarkedGridNormalization.construct (by omega) ha hb hsep hm halpha.le halpha1 h
  obtain ⟨hkap,hkap100,hangle,hradius,hlegal⟩ := MarkedNormalizationKappa.admissible
    hW0 hC h.ends_ge_one halpha h.theta_pos
  have hkap1 : kappa (k+2) a b sep width B alpha theta ≤ 1 := hkap100.trans (by norm_num)
  have htests := MarkedNormalizationKappa.refined_tests (k+2) h.scale_pos hQ hW0 hkap hkap1 hscale
  have hfour := hraw U.padding.family (refine j E) (marked j marks) U.normalized
    U.density_le_one U.fraction_le_one hkap hkap1 hangle hradius hlegal htests
  have hnat := PositivePivotAlgebra.natural_log_fourth U.normalized.scale_pos U.normalized.scale_le_one
    hcraw (zero_lt_one.trans_le h.cap_ge_one) hkap U.normalized.marked_fraction_pos hp
    U.normalized.density_pos (by positivity [U.normalized.scale_pos] : 0 ≤ (M:ℝ)*(δ/Q)^m) hfour
  have hnorm : cnat*A⁻¹*(kappa (k+2) a b sep width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
      (xi/(2*max 1 b))^(p+3)*(Real.log (2/(δ/Q)))^(-(p+4))*(δ/Q)^(-2*m-3-d'+3*eps)*
      (newDensity j δ lam b)^(p+2*q+4+2*eps)*((M:ℝ)*(δ/Q)^m)^3 ≤ (Q^(k+2)*(E.card:ℝ))^4 := by
    simpa only [cnat,Q,j,W,C,kappa,newFraction,refine_card,Nat.cast_mul,Nat.cast_pow] using hnat
  exact transport_fourth (k+2) hcnat.le (zero_lt_one.trans_le h.cap_ge_one) hkap h.fraction_pos
    h.scale_pos h.scale_le_one h.density_pos (Nat.cast_nonneg M) hQ hb (by positivity)
    (by linarith : 0 ≤ p+4) (by linarith : 0 ≤ p+2*q+4+2*eps) U.density_lower hnorm

/-- The literal source N,L=log(2N),S=M/N^m notation, at a fixed absolute
original cap coefficient. Full and marked rows have arbitrary fixed positive
density multiples; original c*delta separation is normalized internally. -/
theorem source_notation {k : ℕ} {m d d' p q : ℝ}
    (hbase : SourceAnalyticInputs.Base (k+2) m d p)
    (hlift : SourceAnalyticInputs.Lifted (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width R a b sep A₀ : ℝ) (hw : 0 ≤ width) (ha : 0 < a) (hb : 0 < b)
    (hsep : 0 < sep) (hA₀ : 1 ≤ A₀) (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (marks : Fin M → Finset (Cell (k+2)))
      {N lam xi B theta alpha : ℝ},
      2 ≤ N → Input F F.unionCells marks (1/N) A₀ lam xi B theta width R m alpha a b sep →
      0 < alpha → alpha ≤ 1 →
      T ≤ N*(kappa (k+2) a b sep width B alpha theta)^20 →
      c*(kappa (k+2) a b sep width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
        xi^(p+3)*(Real.log (2*N))^(-(p+4))*N^(2*m+3+d'-3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)/N^m)^3 ≤ (F.unionCells.card:ℝ)^4 := by
  obtain ⟨T,c,hT,hc,hbound⟩ := source_fourth hbase hlift hm hp hd hq width R a b sep hw ha hb hsep eps heps heps1
  refine ⟨T,c*A₀⁻¹,hT,by positivity,?_⟩
  intro M F marks N lam xi B theta alpha hN h halpha halpha1 hscale
  have hN0 : 0 < N := by linarith
  have hscale' : T ≤ (1/(1/N))*(kappa (k+2) a b sep width B alpha theta)^20 := by
    simpa only [one_div,inv_inv] using hscale
  have hh := hbound F F.unionCells marks h halpha halpha1 hscale'
  have hlog : 2/(1/N)=2*N := by field_simp
  have hpower : (1/N)^(-2*m-3-d'+3*eps)=N^(2*m+3+d'-3*eps) := by
    rw [one_div,Real.inv_rpow hN0.le,← Real.rpow_neg hN0.le]
    congr 1
    ring
  have hpop : (M:ℝ)*(1/N)^m=(M:ℝ)/N^m := by
    rw [one_div,Real.inv_rpow hN0.le,div_eq_mul_inv]
  rwa [hlog,hpower,hpop] at hh

end
end KakeyaFormal.SourceMarkedNormalization
