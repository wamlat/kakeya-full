import AdmissiblePivotClosing
import MarkedPivotEstimate

/-! The source-minimum marked pivot fourth-power estimate on actual original
families. Constants precede B, theta, alpha and configurations; the only extra
scale restriction is the explicit original N*kappa^20 cutoff. This module keeps
the existing analytic range p>=1 visible. -/
namespace KakeyaFormal.SourceMarkedPivot
open Finset AdmissiblePivotSlabs
noncomputable section
open Classical

/-- Actual original-input fourth-power bound at any supplied admissible radius.
No pruning, sample population, selected output, spatial bound or energy premise
is supplied by the caller. -/
theorem admissible_fourth {k : ℕ} {m d d' p q : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p)
    (hlift : DiscreteEstimate (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta alpha kap : ℝ},
      Hypotheses F E marks δ A lam xi B theta width baseRadius m alpha →
      lam ≤ 1 → xi ≤ 1 → 0 < kap → kap ≤ 1 → 2*kap ≤ theta →
      (2*width+1)*kap ≤ 1 → (2*B)*((2*width+1)*kap)^alpha ≤ 1/16 →
      PivotGeometryScale.Tests (k+2) δ kap width →
      c*kap^(5*((k+1:ℕ):ℝ)+6*q+12)*A⁻¹*xi^(p+3)*
        (PivotSelectionBudgets.pivotLog δ)^(-(p+4))*δ^(-2*m-3-d'+3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)*δ^m)^3 ≤ (E.card:ℝ)^4 := by
  have hw0 : 0 ≤ width := by linarith
  have hwp : 0 < width := by linarith
  obtain ⟨K,hK,hpackage⟩ := AdmissiblePivotSlabs.construct
    hbase hm hp hd width baseRadius hw eps heps
  let geom : Normalization := {
    width := width
    separation := 1
    radius := max 1 baseRadius
    width_pos := hwp
    separation_pos := by norm_num
    radius_pos := zero_lt_one.trans_le (le_max_left _ _) }
  obtain ⟨cBase,hBase,hbaseBound⟩ := hbase geom eps heps
  have hlift' : DiscreteEstimate (k+3) d d' (q+eps) :=
    hlift.weaken_density (by linarith)
  obtain ⟨cClose,hClose,henergy⟩ := AdmissiblePivotClosing.energy width baseRadius hw0 hd
    hlift' (by linarith : 1 ≤ q+eps) heps
  refine ⟨OriginalPivotScalar.coefficient k width K cBase cClose p q eps,
    OriginalPivotScalar.coefficient_pos k hw0 hK hBase hClose,?_⟩
  intro M F E marks δ A lam xi B theta alpha kap h hlam1 hxi1 hk hk1 hangle hradius hlegal htests
  obtain ⟨U⟩ := hpackage F E marks h hk hk1 hangle hradius hlegal htests
  obtain ⟨rho,hrho,hRho,hCloseBound⟩ := henergy K F E marks U
  let V : ShadedConfiguration (k+2) geom m := {
    M := M
    δ := δ
    lam := lam
    A := A
    family := F
    scale_pos := h.scale_pos
    scale_le_one := h.scale_le_one
    density_pos := h.density_pos
    density_le_one := hlam1
    cap_ge_one := h.cap_coefficient
    admissible := h.admissible
    separated := by simpa only [geom,one_mul] using h.separated
    bounded := fun i => (h.bounded i).trans (le_max_right _ _)
    cap_bound := h.cap_bound
    comparable := h.comparable }
  have hUE : F.unionCells ⊆ E := by
    intro z hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    exact h.cover i hi
  have hbaseOriginal : cBase*A⁻¹*δ^(m-d+eps)*lam^p*(M:ℝ) ≤ (E.card:ℝ) :=
    (hbaseBound V).trans (by exact_mod_cast card_le_card hUE)
  exact AdmissiblePivotClosing.fourth_power U hK hBase hClose
    (zero_lt_one.trans_le h.cap_coefficient) h.density_pos h.marked_fraction_pos hxi1 h.count_pos
    hp hq heps.le heps1 hbaseOriginal hRho hCloseBound


/-- Literal minimum-kappa fourth-power bound, with the source natural logarithm.
The constant is uniform in original B, theta, alpha, scale and density. -/
theorem source_fourth {k : ℕ} {m d d' p q : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p)
    (hlift : DiscreteEstimate (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta alpha : ℝ},
      Hypotheses F E marks δ A lam xi B theta width baseRadius m alpha →
      lam ≤ 1 → xi ≤ 1 → 0 < alpha →
      PivotGeometryScale.geometryConstant (k+2) width*(1+2*width)^20 ≤
        (1/δ)*(MinPivotKappa.sourceChoice width B alpha theta)^20 →
      c*A⁻¹*(MinPivotKappa.sourceChoice width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
        xi^(p+3)*(Real.log (2/δ))^(-(p+4))*δ^(-2*m-3-d'+3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)*δ^m)^3 ≤ (E.card:ℝ)^4 := by
  obtain ⟨c,hc,hfour⟩ := admissible_fourth hbase hlift hm hp hd hq width baseRadius hw eps heps heps1
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  refine ⟨c*(3/Real.log 2)^(-(p+4)),by positivity,?_⟩
  intro M F E marks δ A lam xi B theta alpha h hlam1 hxi1 ha hscale
  have hw0 : 0 ≤ width := by linarith
  obtain ⟨hk,hk100,hangle,hradius,hlegal⟩ := MinPivotKappa.source_admissible hw0
    h.two_ends_coefficient ha h.angular_radius_pos
  have hk1 : MinPivotKappa.sourceChoice width B alpha theta ≤ 1 := hk100.trans (by norm_num)
  have htests := PivotGeometryScale.tests_of_original_twentieth (k+2) h.scale_pos hk hk1 hw0 hscale
  have hh := hfour F E marks h hlam1 hxi1 hk hk1 hangle hradius hlegal htests
  exact MarkedPivotEstimate.natural_log_fourth h.scale_pos h.scale_le_one hc
    (zero_lt_one.trans_le h.cap_coefficient) hk h.marked_fraction_pos hp h.density_pos
    (by positivity [h.scale_pos] : 0 ≤ (M:ℝ)*δ^m) hh

/-- Source Theorem 5.1 at a fixed absolute cap coefficient and the literal
original occupied union. The cutoff and estimate constants are chosen before
N, lambda, M, xi, B, theta and alpha. The same source minimum is used throughout.
The currently formalized base-density range is p>=1. -/
theorem source_union {k : ℕ} {m d d' p q : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p)
    (hlift : DiscreteEstimate (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width baseRadius A₀ : ℝ) (hw : (1:ℝ)/12 ≤ width) (hA₀ : 1 ≤ A₀)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M)
      (marks : Fin M → Finset (Cell (k+2))) {δ lam xi B theta alpha : ℝ},
      Hypotheses F F.unionCells marks δ A₀ lam xi B theta width baseRadius m alpha →
      lam ≤ 1 → xi ≤ 1 → 0 < alpha →
      T ≤ (1/δ)*(MinPivotKappa.sourceChoice width B alpha theta)^20 →
      c*(MinPivotKappa.sourceChoice width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
        xi^(p+3)*(Real.log (2/δ))^(-(p+4))*δ^(-2*m-3-d'+3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)*δ^m)^3 ≤ (F.unionCells.card:ℝ)^4 := by
  obtain ⟨c,hc,hfour⟩ := source_fourth hbase hlift hm hp hd hq width baseRadius hw eps heps heps1
  have hT : 0 < PivotGeometryScale.geometryConstant (k+2) width :=
    zero_lt_one.trans_le (PivotGeometryScale.constant_bounds (k+2) width).1
  have hw0 : 0 ≤ width := by linarith
  refine ⟨PivotGeometryScale.geometryConstant (k+2) width*(1+2*width)^20,
    c*A₀⁻¹,by positivity,by positivity,?_⟩
  intro M F marks δ lam xi B theta alpha h hlam1 hxi1 ha hscale
  exact hfour F F.unionCells marks h hlam1 hxi1 ha hscale

/-- The same actual-union theorem in the manuscript's N, L=log(2N),
S=M/N^m notation. N may be real; the original grid mesh is exactly 1/N. -/
theorem source_notation {k : ℕ} {m d d' p q : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p)
    (hlift : DiscreteEstimate (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width baseRadius A₀ : ℝ) (hw : (1:ℝ)/12 ≤ width) (hA₀ : 1 ≤ A₀)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    ∃ T c : ℝ, 0 < T ∧ 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M)
      (marks : Fin M → Finset (Cell (k+2))) {N lam xi B theta alpha : ℝ},
      2 ≤ N →
      Hypotheses F F.unionCells marks (1/N) A₀ lam xi B theta width baseRadius m alpha →
      lam ≤ 1 → xi ≤ 1 → 0 < alpha →
      T ≤ N*(MinPivotKappa.sourceChoice width B alpha theta)^20 →
      c*(MinPivotKappa.sourceChoice width B alpha theta)^(5*((k+1:ℕ):ℝ)+6*q+12)*
        xi^(p+3)*(Real.log (2*N))^(-(p+4))*N^(2*m+3+d'-3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)/N^m)^3 ≤ (F.unionCells.card:ℝ)^4 := by
  obtain ⟨T,c,hT,hc,hbound⟩ := source_union hbase hlift hm hp hd hq
    width baseRadius A₀ hw hA₀ eps heps heps1
  refine ⟨T,c,hT,hc,?_⟩
  intro M F marks N lam xi B theta alpha hN h hlam1 hxi1 ha hscale
  have hN0 : 0 < N := by linarith
  have hscale' : T ≤ (1/(1/N))*(MinPivotKappa.sourceChoice width B alpha theta)^20 := by
    simpa only [one_div,inv_inv] using hscale
  have hh := hbound F marks h hlam1 hxi1 ha hscale'
  have hlog : 2/(1/N) = 2*N := by field_simp
  have hpower : (1/N)^(-2*m-3-d'+3*eps) = N^(2*m+3+d'-3*eps) := by
    rw [one_div,Real.inv_rpow hN0.le,← Real.rpow_neg hN0.le]
    congr 1
    ring
  have hpop : (M:ℝ)*(1/N)^m = (M:ℝ)/N^m := by
    rw [one_div,Real.inv_rpow hN0.le,div_eq_mul_inv]
  rw [hlog,hpower,hpop] at hh
  exact hh

end
end KakeyaFormal.SourceMarkedPivot
