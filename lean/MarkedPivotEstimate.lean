import OriginalMarkedPivot
import PivotLossAbsorption

/-! Uniform original marked pivot estimates. The actual fourth-power
construction and explicit product-kappa choice are instantiated internally;
the caller supplies only the original marked geometry and fixed logarithmic
conditioning budgets. Angular conditioning and two-ends removal remain outside
this module. -/
namespace KakeyaFormal.MarkedPivotEstimate
open Finset OriginalPivotSlabs PivotLossAbsorption
noncomputable section
open Classical

theorem enlarge_scale {n M : ℕ} {F : TubeFamily n M} {E : Finset (Cell n)}
    {marks : Fin M → Finset (Cell n)}
    {δ₀ δ₁ δ A lam xi B theta width baseRadius m alpha B₀ K₀ b q : ℝ}
    (h : Hypotheses F E marks δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ b q)
    (hscale : δ₀ ≤ δ₁) :
    Hypotheses F E marks δ₁ δ A lam xi B theta width baseRadius m alpha B₀ K₀ b q :=
  { h with scale_small := h.scale_small.trans hscale }

def normalization (width baseRadius : ℝ) (hw : 0 < width) : Normalization where
  width := width
  separation := 1
  radius := max 1 baseRadius
  width_pos := hw
  separation_pos := by norm_num
  radius_pos := zero_lt_one.trans_le (le_max_left _ _)

/-- The original family itself supplies the finite-density and total-population
budgets. There is no additional geometric hypothesis hidden in this adapter. -/
def configuration {n M : ℕ} {F : TubeFamily n M} {E : Finset (Cell n)}
    {marks : Fin M → Finset (Cell n)}
    {δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ b q : ℝ}
    (h : Hypotheses F E marks δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ b q)
    (hw : 0 < width) (hδ₀ : δ₀ ≤ 1) (hlam : lam ≤ 1) :
    ShadedConfiguration n (normalization width baseRadius hw) m where
  M := M
  δ := δ
  lam := lam
  A := A
  family := F
  scale_pos := h.scale_pos
  scale_le_one := h.scale_small.trans hδ₀
  density_pos := h.density_pos
  density_le_one := hlam
  cap_ge_one := h.cap_coefficient
  admissible := h.admissible
  separated := by simpa only [normalization,one_mul] using h.separated
  bounded := fun i => (h.bounded i).trans (le_max_right _ _)
  cap_bound := h.cap_bound
  comparable := h.comparable

/-- The actual choice uses the recovered two-ends coefficient 2B. Its lower
budget has a fixed prefactor and exponent b/alpha+q, without a density loss. -/
theorem kappa_log_lower {n M : ℕ} {F : TubeFamily n M} {E : Finset (Cell n)}
    {marks : Fin M → Finset (Cell n)}
    {δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ b q : ℝ}
    (h : Hypotheses F E marks δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ b q)
    (hw : 0 ≤ width) (hδ₀ : δ₀ ≤ 1) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) :
    PivotKappa.choice width (2*B₀) K₀ alpha 1 *
      (Real.log (2/δ))^(-(b/alpha+q)) ≤ kappa width B theta alpha := by
  have hδ1 : δ ≤ 1 := h.scale_small.trans hδ₀
  have hL : 0 < Real.log (2/δ) :=
    Real.log_pos ((lt_div_iff₀ h.scale_pos).mpr (by linarith))
  have hB : 0 < B := zero_lt_one.trans_le h.two_ends_coefficient
  have hBB : 2*B ≤ (2*B₀)*(Real.log (2/δ))^b := by
    nlinarith [h.two_ends_budget]
  have hh := PivotKappa.choice_log_lower hw (by positivity : 0 < 2*B)
    (inv_pos.mpr h.angular_radius_pos) (by positivity : 0 < 2*B₀) hK₀ ha
    (by norm_num : (0:ℝ) < 1) hL hBB h.angular_budget
  simpa only [PivotKappa.loss,div_one] using hh

/-- The base-two selection depth can be replaced by the common natural log
with a fixed coefficient, preserving the exact fourth-power exponents. -/
theorem natural_log_fourth {δ c A kap xi p q n m d' e lam S E : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hc : 0 < c) (hA : 0 < A)
    (hk : 0 < kap) (hx : 0 < xi) (hp : 1 ≤ p) (hlam : 0 < lam) (hS : 0 ≤ S)
    (hfour : c*kap^(5*n+6*q+12)*A⁻¹*xi^(p+3)*
      (PivotSelectionBudgets.pivotLog δ)^(-(p+4))*δ^(-2*m-3-d'+3*e)*
      lam^(p+2*q+4+2*e)*S^3 ≤ E^4) :
    (c*(3/Real.log 2)^(-(p+4)))*A⁻¹*kap^(5*n+6*q+12)*xi^(p+3)*
      (Real.log (2/δ))^(-(p+4))*δ^(-2*m-3-d'+3*e)*
      lam^(p+2*q+4+2*e)*S^3 ≤ E^4 := by
  have hlog := pivotLog_inverse_power hδ hδ1 (by linarith : 0 ≤ p+4)
  have hh := mul_le_mul_of_nonneg_left hlog
    (by positivity : 0 ≤ c*kap^(5*n+6*q+12)*A⁻¹*xi^(p+3)*
      δ^(-2*m-3-d'+3*e)*lam^(p+2*q+4+2*e)*S^3)
  calc
    _ = (c*kap^(5*n+6*q+12)*A⁻¹*xi^(p+3)*δ^(-2*m-3-d'+3*e)*
        lam^(p+2*q+4+2*e)*S^3)*
        ((3/Real.log 2)^(-(p+4))*(Real.log (2/δ))^(-(p+4))) := by ring
    _ ≤ (c*kap^(5*n+6*q+12)*A⁻¹*xi^(p+3)*δ^(-2*m-3-d'+3*e)*
        lam^(p+2*q+4+2*e)*S^3)*(PivotSelectionBudgets.pivotLog δ)^(-(p+4)) := hh
    _ = _ := by ring
    _ ≤ _ := hfour

/-- Uniform marked first-power estimate for original finite configurations.
The absorption error is chosen before the actual fourth-power constant.
No analytic energy, desired E-fourth inequality, or kappa budget is an input. -/
theorem construct {k : ℕ} {m d d' p q : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p)
    (hlift : DiscreteEstimate (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width)
    (eps : ℝ) (heps : 0 < eps)
    (B₀ K₀ xi₀ alpha bLog qLog xLog : ℝ)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hx₀ : 0 < xi₀)
    (ha : 0 < alpha) (hb : 0 ≤ bLog) (hlogq : 0 ≤ qLog) (hxlog : 0 ≤ xLog) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta : ℝ},
      Hypotheses F E marks δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ bLog qLog →
      lam ≤ 1 → xi ≤ 1 → xi₀*(Real.log (2/δ))^(-xLog) ≤ xi →
      c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity p q)*(M:ℝ) ≤ (E.card:ℝ) := by
  have hw0 : 0 ≤ width := by linarith
  have hwp : 0 < width := by linarith
  let k₀ := PivotKappa.choice width (2*B₀) K₀ alpha 1
  have hk₀ : 0 < k₀ := PivotKappa.choice_pos hw0 (by positivity) hK₀
  have haLog : 0 ≤ bLog/alpha+qLog := by positivity
  have hC : 0 < ProjectiveGeometry.packingConstant (k+1) :=
    zero_lt_one.trans_le (ProjectiveGeometry.packingConstant_ge_one (k+1))
  obtain ⟨e,he,he1,habsorb⟩ := pivot_small_scale_absorption (k+1)
    (m := m) (d' := d') (T := 0) hp hq hk₀ hx₀ haLog hxlog hC heps
  obtain ⟨δraw,hδraw,hδraw1,craw,hcraw,hraw⟩ := OriginalMarkedPivot.construct
    hbase hlift hm hp hd hq width baseRadius hw e he he1
    B₀ K₀ alpha bLog qLog hB₀ hK₀ ha hb hlogq
  let cnat := craw*(3/Real.log 2)^(-(p+4))
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hcnat : 0 < cnat := by dsimp [cnat]; positivity
  obtain ⟨δabs,c,hδabs,hδabs1,hc,hfirst⟩ := habsorb cnat hcnat
  refine ⟨min δraw δabs,lt_min hδraw hδabs,(min_le_left _ _).trans hδraw1,c,hc,?_⟩
  intro M F E marks δ A lam xi B theta h hlam1 hxi1 hxi
  have hδ1 : δ ≤ 1 := h.scale_small.trans ((min_le_left _ _).trans hδraw1)
  have hrawHyp := enlarge_scale h (min_le_left δraw δabs)
  have hfour := hraw F E marks hrawHyp hlam1 hxi1
  have hk := kappa_log_lower h hw0 ((min_le_left _ _).trans hδraw1) hB₀ hK₀ ha
  have hkap : 0 < kappa width B theta alpha := PivotKappa.choice_pos hw0
    (by linarith [h.two_ends_coefficient]) (inv_pos.mpr h.angular_radius_pos)
  let V := configuration h hwp ((min_le_left _ _).trans hδraw1) hlam1
  have hS : 0 < (M:ℝ)*δ^m := by
    have hM : (0:ℝ) < M := by exact_mod_cast h.count_pos
    positivity [h.scale_pos]
  have hpop : (M:ℝ)*δ^m ≤ ProjectiveGeometry.packingConstant (k+1)*A :=
    configuration_population_bound _ V
  have hnat := natural_log_fourth h.scale_pos hδ1 hcraw
    (zero_lt_one.trans_le h.cap_coefficient) hkap h.marked_fraction_pos hp h.density_pos hS.le hfour
  have hfinal := (hfirst δ (kappa width B theta alpha) xi lam A ((M:ℝ)*δ^m) (E.card:ℝ)
    h.scale_pos (h.scale_small.trans (min_le_right _ _)) h.density_pos
    (V.density_ge_half_scale h.count_pos) h.cap_coefficient hS hpop (Nat.cast_nonneg _) hk hxi).2.2 hnat
  have hid : δ^(m-KakeyaScalar.pivotSet m d'+eps) =
      δ^(-KakeyaScalar.pivotSet m d'+eps)*δ^m := by
    rw [← Real.rpow_add h.scale_pos]
    congr 1
    ring
  rw [hid]
  convert hfinal using 1
  ring

/-- The remaining coarse scales follow from one actual tube and the actual cap
population bound. This estimate is uniform for every 0<delta<=1 satisfying the
original marked hypotheses and the fixed conditioning budgets. -/
theorem all_scales {k : ℕ} {m d d' p q : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p)
    (hlift : DiscreteEstimate (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width)
    (eps : ℝ) (heps : 0 < eps)
    (B₀ K₀ xi₀ alpha bLog qLog xLog : ℝ)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hx₀ : 0 < xi₀)
    (ha : 0 < alpha) (hb : 0 ≤ bLog) (hlogq : 0 ≤ qLog) (hxlog : 0 ≤ xLog) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta : ℝ},
      Hypotheses F E marks 1 δ A lam xi B theta width baseRadius m alpha B₀ K₀ bLog qLog →
      lam ≤ 1 → xi ≤ 1 → xi₀*(Real.log (2/δ))^(-xLog) ≤ xi →
      c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity p q)*(M:ℝ) ≤ (E.card:ℝ) := by
  obtain ⟨δ₀,hδ₀,_,c,hc,hfine⟩ := construct hbase hlift hm hp hd hq
    width baseRadius hw eps heps B₀ K₀ xi₀ alpha bLog qLog xLog
    hB₀ hK₀ hx₀ ha hb hlogq hxlog
  let C := 1/(ProjectiveGeometry.packingConstant (k+1)*
    max 1 (δ₀^(1-KakeyaScalar.pivotSet m d'+eps)))
  have hpacking : 0 < ProjectiveGeometry.packingConstant (k+1) :=
    zero_lt_one.trans_le (ProjectiveGeometry.packingConstant_ge_one (k+1))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min c C,lt_min hc hC,?_⟩
  intro M F E marks δ A lam xi B theta h hlam1 hxi1 hxi
  have hA : 0 < A := zero_lt_one.trans_le h.cap_coefficient
  have hcoef : 0 ≤ A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
      lam^(KakeyaScalar.pivotDensity p q)*(M:ℝ) := by
    positivity [h.scale_pos,h.density_pos]
  by_cases hscale : δ ≤ δ₀
  · have hh := mul_le_mul_of_nonneg_right (min_le_left c C) hcoef
    have hsmall : Hypotheses F E marks δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ bLog qLog :=
      { h with scale_small := hscale }
    have hbound := hfine F E marks hsmall hlam1 hxi1 hxi
    have hle : (min c C)*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity p q)*(M:ℝ) ≤
        c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity p q)*(M:ℝ) := by
      simpa only [mul_assoc] using hh
    exact hle.trans hbound
  · let V := configuration h (by linarith : 0 < width) le_rfl hlam1
    have hpower : 1 ≤ KakeyaScalar.pivotDensity p q := by
      unfold KakeyaScalar.pivotDensity
      linarith
    have hbound := CoarseBounds.coarse_configuration_bound
      (d := KakeyaScalar.pivotSet m d') (eps := eps) hδ₀ hpower _ V (le_of_lt (lt_of_not_ge hscale))
    have hcover : F.unionCells ⊆ E := by
      intro z hz
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
      exact h.cover i hi
    have hcovered : (F.unionCells.card:ℝ) ≤ (E.card:ℝ) := by
      exact_mod_cast card_le_card hcover
    have hh := mul_le_mul_of_nonneg_right (min_le_right c C) hcoef
    have hle : (min c C)*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity p q)*(M:ℝ) ≤
        C*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity p q)*(M:ℝ) := by
      simpa only [mul_assoc] using hh
    exact hle.trans (hbound.trans hcovered)

end
end KakeyaFormal.MarkedPivotEstimate
