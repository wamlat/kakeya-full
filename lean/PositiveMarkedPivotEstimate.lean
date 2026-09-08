import SourceMarkedPivotFullRange
import MarkedPivotEstimate

/-! Positive-base-density extension of the actual marked first-power pivot.
The positive trimming theorem constructs the fourth-power bound at the old
explicit product radius, and the same fixed logarithmic losses are absorbed.
The marked normalization is deliberately unchanged. -/
namespace KakeyaFormal.PositiveMarkedPivotEstimate
open Finset OriginalPivotSlabs PivotLossAbsorption MarkedPivotEstimate
noncomputable section
open Classical

theorem pivot_small_scale_absorption (n : ℕ)
    {m d' p q k₀ x₀ a b C₀ T eps : ℝ}
    (hp : 0 < p) (hq : 2 ≤ q) (hk₀ : 0 < k₀) (hx₀ : 0 < x₀)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC₀ : 0 < C₀) (heps : 0 < eps) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ ∀ c₀ : ℝ, 0 < c₀ →
      ∃ δ₀ c : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ 0 < c ∧
      ∀ δ kappa xi lam A S E : ℝ,
      0 < δ → δ ≤ δ₀ → 0 < lam → δ/2 ≤ lam → 1 ≤ A → 0 < S → S ≤ C₀*A → 0 ≤ E →
      k₀*(Real.log (2/δ))^(-a) ≤ kappa → x₀*(Real.log (2/δ))^(-b) ≤ xi →
      δ ≤ kappa ∧ T ≤ (1/δ)*kappa^20 ∧
      (c₀*A⁻¹*kappa^(5*(n:ℝ)+6*q+12)*xi^(p+3)*(Real.log (2/δ))^(-(p+4))*
        δ^(-2*m-3-d'+3*e)*lam^(p+2*q+4+2*e)*S^3 ≤ E^4 →
        c*A⁻¹*δ^(-KakeyaScalar.pivotSet m d'+eps)*lam^(KakeyaScalar.pivotDensity p q)*S ≤ E) := by
  let e := min (1/2:ℝ) (eps/4)
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have he1 : e ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have herror : 7*e ≤ 4*eps := by have := min_le_right (1/2:ℝ) (eps/4); dsimp [e]; linarith
  refine ⟨e,he,he1,?_⟩
  intro c₀ hc₀
  obtain ⟨c,hc,hbound⟩ := uniform_absorption
    (D := KakeyaScalar.pivotSet m d') (C := KakeyaScalar.pivotDensity p q)
    (H := 5*(n:ℝ)+6*q+12) (P := p+3) (Z := p+4)
    (by positivity : 0 ≤ 5*(n:ℝ)+6*q+12) (by linarith : 0 ≤ p+3) (by linarith : 0 ≤ p+4)
    ha hb hk₀ hx₀ hC₀ hc₀ he herror
  obtain ⟨δ₀,hδ₀,hδ₀1,hscale⟩ := polylog_small_scales (T := T) hk₀ ha
  refine ⟨δ₀,c,hδ₀,hδ₀1,hc,?_⟩
  intro δ kappa xi lam A S E hδ hδsmall hlam hdensity hA hS hSC hE hk hx
  obtain ⟨hδk,h20⟩ := hscale δ kappa hδ hδsmall hk
  refine ⟨hδk,h20,?_⟩
  intro hfour
  apply hbound δ kappa xi lam A S E hδ (hδsmall.trans hδ₀1) hlam hdensity hA hS hSC hE hk hx
  have hd : -4*KakeyaScalar.pivotSet m d'+3*e = -2*m-3-d'+3*e := by unfold KakeyaScalar.pivotSet; ring
  have hl : 4*KakeyaScalar.pivotDensity p q+2*e = p+2*q+4+2*e := by unfold KakeyaScalar.pivotDensity; ring
  simpa only [hd,hl] using hfour


/-- Actual original marked estimate for every positive base-density power. -/
theorem construct {k : ℕ} {m d d' p q : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p)
    (hlift : DiscreteEstimate (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
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
    (m := m) (d' := d') (T := PivotGeometryScale.geometryConstant (k+2) width*(1+2*width)^20) hp hq hk₀ hx₀ haLog hxlog hC heps
  obtain ⟨craw,hcraw,hraw⟩ := SourceMarkedPivotFullRange.admissible_fourth
    hbase hlift hm hp hd hq width baseRadius hw e he he1
  let cnat := craw*(3/Real.log 2)^(-(p+4))
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hcnat : 0 < cnat := by dsimp [cnat]; positivity
  obtain ⟨δabs,c,hδabs,hδabs1,hc,hfirst⟩ := habsorb cnat hcnat
  refine ⟨δabs,hδabs,hδabs1,c,hc,?_⟩
  intro M F E marks δ A lam xi B theta h hlam1 hxi1 hxi
  have hδ1 : δ ≤ 1 := h.scale_small.trans hδabs1
  have hk := kappa_log_lower h hw0 hδabs1 hB₀ hK₀ ha
  have hkap : 0 < kappa width B theta alpha := PivotKappa.choice_pos hw0
    (by linarith [h.two_ends_coefficient]) (inv_pos.mpr h.angular_radius_pos)
  let V := configuration h hwp hδabs1 hlam1
  have hS : 0 < (M:ℝ)*δ^m := by
    have hM : (0:ℝ) < M := by exact_mod_cast h.count_pos
    positivity [h.scale_pos]
  have hpop : (M:ℝ)*δ^m ≤ ProjectiveGeometry.packingConstant (k+1)*A :=
    configuration_population_bound _ V
  have hfirstData := hfirst δ (kappa width B theta alpha) xi lam A ((M:ℝ)*δ^m) (E.card:ℝ)
    h.scale_pos h.scale_small h.density_pos
    (V.density_ge_half_scale h.count_pos) h.cap_coefficient hS hpop (Nat.cast_nonneg _) hk hxi
  have hrawHyp : AdmissiblePivotSlabs.Hypotheses F E marks δ A lam xi B theta width baseRadius m alpha := {
    scale_le_one := hδ1
    scale_pos := h.scale_pos
    cap_coefficient := h.cap_coefficient
    density_pos := h.density_pos
    marked_fraction_pos := h.marked_fraction_pos
    count_pos := h.count_pos
    two_ends_coefficient := h.two_ends_coefficient
    angular_radius_pos := h.angular_radius_pos
    angular_radius_le_one := h.angular_radius_le_one
    cover := h.cover
    admissible := h.admissible
    separated := h.separated
    bounded := h.bounded
    cap_bound := h.cap_bound
    comparable := h.comparable
    marks_subset := h.marks_subset
    marked_mass := h.marked_mass
    marked_broad := h.marked_broad
    two_ends := h.two_ends
  }
  obtain ⟨hkap',hk100,hangle,hradius,hlegal⟩ := MarkedSubsetSamples.fixed_radius_choice hw0
    (by linarith [h.two_ends_coefficient] : 1 ≤ 2*B) ha h.angular_radius_pos h.angular_radius_le_one
  have hk1 : kappa width B theta alpha ≤ 1 := hk100.trans (by norm_num)
  have htests := PivotGeometryScale.tests_of_original_twentieth (k+2)
    h.scale_pos hkap hk1 hw0 hfirstData.2.1
  have hfour := hraw F E marks hrawHyp hlam1 hxi1 hkap' hk1 hangle hradius hlegal htests
  have hnat := PositivePivotAlgebra.natural_log_fourth h.scale_pos hδ1 hcraw
    (zero_lt_one.trans_le h.cap_coefficient) hkap h.marked_fraction_pos hp h.density_pos hS.le hfour
  have hfinal := hfirstData.2.2 hnat
  have hid : δ^(m-KakeyaScalar.pivotSet m d'+eps) =
      δ^(-KakeyaScalar.pivotSet m d'+eps)*δ^m := by
    rw [← Real.rpow_add h.scale_pos]
    congr 1
    ring
  rw [hid]
  convert hfinal using 1
  ring


/-- Every original scale, with the same actual marked inputs and fixed budgets. -/
theorem all_scales {k : ℕ} {m d d' p q : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p)
    (hlift : DiscreteEstimate (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
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
end KakeyaFormal.PositiveMarkedPivotEstimate
