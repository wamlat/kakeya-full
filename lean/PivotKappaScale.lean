import PivotKappa
import LogLoss

/-! Uniform scale cutoffs for the explicit legal pivot parameter. The cutoff
is chosen before the concentration coefficients or configurations vary. -/
namespace KakeyaFormal.PivotKappaScale
open Filter PivotKappa

/-- A fixed positive lower power bound for kappa gives a cutoff that is
uniform over every later choice of kappa. The twentieth power is the manuscript's
strongest displayed small-scale requirement at the pivot step. -/
theorem power_lower_cutoff {a T : ℝ} (ha : 0 < a) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N kap : ℝ, N₀ ≤ N →
      a*N^(-(1:ℝ)/40) ≤ kap → 1/N ≤ kap ∧ T ≤ N*kap^20 := by
  have hfirst := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<39/40)).const_mul_atTop ha
  have hsecond := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).const_mul_atTop
    (show 0 < a^20 by positivity)
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (hfirst.eventually_ge_atTop 1)
  obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp (hsecond.eventually_ge_atTop T)
  refine ⟨max 1 (max N₁ N₂),le_max_left _ _,?_⟩
  intro N kap hN hk
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by linarith
  have h₁ := hN₁ N ((le_max_left N₁ N₂).trans ((le_max_right 1 _).trans hN))
  have h₂ := hN₂ N ((le_max_right N₁ N₂).trans ((le_max_right 1 _).trans hN))
  have hid₁ : N*(a*N^(-(1:ℝ)/40)) = a*N^((39:ℝ)/40) := by
    calc
      _ = a*(N^(1:ℝ)*N^(-(1:ℝ)/40)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hNpos]; norm_num
  have hid₂ : N*(a*N^(-(1:ℝ)/40))^20 = a^20*N^((1:ℝ)/2) := by
    calc
      _ = a^20*(N^(1:ℝ)*(N^(-(1:ℝ)/40))^20) := by rw [Real.rpow_one,mul_pow]; ring
      _ = _ := by rw [← Real.rpow_mul_natCast hNpos.le,← Real.rpow_add hNpos]; norm_num
  have hmul := mul_le_mul_of_nonneg_left hk hNpos.le
  have hpow := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0 ≤ a*N^(-(1:ℝ)/40)) hk 20) hNpos.le
  rw [hid₁] at hmul
  rw [hid₂] at hpow
  exact ⟨(div_le_iff₀ hNpos).mpr (by nlinarith),h₂.trans hpow⟩

/-- Fixed polynomial logarithmic budgets give a single uniform pivot-scale
cutoff, also after an arbitrary fixed positive common homothety. Neither N₀
nor its proof depends on the later B,K, density, tube family, or shadings. -/
theorem normalized_choice_cutoff {width B₀ K₀ alpha beta b q R T : ℝ}
    (hw : 0 ≤ width) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 < beta) (hb₀ : 0 ≤ b) (hq : 0 ≤ q) (hR : 0 < R) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N B K : ℝ, N₀ ≤ N → 0 < B → 0 < K →
      B ≤ B₀*(Real.log (2*N))^b → K ≤ K₀*(Real.log (2*N))^q →
      1/N ≤ choice width B K alpha beta/R ∧
        T ≤ N*(choice width B K alpha beta/R)^20 := by
  obtain ⟨c,hc,hclog⟩ := inverse_log_power_uniform_bound
    (loss_nonneg ha hb hb₀ hq) (by norm_num : (0:ℝ)<1/40)
  have hbase := choice_pos (alpha:=alpha) (beta:=beta) hw hB₀ hK₀
  obtain ⟨N₀,hN₀,hcut⟩ := power_lower_cutoff (T:=T)
    (show 0 < (choice width B₀ K₀ alpha beta/R)*c by positivity)
  refine ⟨N₀,hN₀,?_⟩
  intro N B K hN hB hK hBB hKK
  have hN1 := hN₀.trans hN
  have hlog : 0 < Real.log (2*N) := Real.log_pos (by linarith)
  have hlogs := normalized_choice_log_lower hw hB hK hB₀ hK₀ ha hb hlog hR hBB hKK
  have hh := mul_le_mul_of_nonneg_left (hclog N hN1)
    (show 0 ≤ choice width B₀ K₀ alpha beta/R by positivity)
  apply hcut N _ hN
  calc
    (choice width B₀ K₀ alpha beta/R*c)*N^(-(1:ℝ)/40) =
        (choice width B₀ K₀ alpha beta/R)*(c*N^(-(1:ℝ)/40)) := by ring
    _ ≤ choice width B K alpha beta/R := by simpa only [neg_div] using hh.trans hlogs

/-- The unnormalized special case retains the same quantifier order. -/
theorem choice_cutoff {width B₀ K₀ alpha beta b q T : ℝ}
    (hw : 0 ≤ width) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 < beta) (hb₀ : 0 ≤ b) (hq : 0 ≤ q) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N B K : ℝ, N₀ ≤ N → 0 < B → 0 < K →
      B ≤ B₀*(Real.log (2*N))^b → K ≤ K₀*(Real.log (2*N))^q →
      1/N ≤ choice width B K alpha beta ∧ T ≤ N*(choice width B K alpha beta)^20 := by
  simpa only [div_one] using normalized_choice_cutoff (R:=1) (T:=T)
    hw hB₀ hK₀ ha hb hb₀ hq (by norm_num)

/-- The same uniform result in the physical delta variable, ready for a
small-scale/coarse-scale estimate split. The threshold is fixed before delta,
B,K and any tube configuration are supplied. -/
theorem normalized_choice_small_scales {width B₀ K₀ alpha beta b q R T : ℝ}
    (hw : 0 ≤ width) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 < beta) (hb₀ : 0 ≤ b) (hq : 0 ≤ q) (hR : 0 < R) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ B K : ℝ, 0 < δ → δ ≤ δ₀ →
      0 < B → 0 < K →
      B ≤ B₀*(Real.log (2/δ))^b → K ≤ K₀*(Real.log (2/δ))^q →
      δ ≤ choice width B K alpha beta/R ∧
        T ≤ (1/δ)*(choice width B K alpha beta/R)^20 := by
  obtain ⟨N₀,hN₀,hcut⟩ := normalized_choice_cutoff (T:=T)
    hw hB₀ hK₀ ha hb hb₀ hq hR
  have hN₀pos : 0 < N₀ := by linarith
  refine ⟨1/N₀,by positivity,(div_le_one hN₀pos).mpr hN₀,?_⟩
  intro δ B K hδ hsmall hB hK hBB hKK
  have hN : N₀ ≤ 1/δ := by
    have hh := one_div_le_one_div_of_le hδ hsmall
    simpa only [one_div_one_div] using hh
  have hBB' : B ≤ B₀*(Real.log (2*(1/δ)))^b := by simpa only [mul_one_div] using hBB
  have hKK' : K ≤ K₀*(Real.log (2*(1/δ)))^q := by simpa only [mul_one_div] using hKK
  simpa only [one_div_one_div] using hcut (1/δ) B K hN hB hK hBB' hKK'

end KakeyaFormal.PivotKappaScale

#print axioms KakeyaFormal.PivotKappaScale.power_lower_cutoff
#print axioms KakeyaFormal.PivotKappaScale.normalized_choice_cutoff
#print axioms KakeyaFormal.PivotKappaScale.choice_cutoff
#print axioms KakeyaFormal.PivotKappaScale.normalized_choice_small_scales
