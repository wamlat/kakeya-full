import LogLoss

/-! The literal angular radius in (6.10), including its uniform logarithmic
lower bound and a scale threshold fixed before the later broadness constant. -/
namespace KakeyaFormal.SamplingTheta
open Filter
noncomputable section

def choice (K beta : ℝ) : ℝ := min (1/100) ((1000*K)^(-1/beta)/2)

theorem choice_pos {K beta : ℝ} (hK : 0 < K) : 0 < choice K beta := by
  unfold choice
  exact lt_min (by norm_num) (div_pos (Real.rpow_pos_of_pos (by positivity) _) (by norm_num))

theorem choice_le_hundredth (K beta : ℝ) : choice K beta ≤ 1/100 := min_le_left _ _

/-- Integrating a power-cap bound at twice the chosen radius gives the exact
small expectation ratio used by the marked upper-tail estimate. -/
theorem cap_budget {K beta : ℝ} (hK : 0 < K) (hb : 0 < beta) :
    1000*K*(2*choice K beta)^beta ≤ 1 := by
  have hbase : 0 < 1000*K := by positivity
  have hc := choice_pos (beta:=beta) hK
  have hmin := min_le_right (1/100:ℝ) ((1000*K)^(-1/beta)/2)
  have hle : 2*choice K beta ≤ (1000*K)^(-1/beta) := by unfold choice; linarith
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 2*choice K beta) hle hb.le
  have hid : ((1000*K)^(-1/beta))^beta = (1000*K)⁻¹ := by
    rw [← Real.rpow_mul hbase.le]
    have he : (-1/beta)*beta = -1 := div_mul_cancel₀ _ hb.ne'
    rw [he,Real.rpow_neg_one]
  rw [hid] at hp
  exact (mul_le_mul_of_nonneg_left hp hbase.le).trans_eq (mul_inv_cancel₀ hbase.ne')

/-- The fixed upper cap in the minimum costs no logarithmic power once L≥1. -/
theorem choice_log_lower {K K₀ beta L A : ℝ}
    (hK : 0 < K) (hK₀ : 0 < K₀) (hb : 0 < beta)
    (hL : 1 ≤ L) (hA : 0 ≤ A) (hbound : K ≤ K₀*L^A) :
    choice K₀ beta*L^(-A/beta) ≤ choice K beta := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hexp : -A/beta ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hA) hb.le
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1000*K)
    (mul_le_mul_of_nonneg_left hbound (by norm_num : (0:ℝ) ≤ 1000))
    (by exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hb.le : -1/beta ≤ 0)
  have hid : (1000*(K₀*L^A))^(-1/beta) = (1000*K₀)^(-1/beta)*L^(-A/beta) := by
    rw [show 1000*(K₀*L^A) = (1000*K₀)*L^A by ring,
      Real.mul_rpow (by positivity : 0 ≤ 1000*K₀) (Real.rpow_nonneg hLp.le _),
      ← Real.rpow_mul hLp.le]
    congr 2
    ring
  rw [hid] at hp
  have hpower : L^(-A/beta) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL hexp
  apply le_min
  · calc
      _ ≤ choice K₀ beta*1 := mul_le_mul_of_nonneg_left hpower (choice_pos hK₀).le
      _ ≤ 1/100 := by simpa using choice_le_hundredth K₀ beta
  · have hh := mul_le_mul_of_nonneg_right
      (min_le_right (1/100:ℝ) ((1000*K₀)^(-1/beta)/2)) (Real.rpow_nonneg hLp.le (-A/beta))
    exact hh.trans (by linarith)

/-- A single cutoff works for every later log-conditioned K. The resulting
radius is positive, above half a mesh, and has the actual small cap budget. -/
theorem uniform_choice {K₀ beta A : ℝ} (hK₀ : 0 < K₀) (hb : 0 < beta) (hA : 0 ≤ A) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N K : ℝ, N₀ ≤ N → 0 < K →
      K ≤ K₀*(Real.log (2*N))^A →
      0 < choice K beta ∧ 2*choice K beta ≤ 1 ∧ 1/N ≤ 2*choice K beta ∧
      1000*K*(2*choice K beta)^beta ≤ 1 ∧
      choice K₀ beta*(Real.log (2*N))^(-A/beta) ≤ choice K beta := by
  obtain ⟨c,hc,hclog⟩ := inverse_log_power_uniform_bound
    (div_nonneg hA hb.le) (by norm_num : (0:ℝ)<1/2)
  have hco : 0 < 2*choice K₀ beta*c := by positivity [choice_pos (beta:=beta) hK₀]
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/2)).const_mul_atTop hco
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  refine ⟨max 1 (max (Real.exp 1) N₁),le_max_left _ _,?_⟩
  intro N K hN hK hbound
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNp : 0 < N := zero_lt_one.trans_le hN1
  have hNe : Real.exp 1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 1 ≤ Real.log (2*N) := by
    have hh := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 2*N by linarith)
    simpa using hh
  have hlo := choice_log_lower hK hK₀ hb hlog hA hbound
  have hpow := mul_le_mul_of_nonneg_left (hclog N hN1) (choice_pos (beta:=beta) hK₀).le
  have htheta : choice K₀ beta*(c*N^(-(1:ℝ)/2)) ≤ choice K beta := by
    simp only [← neg_div] at hpow
    exact hpow.trans hlo
  have hlarge := hN₁ N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hid : N*(2*(choice K₀ beta*(c*N^(-(1:ℝ)/2)))) =
      (2*choice K₀ beta*c)*N^((1:ℝ)/2) := by
    calc
      _ = (2*choice K₀ beta*c)*(N^(1:ℝ)*N^(-(1:ℝ)/2)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hNp]; norm_num
  have hmesh : 1/N ≤ 2*choice K beta := by
    apply (div_le_iff₀ hNp).mpr
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htheta (by norm_num : (0:ℝ)≤2)) hNp.le
    rw [hid] at hh
    nlinarith
  refine ⟨choice_pos hK,?_,hmesh,cap_budget hK hb,hlo⟩
  linarith [choice_le_hundredth K beta]

/-- Physical-mesh form, with the threshold chosen before delta and K. -/
theorem uniform_small_scales {K₀ beta A : ℝ} (hK₀ : 0 < K₀) (hb : 0 < beta) (hA : 0 ≤ A) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ K : ℝ, 0 < δ → δ ≤ δ₀ → 0 < K →
      K ≤ K₀*(Real.log (2/δ))^A →
      0 < choice K beta ∧ δ ≤ 2*choice K beta ∧ 2*choice K beta ≤ 1 ∧
      1000*K*(2*choice K beta)^beta ≤ 1 ∧
      choice K₀ beta*(Real.log (2/δ))^(-A/beta) ≤ choice K beta := by
  obtain ⟨N₀,hN₀,hcut⟩ := uniform_choice hK₀ hb hA
  have hN₀p : 0 < N₀ := zero_lt_one.trans_le hN₀
  refine ⟨1/N₀,by positivity,(div_le_one hN₀p).mpr hN₀,?_⟩
  intro δ K hδ hsmall hK hbound
  have hN : N₀ ≤ 1/δ := by
    have hh := one_div_le_one_div_of_le hδ hsmall
    simpa only [one_div_one_div] using hh
  obtain ⟨hp,hu,hl,hcap,hlog⟩ := hcut (1/δ) K hN hK (by simpa only [mul_one_div] using hbound)
  exact ⟨hp,by simpa only [one_div_one_div] using hl,hu,hcap,by simpa only [mul_one_div] using hlog⟩

end
end KakeyaFormal.SamplingTheta

#print axioms KakeyaFormal.SamplingTheta.cap_budget
#print axioms KakeyaFormal.SamplingTheta.uniform_small_scales
