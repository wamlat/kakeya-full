import SamplingApplication
import LogLoss

/-! Uniform scale thresholds for the actual coupled sampling construction.
Polynomially many tube/ball/high-cell tests are controlled internally; no
failure probability or simultaneous realization is assumed. -/
namespace KakeyaFormal.SamplingThreshold
open Finset Filter KakeyaSamplingApplication
open scoped Topology BigOperators
noncomputable section
universe uT uC uB uA

theorem stretched_exp_limit (u : ℝ) {c eta : ℝ} (hc : 0 < c) (heta : 0 < eta) :
    Tendsto (fun N : ℝ => N^u*Real.exp (-c*N^eta)) atTop (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (u/eta) c hc).comp
    (tendsto_rpow_atTop heta)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
  dsimp
  rw [← Real.rpow_mul hN.le]
  congr 2
  field_simp

theorem logarithmic_tail_bound {N a w : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a) :
    N^w*Real.exp (-a*Real.log (2*N)/8) ≤ N^(w-a/8) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hlog := Real.log_le_log hN0 (by linarith : N ≤ 2*N)
  have hexp : Real.exp (-a*Real.log (2*N)/8) ≤ Real.exp (Real.log N*(-a/8)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hh := mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hN0.le w)
  rw [← Real.rpow_def_of_pos hN0,← Real.rpow_add hN0] at hh
  simpa only [sub_eq_add_neg,neg_div] using hh

/-- The threshold depends only on the displayed fixed coefficients and powers.
It is selected before all scale, probability, and finite testing data. -/
theorem uniform_threshold {CT CB CH cf cb eta phi u v w a : ℝ}
    (hCH : 0 ≤ CH)
    (hcf : 0 < cf) (hcb : 0 < cb) (heta : 0 < eta) (hphi : 0 < phi)
    (ha : 0 ≤ a) (hmargin : w < a/8) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      2*CT*N^u*Real.exp (-(cf*N^eta)/12)+
      CB*N^v*Real.exp (-(cb*N^phi)/4)+
      CH*N^w*Real.exp (-a*Real.log (2*N)/8) < 1 := by
  have hfirst := (stretched_exp_limit u (show 0 < cf/12 by positivity) heta).const_mul (2*CT)
  have hsecond := (stretched_exp_limit v (show 0 < cb/4 by positivity) hphi).const_mul CB
  have hthird := (tendsto_rpow_neg_atTop (sub_pos.mpr hmargin)).const_mul CH
  have hall : Tendsto (fun N : ℝ =>
      (2*CT)*(N^u*Real.exp (-(cf/12)*N^eta))+
      CB*(N^v*Real.exp (-(cb/4)*N^phi))+CH*N^(-(a/8-w))) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using (hfirst.add hsecond).add hthird
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp
    (hall.eventually (gt_mem_nhds (show (0:ℝ) < 1 by norm_num)))
  refine ⟨max 1 N₁,le_max_left _ _,?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have htail := mul_le_mul_of_nonneg_left (logarithmic_tail_bound (w := w) hN1 ha) hCH
  have hbound := hN₁ N ((le_max_right _ _).trans hN)
  have hid : -(a/8-w) = w-a/8 := by ring
  rw [hid] at hbound
  have heq₁ : -(cf*N^eta)/12 = -(cf/12)*N^eta := by ring
  have heq₂ : -(cb*N^phi)/4 = -(cb/4)*N^phi := by ring
  rw [heq₁,heq₂]
  nlinarith

/-- Exact finite probability budget, obtained from actual counts and means. -/
theorem failure_budget_bound {T C B A : Type*}
    [Fintype T] [Fintype C] [Fintype B] [Fintype A] [DecidableEq C]
    (p q : T → C → ℝ) (high : Finset C) (cutoff : T → B → ℝ)
    {N CT CB CH cf cb eta phi u v w a : ℝ}
    (ht : (Fintype.card T:ℝ) ≤ CT*N^u)
    (hb : (Fintype.card T:ℝ)*(Fintype.card B:ℝ) ≤ CB*N^v)
    (hc : (high.card:ℝ)*(1+(Fintype.card A:ℝ)) ≤ CH*N^w)
    (hfull : ∀ t, cf*N^eta ≤ fullMean p t)
    (hball : ∀ t b, cb*N^phi ≤ cutoff t b)
    (hhigh : ∀ c ∈ high, a*Real.log (2*N) ≤ markedMean q c) :
    failureBudget (A := A) p q high cutoff ≤
      2*CT*N^u*Real.exp (-(cf*N^eta)/12)+
      CB*N^v*Real.exp (-(cb*N^phi)/4)+
      CH*N^w*Real.exp (-a*Real.log (2*N)/8) := by
  have hh := failureBudget_le_uniform (A := A) p q high cutoff hfull hball hhigh
  refine hh.trans ?_
  have hfirst := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 2))
    (Real.exp_pos (-(cf*N^eta)/12)).le
  have hsecond := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-(cb*N^phi)/4)).le
  have hthird := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-(a*Real.log (2*N))/8)).le
  simp only [neg_mul] at hthird ⊢
  nlinarith

/-- Uniform actual simultaneous sampling: the large-scale threshold precedes
even the finite index types. The finite expectation and count hypotheses are
the exact interfaces supplied by spatial tests and actual cap masks. -/
theorem uniform_sampling {CT CB CH cf cb eta phi u v w a : ℝ}
    (hCH : 0 ≤ CH) (hcf : 0 < cf) (hcb : 0 < cb)
    (heta : 0 < eta) (hphi : 0 < phi) (ha : 0 ≤ a) (hmargin : w < a/8) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (T : Type uT) (C : Type uC) (B : Type uB) (A : Type uA)
      [Fintype T] [Fintype C] [Fintype B] [Fintype A] [DecidableEq T] [DecidableEq C]
      (p q : T → C → ℝ) (high : Finset C) (ball : B → C → Bool)
      (cap : A → T → Bool) (cutoff : T → B → ℝ),
      (∀ t c, 0 ≤ q t c) → (∀ t c, q t c ≤ p t c) → (∀ t c, p t c ≤ 1) →
      (Fintype.card T:ℝ) ≤ CT*N^u →
      (Fintype.card T:ℝ)*(Fintype.card B:ℝ) ≤ CB*N^v →
      (high.card:ℝ)*(1+(Fintype.card A:ℝ)) ≤ CH*N^w →
      (∀ t, cf*N^eta ≤ fullMean p t) →
      (∀ t b, cb*N^phi ≤ cutoff t b) →
      (∀ c ∈ high, a*Real.log (2*N) ≤ markedMean q c) →
      (∀ t b, 4*ballMean p ball t b ≤ cutoff t b) →
      (∀ c ∈ high, ∀ a, 1000*capMean q cap c a ≤ markedMean q c) →
      (∑ c, markedMean q c)/2 ≤ ∑ c ∈ high, markedMean q c →
      ∃ ω : Outcome T C, SampleGood p q high ball cap cutoff ω := by
  obtain ⟨N₀,hN₀,hsmall⟩ := uniform_threshold
    (CT := CT) (CB := CB) (u := u) (v := v) hCH hcf hcb heta hphi ha hmargin
  refine ⟨N₀,hN₀,?_⟩
  intro N hN T C B A _ _ _ _ _ _ p q high ball cap cutoff hq hqp hp ht hb hc hfull hball hhigh
    hballMean hcapMean hmass
  apply finite_sampling_assembly p q hq hqp hp high ball cap cutoff hballMean hcapMean hmass
  exact (failure_budget_bound p q high cutoff ht hb hc hfull hball hhigh).trans_lt (hsmall N hN)

theorem depth_log_bound {N : ℝ} (hN : 1 ≤ N) :
    Real.log N/Real.log 2+1 ≤ (1/Real.log 2+1)*N := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
  have hh := div_le_div_of_nonneg_right hlog hlog2.le
  calc
    _ ≤ N/Real.log 2+1 := by linarith
    _ ≤ N/Real.log 2+N := by linarith
    _ = _ := by ring

/-- The actual n-dimensional cell, tube, and ball counts give the aggregate
polynomial test counts, when all original directions are used as cap labels. -/
theorem source_counts (n : ℕ) {N CT CB CE tubes balls cells caps : ℝ}
    (hN : 1 ≤ N) (hCT : 0 ≤ CT) (hCB : 0 ≤ CB) (hCE : 0 ≤ CE)
    (hb0 : 0 ≤ balls) (ha0 : 0 ≤ caps)
    (ht : tubes ≤ CT*N^((n:ℝ)-1))
    (hb : balls ≤ CB*N^(n:ℝ)*(Real.log N/Real.log 2+1))
    (hc : cells ≤ CE*N^(n:ℝ)) (hcap : caps ≤ tubes) :
    tubes*balls ≤ (CT*CB*(1/Real.log 2+1))*N^(2*(n:ℝ)) ∧
      cells*(1+caps) ≤ (CE*(1+CT))*N^(2*(n:ℝ)) := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hbb : balls ≤ CB*N^(n:ℝ)*((1/Real.log 2+1)*N) :=
    hb.trans (mul_le_mul_of_nonneg_left (depth_log_bound hN) (by positivity))
  have hmul := mul_le_mul ht hbb hb0 (by positivity : 0 ≤ CT*N^((n:ℝ)-1))
  have hpowers : N^((n:ℝ)-1)*N^(n:ℝ)*N = N^(2*(n:ℝ)) := by
    rw [← Real.rpow_add hN0,← Real.rpow_add_one hN0.ne']
    congr 1
    ring
  constructor
  · calc
      tubes*balls ≤ (CT*N^((n:ℝ)-1))*(CB*N^(n:ℝ)*((1/Real.log 2+1)*N)) := hmul
      _ = (CT*CB*(1/Real.log 2+1))*(N^((n:ℝ)-1)*N^(n:ℝ)*N) := by ring
      _ = _ := by rw [hpowers]
  · have hpow : N^((n:ℝ)-1) ≤ N^(n:ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    have ht' : tubes ≤ CT*N^(n:ℝ) := ht.trans (mul_le_mul_of_nonneg_left hpow hCT)
    have hone : (1:ℝ) ≤ N^(n:ℝ) := Real.one_le_rpow hN (Nat.cast_nonneg _)
    have hcap' : 1+caps ≤ (1+CT)*N^(n:ℝ) := by nlinarith
    have hboth := mul_le_mul hc hcap' (by linarith : 0 ≤ 1+caps) (by positivity : 0 ≤ CE*N^(n:ℝ))
    calc
      _ ≤ (CE*N^(n:ℝ))*((1+CT)*N^(n:ℝ)) := hboth
      _ = (CE*(1+CT))*(N^(n:ℝ)*N^(n:ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hN0]; congr 2; ring

/-- The source density cutoff and alpha<=1/4 give the actual mean powers
2/3 and 5/12. No sub-mesh two-ends hypothesis enters this calculation. -/
theorem source_mean_powers {N lam B r alpha : ℝ}
    (hN : 1 ≤ N) (hlam : N^(-(1:ℝ)/3) ≤ lam)
    (hB : 1 ≤ B) (hr : 1/N ≤ r) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1/4) :
    N^(2/3:ℝ) ≤ lam*N ∧ N^(5/12:ℝ) ≤ B*r^alpha*lam*N := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hlam0 : 0 < lam := (Real.rpow_pos_of_pos hN0 _).trans_le hlam
  have hr0 : 0 < r := (one_div_pos.mpr hN0).trans_le hr
  have hfull : N^(2/3:ℝ) ≤ lam*N := by
    have hh := mul_le_mul_of_nonneg_right hlam hN0.le
    rw [← Real.rpow_add_one hN0.ne'] at hh
    norm_num at hh
    exact hh
  have hrpow : N^(-(1:ℝ)/4) ≤ r^alpha := by
    have hp := Real.rpow_le_rpow (le_of_lt (one_div_pos.mpr hN0)) hr ha
    have hinv : (1/N)^alpha = N^(-alpha) := by
      rw [one_div,Real.inv_rpow hN0.le,Real.rpow_neg hN0.le]
    rw [hinv] at hp
    exact (Real.rpow_le_rpow_of_exponent_le hN (by linarith : -(1:ℝ)/4 ≤ -alpha)).trans hp
  have hmul := mul_le_mul hrpow hfull (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hr0.le alpha)
  have hid : N^(-(1:ℝ)/4)*N^(2/3:ℝ)=N^(5/12:ℝ) := by
    rw [← Real.rpow_add hN0]
    norm_num
  rw [hid] at hmul
  refine ⟨hfull,hmul.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right hB (by positivity : 0 ≤ r^alpha*lam*N)
  nlinarith

/-- Concrete Section 6 scale theorem with actual ambient-dimension counts.
All original directions may serve as cap labels. The dimensional high-cell
threshold 64(n+4)log(2N) controls that larger polynomial testing family. -/
theorem source_sampling (n : ℕ) {CT CB CE cf cb : ℝ}
    (hCT : 0 ≤ CT) (hCB : 0 ≤ CB) (hCE : 0 ≤ CE) (hcf : 0 < cf) (hcb : 0 < cb) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (T : Type uT) (C : Type uC) (Balls : Type uB) (Caps : Type uA)
      [Fintype T] [Fintype C] [Fintype Balls] [Fintype Caps] [DecidableEq T] [DecidableEq C]
      (p q : T → C → ℝ) (high : Finset C) (ball : Balls → C → Bool)
      (cap : Caps → T → Bool) (cutoff : T → Balls → ℝ) (r : Balls → ℝ)
      (lam B alpha : ℝ),
      (∀ t c, 0 ≤ q t c) → (∀ t c, q t c ≤ p t c) → (∀ t c, p t c ≤ 1) →
      (Fintype.card T:ℝ) ≤ CT*N^((n:ℝ)-1) →
      (Fintype.card Balls:ℝ) ≤ CB*N^(n:ℝ)*(Real.log N/Real.log 2+1) →
      (high.card:ℝ) ≤ CE*N^(n:ℝ) → Fintype.card Caps ≤ Fintype.card T →
      N^(-(1:ℝ)/3) ≤ lam → 1 ≤ B → 0 ≤ alpha → alpha ≤ 1/4 →
      (∀ b, 1/N ≤ r b) →
      (∀ t, cf*lam*N ≤ fullMean p t) →
      (∀ t b, cb*B*(r b)^alpha*lam*N ≤ cutoff t b) →
      (∀ c ∈ high, (64*((n:ℝ)+4))*Real.log (2*N) ≤ markedMean q c) →
      (∀ t b, 4*ballMean p ball t b ≤ cutoff t b) →
      (∀ c ∈ high, ∀ a, 1000*capMean q cap c a ≤ markedMean q c) →
      (∑ c, markedMean q c)/2 ≤ ∑ c ∈ high, markedMean q c →
      ∃ ω : Outcome T C, SampleGood p q high ball cap cutoff ω := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  obtain ⟨N₀,hN₀,hsample⟩ := uniform_sampling
    (CT := CT) (CB := CT*CB*(1/Real.log 2+1)) (CH := CE*(1+CT))
    (cf := cf) (cb := cb) (eta := 2/3) (phi := 5/12)
    (u := (n:ℝ)-1) (v := 2*(n:ℝ)) (w := 2*(n:ℝ)) (a := 64*((n:ℝ)+4))
    (by positivity) hcf hcb (by norm_num) (by norm_num) (by positivity)
    (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _; linarith)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN T C Balls Caps _ _ _ _ _ _ p q high ball cap cutoff r lam B alpha
    hq hqp hp ht hb hc hcap hlam hB ha ha1 hr hfull hball hhigh hballMean hcapMean hmass
  have hN1 : 1 ≤ N := hN₀.trans hN
  have hcounts := source_counts n hN1 hCT hCB hCE (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ht hb hc (by exact_mod_cast hcap)
  have hfullPower : N^(2/3:ℝ) ≤ lam*N :=
    (source_mean_powers (B := 1) (r := 1/N) (alpha := 0)
      hN1 hlam le_rfl le_rfl le_rfl (by norm_num)).1
  have hfullMean : ∀ t, cf*N^(2/3:ℝ) ≤ fullMean p t := by
    intro t
    have hh := mul_le_mul_of_nonneg_left hfullPower hcf.le
    have hle : cf*N^(2/3:ℝ) ≤ cf*lam*N := by simpa only [mul_assoc] using hh
    exact hle.trans (hfull t)
  have hballCutoff : ∀ t b, cb*N^(5/12:ℝ) ≤ cutoff t b := by
    intro t b
    have hh := mul_le_mul_of_nonneg_left
      (source_mean_powers hN1 hlam hB (hr b) ha ha1).2 hcb.le
    have hle : cb*N^(5/12:ℝ) ≤ cb*B*(r b)^alpha*lam*N := by simpa only [mul_assoc] using hh
    exact hle.trans (hball t b)
  exact hsample N hN T C Balls Caps p q high ball cap cutoff
    hq hqp hp ht hcounts.1 hcounts.2 hfullMean hballCutoff hhigh hballMean hcapMean hmass

end
end KakeyaFormal.SamplingThreshold
