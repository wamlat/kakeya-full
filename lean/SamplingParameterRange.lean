import SamplingExactDensity

/-! Full positive-gap parameter range of the Section6 sampling argument.
The exponents are1−s and1−s−alpha, fixed before scale and finite data. -/
namespace KakeyaFormal.SamplingParameterRange
open Finset KakeyaSamplingApplication
open scoped BigOperators
noncomputable section
universe uT uC uB uA

/-- The full mean grows at its exact fixed power, not a specialized exponent. -/
theorem full_mean_power {N lam s : ℝ} (hN : 1 ≤ N) (hlam : N^(-s) ≤ lam) :
    N^(1-s) ≤ lam*N := by
  have hN0 : 0<N := zero_lt_one.trans_le hN
  have hh := mul_le_mul_of_nonneg_right hlam hN0.le
  rw [← Real.rpow_add_one hN0.ne'] at hh
  have he : -s + 1 = 1-s := by ring
  simpa only [he] using hh

/-- No sub-mesh two-ends hypothesis enters the positive-gap calculation. -/
theorem source_mean_powers {N lam B r s alpha : ℝ}
    (hN : 1 ≤ N) (hlam : N^(-s) ≤ lam)
    (hB : 1 ≤ B) (hr : 1/N ≤ r) (ha : 0 ≤ alpha) :
    N^(1-s) ≤ lam*N ∧ N^(1-s-alpha) ≤ B*r^alpha*lam*N := by
  have hN0 : 0<N := zero_lt_one.trans_le hN
  have hlam0 : 0<lam := (Real.rpow_pos_of_pos hN0 _).trans_le hlam
  have hr0 : 0<r := (one_div_pos.mpr hN0).trans_le hr
  have hfull := full_mean_power hN hlam
  have hrpow : N^(-alpha) ≤ r^alpha := by
    have hp := Real.rpow_le_rpow (le_of_lt (one_div_pos.mpr hN0)) hr ha
    have hi : (1/N)^alpha = N^(-alpha) := by
      rw [one_div,Real.inv_rpow hN0.le,Real.rpow_neg hN0.le]
    rwa [hi] at hp
  have hmul := mul_le_mul hrpow hfull (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hr0.le alpha)
  have hid : N^(-alpha)*N^(1-s) = N^(1-s-alpha) := by
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  rw [hid] at hmul
  refine ⟨hfull,hmul.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_right hB (by positivity : 0≤r^alpha*lam*N)
  nlinarith

/-- The complete sharp union budget tends uniformly below one for every
fixed positive gap. The full-row concentration uses its honest rate 1/100. -/
theorem uniform_source_budget (n : ℕ) {s alpha CT CB CE cf cb : ℝ}
    (hs1 : s < 1) (hgap : alpha < 1-s)
    (hCT : 0 ≤ CT) (hCE : 0 ≤ CE) (hcf : 0 < cf) (hcb : 0 < cb) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      2*CT*N^((n:ℝ)-1)*Real.exp (-(cf*N^(1-s))/100)+
      (CT*CB*(1/Real.log 2+1))*N^(2*(n:ℝ))*Real.exp (-(cb*N^(1-s-alpha))/4)+
      (CE*(1+CT))*N^(2*(n:ℝ))*Real.exp (-(64*((n:ℝ)+4))*Real.log (2*N)/8) < 1 := by
  obtain ⟨N₀,hN₀,hsmall⟩ := SamplingThreshold.uniform_threshold
    (CT := CT) (CB := CT*CB*(1/Real.log 2+1)) (CH := CE*(1+CT))
    (cf := (3/25)*cf) (cb := cb) (eta := 1-s) (phi := 1-s-alpha)
    (u := (n:ℝ)-1) (v := 2*(n:ℝ)) (w := 2*(n:ℝ)) (a := 64*((n:ℝ)+4))
    (by positivity) (by positivity) hcb (by linarith) (by linarith) (by positivity)
    (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _; linarith)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN
  have he : -((3/25)*cf*N^(1-s))/12 = -(cf*N^(1-s))/100 := by ring
  simpa only [he] using hsmall N hN

/-- Actual simultaneous sampling over the complete fixed positive-gap range.
The original nested arrays p,q are used throughout, without row rescaling. -/
theorem source_sampling_narrow (n : ℕ) (s alpha : ℝ)
    (_hs : 0 < s) (hs1 : s < 1) (ha : 0 ≤ alpha) (hgap : alpha < 1-s)
    {CT CB CE cf cb : ℝ}
    (hCT : 0 ≤ CT) (hCB : 0 ≤ CB) (hCE : 0 ≤ CE) (hcf : 0 < cf) (hcb : 0 < cb) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (T : Type uT) (C : Type uC) (Balls : Type uB) (Caps : Type uA)
      [Fintype T] [Fintype C] [Fintype Balls] [Fintype Caps] [DecidableEq T] [DecidableEq C]
      (p q : T → C → ℝ) (high : Finset C) (ball : Balls → C → Bool)
      (cap : Caps → T → Bool) (cutoff : T → Balls → ℝ) (r : Balls → ℝ)
      (lam B : ℝ),
      (∀ t c, 0 ≤ q t c) → (∀ t c, q t c ≤ p t c) → (∀ t c, p t c ≤ 1) →
      (Fintype.card T:ℝ) ≤ CT*N^((n:ℝ)-1) →
      (Fintype.card Balls:ℝ) ≤ CB*N^(n:ℝ)*(Real.log N/Real.log 2+1) →
      (high.card:ℝ) ≤ CE*N^(n:ℝ) → Fintype.card Caps ≤ Fintype.card T →
      N^(-s) ≤ lam → 1 ≤ B →
      (∀ b, 1/N ≤ r b) →
      (∀ t, cf*lam*N ≤ fullMean p t) →
      (∀ t b, cb*B*(r b)^alpha*lam*N ≤ cutoff t b) →
      (∀ c ∈ high, (64*((n:ℝ)+4))*Real.log (2*N) ≤ markedMean q c) →
      (∀ t b, 4*ballMean p ball t b ≤ cutoff t b) →
      (∀ c ∈ high, ∀ a, 1000*capMean q cap c a ≤ markedMean q c) →
      (∑ c, markedMean q c)/2 ≤ ∑ c ∈ high, markedMean q c →
      ∃ ω : Outcome T C, SampleGood p q high ball cap cutoff ω ∧
        ∀ t, (2/3:ℝ)*fullMean p t ≤ (fullShading ω t).card ∧
          ((fullShading ω t).card:ℝ) ≤ (4/3:ℝ)*fullMean p t := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  obtain ⟨N₀,hN₀,hsample⟩ := SamplingExactDensity.uniform_sampling_narrow
    (CT := CT) (CB := CT*CB*(1/Real.log 2+1)) (CH := CE*(1+CT))
    (cf := cf) (cb := cb) (eta := 1-s) (phi := 1-s-alpha)
    (u := (n:ℝ)-1) (v := 2*(n:ℝ)) (w := 2*(n:ℝ)) (a := 64*((n:ℝ)+4))
    (by positivity) hcf hcb (by linarith) (by linarith) (by positivity)
    (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _; linarith)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN T C Balls Caps _ _ _ _ _ _ p q high ball cap cutoff r lam B
    hq hqp hp ht hb hc hcap hlam hB hr hfull hball hhigh hballMean hcapMean hmass
  have hN1 : 1 ≤ N := hN₀.trans hN
  have hcounts := SamplingThreshold.source_counts n hN1 hCT hCB hCE (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ht hb hc (by exact_mod_cast hcap)
  have hfullPower : N^(1-s) ≤ lam*N := full_mean_power hN1 hlam
  have hfullMean : ∀ t, cf*N^(1-s) ≤ fullMean p t := by
    intro t
    have hh := mul_le_mul_of_nonneg_left hfullPower hcf.le
    have hle : cf*N^(1-s) ≤ cf*lam*N := by simpa only [mul_assoc] using hh
    exact hle.trans (hfull t)
  have hballCutoff : ∀ t b, cb*N^(1-s-alpha) ≤ cutoff t b := by
    intro t b
    have hh := mul_le_mul_of_nonneg_left
      (source_mean_powers hN1 hlam hB (hr b) ha).2 hcb.le
    have hle : cb*N^(1-s-alpha) ≤ cb*B*(r b)^alpha*lam*N := by simpa only [mul_assoc] using hh
    exact hle.trans (hball t b)
  exact hsample N hN T C Balls Caps p q high ball cap cutoff
    hq hqp hp ht hcounts.1 hcounts.2 hfullMean hballCutoff hhigh hballMean hcapMean hmass

end
end KakeyaFormal.SamplingParameterRange
