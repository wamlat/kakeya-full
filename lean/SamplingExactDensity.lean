import SamplingApplication
import SamplingThreshold

/-! Sharper full-density concentration in the same coupled sampling model.
The resulting density interval has ratio two. Marks, angular fractions and
all other SampleGood conclusions are retained on the same outcome. -/
namespace KakeyaFormal.SamplingExactDensity
open Finset KakeyaSampling KakeyaSamplingApplication
open scoped BigOperators
noncomputable section
universe uT uC uB uA

theorem log_four_thirds_bounds :
    (27/100:ℝ) ≤ Real.log (4/3:ℝ) ∧ Real.log (4/3:ℝ) ≤ 3/10 := by
  rw [Real.log_div (by norm_num : (4:ℝ) ≠ 0) (by norm_num : (3:ℝ) ≠ 0),Real.log_four_eq]
  constructor <;> linarith [Real.log_two_gt_d9,Real.log_two_lt_d9,Real.log_three_gt_d9,Real.log_three_lt_d9]

/-- A proved multiplicative Chernoff band with ratio exactly two. The fixed
exponent 1/100 is conservative and independent of the individual probabilities. -/
theorem poisson_binomial_narrow {Ω : Type*} [Fintype Ω]
    (D : FiniteLaw Ω) (X : Ω → ℝ) {mu : ℝ} (hmu : 0 ≤ mu)
    (hmgf : ∀ t : ℝ, D.expectation (fun ω => Real.exp (t*X ω)) ≤
      Real.exp (mu*(Real.exp t-1))) :
    D.probability (fun ω => X ω ≤ (2/3:ℝ)*mu ∨ (4/3:ℝ)*mu ≤ X ω) ≤
      2*Real.exp (-mu/100) := by
  have hlog0 : 0 ≤ Real.log (4/3:ℝ) := Real.log_nonneg (by norm_num)
  have he : Real.exp (Real.log (4/3:ℝ)) = 4/3 := Real.exp_log (by norm_num)
  have hinv : Real.exp (-Real.log (4/3:ℝ)) = 3/4 := by rw [Real.exp_neg,he]; norm_num
  have hu := chernoff_upper D X (u := (4/3:ℝ)*mu) hlog0 (hmgf (Real.log (4/3:ℝ)))
  have hl := chernoff_lower D X (u := (2/3:ℝ)*mu) (neg_nonpos.mpr hlog0) (hmgf (-Real.log (4/3:ℝ)))
  rw [he] at hu
  rw [hinv] at hl
  have hupper : mu*((4/3:ℝ)-1)-Real.log (4/3:ℝ)*((4/3:ℝ)*mu) ≤ -mu/100 := by
    have hh := mul_le_mul_of_nonneg_right log_four_thirds_bounds.1 hmu
    nlinarith
  have hlower : mu*((3/4:ℝ)-1)-(-Real.log (4/3:ℝ))*((2/3:ℝ)*mu) ≤ -mu/100 := by
    have hh := mul_le_mul_of_nonneg_right log_four_thirds_bounds.2 hmu
    nlinarith
  have hu' := hu.trans (Real.exp_le_exp.mpr hupper)
  have hl' := hl.trans (Real.exp_le_exp.mpr hlower)
  have hsum := D.probability_union (fun ω => X ω ≤ (2/3:ℝ)*mu) (fun ω => (4/3:ℝ)*mu ≤ X ω)
  linarith

theorem coupled_test_narrow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hqp : ∀ i, q i ≤ p i) (hp : ∀ i, p i ≤ 1)
    (active : ι → Bool) (mark : Bool) :
    (coupledLaw p q hq hqp hp).probability (fun ω =>
      testCount active mark ω ≤ (2/3:ℝ)*testMean p q active mark ∨
      (4/3:ℝ)*testMean p q active mark ≤ testCount active mark ω) ≤
      2*Real.exp (-testMean p q active mark/100) :=
  poisson_binomial_narrow _ _ (test_mean_nonneg p q hq hqp active mark)
    (coupled_test_mgf_bound p q hq hqp hp active mark)

def sharpBudget {T C B A : Type*} [Fintype T] [Fintype C] [Fintype B] [Fintype A]
    (p q : T → C → ℝ) (high : Finset C) (cutoff : T → B → ℝ) : ℝ :=
    (∑ t, 2*Real.exp (-fullMean p t/100))+
    (∑ t, ∑ b, Real.exp (-cutoff t b/4))+
    (∑ c ∈ high, Real.exp (-markedMean q c/8))+
    (∑ c ∈ high, ∑ _a : A, Real.exp (-markedMean q c/8))

/-- This is an arithmetic identity for the rate budget only. The actual law
always uses the original nested p,q, not the auxiliary rescaled full array. -/
theorem sharpBudget_eq_rescaled {T C B A : Type*}
    [Fintype T] [Fintype C] [Fintype B] [Fintype A]
    (p q : T → C → ℝ) (high : Finset C) (cutoff : T → B → ℝ) :
    sharpBudget (A := A) p q high cutoff =
      failureBudget (A := A) (fun t c => (3/25:ℝ)*p t c) q high cutoff := by
  have hmean (t : T) : fullMean (fun t c => (3/25:ℝ)*p t c) t = (3/25:ℝ)*fullMean p t := by
    unfold fullMean
    rw [mul_sum]
  unfold sharpBudget failureBudget
  simp_rw [hmean]
  congr 3
  apply sum_congr rfl
  intro t _
  congr 2
  ring

theorem sharp_budget_bound {T C B A : Type*}
    [Fintype T] [Fintype C] [Fintype B] [Fintype A] [DecidableEq C]
    (p q : T → C → ℝ) (high : Finset C) (cutoff : T → B → ℝ)
    {N CT CB CH cf cb eta phi u v w a : ℝ}
    (ht : (Fintype.card T:ℝ) ≤ CT*N^u)
    (hb : (Fintype.card T:ℝ)*(Fintype.card B:ℝ) ≤ CB*N^v)
    (hc : (high.card:ℝ)*(1+(Fintype.card A:ℝ)) ≤ CH*N^w)
    (hfull : ∀ t, cf*N^eta ≤ fullMean p t)
    (hball : ∀ t b, cb*N^phi ≤ cutoff t b)
    (hhigh : ∀ c ∈ high, a*Real.log (2*N) ≤ markedMean q c) :
    sharpBudget (A := A) p q high cutoff ≤
      2*CT*N^u*Real.exp (-(((3/25:ℝ)*cf)*N^eta)/12)+
      CB*N^v*Real.exp (-(cb*N^phi)/4)+
      CH*N^w*Real.exp (-a*Real.log (2*N)/8) := by
  rw [sharpBudget_eq_rescaled]
  apply SamplingThreshold.failure_budget_bound _ q high cutoff ht hb hc ?_ hball hhigh
  intro t
  have hh := mul_le_mul_of_nonneg_left (hfull t) (by norm_num : (0:ℝ) ≤ 3/25)
  unfold fullMean
  rw [← mul_sum]
  simpa only [mul_assoc,fullMean] using hh

/-- Actual coupled sampling with the sharper full band and all original
SampleGood fields on the same positive-support outcome. -/
theorem finite_sampling_narrow {T C B A : Type*}
    [Fintype T] [Fintype C] [Fintype B] [Fintype A]
    [DecidableEq T] [DecidableEq C] (p q : T → C → ℝ)
    (hq : ∀ t c, 0 ≤ q t c) (hqp : ∀ t c, q t c ≤ p t c) (hp : ∀ t c, p t c ≤ 1)
    (high : Finset C) (ball : B → C → Bool) (cap : A → T → Bool) (cutoff : T → B → ℝ)
    (hball : ∀ t b, 4 * ballMean p ball t b ≤ cutoff t b)
    (hcap : ∀ c ∈ high, ∀ a, 1000 * capMean q cap c a ≤ markedMean q c)
    (hhigh : (∑ c, markedMean q c) / 2 ≤ ∑ c ∈ high, markedMean q c)
    (hbudget : sharpBudget (A := A) p q high cutoff < 1) :
    ∃ ω : Outcome T C, SampleGood p q high ball cap cutoff ω ∧
      ∀ t, (2/3:ℝ)*fullMean p t ≤ (fullShading ω t).card ∧
        ((fullShading ω t).card:ℝ) ≤ (4/3:ℝ)*fullMean p t := by
  classical
  let D := coupledLaw (flatten p) (flatten q)
    (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2)
  let J := T ⊕ ((T × B) ⊕ (↥high ⊕ (↥high × A)))
  let bad : J → Outcome T C → Prop := fun j ω => match j with
    | Sum.inl t => fullTubeCount ω t ≤ (2/3:ℝ)*fullMean p t ∨ (4/3:ℝ)*fullMean p t ≤ fullTubeCount ω t
    | Sum.inr (Sum.inl tb) => cutoff tb.1 tb.2 ≤ fullBallCount ω ball tb.1 tb.2
    | Sum.inr (Sum.inr (Sum.inl c)) => markedCellCount ω c.val ≤ markedMean q c.val / 2
    | Sum.inr (Sum.inr (Sum.inr ca)) => markedMean q ca.1.val / 20 ≤ markedCapCount ω cap ca.1.val ca.2
  let rate : J → ℝ := fun j => match j with
    | Sum.inl t => 2 * Real.exp (-fullMean p t / 100)
    | Sum.inr (Sum.inl tb) => Real.exp (-cutoff tb.1 tb.2 / 4)
    | Sum.inr (Sum.inr (Sum.inl c)) => Real.exp (-markedMean q c.val / 8)
    | Sum.inr (Sum.inr (Sum.inr ca)) => Real.exp (-markedMean q ca.1.val / 8)
  have hbound : ∀ j, D.probability (bad j) ≤ rate j := by
    intro j
    rcases j with t | j
    · simpa [D, bad, rate] using coupled_test_narrow (flatten p) (flatten q)
        (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2)
        (tubeMask t) false
    rcases j with tb | j
    · have hexpected : 4 * testMean (flatten p) (flatten q) (ballMask ball tb.1 tb.2) false ≤
          cutoff tb.1 tb.2 := by simpa using hball tb.1 tb.2
      simpa [D, bad, rate] using coupled_test_large_upper (flatten p) (flatten q)
        (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2)
        (ballMask ball tb.1 tb.2) false hexpected
    rcases j with c | ca
    · simpa [D, bad, rate] using coupled_test_half_lower (flatten p) (flatten q)
        (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2)
        (cellMask c.val) true
    · have hexpected : 1000 * testMean (flatten p) (flatten q) (capMask cap ca.1.val ca.2) true ≤
          markedMean q ca.1.val := by simpa using hcap ca.1.val ca.1.property ca.2
      simpa [D, bad, rate] using coupled_test_tiny_mean_upper (flatten p) (flatten q)
        (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2)
        (capMask cap ca.1.val ca.2) true hexpected
  have hrates : (∑ j, rate j) = sharpBudget (A := A) p q high cutoff := by
    simp only [rate, J, Fintype.sum_sum_type, Fintype.sum_prod_type, sharpBudget]
    rw [← sum_subtype high (fun _ => Iff.rfl) (fun c : C => Real.exp (-markedMean q c / 8)),
      ← sum_subtype high (fun _ => Iff.rfl) (fun c : C => ∑ _a : A, Real.exp (-markedMean q c / 8))]
    ring
  have hprobs : (∑ j, D.probability (bad j)) < 1 := by
    calc
      (∑ j, D.probability (bad j)) ≤ ∑ j, rate j := sum_le_sum (fun j _ => hbound j)
      _ < 1 := by rwa [hrates]
  obtain ⟨ω, hpositive, hω⟩ := D.exists_positive_avoiding_of_probability_sum_lt_one bad hprobs
  have hnarrow (t : T) : (2/3:ℝ)*fullMean p t < fullTubeCount ω t ∧
      fullTubeCount ω t < (4/3:ℝ)*fullMean p t := by
    simpa [bad, not_or, not_le] using hω (Sum.inl t)
  have hdensity (t : T) : fullMean p t / 2 < fullTubeCount ω t ∧
      fullTubeCount ω t < 2 * fullMean p t := by
    have hm : 0 ≤ fullMean p t := sum_nonneg (fun c _ => (hq t c).trans (hqp t c))
    constructor <;> linarith [(hnarrow t).1,(hnarrow t).2]
  have hballs (t : T) (b : B) : fullBallCount ω ball t b < cutoff t b := by
    simpa [bad, not_le] using hω (Sum.inr (Sum.inl (t,b)))
  have hcells (c : C) (hc : c ∈ high) : markedMean q c / 2 < markedCellCount ω c := by
    simpa [bad, not_le] using hω (Sum.inr (Sum.inr (Sum.inl ⟨c,hc⟩)))
  have hcaps (c : C) (hc : c ∈ high) (a : A) : markedCapCount ω cap c a < markedMean q c / 20 := by
    simpa [bad, not_le] using hω (Sum.inr (Sum.inr (Sum.inr (⟨c,hc⟩,a))))
  have hsupport := coupled_positive_support (flatten p) (flatten q)
    (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2) ω hpositive
  refine ⟨ω, ?_, ?_⟩
  rotate_left
  · intro t
    rw [← fullTubeCount_eq_card]
    exact ⟨(hnarrow t).1.le,(hnarrow t).2.le⟩
  constructor
  · intro t
    rw [← fullTubeCount_eq_card]
    exact ⟨(hdensity t).1.le, (hdensity t).2.le⟩
  · intro t b
    exact (hballs t b).le
  · intro c hc
    exact (hcells c hc).le
  · intro c hc a
    have hl := hcells c hc
    have hu := hcaps c hc a
    linarith
  · rw [marked_total_identity]
    have hs : (∑ c ∈ high, markedMean q c) / 2 ≤ ∑ c ∈ high, markedCellCount ω c := by
      rw [sum_div]
      exact sum_le_sum (fun c hc => (hcells c hc).le)
    linarith
  · simp_rw [← fullTubeCount_eq_card]
    rw [mul_sum]
    exact sum_le_sum (fun t _ => (hdensity t).2.le)
  · exact markedShading_subset high ω
  · intro t c hc
    have hval : (ω (t,c)).val ≠ 0 := (mem_filter.mp hc).2
    exact (hsupport (t,c)).1 (by simp [fullBit, hval])
  · intro t c hc
    have hval : (ω (t,c)).val = 2 := (mem_filter.mp hc).2.2
    exact (hsupport (t,c)).2 (by simp [markedBit, hval])


/-- Uniform threshold for the sharp outcome, before all finite index data. -/
theorem uniform_sampling_narrow {CT CB CH cf cb eta phi u v w a : ℝ}
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
      ∃ ω : Outcome T C, SampleGood p q high ball cap cutoff ω ∧
        ∀ t, (2/3:ℝ)*fullMean p t ≤ (fullShading ω t).card ∧
          ((fullShading ω t).card:ℝ) ≤ (4/3:ℝ)*fullMean p t := by
  obtain ⟨N₀,hN₀,hsmall⟩ := SamplingThreshold.uniform_threshold
    (CT := CT) (CB := CB) (u := u) (v := v) hCH
      (show 0 < (3/25:ℝ)*cf by positivity) hcb heta hphi ha hmargin
  refine ⟨N₀,hN₀,?_⟩
  intro N hN T C B A _ _ _ _ _ _ p q high ball cap cutoff hq hqp hp ht hb hc hfull hball hhigh
    hballMean hcapMean hmass
  apply finite_sampling_narrow p q hq hqp hp high ball cap cutoff hballMean hcapMean hmass
  exact (sharp_budget_bound p q high cutoff ht hb hc hfull hball hhigh).trans_lt (hsmall N hN)


/-- Actual ambient-count and source-density specialization with no probability-budget premise. -/
theorem source_sampling_narrow (n : ℕ) {CT CB CE cf cb : ℝ}
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
      ∃ ω : Outcome T C, SampleGood p q high ball cap cutoff ω ∧
        ∀ t, (2/3:ℝ)*fullMean p t ≤ (fullShading ω t).card ∧
          ((fullShading ω t).card:ℝ) ≤ (4/3:ℝ)*fullMean p t := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  obtain ⟨N₀,hN₀,hsample⟩ := uniform_sampling_narrow
    (CT := CT) (CB := CT*CB*(1/Real.log 2+1)) (CH := CE*(1+CT))
    (cf := cf) (cb := cb) (eta := 2/3) (phi := 5/12)
    (u := (n:ℝ)-1) (v := 2*(n:ℝ)) (w := 2*(n:ℝ)) (a := 64*((n:ℝ)+4))
    (by positivity) hcf hcb (by norm_num) (by norm_num) (by positivity)
    (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _; linarith)
  refine ⟨N₀,hN₀,?_⟩
  intro N hN T C Balls Caps _ _ _ _ _ _ p q high ball cap cutoff r lam B alpha
    hq hqp hp ht hb hc hcap hlam hB ha ha1 hr hfull hball hhigh hballMean hcapMean hmass
  have hN1 : 1 ≤ N := hN₀.trans hN
  have hcounts := SamplingThreshold.source_counts n hN1 hCT hCB hCE (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ht hb hc (by exact_mod_cast hcap)
  have hfullPower : N^(2/3:ℝ) ≤ lam*N :=
    (SamplingThreshold.source_mean_powers (B := 1) (r := 1/N) (alpha := 0)
      hN1 hlam le_rfl le_rfl le_rfl (by norm_num)).1
  have hfullMean : ∀ t, cf*N^(2/3:ℝ) ≤ fullMean p t := by
    intro t
    have hh := mul_le_mul_of_nonneg_left hfullPower hcf.le
    have hle : cf*N^(2/3:ℝ) ≤ cf*lam*N := by simpa only [mul_assoc] using hh
    exact hle.trans (hfull t)
  have hballCutoff : ∀ t b, cb*N^(5/12:ℝ) ≤ cutoff t b := by
    intro t b
    have hh := mul_le_mul_of_nonneg_left
      (SamplingThreshold.source_mean_powers hN1 hlam hB (hr b) ha ha1).2 hcb.le
    have hle : cb*N^(5/12:ℝ) ≤ cb*B*(r b)^alpha*lam*N := by simpa only [mul_assoc] using hh
    exact hle.trans (hball t b)
  exact hsample N hN T C Balls Caps p q high ball cap cutoff
    hq hqp hp ht hcounts.1 hcounts.2 hfullMean hballCutoff hhigh hballMean hcapMean hmass

end
end KakeyaFormal.SamplingExactDensity
