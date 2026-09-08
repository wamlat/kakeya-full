import SamplingThreshold

/-! The actual density and full-ball failure probabilities in (6.14)-(6.16),
with a separate uniform one-eighth budget. The event is on the same concrete
coupled product law as marked high-cell and net-cap sampling. -/
namespace KakeyaFormal.SamplingGeometricFailure
open KakeyaSampling KakeyaSamplingApplication SamplingThreshold Finset Filter
open scoped Topology BigOperators
noncomputable section
open Classical
universe uT uC uB

variable {T C B : Type*} [Fintype T] [Fintype C] [Fintype B]
  [DecidableEq T] [DecidableEq C]

def law (p q : T → C → ℝ) (hq : ∀ t c, 0 ≤ q t c)
    (hqp : ∀ t c, q t c ≤ p t c) (hp : ∀ t c, p t c ≤ 1) : FiniteLaw (Outcome T C) :=
  coupledLaw (flatten p) (flatten q) (fun tc => hq tc.1 tc.2)
    (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2)

def bad (p : T → C → ℝ) (ball : B → C → Bool) (cutoff : T → B → ℝ)
    (j : T ⊕ (T × B)) (ω : Outcome T C) : Prop := match j with
  | Sum.inl t => fullTubeCount ω t ≤ fullMean p t/2 ∨ 2*fullMean p t ≤ fullTubeCount ω t
  | Sum.inr tb => cutoff tb.1 tb.2 ≤ fullBallCount ω ball tb.1 tb.2

def geometricFailure (p : T → C → ℝ) (ball : B → C → Bool) (cutoff : T → B → ℝ)
    (ω : Outcome T C) : Prop := ∃ j, bad p ball cutoff j ω

def budget (p : T → C → ℝ) (cutoff : T → B → ℝ) : ℝ :=
  (∑ t, 2*Real.exp (-fullMean p t/12)) + ∑ t, ∑ b, Real.exp (-cutoff t b/4)

/-- No geometric failure probability is assumed: each actual subset count
has its previously proved finite-product tail, and the union is finite. -/
theorem probability_le (p q : T → C → ℝ) (hq : ∀ t c, 0 ≤ q t c)
    (hqp : ∀ t c, q t c ≤ p t c) (hp : ∀ t c, p t c ≤ 1)
    (ball : B → C → Bool) (cutoff : T → B → ℝ)
    (hball : ∀ t b, 4*ballMean p ball t b ≤ cutoff t b) :
    (law p q hq hqp hp).probability (geometricFailure p ball cutoff) ≤ budget p cutoff := by
  let rate : T ⊕ (T × B) → ℝ := fun j => match j with
    | Sum.inl t => 2*Real.exp (-fullMean p t/12)
    | Sum.inr tb => Real.exp (-cutoff tb.1 tb.2/4)
  have hj : ∀ j, (law p q hq hqp hp).probability (bad p ball cutoff j) ≤ rate j := by
    intro j
    rcases j with t | tb
    · change (law p q hq hqp hp).probability
        (fun ω => fullTubeCount ω t ≤ fullMean p t/2 ∨
          2*fullMean p t ≤ fullTubeCount ω t) ≤ 2*Real.exp (-fullMean p t/12)
      simpa [law] using coupled_test_concentration (flatten p) (flatten q)
        (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2)
        (tubeMask t) false
    · have hh : 4*testMean (flatten p) (flatten q) (ballMask ball tb.1 tb.2) false ≤ cutoff tb.1 tb.2 :=
        by simpa using hball tb.1 tb.2
      change (law p q hq hqp hp).probability
        (fun ω => cutoff tb.1 tb.2 ≤ fullBallCount ω ball tb.1 tb.2) ≤
        Real.exp (-cutoff tb.1 tb.2/4)
      simpa [law] using coupled_test_large_upper (flatten p) (flatten q)
        (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2)
        (ballMask ball tb.1 tb.2) false hh
  have hu := (law p q hq hqp hp).probability_exists_le_sum (bad p ball cutoff)
  have hs := hu.trans (sum_le_sum (fun j _ => hj j))
  change (law p q hq hqp hp).probability (fun ω => ∃ j, bad p ball cutoff j ω) ≤ _
  simpa only [rate,Fintype.sum_sum_type,Fintype.sum_prod_type,budget] using hs

omit [DecidableEq T] [DecidableEq C] in
theorem budget_le_uniform (p : T → C → ℝ) (cutoff : T → B → ℝ)
    {N CT CB cf cb eta phi u v : ℝ}
    (ht : (Fintype.card T:ℝ) ≤ CT*N^u)
    (hb : (Fintype.card T:ℝ)*(Fintype.card B:ℝ) ≤ CB*N^v)
    (hfull : ∀ t, cf*N^eta ≤ fullMean p t)
    (hball : ∀ t b, cb*N^phi ≤ cutoff t b) :
    budget p cutoff ≤ 2*CT*N^u*Real.exp (-(cf*N^eta)/12)+
      CB*N^v*Real.exp (-(cb*N^phi)/4) := by
  have ht' : (∑ t, 2*Real.exp (-fullMean p t/12)) ≤
      (Fintype.card T:ℝ)*(2*Real.exp (-(cf*N^eta)/12)) := by
    calc
      _ ≤ ∑ _t : T, 2*Real.exp (-(cf*N^eta)/12) := sum_le_sum (fun t _ => by
        gcongr; linarith [hfull t])
      _ = _ := by simp
  have hb' : (∑ t, ∑ b, Real.exp (-cutoff t b/4)) ≤
      (Fintype.card T:ℝ)*(Fintype.card B:ℝ)*Real.exp (-(cb*N^phi)/4) := by
    calc
      _ ≤ ∑ _t : T, ∑ _b : B, Real.exp (-(cb*N^phi)/4) := sum_le_sum (fun t _ =>
        sum_le_sum (fun b _ => Real.exp_le_exp.mpr (by linarith [hball t b])))
      _ = _ := by simp; ring
  have h₁ := mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ 2*Real.exp (-(cf*N^eta)/12))
  have h₂ := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-(cb*N^phi)/4)).le
  dsimp [budget]
  nlinarith

/-- A threshold before all actual arrays and finite types gives the literal
separate one-eighth density/two-ends budget, for every positive mean power. -/
theorem uniform_threshold {CT CB cf cb eta phi u v : ℝ}
    (hcf : 0 < cf) (hcb : 0 < cb) (heta : 0 < eta) (hphi : 0 < phi) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      2*CT*N^u*Real.exp (-(cf*N^eta)/12)+CB*N^v*Real.exp (-(cb*N^phi)/4) < 1/8 := by
  have hfirst := (stretched_exp_limit u (show 0 < cf/12 by positivity) heta).const_mul (2*CT)
  have hsecond := (stretched_exp_limit v (show 0 < cb/4 by positivity) hphi).const_mul CB
  have hall : Tendsto (fun N : ℝ =>
      (2*CT)*(N^u*Real.exp (-(cf/12)*N^eta))+CB*(N^v*Real.exp (-(cb/4)*N^phi)))
      atTop (𝓝 0) := by simpa only [mul_zero,add_zero] using hfirst.add hsecond
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (hall.eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/8)))
  refine ⟨max 1 N₁,le_max_left _ _,?_⟩
  intro N hN
  have hh := hN₁ N ((le_max_right _ _).trans hN)
  have he₁ : -(cf*N^eta)/12 = -(cf/12)*N^eta := by ring
  have he₂ : -(cb*N^phi)/4 = -(cb/4)*N^phi := by ring
  rw [he₁,he₂]
  simpa only [mul_assoc] using hh

/-- Actual density/two-ends failure is below1/8 above one uniform threshold;
the expected-count and cardinality bounds remain explicit generic inputs. -/
theorem uniform_probability {CT CB cf cb eta phi u v : ℝ}
    (hcf : 0 < cf) (hcb : 0 < cb) (heta : 0 < eta) (hphi : 0 < phi) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (T : Type uT) (C : Type uC) (B : Type uB)
      [Fintype T] [Fintype C] [Fintype B] [DecidableEq T] [DecidableEq C],
      ∀ (p q : T → C → ℝ) (hq : ∀ t c, 0 ≤ q t c)
      (hqp : ∀ t c, q t c ≤ p t c) (hp : ∀ t c, p t c ≤ 1)
      (ball : B → C → Bool) (cutoff : T → B → ℝ),
      (Fintype.card T:ℝ) ≤ CT*N^u →
      (Fintype.card T:ℝ)*(Fintype.card B:ℝ) ≤ CB*N^v →
      (∀ t, cf*N^eta ≤ fullMean p t) → (∀ t b, cb*N^phi ≤ cutoff t b) →
      (∀ t b, 4*ballMean p ball t b ≤ cutoff t b) →
      (law p q hq hqp hp).probability (geometricFailure p ball cutoff) < 1/8 := by
  obtain ⟨N₀,hN₀,hsmall⟩ := uniform_threshold (CT:=CT) (CB:=CB) (u:=u) (v:=v) hcf hcb heta hphi
  refine ⟨N₀,hN₀,?_⟩
  intro N hN T C B _ _ _ _ _ p q hq hqp hp ball cutoff ht hb hf hcut hball
  exact ((probability_le p q hq hqp hp ball cutoff hball).trans
    (budget_le_uniform p cutoff ht hb hf hcut)).trans_lt (hsmall N hN)

end
end KakeyaFormal.SamplingGeometricFailure
