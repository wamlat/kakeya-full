import Mathlib

/-!
A genuine finite sampling model for the probabilistic core of Lemma 6.1.
Every tube-cell coordinate takes one of three states: absent, full-only, marked.
Product probabilities are constructed and normalized. Marks imply full selection
at every outcome. Chernoff bounds below are derived from this model, not assumed.
No tube geometry, finite geometric nets, or asymptotic parameter thresholds are
encoded by this module.
-/

namespace KakeyaSampling
open Finset
open scoped BigOperators
noncomputable section

/-- An ordinary probability distribution on a finite sample space. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

def expectation (D : FiniteLaw Ω) (X : Ω → ℝ) : ℝ := ∑ ω, D.weight ω * X ω

def probability (D : FiniteLaw Ω) (E : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if E ω then D.weight ω else 0

/-- Bridge to Mathlib's normalized probability mass functions. -/
def toPMF (D : FiniteLaw Ω) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (D.weight ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => D.nonneg ω), D.total]
    norm_num)

@[simp] theorem toPMF_apply (D : FiniteLaw Ω) (ω : Ω) :
    D.toPMF ω = ENNReal.ofReal (D.weight ω) := rfl

@[simp] theorem probability_true (D : FiniteLaw Ω) : D.probability (fun _ => True) = 1 := by
  simp [probability, D.total]

theorem probability_nonneg (D : FiniteLaw Ω) (E : Ω → Prop) : 0 ≤ D.probability E := by
  classical
  apply sum_nonneg
  intro ω hω
  split_ifs
  · exact D.nonneg ω
  · exact le_rfl

theorem probability_mono (D : FiniteLaw Ω) {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    D.probability E ≤ D.probability F := by
  classical
  apply sum_le_sum
  intro ω hω
  by_cases hE : E ω
  · simp [hE, h ω hE]
  · simp only [hE, if_false]
    split_ifs
    · exact D.nonneg ω
    · exact le_rfl

theorem probability_le_one (D : FiniteLaw Ω) (E : Ω → Prop) : D.probability E ≤ 1 := by
  simpa using D.probability_mono (E := E) (F := fun _ => True) (fun _ _ => True.intro)

theorem probability_union (D : FiniteLaw Ω) (E F : Ω → Prop) :
    D.probability (fun ω => E ω ∨ F ω) ≤ D.probability E + D.probability F := by
  classical
  simp only [probability, ← sum_add_distrib]
  apply sum_le_sum
  intro ω hω
  by_cases hE : E ω <;> by_cases hF : F ω <;> simp [hE, hF, D.nonneg ω]

/-- A union bound on an actual finite probability distribution. -/
theorem probability_exists_le_sum {J : Type*} [Fintype J]
    (D : FiniteLaw Ω) (E : J → Ω → Prop) :
    D.probability (fun ω => ∃ j, E j ω) ≤ ∑ j, D.probability (E j) := by
  classical
  simp only [probability]
  rw [sum_comm]
  apply sum_le_sum
  intro ω hω
  by_cases he : ∃ j, E j ω
  · obtain ⟨j, hj⟩ := he
    simp only [show (∃ j, E j ω) from ⟨j, hj⟩, if_true]
    have hnonneg : ∀ k ∈ (univ : Finset J), 0 ≤ (if E k ω then D.weight ω else 0) := by
      intro k hk
      split_ifs
      · exact D.nonneg ω
      · exact le_rfl
    simpa [hj] using (single_le_sum hnonneg (mem_univ j))
  · simp only [he, if_false]
    apply sum_nonneg
    intro j hj
    split_ifs
    · exact D.nonneg ω
    · exact le_rfl

/-- A strict probability budget gives one outcome satisfying every test. -/
theorem exists_avoiding_of_probability_sum_lt_one {J : Type*} [Fintype J]
    (D : FiniteLaw Ω) (bad : J → Ω → Prop)
    (hbudget : (∑ j, D.probability (bad j)) < 1) :
    ∃ ω, ∀ j, ¬ bad j ω := by
  classical
  by_contra h
  push Not at h
  have hid : D.probability (fun ω => ∃ j, bad j ω) = 1 := by
    have hf : (fun ω => ∃ j, bad j ω) = (fun _ => True) := by
      funext ω
      exact propext ⟨fun _ => True.intro, fun _ => h ω⟩
    rw [hf, D.probability_true]
  have := D.probability_exists_le_sum bad
  linarith

/-- The realization can be taken in the positive-mass support. This prevents
zero-probability selections when p=0 or q=0, a necessary support guarantee for
Lemma 6.1's measurable-to-grid use. -/
theorem exists_positive_avoiding_of_probability_sum_lt_one {J : Type*} [Fintype J]
    (D : FiniteLaw Ω) (bad : J → Ω → Prop)
    (hbudget : (∑ j, D.probability (bad j)) < 1) :
    ∃ ω, 0 < D.weight ω ∧ ∀ j, ¬ bad j ω := by
  classical
  by_contra h
  push Not at h
  have hid : D.probability (fun ω => ∃ j, bad j ω) = 1 := by
    rw [probability, ← D.total]
    apply sum_congr rfl
    intro ω hω
    by_cases hb : ∃ j, bad j ω
    · simp [hb]
    · have hw : D.weight ω = 0 := by
        have hn : ¬ 0 < D.weight ω := fun hp => hb (h ω hp)
        exact le_antisymm (le_of_not_gt hn) (D.nonneg ω)
      simp [hw]
  have := D.probability_exists_le_sum bad
  linarith

theorem probability_eq_sum_pmf (D : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    D.probability E = ∑ ω, if E ω then (D.toPMF ω).toReal else 0 := by
  classical
  simp only [probability, toPMF_apply]
  apply sum_congr rfl
  intro ω hω
  by_cases h : E ω
  · simp [h, ENNReal.toReal_ofReal (D.nonneg ω)]
  · simp [h]

/-- Finite exponential Markov bound, proved directly from the probability weights. -/
theorem exponential_event_bound (D : FiniteLaw Ω) (X : Ω → ℝ) (E : Ω → Prop)
    {t u : ℝ} (hevent : ∀ ω, E ω → t * u ≤ t * X ω) :
    D.probability E ≤ Real.exp (-t * u) * D.expectation (fun ω => Real.exp (t * X ω)) := by
  classical
  have hmul : Real.exp (t * u) * D.probability E ≤
      D.expectation (fun ω => Real.exp (t * X ω)) := by
    simp only [probability, expectation, mul_sum]
    apply sum_le_sum
    intro ω hω
    by_cases he : E ω
    · simp only [he, if_true]
      nlinarith [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hevent ω he)) (D.nonneg ω)]
    · simp only [he, if_false, mul_zero]
      exact mul_nonneg (D.nonneg ω) (Real.exp_pos _).le
  have hc := mul_le_mul_of_nonneg_left hmul (Real.exp_pos (-t * u)).le
  have hz : -t * u + t * u = 0 := by ring
  simpa only [← mul_assoc, ← Real.exp_add, hz, Real.exp_zero, one_mul] using hc

end FiniteLaw

/-- Independent finite-coordinate product probability law. -/
def productLaw {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq ι]
    (D : ι → FiniteLaw S) : FiniteLaw (ι → S) where
  weight ω := ∏ i, (D i).weight (ω i)
  nonneg ω := prod_nonneg (fun i _ => (D i).nonneg (ω i))
  total := by
    rw [← Fintype.prod_sum]
    simp [FiniteLaw.total]

/-- Exact factorization of expectations. This proves coordinate independence
for the constructed finite product model. -/
theorem product_expectation {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq ι]
    (D : ι → FiniteLaw S) (f : ι → S → ℝ) :
    (productLaw D).expectation (fun ω => ∏ i, f i (ω i)) =
      ∏ i, (D i).expectation (f i) := by
  simp only [FiniteLaw.expectation, productLaw, ← prod_mul_distrib]
  exact (Fintype.prod_sum (fun (i : ι) (a : S) => (D i).weight a * f i a)).symm

theorem product_marginal {ι S : Type*} [Fintype ι] [Fintype S] [DecidableEq ι]
    (D : ι → FiniteLaw S) (i : ι) (f : S → ℝ) :
    (productLaw D).expectation (fun ω => f (ω i)) = (D i).expectation f := by
  have h := product_expectation D (fun j a => if j = i then f a else 1)
  simpa [FiniteLaw.expectation, FiniteLaw.total] using h

theorem expectation_sum {Ω J : Type*} [Fintype Ω] [Fintype J]
    (D : FiniteLaw Ω) (X : J → Ω → ℝ) :
    D.expectation (fun ω => ∑ j, X j ω) = ∑ j, D.expectation (X j) := by
  simp only [FiniteLaw.expectation, mul_sum]
  rw [sum_comm]

/-- States 0,1,2 mean absent, full-only, and marked, respectively. -/
def pairLaw (p q : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1) : FiniteLaw (Fin 3) where
  weight a := if a.val = 0 then 1-p else if a.val = 1 then p-q else q
  nonneg a := by split_ifs <;> linarith
  total := by norm_num [Fin.sum_univ_succ]

def fullBit (a : Fin 3) : ℝ := if a.val = 0 then 0 else 1
def markedBit (a : Fin 3) : ℝ := if a.val = 2 then 1 else 0

theorem marked_le_full (a : Fin 3) : markedBit a ≤ fullBit a := by
  fin_cases a <;> norm_num [markedBit, fullBit]

theorem pair_full_mean (p q : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1) :
    (pairLaw p q hq hqp hp).expectation fullBit = p := by
  norm_num [FiniteLaw.expectation, pairLaw, fullBit, Fin.sum_univ_succ]

theorem pair_marked_mean (p q : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1) :
    (pairLaw p q hq hqp hp).expectation markedBit = q := by
  norm_num [FiniteLaw.expectation, pairLaw, markedBit, Fin.sum_univ_succ]

theorem pair_full_mgf (p q t : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1) :
    (pairLaw p q hq hqp hp).expectation (fun a => Real.exp (t * fullBit a)) =
      1 - p + p * Real.exp t := by
  norm_num [FiniteLaw.expectation, pairLaw, fullBit, Fin.sum_univ_succ]
  ring

theorem pair_marked_mgf (p q t : ℝ) (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1) :
    (pairLaw p q hq hqp hp).expectation (fun a => Real.exp (t * markedBit a)) =
      1 - q + q * Real.exp t := by
  norm_num [FiniteLaw.expectation, pairLaw, markedBit, Fin.sum_univ_succ]
  ring

/-- Elementary Bernoulli MGF bound for arbitrary real exponential parameter.
The probabilities may vary independently between coordinates. -/
theorem bernoulli_product_mgf_bound {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (t : ℝ) :
    (∏ i, (1 - p i + p i * Real.exp t)) ≤
      Real.exp ((∑ i, p i) * (Real.exp t - 1)) := by
  have hprod : (∏ i, (1 - p i + p i * Real.exp t)) ≤
      ∏ i, Real.exp (p i * (Real.exp t - 1)) := by
    apply prod_le_prod
    · intro i hi
      exact add_nonneg (sub_nonneg.mpr (hp1 i)) (mul_nonneg (hp0 i) (Real.exp_pos t).le)
    · intro i hi
      have := Real.add_one_le_exp (p i * (Real.exp t - 1))
      nlinarith
  have hidentity : (∏ i, Real.exp (p i * (Real.exp t - 1))) =
      Real.exp ((∑ i, p i) * (Real.exp t - 1)) := by
    rw [← Real.exp_sum, sum_mul]
  exact hprod.trans_eq hidentity

/-- Poisson-binomial upper tail derived by exponential Markov and the MGF bound. -/
theorem chernoff_upper {Ω : Type*} [Fintype Ω] (D : FiniteLaw Ω) (X : Ω → ℝ)
    {mu t u : ℝ} (ht : 0 ≤ t)
    (hmgf : D.expectation (fun ω => Real.exp (t * X ω)) ≤ Real.exp (mu * (Real.exp t - 1))) :
    D.probability (fun ω => u ≤ X ω) ≤ Real.exp (mu * (Real.exp t - 1) - t * u) := by
  have hm := D.exponential_event_bound X (fun ω => u ≤ X ω)
    (fun ω hω => mul_le_mul_of_nonneg_left hω ht)
  refine hm.trans ?_
  calc
    Real.exp (-t * u) * D.expectation (fun ω => Real.exp (t * X ω)) ≤
      Real.exp (-t * u) * Real.exp (mu * (Real.exp t - 1)) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (mu * (Real.exp t - 1) - t * u) := by rw [← Real.exp_add]; congr 1; ring

/-- Poisson-binomial lower tail, using a negative exponential parameter. -/
theorem chernoff_lower {Ω : Type*} [Fintype Ω] (D : FiniteLaw Ω) (X : Ω → ℝ)
    {mu t u : ℝ} (ht : t ≤ 0)
    (hmgf : D.expectation (fun ω => Real.exp (t * X ω)) ≤ Real.exp (mu * (Real.exp t - 1))) :
    D.probability (fun ω => X ω ≤ u) ≤ Real.exp (mu * (Real.exp t - 1) - t * u) := by
  have hm := D.exponential_event_bound X (fun ω => X ω ≤ u)
    (fun ω hω => mul_le_mul_of_nonpos_left hω ht)
  refine hm.trans ?_
  calc
    Real.exp (-t * u) * D.expectation (fun ω => Real.exp (t * X ω)) ≤
      Real.exp (-t * u) * Real.exp (mu * (Real.exp t - 1)) :=
        mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (mu * (Real.exp t - 1) - t * u) := by rw [← Real.exp_add]; congr 1; ring

/-- The actual constants in (6.14): both tails cost at most exp(-mu/12).
This is a multiplicative, mean-dependent bound, so it remains useful for
sparse incidences; an additive Hoeffding bound would not suffice here. -/
theorem poisson_binomial_two_sided {Ω : Type*} [Fintype Ω]
    (D : FiniteLaw Ω) (X : Ω → ℝ) {mu : ℝ} (hmu : 0 ≤ mu)
    (hmgf : ∀ t : ℝ, D.expectation (fun ω => Real.exp (t * X ω)) ≤
      Real.exp (mu * (Real.exp t - 1))) :
    D.probability (fun ω => X ω ≤ mu / 2 ∨ 2 * mu ≤ X ω) ≤ 2 * Real.exp (-mu / 12) := by
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have hehalf : Real.exp (-Real.log 2) = 1 / 2 := by rw [Real.exp_neg, he2]; norm_num
  have hu := chernoff_upper D X (u := 2 * mu) hlog0 (hmgf (Real.log 2))
  have hl := chernoff_lower D X (u := mu / 2) (neg_nonpos.mpr hlog0) (hmgf (-Real.log 2))
  rw [he2] at hu
  rw [hehalf] at hl
  have hupper : mu * (2 - 1) - Real.log 2 * (2 * mu) ≤ -mu / 12 := by
    have hgap : 0 ≤ 2 * Real.log 2 - 13 / 12 := by linarith [Real.log_two_gt_d9]
    nlinarith [mul_nonneg hmu hgap]
  have hlower : mu * (1 / 2 - 1) - -Real.log 2 * (mu / 2) ≤ -mu / 12 := by
    have hgap : 0 ≤ 5 / 6 - Real.log 2 := by linarith [Real.log_two_lt_d9]
    nlinarith [mul_nonneg hmu hgap]
  have hu' := hu.trans (Real.exp_le_exp.mpr hupper)
  have hl' := hl.trans (Real.exp_le_exp.mpr hlower)
  have hsum := D.probability_union (fun ω => X ω ≤ mu / 2) (fun ω => 2 * mu ≤ X ω)
  linarith

/-- A useful uniform upper tail for the tube-ball and angular-cap tests:
if the threshold is at least four times the mean, the failure is at most exp(-u/4). -/
theorem poisson_binomial_large_upper {Ω : Type*} [Fintype Ω]
    (D : FiniteLaw Ω) (X : Ω → ℝ) {mu u : ℝ} (hmu : 0 ≤ mu) (hu : 4 * mu ≤ u)
    (hmgf : ∀ t : ℝ, D.expectation (fun ω => Real.exp (t * X ω)) ≤
      Real.exp (mu * (Real.exp t - 1))) :
    D.probability (fun ω => u ≤ X ω) ≤ Real.exp (-u / 4) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have h := chernoff_upper D X (u := u) hlog (hmgf (Real.log 2))
  rw [he] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hu0 : 0 ≤ u := by linarith
  have hgap : 0 ≤ Real.log 2 - 1 / 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_nonneg hu0 hgap]

/-- The sharper lower-half bound used in (6.18). -/
theorem poisson_binomial_half_lower {Ω : Type*} [Fintype Ω]
    (D : FiniteLaw Ω) (X : Ω → ℝ) {mu : ℝ} (hmu : 0 ≤ mu)
    (hmgf : ∀ t : ℝ, D.expectation (fun ω => Real.exp (t * X ω)) ≤
      Real.exp (mu * (Real.exp t - 1))) :
    D.probability (fun ω => X ω ≤ mu / 2) ≤ Real.exp (-mu / 8) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have h := chernoff_lower D X (u := mu / 2) (neg_nonpos.mpr hlog) (hmgf (-Real.log 2))
  rw [he] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hgap : 0 ≤ 3 / 4 - Real.log 2 := by linarith [Real.log_two_lt_d9]
  nlinarith [mul_nonneg hmu hgap]

/-- Angular-cap tail from (6.18), with its actual constants: cap expectation
at most mu/1000 gives probability at most exp(-mu/8) of reaching mu/20. -/
theorem poisson_binomial_tiny_mean_upper {Ω : Type*} [Fintype Ω]
    (D : FiniteLaw Ω) (X : Ω → ℝ) {nu mu : ℝ} (hnu : 0 ≤ nu) (hsmall : 1000 * nu ≤ mu)
    (hmgf : ∀ t : ℝ, D.expectation (fun ω => Real.exp (t * X ω)) ≤
      Real.exp (nu * (Real.exp t - 1))) :
    D.probability (fun ω => mu / 20 ≤ X ω) ≤ Real.exp (-mu / 8) := by
  have hexp : Real.exp 3 ≤ 26 := by
    have h1 : Real.exp 1 ≤ 11 / 4 := by linarith [Real.exp_one_lt_d9]
    have h3 : Real.exp 3 = (Real.exp 1) ^ 3 := by
      have hsum : (3 : ℝ) = (1 + 1) + 1 := by norm_num
      rw [hsum, Real.exp_add, Real.exp_add]
      ring
    rw [h3]
    calc
      (Real.exp 1) ^ 3 ≤ (11 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ (Real.exp_pos 1).le h1 3
      _ ≤ 26 := by norm_num
  have h := chernoff_upper D X (u := mu / 20) (t := 3) (by norm_num) (hmgf 3)
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hm := mul_le_mul_of_nonneg_left (sub_le_sub_right hexp 1) hnu
  nlinarith

def selectionBit (marked : Bool) (a : Fin 3) : ℝ :=
  if marked then markedBit a else fullBit a

def selectionProbability (marked : Bool) (p q : ℝ) : ℝ := if marked then q else p

theorem pair_selection_mgf (marked : Bool) (p q t : ℝ)
    (hq : 0 ≤ q) (hqp : q ≤ p) (hp : p ≤ 1) :
    (pairLaw p q hq hqp hp).expectation (fun a => Real.exp (t * selectionBit marked a)) =
      1 - selectionProbability marked p q + selectionProbability marked p q * Real.exp t := by
  cases marked
  · exact pair_full_mgf p q t hq hqp hp
  · exact pair_marked_mgf p q t hq hqp hp

section Coupled
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) (hqp : ∀ i, q i ≤ p i) (hp : ∀ i, p i ≤ 1)

def coupledLaw : FiniteLaw (ι → Fin 3) :=
  productLaw (fun i => pairLaw (p i) (q i) (hq i) (hqp i) (hp i))

def fullCount (ω : ι → Fin 3) : ℝ := ∑ i, fullBit (ω i)
def markedCount (ω : ι → Fin 3) : ℝ := ∑ i, markedBit (ω i)

def fullSelected (ω : ι → Fin 3) : Finset ι := univ.filter (fun i => (ω i).val ≠ 0)
def markedSelected (ω : ι → Fin 3) : Finset ι := univ.filter (fun i => (ω i).val = 2)

omit [DecidableEq ι] in
theorem markedSelected_subset (ω : ι → Fin 3) : markedSelected ω ⊆ fullSelected ω := by
  intro i hi
  simp only [markedSelected, fullSelected, mem_filter, mem_univ, true_and] at *
  omega

omit [DecidableEq ι] in
theorem fullCount_eq_card (ω : ι → Fin 3) : fullCount ω = (fullSelected ω).card := by
  classical
  simp [fullCount, fullSelected, fullBit, sum_ite]

omit [DecidableEq ι] in
theorem markedCount_eq_card (ω : ι → Fin 3) : markedCount ω = (markedSelected ω).card := by
  classical
  simp [markedCount, markedSelected, markedBit]

theorem coupled_full_mgf (t : ℝ) :
    (coupledLaw p q hq hqp hp).expectation (fun ω => Real.exp (t * fullCount ω)) =
      ∏ i, (1 - p i + p i * Real.exp t) := by
  have he (ω : ι → Fin 3) : Real.exp (t * fullCount ω) =
      ∏ i, Real.exp (t * fullBit (ω i)) := by
    simp only [fullCount, mul_sum, Real.exp_sum]
  simp_rw [he]
  rw [coupledLaw, product_expectation _ (fun (_ : ι) (a : Fin 3) => Real.exp (t * fullBit a))]
  simp_rw [pair_full_mgf]

theorem coupled_marked_mgf (t : ℝ) :
    (coupledLaw p q hq hqp hp).expectation (fun ω => Real.exp (t * markedCount ω)) =
      ∏ i, (1 - q i + q i * Real.exp t) := by
  have he (ω : ι → Fin 3) : Real.exp (t * markedCount ω) =
      ∏ i, Real.exp (t * markedBit (ω i)) := by
    simp only [markedCount, mul_sum, Real.exp_sum]
  simp_rw [he]
  rw [coupledLaw, product_expectation _ (fun (_ : ι) (a : Fin 3) => Real.exp (t * markedBit a))]
  simp_rw [pair_marked_mgf]

theorem coupled_full_mgf_bound (t : ℝ) :
    (coupledLaw p q hq hqp hp).expectation (fun ω => Real.exp (t * fullCount ω)) ≤
      Real.exp ((∑ i, p i) * (Real.exp t - 1)) := by
  rw [coupled_full_mgf]
  exact bernoulli_product_mgf_bound p (fun i => (hq i).trans (hqp i)) hp t

theorem coupled_marked_mgf_bound (t : ℝ) :
    (coupledLaw p q hq hqp hp).expectation (fun ω => Real.exp (t * markedCount ω)) ≤
      Real.exp ((∑ i, q i) * (Real.exp t - 1)) := by
  rw [coupled_marked_mgf]
  exact bernoulli_product_mgf_bound q hq (fun i => (hqp i).trans (hp i)) t

theorem coupled_full_concentration :
    (coupledLaw p q hq hqp hp).probability (fun ω =>
      fullCount ω ≤ (∑ i, p i) / 2 ∨ 2 * (∑ i, p i) ≤ fullCount ω) ≤
      2 * Real.exp (-(∑ i, p i) / 12) :=
  poisson_binomial_two_sided _ _ (sum_nonneg (fun i _ => (hq i).trans (hqp i)))
    (coupled_full_mgf_bound p q hq hqp hp)

theorem coupled_marked_concentration :
    (coupledLaw p q hq hqp hp).probability (fun ω =>
      markedCount ω ≤ (∑ i, q i) / 2 ∨ 2 * (∑ i, q i) ≤ markedCount ω) ≤
      2 * Real.exp (-(∑ i, q i) / 12) :=
  poisson_binomial_two_sided _ _ (sum_nonneg (fun i _ => hq i))
    (coupled_marked_mgf_bound p q hq hqp hp)

/-- Positive-weight outcomes select no impossible full or marked incidence. -/
theorem coupled_positive_support (ω : ι → Fin 3)
    (hω : 0 < (coupledLaw p q hq hqp hp).weight ω) :
    ∀ i, (0 < fullBit (ω i) → 0 < p i) ∧ (0 < markedBit (ω i) → 0 < q i) := by
  intro i
  have hprod : (∏ j, (pairLaw (p j) (q j) (hq j) (hqp j) (hp j)).weight (ω j)) ≠ 0 := hω.ne'
  have hn := prod_ne_zero_iff.mp hprod i (mem_univ i)
  have hpos : 0 < (pairLaw (p i) (q i) (hq i) (hqp i) (hp i)).weight (ω i) :=
    lt_of_le_of_ne ((pairLaw (p i) (q i) (hq i) (hqp i) (hp i)).nonneg (ω i)) hn.symm
  have hqi := hq i
  have hqpi := hqp i
  generalize ha : ω i = a at *
  fin_cases a <;> norm_num [pairLaw, fullBit, markedBit] at *
  all_goals first | (constructor <;> linarith) | linarith

theorem coupled_full_mean :
    (coupledLaw p q hq hqp hp).expectation fullCount = ∑ i, p i := by
  change (coupledLaw p q hq hqp hp).expectation (fun ω => ∑ i, fullBit (ω i)) = _
  rw [expectation_sum]
  apply sum_congr rfl
  intro i hi
  rw [coupledLaw, product_marginal, pair_full_mean]

theorem coupled_marked_mean :
    (coupledLaw p q hq hqp hp).expectation markedCount = ∑ i, q i := by
  change (coupledLaw p q hq hqp hp).expectation (fun ω => ∑ i, markedBit (ω i)) = _
  rw [expectation_sum]
  apply sum_congr rfl
  intro i hi
  rw [coupledLaw, product_marginal, pair_marked_mean]

/-- An arbitrary subset of incidences, using full or marked selection, all on
one common product outcome space. Tubes, balls and direction caps can be encoded
as such masks once the finite geometric test families are constructed. -/
def testCount (active : ι → Bool) (marked : Bool) (ω : ι → Fin 3) : ℝ :=
  ∑ i, if active i then selectionBit marked (ω i) else 0

def testMean (active : ι → Bool) (marked : Bool) : ℝ :=
  ∑ i, if active i then selectionProbability marked (p i) (q i) else 0

include hq hqp in
omit [DecidableEq ι] in
theorem test_mean_nonneg (active : ι → Bool) (marked : Bool) :
    0 ≤ testMean p q active marked := by
  apply sum_nonneg
  intro i hi
  cases ha : active i <;> cases hm : marked <;>
    simp [selectionProbability, hq i, (hq i).trans (hqp i)]

theorem coupled_test_mean (active : ι → Bool) (marked : Bool) :
    (coupledLaw p q hq hqp hp).expectation (testCount active marked) =
      testMean p q active marked := by
  change (coupledLaw p q hq hqp hp).expectation
    (fun ω => ∑ i, if active i then selectionBit marked (ω i) else 0) = _
  rw [expectation_sum]
  apply sum_congr rfl
  intro i hi
  rw [coupledLaw, product_marginal _ i (fun a => if active i then selectionBit marked a else 0)]
  cases ha : active i <;> cases hm : marked <;>
    norm_num [selectionBit, selectionProbability, FiniteLaw.expectation, pairLaw,
      fullBit, markedBit, Fin.sum_univ_succ]

theorem coupled_test_mgf (active : ι → Bool) (marked : Bool) (t : ℝ) :
    (coupledLaw p q hq hqp hp).expectation (fun ω => Real.exp (t * testCount active marked ω)) =
      ∏ i, (1 - (if active i then selectionProbability marked (p i) (q i) else 0) +
        (if active i then selectionProbability marked (p i) (q i) else 0) * Real.exp t) := by
  have he (ω : ι → Fin 3) : Real.exp (t * testCount active marked ω) =
      ∏ i, Real.exp (t * (if active i then selectionBit marked (ω i) else 0)) := by
    simp only [testCount, mul_sum, Real.exp_sum]
  simp_rw [he]
  rw [coupledLaw, product_expectation _
    (fun i a => Real.exp (t * (if active i then selectionBit marked a else 0)))]
  apply prod_congr rfl
  intro i hi
  cases ha : active i
  · simp [FiniteLaw.expectation, FiniteLaw.total]
  · simp only [if_true]
    exact pair_selection_mgf marked (p i) (q i) t (hq i) (hqp i) (hp i)

theorem coupled_test_mgf_bound (active : ι → Bool) (marked : Bool) (t : ℝ) :
    (coupledLaw p q hq hqp hp).expectation (fun ω => Real.exp (t * testCount active marked ω)) ≤
      Real.exp (testMean p q active marked * (Real.exp t - 1)) := by
  rw [coupled_test_mgf]
  apply bernoulli_product_mgf_bound
  · intro i
    cases ha : active i <;> cases hm : marked <;>
      simp [selectionProbability, hq i, (hq i).trans (hqp i)]
  · intro i
    cases ha : active i <;> cases hm : marked <;>
      simp [selectionProbability, hp i, (hqp i).trans (hp i)]

theorem coupled_test_concentration (active : ι → Bool) (marked : Bool) :
    (coupledLaw p q hq hqp hp).probability (fun ω =>
      testCount active marked ω ≤ testMean p q active marked / 2 ∨
      2 * testMean p q active marked ≤ testCount active marked ω) ≤
      2 * Real.exp (-testMean p q active marked / 12) :=
  poisson_binomial_two_sided _ _ (test_mean_nonneg p q hq hqp active marked)
    (coupled_test_mgf_bound p q hq hqp hp active marked)

theorem coupled_test_large_upper (active : ι → Bool) (marked : Bool) {u : ℝ}
    (hu : 4 * testMean p q active marked ≤ u) :
    (coupledLaw p q hq hqp hp).probability (fun ω => u ≤ testCount active marked ω) ≤
      Real.exp (-u / 4) :=
  poisson_binomial_large_upper _ _ (test_mean_nonneg p q hq hqp active marked) hu
    (coupled_test_mgf_bound p q hq hqp hp active marked)

theorem coupled_test_half_lower (active : ι → Bool) (marked : Bool) :
    (coupledLaw p q hq hqp hp).probability (fun ω =>
      testCount active marked ω ≤ testMean p q active marked / 2) ≤
      Real.exp (-testMean p q active marked / 8) :=
  poisson_binomial_half_lower _ _ (test_mean_nonneg p q hq hqp active marked)
    (coupled_test_mgf_bound p q hq hqp hp active marked)

theorem coupled_test_tiny_mean_upper (active : ι → Bool) (marked : Bool) {mu : ℝ}
    (hsmall : 1000 * testMean p q active marked ≤ mu) :
    (coupledLaw p q hq hqp hp).probability (fun ω => mu / 20 ≤ testCount active marked ω) ≤
      Real.exp (-mu / 8) :=
  poisson_binomial_tiny_mean_upper _ _ (test_mean_nonneg p q hq hqp active marked) hsmall
    (coupled_test_mgf_bound p q hq hqp hp active marked)

/-- The high-cell and cap events in (6.18), on their common marked sampling
space. Their union has probability at most 2 exp(-mu/8); no independence
between a cell total and a cap total is assumed or needed. -/
theorem coupled_angular_failure (cell cap : ι → Bool)
    (hsmall : 1000 * testMean p q cap true ≤ testMean p q cell true) :
    (coupledLaw p q hq hqp hp).probability (fun ω =>
      testCount cell true ω ≤ testMean p q cell true / 2 ∨
      testMean p q cell true / 20 ≤ testCount cap true ω) ≤
      2 * Real.exp (-testMean p q cell true / 8) := by
  have hl := coupled_test_half_lower p q hq hqp hp cell true
  have hu := coupled_test_tiny_mean_upper p q hq hqp hp cap true hsmall
  have hsum := (coupledLaw p q hq hqp hp).probability_union
    (fun ω => testCount cell true ω ≤ testMean p q cell true / 2)
    (fun ω => testMean p q cell true / 20 ≤ testCount cap true ω)
  linarith

omit [DecidableEq ι] in
theorem angular_good_fraction (cell cap : ι → Bool) (ω : ι → Fin 3)
    (hcell : testMean p q cell true / 2 < testCount cell true ω)
    (hcap : testCount cap true ω < testMean p q cell true / 20) :
    testCount cap true ω < testCount cell true ω / 10 := by linarith

include hq hqp hp in
/-- A finite family of actual full/marked subset tests has a simultaneous
realization. `band=true` requests mean/2 < count < 2*mean; `band=false`
requests count < threshold. Failure probabilities here are the Chernoff bounds
proved above for the concrete product law. Test events need not be independent. -/
theorem coupled_simultaneous_realization {J : Type*} [Fintype J]
    (active : J → ι → Bool) (marked band : J → Bool) (threshold : J → ℝ)
    (hthreshold : ∀ j, band j = false → 4 * testMean p q (active j) (marked j) ≤ threshold j)
    (hbudget : (∑ j, if band j then
      2 * Real.exp (-testMean p q (active j) (marked j) / 12)
      else Real.exp (-threshold j / 4)) < 1) :
    ∃ ω : ι → Fin 3,
      (∀ i, markedBit (ω i) ≤ fullBit (ω i)) ∧
      (∀ i, (0 < fullBit (ω i) → 0 < p i) ∧ (0 < markedBit (ω i) → 0 < q i)) ∧
      ∀ j, if band j then
        testMean p q (active j) (marked j) / 2 < testCount (active j) (marked j) ω ∧
        testCount (active j) (marked j) ω < 2 * testMean p q (active j) (marked j)
      else testCount (active j) (marked j) ω < threshold j := by
  classical
  let bad : J → (ι → Fin 3) → Prop := fun j ω =>
    if band j then
      testCount (active j) (marked j) ω ≤ testMean p q (active j) (marked j) / 2 ∨
      2 * testMean p q (active j) (marked j) ≤ testCount (active j) (marked j) ω
    else threshold j ≤ testCount (active j) (marked j) ω
  have hbound (j : J) : (coupledLaw p q hq hqp hp).probability (bad j) ≤
      if band j then 2 * Real.exp (-testMean p q (active j) (marked j) / 12)
      else Real.exp (-threshold j / 4) := by
    cases hb : band j
    · simpa [bad, hb] using coupled_test_large_upper p q hq hqp hp
        (active j) (marked j) (hthreshold j hb)
    · simpa [bad, hb] using coupled_test_concentration p q hq hqp hp (active j) (marked j)
  have hprob : (∑ j, (coupledLaw p q hq hqp hp).probability (bad j)) < 1 :=
    (sum_le_sum (fun j _ => hbound j)).trans_lt hbudget
  obtain ⟨ω, hpositive, hω⟩ := (coupledLaw p q hq hqp hp).exists_positive_avoiding_of_probability_sum_lt_one bad hprob
  refine ⟨ω, (fun i => marked_le_full (ω i)), coupled_positive_support p q hq hqp hp ω hpositive, ?_⟩
  intro j
  have hj := hω j
  cases hb : band j
  · simpa [bad, hb] using hj
  · simpa [bad, hb, not_or, not_le] using hj

end Coupled
end
end KakeyaSampling

-- Kernel dependency checks for every exported theorem.
#print axioms KakeyaSampling.FiniteLaw.toPMF_apply
#print axioms KakeyaSampling.FiniteLaw.probability_true
#print axioms KakeyaSampling.FiniteLaw.probability_nonneg
#print axioms KakeyaSampling.FiniteLaw.probability_mono
#print axioms KakeyaSampling.FiniteLaw.probability_le_one
#print axioms KakeyaSampling.FiniteLaw.probability_union
#print axioms KakeyaSampling.FiniteLaw.probability_exists_le_sum
#print axioms KakeyaSampling.FiniteLaw.exists_avoiding_of_probability_sum_lt_one
#print axioms KakeyaSampling.FiniteLaw.exists_positive_avoiding_of_probability_sum_lt_one
#print axioms KakeyaSampling.FiniteLaw.probability_eq_sum_pmf
#print axioms KakeyaSampling.FiniteLaw.exponential_event_bound
#print axioms KakeyaSampling.product_expectation
#print axioms KakeyaSampling.product_marginal
#print axioms KakeyaSampling.expectation_sum
#print axioms KakeyaSampling.marked_le_full
#print axioms KakeyaSampling.pair_full_mean
#print axioms KakeyaSampling.pair_marked_mean
#print axioms KakeyaSampling.pair_full_mgf
#print axioms KakeyaSampling.pair_marked_mgf
#print axioms KakeyaSampling.bernoulli_product_mgf_bound
#print axioms KakeyaSampling.chernoff_upper
#print axioms KakeyaSampling.chernoff_lower
#print axioms KakeyaSampling.poisson_binomial_two_sided
#print axioms KakeyaSampling.poisson_binomial_large_upper
#print axioms KakeyaSampling.poisson_binomial_half_lower
#print axioms KakeyaSampling.poisson_binomial_tiny_mean_upper
#print axioms KakeyaSampling.pair_selection_mgf
#print axioms KakeyaSampling.markedSelected_subset
#print axioms KakeyaSampling.fullCount_eq_card
#print axioms KakeyaSampling.markedCount_eq_card
#print axioms KakeyaSampling.coupled_full_mgf
#print axioms KakeyaSampling.coupled_marked_mgf
#print axioms KakeyaSampling.coupled_full_mgf_bound
#print axioms KakeyaSampling.coupled_marked_mgf_bound
#print axioms KakeyaSampling.coupled_full_concentration
#print axioms KakeyaSampling.coupled_marked_concentration
#print axioms KakeyaSampling.coupled_positive_support
#print axioms KakeyaSampling.coupled_full_mean
#print axioms KakeyaSampling.coupled_marked_mean
#print axioms KakeyaSampling.test_mean_nonneg
#print axioms KakeyaSampling.coupled_test_mgf
#print axioms KakeyaSampling.coupled_test_mgf_bound
#print axioms KakeyaSampling.coupled_test_concentration
#print axioms KakeyaSampling.coupled_test_large_upper
#print axioms KakeyaSampling.coupled_test_half_lower
#print axioms KakeyaSampling.coupled_test_tiny_mean_upper
#print axioms KakeyaSampling.coupled_angular_failure
#print axioms KakeyaSampling.angular_good_fraction
#print axioms KakeyaSampling.coupled_simultaneous_realization
#print axioms KakeyaSampling.coupled_test_mean
