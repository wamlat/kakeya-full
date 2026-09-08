import Sampling

/-!
Finite tube-cell assembly of the probability core of Lemma 6.1.
Tube, cell, ball and cap labels are finite types. The geometric meaning of their
incidence masks and the expectation inequalities remain explicit input data.
No failure probabilities or simultaneous good event are assumed.
-/

namespace KakeyaSamplingApplication
open Finset
open scoped BigOperators
open KakeyaSampling
noncomputable section

variable {T C B A : Type*} [Fintype T] [Fintype C] [Fintype B] [Fintype A]
variable [DecidableEq T] [DecidableEq C]

abbrev Outcome (T C : Type*) := T × C → Fin 3

def flatten (p : T → C → ℝ) : T × C → ℝ := fun tc => p tc.1 tc.2

def tubeMask (t : T) : T × C → Bool := fun tc => decide (tc.1 = t)
def ballMask (ball : B → C → Bool) (t : T) (b : B) : T × C → Bool :=
  fun tc => decide (tc.1 = t) && ball b tc.2

def cellMask (c : C) : T × C → Bool := fun tc => decide (tc.2 = c)
def capMask (cap : A → T → Bool) (c : C) (a : A) : T × C → Bool :=
  fun tc => decide (tc.2 = c) && cap a tc.1

def fullMean (p : T → C → ℝ) (t : T) : ℝ := ∑ c, p t c
def markedMean (q : T → C → ℝ) (c : C) : ℝ := ∑ t, q t c

def ballMean (p : T → C → ℝ) (ball : B → C → Bool) (t : T) (b : B) : ℝ :=
  ∑ c, if ball b c then p t c else 0

def capMean (q : T → C → ℝ) (cap : A → T → Bool) (c : C) (a : A) : ℝ :=
  ∑ t, if cap a t then q t c else 0

def fullTubeCount (ω : Outcome T C) (t : T) : ℝ := ∑ c, fullBit (ω (t,c))
def markedCellCount (ω : Outcome T C) (c : C) : ℝ := ∑ t, markedBit (ω (t,c))
def fullBallCount (ω : Outcome T C) (ball : B → C → Bool) (t : T) (b : B) : ℝ :=
  ∑ c, if ball b c then fullBit (ω (t,c)) else 0

def markedCapCount (ω : Outcome T C) (cap : A → T → Bool) (c : C) (a : A) : ℝ :=
  ∑ t, if cap a t then markedBit (ω (t,c)) else 0

omit [DecidableEq C] in
@[simp] theorem tube_test_mean (p q : T → C → ℝ) (t : T) :
    testMean (flatten p) (flatten q) (tubeMask t) false = fullMean p t := by
  simp [testMean, flatten, tubeMask, selectionProbability, Fintype.sum_prod_type, fullMean]

omit [DecidableEq T] in
@[simp] theorem cell_test_mean (p q : T → C → ℝ) (c : C) :
    testMean (flatten p) (flatten q) (cellMask c) true = markedMean q c := by
  simp [testMean, flatten, cellMask, selectionProbability, Fintype.sum_prod_type, markedMean]

omit [Fintype B] [DecidableEq C] in
@[simp] theorem ball_test_mean (p q : T → C → ℝ) (ball : B → C → Bool) (t : T) (b : B) :
    testMean (flatten p) (flatten q) (ballMask ball t b) false = ballMean p ball t b := by
  simp [testMean, flatten, ballMask, selectionProbability, Fintype.sum_prod_type, ballMean,
    ite_and]

omit [Fintype A] [DecidableEq T] in
@[simp] theorem cap_test_mean (p q : T → C → ℝ) (cap : A → T → Bool) (c : C) (a : A) :
    testMean (flatten p) (flatten q) (capMask cap c a) true = capMean q cap c a := by
  simp [testMean, flatten, capMask, selectionProbability, Fintype.sum_prod_type, capMean,
    ite_and]

omit [DecidableEq C] in
@[simp] theorem tube_test_count (ω : Outcome T C) (t : T) :
    testCount (tubeMask t) false ω = fullTubeCount ω t := by
  simp only [testCount, tubeMask, selectionBit, Bool.false_eq_true, if_false,
    Fintype.sum_prod_type, decide_eq_true_eq, fullTubeCount]
  rw [sum_comm]
  simp

omit [DecidableEq T] in
@[simp] theorem cell_test_count (ω : Outcome T C) (c : C) :
    testCount (cellMask c) true ω = markedCellCount ω c := by
  simp [testCount, cellMask, selectionBit, Fintype.sum_prod_type, markedCellCount]

omit [Fintype B] [DecidableEq C] in
@[simp] theorem ball_test_count (ω : Outcome T C) (ball : B → C → Bool) (t : T) (b : B) :
    testCount (ballMask ball t b) false ω = fullBallCount ω ball t b := by
  simp [testCount, ballMask, selectionBit, Fintype.sum_prod_type, fullBallCount, ite_and]

omit [Fintype A] [DecidableEq T] in
@[simp] theorem cap_test_count (ω : Outcome T C) (cap : A → T → Bool) (c : C) (a : A) :
    testCount (capMask cap c a) true ω = markedCapCount ω cap c a := by
  simp [testCount, capMask, selectionBit, Fintype.sum_prod_type, markedCapCount, ite_and]

/-- Actual finite full shading and retained high-cell marked shading. -/
def fullShading (ω : Outcome T C) (t : T) : Finset C :=
  univ.filter (fun c => (ω (t,c)).val ≠ 0)
def markedShading (high : Finset C) (ω : Outcome T C) (t : T) : Finset C :=
  univ.filter (fun c => c ∈ high ∧ (ω (t,c)).val = 2)

omit [Fintype T] [DecidableEq T] in
theorem markedShading_subset (high : Finset C) (ω : Outcome T C) (t : T) :
    markedShading high ω t ⊆ fullShading ω t := by
  intro c hc
  simp only [markedShading, fullShading, mem_filter, mem_univ, true_and] at *
  omega

omit [Fintype T] [DecidableEq T] [DecidableEq C] in
theorem fullTubeCount_eq_card (ω : Outcome T C) (t : T) :
    fullTubeCount ω t = (fullShading ω t).card := by
  simp [fullTubeCount, fullShading, fullBit, sum_ite]

omit [DecidableEq T] in
/-- Summing the retained marked shading cardinalities counts exactly the high-cell marks. -/
theorem marked_total_identity (high : Finset C) (ω : Outcome T C) :
    (∑ t, ((markedShading high ω t).card : ℝ)) = ∑ c ∈ high, markedCellCount ω c := by
  simp only [markedCellCount]
  rw [sum_comm]
  apply sum_congr rfl
  intro t ht
  have heq : markedShading high ω t = high.filter (fun c => (ω (t,c)).val = 2) := by
    ext c
    simp [markedShading]
  rw [heq]
  simp [markedBit]

/-- The concrete sum of the derived Chernoff failure bounds. -/
def failureBudget (p q : T → C → ℝ) (high : Finset C) (cutoff : T → B → ℝ) : ℝ :=
    (∑ t, 2 * Real.exp (-fullMean p t / 12)) +
    (∑ t, ∑ b, Real.exp (-cutoff t b / 4)) +
    (∑ c ∈ high, Real.exp (-markedMean q c / 8)) +
    (∑ c ∈ high, ∑ _a : A, Real.exp (-markedMean q c / 8))

omit [DecidableEq T] [DecidableEq C] in
/-- A usable bound for the failure budget from uniform expectation/cutoff
lower bounds and the actual numbers of tubes, balls, high cells and caps. This
is the finite counting interface for the large-N argument in (6.14)–(6.19). -/
theorem failureBudget_le_uniform (p q : T → C → ℝ) (high : Finset C) (cutoff : T → B → ℝ)
    {muFull muBall muHigh : ℝ}
    (hfull : ∀ t, muFull ≤ fullMean p t)
    (hball : ∀ t b, muBall ≤ cutoff t b)
    (hhigh : ∀ c ∈ high, muHigh ≤ markedMean q c) :
    failureBudget (A := A) p q high cutoff ≤
      2 * (Fintype.card T : ℝ) * Real.exp (-muFull / 12) +
      (Fintype.card T : ℝ) * (Fintype.card B : ℝ) * Real.exp (-muBall / 4) +
      (high.card : ℝ) * (1 + (Fintype.card A : ℝ)) * Real.exp (-muHigh / 8) := by
  have ht : (∑ t, 2 * Real.exp (-fullMean p t / 12)) ≤
      2 * (Fintype.card T : ℝ) * Real.exp (-muFull / 12) := by
    calc
      (∑ t, 2 * Real.exp (-fullMean p t / 12)) ≤ ∑ _t : T, 2 * Real.exp (-muFull / 12) := by
        apply sum_le_sum
        intro t ht
        have he := Real.exp_le_exp.mpr (show -fullMean p t / 12 ≤ -muFull / 12 by linarith [hfull t])
        linarith
      _ = _ := by simp; ring
  have hb : (∑ t, ∑ b, Real.exp (-cutoff t b / 4)) ≤
      (Fintype.card T : ℝ) * (Fintype.card B : ℝ) * Real.exp (-muBall / 4) := by
    calc
      (∑ t, ∑ b, Real.exp (-cutoff t b / 4)) ≤ ∑ _t : T, ∑ _b : B, Real.exp (-muBall / 4) := by
        apply sum_le_sum
        intro t ht
        apply sum_le_sum
        intro b hb
        exact Real.exp_le_exp.mpr (by linarith [hball t b])
      _ = _ := by simp; ring
  have hh : (∑ c ∈ high, Real.exp (-markedMean q c / 8)) ≤
      (high.card : ℝ) * Real.exp (-muHigh / 8) := by
    calc
      (∑ c ∈ high, Real.exp (-markedMean q c / 8)) ≤ ∑ _c ∈ high, Real.exp (-muHigh / 8) := by
        apply sum_le_sum
        intro c hc
        exact Real.exp_le_exp.mpr (by linarith [hhigh c hc])
      _ = _ := by simp
  have hc : (∑ c ∈ high, ∑ _a : A, Real.exp (-markedMean q c / 8)) ≤
      (high.card : ℝ) * (Fintype.card A : ℝ) * Real.exp (-muHigh / 8) := by
    calc
      (∑ c ∈ high, ∑ _a : A, Real.exp (-markedMean q c / 8)) ≤
          ∑ _c ∈ high, ∑ _a : A, Real.exp (-muHigh / 8) := by
        apply sum_le_sum
        intro c hc
        apply sum_le_sum
        intro a ha
        exact Real.exp_le_exp.mpr (by linarith [hhigh c hc])
      _ = _ := by simp; ring
  dsimp [failureBudget]
  nlinarith

/-- Every promised finite conclusion is a field of this structure. Full and
marked shadings are actual finite sets of cells on the original tube index type. -/
structure SampleGood (p q : T → C → ℝ) (high : Finset C)
    (ball : B → C → Bool) (cap : A → T → Bool) (cutoff : T → B → ℝ)
    (ω : Outcome T C) : Prop where
  density : ∀ t, fullMean p t / 2 ≤ (fullShading ω t).card ∧
    ((fullShading ω t).card : ℝ) ≤ 2 * fullMean p t
  ball_upper : ∀ t b, fullBallCount ω ball t b ≤ cutoff t b
  high_cell_lower : ∀ c ∈ high, markedMean q c / 2 ≤ markedCellCount ω c
  angular : ∀ c ∈ high, ∀ a, markedCapCount ω cap c a ≤ markedCellCount ω c / 10
  marked_mass : (∑ c, markedMean q c) / 4 ≤ ∑ t, ((markedShading high ω t).card : ℝ)
  full_mass : (∑ t, ((fullShading ω t).card : ℝ)) ≤ 2 * ∑ t, fullMean p t
  marked_subset : ∀ t, markedShading high ω t ⊆ fullShading ω t
  full_support : ∀ t c, c ∈ fullShading ω t → 0 < p t c
  marked_support : ∀ t c, c ∈ markedShading high ω t → 0 < q t c

/-- Finite assembly of (6.14)–(6.18). Expected ball/cap bounds and the explicit
numeric Chernoff budget imply one simultaneous realization. No good-event or
failure-probability hypothesis is assumed. The high-cell mass premise yields
the quarter-total retained marked incidence bound. -/
theorem finite_sampling_assembly (p q : T → C → ℝ)
    (hq : ∀ t c, 0 ≤ q t c) (hqp : ∀ t c, q t c ≤ p t c) (hp : ∀ t c, p t c ≤ 1)
    (high : Finset C) (ball : B → C → Bool) (cap : A → T → Bool) (cutoff : T → B → ℝ)
    (hball : ∀ t b, 4 * ballMean p ball t b ≤ cutoff t b)
    (hcap : ∀ c ∈ high, ∀ a, 1000 * capMean q cap c a ≤ markedMean q c)
    (hhigh : (∑ c, markedMean q c) / 2 ≤ ∑ c ∈ high, markedMean q c)
    (hbudget : failureBudget (A := A) p q high cutoff < 1) :
    ∃ ω : Outcome T C, SampleGood p q high ball cap cutoff ω := by
  classical
  let D := coupledLaw (flatten p) (flatten q)
    (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2)
  let J := T ⊕ ((T × B) ⊕ (↥high ⊕ (↥high × A)))
  let bad : J → Outcome T C → Prop := fun j ω => match j with
    | Sum.inl t => fullTubeCount ω t ≤ fullMean p t / 2 ∨ 2 * fullMean p t ≤ fullTubeCount ω t
    | Sum.inr (Sum.inl tb) => cutoff tb.1 tb.2 ≤ fullBallCount ω ball tb.1 tb.2
    | Sum.inr (Sum.inr (Sum.inl c)) => markedCellCount ω c.val ≤ markedMean q c.val / 2
    | Sum.inr (Sum.inr (Sum.inr ca)) => markedMean q ca.1.val / 20 ≤ markedCapCount ω cap ca.1.val ca.2
  let rate : J → ℝ := fun j => match j with
    | Sum.inl t => 2 * Real.exp (-fullMean p t / 12)
    | Sum.inr (Sum.inl tb) => Real.exp (-cutoff tb.1 tb.2 / 4)
    | Sum.inr (Sum.inr (Sum.inl c)) => Real.exp (-markedMean q c.val / 8)
    | Sum.inr (Sum.inr (Sum.inr ca)) => Real.exp (-markedMean q ca.1.val / 8)
  have hbound : ∀ j, D.probability (bad j) ≤ rate j := by
    intro j
    rcases j with t | j
    · simpa [D, bad, rate] using coupled_test_concentration (flatten p) (flatten q)
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
  have hrates : (∑ j, rate j) = failureBudget (A := A) p q high cutoff := by
    simp only [rate, J, Fintype.sum_sum_type, Fintype.sum_prod_type, failureBudget]
    rw [← sum_subtype high (fun _ => Iff.rfl) (fun c : C => Real.exp (-markedMean q c / 8)),
      ← sum_subtype high (fun _ => Iff.rfl) (fun c : C => ∑ _a : A, Real.exp (-markedMean q c / 8))]
    ring
  have hprobs : (∑ j, D.probability (bad j)) < 1 := by
    calc
      (∑ j, D.probability (bad j)) ≤ ∑ j, rate j := sum_le_sum (fun j _ => hbound j)
      _ < 1 := by rwa [hrates]
  obtain ⟨ω, hpositive, hω⟩ := D.exists_positive_avoiding_of_probability_sum_lt_one bad hprobs
  have hdensity (t : T) : fullMean p t / 2 < fullTubeCount ω t ∧
      fullTubeCount ω t < 2 * fullMean p t := by
    simpa [bad, not_or, not_le] using hω (Sum.inl t)
  have hballs (t : T) (b : B) : fullBallCount ω ball t b < cutoff t b := by
    simpa [bad, not_le] using hω (Sum.inr (Sum.inl (t,b)))
  have hcells (c : C) (hc : c ∈ high) : markedMean q c / 2 < markedCellCount ω c := by
    simpa [bad, not_le] using hω (Sum.inr (Sum.inr (Sum.inl ⟨c,hc⟩)))
  have hcaps (c : C) (hc : c ∈ high) (a : A) : markedCapCount ω cap c a < markedMean q c / 20 := by
    simpa [bad, not_le] using hω (Sum.inr (Sum.inr (Sum.inr (⟨c,hc⟩,a))))
  have hsupport := coupled_positive_support (flatten p) (flatten q)
    (fun tc => hq tc.1 tc.2) (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2) ω hpositive
  refine ⟨ω, ?_⟩
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

/-- Capping retains valid probabilities, including zero weights. -/
def capped (scale w : ℝ) : ℝ := min 1 (scale * w)

theorem capped_probabilities {alpha beta w : ℝ}
    (hbeta : 0 ≤ beta) (hba : beta ≤ alpha) (hw : 0 ≤ w) :
    0 ≤ capped beta w ∧ capped beta w ≤ capped alpha w ∧ capped alpha w ≤ 1 := by
  refine ⟨le_min (by norm_num) (mul_nonneg hbeta hw), ?_, min_le_left _ _⟩
  exact min_le_min_left 1 (mul_le_mul_of_nonneg_right hba hw)


/-- Requested capped-weight specialization. Full and marked probabilities are
min(1,alpha*w) and min(1,beta*w), with 0≤beta≤alpha and w≥0. The resulting
full/marked finite sets are sampled with the coupled product law above. -/
theorem capped_sampling_assembly (w : T → C → ℝ) {alpha beta : ℝ}
    (hbeta : 0 ≤ beta) (hba : beta ≤ alpha) (hw : ∀ t c, 0 ≤ w t c)
    (high : Finset C) (ball : B → C → Bool) (cap : A → T → Bool) (cutoff : T → B → ℝ)
    (hball : ∀ t b, 4 * ballMean (fun t c => capped alpha (w t c)) ball t b ≤ cutoff t b)
    (hcap : ∀ c ∈ high, ∀ a, 1000 * capMean (fun t c => capped beta (w t c)) cap c a ≤
      markedMean (fun t c => capped beta (w t c)) c)
    (hhigh : (∑ c, markedMean (fun t c => capped beta (w t c)) c) / 2 ≤
      ∑ c ∈ high, markedMean (fun t c => capped beta (w t c)) c)
    (hbudget : failureBudget (A := A) (fun t c => capped alpha (w t c))
      (fun t c => capped beta (w t c)) high cutoff < 1) :
    ∃ ω : Outcome T C, SampleGood (fun t c => capped alpha (w t c))
      (fun t c => capped beta (w t c)) high ball cap cutoff ω := by
  apply finite_sampling_assembly _ _
    (fun t c => (capped_probabilities hbeta hba (hw t c)).1)
    (fun t c => (capped_probabilities hbeta hba (hw t c)).2.1)
    (fun t c => (capped_probabilities hbeta hba (hw t c)).2.2)
    high ball cap cutoff hball hcap hhigh hbudget

omit [Fintype B] [Fintype A] [DecidableEq T] in
/-- The numerical density normalization in (6.7) and marked/full mass ratio
in (6.9). Here r denotes lambda*N. All counts are actual shading cardinalities. -/
theorem SampleGood.density_normalization {p q : T → C → ℝ} {high : Finset C}
    {ball : B → C → Bool} {cap : A → T → Bool} {cutoff : T → B → ℝ} {ω : Outcome T C}
    (good : SampleGood p q high ball cap cutoff ω) {c0 C0 r xi : ℝ}
    (hC0 : 0 < C0) (hxi : 0 ≤ xi)
    (hmean : ∀ t, c0 * r ≤ fullMean p t ∧ fullMean p t ≤ C0 * r)
    (hmarked : xi * r * (Fintype.card T : ℝ) ≤ ∑ c, markedMean q c) :
    (∀ t, c0 * r / 2 ≤ (fullShading ω t).card ∧
      ((fullShading ω t).card : ℝ) ≤ 2 * C0 * r) ∧
    xi / (8 * C0) * (∑ t, ((fullShading ω t).card : ℝ)) ≤
      ∑ t, ((markedShading high ω t).card : ℝ) := by
  constructor
  · intro t
    have hg := good.density t
    have hm := hmean t
    constructor <;> linarith
  · have hmeans : (∑ t, fullMean p t) ≤ (Fintype.card T : ℝ) * (C0 * r) := by
      calc
        (∑ t, fullMean p t) ≤ ∑ _t : T, C0 * r := sum_le_sum (fun t _ => (hmean t).2)
        _ = (Fintype.card T : ℝ) * (C0 * r) := by simp
    have hfull : (∑ t, ((fullShading ω t).card : ℝ)) ≤ 2 * (Fintype.card T : ℝ) * C0 * r := by
      nlinarith [good.full_mass]
    have hret : xi * r * (Fintype.card T : ℝ) / 4 ≤
        ∑ t, ((markedShading high ω t).card : ℝ) := by linarith [good.marked_mass]
    have hm := mul_le_mul_of_nonneg_left hfull (div_nonneg hxi (by positivity : 0 ≤ 8 * C0))
    have heq : xi / (8 * C0) * (2 * (Fintype.card T : ℝ) * C0 * r) =
        xi * r * (Fintype.card T : ℝ) / 4 := by field_simp; ring
    rw [heq] at hm
    exact hm.trans hret

omit [Fintype B] [Fintype A] [DecidableEq T] in
/-- Dividing the ball threshold by the retained full count gives a relative
two-ends-type bound; the actual geometric factor is an explicit nonnegative input. -/
theorem SampleGood.relative_ball_bound {p q : T → C → ℝ} {high : Finset C}
    {ball : B → C → Bool} {cap : A → T → Bool} {cutoff : T → B → ℝ} {ω : Outcome T C}
    (good : SampleGood p q high ball cap cutoff ω) (factor : T → B → ℝ)
    (hfactor : ∀ t b, 0 ≤ factor t b)
    (hcutoff : ∀ t b, cutoff t b ≤ factor t b * fullMean p t) :
    ∀ t b, fullBallCount ω ball t b ≤ 2 * factor t b * (fullShading ω t).card := by
  intro t b
  have hdensity := (good.density t).1
  have hmult := mul_le_mul_of_nonneg_left hdensity (hfactor t b)
  have hball := good.ball_upper t b
  have hcut := hcutoff t b
  nlinarith

end
end KakeyaSamplingApplication

-- Kernel dependency checks for every exported theorem.
#print axioms KakeyaSamplingApplication.tube_test_mean
#print axioms KakeyaSamplingApplication.cell_test_mean
#print axioms KakeyaSamplingApplication.ball_test_mean
#print axioms KakeyaSamplingApplication.cap_test_mean
#print axioms KakeyaSamplingApplication.tube_test_count
#print axioms KakeyaSamplingApplication.cell_test_count
#print axioms KakeyaSamplingApplication.ball_test_count
#print axioms KakeyaSamplingApplication.cap_test_count
#print axioms KakeyaSamplingApplication.markedShading_subset
#print axioms KakeyaSamplingApplication.fullTubeCount_eq_card
#print axioms KakeyaSamplingApplication.marked_total_identity
#print axioms KakeyaSamplingApplication.failureBudget_le_uniform
#print axioms KakeyaSamplingApplication.finite_sampling_assembly
#print axioms KakeyaSamplingApplication.capped_probabilities
#print axioms KakeyaSamplingApplication.capped_sampling_assembly
#print axioms KakeyaSamplingApplication.SampleGood.density_normalization
#print axioms KakeyaSamplingApplication.SampleGood.relative_ball_bound
