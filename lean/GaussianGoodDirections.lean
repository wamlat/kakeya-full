import GaussianSmallBall
import GaussianMatrixMoments
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual good-direction events for one Gaussian matrix. The direction
counts use only the proved single-vector marginal law; no independence
between the different original directions is assumed. -/
namespace KakeyaFormal.GaussianGoodDirections
open MeasureTheory ProbabilityTheory GaussianMatrix GaussianLinearOperator
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- The actual original indices whose image is smaller than the cutoff. -/
def badIndices {rows cols M : ℕ} (v : Fin M → Space cols) (c : ℝ)
    (ω : Sample rows cols) : Finset (Fin M) :=
  Finset.univ.filter (fun i => ‖projection (v i) ω‖ < c)

/-- The complementary actual original indices, keeping equality at the cutoff. -/
def goodIndices {rows cols M : ℕ} (v : Fin M → Space cols) (c : ℝ)
    (ω : Sample rows cols) : Finset (Fin M) :=
  Finset.univ.filter (fun i => c ≤ ‖projection (v i) ω‖)

def badCount {rows cols M : ℕ} (v : Fin M → Space cols) (c : ℝ)
    (ω : Sample rows cols) : ℝ := (badIndices v c ω).card

theorem small_event_measurable {rows cols : ℕ} (v : Space cols) (c : ℝ) :
    MeasurableSet {ω : Sample rows cols | ‖projection v ω‖ < c} :=
  measurableSet_lt (projection v).measurable.norm measurable_const

/-- The dimension-power marginal bound is for the actual original matrix. -/
theorem small_event_bound {rows cols : ℕ} (v : Space cols) (hv : ‖v‖=1)
    {c : ℝ} (hc : 0 ≤ c) :
    (law rows cols).real {ω | ‖projection v ω‖ < c} ≤ (2*c)^rows := by
  have hball := GaussianSmallBall.closedBall_bound rows hc
  rw [← unit_image_law v hv,Measure.map_apply (projection v).measurable
    Metric.isClosed_closedBall.measurableSet] at hball
  have hsub : {ω : Sample rows cols | ‖projection v ω‖ < c} ⊆
      projection v ⁻¹' Metric.closedBall 0 c := by
    intro ω hω
    simpa only [Set.mem_preimage,Metric.mem_closedBall,dist_zero_right] using hω.le
  have hh := (measure_mono hsub).trans hball
  have ht := ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.ofReal_ne_top) |>.mpr hh
  simpa only [measureReal_def,ENNReal.toReal_ofReal (by positivity : 0 ≤ (2*c)^rows)] using ht

theorem badCount_sum {rows cols M : ℕ} (v : Fin M → Space cols) (c : ℝ)
    (ω : Sample rows cols) :
    badCount v c ω = ∑ i, ({ω : Sample rows cols | ‖projection (v i) ω‖ < c}).indicator
      (fun _ => (1:ℝ)) ω := by
  simp only [badCount,badIndices,Set.indicator_apply,Set.mem_ofPred_eq]
  rw [← Finset.sum_filter]
  simp

theorem badCount_measurable {rows cols M : ℕ} (v : Fin M → Space cols) (c : ℝ) :
    Measurable (badCount (rows:=rows) v c) := by
  have heq : badCount (rows:=rows) v c = fun ω => ∑ i,
      ({ω : Sample rows cols | ‖projection (v i) ω‖ < c}).indicator (fun _ => (1:ℝ)) ω :=
    funext (badCount_sum v c)
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator (small_event_measurable (v i) c)

theorem badCount_integrable {rows cols M : ℕ} (v : Fin M → Space cols) (c : ℝ) :
    Integrable (badCount v c) (law rows cols) := by
  have heq : badCount (rows:=rows) v c = fun ω => ∑ i,
      ({ω : Sample rows cols | ‖projection (v i) ω‖ < c}).indicator (fun _ => (1:ℝ)) ω :=
    funext (badCount_sum v c)
  rw [heq]
  exact integrable_finsetSum _ fun i _ => (integrable_const (1:ℝ)).indicator
    (small_event_measurable (v i) c)

/-- Linearity of expectation on the actual finite indicators, without a
joint independence premise or a cardinality-dependent constant. -/
theorem expected_badCount {rows cols M : ℕ} (v : Fin M → Space cols)
    (hv : ∀ i, ‖v i‖=1) {c : ℝ} (hc : 0 ≤ c) :
    (∫ ω, badCount v c ω ∂law rows cols) ≤ (M:ℝ)*(2*c)^rows := by
  simp_rw [badCount_sum]
  rw [integral_finsetSum _ (fun i _ => (integrable_const (1:ℝ)).indicator
    (small_event_measurable (v i) c))]
  calc
    _ = ∑ i, (law rows cols).real {ω | ‖projection (v i) ω‖ < c} := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_indicator_one (small_event_measurable (v i) c)
    _ ≤ ∑ _i : Fin M, (2*c)^rows := Finset.sum_le_sum fun i _ => small_event_bound (v i) (hv i) hc
    _ = _ := by simp

/-- Markov's inequality applied to the actual bad-index count. -/
theorem half_bad_probability {rows cols M : ℕ} (v : Fin M → Space cols)
    (hv : ∀ i, ‖v i‖=1) (hM : 0 < M) {c : ℝ} (hc : 0 ≤ c) :
    (law rows cols).real {ω | (M:ℝ)/2 ≤ badCount v c ω} ≤ 2*(2*c)^rows := by
  have hh := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (law rows cols) (fun ω => by dsimp [badCount]; positivity))
    (badCount_integrable v c) ((M:ℝ)/2)
  have he := expected_badCount (rows:=rows) v hv hc
  have hMp : 0 < (M:ℝ) := by exact_mod_cast hM
  nlinarith

/-- The explicit five-dimensional constant used before source (2.3). -/
theorem half_bad_probability_five {M : ℕ} (v : Fin M → Space 7)
    (hv : ∀ i, ‖v i‖=1) (hM : 0 < M) :
    (law 5 7).real {ω | (M:ℝ)/2 ≤ badCount v (1/4) ω} ≤ 1/16 := by
  have hh := half_bad_probability (rows:=5) v hv hM (by norm_num : (0:ℝ) ≤ 1/4)
  norm_num at hh ⊢
  exact hh

theorem bad_good_count {rows cols M : ℕ} (v : Fin M → Space cols) (c : ℝ)
    (ω : Sample rows cols) :
    badCount v c ω+((goodIndices v c ω).card:ℝ)=(M:ℝ) := by
  have hh := Finset.card_filter_add_card_filter_not (s:=Finset.univ)
    (fun i : Fin M => ‖projection (v i) ω‖ < c)
  have hn : (badIndices v c ω).card+(goodIndices v c ω).card=M := by
    simpa only [badIndices,goodIndices,not_lt,Finset.card_univ,Fintype.card_fin] using hh
  dsimp [badCount]
  exact_mod_cast hn

/-- Cardinality of the complementary actual row is a measurable function. -/
theorem goodCount_measurable {rows cols M : ℕ} (v : Fin M → Space cols) (c : ℝ) :
    Measurable (fun ω : Sample rows cols => ((goodIndices v c ω).card:ℝ)) := by
  have heq : (fun ω : Sample rows cols => ((goodIndices v c ω).card:ℝ)) =
      fun ω => (M:ℝ)-badCount v c ω := by
    funext ω
    linarith [bad_good_count v c ω]
  rw [heq]
  exact measurable_const.sub (badCount_measurable v c)

/-- The literal event used in the projection argument: the same matrix is
bounded and at least half of the original indexed directions have large image. -/
def goodEvent {M : ℕ} (v : Fin M → Space 7) : Set (Sample 5 7) :=
  {ω | ‖operator ω‖ ≤ 20 ∧ (M:ℝ)/2 ≤ ((goodIndices v (1/4) ω).card:ℝ)}

theorem goodEvent_measurable {M : ℕ} (v : Fin M → Space 7) :
    MeasurableSet (goodEvent v) :=
  (measurableSet_le (operator_measurable 5 7).norm measurable_const).inter
    (measurableSet_le measurable_const (goodCount_measurable v (1/4)))

/-- The exact half-count failure event is disabled for the empty family,
where every matrix already retains at least half the directions. -/
def countFailure {M : ℕ} (v : Fin M → Space 7) : Set (Sample 5 7) :=
  {ω | 0 < M ∧ (M:ℝ)/2 ≤ badCount v (1/4) ω}

theorem countFailure_measurable {M : ℕ} (v : Fin M → Space 7) :
    MeasurableSet (countFailure v) := by
  by_cases hM : 0 < M
  · simpa only [countFailure,hM,true_and] using
      measurableSet_le measurable_const (badCount_measurable (rows:=5) v (1/4))
  · simp [countFailure,hM]

theorem countFailure_bound {M : ℕ} (v : Fin M → Space 7) (hv : ∀ i, ‖v i‖=1) :
    (law 5 7).real (countFailure v) ≤ 1/16 := by
  by_cases hM : 0 < M
  · simpa only [countFailure,hM,true_and] using half_bad_probability_five v hv hM
  · simp [countFailure,hM]

/-- A positive-probability statement for the ACTUAL Gaussian five-by-seven
matrix and all the given directions simultaneously. The union estimate is
17/20, stronger than the three-quarter budget requested in the source proof. -/
theorem good_probability {M : ℕ} (v : Fin M → Space 7) (hv : ∀ i, ‖v i‖=1) :
    (17/20:ℝ) ≤ (law 5 7).real (goodEvent v) := by
  let E : Set (Sample 5 7) := {ω | (20:ℝ) ≤ ‖operator ω‖} ∪ countFailure v
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_const (operator_measurable 5 7).norm).union
      (countFailure_measurable v)
  have hbad : (law 5 7).real E ≤ 3/20 := by
    have hh := measureReal_union_le (μ:=law 5 7)
      {ω | (20:ℝ) ≤ ‖operator ω‖} (countFailure v)
    have htail := GaussianMatrixMoments.five_by_seven_tail
    have hcount := countFailure_bound v hv
    dsimp [E]
    linarith
  have hsub : Eᶜ ⊆ goodEvent v := by
    intro ω hω
    have hfail : ¬ (20:ℝ) ≤ ‖operator ω‖ ∧ ¬ ω∈countFailure v := by
      simpa only [E,Set.mem_compl_iff,Set.mem_union,Set.mem_ofPred_eq,not_or] using hω
    refine ⟨(lt_of_not_ge hfail.1).le,?_⟩
    by_cases hM : 0 < M
    · have hh : ¬ (M:ℝ)/2 ≤ badCount v (1/4) ω := by
        intro hh
        exact hfail.2 ⟨hM,hh⟩
      linarith [bad_good_count v (1/4) ω]
    · have hz : M=0 := Nat.eq_zero_of_not_pos hM
      have hzero : (M:ℝ)=0 := by exact_mod_cast hz
      rw [hzero,zero_div]
      exact Nat.cast_nonneg _
  have hm := measureReal_mono hsub (measure_ne_top (law 5 7) _)
  rw [measureReal_compl hE,probReal_univ] at hm
  linarith

/-- The advertised absolute positive probability is therefore available. -/
theorem good_probability_three_quarters {M : ℕ} (v : Fin M → Space 7)
    (hv : ∀ i, ‖v i‖=1) :
    (3/4:ℝ) ≤ (law 5 7).real (goodEvent v) := by
  have hh := good_probability v hv
  linarith

/-- Existence includes the actual retained original-index set and its
pointwise image lower bound, without any event or count oracle. -/
theorem exists_good_matrix {M : ℕ} (v : Fin M → Space 7) (hv : ∀ i, ‖v i‖=1) :
    ∃ ω : Sample 5 7, ‖operator ω‖ ≤ 20 ∧
      (M:ℝ)/2 ≤ ((goodIndices v (1/4) ω).card:ℝ) ∧
      ∀ i ∈ goodIndices v (1/4) ω, (1/4:ℝ) ≤ ‖operator ω (v i)‖ := by
  have hne : (goodEvent v).Nonempty := by
    by_contra hh
    have hz := Set.not_nonempty_iff_eq_empty.mp hh
    have hp := good_probability v hv
    rw [hz,measureReal_empty] at hp
    norm_num at hp
  obtain ⟨ω,hω⟩ := hne
  refine ⟨ω,hω.1,hω.2,?_⟩
  intro i hi
  exact (Finset.mem_filter.mp hi).2

end
end KakeyaFormal.GaussianGoodDirections
