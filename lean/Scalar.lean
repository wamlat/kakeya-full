import Mathlib

/-!
# Scalar verification for `kakeya_combined (1).pdf`, 5 September 2026

This file verifies algebra, scalar induction, limiting exponents, and density-power
comparisons. It does NOT assert the geometric Kakeya implication (1.7), or any
Kakeya theorem. Analytic inputs must be proved separately. No `sorry`, `admit`,
custom axioms, or `native_decide` are used.

Checked with Lean 4.33.1 and Mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474.
-/

namespace KakeyaScalar
open Filter
open scoped Topology

noncomputable section

def pivotSet (m d' : ℝ) : ℝ := (2 * m + 3 + d') / 4
def pivotDensity (p q : ℝ) : ℝ := (p + 2 * q + 4) / 4

def slope : ℕ → ℝ
  | 0 => 1 / 2
  | j + 1 => (2 + slope j ^ 2) / 4

def slopeLimit : ℝ := 2 - Real.sqrt 2
def profile (j : ℕ) (m : ℝ) : ℝ := 3 + slope j * (m - 3)
def envelope (j : ℕ) (m : ℝ) : ℝ := max (profile j m) 4
def limitProfile (m : ℝ) : ℝ := 3 + slopeLimit * (m - 3)

theorem slopeLimit_bounds : (1 : ℝ) / 2 < slopeLimit ∧ slopeLimit < 1 := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  dsimp [slopeLimit]
  constructor <;> nlinarith

theorem slopeLimit_fixed : (2 + slopeLimit ^ 2) / 4 = slopeLimit := by
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  dsimp [slopeLimit]
  nlinarith

theorem slope_bounds (j : ℕ) : (1 : ℝ) / 2 ≤ slope j ∧ slope j < slopeLimit := by
  induction j with
  | zero => simpa [slope] using And.intro (le_refl ((1 : ℝ) / 2)) slopeLimit_bounds.1
  | succ j ih =>
    rw [slope]
    constructor
    · nlinarith [sq_nonneg (slope j)]
    · have hpos : 0 < slopeLimit + slope j := by linarith [slopeLimit_bounds.1]
      have hmul := mul_pos (sub_pos.mpr ih.2) hpos
      nlinarith [slopeLimit_fixed]

theorem slope_step_strict (j : ℕ) : slope j < slope (j + 1) := by
  have hb := slope_bounds j
  have hlim := slopeLimit_bounds
  have hp := mul_pos (sub_pos.mpr hb.2)
    (show 0 < 4 - slopeLimit - slope j by linarith)
  rw [slope]
  nlinarith [slopeLimit_fixed]

theorem slope_strictMono : StrictMono slope := strictMono_nat_of_lt_succ slope_step_strict

theorem slope_error_identity (j : ℕ) :
    slopeLimit - slope (j + 1) =
      (slopeLimit - slope j) * (slopeLimit + slope j) / 4 := by
  rw [slope]
  nlinarith [slopeLimit_fixed]

/-- An explicit geometric bound, stronger than merely existence of the limit. -/
theorem slope_error_bound (j : ℕ) :
    0 ≤ slopeLimit - slope j ∧
      slopeLimit - slope j ≤ ((1 : ℝ) / 2) ^ j * (slopeLimit - 1 / 2) := by
  constructor
  · exact sub_nonneg.mpr (le_of_lt (slope_bounds j).2)
  · induction j with
    | zero => simp [slope]
    | succ j ih =>
      rw [slope_error_identity, pow_succ]
      have hb := slope_bounds j
      have hr := slopeLimit_bounds
      have he : 0 ≤ slopeLimit - slope j := by linarith
      have hs : slopeLimit + slope j ≤ 2 := by linarith
      have hm := mul_le_mul_of_nonneg_left hs he
      nlinarith

theorem slope_tendsto : Tendsto slope atTop (𝓝 slopeLimit) := by
  have hz : Tendsto (fun j : ℕ => slopeLimit - slope j) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => (slope_error_bound j).1)
      (fun j => (slope_error_bound j).2)
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 < 1 by norm_num)
    simpa using hp.mul_const (slopeLimit - 1 / 2)
  have ht := hz.const_sub slopeLimit
  simpa using ht

theorem profile_tendsto (m : ℝ) :
    Tendsto (fun j => profile j m) atTop (𝓝 (limitProfile m)) := by
  exact tendsto_const_nhds.add (slope_tendsto.mul_const (m - 3))

theorem profile_composition (j : ℕ) (m : ℝ) :
    profile j (profile j m) = 3 + slope j ^ 2 * (m - 3) := by
  simp only [profile]
  ring

theorem profile_pivot (j : ℕ) (m : ℝ) :
    pivotSet m (profile j (profile j m)) = profile (j + 1) m := by
  simp only [pivotSet, profile, slope]
  ring

theorem profile_seed (m : ℝ) : profile 0 m = (m + 3) / 2 := by
  simp only [profile, slope]
  ring

/-- Every finite profile invocation lies inside the strict domain stated in (1.7). -/
theorem profile_domain (j : ℕ) {m : ℝ} (hm : 3 < m) :
    3 < profile j (profile j m) ∧
    profile j (profile j m) < profile j m ∧
    profile j m < profile (j + 1) m ∧ profile (j + 1) m < m := by
  have hb := slope_bounds j
  have hn := slope_bounds (j + 1)
  have hl := slopeLimit_bounds
  have ha : 0 < slope j := by linarith
  have ha1 : slope j < 1 := lt_trans hb.2 hl.2
  have hm' : 0 < m - 3 := sub_pos.mpr hm
  have hh : 0 < slope j * (m - 3) := mul_pos ha hm'
  have hsmall := mul_lt_mul_of_pos_right ha1 hh
  have hstep := mul_lt_mul_of_pos_right (slope_step_strict j) hm'
  have hnsmall := mul_lt_mul_of_pos_right (lt_trans hn.2 hl.2) hm'
  have hdouble := mul_pos ha hh
  simp only [profile]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Universal domain check for the formal set-exponent map. -/
theorem pivot_set_domain {m d d' : ℝ} (h1 : 3 < d') (h2 : d' < d) (h3 : d < m) :
    3 < pivotSet m d' ∧ pivotSet m d' < m := by
  dsimp [pivotSet]
  constructor <;> linarith

/-- The elementary inequality that closes the density envelope. -/
theorem density_envelope_bound {p q P : ℝ}
    (hp : p ≤ P) (hq : q ≤ P) (h4 : 4 ≤ P) : pivotDensity p q ≤ P := by
  dsimp [pivotDensity]
  linarith

theorem profile_density_closure (j : ℕ) {m : ℝ} (hm : 3 < m) :
    max (pivotSet m (profile j (profile j m)))
      (pivotDensity (envelope j m) (envelope j (profile j m))) ≤ envelope (j + 1) m := by
  have hd := profile_domain j hm
  have hp : envelope j m ≤ envelope (j + 1) m :=
    max_le_max hd.2.2.1.le le_rfl
  have hq : envelope j (profile j m) ≤ envelope (j + 1) m :=
    max_le_max (le_trans hd.2.1.le hd.2.2.1.le) le_rfl
  rw [profile_pivot]
  exact max_le (le_max_left _ _) (density_envelope_bound hp hq (le_max_right _ _))

/-- Conditional logical formalization of Section 9.2. The unproved analytic seed,
density weakening, and pivot implication are explicit hypotheses, not axioms.
No geometric meaning is assigned to K here. -/
theorem conditional_real_cap_iteration
    (K : ℝ → ℝ → ℝ → Prop)
    (seed : ∀ m : ℝ, 3 < m → K m ((m+3)/2) ((m+3)/2))
    (weaken : ∀ m d p p' : ℝ, p ≤ p' → K m d p → K m d p')
    (pivot : ∀ m d d' p q : ℝ,
      3 < d' → d' < d → d < m → d ≤ p → d' ≤ q →
      K m d p → K d d' q →
      K m (pivotSet m d') (max (pivotSet m d') (pivotDensity p q))) :
    ∀ j : ℕ, ∀ m : ℝ, 3 < m → K m (profile j m) (envelope j m) := by
  intro j
  induction j with
  | zero =>
    intro m hm
    apply weaken m (profile 0 m) (profile 0 m) (envelope 0 m) (le_max_left _ _)
    simpa only [profile_seed] using seed m hm
  | succ j ih =>
    intro m hm
    have hd := profile_domain j hm
    have hdm : profile j m < m := lt_trans hd.2.2.1 hd.2.2.2
    have h3d : 3 < profile j m := lt_trans hd.1 hd.2.1
    have hk := pivot m (profile j m) (profile j (profile j m))
      (envelope j m) (envelope j (profile j m)) hd.1 hd.2.1 hdm
      (le_max_left _ _) (le_max_left _ _) (ih m hm) (ih (profile j m) h3d)
    have hw := weaken m (pivotSet m (profile j (profile j m)))
      (max (pivotSet m (profile j (profile j m)))
        (pivotDensity (envelope j m) (envelope j (profile j m))))
      (envelope (j+1) m) (profile_density_closure j hm) hk
    simpa only [profile_pivot] using hw

theorem profile_below_limit (j : ℕ) {m : ℝ} (hm : 3 < m) :
    profile j m < limitProfile m := by
  dsimp [profile, limitProfile]
  nlinarith [mul_lt_mul_of_pos_right (slope_bounds j).2 (sub_pos.mpr hm)]

theorem envelope_below_limit (j : ℕ) {m : ℝ} (hm : 3 < m) :
    envelope j m ≤ max (limitProfile m) 4 :=
  max_le_max (profile_below_limit j hm).le le_rfl

/-- Raising the density power weakens the estimate for densities at most one. -/
theorem limiting_density_comparison (j : ℕ) {m lam : ℝ}
    (hm : 3 < m) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    lam ^ (max (limitProfile m) 4) ≤ lam ^ (envelope j m) :=
  Real.rpow_le_rpow_of_exponent_ge hlam hlam1 (envelope_below_limit j hm)

theorem limit_diagonal_for_n_ge_six {n : ℝ} (hn : 6 ≤ n) :
    4 < limitProfile (n - 1) := by
  have hr := slopeLimit_bounds
  have hp := mul_le_mul_of_nonneg_left (show 2 ≤ n - 1 - 3 by linarith)
    (show 0 ≤ slopeLimit by linarith)
  dsimp [limitProfile]
  nlinarith

theorem dimension_five_envelope_is_four : max (limitProfile 4) 4 = 4 := by
  apply max_eq_right
  dsimp [limitProfile]
  linarith [slopeLimit_bounds.2]

/-- No density envelope below 4 closes the worst case p=q=P. -/
theorem diagonal_envelope_obstruction {P : ℝ} (hP : P < 4) :
    P < pivotDensity P P := by
  dsimp [pivotDensity]
  linarith

/-- Exact table entries in Section 9.2. -/
theorem slope_first_values :
    slope 0 = 1/2 ∧ slope 1 = 9/16 ∧ slope 2 = 593/1024 ∧
    slope 3 = 2448801/4194304 := by norm_num [slope]

theorem dimension_six_first_values :
    profile 0 5 = 4 ∧ profile 1 5 = 33/8 ∧ profile 2 5 = 2129/512 ∧
    profile 3 5 = 8740257/2097152 := by norm_num [profile, slope]

theorem dimension_eight_first_values :
    profile 0 7 = 5 ∧ profile 1 7 = 21/4 ∧ profile 2 7 = 1361/256 ∧
    profile 3 7 = 5594529/1048576 := by norm_num [profile, slope]

theorem dimension_six_limit : limitProfile 5 = 7 - 2 * Real.sqrt 2 := by
  dsimp [limitProfile, slopeLimit]; ring

theorem dimension_eight_limit : limitProfile 7 = 11 - 4 * Real.sqrt 2 := by
  dsimp [limitProfile, slopeLimit]; ring

/-- (9.1), with the fractional Wolff lifted input. -/
theorem wolff_substitution (n d : ℝ) :
    pivotSet (n - 1) ((d + 3) / 2) = (4*n + d + 5)/8 ∧
    pivotDensity d ((d + 3) / 2) = (2*d + 7)/4 ∧
    (4*n + d + 5)/8 - (2*d + 7)/4 = (4*n - 3*d - 9)/8 ∧
    (n+2)/2 - (4*n+d+5)/8 + (((2*d+7)/4)-2)/3 = (d+7)/24 := by
  dsimp [pivotSet, pivotDensity]
  and_intros <;> ring

/-- Appendix A.2: the bush substitution, including the angular margin. -/
theorem bush_substitution (n d : ℝ) :
    pivotSet (n - 1) ((d + 2) / 2) = (4*n + d + 4)/8 ∧
    pivotDensity d ((d + 2) / 2) = (d + 3)/2 ∧
    (4*n + d + 4)/8 - (d + 3)/2 = (4*n - 3*d - 8)/8 ∧
    (n+2)/2 - (4*n+d+4)/8 + (((d+3)/2)-2)/3 = (d+8)/24 := by
  dsimp [pivotSet, pivotDensity]
  and_intros <;> ring

/-- Appendix A.3: weakening only the lifted set exponent preserves the density cost. -/
theorem weakened_bush_substitution (n d : ℝ) :
    pivotSet (n - 1) ((d + 1) / 2) = (4*n + d + 3)/8 ∧
    pivotDensity d ((d + 2) / 2) = (d + 3)/2 ∧
    (n+2)/2 - (4*n+d+3)/8 + (((d+3)/2)-2)/3 = (d+11)/24 := by
  dsimp [pivotSet, pivotDensity]
  and_intros <;> ring

/-- All three affine iterations (offset c = 5, 4, 3). -/
def diagonal (n c seed : ℝ) : ℕ → ℝ
  | 0 => seed
  | j+1 => (4*n + c + diagonal n c seed j)/8

def diagonalLimit (n c : ℝ) : ℝ := (4*n+c)/7

theorem diagonal_closed_form (n c seed : ℝ) (j : ℕ) :
    diagonal n c seed j = diagonalLimit n c +
      (seed - diagonalLimit n c) * ((1:ℝ)/8)^j := by
  induction j with
  | zero => simp [diagonal]
  | succ j ih => rw [diagonal, ih, pow_succ]; dsimp [diagonalLimit]; ring

theorem diagonal_tendsto (n c seed : ℝ) :
    Tendsto (diagonal n c seed) atTop (𝓝 (diagonalLimit n c)) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0:ℝ) ≤ 1/8 by norm_num) (show (1:ℝ)/8 < 1 by norm_num)
  have ht := (tendsto_const_nhds (x := diagonalLimit n c)).add (hp.const_mul (seed - diagonalLimit n c))
  simpa only [mul_zero, add_zero, ← diagonal_closed_form] using ht

theorem diagonal_monotone_and_bounds {n c seed : ℝ}
    (hs : seed < diagonalLimit n c) (j : ℕ) :
    seed ≤ diagonal n c seed j ∧ diagonal n c seed j < diagonalLimit n c ∧
    diagonal n c seed j < diagonal n c seed (j+1) := by
  have hd : diagonal n c seed j < diagonalLimit n c := by
    rw [diagonal_closed_form]
    have hp : (0:ℝ) < (1/8)^j := pow_pos (by norm_num) _
    nlinarith [mul_neg_of_neg_of_pos (sub_neg.mpr hs) hp]
  have hinc : diagonal n c seed j < diagonal n c seed (j+1) := by
    rw [diagonal]
    dsimp [diagonalLimit] at hd
    linarith
  refine ⟨?_, hd, hinc⟩
  rw [diagonal_closed_form]
  have hp : ((1:ℝ)/8)^j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonpos_left hp (sub_nonpos.mpr hs.le)
  nlinarith

theorem diagonal_six_table :
    diagonal 6 5 4 1 = 33/8 ∧ diagonal 6 5 4 2 = 265/64 ∧
    diagonalLimit 6 5 = 29/7 := by norm_num [diagonal, diagonalLimit]

theorem diagonal_eight_table :
    diagonal 8 5 5 1 = 21/4 ∧ diagonal 8 5 5 2 = 169/32 ∧
    diagonalLimit 8 5 = 37/7 := by norm_num [diagonal, diagonalLimit]

theorem wolff_diagonal_six_domain {d : ℝ} (hlo : 4 ≤ d) (hhi : d ≤ 29/7) :
    (2*d+7)/4 < (4*6+d+5)/8 ∧ (4*6+d+5)/8 < 6-1 ∧
      0 < (d+7)/24 := by constructor <;> (try constructor) <;> linarith

theorem wolff_diagonal_eight_domain {d : ℝ} (hlo : 5 ≤ d) (hhi : d ≤ 37/7) :
    (2*d+7)/4 < (4*8+d+5)/8 ∧ (4*8+d+5)/8 < 8-1 ∧
      0 < (d+7)/24 := by constructor <;> (try constructor) <;> linarith

theorem bush_diagonal_domain {n d : ℝ} (hn : 5 ≤ n)
    (hlo : (n+1)/2 ≤ d) (hhi : d ≤ (4*n+4)/7) :
    1 < d ∧ d < n-1 ∧ 2 ≤ (d+2)/2 ∧ 2 < (d+3)/2 ∧
    (d+3)/2 < (4*n+d+4)/8 ∧ (4*n+d+4)/8 < n-1 ∧ 0 < (d+8)/24 := by
  and_intros <;> linarith

theorem weakened_bush_diagonal_domain {n d : ℝ} (hn : 5 ≤ n)
    (hlo : (n+1)/2 ≤ d) (hhi : d ≤ (4*n+3)/7) :
    1 < d ∧ d < n-1 ∧ 2 ≤ (d+2)/2 ∧ 2 < (d+3)/2 ∧
    (d+3)/2 < (4*n+d+3)/8 ∧ (4*n+d+3)/8 < n-1 ∧ 0 < (d+11)/24 := by
  and_intros <;> linarith

theorem bush_improvement_threshold (n : ℝ) :
    (4*n+4)/7 - (n+2)/2 = (n-6)/14 ∧
    (4*n+3)/7 - (n+2)/2 = (n-8)/14 := by constructor <;> ring

theorem six_model_constants :
    pivotSet 5 (7/2) = 33/8 ∧ pivotDensity 4 (7/2) = 15/4 ∧
    (6:ℝ) - 33/8 = 15/8 ∧ (15:ℝ)/4 < 33/8 ∧
    (6 - 29/7)/(29/7) = (13:ℝ)/29 ∧
    (8 - 37/7)/(37/7) = (19:ℝ)/37 := by
  norm_num [pivotSet, pivotDensity]

/-- Appendix B's finite maximization, encoded as attainment and an upper bound
for every eligible integer ell. This is the exact max-min specification. -/
def benchmarkCandidate (n ell : ℕ) : ℚ :=
  min ((n:ℚ) - ell + 2) (((n:ℚ)^2 + (ell:ℚ)^2 + n - ell)/(2*n))

def benchmarkCorrect (n : ℕ) (b : ℚ) : Prop :=
  (∃ ell : Fin (n+1), 2 ≤ ell.val ∧ benchmarkCandidate n ell.val = b) ∧
  (∀ ell : Fin (n+1), 2 ≤ ell.val → benchmarkCandidate n ell.val ≤ b)

theorem benchmark_five : benchmarkCorrect 5 (18/5) := by
  constructor
  · exact ⟨⟨3, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem benchmark_six : benchmarkCorrect 6 (4) := by
  constructor
  · exact ⟨⟨4, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem benchmark_seven : benchmarkCorrect 7 (34/7) := by
  constructor
  · exact ⟨⟨4, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem benchmark_eight : benchmarkCorrect 8 (21/4) := by
  constructor
  · exact ⟨⟨4, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem benchmark_nine : benchmarkCorrect 9 (6) := by
  constructor
  · exact ⟨⟨5, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem benchmark_ten : benchmarkCorrect 10 (13/2) := by
  constructor
  · exact ⟨⟨5, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem benchmark_eleven : benchmarkCorrect 11 (7) := by
  constructor
  · exact ⟨⟨6, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem benchmark_twelve : benchmarkCorrect 12 (31/4) := by
  constructor
  · exact ⟨⟨6, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem benchmark_thirteen : benchmarkCorrect 13 (106/13) := by
  constructor
  · exact ⟨⟨6, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem benchmark_fourteen : benchmarkCorrect 14 (9) := by
  constructor
  · exact ⟨⟨7, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem benchmark_fifteen : benchmarkCorrect 15 (47/5) := by
  constructor
  · exact ⟨⟨7, by norm_num⟩, by norm_num [benchmarkCandidate]⟩
  · intro ell h
    fin_cases ell <;> norm_num [benchmarkCandidate] at *

theorem sqrt_two_rational_bounds :
    (14142:ℝ)/10000 < Real.sqrt 2 ∧ Real.sqrt 2 < (14143:ℝ)/10000 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  constructor <;> nlinarith

/-- Every sign in Appendix B, including the dimension-five comparison only. -/
theorem benchmark_comparison_signs :
    limitProfile 4 < 18/5 ∧
    4 < limitProfile 5 ∧
    limitProfile 6 < 34/7 ∧
    21/4 < limitProfile 7 ∧
    limitProfile 8 < 6 ∧
    13/2 < limitProfile 9 ∧
    7 < limitProfile 10 ∧
    limitProfile 11 < 31/4 ∧
    106/13 < limitProfile 12 ∧
    limitProfile 13 < 9 ∧
    47/5 < limitProfile 14 := by
  have hs := sqrt_two_rational_bounds
  dsimp [limitProfile, slopeLimit]
  and_intros <;> linarith

/-- The listed adjoint thresholds r and maximal exponents B are conjugate. -/
theorem benchmark_adjoint_conversion :
    (18/5:ℚ)/((18/5)-1) = 18/13 ∧
    (4:ℚ)/(4-1) = 4/3 ∧
    (34/7:ℚ)/((34/7)-1) = 34/27 ∧
    (21/4:ℚ)/((21/4)-1) = 21/17 ∧
    (6:ℚ)/(6-1) = 6/5 ∧
    (13/2:ℚ)/((13/2)-1) = 13/11 ∧
    (7:ℚ)/(7-1) = 7/6 ∧
    (31/4:ℚ)/((31/4)-1) = 31/27 ∧
    (106/13:ℚ)/((106/13)-1) = 106/93 ∧
    (9:ℚ)/(9-1) = 9/8 ∧
    (47/5:ℚ)/((47/5)-1) = 47/42 := by norm_num

theorem six_conditioning_and_angular_constants :
    (5:ℝ)*(6-1) + 6*(7/2) + 12 = 58 ∧
    (4:ℝ)*(33/8) = 33/2 ∧
    (4:ℝ)*(15/4) = 15 ∧
    (4:ℝ) - 33/8 + ((15/4)-2)/3 = 11/24 ∧
    (33/8:ℝ)-5+1/4 = -5/8 ∧
    (33/8:ℝ)-15/4 = 3/8 := by norm_num

end
end KakeyaScalar
