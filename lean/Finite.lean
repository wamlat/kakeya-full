import Mathlib

/-!
Finite combinatorial verification accompanying `kakeya_combined (1).pdf`.

Every result below is an unconditional theorem about finite sums of real numbers,
or a theorem conditional on the explicitly displayed analytic/support bounds.
No geometry of tubes, broadness decomposition, cap selection, lifting, geometric
support count, analytic Kakeya estimate, or asymptotic dyadic-bin count is proved.
The parameter `r : ℝ` really is real; the convexity results are not restricted to
integer exponents. See the accompanying audit for the scope of each theorem.
-/

namespace KakeyaFinite

open Finset
open scoped BigOperators

/-- Weighted convexity with arbitrary total weight. This is the precise
no-loss-in-the-number-of-groups step in (5.27). Zero weights are permitted. -/
theorem weighted_power {ι : Type*} (s : Finset ι) (w x : ι → ℝ)
    {Q r : ℝ} (hQ : 0 < Q) (hr : 1 ≤ r)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hx : ∀ i ∈ s, 0 ≤ x i)
    (hsum : ∑ i ∈ s, w i = Q) :
    Q * ((∑ i ∈ s, w i * x i) / Q) ^ r ≤ ∑ i ∈ s, w i * x i ^ r := by
  have hn : ∑ i ∈ s, w i / Q = 1 := by rw [← sum_div, hsum, div_self hQ.ne']
  have hj := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => w i / Q) x
    (fun i hi => div_nonneg (hw i hi) hQ.le) hn hx hr
  have hleft : (∑ i ∈ s, w i / Q * x i) = (∑ i ∈ s, w i * x i) / Q := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    ring
  have hright : (∑ i ∈ s, w i / Q * x i ^ r) =
      (∑ i ∈ s, w i * x i ^ r) / Q := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hleft, hright] at hj
  have := (le_div_iff₀ hQ).mp hj
  nlinarith

/-- A cumulative-density bound from finitely many comparable-density bins.
All bins' unions lie in a common union of size `U`; `a` is the analytic prefactor.
The result costs exactly the number of bins. The bin-density weighted mean need
only be at least `rho`, so dyadic lower endpoints can be used with a factor 2.
In contrast to applying pigeonhole to incidence alone, this keeps the same real
power `r` and introduces no extra logarithmic power. -/
theorem cumulative_from_bins {ι : Type*} (bins : Finset ι) (w density : ι → ℝ)
    {Q rho r a U : ℝ} (hQ : 0 < Q) (hrho : 0 ≤ rho) (hr : 1 ≤ r)
    (ha : 0 ≤ a) (hw : ∀ i ∈ bins, 0 ≤ w i)
    (hdensity : ∀ i ∈ bins, 0 ≤ density i)
    (hsum : ∑ i ∈ bins, w i = Q)
    (hmass : rho * Q ≤ ∑ i ∈ bins, w i * density i)
    (hbound : ∀ i ∈ bins, a * (w i * density i ^ r) ≤ U) :
    a * (Q * rho ^ r) ≤ (bins.card : ℝ) * U := by
  have hmean : rho ≤ (∑ i ∈ bins, w i * density i) / Q :=
    (le_div_iff₀ hQ).mpr hmass
  have hp := Real.rpow_le_rpow hrho hmean (by linarith : 0 ≤ r)
  have hwtd := weighted_power bins w density hQ hr hw hdensity hsum
  have htotal : Q * rho ^ r ≤ ∑ i ∈ bins, w i * density i ^ r :=
    (mul_le_mul_of_nonneg_left hp hQ.le).trans hwtd
  calc
    a * (Q * rho ^ r) ≤ a * ∑ i ∈ bins, w i * density i ^ r :=
      mul_le_mul_of_nonneg_left htotal ha
    _ = ∑ i ∈ bins, a * (w i * density i ^ r) := mul_sum ..
    _ ≤ ∑ i ∈ bins, U := sum_le_sum hbound
    _ = (bins.card : ℝ) * U := by simp

/-- Every positive integer count at most `B` belongs to a dyadic bin,
whose index is less than `log₂ B + 1`. In particular bin count depends on
maximum positive count, not on the possibly much smaller cumulative density. -/
theorem dyadic_bin_membership {n B : ℕ} (hn : 0 < n) (hB : n ≤ B) :
    2 ^ Nat.log 2 n ≤ n ∧ n < 2 ^ (Nat.log 2 n + 1) ∧
      Nat.log 2 n ∈ Finset.range (Nat.log 2 B + 1) := by
  refine ⟨Nat.pow_log_le_self 2 hn.ne', ?_, ?_⟩
  · exact (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hn.ne').mp (by omega)
  · exact Finset.mem_range.mpr (by have := Nat.log_mono_right hB (b := 2); omega)

/-- The nonempty truncation in (5.22) loses at most a factor two and remains
uniformly bounded by its input plus one, including inputs below one. -/
theorem nonempty_floor_truncation {x : ℝ} (hx : 0 ≤ x) :
    x / 2 ≤ (max 1 ⌊x⌋₊ : ℕ) ∧ ((max 1 ⌊x⌋₊ : ℕ) : ℝ) ≤ x + 1 := by
  have hlo : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hhi : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have h₁ : (1 : ℝ) ≤ ((max 1 ⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast (le_max_left 1 ⌊x⌋₊)
  have h₂ : (⌊x⌋₊ : ℝ) ≤ ((max 1 ⌊x⌋₊ : ℕ) : ℝ) := by exact_mod_cast (le_max_right 1 ⌊x⌋₊)
  constructor
  · by_cases hx₂ : x ≤ 2
    · linarith
    · linarith
  · rw [Nat.cast_max, Nat.cast_one]
    exact max_le (by linarith) (by linarith)

/-- If at most `D` mass is deleted, the surviving mass at points where less
than half the original multiplicity remains is at most `D`.
This is (3.8), with no geometric assumptions. -/
theorem proportional_bad_mass {ι : Type*} (s : Finset ι) (before after : ι → ℝ)
    (hsub : ∀ i ∈ s, after i ≤ before i) :
    (∑ i ∈ s, if 2 * after i < before i then after i else 0) ≤
      ∑ i ∈ s, (before i - after i) := by
  apply sum_le_sum
  intro i hi
  split_ifs with h
  · linarith
  · linarith [hsub i hi]

/-- The first proportional restoration retains at least `W - 2 D` good mass,
where `W` is original incidence mass and `D` is deleted incidence mass. -/
theorem proportional_good_mass {ι : Type*} (s : Finset ι) (before after : ι → ℝ)
    (hsub : ∀ i ∈ s, after i ≤ before i) :
    (∑ i ∈ s, before i) - 2 * (∑ i ∈ s, (before i - after i)) ≤
      ∑ i ∈ s, if before i ≤ 2 * after i then after i else 0 := by
  have hbad := proportional_bad_mass s before after hsub
  have hsplit : (∑ i ∈ s, if before i ≤ 2 * after i then after i else 0) +
      (∑ i ∈ s, if 2 * after i < before i then after i else 0) = ∑ i ∈ s, after i := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases h : before i ≤ 2 * after i
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  rw [sum_sub_distrib] at hbad ⊢
  linarith

/-- Second proportional restoration, now on pieces: if good mass totals at
least `W - 2 D` and surviving mass totals `W - D`, keeping only pieces with at
least half their surviving mass good retains at least `W - 3 D`, equation (3.10).
The actual finite deletion threshold is used; no assumed 'retained mass' bound
is hidden in the conclusion. -/
theorem retain_good_pieces {ι : Type*} (pieces : Finset ι) (surviving good : ι → ℝ)
    {W D : ℝ} (hsub : ∀ i ∈ pieces, good i ≤ surviving i)
    (hsurviving : ∑ i ∈ pieces, surviving i = W - D)
    (hgood : W - 2 * D ≤ ∑ i ∈ pieces, good i) :
    W - 3 * D ≤ ∑ i ∈ pieces,
      if surviving i ≤ 2 * good i then good i else 0 := by
  have hb := proportional_bad_mass pieces surviving good hsub
  have hsplit : (∑ i ∈ pieces, if surviving i ≤ 2 * good i then good i else 0) +
      (∑ i ∈ pieces, if 2 * good i < surviving i then good i else 0) =
      ∑ i ∈ pieces, good i := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    by_cases h : surviving i ≤ 2 * good i
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  rw [sum_sub_distrib, hsurviving] at hb
  linarith

/-- The quantitative constants claimed in (3.9)–(3.10). -/
theorem restoration_constants {W D retained₁ retained₂ : ℝ}
    (hD : D ≤ W / 8) (h₁ : W - 2 * D ≤ retained₁)
    (h₂ : W - 3 * D ≤ retained₂) :
    3 * W / 4 ≤ retained₁ ∧ 5 * W / 8 ≤ retained₂ := by constructor <;> linarith

/-- Full finite grouped pruning implication, (5.27)–(5.29).
`w` counts original lines of each (group,color), `density` is deleted incidence
mass divided by `N*w`, and `unions` counts their deleted-cell unions.
The two genuine input hypotheses are the per-color analytic lower bounds
`hanalytic` and the high-cell overlap bound `hupper`. The latter uses the
original mass `rho*N*Q`. No bound on the number of groups occurs. -/
theorem grouped_cutoff_retains_half {ι : Type*} (groups : Finset ι)
    (w density unions : ι → ℝ) {Q N rho r a J H : ℝ}
    (hQ : 0 < Q) (hN : 0 < N) (hrho : 0 < rho) (hr : 1 ≤ r)
    (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hw : ∀ i ∈ groups, 0 ≤ w i)
    (hdensity : ∀ i ∈ groups, 0 ≤ density i)
    (hsum : ∑ i ∈ groups, w i = Q)
    (hanalytic : ∀ i ∈ groups, a * (w i * density i ^ r) ≤ unions i)
    (hupper : H * (∑ i ∈ groups, unions i) ≤ J * (rho * N * Q))
    (hcalibrate : J * (rho * N * Q) < H * (a * (Q * (rho / 2) ^ r))) :
    N * (∑ i ∈ groups, w i * density i) < (rho * N * Q) / 2 := by
  by_contra h
  have hhigh : (rho * N * Q) / 2 ≤ N * (∑ i ∈ groups, w i * density i) :=
    le_of_not_gt h
  have hmass : (rho / 2) * Q ≤ ∑ i ∈ groups, w i * density i := by nlinarith
  have hmean : rho / 2 ≤ (∑ i ∈ groups, w i * density i) / Q :=
    (le_div_iff₀ hQ).mpr hmass
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ rho / 2) hmean
    (by linarith : 0 ≤ r)
  have hj := weighted_power groups w density hQ hr hw hdensity hsum
  have hanalyticSum : a * (∑ i ∈ groups, w i * density i ^ r) ≤
      ∑ i ∈ groups, unions i := by
    rw [mul_sum]
    exact sum_le_sum hanalytic
  have hlow : a * (Q * (rho / 2) ^ r) ≤ ∑ i ∈ groups, unions i := by
    exact (mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hp hQ.le).trans hj) ha).trans hanalyticSum
  have := mul_le_mul_of_nonneg_left hlow hH
  linarith

/-- An explicit sufficient cutoff calibration. With analytic prefactor `a`,
`H = 2^(r+1)*J*N/(a*rho^(r-1))` has a factor-two margin in the previous
lemma. For the PDF, substitute `a = c_e F⁻¹ N^(d'−d−e)` and `r = q+e`.
This yields exactly the rho and N powers displayed in (5.26). -/
theorem cutoff_calibration_identity {rho r a J N Q : ℝ}
    (hrho : 0 < rho) (ha : a ≠ 0) :
    ((2 : ℝ) ^ (r + 1) * J * N / (a * rho ^ (r - 1))) *
      (a * (Q * (rho / 2) ^ r)) = 2 * J * (rho * N * Q) := by
  rw [Real.div_rpow hrho.le (by norm_num), Real.rpow_sub hrho,
    Real.rpow_one, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hp : rho ^ r ≠ 0 := (Real.rpow_pos_of_pos hrho r).ne'
  have ht : (2 : ℝ) ^ r ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) r).ne'
  field_simp

/-- A bound on retained multiplicity gives the energy upper bound in (5.29). -/
theorem bounded_multiplicity_energy {ι : Type*} (s : Finset ι) (m : ι → ℝ)
    {H : ℝ} (hm : ∀ i ∈ s, 0 ≤ m i) (hH : ∀ i ∈ s, m i ≤ H) :
    (∑ i ∈ s, m i ^ 2) ≤ H * ∑ i ∈ s, m i := by
  rw [mul_sum]
  apply sum_le_sum
  intro i hi
  nlinarith [mul_nonneg (hm i hi) (sub_nonneg.mpr (hH i hi))]

/-- Counting occupied labels by their triple. A uniform per-triple support
bound `R` gives `#labels ≤ #triples * R`. Together with the next theorem,
this is the purely finite part of the triple/energy-position argument. -/
theorem support_card_by_fibers {α β : Type*} [DecidableEq β]
    (labels : Finset α) (triples : Finset β) (triple : α → β) {R : ℕ}
    (hmap : ∀ i ∈ labels, triple i ∈ triples)
    (hfiber : ∀ t ∈ triples, (labels.filter (fun i => triple i = t)).card ≤ R) :
    labels.card ≤ triples.card * R := by
  have hsum : ∑ t ∈ triples, (labels.filter (fun i => triple i = t)).card = labels.card := by
    simpa only [Finset.card_eq_sum_ones] using
      (Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1 : ℕ)))
  calc
    labels.card = ∑ t ∈ triples, (labels.filter (fun i => triple i = t)).card := hsum.symm
    _ ≤ ∑ t ∈ triples, R := sum_le_sum hfiber
    _ = triples.card * R := by simp

/-- The support-sensitive energy lower bound underlying (5.32).
`labels` indexes occupied (triple, energy-position) pairs and `position`
forgets the triple. Nonnegative weights count incidences on each occupied pair.
In particular, `B` counts occupied pair labels, not all possible ambient cells.
The geometric assertion `labels.card ≤ B` is an explicit hypothesis. -/
theorem finite_support_energy {α β : Type*} [Fintype β] [DecidableEq β]
    (labels : Finset α) (position : α → β) (weight : α → ℝ) {B : ℝ}
    (hw : ∀ i ∈ labels, 0 ≤ weight i) (hB : (labels.card : ℝ) ≤ B) :
    (∑ i ∈ labels, weight i) ^ 2 ≤
      B * ∑ p : β, (∑ i ∈ labels with position i = p, weight i) ^ 2 := by
  have hcs := sum_mul_sq_le_sq_mul_sq labels (fun _ => (1 : ℝ)) weight
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  have hag : (∑ i ∈ labels, weight i ^ 2) ≤
      ∑ p : β, (∑ i ∈ labels with position i = p, weight i) ^ 2 := by
    rw [← sum_fiberwise labels position (fun i => weight i ^ 2)]
    apply sum_le_sum
    intro p hp
    apply sum_sq_le_sq_sum_of_nonneg
    intro i hi
    exact hw i (mem_filter.mp hi).1
  have henergy : 0 ≤ ∑ p : β, (∑ i ∈ labels with position i = p, weight i) ^ 2 :=
    sum_nonneg fun p hp => sq_nonneg _
  exact hcs.trans ((mul_le_mul_of_nonneg_left hag (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hB henergy))

/-- Closing energy argument with all cardinality constants kept visible.
If support is bounded by `C * N * E²`, multiplicity by `H`, and incidence
mass is at least `I₀/2`, then `I₀ ≤ 2 C N H E²`. This is the finite/algebraic
part of passing from (5.29),(5.32) to (5.33). -/
theorem close_energy {I I₀ energy C N E H : ℝ}
    (hI : 0 < I) (hCN : 0 ≤ C * N)
    (hretained : I₀ / 2 ≤ I)
    (hlower : I ^ 2 ≤ (C * N * E ^ 2) * energy)
    (hupper : energy ≤ H * I) :
    I₀ ≤ 2 * C * N * H * E ^ 2 := by
  have hcoef : 0 ≤ C * N * E ^ 2 := mul_nonneg hCN (sq_nonneg E)
  have hboth := hlower.trans (mul_le_mul_of_nonneg_left hupper hcoef)
  have hcancel : I ≤ C * N * E ^ 2 * H := by nlinarith
  nlinarith

end KakeyaFinite

#print axioms KakeyaFinite.weighted_power
#print axioms KakeyaFinite.cumulative_from_bins
#print axioms KakeyaFinite.dyadic_bin_membership
#print axioms KakeyaFinite.nonempty_floor_truncation
#print axioms KakeyaFinite.proportional_bad_mass
#print axioms KakeyaFinite.proportional_good_mass
#print axioms KakeyaFinite.retain_good_pieces
#print axioms KakeyaFinite.restoration_constants
#print axioms KakeyaFinite.grouped_cutoff_retains_half
#print axioms KakeyaFinite.cutoff_calibration_identity
#print axioms KakeyaFinite.bounded_multiplicity_energy
#print axioms KakeyaFinite.support_card_by_fibers
#print axioms KakeyaFinite.finite_support_energy
#print axioms KakeyaFinite.close_energy
