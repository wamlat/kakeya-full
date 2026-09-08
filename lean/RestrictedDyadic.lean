import RestrictedInterpolation
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Uniform distribution bounds for actual finite disjoint dyadic inputs.
The dyadic cutoff and normalized geometric budget are constructed explicitly. -/
namespace KakeyaFormal.RestrictedInterpolation
open Finset MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
open Classical

def decayRatio (γ : ℝ) : ℝ≥0 := (2:ℝ≥0)^(-γ)

theorem decayRatio_pos (γ : ℝ) : 0 < decayRatio γ := NNReal.rpow_pos (by norm_num)

theorem decayRatio_lt_one {γ : ℝ} (hγ : 0 < γ) : decayRatio γ < 1 :=
  NNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hγ)

theorem dyadicHeight_coe (j : ℤ) : (dyadicHeight j:ℝ) = (2:ℝ)^(j:ℝ) := by
  simp only [dyadicHeight, NNReal.coe_zpow, NNReal.coe_ofNat, Real.rpow_intCast]

/-- Every positive cutoff lies between two adjacent actual dyadic heights. -/
theorem exists_dyadic_cutoff {t : ℝ≥0} (ht : 0 < t) :
    ∃ J : ℤ, dyadicHeight J ≤ t ∧ t < dyadicHeight (J+1) := by
  let x : ℝ := Real.log (t:ℝ) / Real.log 2
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hpow : (2:ℝ)^x = t := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    dsimp [x]
    rw [mul_div_cancel₀ _ hlog]
    exact Real.exp_log (show (0:ℝ)<t from ht)
  refine ⟨⌊x⌋, ?_, ?_⟩
  · change (dyadicHeight ⌊x⌋:ℝ) ≤ (t:ℝ)
    rw [dyadicHeight_coe, ← hpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Int.floor_le x)
  · change (t:ℝ) < (dyadicHeight (⌊x⌋+1):ℝ)
    rw [dyadicHeight_coe, ← hpow, Int.cast_add, Int.cast_one]
    exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1:ℝ)<2)).mpr (Int.lt_floor_add_one x)

theorem dyadicHeight_offset {J j : ℤ} (hj : J < j) :
    dyadicHeight j = dyadicHeight (J+1)*(2:ℝ≥0)^((j-J-1).toNat) := by
  have hn : ((j-J-1).toNat:ℤ) = j-J-1 := Int.toNat_of_nonneg (by omega)
  have heq : j = (J+1)+((j-J-1).toNat:ℤ) := by omega
  conv_lhs => rw [heq]
  unfold dyadicHeight
  rw [zpow_add₀ (by norm_num), zpow_natCast]

/-- The geometric budget dominates the continuous power needed for layer cake. -/
theorem geometricWeight_power_lower {γ : ℝ} (hγ : 0 < γ)
    {J j : ℤ} (hj : J < j) {t : ℝ≥0} (ht : t ≤ dyadicHeight (J+1)) :
    (1-decayRatio γ)*(t/dyadicHeight j)^γ ≤ geometricWeight (decayRatio γ) J j := by
  let N := (j-J-1).toNat
  have hr : t/dyadicHeight j ≤ ((2:ℝ≥0)^N)⁻¹ := by
    calc
      t/dyadicHeight j ≤ dyadicHeight (J+1)/dyadicHeight j := div_le_div_of_nonneg_right ht (by positivity)
      _ = ((2:ℝ≥0)^N)⁻¹ := by
        rw [dyadicHeight_offset hj]
        dsimp [N]
        field_simp [(dyadicHeight_pos (J+1)).ne']
  have hid : (((2:ℝ≥0)^N)⁻¹)^γ = decayRatio γ ^ N := by
    unfold decayRatio
    rw [NNReal.inv_rpow, ← NNReal.rpow_natCast_mul, ← NNReal.rpow_neg,
      ← NNReal.rpow_mul_natCast]
    congr 1
    ring
  have hp := NNReal.rpow_le_rpow hr hγ.le
  rw [hid] at hp
  exact mul_le_mul_right hp _

/-- The explicit geometric weights change the weak exponent from a to
a(1+γ), with a fixed constant independent of the cutoff and band count. -/
theorem geometric_cost_le {γ a A : ℝ} (hγ : 0 < γ) (ha : 0 < a) (hA : 0 ≤ A)
    {J j : ℤ} (hj : J < j) {t : ℝ≥0} (ht0 : 0 < t) (ht : t ≤ dyadicHeight (J+1)) :
    A*((t:ℝ)*(geometricWeight (decayRatio γ) J j:ℝ)/(dyadicHeight j:ℝ))^(-a) ≤
      A*(1-(decayRatio γ:ℝ))^(-a)*((t:ℝ)/(dyadicHeight j:ℝ))^(-(a*(1+γ))) := by
  let x : ℝ := (t:ℝ)/(dyadicHeight j:ℝ)
  let d : ℝ := 1-(decayRatio γ:ℝ)
  have hx : 0 < x := div_pos ht0 (dyadicHeight_pos j)
  have hd : 0 < d := sub_pos.mpr (decayRatio_lt_one hγ)
  have hw : d*x^γ ≤ (geometricWeight (decayRatio γ) J j:ℝ) := by
    have hh := geometricWeight_power_lower hγ hj ht
    change (((1-decayRatio γ)*(t/dyadicHeight j)^γ:ℝ≥0):ℝ) ≤ _ at hh
    rw [NNReal.coe_mul, NNReal.coe_sub (decayRatio_lt_one hγ).le,
      NNReal.coe_one, NNReal.coe_rpow, NNReal.coe_div] at hh
    convert hh using 1
    norm_cast
  have hb : d*x^(1+γ) ≤ (t:ℝ)*(geometricWeight (decayRatio γ) J j:ℝ)/(dyadicHeight j:ℝ) := by
    have hm := mul_le_mul_of_nonneg_left hw hx.le
    calc
      d*x^(1+γ) = x*(d*x^γ) := by rw [Real.rpow_add hx, Real.rpow_one]; ring
      _ ≤ x*(geometricWeight (decayRatio γ) J j:ℝ) := hm
      _ = _ := by dsimp [x]; ring
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hd (Real.rpow_pos_of_pos hx _)) hb (neg_nonpos.mpr ha.le)
  have hid : (d*x^(1+γ))^(-a) = d^(-a)*x^(-(a*(1+γ))) := by
    rw [Real.mul_rpow hd.le (Real.rpow_nonneg hx.le _), ← Real.rpow_mul hx.le]
    congr 2
    ring
  rw [hid] at hp
  simpa only [mul_assoc, x, d] using mul_le_mul_of_nonneg_left hp hA

/-- A distribution estimate for every actual finite dyadic simple function.
Its power and prefactor depend only on the weak exponent and chosen γ. -/
theorem dyadic_distribution {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {T : (X → ℝ≥0∞) → Y → ℝ≥0∞}
    (hT : PositiveLaws T) (s : Finset ℤ) (E : ℤ → Set X)
    (hE : ∀ j ∈ s, MeasurableSet (E j))
    (hdisj : (↑s : Set ℤ).Pairwise (fun i j => Disjoint (E i) (E j)))
    {γ a A : ℝ} (hγ : 0<γ) (ha : 0<a) (hA : 0≤A)
    (hweak : ∀ j ∈ s, ∀ u : ℝ, 0<u →
      ν {y | ENNReal.ofReal u<T (indicator (E j)) y} ≤
        ENNReal.ofReal (A*u^(-a))*μ (E j)) {t : ℝ≥0} (ht : 0<t) :
    ν {y | ((2*t:ℝ≥0):ℝ≥0∞)<T (bandSum s dyadicHeight E) y} ≤
      ∑ j ∈ s.filter (fun j => t<dyadicHeight j),
        ENNReal.ofReal (A*(1-(decayRatio γ:ℝ))^(-a)*
          ((t:ℝ)/(dyadicHeight j:ℝ))^(-(a*(1+γ))))*μ (E j) := by
  obtain ⟨J,hJ0,hJ1⟩ := exists_dyadic_cutoff ht
  apply (dyadic_restricted_level μ ν hT s E hE hdisj (decayRatio_pos γ)
    (decayRatio_lt_one hγ) ht J hJ0 hA hweak).trans
  calc
    _ ≤ ∑ j ∈ s.filter (fun j => J<j),
        ENNReal.ofReal (A*(1-(decayRatio γ:ℝ))^(-a)*
          ((t:ℝ)/(dyadicHeight j:ℝ))^(-(a*(1+γ))))*μ (E j) := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
        (geometric_cost_le hγ ha hA (mem_filter.mp hj).2 ht hJ1.le)) _
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro j hj
        exact mem_filter.mpr ⟨(mem_filter.mp hj).1,
          hJ1.trans_le (dyadicHeight_mono (by have hh := (mem_filter.mp hj).2; omega))⟩
      · intro _ _ _
        exact bot_le

end
end KakeyaFormal.RestrictedInterpolation
