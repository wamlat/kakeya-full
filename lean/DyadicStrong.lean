import RestrictedDyadic
import PowerKernel
import ENNRealLayerCake

/-! First-stage strong interpolation: integrating the proved uniform dyadic
indicator distribution bound. -/
namespace KakeyaFormal.RestrictedInterpolation
open Finset MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
open Classical

/-- The actual dyadic simple function has exactly the disjoint-band power
integral, including when some bands have infinite measure. -/
theorem bandSum_rpow {X ι : Type*} (s : Finset ι) (height : ι → ℝ≥0) (E : ι → Set X)
    (hdisj : (↑s : Set ι).Pairwise (fun i j => Disjoint (E i) (E j)))
    {r : ℝ} (hr : 0<r) (x : X) :
    (bandSum s height E x)^r = ∑ j ∈ s, (height j:ℝ≥0∞)^r*indicator (E j) x := by
  by_cases hx : ∃ i ∈ s, x ∈ E i
  · obtain ⟨i,hi,hxi⟩ := hx
    have hz (j) (hj : j ∈ s) (hne : j ≠ i) : x ∉ E j := by
      intro hxj
      exact Set.disjoint_left.mp (hdisj hj hi hne) hxj hxi
    have hleft : bandSum s height E x = height i := by
      unfold bandSum
      rw [sum_eq_single i]
      · simp [indicator, hxi]
      · intro j hj hne
        simp [indicator, hz j hj hne]
      · exact fun hn => (hn hi).elim
    rw [hleft, sum_eq_single i]
    · simp [indicator, hxi]
    · intro j hj hne
      simp [indicator, hz j hj hne]
    · exact fun hn => (hn hi).elim
  · have hz (i) (hi : i ∈ s) : x ∉ E i := fun h => hx ⟨i,hi,h⟩
    have hleft : bandSum s height E x = 0 :=
      sum_eq_zero (fun i hi => by simp [indicator, hz i hi])
    rw [hleft, ENNReal.zero_rpow_of_pos hr]
    exact (sum_eq_zero (fun i hi => by simp [indicator, hz i hi])).symm

theorem lintegral_bandSum_rpow {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset ι) (height : ι → ℝ≥0) (E : ι → Set X)
    (hE : ∀ j ∈ s, MeasurableSet (E j))
    (hdisj : (↑s : Set ι).Pairwise (fun i j => Disjoint (E i) (E j)))
    {r : ℝ} (hr : 0<r) :
    ∫⁻ x, (bandSum s height E x)^r ∂μ = ∑ j ∈ s, (height j:ℝ≥0∞)^r*μ (E j) := by
  simp_rw [bandSum_rpow s height E hdisj hr]
  rw [lintegral_finsetSum s (f := fun j x => (height j:ℝ≥0∞)^r*indicator (E j) x)
    (fun j hj => measurable_const.mul (indicator_measurable (hE j hj)))]
  apply sum_congr rfl
  intro j hj
  rw [lintegral_const_mul _ (indicator_measurable (hE j hj))]
  simp only [indicator, lintegral_indicator_const (hE j hj), one_mul]

def bandKernel (U b r : ℝ) (t : ℝ) : ℝ≥0∞ :=
  (Iio U).indicator (fun t => ENNReal.ofReal ((t/U)^(-b)*t^(r-1))) t

theorem bandKernel_measurable (U b r : ℝ) : Measurable (bandKernel U b r) := by
  unfold bandKernel
  apply Measurable.indicator _ measurableSet_Iio
  fun_prop

theorem lintegral_bandKernel {U b r : ℝ} (hU : 0<U) (hbr : b<r) :
    ∫⁻ t in Ioi 0, bandKernel U b r t = ENNReal.ofReal (U^r/(r-b)) := by
  unfold bandKernel
  rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hs : Iio U ∩ Ioi (0:ℝ) = Ioo 0 U := by ext t; simp [and_comm]
  rw [hs]
  exact lintegral_cutoff_power hU hbr

/-- Integration of the literal finite-band distribution majorant. This is
a kernel-composition lemma; the distribution premise is proved in
`RestrictedDyadic.dyadic_distribution` for actual operator inputs. -/
theorem integrate_band_distribution {ι : Type*} (s : Finset ι)
    (height : ι → ℝ≥0) (mass : ι → ℝ≥0∞) (tail : ℝ → ℝ≥0∞)
    (hh : ∀ j ∈ s, 0 < height j) {K b r : ℝ} (hK : 0≤K) (hbr : b<r)
    (hbound : ∀ t : ℝ, 0<t → tail t ≤
      ∑ j ∈ s.filter (fun j => t<(height j:ℝ)),
        ENNReal.ofReal (K*(t/(height j:ℝ))^(-b))*mass j) :
    ∫⁻ t in Ioi 0, tail t*ENNReal.ofReal (t^(r-1)) ≤
      ENNReal.ofReal (K/(r-b))*∑ j ∈ s, (height j:ℝ≥0∞)^r*mass j := by
  have hp : ∀ t : ℝ, 0<t → tail t*ENNReal.ofReal (t^(r-1)) ≤
      ∑ j ∈ s, ENNReal.ofReal K*bandKernel (height j) b r t*mass j := by
    intro t ht
    apply (mul_le_mul_left (hbound t ht) (ENNReal.ofReal (t^(r-1)))).trans_eq
    rw [sum_filter, sum_mul]
    apply sum_congr rfl
    intro j hj
    by_cases hlt : t < (height j:ℝ)
    · simp only [bandKernel, Set.indicator, Set.mem_Iio, if_pos hlt]
      rw [ENNReal.ofReal_mul hK,
        ENNReal.ofReal_mul (p:=(t/(height j:ℝ))^(-b)) (q:=t^(r-1))
          (Real.rpow_nonneg (div_nonneg ht.le (height j).property) _)]
      ring
    · simp only [bandKernel, Set.indicator, Set.mem_Iio, if_neg hlt, mul_zero, zero_mul]
  calc
    _ ≤ ∫⁻ t in Ioi 0, ∑ j ∈ s, ENNReal.ofReal K*bandKernel (height j) b r t*mass j := by
      apply lintegral_mono_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact hp t ht
    _ = ∑ j ∈ s, (ENNReal.ofReal K*ENNReal.ofReal ((height j:ℝ)^r/(r-b)))*mass j := by
      rw [lintegral_finsetSum s (f:=fun j t => ENNReal.ofReal K*bandKernel (height j) b r t*mass j)
        (fun j _ => (measurable_const.mul (bandKernel_measurable _ _ _)).mul_const _)]
      apply sum_congr rfl
      intro j hj
      rw [lintegral_mul_const (mass j)
        (f := fun t => ENNReal.ofReal K*bandKernel (height j) b r t)
        (measurable_const.mul (bandKernel_measurable _ _ _)),
        lintegral_const_mul (ENNReal.ofReal K) (bandKernel_measurable (height j) b r),
        lintegral_bandKernel (b:=b) (r:=r) (show (0:ℝ)<height j from hh j hj) hbr]
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      have hj0 : (0:ℝ)<height j := hh j hj
      have he : ENNReal.ofReal K*ENNReal.ofReal ((height j:ℝ)^r/(r-b)) =
          ENNReal.ofReal (K/(r-b))*(height j:ℝ≥0∞)^r := by
        rw [← ENNReal.ofReal_mul hK]
        rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_pos hj0,
          ← ENNReal.ofReal_mul (div_nonneg hK (sub_pos.mpr hbr).le)]
        congr 1
        ring
      rw [he]
      ring

/-- The first strong estimate for actual finite dyadic inputs. Only indicators
are tested by the restricted weak hypothesis; all sums and distribution
integrals are constructed by the proof. -/
theorem dyadic_strong_moment {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {T : (X → ℝ≥0∞) → Y → ℝ≥0∞}
    (hT : PositiveLaws T) (s : Finset ℤ) (E : ℤ → Set X)
    (hE : ∀ j ∈ s, MeasurableSet (E j))
    (hdisj : (↑s : Set ℤ).Pairwise (fun i j => Disjoint (E i) (E j)))
    (hmout : Measurable (T (bandSum s dyadicHeight E)))
    {γ a A r : ℝ} (hγ : 0<γ) (ha : 0<a) (hA : 0≤A) (hbr : a*(1+γ)<r)
    (hweak : ∀ j ∈ s, ∀ u : ℝ, 0<u →
      ν {y | ENNReal.ofReal u<T (indicator (E j)) y} ≤
        ENNReal.ofReal (A*u^(-a))*μ (E j)) :
    ∫⁻ y, (T (bandSum s dyadicHeight E) y)^r ∂ν ≤
      (2:ℝ≥0∞)^r * ENNReal.ofReal r *
        ENNReal.ofReal ((A*(1-(decayRatio γ:ℝ))^(-a))/(r-a*(1+γ))) *
          ∫⁻ x, (bandSum s dyadicHeight E x)^r ∂μ := by
  let g : Y → ℝ≥0∞ := fun y => T (bandSum s dyadicHeight E) y / 2
  have hr : 0<r := (mul_pos ha (by linarith : 0<1+γ)).trans hbr
  have hg : Measurable g := hmout.div_const 2
  have hd : 0 < 1-(decayRatio γ:ℝ) := sub_pos.mpr (decayRatio_lt_one hγ)
  have hK : 0 ≤ A*(1-(decayRatio γ:ℝ))^(-a) :=
    mul_nonneg hA (Real.rpow_nonneg hd.le _)
  have hbound : ∀ t : ℝ, 0<t → ν {y | ENNReal.ofReal t<g y} ≤
      ∑ j ∈ s.filter (fun j => t<(dyadicHeight j:ℝ)),
        ENNReal.ofReal ((A*(1-(decayRatio γ:ℝ))^(-a))*
          (t/(dyadicHeight j:ℝ))^(-(a*(1+γ))))*μ (E j) := by
    intro t ht
    let t' : ℝ≥0 := ⟨t,ht.le⟩
    have hlevel : {y | ENNReal.ofReal t<g y} =
        {y | ((2*t':ℝ≥0):ℝ≥0∞)<T (bandSum s dyadicHeight E) y} := by
      ext y
      change ENNReal.ofReal t < T (bandSum s dyadicHeight E) y / 2 ↔
        ((2*t':ℝ≥0):ℝ≥0∞) < T (bandSum s dyadicHeight E) y
      rw [ENNReal.lt_div_iff_mul_lt (Or.inl (by norm_num : (2:ℝ≥0∞)≠0))
        (Or.inl (by norm_num : (2:ℝ≥0∞)≠∞))]
      have ht' : ENNReal.ofReal t = (t':ℝ≥0∞) := by
        change ENNReal.ofReal (t':ℝ) = (t':ℝ≥0∞)
        simp only [ENNReal.ofReal_coe_nnreal]
      rw [ht', ENNReal.coe_mul, ENNReal.coe_ofNat, mul_comm]
    rw [hlevel]
    have hh := dyadic_distribution μ ν hT s E hE hdisj hγ ha hA hweak (t:=t') ht
    convert hh using 1
    norm_cast
  have hmom : (∫⁻ y, (g y)^r ∂ν) ≤
      ENNReal.ofReal r * (ENNReal.ofReal ((A*(1-(decayRatio γ:ℝ))^(-a))/(r-a*(1+γ))) *
        ∑ j ∈ s, (dyadicHeight j:ℝ≥0∞)^r*μ (E j)) := by
    rw [ENNRealLayerCake.power_layercake ν hg hr]
    exact mul_le_mul_right
      (integrate_band_distribution s dyadicHeight (fun j => μ (E j))
        (fun t => ν {y | ENNReal.ofReal t<g y}) (fun j _ => dyadicHeight_pos j) hK hbr hbound) _
  have hscale : (∫⁻ y, (T (bandSum s dyadicHeight E) y)^r ∂ν) =
      (2:ℝ≥0∞)^r*(∫⁻ y, (g y)^r ∂ν) := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le (by norm_num))]
    apply lintegral_congr
    intro y
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hr.le]
    congr 1
    exact (ENNReal.mul_div_cancel (by norm_num : (2:ℝ≥0∞)≠0)
      (by norm_num : (2:ℝ≥0∞)≠∞)).symm
  rw [hscale]
  have hh := mul_le_mul_right hmom ((2:ℝ≥0∞)^r)
  rw [← lintegral_bandSum_rpow μ s dyadicHeight E hE hdisj hr] at hh
  simpa only [mul_assoc] using hh

end
end KakeyaFormal.RestrictedInterpolation
