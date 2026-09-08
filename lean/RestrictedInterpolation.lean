import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Analysis.SpecificLimits.Normed

/-! Constructive restricted-weak interpolation for positive operators.
Finite superpositions and dyadic functions are built explicitly; the input
estimate is applied only to actual indicators. -/
namespace KakeyaFormal.RestrictedInterpolation
open Finset MeasureTheory Set
open scoped ENNReal NNReal
noncomputable section
open Classical

/-- Elementary laws of an actual positive averaging supremum. No norm or
interpolation estimate is hidden in these fields. Output measurability and
monotone-limit compatibility are separate from this finite-stage interface. -/
structure PositiveLaws {X Y : Type*} [MeasurableSpace X]
    (T : (X → ℝ≥0∞) → Y → ℝ≥0∞) : Prop where
  zero : ∀ y, T (fun _ => 0) y = 0
  monotone : Monotone T
  add_le : ∀ f g, Measurable f → Measurable g → T (f+g) ≤ T f+T g
  mul_const : ∀ (c : ℝ≥0) f, Measurable f → T (fun x => (c:ℝ≥0∞)*f x)=fun y => (c:ℝ≥0∞)*T f y
  bounded : ∀ (c : ℝ≥0) (f : X → ℝ≥0∞), Measurable f → (∀ x, f x≤c) → ∀ y, T f y≤c

def indicator {X : Type*} (E : Set X) : X → ℝ≥0∞ := E.indicator (fun _ => 1)

def bandSum {X ι : Type*} (s : Finset ι) (height : ι → ℝ≥0) (E : ι → Set X) : X → ℝ≥0∞ :=
  fun x => ∑ i ∈ s, (height i:ℝ≥0∞)*indicator (E i) x

theorem indicator_measurable {X : Type*} [MeasurableSpace X] {E : Set X}
    (hE : MeasurableSet E) : Measurable (indicator E) := measurable_const.indicator hE

theorem bandSum_measurable {X ι : Type*} [MeasurableSpace X]
    (s : Finset ι) (height : ι → ℝ≥0) (E : ι → Set X)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) : Measurable (bandSum s height E) := by
  unfold bandSum
  exact Finset.measurable_sum _ (fun i hi => measurable_const.mul (indicator_measurable (hE i hi)))

theorem PositiveLaws.sum_le {X Y ι : Type*} [MeasurableSpace X]
    {T : (X → ℝ≥0∞) → Y → ℝ≥0∞} (hT : PositiveLaws T)
    (s : Finset ι) (f : ι → X → ℝ≥0∞) (hf : ∀ i ∈ s, Measurable (f i)) :
    T (fun x => ∑ i ∈ s, f i x) ≤ fun y => ∑ i ∈ s, T (f i) y := by
  induction s using Finset.induction_on with
  | empty =>
    intro y
    simpa only [sum_empty] using (hT.zero y).le
  | @insert i s hi ih =>
    simp only [sum_insert hi]
    have hm : Measurable (fun x => ∑ j ∈ s, f j x) :=
      Finset.measurable_sum _ (fun j hj => hf j (mem_insert_of_mem hj))
    exact (hT.add_le (f i) _ (hf i (mem_insert_self _ _)) hm).trans
      (fun y => add_le_add le_rfl (ih (fun j hj => hf j (mem_insert_of_mem hj)) y))

theorem PositiveLaws.bandSum_le {X Y ι : Type*} [MeasurableSpace X]
    {T : (X → ℝ≥0∞) → Y → ℝ≥0∞} (hT : PositiveLaws T)
    (s : Finset ι) (height : ι → ℝ≥0) (E : ι → Set X)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) :
    T (bandSum s height E) ≤ fun y => ∑ i ∈ s, (height i:ℝ≥0∞)*T (indicator (E i)) y := by
  have hh := hT.sum_le s (fun i x => (height i:ℝ≥0∞)*indicator (E i) x)
    (fun i hi => measurable_const.mul (indicator_measurable (hE i hi)))
  apply hh.trans
  intro y
  apply sum_le_sum
  intro i hi
  rw [hT.mul_const (height i) _ (indicator_measurable (hE i hi))]

/-- Weighted finite pigeonholing in the level set, valid even when an output
value is infinite and without assuming output measurability. -/
theorem weighted_level_cover {Y ι : Type*} (s : Finset ι) (u : ι → Y → ℝ≥0∞)
    (weights : ι → ℝ≥0) {t : ℝ≥0} (hweights : ∑ i ∈ s, weights i ≤ 1) :
    {y | (t:ℝ≥0∞)<∑ i ∈ s, u i y} ⊆
      ⋃ i ∈ s, {y | ((t*weights i:ℝ≥0):ℝ≥0∞)<u i y} := by
  intro y hy
  by_contra hn
  have hpoint (i) (hi : i ∈ s) : u i y ≤ ((t*weights i:ℝ≥0):ℝ≥0∞) := by
    apply le_of_not_gt
    intro hlt
    exact hn (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨hi,hlt⟩⟩)
  have hh := sum_le_sum hpoint
  have hsum : (∑ i ∈ s, ((t*weights i:ℝ≥0):ℝ≥0∞)) ≤ t := by
    norm_cast
    rw [← mul_sum]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hweights (show 0 ≤ t from bot_le)
  exact (not_lt_of_ge (hh.trans hsum)) hy

/-- Indicator estimates control the actual finite positive superposition.
The weak bound is tested only on E_i, never on a general input function. -/
theorem finite_restricted_level {X Y ι : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {T : (X → ℝ≥0∞) → Y → ℝ≥0∞}
    (hT : PositiveLaws T) (s : Finset ι) (height weights : ι → ℝ≥0) (E : ι → Set X)
    (hE : ∀ i ∈ s, MeasurableSet (E i)) (hc : ∀ i ∈ s, 0<height i)
    (hw : ∀ i ∈ s, 0<weights i) (hsum : ∑ i ∈ s, weights i≤1)
    {t : ℝ≥0} (ht : 0<t) {a A : ℝ} (_hA : 0≤A)
    (hweak : ∀ i ∈ s, ∀ u : ℝ, 0<u →
      ν {y | ENNReal.ofReal u<T (indicator (E i)) y} ≤
        ENNReal.ofReal (A*u^(-a))*μ (E i)) :
    ν {y | (t:ℝ≥0∞)<T (bandSum s height E) y} ≤
      ∑ i ∈ s, ENNReal.ofReal (A*((t:ℝ)*(weights i:ℝ)/(height i:ℝ))^(-a))*μ (E i) := by
  have hcover : {y | (t:ℝ≥0∞)<T (bandSum s height E) y} ⊆
      ⋃ i ∈ s, {y | ((t*weights i:ℝ≥0):ℝ≥0∞)<(height i:ℝ≥0∞)*T (indicator (E i)) y} :=
    (fun _ hy => (weighted_level_cover s (fun i y => (height i:ℝ≥0∞)*T (indicator (E i)) y)
      weights hsum) (hy.trans_le (hT.bandSum_le s height E hE _)))
  apply (measure_mono hcover).trans ((measure_biUnion_finset_le s _).trans ?_)
  apply sum_le_sum
  intro i hi
  have hi0 : (0:ℝ)<height i := hc i hi
  have hu : 0<(t:ℝ)*(weights i:ℝ)/(height i:ℝ) := by positivity [hw i hi]
  apply le_trans ?_ (hweak i hi _ hu)
  apply measure_mono
  intro y hy
  by_contra hn
  have hh := mul_le_mul_right (le_of_not_gt hn) (height i:ℝ≥0∞)
  have hid : (height i:ℝ≥0∞)*ENNReal.ofReal ((t:ℝ)*(weights i:ℝ)/(height i:ℝ)) =
      ((t*weights i:ℝ≥0):ℝ≥0∞) := by
    calc
      _ = ENNReal.ofReal ((height i:ℝ)*((t:ℝ)*(weights i:ℝ)/(height i:ℝ))) := by
        simpa only [ENNReal.ofReal_coe_nnreal] using
          (ENNReal.ofReal_mul (q := (t:ℝ)*(weights i:ℝ)/(height i:ℝ)) hi0.le).symm
      _ = ENNReal.ofReal ((t:ℝ)*(weights i:ℝ)) := by
        congr 1
        field_simp
      _ = _ := by simp only [← NNReal.coe_mul, ENNReal.ofReal_coe_nnreal]
  rw [hid] at hh
  exact (not_lt_of_ge hh) hy

/-- Disjoint measurable bands have a genuine pointwise bound independent of
the number of bands. This is the infinity endpoint used in the split. -/
theorem bandSum_le_of_disjoint {X ι : Type*} (s : Finset ι)
    (height : ι → ℝ≥0) (E : ι → Set X) {c : ℝ≥0}
    (hdisj : (↑s : Set ι).Pairwise (fun i j => Disjoint (E i) (E j)))
    (hc : ∀ i ∈ s, height i ≤ c) : ∀ x, bandSum s height E x ≤ c := by
  intro x
  by_cases hx : ∃ i ∈ s, x ∈ E i
  · obtain ⟨i, hi, hxi⟩ := hx
    have hz (j) (hj : j ∈ s) (hne : j ≠ i) : x ∉ E j := by
      intro hxj
      exact Set.disjoint_left.mp (hdisj hj hi hne) hxj hxi
    unfold bandSum
    rw [sum_eq_single i]
    · simpa [indicator, hxi] using ENNReal.coe_le_coe.mpr (hc i hi)
    · intro j hj hne
      simp [indicator, hz j hj hne]
    · exact fun hn => (hn hi).elim
  · have hz (i) (hi : i ∈ s) : x ∉ E i := fun h => hx ⟨i,hi,h⟩
    have heq : bandSum s height E x = 0 := by
      exact sum_eq_zero (fun i hi => by simp [indicator, hz i hi])
    rw [heq]
    exact bot_le

theorem bandSum_partition {X ι : Type*} (s : Finset ι)
    (height : ι → ℝ≥0) (E : ι → Set X) (p : ι → Prop) :
    bandSum s height E = bandSum (s.filter p) height E +
      bandSum (s.filter (fun i => ¬ p i)) height E := by
  funext x
  exact (sum_filter_add_sum_filter_not s p _).symm

/-- Removing a bounded part of size t reduces the level 2t to the level t
of the remaining actual input. Extended-real outputs are allowed. -/
theorem PositiveLaws.level_after_bounded_part {X Y : Type*} [MeasurableSpace X]
    {T : (X → ℝ≥0∞) → Y → ℝ≥0∞} (hT : PositiveLaws T)
    {f g : X → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {t : ℝ≥0} (hbound : ∀ x, f x ≤ t) :
    {y | ((2*t:ℝ≥0):ℝ≥0∞) < T (f+g) y} ⊆ {y | (t:ℝ≥0∞) < T g y} := by
  intro y hy
  by_contra hn
  have hu : T (f+g) y ≤ (t:ℝ≥0∞)+(t:ℝ≥0∞) :=
    (hT.add_le f g hf hg y).trans (add_le_add (hT.bounded t f hf hbound y) (le_of_not_gt hn))
  have hid : ((2*t:ℝ≥0):ℝ≥0∞) = (t:ℝ≥0∞)+(t:ℝ≥0∞) := by
    norm_cast
    ring
  rw [hid] at hy
  exact (not_lt_of_ge hu) hy

/-- A concrete probability budget for every finite subset of the nonnegative
integers. Its constant is independent of the number of selected bands. -/
theorem geometric_weights_sum_le (s : Finset ℕ) {q : ℝ≥0} (hq : q < 1) :
    ∑ n ∈ s, (1-q)*q^n ≤ 1 := by
  rw [← mul_sum]
  have hs : ∑ n ∈ s, q^n ≤ (1-q)⁻¹ := by
    simpa only [NNReal.tsum_geometric hq] using
      (NNReal.summable_geometric hq).sum_le_tsum s (fun _ _ => bot_le)
  have hd : 1-q ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr hq)
  calc
    (1-q)*(∑ n ∈ s, q^n) ≤ (1-q)*(1-q)⁻¹ := mul_le_mul_right hs _
    _ = 1 := mul_inv_cancel₀ hd

def dyadicHeight (j : ℤ) : ℝ≥0 := (2:ℝ≥0)^j

def geometricWeight (q : ℝ≥0) (J j : ℤ) : ℝ≥0 := (1-q)*q^((j-J-1).toNat)

theorem dyadicHeight_pos (j : ℤ) : 0 < dyadicHeight j := zpow_pos (by norm_num) _

theorem dyadicHeight_mono : Monotone dyadicHeight := by
  intro i j hij
  exact zpow_le_zpow_right₀ (by norm_num) hij

theorem geometricWeight_pos {q : ℝ≥0} (hq0 : 0 < q) (hq1 : q < 1) (J j : ℤ) :
    0 < geometricWeight q J j := mul_pos (tsub_pos_iff_lt.mpr hq1) (pow_pos hq0 _)

theorem geometricWeight_sum_le (s : Finset ℤ) {q : ℝ≥0} (hq : q < 1) (J : ℤ) :
    ∑ j ∈ s.filter (fun j => J < j), geometricWeight q J j ≤ 1 := by
  have hinj : Set.InjOn (fun j : ℤ => (j-J-1).toNat) ↑(s.filter (fun j => J < j)) := by
    intro i hi j hj heq
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    have hcast := congrArg (fun n : ℕ => (n:ℤ)) heq
    simp only [Int.toNat_of_nonneg (show 0 ≤ i-J-1 by omega),
      Int.toNat_of_nonneg (show 0 ≤ j-J-1 by omega)] at hcast
    omega
  simpa only [sum_image hinj, geometricWeight] using
    geometric_weights_sum_le ((s.filter (fun j => J < j)).image (fun j => (j-J-1).toNat)) hq

/-- The genuine dyadic low/high decomposition with an explicit geometric
budget. The weak hypothesis is still tested only on the individual bands. -/
theorem dyadic_restricted_level {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) {T : (X → ℝ≥0∞) → Y → ℝ≥0∞}
    (hT : PositiveLaws T) (s : Finset ℤ) (E : ℤ → Set X)
    (hE : ∀ j ∈ s, MeasurableSet (E j))
    (hdisj : (↑s : Set ℤ).Pairwise (fun i j => Disjoint (E i) (E j)))
    {q t : ℝ≥0} (hq0 : 0<q) (hq1 : q<1) (ht : 0<t) (J : ℤ)
    (hcut : dyadicHeight J ≤ t) {a A : ℝ} (hA : 0≤A)
    (hweak : ∀ j ∈ s, ∀ u : ℝ, 0<u →
      ν {y | ENNReal.ofReal u<T (indicator (E j)) y} ≤
        ENNReal.ofReal (A*u^(-a))*μ (E j)) :
    ν {y | ((2*t:ℝ≥0):ℝ≥0∞)<T (bandSum s dyadicHeight E) y} ≤
      ∑ j ∈ s.filter (fun j => J<j),
        ENNReal.ofReal (A*((t:ℝ)*(geometricWeight q J j:ℝ)/(dyadicHeight j:ℝ))^(-a))*μ (E j) := by
  let lo := s.filter (fun j => ¬ J<j)
  let hi := s.filter (fun j => J<j)
  have hsplit : bandSum s dyadicHeight E = bandSum lo dyadicHeight E + bandSum hi dyadicHeight E := by
    funext x
    change (∑ j ∈ s, (dyadicHeight j:ℝ≥0∞)*indicator (E j) x) =
      (∑ j ∈ lo, (dyadicHeight j:ℝ≥0∞)*indicator (E j) x) +
      (∑ j ∈ hi, (dyadicHeight j:ℝ≥0∞)*indicator (E j) x)
    exact (sum_filter_add_sum_filter_not s (fun j => J<j)
      (fun j => (dyadicHeight j:ℝ≥0∞)*indicator (E j) x)).symm.trans (add_comm _ _)
  have hlo : ∀ x, bandSum lo dyadicHeight E x ≤ t :=
    bandSum_le_of_disjoint lo dyadicHeight E
      (hdisj.mono (filter_subset _ _))
      (fun j hj => (dyadicHeight_mono (le_of_not_gt (mem_filter.mp hj).2)).trans hcut)
  have hmlo := bandSum_measurable lo dyadicHeight E (fun j hj => hE j (mem_filter.mp hj).1)
  have hmhi := bandSum_measurable hi dyadicHeight E (fun j hj => hE j (mem_filter.mp hj).1)
  rw [hsplit]
  exact (measure_mono (hT.level_after_bounded_part hmlo hmhi hlo)).trans
    (finite_restricted_level μ ν hT hi dyadicHeight (geometricWeight q J) E
      (fun j hj => hE j (mem_filter.mp hj).1) (fun j _ => dyadicHeight_pos j)
      (fun j _ => geometricWeight_pos hq0 hq1 J j) (geometricWeight_sum_le s hq1 J)
      ht hA (fun j hj => hweak j (mem_filter.mp hj).1))

end
end KakeyaFormal.RestrictedInterpolation
