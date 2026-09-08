import HairbrushRemoval

/-!
# Actual stem incidences, bristle count, and transverse hairbrush volume

A pointwise lower bound on the number of actual bristles meeting a measurable
part of the stem is integrated. The proved transverse tube-intersection bound
then gives the number of bristles; the crossing-ball hairbrush theorem turns
that actual count into the union lower bound (4.15).
-/
namespace KakeyaFormal.HairbrushStem
open MeasureTheory
open scoped ENNReal
open KakeyaFormal.MeasurableEnergy KakeyaFormal.HairbrushRemoval
open KakeyaFormal.TubeIntersection KakeyaFormal.TubeVolume
noncomputable section

/-- Integrate a lower bound on actual finite incidence MeasurableEnergy.multiplicity over an
actual measurable set. The conclusion is not assumed as an energy interface. -/
theorem incidence_integral_lower {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {ι : Type*} [Fintype ι] (Y : ι → Set X) (S : Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (hS : MeasurableSet S) (hSf : ν S ≠ ∞)
    {mu : ℝ} (hpoint : ∀ x ∈ S, mu ≤ (overlapCount Y x:ℝ)) :
    mu*ν.real S ≤ ∑ i, ν.real (S ∩ Y i) := by
  have hmeas (i : ι) := hS.inter (hY i)
  have hfin (i : ι) : ν (S ∩ Y i) ≠ ∞ := measure_ne_top_of_subset Set.inter_subset_left hSf
  have hmul : ∀ x, mu*oneIndicator S x ≤ MeasurableEnergy.multiplicity (fun i => S ∩ Y i) x := by
    intro x
    classical
    by_cases hx : x ∈ S
    · have hid : MeasurableEnergy.multiplicity (fun i => S ∩ Y i) x = MeasurableEnergy.multiplicity Y x := by
        simp [MeasurableEnergy.multiplicity,oneIndicator,Set.indicator_apply,hx]
      rw [hid,multiplicity_eq_card]
      simpa [oneIndicator,hx] using hpoint x hx
    · simp [MeasurableEnergy.multiplicity,oneIndicator,hx]
  have h := integral_mono ((indicator_integrable hS hSf).const_mul mu)
    (memLp_one_iff_integrable.mp (multiplicity_memLp (fun i => S ∩ Y i) hmeas hfin 1)) hmul
  rw [integral_const_mul,indicator_integral hS,multiplicity_integral _ hmeas hfin] at h
  exact h

/-- Explicit ambient-dimensional constant in the actual transverse intersection
bound; it is independent of all thickness, angle and density parameters. -/
def pairConstant (k : ℕ) : ℝ := 44*(2:ℝ)^(k+2)*unitBallVolume (k+2)

theorem pairConstant_pos (k : ℕ) : 0 < pairConstant k := by
  have h := unitBallVolume_pos (k+2)
  unfold pairConstant
  positivity

/-- Actual transverse incidences on a stem force many actual bristles. -/
theorem bristle_count {ι : Type*} [Fintype ι] {k : ℕ}
    (stem : UnitTube (k+2)) (bristle : ι → UnitTube (k+2))
    (Y : ι → Set (Space (k+2))) (S : Set (Space (k+2)))
    {δ theta mu lam L : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (htheta : 0 < theta)
    (hmu : 0 ≤ mu) (hL : 0 < L)
    (hangle : ∀ i, theta ≤ projectiveDistance stem.direction (bristle i).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hS : MeasurableSet S) (hSsub : S ⊆ stem.carrier δ)
    (hmass : lam*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real S)
    (hpoint : ∀ x ∈ S, mu ≤ (overlapCount Y x:ℝ)) :
    mu*lam*theta/(pairConstant k*δ*L) ≤ (Fintype.card ι:ℝ) := by
  have hSf := measure_ne_top_of_subset hSsub (carrier_finite stem δ)
  have hinc := incidence_integral_lower Y S hY hS hSf hpoint
  have hpair (i : ι) : (volume : Measure (Space (k+2))).real (S ∩ Y i) ≤
      pairConstant k*δ^(k+2)/theta := by
    have hmono := measureReal_mono (Set.inter_subset_inter hSsub (hsub i))
      (measure_ne_top_of_subset Set.inter_subset_left (carrier_finite stem δ))
    have h := hmono.trans (intersection_volume_upper stem (bristle i) hδ hδ1)
    have hmax : theta ≤ max (projectiveDistance stem.direction (bristle i).direction) δ :=
      (hangle i).trans (le_max_left _ _)
    exact h.trans (div_le_div_of_nonneg_left
      (by have hp := pairConstant_pos k; change 0 ≤ pairConstant k*δ^(k+2); positivity)
      htheta hmax)
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hpair i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hm := mul_le_mul_of_nonneg_left hmass hmu
  have htot := hm.trans (hinc.trans hsum)
  have hp := pairConstant_pos k
  have hid : mu*(lam*δ^(k+1)/L)/(pairConstant k*δ^(k+2)/theta) =
      mu*lam*theta/(pairConstant k*δ*L) := by
    rw [show δ^(k+2) = δ^(k+1)*δ by rw [pow_succ]]
    field_simp
  have hc : 0 < pairConstant k*δ^(k+2)/theta := by positivity
  have hh := (div_le_iff₀ hc).mpr htot
  rwa [hid] at hh

/-- Constant in the actual transverse hairbrush estimate (4.15). -/
def stemConstant (k : ℕ) : ℝ := pairConstant k*removalConstant k

theorem stemConstant_pos (k : ℕ) : 0 < stemConstant k := by
  exact mul_pos (pairConstant_pos k) (removalConstant_pos k)

/-- Equation (4.15), with actual measurable stem and bristle incidences, real
tube geometry, actual crossing-point choices, measured two ends and actual
plane-bin packing and integration all proved inside the theorem chain. -/
theorem stem_hairbrush_union_lower {ι : Type*} [Fintype ι] {k : ℕ}
    (stem : UnitTube (k+2)) (bristle : ι → UnitTube (k+2))
    (Y : ι → Set (Space (k+2))) (S : Set (Space (k+2)))
    {δ theta r mu lam L B alpha : ℝ}
    (hδ : 0 < δ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hscale : 88*δ ≤ r*theta)
    (hmu : 0 ≤ mu) (hlam : 0 ≤ lam) (hL : 0 < L) (hlogL : Real.logb 2 (2/δ)+2 ≤ L)
    (hangle : ∀ i, theta ≤ projectiveDistance stem.direction (bristle i).direction)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (bristle i).direction (bristle j).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hS : MeasurableSet S) (hSsub : S ⊆ stem.carrier δ)
    (hSmass : lam*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real S)
    (hmeet : ∀ i, (S ∩ Y i).Nonempty)
    (hpoint : ∀ x ∈ S, mu ≤ (overlapCount Y x:ℝ))
    (hmass : ∀ i, lam*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hsmall : B*r^alpha ≤ 1/2) :
    mu*lam^3*theta*δ^k*(r*theta)^k/(stemConstant k*L^4) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  have hδ1 : δ ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left htheta1 hr.le]
  have hcross (i : ι) : ∃ p, p ∈ S ∩ Y i := hmeet i
  let crossing := fun i => Classical.choose (hcross i)
  have hcrossing (i : ι) : crossing i ∈ stem.carrier δ ∩ (bristle i).carrier δ := by
    have h := Classical.choose_spec (hcross i)
    exact ⟨hSsub h.1,hsub i h.2⟩
  have hhair := two_ends_crossing_hairbrush stem bristle Y crossing hδ htheta htheta1 hr hr1 hscale
    hlam hL hlogL hangle hcrossing hdir hY hsub hmass hends hsmall
  have hcount := bristle_count stem bristle Y S hδ hδ1 htheta hmu hL hangle hY hsub
    hS hSsub hSmass hpoint
  have hC := removalConstant_pos k
  have hfactor : 0 ≤ lam^2*δ^(k+1)*(r*theta)^k/(removalConstant k*L^3) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcount hfactor
  have hid : (mu*lam*theta/(pairConstant k*δ*L)) *
      (lam^2*δ^(k+1)*(r*theta)^k/(removalConstant k*L^3)) =
      mu*lam^3*theta*δ^k*(r*theta)^k/(stemConstant k*L^4) := by
    unfold stemConstant
    rw [pow_succ]
    field_simp
    ring
  rw [hid] at hmul
  have hid₂ : (Fintype.card ι:ℝ)*(lam^2*δ^(k+1)*(r*theta)^k/(removalConstant k*L^3)) =
      (Fintype.card ι:ℝ)*lam^2*δ^(k+1)*(r*theta)^k/(removalConstant k*L^3) := by ring
  rw [hid₂] at hmul
  exact hmul.trans hhair

end
end KakeyaFormal.HairbrushStem

#print axioms KakeyaFormal.HairbrushStem.stem_hairbrush_union_lower
