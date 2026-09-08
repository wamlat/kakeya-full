import MeasurableDensityRecovery

/-! Actual half-multiplicity good sets and their exact deleted-mass budget,
as used in section 3.3. No retention inequality is supplied as a premise. -/
namespace KakeyaFormal.SourceGoodMass
open MeasureTheory MeasurableEnergy HairbrushSelection
open scoped ENNReal
noncomputable section
open Classical

variable {X : Type*} [MeasurableSpace X] {M : ℕ}

def mass (μ : Measure X) (Y : Fin M → Set X) : ℝ := ∑ i, μ.real (Y i)

def good (Ref Surv : Fin M → Set X) : Set X :=
  {x | multiplicity Ref x ≤ 2*multiplicity Surv x}

def goodRows (Ref Surv : Fin M → Set X) : Fin M → Set X :=
  fun i => Surv i ∩ good Ref Surv

def badRows (Ref Surv : Fin M → Set X) : Fin M → Set X :=
  fun i => Surv i \ good Ref Surv

theorem good_measurable (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hSurv : ∀ i, MeasurableSet (Surv i)) :
    MeasurableSet (good Ref Surv) :=
  measurableSet_le (multiplicity_measurable Ref hRef)
    ((multiplicity_measurable Surv hSurv).const_mul 2)

theorem goodRows_measurable (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hSurv : ∀ i, MeasurableSet (Surv i)) :
    ∀ i, MeasurableSet (goodRows Ref Surv i) :=
  fun i => (hSurv i).inter (good_measurable Ref Surv hRef hSurv)

theorem badRows_measurable (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hSurv : ∀ i, MeasurableSet (Surv i)) :
    ∀ i, MeasurableSet (badRows Ref Surv i) :=
  fun i => (hSurv i).diff (good_measurable Ref Surv hRef hSurv)

omit [MeasurableSpace X] in
theorem multiplicity_mono (Ref Surv : Fin M → Set X)
    (hsub : ∀ i, Surv i ⊆ Ref i) (x : X) : multiplicity Surv x ≤ multiplicity Ref x := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hx : x ∈ Surv i
  · simp [oneIndicator,hx,hsub i hx]
  · simp only [oneIndicator,Set.indicator_apply,hx,ite_false]
    split_ifs <;> norm_num

omit [MeasurableSpace X] in
/-- At a bad point, the surviving population is at most the deleted population.
At a good point the discarded population vanishes. -/
theorem bad_pointwise (Ref Surv : Fin M → Set X)
    (hsub : ∀ i, Surv i ⊆ Ref i) (x : X) :
    multiplicity (badRows Ref Surv) x ≤ multiplicity Ref x-multiplicity Surv x := by
  by_cases hx : x ∈ good Ref Surv
  · have hz : multiplicity (badRows Ref Surv) x = 0 := by
      simp [badRows,MeasurableEnergy.multiplicity,oneIndicator,hx]
    rw [hz]
    exact sub_nonneg.mpr (multiplicity_mono Ref Surv hsub x)
  · have hid : multiplicity (badRows Ref Surv) x = multiplicity Surv x := by
      simp [badRows,MeasurableEnergy.multiplicity,oneIndicator,Set.indicator_apply,hx]
    rw [hid]
    have hh : ¬ multiplicity Ref x ≤ 2*multiplicity Surv x := hx
    linarith

/-- Literal (3.8): integrate the actual bad surviving incidence. -/
theorem bad_mass_le_deleted (μ : Measure X) (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hSurv : ∀ i, MeasurableSet (Surv i))
    (hfin : ∀ i, μ (Ref i) ≠ ∞) (hsub : ∀ i, Surv i ⊆ Ref i) :
    mass μ (badRows Ref Surv) ≤ mass μ Ref-mass μ Surv := by
  have hsf i := measure_ne_top_of_subset (hsub i) (hfin i)
  have hbf i : μ (badRows Ref Surv i) ≠ ∞ :=
    measure_ne_top_of_subset Set.sdiff_subset (hsf i)
  have hb := badRows_measurable Ref Surv hRef hSurv
  have hRI := memLp_one_iff_integrable.mp (multiplicity_memLp Ref hRef hfin 1)
  have hSI := memLp_one_iff_integrable.mp (multiplicity_memLp Surv hSurv hsf 1)
  have hh := integral_mono (memLp_one_iff_integrable.mp (multiplicity_memLp _ hb hbf 1))
    (hRI.sub hSI) (bad_pointwise Ref Surv hsub)
  simp only [Pi.sub_apply] at hh
  rw [integral_sub hRI hSI,multiplicity_integral _ hb hbf,
    multiplicity_integral Ref hRef hfin,multiplicity_integral Surv hSurv hsf] at hh
  exact hh

theorem mass_split (μ : Measure X) (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hSurv : ∀ i, MeasurableSet (Surv i))
    (hfin : ∀ i, μ (Surv i) ≠ ∞) :
    mass μ (badRows Ref Surv)+mass μ (goodRows Ref Surv) = mass μ Surv := by
  unfold mass
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ =>
    measureReal_sdiff_add_inter (good_measurable Ref Surv hRef hSurv) (hfin i))

/-- Literal pre-budget form of (3.9) for any actual surviving restrictions. -/
theorem good_mass_lower (μ : Measure X) (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hSurv : ∀ i, MeasurableSet (Surv i))
    (hfin : ∀ i, μ (Ref i) ≠ ∞) (hsub : ∀ i, Surv i ⊆ Ref i) :
    mass μ Ref-2*(mass μ Ref-mass μ Surv) ≤ mass μ (goodRows Ref Surv) := by
  have hh := bad_mass_le_deleted μ Ref Surv hRef hSurv hfin hsub
  have hs := mass_split μ Ref Surv hRef hSurv
    (fun i => measure_ne_top_of_subset (hsub i) (hfin i))
  linarith

end
end KakeyaFormal.SourceGoodMass
