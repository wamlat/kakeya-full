import SourceDensityPruningGeometry

/-! Section 3.3 for completed-measurable ORIGINAL rows. Completion has exactly
the same outer measure on every set, so the original deletion masks, good sets,
assigned pieces and retained labels remain literally unchanged. -/
namespace KakeyaFormal.LebesgueDensityPruning
open MeasureTheory SourceGoodMass SourceDensityPruning SourceDensityPruningGeometry
open scoped ENNReal
noncomputable section

variable {X : Type*} [MeasurableSpace X] {M J : ℕ}

/-- Completing the measurable space does not change any actual row mass. -/
theorem mass_completion (μ : Measure X) (Y : Fin M → Set X) :
    mass μ.completion Y = mass μ Y := rfl

/-- In particular the original density threshold selects exactly the same
original full rows, not a family of representatives. -/
theorem survivors_completion (μ : Measure X) (Full Y : Fin M → Set X) (a : ℝ) :
    survivors μ.completion Full Y a = survivors μ Full Y a := rfl

theorem retained_completion (μ : Measure X) (Ref Surv : Fin J → Fin M → Set X) :
    retained μ.completion Ref Surv = retained μ Ref Surv := rfl

theorem good_nullMeasurable (μ : Measure X) (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, NullMeasurableSet (Ref i) μ)
    (hSurv : ∀ i, NullMeasurableSet (Surv i) μ) :
    NullMeasurableSet (good Ref Surv) μ :=
  @SourceGoodMass.good_measurable (NullMeasurableSpace X μ) _ M Ref Surv hRef hSurv

theorem goodRows_nullMeasurable (μ : Measure X) (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, NullMeasurableSet (Ref i) μ)
    (hSurv : ∀ i, NullMeasurableSet (Surv i) μ) :
    ∀ i, NullMeasurableSet (goodRows Ref Surv i) μ :=
  @SourceGoodMass.goodRows_measurable (NullMeasurableSpace X μ) _ M Ref Surv hRef hSurv

theorem badRows_nullMeasurable (μ : Measure X) (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, NullMeasurableSet (Ref i) μ)
    (hSurv : ∀ i, NullMeasurableSet (Surv i) μ) :
    ∀ i, NullMeasurableSet (badRows Ref Surv i) μ :=
  @SourceGoodMass.badRows_measurable (NullMeasurableSpace X μ) _ M Ref Surv hRef hSurv

/-- Literal bad-incidence estimate (3.8), with original sets and original
outer measures, proved by integration on the completed measurable space. -/
theorem bad_mass_le_deleted (μ : Measure X) (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, NullMeasurableSet (Ref i) μ)
    (hSurv : ∀ i, NullMeasurableSet (Surv i) μ)
    (hfin : ∀ i, μ (Ref i) ≠ ∞) (hsub : ∀ i, Surv i ⊆ Ref i) :
    mass μ (badRows Ref Surv) ≤ mass μ Ref-mass μ Surv :=
  @SourceGoodMass.bad_mass_le_deleted (NullMeasurableSpace X μ) _ M
    μ.completion Ref Surv hRef hSurv hfin hsub

theorem mass_split (μ : Measure X) (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, NullMeasurableSet (Ref i) μ)
    (hSurv : ∀ i, NullMeasurableSet (Surv i) μ)
    (hfin : ∀ i, μ (Surv i) ≠ ∞) :
    mass μ (badRows Ref Surv)+mass μ (goodRows Ref Surv) = mass μ Surv :=
  @SourceGoodMass.mass_split (NullMeasurableSpace X μ) _ M
    μ.completion Ref Surv hRef hSurv hfin

theorem good_mass_lower (μ : Measure X) (Ref Surv : Fin M → Set X)
    (hRef : ∀ i, NullMeasurableSet (Ref i) μ)
    (hSurv : ∀ i, NullMeasurableSet (Surv i) μ)
    (hfin : ∀ i, μ (Ref i) ≠ ∞) (hsub : ∀ i, Surv i ⊆ Ref i) :
    mass μ Ref-2*(mass μ Ref-mass μ Surv) ≤ mass μ (goodRows Ref Surv) :=
  @SourceGoodMass.good_mass_lower (NullMeasurableSpace X μ) _ M
    μ.completion Ref Surv hRef hSurv hfin hsub

theorem pieces_nullMeasurable (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ)
    (hY : ∀ i, NullMeasurableSet (Y i) μ) (g : Fin J) :
    (∀ i, NullMeasurableSet (survivingPiece μ Full Y assign a g i) μ) ∧
      (∀ i, NullMeasurableSet (markedPiece μ Full Y assign a g i) μ) :=
  @SourceDensityPruningGeometry.pieces_measurable (NullMeasurableSpace X μ) _ M J
    μ.completion Full Y assign a hY g

/-- The original mask construction has the same literal fractions (3.5),
(3.9), and (3.10) for all completed-measurable input rows. No rows, incidence
patterns or retained labels are changed on a null exceptional set. -/
theorem source_fractions (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) {kappa : ℝ} (hk : 0 ≤ kappa)
    (hY : ∀ i, NullMeasurableSet (Y i) μ) (hfin : ∀ i, μ (Y i) ≠ ∞)
    (hmass : kappa*mass μ Full ≤ mass μ Y) :
    let S := survivors μ Full Y (kappa/8)
    let Ref := piece assign Y
    let Surv := piece assign S
    mass μ Y-mass μ S ≤ mass μ Y/8 ∧
      3*mass μ Y/4 ≤ ∑ g, mass μ (goodRows (Ref g) (Surv g)) ∧
      5*mass μ Y/8 ≤ ∑ g ∈ retained μ Ref Surv, mass μ (goodRows (Ref g) (Surv g)) :=
  @SourceDensityPruning.source_fractions (NullMeasurableSpace X μ) _ M J
    μ.completion Full Y assign kappa hk hY hfin hmass

end
end KakeyaFormal.LebesgueDensityPruning
