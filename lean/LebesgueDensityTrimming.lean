import MeasurableDensityTrimming
import LebesgueRepresentatives

/-! Exact prescribed-mass trimming in Section 8.1 for original completed-
Lebesgue shadings. The output is a Borel subset of each original input, with
the exact prescribed volume and the same original tube family. -/
namespace KakeyaFormal.LebesgueDensityTrimming
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Every mass between zero and the original bounded shading mass is realized
by an actual measurable subset, including both endpoints. -/
theorem exists_exact_subset {n : ℕ} {Y : Set (Space (n+1))} {a : ℝ}
    (hY : NullMeasurableSet Y volume) (hbounded : Bornology.IsBounded Y)
    (ha : 0 ≤ a) (hle : a ≤ (volume : Measure (Space (n+1))).real Y) :
    ∃ Z : Set (Space (n+1)), MeasurableSet Z ∧ Z ⊆ Y ∧ volume Z ≠ ∞ ∧
      (volume : Measure (Space (n+1))).real Z = a := by
  obtain ⟨Y₀,hsub,hmeas,hae⟩ := hY.exists_measurable_subset_ae_eq
  have hmass : (volume : Measure (Space (n+1))).real Y₀ = volume.real Y :=
    measureReal_congr hae
  obtain ⟨Z,hZ,hZY,hfin,hexact⟩ := MeasurableDensityTrimming.exists_exact_subset
    hmeas (hbounded.subset hsub) ha (hmass ▸ hle)
  exact ⟨Z,hZ,hZY.trans hsub,hfin,hexact⟩

/-- Simultaneous trimming returns the existing exact-volume output record
with the ORIGINAL input rows. All its union, total-mass and two-ends methods
therefore apply directly, without changing the input family. -/
theorem construct {n M : ℕ} (F : TubeFamily (n+1) M)
    (Y : Fin M → Set (Space (n+1))) {radius a : ℝ}
    (hY : ∀ i, NullMeasurableSet (Y i) volume)
    (hsub : ∀ i, Y i ⊆ (F.tube i).carrier radius)
    (ha : 0 ≤ a) (hle : ∀ i, a ≤ (volume : Measure (Space (n+1))).real (Y i)) :
    Nonempty (MeasurableDensityTrimming.Output F Y radius a) := by
  have hex (i : Fin M) := exists_exact_subset (hY i)
    ((TubeVolume.carrier_compact (F.tube i) radius).isBounded.subset (hsub i)) ha (hle i)
  choose Z hm hs hf he using hex
  exact ⟨⟨Z,hm,hs,fun i => (hs i).trans (hsub i),hf,he⟩⟩

end
end KakeyaFormal.LebesgueDensityTrimming
