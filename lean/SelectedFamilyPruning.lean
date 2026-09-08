import SelectedColoredFamilies
import SelectedOutputDensity

/-! The actual selected-output groups are normalized, colored and pruned from
the original normalized-mesh spatial ball bound. The analytic constant is
chosen before all original configurations, selections and spatial coefficients. -/
namespace KakeyaFormal.SelectedFamilyPruning
open Finset ActualLabelSelection LegalAngleSamples SelectedOutputPairs SelectedOutputSlabs
open SelectedBaseFamilies SelectedColoredFamilies
open scoped BigOperators
noncomputable section
open Classical
set_option maxHeartbeats 1600000

/-- The exact size of the common computed residue palette. -/
def paletteCount (k : ℕ) (width : ℝ) : ℕ :=
  (SelectedSlabGeometry.colorModulus (2*width+((k+1 : ℕ) : ℝ)/2))^(k+1)

theorem palette_modulus_pos (k : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    0 < SelectedSlabGeometry.colorModulus (2*width+((k+1 : ℕ) : ℝ)/2) :=
  (SelectedSlabGeometry.color_modulus_bounds (by positivity)).1

theorem paletteCount_pos (k : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    0 < paletteCount k width := pow_pos (palette_modulus_pos k hw) _

theorem capCoefficient_ge_one (k : ℕ) {width d C : ℝ}
    (hw : 0 ≤ width) (hd : 0 ≤ d) (hC : 1 ≤ C) :
    1 ≤ capCoefficient (k := k) (width := width) d C := by
  have hb : 1 ≤ 16+2*(2*width+((k+1 : ℕ) : ℝ)/2) := by
    have hk0 := Nat.cast_nonneg (α := ℝ) (k+1)
    linarith
  have hp := Real.one_le_rpow hb hd
  exact (one_mul (1:ℝ)).symm.trans_le
    (mul_le_mul hC hp (by norm_num) (by linarith))

/-- Full actual normalized family construction and grouped incidence pruning.
The only analytic input is the normalized discrete estimate. The spatial input
is the literal all-radius count on the original union labels at delta/(1+2width).
The resulting families and retained set are constructed existentially here. -/
theorem constructed_pruning {k : ℕ} {width R d d' p eps : ℝ}
    (hw : 0 ≤ width) (hd : 0 ≤ d)
    (hestimate : DiscreteEstimate (k+2) d d' p) (hp : 1 ≤ p) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} {δ lam kappa : ℝ}
      {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
      {S : SampleSystem F H δ lam kappa width}
      (hkappa : 0 < kappa) (hadm : F.Admissible width δ)
      (P : Selection S hkappa hw hadm) (D : ∀ q, LineData P q) (C : ℝ),
      0 < δ → δ ≤ 1 → 1 ≤ C → F.Bounded R →
      (∀ x : Space (k+1), ∀ r : ℝ, δ/(1+2*width) ≤ r →
        (((F.unionCells).filter (fun z => dist (cellCenter (δ/(1+2*width)) z) x ≤ r)).card : ℝ) ≤
          C*(r/(δ/(1+2*width)))^d) →
      ∃ A : ∀ g, GroupData P D R d C g,
      ∃ T : Finset (GroupedCumulative.Record (k := k+2) (coloredPopulation P D)),
        T ⊆ SelectedColoredFamilies.incidences P D A ∧
        ((SelectedColoredFamilies.incidences P D A).card : ℝ)/2 < (T.card : ℝ) ∧
        (∑ b ∈ T.image (ActualGroupedIncidence.position (base P D) (color P)),
          (GroupedIncidence.degree T (ActualGroupedIncidence.position (base P D) (color P)) b : ℝ)^2) ≤
        ((2:ℝ)^(p+1)*(paletteCount k width : ℝ)*(1/(δ/(1+2*width)))/
          ((c*(capCoefficient (k := k) (width := width) d C)⁻¹*(δ/(1+2*width))^(d-d'+eps))*
            (SelectedOutputDensity.rho P D (color P) (shading P D A))^(p-1)))*(T.card : ℝ) := by
  let _ : NeZero (SelectedSlabGeometry.colorModulus (2*width+((k+1 : ℕ) : ℝ)/2)) :=
    ⟨(palette_modulus_pos k hw).ne'⟩
  have hpalette : Fintype.card (Fin (k+1) → ZMod
      (SelectedSlabGeometry.colorModulus (2*width+((k+1 : ℕ) : ℝ)/2))) = paletteCount k width := by
    simp only [Fintype.card_fun,Fintype.card_fin,ZMod.card,paletteCount]
  obtain ⟨c,hc,hprune⟩ := GroupedCumulative.discrete_pruning
    (geom := geometry (k := k) (width := width) R) hestimate hp heps
  refine ⟨c,hc,?_⟩
  intro M δ lam kappa F H S hkappa hadm P D C hδ hδ1 hC hbounded hball
  let A := normalizedGroup P D hδ hδ1 (zero_le_one.trans hC) hbounded hball
  have hnorm : 0 < δ/(1+2*width) := div_pos hδ (by linarith)
  have hnorm1 : δ/(1+2*width) ≤ 1 := (div_le_one (by linarith : 0 < 1+2*width)).mpr (by linarith)
  have hgeom := colored_geometry P D A hδ
  have hshade : ∀ r ∈ SelectedColoredFamilies.incidences P D A,
      r.2 ∈ (coloredFamily P D A r.1.1).shade r.1.2 :=
    ActualGroupedIncidence.incidence_admissible_record (base P D) (color P)
      (tube P D A) (shading P D A)
  obtain ⟨T,hT,hretain,hupper⟩ := hprune (ColoredGroup P D) (Cell (k+1) × ℕ)
    (Fin (k+1) → ZMod (SelectedSlabGeometry.colorModulus (2*width+((k+1 : ℕ) : ℝ)/2)))
    (fun g => g.val.1) (fun g => g.val.2)
    (ActualGroupedIncidence.group_encoding_injective (base P D) (color P))
    (coloredPopulation P D) (δ/(1+2*width)) (capCoefficient (k := k) (width := width) d C)
    hnorm hnorm1 (capCoefficient_ge_one k hw hd hC)
    (coloredFamily P D A) (SelectedColoredFamilies.incidences P D A)
    (incidence_nonempty P D A) hshade
    (fun g => (hgeom g).1) (fun g => (hgeom g).2.1)
    (fun g => (hgeom g).2.2.1) (fun g => (hgeom g).2.2.2)
  have hpop : ∑ g : ColoredGroup P D, (coloredPopulation P D g : ℝ) =
      ((AngleFiberSelection.outputSupport P.retained).card : ℝ) := by
    exact_mod_cast population_total P D
  refine ⟨A,T,hT,hretain,?_⟩
  rw [hpop,hpalette] at hupper
  dsimp only [SelectedOutputDensity.rho]
  convert hupper using 1
  congr! 12
  unfold SelectedColoredFamilies.incidences SelectedBaseFamilies.base
  congr! 20

end
end KakeyaFormal.SelectedFamilyPruning
