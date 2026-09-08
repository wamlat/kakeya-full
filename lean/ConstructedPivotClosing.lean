import SelectedFamilyPruning
import SelectedOutputClosing

/-! The normalized discrete estimate is applied to the actual families built
from selected original outputs. The same constructed incidences supply the
closing witnesses, so no retained-mass or energy bound is supplied by a caller. -/
namespace KakeyaFormal.ConstructedPivotClosing
open Finset ActualLabelSelection LegalAngleSamples AngleFiberSelection
open SelectedOutputPairs SelectedOutputSlabs SelectedBaseFamilies SelectedColoredFamilies
open scoped BigOperators
noncomputable section
open Classical

/-- Complete actual grouped analytic/energy composition. Its constant precedes
the original family, selected sample fibers, common slabs and spatial cutoff.
All normalized tube/shading families and the retained energy set are constructed.
The actual lower cumulative density is included for the next population step. -/
theorem construct {k : ℕ} {width R d d' r eps : ℝ}
    (hw : 0 ≤ width) (hd : 0 ≤ d)
    (hestimate : DiscreteEstimate (k+2) d d' r) (hr : 1 ≤ r) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} {δ lam kappa : ℝ}
      {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
      {S : SampleSystem F H δ lam kappa width}
      (hkappa : 0 < kappa) (hadm : F.Admissible width δ)
      (P : Selection S hkappa hw hadm) (D : ∀ q, LineData P q) (C : ℝ),
      0 < δ → δ ≤ 1 → kappa ≤ 1 → 1 ≤ C → F.Bounded R →
      (∀ x : Space (k+1), ∀ radius : ℝ, δ/(1+2*width) ≤ radius →
        ((F.unionCells.filter (fun z => dist (cellCenter (δ/(1+2*width)) z) x ≤ radius)).card:ℝ) ≤
          C*(radius/(δ/(1+2*width)))^d) →
      2*SelectedLiftWitness.errorConstant (k+1) (2*width)*(δ/(1+2*width)) ≤
        (kappa/(1+2*width))^5/4 →
      ∃ A : ∀ g, GroupData P D R d C g,
        let rho := SelectedOutputDensity.rho P D (color P) (shading P D A)
        0 < rho ∧
        SelectedOutputDensity.lowerCoefficient k width*kappa^6*((2^P.level:ℕ)*δ) ≤ rho ∧
        c*kappa^5*(capCoefficient (k:=k) (width:=width) d C)⁻¹*rho^r*
          δ^(d-d'+1+eps)*(outputSupport P.retained).card ≤ (F.unionCells.card:ℝ)^2 := by
  obtain ⟨c₀,hc₀,hprune⟩ := SelectedFamilyPruning.constructed_pruning
    (R:=R) hw hd hestimate hr heps
  let J : ℝ := SelectedFamilyPruning.paletteCount k width
  have hJ : 0 < J := by
    dsimp [J]
    exact_mod_cast SelectedFamilyPruning.paletteCount_pos k hw
  let c := SelectedOutputClosing.originalCoefficient k width c₀ J r (d-d'+1+eps)
  have hc : 0 < c := SelectedOutputClosing.originalCoefficient_pos k hw hc₀ hJ
  refine ⟨c,hc,?_⟩
  intro M δ lam kappa F H S hkappa hadm P D C hδ hδ1 hkappa1 hC hbounded hball hscale
  obtain ⟨A,T,hT,hretain,hupper⟩ := hprune hkappa hadm P D C hδ hδ1 hC hbounded hball
  have hsub : ∀ q, shading P D A q ⊆
      (D q).cells.image (SlabNormalization.shiftCell (δ/(1+2*width)) (D q).slab) :=
    shade_subset P D A
  have hcap : 0 < capCoefficient (k:=k) (width:=width) d C :=
    zero_lt_one.trans_le (SelectedFamilyPruning.capCoefficient_ge_one k hw hd hC)
  have hh := SelectedOutputClosing.retained_closing P D (color P) (shading P D A)
    hδ hδ1 hkappa1 hc₀ hJ hcap hsub (shade_mass P D A) hscale T hT hretain.le hupper
  exact ⟨A,SelectedOutputDensity.rho_pos P D (color P) (shading P D A) hδ (shade_mass P D A),
    SelectedOutputDensity.rho_lower P D (color P) (shading P D A) hδ (shade_mass P D A),hh⟩

end
end KakeyaFormal.ConstructedPivotClosing
