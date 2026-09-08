import SelectedOutputSlabs
import GroupedSlabPositions
import ClosingEnergyAlgebra

/-! Actual selected original endpoint representatives supply the closing-energy
witness for every normalized shaded-cell incidence and every pruning subset. -/
namespace KakeyaFormal.SelectedOutputWitness
open Finset ActualLabelSelection AngleFiberSelection LegalAngleSamples
open SelectedOutputPairs SelectedOutputSlabs SelectedFiberLift SlabNormalization
open SelectedLiftWitness ActualGroupedIncidence PivotWitnesses PivotSupport
open scoped BigOperators
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
    {δ lam kappa width : ℝ} {S : SampleSystem F H δ lam kappa width}
    {hkappa : 0 < kappa} {hwidth : 0 ≤ width} {hadm : F.Admissible width δ}
    (P : Selection S hkappa hwidth hadm)
    (D : ∀ q : Index P, LineData P q)

/-- The exact inverse common translation recovers a cell of the same selected
original output, rather than an arbitrary cell from another lift fiber. -/
theorem unshift_mem (q : Index P) (z : Cell (k+2))
    (hz : z ∈ (D q).cells.image (shiftCell (δ/(1+2*width)) (D q).slab)) :
    unshiftCell (δ/(1+2*width)) (D q).slab z ∈ (D q).cells := by
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hz
  simpa only [unshift_shift] using hv

/-- The actual selected representative is attached to its original pivot,
intermediate, endpoint labels and centered lifted cell. -/
def cellSample (hδ : 0 < δ) (q : Index P) (z : Cell (k+2))
    (hz : z ∈ (D q).cells.image (shiftCell (δ/(1+2*width)) (D q).slab)) :
    AttachedSample (k+1) (δ/(1+2*width)) (kappa/(1+2*width))
      (errorConstant (k+1) (2*width)) :=
  attach (reference P q)
    ((D q).representative ⟨unshiftCell (δ/(1+2*width)) (D q).slab z,unshift_mem P D q z hz⟩)
    (P.chosen_output q).2 (div_pos hδ (by linarith)) (by linarith)
    ((raw_pivot P q _ ((D q).representative_mem _)).trans (reference_pivot P q).symm)
    (intermediate_close P q)

theorem cellSample_occupied (hδ : 0 < δ) (q : Index P) (z : Cell (k+2))
    (hz : z ∈ (D q).cells.image (shiftCell (δ/(1+2*width)) (D q).slab)) :
    (cellSample P D hδ q z hz).firstLabel ∈ F.unionCells ∧
      (cellSample P D hδ q z hz).secondLabel ∈ F.unionCells := by
  have hh := (D q).representative_occupied P
    ⟨unshiftCell (δ/(1+2*width)) (D q).slab z,unshift_mem P D q z hz⟩
  exact ⟨mem_biUnion.mpr ⟨(P.chosen_angle q).val.2.1,mem_univ _,hh.1⟩,
    mem_biUnion.mpr ⟨(P.chosen_angle q).val.2.2,mem_univ _,hh.2⟩⟩

theorem cellSample_position (hδ : 0 < δ) (q : Index P) (z : Cell (k+2))
    (hz : z ∈ (D q).cells.image (shiftCell (δ/(1+2*width)) (D q).slab)) :
    energyPosition (cellSample P D hδ q z hz).label =
      originalPosition (δ/(1+2*width)) ((D q).base P,z) := by
  change ((reference P q).pivotLabel,
      splitCell (liftedCell (reference P q)
        ((D q).representative ⟨_,unshift_mem P D q z hz⟩))) = _
  rw [(D q).representative_cell,reference_pivot]
  rfl

/-- An actual selected-cell witness exists even before the incidence set is
formed. It is used only to totalize the map outside actual incidences. -/
def defaultSample (hδ : 0 < δ) :
    AttachedSample (k+1) (δ/(1+2*width)) (kappa/(1+2*width))
      (errorConstant (k+1) (2*width)) := by
  let q : Index P := Classical.choice (index_nonempty P)
  let z := ((D q).cells_nonempty P).choose
  exact cellSample P D hδ q (shiftCell (δ/(1+2*width)) (D q).slab z)
    (mem_image.mpr ⟨z,((D q).cells_nonempty P).choose_spec,rfl⟩)

variable {C : Type*} (color : Index P → C) (shading : Index P → Finset (Cell (k+2)))
    (hsub : ∀ q, shading q ⊆ (D q).cells.image (shiftCell (δ/(1+2*width)) (D q).slab))

/-- Every actual grouped record chooses its own original selected endpoint
pair; values outside the actual incidence set do not enter any count. -/
def groupedSample (hδ : 0 < δ)
    (r : GroupedCumulative.Record (k:=k+2) (population (fun q => (D q).base P) color)) :
    AttachedSample (k+1) (δ/(1+2*width)) (kappa/(1+2*width))
      (errorConstant (k+1) (2*width)) :=
  if hr : r ∈ incidences (fun q => (D q).base P) color shading then
    cellSample P D hδ (indexEquiv (fun q => (D q).base P) color r.1) r.2
      (hsub _ ((mem_incidences _ _ shading r).mp hr))
  else defaultSample P D hδ

theorem groupedSample_occupied (hδ : 0 < δ)
    (r : GroupedCumulative.Record (k:=k+2) (population (fun q => (D q).base P) color))
    (hr : r ∈ incidences (fun q => (D q).base P) color shading) :
    (groupedSample P D color shading hsub hδ r).firstLabel ∈ F.unionCells ∧
      (groupedSample P D color shading hsub hδ r).secondLabel ∈ F.unionCells := by
  simp only [groupedSample,dif_pos hr]
  exact cellSample_occupied P D hδ _ _ _

theorem groupedSample_position (hδ : 0 < δ)
    (r : GroupedCumulative.Record (k:=k+2) (population (fun q => (D q).base P) color))
    (hr : r ∈ incidences (fun q => (D q).base P) color shading) :
    energyPosition (groupedSample P D color shading hsub hδ r).label =
      originalPosition (δ/(1+2*width)) (position (fun q => (D q).base P) color r) := by
  simp only [groupedSample,dif_pos hr]
  rw [position_original]
  exact cellSample_position P D hδ _ _ _

include hsub in
/-- The closing lower-energy bound now uses actual representatives of the
selected output fibers. No supplied sample, endpoint-occupancy, position
identity, or energy comparison is needed. -/
theorem retained_energy (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hkappa1 : kappa ≤ 1)
    (hscale : 2*errorConstant (k+1) (2*width)*(δ/(1+2*width)) ≤
      (kappa/(1+2*width))^5/4)
    (T : Finset (GroupedCumulative.Record (k:=k+2) (population (fun q => (D q).base P) color)))
    (hT : T ⊆ incidences (fun q => (D q).base P) color shading) :
    (T.card:ℝ)^2 ≤ (F.unionCells.card:ℝ)^2*
      (ClosingEnergyAlgebra.pivotCoefficient (k+1) (errorConstant (k+1) (2*width))/(δ/(1+2*width)))*
      (ClosingEnergyAlgebra.liftCoefficient (k+1) (errorConstant (k+1) (2*width))/(kappa/(1+2*width))^5)*
      ∑ p ∈ T.image (position (fun q => (D q).base P) color),
        (GroupedIncidence.degree T (position (fun q => (D q).base P) color) p:ℝ)^2 := by
  have hR : 0 < 1+2*width := by linarith
  have hdim : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
  have hpos := GroupedSlabPositions.restricted_position_legal
    (fun q => (D q).base P) color (fun q => (D q).cells) shading hsub
    (fun q => (D q).center_slab) T hT
  have hh := ClosingEnergyAlgebra.grouped_witness_bound T
    (groupedSample P D color shading hsub hδ) (position (fun q => (D q).base P) color) F.unionCells
    (div_pos hδ hR) ((div_le_one hR).mpr (by linarith))
    (by dsimp [errorConstant]; push_cast; linarith :
      (1:ℝ)/2 ≤ errorConstant (k+1) (2*width))
    (div_pos hkappa hR) ((div_le_one hR).mpr (by linarith)) hscale
    (fun r hr => groupedSample_occupied P D color shading hsub hδ r (hT hr)) hpos
    (fun r hr => groupedSample_position P D color shading hsub hδ r (hT hr))
  unfold GroupedIncidence.degree
  convert hh using 1
  congr! 10

end
end KakeyaFormal.SelectedOutputWitness
