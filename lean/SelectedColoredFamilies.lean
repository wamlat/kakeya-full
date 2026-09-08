import SelectedBaseFamilies

/-! Actual normalized base families are returned to their unchanged original
output indices and partitioned by the computed common residue palette. -/
namespace KakeyaFormal.SelectedColoredFamilies
open Finset ActualLabelSelection LegalAngleSamples SelectedOutputPairs SelectedOutputSlabs
open SelectedBaseFamilies
open scoped BigOperators
noncomputable section
open Classical
set_option maxHeartbeats 1600000

variable {k M : ℕ} {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
    {δ lam kappa width : ℝ} {S : SampleSystem F H δ lam kappa width}
    {hkappa : 0 < kappa} {hwidth : 0 ≤ width} {hadm : F.Admissible width δ}
    (P : Selection S hkappa hwidth hadm) (D : ∀ q, LineData P q)

/-- The actual original output is located in its unique base group. -/
def locate (q : Index P) : (g : Group P D) × Fin (population P D g) :=
  (ActualGroupedIncidence.indexEquiv (base P D) (fun _ => ())).symm q

theorem original_locate (q : Index P) :
    original P D (locate P D q).1 (locate P D q).2 = q :=
  (ActualGroupedIncidence.indexEquiv (base P D) (fun _ => ())).apply_symm_apply q

theorem locate_original (g : Group P D) (j : Fin (population P D g)) :
    locate P D (original P D g j) = ⟨g,j⟩ :=
  (ActualGroupedIncidence.indexEquiv (base P D) (fun _ => ())).symm_apply_apply ⟨g,j⟩

theorem locate_base (q : Index P) : base P D q = (locate P D q).1.val.1 := by
  have hh := original_base P D (locate P D q).1 (locate P D q).2
  rwa [original_locate] at hh

theorem original_exists (g : Group P D) (q : Index P) (hb : base P D q = g.val.1) :
    ∃ j, original P D g j = q := by
  rcases he : locate P D q with ⟨g',j⟩
  have ho : original P D g' j=q := by
    have hh := original_locate P D q
    rw [he] at hh
    exact hh
  have hg : g'=g := by
    apply Subtype.ext
    apply Prod.ext
    · exact (original_base P D g' j).symm.trans (by rw [ho]; exact hb)
    · exact Subsingleton.elim _ _
  subst g'
  exact ⟨j,ho⟩

variable {R d C : ℝ} (A : ∀ g, GroupData P D R d C g)

def tube (q : Index P) : UnitTube (k+2) :=
  (A (locate P D q).1).family.tube (locate P D q).2

def shading (q : Index P) : Finset (Cell (k+2)) :=
  (A (locate P D q).1).family.shade (locate P D q).2

theorem tube_original (g : Group P D) (j : Fin (population P D g)) :
    tube P D A (original P D g j) = (A g).family.tube j := by
  unfold tube
  rw [locate_original P D g j]

theorem shading_original (g : Group P D) (j : Fin (population P D g)) :
    shading P D A (original P D g j) = (A g).family.shade j := by
  unfold shading
  rw [locate_original P D g j]

theorem direction (q : Index P) :
    (tube P D A q).direction = LiftGraph.graphDirection (slope P q) := by
  have hh := (A (locate P D q).1).direction (locate P D q).2
  rw [original_locate P D q] at hh
  convert hh using 1
  congr! 10

theorem shade_subset (q : Index P) : shading P D A q ⊆
    (D q).cells.image (SlabNormalization.shiftCell (δ/(1+2*width)) (base P D q).2) := by
  have hh := (A (locate P D q).1).shade_subset (locate P D q).2
  rw [original_locate P D q] at hh
  rw [locate_base P D q]
  convert hh using 1
  congr! 10

theorem shade_mass (q : Index P) : (commonK P : ℝ)/3 ≤ ((shading P D A q).card : ℝ) :=
  (A (locate P D q).1).shade_mass (locate P D q).2

theorem shade_nonempty (q : Index P) : (shading P D A q).Nonempty :=
  (A (locate P D q).1).nonempty_shade (locate P D q).2

theorem admissible (q : Index P) (z : Cell (k+2)) (hz : z ∈ shading P D A q) :
    ∃ t ∈ Set.Icc (0:ℝ) 1, dist (cellCenter (δ/(1+2*width)) z) ((tube P D A q).axisPoint t) ≤
      (geometry (k := k) (width := width) R).width*(δ/(1+2*width)) :=
  (A (locate P D q).1).admissible (locate P D q).2 z hz

theorem bounded (q : Index P) : ‖(tube P D A q).base‖ ≤
    (geometry (k := k) (width := width) R).radius :=
  (A (locate P D q).1).bounded (locate P D q).2

/-- The cap count over original output indices in any actual base equals a
restriction of that base's already constructed normalized tube family. -/
theorem base_cap_count (b : Cell (k+1) × ℕ) (v : Space (k+2))
    (hv : ‖v‖ = 1) (r : ℝ) (hr : δ/(1+2*width) ≤ r) (hr1 : r ≤ 1) :
    (((univ : Finset (Index P)).filter (fun q => base P D q=b ∧
      projectiveDistance (tube P D A q).direction v ≤ r)).card : ℝ) ≤
        capCoefficient (k := k) (width := width) d C*(r/(δ/(1+2*width)))^d := by
  let V := (univ : Finset (Index P)).filter (fun q => base P D q=b ∧
    projectiveDistance (tube P D A q).direction v ≤ r)
  by_cases hV : V.Nonempty
  · obtain ⟨q0,hq0⟩ := hV
    let g := (locate P D q0).1
    have hgb : g.val.1=b := (locate_base P D q0).symm.trans (mem_filter.mp hq0).2.1
    let U := (univ : Finset (Fin (population P D g))).filter
      (fun j => projectiveDistance ((A g).family.tube j).direction v ≤ r)
    have hsub : V ⊆ U.image (original P D g) := by
      intro q hq
      have hb := (mem_filter.mp hq).2.1
      obtain ⟨j,hj⟩ := original_exists P D g q (hb.trans hgb.symm)
      have ht : tube P D A q=(A g).family.tube j := by rw [← hj,tube_original]
      exact mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,by
        rw [← ht]; exact (mem_filter.mp hq).2.2⟩,hj⟩
    have hh : V.card ≤ U.card := (card_le_card hsub).trans (card_image_le)
    exact (Nat.cast_le.mpr hh).trans ((A g).cap v hv r hr hr1)
  · have hz : V=∅ := not_nonempty_iff_eq_empty.mp hV
    change (V.card : ℝ) ≤ _
    rw [hz,card_empty,Nat.cast_zero]
    let q0 := Classical.choice (index_nonempty P)
    exact (Nat.cast_nonneg _).trans ((A (locate P D q0).1).cap v hv r hr hr1)

/-- One common computed residue color for every original output. -/
def color (q : Index P) : Fin (k+1) → ZMod
    (SelectedSlabGeometry.colorModulus (2*width+((k+1 : ℕ) : ℝ)/2)) :=
  SelectedSlabGeometry.residueColor (2*width+((k+1 : ℕ) : ℝ)/2)
    (fun q => (P.chosen_output q).2) q

abbrev ColoredGroup := ActualGroupedIncidence.Group (base P D) (color P)
abbrev coloredPopulation (g : ColoredGroup P D) :=
  ActualGroupedIncidence.population (base P D) (color P) g

def coloredFamily (g : ColoredGroup P D) : TubeFamily (k+2) (coloredPopulation P D g) :=
  ActualGroupedIncidence.family (base P D) (color P) (tube P D A) (shading P D A) g

/-- Every original output occurs in one actual pivot/slab/color family, whose
separation is derived from the computed color and the actual pivot residual. -/
theorem colored_geometry (hδ : 0 < δ) (g : ColoredGroup P D) :
    (coloredFamily P D A g).Admissible (geometry (k := k) (width := width) R).width (δ/(1+2*width)) ∧
    (coloredFamily P D A g).Separated ((geometry (k := k) (width := width) R).separation*(δ/(1+2*width))) ∧
    (coloredFamily P D A g).Bounded (geometry (k := k) (width := width) R).radius ∧
    (coloredFamily P D A g).CapBound (δ/(1+2*width)) d (capCoefficient (k := k) (width := width) d C) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact ActualGroupedIncidence.family_admissible (base P D) (color P)
      (tube P D A) (shading P D A) (admissible P D A) g
  · exact ActualGroupedGeometry.graph_family_separated (base P D) (fun q => (P.chosen_output q).2)
      (slope P) (tube P D A) (shading P D A) (div_pos hδ (by linarith)) (by positivity)
      (line_output_injective P D) (SelectedOutputSlabs.reference_slope_bound P)
      (direction P D A) (SelectedOutputSlabs.reference_pivot_residual P hδ) g
  · exact ActualGroupedIncidence.family_bounded (base P D) (color P)
      (tube P D A) (shading P D A) (bounded P D A) g
  · apply ActualGroupedIncidence.family_cap_bound (base P D) (color P)
      (tube P D A) (shading P D A) (g := g)
    intro b v hv r hr hr1
    convert base_cap_count P D A b v hv r hr hr1 using 1
    congr! 10

/-- The final actual normalized incidence set, ready for grouped pruning. -/
def incidences : Finset (GroupedCumulative.Record (k := k+2) (coloredPopulation P D)) :=
  ActualGroupedIncidence.incidences (base P D) (color P) (shading P D A)

theorem incidence_mass : (commonK P : ℝ)*((AngleFiberSelection.outputSupport P.retained).card : ℝ)/3 ≤
    ((incidences P D A).card : ℝ) := by
  have hh := ActualGroupedIncidence.incidence_mass_lower (base P D) (color P)
    (shading P D A) (shade_mass P D A)
  simp only [Fintype.card_fin] at hh
  convert hh using 1
  congr! 10

theorem incidence_nonempty : (incidences P D A).Nonempty := by
  let q := Classical.choice (index_nonempty P)
  exact ActualGroupedIncidence.incidences_nonempty _ _ _ ⟨q,shade_nonempty P D A q⟩

/-- The total count remains the exact original output support cardinality. -/
theorem population_total : ∑ g : ColoredGroup P D, coloredPopulation P D g =
    (AngleFiberSelection.outputSupport P.retained).card := by
  simpa only [Fintype.card_fin] using ActualGroupedIncidence.sum_population (base P D) (color P)

end
end KakeyaFormal.SelectedColoredFamilies
