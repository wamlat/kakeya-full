import SelectedOutputSlabs
import ActualGroupedGeometry

/-! Actual unit-tube normalization of every original selected pivot/slab group.
The normalized spatial ball bound is tested on the same original integer labels;
tube geometry is never presumed at the changed mesh. -/
namespace KakeyaFormal.SelectedBaseFamilies
open Finset ActualLabelSelection LegalAngleSamples LegalLabeledSamples
open SelectedOutputPairs SelectedOutputSlabs SelectedFiberLift SlabNormalization
open scoped BigOperators
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
    {δ lam kappa width : ℝ} {S : SampleSystem F H δ lam kappa width}
    {hkappa : 0 < kappa} {hwidth : 0 ≤ width} {hadm : F.Admissible width δ}
    (P : Selection S hkappa hwidth hadm) (D : ∀ q, LineData P q)

def base (q : Index P) : Cell (k+1) × ℕ := (D q).base P
abbrev Group := ActualGroupedIncidence.Group (base P D) (fun _ => ())
abbrev population (g : Group P D) := ActualGroupedIncidence.population (base P D) (fun _ => ()) g
abbrev original (g : Group P D) (j : Fin (population P D g)) :=
  ActualGroupedIncidence.original (base P D) (fun _ => ()) g j

theorem original_base (g : Group P D) (j : Fin (population P D g)) :
    base P D (original P D g j) = g.val.1 :=
  ActualGroupedIncidence.original_base (base P D) (fun _ => ()) g j

def slope (q : Index P) : Space (k+1) :=
  (reference P q).endpoints.coefficient • (normalizedAngle P q).second

def geometry (R : ℝ) : Normalization :=
  SelectedSlabGeometry.geometry (k+1) (PrunedGraphLift.regionRadius width R)

def capCoefficient (d C : ℝ) : ℝ := C*(16+2*(2*width+((k+1 : ℕ) : ℝ)/2))^d

/-- The actual intermediate label is in the original union used by spatial
pruning, before the legal-sample homothety. -/
theorem intermediate_in_union (q : Index P) : (P.chosen_output q).2 ∈ F.unionCells := by
  obtain ⟨p,hp⟩ := chosen_samples_nonempty P q
  have hl := S.legal (P.chosen_angle q) p (P.chosen_samples_actual q p hp).1
  have hm : p.1=(P.chosen_output q).2 := sample_intermediate P q ⟨p,hp⟩
  rw [← hm]
  exact mem_biUnion.mpr ⟨(P.chosen_angle q).val.2.1,mem_univ _,hl.1⟩

/-- Concrete normalized tube and shading data for one actually used base. -/
structure GroupData (R d C : ℝ) (g : Group P D) where
  family : TubeFamily (k+2) (population P D g)
  direction : ∀ j, (family.tube j).direction = LiftGraph.graphDirection (slope P (original P D g j))
  shade_subset : ∀ j, family.shade j ⊆
    ((D (original P D g j)).cells).image (shiftCell (δ/(1+2*width)) g.val.1.2)
  shade_mass : ∀ j, (commonK P : ℝ)/3 ≤ ((family.shade j).card : ℝ)
  admissible : family.Admissible (geometry (k := k) (width := width) R).width (δ/(1+2*width))
  bounded : family.Bounded (geometry (k := k) (width := width) R).radius
  cap : family.CapBound (δ/(1+2*width)) d (capCoefficient (k := k) (width := width) d C)
  nonempty_shade : ∀ j, (family.shade j).Nonempty
  union_subset : family.unionCells ⊆
    (univ.biUnion (fun j => (D (original P D g j)).cells)).image
      (shiftCell (δ/(1+2*width)) g.val.1.2)
  union_card : family.unionCells.card ≤ (univ.biUnion (fun j => (D (original P D g j)).cells)).card

/-- Actual group normalization and the actual normalized spatial ball test
construct all cap and tube fields with fixed geometric constants. -/
theorem group_exists {R d C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 0 ≤ C) (hbounded : F.Bounded R)
    (hball : ∀ x : Space (k+1), ∀ r : ℝ, δ/(1+2*width) ≤ r →
      (((F.unionCells).filter (fun z => dist (cellCenter (δ/(1+2*width)) z) x ≤ r)).card : ℝ) ≤
        C*(r/(δ/(1+2*width)))^d)
    (g : Group P D) : Nonempty (GroupData P D R d C g) := by
  let e := original P D g
  let aa := fun j => normalizedAngle P (e j)
  let fc := fun j => firstCoord S (P.chosen_angle (e j))
  let sc := fun j => secondCoord S (P.chosen_angle (e j))
  let ref := fun j => reference P (e j)
  let rawPairs := fun j => raw P (e j)
  let cells := fun j => (D (e j)).cells
  let label := fun j => (P.chosen_output (e j)).2
  have hRnorm : 0 < 1+2*width := by linarith
  have hδnorm := div_pos hδ hRnorm
  have hδnorm1 : δ/(1+2*width) ≤ 1 := (div_le_one hRnorm).mpr (by linarith)
  have hknorm := div_pos hkappa hRnorm
  have hslab (j) (z) (hz : z ∈ cells j) :
      (g.val.1.2 : ℝ) ≤ (δ/(1+2*width))*(z 0 : ℝ) ∧
        (δ/(1+2*width))*(z 0 : ℝ) < (g.val.1.2 : ℝ)+1 := by
    have hb : (D (e j)).slab = g.val.1.2 := congrArg Prod.snd (original_base P D g j)
    simpa only [hb] using (D (e j)).center_slab z hz
  have hpivot (j) : (ref j).pivotLabel = g.val.1.1 :=
    (reference_pivot P (e j)).trans (congrArg Prod.fst (original_base P D g j))
  obtain ⟨G,hdir,hshade,hmass,hadmiss,hbound,hU,hUc,hres⟩ :=
    normalize_selected_group aa fc sc ref rawPairs cells g.val.1 label hδnorm hδnorm1 hknorm
      (fun j => (D (e j)).cells_nonempty P)
      (fun j => normalized_vertex_bound P hδ1 hbounded (e j))
      (fun j => (D (e j)).cells_subset) hslab hpivot
      (fun j => intermediate_close P (e j))
  have hinj : Function.Injective label :=
    ActualGroupedGeometry.intermediate_injective (base P D) (fun q => (P.chosen_output q).2)
      (fun _ => ()) (line_output_injective P D) g
  have hcap := LiftGraph.lifted_family_cap_bound G (fun j => slope P (e j)) label
    (cellCenter (δ/(1+2*width)) g.val.1.1) F.unionCells hinj
    (fun j => intermediate_in_union P (e j)) hδnorm (by norm_num : (0:ℝ) ≤ 1)
    (by positivity : 0 ≤ 2*width+((k+1 : ℕ) : ℝ)/2) hC
    (fun j => SelectedOutputSlabs.reference_slope_bound P (e j)) hres hdir hball
  refine ⟨{
    family := G
    direction := hdir
    shade_subset := hshade
    shade_mass := ?_
    admissible := hadmiss
    bounded := fun j => (hbound j).trans (le_max_right _ _)
    cap := ?_
    nonempty_shade := ?_
    union_subset := hU
    union_card := hUc }⟩
  · intro j
    simpa only [cells,LineData.cells_card] using hmass j
  · norm_num at hcap
    simpa only [capCoefficient,Nat.cast_add,Nat.cast_one] using hcap
  · intro j
    have hh : (0:ℝ) < (G.shade j).card := by
      have hlo : (0:ℝ) < (cells j).card := by exact_mod_cast card_pos.mpr ((D (e j)).cells_nonempty P)
      exact (div_pos hlo (by norm_num)).trans_le (hmass j)
    exact card_pos.mp (by exact_mod_cast hh)

/-- Every actually used base receives its own constructed normalized family;
all still share the original output-index partition and geometric constants. -/
def normalizedGroup {R d C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 0 ≤ C) (hbounded : F.Bounded R)
    (hball : ∀ x : Space (k+1), ∀ r : ℝ, δ/(1+2*width) ≤ r →
      (((F.unionCells).filter (fun z => dist (cellCenter (δ/(1+2*width)) z) x ≤ r)).card : ℝ) ≤
        C*(r/(δ/(1+2*width)))^d)
    (g : Group P D) : GroupData P D R d C g :=
  Classical.choice (group_exists P D hδ hδ1 hC hbounded hball g)

end
end KakeyaFormal.SelectedBaseFamilies
