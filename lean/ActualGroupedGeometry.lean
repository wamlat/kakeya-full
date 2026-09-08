import ActualGroupedIncidence

/-! The common residue palette is constructed from actual intermediate grid
labels.  Its within-group separation follows from the exact bounded graph
chart and rounded pivot residual, without selecting a color or dropping lines. -/
namespace KakeyaFormal.ActualGroupedGeometry
open Finset ActualGroupedIncidence SelectedSlabGeometry
open scoped BigOperators
noncomputable section
open Classical

variable {I : Type*} [Fintype I] {k : ℕ}

/-- Injective original (pivot, intermediate) outputs give injective line labels
inside every actual pivot/slab/color group. -/
theorem intermediate_injective (base : I → Cell k × ℕ) (label : I → Cell k)
    {C : Type*} (color : I → C)
    (hinj : Function.Injective (fun i => ((base i).1,label i)))
    (g : Group base color) :
    Function.Injective (fun j => label (original base color g j)) := by
  apply within_group_label_injective base color label
  intro i j hij
  apply hinj
  exact Prod.ext (congrArg (fun t : (Cell k × ℕ) × Cell k => t.1.1) hij)
    (congrArg (fun t : (Cell k × ℕ) × Cell k => t.2) hij)

/-- Actual graph slopes of norm at most one and common rounded pivot residual
produce delta/8 separation in every residue class. The index set is the full
original set, and the color is computed from each original intermediate label. -/
theorem graph_family_separated (base : I → Cell k × ℕ) (label : I → Cell k)
    (slope : I → Space k) (tube : I → UnitTube (k+1))
    (shading : I → Finset (Cell (k+1))) {δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (hinj : Function.Injective (fun i => ((base i).1,label i)))
    (hslope : ∀ i, ‖slope i‖ ≤ 1)
    (hdir : ∀ i, (tube i).direction = LiftGraph.graphDirection (slope i))
    (hres : ∀ i, ‖slope i-(cellCenter δ (base i).1-cellCenter δ (label i))‖ ≤ C*δ)
    (g : Group base (residueColor C label)) :
    (family base (residueColor C label) tube shading g).Separated ((1/8)*δ) := by
  let color := residueColor C label
  let e := original base color g
  have hlabel : Function.Injective (fun j => label (e j)) :=
    intermediate_injective base label color hinj g
  have hlocal (j) : ‖slope (e j)-(cellCenter δ g.val.1.1-cellCenter δ (label (e j)))‖ ≤ C*δ := by
    have hb : (base (e j)).1 = g.val.1.1 :=
      congrArg Prod.fst (original_base base color g j)
    simpa only [hb] using hres (e j)
  have hsep := common_color_separation (fun j => slope (e j)) (fun j => label (e j))
    (cellCenter δ g.val.1.1) hδ (by norm_num : (0:ℝ) ≤ 1) hC hlabel
    (fun j => hslope (e j)) hlocal
  intro i j hij
  have hcolor : color (e i) = color (e j) :=
    (original_color base color g i).trans (original_color base color g j).symm
  have hh := hsep i j hij hcolor
  change (1/8)*δ ≤ projectiveDistance (tube (e i)).direction (tube (e j)).direction
  rw [hdir,hdir]
  convert hh using 1
  norm_num
  ring

/-- The single palette used across all pivot/slab groups is dimension bounded,
with no delta, kappa, tube-count or number-of-groups dependence. -/
theorem palette_card {C : ℝ} (hC : 0 ≤ C) :
    let _ : NeZero (colorModulus C) := ⟨(color_modulus_bounds hC).1.ne'⟩
    (Fintype.card (Fin k → ZMod (colorModulus C)) : ℝ) ≤ (2*C+2)^k :=
  common_color_count hC

/-- Equal-cardinality actual trimmed slabs and their actual unit-segment
normalizations instantiate the incidence lower bound KQ/3. -/
theorem trimmed_incidence_mass {B D : Type*} (base : I → B) (color : I → D)
    (trimmed shading : I → Finset (Cell (k+1))) (K : ℕ)
    (htrim : ∀ i, (trimmed i).card = K)
    (hnormalize : ∀ i, ((trimmed i).card : ℝ)/3 ≤ ((shading i).card : ℝ)) :
    (K : ℝ)*(Fintype.card I : ℝ)/3 ≤ ((incidences base color shading).card : ℝ) := by
  apply incidence_mass_lower
  intro i
  simpa only [htrim i] using hnormalize i

end
end KakeyaFormal.ActualGroupedGeometry
