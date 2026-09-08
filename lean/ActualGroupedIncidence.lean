import GroupedCumulative
import SelectedSlabGeometry

/-! Lossless grouping of actual original line indices by their geometric base
label and a common finite color.  The base label may be the literal pivot/slab
pair.  Every grouped line and incidence has a unique original index. -/
namespace KakeyaFormal.ActualGroupedIncidence
open Finset
open scoped BigOperators
noncomputable section
open Classical

universe u v w
variable {I : Type u} [Fintype I] {B : Type v} {C : Type w}
    (base : I → B) (color : I → C)

/-- Only base/color pairs actually used by original indices occur as groups. -/
def Group := ↥((univ : Finset I).image (fun i => (base i, color i)))

instance : Fintype (Group base color) := inferInstanceAs (Fintype ↥((univ : Finset I).image _))

def key (i : I) : Group base color :=
  ⟨(base i,color i),mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩

def population (g : Group base color) : ℕ := Fintype.card {i : I // key base color i = g}

def original (g : Group base color) (j : Fin (population base color g)) : I :=
  ((Fintype.equivFin {i : I // key base color i = g}).symm j).val

theorem original_key (g : Group base color) (j : Fin (population base color g)) :
    key base color (original base color g j) = g :=
  ((Fintype.equivFin {i : I // key base color i = g}).symm j).property

/-- The finite grouping is a bijection with all original indices, not a selected
subfamily. Empty original families are included. -/
def indexEquiv : GroupedCumulative.Index (population base color) ≃ I :=
  (Equiv.sigmaCongrRight (fun g =>
    (Fintype.equivFin {i : I // key base color i = g}).symm)).trans
      (Equiv.sigmaFiberEquiv (key base color))

theorem indexEquiv_apply (g : Group base color) (j : Fin (population base color g)) :
    indexEquiv base color ⟨g,j⟩ = original base color g j := rfl

theorem original_injective (g : Group base color) :
    Function.Injective (original base color g) := by
  intro i j hij
  have hh := (indexEquiv base color).injective (show
    indexEquiv base color ⟨g,i⟩ = indexEquiv base color ⟨g,j⟩ from hij)
  exact eq_of_heq (Sigma.mk.inj_iff.mp hh).2

theorem original_base (g : Group base color) (j : Fin (population base color g)) :
    base (original base color g j) = g.val.1 :=
  congrArg (fun t : Group base color => t.val.1) (original_key base color g j)

theorem original_color (g : Group base color) (j : Fin (population base color g)) :
    color (original base color g j) = g.val.2 :=
  congrArg (fun t : Group base color => t.val.2) (original_key base color g j)

theorem group_encoding_injective : Function.Injective
    (fun g : Group base color => (g.val.1,g.val.2)) := by
  intro g h he
  exact Subtype.val_injective he

theorem sum_population : ∑ g, population base color g = Fintype.card I := by
  simpa only [Fintype.card_sigma,Fintype.card_fin] using
    Fintype.card_congr (indexEquiv base color)

theorem sum_original {R : Type*} [AddCommMonoid R] (f : I → R) :
    ∑ g, ∑ j, f (original base color g j) = ∑ i, f i := by
  calc
    _ = ∑ j : GroupedCumulative.Index (population base color), f (indexEquiv base color j) :=
      (Fintype.sum_sigma _).symm
    _ = _ := (indexEquiv base color).sum_comp f

/-- For output indices injectively labeled by (pivot, intermediate), equality
of the pivot/slab base within a group gives injective intermediate labels. -/
theorem within_group_label_injective {L : Type*} (label : I → L)
    (hinj : Function.Injective (fun i => (base i,label i))) (g : Group base color) :
    Function.Injective (fun j => label (original base color g j)) := by
  intro i j hij
  apply original_injective base color g
  apply hinj
  exact Prod.ext ((original_base base color g i).trans (original_base base color g j).symm) hij

variable {n : ℕ}

def family (tube : I → UnitTube n) (shading : I → Finset (Cell n))
    (g : Group base color) : TubeFamily n (population base color g) :=
  ⟨fun j => tube (original base color g j),fun j => shading (original base color g j)⟩

/-- The literal set of all normalized shaded-cell incidences, with each
original output retained in its unique group and local index. -/
def incidences (shading : I → Finset (Cell n)) :
    Finset (GroupedCumulative.Record (k := n) (population base color)) :=
  univ.biUnion fun j => (shading (indexEquiv base color j)).image (fun z => (j,z))

theorem mem_incidences (shading : I → Finset (Cell n))
    (r : GroupedCumulative.Record (k := n) (population base color)) :
    r ∈ incidences base color shading ↔ r.2 ∈ shading (indexEquiv base color r.1) := by
  simp only [incidences,mem_biUnion,mem_univ,true_and,mem_image]
  constructor
  · rintro ⟨j,z,hz,he⟩
    have hj : j = r.1 := congrArg Prod.fst he
    have hzz : z = r.2 := congrArg Prod.snd he
    simpa only [hj,hzz] using hz
  · intro h
    exact ⟨r.1,r.2,h,rfl⟩

theorem incidence_shade (shading : I → Finset (Cell n))
    (g : Group base color) (j : Fin (population base color g)) :
    GroupedCumulative.shade (population base color) (incidences base color shading) g j =
      shading (original base color g j) := by
  ext z
  rw [GroupedCumulative.mem_shade,mem_incidences]
  simp only [indexEquiv_apply]

/-- The exact incidence count is the sum of the actual normalized shading
cardinalities; neither colors nor base groups cost a cardinality factor. -/
theorem incidence_card (shading : I → Finset (Cell n)) :
    (incidences base color shading).card = ∑ i, (shading i).card := by
  rw [← GroupedCumulative.total_incidence (population base color)]
  simp_rw [incidence_shade]
  exact sum_original base color (fun i => (shading i).card)

/-- The common K selected before unit-segment normalization retains at least
KQ/3 actual incidences, where Q is exactly the number of original outputs. -/
theorem incidence_mass_lower (shading : I → Finset (Cell n)) {K : ℝ}
    (hmass : ∀ i, K/3 ≤ ((shading i).card : ℝ)) :
    K*(Fintype.card I : ℝ)/3 ≤ ((incidences base color shading).card : ℝ) := by
  rw [incidence_card,Nat.cast_sum]
  have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset I)) => hmass i)
  simp only [sum_const,card_univ,nsmul_eq_mul] at hh
  convert hh using 1 <;> first | rfl | ring


/-- Actual incidence membership uses exactly the reindexed family's shading. -/
theorem incidence_admissible_record (tube : I → UnitTube n)
    (shading : I → Finset (Cell n))
    (r : GroupedCumulative.Record (k := n) (population base color))
    (hr : r ∈ incidences base color shading) :
    r.2 ∈ (family base color tube shading r.1.1).shade r.1.2 :=
  (mem_incidences base color shading r).mp hr

theorem incidences_nonempty (shading : I → Finset (Cell n))
    (h : ∃ i, (shading i).Nonempty) : (incidences base color shading).Nonempty := by
  obtain ⟨i,z,hz⟩ := h
  refine ⟨((indexEquiv base color).symm i,z),?_⟩
  apply (mem_incidences base color shading _).mpr
  simpa only [Equiv.apply_symm_apply] using hz

theorem family_admissible (tube : I → UnitTube n) (shading : I → Finset (Cell n))
    {width δ : ℝ} (hadm : ∀ i z, z ∈ shading i →
      ∃ t ∈ Set.Icc (0:ℝ) 1, dist (cellCenter δ z) ((tube i).axisPoint t) ≤ width*δ)
    (g : Group base color) : (family base color tube shading g).Admissible width δ := by
  intro j z hz
  exact hadm (original base color g j) z hz

theorem family_bounded (tube : I → UnitTube n) (shading : I → Finset (Cell n))
    {R : ℝ} (hbound : ∀ i, ‖(tube i).base‖ ≤ R) (g : Group base color) :
    (family base color tube shading g).Bounded R := by
  intro j
  exact hbound (original base color g j)

/-- A single common color palette gives the target separation in every actual
base/color group; the palette is never selected by a mass pigeonhole. -/
theorem family_separated (tube : I → UnitTube n) (shading : I → Finset (Cell n))
    {sep : ℝ} (hsep : ∀ i j, i ≠ j → base i = base j → color i = color j →
      sep ≤ projectiveDistance (tube i).direction (tube j).direction)
    (g : Group base color) : (family base color tube shading g).Separated sep := by
  intro i j hij
  apply hsep (original base color g i) (original base color g j)
    (fun he => hij (original_injective base color g he))
  · exact (original_base base color g i).trans (original_base base color g j).symm
  · exact (original_color base color g i).trans (original_color base color g j).symm

/-- Cap counts decrease under actual injective within-base reindexing. The
input counts the original directions in the geometric base, before coloring. -/
theorem family_cap_bound (tube : I → UnitTube n) (shading : I → Finset (Cell n))
    {δ m A : ℝ} (hcap : ∀ b v, ‖v‖ = 1 → ∀ r, δ ≤ r → r ≤ 1 →
      (((univ : Finset I).filter (fun i => base i = b ∧
        projectiveDistance (tube i).direction v ≤ r)).card : ℝ) ≤ A*(r/δ)^m)
    (g : Group base color) : (family base color tube shading g).CapBound δ m A := by
  intro v hv r hr hr1
  let U := (univ : Finset (Fin (population base color g))).filter
    (fun j => projectiveDistance (tube (original base color g j)).direction v ≤ r)
  let V := (univ : Finset I).filter
    (fun i => base i = g.val.1 ∧ projectiveDistance (tube i).direction v ≤ r)
  have hsub : U.image (original base color g) ⊆ V := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact mem_filter.mpr ⟨mem_univ _,original_base base color g j,(mem_filter.mp hj).2⟩
  have hh := card_le_card hsub
  rw [card_image_of_injective _ (original_injective base color g)] at hh
  have hh' : (U.card : ℝ) ≤ (V.card : ℝ) := by exact_mod_cast hh
  exact hh'.trans (hcap g.val.1 v hv r hr hr1)

/-- Removing the common color leaves the exact original geometric base/slab
label attached to each normalized cell. -/
def position (r : GroupedCumulative.Record (k := n) (population base color)) : B × Cell n :=
  (r.1.1.val.1,r.2)

theorem position_original (r : GroupedCumulative.Record (k := n) (population base color)) :
    position base color r = (base (indexEquiv base color r.1),r.2) := by
  exact Prod.ext (original_base base color r.1.1 r.1.2).symm rfl

/-- Exact population identity in the real arithmetic used by pruning. -/
theorem sum_population_real : ∑ g, (population base color g : ℝ) = (Fintype.card I : ℝ) := by
  exact_mod_cast sum_population base color



end
noncomputable section
open Classical

/-- The normalized discrete estimate prunes the actual grouped incidences.
The positive constant is uniform before the number of outputs, their base/slab
labels, common palette, normalized tube/shading maps, scale, and cap coefficient.
The incidence set and Q are constructed here, not supplied as abstract counts. -/
theorem actual_discrete_pruning {n : ℕ} {geom : Normalization} {m d p ε : ℝ}
    (h : DiscreteEstimate n m d p) (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (I : Type u) [Fintype I] (B : Type v) (C : Type w)
      [Fintype C] [Nonempty C] (base : I → B) (color : I → C)
      (tube : I → UnitTube n) (shading : I → Finset (Cell n))
      (δ A : ℝ), 0 < δ → δ ≤ 1 → 1 ≤ A →
      (∃ i, (shading i).Nonempty) →
      (∀ i z, z ∈ shading i → ∃ t ∈ Set.Icc (0:ℝ) 1,
        dist (cellCenter δ z) ((tube i).axisPoint t) ≤ geom.width*δ) →
      (∀ i j, i ≠ j → base i = base j → color i = color j →
        geom.separation*δ ≤ projectiveDistance (tube i).direction (tube j).direction) →
      (∀ i, ‖(tube i).base‖ ≤ geom.radius) →
      (∀ b v, ‖v‖ = 1 → ∀ r, δ ≤ r → r ≤ 1 →
        (((univ : Finset I).filter (fun i => base i = b ∧
          projectiveDistance (tube i).direction v ≤ r)).card : ℝ) ≤ A*(r/δ)^m) →
      let S := incidences base color shading
      let rho := δ*(S.card : ℝ)/(Fintype.card I : ℝ)
      let a := c*A⁻¹*δ^(m-d+ε)
      let H := (2:ℝ)^(p+1)*(Fintype.card C : ℝ)*(1/δ)/(a*rho^(p-1))
      let f := position (n := n) base color
      ∃ T ⊆ S, (S.card : ℝ)/2 < (T.card : ℝ) ∧
        (∑ b ∈ T.image f, (GroupedIncidence.degree T f b : ℝ)^2) ≤ H*(T.card : ℝ) := by
  obtain ⟨c,hc,hprune⟩ := GroupedCumulative.discrete_pruning (geom := geom) h hp hε
  refine ⟨c,hc,?_⟩
  intro I _ B C _ _ base color tube shading δ A hδ hδ1 hA hne hadm hsep hbounded hcap
  have hh := hprune (Group base color) B C (fun g => g.val.1) (fun g => g.val.2)
    (group_encoding_injective base color) (population base color) δ A hδ hδ1 hA
    (family base color tube shading) (incidences base color shading)
    (incidences_nonempty base color shading hne)
    (incidence_admissible_record base color tube shading)
    (family_admissible base color tube shading hadm)
    (family_separated base color tube shading hsep)
    (family_bounded base color tube shading hbounded)
    (family_cap_bound base color tube shading hcap)
  have hd : (instDecidableEqProd : DecidableEq (B × Cell n)) = Classical.decEq (B × Cell n) :=
    Subsingleton.elim _ _
  simp only [sum_population_real] at hh
  rw [hd] at hh
  dsimp only
  unfold position
  convert hh using 1
  congr! 10


end
end KakeyaFormal.ActualGroupedIncidence
