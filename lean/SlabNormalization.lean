import SelectedFiberSlab
import Rescaling

/-! One exact grid-compatible vertical translation is used throughout each
fixed original-pivot/unit-slab group. No per-line translation of a group union
is permitted. The subsequent unit-segment normalization is geometric. -/
namespace KakeyaFormal.SlabNormalization
open Finset EuclideanSplit LiftSegments PivotOutputCount PivotWitnesses SelectedFiberLift
open scoped BigOperators
noncomputable section
open Classical

/-- The integer vertical mesh shift of a common unit-slab index. -/
def shiftIndex (δ : ℝ) (j : ℕ) : ℤ := Int.floor ((j : ℝ)/δ)

def shiftHeight (δ : ℝ) (j : ℕ) : ℝ := δ*(shiftIndex δ j : ℝ)

def shiftCell {k : ℕ} (δ : ℝ) (j : ℕ) (z : Cell (k+1)) : Cell (k+1) :=
  Rescaling.shiftLabel (Fin.cons (shiftIndex δ j) (fun _ : Fin k => (0:ℤ))) z

def shiftPoint {k : ℕ} (δ : ℝ) (j : ℕ) (x : Space (k+1)) : Space (k+1) :=
  x-cons (shiftHeight δ j) 0

/-- The physical shift differs from the original unit-slab height by less than
one mesh at every positive real scale. -/
theorem shift_height_bounds {δ : ℝ} (hδ : 0 < δ) (j : ℕ) :
    0 ≤ shiftHeight δ j ∧ shiftHeight δ j ≤ j ∧ (j : ℝ) < shiftHeight δ j+δ := by
  have hnonneg : 0 ≤ shiftIndex δ j := Int.floor_nonneg.mpr (by positivity)
  have hlo := (le_div_iff₀ hδ).mp (Int.floor_le ((j : ℝ)/δ))
  have hhi := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one ((j : ℝ)/δ))
  dsimp [shiftHeight,shiftIndex] at *
  constructor
  · positivity
  constructor <;> nlinarith

theorem shiftCell_injective {k : ℕ} (δ : ℝ) (j : ℕ) :
    Function.Injective (shiftCell (k := k) δ j) := Rescaling.shiftLabel_injective _

/-- Horizontal cell labels remain exactly the original ones. -/
theorem shiftCell_tail {k : ℕ} (δ : ℝ) (j : ℕ) (z : Cell (k+1)) (i : Fin k) :
    shiftCell δ j z i.succ = z i.succ := by simp [shiftCell,Rescaling.shiftLabel]

/-- Actual Euclidean horizontal coordinates remain exactly unchanged. -/
theorem shiftPoint_tail {k : ℕ} (δ : ℝ) (j : ℕ) (x : Space (k+1)) :
    tail (shiftPoint δ j x) = tail x := by simp [shiftPoint]

/-- Exact, rather than approximate, compatibility of the shared point and grid shifts. -/
theorem shift_grid {k : ℕ} (δ : ℝ) (j : ℕ) (z : Cell (k+1)) :
    cellCenter δ (shiftCell δ j z) = shiftPoint δ j (cellCenter δ z) := by
  apply WithLp.ofLp_injective
  funext i
  cases i using Fin.cases
  · change δ*((z 0-shiftIndex δ j : ℤ) : ℝ) = δ*(z 0 : ℝ)-shiftHeight δ j
    dsimp [shiftHeight]
    push_cast
    ring
  · rename_i i
    change δ*((z i.succ-0 : ℤ) : ℝ) = δ*(z i.succ : ℝ)-0
    simp

theorem shift_distance {k : ℕ} (δ : ℝ) (j : ℕ) (x y : Space (k+1)) :
    dist (shiftPoint δ j x) (shiftPoint δ j y) = dist x y := by
  exact dist_sub_right _ _ _

/-- One shared vertical translation changes each intercept by the same time
increment along that line and leaves every slope and direction unchanged. -/
theorem shift_graph {k : ℕ} (δ : ℝ) (j : ℕ) (a v : Space k) (t : ℝ) :
    shiftPoint δ j (graphPoint a v t) =
      graphPoint (a+shiftHeight δ j • v) v (t-shiftHeight δ j) := by
  unfold shiftPoint graphPoint
  apply WithLp.ofLp_injective
  funext i
  cases i using Fin.cases
  · rfl
  · rename_i i
    change WithLp.ofLp (a+t • v) i-0 = WithLp.ofLp (a+shiftHeight δ j • v+(t-shiftHeight δ j) • v) i
    simp only [PiLp.add_apply,PiLp.smul_apply]
    ring

/-- Cell-center time in the selected unit slab becomes time in [0,1+delta). -/
theorem shifted_center_slab {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (j : ℕ) (z : Cell (k+1))
    (hz : (j : ℝ) ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) < (j : ℝ)+1) :
    0 ≤ δ*(shiftCell δ j z 0 : ℝ) ∧ δ*(shiftCell δ j z 0 : ℝ) < 1+δ := by
  have h := shift_height_bounds hδ j
  change 0 ≤ δ*((z 0-shiftIndex δ j : ℤ) : ℝ) ∧ δ*((z 0-shiftIndex δ j : ℤ) : ℝ) < 1+δ
  push_cast
  dsimp [shiftHeight] at h
  constructor <;> nlinarith

/-- Center-slab membership and actual graph incidence imply the shifted graph
parameter lies within only a fixed one-mesh boundary error. -/
theorem shifted_graph_incidence {k : ℕ} {δ width : ℝ} (hδ : 0 < δ) (_hw : 0 ≤ width)
    (j : ℕ) (z : Cell (k+1)) (a v : Space k) (t : ℝ)
    (hz : (j : ℝ) ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) < (j : ℝ)+1)
    (hclose : dist (cellCenter δ z) (graphPoint a v t) ≤ width*δ) :
    (t-shiftHeight δ j) ∈ Set.Icc (-((width+1)*δ)) (1+(width+1)*δ) ∧
      dist (cellCenter δ (shiftCell δ j z))
        (graphPoint (a+shiftHeight δ j • v) v (t-shiftHeight δ j)) ≤ width*δ := by
  have hcoord := (GridGeometry.coordinate_dist_le (cellCenter δ z) (graphPoint a v t) 0).trans hclose
  change |δ*(z 0 : ℝ)-t| ≤ width*δ at hcoord
  obtain ⟨hlo,hhi⟩ := abs_le.mp hcoord
  have hshift := shift_height_bounds hδ j
  constructor
  · constructor <;> nlinarith
  · rw [shift_grid,← shift_graph,shift_distance]
    exact hclose

/-- Every per-line cardinality is preserved by the common grid shift. -/
theorem shifted_card {k : ℕ} (δ : ℝ) (j : ℕ) (S : Finset (Cell (k+1))) :
    (S.image (shiftCell δ j)).card = S.card := card_image_of_injective _ (shiftCell_injective δ j)

/-- The same grid shift applies to the entire group union. This exact equality
would fail if each line were independently translated. -/
theorem shifted_union {k M : ℕ} (δ : ℝ) (j : ℕ) (S : Fin M → Finset (Cell (k+1))) :
    (univ.biUnion (fun i => (S i).image (shiftCell δ j))) =
      (univ.biUnion S).image (shiftCell δ j) := by rw [biUnion_image]

theorem shifted_union_card {k M : ℕ} (δ : ℝ) (j : ℕ) (S : Fin M → Finset (Cell (k+1))) :
    (univ.biUnion (fun i => (S i).image (shiftCell δ j))).card = (univ.biUnion S).card := by
  rw [shifted_union,shifted_card]

/-- A retained horizontal point controls the graph intercept uniformly in its
unit-slab index. No inverse-kappa bound on the index is needed here. -/
theorem intercept_from_horizontal {k : ℕ} (a v : Space k) (x : Space (k+1))
    {R V width δ t b : ℝ} (_hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hb : 0 ≤ b) (_hV : 0 ≤ V) (hv : ‖v‖ ≤ V)
    (hx : ‖tail x‖ ≤ R) (ht : t ∈ Set.Icc (-(b*δ)) (1+b*δ))
    (hclose : dist x (graphPoint a v t) ≤ width*δ) :
    ‖a‖ ≤ R+width+(1+b)*V := by
  have htail := tail_norm_le (x-graphPoint a v t)
  rw [tail_sub] at htail
  change ‖tail x-(a+t • v)‖ ≤ ‖x-graphPoint a v t‖ at htail
  have herr : ‖tail x-(a+t • v)‖ ≤ width*δ := htail.trans hclose
  have htabs : |t| ≤ 1+b := abs_le.mpr ⟨by nlinarith [ht.1],by nlinarith [ht.2]⟩
  have hnorm := norm_sub_le (a+t • v) (t • v)
  rw [add_sub_cancel_right,norm_smul,Real.norm_eq_abs] at hnorm
  have haxis : ‖a+t • v‖ ≤ R+width*δ := by
    have hh := norm_le_norm_add_norm_sub (tail x) (a+t • v)
    have herr' : ‖a+t • v-tail x‖ ≤ width*δ := by simpa only [norm_sub_rev] using herr
    linarith
  have hmul := mul_le_mul htabs hv (norm_nonneg _) (by positivity : 0 ≤ 1+b)
  nlinarith


/-- Actual common-slab graph shadings are shifted together and normalized to
unit tubes. Intercept bounds come from retained horizontal points and therefore
are uniform in the common slab index. -/
theorem normalize_common_slab {k M : ℕ} {δ width R V : ℝ}
    (a v : Fin M → Space k) (S : Fin M → Finset (Cell (k+1))) (j : ℕ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (hV : 0 ≤ V)
    (hne : ∀ i, (S i).Nonempty) (hv : ∀ i, ‖v i‖ ≤ V)
    (hslab : ∀ i z, z ∈ S i → (j : ℝ) ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) < (j : ℝ)+1)
    (hhorizontal : ∀ i z, z ∈ S i → ‖tail (cellCenter δ z)‖ ≤ R)
    (hpoint : ∀ i z, z ∈ S i → ∃ t : ℝ, dist (cellCenter δ z) (graphPoint (a i) (v i) t) ≤ width*δ) :
    ∃ G : TubeFamily (k+1) M,
      (∀ i, (G.tube i).direction = LiftGraph.graphDirection (v i)) ∧
      (∀ i, G.shade i ⊆ (S i).image (shiftCell δ j)) ∧
      (∀ i, ((S i).card : ℝ)/(Nat.ceil (1+V)+1 : ℕ) ≤ ((G.shade i).card : ℝ)) ∧
      G.Admissible (width+(width+1)*(1+V)) δ ∧
      G.Bounded (R+width+(2+width)*V+V+2) ∧
      G.unionCells ⊆ (univ.biUnion S).image (shiftCell δ j) ∧
      G.unionCells.card ≤ (univ.biUnion S).card := by
  let shiftedA := fun i => a i+shiftHeight δ j • v i
  let shiftedS := fun i => (S i).image (shiftCell δ j)
  have hinc : ∀ i z, z ∈ shiftedS i → ∃ t ∈ Set.Icc (-((width+1)*δ)) (1+(width+1)*δ),
      dist (cellCenter δ z) (graphPoint (shiftedA i) (v i) t) ≤ width*δ := by
    intro i z hz
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hz
    obtain ⟨t,ht⟩ := hpoint i q hq
    exact ⟨t-shiftHeight δ j,shifted_graph_incidence hδ hw j q (a i) (v i) t (hslab i q hq) ht⟩
  have hbase (i) : ‖shiftedA i‖ ≤ R+width+(2+width)*V := by
    obtain ⟨z,hz⟩ := hne i
    obtain ⟨t,ht⟩ := hpoint i z hz
    obtain ⟨hnewt,hnewclose⟩ := shifted_graph_incidence hδ hw j z (a i) (v i) t (hslab i z hz) ht
    have hx : ‖tail (cellCenter δ (shiftCell δ j z))‖ ≤ R := by
      rw [shift_grid,shiftPoint_tail]
      exact hhorizontal i z hz
    have hh := intercept_from_horizontal (shiftedA i) (v i) (cellCenter δ (shiftCell δ j z))
      hδ hδ1 hw (by positivity : 0 ≤ width+1) hV (hv i) hx hnewt hnewclose
    convert hh using 1
    ring
  obtain ⟨G,hdir,hsub,hcount,hadm,hbound,hunion⟩ := normalize_graph_family shiftedA v shiftedS
    hδ hV (by positivity : 0 ≤ width+1) hbase hv hinc
  have hsubU : G.unionCells ⊆ (univ.biUnion S).image (shiftCell δ j) := by
    rwa [shifted_union] at hunion
  have hUcard := (card_le_card hsubU).trans_eq (shifted_card δ j (univ.biUnion S))
  refine ⟨G,hdir,hsub,?_,hadm,hbound,hsubU,hUcard⟩
  intro i
  simpa only [shiftedS,shifted_card] using hcount i

/-- The slope of a selected reference graph is uniformly bounded by one. -/
theorem reference_slope_bound {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (reference : LabeledPair a δ width fc sc) (hk : 0 < kap) :
    ‖reference.endpoints.coefficient • a.second‖ ≤ 1 := by
  rw [norm_smul,Real.norm_eq_abs,a.second_unit,mul_one]
  exact coefficient_abs_le_one reference.endpoints hk

/-- Original intermediate and pivot cell labels determine the graph slope up
to the actual rounding/projection error. Vertical shifts never alter these
horizontal coordinates or this residual. -/
theorem reference_pivot_residual {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (reference : LabeledPair a δ width fc sc) (label pivot : Cell k)
    (hδ : 0 < δ) (hpivot : reference.pivotLabel = pivot)
    (hintermediate : dist (cellCenter δ label) (a.vertex+a.intermediate • a.first) ≤ width*δ) :
    ‖reference.endpoints.coefficient • a.second-(cellCenter δ pivot-cellCenter δ label)‖ ≤
      (width+(k : ℝ)/2)*δ := by
  have hp := reference.pivot_rounding hδ
  rw [hpivot] at hp
  have hid : reference.endpoints.coefficient • a.second-(cellCenter δ pivot-cellCenter δ label) =
      (reference.endpoints.pivot-cellCenter δ pivot)+
        (cellCenter δ label-(a.vertex+a.intermediate • a.first)) := by
    dsimp [Endpoints.pivot]
    module
  rw [hid]
  have hh := norm_add_le (reference.endpoints.pivot-cellCenter δ pivot)
    (cellCenter δ label-(a.vertex+a.intermediate • a.first))
  change ‖reference.endpoints.pivot-cellCenter δ pivot‖ ≤ _ at hp
  change ‖cellCenter δ label-(a.vertex+a.intermediate • a.first)‖ ≤ _ at hintermediate
  nlinarith

/-- Horizontal centers of actual lifted cells stay in the original bounded
region, independently of the selected slab or the lift's large time parameter. -/
theorem lifted_horizontal_bound {k : ℕ} {kap δ width R : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (reference s : LabeledPair a δ width fc sc)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hvertex : ‖a.vertex‖ ≤ R) :
    ‖tail (cellCenter δ (liftedCell reference s))‖ ≤ R+1+((k : ℝ)+1)/2 := by
  have hround := GridCells.cell_center_distance (GridCells.gridCell_covers hδ (liftedPoint reference s))
  change dist (liftedPoint reference s) (cellCenter δ (liftedCell reference s)) ≤ _ at hround
  have htail := tail_norm_le (cellCenter δ (liftedCell reference s)-liftedPoint reference s)
  simp only [tail_sub,liftedPoint,tail_cons] at htail
  have herr : ‖tail (cellCenter δ (liftedCell reference s))-s.endpoints.secondPoint‖ ≤ ((k : ℝ)+1)*δ/2 := by
    have hh : ‖cellCenter δ (liftedCell reference s)-liftedPoint reference s‖ ≤ ((k : ℝ)+1)*δ/2 := by
      simpa only [Nat.cast_add,Nat.cast_one,dist_eq_norm,norm_sub_rev] using hround
    exact htail.trans hh
  have hsecond : ‖s.endpoints.secondPoint‖ ≤ R+1 := by
    have hh := norm_add_le a.vertex (s.endpoints.secondCoord • a.second)
    rw [norm_smul,Real.norm_eq_abs,a.second_unit,mul_one] at hh
    change ‖a.vertex+s.endpoints.secondCoord • a.second‖ ≤ _
    exact hh.trans (add_le_add hvertex s.second_upper)
  have hh := norm_le_norm_add_norm_sub s.endpoints.secondPoint (tail (cellCenter δ (liftedCell reference s)))
  have herr' : ‖s.endpoints.secondPoint-tail (cellCenter δ (liftedCell reference s))‖ ≤ ((k : ℝ)+1)*δ/2 := by
    simpa only [norm_sub_rev] using herr
  have hkn : (0:ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith

/-- The concrete selected-fiber adapter for one ORIGINAL (pivot,slab) group.
All lines share the same grid translation. It constructs normalized unit tubes,
pays only a factor three in each shading, preserves the original horizontal
pivot-label residual, and bounds the normalized union by the original group
union with no group-count factor and no inverse-kappa normalization constant. -/
theorem normalize_selected_group {k M : ℕ} {kap δ width R : ℝ}
    (angles : Fin M → Angle k kap) (fc sc : Fin M → Cell k → ℝ)
    (reference : ∀ i, LabeledPair (angles i) δ width (fc i) (sc i))
    (raw : ∀ i, Finset (LabeledPair (angles i) δ width (fc i) (sc i)))
    (S : Fin M → Finset (Cell (k+1))) (group : Cell k × ℕ) (label : Fin M → Cell k)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap)
    (hne : ∀ i, (S i).Nonempty) (hvertex : ∀ i, ‖(angles i).vertex‖ ≤ R)
    (hsub : ∀ i, S i ⊆ liftedCells (reference i) (raw i))
    (hslab : ∀ i z, z ∈ S i → (group.2 : ℝ) ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) < (group.2 : ℝ)+1)
    (hpivot : ∀ i, (reference i).pivotLabel = group.1)
    (hintermediate : ∀ i, dist (cellCenter δ (label i))
      ((angles i).vertex+(angles i).intermediate • (angles i).first) ≤ width*δ) :
    ∃ G : TubeFamily (k+1) M,
      (∀ i, (G.tube i).direction = LiftGraph.graphDirection ((reference i).endpoints.coefficient • (angles i).second)) ∧
      (∀ i, G.shade i ⊆ (S i).image (shiftCell δ group.2)) ∧
      (∀ i, ((S i).card : ℝ)/3 ≤ ((G.shade i).card : ℝ)) ∧
      G.Admissible (3*(((k : ℝ)+1)/2)+2) δ ∧
      G.Bounded (R+6+3*(((k : ℝ)+1)/2)) ∧
      G.unionCells ⊆ (univ.biUnion S).image (shiftCell δ group.2) ∧
      G.unionCells.card ≤ (univ.biUnion S).card ∧
      (∀ i, ‖(reference i).endpoints.coefficient • (angles i).second-
        (cellCenter δ group.1-cellCenter δ (label i))‖ ≤ (width+(k : ℝ)/2)*δ) := by
  let aa := fun i => (angles i).vertex
  let vv := fun i => (reference i).endpoints.coefficient • (angles i).second
  let w := ((k : ℝ)+1)/2
  have hv (i) : ‖vv i‖ ≤ 1 := reference_slope_bound (reference i) hk
  have hhor : ∀ i z, z ∈ S i → ‖tail (cellCenter δ z)‖ ≤ R+1+w := by
    intro i z hz
    obtain ⟨s,hs,rfl⟩ := mem_image.mp (hsub i hz)
    exact lifted_horizontal_bound (reference i) s hδ hδ1 (hvertex i)
  have hpoint : ∀ i z, z ∈ S i → ∃ t : ℝ, dist (cellCenter δ z) (graphPoint (aa i) (vv i) t) ≤ w*δ := by
    intro i z hz
    obtain ⟨s,hs,rfl⟩ := mem_image.mp (hsub i hz)
    refine ⟨s.endpoints.secondCoord/(reference i).endpoints.coefficient,?_⟩
    have hh := liftedCell_graph_incidence (reference i) s hδ hk
    convert hh using 1
    dsimp [w]
    ring
  obtain ⟨G,hdir,hshades,hcard,hadm,hbound,hU,hUc⟩ := normalize_common_slab aa vv S group.2
    hδ hδ1 (by dsimp [w]; positivity : 0 ≤ w) (by norm_num : (0:ℝ) ≤ 1) hne hv hslab hhor hpoint
  refine ⟨G,hdir,hshades,?_,?_,?_,hU,hUc,fun i => reference_pivot_residual (reference i) (label i) group.1 hδ (hpivot i) (hintermediate i)⟩
  · intro i
    norm_num at hcard
    exact hcard i
  · convert hadm using 1
    dsimp [w]
    ring
  · convert hbound using 1
    dsimp [w]
    ring

end
end KakeyaFormal.SlabNormalization

#print axioms KakeyaFormal.SlabNormalization.shift_grid
#print axioms KakeyaFormal.SlabNormalization.shift_graph
#print axioms KakeyaFormal.SlabNormalization.shifted_graph_incidence
#print axioms KakeyaFormal.SlabNormalization.shifted_union_card
#print axioms KakeyaFormal.SlabNormalization.normalize_common_slab
#print axioms KakeyaFormal.SlabNormalization.reference_pivot_residual
#print axioms KakeyaFormal.SlabNormalization.normalize_selected_group
