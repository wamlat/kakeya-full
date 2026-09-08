import SamplingBallTests

/-! The actual finite available support of restricted measurable tube shadings.
All positive-measure cell intersections are included, with no supplied finite
support or cell-count premise. The normalized intersection weights are genuine
coupled full/marked probabilities. -/
namespace KakeyaFormal.SamplingSupport
open Finset GridCells GridGeometry
open MeasureTheory
open scoped BigOperators
noncomputable section
open Classical

/-- Fixed bounded geometry controls every actual shading point. -/
theorem shading_point_bound {n : ℕ} (T : UnitTube n) {Y : Set (Space n)}
    {δ width R : ℝ} (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (hbase : ‖T.base‖ ≤ R)
    (hY : Y ⊆ T.carrier (width*δ)) {x : Space n} (hx : x ∈ Y) :
    ‖x‖ ≤ PrunedGraphLift.regionRadius width R := by
  obtain ⟨t,ht,hdist⟩ := hY hx
  have haxis : ‖T.axisPoint t‖ ≤ R+1 := by
    have hh := norm_add_le T.base (t • T.direction)
    rw [norm_smul,Real.norm_eq_abs,T.unit_direction,mul_one,abs_of_nonneg ht.1] at hh
    exact hh.trans (by linarith [ht.2])
  have htri := dist_triangle x (T.axisPoint t) 0
  simp only [dist_zero_right] at htri
  have hwidth := mul_le_mul_of_nonneg_left hδ1 hw
  dsimp [PrunedGraphLift.regionRadius]
  nlinarith [le_max_right (0:ℝ) R]

def candidates (n : ℕ) (δ width R : ℝ) : Finset (Cell n) :=
  gridBox (fun _ => 0) (Nat.ceil (PrunedGraphLift.regionRadius width R/δ+(n:ℝ)/2)+1)

def positiveFamily {n M : ℕ} (tube : Fin M → UnitTube n) (Y : Fin M → Set (Space n))
    (δ width R : ℝ) : TubeFamily n M :=
  ⟨tube,fun i => (candidates n δ width R).filter
    (fun z => 0 < (volume : Measure (Space n)).real (Y i ∩ gridCell δ z))⟩

def support {n M : ℕ} (tube : Fin M → UnitTube n) (Y : Fin M → Set (Space n))
    (δ width R : ℝ) : Finset (Cell n) := (positiveFamily tube Y δ width R).unionCells

theorem positive_intersection_nonempty {n : ℕ} {Y : Set (Space n)} {δ : ℝ} {z : Cell n}
    (hpos : 0 < (volume : Measure (Space n)).real (Y ∩ gridCell δ z)) :
    (Y ∩ gridCell δ z).Nonempty := by
  by_contra hn
  have hz : Y ∩ gridCell δ z = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  simp only [hz,measureReal_empty,lt_self_iff_false] at hpos

/-- Every positive full incidence lies in the constructed finite box. -/
theorem positive_mem_candidates {n : ℕ} (T : UnitTube n) {Y : Set (Space n)}
    {δ width R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ‖T.base‖ ≤ R) (hY : Y ⊆ T.carrier (width*δ)) {z : Cell n}
    (hpos : 0 < (volume : Measure (Space n)).real (Y ∩ gridCell δ z)) :
    z ∈ candidates n δ width R := by
  obtain ⟨x,hx,hcell⟩ := positive_intersection_nonempty hpos
  exact touching_bounded_set_label hδ (fun x hx => shading_point_bound T hδ1 hw hbase hY hx)
    ⟨x,hcell,hx⟩

/-- The finite family contains precisely every positive tube-cell incidence;
there is no omitted positive cell outside its finite candidate box. -/
theorem mem_positiveFamily {n M : ℕ} (tube : Fin M → UnitTube n) (Y : Fin M → Set (Space n))
    {δ width R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ∀ i, ‖(tube i).base‖ ≤ R) (hY : ∀ i, Y i ⊆ (tube i).carrier (width*δ))
    (i : Fin M) (z : Cell n) : z ∈ (positiveFamily tube Y δ width R).shade i ↔
      0 < (volume : Measure (Space n)).real (Y i ∩ gridCell δ z) := by
  constructor
  · intro hz; exact (mem_filter.mp hz).2
  · intro hp
    exact mem_filter.mpr ⟨positive_mem_candidates (tube i) hδ hδ1 hw (hbase i) (hY i) hp,hp⟩

/-- Exact support, defined by positive measure rather than bare intersection. -/
theorem mem_support {n M : ℕ} (tube : Fin M → UnitTube n) (Y : Fin M → Set (Space n))
    {δ width R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ∀ i, ‖(tube i).base‖ ≤ R) (hY : ∀ i, Y i ⊆ (tube i).carrier (width*δ))
    (z : Cell n) : z ∈ support tube Y δ width R ↔
      ∃ i, 0 < (volume : Measure (Space n)).real (Y i ∩ gridCell δ z) := by
  simp only [support,TubeFamily.unionCells,mem_biUnion,mem_univ,true_and]
  exact exists_congr (fun i => mem_positiveFamily tube Y hδ hδ1 hw hbase hY i z)

/-- The actual positive-intersection centers are near the unchanged original
unit tubes with only the fixed grid enlargement. -/
theorem positive_admissible {n M : ℕ} (tube : Fin M → UnitTube n) (Y : Fin M → Set (Space n))
    {δ width R : ℝ} (hY : ∀ i, Y i ⊆ (tube i).carrier (width*δ)) :
    (positiveFamily tube Y δ width R).Admissible (width+(n:ℝ)/2) δ := by
  intro i z hz
  obtain ⟨x,hx,hcell⟩ := positive_intersection_nonempty ((mem_filter.mp hz).2)
  exact touching_tube_center (tube i) ⟨x,hcell,hY i hx⟩

theorem support_bounded {n M : ℕ} (tube : Fin M → UnitTube n) (Y : Fin M → Set (Space n))
    {δ width R : ℝ} (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ∀ i, ‖(tube i).base‖ ≤ R) (hY : ∀ i, Y i ⊆ (tube i).carrier (width*δ)) :
    ∀ z ∈ support tube Y δ width R,
      ‖cellCenter δ z‖ ≤ PrunedGraphLift.regionRadius (width+(n:ℝ)/2) R := by
  have hh := PrunedGraphLift.union_bounded (positiveFamily tube Y δ width R) hδ1
    (by positivity : 0 ≤ width+(n:ℝ)/2) (positive_admissible tube Y hY) hbase
  simpa only [support,dist_zero_right] using hh

/-- Actual support count needed by the simultaneous high-cell/cap union bound. -/
theorem support_card {n M : ℕ} (tube : Fin M → UnitTube n) (Y : Fin M → Set (Space n))
    {δ width R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ∀ i, ‖(tube i).base‖ ≤ R) (hY : ∀ i, Y i ⊆ (tube i).carrier (width*δ)) :
    ((support tube Y δ width R).card : ℝ) ≤ (5:ℝ)^n*
      (1+PrunedGraphLift.regionRadius (width+(n:ℝ)/2) R)^n*(1/δ)^n :=
  SamplingBallTests.support_card _ hδ hδ1
    (PrunedGraphLift.regionRadius_pos (by positivity : 0 ≤ width+(n:ℝ)/2)).le
    (support_bounded tube Y hδ1 hw hbase hY)

/-- Literal normalized cell-intersection weight, as in equation (6.5). -/
def weight {n : ℕ} (Y : Set (Space n)) (δ : ℝ) (z : Cell n) : ℝ :=
  (volume : Measure (Space n)).real (Y ∩ gridCell δ z)/δ^n

theorem weight_nonneg {n : ℕ} (Y : Set (Space n)) {δ : ℝ} (hδ : 0 < δ) (z : Cell n) :
    0 ≤ weight Y δ z := div_nonneg measureReal_nonneg (pow_pos hδ n).le

theorem weight_le_one {n : ℕ} (Y : Set (Space n)) {δ : ℝ} (hδ : 0 < δ) (z : Cell n) :
    weight Y δ z ≤ 1 := by
  apply (div_le_one (pow_pos hδ n)).mpr
  have hh := measureReal_mono (μ:=volume) (Set.inter_subset_right : Y ∩ gridCell δ z ⊆ gridCell δ z)
    (finite_gridCell δ z)
  rwa [real_volume_gridCell hδ.le] at hh

theorem weight_mono {n : ℕ} {G Y : Set (Space n)} (hGY : G ⊆ Y)
    {δ : ℝ} (hδ : 0 < δ) (z : Cell n) : weight G δ z ≤ weight Y δ z := by
  apply div_le_div_of_nonneg_right _ (pow_pos hδ n).le
  exact measureReal_mono (Set.inter_subset_inter_left _ hGY)
    (measure_ne_top_of_subset Set.inter_subset_right (finite_gridCell δ z))

/-- The actual measurable full/marked weights meet the coupled law's three
probability inequalities without capping, positive-mass assumptions or clipping. -/
theorem coupled_weights {n : ℕ} {G Y : Set (Space n)} (hGY : G ⊆ Y)
    {δ : ℝ} (hδ : 0 < δ) (z : Cell n) :
    0 ≤ weight G δ z ∧ weight G δ z ≤ weight Y δ z ∧ weight Y δ z ≤ 1 :=
  ⟨weight_nonneg G hδ z,weight_mono hGY hδ z,weight_le_one Y hδ z⟩

end
end KakeyaFormal.SamplingSupport

#print axioms KakeyaFormal.SamplingSupport.mem_support
#print axioms KakeyaFormal.SamplingSupport.support_card
#print axioms KakeyaFormal.SamplingSupport.coupled_weights
