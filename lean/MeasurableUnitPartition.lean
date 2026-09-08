import SamplingMeans
import SpatialMarkedPartition
import MeasurableRescaling

/-! Actual unit spatial bins for measurable unit-tube shadings at arbitrary
positions. A fixed fraction is selected on every tube, and the resulting
OLD measurable group unions are disjoint. -/
namespace KakeyaFormal.MeasurableUnitPartition
open Finset MeasureTheory GridCells GridGeometry GridShadingMeasure SpatialMarkedPartition
open scoped ENNReal
noncomputable section
open Classical

def radius (n : ℕ) : ℝ := 2+(n:ℝ)/2
def binsPerTube (n : ℕ) : ℕ := (2*(Nat.ceil (radius n)+1)+1)^n
def candidates {n : ℕ} (T : UnitTube n) : Finset (Cell n) :=
  gridBox (fun i => ⌊WithLp.ofLp T.base i⌋) (Nat.ceil (radius n)+1)

theorem binsPerTube_pos (n : ℕ) : 0 < binsPerTube n := by unfold binsPerTube; positivity
theorem candidates_card {n : ℕ} (T : UnitTube n) : (candidates T).card=binsPerTube n :=
  gridBox_card _ _

theorem point_base_distance {n : ℕ} (T : UnitTube n) {δ : ℝ} (hδ1 : δ ≤ 1)
    {x : Space n} (hx : x ∈ T.carrier δ) : dist x T.base ≤ 2 := by
  obtain ⟨t,ht,hd⟩ := hx
  have hh := dist_triangle x (T.axisPoint t) (T.axisPoint 0)
  rw [T.axisPoint_distance,sub_zero,abs_of_nonneg ht.1] at hh
  simpa only [UnitTube.axisPoint,zero_smul,add_zero] using
    (show dist x (T.axisPoint 0) ≤ 2 by linarith [ht.2])

theorem cell_base_distance {n : ℕ} (T : UnitTube n) {δ : ℝ} (hδ1 : δ ≤ 1)
    {x : Space n} {q : Cell n} (hx : x ∈ T.carrier δ) (hq : x ∈ gridCell 1 q) :
    dist T.base (cellCenter 1 q) ≤ radius n := by
  have hp := point_base_distance T hδ1 hx
  have hc := cell_center_distance hq
  have hh := dist_triangle T.base x (cellCenter 1 q)
  rw [dist_comm T.base x] at hh
  dsimp [radius]
  nlinarith

theorem candidate_cover {n : ℕ} (T : UnitTube n) {δ : ℝ} (hδ1 : δ ≤ 1) :
    T.carrier δ ⊆ cellUnion 1 (candidates T) := by
  intro x hx
  apply (mem_cellUnion (by norm_num) _ x).mpr
  have hc := cell_base_distance T hδ1 hx (gridCell_covers (by norm_num) x)
  have hb := ball_subset_gridBox (by norm_num : (0:ℝ)<1) T.base
    (R:=radius n) (z:=label 1 x) (by simpa only [mul_one,dist_comm] using hc)
  simpa only [candidates,div_one] using hb

/-- Choose an actual largest-mass unit-cell intersection on each tube.
The cell count, mass retention, and bounded distance from its center are proved. -/
theorem choose_cell {n : ℕ} (T : UnitTube n) {δ : ℝ} (hδ1 : δ ≤ 1)
    (Y : Set (Space n)) (hY : MeasurableSet Y) (hsub : Y ⊆ T.carrier δ)
    (hpos : 0 < (volume : Measure (Space n)).real Y) :
    ∃ q : Cell n,
      (volume : Measure (Space n)).real Y ≤ (binsPerTube n:ℝ)*
        (volume : Measure (Space n)).real (Y ∩ gridCell 1 q) ∧
      dist T.base (cellCenter 1 q) ≤ radius n := by
  have hne : (candidates T).Nonempty := card_pos.mp (by rw [candidates_card]; exact binsPerTube_pos n)
  obtain ⟨q,hq,hmax⟩ := (candidates T).exists_max_image
    (fun q => (volume : Measure (Space n)).real (Y ∩ gridCell 1 q)) hne
  have hcover : Y ⊆ cellUnion 1 (candidates T) := hsub.trans (candidate_cover T hδ1)
  have hsum := SamplingMeans.cell_mass_sum (by norm_num : (0:ℝ)<1) (candidates T) hY
  rw [Set.inter_eq_left.mpr hcover] at hsum
  have hle := sum_le_sum (fun r (hr : r ∈ candidates T) => hmax r hr)
  simp only [sum_const,nsmul_eq_mul,candidates_card] at hle
  have hmass := hsum.symm.trans_le hle
  have hp : 0 < (volume : Measure (Space n)).real (Y ∩ gridCell 1 q) := by
    have hK : (0:ℝ) < binsPerTube n := Nat.cast_pos.mpr (binsPerTube_pos n)
    nlinarith
  have hi : (Y ∩ gridCell 1 q).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn,measureReal_empty] at hp
    linarith
  obtain ⟨x,hx,hxq⟩ := hi
  exact ⟨q,hmass,cell_base_distance T hδ1 (hsub hx) hxq⟩

structure Partition {n M : ℕ} (F : TubeFamily n M) (Y : Fin M → Set (Space n)) where
  assignment : Fin M → Cell n
  retention : ∀ i, (volume : Measure (Space n)).real (Y i) ≤ (binsPerTube n:ℝ)*
    (volume : Measure (Space n)).real (Y i ∩ gridCell 1 (assignment i))
  bounded : ∀ i, dist (F.tube i).base (cellCenter 1 (assignment i)) ≤ radius n

theorem construct {n M : ℕ} (F : TubeFamily n M) (Y : Fin M → Set (Space n))
    {δ : ℝ} (hδ1 : δ ≤ 1) (hY : ∀ i, MeasurableSet (Y i))
    (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hpos : ∀ i, 0 < (volume : Measure (Space n)).real (Y i)) :
    Nonempty (Partition F Y) := by
  choose assignment hret hb using fun i => choose_cell (F.tube i) hδ1 (Y i) (hY i) (hsub i) (hpos i)
  exact ⟨⟨assignment,hret,hb⟩⟩

def Partition.selected {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) (i : Fin M) : Set (Space n) := Y i ∩ gridCell 1 (P.assignment i)

def Partition.group {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) (q : Cell n) : Set (Space n) :=
  ⋃ i, SpatialMarkedPartition.Full P.selected P.assignment q i

theorem Partition.group_cell {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) (q : Cell n) : P.group q ⊆ gridCell 1 q := by
  intro x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  have hh : x ∈ gridCell 1 (P.assignment (MeasurableMarkedSelection.index (indices P.assignment q) i)) := hi.2
  rwa [index_label P.assignment q i] at hh

theorem Partition.group_measurable {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) (hY : ∀ i, MeasurableSet (Y i)) (q : Cell n) : MeasurableSet (P.group q) := by
  apply MeasurableSet.iUnion
  intro i
  exact (hY _).inter (measurable_gridCell 1 _)

theorem Partition.group_finite {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) (q : Cell n) : (volume : Measure (Space n)) (P.group q) ≠ ∞ :=
  measure_ne_top_of_subset (P.group_cell q) (finite_gridCell 1 q)

theorem Partition.groups_disjoint {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) : Pairwise (fun q r => Disjoint (P.group q) (P.group r)) := by
  intro q r hqr
  exact (gridCell_disjoint (by norm_num : (0:ℝ)<1) hqr).mono (P.group_cell q) (P.group_cell r)

/-- The selected groups occupy disjoint ORIGINAL unit cells. Their actual
union measures therefore sum to at most the original full union measure. -/
theorem Partition.union_sum {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) (hY : ∀ i, MeasurableSet (Y i))
    (hfinite : (volume : Measure (Space n)) (⋃ i, Y i) ≠ ∞) :
    (∑ q ∈ labels P.assignment, (volume : Measure (Space n)).real (P.group q)) ≤
      (volume : Measure (Space n)).real (⋃ i, Y i) := by
  have heq := measureReal_biUnion_finset (μ:=(volume : Measure (Space n)))
    (s:=labels P.assignment) (f:=P.group)
    (fun q _ r _ hqr => P.groups_disjoint hqr)
    (fun q _ => P.group_measurable hY q) (fun q _ => P.group_finite q)
  rw [← heq]
  apply measureReal_mono _ hfinite
  intro x hx
  obtain ⟨q,_,hq⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
  exact Set.mem_iUnion.mpr ⟨_,hi.1⟩

end
end KakeyaFormal.MeasurableUnitPartition
