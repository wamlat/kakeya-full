import GridGeometry
import MeasurableOccupancy

/-! Concrete half-open Euclidean grid cells, centered at the formal grid points.
Their exact Lebesgue volumes and disjointness instantiate the measurable
occupancy system, and any cell touching a tube has a controlled center. -/
open MeasureTheory Set
open scoped ENNReal
namespace KakeyaFormal.GridCells

noncomputable def coordinateCell {k : ℕ} (δ : ℝ) (z : Cell k) : Set (Fin k → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico (δ*((z i:ℝ)-1/2)) (δ*((z i:ℝ)+1/2)))

noncomputable def gridCell {k : ℕ} (δ : ℝ) (z : Cell k) : Set (Space k) :=
  WithLp.ofLp ⁻¹' coordinateCell δ z

theorem mem_gridCell {k : ℕ} (δ : ℝ) (z : Cell k) (x : Space k) :
    x ∈ gridCell δ z ↔ ∀ i,
      δ*((z i:ℝ)-1/2) ≤ WithLp.ofLp x i ∧ WithLp.ofLp x i < δ*((z i:ℝ)+1/2) := by
  simp [gridCell,coordinateCell,Set.mem_pi]

theorem measurable_coordinateCell {k : ℕ} (δ : ℝ) (z : Cell k) :
    MeasurableSet (coordinateCell δ z) := by
  apply (measurableSet_pi (Set.to_countable _)).mpr
  exact Or.inl (fun _ _ => measurableSet_Ico)

theorem measurable_gridCell {k : ℕ} (δ : ℝ) (z : Cell k) :
    MeasurableSet (gridCell δ z) :=
  (measurable_coordinateCell δ z).preimage (PiLp.volume_preserving_ofLp (Fin k)).measurable

theorem volume_gridCell {k : ℕ} (δ : ℝ) (z : Cell k) :
    volume (gridCell δ z) = (ENNReal.ofReal δ)^k := by
  rw [gridCell,(PiLp.volume_preserving_ofLp (Fin k)).measure_preimage
    (measurable_coordinateCell δ z).nullMeasurableSet]
  unfold coordinateCell
  rw [Real.volume_pi_Ico]
  have hid : ∀ i : Fin k, δ*((z i:ℝ)+1/2)-δ*((z i:ℝ)-1/2) = δ := by intro i; ring
  simp only [hid,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem real_volume_gridCell {k : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (z : Cell k) :
    (volume : Measure (Space k)).real (gridCell δ z) = δ^k := by
  simp only [Measure.real,volume_gridCell,ENNReal.toReal_pow,ENNReal.toReal_ofReal hδ]

theorem finite_gridCell {k : ℕ} (δ : ℝ) (z : Cell k) :
    volume (gridCell δ z) ≠ ∞ := by rw [volume_gridCell]; finiteness

noncomputable def label {k : ℕ} (δ : ℝ) (x : Space k) : Cell k :=
  fun i => ⌊WithLp.ofLp x i / δ + 1/2⌋

theorem mem_gridCell_iff_label {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Cell k) (x : Space k) : x ∈ gridCell δ z ↔ label δ x = z := by
  rw [mem_gridCell,funext_iff]
  apply forall_congr'
  intro i
  rw [label,Int.floor_eq_iff]
  have hlo : δ*((z i:ℝ)-1/2) ≤ WithLp.ofLp x i ↔
      (z i:ℝ)-1/2 ≤ WithLp.ofLp x i/δ := by
    rw [le_div_iff₀ hδ]
    constructor <;> intro h <;> nlinarith
  have hhi : WithLp.ofLp x i < δ*((z i:ℝ)+1/2) ↔
      WithLp.ofLp x i/δ < (z i:ℝ)+1/2 := by
    rw [div_lt_iff₀ hδ]
    constructor <;> intro h <;> nlinarith
  rw [hlo,hhi]
  constructor <;> rintro ⟨a,b⟩ <;> constructor <;> linarith

theorem gridCell_covers {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (x : Space k) :
    x ∈ gridCell δ (label δ x) := (mem_gridCell_iff_label hδ _ _).mpr rfl

theorem gridCell_disjoint {k : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Pairwise (fun z w : Cell k => Disjoint (gridCell δ z) (gridCell δ w)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hzw (((mem_gridCell_iff_label hδ z x).mp hx).symm.trans
    ((mem_gridCell_iff_label hδ w x).mp hy))

/-- A dimension-only distance bound; the sharper sqrt(k)*δ/2 is unnecessary. -/
theorem cell_center_distance {k : ℕ} {δ : ℝ}
    {z : Cell k} {x : Space k} (hx : x ∈ gridCell δ z) :
    dist x (cellCenter δ z) ≤ (k:ℝ)*δ/2 := by
  have hcoords := (mem_gridCell δ z x).mp hx
  have hcoord : ∀ i : Fin k, |WithLp.ofLp (x-cellCenter δ z) i| ≤ δ/2 := by
    intro i
    have hi := hcoords i
    change |WithLp.ofLp x i - δ*(z i:ℝ)| ≤ δ/2
    exact abs_le.mpr ⟨by nlinarith [hi.1],by nlinarith [hi.2]⟩
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Fin k)))
    (f := fun i => |WithLp.ofLp (x-cellCenter δ z) i|) (fun i _ => abs_nonneg _)
  simp only [sq_abs, ← EuclideanSpace.real_norm_sq_eq] at hs
  have hsum : (∑ i, |WithLp.ofLp (x-cellCenter δ z) i|) ≤ (k:ℝ)*δ/2 := by
    calc
      _ ≤ ∑ _i : Fin k, δ/2 := Finset.sum_le_sum (fun i _ => hcoord i)
      _ = _ := by simp; ring
  have hsum0 : 0 ≤ ∑ i, |WithLp.ofLp (x-cellCenter δ z) i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg _)
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (x-cellCenter δ z)]

/-- Any finite list of distinct concrete grid cells gives the measurable system. -/
noncomputable def cellSystem {k Q : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (labels : Fin Q → Cell k) (hinj : Function.Injective labels) :
    Occupancy.CellSystem (volume : Measure (Space k)) Q where
  cell q := gridCell δ (labels q)
  measurable q := measurable_gridCell δ (labels q)
  disjoint := fun _i _j hij => gridCell_disjoint hδ (fun heq => hij (hinj heq))
  finite q := finite_gridCell δ (labels q)

/-- Physical cell incidence gives admissibility of its formal center, with only a
fixed enlargement of the tube width. -/
theorem touching_tube_center {k : ℕ} (T : UnitTube k) {δ width : ℝ}
    {z : Cell k}
    (htouch : (gridCell δ z ∩ T.carrier (width*δ)).Nonempty) :
    ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ z) (T.axisPoint t) ≤ (width+(k:ℝ)/2)*δ := by
  obtain ⟨x,hx,ht⟩ := htouch
  obtain ⟨t,ht,hxt⟩ := ht
  refine ⟨t,ht,?_⟩
  have hcell : dist (cellCenter δ z) x ≤ (k:ℝ)*δ/2 := by
    rw [dist_comm]
    exact cell_center_distance hx
  have htri := dist_triangle (cellCenter δ z) x (T.axisPoint t)
  nlinarith

/-- An explicitly bounded finite grid box contains every cell touching a bounded set. -/
theorem touching_bounded_set_label {k : ℕ} {δ R : ℝ} (hδ : 0 < δ)
    {z : Cell k} {Y : Set (Space k)}
    (hY : ∀ x ∈ Y, ‖x‖ ≤ R) (htouch : (gridCell δ z ∩ Y).Nonempty) :
    z ∈ GridGeometry.gridBox (fun _ => 0) (Nat.ceil (R/δ+(k:ℝ)/2)+1) := by
  obtain ⟨x,hcell,hx⟩ := htouch
  have hdist : dist (cellCenter δ z) (0 : Space k) ≤ (R/δ+(k:ℝ)/2)*δ := by
    have htri := dist_triangle (cellCenter δ z) x (0 : Space k)
    have hc : dist (cellCenter δ z) x ≤ (k:ℝ)*δ/2 := by
      rw [dist_comm]
      exact cell_center_distance hcell
    simp only [dist_zero_right] at htri
    have hid : (R/δ+(k:ℝ)/2)*δ = R+(k:ℝ)*δ/2 := by field_simp
    rw [hid]
    rw [dist_zero_right]
    linarith [hY x hx]
  have h := GridGeometry.ball_subset_gridBox hδ (0 : Space k) hdist
  simpa only [WithLp.ofLp_zero,Pi.zero_apply,zero_div,Int.floor_zero] using h

noncomputable def finiteCellSystem {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (labels : Finset (Cell k)) : Occupancy.CellSystem (volume : Measure (Space k)) labels.card :=
  cellSystem hδ (fun i => (labels.equivFin.symm i).val)
    (Subtype.val_injective.comp labels.equivFin.symm.injective)

/-- Every bounded measurable shading is covered by finitely many of the actual
half-open cells. This supplies the finite-partition hypothesis in occupancy. -/
theorem bounded_set_covered {k : ℕ} {δ R : ℝ} (hδ : 0 < δ)
    {Y : Set (Space k)} (hY : ∀ x ∈ Y, ‖x‖ ≤ R) :
    Y ⊆ (finiteCellSystem hδ
      (GridGeometry.gridBox (fun _ => 0) (Nat.ceil (R/δ+(k:ℝ)/2)+1))).covered := by
  intro x hx
  let labels := GridGeometry.gridBox (fun _ : Fin k => 0) (Nat.ceil (R/δ+(k:ℝ)/2)+1)
  have hlabel : label δ x ∈ labels :=
    touching_bounded_set_label hδ hY ⟨x,gridCell_covers hδ x,hx⟩
  let q := labels.equivFin ⟨label δ x,hlabel⟩
  apply Set.mem_iUnion.mpr
  refine ⟨q,?_⟩
  change x ∈ gridCell δ (labels.equivFin.symm q).val
  simp only [q,Equiv.symm_apply_apply]
  exact gridCell_covers hδ x

/-- Positive-measure incidences of any shading inside a physical tube obey the
actual tube-grid cardinality bound. No premise counting its cells is needed. -/
theorem positive_tube_cell_count {k : ℕ} (T : UnitTube k) {δ width : ℝ}
    (hδ : 0 < δ) (labels : Finset (Cell k)) {Y : Set (Space k)}
    (hYT : Y ⊆ T.carrier (width*δ)) :
    (labels.filter (fun z => 0 < (volume : Measure (Space k)).real (Y ∩ gridCell δ z))).card ≤
      (Nat.ceil (1/δ)+1)*(2*Nat.ceil (width+(k:ℝ)/2+1)+3)^k := by
  classical
  apply GridGeometry.unit_tube_grid_count T hδ
  intro z hz
  have hpos := (Finset.mem_filter.mp hz).2
  have hne : (Y ∩ gridCell δ z).Nonempty := by
    by_contra hn
    have hempty : Y ∩ gridCell δ z = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp only [hempty,measureReal_empty,lt_self_iff_false] at hpos
  obtain ⟨x,hx,hcell⟩ := hne
  exact touching_tube_center T ⟨x,hcell,hYT hx⟩

end KakeyaFormal.GridCells
