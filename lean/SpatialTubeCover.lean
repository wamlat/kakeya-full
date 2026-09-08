import SpatialAngular
import SamplingGeometry

/-! A finite-length spatial cover at arbitrary positions. The transverse
grid has spacing `2*tau`; the longitudinal grid has spacing one. Every
cap-local tube is assigned once, and actual pointwise overlap is bounded by
a fixed product of lattice counts. No bounded-base hypothesis is used. -/
namespace KakeyaFormal.SpatialTubeCover
open EuclideanSplit SpatialAngular
noncomputable section

abbrev Label (k : ℕ) := Cell 1 × Cell k

def longitudinal {k : ℕ} (u x : Space (k+1)) : Space 1 :=
  cons (head (alignStem u x)) (0 : Space 0)

theorem longitudinal_distance {k : ℕ} (u x y : Space (k+1)) :
    dist (longitudinal u x) (longitudinal u y) ≤ dist x y := by
  rw [dist_eq_norm, longitudinal, longitudinal]
  have he : cons (head (alignStem u x)) (0 : Space 0) -
      cons (head (alignStem u y)) 0 = cons (head (alignStem u (x-y))) 0 := by
    rw [map_sub, head_sub]
    ext i
    fin_cases i
    rfl
  rw [he, norm_cons_axis]
  have hh := PiLp.norm_apply_le (alignStem u (x-y)) (0 : Fin (k+1))
  simpa only [head, Real.norm_eq_abs, (alignStem u).norm_map, dist_eq_norm] using hh

def label {k : ℕ} (u : Space (k+1)) (tau : ℝ) (T : UnitTube (k+1)) : Label k :=
  (GridCells.label 1 (longitudinal u T.base), spatialLabel u tau T)

def parallelBox {k : ℕ} (u : Space (k+1)) (tau : ℝ) (q : Label k)
    (H W : ℝ) : Set (Space (k+1)) :=
  {x | dist (longitudinal u x) (cellCenter 1 q.1) ≤ H ∧
    x ∈ cylinder u tau q.2 W}

theorem tube_in_box {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1)
    (T : UnitTube (k+1)) {δ tau width angular : ℝ}
    (htau : 0 < tau) (hdr : δ ≤ tau) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ width) (ha : 0 ≤ angular)
    (hcap : projectiveDistance T.direction u ≤ angular*tau) :
    T.carrier (width*δ) ⊆ parallelBox u tau (label u tau T)
      (2+width) ((k:ℝ)+width+angular) := by
  intro x hx
  refine ⟨?_,tube_in_spatial_cylinder u hu T htau hdr hw ha hcap hx⟩
  have hbase : dist x T.base ≤ 1+width := by
    obtain ⟨t,ht,hxt⟩ := hx
    have he : dist (T.axisPoint t) T.base ≤ 1 := by
      rw [dist_eq_norm, UnitTube.axisPoint, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, T.unit_direction, mul_one, abs_of_nonneg ht.1]
      exact ht.2
    have hh := dist_triangle x (T.axisPoint t) T.base
    have hwδ := mul_le_mul_of_nonneg_left hδ1 hw
    change dist x (T.axisPoint t) ≤ width*δ at hxt
    linarith
  have hproj := (longitudinal_distance u x T.base).trans hbase
  have hquant := GridCells.cell_center_distance
    (GridCells.gridCell_covers (by norm_num : (0:ℝ)<1) (longitudinal u T.base))
  have htri := dist_triangle (longitudinal u x) (longitudinal u T.base)
    (cellCenter 1 (label u tau T).1)
  change dist (longitudinal u x) (cellCenter 1 (label u tau T).1) ≤ 2+width
  norm_num only [Nat.cast_one, one_mul] at hquant
  change dist (longitudinal u T.base) (cellCenter 1 (label u tau T).1) ≤ (1:ℝ)/2 at hquant
  linarith

def overlapConstant (k : ℕ) (H W : ℝ) : ℕ :=
  (2*Nat.ceil H+3)*(2*Nat.ceil (W/2)+3)^k

theorem overlapConstant_pos (k : ℕ) (H W : ℝ) :
    0 < overlapConstant k H W := by unfold overlapConstant; positivity

theorem box_overlap {k : ℕ} (u x : Space (k+1)) {tau H W : ℝ}
    (htau : 0 < tau) (labels : Finset (Label k))
    (hpoint : ∀ q ∈ labels, x ∈ parallelBox u tau q H W) :
    labels.card ≤ overlapConstant k H W := by
  classical
  have hlong : (labels.image Prod.fst).card ≤ 2*Nat.ceil H+3 := by
    have hh := GridGeometry.ball_grid_count (by norm_num : (0:ℝ)<1)
      (longitudinal u x) (labels.image Prod.fst) (R := H) (by
        intro q hq
        obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
        simpa only [mul_one, dist_comm] using (hpoint p hp).1)
    simpa only [pow_one] using hh
  have htrans : (labels.image Prod.snd).card ≤ (2*Nat.ceil (W/2)+3)^k := by
    apply cylinder_overlap u x htau
    intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    exact (hpoint p hp).2
  have hsub : labels ⊆ (labels.image Prod.fst) ×ˢ (labels.image Prod.snd) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p,hp,rfl⟩,
      Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩
  exact (Finset.card_le_card hsub).trans (by
    rw [Finset.card_product]
    exact Nat.mul_le_mul hlong htrans)

theorem occupied_labels {ι : Type*} {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1)
    (tubes : ι → UnitTube (k+1)) (indices : Finset ι) (x : Space (k+1))
    {δ tau width angular : ℝ} (htau : 0 < tau) (hdr : δ ≤ tau) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ width) (ha : 0 ≤ angular)
    (hcap : ∀ i ∈ indices, projectiveDistance (tubes i).direction u ≤ angular*tau)
    (hpoint : ∀ i ∈ indices, x ∈ (tubes i).carrier (width*δ)) :
    (indices.image (fun i => label u tau (tubes i))).card ≤
      overlapConstant k (2+width) ((k:ℝ)+width+angular) := by
  classical
  apply box_overlap u x htau
  intro q hq
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
  exact tube_in_box u hu (tubes i) htau hdr hδ1 hw ha (hcap i hi) (hpoint i hi)

/-- The actual containing tube starts at the lower end of the box axis. -/
def containingTube {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1)
    (tau : ℝ) (q : Label k) (H : ℝ) : UnitTube (k+1) where
  base := latticeAxisPoint u tau q.2 (head (cellCenter 1 q.1)-H)
  direction := u
  unit_direction := hu

theorem containing_axis {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1)
    (tau : ℝ) (q : Label k) (H t : ℝ) :
    (containingTube u hu tau q H).axisPoint t =
      latticeAxisPoint u tau q.2 (head (cellCenter 1 q.1)-H+t) := by
  apply (alignStem u).injective
  simp only [UnitTube.axisPoint, containingTube, map_add, map_smul,
    latticeAxisPoint, LinearIsometryEquiv.apply_symm_apply, alignStem_apply u hu,
    axisUnit]
  rw [← cons_smul]
  simp only [smul_zero, mul_one, ← cons_add, add_zero]

theorem box_in_length_carrier {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1)
    (tau : ℝ) (q : Label k) (H W : ℝ) :
    parallelBox u tau q H W ⊆
      SamplingGeometry.lengthCarrier (containingTube u hu tau q H) (2*H) (W*tau) := by
  intro x hx
  have he : dist (longitudinal u x) (cellCenter 1 q.1) =
      |head (alignStem u x)-head (cellCenter 1 q.1)| := by
    rw [dist_eq_norm]
    have hz : (cellCenter 1 q.1 : Space 1) = cons (head (cellCenter 1 q.1)) (0 : Space 0) := by
      ext i
      fin_cases i
      rfl
    rw [hz]
    have hd : longitudinal u x-cons (head (cellCenter 1 q.1)) (0 : Space 0) =
        cons (head (alignStem u x)-head (cellCenter 1 q.1)) (0 : Space 0) := by
      ext i
      fin_cases i
      rfl
    rw [hd, norm_cons_axis, head_cons]
  have hb := abs_le.mp (he ▸ hx.1)
  refine ⟨head (alignStem u x)-head (cellCenter 1 q.1)+H, ⟨by linarith,by linarith⟩,?_⟩
  rw [containing_axis]
  have ht : head (cellCenter 1 q.1)-H+
      (head (alignStem u x)-head (cellCenter 1 q.1)+H)=head (alignStem u x) := by ring
  rw [ht, matching_axis_distance]
  exact hx.2

end
end KakeyaFormal.SpatialTubeCover
