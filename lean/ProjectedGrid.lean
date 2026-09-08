import GridCells
import TubeGeometry
import SamplingGeometry

/-! One common rounded projection map on the original integer-grid labels.
The image shading has a geometric fiber bound on every noncollapsed tube;
no cell-count or projected-density estimate is an input. -/
namespace KakeyaFormal.ProjectedGrid
open GridCells GridGeometry SamplingGeometry
noncomputable section
open Classical

/-- The same rounding map is used for every original tube and shading. -/
def labelMap {n d : ℕ} (P : Space n →L[ℝ] Space d) (δ : ℝ) (z : Cell n) : Cell d :=
  label δ (P (cellCenter δ z))

theorem rounding_distance {n d : ℕ} (P : Space n →L[ℝ] Space d) {δ : ℝ}
    (hδ : 0 < δ) (z : Cell n) :
    dist (P (cellCenter δ z)) (cellCenter δ (labelMap P δ z)) ≤ (d:ℝ)*δ/2 :=
  cell_center_distance (gridCell_covers hδ _)

theorem same_label_distance {n d : ℕ} (P : Space n →L[ℝ] Space d) {δ : ℝ}
    (hδ : 0 < δ) {z w : Cell n} (heq : labelMap P δ z=labelMap P δ w) :
    dist (P (cellCenter δ z)) (P (cellCenter δ w)) ≤ (d:ℝ)*δ := by
  have hz := rounding_distance P hδ z
  have hw := rounding_distance P hδ w
  rw [heq] at hz
  have hh := dist_triangle (P (cellCenter δ z)) (cellCenter δ (labelMap P δ w))
    (P (cellCenter δ w))
  rw [dist_comm (cellCenter δ (labelMap P δ w))] at hh
  linarith

/-- The original-space radius of one actual map fiber on a good tube. -/
def fiberRadius (d : ℕ) (c K width : ℝ) : ℝ :=
  2*width+((d:ℝ)+2*K*width)/c

def fiberConstant (n d : ℕ) (c K width : ℝ) : ℕ :=
  (2*Nat.ceil (fiberRadius d c K width)+3)^n

theorem fiberConstant_pos (n d : ℕ) (c K width : ℝ) :
    0 < fiberConstant n d c K width := by unfold fiberConstant; positivity

/-- Actual original centers in the same projected cell stay a bounded number
of original mesh lengths apart along every noncollapsed original tube. -/
theorem fiber_center_distance {n d : ℕ} (P : Space n →L[ℝ] Space d) (T : UnitTube n)
    {δ c K width : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hK : ‖P‖ ≤ K)
    (hdir : c ≤ ‖P T.direction‖) {z w : Cell n}
    (hz : ∃ t ∈ Set.Icc (0:ℝ) 1, dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ)
    (hw : ∃ t ∈ Set.Icc (0:ℝ) 1, dist (cellCenter δ w) (T.axisPoint t) ≤ width*δ)
    (heq : labelMap P δ z=labelMap P δ w) :
    dist (cellCenter δ z) (cellCenter δ w) ≤ fiberRadius d c K width*δ := by
  obtain ⟨t,_,ht⟩ := hz
  obtain ⟨s,_,hs⟩ := hw
  let e1 := cellCenter δ z-T.axisPoint t
  let e2 := cellCenter δ w-T.axisPoint s
  have he1 : ‖e1‖ ≤ width*δ := by simpa only [e1,dist_eq_norm] using ht
  have he2 : ‖e2‖ ≤ width*δ := by simpa only [e2,dist_eq_norm] using hs
  have hzid : T.base+t • T.direction+e1=cellCenter δ z := by dsimp [e1,UnitTube.axisPoint]; abel
  have hwid : T.base+s • T.direction+e2=cellCenter δ w := by dsimp [e2,UnitTube.axisPoint]; abel
  have himage : ‖P (T.base+t • T.direction+e1)-P (T.base+s • T.direction+e2)‖ ≤ (d:ℝ)*δ := by
    rw [hzid,hwid]
    exact same_label_distance P hδ heq
  have hparam := KakeyaAudit.TubeGeometry.projected_tube_parameter_bound P T.base T.direction
    e1 e2 hc hdir hK he1 he2 himage
  have haxis := T.axisPoint_distance t s
  have htri := dist_triangle (cellCenter δ z) (T.axisPoint t) (cellCenter δ w)
  have htri2 := dist_triangle (T.axisPoint t) (T.axisPoint s) (cellCenter δ w)
  rw [haxis,dist_comm (T.axisPoint s)] at htri2
  have hid : ((d:ℝ)*δ+2*K*(width*δ))/c = (((d:ℝ)+2*K*width)/c)*δ := by ring
  rw [hid] at hparam
  dsimp [fiberRadius]
  linarith

/-- Actual integer-grid counting closes the collapse estimate, with an
explicit constant depending only on dimensions and fixed c,K,width. -/
theorem fiber_card {n d : ℕ} (P : Space n →L[ℝ] Space d) (T : UnitTube n)
    {δ c K width : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hK : ‖P‖ ≤ K)
    (hdir : c ≤ ‖P T.direction‖) (S : Finset (Cell n))
    (hinc : ∀ z ∈ S, ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ) (q : Cell d) :
    (S.filter (fun z => labelMap P δ z=q)).card ≤ fiberConstant n d c K width := by
  let B := S.filter (fun z => labelMap P δ z=q)
  by_cases hB : B.Nonempty
  · obtain ⟨w,hw⟩ := hB
    apply ball_grid_count hδ (cellCenter δ w) B
    intro z hz
    exact fiber_center_distance P T hδ hc hK hdir
      (hinc z (Finset.mem_filter.mp hz).1) (hinc w (Finset.mem_filter.mp hw).1)
      ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hw).2.symm)
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hB
    change B.card ≤ _
    rw [hz,Finset.card_empty]
    exact Nat.zero_le _

/-- The image loses at most the proved fixed fiber factor. -/
theorem image_card_lower {n d : ℕ} (P : Space n →L[ℝ] Space d) (T : UnitTube n)
    {δ c K width : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hK : ‖P‖ ≤ K)
    (hdir : c ≤ ‖P T.direction‖) (S : Finset (Cell n))
    (hinc : ∀ z ∈ S, ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ) :
    (S.card:ℝ)/(fiberConstant n d c K width:ℝ) ≤ ((S.image (labelMap P δ)).card:ℝ) := by
  have hsum : (S.card:ℝ) = ∑ q ∈ S.image (labelMap P δ),
      ((S.filter (fun z => labelMap P δ z=q)).card:ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to (s:=S) (t:=S.image (labelMap P δ))
      (g:=labelMap P δ) (fun z hz => Finset.mem_image.mpr ⟨z,hz,rfl⟩) (fun _ => (1:ℝ))
    simpa using hh.symm
  have hbound : (S.card:ℝ) ≤ ((S.image (labelMap P δ)).card:ℝ)*(fiberConstant n d c K width:ℝ) := by
    rw [hsum]
    calc
      _ ≤ ∑ _q ∈ S.image (labelMap P δ), (fiberConstant n d c K width:ℝ) := by
        apply Finset.sum_le_sum
        intro q _
        exact_mod_cast fiber_card P T hδ hc hK hdir S hinc q
      _ = _ := by simp
  exact (div_le_iff₀ (by exact_mod_cast fiberConstant_pos n d c K width)).mpr hbound

end
end KakeyaFormal.ProjectedGrid
