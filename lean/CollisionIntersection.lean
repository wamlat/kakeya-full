import TubeIntersection
import TransverseAngles

/-! Actual finite original-grid label counts for the intersections appearing
in the pivot collision row. No estimate is inferred from volume, and no cell
intersection count is included among the hypotheses. -/
namespace KakeyaFormal.CollisionIntersection
open Finset TubeIntersection TubeLocalCount TransverseAngles
noncomputable section
open Classical

/-- Fixed geometric constant; the original tube width is used for local grid
packing, with a positive auxiliary enlargement only in the diameter bound. -/
def intersectionConstant (k : ℕ) (width : ℝ) : ℝ :=
  16*(1+width)*((6+4*width)*((2*Nat.ceil (width+1)+3:ℕ):ℝ)^k)

theorem intersectionConstant_pos (k : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    0 < intersectionConstant k width := by
  unfold intersectionConstant
  positivity

/-- Actual centers in two transverse finite tube carriers occupy only C/theta
original mesh cells. Empty intersections and zero original width are included. -/
theorem common_cell_count {k : ℕ} (T S : UnitTube k) {δ width theta : ℝ}
    (hδ : 0 < δ) (hw : 0 ≤ width) (htheta : 0 < theta)
    (hangle : theta ≤ projectiveDistance T.direction S.direction)
    (cells : Finset (Cell k))
    (hT : ∀ z ∈ cells, cellCenter δ z ∈ T.carrier (width*δ))
    (hS : ∀ z ∈ cells, cellCenter δ z ∈ S.carrier (width*δ)) :
    (cells.card:ℝ) ≤ intersectionConstant k width/theta := by
  by_cases hne : cells.Nonempty
  · obtain ⟨z₀,hz₀⟩ := hne
    have hthick : 0 < (1+width)*δ := by positivity
    have hwidth : width*δ ≤ (1+width)*δ := by nlinarith
    have hT' (z) (hz : z ∈ cells) : cellCenter δ z ∈ T.carrier ((1+width)*δ) := by
      obtain ⟨t,ht,hzt⟩ := hT z hz
      exact ⟨t,ht,hzt.trans hwidth⟩
    have hS' (z) (hz : z ∈ cells) : cellCenter δ z ∈ S.carrier ((1+width)*δ) := by
      obtain ⟨t,ht,hzt⟩ := hS z hz
      exact ⟨t,ht,hzt.trans hwidth⟩
    have htheta2 := hangle.trans (unit_projective_le_two _ _ T.unit_direction S.unit_direction)
    have hr : δ ≤ 16*((1+width)*δ)/theta := by
      apply (le_div_iff₀ htheta).mpr
      nlinarith [mul_le_mul_of_nonneg_left htheta2 hδ.le]
    have hball : ∀ z ∈ cells,
        dist (cellCenter δ z) (cellCenter δ z₀) ≤ 16*((1+width)*δ)/theta := by
      intro z hz
      exact common_point_distance T S hthick htheta hangle (hT' z hz) (hT' z₀ hz₀)
        (hS' z hz) (hS' z₀ hz₀)
    have hh := tube_ball_grid_count_real T hδ hw hr (cellCenter δ z₀) cells hT hball
    have hid : ((6+4*width)*((2*Nat.ceil (width+1)+3:ℕ):ℝ)^k)*
        ((16*((1+width)*δ)/theta)/δ) = intersectionConstant k width/theta := by
      unfold intersectionConstant
      field_simp
    exact hh.trans_eq hid
  · rw [not_nonempty_iff_eq_empty.mp hne,card_empty,Nat.cast_zero]
    exact div_nonneg (intersectionConstant_pos k hw).le htheta.le

/-- Common occupied labels of two original tubes satisfy the preceding actual
geometric bound. No direction separation for other tubes is required. -/
theorem common_shading_count {k M : ℕ} (F : TubeFamily k M) {δ width theta : ℝ}
    (hδ : 0 < δ) (hw : 0 ≤ width) (htheta : 0 < theta)
    (hadm : F.Admissible width δ) (i j : Fin M)
    (hangle : theta ≤ projectiveDistance (F.tube i).direction (F.tube j).direction) :
    ((F.shade i ∩ F.shade j).card:ℝ) ≤ intersectionConstant k width/theta := by
  apply common_cell_count (F.tube i) (F.tube j) hδ hw htheta hangle
  · intro z hz
    exact hadm i z (mem_inter.mp hz).1
  · intro z hz
    exact hadm j z (mem_inter.mp hz).2

/-- Any genuinely represented set of common intermediate labels is bounded
by C/phi. In particular this applies throughout each collision shell phi≥delta. -/
theorem common_label_subset_count {k M : ℕ} (F : TubeFamily k M) {δ width phi : ℝ}
    (hδ : 0 < δ) (hw : 0 ≤ width) (hphi : 0 < phi)
    (hadm : F.Admissible width δ) (i j : Fin M)
    (hangle : phi ≤ projectiveDistance (F.tube i).direction (F.tube j).direction)
    (labels : Finset (Cell k)) (hlabels : labels ⊆ F.shade i ∩ F.shade j) :
    (labels.card:ℝ) ≤ intersectionConstant k width/phi := by
  have hh : (labels.card:ℝ) ≤ ((F.shade i ∩ F.shade j).card:ℝ) := by
    exact_mod_cast card_le_card hlabels
  exact hh.trans (common_shading_count F hδ hw hphi hadm i j hangle)

/-- Vertex labels on the original competing-first and fixed-second tubes have
the stronger C/(2*kappa) bound at the actual marked-angle threshold. -/
theorem common_vertex_count {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ width kappa : ℝ} (hδ : 0 < δ) (hw : 0 ≤ width) (hkappa : 0 < kappa)
    (hadm : F.Admissible width δ) (i j : Fin M)
    (hangle : 2*kappa ≤ projectiveDistance (F.tube i).direction (F.tube j).direction) :
    ((H ∩ (F.shade i ∩ F.shade j)).card:ℝ) ≤ intersectionConstant k width/(2*kappa) :=
  common_label_subset_count F hδ hw (by positivity) hadm i j hangle _ inter_subset_right

/-- An actual marked angle is uniquely determined by its common vertex once
its two original tube indices are fixed. Thus no multiplicity of witnesses is
hidden when vertex labels are used to count competing angles. -/
theorem fixed_pair_vertex_injective {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    (kappa : ℝ) (i j : Fin M) :
    Set.InjOn Sigma.fst ((angles F H kappa).filter (fun a => a.2.1=i ∧ a.2.2=j) :
      Set (Σ _z : Cell k, Fin M × Fin M)) := by
  intro a ha b hb hab
  obtain ⟨_,hai,haj⟩ := mem_filter.mp ha
  obtain ⟨_,hbi,hbj⟩ := mem_filter.mp hb
  exact Sigma.ext hab (heq_of_eq (Prod.ext (hai.trans hbi.symm) (haj.trans hbj.symm)))

/-- The actual finite set of competing marked angles for fixed original first
and second tubes has C/(2*kappa) elements. Its angle separation is obtained
from its membership condition, rather than added as a further premise. -/
theorem fixed_pair_angle_count {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ width kappa : ℝ} (hδ : 0 < δ) (hw : 0 ≤ width) (hkappa : 0 < kappa)
    (hadm : F.Admissible width δ) (i j : Fin M) :
    (((angles F H kappa).filter (fun a => a.2.1=i ∧ a.2.2=j)).card:ℝ) ≤
      intersectionConstant k width/(2*kappa) := by
  let A := (angles F H kappa).filter (fun a => a.2.1=i ∧ a.2.2=j)
  by_cases hne : A.Nonempty
  · obtain ⟨a,ha⟩ := hne
    obtain ⟨ha,hai,haj⟩ := mem_filter.mp ha
    have hangle := ((mem_angles F H kappa a).mp ha).2.2.2
    rw [hai,haj] at hangle
    have hsub : A.image Sigma.fst ⊆ H ∩ (F.shade i ∩ F.shade j) := by
      intro z hz
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hz
      obtain ⟨hb,hbi,hbj⟩ := mem_filter.mp hb
      obtain ⟨hbH,hb1,hb2,_⟩ := (mem_angles F H kappa b).mp hb
      rw [hbi] at hb1
      rw [hbj] at hb2
      exact mem_inter.mpr ⟨hbH,mem_inter.mpr ⟨hb1,hb2⟩⟩
    have hc : ((A.image Sigma.fst).card:ℝ) ≤ ((H ∩ (F.shade i ∩ F.shade j)).card:ℝ) := by
      exact_mod_cast card_le_card hsub
    have hcard := card_image_of_injOn (fixed_pair_vertex_injective F H kappa i j)
    rw [hcard] at hc
    exact hc.trans (common_vertex_count F H hδ hw hkappa hadm i j hangle)
  · have hempty : A=∅ := not_nonempty_iff_eq_empty.mp hne
    change (A.card:ℝ) ≤ _
    rw [hempty,card_empty,Nat.cast_zero]
    exact div_nonneg (intersectionConstant_pos k hw).le (by positivity)


/-- A whole unit tube supplies the bottom-shell bound at theta=delta,
including a tube paired with itself. -/
theorem unit_cell_count {k : ℕ} (T : UnitTube k) {δ width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (cells : Finset (Cell k))
    (hT : ∀ z ∈ cells, cellCenter δ z ∈ T.carrier (width*δ)) :
    (cells.card:ℝ) ≤ intersectionConstant k width/δ := by
  have hh := GridGeometry.unit_tube_grid_count_real T hδ cells hT
  let box : ℝ := ((2*Nat.ceil (width+1)+3:ℕ):ℝ)^k
  have hbox : 0 ≤ box := by dsimp [box]; positivity
  have hratio : 1 ≤ 1/δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hfac : 1+1/δ ≤ 2/δ := by
    rw [show (2:ℝ)/δ=1/δ+1/δ by ring]
    exact add_le_add hratio (le_refl (1/δ))
  have hm := mul_le_mul_of_nonneg_left hfac (show 0 ≤ 2*box by positivity)
  have hfour : (cells.card:ℝ) ≤ 4*box/δ := by
    exact (hh.trans hm).trans_eq (by ring)
  have hcoeff : 4 ≤ 16*(1+width)*(6+4*width) := by nlinarith [sq_nonneg width]
  have hconst : 4*box ≤ intersectionConstant k width := by
    have hc := mul_le_mul_of_nonneg_right hcoeff hbox
    exact hc.trans_eq (by dsimp [intersectionConstant,box]; ring)
  exact hfour.trans (div_le_div_of_nonneg_right hconst hδ.le)

/-- All angular shells, including the diagonal and below-mesh shell, are
covered by one actual grid-label intersection bound. -/
theorem common_cell_count_max {k : ℕ} (T S : UnitTube k) {δ width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (cells : Finset (Cell k))
    (hT : ∀ z ∈ cells, cellCenter δ z ∈ T.carrier (width*δ))
    (hS : ∀ z ∈ cells, cellCenter δ z ∈ S.carrier (width*δ)) :
    (cells.card:ℝ) ≤ intersectionConstant k width/
      max (projectiveDistance T.direction S.direction) δ := by
  by_cases hangle : projectiveDistance T.direction S.direction ≤ δ
  · rw [max_eq_right hangle]
    exact unit_cell_count T hδ hδ1 hw cells hT
  · have hlt : δ < projectiveDistance T.direction S.direction := lt_of_not_ge hangle
    rw [max_eq_left hlt.le]
    exact common_cell_count T S hδ hw (hδ.trans hlt) le_rfl cells hT hS

/-- The original occupied-label version of the complete shell bound. -/
theorem common_shading_count_max {k M : ℕ} (F : TubeFamily k M) {δ width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hadm : F.Admissible width δ) (i j : Fin M) :
    ((F.shade i ∩ F.shade j).card:ℝ) ≤ intersectionConstant k width/
      max (projectiveDistance (F.tube i).direction (F.tube j).direction) δ := by
  apply common_cell_count_max (F.tube i) (F.tube j) hδ hδ1 hw
  · intro z hz
    exact hadm i z (mem_inter.mp hz).1
  · intro z hz
    exact hadm j z (mem_inter.mp hz).2


/-- The same count on the actual angle subtype used by the finite output
selection, with the original labels preserved exactly. -/
theorem fixed_pair_angle_subtype_count {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ width kappa : ℝ} (hδ : 0 < δ) (hw : 0 ≤ width) (hkappa : 0 < kappa)
    (hadm : F.Admissible width δ) (i j : Fin M) :
    (((univ : Finset ↥(angles F H kappa)).filter (fun a => a.val.2.1=i ∧ a.val.2.2=j)).card:ℝ) ≤
      intersectionConstant k width/(2*kappa) := by
  let A := (univ : Finset ↥(angles F H kappa)).filter (fun a => a.val.2.1=i ∧ a.val.2.2=j)
  have himage : A.image Subtype.val = (angles F H kappa).filter (fun a => a.2.1=i ∧ a.2.2=j) := by
    ext a
    simp only [A,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨⟨b,hb⟩,hbij,rfl⟩
      exact ⟨hb,hbij⟩
    · rintro ⟨ha,haij⟩
      exact ⟨⟨a,ha⟩,haij,rfl⟩
  have hcard := card_image_of_injective A Subtype.val_injective
  rw [himage] at hcard
  have hh := fixed_pair_angle_count F H hδ hw hkappa hadm i j
  rwa [hcard] at hh

end
end KakeyaFormal.CollisionIntersection
