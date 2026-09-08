import HairbrushPlanes

/-!
# Actual packing near a great circle

An anisotropic spherical-chart box has one tangential coordinate of length O(ψ)
and actual transverse coordinates of width O(δ). The dimension drop in its
cardinality is proved by integer-box counting, not assumed as a planar estimate.
-/
namespace KakeyaFormal.ThickCircle

open KakeyaFormal.EuclideanSplit KakeyaFormal.GridGeometry KakeyaFormal.ProjectiveGeometry
open KakeyaFormal.HairbrushPlanes KakeyaFormal.PivotDirections

noncomputable section

def normalTail {k : ℕ} (v : Space (k+2)) : Space k := tail (tail v)

def thinBox {k : ℕ} (anchor : ℤ) (long short : ℕ) : Finset (Cell (k+1)) :=
  Fintype.piFinset (Fin.cases (Finset.Icc (anchor-(long:ℤ)) (anchor+(long:ℤ)))
    (fun _ : Fin k => Finset.Icc (-(short:ℤ)) (short:ℤ)))

theorem thinBox_card {k : ℕ} (anchor : ℤ) (long short : ℕ) :
    (thinBox (k := k) anchor long short).card = (2*long+1)*(2*short+1)^k := by
  rw [thinBox,Fintype.card_piFinset,Fin.prod_univ_succ]
  have hlong : (Finset.Icc (anchor-(long:ℤ)) (anchor+(long:ℤ))).card = 2*long+1 := by
    rw [Int.card_Icc]
    have hid : anchor+(long:ℤ)+1-(anchor-(long:ℤ)) = (2*long+1:ℕ) := by omega
    rw [hid,Int.toNat_natCast]
  have hshort : (Finset.Icc (-(short:ℤ)) (short:ℤ)).card = 2*short+1 := by
    rw [Int.card_Icc]
    have hid : (short:ℤ)+1-(-(short:ℤ)) = (2*short+1:ℕ) := by omega
    rw [hid,Int.toNat_natCast]
  simp only [Fin.cases_zero,Fin.cases_succ,hlong,hshort,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- An anisotropic integer box counts the actual spherical chart: only one
coordinate contributes the cap radius, while all normal coordinates stay thin. -/
theorem thick_chart_count {k : ℕ} (directions : Finset (Space (k+2)))
    (center : Space (k+2)) {δ c ψ width : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hunit : ∀ v ∈ directions, ‖v‖ = 1)
    (hchart : ∀ v ∈ directions, c ≤ head v)
    (hcap : ∀ v ∈ directions, dist v center ≤ ψ)
    (hthin : ∀ v ∈ directions, ‖normalTail v‖ ≤ width*δ)
    (hsep : ∀ v ∈ directions, ∀ w ∈ directions, v ≠ w → δ ≤ projectiveDistance v w) :
    let h := δ/(2*chartConstant (k+1) c)
    directions.card ≤ (2*Nat.ceil (ψ/h)+3)*(2*Nat.ceil ((width*δ)/h)+3)^k := by
  classical
  let h := δ/(2*chartConstant (k+1) c)
  have hC := chartConstant_pos (k+1) hc
  have hh : 0 < h := by dsimp [h]; positivity
  have hinj := chartBin_injective directions hc hδ hunit hchart hsep
  have hcard : (directions.image (chartBin h)).card = directions.card :=
    Finset.card_image_of_injOn hinj
  have hsub : directions.image (chartBin h) ⊆ thinBox
      ⌊WithLp.ofLp center (Fin.succ 0)/h⌋ (Nat.ceil (ψ/h)+1) (Nat.ceil ((width*δ)/h)+1) := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    rw [thinBox,Fintype.mem_piFinset]
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero,Finset.mem_Icc]
      exact floor_distance_bounds hh ((coordinate_dist_le v center (Fin.succ 0)).trans (hcap v hv))
    | succ i =>
      simp only [Fin.cases_succ,Finset.mem_Icc]
      have hcoord : |WithLp.ofLp v i.succ.succ| ≤ ‖normalTail v‖ := by
        simpa [normalTail,tail,Real.norm_eq_abs] using PiLp.norm_apply_le (normalTail v) i
      have hi : |WithLp.ofLp v i.succ.succ| ≤ width*δ := hcoord.trans (hthin v hv)
      have hb := floor_distance_bounds hh (by simpa only [sub_zero] using hi :
        |WithLp.ofLp v i.succ.succ-0| ≤ width*δ)
      simpa only [zero_div,Int.floor_zero,zero_sub,zero_add,chartBin] using hb
  have h := Finset.card_le_card hsub
  rw [hcard,thinBox_card] at h
  simpa [Nat.mul_add,Nat.add_assoc] using h

/-- The chart count is linear in ψ/δ, with dimension-dependent normal-width cost. -/
theorem thick_chart_count_real {k : ℕ} (directions : Finset (Space (k+2)))
    (center : Space (k+2)) {δ c ψ width : ℝ} (hδ : 0 < δ) (hc : 0 < c)
    (hψ : δ ≤ ψ) (hw : 0 ≤ width)
    (hunit : ∀ v ∈ directions, ‖v‖ = 1)
    (hchart : ∀ v ∈ directions, c ≤ head v)
    (hcap : ∀ v ∈ directions, dist v center ≤ ψ)
    (hthin : ∀ v ∈ directions, ‖normalTail v‖ ≤ width*δ)
    (hsep : ∀ v ∈ directions, ∀ w ∈ directions, v ≠ w → δ ≤ projectiveDistance v w) :
    (directions.card:ℝ) ≤
      (4*chartConstant (k+1) c+5)*(4*chartConstant (k+1) c*width+5)^k*(ψ/δ) := by
  have h := thick_chart_count directions center hδ hc hunit hchart hcap hthin hsep
  let Q := chartConstant (k+1) c
  have hQ : 0 < Q := chartConstant_pos (k+1) hc
  let hmesh := δ/(2*Q)
  have hm : 0 < hmesh := by dsimp [hmesh]; positivity
  have hp : 1 ≤ ψ/δ := (le_div_iff₀ hδ).mpr (by simpa using hψ)
  have hp0 : 0 < ψ := hδ.trans_le hψ
  have hcl := Nat.ceil_lt_add_one (by positivity : 0 ≤ ψ/hmesh)
  have hcs := Nat.ceil_lt_add_one (by positivity : 0 ≤ (width*δ)/hmesh)
  have hid1 : ψ/hmesh = 2*Q*(ψ/δ) := by dsimp [hmesh]; field_simp
  have hid2 : (width*δ)/hmesh = 2*Q*width := by dsimp [hmesh]; field_simp
  rw [hid1] at hcl
  rw [hid2] at hcs
  have hlong : ((2*Nat.ceil (ψ/hmesh)+3:ℕ):ℝ) ≤ (4*Q+5)*(ψ/δ) := by rw [hid1]; push_cast; nlinarith
  have hshort : ((2*Nat.ceil ((width*δ)/hmesh)+3:ℕ):ℝ) ≤ 4*Q*width+5 := by rw [hid2]; push_cast; linarith
  have hcast : (directions.card:ℝ) ≤
      ((2*Nat.ceil (ψ/hmesh)+3:ℕ):ℝ)*((2*Nat.ceil ((width*δ)/hmesh)+3:ℕ):ℝ)^k := by
    exact_mod_cast h
  have hshortpow := pow_le_pow_left₀ (by positivity) hshort k
  have hmul := mul_le_mul hlong hshortpow (by positivity) (by positivity : 0 ≤ (4*Q+5)*(ψ/δ))
  exact hcast.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hmul)

def planeChart {k : ℕ} (move sign : Bool) (v : Space (k+2)) : Space (k+2) :=
  chartMove (if move then (1 : Fin (k+2)) else 0) sign v

theorem planeChart_norm {k : ℕ} (move sign : Bool) (v : Space (k+2)) :
    ‖planeChart move sign v‖ = ‖v‖ := chartMove_norm _ _ _

theorem planeChart_dist {k : ℕ} (move sign : Bool) (v w : Space (k+2)) :
    dist (planeChart move sign v) (planeChart move sign w) = dist v w := chartMove_dist _ _ _ _

theorem planeChart_projective {k : ℕ} (move sign : Bool) (v w : Space (k+2)) :
    projectiveDistance (planeChart move sign v) (planeChart move sign w) = projectiveDistance v w :=
  chartMove_projective _ _ _ _

theorem planeChart_injective {k : ℕ} (move sign : Bool) :
    Function.Injective (planeChart (k := k) move sign) := chartMove_injective _ _

/-- Only the two tangential coordinates are exchanged; normal thickness is
preserved exactly under every one of the four required signed charts. -/
theorem planeChart_normalTail {k : ℕ} (move sign : Bool) (v : Space (k+2)) :
    ‖normalTail (planeChart move sign v)‖ = ‖normalTail v‖ := by
  let idx : Fin (k+2) := if move then 1 else 0
  have hidx : idx.val < 2 := by cases move <;> norm_num [idx]
  have heq : normalTail (reindex (Equiv.swap 0 idx) v) = normalTail v := by
    ext i
    change WithLp.ofLp v ((Equiv.swap 0 idx) i.succ.succ) = WithLp.ofLp v i.succ.succ
    have hi0 : i.succ.succ ≠ (0 : Fin (k+2)) := by intro h; have := congrArg Fin.val h; simp at this
    have hii : i.succ.succ ≠ idx := by
      intro h
      have he := congrArg Fin.val h
      simp only [Fin.val_succ] at he
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hi0 hii]
  cases sign with
  | false =>
    change ‖normalTail (-(reindex (Equiv.swap 0 idx) v))‖ = ‖normalTail v‖
    have hn := congrArg norm heq
    simpa only [normalTail,tail_neg,norm_neg] using hn
  | true => exact congrArg norm heq

/-- Every unit vector within half-unit normal thickness lies in one of four
positive tangential charts, independent of ambient dimension. -/
theorem unit_in_plane_chart {k : ℕ} (v : Space (k+2)) (hv : ‖v‖ = 1)
    (hthin : ‖normalTail v‖ ≤ 1/2) :
    ∃ move sign : Bool, (1/2:ℝ) ≤ head (planeChart move sign v) := by
  have hs1 := norm_sq_split v
  have hs2 := norm_sq_split (tail v)
  rw [hv,one_pow] at hs1
  have hn : 0 ≤ ‖normalTail v‖ := norm_nonneg _
  have hchoices : (1/2:ℝ) ≤ |head v| ∨ (1/2:ℝ) ≤ |head (tail v)| := by
    by_contra h
    push Not at h
    have h0 := sq_abs (head v)
    have h1 := sq_abs (head (tail v))
    change ‖tail v‖^2 = head (tail v)^2+‖normalTail v‖^2 at hs2
    nlinarith [abs_nonneg (head v),abs_nonneg (head (tail v))]
  rcases hchoices with hzero | hone
  · by_cases hp : 0 ≤ head v
    · refine ⟨false,true,?_⟩
      rw [abs_of_nonneg hp] at hzero
      simpa [head,planeChart,chartMove_zero] using hzero
    · refine ⟨false,false,?_⟩
      rw [abs_of_neg (lt_of_not_ge hp)] at hzero
      simpa [head,planeChart,chartMove_zero] using hzero
  · by_cases hp : 0 ≤ head (tail v)
    · refine ⟨true,true,?_⟩
      rw [abs_of_nonneg hp] at hone
      simpa [head,tail,planeChart,chartMove_zero] using hone
    · refine ⟨true,false,?_⟩
      rw [abs_of_neg (lt_of_not_ge hp)] at hone
      simpa [head,tail,planeChart,chartMove_zero] using hone

def circleConstant (k : ℕ) (width : ℝ) : ℝ :=
  4*(4*chartConstant (k+1) (1/2)+5)*(4*chartConstant (k+1) (1/2)*width+5)^k

/-- Full actual spherical cap packing near the coordinate great circle.
The cap exponent is one, and all k normal directions cost only a width constant. -/
theorem spherical_thick_circle_count {k : ℕ} (directions : Finset (Space (k+2)))
    (center : Space (k+2)) {δ ψ width : ℝ} (hδ : 0 < δ) (hψ : δ ≤ ψ)
    (hw : 0 ≤ width) (hsmall : width*δ ≤ 1/2)
    (hunit : ∀ v ∈ directions, ‖v‖ = 1)
    (hcap : ∀ v ∈ directions, dist v center ≤ ψ)
    (hthin : ∀ v ∈ directions, ‖normalTail v‖ ≤ width*δ)
    (hsep : ∀ v ∈ directions, ∀ w ∈ directions, v ≠ w → δ ≤ projectiveDistance v w) :
    (directions.card:ℝ) ≤ circleConstant k width*(ψ/δ) := by
  classical
  let blocks : (Bool × Bool) → Finset (Space (k+2)) := fun label =>
    directions.filter (fun v => (1/2:ℝ) ≤ head (planeChart label.1 label.2 v))
  have hcover : directions ⊆ Finset.univ.biUnion blocks := by
    intro v hv
    obtain ⟨move,sign,hchart⟩ := unit_in_plane_chart v (hunit v hv) ((hthin v hv).trans hsmall)
    exact Finset.mem_biUnion.mpr ⟨(move,sign),Finset.mem_univ _,Finset.mem_filter.mpr ⟨hv,hchart⟩⟩
  have hblock (label : Bool × Bool) : ((blocks label).card:ℝ) ≤
      (4*chartConstant (k+1) (1/2)+5)*(4*chartConstant (k+1) (1/2)*width+5)^k*(ψ/δ) := by
    let moved := (blocks label).image (planeChart label.1 label.2)
    have hcard : moved.card = (blocks label).card :=
      Finset.card_image_of_injective _ (planeChart_injective _ _)
    have hu : ∀ v ∈ moved, ‖v‖ = 1 := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      rw [planeChart_norm]
      exact hunit w (Finset.mem_filter.mp hw).1
    have hc : ∀ v ∈ moved, (1/2:ℝ) ≤ head v := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hw).2
    have hd : ∀ v ∈ moved, dist v (planeChart label.1 label.2 center) ≤ ψ := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      rw [planeChart_dist]
      exact hcap w (Finset.mem_filter.mp hw).1
    have ht : ∀ v ∈ moved, ‖normalTail v‖ ≤ width*δ := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      rw [planeChart_normalTail]
      exact hthin w (Finset.mem_filter.mp hw).1
    have hs : ∀ v ∈ moved, ∀ w ∈ moved, v ≠ w → δ ≤ projectiveDistance v w := by
      intro v hv w hw hne
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hw
      rw [planeChart_projective]
      apply hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      intro hab
      exact hne (congrArg _ hab)
    simpa only [hcard] using thick_chart_count_real moved (planeChart label.1 label.2 center)
      hδ (show (0:ℝ) < 1/2 by norm_num) hψ hw hu hc hd ht hs
  have hcount := (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hcountR : (directions.card:ℝ) ≤ ∑ label : Bool × Bool, ((blocks label).card:ℝ) := by
    exact_mod_cast hcount
  calc
    _ ≤ ∑ label : Bool × Bool, ((blocks label).card:ℝ) := hcountR
    _ ≤ ∑ _label : Bool × Bool,
        (4*chartConstant (k+1) (1/2)+5)*(4*chartConstant (k+1) (1/2)*width+5)^k*(ψ/δ) :=
      Finset.sum_le_sum (fun label _ => hblock label)
    _ = _ := by simp [circleConstant]; ring

/-- Antipodal representative selection preserves the actual normal thickness. -/
theorem normalTail_nearRepresentative {k : ℕ} (center v : Space (k+2)) (r : ℝ) :
    ‖normalTail (nearRepresentative center r v)‖ = ‖normalTail v‖ := by
  unfold nearRepresentative
  split_ifs <;> simp only [normalTail,tail_neg,norm_neg]

/-- The corresponding projective-cap count uses actual antipodal representatives. -/
theorem projective_thick_circle_count {k : ℕ} (directions : Finset (Space (k+2)))
    (center : Space (k+2)) {δ ψ width : ℝ} (hδ : 0 < δ) (hψ : δ ≤ ψ)
    (hw : 0 ≤ width) (hsmall : width*δ ≤ 1/2)
    (hunit : ∀ v ∈ directions, ‖v‖ = 1)
    (hcap : ∀ v ∈ directions, projectiveDistance v center ≤ ψ)
    (hthin : ∀ v ∈ directions, ‖normalTail v‖ ≤ width*δ)
    (hsep : ∀ v ∈ directions, ∀ w ∈ directions, v ≠ w → δ ≤ projectiveDistance v w) :
    (directions.card:ℝ) ≤ circleConstant k width*(ψ/δ) := by
  classical
  let reps := directions.image (nearRepresentative center ψ)
  have hcard : reps.card = directions.card :=
    Finset.card_image_of_injOn (nearRepresentative_injective directions center ψ hδ hsep)
  have hu : ∀ v ∈ reps, ‖v‖ = 1 := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rw [nearRepresentative_norm]
    exact hunit w hw
  have hc : ∀ v ∈ reps, dist v center ≤ ψ := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    exact nearRepresentative_in_cap center w (hcap w hw)
  have ht : ∀ v ∈ reps, ‖normalTail v‖ ≤ width*δ := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    rw [normalTail_nearRepresentative]
    exact hthin w hw
  have hs : ∀ v ∈ reps, ∀ w ∈ reps, v ≠ w → δ ≤ projectiveDistance v w := by
    intro v hv w hw hne
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hw
    rw [nearRepresentative_projective]
    apply hsep a ha b hb
    intro hab
    exact hne (congrArg _ hab)
  simpa only [hcard] using spherical_thick_circle_count reps center hδ hψ hw hsmall hu hc ht hs

/-- Indexed original directions retain their true index count: separation proves
injectivity of the actual direction map. -/
theorem indexed_thick_circle_count {ι : Type*} {k : ℕ}
    (indices : Finset ι) (direction : ι → Space (k+2)) (center : Space (k+2))
    {δ ψ width : ℝ} (hδ : 0 < δ) (hψ : δ ≤ ψ) (hw : 0 ≤ width) (hsmall : width*δ ≤ 1/2)
    (hunit : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hcap : ∀ i ∈ indices, projectiveDistance (direction i) center ≤ ψ)
    (hthin : ∀ i ∈ indices, ‖normalTail (direction i)‖ ≤ width*δ)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j → δ ≤ projectiveDistance (direction i) (direction j)) :
    (indices.card:ℝ) ≤ circleConstant k width*(ψ/δ) := by
  classical
  have hinj : Set.InjOn direction (indices : Set ι) := by
    intro i hi j hj heq
    by_contra hne
    have h := hsep i hi j hj hne
    rw [heq,projectiveDistance_self] at h
    linarith
  have hcard := Finset.card_image_of_injOn hinj
  have h := projective_thick_circle_count (indices.image direction) center hδ hψ hw hsmall ?_ ?_ ?_ ?_
  · simpa only [hcard] using h
  · intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact hunit i hi
  · intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact hcap i hi
  · intro v hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    exact hthin i hi
  · intro v hv w hw hne
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    exact hsep i hi j hj (fun heq => hne (congrArg direction heq))

/-- Straighten any actual stem plane by an orthogonal transverse reflection. -/
def straightenPlane {k : ℕ} (f : Space (k+2) ≃ₗᵢ[ℝ] Space (k+2)) (w : Space (k+1)) :
    Space (k+2) ≃ₗᵢ[ℝ] Space (k+2) := f.trans (liftIsometry (alignStem w))

theorem normalTail_straightenPlane {k : ℕ}
    (f : Space (k+2) ≃ₗᵢ[ℝ] Space (k+2)) (w : Space (k+1)) (v : Space (k+2)) :
    normalTail (straightenPlane f w v) =
      transverseCoordinate (alignStem w) (transverseCoordinate f v) := by
  simp [straightenPlane,liftIsometry,normalTail,transverseCoordinate]

/-- A direction assigned to a δ-near plane bin is within actual normal distance
δ of its great circle after straightening; there is no inverse-transversality loss. -/
theorem assigned_direction_thin {k : ℕ} (f : Space (k+2) ≃ₗᵢ[ℝ] Space (k+2))
    (w : Space (k+1)) (v : Space (k+2)) {δ : ℝ}
    (hδ : 0 ≤ δ) (hw : ‖w‖ = 1) (hv : ‖v‖ = 1)
    (hnear : projectiveDistance (unitize (transverseCoordinate f v)) w ≤ δ) :
    ‖normalTail (straightenPlane f w v)‖ ≤ δ := by
  obtain ⟨b,hb⟩ := scalar_projective_match (unitize (transverseCoordinate f v)) w
    ‖transverseCoordinate f v‖ hnear
  rw [norm_smul_unitize,abs_of_nonneg (norm_nonneg _)] at hb
  have hcoord : ‖transverseCoordinate f v‖ ≤ 1 := by
    simpa only [hv] using transverseCoordinate_norm_le f v
  have hstem : transverseCoordinate (alignStem w) w = 0 := by
    simp [transverseCoordinate,alignStem_apply w hw,axisUnit]
  have h := (transverseCoordinate_norm_le (alignStem w) (transverseCoordinate f v-b • w)).trans hb
  rw [transverseCoordinate_sub,transverseCoordinate_smul,hstem,smul_zero,sub_zero] at h
  rw [normalTail_straightenPlane]
  exact h.trans (by nlinarith)

/-- Actual original tube directions in one plane bin obey O(ψ/δ) cap counting.
The orthogonal straightening map is constructed from its actual stem and bin. -/
theorem plane_bin_direction_count {ι : Type*} {k : ℕ} (stem : UnitTube (k+2))
    (indices : Finset ι) (bristle : ι → UnitTube (k+2)) (w : Space (k+1))
    (center : Space (k+2)) {δ ψ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/2) (hψ : δ ≤ ψ)
    (hw : ‖w‖ = 1)
    (hbin : ∀ i ∈ indices, projectiveDistance (bristleNormal stem (bristle i)) w ≤ δ)
    (hcap : ∀ i ∈ indices, projectiveDistance (bristle i).direction center ≤ ψ)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      δ ≤ projectiveDistance (bristle i).direction (bristle j).direction) :
    (indices.card:ℝ) ≤ circleConstant k 1*(ψ/δ) := by
  let f := straightenPlane (alignStem stem.direction) w
  apply indexed_thick_circle_count (width := (1:ℝ)) indices (fun i => f (bristle i).direction) (f center)
    hδ hψ (show (0:ℝ) ≤ 1 by norm_num) (by simpa using hδsmall)
  · intro i hi
    rw [f.norm_map,(bristle i).unit_direction]
  · intro i hi
    rw [isometry_projective]
    exact hcap i hi
  · intro i hi
    simpa only [one_mul] using assigned_direction_thin (alignStem stem.direction) w (bristle i).direction
      hδ.le hw (bristle i).unit_direction (hbin i hi)
  · intro i hi j hj hne
    rw [isometry_projective]
    exact hsep i hi j hj hne

end
end KakeyaFormal.ThickCircle

#print axioms KakeyaFormal.ThickCircle.plane_bin_direction_count
