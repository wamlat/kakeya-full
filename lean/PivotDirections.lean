import PivotWitnesses
import ProjectiveGeometry

/-!
# Directions determined by actual separated rounded points

Quantitative normalization and projective-cap bounds derived from Euclidean
point/axis incidence. These statements supply a geometric part of the collision
argument rather than presuming an angular packing bound.
-/
namespace KakeyaFormal.PivotDirections

open KakeyaFormal KakeyaFormal.ProjectiveGeometry KakeyaFormal.PivotWitnesses

noncomputable section

def unitize {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x : E) : E :=
  ‖x‖⁻¹ • x

theorem unitize_unit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : E) (hx : x ≠ 0) : ‖unitize x‖ = 1 := by
  rw [unitize,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)

/-- Normalizing a perturbation costs at most twice its relative error. -/
theorem unitize_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖unitize x-unitize y‖ ≤ 2*‖x-y‖/‖y‖ := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hid : unitize x-unitize y =
      (‖x‖⁻¹-‖y‖⁻¹) • x+‖y‖⁻¹ • (x-y) := by
    dsimp [unitize]
    module
  have hcoef : |‖x‖⁻¹-‖y‖⁻¹| *‖x‖ = |‖y‖-‖x‖|/‖y‖ := by
    have hid' : (‖x‖⁻¹-‖y‖⁻¹)*‖x‖ = (‖y‖-‖x‖)/‖y‖ := by field_simp
    calc
      _ = |(‖x‖⁻¹-‖y‖⁻¹)*‖x‖| := by rw [abs_mul,abs_of_pos hxn]
      _ = _ := by rw [hid',abs_div,abs_of_pos hyn]
  have hrev : |‖y‖-‖x‖| ≤ ‖x-y‖ := by
    simpa only [abs_sub_comm] using abs_norm_sub_norm_le x y
  rw [hid]
  calc
    _ ≤ ‖(‖x‖⁻¹-‖y‖⁻¹) • x‖+‖‖y‖⁻¹ • (x-y)‖ := norm_add_le _ _
    _ = |‖y‖-‖x‖|/‖y‖+‖x-y‖/‖y‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hcoef,
        abs_of_pos (inv_pos.mpr hyn)]
      ring
    _ ≤ ‖x-y‖/‖y‖+‖x-y‖/‖y‖ :=
      add_le_add (div_le_div_of_nonneg_right hrev hyn.le) (le_refl _)
    _ = _ := by ring

/-- Normalization ignores positive rescaling of a unit vector. -/
theorem unitize_pos_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (hv : ‖v‖ = 1) {a : ℝ} (ha : 0 < a) : unitize (a • v) = v := by
  simp [unitize,norm_smul,hv,Real.norm_eq_abs,abs_of_pos ha,smul_smul,ha.ne']

/-- Negative rescaling selects the antipodal unit representative. -/
theorem unitize_neg_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (hv : ‖v‖ = 1) {a : ℝ} (ha : a < 0) : unitize (a • v) = -v := by
  rw [unitize,norm_smul,Real.norm_eq_abs,hv,mul_one,abs_of_neg ha,smul_smul]
  have hid : (-a)⁻¹*a = -1 := by field_simp [ha.ne]
  rw [hid,neg_one_smul]

/-- A noncollapsed scalar-axis displacement determines its unit direction up to
an explicit projective error. No sign of the scalar is imposed. -/
theorem projective_direction_of_displacement {k : ℕ} (d v : Space k)
    {a err r : ℝ} (hv : ‖v‖ = 1) (hd : d ≠ 0) (hr : 0 < r)
    (ha : r ≤ |a|) (herr : ‖d-a • v‖ ≤ err) :
    projectiveDistance v (unitize d) ≤ 2*err/r := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha; linarith
  have hav : a • v ≠ 0 := by
    have hn : ‖a • v‖ = |a| := by simp [norm_smul,hv,Real.norm_eq_abs]
    intro h
    rw [h,norm_zero] at hn
    exact ha0 (abs_eq_zero.mp hn.symm)
  have hnorm := unitize_perturbation d (a • v) hd hav
  have hnorm' : ‖unitize d-unitize (a • v)‖ ≤ 2*err/r := by
    rw [norm_smul,Real.norm_eq_abs,hv,mul_one] at hnorm
    have he0 : 0 ≤ err := (norm_nonneg _).trans herr
    calc
      _ ≤ 2*‖d-a • v‖/|a| := hnorm
      _ ≤ 2*err/|a| := div_le_div_of_nonneg_right (by nlinarith) (abs_nonneg a)
      _ ≤ 2*err/r := div_le_div_of_nonneg_left (by positivity) hr ha
  rcases lt_or_gt_of_ne ha0 with hneg | hpos
  · rw [unitize_neg_smul v hv hneg] at hnorm'
    have h := projective_le_chord (-v) (unitize d)
    rw [projective_neg_left] at h
    exact h.trans (by simpa only [norm_sub_rev] using hnorm')
  · rw [unitize_pos_smul v hv hpos] at hnorm'
    exact (projective_le_chord v (unitize d)).trans
      (by simpa only [norm_sub_rev] using hnorm')

/-- The projective estimate remains valid if the observed displacement collapses;
then its large relative error already makes the bound trivial. -/
theorem projective_direction_of_displacement_any {k : ℕ} (d v : Space k)
    {a err r : ℝ} (hv : ‖v‖ = 1) (hr : 0 < r)
    (ha : r ≤ |a|) (herr : ‖d-a • v‖ ≤ err) :
    projectiveDistance v (unitize d) ≤ 2*err/r := by
  by_cases hd : d = 0
  · subst d
    have he : |a| ≤ err := by simpa [norm_smul,hv,Real.norm_eq_abs] using herr
    have hb : 1 ≤ 2*err/r := (le_div_iff₀ hr).mpr (by nlinarith)
    simpa [unitize,projectiveDistance,hv] using hb
  · exact projective_direction_of_displacement d v hv hd hr ha herr

/-- Subtracting two point/axis incidences gives an actual displacement error. -/
theorem two_point_axis_displacement {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p q x v : E) {s t err : ℝ}
    (hp : ‖p-(x+s • v)‖ ≤ err) (hq : ‖q-(x+t • v)‖ ≤ err) :
    ‖(q-p)-(t-s) • v‖ ≤ 2*err := by
  have hid : (q-p)-(t-s) • v = (q-(x+t • v))-(p-(x+s • v)) := by module
  rw [hid]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Two rounded points with separated actual axis coordinates locate the tube's
projective direction, including signed longitudinal parameters. -/
theorem two_point_direction_bound {k : ℕ} (p q x v : Space k)
    {s t err r : ℝ} (hv : ‖v‖ = 1) (hr : 0 < r) (hsep : r ≤ |t-s|)
    (hp : ‖p-(x+s • v)‖ ≤ err) (hq : ‖q-(x+t • v)‖ ≤ err) :
    projectiveDistance v (unitize (q-p)) ≤ 4*err/r := by
  have h := projective_direction_of_displacement_any (q-p) v hv hr hsep
    (two_point_axis_displacement p q x v hp hq)
  convert h using 1; ring

/-- The observed points themselves are distinct when their errors are smaller
than half the true longitudinal separation. -/
theorem two_point_observation_separated {k : ℕ} (p q x v : Space k)
    {s t err r : ℝ} (hv : ‖v‖ = 1) (hsep : r ≤ |t-s|)
    (hp : ‖p-(x+s • v)‖ ≤ err) (hq : ‖q-(x+t • v)‖ ≤ err) :
    r-2*err ≤ ‖q-p‖ := by
  have hd := two_point_axis_displacement p q x v hp hq
  have ht := norm_sub_le (q-p) ((q-p)-(t-s) • v)
  have hid : (q-p)-((q-p)-(t-s) • v) = (t-s) • v := by abel
  rw [hid,norm_smul,Real.norm_eq_abs,hv,mul_one] at ht
  linarith

/-- Actual projectively separated directions whose axes pass near two common
points are counted by dimension-(k) sphere packing in ambient dimension k+1.
The angular cap is derived from point incidences and longitudinal separation. -/
theorem common_two_point_direction_count {ι : Type*} {k : ℕ}
    (indices : Finset ι) (base direction : ι → Space (k+1))
    (first second : ι → ℝ) (p q : Space (k+1))
    {δ err r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (hcapScale : δ ≤ 4*err/r)
    (hunit : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hgap : ∀ i ∈ indices, r ≤ |second i-first i|)
    (hp : ∀ i ∈ indices, ‖p-(base i+first i • direction i)‖ ≤ err)
    (hq : ∀ i ∈ indices, ‖q-(base i+second i • direction i)‖ ≤ err)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      δ ≤ projectiveDistance (direction i) (direction j)) :
    (indices.card:ℝ) ≤ packingConstant k * ((4*err/r)/δ)^k := by
  exact indexed_projective_cap_packing indices direction (unitize (q-p)) hδ hcapScale hunit
    (fun i hi => two_point_direction_bound p q (base i) (direction i)
      (hunit i hi) hr (hgap i hi) (hp i hi) (hq i hi)) hsep

/-- The preceding count at the manuscript's pivot-output parameters. This is
O(C,k)*κ^(-2k) possible second-tube directions in ambient dimension k+1. -/
theorem pivot_output_direction_count {ι : Type*} {k : ℕ}
    (indices : Finset ι) (base direction : ι → Space (k+1))
    (first second : ι → ℝ) (p q : Space (k+1))
    {δ C kap : ℝ} (hδ : 0 < δ) (hC : 1 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hunit : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hgap : ∀ i ∈ indices, kap^2 ≤ |second i-first i|)
    (hp : ∀ i ∈ indices, ‖p-(base i+first i • direction i)‖ ≤ C*δ)
    (hq : ∀ i ∈ indices, ‖q-(base i+second i • direction i)‖ ≤ C*δ)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      δ ≤ projectiveDistance (direction i) (direction j)) :
    (indices.card:ℝ) ≤ packingConstant k * (4*C/kap^2)^k := by
  have hk2 : kap^2 ≤ 1 := pow_le_one₀ hk.le hk1
  have hc : δ ≤ 4*(C*δ)/kap^2 := (le_div_iff₀ (sq_pos_of_pos hk)).mpr (by nlinarith)
  have h := common_two_point_direction_count indices base direction first second p q
    hδ (sq_pos_of_pos hk) hc hunit hgap hp hq hsep
  have hid : (4*(C*δ)/kap^2)/δ = 4*C/kap^2 := by field_simp
  rwa [hid] at h

/-- Direct common-output application to the actual legal fiber records. The
indices represent distinct second-tube directions; their required separation is
exactly the original one-tube-per-direction hypothesis at this step. -/
theorem distinct_fiber_second_direction_count {ι : Type*} {k : ℕ}
    {δ C kap : ℝ} (indices : Finset ι) (fiber : ι → Fiber (k+1) δ kap C)
    (intermediate pivot : Cell (k+1))
    (hδ : 0 < δ) (hC : 1 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hintermediate : ∀ i ∈ indices, (fiber i).intermediateLabel = intermediate)
    (hpivot : ∀ i ∈ indices, (fiber i).pivotLabel = pivot)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      δ ≤ projectiveDistance (fiber i).angle.second (fiber j).angle.second) :
    (indices.card:ℝ) ≤ packingConstant k * (4*C/kap^2)^k := by
  apply pivot_output_direction_count indices
    (fun i => (fiber i).angle.vertex+(fiber i).angle.intermediate • (fiber i).angle.first)
    (fun i => (fiber i).angle.second) (fun _ => 0) (fun i => (fiber i).reference.coefficient)
    (cellCenter δ intermediate) (cellCenter δ pivot) hδ hC hk hk1
  · intro i hi
    exact (fiber i).angle.second_unit
  · intro i hi
    simpa only [sub_zero] using (fiber i).reference.coefficient_lower hk
  · intro i hi
    have h := (fiber i).intermediate_close
    rw [hintermediate i hi] at h
    simpa only [zero_smul,add_zero] using h
  · intro i hi
    have h := (fiber i).reference_close
    rw [hpivot i hi] at h
    exact h
  · exact hsep

/-- Physical separation of the two observed points gives a longitudinal gap,
provided their transverse errors occupy at most one quarter of that separation. -/
theorem observed_distance_axis_gap {k : ℕ} (p q x v : Space k)
    {s t err r : ℝ} (hv : ‖v‖ = 1) (hsep : r ≤ dist p q)
    (hsmall : 4*err ≤ r)
    (hp : ‖p-(x+s • v)‖ ≤ err) (hq : ‖q-(x+t • v)‖ ≤ err) :
    r/2 ≤ |t-s| := by
  have hd := two_point_axis_displacement p q x v hp hq
  have ht := norm_add_le ((q-p)-(t-s) • v) ((t-s) • v)
  have hid : ((q-p)-(t-s) • v)+(t-s) • v = q-p := by abel
  rw [hid,norm_smul,Real.norm_eq_abs,hv,mul_one] at ht
  have hdist : r ≤ ‖q-p‖ := by simpa only [dist_eq_norm,norm_sub_rev] using hsep
  linarith

/-- A tube through two physically distant observed points lies in a small cap
about their observed displacement direction. This is the bush incidence geometry. -/
theorem distant_two_point_direction_bound {k : ℕ} (p q x v : Space k)
    {s t err r : ℝ} (hv : ‖v‖ = 1) (hr : 0 < r) (hsep : r ≤ dist p q)
    (hsmall : 4*err ≤ r)
    (hp : ‖p-(x+s • v)‖ ≤ err) (hq : ‖q-(x+t • v)‖ ≤ err) :
    projectiveDistance v (unitize (q-p)) ≤ 8*err/r := by
  have hgap := observed_distance_axis_gap p q x v hv hsep hsmall hp hq
  have h := two_point_direction_bound p q x v hv (by linarith : 0 < r/2) hgap hp hq
  convert h using 1; ring

/-- Actual geometric cap localization for the two-cell incidence relation of an
admissible tube family. No direction-separation assumption is needed here. -/
theorem two_cell_incidence_cap {k M : ℕ} (F : TubeFamily k M)
    {δ width r : ℝ} (hF : F.Admissible width δ) (hr : 0 < r)
    (hsmall : 4*(width*δ) ≤ r) (x y : Cell k)
    (hfar : r ≤ dist (cellCenter δ x) (cellCenter δ y)) (i : Fin M)
    (hx : x ∈ F.shade i) (hy : y ∈ F.shade i) :
    projectiveDistance (F.tube i).direction
      (unitize (cellCenter δ y-cellCenter δ x)) ≤ 8*(width*δ)/r := by
  obtain ⟨s,_,hs⟩ := hF i x hx
  obtain ⟨t,_,ht⟩ := hF i y hy
  exact distant_two_point_direction_bound (cellCenter δ x) (cellCenter δ y)
    (F.tube i).base (F.tube i).direction (F.tube i).unit_direction hr hfar hsmall hs ht

/-- The arbitrary-real-cap hypothesis bounds common incidences of two separated
shading cells. Both cap membership and the unit cap center are geometrically derived. -/
theorem two_cell_cap_multiplicity {k M : ℕ} (F : TubeFamily k M)
    {δ width r m A : ℝ} (hF : F.Admissible width δ) (hcap : F.CapBound δ m A)
    (hδ : 0 < δ) (hr : 0 < r) (hsmall : 4*(width*δ) ≤ r)
    (hcaplo : δ ≤ 8*(width*δ)/r) (hcaphi : 8*(width*δ)/r ≤ 1)
    (x y : Cell k) (hfar : r ≤ dist (cellCenter δ x) (cellCenter δ y)) :
    ((Finset.univ.filter fun i => x ∈ F.shade i ∧ y ∈ F.shade i).card:ℝ) ≤
      A*(8*width/r)^m := by
  classical
  have hxy : cellCenter δ y-cellCenter δ x ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    rw [heq,dist_self] at hfar
    linarith
  have hcenter := unitize_unit _ hxy
  have hcount := hcap (unitize (cellCenter δ y-cellCenter δ x)) hcenter
    (8*(width*δ)/r) hcaplo hcaphi
  have hsub : (Finset.univ.filter fun i => x ∈ F.shade i ∧ y ∈ F.shade i) ⊆
      Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction
        (unitize (cellCenter δ y-cellCenter δ x)) ≤ 8*(width*δ)/r) := by
    intro i hi
    obtain ⟨hx,hy⟩ := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,two_cell_incidence_cap F hF hr hsmall x y hfar i hx hy⟩
  have hcard : ((Finset.univ.filter fun i => x ∈ F.shade i ∧ y ∈ F.shade i).card:ℝ) ≤
      ((Finset.univ.filter fun i => projectiveDistance (F.tube i).direction
        (unitize (cellCenter δ y-cellCenter δ x)) ≤ 8*(width*δ)/r).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hid : (8*(width*δ)/r)/δ = 8*width/r := by field_simp
  rw [hid] at hcount
  exact hcard.trans hcount

end
end KakeyaFormal.PivotDirections

#print axioms KakeyaFormal.PivotDirections.distinct_fiber_second_direction_count
#print axioms KakeyaFormal.PivotDirections.two_cell_cap_multiplicity
