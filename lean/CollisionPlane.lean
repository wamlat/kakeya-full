import ThickCircle
import LegalSampleOutputs

/-! Actual collision geometry confines the second first-tube direction to the
plane of the original angle. This is a Euclidean implication, not a packing
assumption; the fixed great-circle packing theorem applies afterwards. -/
namespace KakeyaFormal.CollisionPlane
open EuclideanSplit HairbrushPlanes ThickCircle PivotDirections
noncomputable section

def normalCoordinate {k : ℕ} (f : Space (k+2) ≃ₗᵢ[ℝ] Space (k+2))
    (x : Space (k+2)) : Space k := normalTail (f x)

theorem normalCoordinate_norm_le {k : ℕ} (f : Space (k+2) ≃ₗᵢ[ℝ] Space (k+2))
    (x : Space (k+2)) : ‖normalCoordinate f x‖ ≤ ‖x‖ := by
  exact ((tail_norm_le (tail (f x))).trans (tail_norm_le (f x))).trans_eq (f.norm_map x)

/-- Aligning the normalized transverse vector kills the actual vector's
remaining normal coordinates, including a zero transverse vector. -/
theorem unitize_normal_zero {k : ℕ} (x : Space (k+1)) :
    transverseCoordinate (alignStem (unitize x)) x = 0 := by
  by_cases hx : x=0
  · subst x
    exact transverseCoordinate_zero _
  · have hu := unitize_unit x hx
    have heq : x = ‖x‖ • unitize x := (norm_smul_unitize x).symm
    conv_lhs => arg 2; rw [heq]
    rw [transverseCoordinate_smul]
    have hz : transverseCoordinate (alignStem (unitize x)) (unitize x) = 0 := by
      simp only [transverseCoordinate,alignStem_apply _ hu,axisUnit,tail_cons]
    rw [hz,smul_zero]

def frame {k : ℕ} (u v : Space (k+2)) : Space (k+2) ≃ₗᵢ[ℝ] Space (k+2) :=
  straightenPlane (alignStem u) (unitize (transverseCoordinate (alignStem u) v))

theorem frame_first_zero {k : ℕ} (u v : Space (k+2)) (hu : ‖u‖=1) :
    normalCoordinate (frame u v) u = 0 := by
  rw [normalCoordinate,frame,normalTail_straightenPlane]
  have hz : transverseCoordinate (alignStem u) u = 0 := by
    simp only [transverseCoordinate,alignStem_apply u hu,axisUnit,tail_cons]
  rw [hz,transverseCoordinate_zero]

theorem frame_second_zero {k : ℕ} (u v : Space (k+2)) :
    normalCoordinate (frame u v) v = 0 := by
  rw [normalCoordinate,frame,normalTail_straightenPlane]
  exact unitize_normal_zero _

/-- Three actual point/axis incidences force the competing direction into
the plane, with only one inverse longitudinal-separation factor. -/
theorem direction_normal_bound {k : ℕ}
    (f : Space (k+2) ≃ₗᵢ[ℝ] Space (k+2)) (x xp q u v w : Space (k+2))
    {a s t err kappa : ℝ} (hfu : normalCoordinate f u=0) (hfv : normalCoordinate f v=0)
    (hkappa : 0 < kappa) (ht : kappa ≤ |t|)
    (hfirst : dist q (x+a • u) ≤ err)
    (hsecond : dist xp (x+s • v) ≤ err)
    (hother : dist q (xp+t • w) ≤ err) :
    ‖normalCoordinate f w‖ ≤ 3*err/kappa := by
  have hid : normalCoordinate f (t • w) =
      normalCoordinate f (q-(x+a • u))-normalCoordinate f (xp-(x+s • v))-
        normalCoordinate f (q-(xp+t • w)) := by
    have hlin : t • w = (q-(x+a • u))-(xp-(x+s • v))-(q-(xp+t • w))+a • u-s • v := by module
    conv_lhs => arg 2; rw [hlin]
    simp only [normalCoordinate,normalTail,map_sub,map_add,map_smul,tail_sub,tail_add,tail_smul] at hfu hfv ⊢
    simp only [hfu,hfv,smul_zero,add_zero,sub_zero]
  have h1 := (normalCoordinate_norm_le f (q-(x+a • u))).trans (by simpa only [dist_eq_norm] using hfirst)
  have h2 := (normalCoordinate_norm_le f (xp-(x+s • v))).trans (by simpa only [dist_eq_norm] using hsecond)
  have h3 := (normalCoordinate_norm_le f (q-(xp+t • w))).trans (by simpa only [dist_eq_norm] using hother)
  have hbound : ‖normalCoordinate f (t • w)‖ ≤ 3*err := by
    rw [hid]
    have hh := norm_sub_le (normalCoordinate f (q-(x+a • u))-normalCoordinate f (xp-(x+s • v)))
      (normalCoordinate f (q-(xp+t • w)))
    have hh' := norm_sub_le (normalCoordinate f (q-(x+a • u))) (normalCoordinate f (xp-(x+s • v)))
    linarith
  have hsmul : normalCoordinate f (t • w) = t • normalCoordinate f w := by
    simp only [normalCoordinate,normalTail,map_smul,tail_smul]
  rw [hsmul,norm_smul,Real.norm_eq_abs] at hbound
  apply (le_div_iff₀ hkappa).mpr
  have hm := mul_le_mul_of_nonneg_right ht (norm_nonneg (normalCoordinate f w))
  linarith

open Finset LegalAngleSamples LegalAngleNormalization LegalLabeledSamples LegalSampleOutputs TransverseAngles
open Classical

/-- A valid output preserves its original intermediate label exactly. -/
theorem output_intermediate {k M : ℕ} {F : TubeFamily k M} {H : Finset (Cell k)}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hkappa : 0 < kappa) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) (p : Triple k) (hp : p ∈ S.samples a) :
    (output S a hkappa hwidth hadm p).2 = p.1 := by
  rw [output_encode S a hkappa hwidth hadm ⟨p,hp⟩]
  rfl

/-- Shared outputs and a shared original second tube give the actual thin
plane conclusion used in the collision shells. The common intermediate cell
and all three axis errors are derived from the original shadings. -/
theorem colliding_angle_thin {k M : ℕ} {F : TubeFamily (k+2) M} {H : Finset (Cell (k+2))}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (a b : ↥(angles F H kappa)) (hkappa : 0 < kappa) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) (p q : Triple (k+2))
    (hp : p ∈ S.samples a) (hq : q ∈ S.samples b)
    (hsecond : a.val.2.2=b.val.2.2)
    (hout : output S a hkappa hwidth hadm p=output S b hkappa hwidth hadm q) :
    ‖normalCoordinate (frame (F.tube a.val.2.1).direction (F.tube a.val.2.2).direction)
      (F.tube b.val.2.1).direction‖ ≤ (6*width/kappa)*δ := by
  have hint : p.1=q.1 := by
    have hh := congrArg Prod.snd hout
    simpa only [output_intermediate S a hkappa hwidth hadm p hp,
      output_intermediate S b hkappa hwidth hadm q hq] using hh
  have ha := S.legal a p hp
  have hb := S.legal b q hq
  obtain ⟨_,hva1,hva2,_⟩ := angle_geometry F H hkappa hadm a.val a.property
  obtain ⟨_,hvb1,hvb2,_⟩ := angle_geometry F H hkappa hadm b.val b.property
  have hfirst := (LegalTubeSamples.shifted_tube_projection (F.tube a.val.2.1)
    (cellCenter δ a.val.1) (cellCenter δ p.1) hva1 (hadm _ _ ha.1)).1
  have hsecond' := (LegalTubeSamples.shifted_tube_projection (F.tube a.val.2.2)
    (cellCenter δ a.val.1) (cellCenter δ b.val.1) hva2 (by simpa only [hsecond] using hvb2)).1
  have hother := (LegalTubeSamples.shifted_tube_projection (F.tube b.val.2.1)
    (cellCenter δ b.val.1) (cellCenter δ q.1) hvb1 (hadm _ _ hb.1)).1
  have ht : kappa ≤ |firstCoordinate F δ b.val q.1| := by
    rcases S.sign_valid b with hs | hs
    · have hh : kappa ≤ firstCoordinate F δ b.val q.1 := by simpa only [hs,one_mul] using hb.2.2.2.1
      exact hh.trans (le_abs_self _)
    · have hh : kappa ≤ -firstCoordinate F δ b.val q.1 := by simpa only [hs,neg_one_mul] using hb.2.2.2.1
      exact hh.trans (neg_le_abs _)
  rw [hint] at hfirst
  have hh := direction_normal_bound
    (frame (F.tube a.val.2.1).direction (F.tube a.val.2.2).direction)
    (cellCenter δ a.val.1) (cellCenter δ b.val.1) (cellCenter δ q.1)
    (F.tube a.val.2.1).direction (F.tube a.val.2.2).direction (F.tube b.val.2.1).direction
    (frame_first_zero _ _ (F.tube a.val.2.1).unit_direction) (frame_second_zero _ _) hkappa ht
    hfirst hsecond' hother
  convert hh using 1; ring

def firstIndices {k M : ℕ} {F : TubeFamily (k+2) M} {H : Finset (Cell (k+2))}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hkappa : 0 < kappa) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) : Finset (Fin M) :=
  (univ.filter (fun b : ↥(angles F H kappa) => b.val.2.2=a.val.2.2 ∧
    ∃ p ∈ S.samples a, ∃ q ∈ S.samples b,
      output S a hkappa hwidth hadm p=output S b hkappa hwidth hadm q)).image (fun b => b.val.2.1)

/-- The actual possible first-tube indices in a collision cap satisfy the
great-circle count. Their thinness is derived from shared outputs above. -/
theorem collision_cap_count {k M : ℕ} {F : TubeFamily (k+2) M} {H : Finset (Cell (k+2))}
    {δ lam kappa width psi : ℝ} (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hδ : 0 < δ) (hpsi : δ ≤ psi)
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ)
    (hsep : F.Separated δ) (hsmall : (6*width/kappa)*δ ≤ 1/2) :
    (((firstIndices S a hkappa hwidth hadm).filter
      (fun i => projectiveDistance (F.tube i).direction (F.tube a.val.2.1).direction ≤ psi)).card:ℝ) ≤
      circleConstant k (6*width/kappa)*(psi/δ) := by
  let f := frame (F.tube a.val.2.1).direction (F.tube a.val.2.2).direction
  apply indexed_thick_circle_count _ (fun i => f (F.tube i).direction) (f (F.tube a.val.2.1).direction)
    hδ hpsi (by positivity : 0 ≤ 6*width/kappa) hsmall
  · intro i _
    rw [f.norm_map,(F.tube i).unit_direction]
  · intro i hi
    rw [isometry_projective]
    exact (mem_filter.mp hi).2
  · intro i hi
    obtain ⟨b,hb,rfl⟩ := mem_image.mp (mem_filter.mp hi).1
    obtain ⟨_,hsecond,p,hp,q,hq,hout⟩ := mem_filter.mp hb
    exact colliding_angle_thin S a b hkappa hwidth hadm p q hp hq hsecond.symm hout
  · intro i _ j _ hij
    rw [isometry_projective]
    exact hsep i j hij

/-- The explicit thick-circle constant has exactly one inverse-kappa factor
per normal coordinate. The tangential cap radius is counted separately. -/
theorem circleConstant_div_le (k : ℕ) {w kappa : ℝ}
    (hw : 0 ≤ w) (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1) :
    circleConstant k (w/kappa) ≤ circleConstant k w/kappa^k := by
  let Q := ProjectiveGeometry.chartConstant (k+1) (1/2)
  have hQ : 0 < Q := ProjectiveGeometry.chartConstant_pos (k+1) (by norm_num)
  have hbase : 4*Q*(w/kappa)+5 ≤ (4*Q*w+5)/kappa := by
    apply (le_div_iff₀ hkappa).mpr
    have hid : (4*Q*(w/kappa)+5)*kappa = 4*Q*w+5*kappa := by field_simp
    rw [hid]
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 4*Q*(w/kappa)+5) hbase k
  rw [div_pow] at hpow
  have hh := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 4*(4*Q+5))
  unfold circleConstant
  convert hh using 1 <;> first | rfl | ring

/-- One dyadic collision shell has the actual ambient bound in (5.17).
The possible directions are aggregated over every shared output with the fixed
angle, so no output-count factor is hidden in this direction count. -/
theorem collision_shell_count {k M : ℕ} {F : TubeFamily (k+2) M} {H : Finset (Cell (k+2))}
    {δ lam kappa width phi : ℝ} (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hδ : 0 < δ) (hphi : δ ≤ phi)
    (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) (hsep : F.Separated δ)
    (hsmall : (6*width/kappa)*δ ≤ 1/2) :
    (((firstIndices S a hkappa hwidth hadm).filter
      (fun i => phi ≤ projectiveDistance (F.tube i).direction (F.tube a.val.2.1).direction ∧
        projectiveDistance (F.tube i).direction (F.tube a.val.2.1).direction ≤ 2*phi)).card:ℝ) ≤
      (2*circleConstant k (6*width))*phi/(kappa^k*δ) := by
  have hphi0 := hδ.trans_le hphi
  have hsub : (firstIndices S a hkappa hwidth hadm).filter
      (fun i => phi ≤ projectiveDistance (F.tube i).direction (F.tube a.val.2.1).direction ∧
        projectiveDistance (F.tube i).direction (F.tube a.val.2.1).direction ≤ 2*phi) ⊆
      (firstIndices S a hkappa hwidth hadm).filter
      (fun i => projectiveDistance (F.tube i).direction (F.tube a.val.2.1).direction ≤ 2*phi) := by
    intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).1,(mem_filter.mp hi).2.2⟩
  have hcard : (((firstIndices S a hkappa hwidth hadm).filter
      (fun i => phi ≤ projectiveDistance (F.tube i).direction (F.tube a.val.2.1).direction ∧
        projectiveDistance (F.tube i).direction (F.tube a.val.2.1).direction ≤ 2*phi)).card:ℝ) ≤
      circleConstant k (6*width/kappa)*(2*phi/δ) :=
    (Nat.cast_le.mpr (card_le_card hsub)).trans
      (collision_cap_count S a hδ (by linarith : δ ≤ 2*phi) hkappa hwidth hadm hsep hsmall)
  have hc := circleConstant_div_le k (by positivity : 0 ≤ 6*width) hkappa hkappa1
  have hh := hcard.trans (mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 2*phi/δ))
  convert hh using 1 <;> first | rfl | ring

end
end KakeyaFormal.CollisionPlane
