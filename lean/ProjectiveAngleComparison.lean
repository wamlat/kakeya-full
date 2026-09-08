import ProjectiveGeometry
import TubeGeometry

/-! Exact comparison of the implemented projective chord with the usual
unoriented angle. This also supplies the sine denominator in Gaussian projection. -/
namespace KakeyaFormal.ProjectiveAngleComparison
open scoped RealInnerProductSpace
noncomputable section

def angle {k : ℕ} (v w : Space k) : ℝ := Real.arccos |⟪v,w⟫|

theorem angle_nonneg {k : ℕ} (v w : Space k) : 0 ≤ angle v w := Real.arccos_nonneg _

theorem angle_le_half_pi {k : ℕ} (v w : Space k) : angle v w ≤ Real.pi/2 :=
  Real.arccos_le_pi_div_two.mpr (abs_nonneg _)

theorem cos_angle {k : ℕ} (v w : Space k) (hv : ‖v‖=1) (hw : ‖w‖=1) :
    Real.cos (angle v w)=|⟪v,w⟫| := by
  apply Real.cos_arccos (by linarith [abs_nonneg ⟪v,w⟫])
  simpa only [hv,hw,one_mul] using abs_real_inner_le_norm v w

theorem sin_angle_nonneg {k : ℕ} (v w : Space k) : 0 ≤ Real.sin (angle v w) :=
  Real.sin_nonneg_of_nonneg_of_le_pi (angle_nonneg v w)
    ((angle_le_half_pi v w).trans (by linarith [Real.pi_pos]))

/-- The implemented minimum of the antipodal chords is exactly 2 sin(psi/2). -/
theorem chord_eq_two_sin_half {k : ℕ} (v w : Space k) (hv : ‖v‖=1) (hw : ‖w‖=1) :
    projectiveDistance v w=2*Real.sin (angle v w/2) := by
  have hchord := ProjectiveGeometry.projective_chord_sq v w hv hw
  have hcos := cos_angle v w hv hw
  have hdouble := Real.cos_two_mul (angle v w/2)
  rw [show 2*(angle v w/2)=angle v w by ring,hcos] at hdouble
  have htrig := Real.sin_sq_add_cos_sq (angle v w/2)
  have hs : 0 ≤ Real.sin (angle v w/2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [angle_nonneg v w])
      (by linarith [angle_le_half_pi v w,Real.pi_pos])
  nlinarith [projectiveDistance_nonneg v w]

/-- Explicit uniform constants comparing both geometric conventions. -/
theorem chord_angle_bounds {k : ℕ} (v w : Space k) (hv : ‖v‖=1) (hw : ‖w‖=1) :
    (2/Real.pi)*angle v w ≤ projectiveDistance v w ∧ projectiveDistance v w ≤ angle v w := by
  rw [chord_eq_two_sin_half v w hv hw]
  have hh0 : 0 ≤ angle v w/2 := by linarith [angle_nonneg v w]
  have hh1 : angle v w/2 ≤ Real.pi/2 := by linarith [angle_le_half_pi v w,Real.pi_pos]
  constructor
  · have h := Real.mul_le_sin hh0 hh1
    nlinarith
  · have h := Real.sin_le hh0
    linarith

/-- The actual perpendicular component has norm sin(psi). Antipodal signs
disappear only after squaring the inner product, as required. -/
theorem transverse_eq_sin {k : ℕ} (v w : Space k) (hv : ‖v‖=1) (hw : ‖w‖=1) :
    ‖KakeyaAudit.TubeGeometry.transverse v w‖=Real.sin (angle v w) := by
  have ht := KakeyaAudit.TubeGeometry.transverse_norm_sq v w hv
  rw [hw,one_pow] at ht
  have hs := Real.sin_sq_add_cos_sq (angle v w)
  rw [cos_angle v w hv hw,sq_abs] at hs
  nlinarith [norm_nonneg (KakeyaAudit.TubeGeometry.transverse v w),sin_angle_nonneg v w]

/-- Replacing sin(psi) by psi in a collision denominator loses only a fixed
factor, uniformly over every nonzero projective angle. -/
theorem sine_angle_bounds {k : ℕ} (v w : Space k) :
    (2/Real.pi)*angle v w ≤ Real.sin (angle v w) ∧ Real.sin (angle v w) ≤ angle v w :=
  ⟨Real.mul_le_sin (angle_nonneg v w) (angle_le_half_pi v w),Real.sin_le (angle_nonneg v w)⟩

theorem sine_pos {k : ℕ} (v w : Space k) (hangle : 0 < angle v w) :
    0 < Real.sin (angle v w) :=
  (mul_pos (div_pos (by norm_num) Real.pi_pos) hangle).trans_le (sine_angle_bounds v w).1

/-- Every angular cap is an actual chord cap at the same radius, and every
chord cap is an angular cap after the explicit fixed enlargement pi/2. -/
theorem cap_comparison {k : ℕ} (v w : Space k) (hv : ‖v‖=1) (hw : ‖w‖=1) (r : ℝ) :
    (angle v w ≤ r → projectiveDistance v w ≤ r) ∧
      (projectiveDistance v w ≤ r → angle v w ≤ (Real.pi/2)*r) := by
  obtain ⟨hlo,hhi⟩ := chord_angle_bounds v w hv hw
  refine ⟨fun h => hhi.trans h,?_⟩
  intro h
  have hh := mul_le_mul_of_nonneg_left (hlo.trans h) (show 0 ≤ Real.pi/2 by positivity)
  have hid : (Real.pi/2)*((2/Real.pi)*angle v w)=angle v w := by
    field_simp
  rwa [hid] at hh

/-- Choose the actual sign of the second original direction with nonnegative
inner product. No choice of an unrelated direction is made. -/
theorem representative {k : ℕ} (v w : Space k) (hw : ‖w‖=1) :
    ∃ w' : Space k, (w'=w ∨ w'=-w) ∧ ‖w'‖=1 ∧ ⟪v,w'⟫=|⟪v,w⟫| := by
  by_cases hi : 0 ≤ ⟪v,w⟫
  · exact ⟨w,Or.inl rfl,hw,(abs_of_nonneg hi).symm⟩
  · refine ⟨-w,Or.inr rfl,by simpa using hw,?_⟩
    rw [inner_neg_right,abs_of_neg (lt_of_not_ge hi)]

/-- Literal orthogonal representation from the Gaussian projection proof:
the selected sign of the original second vector equals cos(psi)*v+sin(psi)*u,
where u is an actual unit vector orthogonal to the original v. -/
theorem orthogonal_decomposition {k : ℕ} (v w : Space k)
    (hv : ‖v‖=1) (hw : ‖w‖=1) (hangle : 0 < angle v w) :
    ∃ w' u : Space k, (w'=w ∨ w'=-w) ∧ ‖u‖=1 ∧ ⟪v,u⟫=0 ∧
      w'=Real.cos (angle v w) • v+Real.sin (angle v w) • u := by
  obtain ⟨w',hrep,hw',hi⟩ := representative v w hw
  have ha : angle v w'=angle v w := by simp only [angle,hi,abs_abs]
  have hs := sine_pos v w hangle
  let t := KakeyaAudit.TubeGeometry.transverse v w'
  have ht : ‖t‖=Real.sin (angle v w) := by
    simpa only [ha] using transverse_eq_sin v w' hv hw'
  let u := (Real.sin (angle v w))⁻¹ • t
  refine ⟨w',u,hrep,?_,?_,?_⟩
  · dsimp only [u]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),ht,inv_mul_cancel₀ hs.ne']
  · dsimp only [u,t]
    rw [inner_smul_right,KakeyaAudit.TubeGeometry.transverse_inner_zero v w' hv,mul_zero]
  · dsimp only [u]
    rw [smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
    dsimp only [t,KakeyaAudit.TubeGeometry.transverse]
    rw [hi,← cos_angle v w hv hw]
    abel

end
end KakeyaFormal.ProjectiveAngleComparison
