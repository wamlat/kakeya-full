import GaussianConditioning
import ProjectiveAngleComparison

/-! Deterministic containment behind the Gaussian projection collision bound.
All maps here are actual continuous linear maps and all angles are the literal
unoriented angles of normalized output vectors. -/
namespace KakeyaFormal.GaussianCollisionGeometry
open GaussianConditioning ProjectiveAngleComparison
open scoped RealInnerProductSpace
noncomputable section

theorem smul_unitDirection {n : ℕ} (x : Space (n+1)) : ‖x‖ • unitDirection x=x := by
  by_cases hx : x=0
  · simp [hx]
  · simp [unitDirection,hx,smul_smul]

theorem unitDirection_neg {n : ℕ} (x : Space (n+1)) (hx : x≠0) :
    unitDirection (-x)=-unitDirection x := by
  simp [unitDirection,hx,neg_ne_zero.mpr hx]

theorem inner_unitDirection {n : ℕ} (x : Space (n+1)) : ⟪unitDirection x,x⟫=‖x‖ := by
  conv_lhs => rhs; rw [← smul_unitDirection x]
  rw [inner_smul_right,real_inner_self_eq_norm_sq,unitDirection_norm]
  ring

theorem perpendicular_self {n : ℕ} (x : Space (n+1)) : perpendicular x x=0 := by
  rw [perpendicular,inner_unitDirection,smul_unitDirection,sub_self]

theorem perpendicular_add_smul {n : ℕ} (x y : Space (n+1)) (a b : ℝ) :
    perpendicular x (a • x+b • y)=b • perpendicular x y := by
  unfold perpendicular
  rw [inner_add_right,inner_smul_right,inner_smul_right,inner_unitDirection]
  rw [add_smul,mul_smul,smul_unitDirection,mul_smul]
  module

/-- Orthogonal distance is bounded by output length times the actual output
angle; zero second vectors are covered by the exact reconstruction identity. -/
theorem perpendicular_angle_bound {n : ℕ} (x y : Space (n+1)) :
    ‖perpendicular x y‖ ≤ ‖y‖*angle (unitDirection x) (unitDirection y) := by
  have he : perpendicular x y=‖y‖ •
      KakeyaAudit.TubeGeometry.transverse (unitDirection x) (unitDirection y) := by
    conv_lhs => rw [← smul_unitDirection y]
    simp only [perpendicular,KakeyaAudit.TubeGeometry.transverse,inner_smul_right]
    module
  rw [he,norm_smul,Real.norm_of_nonneg (norm_nonneg y),
    transverse_eq_sin _ _ (unitDirection_norm x) (unitDirection_norm y)]
  exact mul_le_mul_of_nonneg_left (sine_angle_bounds _ _).2 (norm_nonneg y)

theorem angle_unitDirection_neg_right {n : ℕ} (x y : Space (n+1)) (hy : y≠0) :
    angle (unitDirection x) (unitDirection (-y))=
      angle (unitDirection x) (unitDirection y) := by
  rw [unitDirection_neg y hy]
  simp only [angle,inner_neg_right,abs_neg]

/-- One fixed original orthogonal decomposition, valid for every later map P.
Consequently the independent Gaussian pair does not depend on the sample. -/
theorem collision_containment {n cols : ℕ} (v w : Space cols)
    (hv : ‖v‖=1) (hw : ‖w‖=1) (hangle : 0 < angle v w) :
    ∃ u : Space cols, ‖u‖=1 ∧ ⟪v,u⟫=0 ∧
      ∀ (P : Space cols →L[ℝ] Space (n+1)) {K δ : ℝ},
        0 ≤ δ → ‖P‖ ≤ K → P w≠0 →
        angle (unitDirection (P v)) (unitDirection (P w)) ≤ δ →
        ‖perpendicular (P v) (P u)‖ ≤ K*δ/Real.sin (angle v w) := by
  obtain ⟨w',u,hrep,hu,huorth,hdecomp⟩ := orthogonal_decomposition v w hv hw hangle
  refine ⟨u,hu,huorth,?_⟩
  intro P K δ _hδ hK hwout hcoll
  have hK0 : 0 ≤ K := (norm_nonneg P).trans hK
  have hw' : ‖w'‖=1 := by rcases hrep with rfl | rfl <;> simpa using hw
  have hz : ‖P w'‖ ≤ K := by
    have h := P.le_opNorm w'
    rw [hw',mul_one] at h
    exact h.trans hK
  have hc : angle (unitDirection (P v)) (unitDirection (P w')) ≤ δ := by
    rcases hrep with rfl | rfl
    · exact hcoll
    · simpa only [map_neg,angle_unitDirection_neg_right _ _ hwout] using hcoll
  have hp : ‖perpendicular (P v) (P w')‖ ≤ K*δ :=
    (perpendicular_angle_bound _ _).trans
      (mul_le_mul hz hc (angle_nonneg _ _) hK0)
  have he : perpendicular (P v) (P w')=
      Real.sin (angle v w) • perpendicular (P v) (P u) := by
    rw [hdecomp,map_add,map_smul,map_smul,perpendicular_add_smul]
  have hs := sine_pos v w hangle
  rw [he,norm_smul,Real.norm_of_nonneg hs.le] at hp
  exact (le_div_iff₀ hs).mpr (by simpa [mul_comm] using hp)

end
end KakeyaFormal.GaussianCollisionGeometry
