import GaussianSmallBall
import SpatialAngular

/-! Actual fixed-frame perpendicular Gaussian laws. This supplies the
four-dimensional section estimate used after fixing the first projected
vector; no conditioning on an operator-norm event is asserted. -/
namespace KakeyaFormal.GaussianPerpendicular
open MeasureTheory ProbabilityTheory EuclideanSplit SpatialAngular
open scoped ENNReal BigOperators RealInnerProductSpace
noncomputable section

/-- A concrete linear coisometry sends the standard Gaussian to the standard
Gaussian on its target. The adjoint norm identity is genuine linear geometry. -/
theorem coisometry_law {m n : ℕ} (L : Space m →L[ℝ] Space n)
    (hL : ∀ x, ‖L.adjoint x‖=‖x‖) :
    (stdGaussian (Space m)).map L=stdGaussian (Space n) := by
  have hgauss : HasGaussianLaw L (stdGaussian (Space m)) :=
    (IsGaussian.hasGaussianLaw_id (μ := stdGaussian (Space m))).map_fun L
  apply Measure.ext_of_charFun
  ext x
  have hmean : (∫ y : Space m, ⟪x,L y⟫ ∂stdGaussian (Space m))=0 := by
    simp_rw [← ContinuousLinearMap.adjoint_inner_left]
    exact integral_strongDual_stdGaussian (innerSL ℝ (L.adjoint x))
  have hvar : Var[fun y : Space m => ⟪x,L y⟫; stdGaussian (Space m)]=‖x‖^2 := by
    simp_rw [← ContinuousLinearMap.adjoint_inner_left]
    rw [← covarianceBilin_self IsGaussian.memLp_two_id,covarianceBilin_stdGaussian,
      innerSL_apply_apply,real_inner_self_eq_norm_sq,hL]
  rw [hgauss.charFun_map_eq x,hmean,hvar,charFun_stdGaussian]
  simp [neg_div]

def tailLinear (n : ℕ) : Space (n+1) →ₗ[ℝ] Space n where
  toFun := tail
  map_add' := tail_add
  map_smul' := by intro c x; exact tail_smul c x

def tailCLM (n : ℕ) : Space (n+1) →L[ℝ] Space n := (tailLinear n).toContinuousLinearMap

theorem tail_adjoint (n : ℕ) (x : Space n) : (tailCLM n).adjoint x=cons 0 x := by
  apply ext_inner_right ℝ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change (∑ i : Fin n, y i.succ*x i)=∑ i : Fin (n+1), y i*(Fin.cases 0 (WithLp.ofLp x) i)
  rw [Fin.sum_univ_succ]
  simp

theorem tail_law (n : ℕ) :
    (stdGaussian (Space (n+1))).map (tailCLM n)=stdGaussian (Space n) :=
  coisometry_law _ (fun x => by rw [tail_adjoint,norm_cons_zero])

/-- For every fixed unit direction u in five dimensions, the actual four
transverse coordinates of a fresh standard Gaussian are standard Gaussian4.
The law also holds for nonunit u because alignStem always is an isometry. -/
theorem transverse_law (n : ℕ) (u : Space (n+1)) :
    (stdGaussian (Space (n+1))).map (transverse u)=stdGaussian (Space n) := by
  have he : transverse u=(tailCLM n) ∘ (alignStem u) := rfl
  rw [he,← Measure.map_map (by fun_prop) (by fun_prop),stdGaussian_map,tail_law]

/-- A uniform section bound at EVERY fixed first-vector direction, in the
actual codimension one. It uses no bounded-norm conditioning assumption. -/
theorem transverse_small_ball (n : ℕ) (u : Space (n+1)) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space (n+1)) {y | ‖transverse u y‖ ≤ r} ≤
      min 1 (ENNReal.ofReal ((2*r)^n)) := by
  have hm : Measurable (transverse u) := by
    change Measurable ((tailCLM n) ∘ (alignStem u))
    fun_prop
  have hh := GaussianSmallBall.closedBall_min_bound n hr
  rw [← transverse_law n u,Measure.map_apply hm Metric.isClosed_closedBall.measurableSet] at hh
  simpa only [Set.preimage_ofPred_eq,Metric.closedBall,dist_zero_right] using hh

theorem head_align {n : ℕ} (u y : Space (n+1)) (hu : ‖u‖=1) :
    head (alignStem u y)=⟪u,y⟫ := by
  have hh := (alignStem u).inner_map_map u y
  rw [alignStem_apply u hu] at hh
  have he (z : Space (n+1)) : ⟪axisUnit n,z⟫=head z := by
    simp [axisUnit,PiLp.inner_apply,RCLike.inner_apply,cons,head,Fin.sum_univ_succ]
  rwa [he] at hh

/-- The coordinates measure the actual orthogonal component, rather than an
uninterpreted four-dimensional linear image. -/
theorem transverse_norm_eq {n : ℕ} (u y : Space (n+1)) (hu : ‖u‖=1) :
    ‖transverse u y‖=‖y-⟪u,y⟫ • u‖ := by
  have he : alignStem u (y-⟪u,y⟫ • u)=cons 0 (transverse u y) := by
    rw [← cons_head_tail (alignStem u (y-⟪u,y⟫ • u))]
    congr 1
    · simp [map_sub,map_smul,head_sub,head_smul,alignStem_apply u hu,axisUnit,head_align u y hu]
    · simp [map_sub,map_smul,tail_sub,tail_smul,alignStem_apply u hu,axisUnit,transverse]
  calc
    _ = ‖cons 0 (transverse u y)‖ := (norm_cons_zero _).symm
    _ = ‖alignStem u (y-⟪u,y⟫ • u)‖ := congrArg norm he.symm
    _ = _ := (alignStem u).norm_map _

/-- The literal four-dimensional power, uniform in the fixed first-vector
frame, is the probabilistic small-ball ingredient in source (2.3). -/
theorem four_dimensional_section (u : Space 5) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space 5) {y | ‖transverse u y‖ ≤ r} ≤
      min 1 (ENNReal.ofReal (16*r^4)) := by
  have hh := transverse_small_ball 4 u hr
  simpa only [show (2*r)^4=16*r^4 by ring] using hh

/-- The literal intrinsic perpendicular norm formulation for each fixed
unit first-vector direction. -/
theorem orthogonal_component_small_ball (u : Space 5) (hu : ‖u‖=1) {r : ℝ} (hr : 0 ≤ r) :
    stdGaussian (Space 5) {y | ‖y-⟪u,y⟫ • u‖ ≤ r} ≤
      min 1 (ENNReal.ofReal (16*r^4)) := by
  simpa only [transverse_norm_eq u _ hu] using four_dimensional_section u hr

end
end KakeyaFormal.GaussianPerpendicular
