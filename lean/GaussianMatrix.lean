import Configurations
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-! Actual standard Gaussian matrices and their action on orthogonal vectors.
The sample space is the Euclidean space of all matrix entries; its standard
Gaussian law is the product law of the original independent real entries. -/
namespace KakeyaFormal.GaussianMatrix
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
noncomputable section

abbrev Sample (rows cols : ℕ) := EuclideanSpace ℝ (Fin rows × Fin cols)

def law (rows cols : ℕ) : Measure (Sample rows cols) := stdGaussian (Sample rows cols)

instance probability_law (rows cols : ℕ) : IsProbabilityMeasure (law rows cols) := by
  unfold law
  infer_instance

def matrix {rows cols : ℕ} (ω : Sample rows cols) : Matrix (Fin rows) (Fin cols) ℝ :=
  fun i j => ω (i,j)

/-- All ORIGINAL matrix entries have the independent product of N(0,1) laws. -/
theorem entries_law (rows cols : ℕ) :
    (law rows cols).map (fun ω ij => matrix ω ij.1 ij.2)=
      Measure.pi (fun _ : Fin rows × Fin cols => gaussianReal 0 1) := by
  rw [law,← map_pi_eq_stdGaussian,Measure.map_map (by unfold matrix; fun_prop) (by fun_prop)]
  change (Measure.pi (fun _ : Fin rows × Fin cols => gaussianReal 0 1)).map id = _
  exact Measure.map_id

def projectionLinear {rows cols : ℕ} (v : Space cols) : Sample rows cols →ₗ[ℝ] Space rows where
  toFun := fun ω => WithLp.toLp 2 (fun i => ∑ j, ω (i,j)*v j)
  map_add' := by
    intro a b
    ext i
    simp [Finset.sum_add_distrib,add_mul]
  map_smul' := by
    intro a b
    ext i
    simp [Finset.mul_sum,mul_assoc]

def projection {rows cols : ℕ} (v : Space cols) : Sample rows cols →L[ℝ] Space rows :=
  (projectionLinear v).toContinuousLinearMap

theorem projection_apply {rows cols : ℕ} (v : Space cols) (ω : Sample rows cols) (i : Fin rows) :
    projection v ω i=∑ j, matrix ω i j*v j := rfl

def tensor {rows cols : ℕ} (x : Space rows) (v : Space cols) : Sample rows cols :=
  WithLp.toLp 2 (fun ij => x ij.1*v ij.2)

/-- Exact tensor-dual formula for the actual row-by-column matrix action. -/
theorem projection_inner {rows cols : ℕ} (v : Space cols) (ω : Sample rows cols) (x : Space rows) :
    ⟪x,projection v ω⟫=⟪tensor x v,ω⟫ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change (∑ i, (∑ j, ω (i,j)*v j)*x i) = ∑ ij, ω ij*(x ij.1*v ij.2)
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tensor_inner {rows cols : ℕ} (x y : Space rows) (v w : Space cols) :
    ⟪tensor x v,tensor y w⟫=⟪x,y⟫*⟪v,w⟫ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change (∑ ij : Fin rows × Fin cols, (y ij.1*w ij.2)*(x ij.1*v ij.2))=
    (∑ i, y i*x i)*(∑ j, w j*v j)
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Covariance of arbitrary output linear observations is computed exactly
from the original input inner product. -/
theorem output_covariance {rows cols : ℕ} (v w : Space cols) (x y : Space rows) :
    cov[fun ω : Sample rows cols => ⟪x,projection v ω⟫,
      fun ω : Sample rows cols => ⟪y,projection w ω⟫; law rows cols]=⟪x,y⟫*⟪v,w⟫ := by
  simp_rw [projection_inner]
  rw [← covarianceBilin_apply_eq_cov (by unfold law; exact IsGaussian.memLp_two_id),law,
    covarianceBilin_stdGaussian,innerSL_apply_apply,tensor_inner]

/-- The pair is genuinely jointly Gaussian as a linear image of the actual
standard Gaussian matrix, not merely two marginally Gaussian vectors. -/
theorem jointly_gaussian {rows cols : ℕ} (v w : Space cols) :
    HasGaussianLaw (fun ω : Sample rows cols => (projection v ω,projection w ω)) (law rows cols) := by
  have h : HasGaussianLaw id (law rows cols) := by
    unfold law
    exact IsGaussian.hasGaussianLaw_id
  exact h.map_fun ((projection v).prod (projection w))

/-- Orthogonal original vectors give independent actual projected vectors. -/
theorem orthogonal_independent {rows cols : ℕ} (v w : Space cols) (horth : ⟪v,w⟫=0) :
    IndepFun (projection (rows := rows) v) (projection w) (law rows cols) := by
  apply (jointly_gaussian v w).indepFun_of_covariance_inner
  intro x y
  rw [output_covariance,horth,mul_zero]

/-- Every unit original vector has the standard Gaussian output law in the
actual target dimension. Its mean and variance are derived, not supplied. -/
theorem unit_image_law {rows cols : ℕ} (v : Space cols) (hv : ‖v‖=1) :
    (law rows cols).map (projection v)=stdGaussian (Space rows) := by
  have hg := (jointly_gaussian (rows := rows) v v).fst
  apply Measure.ext_of_charFun
  ext x
  have hmean : (∫ ω : Sample rows cols, ⟪x,projection v ω⟫ ∂law rows cols)=0 := by
    simp_rw [projection_inner]
    change (∫ ω : Sample rows cols, (innerSL ℝ (tensor x v)) ω ∂stdGaussian (Sample rows cols))=0
    exact integral_strongDual_stdGaussian _
  have hvar : Var[fun ω : Sample rows cols => ⟪x,projection v ω⟫; law rows cols]=‖x‖^2 := by
    rw [← covariance_self,output_covariance,real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq,hv,one_pow,mul_one]
    fun_prop
  rw [hg.charFun_map_eq x,hmean,hvar,charFun_stdGaussian]
  simp [neg_div]

/-- The exact orthogonal-pair conclusion needed in the 5-by-7 projection
argument; both vectors refer to the same original random matrix. -/
theorem orthogonal_unit_pair (v w : Space 7) (hv : ‖v‖=1) (hw : ‖w‖=1) (horth : ⟪v,w⟫=0) :
    (law 5 7).map (projection v)=stdGaussian (Space 5) ∧
      (law 5 7).map (projection w)=stdGaussian (Space 5) ∧
      IndepFun (projection (rows := 5) v) (projection w) (law 5 7) :=
  ⟨unit_image_law v hv,unit_image_law w hw,orthogonal_independent v w horth⟩

/-- The exact joint distribution identifies both vectors with a product of
independent target-dimensional standard Gaussians on the SAME sample space. -/
theorem orthogonal_joint_law {rows cols : ℕ} (v w : Space cols)
    (hv : ‖v‖=1) (hw : ‖w‖=1) (horth : ⟪v,w⟫=0) :
    (law rows cols).map (fun ω => (projection v ω,projection w ω))=
      (stdGaussian (Space rows)).prod (stdGaussian (Space rows)) := by
  rw [(orthogonal_independent v w horth).map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
    unit_image_law v hv,unit_image_law w hw]

end
end KakeyaFormal.GaussianMatrix
