import Configurations
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Actual orthogonal coordinate splitting and stem normalization

Coordinates are genuine Euclidean coordinates. Head/tail norm identities prove
that the transverse map is a contraction and that its zero-head inverse is an
isometric embedding; no abstract projection estimate is assumed.
-/
namespace KakeyaFormal.EuclideanSplit

noncomputable section

def head {k : ℕ} (x : Space (k+1)) : ℝ := WithLp.ofLp x 0

def tail {k : ℕ} (x : Space (k+1)) : Space k :=
  WithLp.toLp 2 (fun i => WithLp.ofLp x i.succ)

def cons {k : ℕ} (a : ℝ) (x : Space k) : Space (k+1) :=
  WithLp.toLp 2 (Fin.cases a (WithLp.ofLp x))

@[simp] theorem head_cons {k : ℕ} (a : ℝ) (x : Space k) : head (cons a x) = a := rfl
@[simp] theorem tail_cons {k : ℕ} (a : ℝ) (x : Space k) : tail (cons a x) = x := by ext i; rfl
@[simp] theorem cons_head_tail {k : ℕ} (x : Space (k+1)) : cons (head x) (tail x) = x := by
  ext i
  cases i using Fin.cases <;> rfl

@[simp] theorem tail_add {k : ℕ} (x y : Space (k+1)) : tail (x+y) = tail x+tail y := by ext i; rfl
@[simp] theorem tail_sub {k : ℕ} (x y : Space (k+1)) : tail (x-y) = tail x-tail y := by ext i; rfl
@[simp] theorem tail_smul {k : ℕ} (a : ℝ) (x : Space (k+1)) : tail (a • x) = a • tail x := by ext i; rfl
@[simp] theorem tail_zero {k : ℕ} : tail (0 : Space (k+1)) = 0 := by ext i; rfl
@[simp] theorem tail_neg {k : ℕ} (x : Space (k+1)) : tail (-x) = -tail x := by ext i; rfl
@[simp] theorem head_add {k : ℕ} (x y : Space (k+1)) : head (x+y) = head x+head y := rfl
@[simp] theorem head_sub {k : ℕ} (x y : Space (k+1)) : head (x-y) = head x-head y := rfl
@[simp] theorem head_smul {k : ℕ} (a : ℝ) (x : Space (k+1)) : head (a • x) = a*head x := rfl
@[simp] theorem head_zero {k : ℕ} : head (0 : Space (k+1)) = 0 := rfl

@[simp] theorem cons_add {k : ℕ} (a b : ℝ) (x y : Space k) :
    cons (a+b) (x+y) = cons a x+cons b y := by
  ext i
  cases i using Fin.cases <;> rfl

@[simp] theorem cons_smul {k : ℕ} (a b : ℝ) (x : Space k) :
    cons (a*b) (a • x) = a • cons b x := by
  ext i
  cases i using Fin.cases <;> rfl

@[simp] theorem cons_zero {k : ℕ} : cons 0 (0 : Space k) = 0 := by
  ext i
  cases i using Fin.cases <;> rfl

/-- Pythagoras for the actual head/tail splitting. -/
theorem norm_sq_split {k : ℕ} (x : Space (k+1)) :
    ‖x‖^2 = head x^2+‖tail x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_succ]
  rfl

/-- Removing the stem coordinate is a contraction. -/
theorem tail_norm_le {k : ℕ} (x : Space (k+1)) : ‖tail x‖ ≤ ‖x‖ := by
  have h := norm_sq_split x
  nlinarith [sq_nonneg (head x),norm_nonneg (tail x),norm_nonneg x]

/-- Adding a zero stem coordinate is an actual isometric embedding. -/
@[simp] theorem norm_cons_zero {k : ℕ} (x : Space k) : ‖cons 0 x‖ = ‖x‖ := by
  have h := norm_sq_split (cons 0 x)
  simp only [head_cons,tail_cons,zero_pow (by omega : 2 ≠ 0),zero_add] at h
  nlinarith [norm_nonneg (cons 0 x),norm_nonneg x]

@[simp] theorem norm_cons_axis {k : ℕ} (a : ℝ) : ‖cons a (0 : Space k)‖ = |a| := by
  have h := norm_sq_split (cons a (0 : Space k))
  simp only [head_cons,tail_cons,norm_zero,zero_pow (by omega : 2 ≠ 0),add_zero] at h
  nlinarith [norm_nonneg (cons a (0 : Space k)),abs_nonneg a,sq_abs a]

def axisUnit (k : ℕ) : Space (k+1) := cons 1 0

@[simp] theorem axisUnit_norm (k : ℕ) : ‖axisUnit k‖ = 1 := by simp [axisUnit]

/-- Householder reflection supplies an actual orthogonal map taking every unit
stem to the first coordinate axis; no favorable coordinate choice is assumed. -/
def alignStem {k : ℕ} (u : Space (k+1)) : Space (k+1) ≃ₗᵢ[ℝ] Space (k+1) :=
  (Submodule.span ℝ {u-axisUnit k})ᗮ.reflection

theorem alignStem_apply {k : ℕ} (u : Space (k+1)) (hu : ‖u‖ = 1) :
    alignStem u u = axisUnit k := by
  exact Submodule.reflection_sub (by simpa using hu)

/-- Applying any orthogonal transverse coordinate change while fixing the stem. -/
def liftIsometry {k : ℕ} (f : Space k ≃ₗᵢ[ℝ] Space k) :
    Space (k+1) ≃ₗᵢ[ℝ] Space (k+1) where
  toFun x := cons (head x) (f (tail x))
  invFun x := cons (head x) (f.symm (tail x))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp
  map_smul' a x := by simp
  norm_map' x := by
    change ‖cons (head x) (f (tail x))‖ = ‖x‖
    have h1 := norm_sq_split (cons (head x) (f (tail x)))
    have h2 := norm_sq_split x
    simp only [head_cons,tail_cons,f.norm_map] at h1
    nlinarith [norm_nonneg x,norm_nonneg (cons (head x) (f (tail x)))]

@[simp] theorem liftIsometry_axis {k : ℕ} (f : Space k ≃ₗᵢ[ℝ] Space k) :
    liftIsometry f (axisUnit k) = axisUnit k := by simp [liftIsometry,axisUnit]

end
end KakeyaFormal.EuclideanSplit
