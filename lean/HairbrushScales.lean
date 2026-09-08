import HairbrushFractional

/-!
# Concrete logarithmic depth and density-independent hairbrush radii

The number of multiplicity levels is derived from actual projective direction
packing, with constants depending only on ambient dimension. Chosen two-ends and
broadness radii depend on their constants and exponents, never on shading density.
-/
namespace KakeyaFormal.HairbrushScales
open KakeyaFormal.ProjectiveGeometry KakeyaFormal.PlanarEnergy
noncomputable section

def constantDepth (k : ℕ) : ℕ := Nat.ceil (Real.logb 2 (packingConstant (k+1)))
def multiplicityDepth (k : ℕ) (δ : ℝ) : ℕ := constantDepth k+(k+1)*dyadicDepth δ

def logCoefficient (k : ℕ) : ℝ := (constantDepth k:ℝ)+(k+1:ℕ)+1

def hairbrushLog (k : ℕ) (δ : ℝ) : ℝ := logCoefficient k*(Real.logb 2 (2/δ)+2)

theorem constantDepth_covers (k : ℕ) : packingConstant (k+1) ≤ (2:ℝ)^(constantDepth k) := by
  have hP := packingConstant_ge_one (k+1)
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    (Nat.le_ceil (Real.logb 2 (packingConstant (k+1))))
  rw [Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    (by linarith : 0 < packingConstant (k+1)),Real.rpow_natCast] at hp
  exact hp

/-- Actual separated unit directions satisfy the concrete dyadic cardinal bound
needed for measurable multiplicity selection. -/
theorem multiplicityDepth_covers {k M : ℕ} (F : TubeFamily (k+2) M) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsep : F.Separated δ) :
    (M:ℝ) ≤ (2:ℝ)^(multiplicityDepth k δ) := by
  have h := separated_total_tube_count F hδ hδ1 hsep
  have hb : 1/δ ≤ (2:ℝ)^(dyadicDepth δ) := by
    apply (div_le_iff₀ hδ).mpr
    have hh := dyadicDepth_covers hδ
    nlinarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1/δ) hb (k+1)
  have hm := mul_le_mul (constantDepth_covers k) hp (by positivity) (by positivity)
  apply h.trans (hm.trans_eq ?_)
  rw [← pow_mul,← pow_add]
  congr 1
  dsimp [multiplicityDepth]
  ring

theorem logCoefficient_ge_one (k : ℕ) : 1 ≤ logCoefficient k := by
  unfold logCoefficient
  have ha : (0:ℝ) ≤ constantDepth k := Nat.cast_nonneg _
  have hk : (0:ℝ) ≤ (k+1:ℕ) := Nat.cast_nonneg _
  linarith

/-- Both the multiplicity depth and inverse-angle row logarithm fit within one
fixed dimensional multiple of log(2/δ)+2. -/
theorem multiplicityDepth_log_bound {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (multiplicityDepth k δ:ℝ)+1 ≤ hairbrushLog k δ := by
  have hb := dyadicDepth_log_bound hδ hδ1
  have hlog := Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    ((le_div_iff₀ hδ).mpr (by linarith) : (1:ℝ) ≤ 2/δ)
  have ha : (0:ℝ) ≤ constantDepth k := Nat.cast_nonneg _
  have hk : (0:ℝ) ≤ k+1 := by positivity
  have h₁ := mul_le_mul_of_nonneg_left hb hk
  have h₂ := mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ Real.logb 2 (2/δ)+2) ha
  dsimp [multiplicityDepth,hairbrushLog,logCoefficient]
  push_cast
  nlinarith

theorem hairbrushLog_covers_row {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.logb 2 (2/δ)+2 ≤ hairbrushLog k δ := by
  have hlog := Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    ((le_div_iff₀ hδ).mpr (by linarith) : (1:ℝ) ≤ 2/δ)
  exact (le_mul_of_one_le_left (by positivity) (logCoefficient_ge_one k))

theorem hairbrushLog_pos {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < hairbrushLog k δ := by
  have hlog := Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    ((le_div_iff₀ hδ).mpr (by linarith) : (1:ℝ) ≤ 2/δ)
  exact lt_of_lt_of_le (by linarith) (hairbrushLog_covers_row hδ hδ1)

/-- Radius chosen from a concentration constant and exponent. -/
def concentrationRadius (B alpha : ℝ) : ℝ := (2*B)^(-1/alpha)

theorem concentrationRadius_pos {B alpha : ℝ} (hB : 0 < B) :
    0 < concentrationRadius B alpha := by unfold concentrationRadius; positivity

theorem concentrationRadius_le_one {B alpha : ℝ} (hB : 1/2 ≤ B) (ha : 0 < alpha) :
    concentrationRadius B alpha ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith : (1:ℝ) ≤ 2*B)
  exact div_nonpos_of_nonpos_of_nonneg (by norm_num) ha.le

/-- The chosen radius makes the actual concentration factor exactly one half,
with no dependence on the shading density. -/
theorem concentrationRadius_factor {B alpha : ℝ} (hB : 0 < B) (ha : 0 < alpha) :
    B*(concentrationRadius B alpha)^alpha = 1/2 := by
  have hid : (-1/alpha)*alpha = (-1:ℝ) := by field_simp
  rw [concentrationRadius,← Real.rpow_mul (by positivity : 0 ≤ 2*B),hid,Real.rpow_neg_one]
  field_simp

end
end KakeyaFormal.HairbrushScales
