import LegalTubeSamples
import Rescaling

/-! A single spatial homothety and one axis orientation convert the actual
bounded legal samples to the normalized PivotWitnesses interface. -/
namespace KakeyaFormal.LegalSampleNormalization
open KakeyaAudit.TubeGeometry KakeyaFormal.PivotWitnesses
noncomputable section

/-- Reversing the first axis preserves its actual perpendicular projection. -/
theorem transverse_signed {k : ℕ} (u v : Space k) {sign : ℝ}
    (hsign : sign=1 ∨ sign= -1) : transverse (sign • u) v = transverse u v := by
  rcases hsign with rfl | rfl
  · rw [one_smul]
  · rw [neg_one_smul]
    simp only [transverse,inner_neg_left,neg_smul,smul_neg,neg_neg]

/-- The intermediate point uses the same orientation and common spatial scale
as every endpoint in its fiber. No tube is independently translated. -/
def normalizeAngle {k : ℕ} (vertex u v : Space k) (a sign kappa R : ℝ)
    (hsign : sign=1 ∨ sign= -1) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hkappa : 0 < kappa) (hR : 1 ≤ R)
    (htrans : kappa ≤ ‖transverse u v‖) (ha : kappa ≤ sign*a) : Angle k (kappa/R) where
  vertex := R⁻¹ • vertex
  first := sign • u
  second := v
  first_unit := by rcases hsign with rfl | rfl <;> simpa only [one_smul,neg_one_smul,norm_neg]
  second_unit := hv
  transverse_lower := by
    rw [transverse_signed u v hsign]
    exact (div_le_self hkappa.le hR).trans htrans
  intermediate := sign*a/R
  intermediate_lower := div_le_div_of_nonneg_right ha (by linarith)

/-- Every legal raw endpoint pair yields a genuine normalized endpoint pair
for that same angle, with unchanged original occupied-cell labels. -/
def normalizeEndpoints {k : ℕ} (vertex u v : Space k) (a b c sign kappa R : ℝ)
    (hsign : sign=1 ∨ sign= -1) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hkappa : 0 < kappa) (hR : 1 ≤ R)
    (htrans : kappa ≤ ‖transverse u v‖) (ha : kappa ≤ sign*a)
    (hgap : kappa ≤ sign*b-sign*a) (hb : sign*b ≤ R)
    (hc : kappa ≤ |c|) (hcR : |c| ≤ R) :
    Endpoints (normalizeAngle vertex u v a sign kappa R hsign hu hv hkappa hR htrans ha) where
  firstCoord := sign*b/R
  secondCoord := c/R
  gap := by
    change kappa/R ≤ sign*b/R-sign*a/R
    rw [← sub_div]
    exact div_le_div_of_nonneg_right hgap (by linarith)
  first_upper := (div_le_one (by linarith : 0 < R)).mpr hb
  second_lower := by
    rw [abs_div,abs_of_pos (by linarith : 0 < R)]
    exact div_le_div_of_nonneg_right hc (by linarith)
  second_upper := by
    rw [abs_div,abs_of_pos (by linarith : 0 < R)]
    exact (div_le_one (by linarith : 0 < R)).mpr hcR

/-- Same lattice labels under a homothety of the whole ambient space. -/
theorem normalized_cell {k : ℕ} (δ R : ℝ) (z : Cell k) :
    cellCenter (δ/R) z = R⁻¹ • cellCenter δ z := by
  apply WithLp.ofLp_injective
  funext i
  change (δ/R)*(z i:ℝ) = R⁻¹*(δ*(z i:ℝ))
  ring

/-- Actual center-to-point errors scale by the very same homothety. -/
theorem normalized_center_distance {k : ℕ} (z : Cell k) (x : Space k)
    {δ R : ℝ} (hR : 0 < R) :
    dist (cellCenter (δ/R) z) (R⁻¹ • x) = dist (cellCenter δ z) x / R := by
  rw [normalized_cell,dist_smul₀,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
  ring

/-- The two normalized endpoints are precisely the common homothetic images
of the original raw projected points, including the reversed-axis case. -/
theorem normalized_endpoints_exact {k : ℕ} (vertex u v : Space k) (a b c sign kappa R : ℝ)
    (hsign : sign=1 ∨ sign= -1) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hkappa : 0 < kappa) (hR : 1 ≤ R)
    (htrans : kappa ≤ ‖transverse u v‖) (ha : kappa ≤ sign*a)
    (hgap : kappa ≤ sign*b-sign*a) (hb : sign*b ≤ R)
    (hc : kappa ≤ |c|) (hcR : |c| ≤ R) :
    let pair := normalizeEndpoints vertex u v a b c sign kappa R hsign hu hv hkappa hR htrans ha hgap hb hc hcR
    pair.firstPoint = R⁻¹ • (vertex+b • u) ∧ pair.secondPoint = R⁻¹ • (vertex+c • v) := by
  dsimp [normalizeEndpoints,normalizeAngle,Endpoints.firstPoint,Endpoints.secondPoint]
  constructor
  · rcases hsign with rfl | rfl <;> simp only [one_smul,neg_one_smul,one_mul,neg_one_mul] <;> module
  · module

/-- The intermediate point and exact pivot also undergo the same homothety.
The ratio a/b is unaffected by the common orientation and scale. -/
theorem normalized_pivot_exact {k : ℕ} (vertex u v : Space k) (a b c sign kappa R : ℝ)
    (hsign : sign=1 ∨ sign= -1) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hkappa : 0 < kappa) (hR : 1 ≤ R)
    (htrans : kappa ≤ ‖transverse u v‖) (ha : kappa ≤ sign*a)
    (hgap : kappa ≤ sign*b-sign*a) (hb : sign*b ≤ R)
    (hc : kappa ≤ |c|) (hcR : |c| ≤ R) :
    let angle := normalizeAngle vertex u v a sign kappa R hsign hu hv hkappa hR htrans ha
    let pair := normalizeEndpoints vertex u v a b c sign kappa R hsign hu hv hkappa hR htrans ha hgap hb hc hcR
    angle.vertex+angle.intermediate • angle.first = R⁻¹ • (vertex+a • u) ∧
      pair.pivot = R⁻¹ • (vertex+a • u+(c*(1-a/b)) • v) := by
  have hR0 : R ≠ 0 := by linarith
  have hquot : (sign*a/R)/(sign*b/R) = a/b := by
    rw [div_div_div_cancel_right₀ hR0]
    rcases hsign with rfl | rfl
    · simp only [one_mul]
    · simp only [neg_one_mul,neg_div_neg_eq]
  dsimp [normalizeAngle,normalizeEndpoints,Endpoints.pivot,Endpoints.coefficient]
  rw [hquot]
  rcases hsign with rfl | rfl <;> simp only [one_smul,neg_one_smul,one_mul,neg_one_mul] <;>
    constructor <;> module

end
end KakeyaFormal.LegalSampleNormalization
