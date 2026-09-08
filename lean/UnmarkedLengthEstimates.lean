import MarkedLengthNormalization
import OriginalLowerDensity
import WideTwoEndsEstimate

/-! Actual original bounded-length full shadings satisfy the normalized
unrestricted and two-ends estimates after one fixed common spatial dilation.
The original integer union is unchanged, and every scalar loss is explicit. -/
namespace KakeyaFormal.UnmarkedLengthEstimates
open MarkedLengthNormalization
noncomputable section

def geometry (geom : Normalization) (lengthUpper : ℝ) : Normalization where
  width := geom.width
  separation := geom.separation
  radius := geom.radius/dilation lengthUpper
  width_pos := geom.width_pos
  separation_pos := geom.separation_pos
  radius_pos := div_pos geom.radius_pos (dilation_pos _)

def factor (lengthUpper U p : ℝ) : ℝ :=
  ((dilation lengthUpper)⁻¹)^U*((dilation lengthUpper)⁻¹)^p

theorem factor_pos (lengthUpper U p : ℝ) : 0 < factor lengthUpper U p := by
  have hW := dilation_pos lengthUpper
  unfold factor
  positivity

theorem power_identity {δ lam W U p : ℝ} (hδ : 0 ≤ δ) (hlam : 0 ≤ lam) (hW : 0 ≤ W) :
    (δ/W)^U*(lam/W)^p = (W⁻¹)^U*(W⁻¹)^p*(δ^U*lam^p) := by
  rw [div_eq_mul_inv,div_eq_mul_inv,Real.mul_rpow hδ (inv_nonneg.mpr hW),
    Real.mul_rpow hlam (inv_nonneg.mpr hW)]
  ring

/-- This actual ball-count weakening permits every positive fixed alpha in
the public adapter, even though the common dilation uses alpha<=1. -/
theorem two_ends_weaken {n M : ℕ} (F : TubeFamily n M) {δ B alpha beta : ℝ}
    (hδ : 0 < δ) (hB : 0 ≤ B) (hba : beta ≤ alpha)
    (h : F.FullTwoEnds δ B alpha) : F.FullTwoEnds δ B beta := by
  intro i x r hr hr1
  have hp := Real.rpow_le_rpow_of_exponent_ge (hδ.trans_le hr) hr1 hba
  exact (h i x r hr hr1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp hB) (Nat.cast_nonneg _))

/-- Arbitrary fixed lower density on actual original bounded-length axes.
No upper full-density bound or lambda<=1 is required. -/
theorem from_discrete {n : ℕ} {m d p : ℝ}
    (hestimate : DiscreteEstimate n m d p) (hm : 0 ≤ m) (hp : 0 < p)
    (geom : Normalization) (lengthUpper c₀ eps : ℝ) (hc₀ : 0 < c₀) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily n M) (lengths : Fin M → ℝ)
      {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → 1 ≤ A →
      (∀ i, lengths i ≤ lengthUpper) →
      (∀ i z, z ∈ F.shade i → cellCenter δ z ∈
        SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (geom.width*δ)) →
      F.Separated (geom.separation*δ) → F.Bounded geom.radius → F.CapBound δ m A →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^(m-d+eps)*lam^p*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let W := dilation lengthUpper
  have hW : 1 ≤ W := dilation_ge_one _
  have hW0 : 0 < W := dilation_pos _
  obtain ⟨c,hc,hbound⟩ := OriginalLowerDensity.from_discrete hestimate hp
    (geometry geom lengthUpper) c₀ eps hc₀ heps
  refine ⟨c*factor lengthUpper (m-d+eps) p,mul_pos hc (factor_pos _ _ _),?_⟩
  intro M F lengths δ lam A hδ hδ1 hlam hA hL hadm hsep hbounded hcap hlower
  have hs : δ/W ≤ 1 := (div_le_one hW0).mpr (hδ1.trans hW)
  have hdensity : c₀*(lam/W)/(δ/W)=c₀*lam/δ := by field_simp
  have hh := hbound (normalizedFamily F W) (div_pos hδ hW0) hs (div_pos hlam hW0) hA
    (MarkedLengthNormalization.admissible F lengths hW0
      (fun i => (hL i).trans (le_max_right _ _)) hadm)
    (MarkedLengthNormalization.separated F hW hδ.le geom.separation_pos.le hsep)
    (MarkedLengthNormalization.bounded F hW0 hbounded)
    (MarkedLengthNormalization.cap_bound F hW hδ hδ1 hm (by linarith) hcap)
    (fun i => by rw [hdensity]; exact hlower i)
  have hid := power_identity (U:=m-d+eps) (p:=p) hδ.le hlam.le hW0.le
  change c*A⁻¹*(δ/W)^(m-d+eps)*(lam/W)^p*(M:ℝ) ≤ (F.unionCells.card:ℝ) at hh
  calc
    _ = (c*A⁻¹)*(((W⁻¹)^(m-d+eps)*(W⁻¹)^p)*(δ^(m-d+eps)*lam^p))*(M:ℝ) := by
      unfold factor
      ring
    _ = c*A⁻¹*(δ/W)^(m-d+eps)*(lam/W)^p*(M:ℝ) := by rw [← hid]; ring
    _ ≤ _ := hh

/-- Actual two-ends full shadings on all bounded-length original axes, with
fixed density multiples and every positive fixed ball exponent. -/
theorem from_two_ends {n : ℕ} {m d p : ℝ}
    (hestimate : TwoEndsDiscreteEstimate n m d p) (hm : 0 ≤ m) (hp : 0 ≤ p)
    (geom : Normalization) (lengthUpper c₀ C₀ B alpha eps : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB : 1 ≤ B)
    (halpha : 0 < alpha) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily n M) (lengths : Fin M → ℝ)
      {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      (∀ i, lengths i ≤ lengthUpper) →
      (∀ i z, z ∈ F.shade i → cellCenter δ z ∈
        SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (geom.width*δ)) →
      F.Separated (geom.separation*δ) → F.Bounded geom.radius → F.CapBound δ m A →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      (∀ i, ((F.shade i).card:ℝ) ≤ C₀*lam/δ) →
      F.FullTwoEnds δ B alpha →
      c*A⁻¹*δ^(m-d+eps)*lam^p*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let W := dilation lengthUpper
  let alpha₀ := min alpha 1
  have hW : 1 ≤ W := dilation_ge_one _
  have hW0 : 0 < W := dilation_pos _
  have ha₀ : 0 < alpha₀ := lt_min halpha (by norm_num)
  have hBnew : 1 ≤ B*W := by nlinarith
  obtain ⟨c,hc,hbound⟩ := WideTwoEndsEstimate.from_two_ends hestimate hp
    (geometry geom lengthUpper) c₀ C₀ (B*W) alpha₀ eps hc₀ hC₀ hBnew ha₀ heps
  refine ⟨c*factor lengthUpper (m-d+eps) p,mul_pos hc (factor_pos _ _ _),?_⟩
  intro M F lengths δ lam A hδ hδ1 hlam hlam1 hA hL hadm hsep hbounded hcap hlower hupper hends
  have hs : δ/W ≤ 1 := (div_le_one hW0).mpr (hδ1.trans hW)
  have hl : lam/W ≤ 1 := (div_le_one hW0).mpr (hlam1.trans hW)
  have hdensity (c : ℝ) : c*(lam/W)/(δ/W)=c*lam/δ := by field_simp
  have hends₀ := two_ends_weaken F hδ (by linarith : 0 ≤ B) (min_le_left alpha 1) hends
  have hendsNew := MarkedLengthNormalization.two_ends F hW hδ hB ha₀.le
    (min_le_right alpha 1) hends₀
  have hh := hbound (normalizedFamily F W) (div_pos hδ hW0) hs (div_pos hlam hW0) hl hA
    (MarkedLengthNormalization.admissible F lengths hW0
      (fun i => (hL i).trans (le_max_right _ _)) hadm)
    (MarkedLengthNormalization.separated F hW hδ.le geom.separation_pos.le hsep)
    (MarkedLengthNormalization.bounded F hW0 hbounded)
    (MarkedLengthNormalization.cap_bound F hW hδ hδ1 hm (by linarith) hcap)
    (fun i => by rw [hdensity]; exact hlower i)
    (fun i => by rw [hdensity]; exact hupper i) hendsNew
  have hid := power_identity (U:=m-d+eps) (p:=p) hδ.le hlam.le hW0.le
  change c*A⁻¹*(δ/W)^(m-d+eps)*(lam/W)^p*(M:ℝ) ≤ (F.unionCells.card:ℝ) at hh
  calc
    _ = (c*A⁻¹)*(((W⁻¹)^(m-d+eps)*(W⁻¹)^p)*(δ^(m-d+eps)*lam^p))*(M:ℝ) := by
      unfold factor
      ring
    _ = c*A⁻¹*(δ/W)^(m-d+eps)*(lam/W)^p*(M:ℝ) := by rw [← hid]; ring
    _ ≤ _ := hh

end
end KakeyaFormal.UnmarkedLengthEstimates
