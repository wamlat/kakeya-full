import SamplingGeometry
import MarkedGridNormalization

/-! One common spatial dilation puts all bounded-length original marked axes
inside unit axes. Integer cells, full rows, marks, directions and union counts
are unchanged. The two-ends coefficient has a fixed geometric cost only. -/
namespace KakeyaFormal.MarkedLengthNormalization
open Finset Rescaling MeasurableRescaling WidthNormalization
open TransverseAngles MarkedSubsetSamples
open scoped BigOperators
noncomputable section
open Classical

def dilation (lengthUpper : ℝ) : ℝ := max 1 lengthUpper

theorem dilation_ge_one (lengthUpper : ℝ) : 1 ≤ dilation lengthUpper := le_max_left _ _

theorem dilation_pos (lengthUpper : ℝ) : 0 < dilation lengthUpper :=
  zero_lt_one.trans_le (dilation_ge_one _)

def normalizedFamily {n M : ℕ} (F : TubeFamily n M) (W : ℝ) : TubeFamily n M :=
  ⟨fun i => normalizedTube (F.tube i) W, F.shade⟩

theorem union_eq {n M : ℕ} (F : TubeFamily n M) (W : ℝ) :
    (normalizedFamily F W).unionCells = F.unionCells := rfl

theorem center_eq {n : ℕ} (W δ : ℝ) (z : Cell n) :
    cellCenter (δ/W) z = rescale W 0 (cellCenter δ z) := by
  apply WithLp.ofLp_injective
  funext i
  change (δ/W)*(z i:ℝ) = W⁻¹*(δ*(z i:ℝ)-0)
  ring

theorem center_distance {n : ℕ} {W : ℝ} (hW : 0 < W)
    (δ : ℝ) (z : Cell n) (x : Space n) :
    dist (cellCenter (δ/W) z) x = dist (cellCenter δ z) (inverse W 0 x)/W := by
  rw [center_eq]
  conv_lhs => rw [← rescale_inverse hW.ne' 0 x]
  exact rescale_distance hW 0 _ _

theorem admissible {n M : ℕ} (F : TubeFamily n M) (lengths : Fin M → ℝ)
    {W δ width : ℝ} (hW : 0 < W) (hL : ∀ i, lengths i ≤ W)
    (hadm : ∀ i z, z ∈ F.shade i → cellCenter δ z ∈
      SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (width*δ)) :
    (normalizedFamily F W).Admissible width (δ/W) := by
  intro i z hz
  have hh := SamplingGeometry.normalized_length_carrier (F.tube i) hW (hL i)
    (SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (width*δ)) (fun _ h => h)
    (show rescale W 0 (cellCenter δ z) ∈ normalizedSet W
      (SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (width*δ)) from
      ⟨cellCenter δ z, hadm i z hz, rfl⟩)
  rw [← center_eq] at hh
  exact hh

theorem separated {n M : ℕ} (F : TubeFamily n M)
    {W δ sep : ℝ} (hW : 1 ≤ W) (hδ : 0 ≤ δ) (hsep0 : 0 ≤ sep)
    (hsep : F.Separated (sep*δ)) :
    (normalizedFamily F W).Separated (sep*(δ/W)) := by
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hscale : δ/W ≤ δ := (div_le_iff₀ hW0).mpr (by nlinarith)
  intro i j hij
  exact (mul_le_mul_of_nonneg_left hscale hsep0).trans (hsep i j hij)

theorem bounded {n M : ℕ} (F : TubeFamily n M)
    {W R : ℝ} (hW : 0 < W) (h : F.Bounded R) :
    (normalizedFamily F W).Bounded (R/W) := by
  intro i
  change ‖W⁻¹ • ((F.tube i).base + (0:ℝ) • (F.tube i).direction - 0)‖ ≤ R/W
  simp only [zero_smul,add_zero,sub_zero,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hW)]
  simpa only [div_eq_mul_inv,mul_comm] using div_le_div_of_nonneg_right (h i) hW.le

theorem cap_bound {n M : ℕ} (F : TubeFamily n M)
    {W δ m A : ℝ} (hW : 1 ≤ W) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 0 ≤ m) (hA : 0 ≤ A) (hcap : F.CapBound δ m A) :
    (normalizedFamily F W).CapBound (δ/W) m A := by
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hscale : δ/W ≤ δ := (div_le_iff₀ hW0).mpr (by nlinarith)
  exact LocalizedDirectionThinning.cap_bound_smaller_scale F
    (div_pos hδ hW0) hscale hδ1 hm hA hcap

/-- The original ball has radius W*r. Above radius one its total row count
supplies the bound; no original all-large-radii hypothesis is required. -/
theorem two_ends {n M : ℕ} (F : TubeFamily n M)
    {W δ B alpha : ℝ} (hW : 1 ≤ W) (hδ : 0 < δ) (hB : 1 ≤ B)
    (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ)) :
    ∀ i x r, δ/W ≤ r → r ≤ 1 →
      ((((normalizedFamily F W).shade i).filter
        (fun z => dist (cellCenter (δ/W) z) x ≤ r)).card:ℝ) ≤
        (B*W)*r^alpha*(((normalizedFamily F W).shade i).card:ℝ) := by
  intro i x r hr _
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hr0 : 0 < r := (div_pos hδ hW0).trans_le hr
  have hδR : δ ≤ W*r := by
    simpa only [mul_comm] using (div_le_iff₀ hW0).mp hr
  have hrow : (((F.shade i).filter
      (fun z => dist (cellCenter δ z) (inverse W 0 x) ≤ W*r)).card:ℝ) ≤
      B*(W*r)^alpha*((F.shade i).card:ℝ) := by
    by_cases hR : W*r ≤ 1
    · exact hends i _ _ hδR hR
    · have hp := Real.one_le_rpow (le_of_not_ge hR) ha
      have hcoef : 1 ≤ B*(W*r)^alpha := by nlinarith
      exact (Nat.cast_le.mpr (card_filter_le _ _)).trans
        (by nlinarith [Nat.cast_nonneg (α:=ℝ) (F.shade i).card])
  have heq : ((normalizedFamily F W).shade i).filter
      (fun z => dist (cellCenter (δ/W) z) x ≤ r) =
      (F.shade i).filter (fun z => dist (cellCenter δ z) (inverse W 0 x) ≤ W*r) := by
    ext z
    simp only [normalizedFamily,mem_filter,center_distance hW0,div_le_iff₀ hW0,mul_comm]
  rw [heq]
  change _ ≤ (B*W)*r^alpha*((F.shade i).card:ℝ)
  have hp : W^alpha ≤ W := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hW ha1
  apply hrow.trans
  rw [Real.mul_rpow hW0.le hr0.le]
  have hb0 : 0 ≤ B := by linarith
  calc
    _ = (B*W^alpha)*r^alpha*((F.shade i).card:ℝ) := by ring
    _ ≤ _ := by gcongr

end
end KakeyaFormal.MarkedLengthNormalization
