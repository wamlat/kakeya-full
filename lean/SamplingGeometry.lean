import SamplingClosedCaps
import WidthNormalization

/-! Geometric conventions for raw sampling: actual finite axes of variable
length and a single common spatial dilation. The original integer cell labels
and normalized intersection probabilities are preserved exactly. -/
namespace KakeyaFormal.SamplingGeometry
open Set MeasureTheory Rescaling MeasurableRescaling WidthNormalization GridCells
noncomputable section

/-- A literal segment of the indicated length along the original unit axis. -/
def lengthCarrier {k : ℕ} (T : UnitTube k) (length width : ℝ) : Set (Space k) :=
  {x | ∃ t ∈ Set.Icc (0:ℝ) length, dist x (T.axisPoint t) ≤ width}

/-- One fixed dilation handles every length up to its fixed upper bound. It
only extends shortened segments when fitting them into unit carriers. -/
theorem normalized_length_carrier {k : ℕ} (T : UnitTube k)
    {W length width δ : ℝ} (hW : 0 < W) (hL : length ≤ W)
    (Y : Set (Space k)) (hY : Y ⊆ lengthCarrier T length (width*δ)) :
    normalizedSet W Y ⊆ (normalizedTube T W).carrier (width*(δ/W)) := by
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨t,ht,hd⟩ := hY hy
  have haxis := rescale_axisPoint T hW.ne' (0:Space k) 0 (t/W)
  have he : (0:ℝ)+W*(t/W)=t := by field_simp; ring
  rw [he] at haxis
  refine ⟨t/W,⟨div_nonneg ht.1 hW.le,(div_le_one hW).mpr (ht.2.trans hL)⟩,?_⟩
  change dist (rescale W 0 y) ((Rescaling.tube T W 0 0).axisPoint (t/W)) ≤ width*(δ/W)
  rw [← haxis,rescale_distance hW]
  exact (div_le_div_of_nonneg_right hd hW.le).trans_eq (by ring)

/-- Exact preservation of half-open grid membership, including every boundary. -/
theorem normalized_grid_membership {k : ℕ} {W : ℝ} (hW : 0 < W)
    (δ : ℝ) (z : Cell k) (x : Space k) :
    rescale W 0 x ∈ gridCell (δ/W) z ↔ x ∈ gridCell δ z := by
  rw [mem_gridCell,mem_gridCell]
  apply forall_congr'
  intro i
  simp only [rescale,sub_zero]
  change (δ/W)*((z i:ℝ)-1/2) ≤ W⁻¹*WithLp.ofLp x i ∧
      W⁻¹*WithLp.ofLp x i < (δ/W)*((z i:ℝ)+1/2) ↔
    δ*((z i:ℝ)-1/2) ≤ WithLp.ofLp x i ∧ WithLp.ofLp x i < δ*((z i:ℝ)+1/2)
  have hmul (a : ℝ) : (δ/W)*a=(δ*a)/W := by ring
  have hcoord : W⁻¹*WithLp.ofLp x i = WithLp.ofLp x i/W := by ring
  rw [hmul,hmul,hcoord,div_le_div_iff_of_pos_right hW,div_lt_div_iff_of_pos_right hW]

theorem normalized_grid_cell {k : ℕ} {W : ℝ} (hW : 0 < W) (δ : ℝ) (z : Cell k) :
    normalizedSet W (gridCell δ z) = gridCell (δ/W) z := by
  ext x
  rw [normalized_membership hW]
  have hh := normalized_grid_membership hW δ z (inverse W 0 x)
  rw [rescale_inverse hW.ne'] at hh
  exact hh.symm

theorem normalized_intersection {k : ℕ} {W : ℝ} (hW : 0 < W)
    (δ : ℝ) (z : Cell k) (Y : Set (Space k)) :
    normalizedSet W (Y ∩ gridCell δ z) = normalizedSet W Y ∩ gridCell (δ/W) z := by
  rw [← normalized_grid_cell hW]
  exact Set.image_inter (rescale_injective hW.ne' 0)

/-- Raw source probabilities are unchanged by one common dilation when the
mesh is dilated by the same factor. There is no row-dependent normalization. -/
theorem normalized_weight {k : ℕ} {W : ℝ} (hW : 0 < W)
    (δ : ℝ) (z : Cell k) (Y : Set (Space k)) :
    SamplingSupport.weight (normalizedSet W Y) (δ/W) z = SamplingSupport.weight Y δ z := by
  unfold SamplingSupport.weight
  rw [← normalized_intersection hW,normalized_volume hW,div_pow]
  field_simp

/-- Positive full and marked support cells keep exactly their original labels. -/
theorem normalized_positive_support {k : ℕ} {W : ℝ} (hW : 0 < W)
    (δ : ℝ) (z : Cell k) (Y : Set (Space k)) :
    0 < (volume : Measure (Space k)).real (normalizedSet W Y ∩ gridCell (δ/W) z) ↔
      0 < (volume : Measure (Space k)).real (Y ∩ gridCell δ z) := by
  rw [← normalized_intersection hW,normalized_volume hW]
  exact div_pos_iff_of_pos_right (pow_pos hW k)

/-- A fixed original c*delta separation becomes new-mesh separation whenever
W≥1/c, while directions are literally unchanged. -/
theorem normalized_separation {k M : ℕ} (F : TubeFamily k M)
    {δ W c : ℝ} (hδ : 0 ≤ δ) (hW : 0 < W) (hcW : 1 ≤ c*W)
    (hsep : F.Separated (c*δ)) :
    ∀ i j, i ≠ j → δ/W ≤ projectiveDistance
      (normalizedTube (F.tube i) W).direction (normalizedTube (F.tube j) W).direction := by
  intro i j hij
  apply le_trans _ (hsep i j hij)
  apply (div_le_iff₀ hW).mpr
  have hh := mul_le_mul_of_nonneg_right hcW hδ
  nlinarith

end
end KakeyaFormal.SamplingGeometry
