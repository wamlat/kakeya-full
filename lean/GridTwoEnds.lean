import LocalizedGridTubes

/-! Exact finite center-ball tests under lattice-preserving common rescaling,
including the total-mass branch above the original localization radius. -/
namespace KakeyaFormal.GridTwoEnds
open Rescaling MeasurableRescaling LocalizedGridTubes Set
noncomputable section
open Classical

/-- The actual distance of every reindexed grid center transforms exactly. -/
theorem rescaled_center_distance {k : ℕ} {L : ℝ} (hL : 0 < L) (δ : ℝ)
    (origin z : Cell k) (x : Space k) :
    dist (cellCenter (δ/L) (shiftLabel origin z)) x =
      dist (cellCenter δ z) (inverse L (cellCenter δ origin) x)/L := by
  rw [← rescale_grid]
  conv_lhs => rw [← rescale_inverse hL.ne' (cellCenter δ origin) x]
  exact rescale_distance hL _ _ _

/-- An exact bijection of actual finite ball-tested shading cells. -/
theorem rescaled_ball_card {M k : ℕ} (F : TubeFamily k M) {L : ℝ} (hL : 0 < L)
    (δ : ℝ) (origin : Cell k) (a : Fin M → ℝ) (i : Fin M) (x : Space k) (r : ℝ) :
    (((Rescaling.family F L δ origin a).shade i).filter
      (fun z => dist (cellCenter (δ/L) z) x ≤ r)).card =
      ((F.shade i).filter (fun z => dist (cellCenter δ z) (inverse L (cellCenter δ origin) x) ≤ L*r)).card := by
  change (((F.shade i).image (shiftLabel origin)).filter _).card = _
  rw [Finset.filter_image,Finset.card_image_of_injective _ (shiftLabel_injective origin)]
  congr 1
  apply Finset.filter_congr
  intro z _
  rw [rescaled_center_distance hL]
  constructor
  · intro h
    simpa only [mul_comm] using (div_le_iff₀ hL).mp h
  · intro h
    exact (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using h)

/-- Every physical-radius finite-grid two-ends test transfers with the exact
relative-scale factor. Large original-radius tests use total cardinality. -/
theorem rescaled_two_ends {M k : ℕ} (F : TubeFamily k M) {L δ rho B alpha : ℝ}
    (hL : 0 < L) (hδ : 0 < δ) (hrho : 0 < rho) (hB : 1 ≤ B) (ha : 0 ≤ alpha)
    (origin : Cell k) (a : Fin M → ℝ)
    (hends : ∀ i, ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ rho →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*(r/rho)^alpha*((F.shade i).card:ℝ)) :
    ∀ i, ∀ x : Space k, ∀ r : ℝ, δ/L ≤ r →
      ((((Rescaling.family F L δ origin a).shade i).filter
        (fun z => dist (cellCenter (δ/L) z) x ≤ r)).card:ℝ) ≤
          (B*(L/rho)^alpha)*r^alpha*(((Rescaling.family F L δ origin a).shade i).card:ℝ) := by
  intro i x r hr
  have hr0 : 0 < r := (div_pos hδ hL).trans_le hr
  have hlo : δ ≤ L*r := by simpa only [mul_comm] using (div_le_iff₀ hL).mp hr
  have hid : (B*(L/rho)^alpha)*r^alpha = B*((L*r)/rho)^alpha := by
    rw [mul_assoc,← Real.mul_rpow (div_nonneg hL.le hrho.le) hr0.le]
    congr 2
    ring
  rw [rescaled_ball_card F hL,rescaled_card,hid]
  by_cases htop : L*r ≤ rho
  · exact hends i _ _ hlo htop
  · have hp : (1:ℝ) ≤ ((L*r)/rho)^alpha := Real.one_le_rpow
      ((one_le_div hrho).mpr (le_of_lt (lt_of_not_ge htop))) ha
    have hcoef : (1:ℝ) ≤ B*((L*r)/rho)^alpha := one_le_mul_of_one_le_of_one_le hB hp
    have hcard : (((F.shade i).filter (fun z => dist (cellCenter δ z)
        (inverse L (cellCenter δ origin) x) ≤ L*r)).card:ℝ) ≤ (F.shade i).card := by
      exact_mod_cast Finset.card_filter_le (F.shade i) _
    exact hcard.trans (by simpa only [one_mul] using (mul_le_mul_of_nonneg_right hcoef
      (show (0:ℝ) ≤ (F.shade i).card by positivity)))

/-- The actual localized-grid tube dilation has a fixed two-ends constant at
all rescaled radii, with no density- or scale-dependent normalization loss. -/
theorem localized_unit_two_ends {M k : ℕ} (F : TubeFamily k M) {δ rho width alpha : ℝ}
    (hδ : 0 < δ) (hrho : 0 < rho) (ha : 0 ≤ alpha) (origin : Cell k) (a : Fin M → ℝ)
    (hends : ∀ i, ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ rho →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        (4:ℝ)^alpha*(r/rho)^alpha*((F.shade i).card:ℝ)) :
    let L := 8*localWidth width*rho
    ∀ i, ∀ x : Space k, ∀ r : ℝ, δ/L ≤ r →
      ((((Rescaling.family F L δ origin a).shade i).filter
        (fun z => dist (cellCenter (δ/L) z) x ≤ r)).card:ℝ) ≤
          (32*localWidth width)^alpha*r^alpha*(((Rescaling.family F L δ origin a).shade i).card:ℝ) := by
  have hW := localWidth_pos width
  have hL : 0 < 8*localWidth width*rho := by positivity
  have hh := rescaled_two_ends F hL hδ hrho (Real.one_le_rpow (by norm_num) ha) ha origin a hends
  have hid : (4:ℝ)^alpha*((8*localWidth width*rho)/rho)^alpha = (32*localWidth width)^alpha := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (by positivity)]
    congr 1
    field_simp
    norm_num
  simpa only [hid] using hh

end
end KakeyaFormal.GridTwoEnds
