import Configurations

/-! A concrete two-ends estimate interface on the SAME actual normalized
finite tube/grid configurations as DiscreteEstimate. This is an explicit
finite ball-count property, not an uninterpreted geometric predicate. -/
namespace KakeyaFormal
open Finset
noncomputable section

/-- Full-shading two ends at every original scale delta<=r<=1. The center
ranges over actual Euclidean space, and counts use the original grid labels. -/
def TubeFamily.FullTwoEnds {n M : ℕ} (F : TubeFamily n M) (δ B alpha : ℝ) : Prop :=
  ∀ i x r, δ ≤ r → r ≤ 1 →
    (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
      B*r^alpha*((F.shade i).card:ℝ)

/-- The geometry, full two-ends coefficient, positive exponent and scale loss
are fixed BEFORE the actual configuration. Width, separation and bounded
region are the literal fields of Normalization/ShadedConfiguration. -/
def TwoEndsDiscreteEstimate (n : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : Normalization, ∀ B alpha eps : ℝ, 1 ≤ B → 0 < alpha → 0 < eps →
    ∃ c : ℝ, 0 < c ∧ ∀ F : ShadedConfiguration n geom m,
      F.family.FullTwoEnds F.δ B alpha →
      c*F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*(F.M:ℝ) ≤ (F.family.unionCells.card:ℝ)

/-- Any actual unrestricted estimate implies its full-two-ends restriction,
with exactly the same constants and original configurations. -/
theorem DiscreteEstimate.to_two_ends {n : ℕ} {m d p : ℝ} (h : DiscreteEstimate n m d p) :
    TwoEndsDiscreteEstimate n m d p := by
  intro geom B alpha eps _hB _halpha heps
  obtain ⟨c,hc,hbound⟩ := h geom eps heps
  exact ⟨c,hc,fun F _hends => hbound F⟩

/-- Increasing the density exponent weakens the estimate because the actual
configuration has density in (0,1]. No change to its full shadings is made. -/
theorem TwoEndsDiscreteEstimate.weaken_density {n : ℕ} {m d p p' : ℝ}
    (h : TwoEndsDiscreteEstimate n m d p) (hpp' : p ≤ p') :
    TwoEndsDiscreteEstimate n m d p' := by
  intro geom B alpha eps hB halpha heps
  obtain ⟨c,hc,hbound⟩ := h geom B alpha eps hB halpha heps
  refine ⟨c,hc,?_⟩
  intro F hends
  have hp := Real.rpow_le_rpow_of_exponent_ge F.density_pos F.density_le_one hpp'
  have hfactor : 0 ≤ c*F.A⁻¹*F.δ^(m-d+eps) := by
    have hA : 0 < F.A := zero_lt_one.trans_le F.cap_ge_one
    have hδ := F.scale_pos
    positivity
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hfactor) (Nat.cast_nonneg F.M)
  exact hh.trans (hbound F hends)

end
end KakeyaFormal
