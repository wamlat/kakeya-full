import HairbrushScales

/-!
# Actual coarse-scale hairbrush union bound

When width dominates the product of the two-ends and broadness radii, full
projective direction packing controls the total multiplicity by a polynomial
in those radii. Integrating actual finite multiplicity gives the coarse union
bound without two-ends, angular broadness, or a hairbrush assumption.
-/
namespace KakeyaFormal.HairbrushCoarse
open MeasureTheory
open scoped ENNReal
open KakeyaFormal.ProjectiveGeometry KakeyaFormal.HairbrushSelection
open KakeyaFormal.MeasurableEnergy KakeyaFormal.HairbrushFractional
noncomputable section

/-- Marked incidence mass is at most the actual number of tubes times the
actual measurable union volume. -/
theorem marked_mass_union_upper {k M : ℕ} (F : TubeFamily k M)
    (Y : Fin M → Set (Space k)) (G : Set (Space k)) {δ : ℝ}
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ) :
    markedMass (ν := volume) Y G ≤ (M:ℝ)*(volume : Measure (Space k)).real (⋃ i, Y i) := by
  have hfin (i : Fin M) := measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite (F.tube i) δ)
  have hm : markedMass (ν := volume) Y G ≤ ∑ i, (volume : Measure (Space k)).real (Y i) :=
    Finset.sum_le_sum (fun i _ => measureReal_mono Set.inter_subset_left (hfin i))
  have hover (x : Space k) : (overlapCount Y x:ℝ) ≤ M := by
    rw [← multiplicity_eq_card]
    simpa only [Fintype.card_fin] using multiplicity_le_card Y x
  exact hm.trans (finite_union_overlap Y hY hfin hover)

def coarseConstant (k : ℕ) : ℝ := packingConstant (k+1)*(88:ℝ)^(k+1)

theorem coarseConstant_pos (k : ℕ) : 0 < coarseConstant k := by
  have hp := packingConstant_ge_one (k+1)
  unfold coarseConstant
  positivity

/-- Actual full-dimensional direction packing closes the complementary coarse
range, with polynomial loss only in the density-independent radii. -/
theorem coarse_hairbrush_union_lower {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) (G : Set (Space (k+2))) {δ r theta : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hr : 0 < r) (htheta : 0 < theta)
    (hcoarse : r*theta ≤ 88*δ) (hsep : F.Separated δ)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ) :
    (r*theta)^(k+1)*markedMass (ν := volume) Y G/coarseConstant k ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  have htotal := separated_total_tube_count F hδ hδ1 hsep
  have hratio : 1/δ ≤ 88/(r*theta) := (div_le_div_iff₀ hδ (by positivity : 0 < r*theta)).mpr (by linarith)
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1/δ) hratio (k+1)
  have hP := packingConstant_ge_one (k+1)
  have hcount := htotal.trans (mul_le_mul_of_nonneg_left hpow (by linarith))
  have hmass := marked_mass_union_upper F Y G hY hsub
  have hproduct := mul_le_mul_of_nonneg_right hcount
    (measureReal_nonneg : 0 ≤ (volume : Measure (Space (k+2))).real (⋃ i, Y i))
  have hbound := hmass.trans hproduct
  have hden : 0 < packingConstant (k+1)*(88/(r*theta))^(k+1) := by positivity
  have hdiv : markedMass (ν := volume) Y G/(packingConstant (k+1)*(88/(r*theta))^(k+1)) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm (packingConstant (k+1)*(88/(r*theta))^(k+1))] using hbound
  have hid : (r*theta)^(k+1)*markedMass (ν := volume) Y G/coarseConstant k =
      markedMass (ν := volume) Y G/(packingConstant (k+1)*(88/(r*theta))^(k+1)) := by
    unfold coarseConstant
    rw [div_pow]
    field_simp
  rwa [← hid] at hdiv

/-- The fractional density/scale factor in (4.16) is at most one under the
actual allowed density interval and m≥1. -/
theorem fractional_factor_le_one {lam δ m A upper L : ℝ}
    (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlamu : lam ≤ upper)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hu : 0 < upper) (hL : 1 ≤ L) :
    lam^((3:ℝ)/2)*δ^((m-1)/2)/(Real.sqrt (A*upper)*L^((5:ℝ)/2)) ≤ 1 := by
  have hδpow := Real.rpow_le_one hδ.le hδ1 (by linarith : 0 ≤ (m-1)/2)
  have hlamsq : (lam^((3:ℝ)/2))^2 = lam^3 := by simpa using half_power_square hlam 3
  have hlam2 : lam^2 ≤ 1 := by nlinarith
  have hlam3 : lam^3 ≤ upper := by nlinarith [mul_le_mul_of_nonneg_left hlam2 hlam]
  have hroot : (Real.sqrt (A*upper))^2 = A*upper := Real.sq_sqrt (by positivity)
  have hcompare : lam^((3:ℝ)/2) ≤ Real.sqrt (A*upper) := by
    have hnonneg : 0 ≤ lam^((3:ℝ)/2) := by positivity
    have hroot0 := Real.sqrt_nonneg (A*upper)
    nlinarith [mul_le_mul_of_nonneg_right hA hu.le]
  have hLpow : 1 ≤ L^((5:ℝ)/2) := Real.one_le_rpow hL (by norm_num)
  have hnum := mul_le_mul hcompare hδpow (by positivity) (Real.sqrt_nonneg _)
  have hden : 0 < Real.sqrt (A*upper)*L^((5:ℝ)/2) := by positivity
  apply (div_le_iff₀ hden).mpr
  have hm := mul_le_mul_of_nonneg_left hLpow (Real.sqrt_nonneg (A*upper))
  nlinarith

end
end KakeyaFormal.HairbrushCoarse

#print axioms KakeyaFormal.HairbrushCoarse.coarse_hairbrush_union_lower
