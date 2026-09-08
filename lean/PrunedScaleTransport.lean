import GridTwoEnds
import PrunedGraphLift

/-! The legal-sample homothety and the original spatial pruning use different
physical meshes with the same integer labels. The actual all-radius ball bound
transports exactly; original tubes are not presumed admissible at the new mesh. -/
namespace KakeyaFormal.PrunedScaleTransport
open Finset BallPruning PrunedGraphLift
noncomputable section
open Classical

theorem same_label_center_distance {n : ℕ} {R : ℝ} (hR : 0 < R) (δ : ℝ)
    (z : Cell n) (x : Space n) :
    dist (cellCenter (δ/R) z) x = dist (cellCenter δ z) (R • x)/R := by
  have hz : Rescaling.shiftLabel (0 : Cell n) z=z := by funext i; simp [Rescaling.shiftLabel]
  have hzero : cellCenter δ (0 : Cell n) = (0 : Space n) := by
    apply WithLp.ofLp_injective
    funext i
    simp [cellCenter]
  simpa only [hz,hzero,MeasurableRescaling.inverse,add_zero] using
    GridTwoEnds.rescaled_center_distance hR δ (0 : Cell n) z x

/-- An equality of the actual tested finite label sets, not a comparison of
their volumes or a covering by independently translated cells. -/
theorem same_label_ball_cells {n : ℕ} (E : Finset (Cell n)) {R : ℝ}
    (hR : 0 < R) (δ : ℝ) (x : Space n) (r : ℝ) :
    ballCells E (δ/R) x r = ballCells E δ (R • x) (R*r) := by
  unfold ballCells
  apply filter_congr
  intro z _
  rw [same_label_center_distance hR]
  exact (div_le_iff₀ hR).trans (by rw [mul_comm])

/-- All radii and centers transform under the same homothety, with exactly
the same spatial population constant and exponent. -/
theorem all_radius_transport {n : ℕ} (E : Finset (Cell n)) {δ R C d : ℝ}
    (hδ : 0 < δ) (hR : 0 < R)
    (hball : ∀ x : Space n, ∀ r : ℝ, δ ≤ r →
      ((ballCells E δ x r).card:ℝ) ≤ C*(r/δ)^d) :
    ∀ x : Space n, ∀ r : ℝ, δ/R ≤ r →
      ((ballCells E (δ/R) x r).card:ℝ) ≤ C*(r/(δ/R))^d := by
  intro x r hr
  rw [same_label_ball_cells E hR]
  have hlo : δ ≤ R*r := by simpa only [mul_comm] using (div_le_iff₀ hR).mp hr
  have hh := hball (R • x) (R*r) hlo
  have hid : (R*r)/δ = r/(δ/R) := by field_simp
  rwa [hid] at hh

/-- The literal original survivor union supplies the normalized-mesh bound
used by the actual selected graph cap estimate. Both physical scales are shown. -/
theorem pruned_normalized_ball_bound {n M J : ℕ} (F : TubeFamily n M)
    (E : Finset (Cell n)) {δ L d width baseRadius R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hR : 0 < R) (hadm : F.Admissible width δ) (hbounded : F.Bounded baseRadius)
    (hsmall : ∀ x : Space n, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((ballCells (PrunedIncidence.family F E δ L d J).unionCells δ x r).card:ℝ) ≤
        (coverConstant n 1*(2:ℝ)^d*L)*(r/δ)^d) :
    ∀ x : Space n, ∀ r : ℝ, δ/R ≤ r →
      ((ballCells (PrunedIncidence.family F E δ L d J).unionCells (δ/R) x r).card:ℝ) ≤
        (spatialConstant n width baseRadius d*L)*(r/(δ/R))^d :=
  all_radius_transport _ hδ hR
    (pruned_all_ball_bound F E hδ hδ1 hw hL hd hadm hbounded hsmall)

end
end KakeyaFormal.PrunedScaleTransport
