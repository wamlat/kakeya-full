import HairbrushAllScales

/-!
# Density-independent radii instantiate the actual broad hairbrush kernel

The inputs are the original actual pointwise projective cap tests and the
original actual physical ball tests. Both radii are computed from their
constants and positive exponents, with no dependence on shading density.
-/
namespace KakeyaFormal.HairbrushKernel
open MeasureTheory
open scoped ENNReal
open KakeyaFormal.ProjectiveGeometry KakeyaFormal.MeasurableEnergy
open KakeyaFormal.HairbrushSelection KakeyaFormal.HairbrushBroad
open KakeyaFormal.HairbrushScales KakeyaFormal.HairbrushAllScales
noncomputable section

/-- Literal measurable angular broadness at unit scale, expressed as actual
finite original direction-cap populations at every marked physical point. -/
def PointwiseBroad {k M : ℕ} (F : TubeFamily k M) (Y : Fin M → Set (Space k))
    (G : Set (Space k)) (δ beta K : ℝ) : Prop := by
  classical
  exact ∀ x ∈ G, ∀ center : Space k, ∀ t : ℝ, δ ≤ t →
    ((Finset.univ.filter (fun i => x ∈ Y i ∧ projectiveDistance (F.tube i).direction center ≤ t)).card:ℝ) ≤
      K*t^beta*(overlapCount Y x:ℝ)

/-- The chosen broadness radius enforces the actual half-cap condition whenever
it lies in the admissible tested radius interval. -/
theorem chosen_radius_half_cap {k M : ℕ} (F : TubeFamily k M)
    (Y : Fin M → Set (Space k)) (G : Set (Space k)) {δ beta K : ℝ}
    (hK : 0 < K) (hb : 0 < beta) (hbroad : PointwiseBroad F Y G δ beta K)
    (hδtheta : δ ≤ concentrationRadius K beta) :
    ∀ x ∈ G, ∀ i, x ∈ Y i →
      (nearCount F.tube Y i (concentrationRadius K beta) x:ℝ) ≤ MeasurableEnergy.multiplicity Y x/2 := by
  classical
  intro x hx i _
  have h := hbroad x hx (F.tube i).direction (concentrationRadius K beta) hδtheta
  have hsub : ((Finset.univ.filter fun j => x ∈ Y j).filter
      fun j => projectiveDistance (F.tube i).direction (F.tube j).direction < concentrationRadius K beta) ⊆
      Finset.univ.filter (fun j => x ∈ Y j ∧
        projectiveDistance (F.tube j).direction (F.tube i).direction ≤ concentrationRadius K beta) := by
    intro j hj
    obtain ⟨hj,hangle⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2,
      by rw [projective_symm]; exact hangle.le⟩
  have hcard : (nearCount F.tube Y i (concentrationRadius K beta) x:ℝ) ≤
      ((Finset.univ.filter (fun j => x ∈ Y j ∧
        projectiveDistance (F.tube j).direction (F.tube i).direction ≤ concentrationRadius K beta)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  rw [concentrationRadius_factor hK hb] at h
  rw [multiplicity_eq_card]
  exact hcard.trans (by linarith)

/-- The actual all-scale fractional broad hairbrush with both radii constructed.
All choices are independent of λ and Λ. What remains for the full seed is the
construction/normalization and summation of broad marked pieces. -/
theorem chosen_radius_hairbrush {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) (G : Set (Space (k+2)))
    {δ lam B alpha beta K m A upper : ℝ} (hM : 0 < M)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 1 ≤ B) (ha : 0 < alpha) (hK : 1 ≤ K) (hb : 0 < beta) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) (hlamu : lam ≤ upper)
    (hm : 1 ≤ m) (hA : 1 ≤ A) (hu : 0 < upper) (hsep : F.Separated δ)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hG : MeasurableSet G)
    (hgood : (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 ≤ markedMass (ν := volume) Y G)
    (hbroad : PointwiseBroad F Y G δ beta K)
    (hmass : ∀ i, lam*δ^(k+1) ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hcap : F.CapBound δ m A)
    (hupper : ∀ i, (volume : Measure (Space (k+2))).real (Y i) ≤ upper*δ^(k+1)) :
    (concentrationRadius B alpha*concentrationRadius K beta)^(k+1)*markedMass (ν := volume) Y G*
        lam^((3:ℝ)/2)*δ^((m-1)/2)/
      (allScaleConstant k*Real.sqrt (A*upper)*(hairbrushLog k δ)^((5:ℝ)/2)) ≤
        (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  apply all_scale_real_cap_hairbrush F Y G hM hδ hδ1
    (concentrationRadius_pos (by linarith : 0 < K)) (concentrationRadius_le_one (by linarith) hb)
    (concentrationRadius_pos (by linarith : 0 < B)) (concentrationRadius_le_one (by linarith) ha)
    hlam hlam1 hlamu hm hA hu hsep hY hsub hG hgood
  · exact chosen_radius_half_cap F Y G (by linarith) hb hbroad
  · exact hmass
  · exact hends
  · exact (concentrationRadius_factor (by linarith : 0 < B) ha).le
  · exact hcap
  · exact hupper

end
end KakeyaFormal.HairbrushKernel

#print axioms KakeyaFormal.HairbrushKernel.chosen_radius_hairbrush
