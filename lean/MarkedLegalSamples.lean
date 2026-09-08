import LegalSampleSelection
import PivotKappa

/-! Original marked cap-broadness and two ends use the same explicit kappa
to construct actual transverse angles and their legal-sample system. -/
namespace KakeyaFormal.MarkedLegalSamples
open Finset LegalAngleSamples TransverseAngles
open scoped BigOperators
noncomputable section
open Classical

/-- No transverse-angle or sample-population premise is assumed: both follow
from actual marked incidence, pointwise cap tests and original tube two ends.
Only the uniform small-scale comparison delta<=the chosen kappa remains here. -/
theorem construct {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ lam width B K alpha beta I E : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hwidth : 0 ≤ width)
    (hB : 1 ≤ B) (hK : 1 ≤ K) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hI : 0 < I) (hE : 0 < E)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam)
    (hmass : I ≤ ∑ z ∈ H, ((incident F z).card:ℝ)) (hH : (H.card:ℝ) ≤ E)
    (hends : ∀ i, ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ))
    (hbroad : ∀ z ∈ H, ∀ v : Space k, ‖v‖=1 → ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((incident F z).filter (fun j => projectiveDistance (F.tube j).direction v < r)).card:ℝ) ≤
        K*r^beta*((incident F z).card:ℝ))
    (hscale : δ ≤ PivotKappa.choice width B K alpha beta) :
    let kappa := PivotKappa.choice width B K alpha beta
    Nonempty (SampleSystem F H δ lam kappa width) ∧
      I^2/(2*E) ≤ ((angles F H kappa).card:ℝ) ∧ (angles F H kappa).Nonempty := by
  dsimp only
  let kappa := PivotKappa.choice width B K alpha beta
  obtain ⟨hkappa,hkappa1,hradius,hsmall,hhalf⟩ :=
    PivotKappa.admissible hwidth hB hK halpha hbeta
  have hδ1 : δ ≤ 1 := by linarith
  have hhalfRows : ∀ z ∈ H, ∀ i ∈ incident F z,
      (((incident F z).filter (fun j =>
        projectiveDistance (F.tube i).direction (F.tube j).direction < 2*kappa)).card:ℝ) ≤
          ((incident F z).card:ℝ)/2 := by
    intro z hz i _
    have htest := hbroad z hz (F.tube i).direction (F.tube i).unit_direction (2*kappa)
      (by dsimp [kappa]; linarith) (by dsimp [kappa]; linarith)
    simp_rw [ProjectiveGeometry.projective_symm (F.tube _).direction (F.tube i).direction] at htest
    have hmul := mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg (incident F z).card : (0:ℝ) ≤ (incident F z).card)
    exact htest.trans (by simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hmul)
  have hcount := angle_count_lower F H hI.le hE hmass hH hhalfRows
  have hnonempty : (angles F H kappa).Nonempty := by
    apply card_pos.mp
    have hh : (0:ℝ) < (angles F H kappa).card :=
      (div_pos (sq_pos_of_pos hI) (by positivity : 0 < 2*E)).trans_le hcount
    exact_mod_cast hh
  exact ⟨LegalAngleSamples.construct F H hδ hδ1 hlam hwidth hscale hadm
    (fun i => (hcomp i).1) hends hradius hsmall,hcount,hnonempty⟩

end
end KakeyaFormal.MarkedLegalSamples
