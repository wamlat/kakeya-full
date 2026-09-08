import MarkedLegalSamples

/-! Marked incidence populations and full legal-sample shadings remain distinct.
Broadness of the marks supplies enough transverse full-family angles; it is
never promoted to an unsupported broadness assertion about all full incidences. -/
namespace KakeyaFormal.MarkedSubsetSamples
open Finset TransverseAngles LegalAngleSamples
open scoped BigOperators
noncomputable section
open Classical

def markedFamily {n M : ℕ} (F : TubeFamily n M) (marks : Fin M → Finset (Cell n)) :
    TubeFamily n M := ⟨F.tube,marks⟩

/-- Every transverse pair of marked incidences is also a transverse pair of
the same original full tubes, with exactly the same vertex and tube indices. -/
theorem marked_angles_subset {n M : ℕ} (F : TubeFamily n M)
    (marks : Fin M → Finset (Cell n)) (H : Finset (Cell n)) (kappa : ℝ)
    (hsub : ∀ i, marks i ⊆ F.shade i) :
    angles (markedFamily F marks) H kappa ⊆ angles F H kappa := by
  intro a ha
  obtain ⟨hz,h1,h2,hangle⟩ := (mem_angles (markedFamily F marks) H kappa a).mp ha
  exact (mem_angles F H kappa a).mpr ⟨hz,hsub _ h1,hsub _ h2,hangle⟩

/-- Broadness is tested on the actual marked rows only. A single original
angular radius suffices; no all-radius power broadness premise is needed. -/
theorem marked_angle_count {n M : ℕ} (F : TubeFamily n M)
    (marks : Fin M → Finset (Cell n)) (H : Finset (Cell n))
    {kappa theta I E : ℝ} (hI : 0 ≤ I) (hE : 0 < E) (hangle : 2*kappa ≤ theta)
    (hsub : ∀ i, marks i ⊆ F.shade i)
    (hmass : I ≤ ∑ z ∈ H, ((incident (markedFamily F marks) z).card:ℝ))
    (hH : (H.card:ℝ) ≤ E)
    (hbroad : ∀ z ∈ H, ∀ v : Space n, ‖v‖=1 →
      (((incident (markedFamily F marks) z).filter (fun i =>
        projectiveDistance (F.tube i).direction v < theta)).card:ℝ) ≤
          ((incident (markedFamily F marks) z).card:ℝ)/2) :
    I^2/(2*E) ≤ ((angles F H kappa).card:ℝ) := by
  have hhalf : ∀ z ∈ H, ∀ i ∈ incident (markedFamily F marks) z,
      (((incident (markedFamily F marks) z).filter (fun j =>
        projectiveDistance ((markedFamily F marks).tube i).direction
          ((markedFamily F marks).tube j).direction < 2*kappa)).card:ℝ) ≤
        ((incident (markedFamily F marks) z).card:ℝ)/2 := by
    intro z hz i _
    have htest := hbroad z hz (F.tube i).direction (F.tube i).unit_direction
    apply le_trans _ htest
    apply Nat.cast_le.mpr
    apply card_le_card
    intro j hj
    refine mem_filter.mpr ⟨(mem_filter.mp hj).1,?_⟩
    rw [ProjectiveGeometry.projective_symm]
    exact ((mem_filter.mp hj).2).trans_le hangle
  exact (angle_count_lower (markedFamily F marks) H hI hE hmass hH hhalf).trans
    (Nat.cast_le.mpr (card_le_card (marked_angles_subset F marks H kappa hsub)))

/-- The actual marked population and full-shading two ends construct the
legal-sample system together. All later angle-output arguments may use the full
transverse angle set, whose lower bound is supplied by the marked subset. -/
theorem construct {n M : ℕ} (F : TubeFamily n M)
    (marks : Fin M → Finset (Cell n)) (H : Finset (Cell n))
    {δ lam width B alpha kappa theta I E : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hw : 0 ≤ width)
    (hI : 0 < I) (hE : 0 < E) (hδk : δ ≤ kappa) (hangle : 2*kappa ≤ theta)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam)
    (hsub : ∀ i, marks i ⊆ F.shade i)
    (hmass : I ≤ ∑ z ∈ H, ((incident (markedFamily F marks) z).card:ℝ))
    (hH : (H.card:ℝ) ≤ E)
    (hbroad : ∀ z ∈ H, ∀ v : Space n, ‖v‖=1 →
      (((incident (markedFamily F marks) z).filter (fun i =>
        projectiveDistance (F.tube i).direction v < theta)).card:ℝ) ≤
          ((incident (markedFamily F marks) z).card:ℝ)/2)
    (hends : ∀ i, ∀ x : Space n, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ))
    (hradius : (2*width+1)*kappa ≤ 1)
    (hsmall : B*((2*width+1)*kappa)^alpha ≤ 1/16) :
    Nonempty (SampleSystem F H δ lam kappa width) ∧
      I^2/(2*E) ≤ ((angles F H kappa).card:ℝ) ∧ (angles F H kappa).Nonempty := by
  have hcount := marked_angle_count F marks H hI.le hE hangle hsub hmass hH hbroad
  have hnonempty : (angles F H kappa).Nonempty := by
    apply card_pos.mp
    have hh : (0:ℝ) < (angles F H kappa).card :=
      (div_pos (sq_pos_of_pos hI) (by positivity : 0 < 2*E)).trans_le hcount
    exact_mod_cast hh
  exact ⟨LegalAngleSamples.construct F H hδ hδ1 hlam hw hδk hadm
    (fun i => (hcomp i).1) hends hradius hsmall,hcount,hnonempty⟩


/-- The existing explicit kappa also handles a single marked angular radius:
use inverse theta as its angular coefficient and exponent one. This preserves
the existing logarithmic and twentieth-power small-scale machinery. -/
theorem fixed_radius_choice {width B alpha theta : ℝ}
    (hw : 0 ≤ width) (hB : 1 ≤ B) (ha : 0 < alpha)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1) :
    let kappa := PivotKappa.choice width B theta⁻¹ alpha 1
    0 < kappa ∧ kappa ≤ 1/100 ∧ 2*kappa ≤ theta ∧
      (2*width+1)*kappa ≤ 1 ∧ B*((2*width+1)*kappa)^alpha ≤ 1/16 := by
  intro kappa
  have hK : 1 ≤ theta⁻¹ := by
    rw [← one_div]
    exact (one_le_div htheta).mpr htheta1
  obtain ⟨hk,hk1,hradius,hlegal,hhalf⟩ := PivotKappa.admissible hw hB hK ha
    (by norm_num : (0:ℝ) < 1)
  rw [Real.rpow_one] at hhalf
  have hangle : 2*kappa ≤ theta := by
    have hh := mul_le_mul_of_nonneg_left hhalf htheta.le
    have hid : theta*(theta⁻¹*(2*kappa)) = 2*kappa := by field_simp
    change theta*(theta⁻¹*(2*kappa)) ≤ theta*(1/2) at hh
    rw [hid] at hh
    linarith
  exact ⟨hk,hk1,hangle,hradius,hlegal⟩

/-- The original one-radius marked broadness and original full-shading two
ends now produce the actual legal system with a single explicit kappa. -/
theorem construct_fixed_radius {n M : ℕ} (F : TubeFamily n M)
    (marks : Fin M → Finset (Cell n)) (H : Finset (Cell n))
    {δ lam width B alpha theta I E : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hw : 0 ≤ width)
    (hB : 1 ≤ B) (ha : 0 < alpha) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hI : 0 < I) (hE : 0 < E)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam)
    (hsub : ∀ i, marks i ⊆ F.shade i)
    (hmass : I ≤ ∑ z ∈ H, ((incident (markedFamily F marks) z).card:ℝ))
    (hH : (H.card:ℝ) ≤ E)
    (hbroad : ∀ z ∈ H, ∀ v : Space n, ‖v‖=1 →
      (((incident (markedFamily F marks) z).filter (fun i =>
        projectiveDistance (F.tube i).direction v < theta)).card:ℝ) ≤
          ((incident (markedFamily F marks) z).card:ℝ)/2)
    (hends : ∀ i, ∀ x : Space n, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ))
    (hscale : δ ≤ PivotKappa.choice width B theta⁻¹ alpha 1) :
    let kappa := PivotKappa.choice width B theta⁻¹ alpha 1
    Nonempty (SampleSystem F H δ lam kappa width) ∧
      I^2/(2*E) ≤ ((angles F H kappa).card:ℝ) ∧ (angles F H kappa).Nonempty := by
  obtain ⟨hk,hk1,hangle,hradius,hlegal⟩ := fixed_radius_choice hw hB ha htheta htheta1
  have hδ1 : δ ≤ 1 := by linarith
  exact construct F marks H hδ hδ1 hlam hw hI hE hscale hangle hadm hcomp hsub
    hmass hH hbroad hends hradius hlegal

end
end KakeyaFormal.MarkedSubsetSamples
