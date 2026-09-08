import LegalTubeSamples
import ProjectiveGeometry
import Finite

/-! Actual transverse ordered tube pairs at the marked occupied cells. -/
namespace KakeyaFormal.TransverseAngles
open Finset
open scoped BigOperators
noncomputable section
open Classical

def pairs {I : Type*} (S : Finset I) (r : I → I → Prop) : Finset (I × I) :=
  (S ×ˢ S).filter (fun p => r p.1 p.2)

theorem pairs_card {I : Type*} (S : Finset I) (r : I → I → Prop) :
    (pairs S r).card = ∑ i ∈ S, (S.filter (fun j => r i j)).card := by
  simp only [pairs,card_eq_sum_ones,sum_filter,sum_product]

/-- A true pointwise half-broadness test retains half of all ordered pairs. -/
theorem pairs_lower {I : Type*} (S : Finset I) (r : I → I → Prop)
    (hbroad : ∀ i ∈ S, ((S.filter (fun j => ¬r i j)).card:ℝ) ≤ (S.card:ℝ)/2) :
    (S.card:ℝ)^2/2 ≤ ((pairs S r).card:ℝ) := by
  have hrow : ∀ i ∈ S, (S.card:ℝ)/2 ≤ ((S.filter (fun j => r i j)).card:ℝ) := by
    intro i hi
    have hp := card_filter_add_card_filter_not (s := S) (r i)
    have hp' : ((S.filter (r i)).card:ℝ)+((S.filter (fun j => ¬r i j)).card:ℝ) = (S.card:ℝ) := by
      exact_mod_cast hp
    linarith [hbroad i hi]
  rw [pairs_card,Nat.cast_sum]
  calc
    (S.card:ℝ)^2/2 = ∑ _i ∈ S, (S.card:ℝ)/2 := by simp only [sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := sum_le_sum hrow

def incident {k M : ℕ} (F : TubeFamily k M) (z : Cell k) : Finset (Fin M) :=
  univ.filter (fun i => z ∈ F.shade i)

def angles {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k)) (kappa : ℝ) :
    Finset (Σ _z : Cell k, Fin M × Fin M) :=
  H.sigma (fun z => pairs (incident F z)
    (fun i j => 2*kappa ≤ projectiveDistance (F.tube i).direction (F.tube j).direction))

/-- The angle labels are actual marked cells and actual incident tube pairs. -/
theorem mem_angles {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k)) (kappa : ℝ)
    (a : Σ _z : Cell k, Fin M × Fin M) :
    a ∈ angles F H kappa ↔ a.1 ∈ H ∧ a.1 ∈ F.shade a.2.1 ∧ a.1 ∈ F.shade a.2.2 ∧
      2*kappa ≤ projectiveDistance (F.tube a.2.1).direction (F.tube a.2.2).direction := by
  simp only [angles,Finset.mem_sigma,pairs,mem_filter,Finset.mem_product,incident,mem_univ,true_and]
  tauto

/-- Projective chord separation 2*kappa implies the required actual
perpendicular-axis separation kappa. -/
theorem transverse_lower {k : ℕ} (u v : Space k) {kappa : ℝ}
    (hu : ‖u‖=1) (hv : ‖v‖=1) (hkappa : 0 ≤ kappa)
    (hsep : 2*kappa ≤ projectiveDistance u v) :
    kappa ≤ ‖KakeyaAudit.TubeGeometry.transverse u v‖ := by
  have hchord := ProjectiveGeometry.projective_chord_sq u v hu hv
  have hperp := KakeyaAudit.TubeGeometry.transverse_norm_sq u v hu
  rw [hv,one_pow] at hperp
  have hi : |inner ℝ u v| ≤ 1 := by simpa only [hu,hv,one_mul] using abs_real_inner_le_norm u v
  have hs : (2*kappa)^2 ≤ projectiveDistance u v^2 :=
    sq_le_sq₀ (by positivity) (projectiveDistance_nonneg _ _) |>.mpr hsep
  apply (sq_le_sq₀ hkappa (norm_nonneg _)).mp
  nlinarith [sq_abs (inner ℝ u v),
    mul_nonneg (abs_nonneg (inner ℝ u v)) (sub_nonneg.mpr hi),sq_nonneg kappa]

/-- Summing the actual ordered pairs loses only the half-broadness factor. -/
theorem angle_energy_lower {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    (kappa : ℝ)
    (hbroad : ∀ z ∈ H, ∀ i ∈ incident F z,
      (((incident F z).filter (fun j =>
        projectiveDistance (F.tube i).direction (F.tube j).direction < 2*kappa)).card:ℝ) ≤
          ((incident F z).card:ℝ)/2) :
    (∑ z ∈ H, ((incident F z).card:ℝ)^2)/2 ≤ ((angles F H kappa).card:ℝ) := by
  have hpoint : ∀ z ∈ H, ((incident F z).card:ℝ)^2/2 ≤
      ((pairs (incident F z) (fun i j =>
        2*kappa ≤ projectiveDistance (F.tube i).direction (F.tube j).direction)).card:ℝ) := by
    intro z hz
    apply pairs_lower
    intro i hi
    simpa only [not_le] using hbroad z hz i hi
  simpa only [angles,Finset.card_sigma,Nat.cast_sum,← sum_div] using sum_le_sum hpoint

/-- The selected angle set has the expected marked-incidence-squared bound
over the number of occupied marked cells. Both the angles and energy are actual. -/
theorem angle_count_lower {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {kappa I E : ℝ} (hI : 0 ≤ I) (hE : 0 < E)
    (hmass : I ≤ ∑ z ∈ H, ((incident F z).card:ℝ)) (hH : (H.card:ℝ) ≤ E)
    (hbroad : ∀ z ∈ H, ∀ i ∈ incident F z,
      (((incident F z).filter (fun j =>
        projectiveDistance (F.tube i).direction (F.tube j).direction < 2*kappa)).card:ℝ) ≤
          ((incident F z).card:ℝ)/2) :
    I^2/(2*E) ≤ ((angles F H kappa).card:ℝ) := by
  have hcs := sum_mul_sq_le_sq_mul_sq H (fun _ => (1:ℝ)) (fun z => ((incident F z).card:ℝ))
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
  have he := angle_energy_lower F H kappa hbroad
  have he0 : 0 ≤ ∑ z ∈ H, ((incident F z).card:ℝ)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hEcs := hcs.trans (mul_le_mul_of_nonneg_right hH he0)
  have hIsq : I^2 ≤ (∑ z ∈ H, ((incident F z).card:ℝ))^2 :=
    (sq_le_sq₀ hI (hI.trans hmass)).mpr hmass
  apply (div_le_iff₀ (by positivity : 0 < 2*E)).mpr
  have hh := mul_le_mul_of_nonneg_left he hE.le
  nlinarith [hIsq.trans hEcs]

/-- Each selected angle has a common actual occupied vertex, distinct incident
tubes and the perpendicular-axis separation needed by the legal pivot records. -/
theorem angle_geometry {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ width kappa : ℝ} (hkappa : 0 < kappa) (hadm : F.Admissible width δ)
    (a : Σ _z : Cell k, Fin M × Fin M) (ha : a ∈ angles F H kappa) :
    a.2.1 ≠ a.2.2 ∧ cellCenter δ a.1 ∈ (F.tube a.2.1).carrier (width*δ) ∧
      cellCenter δ a.1 ∈ (F.tube a.2.2).carrier (width*δ) ∧
      kappa ≤ ‖KakeyaAudit.TubeGeometry.transverse (F.tube a.2.1).direction (F.tube a.2.2).direction‖ := by
  obtain ⟨_,hi,hj,hsep⟩ := (mem_angles F H kappa a).mp ha
  refine ⟨?_,hadm _ _ hi,hadm _ _ hj,
    transverse_lower _ _ (F.tube a.2.1).unit_direction (F.tube a.2.2).unit_direction hkappa.le hsep⟩
  intro hij
  rw [hij,projectiveDistance_self] at hsep
  linarith

end
end KakeyaFormal.TransverseAngles
