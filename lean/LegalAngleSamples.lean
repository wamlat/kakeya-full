import TransverseAngles
import LegalSampleNormalization
import AngleFiberSelection

/-! The actual marked transverse angles now supply a single legal-sample
system, ready for the finite angle-output fiber construction. -/
namespace KakeyaFormal.LegalAngleSamples
open Finset
open scoped BigOperators
open TransverseAngles
noncomputable section
open Classical

abbrev AngleIndex (k M : ℕ) := Σ _z : Cell k, Fin M × Fin M
abbrev Triple (k : ℕ) := Cell k × (Cell k × Cell k)

def firstCoordinate {k M : ℕ} (F : TubeFamily k M) (δ : ℝ)
    (a : AngleIndex k M) (z : Cell k) : ℝ :=
  LegalTubeSamples.coordinate (F.tube a.2.1).direction (cellCenter δ a.1) (cellCenter δ z)

def secondCoordinate {k M : ℕ} (F : TubeFamily k M) (δ : ℝ)
    (a : AngleIndex k M) (z : Cell k) : ℝ :=
  LegalTubeSamples.coordinate (F.tube a.2.2).direction (cellCenter δ a.1) (cellCenter δ z)

/-- The sample values are original occupied labels. One fixed orientation is
used throughout each actual marked angle. -/
structure SampleSystem {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    (δ lam kappa width : ℝ) where
  sign : ↥(angles F H kappa) → ℝ
  samples : ↥(angles F H kappa) → Finset (Triple k)
  sign_valid : ∀ a, sign a=1 ∨ sign a= -1
  card_lower : ∀ a, (lam/δ)^3/128 ≤ ((samples a).card:ℝ)
  legal : ∀ a p, p ∈ samples a →
    p.1 ∈ F.shade a.val.2.1 ∧ p.2.1 ∈ F.shade a.val.2.1 ∧ p.2.2 ∈ F.shade a.val.2.2 ∧
    kappa ≤ sign a*firstCoordinate F δ a.val p.1 ∧
    kappa ≤ sign a*firstCoordinate F δ a.val p.2.1-sign a*firstCoordinate F δ a.val p.1 ∧
    kappa ≤ |secondCoordinate F δ a.val p.2.2| ∧
    sign a*firstCoordinate F δ a.val p.2.1 ≤ 1+2*width ∧
    |secondCoordinate F δ a.val p.2.2| ≤ 1+2*width

/-- All angle-specific samples are constructed simultaneously from the actual
family. Common-vertex membership comes from marked incidence; coordinate
abundance comes from the original ball two-ends tests. -/
theorem construct {k M : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ lam kappa width B alpha : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hwidth : 0 ≤ width)
    (hδkappa : δ ≤ kappa) (hadm : F.Admissible width δ)
    (hmass : ∀ i, lam/δ ≤ ((F.shade i).card:ℝ))
    (hends : ∀ i, ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ))
    (hradius : (2*width+1)*kappa ≤ 1)
    (hsmall : B*((2*width+1)*kappa)^alpha ≤ 1/16) :
    Nonempty (SampleSystem F H δ lam kappa width) := by
  have hex : ∀ a : ↥(angles F H kappa), ∃ sign : ℝ, ∃ samples : Finset (Triple k),
      (sign=1 ∨ sign= -1) ∧ (lam/δ)^3/128 ≤ (samples.card:ℝ) ∧
      ∀ p ∈ samples, p.1 ∈ F.shade a.val.2.1 ∧ p.2.1 ∈ F.shade a.val.2.1 ∧ p.2.2 ∈ F.shade a.val.2.2 ∧
        kappa ≤ sign*firstCoordinate F δ a.val p.1 ∧
        kappa ≤ sign*firstCoordinate F δ a.val p.2.1-sign*firstCoordinate F δ a.val p.1 ∧
        kappa ≤ |secondCoordinate F δ a.val p.2.2| ∧
        sign*firstCoordinate F δ a.val p.2.1 ≤ 1+2*width ∧
        |secondCoordinate F δ a.val p.2.2| ≤ 1+2*width := by
    intro a
    obtain ⟨_,hv1,hv2,_⟩ := angle_geometry F H (hδ.trans_le hδkappa) hadm a.val a.property
    exact LegalTubeSamples.legal_triples_from_tubes (F.tube a.val.2.1) (F.tube a.val.2.2)
      (F.shade a.val.2.1) (F.shade a.val.2.2) (cellCenter δ a.val.1)
      hδ hδ1 hlam hwidth hδkappa hv1 hv2 (hadm _) (hadm _)
      (hmass _) (hmass _) (hends _) (hends _) hradius hsmall
  choose sign samples hsign hcard hlegal using hex
  exact ⟨⟨sign,samples,hsign,hcard,hlegal⟩⟩

/-- The actual total sample population is cubic per angle, including all
angles and all their own original-label triples. -/
theorem sample_mass {k M : ℕ} {F : TubeFamily k M} {H : Finset (Cell k)}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width) :
    (lam/δ)^3/128*((angles F H kappa).card:ℝ) ≤
      ∑ a : ↥(angles F H kappa), ((S.samples a).card:ℝ) := by
  have hh := sum_le_sum (s := (univ : Finset ↥(angles F H kappa))) (fun a _ => S.card_lower a)
  simpa only [sum_const,card_univ,Fintype.card_coe,Nat.cast_id,nsmul_eq_mul,mul_comm] using hh

end
end KakeyaFormal.LegalAngleSamples
