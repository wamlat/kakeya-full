import LegalAngleNormalization
import PivotOutputCount

/-! Original occupied triples give actual labeled normalized endpoint records.
The encoding is injective, and all records belong to their constructed finite
intermediate/endpoint sets. -/
namespace KakeyaFormal.LegalLabeledSamples
open Finset LegalAngleSamples LegalAngleNormalization TransverseAngles PivotOutputCount
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily k M} {H : Finset (Cell k)} {δ lam kappa width : ℝ}

def firstCoord (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (z : Cell k) : ℝ :=
  S.sign a*firstCoordinate F δ a.val z/(1+2*width)

def secondCoord (_S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (z : Cell k) : ℝ :=
  secondCoordinate F δ a.val z/(1+2*width)

/-- The existing legal endpoints obtain the actual grid-center errors needed
by geometric output counting, at the same normalized mesh and unchanged labels. -/
def labeledPair (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (i : ↥(intermediates S a))
    (e : ↥(endpointLabels S a i.val))
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) :
    LabeledPair (angle S a i hkappa hwidth) (δ/(1+2*width)) (2*width)
      (firstCoord S a) (secondCoord S a) where
  firstLabel := e.val.1
  secondLabel := e.val.2
  gap := (LegalAngleNormalization.endpoints S a i e hkappa hwidth).gap
  first_upper := (LegalAngleNormalization.endpoints S a i e hkappa hwidth).first_upper
  second_lower := (LegalAngleNormalization.endpoints S a i e hkappa hwidth).second_lower
  second_upper := (LegalAngleNormalization.endpoints S a i e hkappa hwidth).second_upper
  first_close := by
    have hp := (mem_endpointLabels S a i.val e.val).mp e.property
    have hb := (S.legal a (i.val,e.val) hp).2.1
    have hv1 := (angle_geometry F H hkappa hadm a.val a.property).2.1
    have hR : 0 < 1+2*width := by linarith
    have hclose := (LegalTubeSamples.shifted_tube_projection (F.tube a.val.2.1)
      (cellCenter δ a.val.1) (cellCenter δ e.val.1) hv1 (hadm _ _ hb)).1
    have haxis : (1+2*width)⁻¹ • (cellCenter δ a.val.1+
        firstCoordinate F δ a.val e.val.1 • (F.tube a.val.2.1).direction) =
        (angle S a i hkappa hwidth).vertex+
          firstCoord S a e.val.1 • (angle S a i hkappa hwidth).first := by
      dsimp [angle,LegalSampleNormalization.normalizeAngle,firstCoord]
      rcases S.sign_valid a with hs | hs
      · rw [hs,one_mul,one_smul]
        module
      · rw [hs,neg_one_mul,neg_one_smul]
        module
    rw [← haxis,LegalSampleNormalization.normalized_center_distance _ _ hR]
    convert div_le_div_of_nonneg_right hclose hR.le using 1 <;> first | rfl | ring
  second_close := by
    have hp := (mem_endpointLabels S a i.val e.val).mp e.property
    have hc := (S.legal a (i.val,e.val) hp).2.2.1
    have hv2 := (angle_geometry F H hkappa hadm a.val a.property).2.2.1
    have hR : 0 < 1+2*width := by linarith
    have hclose := (LegalTubeSamples.shifted_tube_projection (F.tube a.val.2.2)
      (cellCenter δ a.val.1) (cellCenter δ e.val.2) hv2 (hadm _ _ hc)).1
    have haxis : (1+2*width)⁻¹ • (cellCenter δ a.val.1+
        secondCoordinate F δ a.val e.val.2 • (F.tube a.val.2.2).direction) =
        (angle S a i hkappa hwidth).vertex+
          secondCoord S a e.val.2 • (angle S a i hkappa hwidth).second := by
      dsimp [angle,LegalSampleNormalization.normalizeAngle,secondCoord]
      module
    rw [← haxis,LegalSampleNormalization.normalized_center_distance _ _ hR]
    convert div_le_div_of_nonneg_right hclose hR.le using 1 <;> first | rfl | ring

def pairSet (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (i : ↥(intermediates S a))
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) :
    Finset (LabeledPair (angle S a i hkappa hwidth) (δ/(1+2*width)) (2*width)
      (firstCoord S a) (secondCoord S a)) :=
  univ.image (fun e => labeledPair S a i e hkappa hwidth hadm)

def encode (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hkappa : 0 < kappa) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) (p : ↥(S.samples a)) :
    (i : ↥(intermediates S a)) × LabeledPair (angle S a i hkappa hwidth)
      (δ/(1+2*width)) (2*width) (firstCoord S a) (secondCoord S a) :=
  let i : ↥(intermediates S a) := ⟨p.val.1,mem_image.mpr ⟨p.val,p.property,rfl⟩⟩
  let e : ↥(endpointLabels S a i.val) :=
    ⟨p.val.2,(mem_endpointLabels S a i.val p.val.2).mpr p.property⟩
  ⟨i,labeledPair S a i e hkappa hwidth hadm⟩

/-- Recovering original labels is an exact left inverse of the encoding. -/
theorem encode_labels (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hkappa : 0 < kappa) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) (p : ↥(S.samples a)) :
    ((encode S a hkappa hwidth hadm p).1.val,
      (encode S a hkappa hwidth hadm p).2.firstLabel,
      (encode S a hkappa hwidth hadm p).2.secondLabel) = p.val := rfl

theorem encode_injective (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hkappa : 0 < kappa) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) : Function.Injective (encode S a hkappa hwidth hadm) := by
  intro p q hpq
  apply Subtype.ext
  have hh := congrArg (fun s => (s.1.val,s.2.firstLabel,s.2.secondLabel)) hpq
  simpa only [encode_labels] using hh

/-- Every encoded record belongs to the genuine finite dependent sample set. -/
theorem encode_mem (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hkappa : 0 < kappa) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) (p : ↥(S.samples a)) :
    encode S a hkappa hwidth hadm p ∈
      univ.sigma (fun i => pairSet S a i hkappa hwidth hadm) := by
  apply mem_sigma.mpr
  refine ⟨mem_univ _,?_⟩
  exact mem_image.mpr ⟨_,mem_univ _,rfl⟩

/-- The intermediate-label population is bounded by the first original shade. -/
theorem intermediate_card_le (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) :
    (intermediates S a).card ≤ (F.shade a.val.2.1).card := by
  apply card_le_card
  intro i hi
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hi
  exact (S.legal a p hp).1

end
end KakeyaFormal.LegalLabeledSamples
