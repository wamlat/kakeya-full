import LegalLabeledSamples
import RawSampleTransfer

/-! Geometric output bounds for the original angle-specific label triples,
with the scalar homothety factors explicit and a common output type. -/
namespace KakeyaFormal.LegalSampleOutputs
open Finset LegalAngleSamples LegalAngleNormalization LegalLabeledSamples TransverseAngles
open PivotOutputCount RawSampleTransfer
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily k M} {H : Finset (Cell k)} {δ lam kappa width : ℝ}

def output (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hkappa : 0 < kappa) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) (p : Triple k) : Cell k × Cell k :=
  if hp : p ∈ S.samples a then
    let s := encode S a hkappa hwidth hadm ⟨p,hp⟩
    (s.2.pivotLabel,s.1.val)
  else (0,0)

theorem output_encode (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hkappa : 0 < kappa) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) (p : ↥(S.samples a)) :
    output S a hkappa hwidth hadm p.val =
      ((encode S a hkappa hwidth hadm p).2.pivotLabel,(encode S a hkappa hwidth hadm p).1.val) := by
  simp only [output,dif_pos p.property]

/-- The actual output set of one original marked angle has at most
C(k,width)*original-first-shade-card/delta elements. -/
theorem output_count (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) :
    (((S.samples a).image (output S a hkappa hwidth hadm)).card:ℝ) ≤
      (4*boxConstant k ((k:ℝ)/2)*(1+2*width))*((F.shade a.val.2.1).card:ℝ)/δ := by
  have hR : 0 < 1+2*width := by linarith
  have hδR : δ/(1+2*width) ≤ 1 := (div_le_one hR).mpr (by linarith)
  have hh := raw_geometric_output_count (S.samples a) (output S a hkappa hwidth hadm)
    univ (fun i => pairSet S a i hkappa hwidth hadm) Subtype.val
    (encode S a hkappa hwidth hadm) (encode_mem S a hkappa hwidth hadm)
    (output_encode S a hkappa hwidth hadm) (div_pos hδ hR) hδR (div_pos hkappa hR)
  have hc : ((univ : Finset ↥(intermediates S a)).card:ℝ) ≤ ((F.shade a.val.2.1).card:ℝ) := by
    simpa only [card_univ,Fintype.card_coe] using (Nat.cast_le.mpr (intermediate_card_le S a) :
      ((intermediates S a).card:ℝ) ≤ ((F.shade a.val.2.1).card:ℝ))
  have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*boxConstant k ((k:ℝ)/2) by
    have := (boxConstant_pos k ((k:ℝ)/2)).le
    positivity)
  have hd := hh.trans (div_le_div_of_nonneg_right hm (div_pos hδ hR).le)
  convert hd using 1 <;> first | rfl | field_simp

/-- Every complete raw output fixes its original intermediate label and one
normalized pivot label; its actual sample count has the required linear loss. -/
theorem fiber_count (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (f : Cell k × Cell k)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) :
    (((S.samples a).filter (fun p => output S a hkappa hwidth hadm p=f)).card:ℝ) ≤
      (fiberConstant k (2*width)*(1+2*width)^2)/(kappa*δ) := by
  have hR : 0 < 1+2*width := by linarith
  have hδR : δ/(1+2*width) ≤ 1 := (div_le_one hR).mpr (by linarith)
  have hkR : kappa/(1+2*width) ≤ 1 := (div_le_one hR).mpr (by linarith)
  have hh := raw_geometric_fiber_count (S.samples a) (output S a hkappa hwidth hadm)
    univ (fun i => pairSet S a i hkappa hwidth hadm) Subtype.val Subtype.val_injective
    (encode S a hkappa hwidth hadm) (encode_injective S a hkappa hwidth hadm)
    (encode_mem S a hkappa hwidth hadm) (output_encode S a hkappa hwidth hadm)
    f (div_pos hδ hR) hδR (div_pos hkappa hR) hkR
  convert hh using 1; field_simp

def outputConstant (k : ℕ) (width : ℝ) : ℝ := 8*boxConstant k ((k:ℝ)/2)*(1+2*width)

theorem outputConstant_pos (k : ℕ) {width : ℝ} (hwidth : 0 ≤ width) :
    0 < outputConstant k width := by
  have := boxConstant_pos k ((k:ℝ)/2)
  unfold outputConstant
  positivity

/-- Comparable original density yields the exact lambda/delta-squared output
budget used to delete low fibers. -/
theorem density_output_count (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ)
    (hcomp : F.Comparable δ lam) :
    (((S.samples a).image (output S a hkappa hwidth hadm)).card:ℝ) ≤
      outputConstant k width*lam/δ^2 := by
  have hbase := output_count S a hδ hδ1 hkappa hwidth hadm
  have hm := mul_le_mul_of_nonneg_left (hcomp a.val.2.1).2
    (show 0 ≤ 4*boxConstant k ((k:ℝ)/2)*(1+2*width) by
      have := (boxConstant_pos k ((k:ℝ)/2)).le
      positivity)
  have hh := hbase.trans (div_le_div_of_nonneg_right hm hδ.le)
  convert hh using 1 <;> first | rfl | (dsimp [outputConstant]; ring)

/-- The integer dyadic budget is a consequence of the actual fiber geometry. -/
theorem integer_fiber_count (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (f : Cell k × Cell k)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) :
    ((S.samples a).filter (fun p => output S a hkappa hwidth hadm p=f)).card ≤
      Nat.ceil ((fiberConstant k (2*width)*(1+2*width)^2)/(kappa*δ)) := by
  have hh := (fiber_count S a f hδ hδ1 hkappa hkappa1 hwidth hadm).trans
    (Nat.le_ceil ((fiberConstant k (2*width)*(1+2*width)^2)/(kappa*δ)))
  exact_mod_cast hh

end
end KakeyaFormal.LegalSampleOutputs
