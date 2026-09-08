import ActualLabelSelection
import SelectedFiberSlab

/-! The exact dyadic sample fiber of every selected original output gives a
same-cardinality finite family of actual normalized labeled endpoint pairs.
All choices keep the original output index, intermediate and pivot labels. -/
namespace KakeyaFormal.SelectedOutputPairs
open Finset ActualLabelSelection AngleFiberSelection LegalAngleSamples
open LegalAngleNormalization LegalLabeledSamples LegalSampleOutputs PivotOutputCount
open scoped BigOperators
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
    {δ lam kappa width : ℝ} {S : SampleSystem F H δ lam kappa width}
    {hkappa : 0 < kappa} {hwidth : 0 ≤ width} {hadm : F.Admissible width δ}
    (P : Selection S hkappa hwidth hadm)

abbrev Index := Fin (outputSupport P.retained).card

theorem chosen_samples_nonempty (q : Index P) : (P.chosen_samples q).Nonempty := by
  apply card_pos.mp
  rw [(P.chosen_fiber q).2.2]
  exact lt_of_lt_of_le Nat.zero_lt_one P.dyadic_pos

/-- The intermediate coordinate of every selected triple is the original
intermediate label of its own indexed output. -/
theorem sample_intermediate (q : Index P) (p : ↥(P.chosen_samples q)) :
    p.val.1 = (P.chosen_output q).2 := by
  have hp := P.chosen_samples_actual q p.val p.property
  have he := output_encode S (P.chosen_angle q) hkappa hwidth hadm ⟨p.val,hp.1⟩
  have hh := congrArg Prod.snd (he.symm.trans hp.2)
  exact hh

/-- Actual membership is obtained from a selected original sample; it is never
postulated for the intermediate label. -/
def intermediate (q : Index P) : ↥(intermediates S (P.chosen_angle q)) := by
  refine ⟨(P.chosen_output q).2,?_⟩
  obtain ⟨p,hp⟩ := chosen_samples_nonempty P q
  exact mem_image.mpr ⟨p,(P.chosen_samples_actual q p hp).1,sample_intermediate P q ⟨p,hp⟩⟩

theorem intermediate_val (q : Index P) : (intermediate P q).val = (P.chosen_output q).2 := rfl

/-- Each selected output has its own genuine normalized angle. -/
def normalizedAngle (q : Index P) : PivotWitnesses.Angle (k+1) (kappa/(1+2*width)) :=
  angle S (P.chosen_angle q) (intermediate P q) hkappa hwidth

/-- Exact normalized mesh delta/(1+2width), transverse parameter
kappa/(1+2width), and projection error width 2width. -/
def pair (q : Index P) (p : ↥(P.chosen_samples q)) :
    LabeledPair (normalizedAngle P q) (δ/(1+2*width)) (2*width)
      (firstCoord S (P.chosen_angle q)) (secondCoord S (P.chosen_angle q)) := by
  let e : ↥(endpointLabels S (P.chosen_angle q) (intermediate P q).val) :=
    ⟨p.val.2,(mem_endpointLabels S (P.chosen_angle q) (intermediate P q).val p.val.2).mpr (by
      have hp := (P.chosen_samples_actual q p.val p.property).1
      have he : ((intermediate P q).val,p.val.2) = p.val :=
        Prod.ext (sample_intermediate P q p).symm rfl
      simpa only [he] using hp)⟩
  exact labeledPair S (P.chosen_angle q) (intermediate P q) e hkappa hwidth hadm

theorem pair_labels (q : Index P) (p : ↥(P.chosen_samples q)) :
    ((pair P q p).firstLabel,(pair P q p).secondLabel) = p.val.2 := rfl

theorem pair_injective (q : Index P) : Function.Injective (pair P q) := by
  intro p t he
  apply Subtype.ext
  apply Prod.ext ((sample_intermediate P q p).trans (sample_intermediate P q t).symm)
  exact (pair_labels P q p).symm.trans
    ((congrArg (fun s => (s.firstLabel,s.secondLabel)) he).trans (pair_labels P q t))

/-- The homogeneous selected pair encoding is exactly the existing actual
sample encoding, at the fixed original intermediate label. -/
theorem encode_pair (q : Index P) (p : ↥(P.chosen_samples q)) :
    encode S (P.chosen_angle q) hkappa hwidth hadm
      ⟨p.val,(P.chosen_samples_actual q p.val p.property).1⟩ =
        ⟨intermediate P q,pair P q p⟩ := by
  have hl := encode_labels S (P.chosen_angle q) hkappa hwidth hadm
    ⟨p.val,(P.chosen_samples_actual q p.val p.property).1⟩
  rcases he : encode S (P.chosen_angle q) hkappa hwidth hadm
      ⟨p.val,(P.chosen_samples_actual q p.val p.property).1⟩ with ⟨i,t⟩
  rw [he] at hl
  have hi : i=intermediate P q := Subtype.ext
    ((congrArg Prod.fst hl).trans (sample_intermediate P q p))
  subst i
  congr 1
  apply LabeledPair.labels_injective
  exact (congrArg Prod.snd hl).trans (pair_labels P q p).symm

/-- Every actual selected endpoint pair has the original selected pivot label. -/
theorem pair_pivot (q : Index P) (p : ↥(P.chosen_samples q)) :
    (pair P q p).pivotLabel = (P.chosen_output q).1 := by
  have hp := P.chosen_samples_actual q p.val p.property
  have ho := output_encode S (P.chosen_angle q) hkappa hwidth hadm ⟨p.val,hp.1⟩
  rw [encode_pair P q p] at ho
  exact congrArg Prod.fst (ho.symm.trans hp.2)

/-- The full image of the exact selected original sample fiber. -/
def raw (q : Index P) : Finset (LabeledPair (normalizedAngle P q) (δ/(1+2*width)) (2*width)
      (firstCoord S (P.chosen_angle q)) (secondCoord S (P.chosen_angle q))) :=
  univ.image (pair P q)

theorem raw_card (q : Index P) : (raw P q).card = 2^P.level := by
  rw [raw,card_image_of_injective _ (pair_injective P q),card_univ,Fintype.card_coe]
  exact (P.chosen_fiber q).2.2

theorem raw_nonempty (q : Index P) : (raw P q).Nonempty := by
  apply card_pos.mp
  rw [raw_card]
  exact lt_of_lt_of_le Nat.zero_lt_one P.dyadic_pos

theorem raw_pivot (q : Index P) (s) (hs : s ∈ raw P q) :
    s.pivotLabel = (P.chosen_output q).1 := by
  obtain ⟨p,_,rfl⟩ := mem_image.mp hs
  exact pair_pivot P q p

/-- Each homogeneous pair still decodes to a sample in the chosen original
angle's exact selected fiber, with unchanged endpoint labels. -/
theorem raw_original_sample (q : Index P) (s) (hs : s ∈ raw P q) :
    ((P.chosen_output q).2,s.firstLabel,s.secondLabel) ∈ P.chosen_samples q := by
  obtain ⟨p,_,rfl⟩ := mem_image.mp hs
  have he : ((P.chosen_output q).2,(pair P q p).firstLabel,(pair P q p).secondLabel) = p.val :=
    Prod.ext (sample_intermediate P q p).symm (pair_labels P q p)
  rw [he]
  exact p.property

/-- A reference is chosen within each actual raw fiber. -/
def reference (q : Index P) : LabeledPair (normalizedAngle P q) (δ/(1+2*width)) (2*width)
      (firstCoord S (P.chosen_angle q)) (secondCoord S (P.chosen_angle q)) :=
  (raw_nonempty P q).choose

theorem reference_mem (q : Index P) : reference P q ∈ raw P q :=
  (raw_nonempty P q).choose_spec

theorem reference_pivot (q : Index P) : (reference P q).pivotLabel=(P.chosen_output q).1 :=
  raw_pivot P q _ (reference_mem P q)

/-- The original output enumeration supplies injective intermediate labels at
fixed pivot, before any slab or color subdivision. -/
theorem fixed_pivot_intermediate_injective (pivot : Cell (k+1)) :
    Set.InjOn (fun q : Index P => (P.chosen_output q).2)
      {q | (P.chosen_output q).1=pivot} := by
  intro q hq r hr he
  exact P.chosen_output_injective (Prod.ext (hq.trans hr.symm) he)

end
end KakeyaFormal.SelectedOutputPairs
