import PivotOutputCount

/-! Transfer actual output and fiber bounds to arbitrary finite raw sample sets.
The common output type is a pair of original cell labels; dependent intermediate
indices and proof wrappers are forgotten by an injective label map. -/
namespace KakeyaFormal.RawSampleTransfer
open Finset PivotOutputCount PivotWitnesses
noncomputable section
open Classical

variable {Raw Index Value Out Out' : Type*}
variable [DecidableEq Out] [DecidableEq Out']

/-- Forget a dependent intermediate wrapper while retaining its actual cell. -/
def forgetOutput {k : ℕ} (indexLabel : Index → Cell k) (f : Cell k × Index) : Cell k × Cell k :=
  (f.1,indexLabel f.2)

theorem forgetOutput_injective {k : ℕ} {indexLabel : Index → Cell k}
    (hinj : Function.Injective indexLabel) : Function.Injective (forgetOutput indexLabel) := by
  intro f g heq
  change (f.1,indexLabel f.2) = (g.1,indexLabel g.2) at heq
  exact Prod.ext (Prod.mk.inj heq).1 (hinj (Prod.mk.inj heq).2)

/-- A filter on attached valid samples has exactly the original raw filter's
cardinality. Proof fields introduce no change in the count. -/
theorem attach_filter_card (P : Finset Raw) (out : Raw → Out) (f : Out) :
    (P.attach.filter (fun p => out p.val = f)).card = (P.filter (fun p => out p = f)).card := by
  have himage : (P.attach.filter (fun p => out p.val = f)).image Subtype.val =
      P.filter (fun p => out p = f) := by
    ext p
    constructor
    · intro hp
      obtain ⟨q,hq,rfl⟩ := mem_image.mp hp
      exact mem_filter.mpr ⟨q.property,(mem_filter.mp hq).2⟩
    · intro hp
      obtain ⟨hpP,hpf⟩ := mem_filter.mp hp
      exact mem_image.mpr ⟨⟨p,hpP⟩,mem_filter.mpr ⟨mem_attach _ _,hpf⟩,rfl⟩
  rw [← himage,card_image_of_injective _ Subtype.val_injective]

/-- Any actual record encoding transports the output support into the record
output support. Injectivity is not needed for this support-only step. -/
theorem raw_output_card_le (P : Finset Raw) (out : Raw → Out') (Q : Finset Value)
    (recordOut : Value → Out) (forget : Out → Out') (encode : ↥P → Value)
    (hmem : ∀ p, encode p ∈ Q) (hout : ∀ p, out p.val = forget (recordOut (encode p))) :
    (P.image out).card ≤ (Q.image recordOut).card := by
  have hsub : P.image out ⊆ (Q.image recordOut).image forget := by
    intro f hf
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hf
    exact mem_image.mpr ⟨recordOut (encode ⟨p,hp⟩),
      mem_image.mpr ⟨encode ⟨p,hp⟩,hmem _,rfl⟩,(hout ⟨p,hp⟩).symm⟩
  exact (card_le_card hsub).trans (card_image_le)

/-- An injective valid-sample encoding transfers an actual raw output fiber to
one specific normalized record fiber. This is a finite-set injection proof. -/
theorem raw_fiber_card_le (P : Finset Raw) (out : Raw → Out') (Q : Finset Value)
    (recordOut : Value → Out) (encode : ↥P → Value) (hinj : Function.Injective encode)
    (hmem : ∀ p, encode p ∈ Q) (f : Out') (g : Out)
    (hfiber : ∀ p, out p.val = f → recordOut (encode p) = g) :
    (P.filter (fun p => out p = f)).card ≤ (Q.filter (fun r => recordOut r = g)).card := by
  rw [← attach_filter_card]
  apply card_le_card_of_injOn encode
  · intro p hp
    exact mem_filter.mpr ⟨hmem p,hfiber p (mem_filter.mp hp).2⟩
  · exact hinj.injOn

/-- A nonempty raw fiber determines one normalized output. Injectivity of the
forgotten label coordinate forces every record in that raw fiber to use it. -/
theorem raw_nonempty_fiber (P : Finset Raw) (out : Raw → Out') (Q : Finset Value)
    (recordOut : Value → Out) (forget : Out → Out') (hforget : Function.Injective forget)
    (encode : ↥P → Value) (hinj : Function.Injective encode)
    (hmem : ∀ p, encode p ∈ Q) (hout : ∀ p, out p.val = forget (recordOut (encode p)))
    (f : Out') (hne : (P.filter (fun p => out p = f)).Nonempty) :
    ∃ g : Out, forget g = f ∧
      (P.filter (fun p => out p = f)).card ≤ (Q.filter (fun r => recordOut r = g)).card := by
  obtain ⟨p,hp⟩ := hne
  obtain ⟨hpP,hpf⟩ := mem_filter.mp hp
  let g := recordOut (encode ⟨p,hpP⟩)
  have hgf : forget g = f := (hout ⟨p,hpP⟩).symm.trans hpf
  refine ⟨g,hgf,raw_fiber_card_le P out Q recordOut encode hinj hmem f g ?_⟩
  intro q hq
  apply hforget
  exact (hout q).symm.trans (hq.trans hgf.symm)

/-- The actual geometric output bound transferred to arbitrary original sample
records, using the same global output type across original angles. -/
theorem raw_geometric_output_count {k : ℕ} {kap δ width : ℝ}
    {a : Index → Angle k kap} {fc sc : Index → Cell k → ℝ}
    (P : Finset Raw) (out : Raw → Cell k × Cell k)
    (I : Finset Index) (S : ∀ i, Finset (LabeledPair (a i) δ width (fc i) (sc i)))
    (indexLabel : Index → Cell k)
    (encode : ↥P → (i : Index) × LabeledPair (a i) δ width (fc i) (sc i))
    (hmem : ∀ p, encode p ∈ I.sigma S)
    (hout : ∀ p, out p.val = ((encode p).2.pivotLabel,indexLabel (encode p).1))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) :
    ((P.image out).card : ℝ) ≤ 4*boxConstant k ((k : ℝ)/2)*(I.card : ℝ)/δ := by
  have hc : ((P.image out).card : ℝ) ≤ (((I.sigma S).image sampleOutput).card : ℝ) := by
    exact_mod_cast raw_output_card_le P out (I.sigma S) sampleOutput (forgetOutput indexLabel)
      encode hmem hout
  exact hc.trans (all_output_count I S hδ hδ1 hk)

/-- The geometric real fiber bound transferred through an actual injective
encoding. Empty raw fibers are handled directly; nonempty ones determine their
unique dependent intermediate index from the common cell-pair output. -/
theorem raw_geometric_fiber_count {k : ℕ} {kap δ width : ℝ}
    {a : Index → Angle k kap} {fc sc : Index → Cell k → ℝ}
    (P : Finset Raw) (out : Raw → Cell k × Cell k)
    (I : Finset Index) (S : ∀ i, Finset (LabeledPair (a i) δ width (fc i) (sc i)))
    (indexLabel : Index → Cell k) (hindex : Function.Injective indexLabel)
    (encode : ↥P → (i : Index) × LabeledPair (a i) δ width (fc i) (sc i))
    (hencode : Function.Injective encode) (hmem : ∀ p, encode p ∈ I.sigma S)
    (hout : ∀ p, out p.val = ((encode p).2.pivotLabel,indexLabel (encode p).1))
    (f : Cell k × Cell k) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) (hk1 : kap ≤ 1) :
    ((P.filter (fun p => out p = f)).card : ℝ) ≤ fiberConstant k width/(kap*δ) := by
  by_cases hne : (P.filter (fun p => out p = f)).Nonempty
  · obtain ⟨g,_,hc⟩ := raw_nonempty_fiber P out (I.sigma S) sampleOutput
      (forgetOutput indexLabel) (forgetOutput_injective hindex) encode hencode hmem hout f hne
    have hc' : ((P.filter (fun p => out p = f)).card : ℝ) ≤
        (((I.sigma S).filter (fun r => sampleOutput r = g)).card : ℝ) := by exact_mod_cast hc
    exact hc'.trans (all_output_fiber_count I S g hδ hδ1 hk hk1)
  · have hz := not_nonempty_iff_eq_empty.mp hne
    rw [hz,card_empty,Nat.cast_zero]
    have := (boxConstant_pos k width).le
    dsimp [fiberConstant]
    positivity

/-- Derived integer fiber budget for the original raw sample set. -/
theorem raw_integer_fiber_bound {k : ℕ} {kap δ width : ℝ}
    {a : Index → Angle k kap} {fc sc : Index → Cell k → ℝ}
    (P : Finset Raw) (out : Raw → Cell k × Cell k)
    (I : Finset Index) (S : ∀ i, Finset (LabeledPair (a i) δ width (fc i) (sc i)))
    (indexLabel : Index → Cell k) (hindex : Function.Injective indexLabel)
    (encode : ↥P → (i : Index) × LabeledPair (a i) δ width (fc i) (sc i))
    (hencode : Function.Injective encode) (hmem : ∀ p, encode p ∈ I.sigma S)
    (hout : ∀ p, out p.val = ((encode p).2.pivotLabel,indexLabel (encode p).1))
    (f : Cell k × Cell k) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) (hk1 : kap ≤ 1) :
    (P.filter (fun p => out p = f)).card ≤ Nat.ceil (fiberConstant k width/(kap*δ)) := by
  have hh := (raw_geometric_fiber_count P out I S indexLabel hindex encode hencode hmem hout f hδ hδ1 hk hk1).trans
    (Nat.le_ceil (fiberConstant k width/(kap*δ)))
  exact_mod_cast hh

end
end KakeyaFormal.RawSampleTransfer

#print axioms KakeyaFormal.RawSampleTransfer.attach_filter_card
#print axioms KakeyaFormal.RawSampleTransfer.raw_fiber_card_le
#print axioms KakeyaFormal.RawSampleTransfer.raw_nonempty_fiber
#print axioms KakeyaFormal.RawSampleTransfer.raw_geometric_output_count
#print axioms KakeyaFormal.RawSampleTransfer.raw_geometric_fiber_count
#print axioms KakeyaFormal.RawSampleTransfer.raw_integer_fiber_bound
