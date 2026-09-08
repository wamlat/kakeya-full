import LegalSampleOutputs

/-! The actual original output population over one intermediate label has the
linear pivot count, without a total-output or intermediate-population factor. -/
namespace KakeyaFormal.ActualPivotFiberCount
open Finset LegalAngleSamples LegalAngleNormalization LegalLabeledSamples LegalSampleOutputs
open TransverseAngles PivotOutputCount
noncomputable section
open Classical

variable {n M : ℕ} {F : TubeFamily n M} {H : Finset (Cell n)} {δ lam kappa width : ℝ}

/-- A fixed original intermediate label leaves only the actual pivot-cell
choices of its normalized endpoint-pair population. The absent-label case is
empty; proof fields in its subtype create no extra multiplicity. -/
theorem output_count_at_intermediate (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (z : Cell n)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hkappa : 0 < kappa)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) :
    ((((S.samples a).image (output S a hkappa hwidth hadm)).filter (fun f => f.2=z)).card:ℝ) ≤
      4*boxConstant n ((n:ℝ)/2)*(1+2*width)/δ := by
  let O := ((S.samples a).image (output S a hkappa hwidth hadm)).filter (fun f => f.2=z)
  have hR : 0 < 1+2*width := by linarith
  by_cases hz : z ∈ intermediates S a
  · let i : ↥(intermediates S a) := ⟨z,hz⟩
    have hsub : O.image Prod.fst ⊆
        (pairSet S a i hkappa hwidth hadm).image LabeledPair.pivotLabel := by
      intro v hv
      obtain ⟨f,hf,rfl⟩ := mem_image.mp hv
      obtain ⟨hf,hfz⟩ := mem_filter.mp hf
      obtain ⟨p,hp,hpf⟩ := mem_image.mp hf
      have hm := encode_mem S a hkappa hwidth hadm ⟨p,hp⟩
      have ho := output_encode S a hkappa hwidth hadm ⟨p,hp⟩
      rcases he : encode S a hkappa hwidth hadm ⟨p,hp⟩ with ⟨j,s⟩
      rw [he] at hm ho
      have hji : j=i := by
        apply Subtype.ext
        change j.val=z
        have heq := ho.symm.trans hpf
        exact (congrArg Prod.snd heq).trans hfz
      subst j
      have hs := (mem_sigma.mp hm).2
      apply mem_image.mpr
      exact ⟨s,hs,congrArg Prod.fst (ho.symm.trans hpf)⟩
    have hinj : Set.InjOn Prod.fst (O : Set (Cell n × Cell n)) := by
      intro f hf g hg hfg
      apply Prod.ext hfg
      exact (mem_filter.mp hf).2.trans (mem_filter.mp hg).2.symm
    have hcard : (O.card:ℝ) ≤ (((pairSet S a i hkappa hwidth hadm).image LabeledPair.pivotLabel).card:ℝ) := by
      have hh := card_le_card hsub
      rw [card_image_of_injOn hinj] at hh
      exact_mod_cast hh
    have hc := pivot_output_count (pairSet S a i hkappa hwidth hadm) (div_pos hδ hR)
      ((div_le_one hR).mpr (by linarith)) (div_pos hkappa hR)
    exact (hcard.trans hc).trans_eq (by field_simp)
  · have hempty : O=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro f hf
      obtain ⟨hf,hfz⟩ := mem_filter.mp hf
      obtain ⟨p,hp,hpf⟩ := mem_image.mp hf
      have hmid : f.2=p.1 := by
        rw [← hpf,output_encode S a hkappa hwidth hadm ⟨p,hp⟩]
        rfl
      exact hz (mem_image.mpr ⟨p,hp,hmid.symm.trans hfz⟩)
    change (O.card:ℝ) ≤ _
    rw [hempty,card_empty,Nat.cast_zero]
    have hb := boxConstant_pos n ((n:ℝ)/2)
    positivity


/-- Every actual restriction of one angle's outputs with the intermediate
fixed inherits the same bound, with no assumed cardinality or loss factor. -/
theorem restricted_output_count (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (z : Cell n)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hkappa : 0 < kappa)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ)
    (outputs : Finset (Cell n × Cell n))
    (hsub : outputs ⊆ (S.samples a).image (output S a hkappa hwidth hadm))
    (hfixed : ∀ f ∈ outputs, f.2=z) :
    (outputs.card:ℝ) ≤ 4*boxConstant n ((n:ℝ)/2)*(1+2*width)/δ := by
  have hs : outputs ⊆ ((S.samples a).image (output S a hkappa hwidth hadm)).filter (fun f => f.2=z) := by
    intro f hf
    exact mem_filter.mpr ⟨hsub hf,hfixed f hf⟩
  have hc : (outputs.card:ℝ) ≤
      ((((S.samples a).image (output S a hkappa hwidth hadm)).filter (fun f => f.2=z)).card:ℝ) := by
    exact_mod_cast card_le_card hs
  exact hc.trans (output_count_at_intermediate S a z hδ hδ1 hkappa hwidth hadm)

end
end KakeyaFormal.ActualPivotFiberCount
