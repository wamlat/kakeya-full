import Coarsening
import CapThinningGeometry
import CumulativeEstimate

/-! Actual cap-preserving coarse tube families, with explicit reindexing and
geometric/cumulative-density data for applying the proved base estimate. -/
namespace KakeyaFormal.CoarseFamily
open Coarsening CapThinningGeometry
noncomputable section
open Classical

/-- Full direction thinning and physical coarse-cell realization combined in
one actual TubeFamily; all geometric and count properties are constructed. -/
theorem thinned_coarse_family {M k : ℕ} (F : TubeFamily (k+1) M)
    {δ r m A width R : ℝ} (hδ : 0 < δ) (hdr : δ ≤ r) (hr1 : r ≤ 1)
    (hm : 0 ≤ m) (hA : 1 ≤ A) (hw : 0 ≤ width)
    (hadm : F.Admissible width δ) (hbounded : F.Bounded R) (hcap : F.CapBound δ m A) :
    ∃ N : ℕ, ∃ e : Fin N → Fin M, Function.Injective e ∧
      ∃ G : TubeFamily (k+1) N,
        (M:ℝ)/(thinningRetentionConstant k m*A*(r/δ)^m) ≤ (N:ℝ) ∧
        (∀ i, G.tube i = F.tube (e i)) ∧
        (∀ i, G.shade i = (F.shade (e i)).image (coarseLabel δ r)) ∧
        G.Admissible (width+(k+1:ℕ)/2) r ∧
        G.Separated ((2/((k:ℝ)+1))*r) ∧ G.Bounded R ∧
        G.CapBound r m (max 1 (thinningCapConstant k m)) ∧
        G.unionCells ⊆ F.unionCells.image (coarseLabel δ r) := by
  obtain ⟨kept,hcount,hsep,hcaps⟩ := full_cap_thinning F hδ hdr hr1 hm hA hcap
  let e : Fin kept.card → Fin M := fun i => (kept.equivFin.symm i).val
  have he : Function.Injective e := Subtype.val_injective.comp kept.equivFin.symm.injective
  have hemem : ∀ i, e i ∈ kept := fun i => (kept.equivFin.symm i).property
  let G : TubeFamily (k+1) kept.card := {
    tube := fun i => F.tube (e i)
    shade := fun i => (F.shade (e i)).image (coarseLabel δ r)
  }
  have hsub : G.unionCells ⊆ F.unionCells.image (coarseLabel δ r) := by
    intro z hz
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨q,Finset.mem_biUnion.mpr ⟨e i,Finset.mem_univ _,hq⟩,rfl⟩
  refine ⟨kept.card,e,he,G,hcount,fun _ => rfl,fun _ => rfl,?_,?_,?_,?_,hsub⟩
  · intro i q hq
    exact family_admissible F hδ hdr hw hadm (e i) q hq
  · intro i j hij
    exact hsep (e i) (hemem i) (e j) (hemem j) (fun h => hij (he h))
  · intro i
    exact hbounded (e i)
  · intro center _ u hru hu1
    let S := Finset.univ.filter (fun i => projectiveDistance (G.tube i).direction center ≤ u)
    have hi : S.image e ⊆ kept.filter (fun i => projectiveDistance (F.tube i).direction center ≤ u) := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_filter.mpr ⟨hemem i,(Finset.mem_filter.mp hi).2⟩
    have hc : (S.card:ℝ) ≤ ((kept.filter (fun i => projectiveDistance (F.tube i).direction center ≤ u)).card:ℝ) := by
      have hh := Finset.card_le_card hi
      rw [Finset.card_image_of_injective _ he] at hh
      exact_mod_cast hh
    have hh := hc.trans (hcaps center u hru hu1)
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right 1 (thinningCapConstant k m))
      (Real.rpow_nonneg (div_nonneg ((hδ.trans_le hdr).le.trans hru) (hδ.trans_le hdr).le) m))

/-- Each selected tube's original fine density transfers to its actual coarse
shading at a fixed geometric loss. This uses the proved local fiber count. -/
theorem selected_coarse_density {M N k : ℕ} (F : TubeFamily k M) (G : TubeFamily k N)
    (e : Fin N → Fin M) {δ r width s : ℝ} (hδ : 0 < δ) (hdr : δ ≤ r) (hw : 0 ≤ width)
    (hadm : F.Admissible width δ)
    (hshades : ∀ i, G.shade i = (F.shade (e i)).image (coarseLabel δ r))
    (hdense : ∀ i, s ≤ δ*((F.shade i).card:ℝ)) :
    ∀ i, s/fiberConstant k width ≤ r*((G.shade i).card:ℝ) := by
  intro i
  have hc := coarse_count_lower (F.tube (e i)) (F.shade (e i)) hδ hdr hw (hadm (e i))
  rw [← hshades i] at hc
  have hK := fiberConstant_pos k hw
  have hr := hδ.trans_le hdr
  have hm := (div_le_iff₀ (mul_pos hK hr)).mp hc
  apply (div_le_iff₀ hK).mpr
  nlinarith [hdense (e i)]


/-- Exact scale arithmetic after cap-preserving thinning, with all constants
and the single inverse cap coefficient retained. -/
lemma coarse_estimate_identity {δ r s m d eps p c A B K T M : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hs : 0 ≤ s) (hK : 0 < K) :
    c*B⁻¹*r^(m-d+eps)*(s/K)^p*(M/(T*A*(r/δ)^m)) =
      (c*B⁻¹/(K^p*T))*A⁻¹*δ^m*r^(-d+eps)*s^p*M := by
  have hscale : r^(m-d+eps) = r^m*r^(-d+eps) := by
    rw [← Real.rpow_add hr]
    congr 1
    ring
  rw [hscale,Real.div_rpow hs hK.le,Real.div_rpow hr.le hδ.le]
  have hrpow : r^m ≠ 0 := (Real.rpow_pos_of_pos hr m).ne'
  field_simp

/-- Applying the base estimate to the constructed coarse family. Its constant
is fixed before every scale, cap coefficient, density and tube family. -/
theorem coarse_union_estimate {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p)
    (width R : ℝ) (hw : 0 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) {δ r s A : ℝ},
      0 < δ → δ ≤ r → r ≤ 1 → 0 ≤ s → 1 ≤ A →
      F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, s ≤ δ*((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^m*r^(-d+eps)*s^p*M ≤ ((F.unionCells.image (coarseLabel δ r)).card:ℝ) := by
  let W := width+(k+1:ℕ)/2
  let geom : Normalization := {
    width := max 1 W
    separation := 2/((k:ℝ)+1)
    radius := max 1 R
    width_pos := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    separation_pos := by positivity
    radius_pos := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  }
  let K := fiberConstant (k+1) width
  let T := thinningRetentionConstant k m
  let B := max 1 (thinningCapConstant k m)
  have hK : 0 < K := fiberConstant_pos (k+1) hw
  have hT : 0 < T := by
    have hpack := ProjectiveGeometry.packingConstant_ge_one k
    dsimp [T,thinningRetentionConstant]
    positivity
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨c,hc,hestimate⟩ := hbase.to_cumulative hp geom eps heps
  refine ⟨c*B⁻¹/(K^p*T),by positivity,?_⟩
  intro M F δ r s A hδ hdr hr1 hs hA hadm hbounded hcap hdense
  have hr := hδ.trans_le hdr
  obtain ⟨N,e,_,G,hN,_,hshades,hGadm,hGsep,hGbound,hGcap,hU⟩ :=
    thinned_coarse_family F hδ hdr hr1 hm hA hw hadm hbounded hcap
  have hdensity := selected_coarse_density F G e hδ hdr hw hadm hshades hdense
  have hGadmissible : G.Admissible geom.width r := by
    intro i q hq
    obtain ⟨t,ht,hqt⟩ := hGadm i q hq
    refine ⟨t,ht,hqt.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right 1 W) hr.le
  have hGbounded : G.Bounded geom.radius := fun i => (hGbound i).trans (le_max_right _ _)
  have hcum : (s/K)*N ≤ r*∑ i, ((G.shade i).card:ℝ) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdensity i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      ← Finset.mul_sum,mul_comm] using hh
  let H : CumulativeConfiguration (k+1) geom m := {
    M := N
    δ := r
    s := s/K
    A := B
    family := G
    scale_pos := hr
    scale_le_one := hr1
    density_nonneg := div_nonneg hs hK.le
    cap_ge_one := le_max_left _ _
    admissible := hGadmissible
    separated := hGsep
    bounded := hGbounded
    cap_bound := hGcap
    cumulative := hcum
  }
  have hh := hestimate H
  change c*B⁻¹*r^(m-d+eps)*(s/K)^p*N ≤ (G.unionCells.card:ℝ) at hh
  have hcoef : 0 ≤ c*B⁻¹*r^(m-d+eps)*(s/K)^p := by positivity
  have hNbound := mul_le_mul_of_nonneg_left hN hcoef
  have hid := coarse_estimate_identity (m := m) (d := d) (eps := eps) (p := p)
    (c := c) (A := A) (B := B) (T := T) (M := (M:ℝ)) hδ hr hs hK
  rw [hid] at hNbound
  exact (hNbound.trans hh).trans (by exact_mod_cast Finset.card_le_card hU)

end
end KakeyaFormal.CoarseFamily
