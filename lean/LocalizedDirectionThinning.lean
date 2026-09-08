import CapThinningGeometry
import SeparationColoring
import OccupancySelection

/-! Actual coarse direction thinning for a common spatial localization scale.
Complete original shadings survive on selected indices; no coarse-cell image
or desired separation/cap subfamily is assumed. -/
namespace KakeyaFormal.LocalizedDirectionThinning
open CapThinningGeometry SeparationColoring
noncomputable section
open Classical

/-- A cap bound at a coarser testing scale also bounds every smaller testing
scale with the same coefficient. Intermediate small caps use the old endpoint. -/
theorem cap_bound_smaller_scale {k M : ℕ} (F : TubeFamily k M) {δ r m A : ℝ}
    (hδ : 0 < δ) (hδr : δ ≤ r) (hr1 : r ≤ 1) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hcap : F.CapBound r m A) : F.CapBound δ m A := by
  intro center hunit u hu hu1
  have hr : 0 < r := hδ.trans_le hδr
  have hu0 : 0 < u := hδ.trans_le hu
  by_cases hru : r ≤ u
  · have hratio : u/r ≤ u/δ := div_le_div_of_nonneg_left hu0.le hδ hδr
    exact (hcap center hunit u hru hu1).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (div_nonneg hu0.le hr.le) hratio hm) hA)
  · have hcount : (Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction center ≤ u)).card ≤
        (Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction center ≤ r)).card := by
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2.trans (le_of_not_ge hru)⟩
    have hend := hcap center hunit r le_rfl hr1
    rw [div_self hr.ne',Real.one_rpow,mul_one] at hend
    have hone := Real.one_le_rpow ((one_le_div hδ).mpr hu) hm
    have hmul : A ≤ A*(u/δ)^m := by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hone hA)
    exact (Nat.cast_le.mpr hcount).trans (hend.trans hmul)

/-- The direction thinning and fixed-palette separation constants. -/
def retentionConstant (k : ℕ) (m : ℝ) : ℝ :=
  thinningRetentionConstant k m*(paletteSize k (2/((k:ℝ)+1)):ℝ)

def capConstant (k : ℕ) (m : ℝ) : ℝ := max 1 (thinningCapConstant k m)

theorem retentionConstant_pos (k : ℕ) (m : ℝ) : 0 < retentionConstant k m := by
  have hP := ProjectiveGeometry.packingConstant_ge_one k
  have hp := paletteSize_pos k (2/((k:ℝ)+1))
  unfold retentionConstant thinningRetentionConstant
  positivity

theorem capConstant_ge_one (k : ℕ) (m : ℝ) : 1 ≤ capConstant k m := le_max_left _ _

/-- Construct an actually target-separated, cap-preserving family of complete
original shadings. The target can be above or below the original direction mesh. -/
theorem thin_to_scale {k M : ℕ} (F : TubeFamily (k+1) M) {δ target m A : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (htarget : 0 < target) (htarget1 : target ≤ 1)
    (hm : 0 ≤ m) (hA : 1 ≤ A) (hcap : F.CapBound δ m A) :
    ∃ N : ℕ, ∃ e : Fin N → Fin M, Function.Injective e ∧
      ∃ G : TubeFamily (k+1) N,
        (M:ℝ)/(retentionConstant k m*A*((max δ target)/δ)^m) ≤ (N:ℝ) ∧
        (∀ i, G.tube i = F.tube (e i)) ∧ (∀ i, G.shade i = F.shade (e i)) ∧
        G.Separated target ∧ G.CapBound target m (capConstant k m) ∧
        G.unionCells ⊆ F.unionCells := by
  let r := max δ target
  have hr : 0 < r := hδ.trans_le (le_max_left _ _)
  have hr1 : r ≤ 1 := max_le hδ1 htarget1
  obtain ⟨kept,hcount,hsep,hcaps⟩ := full_cap_thinning F hδ (le_max_left _ _) hr1 hm hA hcap
  let e₀ : Fin kept.card → Fin M := fun i => (kept.equivFin.symm i).val
  have he₀ : Function.Injective e₀ := Subtype.val_injective.comp kept.equivFin.symm.injective
  have hemem : ∀ i, e₀ i ∈ kept := fun i => (kept.equivFin.symm i).property
  let H : TubeFamily (k+1) kept.card := {tube := fun i => F.tube (e₀ i),shade := fun i => F.shade (e₀ i)}
  have hσ : 0 < 2/((k:ℝ)+1) := by positivity
  have hHsep : H.Separated ((2/((k:ℝ)+1))*target) := by
    intro i j hij
    exact (mul_le_mul_of_nonneg_left (le_max_right δ target) hσ.le).trans
      (hsep _ (hemem i) _ (hemem j) (fun h => hij (he₀ h)))
  have hHcap : H.CapBound r m (capConstant k m) := by
    intro center _ u hru hu1
    have hcard : (Finset.univ.filter (fun i => projectiveDistance (H.tube i).direction center ≤ u)).card ≤
        (kept.filter (fun i => projectiveDistance (F.tube i).direction center ≤ u)).card := by
      apply Finset.card_le_card_of_injOn e₀
      · intro i hi
        exact Finset.mem_filter.mpr ⟨hemem i,(Finset.mem_filter.mp hi).2⟩
      · exact fun _ _ _ _ h => he₀ h
    exact (Nat.cast_le.mpr hcard).trans ((hcaps center u hru hu1).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (div_nonneg (hr.le.trans hru) hr.le) m)))
  have hHsmall := cap_bound_smaller_scale H htarget (le_max_right δ target) hr1 hm
    (zero_le_one.trans (capConstant_ge_one k m)) hHcap
  obtain ⟨color,hcolor⟩ := full_separation_coloring H htarget hσ hHsep
  obtain ⟨c,hc⟩ := OccupancySelection.weighted_class_selection
    (Finset.univ : Finset (Fin kept.card)) (fun _ => (1:ℝ))
    (paletteSize_pos k (2/((k:ℝ)+1))) color
  have hcN : (kept.card:ℝ)/(paletteSize k (2/((k:ℝ)+1)):ℝ) ≤ ((colorClass color c).card:ℝ) := by
    simpa only [colorClass,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hc
  let e : Fin (colorClass color c).card → Fin M := fun i => e₀ (classIndex color c i)
  let G := classFamily H color c
  have he : Function.Injective e := he₀.comp (classIndex_injective color c)
  have hN := (div_le_div_of_nonneg_right hcount (by positivity : (0:ℝ) ≤ (paletteSize k (2/((k:ℝ)+1)):ℝ))).trans hcN
  refine ⟨(colorClass color c).card,e,he,G,?_,fun _ => rfl,fun _ => rfl,
    classFamily_separated H color hcolor c,classFamily_cap_bound H color hHsmall c,?_⟩
  · calc
      _ = ((M:ℝ)/(thinningRetentionConstant k m*A*(r/δ)^m))/(paletteSize k (2/((k:ℝ)+1)):ℝ) := by
        unfold retentionConstant
        rw [div_div]
        congr 1
        ring
      _ ≤ _ := hN
  · intro z hz
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
    exact F.shade_subset_union (e i) hi

/-- A localization-scale dilation loses only rho^m/A of the original family.
The selected tubes still retain their entire actual localized shadings. -/
theorem thin_at_localized_scale {k M : ℕ} (F : TubeFamily (k+1) M) {δ rho L m A : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hrhoL : rho ≤ L) (hδL : δ ≤ L) (hm : 0 ≤ m) (hA : 1 ≤ A) (hcap : F.CapBound δ m A) :
    ∃ N : ℕ, ∃ e : Fin N → Fin M, Function.Injective e ∧
      ∃ G : TubeFamily (k+1) N,
        ((M:ℝ)*rho^m)/(retentionConstant k m*A) ≤ (N:ℝ) ∧
        (∀ i, G.tube i = F.tube (e i)) ∧ (∀ i, G.shade i = F.shade (e i)) ∧
        G.Separated (δ/L) ∧ G.CapBound (δ/L) m (capConstant k m) ∧
        G.unionCells ⊆ F.unionCells := by
  have hL : 0 < L := hrho.trans_le hrhoL
  obtain ⟨N,e,he,G,hN,htubes,hshades,hsep,hcaps,hU⟩ := thin_to_scale F hδ hδ1
    (div_pos hδ hL) ((div_le_one hL).mpr hδL) hm hA hcap
  refine ⟨N,e,he,G,?_,htubes,hshades,hsep,hcaps,hU⟩
  have hratio : (max δ (δ/L))/δ ≤ 1/rho := by
    apply (div_le_iff₀ hδ).mpr
    apply max_le
    · exact le_mul_of_one_le_left hδ.le ((one_le_div hrho).mpr hrho1)
    · have hh := div_le_div_of_nonneg_left hδ.le hrho hrhoL
      convert hh using 1; first | rfl | ring
  have hR : 0 < (max δ (δ/L))/δ := div_pos (hδ.trans_le (le_max_left _ _)) hδ
  have hp := Real.rpow_le_rpow hR.le hratio hm
  have hCA : 0 < retentionConstant k m*A := mul_pos (retentionConstant_pos k m) (zero_lt_one.trans_le hA)
  have hd := div_le_div_of_nonneg_left (show (0:ℝ) ≤ M from Nat.cast_nonneg M)
    (mul_pos hCA (Real.rpow_pos_of_pos hR m)) (mul_le_mul_of_nonneg_left hp hCA.le)
  calc
    _ = (M:ℝ)/(retentionConstant k m*A*(1/rho)^m) := by
      rw [one_div,Real.inv_rpow hrho.le]
      field_simp
    _ ≤ _ := hd.trans hN

end
end KakeyaFormal.LocalizedDirectionThinning
