import FiniteLocalizedFamily

/-! One initial fixed homothety places every original tube shading in a
unit-radius ball around its own base. All original cell cardinalities are
preserved, and the cap coefficient does not increase. -/
namespace KakeyaFormal.SeedCoverNormalization
open LocalizedGridTubes LocalizedDirectionThinning Rescaling
noncomputable section
open Classical

def coverFactor (width : ℝ) : ℝ := 1+localWidth width

theorem coverFactor_ge_one (width : ℝ) : 1 ≤ coverFactor width := by
  have hW := (localWidth_pos width).le
  unfold coverFactor
  linarith

theorem coverFactor_pos (width : ℝ) : 0 < coverFactor width := zero_lt_one.trans_le (coverFactor_ge_one width)

def family {k M : ℕ} (F : TubeFamily k M) (δ width : ℝ) : TubeFamily k M :=
  Rescaling.family F (coverFactor width) δ 0 (fun _ => 0)

theorem original_base_cover {k M : ℕ} (F : TubeFamily k M) {δ width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hadm : F.Admissible width δ) :
    ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (F.tube i).base ≤ coverFactor width := by
  intro i z hz
  obtain ⟨t,ht,hd⟩ := hadm i z hz
  have htube : dist ((F.tube i).axisPoint t) (F.tube i).base ≤ 1 := by
    have hh := (F.tube i).axisPoint_distance t 0
    simp only [UnitTube.axisPoint,zero_smul,add_zero,sub_zero,abs_of_nonneg ht.1] at hh
    exact hh.trans_le ht.2
  have hwidth : width*δ ≤ localWidth width := by
    calc
      _ ≤ localWidth width*δ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le
      _ ≤ localWidth width := mul_le_of_le_one_right (localWidth_pos width).le hδ1
  have htri := dist_triangle (cellCenter δ z) ((F.tube i).axisPoint t) (F.tube i).base
  unfold coverFactor
  linarith

/-- Exact original cell centers fit a unit ball after the shared fixed map. -/
theorem family_cover {k M : ℕ} (F : TubeFamily k M) {δ width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hadm : F.Admissible width δ) :
    ∀ i z, z ∈ (family F δ width).shade i →
      dist (cellCenter (δ/coverFactor width) z) ((family F δ width).tube i).base ≤ 1 := by
  intro i z hz
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  change dist (cellCenter (δ/coverFactor width) (shiftLabel 0 q))
    (rescale (coverFactor width) (cellCenter δ 0) ((F.tube i).axisPoint 0)) ≤ 1
  rw [← rescale_grid,rescale_distance (coverFactor_pos width)]
  simp only [UnitTube.axisPoint,zero_smul,add_zero]
  exact (div_le_one (coverFactor_pos width)).mpr (original_base_cover F hδ hδ1 hadm i q hq)

theorem family_admissible {k M : ℕ} (F : TubeFamily k M) {δ width : ℝ}
    (hδ : 0 < δ) (hadm : F.Admissible width δ) :
    (family F δ width).Admissible (localWidth width) (δ/coverFactor width) := by
  apply rescaled_admissible F (coverFactor_pos width)
  intro i z hz
  obtain ⟨t,ht,hd⟩ := hadm i z hz
  refine ⟨t,⟨by simpa using ht.1,by simpa using ht.2.trans (coverFactor_ge_one width)⟩,?_⟩
  exact hd.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le)

theorem family_comparable {k M : ℕ} (F : TubeFamily k M) {δ width lam : ℝ}
    (hcomp : F.Comparable δ lam) :
    (family F δ width).Comparable (δ/coverFactor width) (lam/coverFactor width) :=
  rescaled_comparable F (coverFactor_pos width).ne' 0 _ hcomp

theorem family_cap_bound {k M : ℕ} (F : TubeFamily k M) {δ width m A : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m) (hA : 0 ≤ A) (hcap : F.CapBound δ m A) :
    (family F δ width).CapBound (δ/coverFactor width) m A := by
  have hh := cap_bound_smaller_scale F (div_pos hδ (coverFactor_pos width))
    (div_le_self hδ.le (coverFactor_ge_one width)) hδ1 hm hA hcap
  exact hh

theorem family_union_card {k M : ℕ} (F : TubeFamily k M) (δ width : ℝ) :
    (family F δ width).unionCells.card = F.unionCells.card := rescaled_union_card F _ _ _ _

theorem normalized_scale {δ width : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    0 < δ/coverFactor width ∧ δ/coverFactor width ≤ 1 :=
  ⟨div_pos hδ (coverFactor_pos width),(div_le_one (coverFactor_pos width)).mpr (hδ1.trans (coverFactor_ge_one width))⟩

theorem normalized_density {lam width : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    0 < lam/coverFactor width ∧ lam/coverFactor width ≤ 1 :=
  ⟨div_pos hlam (coverFactor_pos width),(div_le_one (coverFactor_pos width)).mpr (hlam1.trans (coverFactor_ge_one width))⟩

end
end KakeyaFormal.SeedCoverNormalization
