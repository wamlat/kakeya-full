import SpatialAngular

/-! Proportional restoration after a deterministic spatial partition. The loss
is pointwise and therefore compatible with later weighted measurable atoms. -/
namespace KakeyaFormal.SpatialSplitting
open KakeyaFormal.AngularAssignment KakeyaFormal.AngularDecomposition
noncomputable section

/-- The actual label fiber of an indexed direction subset. -/
def fiber {M : ℕ} {γ : Type*} [DecidableEq γ]
    (parent : Finset (Fin M)) (label : Fin M → γ) (q : γ) : Finset (Fin M) :=
  parent.filter (fun i => label i = q)

/-- Restore broadness by retaining a spatial fiber only if it contains at least
1/(4B) of its angular parent. -/
def restore {M : ℕ} {γ : Type*} [DecidableEq γ]
    (parent : Finset (Fin M)) (label : Fin M → γ) (B : ℝ) (q : γ) : Finset (Fin M) := by
  classical
  exact if (parent.card : ℝ) ≤ 4*B*((fiber parent label q).card : ℝ)
    then fiber parent label q else ∅

theorem restore_subset_fiber {M : ℕ} {γ : Type*} [DecidableEq γ]
    (parent : Finset (Fin M)) (label : Fin M → γ) (B : ℝ) (q : γ) :
    restore parent label B q ⊆ fiber parent label q := by
  classical
  unfold restore
  split_ifs
  · exact le_rfl
  · exact Finset.empty_subset _

theorem restore_subset_parent {M : ℕ} {γ : Type*} [DecidableEq γ]
    (parent : Finset (Fin M)) (label : Fin M → γ) (B : ℝ) (q : γ) :
    restore parent label B q ⊆ parent :=
  (restore_subset_fiber parent label B q).trans (Finset.filter_subset _ _)

theorem restore_label {M : ℕ} {γ : Type*} [DecidableEq γ]
    (parent : Finset (Fin M)) (label : Fin M → γ) (B : ℝ) (q : γ)
    {i : Fin M} (hi : i ∈ restore parent label B q) : label i = q :=
  (Finset.mem_filter.mp (restore_subset_fiber parent label B q hi)).2

/-- The restoration loses at most one quarter of the parent population at each
point, using the proved bound on the number of occupied spatial labels. -/
theorem pointwise_restoration_mass {M : ℕ} {γ : Type*} [DecidableEq γ]
    (parent : Finset (Fin M)) (label : Fin M → γ) {B : ℝ} (hB : 0 < B)
    (hcount : ((parent.image label).card : ℝ) ≤ B) :
    (3/4:ℝ)*(parent.card : ℝ) ≤
      ∑ q ∈ parent.image label, ((restore parent label B q).card : ℝ) := by
  classical
  have hsum : (∑ q ∈ parent.image label, ((fiber parent label q).card : ℝ)) = parent.card := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := parent) (t := parent.image label) (f := label)
      (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩)
    exact_mod_cast h.symm
  have hcal : (∑ _q ∈ parent.image label, (parent.card : ℝ)) ≤
      B*(∑ q ∈ parent.image label, ((fiber parent label q).card : ℝ)) := by
    rw [hsum]
    simp only [Finset.sum_const,nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)
  have h := threshold_retains_three_quarters (parent.image label)
    (fun _ => (parent.card : ℝ)) (fun q => ((fiber parent label q).card : ℝ)) hB
    (fun _ _ => Nat.cast_nonneg _) hcal
  rw [hsum] at h
  have hcard (q : γ) : ((restore parent label B q).card : ℝ) =
      if (parent.card : ℝ) ≤ 4*B*((fiber parent label q).card : ℝ)
        then ((fiber parent label q).card : ℝ) else 0 := by
    unfold restore
    split_ifs <;> simp
  simpa only [hcard] using h

/-- Summing over any finite set containing the occupied labels preserves that
pointwise mass bound. Unoccupied labels contribute zero or harmlessly nonnegative mass. -/
theorem pointwise_restoration_mass_on {M : ℕ} {γ : Type*} [DecidableEq γ]
    (parent : Finset (Fin M)) (label : Fin M → γ) (labels : Finset γ)
    (hlabels : parent.image label ⊆ labels) {B : ℝ} (hB : 0 < B)
    (hcount : ((parent.image label).card : ℝ) ≤ B) :
    (3/4:ℝ)*(parent.card : ℝ) ≤
      ∑ q ∈ labels, ((restore parent label B q).card : ℝ) :=
  (pointwise_restoration_mass parent label hB hcount).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hlabels (fun _ _ _ => Nat.cast_nonneg _))

/-- Every retained spatial subset inherits actual projective broadness with
only the fixed factor4B in the error constant. -/
theorem restore_broad {k M : ℕ} {γ : Type*} [DecidableEq γ]
    (F : TubeFamily k M) (parent : Finset (Fin M)) (label : Fin M → γ) (B : ℝ) (q : γ)
    {δ beta tau K : ℝ} (hδ : 0 ≤ δ) (htau : 0 < tau) (hK : 0 ≤ K)
    (hbroad : Broad F parent δ beta tau K) :
    Broad F (restore parent label B q) δ beta tau (K*(4*B)) := by
  classical
  unfold restore
  split_ifs with hgood
  · exact broad_proportional_subset F (Finset.filter_subset _ _) hδ htau hK hgood hbroad
  · intro center r hr
    simp [cap]

/-- Only originally occupied labels can support a retained spatial subset. -/
theorem occupied_restored_count {M : ℕ} {γ : Type*} [DecidableEq γ]
    (parent : Finset (Fin M)) (label : Fin M → γ) (B : ℝ) (labels : Finset γ) :
    (labels.filter (fun q => (restore parent label B q).Nonempty)).card ≤ (parent.image label).card := by
  classical
  apply Finset.card_le_card
  intro q hq
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hq).2
  exact Finset.mem_image.mpr ⟨i,restore_subset_parent parent label B q hi,restore_label parent label B q hi⟩

end
end KakeyaFormal.SpatialSplitting
