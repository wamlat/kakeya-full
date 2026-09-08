import MeasurableAngularGroups

/-! Actual low-mass group deletion after unique angular assignment. The mass
loss is bounded by the original tube count because the active groups are disjoint. -/
namespace KakeyaFormal.MeasurableAngularPruning
open MeasurableAngularGroups MeasureTheory
open scoped ENNReal
noncomputable section
open Classical

/-- Actual finite incidence mass in an original-indexed group. -/
def mass {α : Type*} [MeasurableSpace α] {M : ℕ} (μ : Measure α) (S : Fin M → Set α) : ℝ := ∑ i, μ.real (S i)

/-- Keep only nonempty participating families with enough incidence per tube. -/
def kept {α γ : Type*} [MeasurableSpace α] {M : ℕ} (μ : Measure α) (groups : Finset γ) (S : γ → Fin M → Set α)
    (threshold : ℝ) : Finset γ :=
  groups.filter (fun g => (active (S g)).Nonempty ∧ threshold*((active (S g)).card:ℝ) ≤ mass μ (S g))

theorem kept_subset {α γ : Type*} [MeasurableSpace α] {M : ℕ} (μ : Measure α) (groups : Finset γ)
    (S : γ → Fin M → Set α) (threshold : ℝ) : kept μ groups S threshold ⊆ groups :=
  Finset.filter_subset _ _

theorem kept_spec {α γ : Type*} [MeasurableSpace α] {M : ℕ} (μ : Measure α) (groups : Finset γ)
    (S : γ → Fin M → Set α) (threshold : ℝ) {g : γ} (hg : g ∈ kept μ groups S threshold) :
    0 < (active (S g)).card ∧ threshold*((active (S g)).card:ℝ) ≤ mass μ (S g) :=
  ⟨Finset.card_pos.mpr (Finset.mem_filter.mp hg).2.1,(Finset.mem_filter.mp hg).2.2⟩

theorem mass_zero_of_inactive {α : Type*} [MeasurableSpace α] {M : ℕ} (μ : Measure α) (S : Fin M → Set α)
    (hS : ¬(active S).Nonempty) : mass μ S = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hnone : ¬(S i).Nonempty := fun hi => hS ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  simp only [Set.not_nonempty_iff_eq_empty.mp hnone,measureReal_empty]

/-- Every deleted group has mass no greater than its actual threshold budget. -/
theorem deleted_mass_pointwise {α γ : Type*} [MeasurableSpace α] {M : ℕ} (μ : Measure α) (groups : Finset γ)
    (S : γ → Fin M → Set α) (threshold : ℝ) {g : γ} (hg : g ∈ groups)
    (hnot : g ∉ kept μ groups S threshold) :
    mass μ (S g) ≤ threshold*((active (S g)).card:ℝ) := by
  by_cases hne : (active (S g)).Nonempty
  · have hbad : ¬threshold*((active (S g)).card:ℝ) ≤ mass μ (S g) :=
      fun hh => hnot (Finset.mem_filter.mpr ⟨hg,hne,hh⟩)
    exact (lt_of_not_ge hbad).le
  · rw [mass_zero_of_inactive μ (S g) hne,Finset.not_nonempty_iff_eq_empty.mp hne,
      Finset.card_empty,Nat.cast_zero,mul_zero]

/-- Actual total deleted group mass is at most threshold times the original
population, with the group count inequality proved from unique assignment. -/
theorem deleted_mass_bound {α γ : Type*} [MeasurableSpace α] [DecidableEq γ] {M : ℕ}
    (μ : Measure α) (groups : Finset γ) (S : γ → Fin M → Set α) (assign : Fin M → γ)
    (hunique : ∀ g i, (S g i).Nonempty → assign i = g)
    {threshold : ℝ} (ht : 0 ≤ threshold) :
    (∑ g ∈ groups.filter (fun g => g ∉ kept μ groups S threshold), mass μ (S g)) ≤ threshold*M := by
  have hcount := total_active_count (groups.filter (fun g => g ∉ kept μ groups S threshold)) S assign hunique
  have hcountR : (∑ g ∈ groups.filter (fun g => g ∉ kept μ groups S threshold), ((active (S g)).card:ℝ)) ≤ M := by
    exact_mod_cast hcount
  calc
    _ ≤ ∑ g ∈ groups.filter (fun g => g ∉ kept μ groups S threshold), threshold*((active (S g)).card:ℝ) :=
      Finset.sum_le_sum (fun g hg => deleted_mass_pointwise μ groups S threshold (Finset.mem_filter.mp hg).1
        (Finset.mem_filter.mp hg).2)
    _ = threshold*∑ g ∈ groups.filter (fun g => g ∉ kept μ groups S threshold), ((active (S g)).card:ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ threshold*M := mul_le_mul_of_nonneg_left hcountR ht

/-- The actual retained group mass satisfies the subtraction bound. -/
theorem retained_mass_bound {α γ : Type*} [MeasurableSpace α] [DecidableEq γ] {M : ℕ}
    (μ : Measure α) (groups : Finset γ) (S : γ → Fin M → Set α) (assign : Fin M → γ)
    (hunique : ∀ g i, (S g i).Nonempty → assign i = g)
    {threshold : ℝ} (ht : 0 ≤ threshold) :
    (∑ g ∈ groups, mass μ (S g))-threshold*M ≤ ∑ g ∈ kept μ groups S threshold, mass μ (S g) := by
  have hdel := deleted_mass_bound μ groups S assign hunique ht
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := groups)
    (fun g => g ∈ kept μ groups S threshold) (fun g => mass μ (S g))
  have hkeep : groups.filter (fun g => g ∈ kept μ groups S threshold) = kept μ groups S threshold := by
    ext g
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨kept_subset μ groups S threshold h,h⟩⟩
  rw [hkeep] at hsplit
  linarith

/-- Low-mass deletion uses actual measured shadings. The common mass scale
is an absolute per-tube volume; no per-tube lower mass is assumed for the
retained group shadings. -/
theorem prune_assigned_groups {X γ : Type*} [MeasurableSpace X] [DecidableEq γ] {M : ℕ}
    (μ : Measure X) (Y : Fin M → Set X) (groups : Finset γ) (S : γ → Fin M → Set X)
    (assign : Fin M → γ) (hunique : ∀ g i, (S g i).Nonempty → assign i = g)
    (hsub : ∀ g i, S g i ⊆ Y i) (hfin : ∀ i, μ (Y i) ≠ ∞) {lam rate : ℝ}
    (hlam : 0 < lam) (hrate : 0 < rate) (hupper : ∀ i, μ.real (Y i) ≤ 2*lam)
    (hmass : rate*lam*(M:ℝ) ≤ ∑ g ∈ groups, mass μ (S g)) :
    let G := kept μ groups S ((rate/4)*lam)
    G ⊆ groups ∧
      (∀ g ∈ G, 0 < (active (S g)).card ∧
        (rate/4)*lam*((active (S g)).card:ℝ) ≤ mass μ (S g)) ∧
      (3*rate/4)*lam*(M:ℝ) ≤ ∑ g ∈ G, mass μ (S g) ∧
      (3*rate/8)*(M:ℝ) ≤ ∑ g ∈ G, ((active (S g)).card:ℝ) ∧
      (∑ g ∈ G, (active (S g)).card) ≤ M := by
  let G := kept μ groups S ((rate/4)*lam)
  have hret := retained_mass_bound μ groups S assign hunique (by positivity : 0 ≤ (rate/4)*lam)
  have hgoodmass : (3*rate/4)*lam*(M:ℝ) ≤ ∑ g ∈ G, mass μ (S g) := by
    dsimp only [G]
    linarith
  have hgupper (g : γ) : mass μ (S g) ≤ (2*lam)*((active (S g)).card:ℝ) :=
    MeasurableAngularGroups.mass_upper μ Y (S g) hfin (hsub g) hupper
  have hsumupper : (∑ g ∈ G, mass μ (S g)) ≤
      (2*lam)*∑ g ∈ G, ((active (S g)).card:ℝ) :=
    (Finset.sum_le_sum (fun g _ => hgupper g)).trans_eq (Finset.mul_sum _ _ _).symm
  have hcard : (3*rate/8)*(M:ℝ) ≤ ∑ g ∈ G, ((active (S g)).card:ℝ) := by
    have hmul := hgoodmass.trans hsumupper
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2*lam)).mp
    convert hmul using 1; ring
  exact ⟨kept_subset μ groups S _,fun _ hg => kept_spec μ groups S _ hg,hgoodmass,hcard,
    total_active_count G S assign hunique⟩

end
end KakeyaFormal.MeasurableAngularPruning
