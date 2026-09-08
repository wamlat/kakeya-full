import AngularGroupRestriction

/-! Actual low-mass group deletion after unique angular assignment. The mass
loss is bounded by the original tube count because the active groups are disjoint. -/
namespace KakeyaFormal.AngularGroupPruning
open AngularGroupRestriction
noncomputable section
open Classical

/-- Actual finite incidence mass in an original-indexed group. -/
def mass {α : Type*} {M : ℕ} (S : Fin M → Finset α) : ℝ := ∑ i, ((S i).card:ℝ)

/-- Keep only nonempty participating families with enough incidence per tube. -/
def kept {α γ : Type*} {M : ℕ} (groups : Finset γ) (S : γ → Fin M → Finset α)
    (threshold : ℝ) : Finset γ :=
  groups.filter (fun g => (active (S g)).Nonempty ∧ threshold*((active (S g)).card:ℝ) ≤ mass (S g))

theorem kept_subset {α γ : Type*} {M : ℕ} (groups : Finset γ)
    (S : γ → Fin M → Finset α) (threshold : ℝ) : kept groups S threshold ⊆ groups :=
  Finset.filter_subset _ _

theorem kept_spec {α γ : Type*} {M : ℕ} (groups : Finset γ)
    (S : γ → Fin M → Finset α) (threshold : ℝ) {g : γ} (hg : g ∈ kept groups S threshold) :
    0 < (active (S g)).card ∧ threshold*((active (S g)).card:ℝ) ≤ mass (S g) :=
  ⟨Finset.card_pos.mpr (Finset.mem_filter.mp hg).2.1,(Finset.mem_filter.mp hg).2.2⟩

theorem mass_zero_of_inactive {α : Type*} {M : ℕ} (S : Fin M → Finset α)
    (hS : ¬(active S).Nonempty) : mass S = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hnone : ¬(S i).Nonempty := fun hi => hS ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩⟩
  simp only [Finset.not_nonempty_iff_eq_empty.mp hnone,Finset.card_empty,Nat.cast_zero]

/-- Every deleted group has mass no greater than its actual threshold budget. -/
theorem deleted_mass_pointwise {α γ : Type*} {M : ℕ} (groups : Finset γ)
    (S : γ → Fin M → Finset α) (threshold : ℝ) {g : γ} (hg : g ∈ groups)
    (hnot : g ∉ kept groups S threshold) :
    mass (S g) ≤ threshold*((active (S g)).card:ℝ) := by
  by_cases hne : (active (S g)).Nonempty
  · have hbad : ¬threshold*((active (S g)).card:ℝ) ≤ mass (S g) :=
      fun hh => hnot (Finset.mem_filter.mpr ⟨hg,hne,hh⟩)
    exact (lt_of_not_ge hbad).le
  · rw [mass_zero_of_inactive (S g) hne,Finset.not_nonempty_iff_eq_empty.mp hne,
      Finset.card_empty,Nat.cast_zero,mul_zero]

/-- Actual total deleted group mass is at most threshold times the original
population, with the group count inequality proved from unique assignment. -/
theorem deleted_mass_bound {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (groups : Finset γ) (S : γ → Fin M → Finset α) (assign : Fin M → γ)
    (hunique : ∀ g i, (S g i).Nonempty → assign i = g)
    {threshold : ℝ} (ht : 0 ≤ threshold) :
    (∑ g ∈ groups.filter (fun g => g ∉ kept groups S threshold), mass (S g)) ≤ threshold*M := by
  have hcount := total_active_count (groups.filter (fun g => g ∉ kept groups S threshold)) S assign hunique
  have hcountR : (∑ g ∈ groups.filter (fun g => g ∉ kept groups S threshold), ((active (S g)).card:ℝ)) ≤ M := by
    exact_mod_cast hcount
  calc
    _ ≤ ∑ g ∈ groups.filter (fun g => g ∉ kept groups S threshold), threshold*((active (S g)).card:ℝ) :=
      Finset.sum_le_sum (fun g hg => deleted_mass_pointwise groups S threshold (Finset.mem_filter.mp hg).1
        (Finset.mem_filter.mp hg).2)
    _ = threshold*∑ g ∈ groups.filter (fun g => g ∉ kept groups S threshold), ((active (S g)).card:ℝ) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ threshold*M := mul_le_mul_of_nonneg_left hcountR ht

/-- The actual retained group mass satisfies the subtraction bound. -/
theorem retained_mass_bound {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (groups : Finset γ) (S : γ → Fin M → Finset α) (assign : Fin M → γ)
    (hunique : ∀ g i, (S g i).Nonempty → assign i = g)
    {threshold : ℝ} (ht : 0 ≤ threshold) :
    (∑ g ∈ groups, mass (S g))-threshold*M ≤ ∑ g ∈ kept groups S threshold, mass (S g) := by
  have hdel := deleted_mass_bound groups S assign hunique ht
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := groups)
    (fun g => g ∈ kept groups S threshold) (fun g => mass (S g))
  have hkeep : groups.filter (fun g => g ∈ kept groups S threshold) = kept groups S threshold := by
    ext g
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2,fun h => ⟨kept_subset groups S threshold h,h⟩⟩
  rw [hkeep] at hsplit
  linarith

/-- Low-group pruning of an actual assigned family with common original
upper density. At least three quarters of the retained mass budget and a
quantitative original tube population remain. -/
theorem prune_assigned_groups {γ : Type*} [DecidableEq γ] {k M : ℕ}
    (F : TubeFamily k M) (groups : Finset γ) (S : γ → Fin M → Finset (Cell k))
    (assign : Fin M → γ) (hunique : ∀ g i, (S g i).Nonempty → assign i = g)
    (hsub : ∀ g i, S g i ⊆ F.shade i) {δ lam rate : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hrate : 0 < rate)
    (hupper : ∀ i, ((F.shade i).card:ℝ) ≤ 2*lam/δ)
    (hmass : rate*(lam/δ)*(M:ℝ) ≤ ∑ g ∈ groups, mass (S g)) :
    let G := kept groups S ((rate/4)*(lam/δ))
    G ⊆ groups ∧
      (∀ g ∈ G, 0 < (active (S g)).card ∧
        (rate/4)*(lam/δ)*((active (S g)).card:ℝ) ≤ mass (S g)) ∧
      (3*rate/4)*(lam/δ)*(M:ℝ) ≤ ∑ g ∈ G, mass (S g) ∧
      (3*rate/8)*(M:ℝ) ≤ ∑ g ∈ G, ((active (S g)).card:ℝ) ∧
      (∑ g ∈ G, (active (S g)).card) ≤ M := by
  let G := kept groups S ((rate/4)*(lam/δ))
  have hret := retained_mass_bound groups S assign hunique (by positivity : 0 ≤ (rate/4)*(lam/δ))
  have hgoodmass : (3*rate/4)*(lam/δ)*(M:ℝ) ≤ ∑ g ∈ G, mass (S g) := by
    dsimp only [G]
    linarith
  have hgupper (g : γ) : mass (S g) ≤ (2*lam/δ)*((active (S g)).card:ℝ) := by
    rw [mass,← mass_eq]
    exact mass_upper F (S g) (hsub g) hupper
  have hsumupper : (∑ g ∈ G, mass (S g)) ≤
      (2*lam/δ)*∑ g ∈ G, ((active (S g)).card:ℝ) := by
    exact (Finset.sum_le_sum (fun g _ => hgupper g)).trans_eq (Finset.mul_sum _ _ _).symm
  have hcard : (3*rate/8)*(M:ℝ) ≤ ∑ g ∈ G, ((active (S g)).card:ℝ) := by
    have hmul := hgoodmass.trans hsumupper
    have hpos : 0 < 2*lam/δ := by positivity
    apply (mul_le_mul_iff_right₀ hpos).mp
    convert hmul using 1; ring
  exact ⟨kept_subset groups S _,fun _ hg => kept_spec groups S _ hg,hgoodmass,hcard,
    total_active_count G S assign hunique⟩

end
end KakeyaFormal.AngularGroupPruning
