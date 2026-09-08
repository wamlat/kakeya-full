import AngularAssignment

/-! Actual finite assignment and pointwise restoration with arbitrary
nonnegative atom weights, including exact measurable atom volumes. -/
namespace KakeyaFormal.WeightedAngularAssignment
open AngularAssignment
noncomputable section
open Classical

theorem sum_weighted_row_cards {α : Type*} (atoms : Finset α) {M : ℕ}
    (w : α → ℝ) (row : α → Finset (Fin M)) :
    (∑ z ∈ atoms, w z*((row z).card:ℝ)) =
      ∑ i : Fin M, ∑ z ∈ atoms, if i ∈ row z then w z else 0 := by
  have hc (z : α) : ((row z).card:ℝ) = ∑ i : Fin M, if i ∈ row z then (1:ℝ) else 0 := by simp
  simp_rw [hc,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]

def tubeWeight {α γ : Type*} (atoms : Finset α) {M : ℕ}
    (w : α → ℝ) (group : α → γ → Finset (Fin M)) (i : Fin M) (g : γ) : ℝ :=
  ∑ z ∈ atoms, if i ∈ group z g then w z else 0

theorem tubeWeight_nonneg {α γ : Type*} (atoms : Finset α) {M : ℕ}
    (w : α → ℝ) (hw : ∀ z ∈ atoms, 0 ≤ w z)
    (group : α → γ → Finset (Fin M)) (i : Fin M) (g : γ) :
    0 ≤ tubeWeight atoms w group i g := by
  apply Finset.sum_nonneg
  intro z hz
  split_ifs
  · exact hw z hz
  · exact le_rfl

theorem tubeWeight_support {α γ : Type*} (atoms : Finset α) {M : ℕ}
    (w : α → ℝ) (group : α → γ → Finset (Fin M)) (i : Fin M) (g : γ)
    (h : tubeWeight atoms w group i g ≠ 0) : ∃ z ∈ atoms, i ∈ group z g := by
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro z hz
  have hi : i ∉ group z g := fun hi => hn ⟨z,hz,hi⟩
  simp [hi]

theorem assigned_total {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (atoms : Finset α) (w : α → ℝ) (groups : Finset γ)
    (group : α → γ → Finset (Fin M)) (assign : Fin M → γ)
    (hassign : ∀ i, assign i ∈ groups) :
    (∑ z ∈ atoms, ∑ g ∈ groups, w z*((assigned group assign z g).card:ℝ)) =
      ∑ i : Fin M, tubeWeight atoms w group i (assign i) := by
  rw [Finset.sum_comm]
  simp_rw [sum_weighted_row_cards]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (assign i)]
  · simp [tubeWeight,assigned]
  · intro g _ hgne
    simp [assigned,Ne.symm hgne]
  · exact fun h => False.elim (h (hassign i))

/-- Zero-volume atoms need no positivity or cancellation assumption. -/
theorem assign_incidence {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (atoms : Finset α) (w : α → ℝ) (hw : ∀ z ∈ atoms, 0 ≤ w z)
    (groups : Finset γ) (hne : groups.Nonempty)
    (group : α → γ → Finset (Fin M)) {C : ℝ} (hC : 0 < C)
    (hcount : ∀ i : Fin M, ((groups.filter (fun g => ∃ z ∈ atoms, i ∈ group z g)).card:ℝ) ≤ C) :
    ∃ assign : Fin M → γ, (∀ i, assign i ∈ groups) ∧
      (∑ z ∈ atoms, ∑ g ∈ groups, w z*((group z g).card:ℝ))/C ≤
        ∑ z ∈ atoms, ∑ g ∈ groups, w z*((assigned group assign z g).card:ℝ) := by
  have hactive (i : Fin M) :
      ((groups.filter (fun g => tubeWeight atoms w group i g ≠ 0)).card:ℝ) ≤ C := by
    apply le_trans ?_ (hcount i)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro g hg
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
      tubeWeight_support atoms w group i g (Finset.mem_filter.mp hg).2⟩
  obtain ⟨assign,hassign,hbound⟩ := weighted_group_assignment groups hne (tubeWeight atoms w group)
    (tubeWeight_nonneg atoms w hw group) hactive
  refine ⟨assign,hassign,?_⟩
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hbound i)
  have hbefore : (∑ z ∈ atoms, ∑ g ∈ groups, w z*((group z g).card:ℝ)) =
      ∑ i : Fin M, ∑ g ∈ groups, tubeWeight atoms w group i g := by
    rw [Finset.sum_comm]
    simp_rw [sum_weighted_row_cards]
    rw [Finset.sum_comm]
    rfl
  rw [hbefore,assigned_total atoms w groups group assign hassign]
  apply (div_le_iff₀ hC).mpr
  simpa only [Finset.mul_sum,mul_comm] using hsum

/-- Restoration uses the actual pointwise cardinality test; only its mass
bookkeeping is weighted. Hence the existing broadness lemma remains applicable. -/
theorem restore_mass {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (atoms : Finset α) (w : α → ℝ) (hw : ∀ z ∈ atoms, 0 ≤ w z)
    (groups : Finset γ) (group : α → γ → Finset (Fin M)) (assign : Fin M → γ)
    {C : ℝ} (hC : 0 < C)
    (hcal : (∑ z ∈ atoms, ∑ g ∈ groups, w z*((group z g).card:ℝ)) ≤
      C*(∑ z ∈ atoms, ∑ g ∈ groups, w z*((assigned group assign z g).card:ℝ))) :
    (3/4:ℝ)*(∑ z ∈ atoms, ∑ g ∈ groups, w z*((assigned group assign z g).card:ℝ)) ≤
      ∑ z ∈ atoms, ∑ g ∈ groups, w z*((restored group assign C z g).card:ℝ) := by
  have hbad : (∑ z ∈ atoms, ∑ g ∈ groups,
      if ((group z g).card:ℝ) ≤ 4*C*((assigned group assign z g).card:ℝ)
        then 0 else w z*((assigned group assign z g).card:ℝ)) ≤
      (∑ z ∈ atoms, ∑ g ∈ groups, w z*((group z g).card:ℝ))/(4*C) := by
    simp_rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro z hz
    apply Finset.sum_le_sum
    intro g _
    split_ifs with hg
    · positivity [hw z hz]
    · apply (le_div_iff₀ (by positivity : 0 < 4*C)).mpr
      have hh := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hg)) (hw z hz)
      nlinarith
  have hbad' : (∑ z ∈ atoms, ∑ g ∈ groups, w z*((group z g).card:ℝ))/(4*C) ≤
      (∑ z ∈ atoms, ∑ g ∈ groups, w z*((assigned group assign z g).card:ℝ))/4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*C)).mpr
    nlinarith
  have hsplit : (∑ z ∈ atoms, ∑ g ∈ groups, w z*((restored group assign C z g).card:ℝ)) +
      (∑ z ∈ atoms, ∑ g ∈ groups,
        if ((group z g).card:ℝ) ≤ 4*C*((assigned group assign z g).card:ℝ)
          then 0 else w z*((assigned group assign z g).card:ℝ)) =
      ∑ z ∈ atoms, ∑ g ∈ groups, w z*((assigned group assign z g).card:ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro g _
    unfold restored
    split_ifs <;> simp
  linarith [hbad.trans hbad']

theorem assign_and_restore {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (atoms : Finset α) (w : α → ℝ) (hw : ∀ z ∈ atoms, 0 ≤ w z)
    (groups : Finset γ) (hne : groups.Nonempty)
    (group : α → γ → Finset (Fin M)) {C : ℝ} (hC : 0 < C)
    (hcount : ∀ i : Fin M, ((groups.filter (fun g => ∃ z ∈ atoms, i ∈ group z g)).card:ℝ) ≤ C) :
    ∃ assign : Fin M → γ, (∀ i, assign i ∈ groups) ∧
      (3/(4*C))*(∑ z ∈ atoms, ∑ g ∈ groups, w z*((group z g).card:ℝ)) ≤
        ∑ z ∈ atoms, ∑ g ∈ groups, w z*((restored group assign C z g).card:ℝ) ∧
      ∀ z g i, i ∈ restored group assign C z g → i ∈ group z g ∧ assign i = g := by
  obtain ⟨assign,hassign,hmass⟩ := assign_incidence atoms w hw groups hne group hC hcount
  have hcal : (∑ z ∈ atoms, ∑ g ∈ groups, w z*((group z g).card:ℝ)) ≤
      C*(∑ z ∈ atoms, ∑ g ∈ groups, w z*((assigned group assign z g).card:ℝ)) :=
    by simpa only [mul_comm] using (div_le_iff₀ hC).mp hmass
  have hret := restore_mass atoms w hw groups group assign hC hcal
  refine ⟨assign,hassign,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ) ≤ 3/4)
    have heq : (3/(4*C))*(∑ z ∈ atoms, ∑ g ∈ groups, w z*((group z g).card:ℝ)) =
        (3/4:ℝ)*((∑ z ∈ atoms, ∑ g ∈ groups, w z*((group z g).card:ℝ))/C) := by ring
    rw [heq]
    exact hh.trans hret
  · intro z g i hi
    exact Finset.mem_filter.mp (restored_subset group assign C z g hi)

end
end KakeyaFormal.WeightedAngularAssignment
