import Mathlib

/-! Constructive smallest-dyadic-scale localizedization for a finite weighted shading.
The minimizing scale and its ball are obtained from the actual shading. Positive
weights include counting measure and finite occupancy data. No two-ends condition
or preselected localizedization is assumed. -/
namespace KakeyaFormal.Localization

noncomputable def radius (J j : ℕ) : ℝ := (2 : ℝ)^j / (2 : ℝ)^J

@[simp] theorem radius_top (J : ℕ) : radius J J = 1 := by
  simp [radius]

theorem radius_pos (J j : ℕ) : 0 < radius J j := by
  unfold radius
  positivity

theorem radius_succ (J j : ℕ) : radius J (j+1) = 2 * radius J j := by
  unfold radius
  rw [pow_succ]
  ring

theorem radius_mono (J : ℕ) : Monotone (radius J) := by
  intro i j hij
  exact div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hij)
    (by positivity)

/-- Round any radius between the bottom and top scales upward, losing at most 2. -/
theorem dyadic_round {J : ℕ} {r : ℝ}
    (hbottom : radius J 0 ≤ r) (htop : r ≤ 1) :
    ∃ j ≤ J, r ≤ radius J j ∧ radius J j ≤ 2*r := by
  classical
  have hex : ∃ j : ℕ, j ≤ J ∧ r ≤ radius J j := ⟨J, le_rfl, by simpa⟩
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  refine ⟨j, hj.1, hj.2, ?_⟩
  by_cases hz : j = 0
  · rw [hz]
    linarith [radius_pos J 0]
  · have hprev : ¬ ((j-1) ≤ J ∧ r ≤ radius J (j-1)) :=
      Nat.find_min hex (by dsimp [j] at hz ⊢; omega)
    have hprevlt : radius J (j-1) < r := by
      exact lt_of_not_ge (fun h => hprev ⟨by omega, h⟩)
    have hid : j = (j-1)+1 := by omega
    rw [hid, radius_succ]
    linarith

variable {X : Type*} [MetricSpace X]

noncomputable def mass (w : X → ℝ) (s : Finset X) : ℝ := ∑ x ∈ s, w x

noncomputable def restrict (s : Finset X) (x : X) (r : ℝ) : Finset X := by
  classical
  exact s.filter (fun y => dist y x ≤ r)

theorem restrict_subset (s : Finset X) (x : X) (r : ℝ) : restrict s x r ⊆ s := by
  classical
  exact Finset.filter_subset _ _

omit [MetricSpace X] in
theorem mass_nonneg {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (s : Finset X) :
    0 ≤ mass w s := Finset.sum_nonneg (fun x _ => hw x)

omit [MetricSpace X] in
theorem mass_mono {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) {s t : Finset X}
    (hst : s ⊆ t) : mass w s ≤ mass w t := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hst (fun x _ _ => hw x)

theorem restrict_mono {s t : Finset X} (hst : s ⊆ t) (x : X) {r R : ℝ}
    (hr : r ≤ R) : restrict s x r ⊆ restrict t x R := by
  classical
  intro y hy
  simp only [restrict, Finset.mem_filter] at hy ⊢
  exact ⟨hst hy.1, hy.2.trans hr⟩

/-- All radii are included, not only the finite dyadic test scales. -/
theorem smallest_scale_two_ends (s : Finset X) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (J : ℕ) {alpha : ℝ} (ha : 0 ≤ alpha)
    (x₀ : X) (hcover : ∀ y ∈ s, dist y x₀ ≤ 1) :
    ∃ j ≤ J, ∃ x : X,
      let localized := restrict s x (radius J j)
      (radius J j)^alpha * mass w s ≤ mass w localized ∧
      ∀ y : X, ∀ r : ℝ, radius J 0 ≤ r → r ≤ radius J j →
        mass w (restrict localized y r) ≤
          (2 : ℝ)^alpha * (r / radius J j)^alpha * mass w localized := by
  classical
  have htop : restrict s x₀ (radius J J) = s := by
    simp only [radius_top, restrict]
    exact Finset.filter_eq_self.mpr hcover
  have hex : ∃ j : ℕ, j ≤ J ∧ ∃ x : X,
      (radius J j)^alpha * mass w s ≤ mass w (restrict s x (radius J j)) := by
    refine ⟨J,le_rfl,x₀,?_⟩
    rw [htop, radius_top]
    simp
  let j := Nat.find hex
  obtain ⟨hj, x, hmass⟩ := Nat.find_spec hex
  let localized := restrict s x (radius J j)
  have hlocal : localized ⊆ s := restrict_subset _ _ _
  have hlocnonneg := mass_nonneg hw localized
  have hradius := radius_pos J j
  refine ⟨j,hj,x,hmass,?_⟩
  intro y r hbottom hr
  change mass w (restrict localized y r) ≤ _
  have hrpos : 0 < r := (radius_pos J 0).trans_le hbottom
  have htrivial : mass w (restrict localized y r) ≤ mass w localized :=
    mass_mono hw (restrict_subset _ _ _)
  have hid : (2 : ℝ)^alpha * (r / radius J j)^alpha =
      (2*r / radius J j)^alpha := by
    rw [← Real.mul_rpow (by norm_num) (div_nonneg hrpos.le hradius.le)]
    congr 1
    ring
  rw [hid]
  by_cases hlarge : radius J j ≤ 2*r
  · have hone : (1 : ℝ) ≤ (2*r / radius J j)^alpha := by
      have hratio : (1 : ℝ) ≤ 2*r / radius J j :=
        (le_div_iff₀ hradius).mpr (by simpa using hlarge)
      simpa using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hratio ha
    exact htrivial.trans (by nlinarith)
  · have hsmall : 2*r < radius J j := lt_of_not_ge hlarge
    have hrtop : r ≤ 1 := hr.trans (by simpa using radius_mono J hj)
    obtain ⟨i,hi,hri,hir⟩ := dyadic_round hbottom hrtop
    have hij : i < j := by
      by_contra hh
      have := radius_mono J (Nat.le_of_not_gt hh)
      linarith
    have hfail := Nat.find_min hex hij
    have hupper : mass w (restrict s y (radius J i)) < (radius J i)^alpha * mass w s := by
      exact lt_of_not_ge (fun h => hfail ⟨hi,y,h⟩)
    have hrestrict := mass_mono hw (restrict_mono hlocal y hri)
    have hscale : (radius J i)^alpha ≤ (2*r)^alpha :=
      Real.rpow_le_rpow (radius_pos J i).le hir ha
    have hstep : mass w (restrict localized y r) ≤ (2*r)^alpha * mass w s :=
      hrestrict.trans (hupper.le.trans (mul_le_mul_of_nonneg_right hscale (mass_nonneg hw s)))
    have hdenom : 0 < (radius J j)^alpha := Real.rpow_pos_of_pos hradius _
    have hmdiv : mass w s ≤ mass w localized / (radius J j)^alpha :=
      (le_div_iff₀ hdenom).mpr (by simpa only [localized, j, mul_comm] using hmass)
    have hh := mul_le_mul_of_nonneg_left hmdiv (Real.rpow_nonneg (by positivity : 0 ≤ 2*r) alpha)
    rw [Real.div_rpow (by positivity : 0 ≤ 2*r) hradius.le]
    exact hstep.trans (by simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh)

end KakeyaFormal.Localization
