import CumulativeEstimate

/-!
The source lifted input (5.5) has the same positive error in its scale and
cumulative-density powers. Recover the normalized comparable estimate at any
requested scale error from that literal input. The extra density error is paid
using the integer-cell lower bound lambda >= delta/2 on a nonempty family.
No new analytic bound is assumed beyond the displayed cumulative premise.
-/

namespace KakeyaFormal
open scoped BigOperators
noncomputable section

/-- The simultaneous scale/density error in the paper's cumulative lifted input.
The constant is fixed before the actual family, scale, cumulative density and
cap coefficient. -/
def LiftedCumulativeInput (k : ℕ) (m d q : ℝ) : Prop :=
  ∀ geom : Normalization, ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ F : CumulativeConfiguration k geom m,
      c * F.A⁻¹ * F.δ ^ (m-d+ε) * F.s ^ (q+ε) * F.M ≤
        (F.family.unionCells.card : ℝ)

namespace LiftedCumulativeInput

/-- Keep every original tube and cell when regarding comparable data as
cumulative data. -/
def cumulative {k : ℕ} {geom : Normalization} {m : ℝ}
    (F : ShadedConfiguration k geom m) : CumulativeConfiguration k geom m where
  M := F.M
  δ := F.δ
  s := F.lam
  A := F.A
  family := F.family
  scale_pos := F.scale_pos
  scale_le_one := F.scale_le_one
  density_nonneg := F.density_pos.le
  cap_ge_one := F.cap_ge_one
  admissible := F.admissible
  separated := F.separated
  bounded := F.bounded
  cap_bound := F.cap_bound
  cumulative := by
    have hsum := Finset.sum_le_sum (s := Finset.univ)
      (fun (i : Fin F.M) _ => (F.comparable i).1)
    have hs : F.lam / F.δ * (F.M : ℝ) ≤
        ∑ i, ((F.family.shade i).card : ℝ) := by
      simpa [mul_comm] using hsum
    have h := mul_le_mul_of_nonneg_left hs F.scale_pos.le
    calc
      F.lam * F.M = F.δ * (F.lam / F.δ * (F.M : ℝ)) := by
        field_simp [F.scale_pos.ne']
      _ ≤ F.δ * ∑ i, ((F.family.shade i).card : ℝ) := h

/-- On nonempty integer shadings, half of the desired scale error pays for
the source's additional density error. -/
theorem power_transfer {δ lam m d q ε : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hhalf : δ / 2 ≤ lam) (hε : 0 ≤ ε) :
    (2 : ℝ) ^ (-(ε/2)) * δ ^ (m-d+ε) * lam ^ q ≤
      δ ^ (m-d+ε/2) * lam ^ (q+ε/2) := by
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ δ / 2) hhalf
    (by positivity : 0 ≤ ε/2)
  rw [Real.div_rpow hδ.le (by norm_num : 0 ≤ (2 : ℝ)),
    div_eq_mul_inv, ← Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ))] at hpow
  have h := mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (Real.rpow_nonneg hδ.le (m-d+ε/2))
      (Real.rpow_nonneg hlam.le q))
  calc
    (2 : ℝ) ^ (-(ε/2)) * δ ^ (m-d+ε) * lam ^ q =
        (δ ^ (m-d+ε/2) * lam ^ q) *
          (δ ^ (ε/2) * (2 : ℝ) ^ (-(ε/2))) := by
      rw [show m-d+ε = (m-d+ε/2)+(ε/2) by ring,
        Real.rpow_add hδ]
      ring
    _ ≤ (δ ^ (m-d+ε/2) * lam ^ q) * lam ^ (ε/2) := h
    _ = δ ^ (m-d+ε/2) * lam ^ (q+ε/2) := by
      rw [Real.rpow_add hlam]
      ring

/-- The literal cumulative source input is enough for the full inverse-cap
comparable input used by the assembled pivot. All real exponents are allowed. -/
theorem to_discrete {k : ℕ} {m d q : ℝ}
    (h : LiftedCumulativeInput k m d q) : DiscreteEstimate k m d q := by
  intro geom ε hε
  obtain ⟨c,hc,hbound⟩ := h geom (ε/2) (by positivity)
  refine ⟨c * (2 : ℝ) ^ (-(ε/2)), by positivity, ?_⟩
  intro F
  by_cases hM : F.M = 0
  · simp [hM]
  have hMpos : 0 < F.M := Nat.pos_of_ne_zero hM
  have hp := power_transfer F.scale_pos F.density_pos
    (F.density_ge_half_scale hMpos) hε.le (m := m) (d := d) (q := q)
  have hA : 0 ≤ F.A⁻¹ := inv_nonneg.mpr (by linarith [F.cap_ge_one])
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hc.le hA))
    (Nat.cast_nonneg F.M)
  have hfinal := hbound (cumulative F)
  change c * F.A⁻¹ * F.δ ^ (m-d+ε/2) * F.lam ^ (q+ε/2) * F.M ≤
    (F.family.unionCells.card : ℝ) at hfinal
  calc
    c * (2 : ℝ) ^ (-(ε/2)) * F.A⁻¹ * F.δ ^ (m-d+ε) * F.lam ^ q * F.M =
        (c * F.A⁻¹) *
          ((2 : ℝ) ^ (-(ε/2)) * F.δ ^ (m-d+ε) * F.lam ^ q) * F.M := by ring
    _ ≤ (c * F.A⁻¹) *
        (F.δ ^ (m-d+ε/2) * F.lam ^ (q+ε/2)) * F.M := hscaled
    _ ≤ (F.family.unionCells.card : ℝ) := by nlinarith [hfinal]

end LiftedCumulativeInput
end
end KakeyaFormal
