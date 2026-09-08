import Configurations
import Scalar
import Reduction

/-!
Endpoint passage for actual finite Euclidean configurations, with the correct
order of all uniform constants. The seed and pivot estimates remain explicit
analytic hypotheses; no new Kakeya bound is asserted without those inputs.
-/

namespace KakeyaFormal
open Filter
open scoped Topology

theorem DiscreteEstimate.weaken_density {k : ℕ} {m d p P : ℝ}
    (h : DiscreteEstimate k m d p) (hp : p ≤ P) : DiscreteEstimate k m d P := by
  intro geom ε hε
  obtain ⟨c,hc,hbound⟩ := h geom ε hε
  refine ⟨c,hc,fun F => ?_⟩
  have hpow := Real.rpow_le_rpow_of_exponent_ge F.density_pos F.density_le_one hp
  have hA : 0 ≤ F.A⁻¹ := inv_nonneg.mpr (by linarith [F.cap_ge_one])
  have hcoef : 0 ≤ c * F.A⁻¹ * F.δ ^ (m-d+ε) :=
    mul_nonneg (mul_nonneg hc.le hA) (Real.rpow_nonneg F.scale_pos.le _)
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow hcoef) (Nat.cast_nonneg F.M)).trans (hbound F)

theorem RealCapEstimate.weaken_density {m d p P : ℝ}
    (h : RealCapEstimate m d p) (hp : p ≤ P) : RealCapEstimate m d P :=
  fun k hk => (h k hk).weaken_density hp

/-- The stage is chosen using only ε and the convergent exponent sequence.
Its constant is then uniform in all geometric configurations, even if their
density, cap coefficient or tube count vary with the scale. -/
theorem DiscreteEstimate.of_limit {k : ℕ} {m D P : ℝ} {d p : ℕ → ℝ}
    (hlim : Tendsto d atTop (𝓝 D)) (hp : ∀ j, p j ≤ P)
    (hstage : ∀ j, DiscreteEstimate k m (d j) (p j)) :
    DiscreteEstimate k m D P := by
  intro geom ε hε
  have hev : ∀ᶠ j in atTop, D-ε/2 < d j :=
    (tendsto_order.1 hlim).1 _ (by linarith)
  obtain ⟨j,hj⟩ := hev.exists
  obtain ⟨c,hc,hbound⟩ := hstage j geom (ε/2) (by linarith)
  refine ⟨c,hc,fun F => ?_⟩
  have hmono := KakeyaAudit.Reduction.finite_depth_transfer
    (n := m) (d := d j) (D := D) (p := p j) (P := P) (eps := ε)
    F.scale_pos F.scale_le_one F.density_pos F.density_le_one
    (by linarith) (hp j)
  have hA : 0 ≤ F.A⁻¹ := inv_nonneg.mpr (by linarith [F.cap_ge_one])
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmono (mul_nonneg hc.le hA)) (Nat.cast_nonneg F.M)
  have hfinal : c*F.A⁻¹*F.δ^(m-D+ε)*F.lam^P*F.M ≤
      c*F.A⁻¹*F.δ^(m-d j+ε/2)*F.lam^(p j)*F.M := by
    simpa only [mul_assoc] using hscaled
  exact hfinal.trans (hbound F)

theorem RealCapEstimate.of_limit {m D P : ℝ} {d p : ℕ → ℝ}
    (hlim : Tendsto d atTop (𝓝 D)) (hp : ∀ j, p j ≤ P)
    (hstage : ∀ j, RealCapEstimate m (d j) (p j)) :
    RealCapEstimate m D P :=
  fun k hk => DiscreteEstimate.of_limit hlim hp (fun j => hstage j k hk)

/-- A complete endpoint theorem for the analytic predicate defined using actual
tubes and integer grid cells. The fractional seed and pivot are NOT proved here. -/
theorem real_cap_endpoint_from_seed_and_pivot
    (seed : ∀ m : ℝ, 3 < m → RealCapEstimate m ((m+3)/2) ((m+3)/2))
    (pivot : ∀ m d d' p q : ℝ,
      3 < d' → d' < d → d < m → d ≤ p → d' ≤ q →
      RealCapEstimate m d p → RealCapEstimate d d' q →
      RealCapEstimate m (KakeyaScalar.pivotSet m d')
        (max (KakeyaScalar.pivotSet m d') (KakeyaScalar.pivotDensity p q)))
    {m : ℝ} (hm : 3 < m) :
    RealCapEstimate m (KakeyaScalar.limitProfile m) (max (KakeyaScalar.limitProfile m) 4) := by
  have hstage := KakeyaScalar.conditional_real_cap_iteration RealCapEstimate seed
    (fun _ _ _ _ hp h => h.weaken_density hp) pivot
  apply RealCapEstimate.of_limit (KakeyaScalar.profile_tendsto m)
    (fun j => KakeyaScalar.envelope_below_limit j hm)
  exact fun j => hstage j m hm

theorem conditional_diagonal_endpoint
    (seed : ∀ m : ℝ, 3 < m → RealCapEstimate m ((m+3)/2) ((m+3)/2))
    (pivot : ∀ m d d' p q : ℝ,
      3 < d' → d' < d → d < m → d ≤ p → d' ≤ q →
      RealCapEstimate m d p → RealCapEstimate d d' q →
      RealCapEstimate m (KakeyaScalar.pivotSet m d')
        (max (KakeyaScalar.pivotSet m d') (KakeyaScalar.pivotDensity p q)))
    {n : ℕ} (hn : 6 ≤ n) :
    DiagonalDiscreteEstimate n (KakeyaScalar.limitProfile ((n : ℝ)-1)) := by
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have h := real_cap_endpoint_from_seed_and_pivot seed pivot
    (show 3 < (n : ℝ)-1 by linarith) n le_rfl
  have hfour := KakeyaScalar.limit_diagonal_for_n_ge_six hnR
  simpa only [DiagonalDiscreteEstimate, max_eq_left hfour.le] using h

end KakeyaFormal
