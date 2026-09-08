import LowerDensityEstimate
import SourceAnalyticInputs

/-! Apply normalized unrestricted estimates to actual original full shadings
with any fixed positive lower density multiple. No upper ratio or two-ends
condition is needed in the conclusion of Proposition 8.1. -/
namespace KakeyaFormal.OriginalLowerDensity
open scoped BigOperators
noncomputable section

theorem from_discrete {n : ℕ} {m d p : ℝ}
    (hestimate : DiscreteEstimate n m d p) (hp : 0 < p)
    (geom : Normalization) (c₀ eps : ℝ) (hc₀ : 0 < c₀) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily n M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → 1 ≤ A →
      F.Admissible geom.width δ → F.Separated (geom.separation*δ) →
      F.Bounded geom.radius → F.CapBound δ m A →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^(m-d+eps)*lam^p*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hbound⟩ := LowerDensityEstimate.lower_density hestimate hp geom eps heps
  refine ⟨c*c₀^p,by positivity,?_⟩
  intro M F δ lam A hδ hδ1 hlam hA hadm hsep hbounded hcap hlower
  have hrow (i : Fin M) : c₀*lam ≤ δ*((F.shade i).card:ℝ) :=
    ((div_le_iff₀ hδ).mp (hlower i)).trans_eq (mul_comm _ _)
  let G : CumulativeConfiguration n geom m := {
    M:=M, δ:=δ, s:=c₀*lam, A:=A, family:=F,
    scale_pos:=hδ, scale_le_one:=hδ1, density_nonneg:=mul_nonneg hc₀.le hlam.le,
    cap_ge_one:=hA, admissible:=hadm, separated:=hsep, bounded:=hbounded, cap_bound:=hcap,
    cumulative:=by
      calc
        c₀*lam*(M:ℝ) = ∑ _i : Fin M, c₀*lam := by simp [mul_comm]
        _ ≤ ∑ i : Fin M, δ*((F.shade i).card:ℝ) := Finset.sum_le_sum (fun i _ => hrow i)
        _ = δ*∑ i : Fin M, ((F.shade i).card:ℝ) := (Finset.mul_sum _ _ _).symm }
  have hh := hbound G hrow
  change c*A⁻¹*δ^(m-d+eps)*(c₀*lam)^p*(M:ℝ) ≤ (F.unionCells.card:ℝ) at hh
  rw [Real.mul_rpow hc₀.le hlam.le] at hh
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hh

/-- Source Proposition8.1 from its absolute-cap N>=2-only premise, for
arbitrary fixed original density multiples and geometric normalizations.
The original shadings satisfy no two-ends condition. -/
theorem globalize {k : ℕ} {m D C : ℝ}
    (h : SourceAnalyticInputs.TwoEnds (k+1) m D C) (hm : 0 ≤ m) (hD : 1 ≤ D)
    (geom : Normalization) (c₀ eps : ℝ) (hc₀ : 0 < c₀) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → 1 ≤ A →
      F.Admissible geom.width δ → F.Separated (geom.separation*δ) →
      F.Bounded geom.radius → F.CapBound δ m A →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^(m-D+eps)*lam^(max D C)*(M:ℝ) ≤ (F.unionCells.card:ℝ) :=
  from_discrete (h.globalize hm hD)
    (zero_lt_one.trans_le (hD.trans (le_max_left _ _))) geom c₀ eps hc₀ heps

end
end KakeyaFormal.OriginalLowerDensity
