import MeasurableEstimate

/-! Cap-free maximal shading predicates in the exact actual tube-volume form.
The bounded and unrestricted position conventions are distinguished explicitly.
Ambient-dimensional cap bounds are derived from direction separation. -/
namespace KakeyaFormal.MaximalShading
open MeasureTheory Finset
noncomputable section

/-- The manuscript's maximal-shading formula within each fixed bounded
normalization. Unlike a real-cap configuration predicate, this has neither
an input cap coefficient nor a cap condition. -/
def BoundedEstimate (n : ℕ) (d : ℝ) : Prop :=
  ∀ geom : MeasurableNormalization, ∀ eps : ℝ, 0 < eps → ∃ c : ℝ, 0 < c ∧
    ∀ {M : ℕ} (F : TubeFamily n M) {δ lam : ℝ} (Y : Fin M → Set (Space n)),
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 →
      (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ (F.tube i).carrier δ) →
      (∀ i, lam*(volume : Measure (Space n)).real ((F.tube i).carrier δ) ≤
        (volume : Measure (Space n)).real (Y i)) →
      F.Separated (geom.separation*δ) → F.Bounded geom.radius →
      c*δ^((n:ℝ)-d+eps)*lam^d*
        (∑ i, (volume : Measure (Space n)).real ((F.tube i).carrier δ)) ≤
          (volume : Measure (Space n)).real (⋃ i, Y i)

/-- The literal position-unrestricted maximal-shading formula (1.1).
The positive separation coefficient is fixed before every tube family,
position, scale, density, and measurable shading. -/
def Estimate (n : ℕ) (d : ℝ) : Prop :=
  ∀ separation : ℝ, 0 < separation → ∀ eps : ℝ, 0 < eps → ∃ c : ℝ, 0 < c ∧
    ∀ {M : ℕ} (F : TubeFamily n M) {δ lam : ℝ} (Y : Fin M → Set (Space n)),
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 →
      (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ (F.tube i).carrier δ) →
      (∀ i, lam*(volume : Measure (Space n)).real ((F.tube i).carrier δ) ≤
        (volume : Measure (Space n)).real (Y i)) →
      F.Separated (separation*δ) →
      c*δ^((n:ℝ)-d+eps)*lam^d*
        (∑ i, (volume : Measure (Space n)).real ((F.tube i).carrier δ)) ≤
          (volume : Measure (Space n)).real (⋃ i, Y i)

/-- At full ambient cap exponent, actual direction separation supplies the
cap condition. Its coefficient is fixed before scale, positions, and density,
so the inverse-cap factor becomes part of the fixed estimate constant. -/
theorem bounded_maximal_of_volume {k : ℕ} {d : ℝ}
    (h : VolumeMeasurableEstimate (k+1) (k:ℝ) d d) :
    BoundedEstimate (k+1) d := by
  intro geom eps heps
  obtain ⟨c,hc,hbound⟩ := h geom eps heps
  let A := ProjectiveGeometry.fullDirectionCoefficient k geom.separation
  have hA : 1 ≤ A := ProjectiveGeometry.fullDirectionCoefficient_ge_one k geom.separation_pos
  refine ⟨c*A⁻¹,by positivity,?_⟩
  intro M F δ lam Y hδ hδ1 hlam hlam1 hmeas hsub hmass hsep hbounded
  let V : MeasurableConfiguration (k+1) geom (k:ℝ) := {
    M := M, δ := δ, lam := lam, A := A, family := F, shading := Y,
    scale_pos := hδ, scale_le_one := hδ1, density_pos := hlam, density_le_one := hlam1,
    cap_ge_one := hA, shading_measurable := hmeas, shading_subset := hsub,
    shading_mass := hmass, separated := hsep, bounded := hbounded,
    cap_bound := ProjectiveGeometry.separated_tube_family_cap_bound F hδ geom.separation_pos hsep }
  simpa only [V,MeasurableConfiguration.unionSet,Nat.cast_add,Nat.cast_one,mul_assoc] using hbound V

end
end KakeyaFormal.MaximalShading
