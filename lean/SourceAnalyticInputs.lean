import AbsoluteCapGlobalization
import LiftedCumulativeInput
import DiscreteScaleCompletion

/-! Analytic premises with exactly the source's eccentricity N>=2 cutoff.
Large meshes are completed by actual cap counting and an occupied original
integer cell; the caller need not assume any estimate near eccentricity one. -/
namespace KakeyaFormal.SourceAnalyticInputs
noncomputable section

/-- Source (5.4), only at eccentricities at least two, with a fixed cap ceiling. -/
def Base (n : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : Normalization, ∀ Q eps : ℝ, 1 ≤ Q → 0 < eps →
    ∃ c : ℝ, 0 < c ∧ ∀ F : ShadedConfiguration n geom m,
      F.δ ≤ 1/2 → F.A ≤ Q →
      c*F.δ^(m-d+eps)*F.lam^p*(F.M:ℝ) ≤ (F.family.unionCells.card:ℝ)

/-- Source (5.5), with both positive errors and only N>=2. -/
def Lifted (n : ℕ) (m d q : ℝ) : Prop :=
  ∀ geom : Normalization, ∀ eps : ℝ, 0 < eps →
    ∃ c : ℝ, 0 < c ∧ ∀ F : CumulativeConfiguration n geom m,
      F.δ ≤ 1/2 →
      c*F.A⁻¹*F.δ^(m-d+eps)*F.s^(q+eps)*(F.M:ℝ) ≤ (F.family.unionCells.card:ℝ)

/-- Source Proposition 8.1's absolute-cap two-ends premise at N>=2. -/
def TwoEnds (n : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : Normalization, ∀ Q B alpha eps : ℝ,
    1 ≤ Q → 1 ≤ B → 0 < alpha → 0 < eps →
    ∃ c : ℝ, 0 < c ∧ ∀ F : ShadedConfiguration n geom m,
      F.δ ≤ 1/2 → F.A ≤ Q → F.family.FullTwoEnds F.δ B alpha →
      c*F.δ^(m-d+eps)*F.lam^p*(F.M:ℝ) ≤ (F.family.unionCells.card:ℝ)

theorem Base.to_discrete {k : ℕ} {m d p : ℝ}
    (h : Base (k+1) m d p) (hm : 0 ≤ m) : DiscreteEstimate (k+1) m d p := by
  apply DiscreteScaleCompletion.complete
  intro geom eps heps
  obtain ⟨c,hc,hbound⟩ := h geom (LocalizedDirectionThinning.capConstant k m) eps
    (LocalizedDirectionThinning.capConstant_ge_one k m) heps
  refine ⟨1/2,c/LocalizedDirectionThinning.retentionConstant k m,by norm_num,
    div_pos hc (LocalizedDirectionThinning.retentionConstant_pos k m),?_⟩
  intro F hscale
  obtain ⟨O⟩ := AbsoluteCapReduction.construct hm F
  exact O.transfer_bound hc (hbound O.selected (by simpa only [O.scale_eq] using hscale)
    (by rw [O.cap_eq]))

theorem Lifted.to_discrete {k : ℕ} {m d q : ℝ}
    (h : Lifted (k+1) m d q) : DiscreteEstimate (k+1) m d q := by
  apply DiscreteScaleCompletion.complete
  intro geom eps heps
  obtain ⟨c,hc,hbound⟩ := h geom (eps/2) (by positivity)
  refine ⟨1/2,c*(2:ℝ)^(-(eps/2)),by norm_num,by positivity,?_⟩
  intro F hscale
  by_cases hM : F.M = 0
  · simp [hM]
  have hMpos : 0 < F.M := Nat.pos_of_ne_zero hM
  have hp := LiftedCumulativeInput.power_transfer F.scale_pos F.density_pos
    (F.density_ge_half_scale hMpos) heps.le (m := m) (d := d) (q := q)
  have hA : 0 ≤ F.A⁻¹ := inv_nonneg.mpr (by linarith [F.cap_ge_one])
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (mul_nonneg hc.le hA)) (Nat.cast_nonneg F.M)
  have hfinal := hbound (LiftedCumulativeInput.cumulative F) hscale
  change c*F.A⁻¹*F.δ^(m-d+eps/2)*F.lam^(q+eps/2)*F.M ≤
    (F.family.unionCells.card:ℝ) at hfinal
  calc
    _ = (c*F.A⁻¹)*((2:ℝ)^(-(eps/2))*F.δ^(m-d+eps)*F.lam^q)*F.M := by ring
    _ ≤ (c*F.A⁻¹)*(F.δ^(m-d+eps/2)*F.lam^(q+eps/2))*F.M := hscaled
    _ ≤ (F.family.unionCells.card:ℝ) := by nlinarith [hfinal]

theorem TwoEnds.to_two_ends {k : ℕ} {m d p : ℝ}
    (h : TwoEnds (k+1) m d p) (hm : 0 ≤ m) :
    TwoEndsDiscreteEstimate (k+1) m d p := by
  intro geom B alpha eps hB halpha heps
  obtain ⟨c,hc,hbound⟩ := h geom (LocalizedDirectionThinning.capConstant k m)
    B alpha eps (LocalizedDirectionThinning.capConstant_ge_one k m) hB halpha heps
  let C := c/LocalizedDirectionThinning.retentionConstant k m
  let G := DiscreteScaleCompletion.coefficient k m d p eps (1/2)
  have hC : 0 < C := div_pos hc (LocalizedDirectionThinning.retentionConstant_pos k m)
  have hG : 0 < G := DiscreteScaleCompletion.coefficient_pos k m d p eps (1/2)
  refine ⟨min C G,lt_min hC hG,?_⟩
  intro F hends
  have hf : 0 ≤ F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*(F.M:ℝ) := by
    have hA := zero_lt_one.trans_le F.cap_ge_one
    have hd := F.scale_pos
    have hl := F.density_pos
    positivity
  by_cases hs : F.δ ≤ 1/2
  · obtain ⟨O⟩ := AbsoluteCapReduction.construct hm F
    have hh := O.transfer_bound hc (hbound O.selected
      (by simpa only [O.scale_eq] using hs) (by rw [O.cap_eq]) (O.full_two_ends hends))
    apply le_trans ?_ hh
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (min_le_left C G) hf
  · have hh := DiscreteScaleCompletion.bounded_scale (d:=d) (p:=p) (eps:=eps)
      (by norm_num : (0:ℝ)<1/2) F (le_of_not_ge hs)
    apply le_trans ?_ hh
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (min_le_right C G) hf

/-- Complete Proposition 8.1, including 0<C<1, from its small-scale-only
absolute-cap hypothesis. -/
theorem TwoEnds.globalize {k : ℕ} {m D C : ℝ}
    (h : TwoEnds (k+1) m D C) (hm : 0 ≤ m) (hD : 1 ≤ D) :
    DiscreteEstimate (k+1) m D (max D C) :=
  (h.to_two_ends hm).remove_two_ends_all_density hm hD

theorem TwoEnds.globalize_measurable {k : ℕ} {m D C : ℝ}
    (h : TwoEnds (k+1) m D C) (hm : 0 ≤ m) (hD : 1 ≤ D) :
    VolumeMeasurableEstimate (k+1) m D (max D C) :=
  (h.globalize hm hD).to_measurable_volume (by omega) hD (le_max_left _ _)

end
end KakeyaFormal.SourceAnalyticInputs
