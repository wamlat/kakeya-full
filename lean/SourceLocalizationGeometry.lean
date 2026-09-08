import SourceLocalization
import TwoEndsGlobalization

/-! Actual midpoint geometry supplies the top-scale localization cover.
At source width one and N>=2 no top-cover hypothesis remains. All selected
shadings retain their original cell labels, exact dyadic radius and relative
all-ball two ends. -/
namespace KakeyaFormal.SourceLocalizationGeometry
open FiniteGridLocalization KakeyaFormal.Localization
noncomputable section

/-- Source Lemma3.1 / first-step Lemma7 on actual admissible unit axes.
The fixed geometric smallness width*delta<=1/2 supplies the top cover. -/
theorem construct (k : ℕ) (width alpha : ℝ) (ha : 0 ≤ alpha) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {M : ℕ} (F : TubeFamily k M) {δ lam : ℝ},
      0 < M → 0 < δ → δ ≤ 1 → 0 < lam → width*δ ≤ 1/2 →
      F.Admissible width δ → F.Comparable δ lam →
      ∃ S : Selection F δ alpha lam,
        (∃ j : ℕ, j ≤ S.J ∧ S.rho = radius S.J j) ∧
        c*(M:ℝ)/(Real.log (2/δ))^2 ≤ (S.selected.card:ℝ) ∧
        S.rho^alpha*lam ≤ S.s ∧ S.s ≤ C*S.rho := by
  obtain ⟨c,C,hc,hC,hmain⟩ := SourceLocalization.construct k width alpha ha
  refine ⟨c,C,hc,hC,?_⟩
  intro M F δ lam hM hδ hδ1 hlam hwidth hadm hcomp
  exact hmain F hM hδ hδ1 hlam hadm hcomp
    (fun i => (F.tube i).axisPoint (1/2)) (TwoEndsGlobalization.unit_ball_cover F hadm hwidth)

/-- Literal source notation at width one and every N>=2. Both density
comparisons, cM/log(2N)^2, actual dyadic radius and original restrictions are
constructed directly from admissibility/comparability. -/
theorem unit_source_notation (k : ℕ) (alpha : ℝ) (ha : 0 ≤ alpha) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {M : ℕ} (F : TubeFamily k M) {N lam : ℝ},
      0 < M → 2 ≤ N → 0 < lam →
      F.Admissible 1 (1/N) → F.Comparable (1/N) lam →
      ∃ S : Selection F (1/N) alpha lam,
        (∃ j : ℕ, j ≤ S.J ∧ S.rho = radius S.J j) ∧
        c*(M:ℝ)/(Real.log (2*N))^2 ≤ (S.selected.card:ℝ) ∧
        S.rho^alpha*lam ≤ S.s ∧ S.s ≤ C*S.rho := by
  obtain ⟨c,C,hc,hC,hmain⟩ := construct k 1 alpha ha
  refine ⟨c,C,hc,hC,?_⟩
  intro M F N lam hM hN hlam hadm hcomp
  have hN0 : 0 < N := by linarith
  have hδ : 0 < 1/N := one_div_pos.mpr hN0
  have hδhalf : 1/N ≤ (1:ℝ)/2 := (one_div_le_one_div hN0 (by norm_num)).mpr hN
  have hδ1 : 1/N ≤ 1 := by linarith
  have hh := hmain F hM hδ hδ1 hlam (by simpa only [one_mul] using hδhalf) hadm hcomp
  have he : 2/(1/N)=2*N := by field_simp
  simpa only [he] using hh

end
end KakeyaFormal.SourceLocalizationGeometry
