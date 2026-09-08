import MeasurableToDiscrete

/-! User-authorized external published results, 6 September2026.
These axioms are trusted normalized restricted-shading consequences of published
integer-dimensional maximal estimates. The translation from the papers' operator
and tube conventions to this predicate is included in the trust boundary, not
presented as a kernel-checked operator adapter. The measurable-to-grid adapter
and all consequences below are proved. No novel manuscript pivot is assumed. -/
namespace KakeyaFormal.ExternalAxioms
open MeasureTheory Finset
noncomputable section

/-- Normalized shading bound independent of the cap coefficient in integer
ambient n. Configurations still carry cap data with parameter n-1; A is unused
in the conclusion. Constants precede all actual configurations. -/
def NormalizedShadingBound (n : ℕ) (d : ℝ) : Prop :=
  ∀ geom : MeasurableNormalization, ∀ eps : ℝ, 0 < eps → ∃ c : ℝ, 0 < c ∧
    ∀ F : MeasurableConfiguration n geom ((n:ℝ)-1),
      c*F.δ^((n:ℝ)+((n:ℝ)-1)-d+eps)*F.lam^d*(F.M:ℝ) ≤
        (volume : Measure (Space n)).real F.unionSet

/-- Zahl's exact finite optimization. The n<2 branch is never imported. -/
def zahlExponent (n : ℕ) : ℝ :=
  if hn : 2 ≤ n then
    (Finset.Icc 2 n).sup' ⟨2,Finset.mem_Icc.mpr ⟨le_rfl,hn⟩⟩
      (fun j => min ((n:ℝ)-(j:ℝ)+2)
        (((n:ℝ)^2+(j:ℝ)^2+(n:ℝ)-(j:ℝ))/(2*(n:ℝ))))
  else 0

/-- Wolff1995, Theorem1, printedp652; normalized shading corollary.
https://ems.press/content/serial-article-files/37888?nt=1 -/
axiom wolff1995 (n : ℕ) (hn : 2 ≤ n) :
  NormalizedShadingBound n (((n:ℝ)+2)/2)

/-- Katz--Tao2002, Theorem1.1/Section5; normalized shading corollary.
Version: arXiv:math/0102135v1, 16February2001.
https://arxiv.org/pdf/math/0102135v1 -/
axiom katzTao2002 (n : ℕ) (hn : 2 ≤ n) :
  NormalizedShadingBound n ((4*(n:ℝ)+3)/7)

/-- Zahl2021, Theorem1.5, equation(1.6); normalized shading corollary.
Version: arXiv:1908.05314v4, 12January2021.
https://arxiv.org/pdf/1908.05314v4 -/
axiom zahl2021 (n : ℕ) (hn : 2 ≤ n) :
  NormalizedShadingBound n (zahlExponent n)

/-- Derived inverse-A weakening to the existing measurable predicate. No
arbitrary-real-cap or larger-ambient statement is imported. -/
theorem NormalizedShadingBound.to_measurable {n : ℕ} {d : ℝ}
    (h : NormalizedShadingBound n d) : MeasurableEstimate n ((n:ℝ)-1) d d := by
  intro geom eps heps
  obtain ⟨c,hc,hbound⟩ := h geom eps heps
  refine ⟨c,hc,?_⟩
  intro F
  have hA : F.A⁻¹ ≤ 1 := inv_le_one_of_one_le₀ F.cap_ge_one
  have hcoef : 0 ≤ c*F.δ^((n:ℝ)+((n:ℝ)-1)-d+eps)*F.lam^d*(F.M:ℝ) := by
    positivity [F.scale_pos,F.density_pos]
  have hh := mul_le_mul_of_nonneg_right hA hcoef
  have heq : c*F.A⁻¹*F.δ^((n:ℝ)+((n:ℝ)-1)-d+eps)*F.lam^d*(F.M:ℝ) =
      F.A⁻¹*(c*F.δ^((n:ℝ)+((n:ℝ)-1)-d+eps)*F.lam^d*(F.M:ℝ)) := by ring
  rw [heq]
  exact hh.trans (by simpa only [one_mul] using hbound F)

theorem wolff_discrete (n : ℕ) (hn : 2 ≤ n) :
    DiagonalDiscreteEstimate n (((n:ℝ)+2)/2) :=
  (NormalizedShadingBound.to_measurable (wolff1995 n hn)).to_discrete

theorem katz_tao_discrete (n : ℕ) (hn : 2 ≤ n) :
    DiagonalDiscreteEstimate n ((4*(n:ℝ)+3)/7) :=
  (NormalizedShadingBound.to_measurable (katzTao2002 n hn)).to_discrete

theorem zahl_discrete (n : ℕ) (hn : 2 ≤ n) :
    DiagonalDiscreteEstimate n (zahlExponent n) :=
  (NormalizedShadingBound.to_measurable (zahl2021 n hn)).to_discrete

theorem wolff_five : DiagonalDiscreteEstimate 5 (7/2) := by
  convert wolff_discrete 5 (by norm_num) using 1
  norm_num

theorem wolff_six : DiagonalDiscreteEstimate 6 4 := by
  convert wolff_discrete 6 (by norm_num) using 1
  norm_num

theorem katz_tao_nine : DiagonalDiscreteEstimate 9 (39/7) := by
  convert katz_tao_discrete 9 (by norm_num) using 1
  norm_num

theorem zahl_eight : DiagonalDiscreteEstimate 8 (21/4) := by
  convert zahl_discrete 8 (by norm_num) using 1
  have hIcc : (Finset.Icc 2 8 : Finset ℕ) = {2,3,4,5,6,7,8} := by decide
  norm_num [zahlExponent,hIcc,Finset.sup'_insert,Finset.sup'_singleton]

end
end KakeyaFormal.ExternalAxioms
