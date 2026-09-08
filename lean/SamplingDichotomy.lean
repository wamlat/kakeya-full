import SamplingApplication

/-! The deterministic low/high partition of actual expected marked cell mass.
Zero-mass cells are omitted from the low alternative; neither a partition nor
the retained high mass is assumed. -/
namespace KakeyaSamplingDichotomy
open Finset KakeyaSamplingApplication
open scoped BigOperators
noncomputable section
open Classical

variable {C : Type*} [Fintype C]

def low (mu : C → ℝ) (cutoff : ℝ) : Finset C :=
  univ.filter (fun c => 0 < mu c ∧ mu c < cutoff)

def high (mu : C → ℝ) (cutoff : ℝ) : Finset C :=
  univ.filter (fun c => cutoff ≤ mu c)

theorem mass_partition (mu : C → ℝ) {cutoff : ℝ}
    (hmu : ∀ c, 0 ≤ mu c) (hcut : 0 < cutoff) :
    (∑ c ∈ low mu cutoff, mu c) + (∑ c ∈ high mu cutoff, mu c) = ∑ c, mu c := by
  rw [low,high,sum_filter,sum_filter,← sum_add_distrib]
  apply sum_congr rfl
  intro c _
  by_cases hp : 0 < mu c
  · by_cases hl : mu c < cutoff
    · simp [hp,hl,not_le.mpr hl]
    · simp [hp,hl,le_of_not_gt hl]
  · have hz : mu c = 0 := le_antisymm (le_of_not_gt hp) (hmu c)
    simp [hz,hcut.not_ge]

theorem low_mass_bound (mu : C → ℝ) (cutoff : ℝ) :
    (∑ c ∈ low mu cutoff, mu c) ≤ cutoff * ((low mu cutoff).card : ℝ) := by
  calc
    _ ≤ ∑ _c ∈ low mu cutoff, cutoff := sum_le_sum (fun c hc => (mem_filter.mp hc).2.2.le)
    _ = _ := by simp [mul_comm]

/-- Exact finite version of (6.6)/(6.13), using the actual positive low cells. -/
theorem dichotomy (mu : C → ℝ) {cutoff : ℝ}
    (hmu : ∀ c, 0 ≤ mu c) (hcut : 0 < cutoff) :
    ((∑ c, mu c)/2 ≤ ∑ c ∈ low mu cutoff, mu c ∧
      (∑ c, mu c)/(2*cutoff) ≤ ((low mu cutoff).card : ℝ)) ∨
    (∑ c, mu c)/2 ≤ ∑ c ∈ high mu cutoff, mu c := by
  by_cases hlo : (∑ c, mu c)/2 ≤ ∑ c ∈ low mu cutoff, mu c
  · refine Or.inl ⟨hlo,?_⟩
    apply (div_le_iff₀ (by positivity : 0 < 2*cutoff)).mpr
    have hb := low_mass_bound mu cutoff
    nlinarith
  · exact Or.inr (by linarith [mass_partition mu hmu hcut])

/-- The low/high alternative on the literal SamplingApplication means. -/
theorem marked_dichotomy {T : Type*} [Fintype T] (q : T → C → ℝ) {cutoff : ℝ}
    (hq : ∀ t c, 0 ≤ q t c) (hcut : 0 < cutoff) :
    ((∑ c, markedMean q c)/2 ≤ ∑ c ∈ low (markedMean q) cutoff, markedMean q c ∧
      (∑ c, markedMean q c)/(2*cutoff) ≤ ((low (markedMean q) cutoff).card : ℝ)) ∨
    (∑ c, markedMean q c)/2 ≤ ∑ c ∈ high (markedMean q) cutoff, markedMean q c :=
  dichotomy _ (fun c => sum_nonneg (fun t _ => hq t c)) hcut

end
end KakeyaSamplingDichotomy

#print axioms KakeyaSamplingDichotomy.marked_dichotomy
