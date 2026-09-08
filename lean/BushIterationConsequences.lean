import BushIteration
import MainMaximal

/-! Measurable consequences obtained through the actual Appendix A bush
iterations. These are shading estimates at arbitrary original tube positions;
no operator assertion is substituted for this predicate. -/
namespace KakeyaFormal.BushIteration
noncomputable section

/-- Every finite A.2 stage passes through the proved exact measurable and
spatial adapters. The exponent is the same actual bush iterate. -/
theorem bush_stage_maximal {n : ℕ} (hn : 5 ≤ n) (j : ℕ) :
    MaximalShading.Estimate n
      (KakeyaScalar.diagonal n 4 (((n:ℝ)+1)/2) j) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+1 := ⟨n-1,by omega⟩
  have hnR : (5:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast hn
  have hseed : (((k+1:ℕ):ℝ)+1)/2 < KakeyaScalar.diagonalLimit ((k+1:ℕ):ℝ) 4 := by
    dsimp [KakeyaScalar.diagonalLimit]; linarith
  have hlo := (KakeyaScalar.diagonal_monotone_and_bounds hseed j).1
  exact MainMaximal.from_diagonal (bush_stage hn j) (by linarith)

/-- Every finite A.3 stage keeps the same density exponent as its correctly
weakened lifted bush input before actual diagonal globalization. -/
theorem weakened_bush_stage_maximal {n : ℕ} (hn : 5 ≤ n) (j : ℕ) :
    MaximalShading.Estimate n
      (KakeyaScalar.diagonal n 3 (((n:ℝ)+1)/2) j) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+1 := ⟨n-1,by omega⟩
  have hnR : (5:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast hn
  have hseed : (((k+1:ℕ):ℝ)+1)/2 < KakeyaScalar.diagonalLimit ((k+1:ℕ):ℝ) 3 := by
    dsimp [KakeyaScalar.diagonalLimit]; linarith
  have hlo := (KakeyaScalar.diagonal_monotone_and_bounds hseed j).1
  exact MainMaximal.from_diagonal (weakened_bush_stage hn j) (by linarith)

/-- The Appendix A.2 endpoint through its prescribed bush iteration route,
including the actual arbitrary-position measurable shading conclusion. -/
theorem bush_endpoint_maximal {n : ℕ} (hn : 5 ≤ n) :
    MaximalShading.Estimate n ((4*(n:ℝ)+4)/7) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+1 := ⟨n-1,by omega⟩
  have hnR : (5:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast hn
  exact MainMaximal.from_diagonal (bush_endpoint hn) (by linarith)

/-- The Appendix A.3 endpoint through its own finite bush stages, rather
than weakening a stronger endpoint theorem after the fact. -/
theorem weakened_bush_endpoint_maximal {n : ℕ} (hn : 5 ≤ n) :
    MaximalShading.Estimate n ((4*(n:ℝ)+3)/7) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+1 := ⟨n-1,by omega⟩
  have hnR : (5:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast hn
  exact MainMaximal.from_diagonal (weakened_bush_endpoint hn) (by linarith)

end
end KakeyaFormal.BushIteration
