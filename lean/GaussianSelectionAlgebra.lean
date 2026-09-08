import Configurations

/-! Scalar population retained by the actual collision graph estimate.
The edge quantity below is the ordered collision count (twice undirected
edge count), matching V^2/(V+E). All constants precede the populations. -/
namespace KakeyaFormal.GaussianSelectionAlgebra
noncomputable section

def denominatorCoefficient (C : ℝ) : ℝ := 1/Real.log 2+4*C

def populationConstant (C : ℝ) : ℝ := 1/(4*denominatorCoefficient C)

theorem denominatorCoefficient_pos {C : ℝ} (hC : 0 < C) :
    0 < denominatorCoefficient C := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold denominatorCoefficient
  positivity

theorem populationConstant_pos {C : ℝ} (hC : 0 < C) : 0 < populationConstant C := by
  have hh := denominatorCoefficient_pos hC
  unfold populationConstant
  positivity

/-- Cap/log factors absorb the diagonal vertex term as well as actual ordered
collisions. No positivity of a scale-dependent cutoff is assumed. -/
theorem denominator_bound {M V E C A L : ℝ} (hM : 0 ≤ M) (hV : V ≤ M)
    (hE : E ≤ 4*C*A*M*L) (hA : 1 ≤ A) (hL : Real.log 2 ≤ L) :
    V+E ≤ denominatorCoefficient C*A*L*M := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 < L := hlog.trans_le hL
  have hAL : Real.log 2 ≤ A*L := by nlinarith
  have hratio : 1 ≤ A*L/Real.log 2 := (le_div_iff₀ hlog).mpr (by simpa using hAL)
  have hdiag := mul_le_mul_of_nonneg_right hratio hM
  unfold denominatorCoefficient
  calc
    V+E ≤ M+4*C*A*M*L := add_le_add hV hE
    _ ≤ (A*L/Real.log 2)*M+4*C*A*M*L := add_le_add (by simpa using hdiag) le_rfl
    _ = _ := by ring

/-- The graph's actual V^2/(V+E) lower bound retains a fixed fraction M/(A L).
E>=0 is essential for arbitrary real variables and automatic for pair counts. -/
theorem population_lower {M V E C A L : ℝ} (hM : 0 ≤ M)
    (hVlo : M/2 ≤ V) (hVhi : V ≤ M) (hE0 : 0 ≤ E)
    (hE : E ≤ 4*C*A*M*L) (hC : 0 < C) (hA : 1 ≤ A) (hL : Real.log 2 ≤ L) :
    populationConstant C*M/(A*L) ≤ V^2/(V+E) := by
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  have hL0 : 0 < L := (Real.log_pos (by norm_num : (1:ℝ)<2)).trans_le hL
  have hD := denominatorCoefficient_pos hC
  by_cases hMp : 0 < M
  · have hVp : 0 < V := (half_pos hMp).trans_le hVlo
    have hden : 0 < V+E := add_pos_of_pos_of_nonneg hVp hE0
    have hbig : 0 < denominatorCoefficient C*A*L*M := by positivity
    have hnum : M^2/4 ≤ V^2 := by nlinarith
    have hh1 := div_le_div_of_nonneg_right hnum hbig.le
    have hh2 := div_le_div_of_nonneg_left (sq_nonneg V) hden
      (denominator_bound hM hVhi hE hA hL)
    have heq : populationConstant C*M/(A*L) =
        (M^2/4)/(denominatorCoefficient C*A*L*M) := by
      unfold populationConstant
      field_simp
    rw [heq]
    exact hh1.trans hh2
  · have hz : M=0 := le_antisymm (le_of_not_gt hMp) hM
    have hvz : V=0 := by linarith
    have hez : E=0 := by rw [hz,mul_zero,zero_mul] at hE; linarith
    simp [hz,hvz,hez]

/-- Cardinalities supply the nonnegative vertex and ordered-pair inputs
internally, including the empty graph. -/
theorem cardinality_lower {M V E : ℕ} {C A L : ℝ}
    (hVlo : (M:ℝ)/2 ≤ V) (hVhi : V ≤ M)
    (hE : (E:ℝ) ≤ 4*C*A*(M:ℝ)*L) (hC : 0 < C) (hA : 1 ≤ A)
    (hL : Real.log 2 ≤ L) :
    populationConstant C*(M:ℝ)/(A*L) ≤ (V:ℝ)^2/((V:ℝ)+(E:ℝ)) :=
  population_lower (Nat.cast_nonneg M) hVlo (by exact_mod_cast hVhi)
    (Nat.cast_nonneg E) hE hC hA hL

end
end KakeyaFormal.GaussianSelectionAlgebra
