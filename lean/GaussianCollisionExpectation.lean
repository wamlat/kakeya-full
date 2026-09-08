import GaussianCollision
import GaussianCollisionKernel

/-! The expected cardinality of actual ordered distinct-pair collisions.
Original cap-four control and separation discharge every pair and shell bound;
the final theorem contains no probability or expected-count premise. -/
namespace KakeyaFormal.GaussianCollisionExpectation
open MeasureTheory ProbabilityTheory GaussianMatrix GaussianCollision
open GaussianCollisionKernel GaussianConditioning ProjectiveAngleComparison ProjectiveGeometry
open scoped ENNReal BigOperators RealInnerProductSpace
noncomputable section

def pairEvent {M : ℕ} (F : TubeFamily 7 M) (K δ : ℝ) (i j : Fin M) : Set (Sample 5 7) :=
  if i=j then ∅ else collisionEvent K δ (F.tube i).direction (F.tube j).direction

theorem pairEvent_measurable {M : ℕ} (F : TubeFamily 7 M) (K δ : ℝ) (i j : Fin M) :
    MeasurableSet (pairEvent F K δ i j) := by
  unfold pairEvent
  split_ifs
  · exact MeasurableSet.empty
  · exact collisionEvent_measurable _ _ _ _

def orderedCollisions {M : ℕ} (F : TubeFamily 7 M) (K δ : ℝ) (ω : Sample 5 7) :
    Finset (Fin M × Fin M) := by
  classical
  exact Finset.univ.filter (fun p => ω∈pairEvent F K δ p.1 p.2)

theorem mem_orderedCollisions {M : ℕ} (F : TubeFamily 7 M) (K δ : ℝ)
    (ω : Sample 5 7) (i j : Fin M) :
    (i,j)∈orderedCollisions F K δ ω ↔ i≠j ∧
      ω∈collisionEvent K δ (F.tube i).direction (F.tube j).direction := by
  classical
  by_cases h : i=j <;> simp [orderedCollisions,pairEvent,h]

/-- The nonnegative random count is the cardinality of the literal original pair set. -/
def collisionCount {M : ℕ} (F : TubeFamily 7 M) (K δ : ℝ) (ω : Sample 5 7) : ℝ≥0∞ :=
  (orderedCollisions F K δ ω).card

theorem count_eq_sum {M : ℕ} (F : TubeFamily 7 M) (K δ : ℝ) (ω : Sample 5 7) :
    collisionCount F K δ ω =
      ∑ i : Fin M, ∑ j : Fin M, (pairEvent F K δ i j).indicator (fun _ => (1:ℝ≥0∞)) ω := by
  classical
  simp only [collisionCount,orderedCollisions,Finset.card_eq_sum_ones,Nat.cast_sum,
    Finset.sum_filter,Set.indicator_apply,Fintype.sum_prod_type,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem count_measurable {M : ℕ} (F : TubeFamily 7 M) (K δ : ℝ) :
    Measurable (collisionCount F K δ) := by
  change Measurable (fun ω => collisionCount F K δ ω)
  simp_rw [count_eq_sum]
  exact Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ =>
    measurable_const.indicator (pairEvent_measurable F K δ i j)))

theorem expected_count_eq {M : ℕ} (F : TubeFamily 7 M) (K δ : ℝ) :
    (∫⁻ ω, collisionCount F K δ ω ∂law 5 7) =
      ∑ i : Fin M, ∑ j : Fin M, law 5 7 (pairEvent F K δ i j) := by
  simp_rw [count_eq_sum]
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ (fun j _ =>
    measurable_const.indicator (pairEvent_measurable F K δ i j)))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_finsetSum _ (fun j _ =>
    measurable_const.indicator (pairEvent_measurable F K δ i j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [lintegral_indicator (pairEvent_measurable F K δ i j),setLIntegral_const,one_mul]

/-- Actual pairwise collision probabilities are controlled by the original
chord kernel; separation makes the original projective angle strictly positive. -/
theorem pair_probability {M : ℕ} (F : TubeFamily 7 M) {K δ : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ) (hsep : F.Separated δ) (i j : Fin M) :
    law 5 7 (pairEvent F K δ i j) ≤
      ENNReal.ofReal (collisionConstant K *
        kernel δ (projectiveDistance (F.tube j).direction (F.tube i).direction)) := by
  by_cases hij : i=j
  · simp [pairEvent,hij]
  have hd := hsep i j hij
  have hchord := (chord_angle_bounds _ _ (F.tube i).unit_direction (F.tube j).unit_direction).2
  have hpsi : 0 < angle (F.tube i).direction (F.tube j).direction :=
    hδ.trans_le (hd.trans hchord)
  have hp := collision_probability hK hδ.le _ _
    (F.tube i).unit_direction (F.tube j).unit_direction hpsi
  rw [pairEvent,if_neg hij]
  apply hp.trans
  have hdiv := div_le_div_of_nonneg_left hδ.le (hδ.trans_le hd) hchord
  have hpow := pow_le_pow_left₀ (div_nonneg hδ.le hpsi.le) hdiv 4
  rw [projective_symm] at hd
  have hk : ((δ/angle (F.tube i).direction (F.tube j).direction)^4) ≤
      kernel δ (projectiveDistance (F.tube j).direction (F.tube i).direction) := by
    unfold kernel
    rw [max_eq_left hd,projective_symm]
    exact hpow
  rw [ENNReal.ofReal_mul (collisionConstant_pos K).le]
  gcongr
  exact (min_le_right _ _).trans (ENNReal.ofReal_le_ofReal hk)

def expectationCoefficient (K : ℝ) : ℝ := collisionConstant K*rowCoefficient 6

theorem expectationCoefficient_pos (K : ℝ) : 0 < expectationCoefficient K :=
  mul_pos (collisionConstant_pos K) (rowCoefficient_pos 6)

/-- The expected number of ACTUAL ordered collisions is O_K(A M log(2/delta)).
The constant is fixed before the original family, scale and cap coefficient.
Empty families and zero cap coefficients are included without dividing by M. -/
theorem expected_count_bound {M : ℕ} (F : TubeFamily 7 M) {K δ A : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A)
    (hsep : F.Separated δ) (hcap : F.CapBound δ 4 A) :
    (∫⁻ ω, collisionCount F K δ ω ∂law 5 7) ≤
      ENNReal.ofReal (expectationCoefficient K*A*(M:ℝ)*Real.log (2/δ)) := by
  rw [expected_count_eq]
  have hnon (i j : Fin M) : 0 ≤ collisionConstant K*
      kernel δ (projectiveDistance (F.tube j).direction (F.tube i).direction) :=
    mul_nonneg (collisionConstant_pos K).le (kernel_nonneg _ _)
  calc
    _ ≤ ∑ i : Fin M, ∑ j : Fin M, ENNReal.ofReal (collisionConstant K*
        kernel δ (projectiveDistance (F.tube j).direction (F.tube i).direction)) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => pair_probability F hK hδ hsep i j))
    _ = ENNReal.ofReal (∑ i : Fin M, ∑ j : Fin M, collisionConstant K*
        kernel δ (projectiveDistance (F.tube j).direction (F.tube i).direction)) := by
      simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hnon _ j)]
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun i _ => Finset.sum_nonneg (fun j _ => hnon i j))).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = ∑ i : Fin M, collisionConstant K*(∑ j : Fin M,
            kernel δ (projectiveDistance (F.tube j).direction (F.tube i).direction)) := by
          simp only [Finset.mul_sum]
        _ ≤ ∑ _i : Fin M, collisionConstant K*(rowCoefficient 6*A*Real.log (2/δ)) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
            (family_row_bound F hδ hδ1 hA hcap i) (collisionConstant_pos K).le)
        _ = _ := by simp [expectationCoefficient]; ring

end
end KakeyaFormal.GaussianCollisionExpectation
