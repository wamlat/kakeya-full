import Bush
import PositiveTwoEndsPivot
import AbsoluteCapGlobalization
import Endpoint

/-! The actual finite bush iterations of Appendix A.2 and A.3. Each stage
uses the proved bush estimate in the actual lifted ambient space, the direct
positive-density pivot, and geometric removal of two ends. In particular the
early lifted exponents need not satisfy the narrower condition d'>3. -/
namespace KakeyaFormal.BushIteration
noncomputable section

/-- Direct positive-p pivot followed by actual two-ends globalization. The
only analytic inputs are the two displayed estimates on actual configurations. -/
theorem direct_pivot {k : ℕ} {m d d' p q : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p)
    (hlift : DiscreteEstimate (k+3) d d' q)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 0 < p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (hDlo : 1 ≤ KakeyaScalar.pivotSet m d')
    (hDhi : KakeyaScalar.pivotSet m d' < m)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+
      (KakeyaScalar.pivotDensity p q-2)/3) :
    DiscreteEstimate (k+2) m (KakeyaScalar.pivotSet m d')
      (max (KakeyaScalar.pivotSet m d') (KakeyaScalar.pivotDensity p q)) :=
  (PositiveTwoEndsPivot.from_base_and_lift hbase hlift hm hmn hp hd hq hDhi
    hmargin).remove_two_ends_all_density (zero_le_one.trans hm) hDlo

/-- Weakening just the set exponent costs no density power or geometric
normalization: the same constant works at every original scale in (0,1]. -/
theorem weaken_set {n : ℕ} {m D d p : ℝ}
    (h : DiscreteEstimate n m D p) (hd : d ≤ D) :
    DiscreteEstimate n m d p := by
  intro geom eps heps
  obtain ⟨c,hc,hbound⟩ := h geom eps heps
  refine ⟨c,hc,fun F => ?_⟩
  have hpow : F.δ^(m-d+eps) ≤ F.δ^(m-D+eps) :=
    Real.rpow_le_rpow_of_exponent_ge F.scale_pos F.scale_le_one (by linarith)
  have hcoef : 0 ≤ c*F.A⁻¹ := mul_nonneg hc.le (inv_nonneg.mpr
    (zero_le_one.trans F.cap_ge_one))
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow hcoef)
    (Real.rpow_nonneg F.density_pos.le _)) (Nat.cast_nonneg F.M)).trans (hbound F)

/-- One literal Appendix A.2 step, with the actual bush lifted input supplied
internally. No lifted estimate, marked family, angular split, or two ends is a premise. -/
theorem bush_step {n : ℕ} {d : ℝ} (hn : 5 ≤ n)
    (hlo : ((n:ℝ)+1)/2 ≤ d) (hhi : d ≤ (4*(n:ℝ)+4)/7)
    (hbase : DiagonalDiscreteEstimate n d) :
    DiagonalDiscreteEstimate n ((4*(n:ℝ)+d+4)/8) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+2 := ⟨n-2,by omega⟩
  have hnR : (5:ℝ) ≤ (k+2:ℕ) := by exact_mod_cast hn
  obtain ⟨hd,_,hq,hC,hCD,hDm,hmargin⟩ :=
    KakeyaScalar.bush_diagonal_domain hnR hlo hhi
  obtain ⟨hset,hdensity,_,hmarginId⟩ :=
    KakeyaScalar.bush_substitution (k+2:ℕ) d
  have hlift : DiscreteEstimate (k+3) d ((d+2)/2) ((d+2)/2) :=
    Bush.bush_discrete_estimate (k+2) (by linarith)
  have H := direct_pivot hbase hlift (by linarith : (1:ℝ) ≤ (k+2:ℕ)-1)
    (by push_cast; linarith : ((k+2:ℕ):ℝ)-1+1 ≤ (k:ℝ)+2)
    (by linarith) (by linarith) hq
    (by rw [hset]; linarith : 1 ≤ KakeyaScalar.pivotSet ((k+2:ℕ)-1) ((d+2)/2))
    (by rw [hset]; exact hDm)
    (by rw [hset,hdensity]; convert hmargin using 1; linarith)
  rw [hset,hdensity,max_eq_left hCD.le] at H
  exact H

/-- Appendix A.3 weakens only the lifted set exponent. The density exponent
is still (d+2)/2, and the actual bush estimate is the sole lifted source. -/
theorem weakened_bush_step {n : ℕ} {d : ℝ} (hn : 5 ≤ n)
    (hlo : ((n:ℝ)+1)/2 ≤ d) (hhi : d ≤ (4*(n:ℝ)+3)/7)
    (hbase : DiagonalDiscreteEstimate n d) :
    DiagonalDiscreteEstimate n ((4*(n:ℝ)+d+3)/8) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+2 := ⟨n-2,by omega⟩
  have hnR : (5:ℝ) ≤ (k+2:ℕ) := by exact_mod_cast hn
  obtain ⟨hd,_,hq,hC,hCD,hDm,hmargin⟩ :=
    KakeyaScalar.weakened_bush_diagonal_domain hnR hlo hhi
  obtain ⟨hset,hdensity,hmarginId⟩ :=
    KakeyaScalar.weakened_bush_substitution (k+2:ℕ) d
  have hlift : DiscreteEstimate (k+3) d ((d+1)/2) ((d+2)/2) :=
    weaken_set (Bush.bush_discrete_estimate (k+2) (by linarith)) (by linarith)
  have H := direct_pivot hbase hlift (by linarith : (1:ℝ) ≤ (k+2:ℕ)-1)
    (by push_cast; linarith : ((k+2:ℕ):ℝ)-1+1 ≤ (k:ℝ)+2)
    (by linarith) (by linarith) hq
    (by rw [hset]; linarith : 1 ≤ KakeyaScalar.pivotSet ((k+2:ℕ)-1) ((d+1)/2))
    (by rw [hset]; exact hDm)
    (by rw [hset,hdensity]; convert hmargin using 1; linarith)
  rw [hset,hdensity,max_eq_left hCD.le] at H
  exact H

/-- The common initial exponent is itself supplied by the actual bush
construction in the original ambient space. -/
theorem initial {n : ℕ} (hn : 5 ≤ n) :
    DiagonalDiscreteEstimate n (((n:ℝ)+1)/2) := by
  obtain ⟨k,rfl⟩ : ∃ k, n = k+1 := ⟨n-1,by omega⟩
  have hnR : (5:ℝ) ≤ (k+1:ℕ) := by exact_mod_cast hn
  have H := Bush.bush_discrete_estimate k (m := ((k+1:ℕ):ℝ)-1) (by linarith)
  have he : (((k+1:ℕ):ℝ)-1+2)/2 = (((k+1:ℕ):ℝ)+1)/2 := by ring
  simpa only [DiagonalDiscreteEstimate,he] using H

/-- Every finite A.2 iterate is an actual unrestricted diagonal estimate,
not merely a scalar recurrence with an assumed induction property. -/
theorem bush_stage {n : ℕ} (hn : 5 ≤ n) (j : ℕ) :
    DiagonalDiscreteEstimate n
      (KakeyaScalar.diagonal n 4 (((n:ℝ)+1)/2) j) := by
  have hnR : (5:ℝ) ≤ n := by exact_mod_cast hn
  have hseed : ((n:ℝ)+1)/2 < KakeyaScalar.diagonalLimit n 4 := by
    dsimp [KakeyaScalar.diagonalLimit]; linarith
  induction j with
  | zero => simpa only [KakeyaScalar.diagonal] using initial hn
  | succ j ih =>
    obtain ⟨hlo,hhi,_⟩ := KakeyaScalar.diagonal_monotone_and_bounds hseed j
    have H := bush_step hn hlo hhi.le ih
    simpa only [KakeyaScalar.diagonal,add_assoc,add_comm,add_left_comm] using H

/-- Every finite A.3 iterate retains the correct bush density exponent at
the lifted stage before the proved diagonal globalization is applied. -/
theorem weakened_bush_stage {n : ℕ} (hn : 5 ≤ n) (j : ℕ) :
    DiagonalDiscreteEstimate n
      (KakeyaScalar.diagonal n 3 (((n:ℝ)+1)/2) j) := by
  have hnR : (5:ℝ) ≤ n := by exact_mod_cast hn
  have hseed : ((n:ℝ)+1)/2 < KakeyaScalar.diagonalLimit n 3 := by
    dsimp [KakeyaScalar.diagonalLimit]; linarith
  induction j with
  | zero => simpa only [KakeyaScalar.diagonal] using initial hn
  | succ j ih =>
    obtain ⟨hlo,hhi,_⟩ := KakeyaScalar.diagonal_monotone_and_bounds hseed j
    have H := weakened_bush_step hn hlo hhi.le ih
    simpa only [KakeyaScalar.diagonal,add_assoc,add_comm,add_left_comm] using H

/-- The A.2 endpoint is obtained from a finite stage chosen before the actual
configuration for each requested scale loss. This proof uses the bush route. -/
theorem bush_endpoint {n : ℕ} (hn : 5 ≤ n) :
    DiagonalDiscreteEstimate n ((4*(n:ℝ)+4)/7) := by
  have hnR : (5:ℝ) ≤ n := by exact_mod_cast hn
  have hseed : ((n:ℝ)+1)/2 < KakeyaScalar.diagonalLimit n 4 := by
    dsimp [KakeyaScalar.diagonalLimit]; linarith
  exact DiscreteEstimate.of_limit (KakeyaScalar.diagonal_tendsto n 4 (((n:ℝ)+1)/2))
    (fun j => (KakeyaScalar.diagonal_monotone_and_bounds hseed j).2.1.le)
    (bush_stage hn)

/-- The A.3 endpoint follows from its own actual finite stages, with only
the lifted set power weakened and no density-exponent substitution. -/
theorem weakened_bush_endpoint {n : ℕ} (hn : 5 ≤ n) :
    DiagonalDiscreteEstimate n ((4*(n:ℝ)+3)/7) := by
  have hnR : (5:ℝ) ≤ n := by exact_mod_cast hn
  have hseed : ((n:ℝ)+1)/2 < KakeyaScalar.diagonalLimit n 3 := by
    dsimp [KakeyaScalar.diagonalLimit]; linarith
  exact DiscreteEstimate.of_limit (KakeyaScalar.diagonal_tendsto n 3 (((n:ℝ)+1)/2))
    (fun j => (KakeyaScalar.diagonal_monotone_and_bounds hseed j).2.1.le)
    (weakened_bush_stage hn)

end
end KakeyaFormal.BushIteration
