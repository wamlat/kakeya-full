import ProjectiveSphereNet
import EuclideanSplit
import LogLoss

/-! The whole-sphere net has at most N^2 tests at a uniform threshold whenever
its inverse radius has a fixed polylogarithmic budget. Its cardinality is the
actual constructed finite set's cardinality, not an assumed count. -/
namespace KakeyaFormal.SphereNetBudget
open ProjectiveSphereNet ProjectiveGeometry
noncomputable section

/-- A net of the entire nonempty unit sphere itself forces positive radius. -/
theorem theta_pos {k : ℕ} {theta : ℝ} (T : Net k theta) : 0 < theta := by
  obtain ⟨w,_,hw⟩ := T.covers (EuclideanSplit.axisUnit k) (EuclideanSplit.axisUnit_norm k)
  exact (projectiveDistance_nonneg _ _).trans_lt hw

/-- The actual net count has the exact dimension-times-log exponent. -/
theorem polylog_count {k : ℕ} {theta B q N : ℝ} (T : Net k theta)
    (hN : 1 ≤ N)
    (htheta : 1/theta ≤ B*(Real.log (2*N))^q) :
    (T.points.card:ℝ) ≤ packingConstant k*B^k*(Real.log (2*N))^(q*(k:ℝ)) := by
  have hp := theta_pos T
  have hlog : 0 ≤ Real.log (2*N) := Real.log_nonneg (by linarith)
  have hpack : 0 ≤ packingConstant k := zero_le_one.trans (packingConstant_ge_one k)
  have hh := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (one_div_nonneg.mpr hp.le) htheta k) hpack
  have he : ((Real.log (2*N))^q)^k = (Real.log (2*N))^(q*(k:ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hlog]
  have hh' := T.card_bound.trans hh
  rw [mul_pow,he] at hh'
  simpa only [mul_assoc] using hh'

/-- The threshold depends only on fixed k,B,q. The original scale, actual
net, radius and test population all occur after it. The k=0 case is included. -/
theorem exists_threshold (k : ℕ) {B q : ℝ} (hB : 0 < B) (hq : 0 ≤ q) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ {N theta : ℝ}, N₀ ≤ N →
      ∀ T : Net k theta, 1/theta ≤ B*(Real.log (2*N))^q →
        (T.points.card:ℝ) ≤ N^2 := by
  obtain ⟨C,hC,hbound⟩ := log_power_uniform_bound
    (mul_nonneg hq (Nat.cast_nonneg k)) (by norm_num : (0:ℝ)<1)
  let H := packingConstant k*B^k*C
  refine ⟨max 1 H,le_max_left _ _,?_⟩
  intro N theta hN T htheta
  have hN1 : 1 ≤ N := (le_max_left 1 H).trans hN
  have hHN : H ≤ N := (le_max_right 1 H).trans hN
  have hh := polylog_count T hN1 htheta
  have hlog := hbound N hN1
  rw [Real.rpow_one] at hlog
  have hcoef : 0 ≤ packingConstant k*B^k := by
    exact mul_nonneg (zero_le_one.trans (packingConstant_ge_one k)) (pow_nonneg hB.le k)
  have hs := mul_le_mul_of_nonneg_left hlog hcoef
  calc
    _ ≤ packingConstant k*B^k*(Real.log (2*N))^(q*(k:ℝ)) := hh
    _ ≤ packingConstant k*B^k*(C*N) := hs
    _ = H*N := by dsimp [H]; ring
    _ ≤ N^2 := by nlinarith

/-- An actual product test set preserves its fixed spatial prefactor. -/
theorem product_count {k : ℕ} {theta N D P : ℝ} (T : Net k theta)
    (hn : (T.points.card:ℝ) ≤ N^2) (hN : 0 < N) (hP : 0 ≤ P)
    {X : Type*} (S : Finset X) (hS : (S.card:ℝ) ≤ P*N^D) :
    ((S ×ˢ T.points).card:ℝ) ≤ P*N^(D+2) := by
  rw [Finset.card_product,Nat.cast_mul]
  have hh := mul_le_mul hS hn (Nat.cast_nonneg _) (mul_nonneg hP (Real.rpow_nonneg hN.le D))
  have he : (P*N^D)*N^2=P*N^(D+2) := by
    rw [Real.rpow_add hN,Real.rpow_two]
    ring
  exact hh.trans_eq he

/-- Uniform form for the actual high-cell-by-net tests. A unit spatial
prefactor gives literally N^(ambient+2), and general fixed P is retained. -/
theorem exists_product_threshold (k : ℕ) {B q : ℝ} (hB : 0 < B) (hq : 0 ≤ q) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ {N theta D P : ℝ}, N₀ ≤ N →
      ∀ T : Net k theta, 1/theta ≤ B*(Real.log (2*N))^q → 0 ≤ P →
      ∀ {X : Type*} (S : Finset X), (S.card:ℝ) ≤ P*N^D →
        ((S ×ˢ T.points).card:ℝ) ≤ P*N^(D+2) := by
  obtain ⟨N₀,hN₀,hbound⟩ := exists_threshold k hB hq
  refine ⟨N₀,hN₀,?_⟩
  intro N theta D P hN T htheta hP X S hS
  exact product_count T (hbound hN T htheta) (zero_lt_one.trans_le (hN₀.trans hN)) hP S hS

end
end KakeyaFormal.SphereNetBudget
