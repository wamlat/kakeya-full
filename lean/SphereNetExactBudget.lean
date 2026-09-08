import SphereNetBudget

/-! The literal high-cell-by-sphere-net count, including absorption of any
fixed spatial prefactor into one uniform threshold. The net is the actual
constructed whole-sphere net; its cardinality is never a supplied hypothesis. -/
namespace KakeyaFormal.SphereNetExactBudget
open ProjectiveSphereNet ProjectiveGeometry
noncomputable section

/-- A fixed polylogarithmic inverse radius gives an actual linear-in-N net
bound. The constant is chosen before N, theta and the net. -/
theorem linear_count_budget (k : ℕ) {B q : ℝ} (hB : 0 < B) (hq : 0 ≤ q) :
    ∃ H : ℝ, 0 < H ∧ ∀ {N theta : ℝ}, 1 ≤ N →
      ∀ T : Net k theta, 1/theta ≤ B*(Real.log (2*N))^q →
        (T.points.card:ℝ) ≤ H*N := by
  obtain ⟨C,hC,hbound⟩ := log_power_uniform_bound
    (mul_nonneg hq (Nat.cast_nonneg k)) (by norm_num : (0:ℝ)<1)
  have hpack : 0 < packingConstant k := zero_lt_one.trans_le (packingConstant_ge_one k)
  refine ⟨packingConstant k*B^k*C,mul_pos (mul_pos hpack (pow_pos hB k)) hC,?_⟩
  intro N theta hN T htheta
  have hlog := hbound N hN
  rw [Real.rpow_one] at hlog
  calc
    _ ≤ packingConstant k*B^k*(Real.log (2*N))^(q*(k:ℝ)) :=
      SphereNetBudget.polylog_count T hN htheta
    _ ≤ packingConstant k*B^k*(C*N) :=
      mul_le_mul_of_nonneg_left hlog (mul_nonneg hpack.le (pow_nonneg hB.le k))
    _ = (packingConstant k*B^k*C)*N := by ring

/-- The fixed spatial prefactor P is absorbed without increasing the final
exponent D+2. The threshold depends only on k,B,q,P, including for k=0 or q=0;
the real exponent D, actual cell set and actual net all occur afterwards. -/
theorem exists_product_threshold (k : ℕ) {B q P : ℝ}
    (hB : 0 < B) (hq : 0 ≤ q) (hP : 0 < P) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ {N theta D : ℝ}, N₀ ≤ N →
      ∀ T : Net k theta, 1/theta ≤ B*(Real.log (2*N))^q →
      ∀ {X : Type*} (S : Finset X), (S.card:ℝ) ≤ P*N^D →
        ((S ×ˢ T.points).card:ℝ) ≤ N^(D+2) := by
  obtain ⟨H,hH,hbound⟩ := linear_count_budget k hB hq
  refine ⟨max 1 (P*H),le_max_left _ _,?_⟩
  intro N theta D hN T htheta X S hS
  have hN1 : 1 ≤ N := (le_max_left 1 (P*H)).trans hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  have hPH : P*H ≤ N := (le_max_right 1 (P*H)).trans hN
  have hnet := hbound hN1 T htheta
  rw [Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ (P*N^D)*(H*N) := mul_le_mul hS hnet (Nat.cast_nonneg _)
      (mul_nonneg hP.le (Real.rpow_nonneg hN0.le D))
    _ = (P*H)*N*N^D := by ring
    _ ≤ N*N*N^D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hPH hN0.le) (Real.rpow_nonneg hN0.le D)
    _ = N^(D+2) := by rw [Real.rpow_add hN0,Real.rpow_two]; ring

/-- The literal simultaneous angular test count includes one marked-cell
lower-tail event and every net-cap upper-tail event at each cell. Both are
absorbed into the same exponent D+2, with all fixed prefactors in the threshold. -/
theorem exists_augmented_threshold (k : ℕ) {B q P : ℝ}
    (hB : 0 < B) (hq : 0 ≤ q) (hP : 0 < P) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ {N theta D : ℝ}, N₀ ≤ N →
      ∀ T : Net k theta, 1/theta ≤ B*(Real.log (2*N))^q →
      ∀ {X : Type*} (S : Finset X), (S.card:ℝ) ≤ P*N^D →
        (S.card:ℝ)*(1+(T.points.card:ℝ)) ≤ N^(D+2) := by
  obtain ⟨H,hH,hbound⟩ := linear_count_budget k hB hq
  refine ⟨max 1 (P*(1+H)),le_max_left _ _,?_⟩
  intro N theta D hN T htheta X S hS
  have hN1 : 1 ≤ N := (le_max_left 1 (P*(1+H))).trans hN
  have hN0 : 0 < N := zero_lt_one.trans_le hN1
  have hPH : P*(1+H) ≤ N := (le_max_right 1 (P*(1+H))).trans hN
  have hnet := hbound hN1 T htheta
  have haug : 1+(T.points.card:ℝ) ≤ (1+H)*N := by nlinarith
  calc
    _ ≤ (P*N^D)*((1+H)*N) := mul_le_mul hS haug
      (by positivity) (mul_nonneg hP.le (Real.rpow_nonneg hN0.le D))
    _ = (P*(1+H))*N*N^D := by ring
    _ ≤ N*N*N^D := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hPH hN0.le) (Real.rpow_nonneg hN0.le D)
    _ = N^(D+2) := by rw [Real.rpow_add hN0,Real.rpow_two]; ring

end
end KakeyaFormal.SphereNetExactBudget
