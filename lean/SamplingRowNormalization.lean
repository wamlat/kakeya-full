import SamplingApplication
import Configurations

/-! Equalizing full tube means before coupled sampling. Full and marked
probabilities receive the same row factor, preserving all tube indices and
positive support. This avoids unsupported broadness inheritance under density
binning after sampling. -/
namespace KakeyaFormal.SamplingRowNormalization
open Finset KakeyaSamplingApplication
open scoped BigOperators
noncomputable section

variable {T C : Type*} [Fintype C]

def factor (p : T → C → ℝ) (mu : ℝ) (t : T) : ℝ := mu/fullMean p t
def full (p : T → C → ℝ) (mu : ℝ) : T → C → ℝ := fun t c => factor p mu t*p t c
def marked (p q : T → C → ℝ) (mu : ℝ) : T → C → ℝ := fun t c => factor p mu t*q t c

theorem factor_bounds (p : T → C → ℝ) {mu R : ℝ}
    (hmu : 0 < mu) (hR : 0 < R)
    (hmean : ∀ t, mu ≤ fullMean p t ∧ fullMean p t ≤ R*mu) (t : T) :
    0 < factor p mu t ∧ factor p mu t ≤ 1 ∧ 1/R ≤ factor p mu t := by
  have hm : 0 < fullMean p t := hmu.trans_le (hmean t).1
  refine ⟨div_pos hmu hm,(div_le_one hm).mpr (hmean t).1,?_⟩
  apply (le_div_iff₀ hm).mpr
  have hh : fullMean p t/R ≤ mu := (div_le_iff₀ hR).mpr (by simpa only [mul_comm] using (hmean t).2)
  simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using hh

theorem probabilities (p q : T → C → ℝ) {mu : ℝ} (hmu : 0 < mu)
    (hmean : ∀ t, mu ≤ fullMean p t)
    (hq : ∀ t c, 0 ≤ q t c) (hqp : ∀ t c, q t c ≤ p t c) (hp : ∀ t c, p t c ≤ 1) :
    ∀ t c, 0 ≤ marked p q mu t c ∧ marked p q mu t c ≤ full p mu t c ∧ full p mu t c ≤ 1 := by
  intro t c
  have hm : 0 < fullMean p t := hmu.trans_le (hmean t)
  have hf : 0 ≤ factor p mu t := (div_pos hmu hm).le
  have hf1 : factor p mu t ≤ 1 := (div_le_one hm).mpr (hmean t)
  refine ⟨mul_nonneg hf (hq t c),mul_le_mul_of_nonneg_left (hqp t c) hf,?_⟩
  exact (mul_le_mul_of_nonneg_left (hp t c) hf).trans (by simpa only [mul_one] using hf1)

/-- The new full and marked probabilities are pointwise below their original
weights, as required by the geometric positive-support realization bridge. -/
theorem pointwise_domination (p q : T → C → ℝ) {mu : ℝ} (hmu : 0 < mu)
    (hmean : ∀ t, mu ≤ fullMean p t)
    (hq : ∀ t c, 0 ≤ q t c) (hqp : ∀ t c, q t c ≤ p t c) :
    ∀ t c, full p mu t c ≤ p t c ∧ marked p q mu t c ≤ q t c := by
  intro t c
  have hm : 0 < fullMean p t := hmu.trans_le (hmean t)
  have hf : factor p mu t ≤ 1 := (div_le_one hm).mpr (hmean t)
  exact ⟨(mul_le_mul_of_nonneg_right hf ((hq t c).trans (hqp t c))).trans_eq (one_mul _),
    (mul_le_mul_of_nonneg_right hf (hq t c)).trans_eq (one_mul _)⟩

theorem full_mean (p : T → C → ℝ) {mu : ℝ} (hmean : ∀ t, fullMean p t ≠ 0) (t : T) :
    fullMean (full p mu) t = mu := by
  unfold fullMean full
  rw [← mul_sum]
  change (mu/fullMean p t)*fullMean p t=mu
  exact div_mul_cancel₀ _ (hmean t)

theorem full_support (p : T → C → ℝ) {mu : ℝ} (hmu : 0 < mu)
    (hmean : ∀ t, 0 < fullMean p t) (t : T) (c : C) :
    0 < full p mu t c ↔ 0 < p t c :=
  mul_pos_iff_of_pos_left (div_pos hmu (hmean t))

theorem marked_support (p q : T → C → ℝ) {mu : ℝ} (hmu : 0 < mu)
    (hmean : ∀ t, 0 < fullMean p t) (t : T) (c : C) :
    0 < marked p q mu t c ↔ 0 < q t c :=
  mul_pos_iff_of_pos_left (div_pos hmu (hmean t))

theorem marked_mean_bounds [Fintype T] (p q : T → C → ℝ) {mu R : ℝ}
    (hmu : 0 < mu) (hR : 0 < R)
    (hmean : ∀ t, mu ≤ fullMean p t ∧ fullMean p t ≤ R*mu)
    (hq : ∀ t c, 0 ≤ q t c) (c : C) :
    (1/R)*markedMean q c ≤ markedMean (marked p q mu) c ∧
      markedMean (marked p q mu) c ≤ markedMean q c := by
  constructor
  · unfold markedMean marked
    rw [mul_sum]
    exact sum_le_sum fun t _ => mul_le_mul_of_nonneg_right (factor_bounds p hmu hR hmean t).2.2 (hq t c)
  · unfold markedMean marked
    apply sum_le_sum
    intro t _
    exact (mul_le_mul_of_nonneg_right (factor_bounds p hmu hR hmean t).2.1 (hq t c)).trans_eq (one_mul _)

theorem marked_mass_lower [Fintype T] (p q : T → C → ℝ) {mu R : ℝ}
    (hmu : 0 < mu) (hR : 0 < R)
    (hmean : ∀ t, mu ≤ fullMean p t ∧ fullMean p t ≤ R*mu)
    (hq : ∀ t c, 0 ≤ q t c) :
    (1/R)*(∑ c, markedMean q c) ≤ ∑ c, markedMean (marked p q mu) c := by
  rw [mul_sum]
  exact sum_le_sum fun c _ => (marked_mean_bounds p q hmu hR hmean hq c).1

theorem ball_mean {B : Type*} (p : T → C → ℝ) (mu : ℝ)
    (ball : B → C → Bool) (t : T) (b : B) :
    ballMean (full p mu) ball t b = factor p mu t*ballMean p ball t b := by
  unfold ballMean full
  rw [mul_sum]
  apply sum_congr rfl
  intro c _
  cases ball b c <;> simp

/-- Relative full-ball expectations retain exactly the original coefficient. -/
theorem ball_relative {B : Type*} (p : T → C → ℝ) (ball : B → C → Bool)
    {mu : ℝ} (hmu : 0 < mu) (hmean : ∀ t, 0 < fullMean p t)
    (K : T → B → ℝ) (hball : ∀ t b, ballMean p ball t b ≤ K t b*fullMean p t) :
    ∀ t b, ballMean (full p mu) ball t b ≤ K t b*mu := by
  intro t b
  rw [ball_mean]
  have hf : 0 < factor p mu t := div_pos hmu (hmean t)
  have hh := mul_le_mul_of_nonneg_left (hball t b) hf.le
  have hid : factor p mu t*(K t b*fullMean p t)=K t b*mu := by
    unfold factor
    field_simp [(hmean t).ne']
  rwa [hid] at hh

theorem cap_mean_le [Fintype T] {A : Type*} (p q : T → C → ℝ) (cap : A → T → Bool)
    {mu R : ℝ} (hmu : 0 < mu) (hR : 0 < R)
    (hmean : ∀ t, mu ≤ fullMean p t ∧ fullMean p t ≤ R*mu)
    (hq : ∀ t c, 0 ≤ q t c) (c : C) (a : A) :
    capMean (marked p q mu) cap c a ≤ capMean q cap c a := by
  unfold capMean marked
  apply sum_le_sum
  intro t _
  cases hh : cap a t
  · simp
  · simp only [ite_true]
    exact (mul_le_mul_of_nonneg_right (factor_bounds p hmu hR hmean t).2.1 (hq t c)).trans_eq (one_mul _)

/-- Expected marked broadness loses only the fixed row ratio R. This is
established before sampling, so the eventual one-tenth fraction is unchanged. -/
theorem cap_relative [Fintype T] {A : Type*} (p q : T → C → ℝ) (cap : A → T → Bool)
    {mu R K : ℝ} (hmu : 0 < mu) (hR : 0 < R) (hK : 0 ≤ K)
    (hmean : ∀ t, mu ≤ fullMean p t ∧ fullMean p t ≤ R*mu)
    (hq : ∀ t c, 0 ≤ q t c) (c : C) (a : A)
    (hcap : capMean q cap c a ≤ K*markedMean q c) :
    capMean (marked p q mu) cap c a ≤ (R*K)*markedMean (marked p q mu) c := by
  have hmark := (marked_mean_bounds p q hmu hR hmean hq c).1
  have hh := mul_le_mul_of_nonneg_left hmark (mul_nonneg hR.le hK)
  have hid : (R*K)*((1/R)*markedMean q c)=K*markedMean q c := by field_simp
  rw [hid] at hh
  exact (cap_mean_le p q cap hmu hR hmean hq c a).trans (hcap.trans hh)

/-- Source mean bounds yield a fixed equalizing coefficient and ratio. -/
theorem source_parameters {c0 C0 lam N : ℝ}
    (hc0 : 0 < c0) (hC : c0 ≤ C0) (hlam : 0 < lam) (hN : 0 < N) :
    let cEq := min c0 1
    0 < cEq ∧ cEq ≤ 1 ∧ 1 ≤ C0/cEq ∧
    (∀ x : ℝ, c0*lam*N ≤ x → x ≤ C0*lam*N →
      cEq*lam*N ≤ x ∧ x ≤ (C0/cEq)*(cEq*lam*N)) := by
  dsimp
  have heq : 0 < min c0 1 := lt_min hc0 zero_lt_one
  refine ⟨heq,min_le_right _ _,(one_le_div heq).mpr ((min_le_left _ _).trans hC),?_⟩
  intro x hlo hhi
  constructor
  · have hh := mul_le_mul_of_nonneg_right (min_le_left c0 1) (mul_pos hlam hN).le
    have hle : min c0 1*lam*N ≤ c0*lam*N := by simpa only [mul_assoc] using hh
    exact hle.trans hlo
  · have hid : (C0/min c0 1)*(min c0 1*lam*N)=C0*lam*N := by field_simp [heq.ne']
    rwa [hid]

/-- A narrow realization has the exact factor-two density required by the
marked core, with density bounded by one and all original tube indices kept. -/
theorem comparable_of_narrow {k M : ℕ} (F : TubeFamily k M)
    {δ cEq lam : ℝ} (hc : 0 < cEq) (hc1 : cEq ≤ 1)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hband : ∀ i, (2/3:ℝ)*(cEq*lam/δ) ≤ (F.shade i).card ∧
      ((F.shade i).card:ℝ) ≤ (4/3:ℝ)*(cEq*lam/δ)) :
    0 < (2/3:ℝ)*cEq*lam ∧ (2/3:ℝ)*cEq*lam ≤ 1 ∧
      F.Comparable δ ((2/3:ℝ)*cEq*lam) := by
  refine ⟨by positivity,?_,?_⟩
  · have hh := mul_le_mul hc1 hlam1 hlam.le zero_le_one
    nlinarith
  · intro i
    constructor
    · convert (hband i).1 using 1
      ring
    · convert (hband i).2 using 1
      ring

end
end KakeyaFormal.SamplingRowNormalization
