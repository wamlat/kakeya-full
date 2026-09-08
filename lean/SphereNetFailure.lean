import SphereNetCapTests
import SphereNetBudget
import SamplingThreshold

/-!
# The actual high-cell and whole-sphere-net failure event

The law is the original independent three-state law on tube-cell coordinates.
Both the marked-cell lower failures and doubled-net-cap upper failures are
included. The same source coefficient 64*(ambient+4) works after absorbing all
fixed geometric prefactors into a threshold chosen before the actual data.
Density and ball failures are deliberately separate events.
-/
namespace KakeyaFormal.SphereNetFailure
open Finset Filter KakeyaSampling KakeyaSamplingApplication ProjectiveSphereNet
  ProjectiveGeometry SphereNetCapTests
open scoped Topology BigOperators
noncomputable section
open Classical

/-- The literal coupled product law, with its original nested probabilities. -/
def law {T C : Type*} [Fintype T] [Fintype C] [DecidableEq T] [DecidableEq C]
    (p q : T → C → ℝ) (hq : ∀ t c, 0 ≤ q t c)
    (hqp : ∀ t c, q t c ≤ p t c) (hp : ∀ t c, p t c ≤ 1) :
    FiniteLaw (Outcome T C) :=
  coupledLaw (flatten p) (flatten q) (fun tc => hq tc.1 tc.2)
    (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2)

/-- The source angular event: a low total marked count at a high cell, or a
large marked count in one actual doubled net cap at a high cell. The non-strict
bad thresholds slightly enlarge the source's bad events. -/
def angularFailure {T C A : Type*} [Fintype T]
    (q : T → C → ℝ) (high : Finset C) (cap : A → T → Bool) (omega : Outcome T C) : Prop :=
  ∃ c ∈ high, markedCellCount omega c ≤ markedMean q c/2 ∨
    ∃ a, markedMean q c/20 ≤ markedCapCount omega cap c a

/-- Each actual finite test gets its own proved Chernoff bound, on the same
product law; no independence between the overlapping tests is assumed. -/
theorem probability_le {T C A : Type*} [Fintype T] [Fintype C] [Fintype A]
    [DecidableEq T] [DecidableEq C]
    (p q : T → C → ℝ) (hq : ∀ t c, 0 ≤ q t c)
    (hqp : ∀ t c, q t c ≤ p t c) (hp : ∀ t c, p t c ≤ 1)
    (high : Finset C) (cap : A → T → Bool) {cut : ℝ}
    (hhigh : ∀ c ∈ high, cut ≤ markedMean q c)
    (hcap : ∀ c ∈ high, ∀ a, 1000*capMean q cap c a ≤ markedMean q c) :
    (law p q hq hqp hp).probability (angularFailure q high cap) ≤
      (high.card : ℝ)*(1+(Fintype.card A : ℝ))*Real.exp (-cut/8) := by
  let D := law p q hq hqp hp
  let J := ↥high × Option A
  let bad : J → Outcome T C → Prop := fun j omega => match j.2 with
    | none => markedCellCount omega j.1.val ≤ markedMean q j.1.val/2
    | some a => markedMean q j.1.val/20 ≤ markedCapCount omega cap j.1.val a
  have hevent : angularFailure q high cap = fun omega => ∃ j : J, bad j omega := by
    funext omega
    apply propext
    constructor
    · rintro ⟨c, hc, h | ⟨a, h⟩⟩
      · exact ⟨(⟨c, hc⟩, none), h⟩
      · exact ⟨(⟨c, hc⟩, some a), h⟩
    · rintro ⟨⟨⟨c, hc⟩, a⟩, h⟩
      rcases a with _ | a
      · exact ⟨c, hc, Or.inl h⟩
      · exact ⟨c, hc, Or.inr ⟨a, h⟩⟩
  have hbound (j : J) : D.probability (bad j) ≤ Real.exp (-cut/8) := by
    have htail : Real.exp (-markedMean q j.1.val/8) ≤ Real.exp (-cut/8) :=
      Real.exp_le_exp.mpr (by linarith [hhigh j.1.val j.1.property])
    apply le_trans _ htail
    rcases j with ⟨c, a⟩
    rcases a with _ | a
    · simpa only [D, law, bad, cell_test_count, cell_test_mean] using
        coupled_test_half_lower (flatten p) (flatten q) (fun tc => hq tc.1 tc.2)
          (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2) (cellMask c.val) true
    · have hsmall : 1000*testMean (flatten p) (flatten q) (capMask cap c.val a) true ≤
          markedMean q c.val := by simpa only [cap_test_mean] using hcap c.val c.property a
      simpa only [D, law, bad, cap_test_count] using
        coupled_test_tiny_mean_upper (flatten p) (flatten q) (fun tc => hq tc.1 tc.2)
          (fun tc => hqp tc.1 tc.2) (fun tc => hp tc.1 tc.2) (capMask cap c.val a) true hsmall
  rw [hevent]
  calc
    _ ≤ ∑ j : J, D.probability (bad j) := D.probability_exists_le_sum bad
    _ ≤ ∑ _j : J, Real.exp (-cut/8) := sum_le_sum (fun j _ => hbound j)
    _ = _ := by simp [J, Fintype.card_prod, Fintype.card_option, mul_assoc, add_comm]

/-- The net bound and fixed spatial prefactor are both absorbed before the
actual net or high-cell set. The exact source total test exponent is ambient+2. -/
theorem test_count_threshold (k : ℕ) {B q P : ℝ}
    (hB : 0 < B) (hq : 0 ≤ q) (hP : 0 ≤ P) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ {N theta : ℝ}, N₀ ≤ N → ∀ net : Net k theta,
      1/theta ≤ B*(Real.log (2*N))^q →
      ∀ {C : Type*} (high : Finset C), (high.card : ℝ) ≤ P*N^((k+1 : ℕ) : ℝ) →
        (high.card : ℝ)*(1+(net.points.card : ℝ)) ≤ N^(((k+1 : ℕ) : ℝ)+2) := by
  obtain ⟨C, hC, hbound⟩ := log_power_uniform_bound
    (mul_nonneg hq (Nat.cast_nonneg k)) (by norm_num : (0:ℝ) < 1)
  let H := packingConstant k*B^k*C
  have hH : 0 ≤ H := by
    dsimp [H]
    exact mul_nonneg (mul_nonneg (zero_le_one.trans (packingConstant_ge_one k))
      (pow_nonneg hB.le k)) hC.le
  refine ⟨max 1 (P*(1+H)), le_max_left _ _, ?_⟩
  intro N theta hN net hinv X high hhigh
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hNpos : 0 < N := zero_lt_one.trans_le hN1
  have hPN : P*(1+H) ≤ N := (le_max_right _ _).trans hN
  have hlog := hbound N hN1
  rw [Real.rpow_one] at hlog
  have hnet : (net.points.card : ℝ) ≤ H*N := by
    have hpoly := SphereNetBudget.polylog_count net hN1 hinv
    have hcoef : 0 ≤ packingConstant k*B^k :=
      mul_nonneg (zero_le_one.trans (packingConstant_ge_one k)) (pow_nonneg hB.le k)
    have hh := mul_le_mul_of_nonneg_left hlog hcoef
    exact hpoly.trans (hh.trans_eq (by dsimp [H]; ring))
  have hsize : P*(1+(net.points.card : ℝ)) ≤ N^2 := by
    calc
      _ ≤ P*(1+H*N) := mul_le_mul_of_nonneg_left (by linarith) hP
      _ ≤ P*((1+H)*N) := mul_le_mul_of_nonneg_left (by nlinarith) hP
      _ = (P*(1+H))*N := by ring
      _ ≤ N^2 := by nlinarith
  have hpow : 0 ≤ N^((k+1 : ℕ) : ℝ) := Real.rpow_nonneg hNpos.le _
  calc
    _ ≤ (P*N^((k+1 : ℕ) : ℝ))*(1+(net.points.card : ℝ)) :=
      mul_le_mul_of_nonneg_right hhigh (by positivity)
    _ = N^((k+1 : ℕ) : ℝ)*(P*(1+(net.points.card : ℝ))) := by ring
    _ ≤ N^((k+1 : ℕ) : ℝ)*N^2 := mul_le_mul_of_nonneg_left hsize hpow
    _ = _ := by rw [Real.rpow_add hNpos, Real.rpow_two]

/-- The literal source a0=64*(ambient+4) makes its exact exponential display
smaller than 1/8 already for N>=16. Fixed prefactors belong in the earlier count cutoff. -/
theorem source_tail (k : ℕ) {N : ℝ} (hN : 16 ≤ N) :
    N^(((k+1 : ℕ) : ℝ)+2)*
      Real.exp (-(64*(((k+1 : ℕ) : ℝ)+4)*Real.log (2*N))/8) < 1/8 := by
  have hN1 : 1 ≤ N := by linarith
  have ha : 0 ≤ 64*(((k+1 : ℕ) : ℝ)+4) := by positivity
  have hh := SamplingThreshold.logarithmic_tail_bound
    (w := ((k+1 : ℕ) : ℝ)+2) hN1 ha
  have hexp : ((k+1 : ℕ) : ℝ)+2-(64*(((k+1 : ℕ) : ℝ)+4))/8 ≤ -1 := by
    have hk := Nat.cast_nonneg (α := ℝ) (k+1)
    linarith
  have hp := Real.rpow_le_rpow_of_exponent_le hN1 hexp
  have hinv : N⁻¹ ≤ (16:ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<16) hN
  simpa only [neg_mul] using
    (hh.trans (hp.trans (by simpa only [Real.rpow_neg_one] using hinv))).trans_lt
      (show (16:ℝ)⁻¹ < 1/8 by norm_num)

/-- Actual cap and marked-cell failure probability, with the fixed source
coefficient and a cutoff uniform before every probability array, net and family. -/
theorem uniform_probability (k : ℕ) {B q P : ℝ}
    (hB : 0 < B) (hq : 0 ≤ q) (hP : 0 ≤ P) :
    ∃ N₀ : ℝ, 16 ≤ N₀ ∧ ∀ {N theta : ℝ}, N₀ ≤ N → ∀ net : Net k theta,
      1/theta ≤ B*(Real.log (2*N))^q →
      ∀ {M : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
        (F : TubeFamily (k+1) M) (p qmark : Fin M → C → ℝ)
        (hqm : ∀ t c, 0 ≤ qmark t c) (hqp : ∀ t c, qmark t c ≤ p t c)
        (hp : ∀ t c, p t c ≤ 1) (high : Finset C),
        (high.card : ℝ) ≤ P*N^((k+1 : ℕ) : ℝ) →
        (∀ c ∈ high, 64*(((k+1 : ℕ) : ℝ)+4)*Real.log (2*N) ≤ markedMean qmark c) →
        (∀ c ∈ high, ∀ a, 1000*capMean qmark (SphereNetCapTests.cap net F) c a ≤ markedMean qmark c) →
        (law p qmark hqm hqp hp).probability
          (angularFailure qmark high (SphereNetCapTests.cap net F)) < 1/8 := by
  obtain ⟨N₁, hN₁, hcount⟩ := test_count_threshold k hB hq hP
  refine ⟨max 16 N₁, le_max_left _ _, ?_⟩
  intro N theta hN net hinv M X _ _ F p qmark hqm hqp hp high hhigh hmean hcap
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hn := hcount ((le_max_right _ _).trans hN) net hinv high hhigh
  have hh := probability_le p qmark hqm hqp hp high (SphereNetCapTests.cap net F) hmean hcap
  simp only [Fintype.card_fin] at hh
  exact (hh.trans (mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le)).trans_lt (source_tail k hN16)

end
end KakeyaFormal.SphereNetFailure
