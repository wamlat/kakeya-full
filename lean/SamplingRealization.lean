import SamplingSupport
import SamplingCapTests

/-! Literal sampled grid families from the common coupled outcome. Finite support
subtypes are mapped back to their original integer labels, without altering axes,
retaining artificial cells or assuming geometric admissibility of the outcome. -/
namespace KakeyaFormal.SamplingRealization
open Finset GridCells SamplingSupport KakeyaSamplingApplication
open scoped BigOperators
noncomputable section
open Classical

abbrev labelEmbedding {n : ℕ} (E : Finset (Cell n)) : ↥E ↪ Cell n :=
  ⟨Subtype.val, Subtype.val_injective⟩

def unlabel {n : ℕ} (E : Finset (Cell n)) (S : Finset ↥E) : Finset (Cell n) :=
  S.map (labelEmbedding E)

def full {n M : ℕ} (tube : Fin M → UnitTube n) (E : Finset (Cell n))
    (omega : Outcome (Fin M) ↥E) : TubeFamily n M :=
  ⟨tube, fun i => unlabel E (fullShading omega i)⟩

def marks {n M : ℕ} (E : Finset (Cell n)) (high : Finset ↥E)
    (omega : Outcome (Fin M) ↥E) (i : Fin M) : Finset (Cell n) :=
  unlabel E (markedShading high omega i)

@[simp] theorem mem_unlabel {n : ℕ} (E : Finset (Cell n)) (S : Finset ↥E) (z : ↥E) :
    z.val ∈ unlabel E S ↔ z ∈ S := by simp [unlabel]

@[simp] theorem unlabel_card {n : ℕ} (E : Finset (Cell n)) (S : Finset ↥E) :
    (unlabel E S).card = S.card := card_map _

theorem unlabel_subset {n : ℕ} (E : Finset (Cell n)) (S : Finset ↥E) :
    unlabel E S ⊆ E := by
  intro z hz
  obtain ⟨c,_,rfl⟩ := mem_map.mp hz
  exact c.property

/-- All outputs have literal original labels and remain in the same finite support. -/
theorem support_and_marks {n M : ℕ} (tube : Fin M → UnitTube n) (E : Finset (Cell n))
    (high : Finset ↥E) (omega : Outcome (Fin M) ↥E) :
    (full tube E omega).unionCells ⊆ E ∧
      ∀ i, marks E high omega i ⊆ (full tube E omega).shade i := by
  constructor
  · intro z hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    exact unlabel_subset E _ hi
  · intro i
    exact map_subset_map.mpr (markedShading_subset high omega i)

/-- Actual positive intersection probabilities force every selected original cell
center to lie in the fixed enlargement of the unchanged original tube. -/
theorem admissible {n M : ℕ} (tube : Fin M → UnitTube n)
    (Y : Fin M → Set (Space n)) (E : Finset (Cell n)) {δ width : ℝ}
    (hδ : 0 < δ) (hY : ∀ i, Y i ⊆ (tube i).carrier (width*δ))
    {B A : Type*} [Fintype B] [Fintype A]
    (p q : Fin M → ↥E → ℝ)
    (hpweight : ∀ i c, p i c ≤ weight (Y i) δ c.val)
    (high : Finset ↥E) (ball : B → ↥E → Bool)
    (cap : A → Fin M → Bool) (cutoff : Fin M → B → ℝ)
    (omega : Outcome (Fin M) ↥E)
    (hgood : SampleGood p q high ball cap cutoff omega) :
    (full tube E omega).Admissible (width+(n:ℝ)/2) δ := by
  intro i z hz
  obtain ⟨c,hc,rfl⟩ := mem_map.mp hz
  have hp := (hgood.full_support i c hc).trans_le (hpweight i c)
  have hpos : 0 < (MeasureTheory.volume : MeasureTheory.Measure (Space n)).real
      (Y i ∩ gridCell δ c.val) :=
    (div_pos_iff_of_pos_right (pow_pos hδ n)).mp hp
  obtain ⟨x,hx,hcell⟩ := positive_intersection_nonempty hpos
  exact touching_tube_center (tube i) ⟨x,hcell,hY i hx⟩

/-- The original-label counts retain the probability core's density and marked
mass guarantees, without cardinality-identification hypotheses. -/
theorem counts {n M : ℕ} (tube : Fin M → UnitTube n) (E : Finset (Cell n))
    {B A : Type*} [Fintype B] [Fintype A]
    (p q : Fin M → ↥E → ℝ) (high : Finset ↥E) (ball : B → ↥E → Bool)
    (cap : A → Fin M → Bool) (cutoff : Fin M → B → ℝ)
    (omega : Outcome (Fin M) ↥E) (hgood : SampleGood p q high ball cap cutoff omega) :
    (∀ i, fullMean p i/2 ≤ ((full tube E omega).shade i).card ∧
      (((full tube E omega).shade i).card:ℝ) ≤ 2*fullMean p i) ∧
    (∑ c, markedMean q c)/4 ≤ ∑ i, ((marks E high omega i).card:ℝ) ∧
    (∑ i, (((full tube E omega).shade i).card:ℝ)) ≤ 2*∑ i, fullMean p i := by
  simpa only [full,marks,unlabel_card] using
    And.intro hgood.density (And.intro hgood.marked_mass hgood.full_mass)

/-- Broadness holds for the actual original-cell marked shadings, at all labels. -/
theorem broadness {n M : ℕ} (F : TubeFamily n M) (E : Finset (Cell n)) (theta : ℝ)
    {B : Type*} [Fintype B]
    (p q : Fin M → ↥E → ℝ) (high : Finset ↥E) (ball : B → ↥E → Bool)
    (cutoff : Fin M → B → ℝ) (omega : Outcome (Fin M) ↥E)
    (hgood : SampleGood p q high ball (SamplingCapTests.cap F theta) cutoff omega) :
    ∀ (z : Cell n) (v : Space n),
      (((univ.filter (fun i => z ∈ marks E high omega i)).filter (fun i =>
        projectiveDistance v (F.tube i).direction < theta)).card : ℝ) ≤
          ((univ.filter (fun i => z ∈ marks E high omega i)).card : ℝ)/10 := by
  intro z v
  by_cases hz : z ∈ E
  · let c : ↥E := ⟨z,hz⟩
    have heq : univ.filter (fun i => z ∈ marks E high omega i) =
        SamplingCapTests.row high omega c := by
      ext i
      simp only [SamplingCapTests.row,mem_filter,mem_univ,true_and]
      exact mem_unlabel E _ c
    rw [heq]
    exact SamplingCapTests.sampled_broadness F theta p q high ball cutoff omega hgood c v
  · have heq : univ.filter (fun i => z ∈ marks E high omega i) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro i _ hi
      exact hz (unlabel_subset E _ hi)
    simp [heq]

theorem test_count {n M J : ℕ} (tube : Fin M → UnitTube n) (E : Finset (Cell n))
    (δ : ℝ) (omega : Outcome (Fin M) ↥E) (i : Fin M) (t : SamplingBallTests.Test E J) :
    ((((full tube E omega).shade i).filter (fun z =>
      dist (cellCenter δ z) (cellCenter δ t.1.val) ≤ SamplingBallTests.testRadius t)).card : ℝ) =
        fullBallCount omega (SamplingBallTests.mask δ) i t := by
  simp only [full,unlabel,filter_map,card_map]
  simp only [fullShading,filter_filter,card_eq_sum_ones,Nat.cast_sum,
    sum_filter,fullBallCount,SamplingBallTests.mask,KakeyaSampling.fullBit]
  apply sum_congr rfl
  intro c _
  dsimp [Function.comp_def,labelEmbedding]
  by_cases hm : (omega (i,c)).val = 0 <;>
    by_cases hb : dist (cellCenter δ c.val) (cellCenter δ t.1.val) ≤
      SamplingBallTests.testRadius t <;> simp [hm,hb]

/-- The literal sampled full shadings satisfy all-radius two ends. The finite
cutoff is measured against the actual full mean; sampled density supplies the
comparison to the actual full shading cardinality. -/
theorem two_ends {n M J : ℕ} (tube : Fin M → UnitTube n) (E : Finset (Cell n))
    {δ C B alpha : ℝ} (hδ : 0 < δ)
    (hbottom : KakeyaFormal.Localization.radius J 0 ≤ 2*δ)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (ha : 0 ≤ alpha)
    {A : Type*} [Fintype A]
    (p q : Fin M → ↥E → ℝ) (hp : ∀ i c, 0 ≤ p i c)
    (high : Finset ↥E) (cap : A → Fin M → Bool)
    (omega : Outcome (Fin M) ↥E)
    (hgood : SampleGood p q high (SamplingBallTests.mask (J:=J) δ) cap
      (fun i t => C*B*(SamplingBallTests.testRadius t)^alpha*fullMean p i) omega) :
    ∀ (i : Fin M) (x : Space n) (r : ℝ), δ ≤ r → r ≤ 1 →
      ((((full tube E omega).shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
        (2*(4:ℝ)^alpha*C)*B*r^alpha*(((full tube E omega).shade i).card:ℝ) := by
  intro i x r hr hr1
  have hr0 : 0 < r := hδ.trans_le hr
  have hmean : 0 ≤ fullMean p i := sum_nonneg (fun c _ => hp i c)
  have htests : ∀ t : SamplingBallTests.Test E J,
      ((((full tube E omega).shade i).filter (fun z =>
        dist (cellCenter δ z) (cellCenter δ t.1.val) ≤ SamplingBallTests.testRadius t)).card : ℝ) ≤
          (C*B*fullMean p i)*(SamplingBallTests.testRadius t)^alpha := by
    intro t
    rw [test_count]
    convert hgood.ball_upper i t using 1
    ring
  have hall := SamplingBallTests.all_ball_from_tests E ((full tube E omega).shade i)
    (unlabel_subset E _) hδ hbottom (mul_nonneg (mul_nonneg hC hB) hmean) ha htests x r hr hr1
  have hdensity : fullMean p i ≤ 2*(((full tube E omega).shade i).card:ℝ) := by
    have h := (hgood.density i).1
    change fullMean p i/2 ≤ ((fullShading omega i).card:ℝ) at h
    simp only [full,unlabel_card]
    linarith
  calc
    _ ≤ (4:ℝ)^alpha*(C*B*fullMean p i)*r^alpha := hall
    _ = ((4:ℝ)^alpha*C*B*r^alpha)*fullMean p i := by ring
    _ ≤ ((4:ℝ)^alpha*C*B*r^alpha)*(2*(((full tube E omega).shade i).card:ℝ)) :=
      mul_le_mul_of_nonneg_left hdensity (by positivity)
    _ = _ := by ring

end
end KakeyaFormal.SamplingRealization
