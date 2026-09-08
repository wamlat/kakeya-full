import GaussianGoodDirections
import GaussianCollisionExpectation
import CollisionIndependentSet

/-! Actual graph extraction among the original good projected directions.
Vertices keep their original indices; edges are literal angular collisions.
The original ordered collision count controls the graph through an injective
map of original pairs, not an assumed graph-count comparison. -/
namespace KakeyaFormal.GaussianCollisionSelection
open GaussianMatrix GaussianLinearOperator GaussianGoodDirections GaussianConditioning
open GaussianCollisionExpectation GaussianCollision ProjectiveAngleComparison CollisionIndependentSet
open scoped RealInnerProductSpace
noncomputable section
open Classical

def good {M : ℕ} (F : TubeFamily 7 M) (ω : Sample 5 7) : Finset (Fin M) :=
  goodIndices (fun i => (F.tube i).direction) (1/4) ω

theorem good_norm {M : ℕ} (F : TubeFamily 7 M) (ω : Sample 5 7)
    (i : Fin M) (hi : i∈good F ω) : (1:ℝ)/4 ≤ ‖projection (F.tube i).direction ω‖ :=
  (Finset.mem_filter.mp hi).2

theorem good_nonzero {M : ℕ} (F : TubeFamily 7 M) (ω : Sample 5 7)
    (i : Fin M) (hi : i∈good F ω) : projection (F.tube i).direction ω≠0 :=
  norm_ne_zero_iff.mp ((lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4)
    (good_norm F ω i hi)).ne')

def graph {M : ℕ} (F : TubeFamily 7 M) (δ : ℝ) (ω : Sample 5 7) :
    SimpleGraph ↥(good F ω) where
  Adj i j := i≠j ∧ angle (unitDirection (projection (F.tube i.val).direction ω))
    (unitDirection (projection (F.tube j.val).direction ω)) ≤ δ
  symm := ⟨by
    intro i j h
    refine ⟨h.1.symm,?_⟩
    simpa only [angle,real_inner_comm] using h.2⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

/-- Every graph edge encodes a distinct original ordered pair in the actual
truncated collision set, with both nonzero tests derived from good membership. -/
theorem orderedCount_le {M : ℕ} (F : TubeFamily 7 M) (δ : ℝ) (ω : Sample 5 7)
    (hK : ‖operator ω‖ ≤ 20) :
    orderedCount (graph F δ ω) ≤ (orderedCollisions F 20 δ ω).card := by
  let encode : (↥(good F ω) × ↥(good F ω)) → Fin M × Fin M :=
    fun p => (p.1.val,p.2.val)
  have hm : Set.MapsTo encode
      (Finset.univ.filter fun p : ↥(good F ω) × ↥(good F ω) => (graph F δ ω).Adj p.1 p.2)
      (orderedCollisions F 20 δ ω) := by
    intro p hp
    have he := (Finset.mem_filter.mp hp).2
    apply (mem_orderedCollisions F 20 δ ω p.1.val p.2.val).mpr
    refine ⟨fun h => he.1 (Subtype.ext h),hK,
      good_nonzero F ω p.1.val p.1.property,good_nonzero F ω p.2.val p.2.property,he.2⟩
  have hinj : Function.Injective encode := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  exact Finset.card_le_card_of_injOn encode hm hinj.injOn

/-- An actual subfamily of the original good indices with no projected
collisions. The exact source denominator uses the actual original ordered
collision count. Empty good sets are included, with the numerator zero. -/
theorem select {M : ℕ} (F : TubeFamily 7 M) (δ : ℝ) (ω : Sample 5 7)
    (hK : ‖operator ω‖ ≤ 20) :
    ∃ S : Finset (Fin M), S ⊆ good F ω ∧
      (∀ i∈S, ∀ j∈S, i≠j →
        δ < angle (unitDirection (projection (F.tube i).direction ω))
          (unitDirection (projection (F.tube j).direction ω))) ∧
      (∀ i∈S, ∀ j∈S, i≠j → (2/Real.pi)*δ ≤
        projectiveDistance (unitDirection (projection (F.tube i).direction ω))
          (unitDirection (projection (F.tube j).direction ω))) ∧
      ((good F ω).card:ℝ)^2 /
        (((good F ω).card:ℝ)+(orderedCollisions F 20 δ ω).card) ≤ (S.card:ℝ) := by
  obtain ⟨T,hT,hsize⟩ := exists_independent_ordered (graph F δ ω)
  let S : Finset (Fin M) := T.image Subtype.val
  have hcard : S.card=T.card := Finset.card_image_of_injective T Subtype.val_injective
  have hsub : S ⊆ good F ω := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact j.property
  have hangle : ∀ i∈S, ∀ j∈S, i≠j →
      δ < angle (unitDirection (projection (F.tube i).direction ω))
        (unitDirection (projection (F.tube j).direction ω)) := by
    intro i hi j hj hij
    obtain ⟨i',hi',rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨j',hj',rfl⟩ := Finset.mem_image.mp hj
    have hne : i'≠j' := fun h => hij (congrArg Subtype.val h)
    apply lt_of_not_ge
    intro ha
    exact (hT hi' hj' hne) ⟨hne,ha⟩
  refine ⟨S,hsub,hangle,?_,?_⟩
  · intro i hi j hj hij
    exact (mul_le_mul_of_nonneg_left (hangle i hi j hj hij).le
      (div_nonneg (by norm_num) Real.pi_pos.le)).trans
      (chord_angle_bounds _ _ (unitDirection_norm _) (unitDirection_norm _)).1
  · have hs : ((good F ω).card:ℝ)^2 /
        (((good F ω).card:ℝ)+orderedCount (graph F δ ω)) ≤ (T.card:ℝ) := by
      simpa only [Fintype.card_coe] using hsize
    rw [hcard]
    by_cases hz : (good F ω).card=0
    · simp only [hz,Nat.cast_zero,zero_pow (by decide : 2≠0),zero_div]
      positivity
    · have hn : (0:ℝ)<(good F ω).card := by exact_mod_cast Nat.pos_of_ne_zero hz
      have hc : (orderedCount (graph F δ ω):ℝ) ≤ (orderedCollisions F 20 δ ω).card := by
        exact_mod_cast orderedCount_le F δ ω hK
      have hden : (0:ℝ)<(good F ω).card+(orderedCount (graph F δ ω):ℝ) :=
        add_pos_of_pos_of_nonneg hn (Nat.cast_nonneg _)
      exact (div_le_div_of_nonneg_left (sq_nonneg _) hden
        (add_le_add (le_refl _) hc)).trans hs

end
end KakeyaFormal.GaussianCollisionSelection
