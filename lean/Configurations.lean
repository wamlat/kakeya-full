import Mathlib

/-!
Actual finite Euclidean tube/grid data for the Kakeya manuscript.
These definitions expose the geometry and every variable in the estimate; they
do not assert that any new analytic bound holds. Fixed width, direction-separation
and bounded-region constants are explicit and chosen before scale and density.
Equivalence between the projective chord convention and angular conventions has
not yet been formalized.
-/

namespace KakeyaFormal

abbrev Space (k : ℕ) := EuclideanSpace ℝ (Fin k)
abbrev Cell (k : ℕ) := Fin k → ℤ

structure UnitTube (k : ℕ) where
  base : Space k
  direction : Space k
  unit_direction : ‖direction‖ = 1

def UnitTube.axisPoint {k : ℕ} (T : UnitTube k) (t : ℝ) : Space k :=
  T.base + t • T.direction

def UnitTube.carrier {k : ℕ} (T : UnitTube k) (δ : ℝ) : Set (Space k) :=
  {x | ∃ t ∈ Set.Icc (0 : ℝ) 1, dist x (T.axisPoint t) ≤ δ}

noncomputable def cellCenter {k : ℕ} (δ : ℝ) (z : Cell k) : Space k :=
  WithLp.toLp 2 (fun i => δ * (z i : ℝ))

/-- The chord metric between unoriented directions represented by unit vectors.
No metric-space instance is asserted here. -/
noncomputable def projectiveDistance {k : ℕ} (v w : Space k) : ℝ :=
  min ‖v-w‖ ‖v+w‖

structure TubeFamily (k M : ℕ) where
  tube : Fin M → UnitTube k
  shade : Fin M → Finset (Cell k)

noncomputable def TubeFamily.unionCells {k M : ℕ} (F : TubeFamily k M) : Finset (Cell k) := by
  classical
  exact Finset.univ.biUnion F.shade

def TubeFamily.Admissible {k M : ℕ} (F : TubeFamily k M) (width δ : ℝ) : Prop :=
  ∀ i z, z ∈ F.shade i →
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      dist (cellCenter δ z) ((F.tube i).axisPoint t) ≤ width * δ

def TubeFamily.Separated {k M : ℕ} (F : TubeFamily k M) (δ : ℝ) : Prop :=
  ∀ i j, i ≠ j → δ ≤ projectiveDistance (F.tube i).direction (F.tube j).direction

def TubeFamily.CapBound {k M : ℕ} (F : TubeFamily k M) (δ m A : ℝ) : Prop := by
  classical
  exact ∀ v : Space k, ‖v‖ = 1 → ∀ r : ℝ, δ ≤ r → r ≤ 1 →
    ((Finset.univ.filter fun i => projectiveDistance (F.tube i).direction v ≤ r).card : ℝ)
      ≤ A * (r / δ) ^ m

def TubeFamily.Comparable {k M : ℕ} (F : TubeFamily k M) (δ lam : ℝ) : Prop :=
  ∀ i, lam / δ ≤ (F.shade i).card ∧ ((F.shade i).card : ℝ) ≤ 2 * lam / δ

def TubeFamily.Bounded {k M : ℕ} (F : TubeFamily k M) (R : ℝ) : Prop :=
  ∀ i, ‖(F.tube i).base‖ ≤ R

structure Normalization where
  width : ℝ
  separation : ℝ
  radius : ℝ
  width_pos : 0 < width
  separation_pos : 0 < separation
  radius_pos : 0 < radius

/-- All variables over which the estimate is uniform, with actual geometric
constraints rather than an abstract predicate standing for a desired theorem. -/
structure ShadedConfiguration (k : ℕ) (geom : Normalization) (m : ℝ) where
  M : ℕ
  δ : ℝ
  lam : ℝ
  A : ℝ
  family : TubeFamily k M
  scale_pos : 0 < δ
  scale_le_one : δ ≤ 1
  density_pos : 0 < lam
  density_le_one : lam ≤ 1
  cap_ge_one : 1 ≤ A
  admissible : family.Admissible geom.width δ
  separated : family.Separated (geom.separation * δ)
  bounded : family.Bounded geom.radius
  cap_bound : family.CapBound δ m A
  comparable : family.Comparable δ lam

/-- Complete scale-loss quantification for a fixed ambient dimension. The constant
is chosen before δ, λ, A, M and the actual tube/grid configuration. -/
def DiscreteEstimate (k : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : Normalization, ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ F : ShadedConfiguration k geom m,
      c * F.A⁻¹ * F.δ ^ (m-d+ε) * F.lam ^ p * F.M ≤ (F.family.unionCells.card : ℝ)

/-- The real-cap estimate, in every adequate *integer* ambient dimension. -/
def RealCapEstimate (m d p : ℝ) : Prop :=
  ∀ k : ℕ, m ≤ (k : ℝ)-1 → DiscreteEstimate k m d p

def DiagonalDiscreteEstimate (n : ℕ) (d : ℝ) : Prop :=
  DiscreteEstimate n ((n : ℝ)-1) d d

theorem projectiveDistance_nonneg {k : ℕ} (v w : Space k) :
    0 ≤ projectiveDistance v w := le_min (norm_nonneg _) (norm_nonneg _)

theorem projectiveDistance_self {k : ℕ} (v : Space k) :
    projectiveDistance v v = 0 := by
  simp [projectiveDistance, norm_nonneg]

theorem projectiveDistance_neg_right {k : ℕ} (v w : Space k) :
    projectiveDistance v (-w) = projectiveDistance v w := by
  simp [projectiveDistance, sub_eq_add_neg, min_comm]

theorem UnitTube.axisPoint_distance {k : ℕ} (T : UnitTube k) (s t : ℝ) :
    dist (T.axisPoint s) (T.axisPoint t) = |s-t| := by
  rw [dist_eq_norm]
  have h : T.axisPoint s - T.axisPoint t = (s-t) • T.direction := by
    dsimp [axisPoint]
    module
  rw [h, norm_smul, Real.norm_eq_abs, T.unit_direction, mul_one]

theorem UnitTube.axisPoint_mem_carrier {k : ℕ} (T : UnitTube k)
    {δ t : ℝ} (hδ : 0 ≤ δ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    T.axisPoint t ∈ T.carrier δ := by
  exact ⟨t, ht, by simpa using hδ⟩

theorem TubeFamily.shade_subset_union {k M : ℕ} (F : TubeFamily k M) (i : Fin M) :
    F.shade i ⊆ F.unionCells := by
  classical
  intro z hz
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩

theorem TubeFamily.one_tube_card_bound {k M : ℕ} (F : TubeFamily k M)
    (i : Fin M) {δ lam : ℝ} (h : F.Comparable δ lam) :
    lam / δ ≤ (F.unionCells.card : ℝ) := by
  exact (h i).1.trans (by exact_mod_cast Finset.card_le_card (F.shade_subset_union i))

theorem ShadedConfiguration.density_ge_half_scale {k : ℕ} {geom : Normalization} {m : ℝ}
    (F : ShadedConfiguration k geom m) (hM : 0 < F.M) : F.δ / 2 ≤ F.lam := by
  let i : Fin F.M := ⟨0,hM⟩
  have hlower := (F.comparable i).1
  have hupper := (F.comparable i).2
  have hcardpos : 0 < (F.family.shade i).card := by
    exact_mod_cast lt_of_lt_of_le (div_pos F.density_pos F.scale_pos) hlower
  have hcard : (1 : ℝ) ≤ (F.family.shade i).card := by exact_mod_cast hcardpos
  have hmult := (le_div_iff₀ F.scale_pos).mp hupper
  have hδ := mul_le_mul_of_nonneg_right hcard F.scale_pos.le
  nlinarith

end KakeyaFormal
