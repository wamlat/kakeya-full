import CapCover

/-!
# A finite net of the entire projective unit sphere

Finite packing bounds the cardinality of every separated set of actual unit
vectors. Maximizing among the resulting bounded natural cardinalities therefore
constructs a finite net covering *all* unit vectors, without a supplied finite
family or covering premise. The final cap-containment theorem is the geometric
net ingredient of the source sampling display (6.19), not its probability bound.
-/
namespace KakeyaFormal.ProjectiveSphereNet
open KakeyaFormal.ProjectiveGeometry KakeyaFormal.CapCover
noncomputable section

/-- The dimension-reduced packing bound applies to every finite separated subset
of the unit sphere: its projective distance to the zero vector is exactly one. -/
theorem sphere_packing {k : ℕ} {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (points : Finset (Space (k+1))) (hunit : ∀ v ∈ points, ‖v‖ = 1)
    (hsep : SeparatedOn id rho points) :
    (points.card : ℝ) ≤ packingConstant k * (1/rho)^k := by
  have h := projective_cap_packing points (0 : Space (k+1)) hrho hrho1 hunit
    (fun v hv => by simp [projectiveDistance, hunit v hv]) hsep
  simpa only [packingConstant] using h

/-- A finite net, including every geometric property used downstream. Its
centers are actual unit representatives, not points of an unspecified cover. -/
structure Net (k : ℕ) (rho : ℝ) where
  points : Finset (Space (k+1))
  unit : ∀ v ∈ points, ‖v‖ = 1
  separated : SeparatedOn id rho points
  covers : ∀ v : Space (k+1), ‖v‖ = 1 →
    ∃ w ∈ points, projectiveDistance v w < rho
  card_bound : (points.card : ℝ) ≤ packingConstant k * (1/rho)^k

/-- Construct a net of the entire projective sphere by maximum finite
cardinality. The maximum exists because the actual packing theorem bounds all
possible cardinalities by one fixed natural number. -/
theorem exists_net {k : ℕ} {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    Nonempty (Net k rho) := by
  classical
  let P : ℕ → Prop := fun n => ∃ points : Finset (Space (k+1)),
    (∀ v ∈ points, ‖v‖ = 1) ∧ SeparatedOn id rho points ∧ points.card = n
  let bound := Nat.ceil (packingConstant k * (1/rho)^k)
  have hbound {n : ℕ} (hn : P n) : n ≤ bound := by
    obtain ⟨points, hu, hs, hc⟩ := hn
    have h := (sphere_packing hrho hrho1 points hu hs).trans
      (Nat.le_ceil (packingConstant k * (1/rho)^k))
    rw [hc] at h
    exact_mod_cast h
  have hzero : P 0 := by
    refine ⟨∅, ?_, ?_, rfl⟩
    · simp
    · intro i hi
      exact False.elim (Finset.notMem_empty _ hi)
  obtain ⟨points, hu, hs, hc⟩ := Nat.findGreatest_spec (Nat.zero_le bound) hzero
  have hcover : ∀ v : Space (k+1), ‖v‖ = 1 →
      ∃ w ∈ points, projectiveDistance v w < rho := by
    intro v hv
    by_contra hnone
    have hnew : ∀ w ∈ points, rho ≤ projectiveDistance v w := by
      intro w hw
      exact le_of_not_gt (fun h => hnone ⟨w, hw, h⟩)
    have hvnot : v ∉ points := by
      intro hin
      have h := hnew v hin
      rw [projectiveDistance_self] at h
      linarith
    have hunit : ∀ w ∈ insert v points, ‖w‖ = 1 := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hv
      · exact hu w hw
    have hsep : SeparatedOn id rho (insert v points) := by
      intro a ha b hb hab
      rcases Finset.mem_insert.mp ha with hae | hanet
      · subst a
        rcases Finset.mem_insert.mp hb with hbe | hbnet
        · exact False.elim (hab hbe.symm)
        · exact hnew b hbnet
      · rcases Finset.mem_insert.mp hb with hbe | hbnet
        · subst b
          simpa only [id_eq, projective_symm] using hnew a hanet
        · exact hs a hanet b hbnet hab
    have hlarger : P (points.card + 1) :=
      ⟨insert v points, hunit, hsep, Finset.card_insert_of_notMem hvnot⟩
    have hmax := Nat.le_findGreatest (hbound hlarger) hlarger
    omega
  exact ⟨⟨points, hu, hs, hcover, sphere_packing hrho hrho1 points hu hs⟩⟩

/-- The same net covers every closed cap by an open enlarged cap. No condition
on the vector being tested inside the cap is needed for the triangle argument. -/
theorem Net.cap_containment {k : ℕ} {rho : ℝ} (N : Net k rho)
    (v : Space (k+1)) (hv : ‖v‖ = 1) (r : ℝ) :
    ∃ w ∈ N.points, ∀ u : Space (k+1), projectiveDistance v u ≤ r →
      projectiveDistance w u < rho + r := by
  obtain ⟨w, hw, hvw⟩ := N.covers v hv
  refine ⟨w, hw, ?_⟩
  intro u hu
  have htri := projective_triangle w v u
  rw [projective_symm w v] at htri
  linarith

/-- In particular, every closed rho-cap lies in one actual open 2*rho net cap. -/
theorem Net.double_cap_containment {k : ℕ} {rho : ℝ} (N : Net k rho)
    (v : Space (k+1)) (hv : ‖v‖ = 1) :
    ∃ w ∈ N.points, ∀ u : Space (k+1), projectiveDistance v u ≤ rho →
      projectiveDistance w u < 2*rho := by
  simpa only [two_mul] using N.cap_containment v hv rho


/-- An actual finite enumeration, convenient for product probability test sets. -/
def Net.center {k : ℕ} {rho : ℝ} (N : Net k rho)
    (i : Fin N.points.card) : Space (k+1) :=
  ((N.points.equivFin).symm i).val

theorem Net.center_mem {k : ℕ} {rho : ℝ} (N : Net k rho)
    (i : Fin N.points.card) : N.center i ∈ N.points :=
  ((N.points.equivFin).symm i).property

theorem Net.center_unit {k : ℕ} {rho : ℝ} (N : Net k rho)
    (i : Fin N.points.card) : ‖N.center i‖ = 1 :=
  N.unit _ (N.center_mem i)

theorem Net.center_injective {k : ℕ} {rho : ℝ} (N : Net k rho) :
    Function.Injective N.center := by
  intro i j hij
  apply (N.points.equivFin).symm.injective
  exact Subtype.ext hij

theorem Net.center_separated {k : ℕ} {rho : ℝ} (N : Net k rho)
    (i j : Fin N.points.card) (hij : i ≠ j) :
    rho ≤ projectiveDistance (N.center i) (N.center j) :=
  N.separated _ (N.center_mem i) _ (N.center_mem j)
    (fun heq => hij (N.center_injective heq))

theorem Net.center_covers {k : ℕ} {rho : ℝ} (N : Net k rho)
    (v : Space (k+1)) (hv : ‖v‖ = 1) :
    ∃ i : Fin N.points.card, projectiveDistance v (N.center i) < rho := by
  obtain ⟨w, hw, hdist⟩ := N.covers v hv
  refine ⟨N.points.equivFin ⟨w, hw⟩, ?_⟩
  simpa only [Net.center, Equiv.symm_apply_apply] using hdist

/-- Every original closed rho-cap fits in a single indexed open double-radius
net test, including caps centered at directions absent from the input tubes. -/
theorem Net.center_double_cap {k : ℕ} {rho : ℝ} (N : Net k rho)
    (v : Space (k+1)) (hv : ‖v‖ = 1) :
    ∃ i : Fin N.points.card, ∀ u : Space (k+1),
      projectiveDistance v u ≤ rho → projectiveDistance (N.center i) u < 2*rho := by
  obtain ⟨i, hi⟩ := N.center_covers v hv
  refine ⟨i, ?_⟩
  intro u hu
  have htri := projective_triangle (N.center i) v u
  rw [projective_symm (N.center i) v] at htri
  linarith

/-- Fully quantified finite-index version, with the same exact packing constant
and simultaneous coverage and cap containment for the entire unit sphere. -/
theorem exists_indexed_net {k : ℕ} {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    ∃ M : ℕ, ∃ center : Fin M → Space (k+1),
      (∀ i, ‖center i‖ = 1) ∧
      (∀ i j, i ≠ j → rho ≤ projectiveDistance (center i) (center j)) ∧
      (M : ℝ) ≤ packingConstant k * (1/rho)^k ∧
      (∀ v : Space (k+1), ‖v‖ = 1 → ∃ i, projectiveDistance v (center i) < rho) ∧
      (∀ v : Space (k+1), ‖v‖ = 1 → ∃ i, ∀ u : Space (k+1),
        projectiveDistance v u ≤ rho → projectiveDistance (center i) u < 2*rho) := by
  obtain ⟨N⟩ := exists_net hrho hrho1
  exact ⟨N.points.card, N.center, N.center_unit, N.center_separated,
    N.card_bound, N.center_covers, N.center_double_cap⟩

end
end KakeyaFormal.ProjectiveSphereNet
