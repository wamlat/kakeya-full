import CapSelection
import ProjectiveGeometry
import CapCover

/-!
# Actual finite dyadic lattice hierarchy for cap-preserving selection

The hierarchy is constructed from finite fibers of explicit integer labels.
Arbitrary-arity nodes and their supports are produced here, not assumed.
Explicit signed sphere charts and two integer-box cap covers connect these
capacities to actual projective geometry and prove global cap-preserving thinning.
-/
namespace KakeyaFormal.CapThinningGeometry
open KakeyaVerification.CapSelection

noncomputable section
variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Label attached to one of the finitely many occupied blocks. -/
def occupiedLabel (points : Finset α) (label : α → β)
    (i : Fin (points.image label).card) : β := (points.image label).equivFin.symm i

def occupiedFiber (points : Finset α) (label : α → β)
    (i : Fin (points.image label).card) : Finset α :=
  points.filter (fun x => label x = occupiedLabel points label i)

omit [DecidableEq α] in
theorem occupiedLabel_injective (points : Finset α) (label : α → β) :
    Function.Injective (occupiedLabel points label) :=
  Subtype.val_injective.comp (points.image label).equivFin.symm.injective

omit [DecidableEq α] in
theorem occupiedFiber_subset (points : Finset α) (label : α → β)
    (i : Fin (points.image label).card) : occupiedFiber points label i ⊆ points :=
  Finset.filter_subset _ _

omit [DecidableEq α] in
theorem occupiedFibers_disjoint (points : Finset α) (label : α → β) :
    Pairwise fun i j => Disjoint (occupiedFiber points label i) (occupiedFiber points label j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hi := (Finset.mem_filter.mp hxi).2
  have hj := (Finset.mem_filter.mp hxj).2
  exact hij (occupiedLabel_injective points label (hi.symm.trans hj))

def occupiedIndex (points : Finset α) (label : α → β) (x : α) (hx : x ∈ points) :
    Fin (points.image label).card :=
  (points.image label).equivFin ⟨label x, Finset.mem_image.mpr ⟨x,hx,rfl⟩⟩

omit [DecidableEq α] in
theorem occupiedLabel_index (points : Finset α) (label : α → β) (x : α) (hx : x ∈ points) :
    occupiedLabel points label (occupiedIndex points label x hx) = label x := by
  simp [occupiedLabel, occupiedIndex]

omit [DecidableEq α] in
theorem mem_occupiedFiber_index (points : Finset α) (label : α → β) (x : α) (hx : x ∈ points) :
    x ∈ occupiedFiber points label (occupiedIndex points label x hx) := by
  exact Finset.mem_filter.mpr ⟨hx, (occupiedLabel_index points label x hx).symm⟩

theorem occupiedFibers_union (points : Finset α) (label : α → β) :
    Finset.univ.biUnion (occupiedFiber points label) = points := by
  apply Finset.Subset.antisymm
  · exact Finset.biUnion_subset.mpr (fun i _ => occupiedFiber_subset points label i)
  · intro x hx
    exact Finset.mem_biUnion.mpr ⟨occupiedIndex points label x hx, Finset.mem_univ _,
      mem_occupiedFiber_index points label x hx⟩

/-- Finer equal labels must give equal coarser labels. -/
def Coherent (label : ℕ → α → β) : Prop :=
  ∀ i j : ℕ, i ≤ j → ∀ x y : α, label i x = label i y → label j x = label j y

/-- An actual hierarchy built by taking all occupied finer fibers at each level. -/
def partitionTree (label : ℕ → α → β) (cap : ℕ → β → ℕ) :
    ℕ → β → Finset α → CapacityTree α
  | 0, block, points => .leaf points (cap 0 block)
  | depth+1, block, points =>
      .node (points.image (label depth)).card
        (fun i => partitionTree label cap depth (occupiedLabel points (label depth) i)
          (occupiedFiber points (label depth) i)) (cap (depth+1) block)

theorem partitionTree_support (label : ℕ → α → β) (cap : ℕ → β → ℕ)
    (depth : ℕ) (block : β) (points : Finset α) :
    (partitionTree label cap depth block points).support = points := by
  induction depth generalizing block points with
  | zero => rfl
  | succ depth ih =>
    simp only [partitionTree, CapacityTree.support, ih]
    exact occupiedFibers_union points (label depth)

theorem partitionTree_partitioned (label : ℕ → α → β) (cap : ℕ → β → ℕ)
    (depth : ℕ) (block : β) (points : Finset α) :
    (partitionTree label cap depth block points).Partitioned := by
  induction depth generalizing block points with
  | zero => trivial
  | succ depth ih =>
    constructor
    · intro i
      exact ih _ _
    · simp only [partitionTree_support]
      exact occupiedFibers_disjoint points (label depth)

/-- The root merely groups the occupied coarsest blocks; its capacity is redundant. -/
def hierarchyTree (label : ℕ → α → β) (cap : ℕ → β → ℕ)
    (depth : ℕ) (points : Finset α) : CapacityTree α :=
  .node (points.image (label depth)).card
    (fun i => partitionTree label cap depth (occupiedLabel points (label depth) i)
      (occupiedFiber points (label depth) i)) points.card

theorem hierarchyTree_support (label : ℕ → α → β) (cap : ℕ → β → ℕ)
    (depth : ℕ) (points : Finset α) : (hierarchyTree label cap depth points).support = points := by
  simp only [hierarchyTree, CapacityTree.support, partitionTree_support]
  exact occupiedFibers_union points (label depth)

theorem hierarchyTree_partitioned (label : ℕ → α → β) (cap : ℕ → β → ℕ)
    (depth : ℕ) (points : Finset α) : (hierarchyTree label cap depth points).Partitioned := by
  constructor
  · intro i
    exact partitionTree_partitioned _ _ _ _ _
  · simp only [partitionTree_support]
    exact occupiedFibers_disjoint points (label depth)


omit [DecidableEq α] in
theorem partitionTree_capacity (label : ℕ → α → β) (cap : ℕ → β → ℕ)
    (depth : ℕ) (block : β) (points : Finset α) :
    (partitionTree label cap depth block points).capacity = cap depth block := by
  cases depth <;> rfl

/-- Every actual finer block occurs with its assigned capacity in the realized tree. -/
theorem partitionTree_occurs (label : ℕ → α → β) (cap : ℕ → β → ℕ)
    (hcoh : Coherent label) (depth : ℕ) (block : β) (points : Finset α)
    (hroot : ∀ y ∈ points, label depth y = block)
    (j : ℕ) (hj : j ≤ depth) (x : α) (hx : x ∈ points) :
    (partitionTree label cap depth block points).Occurs
      (points.filter (fun y => label j y = label j x)) (cap j (label j x)) := by
  induction depth generalizing block points j with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    have hf : points.filter (fun y => label 0 y = label 0 x) = points := by
      apply Finset.filter_eq_self.mpr
      intro y hy
      exact (hroot y hy).trans (hroot x hx).symm
    rw [hf, hroot x hx]
    exact CapacityTree.Occurs.self (.leaf points (cap 0 block))
  | succ depth ih =>
    by_cases htop : j = depth+1
    · subst j
      have hf : points.filter (fun y => label (depth+1) y = label (depth+1) x) = points := by
        apply Finset.filter_eq_self.mpr
        intro y hy
        exact (hroot y hy).trans (hroot x hx).symm
      rw [hf, hroot x hx]
      have hself := CapacityTree.Occurs.self (partitionTree label cap (depth+1) block points)
      simpa only [partitionTree_support, partitionTree_capacity] using hself
    · have hjd : j ≤ depth := by omega
      let i := occupiedIndex points (label depth) x hx
      have hxf : x ∈ occupiedFiber points (label depth) i := mem_occupiedFiber_index _ _ _ hx
      have hchild := ih (occupiedLabel points (label depth) i)
        (occupiedFiber points (label depth) i)
        (fun y hy => (Finset.mem_filter.mp hy).2) j hjd hxf
      have hf : (occupiedFiber points (label depth) i).filter (fun y => label j y = label j x) =
          points.filter (fun y => label j y = label j x) := by
        ext y
        simp only [occupiedFiber, Finset.mem_filter]
        constructor
        · rintro ⟨⟨hy,_⟩,heq⟩
          exact ⟨hy,heq⟩
        · rintro ⟨hy,heq⟩
          refine ⟨⟨hy,?_⟩,heq⟩
          rw [occupiedLabel_index]
          exact hcoh j depth hjd y x heq
      rw [hf] at hchild
      exact CapacityTree.Occurs.child i hchild

/-- The root construction contains every occupied block at every finite dyadic level. -/
theorem hierarchyTree_occurs (label : ℕ → α → β) (cap : ℕ → β → ℕ)
    (hcoh : Coherent label) (depth : ℕ) (points : Finset α)
    (j : ℕ) (hj : j ≤ depth) (x : α) (hx : x ∈ points) :
    (hierarchyTree label cap depth points).Occurs
      (points.filter (fun y => label j y = label j x)) (cap j (label j x)) := by
  let i := occupiedIndex points (label depth) x hx
  have hxf := mem_occupiedFiber_index points (label depth) x hx
  have hchild := partitionTree_occurs label cap hcoh depth
    (occupiedLabel points (label depth) i) (occupiedFiber points (label depth) i)
    (fun y hy => (Finset.mem_filter.mp hy).2) j hj x hxf
  have hf : (occupiedFiber points (label depth) i).filter (fun y => label j y = label j x) =
      points.filter (fun y => label j y = label j x) := by
    ext y
    simp only [occupiedFiber, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hy,_⟩,heq⟩
      exact ⟨hy,heq⟩
    · rintro ⟨hy,heq⟩
      refine ⟨⟨hy,?_⟩,heq⟩
      rw [occupiedLabel_index]
      exact hcoh j depth hj y x heq
  rw [hf] at hchild
  exact CapacityTree.Occurs.child i hchild


/-- Capacities are computed from the actual original block populations. -/
def proportionalCapacity (label : ℕ → α → β) (original : Finset α) (rho : ℝ)
    (depth : ℕ) (block : β) : ℕ :=
  Nat.ceil (rho * ((original.filter (fun x => label depth x = block)).card : ℝ))

omit [DecidableEq α] in
theorem proportional_block_feasible (label : ℕ → α → β) (original : Finset α)
    {rho : ℝ} (hrho : 0 ≤ rho) (depth : ℕ) (block : β) (points : Finset α)
    (hsub : points ⊆ original) (hroot : ∀ x ∈ points, label depth x = block) :
    (∑ _x ∈ points, rho) ≤ (proportionalCapacity label original rho depth block : ℝ) := by
  have hs : points ⊆ original.filter (fun x => label depth x = block) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hsub hx,hroot x hx⟩
  have hcard : (points.card : ℝ) ≤ (original.filter (fun x => label depth x = block)).card := by
    exact_mod_cast Finset.card_le_card hs
  have hm := mul_le_mul_of_nonneg_left hcard hrho
  have hc := Nat.le_ceil (rho * ((original.filter (fun x => label depth x = block)).card : ℝ))
  simpa [proportionalCapacity, mul_comm] using hm.trans hc

theorem partitionTree_proportional_feasible (label : ℕ → α → β) (original : Finset α)
    {rho : ℝ} (hrho : 0 ≤ rho) (depth : ℕ) (block : β) (points : Finset α)
    (hsub : points ⊆ original) (hroot : ∀ x ∈ points, label depth x = block) :
    (partitionTree label (proportionalCapacity label original rho) depth block points).Feasible
      (fun _ => rho) := by
  induction depth generalizing block points with
  | zero => exact proportional_block_feasible label original hrho 0 block points hsub hroot
  | succ depth ih =>
    constructor
    · simpa only [partitionTree_support, occupiedFibers_union] using
        proportional_block_feasible label original hrho (depth+1) block points hsub hroot
    · intro i
      apply ih _ _ ((occupiedFiber_subset points (label depth) i).trans hsub)
      intro x hx
      exact (Finset.mem_filter.mp hx).2

theorem hierarchyTree_proportional_feasible (label : ℕ → α → β) (original : Finset α)
    {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (depth : ℕ) :
    (hierarchyTree label (proportionalCapacity label original rho) depth original).Feasible
      (fun _ => rho) := by
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hrho1 (Nat.cast_nonneg original.card : (0:ℝ) ≤ original.card)
    simpa [partitionTree_support, occupiedFibers_union, mul_comm] using hmul
  · intro i
    apply partitionTree_proportional_feasible label original hrho depth _ _
      (occupiedFiber_subset original (label depth) i)
    intro x hx
    exact (Finset.mem_filter.mp hx).2

theorem inter_original_filter {selected original : Finset α} (hsub : selected ⊆ original)
    (pred : α → Prop) [DecidablePred pred] :
    selected ∩ original.filter pred = selected.filter pred := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨hx,_,hp⟩
    exact ⟨hx,hp⟩
  · rintro ⟨hx,hp⟩
    exact ⟨hx,hsub hx,hp⟩

/-- Actual selection with simultaneous proportional ceilings for every occupied
block at every level. The capacities are computed, and feasibility is proved. -/
theorem hierarchy_proportional_selection (label : ℕ → α → β) (original : Finset α)
    (hcoh : Coherent label) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (depth : ℕ) :
    ∃ selected ⊆ original,
      rho*(original.card : ℝ) ≤ (selected.card : ℝ) ∧
      ∀ j : ℕ, j ≤ depth → ∀ block : β,
        (selected.filter (fun x => label j x = block)).card ≤
          Nat.ceil (rho*((original.filter (fun x => label j x = block)).card : ℝ)) := by
  let tree := hierarchyTree label (proportionalCapacity label original rho) depth original
  have hp : tree.Partitioned := hierarchyTree_partitioned _ _ _ _
  have hf : tree.Feasible (fun _ => rho) := hierarchyTree_proportional_feasible label original hrho hrho1 depth
  obtain ⟨selected,hsub,hadm,hmass⟩ := tree.fractionalSelection hp (fun _ => rho) (fun _ _ => ⟨hrho,hrho1⟩) hf
  have hs : selected ⊆ original := by simpa only [tree,hierarchyTree_support] using hsub
  refine ⟨selected,hs,?_,?_⟩
  · simpa only [tree,hierarchyTree_support, Finset.sum_const, nsmul_eq_mul, mul_comm] using hmass
  · intro j hj block
    by_cases hne : (original.filter (fun x => label j x = block)).Nonempty
    · obtain ⟨x,hx⟩ := hne
      have hxo := (Finset.mem_filter.mp hx).1
      have hxb := (Finset.mem_filter.mp hx).2
      have ho := hierarchyTree_occurs label (proportionalCapacity label original rho)
        hcoh depth original j hj x hxo
      have hb := CapacityTree.all_capacities ho hsub hadm
      rw [hxb,inter_original_filter hs] at hb
      exact hb
    · have hsel : selected.filter (fun x => label j x = block) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact hne ⟨x,Finset.mem_filter.mpr ⟨hs (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩⟩
      simp [hsel]

/-- Actual integer dyadic labels, obtained by coordinatewise division by 2^depth. -/
def dyadicLabel {k : ℕ} (fine : α → Cell k) (depth : ℕ) (x : α) : Cell k :=
  fun i => fine x i / (2:ℤ)^depth

omit [DecidableEq α] in
theorem dyadicLabel_coherent {k : ℕ} (fine : α → Cell k) : Coherent (dyadicLabel fine) := by
  intro i j hij x y hxy
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hij
  funext coord
  have h := congrArg (fun z : ℤ => z/(2:ℤ)^t) (congrFun hxy coord)
  have hn : ¬(2:ℤ)^i < 0 := not_lt.mpr (pow_nonneg (by norm_num) i)
  simpa only [dyadicLabel, Int.ediv_ediv, pow_add, hn, false_and, ite_false, sub_zero] using h

/-- For sphere charts the finest labels are actual integer floors of the remaining
coordinates; the constructed dyadic hierarchy is therefore a physical chart partition. -/
def chartDyadicLabel {k : ℕ} (h : ℝ) : ℕ → Space (k+1) → Cell k :=
  dyadicLabel (ProjectiveGeometry.chartBin h)

theorem chartDyadicLabel_coherent {k : ℕ} (h : ℝ) : Coherent (@chartDyadicLabel k h) :=
  dyadicLabel_coherent _

/-- Coarsening integer fine labels agrees exactly with physical dyadic scaling. -/
theorem chartDyadicLabel_floor {k : ℕ} (h : ℝ) (depth : ℕ)
    (v : Space (k+1)) (i : Fin k) :
    chartDyadicLabel h depth v i = ⌊WithLp.ofLp v i.succ / (h*(2:ℝ)^depth)⌋ := by
  have hf := Int.floor_div_natCast (WithLp.ofLp v i.succ / h) (2^depth)
  simpa [chartDyadicLabel, dyadicLabel, ProjectiveGeometry.chartBin, div_div] using hf.symm

/-- Dyadic proportional selection with capacities calculated from the input set. -/
theorem dyadic_proportional_selection {k : ℕ} (fine : α → Cell k) (original : Finset α)
    {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1) (depth : ℕ) :
    ∃ selected ⊆ original,
      rho*(original.card : ℝ) ≤ (selected.card : ℝ) ∧
      ∀ j : ℕ, j ≤ depth → ∀ block : Cell k,
        (selected.filter (fun x => dyadicLabel fine j x = block)).card ≤
          Nat.ceil (rho*((original.filter (fun x => dyadicLabel fine j x = block)).card : ℝ)) :=
  hierarchy_proportional_selection (dyadicLabel fine) original (dyadicLabel_coherent fine) hrho hrho1 depth

/-- If original fine cells contain at most B elements, actual dyadic rounding
retains M/B elements, selects at most one per fine cell, and preserves every
coarser block population up to the exact proportional ceiling. -/
theorem dyadic_inverse_selection {k : ℕ} (fine : α → Cell k) (original : Finset α)
    {B : ℝ} (hB : 1 ≤ B)
    (hfine : ∀ block : Cell k, ((original.filter (fun x => fine x = block)).card : ℝ) ≤ B)
    (depth : ℕ) :
    ∃ selected ⊆ original,
      (original.card : ℝ)/B ≤ (selected.card : ℝ) ∧
      (∀ block : Cell k, (selected.filter (fun x => fine x = block)).card ≤ 1) ∧
      ∀ j : ℕ, j ≤ depth → ∀ block : Cell k,
        (selected.filter (fun x => dyadicLabel fine j x = block)).card ≤
          Nat.ceil (((original.filter (fun x => dyadicLabel fine j x = block)).card : ℝ)/B) := by
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨selected,hs,hmass,hblocks⟩ := dyadic_proportional_selection fine original
    (le_of_lt (one_div_pos.mpr hBpos)) ((div_le_one hBpos).mpr hB) depth
  refine ⟨selected,hs,?_,?_,?_⟩
  · simpa [div_eq_mul_inv, mul_comm] using hmass
  · intro block
    have h := hblocks 0 (Nat.zero_le _) block
    have hzero : dyadicLabel fine 0 = fine := by
      funext x i
      simp [dyadicLabel]
    rw [hzero] at h
    have hreal : (1/B)*((original.filter (fun x => fine x = block)).card : ℝ) ≤ 1 := by
      rw [one_div, ← div_eq_inv_mul]
      exact (div_le_one hBpos).mpr (hfine block)
    exact h.trans (Nat.ceil_le.mpr (by simpa only [Nat.cast_one] using hreal))
  · intro j hj block
    simpa [div_eq_mul_inv,mul_comm] using hblocks j hj block


/-- Actual projected chart-cell populations are bounded from the original real-m
projective cap hypothesis. Large cells use the independently proved finite cap cover. -/
theorem chart_fiber_population_bound {k M : ℕ} (F : TubeFamily (k+1) M)
    (points : Finset (Fin M)) {δ m A c h : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m) (hA : 1 ≤ A) (hc : 0 < c) (hh : 0 < h)
    (hchart : ∀ i ∈ points, c ≤ WithLp.ofLp (F.tube i).direction 0)
    (hcap : F.CapBound δ m A) (hscale : δ ≤ ProjectiveGeometry.chartConstant k c*h)
    (block : Cell k) :
    ((points.filter (fun i => ProjectiveGeometry.chartBin h (F.tube i).direction = block)).card : ℝ) ≤
      ProjectiveGeometry.packingConstant k*A*(ProjectiveGeometry.chartConstant k c*h/δ)^m := by
  classical
  let R := ProjectiveGeometry.chartConstant k c*h
  have hC := ProjectiveGeometry.chartConstant_pos k hc
  have hR : 0 < R := mul_pos hC hh
  let fiber := points.filter (fun i => ProjectiveGeometry.chartBin h (F.tube i).direction = block)
  by_cases hsmall : R ≤ 1
  · by_cases hne : fiber.Nonempty
    · obtain ⟨i₀,hi₀⟩ := hne
      have hi₀p := (Finset.mem_filter.mp hi₀).1
      have hsub : fiber ⊆ Finset.univ.filter
          (fun i => projectiveDistance (F.tube i).direction (F.tube i₀).direction ≤ R) := by
        intro i hi
        have hip := (Finset.mem_filter.mp hi).1
        have heq : ProjectiveGeometry.chartBin h (F.tube i).direction =
            ProjectiveGeometry.chartBin h (F.tube i₀).direction :=
          (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hi₀).2.symm
        have hdist := ProjectiveGeometry.sphere_chart_distance
          (F.tube i).unit_direction (F.tube i₀).unit_direction hc hh.le
          (hchart i hip) (hchart i₀ hi₀p)
          (fun coord => ProjectiveGeometry.same_floor_distance hh (congrFun heq coord))
        have hpd := (ProjectiveGeometry.projective_le_chord (F.tube i).direction
          (F.tube i₀).direction).trans hdist
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpd⟩
      have hcard : (fiber.card : ℝ) ≤
          ((Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction (F.tube i₀).direction ≤ R)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hbound := hcard.trans (hcap (F.tube i₀).direction (F.tube i₀).unit_direction R hscale hsmall)
      have hpos : 0 ≤ A*(R/δ)^m := by positivity
      have hmulp := mul_le_mul_of_nonneg_right (ProjectiveGeometry.packingConstant_ge_one k) hpos
      simpa only [one_mul, mul_assoc] using hbound.trans (by simpa only [one_mul] using hmulp)
    · have hempty : fiber = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      change (fiber.card : ℝ) ≤ _
      rw [hempty, Finset.card_empty, Nat.cast_zero]
      have hp := ProjectiveGeometry.packingConstant_ge_one k
      positivity
  · have htotal := CapCover.cap_bound_total_count F hδ hδ1 (by linarith) hcap
    have hsub : fiber ⊆ Finset.univ := Finset.subset_univ _
    have hM : (fiber.card : ℝ) ≤ M := by
      exact_mod_cast (by simpa using Finset.card_le_card hsub : fiber.card ≤ M)
    have hratio : 1/δ ≤ R/δ := div_le_div_of_nonneg_right (le_of_not_ge hsmall) hδ.le
    have hpow := Real.rpow_le_rpow (one_div_nonneg.mpr hδ.le) hratio hm
    have hcoef : 0 ≤ ProjectiveGeometry.packingConstant k*A := by
      have hp := ProjectiveGeometry.packingConstant_ge_one k
      positivity
    exact hM.trans (htotal.trans (mul_le_mul_of_nonneg_left hpow hcoef))

/-- Every physical dyadic chart block inherits the correct 2^(j*m) growth,
with constants derived from the actual real-m cap hypothesis. -/
theorem chart_dyadic_population_bound {k M : ℕ} (F : TubeFamily (k+1) M)
    (points : Finset (Fin M)) {δ m A c h : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m) (hA : 1 ≤ A) (hc : 0 < c) (hh : 0 < h)
    (hchart : ∀ i ∈ points, c ≤ WithLp.ofLp (F.tube i).direction 0)
    (hcap : F.CapBound δ m A) (hscale : δ ≤ ProjectiveGeometry.chartConstant k c*h)
    (j : ℕ) (block : Cell k) :
    ((points.filter (fun i => chartDyadicLabel h j (F.tube i).direction = block)).card : ℝ) ≤
      (ProjectiveGeometry.packingConstant k*A*(ProjectiveGeometry.chartConstant k c*h/δ)^m)*
        (((2:ℝ)^j)^m) := by
  have hpow : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hpos : 0 < (2:ℝ)^j := pow_pos (by norm_num) _
  have hC := ProjectiveGeometry.chartConstant_pos k hc
  have hstep : δ ≤ ProjectiveGeometry.chartConstant k c*(h*(2:ℝ)^j) := by
    nlinarith [mul_le_mul_of_nonneg_left hpow (mul_pos hC hh).le]
  have hb := chart_fiber_population_bound F points hδ hδ1 hm hA hc (mul_pos hh hpos)
    hchart hcap hstep block
  have heq (i : Fin M) : chartDyadicLabel h j (F.tube i).direction =
      ProjectiveGeometry.chartBin (h*(2:ℝ)^j) (F.tube i).direction := by
    funext coord
    exact chartDyadicLabel_floor h j _ coord
  simp_rw [heq]
  have hid : ProjectiveGeometry.chartConstant k c*(h*(2:ℝ)^j)/δ =
      (ProjectiveGeometry.chartConstant k c*h/δ)*(2:ℝ)^j := by ring
  rw [hid, Real.mul_rpow (by positivity) hpos.le] at hb
  simpa only [mul_assoc] using hb

/-- A concrete finite-depth cap-preserving thinning on an actual spherical chart.
The subset and hierarchy are constructed; block capacities are consequences of
F.CapBound. The output has one original tube per fine chart cell and proportional
retention with a single inverse cap coefficient. -/
theorem chart_real_cap_dyadic_selection {k M : ℕ} (F : TubeFamily (k+1) M)
    (points : Finset (Fin M)) {δ m A c h : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m) (hA : 1 ≤ A) (hc : 0 < c) (hh : 0 < h)
    (hchart : ∀ i ∈ points, c ≤ WithLp.ofLp (F.tube i).direction 0)
    (hcap : F.CapBound δ m A) (hscale : δ ≤ ProjectiveGeometry.chartConstant k c*h)
    (depth : ℕ) :
    ∃ selected ⊆ points,
      (points.card : ℝ)/(ProjectiveGeometry.packingConstant k*A*
        (ProjectiveGeometry.chartConstant k c*h/δ)^m) ≤ (selected.card : ℝ) ∧
      (∀ block : Cell k, (selected.filter
        (fun i => ProjectiveGeometry.chartBin h (F.tube i).direction = block)).card ≤ 1) ∧
      ∀ j : ℕ, j ≤ depth → ∀ block : Cell k,
        (selected.filter (fun i => chartDyadicLabel h j (F.tube i).direction = block)).card ≤
          Nat.ceil (((2:ℝ)^j)^m) := by
  let B := ProjectiveGeometry.packingConstant k*A*(ProjectiveGeometry.chartConstant k c*h/δ)^m
  have hratio : 1 ≤ ProjectiveGeometry.chartConstant k c*h/δ :=
    (le_div_iff₀ hδ).mpr (by simpa using hscale)
  have hpower : 1 ≤ (ProjectiveGeometry.chartConstant k c*h/δ)^m := Real.one_le_rpow hratio hm
  have hpack := ProjectiveGeometry.packingConstant_ge_one k
  have hpa : 1 ≤ ProjectiveGeometry.packingConstant k*A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpack) (sub_nonneg.mpr hA)]
  have hB : 1 ≤ B := by
    dsimp [B]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpa) (sub_nonneg.mpr hpower)]
  have hfine : ∀ block : Cell k,
      ((points.filter (fun i => ProjectiveGeometry.chartBin h (F.tube i).direction = block)).card : ℝ) ≤ B :=
    fun block => chart_fiber_population_bound F points hδ hδ1 hm hA hc hh hchart hcap hscale block
  obtain ⟨selected,hs,hmass,hfineSel,hblocks⟩ :=
    dyadic_inverse_selection (fun i => ProjectiveGeometry.chartBin h (F.tube i).direction) points hB hfine depth
  refine ⟨selected,hs,hmass,hfineSel,?_⟩
  intro j hj block
  have hpop := chart_dyadic_population_bound F points hδ hδ1 hm hA hc hh hchart hcap hscale j block
  have hdiv : ((points.filter (fun i => chartDyadicLabel h j (F.tube i).direction = block)).card : ℝ)/B ≤
      ((2:ℝ)^j)^m := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hB)).mpr (by simpa [B,mul_comm] using hpop)
  exact (hblocks j hj block).trans (Nat.ceil_mono hdiv)


/-- A gap of three quantized coordinates gives a physical coordinate gap of at least2h. -/
theorem floor_gap_physical {a b h : ℝ} (hh : 0 < h)
    (hgap : (3:ℤ) ≤ |⌊a/h⌋-⌊b/h⌋|) : 2*h ≤ |a-b| := by
  have hgapR : (3:ℝ) ≤ |(⌊a/h⌋:ℝ)-(⌊b/h⌋:ℝ)| := by exact_mod_cast hgap
  have hal := (le_div_iff₀ hh).mp (Int.floor_le (a/h))
  have hau := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (a/h))
  have hbl := (le_div_iff₀ hh).mp (Int.floor_le (b/h))
  have hbu := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (b/h))
  rcases le_abs.mp hgapR with hpos | hneg
  · have hmul := mul_le_mul_of_nonneg_right hpos hh.le
    nlinarith [le_abs_self (a-b)]
  · have hmul := mul_le_mul_of_nonneg_right hneg hh.le
    nlinarith [neg_le_abs (a-b)]

/-- The modular lattice separation is genuine projective separation on a positive chart. -/
theorem chart_lattice_projective_separation {k : ℕ} {v w : Space (k+1)} {c h : ℝ}
    (hh : 0 < h) (hhc : h ≤ c)
    (hvc : c ≤ WithLp.ofLp v 0) (hwc : c ≤ WithLp.ofLp w 0)
    (hgap : ∃ i : Fin k, (3:ℤ) ≤ |ProjectiveGeometry.chartBin h v i - ProjectiveGeometry.chartBin h w i|) :
    2*h ≤ projectiveDistance v w := by
  obtain ⟨i,hi⟩ := hgap
  have hdiff := floor_gap_physical hh hi
  have hcoord := GridGeometry.coordinate_dist_le v w i.succ
  have hminus : 2*h ≤ ‖v-w‖ := hdiff.trans hcoord
  have hsum := PiLp.norm_apply_le (v+w) (0 : Fin (k+1))
  simp only [PiLp.add_apply,Real.norm_eq_abs] at hsum
  have hplus : 2*h ≤ ‖v+w‖ := by nlinarith [le_abs_self (WithLp.ofLp v 0 + WithLp.ofLp w 0)]
  exact le_min hminus hplus

/-- Color an actual one-per-fine-cell selection, keeping a dimensional fraction
and all existing dyadic bounds, while obtaining coarse projective separation. -/
theorem chart_dyadic_coloring {k M : ℕ} (F : TubeFamily (k+1) M)
    (selected : Finset (Fin M)) {c h : ℝ} (hh : 0 < h) (hhc : h ≤ c)
    (hchart : ∀ i ∈ selected, c ≤ WithLp.ofLp (F.tube i).direction 0)
    (hfine : ∀ block : Cell k, (selected.filter
      (fun i => ProjectiveGeometry.chartBin h (F.tube i).direction = block)).card ≤ 1)
    (depth : ℕ) (bound : ℕ → ℕ)
    (hblocks : ∀ j : ℕ, j ≤ depth → ∀ block : Cell k,
      (selected.filter (fun i => chartDyadicLabel h j (F.tube i).direction = block)).card ≤ bound j) :
    ∃ kept ⊆ selected,
      (selected.card : ℝ)/(3:ℝ)^k ≤ (kept.card : ℝ) ∧
      (∀ i ∈ kept, ∀ j ∈ kept, i ≠ j →
        2*h ≤ projectiveDistance (F.tube i).direction (F.tube j).direction) ∧
      ∀ j : ℕ, j ≤ depth → ∀ block : Cell k,
        (kept.filter (fun i => chartDyadicLabel h j (F.tube i).direction = block)).card ≤ bound j := by
  classical
  let fine := fun i => ProjectiveGeometry.chartBin h (F.tube i).direction
  have hinj : Set.InjOn fine (selected : Set (Fin M)) := by
    intro i hi j hj heq
    have hcard := hfine (fine i)
    exact Finset.card_le_one.mp hcard i (Finset.mem_filter.mpr ⟨hi,rfl⟩) j
      (Finset.mem_filter.mpr ⟨hj,heq.symm⟩)
  let tree : CapacityTree (Fin M) := .leaf selected selected.card
  obtain ⟨color,kept,hsub,hmass,_,hcolor,_⟩ := tree.monochromaticSelection
    (by rfl : selected ⊆ tree.support) (by exact le_rfl : tree.Admissible selected)
    (fun i coord => (fine i coord : ZMod 3))
  refine ⟨kept,hsub,?_,?_,?_⟩
  · simpa [Fintype.card_fun,ZMod.card] using hmass
  · intro i hi j hj hne
    apply chart_lattice_projective_separation hh hhc (hchart i (hsub hi)) (hchart j (hsub hj))
    exact CapacityTree.lattice_color_separates fine (hinj.mono hsub) hcolor hi hj hne
  · intro j hj block
    exact (Finset.card_le_card (Finset.filter_subset_filter _ hsub)).trans (hblocks j hj block)

/-- Actual coarse separated thinning with a single inverse real-cap coefficient,
plus all finite-depth dyadic m-growth bounds. -/
theorem chart_real_cap_thinning {k M : ℕ} (F : TubeFamily (k+1) M)
    (points : Finset (Fin M)) {δ m A c h : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m) (hA : 1 ≤ A) (hc : 0 < c) (hh : 0 < h) (hhc : h ≤ c)
    (hchart : ∀ i ∈ points, c ≤ WithLp.ofLp (F.tube i).direction 0)
    (hcap : F.CapBound δ m A) (hscale : δ ≤ ProjectiveGeometry.chartConstant k c*h)
    (depth : ℕ) :
    ∃ kept ⊆ points,
      (points.card : ℝ)/((ProjectiveGeometry.packingConstant k*A*
        (ProjectiveGeometry.chartConstant k c*h/δ)^m)*(3:ℝ)^k) ≤ (kept.card : ℝ) ∧
      (∀ i ∈ kept, ∀ j ∈ kept, i ≠ j →
        2*h ≤ projectiveDistance (F.tube i).direction (F.tube j).direction) ∧
      ∀ j : ℕ, j ≤ depth → ∀ block : Cell k,
        (kept.filter (fun i => chartDyadicLabel h j (F.tube i).direction = block)).card ≤
          Nat.ceil (((2:ℝ)^j)^m) := by
  obtain ⟨selected,hs,hmass,hfine,hblocks⟩ := chart_real_cap_dyadic_selection F points
    hδ hδ1 hm hA hc hh hchart hcap hscale depth
  obtain ⟨kept,hk,hkmass,hsep,hcaps⟩ := chart_dyadic_coloring F selected hh hhc
    (fun i hi => hchart i (hs hi)) hfine depth (fun j => Nat.ceil (((2:ℝ)^j)^m)) hblocks
  refine ⟨kept,hk.trans hs,?_,hsep,hcaps⟩
  rw [← div_div]
  exact (div_le_div_of_nonneg_right hmass (by positivity)).trans hkmass


/-- A bounded scale has a dyadic majorant at most twice as large, without an
unbounded hierarchy or an asymptotic scale assumption. -/
theorem dyadic_scale_between {h u : ℝ} {depth : ℕ} (hh : 0 < h)
    (hhu : h ≤ u) (htop : u ≤ h*(2:ℝ)^depth) :
    ∃ j ≤ depth, u ≤ h*(2:ℝ)^j ∧ h*(2:ℝ)^j ≤ 2*u := by
  let H : ∃ j : ℕ, u ≤ h*(2:ℝ)^j := ⟨depth, htop⟩
  refine ⟨Nat.find H, Nat.find_min' H htop, Nat.find_spec H, ?_⟩
  cases heq : Nat.find H with
  | zero => simp only [pow_zero, mul_one]; linarith
  | succ n =>
    have hprev : ¬u ≤ h*(2:ℝ)^n := Nat.find_min H (by omega)
    rw [pow_succ]
    nlinarith [lt_of_not_ge hprev]

/-- A finite dyadic depth reaches the top direction scale for every positive mesh. -/
theorem exists_dyadic_top {h : ℝ} (hh : 0 < h) :
    ∃ depth : ℕ, 1 ≤ h*(2:ℝ)^depth := by
  obtain ⟨depth,hd⟩ := pow_unbounded_of_one_lt (1/h) (by norm_num : (1:ℝ)<2)
  exact ⟨depth, (div_le_iff₀ hh).mp hd.le |>.trans_eq (mul_comm _ _)⟩

/-- A Euclidean cap whose radius does not exceed the dyadic side length meets
at most five cells in each projected coordinate. -/
theorem euclidean_cap_label_box {k : ℕ} {h u : ℝ} {j : ℕ}
    (hh : 0 < h) (hu : u ≤ h*(2:ℝ)^j) (v center : Space (k+1))
    (hcap : dist v center ≤ u) :
    chartDyadicLabel h j v ∈ GridGeometry.gridBox
      (ProjectiveGeometry.chartBin (h*(2:ℝ)^j) center) 2 := by
  have hS : 0 < h*(2:ℝ)^j := by positivity
  have hc : Nat.ceil (u/(h*(2:ℝ)^j)) ≤ 1 :=
    Nat.ceil_le.mpr (by simpa only [Nat.cast_one] using (div_le_one hS).mpr hu)
  rw [GridGeometry.mem_gridBox]
  intro i
  have hi := ProjectiveGeometry.floor_distance_bounds hS
    ((GridGeometry.coordinate_dist_le v center i.succ).trans hcap)
  rw [chartDyadicLabel_floor]
  change ⌊WithLp.ofLp center i.succ/(h*(2:ℝ)^j)⌋ - (2:ℤ) ≤ _ ∧
    _ ≤ ⌊WithLp.ofLp center i.succ/(h*(2:ℝ)^j)⌋ + (2:ℤ)
  constructor <;> omega

/-- An actual projective cap is covered by two explicitly constructed projected
lattice boxes, one for each sign of its center. -/
theorem projective_cap_label_cover {k : ℕ} {h u : ℝ} {j : ℕ}
    (hh : 0 < h) (hu : u ≤ h*(2:ℝ)^j) (v center : Space (k+1))
    (hcap : projectiveDistance v center ≤ u) :
    chartDyadicLabel h j v ∈
      GridGeometry.gridBox (ProjectiveGeometry.chartBin (h*(2:ℝ)^j) center) 2 ∪
      GridGeometry.gridBox (ProjectiveGeometry.chartBin (h*(2:ℝ)^j) (-center)) 2 := by
  rcases min_le_iff.mp hcap with hminus | hplus
  · exact Finset.mem_union_left _ (euclidean_cap_label_box hh hu v center hminus)
  · exact Finset.mem_union_right _ (euclidean_cap_label_box hh hu v (-center)
      (by simpa only [dist_eq_norm, sub_neg_eq_add] using hplus))

/-- Explicit finite box covering turns dyadic capacities into arbitrary cap counts. -/
theorem dyadic_cap_count {k M : ℕ} (F : TubeFamily (k+1) M)
    (kept : Finset (Fin M)) {h u : ℝ} {j B : ℕ}
    (hh : 0 < h) (hu : u ≤ h*(2:ℝ)^j)
    (hblocks : ∀ block : Cell k,
      (kept.filter (fun i => chartDyadicLabel h j (F.tube i).direction = block)).card ≤ B)
    (center : Space (k+1)) :
    (kept.filter (fun i => projectiveDistance (F.tube i).direction center ≤ u)).card ≤
      2*5^k*B := by
  classical
  let cover := GridGeometry.gridBox (ProjectiveGeometry.chartBin (h*(2:ℝ)^j) center) 2 ∪
      GridGeometry.gridBox (ProjectiveGeometry.chartBin (h*(2:ℝ)^j) (-center)) 2
  let blocks := fun block => kept.filter (fun i => chartDyadicLabel h j (F.tube i).direction = block)
  have hcover : (kept.filter (fun i => projectiveDistance (F.tube i).direction center ≤ u)) ⊆
      cover.biUnion blocks := by
    intro i hi
    have hip := Finset.mem_filter.mp hi
    exact Finset.mem_biUnion.mpr ⟨chartDyadicLabel h j (F.tube i).direction,
      projective_cap_label_cover hh hu _ center hip.2, Finset.mem_filter.mpr ⟨hip.1,rfl⟩⟩
  have hcard : cover.card ≤ 2*5^k := by
    exact Finset.card_union_le _ _ |>.trans_eq (by simp [GridGeometry.gridBox_card]; omega)
  calc
    _ ≤ (cover.biUnion blocks).card := Finset.card_le_card hcover
    _ ≤ ∑ b ∈ cover, (blocks b).card := Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ cover, B := Finset.sum_le_sum (fun b _ => hblocks b)
    _ = cover.card*B := by simp
    _ ≤ 2*5^k*B := Nat.mul_le_mul_right B hcard

/-- All actual projective caps at the new scale inherit m-growth, uniformly in
original population, density, and hierarchy depth. -/
theorem dyadic_bounds_give_cap_bound {k M : ℕ} (F : TubeFamily (k+1) M)
    (kept : Finset (Fin M)) {h m : ℝ} (hh : 0 < h) (hm : 0 ≤ m)
    (depth : ℕ) (htop : 1 ≤ h*(2:ℝ)^depth)
    (hblocks : ∀ j : ℕ, j ≤ depth → ∀ block : Cell k,
      (kept.filter (fun i => chartDyadicLabel h j (F.tube i).direction = block)).card ≤
        Nat.ceil (((2:ℝ)^j)^m)) :
    ∀ center : Space (k+1), ∀ u : ℝ, h ≤ u → u ≤ 1 →
      ((kept.filter (fun i => projectiveDistance (F.tube i).direction center ≤ u)).card : ℝ) ≤
        (4*(5:ℝ)^k*(2:ℝ)^m)*(u/h)^m := by
  intro center u hhu hu1
  obtain ⟨j,hjd,hul,huh⟩ := dyadic_scale_between hh hhu (hu1.trans htop)
  have hcount := dyadic_cap_count F kept hh hul (hblocks j hjd) center
  have hcountR : ((kept.filter (fun i => projectiveDistance (F.tube i).direction center ≤ u)).card : ℝ) ≤
      2*(5:ℝ)^k*(Nat.ceil (((2:ℝ)^j)^m) : ℝ) := by exact_mod_cast hcount
  have hp : 1 ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
  have hpm : 1 ≤ ((2:ℝ)^j)^m := Real.one_le_rpow hp hm
  have hceil : (Nat.ceil (((2:ℝ)^j)^m) : ℝ) ≤ 2*((2:ℝ)^j)^m := by
    have hc := Nat.ceil_lt_add_one (zero_le_one.trans hpm)
    linarith
  have hpow : ((2:ℝ)^j)^m ≤ (2*(u/h))^m := by
    apply Real.rpow_le_rpow (by positivity) _ hm
    have hd : (2:ℝ)^j ≤ 2*u/h := (le_div_iff₀ hh).mpr (by nlinarith)
    simpa only [mul_div_assoc] using hd
  have hnon : 0 ≤ u/h := div_nonneg (hh.le.trans hhu) hh.le
  calc
    _ ≤ 2*(5:ℝ)^k*(Nat.ceil (((2:ℝ)^j)^m) : ℝ) := hcountR
    _ ≤ 2*(5:ℝ)^k*(2*((2:ℝ)^j)^m) := mul_le_mul_of_nonneg_left hceil (by positivity)
    _ ≤ 2*(5:ℝ)^k*(2*(2*(u/h))^m) := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num) hnon]; ring

/-- Concrete chart thinning: a finite subfamily retains the expected single
inverse cap coefficient, is separated at the new scale, and obeys every actual
projective m-cap estimate down to that scale. -/
theorem chart_full_cap_thinning {k M : ℕ} (F : TubeFamily (k+1) M)
    (points : Finset (Fin M)) {δ m A c h : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m) (hA : 1 ≤ A) (hc : 0 < c)
    (hh : 0 < h) (hhc : h ≤ c)
    (hchart : ∀ i ∈ points, c ≤ WithLp.ofLp (F.tube i).direction 0)
    (hcap : F.CapBound δ m A) (hscale : δ ≤ ProjectiveGeometry.chartConstant k c*h) :
    ∃ kept ⊆ points,
      (points.card : ℝ)/((ProjectiveGeometry.packingConstant k*A*
        (ProjectiveGeometry.chartConstant k c*h/δ)^m)*(3:ℝ)^k) ≤ (kept.card : ℝ) ∧
      (∀ i ∈ kept, ∀ j ∈ kept, i ≠ j →
        2*h ≤ projectiveDistance (F.tube i).direction (F.tube j).direction) ∧
      ∀ center : Space (k+1), ∀ u : ℝ, h ≤ u → u ≤ 1 →
        ((kept.filter (fun i => projectiveDistance (F.tube i).direction center ≤ u)).card : ℝ) ≤
          (4*(5:ℝ)^k*(2:ℝ)^m)*(u/h)^m := by
  obtain ⟨depth,htop⟩ := exists_dyadic_top hh
  obtain ⟨kept,hsub,hmass,hsep,hblocks⟩ := chart_real_cap_thinning F points
    hδ hδ1 hm hA hc hh hhc hchart hcap hscale depth
  exact ⟨kept,hsub,hmass,hsep,dyadic_bounds_give_cap_bound F kept hh hm depth htop hblocks⟩

/-- The signed coordinate chart map is its own inverse. -/
theorem chartMove_involutive {k : ℕ} (i : Fin (k+1)) (sign : Bool)
    (v : Space (k+1)) :
    ProjectiveGeometry.chartMove i sign (ProjectiveGeometry.chartMove i sign v) = v := by
  apply WithLp.ofLp_injective
  funext coord
  cases sign <;> simp [ProjectiveGeometry.chartMove, ProjectiveGeometry.reindex]

/-- Auxiliary direction family for applying a chart theorem; its empty shades
make explicit that this construction only changes direction coordinates. -/
def directionChartFamily {k M : ℕ} (F : TubeFamily (k+1) M)
    (coord : Fin (k+1)) (sign : Bool) : TubeFamily (k+1) M where
  tube i := {
    base := 0
    direction := ProjectiveGeometry.chartMove coord sign (F.tube i).direction
    unit_direction := (ProjectiveGeometry.chartMove_norm _ _ _).trans (F.tube i).unit_direction }
  shade _ := ∅

/-- The actual cap condition is invariant under a signed coordinate chart map. -/
theorem directionChartFamily_cap {k M : ℕ} (F : TubeFamily (k+1) M)
    (coord : Fin (k+1)) (sign : Bool) {δ m A : ℝ} (hcap : F.CapBound δ m A) :
    (directionChartFamily F coord sign).CapBound δ m A := by
  intro v hv r hdr hr1
  have hv' : ‖ProjectiveGeometry.chartMove coord sign v‖ = 1 :=
    (ProjectiveGeometry.chartMove_norm _ _ _).trans hv
  have heq (w : Space (k+1)) :
      projectiveDistance (ProjectiveGeometry.chartMove coord sign w) v =
        projectiveDistance w (ProjectiveGeometry.chartMove coord sign v) := by
    have h := ProjectiveGeometry.chartMove_projective coord sign w
      (ProjectiveGeometry.chartMove coord sign v)
    simpa only [chartMove_involutive] using h
  simpa only [directionChartFamily, heq] using hcap _ hv' r hdr hr1

/-- One of the actual signed sphere charts contains a dimensional fraction of
all indexed directions, even if the original directions repeat. -/
theorem populous_signed_chart {k M : ℕ} (F : TubeFamily (k+1) M) :
    ∃ coord : Fin (k+1), ∃ sign : Bool, ∃ points : Finset (Fin M),
      (M : ℝ)/(2*((k:ℝ)+1)) ≤ (points.card : ℝ) ∧
      ∀ i ∈ points, 1/((k:ℝ)+1) ≤
        WithLp.ofLp (ProjectiveGeometry.chartMove coord sign (F.tube i).direction) 0 := by
  classical
  have Hex (i : Fin M) : ∃ label : Fin (k+1) × Bool,
      1/((k:ℝ)+1) ≤ WithLp.ofLp
        (ProjectiveGeometry.chartMove label.1 label.2 (F.tube i).direction) 0 := by
    obtain ⟨coord,sign,hs⟩ := ProjectiveGeometry.unit_in_signed_chart (F.tube i).direction (F.tube i).unit_direction
    exact ⟨(coord,sign),hs⟩
  let color := fun i => Classical.choose (Hex i)
  let tree : CapacityTree (Fin M) := .leaf Finset.univ M
  obtain ⟨label,points,_,hmass,_,hcolor,_⟩ := tree.monochromaticSelection
    (by rfl : Finset.univ ⊆ tree.support)
    (by simp [tree, CapacityTree.Admissible] : tree.Admissible Finset.univ) color
  refine ⟨label.1,label.2,points,?_,?_⟩
  · simpa [Fintype.card_prod, Fintype.card_fin, mul_comm] using hmass
  · intro i hi
    have h := Classical.choose_spec (Hex i)
    change 1/((k:ℝ)+1) ≤ WithLp.ofLp
      (ProjectiveGeometry.chartMove (color i).1 (color i).2 (F.tube i).direction) 0 at h
    simpa only [hcolor i hi] using h

/-- Uniform loss for global cap-preserving thinning in ambient dimension k+1. -/
def thinningRetentionConstant (k : ℕ) (m : ℝ) : ℝ :=
  2*((k:ℝ)+1)*ProjectiveGeometry.packingConstant k*((k:ℝ)+2)^m*(3:ℝ)^k

/-- Uniform cap coefficient of the selected coarse family. -/
def thinningCapConstant (k : ℕ) (m : ℝ) : ℝ :=
  4*(5:ℝ)^k*(2:ℝ)^m*((k:ℝ)+1)^m

/-- Global geometric thinning from the actual input cap condition. No laminar
blocks, covering hypothesis, rounding oracle, or original separation is assumed.
The selected original indices retain M/[C(k,m) A (r/δ)^m], have separation
2r/(k+1), and satisfy all actual projective m-caps at scale r. -/
theorem full_cap_thinning {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ r m A : ℝ} (hδ : 0 < δ) (hdr : δ ≤ r) (hr1 : r ≤ 1)
    (hm : 0 ≤ m) (hA : 1 ≤ A) (hcap : F.CapBound δ m A) :
    ∃ kept : Finset (Fin M),
      (M:ℝ)/(thinningRetentionConstant k m*A*(r/δ)^m) ≤ (kept.card : ℝ) ∧
      (∀ i ∈ kept, ∀ j ∈ kept, i ≠ j →
        (2/((k:ℝ)+1))*r ≤ projectiveDistance (F.tube i).direction (F.tube j).direction) ∧
      ∀ center : Space (k+1), ∀ u : ℝ, r ≤ u → u ≤ 1 →
        ((kept.filter (fun i => projectiveDistance (F.tube i).direction center ≤ u)).card : ℝ) ≤
          thinningCapConstant k m*(u/r)^m := by
  classical
  have hd : 0 < (k:ℝ)+1 := by positivity
  have hr : 0 < r := hδ.trans_le hdr
  let c : ℝ := 1/((k:ℝ)+1)
  let h : ℝ := r/((k:ℝ)+1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hhc : h ≤ c := div_le_div_of_nonneg_right hr1 hd.le
  have hhr : h ≤ r := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg hr.le (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hscale_eq : ProjectiveGeometry.chartConstant k c*h = ((k:ℝ)+2)*r := by
    dsimp [ProjectiveGeometry.chartConstant,c,h]
    field_simp
    ring
  have hscale : δ ≤ ProjectiveGeometry.chartConstant k c*h := by
    rw [hscale_eq]
    nlinarith [mul_nonneg hr.le (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  obtain ⟨coord,sign,points,hpoints,hchart⟩ := populous_signed_chart F
  let G := directionChartFamily F coord sign
  obtain ⟨kept,hsub,hmass,hsep,hcaps⟩ := chart_full_cap_thinning G points
    hδ (hdr.trans hr1) hm hA hc hh hhc hchart (directionChartFamily_cap F coord sign hcap) hscale
  have hden : 0 < (ProjectiveGeometry.packingConstant k*A*
      (ProjectiveGeometry.chartConstant k c*h/δ)^m)*(3:ℝ)^k := by
    have hp := ProjectiveGeometry.packingConstant_ge_one k
    have hC := ProjectiveGeometry.chartConstant_pos k hc
    positivity
  have hfactor : (ProjectiveGeometry.chartConstant k c*h/δ)^m =
      ((k:ℝ)+2)^m*(r/δ)^m := by
    rw [hscale_eq, mul_div_assoc, Real.mul_rpow (by positivity) (by positivity)]
  refine ⟨kept,?_,?_,?_⟩
  · calc
      _ = ((M:ℝ)/(2*((k:ℝ)+1)))/((ProjectiveGeometry.packingConstant k*A*
          (ProjectiveGeometry.chartConstant k c*h/δ)^m)*(3:ℝ)^k) := by
            rw [hfactor,div_div]; congr 1; unfold thinningRetentionConstant; ring
      _ ≤ (points.card : ℝ)/((ProjectiveGeometry.packingConstant k*A*
          (ProjectiveGeometry.chartConstant k c*h/δ)^m)*(3:ℝ)^k) :=
        div_le_div_of_nonneg_right hpoints hden.le
      _ ≤ _ := hmass
  · intro i hi j hj hne
    have hs := hsep i hi j hj hne
    simpa [G,directionChartFamily,ProjectiveGeometry.chartMove_projective,h,mul_div_assoc,
      div_mul_eq_mul_div] using hs
  · intro center u hru hu1
    have hs := hcaps (ProjectiveGeometry.chartMove coord sign center) u (hhr.trans hru) hu1
    have heq : u/h = ((k:ℝ)+1)*(u/r) := by dsimp [h]; field_simp
    simp only [G,directionChartFamily,ProjectiveGeometry.chartMove_projective] at hs
    rw [heq, Real.mul_rpow hd.le (div_nonneg (hr.le.trans hru) hr.le)] at hs
    simpa only [thinningCapConstant,mul_assoc] using hs

end
end KakeyaFormal.CapThinningGeometry
