import AngularIncidence

/-! Actual simultaneous tube-to-group assignment and proportional whole-cell
restoration for the angular decomposition. -/
namespace KakeyaFormal.AngularAssignment
open KakeyaFormal.AngularIncidence KakeyaFormal.AngularDecomposition
noncomputable section

/-- Finite maximization assigns every index to one group, with the reciprocal
loss determined by the number of groups in which it has nonzero weight. -/
theorem weighted_group_assignment {ι γ : Type*} [DecidableEq γ]
    (groups : Finset γ) (hne : groups.Nonempty) (weight : ι → γ → ℝ)
    (hw : ∀ i g, 0 ≤ weight i g) {C : ℝ}
    (hcount : ∀ i, ((groups.filter (fun g => weight i g ≠ 0)).card : ℝ) ≤ C) :
    ∃ assign : ι → γ, (∀ i, assign i ∈ groups) ∧
      ∀ i, (∑ g ∈ groups, weight i g) ≤ C*weight i (assign i) := by
  classical
  have hex (i : ι) := Finset.exists_max_image groups (weight i) hne
  choose assign hassign hmax using hex
  refine ⟨assign,hassign,?_⟩
  intro i
  let active := groups.filter (fun g => weight i g ≠ 0)
  have hsum : ∑ g ∈ groups, weight i g = ∑ g ∈ active, weight i g := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro g hg hgn
    by_contra hwg
    exact hgn (Finset.mem_filter.mpr ⟨hg,hwg⟩)
  rw [hsum]
  calc
    _ ≤ ∑ _g ∈ active, weight i (assign i) :=
      Finset.sum_le_sum (fun g hg => hmax i g (Finset.mem_filter.mp hg).1)
    _ = (active.card : ℝ)*weight i (assign i) := by simp
    _ ≤ C*weight i (assign i) := mul_le_mul_of_nonneg_right (hcount i) (hw i (assign i))

/-- Exact finite whole-cell incidence double counting. -/
theorem sum_row_cards {α : Type*} (cells : Finset α) {M : ℕ}
    (row : α → Finset (Fin M)) :
    (∑ z ∈ cells, (row z).card) = ∑ i : Fin M, (cells.filter (fun z => i ∈ row z)).card := by
  classical
  have hrow (z : α) : (row z).card = ∑ i : Fin M, if i ∈ row z then 1 else 0 := by simp
  simp_rw [hrow]
  rw [Finset.sum_comm]
  congr 1
  funext i
  simp

/-- Count weight for one original tube in one group over all original cells. -/
def tubeWeight {α γ : Type*} (cells : Finset α) {M : ℕ}
    (group : α → γ → Finset (Fin M)) (i : Fin M) (g : γ) : ℝ :=
  ((cells.filter (fun z => i ∈ group z g)).card : ℝ)

/-- Keep the whole cell precisely when its tube has been assigned to this group. -/
def assigned {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (group : α → γ → Finset (Fin M)) (assign : Fin M → γ) (z : α) (g : γ) : Finset (Fin M) :=
  (group z g).filter (fun i => assign i = g)

/-- The assigned tube contributes exactly its chosen group's original weight. -/
theorem assigned_total {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (cells : Finset α) (groups : Finset γ) (group : α → γ → Finset (Fin M))
    (assign : Fin M → γ) (hassign : ∀ i, assign i ∈ groups) :
    (∑ z ∈ cells, ∑ g ∈ groups, ((assigned group assign z g).card : ℝ)) =
      ∑ i : Fin M, tubeWeight cells group i (assign i) := by
  classical
  rw [Finset.sum_comm]
  have hrows (g : γ) : (∑ z ∈ cells, ((assigned group assign z g).card : ℝ)) =
      ∑ i : Fin M, tubeWeight cells (assigned group assign) i g := by
    unfold tubeWeight
    exact_mod_cast sum_row_cards cells (fun z => assigned group assign z g)
  simp_rw [hrows]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (assign i)]
  · simp [tubeWeight,assigned]
  · intro g _ hgne
    simp [tubeWeight,assigned,Ne.symm hgne]
  · exact fun h => False.elim (h (hassign i))

/-- Actual finite assignment retains the inverse overlap fraction of incidence. -/
theorem assign_incidence {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (cells : Finset α) (groups : Finset γ) (hne : groups.Nonempty)
    (group : α → γ → Finset (Fin M)) {C : ℝ} (hC : 0 < C)
    (hcount : ∀ i : Fin M, ((groups.filter (fun g => ∃ z ∈ cells, i ∈ group z g)).card : ℝ) ≤ C) :
    ∃ assign : Fin M → γ, (∀ i, assign i ∈ groups) ∧
      (∑ z ∈ cells, ∑ g ∈ groups, ((group z g).card : ℝ))/C ≤
        ∑ z ∈ cells, ∑ g ∈ groups, ((assigned group assign z g).card : ℝ) := by
  classical
  have hw : ∀ i g, 0 ≤ tubeWeight cells group i g := fun _ _ => Nat.cast_nonneg _
  have hactive (i : Fin M) : groups.filter (fun g => tubeWeight cells group i g ≠ 0) =
      groups.filter (fun g => ∃ z ∈ cells, i ∈ group z g) := by
    ext g
    simp [tubeWeight]
  obtain ⟨assign,hassign,hbound⟩ := weighted_group_assignment groups hne (tubeWeight cells group) hw
    (fun i => by simpa only [hactive] using hcount i)
  refine ⟨assign,hassign,?_⟩
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
  have hbefore : (∑ z ∈ cells, ∑ g ∈ groups, ((group z g).card : ℝ)) =
      ∑ i : Fin M, ∑ g ∈ groups, tubeWeight cells group i g := by
    rw [Finset.sum_comm,Finset.sum_comm (s := (Finset.univ : Finset (Fin M)))]
    apply Finset.sum_congr rfl
    intro g _
    unfold tubeWeight
    exact_mod_cast sum_row_cards cells (fun z => group z g)
  rw [hbefore, assigned_total cells groups group assign hassign]
  apply (div_le_iff₀ hC).mpr
  simpa only [Finset.mul_sum,mul_comm] using hsum

/-- Proportional whole-piece restoration after a1/C assignment loss discards at
most one quarter of post-assignment mass. The threshold is explicitly4C. -/
theorem threshold_retains_three_quarters {ι : Type*} (s : Finset ι)
    (before after : ι → ℝ) {C : ℝ} (hC : 0 < C)
    (hbefore : ∀ i ∈ s, 0 ≤ before i)
    (hcalibrate : (∑ i ∈ s, before i) ≤ C*(∑ i ∈ s, after i)) :
    (3/4:ℝ)*(∑ i ∈ s, after i) ≤
      ∑ i ∈ s, if before i ≤ 4*C*after i then after i else 0 := by
  classical
  have hbad : (∑ i ∈ s, if before i ≤ 4*C*after i then 0 else after i) ≤
      (∑ i ∈ s, before i)/(4*C) := by
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    split_ifs with hgood
    · exact div_nonneg (hbefore i hi) (by positivity)
    · apply (le_div_iff₀ (by positivity : 0 < 4*C)).mpr
      nlinarith [lt_of_not_ge hgood]
  have hbad' : (∑ i ∈ s, before i)/(4*C) ≤ (∑ i ∈ s, after i)/4 := by
    apply (div_le_iff₀ (by positivity : 0 < 4*C)).mpr
    nlinarith
  have hsplit : (∑ i ∈ s, if before i ≤ 4*C*after i then after i else 0) +
      (∑ i ∈ s, if before i ≤ 4*C*after i then 0 else after i) = ∑ i ∈ s, after i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  linarith [hbad.trans hbad']

/-- The restored incidence set keeps or deletes an entire original cell in a
group, according to its actual before/after cardinality ratio. -/
def restored {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (group : α → γ → Finset (Fin M)) (assign : Fin M → γ) (C : ℝ)
    (z : α) (g : γ) : Finset (Fin M) := by
  classical
  exact if ((group z g).card : ℝ) ≤ 4*C*((assigned group assign z g).card : ℝ)
    then assigned group assign z g else ∅

theorem restored_subset {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (group : α → γ → Finset (Fin M)) (assign : Fin M → γ) (C : ℝ) (z : α) (g : γ) :
    restored group assign C z g ⊆ assigned group assign z g := by
  classical
  unfold restored
  split_ifs
  · exact le_rfl
  · exact Finset.empty_subset _

theorem restored_broad {k M : ℕ} {γ : Type*} [DecidableEq γ]
    (F : TubeFamily k M) (group : Cell k → γ → Finset (Fin M))
    (assign : Fin M → γ) {δ beta tau K C : ℝ} (hδ : 0 ≤ δ) (htau : 0 < tau) (hK : 0 ≤ K)
    (z : Cell k) (g : γ) (hbroad : Broad F (group z g) δ beta tau K) :
    Broad F (restored group assign C z g) δ beta tau (K*(4*C)) := by
  classical
  unfold restored
  split_ifs with hgood
  · exact broad_proportional_subset F (Finset.filter_subset _ _) hδ htau hK hgood hbroad
  · intro center r hr
    simp [cap]

/-- Simultaneous actual assignment and whole-cell restoration: every surviving
index has its unique chosen group, and at least3/(4C) of incidence survives. -/
theorem assign_and_restore {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (cells : Finset α) (groups : Finset γ) (hne : groups.Nonempty)
    (group : α → γ → Finset (Fin M)) {C : ℝ} (hC : 0 < C)
    (hcount : ∀ i : Fin M, ((groups.filter (fun g => ∃ z ∈ cells, i ∈ group z g)).card : ℝ) ≤ C) :
    ∃ assign : Fin M → γ, (∀ i, assign i ∈ groups) ∧
      (3/(4*C))*(∑ z ∈ cells, ∑ g ∈ groups, ((group z g).card : ℝ)) ≤
        ∑ z ∈ cells, ∑ g ∈ groups, ((restored group assign C z g).card : ℝ) ∧
      ∀ z g i, i ∈ restored group assign C z g → i ∈ group z g ∧ assign i = g := by
  classical
  obtain ⟨assign,hassign,hmass⟩ := assign_incidence cells groups hne group hC hcount
  have hcal : (∑ z ∈ cells, ∑ g ∈ groups, ((group z g).card : ℝ)) ≤
      C*(∑ z ∈ cells, ∑ g ∈ groups, ((assigned group assign z g).card : ℝ)) :=
    by simpa only [mul_comm] using (div_le_iff₀ hC).mp hmass
  have hrestore := threshold_retains_three_quarters (cells ×ˢ groups)
    (fun p => ((group p.1 p.2).card : ℝ))
    (fun p => ((assigned group assign p.1 p.2).card : ℝ)) hC
    (fun _ _ => Nat.cast_nonneg _) (by simpa only [Finset.sum_product] using hcal)
  have hret : (3/4:ℝ)*(∑ z ∈ cells, ∑ g ∈ groups, ((assigned group assign z g).card : ℝ)) ≤
      ∑ z ∈ cells, ∑ g ∈ groups, ((restored group assign C z g).card : ℝ) := by
    have hid (z : α) (g : γ) : ((restored group assign C z g).card : ℝ) =
        if ((group z g).card : ℝ) ≤ 4*C*((assigned group assign z g).card : ℝ)
          then ((assigned group assign z g).card : ℝ) else 0 := by
      unfold restored
      split_ifs <;> simp
    simp_rw [hid]
    simpa only [Finset.sum_product] using hrestore
  refine ⟨assign,hassign,?_,?_⟩
  · have h := mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ) ≤ 3/4)
    have heq : (3/(4*C))*(∑ z ∈ cells, ∑ g ∈ groups, ((group z g).card : ℝ)) =
        (3/4:ℝ)*((∑ z ∈ cells, ∑ g ∈ groups, ((group z g).card : ℝ))/C) := by ring
    rw [heq]
    exact h.trans hret
  · intro z g i hi
    exact Finset.mem_filter.mp (restored_subset group assign C z g hi)

/-- Actual finite shading after assignment/restoration in a group. -/
def restoredShading {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (cells : Finset α) (group : α → γ → Finset (Fin M)) (assign : Fin M → γ)
    (C : ℝ) (g : γ) (i : Fin M) : Finset α := by
  classical
  exact cells.filter (fun z => i ∈ restored group assign C z g)

/-- Full-cell incidence of the constructed shading agrees with the restored
finite direction subset on every retained original cell. -/
theorem restored_cell_incidence {α γ : Type*} [DecidableEq α] [DecidableEq γ] {M : ℕ}
    (cells : Finset α) (group : α → γ → Finset (Fin M)) (assign : Fin M → γ)
    (C : ℝ) (g : γ) {z : α} (hz : z ∈ cells) :
    (Finset.univ.filter (fun i => z ∈ restoredShading cells group assign C g i)) =
      restored group assign C z g := by
  classical
  ext i
  simp [restoredShading,hz]

/-- Exact equality of incidence mass and the sum of actual constructed shading sizes. -/
theorem total_restored_shading {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (cells : Finset α) (groups : Finset γ) (group : α → γ → Finset (Fin M))
    (assign : Fin M → γ) (C : ℝ) :
    (∑ g ∈ groups, ∑ i : Fin M, ((restoredShading cells group assign C g i).card : ℝ)) =
      ∑ z ∈ cells, ∑ g ∈ groups, ((restored group assign C z g).card : ℝ) := by
  classical
  rw [Finset.sum_comm (s := cells)]
  apply Finset.sum_congr rfl
  intro g _
  unfold restoredShading
  exact_mod_cast (sum_row_cards cells (fun z => restored group assign C z g)).symm

/-- Concrete simultaneous angular assignment of actual original tube shadings.
Every tube has one assigned cap; broadness and angular overlap hold on whole
cells; all constants are uniform in delta, tube count and the input shading. -/
theorem actual_angular_shading_assignment {k M : ℕ} (F : TubeFamily (k+1) M) (hM : 0 < M)
    (cells : Finset (Cell (k+1))) (hcells : cells ⊆ F.unionCells)
    {δ beta : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) :
    let C := ProjectiveGeometry.packingConstant k*(3:ℝ)^k
    ∃ J : ℕ, ∃ j : Fin (J+1), ∃ net : Finset (Fin M), ∃ assign : Fin M → Fin M,
      ∃ shading : Fin M → Fin M → Finset (Cell (k+1)),
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      δ ≤ Localization.radius J j ∧ Localization.radius J j ≤ 1 ∧
      (∀ i, assign i ∈ net) ∧
      (∀ g i, shading g i ⊆ F.shade i ∧ shading g i ⊆ cells) ∧
      (∀ g i, (shading g i).Nonempty → assign i = g) ∧
      (∀ g ∈ net, ∀ i, (shading g i).Nonempty →
        projectiveDistance (F.tube i).direction (F.tube g).direction ≤ 3*Localization.radius J j) ∧
      (3/(4*C))*(incidenceMass F cells/(2*((J:ℝ)+1))) ≤
        ∑ g ∈ net, ∑ i : Fin M, ((shading g i).card : ℝ) ∧
      (∀ z : Cell (k+1), ∀ g ∈ net,
        Broad F (Finset.univ.filter (fun i => z ∈ shading g i))
          δ beta (Localization.radius J j) (((4:ℝ)^beta)*(4*C))) ∧
      ∀ z : Cell (k+1),
        ((net.filter (fun g => ∃ i, z ∈ shading g i)).card : ℝ) ≤
          2*(Localization.radius J j)^(-beta) := by
  classical
  let C := ProjectiveGeometry.packingConstant k*(3:ℝ)^k
  have hC : 0 < C := by
    have hp := ProjectiveGeometry.packingConstant_ge_one k
    dsimp [C]
    positivity
  obtain ⟨J,j,net,group,hdepth,hdτ,hτ1,hnet,hsub,hcap,hdis,hbroad,hmass,hover,hcount⟩ :=
    actual_angular_groups F hM cells hcells hδ hδ1 hb
  obtain ⟨assign,hassign,hretain,hunique⟩ := assign_and_restore cells net hnet group hC hcount
  let shading := restoredShading cells group assign C
  have hcell (z : Cell (k+1)) (hz : z ∈ cells) (g : Fin M) :
      Finset.univ.filter (fun i => z ∈ shading g i) = restored group assign C z g :=
    restored_cell_incidence cells group assign C g hz
  have hraw (g i : Fin M) {z : Cell (k+1)} (hz : z ∈ shading g i) :
      z ∈ cells ∧ i ∈ group z g ∧ assign i = g := by
    have hs := Finset.mem_filter.mp hz
    exact ⟨hs.1,hunique z g i hs.2⟩
  have hgnet (g i : Fin M) {z : Cell (k+1)} (hz : z ∈ shading g i) : g ∈ net := by
    rw [← (hraw g i hz).2.2]
    exact hassign i
  refine ⟨J,j,net,assign,shading,hdepth,hdτ,hτ1,hassign,?_,?_,?_,?_,?_,?_⟩
  · intro g i
    constructor
    · intro z hz
      have hs := hraw g i hz
      exact (mem_incident F z i).mp (hsub z hs.1 g (hgnet g i hz) hs.2.1)
    · exact Finset.filter_subset _ _
  · intro g i hi
    obtain ⟨z,hz⟩ := hi
    exact (hraw g i hz).2.2
  · intro g hg i hi
    obtain ⟨z,hz⟩ := hi
    exact hcap z (hraw g i hz).1 g hg i (hraw g i hz).2.1
  · rw [total_restored_shading]
    exact (mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 3/(4*C))).trans hretain
  · intro z g hg
    by_cases hz : z ∈ cells
    · rw [hcell z hz g]
      exact restored_broad F group assign hδ.le (Localization.radius_pos J j)
        (Real.rpow_nonneg (by norm_num) beta) z g (hbroad z hz g hg)
    · have hempty : Finset.univ.filter (fun i => z ∈ shading g i) = ∅ := by
        simp [shading,restoredShading,hz]
      rw [hempty]
      intro center r hr
      simp [cap]
  · intro z
    by_cases hz : z ∈ cells
    · have hs : net.filter (fun g => ∃ i, z ∈ shading g i) ⊆
          net.filter (fun g => (group z g).Nonempty) := by
        intro g hg
        obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hg).2
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,⟨i,(hraw g i hi).2.1⟩⟩
      have hc : ((net.filter (fun g => ∃ i, z ∈ shading g i)).card : ℝ) ≤
          (net.filter (fun g => (group z g).Nonempty)).card := by exact_mod_cast Finset.card_le_card hs
      exact hc.trans (hover z hz)
    · have hempty : net.filter (fun g => ∃ i, z ∈ shading g i) = ∅ := by
        simp [shading,restoredShading,hz]
      rw [hempty,Finset.card_empty,Nat.cast_zero]
      have ht := Localization.radius_pos J j
      positivity

end
end KakeyaFormal.AngularAssignment
