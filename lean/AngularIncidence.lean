import AngularDecomposition

/-! Actual angular cap covers and cellwise angular pieces for a finite shaded
tube family. The finite pieces retain whole original grid cells. -/
namespace KakeyaFormal.AngularIncidence
open KakeyaFormal.AngularDecomposition KakeyaFormal.Localization KakeyaFormal.ProjectiveGeometry
noncomputable section

/-- A separated actual angular net covers every original direction, and the
radius3tau caps around its centers have uniformly bounded directional overlap. -/
theorem bounded_angular_cap_cover {k M : ℕ} (F : TubeFamily (k+1) M)
    {tau : ℝ} (htau : 0 < tau) :
    ∃ net : Finset (Fin M),
      CapCover.SeparatedOn (fun i => (F.tube i).direction) tau net ∧
      (∀ i : Fin M, ∃ j ∈ net,
        projectiveDistance (F.tube i).direction (F.tube j).direction < tau) ∧
      ∀ v : Space (k+1),
        ((net.filter (fun j => projectiveDistance (F.tube j).direction v ≤ 3*tau)).card : ℝ) ≤
          packingConstant k*(3:ℝ)^k := by
  classical
  obtain ⟨net,_,hsep,hcover⟩ := CapCover.finite_projective_net (Finset.univ : Finset (Fin M))
    (fun i => (F.tube i).direction) htau
  refine ⟨net,hsep,fun i => hcover i (Finset.mem_univ _),?_⟩
  intro v
  have hs : ∀ i ∈ net.filter (fun j => projectiveDistance (F.tube j).direction v ≤ 3*tau),
      ∀ j ∈ net.filter (fun j => projectiveDistance (F.tube j).direction v ≤ 3*tau), i ≠ j →
        tau ≤ projectiveDistance (F.tube i).direction (F.tube j).direction :=
    fun i hi j hj hne => hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne
  have h := indexed_projective_cap_packing
    (net.filter (fun j => projectiveDistance (F.tube j).direction v ≤ 3*tau))
    (fun i => (F.tube i).direction) v htau (by linarith : tau ≤ 3*tau)
    (fun i _ => (F.tube i).unit_direction) (fun i hi => (Finset.mem_filter.mp hi).2) hs
  have heq : 3*tau/tau = (3:ℝ) := by field_simp
  simpa only [heq,packingConstant] using h

/-- Each pointwise radius2tau cap fits in a radius3tau global net cap. -/
theorem piece_in_global_cap {k M : ℕ} (F : TubeFamily (k+1) M)
    {tau : ℝ} (net : Finset (Fin M))
    (hcover : ∀ i : Fin M, ∃ j ∈ net,
      projectiveDistance (F.tube i).direction (F.tube j).direction < tau)
    (points : Finset (Fin M)) (i : Fin M)
    (hpiece : ∀ a ∈ points, projectiveDistance (F.tube a).direction (F.tube i).direction ≤ 2*tau) :
    ∃ j ∈ net, ∀ a ∈ points,
      projectiveDistance (F.tube a).direction (F.tube j).direction ≤ 3*tau := by
  obtain ⟨j,hj,hij⟩ := hcover i
  refine ⟨j,hj,?_⟩
  intro a ha
  have ht := projective_triangle (F.tube a).direction (F.tube i).direction (F.tube j).direction
  linarith [hpiece a ha]

/-- Actual original tube indices incident to a full grid cell. -/
def incident {k M : ℕ} (F : TubeFamily k M) (z : Cell k) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter (fun i => z ∈ F.shade i)

theorem mem_incident {k M : ℕ} (F : TubeFamily k M) (z : Cell k) (i : Fin M) :
    i ∈ incident F z ↔ z ∈ F.shade i := by
  classical
  simp [incident]

/-- Total whole-cell incidence, counted with original tube multiplicities. -/
def incidenceMass {k M : ℕ} (F : TubeFamily k M) (cells : Finset (Cell k)) : ℝ :=
  ∑ z ∈ cells, ((incident F z).card : ℝ)

/-- A cell in the actual union has at least one original incident tube. -/
theorem incident_nonempty {k M : ℕ} (F : TubeFamily k M) {z : Cell k}
    (hz : z ∈ F.unionCells) : (incident F z).Nonempty := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
  exact ⟨i,(mem_incident F z i).mpr hi⟩

/-- Construct cellwise disjoint broad index sets at one common actual angular
scale, retaining a single explicit logarithmic fraction of weighted incidence.
Every choice is indexed by original grid cells. -/
theorem common_scale_cell_pieces {k M : ℕ} (F : TubeFamily k M)
    (cells : Finset (Cell k)) (hcells : cells ⊆ F.unionCells)
    {δ beta : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) :
    ∃ J : ℕ, ∃ j : Fin (J+1), ∃ pieces : Cell k → Finset (Fin (J+1) × Finset (Fin M)),
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧ δ ≤ radius J j ∧ radius J j ≤ 1 ∧
      (∀ z ∈ cells, (↑(pieces z) : Set (Fin (J+1) × Finset (Fin M))).PairwiseDisjoint Prod.snd) ∧
      (∀ z ∈ cells, ∀ p ∈ pieces z, p.1 = j ∧ GoodPiece F (incident F z) δ beta J p) ∧
      incidenceMass F cells/(2*((J:ℝ)+1)) ≤ ∑ z ∈ cells, ∑ p ∈ pieces z, (p.2.card : ℝ) ∧
      ∀ z ∈ cells, ((pieces z).card : ℝ) ≤ 2*(radius J j)^(-beta) := by
  classical
  obtain ⟨J,hbottom,hbottom2,hdepth⟩ := ScaleChoice.dyadic_depth hδ hδ1
  have hex (z : Cell k) := disjoint_broad_decomposition F (incident F z) hδ hb J hbottom2.le
  choose allpieces hdis hgood hmass using hex
  have htotal : incidenceMass F cells/2 ≤ ∑ z ∈ cells, ∑ p ∈ allpieces z, (p.2.card : ℝ) := by
    have h := Finset.sum_le_sum (s := cells) (fun z _ => hmass z)
    simpa only [incidenceMass,Finset.sum_div] using h
  have hsum : (∑ j : Fin (J+1), ∑ z ∈ cells,
      ∑ p ∈ allpieces z with p.1 = j, (p.2.card : ℝ)) =
        ∑ z ∈ cells, ∑ p ∈ allpieces z, (p.2.card : ℝ) := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_fiberwise]
  have hpos : (0:ℝ) < J+1 := by positivity
  have havg : (∑ _j : Fin (J+1), incidenceMass F cells/(2*((J:ℝ)+1))) ≤
      ∑ j : Fin (J+1), ∑ z ∈ cells, ∑ p ∈ allpieces z with p.1 = j, (p.2.card : ℝ) := by
    rw [hsum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
    have heq : ((J:ℝ)+1)*(incidenceMass F cells/(2*((J:ℝ)+1))) = incidenceMass F cells/2 := by
      field_simp
    simpa only [heq,packingConstant] using htotal
  obtain ⟨j,_,hjmass⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  let pieces := fun z => (allpieces z).filter (fun p => p.1 = j)
  have hsub (z : Cell k) : pieces z ⊆ allpieces z := Finset.filter_subset _ _
  have hpdis (z : Cell k) : (↑(pieces z) : Set (Fin (J+1) × Finset (Fin M))).PairwiseDisjoint Prod.snd := by
    intro p hp q hq hpq
    exact hdis z (hsub z hp) (hsub z hq) hpq
  have hpgood (z : Cell k) : ∀ p ∈ pieces z, GoodPiece F (incident F z) δ beta J p :=
    fun p hp => hgood z p (hsub z hp)
  have hpscale (z : Cell k) : ∀ p ∈ pieces z, p.1 = j := fun p hp => (Finset.mem_filter.mp hp).2
  refine ⟨J,j,pieces,hdepth,hbottom.trans (radius_mono J (Nat.zero_le j)),?_,
    fun z _ => hpdis z,fun z _ p hp => ⟨hpscale z p hp,hpgood z p hp⟩,hjmass,?_⟩
  · simpa only [radius_top] using radius_mono J (show j.val ≤ J by omega)
  · intro z hz
    exact common_scale_piece_count F (incident F z) (incident_nonempty F (hcells hz))
      (pieces z) (hpdis z) (hpgood z) j (hpscale z)

/-- Group finite original pieces according to an actual label assignment. -/
def regroup {α ι γ : Type*} [DecidableEq α] [DecidableEq γ]
    (pieces : Finset ι) (support : ι → Finset α) (assign : ι → γ) (g : γ) : Finset α :=
  (pieces.filter (fun p => assign p = g)).biUnion support

theorem mem_regroup {α ι γ : Type*} [DecidableEq α] [DecidableEq γ]
    (pieces : Finset ι) (support : ι → Finset α) (assign : ι → γ) (g : γ) (a : α) :
    a ∈ regroup pieces support assign g ↔ ∃ p ∈ pieces, assign p = g ∧ a ∈ support p := by
  classical
  simp only [regroup,Finset.mem_biUnion,Finset.mem_filter]
  aesop

/-- Different assigned groups still have disjoint actual direction-index sets. -/
theorem regroup_disjoint {α ι γ : Type*} [DecidableEq α] [DecidableEq γ]
    (pieces : Finset ι) (support : ι → Finset α) (assign : ι → γ)
    (hdis : (↑pieces : Set ι).PairwiseDisjoint support) {g h : γ} (hgh : g ≠ h) :
    Disjoint (regroup pieces support assign g) (regroup pieces support assign h) := by
  classical
  apply Finset.disjoint_left.mpr
  intro a hag hah
  obtain ⟨p,hp,hpg,hpa⟩ := (mem_regroup _ _ _ _ _).mp hag
  obtain ⟨q,hq,hqh,hqa⟩ := (mem_regroup _ _ _ _ _).mp hah
  by_cases hpq : p = q
  · subst q
    exact hgh (hpg.symm.trans hqh)
  · exact Finset.disjoint_left.mp (hdis hp hq hpq) hpa hqa

/-- Regrouping disjoint pieces preserves the exact total incidence count. -/
theorem regroup_sum_card {α ι γ : Type*} [DecidableEq α] [DecidableEq γ]
    (pieces : Finset ι) (support : ι → Finset α) (assign : ι → γ)
    (groups : Finset γ) (hassign : ∀ p ∈ pieces, assign p ∈ groups)
    (hdis : (↑pieces : Set ι).PairwiseDisjoint support) :
    (∑ g ∈ groups, (regroup pieces support assign g).card) = ∑ p ∈ pieces, (support p).card := by
  classical
  have heq (g : γ) : (regroup pieces support assign g).card =
      ∑ p ∈ pieces with assign p = g, (support p).card := by
    apply Finset.card_biUnion
    intro p hp q hq hpq
    exact hdis (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 hpq
  simp_rw [heq]
  exact Finset.sum_fiberwise_of_maps_to hassign _

/-- Regrouping disjoint broad subsets at one scale preserves their broadness. -/
theorem regroup_broad {k M : ℕ} {ι γ : Type*} [DecidableEq γ]
    (F : TubeFamily k M) (pieces : Finset ι) (support : ι → Finset (Fin M))
    (assign : ι → γ) (hdis : (↑pieces : Set ι).PairwiseDisjoint support)
    {δ beta tau K : ℝ} (hbroad : ∀ p ∈ pieces, Broad F (support p) δ beta tau K) (g : γ) :
    Broad F (regroup pieces support assign g) δ beta tau K := by
  classical
  apply broad_biUnion
  · intro p hp q hq hpq
    exact hdis (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 hpq
  · intro p hp
    exact hbroad p (Finset.mem_filter.mp hp).1

/-- The number of occupied groups cannot exceed the number of original pieces. -/
theorem regroup_occupied_count {α ι γ : Type*} [DecidableEq α] [DecidableEq γ]
    (pieces : Finset ι) (support : ι → Finset α) (assign : ι → γ) (groups : Finset γ) :
    (groups.filter (fun g => (regroup pieces support assign g).Nonempty)).card ≤ pieces.card := by
  classical
  have hs : groups.filter (fun g => (regroup pieces support assign g).Nonempty) ⊆ pieces.image assign := by
    intro g hg
    obtain ⟨a,ha⟩ := (Finset.mem_filter.mp hg).2
    obtain ⟨p,hp,hpg,_⟩ := (mem_regroup _ _ _ _ _).mp ha
    exact Finset.mem_image.mpr ⟨p,hp,hpg⟩
  exact (Finset.card_le_card hs).trans Finset.card_image_le

/-- Actual global angular groups of whole-cell incidences. Both the global cap
cover and the pointwise broad subsets are constructed. Directional overlap is
bounded by a dimension-only constant, ready for assigning each tube once. -/
theorem actual_angular_groups {k M : ℕ} (F : TubeFamily (k+1) M) (hM : 0 < M)
    (cells : Finset (Cell (k+1))) (hcells : cells ⊆ F.unionCells)
    {δ beta : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) :
    ∃ J : ℕ, ∃ j : Fin (J+1), ∃ net : Finset (Fin M),
      ∃ group : Cell (k+1) → Fin M → Finset (Fin M),
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧ δ ≤ radius J j ∧ radius J j ≤ 1 ∧
      net.Nonempty ∧
      (∀ z ∈ cells, ∀ g ∈ net, group z g ⊆ incident F z) ∧
      (∀ z ∈ cells, ∀ g ∈ net, ∀ a ∈ group z g,
        projectiveDistance (F.tube a).direction (F.tube g).direction ≤ 3*radius J j) ∧
      (∀ z ∈ cells, Pairwise (fun g h => Disjoint (group z g) (group z h))) ∧
      (∀ z ∈ cells, ∀ g ∈ net, Broad F (group z g) δ beta (radius J j) ((4:ℝ)^beta)) ∧
      incidenceMass F cells/(2*((J:ℝ)+1)) ≤ ∑ z ∈ cells, ∑ g ∈ net, ((group z g).card : ℝ) ∧
      (∀ z ∈ cells, ((net.filter (fun g => (group z g).Nonempty)).card : ℝ) ≤
        2*(radius J j)^(-beta)) ∧
      ∀ a : Fin M, ((net.filter (fun g => ∃ z ∈ cells, a ∈ group z g)).card : ℝ) ≤
        packingConstant k*(3:ℝ)^k := by
  classical
  obtain ⟨J,j,pieces,hdepth,hdτ,hτ1,hdis,hgood,hmass,hnumber⟩ :=
    common_scale_cell_pieces F cells hcells hδ hδ1 hb
  obtain ⟨net,_,hcover,hnetcount⟩ := bounded_angular_cap_cover F (radius_pos J j)
  obtain ⟨fallback,hfallback,_⟩ := hcover (⟨0,hM⟩ : Fin M)
  have hex (z : Cell (k+1)) (p : Fin (J+1) × Finset (Fin M)) :
      ∃ g ∈ net, z ∈ cells → p ∈ pieces z → ∀ a ∈ p.2,
        projectiveDistance (F.tube a).direction (F.tube g).direction ≤ 3*radius J j := by
    by_cases hz : z ∈ cells
    · by_cases hp : p ∈ pieces z
      · obtain ⟨i,_,hi⟩ := (hgood z hz p hp).2.2.2.1
        have hc : ∀ a ∈ p.2,
            projectiveDistance (F.tube a).direction (F.tube i).direction ≤ 2*radius J j := by
          simpa only [(hgood z hz p hp).1] using hi
        obtain ⟨g,hg,hcap⟩ := piece_in_global_cap F net hcover p.2 i hc
        exact ⟨g,hg,fun _ _ => hcap⟩
      · exact ⟨fallback,hfallback,fun _ hp' => False.elim (hp hp')⟩
    · exact ⟨fallback,hfallback,fun hz' => False.elim (hz hz')⟩
  choose assign hassign hcontain using hex
  let group := fun z g => regroup (pieces z) Prod.snd (assign z) g
  have hgsub (z : Cell (k+1)) (hz : z ∈ cells) (g : Fin M) : group z g ⊆ incident F z := by
    intro a ha
    obtain ⟨p,hp,_,hpa⟩ := (mem_regroup _ _ _ _ _).mp ha
    exact (hgood z hz p hp).2.2.1 hpa
  have hgcap (z : Cell (k+1)) (hz : z ∈ cells) (g : Fin M) : ∀ a ∈ group z g,
      projectiveDistance (F.tube a).direction (F.tube g).direction ≤ 3*radius J j := by
    intro a ha
    obtain ⟨p,hp,hpg,hpa⟩ := (mem_regroup _ _ _ _ _).mp ha
    simpa only [hpg] using hcontain z p hz hp a hpa
  have hgdis (z : Cell (k+1)) (hz : z ∈ cells) :
      Pairwise (fun g h => Disjoint (group z g) (group z h)) :=
    fun _ _ hne => regroup_disjoint (pieces z) Prod.snd (assign z) (hdis z hz) hne
  have hgbroad (z : Cell (k+1)) (hz : z ∈ cells) (g : Fin M) :
      Broad F (group z g) δ beta (radius J j) ((4:ℝ)^beta) := by
    apply regroup_broad F (pieces z) Prod.snd (assign z) (hdis z hz)
    intro p hp
    have h := (hgood z hz p hp).2.2.2.2.2
    simpa only [(hgood z hz p hp).1,Broad] using h
  have hgsum (z : Cell (k+1)) (hz : z ∈ cells) :
      (∑ g ∈ net, ((group z g).card : ℝ)) = ∑ p ∈ pieces z, (p.2.card : ℝ) := by
    have h := regroup_sum_card (pieces z) Prod.snd (assign z) net (fun p _ => hassign z p) (hdis z hz)
    exact_mod_cast h
  refine ⟨J,j,net,group,hdepth,hdτ,hτ1,⟨fallback,hfallback⟩,
    fun z hz g _ => hgsub z hz g,fun z hz g _ => hgcap z hz g,hgdis,
    fun z hz g _ => hgbroad z hz g,?_,?_,?_⟩
  · exact hmass.trans_eq (Finset.sum_congr rfl (fun z hz => (hgsum z hz).symm))
  · intro z hz
    have h := regroup_occupied_count (pieces z) Prod.snd (assign z) net
    exact (by exact_mod_cast h : ((net.filter (fun g => (group z g).Nonempty)).card : ℝ) ≤ (pieces z).card).trans
      (hnumber z hz)
  · intro a
    have hs : net.filter (fun g => ∃ z ∈ cells, a ∈ group z g) ⊆
        net.filter (fun g => projectiveDistance (F.tube g).direction (F.tube a).direction ≤ 3*radius J j) := by
      intro g hg
      obtain ⟨z,hz,ha⟩ := (Finset.mem_filter.mp hg).2
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
        by simpa only [projective_symm] using hgcap z hz g a ha⟩
    have hc : ((net.filter (fun g => ∃ z ∈ cells, a ∈ group z g)).card : ℝ) ≤
        (net.filter (fun g => projectiveDistance (F.tube g).direction (F.tube a).direction ≤ 3*radius J j)).card := by
      exact_mod_cast Finset.card_le_card hs
    exact hc.trans (hnetcount (F.tube a).direction)

end
end KakeyaFormal.AngularIncidence
