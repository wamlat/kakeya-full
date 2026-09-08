import WeightedAngularAssignment

/-! Angular selection on arbitrary finite weighted incidence atoms. All
geometry depends only on original directions; no atom-count loss is incurred. -/
namespace KakeyaFormal.WeightedAngularSelection
open AngularDecomposition AngularIncidence KakeyaFormal.Localization ProjectiveGeometry
noncomputable section
open Classical

theorem common_scale_pieces {α : Type*} {k M : ℕ} (F : TubeFamily k M)
    (atoms : Finset α) (w : α → ℝ) (hw : ∀ z ∈ atoms, 0 ≤ w z)
    (row : α → Finset (Fin M)) (hrow : ∀ z ∈ atoms, (row z).Nonempty)
    {δ beta : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) :
    ∃ J : ℕ, ∃ j : Fin (J+1), ∃ pieces : α → Finset (Fin (J+1) × Finset (Fin M)),
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧ δ ≤ radius J j ∧ radius J j ≤ 1 ∧
      (∀ z ∈ atoms, (↑(pieces z) : Set (Fin (J+1) × Finset (Fin M))).PairwiseDisjoint Prod.snd) ∧
      (∀ z ∈ atoms, ∀ p ∈ pieces z, p.1 = j ∧ GoodPiece F (row z) δ beta J p) ∧
      (∑ z ∈ atoms, w z*((row z).card:ℝ))/(2*((J:ℝ)+1)) ≤ ∑ z ∈ atoms, w z*(∑ p ∈ pieces z, (p.2.card : ℝ)) ∧
      ∀ z ∈ atoms, ((pieces z).card : ℝ) ≤ 2*(radius J j)^(-beta) := by
  classical
  obtain ⟨J,hbottom,hbottom2,hdepth⟩ := ScaleChoice.dyadic_depth hδ hδ1
  have hex (z : α) := disjoint_broad_decomposition F (row z) hδ hb J hbottom2.le
  choose allpieces hdis hgood hmass using hex
  have htotal : (∑ z ∈ atoms, w z*((row z).card:ℝ))/2 ≤ ∑ z ∈ atoms, w z*(∑ p ∈ allpieces z, (p.2.card : ℝ)) := by
    have h := Finset.sum_le_sum (s := atoms)
      (fun z hz => mul_le_mul_of_nonneg_left (hmass z) (hw z hz))
    simpa only [← mul_div_assoc,Finset.sum_div] using h
  have hsum : (∑ j : Fin (J+1), ∑ z ∈ atoms,
      w z*(∑ p ∈ allpieces z with p.1 = j, (p.2.card : ℝ))) =
        ∑ z ∈ atoms, w z*(∑ p ∈ allpieces z, (p.2.card : ℝ)) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,Finset.sum_fiberwise]
  have hpos : (0:ℝ) < J+1 := by positivity
  have havg : (∑ _j : Fin (J+1), (∑ z ∈ atoms, w z*((row z).card:ℝ))/(2*((J:ℝ)+1))) ≤
      ∑ j : Fin (J+1), ∑ z ∈ atoms, w z*(∑ p ∈ allpieces z with p.1 = j, (p.2.card : ℝ)) := by
    rw [hsum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
    have heq : ((J:ℝ)+1)*((∑ z ∈ atoms, w z*((row z).card:ℝ))/(2*((J:ℝ)+1))) = (∑ z ∈ atoms, w z*((row z).card:ℝ))/2 := by
      field_simp
    simpa only [heq,packingConstant] using htotal
  obtain ⟨j,_,hjmass⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty havg
  let pieces := fun z => (allpieces z).filter (fun p => p.1 = j)
  have hsub (z : α) : pieces z ⊆ allpieces z := Finset.filter_subset _ _
  have hpdis (z : α) : (↑(pieces z) : Set (Fin (J+1) × Finset (Fin M))).PairwiseDisjoint Prod.snd := by
    intro p hp q hq hpq
    exact hdis z (hsub z hp) (hsub z hq) hpq
  have hpgood (z : α) : ∀ p ∈ pieces z, GoodPiece F (row z) δ beta J p :=
    fun p hp => hgood z p (hsub z hp)
  have hpscale (z : α) : ∀ p ∈ pieces z, p.1 = j := fun p hp => (Finset.mem_filter.mp hp).2
  refine ⟨J,j,pieces,hdepth,hbottom.trans (radius_mono J (Nat.zero_le j)),?_,
    fun z _ => hpdis z,fun z _ p hp => ⟨hpscale z p hp,hpgood z p hp⟩,hjmass,?_⟩
  · simpa only [radius_top] using radius_mono J (show j.val ≤ J by omega)
  · intro z hz
    exact common_scale_piece_count F (row z) (hrow z hz)
      (pieces z) (hpdis z) (hpgood z) j (hpscale z)

theorem actual_angular_groups {α : Type*} {k M : ℕ} (F : TubeFamily (k+1) M) (hM : 0 < M)
    (atoms : Finset α) (w : α → ℝ) (hw : ∀ z ∈ atoms, 0 ≤ w z)
    (row : α → Finset (Fin M)) (hrow : ∀ z ∈ atoms, (row z).Nonempty)
    {δ beta : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) :
    ∃ J : ℕ, ∃ j : Fin (J+1), ∃ net : Finset (Fin M),
      ∃ group : α → Fin M → Finset (Fin M),
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧ δ ≤ radius J j ∧ radius J j ≤ 1 ∧
      net.Nonempty ∧
      (∀ z ∈ atoms, ∀ g ∈ net, group z g ⊆ row z) ∧
      (∀ z ∈ atoms, ∀ g ∈ net, ∀ a ∈ group z g,
        projectiveDistance (F.tube a).direction (F.tube g).direction ≤ 3*radius J j) ∧
      (∀ z ∈ atoms, Pairwise (fun g h => Disjoint (group z g) (group z h))) ∧
      (∀ z ∈ atoms, ∀ g ∈ net, Broad F (group z g) δ beta (radius J j) ((4:ℝ)^beta)) ∧
      (∑ z ∈ atoms, w z*((row z).card:ℝ))/(2*((J:ℝ)+1)) ≤ ∑ z ∈ atoms, w z*(∑ g ∈ net, ((group z g).card : ℝ)) ∧
      (∀ z ∈ atoms, ((net.filter (fun g => (group z g).Nonempty)).card : ℝ) ≤
        2*(radius J j)^(-beta)) ∧
      ∀ a : Fin M, ((net.filter (fun g => ∃ z ∈ atoms, a ∈ group z g)).card : ℝ) ≤
        packingConstant k*(3:ℝ)^k := by
  classical
  obtain ⟨J,j,pieces,hdepth,hdτ,hτ1,hdis,hgood,hmass,hnumber⟩ :=
    common_scale_pieces F atoms w hw row hrow hδ hδ1 hb
  obtain ⟨net,_,hcover,hnetcount⟩ := bounded_angular_cap_cover F (radius_pos J j)
  obtain ⟨fallback,hfallback,_⟩ := hcover (⟨0,hM⟩ : Fin M)
  have hex (z : α) (p : Fin (J+1) × Finset (Fin M)) :
      ∃ g ∈ net, z ∈ atoms → p ∈ pieces z → ∀ a ∈ p.2,
        projectiveDistance (F.tube a).direction (F.tube g).direction ≤ 3*radius J j := by
    by_cases hz : z ∈ atoms
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
  have hgsub (z : α) (hz : z ∈ atoms) (g : Fin M) : group z g ⊆ row z := by
    intro a ha
    obtain ⟨p,hp,_,hpa⟩ := (mem_regroup _ _ _ _ _).mp ha
    exact (hgood z hz p hp).2.2.1 hpa
  have hgcap (z : α) (hz : z ∈ atoms) (g : Fin M) : ∀ a ∈ group z g,
      projectiveDistance (F.tube a).direction (F.tube g).direction ≤ 3*radius J j := by
    intro a ha
    obtain ⟨p,hp,hpg,hpa⟩ := (mem_regroup _ _ _ _ _).mp ha
    simpa only [hpg] using hcontain z p hz hp a hpa
  have hgdis (z : α) (hz : z ∈ atoms) :
      Pairwise (fun g h => Disjoint (group z g) (group z h)) :=
    fun _ _ hne => regroup_disjoint (pieces z) Prod.snd (assign z) (hdis z hz) hne
  have hgbroad (z : α) (hz : z ∈ atoms) (g : Fin M) :
      Broad F (group z g) δ beta (radius J j) ((4:ℝ)^beta) := by
    apply regroup_broad F (pieces z) Prod.snd (assign z) (hdis z hz)
    intro p hp
    have h := (hgood z hz p hp).2.2.2.2.2
    simpa only [(hgood z hz p hp).1,Broad] using h
  have hgsum (z : α) (hz : z ∈ atoms) :
      (∑ g ∈ net, ((group z g).card : ℝ)) = ∑ p ∈ pieces z, (p.2.card : ℝ) := by
    have h := regroup_sum_card (pieces z) Prod.snd (assign z) net (fun p _ => hassign z p) (hdis z hz)
    exact_mod_cast h
  refine ⟨J,j,net,group,hdepth,hdτ,hτ1,⟨fallback,hfallback⟩,
    fun z hz g _ => hgsub z hz g,fun z hz g _ => hgcap z hz g,hgdis,
    fun z hz g _ => hgbroad z hz g,?_,?_,?_⟩
  · exact hmass.trans_eq (Finset.sum_congr rfl (fun z hz => congrArg (fun t => w z*t) (hgsum z hz).symm))
  · intro z hz
    have h := regroup_occupied_count (pieces z) Prod.snd (assign z) net
    exact (by exact_mod_cast h : ((net.filter (fun g => (group z g).Nonempty)).card : ℝ) ≤ (pieces z).card).trans
      (hnumber z hz)
  · intro a
    have hs : net.filter (fun g => ∃ z ∈ atoms, a ∈ group z g) ⊆
        net.filter (fun g => projectiveDistance (F.tube g).direction (F.tube a).direction ≤ 3*radius J j) := by
      intro g hg
      obtain ⟨z,hz,ha⟩ := (Finset.mem_filter.mp hg).2
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,
        by simpa only [projective_symm] using hgcap z hz g a ha⟩
    have hc : ((net.filter (fun g => ∃ z ∈ atoms, a ∈ group z g)).card : ℝ) ≤
        (net.filter (fun g => projectiveDistance (F.tube g).direction (F.tube a).direction ≤ 3*radius J j)).card := by
      exact_mod_cast Finset.card_le_card hs
    exact hc.trans (hnetcount (F.tube a).direction)


/-- Simultaneous actual tube assignment and restoration for weighted incidence
atoms. Broadness and overlap are pointwise cardinality assertions; retention
uses exactly the original atom weights. -/
theorem actual_angular_assignment {α : Type*} {k M : ℕ}
    (F : TubeFamily (k+1) M) (hM : 0 < M)
    (atoms : Finset α) (w : α → ℝ) (hw : ∀ z ∈ atoms, 0 ≤ w z)
    (row : α → Finset (Fin M)) (hrow : ∀ z ∈ atoms, (row z).Nonempty)
    {δ beta : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) :
    let C := packingConstant k*(3:ℝ)^k
    ∃ J : ℕ, ∃ j : Fin (J+1), ∃ net : Finset (Fin M),
      ∃ assign : Fin M → Fin M, ∃ kept : α → Fin M → Finset (Fin M),
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧ δ ≤ radius J j ∧ radius J j ≤ 1 ∧
      (∀ i, assign i ∈ net) ∧
      (∀ z ∈ atoms, ∀ g, kept z g ⊆ row z) ∧
      (∀ z g i, i ∈ kept z g → assign i = g) ∧
      (∀ z ∈ atoms, ∀ g ∈ net, ∀ i ∈ kept z g,
        projectiveDistance (F.tube i).direction (F.tube g).direction ≤ 3*radius J j) ∧
      (3/(4*C))*((∑ z ∈ atoms, w z*((row z).card:ℝ))/(2*((J:ℝ)+1))) ≤
        ∑ z ∈ atoms, w z*(∑ g ∈ net, ((kept z g).card:ℝ)) ∧
      (∀ z ∈ atoms, ∀ g ∈ net, Broad F (kept z g)
        δ beta (radius J j) (((4:ℝ)^beta)*(4*C))) ∧
      ∀ z ∈ atoms, ((net.filter (fun g => (kept z g).Nonempty)).card:ℝ) ≤
        2*(radius J j)^(-beta) := by
  let C := packingConstant k*(3:ℝ)^k
  have hC : 0 < C := by
    have hp := packingConstant_ge_one k
    dsimp [C]
    positivity
  obtain ⟨J,j,net,group,hdepth,hdτ,hτ1,hnet,hsub,hcap,_hdis,hbroad,hmass,hover,hcount⟩ :=
    actual_angular_groups F hM atoms w hw row hrow hδ hδ1 hb
  obtain ⟨assign,hassign,hretain,hunique⟩ :=
    WeightedAngularAssignment.assign_and_restore atoms w hw net hnet group hC hcount
  let kept := AngularAssignment.restored group assign C
  refine ⟨J,j,net,assign,kept,hdepth,hdτ,hτ1,hassign,?_,?_,?_,?_,?_,?_⟩
  · intro z hz g i hi
    have hraw := hunique z g i hi
    have hg : g ∈ net := by rw [← hraw.2]; exact hassign i
    exact hsub z hz g hg hraw.1
  · intro z g i hi
    exact (hunique z g i hi).2
  · intro z hz g hg i hi
    exact hcap z hz g hg i (hunique z g i hi).1
  · have hh := mul_le_mul_of_nonneg_left hmass (by positivity : 0 ≤ 3/(4*C))
    apply hh.trans
    simpa only [Finset.mul_sum] using hretain
  · intro z hz g hg
    dsimp [kept]
    unfold AngularAssignment.restored
    split_ifs with hgood
    · exact broad_proportional_subset F (Finset.filter_subset _ _) hδ.le (radius_pos J j)
        (Real.rpow_nonneg (by norm_num) beta) hgood (hbroad z hz g hg)
    · intro center r hr
      simp [cap]
  · intro z hz
    have hs : net.filter (fun g => (kept z g).Nonempty) ⊆
        net.filter (fun g => (group z g).Nonempty) := by
      intro g hg
      obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hg).2
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hg).1,⟨i,(hunique z g i hi).1⟩⟩
    have hc : ((net.filter (fun g => (kept z g).Nonempty)).card:ℝ) ≤
        ((net.filter (fun g => (group z g).Nonempty)).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hs
    exact hc.trans (hover z hz)

end
end KakeyaFormal.WeightedAngularSelection
