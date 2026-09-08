import CapCover
import ScaleChoice

/-! Actual finite angular selection on indexed unit directions. Maxima are taken
on explicit finite dyadic caps centered at existing directions. -/
namespace KakeyaFormal.AngularDecomposition
open KakeyaFormal.Localization

noncomputable section

def cap {k M : ℕ} (F : TubeFamily k M) (points : Finset (Fin M))
    (center : Space k) (r : ℝ) : Finset (Fin M) := by
  classical
  exact points.filter (fun i => projectiveDistance (F.tube i).direction center ≤ r)

theorem cap_subset {k M : ℕ} (F : TubeFamily k M) (points : Finset (Fin M))
    (center : Space k) (r : ℝ) : cap F points center r ⊆ points := Finset.filter_subset _ _

theorem unit_direction_distance_le_two {k M : ℕ} (F : TubeFamily k M) (i j : Fin M) :
    projectiveDistance (F.tube i).direction (F.tube j).direction ≤ 2 := by
  exact (ProjectiveGeometry.projective_le_chord _ _).trans
    ((norm_sub_le _ _).trans_eq (by rw [(F.tube i).unit_direction,(F.tube j).unit_direction]; norm_num))

theorem top_cap {k M : ℕ} (F : TubeFamily k M) (points : Finset (Fin M)) (i : Fin M) :
    cap F points (F.tube i).direction 2 = points := by
  classical
  exact Finset.filter_eq_self.mpr (fun j _ => unit_direction_distance_le_two F j i)

/-- A dyadic scale at least r is at most4r even when the real bottom scale delta
is between two dyadic values. -/
theorem round_real_radius {J : ℕ} {δ r : ℝ} (hδ : 0 < δ)
    (hbottom : radius J 0 ≤ 2*δ) (hrδ : δ ≤ r) (hr1 : r ≤ 1) :
    ∃ j ≤ J, r ≤ radius J j ∧ radius J j ≤ 4*r := by
  let R := max r (radius J 0)
  have hR1 : R ≤ 1 := max_le hr1 (by simpa only [radius_top] using radius_mono J (Nat.zero_le J))
  obtain ⟨j,hj,hRj,hjR⟩ := dyadic_round (le_max_right r (radius J 0)) hR1
  have hR2 : R ≤ 2*r := max_le (by linarith) (by linarith)
  exact ⟨j,hj,(le_max_left r (radius J 0)).trans hRj,by linarith⟩

/-- Division-free consequence of maximizing count/scale^beta. -/
theorem score_comparison {a b s t beta : ℝ} (hs : 0 < s) (ht : 0 < t)
    (hscore : a/s^beta ≤ b/t^beta) : a ≤ (s/t)^beta*b := by
  have hsB : 0 < s^beta := Real.rpow_pos_of_pos hs beta
  have htB : 0 < t^beta := Real.rpow_pos_of_pos ht beta
  have hm := (div_le_iff₀ hsB).mp hscore
  rw [Real.div_rpow hs.le ht.le]
  simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hm

/-- A maximizing cap of the actual finite family is internally broad at every
real radius, and contains at least tau^beta of the remaining population. Its
containing cap has radius2tau, with tau an actual dyadic scale. -/
theorem maximizing_broad_subset {k M : ℕ} (F : TubeFamily k M)
    (points : Finset (Fin M)) (hne : points.Nonempty) {δ beta : ℝ}
    (hδ : 0 < δ) (hb : 0 ≤ beta) (J : ℕ)
    (hbottom : radius J 0 ≤ 2*δ) :
    ∃ j ≤ J, ∃ i ∈ points, ∃ W ⊆ points,
      W.Nonempty ∧ W = cap F points (F.tube i).direction (2*radius J j) ∧
      (radius J j)^beta*(points.card : ℝ) ≤ (W.card : ℝ) ∧
      ∀ center : Space k, ∀ r : ℝ, δ ≤ r →
        ((cap F W center r).card : ℝ) ≤
          (4:ℝ)^beta*(r/radius J j)^beta*(W.card : ℝ) := by
  classical
  let candidates := points ×ˢ (Finset.univ : Finset (Fin (J+1)))
  let score := fun p : Fin M × Fin (J+1) =>
    ((cap F points (F.tube p.1).direction (2*radius J p.2)).card : ℝ)/(radius J p.2)^beta
  have hcand : candidates.Nonempty := hne.product Finset.univ_nonempty
  obtain ⟨choice,hchoice,hmax⟩ := Finset.exists_max_image candidates score hcand
  have hic : choice.1 ∈ points := (Finset.mem_product.mp hchoice).1
  have hj : choice.2.val ≤ J := by omega
  let tau := radius J choice.2
  let W := cap F points (F.tube choice.1).direction (2*tau)
  have ht : 0 < tau := radius_pos J choice.2
  have hcomparison (i : Fin M) (hi : i ∈ points) (j : ℕ) (hj : j ≤ J) :
      ((cap F points (F.tube i).direction (2*radius J j)).card : ℝ) ≤
        (radius J j/tau)^beta*(W.card : ℝ) := by
    have hs := hmax (i,⟨j,by omega⟩) (Finset.mem_product.mpr ⟨hi,Finset.mem_univ _⟩)
    exact score_comparison (radius_pos J j) ht hs
  have hpopulation : tau^beta*(points.card : ℝ) ≤ (W.card : ℝ) := by
    have hh := hcomparison choice.1 hic J le_rfl
    rw [radius_top] at hh
    norm_num only [mul_one] at hh
    rw [top_cap] at hh
    have hpower := Real.rpow_pos_of_pos ht beta
    rw [Real.div_rpow zero_le_one ht.le,Real.one_rpow] at hh
    have hmul := mul_le_mul_of_nonneg_left hh hpower.le
    simpa only [mul_assoc,one_div,mul_inv_cancel_left₀ hpower.ne'] using hmul
  have hWne : W.Nonempty := by
    have hp : 0 < (points.card : ℝ) := by exact_mod_cast hne.card_pos
    have hpos : 0 < (W.card : ℝ) := (mul_pos (Real.rpow_pos_of_pos ht beta) hp).trans_le hpopulation
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  refine ⟨choice.2,hj,choice.1,hic,W,cap_subset F points _ _,hWne,rfl,hpopulation,?_⟩
  intro center r hrδ
  have hr : 0 < r := hδ.trans_le hrδ
  let Q := cap F W center r
  by_cases hQne : Q.Nonempty
  · obtain ⟨i,hi⟩ := hQne
    have hiW : i ∈ W := (Finset.mem_filter.mp hi).1
    have hiP : i ∈ points := cap_subset F points _ _ hiW
    have hiC : projectiveDistance (F.tube i).direction center ≤ r := (Finset.mem_filter.mp hi).2
    have hbound : ∃ j ≤ J, (Q.card : ℝ) ≤
        ((cap F points (F.tube i).direction (2*radius J j)).card : ℝ) ∧ radius J j ≤ 4*r := by
      by_cases hr1 : r ≤ 1
      · obtain ⟨j,hj,hrj,hjr⟩ := round_real_radius hδ hbottom hrδ hr1
        refine ⟨j,hj,?_,hjr⟩
        have hs : Q ⊆ cap F points (F.tube i).direction (2*radius J j) := by
          intro a ha
          have haW : a ∈ W := (Finset.mem_filter.mp ha).1
          have haC : projectiveDistance (F.tube a).direction center ≤ r := (Finset.mem_filter.mp ha).2
          apply Finset.mem_filter.mpr
          refine ⟨cap_subset F points _ _ haW,?_⟩
          have ht := ProjectiveGeometry.projective_triangle (F.tube a).direction center (F.tube i).direction
          rw [ProjectiveGeometry.projective_symm center] at ht
          linarith
        exact_mod_cast Finset.card_le_card hs
      · refine ⟨J,le_rfl,?_,?_⟩
        · rw [radius_top]
          norm_num only [mul_one]
          rw [top_cap]
          exact_mod_cast Finset.card_le_card ((cap_subset F W center r).trans (cap_subset F points _ _))
        · rw [radius_top]; linarith
    obtain ⟨j,hj,hcount,hjr⟩ := hbound
    have hpow : (radius J j/tau)^beta ≤ (4*r/tau)^beta :=
      Real.rpow_le_rpow (div_nonneg (radius_pos J j).le ht.le)
        (div_le_div_of_nonneg_right hjr ht.le) hb
    have hh := hcount.trans ((hcomparison i hiP j hj).trans
      (mul_le_mul_of_nonneg_right hpow (by positivity)))
    have hid : (4*r/tau)^beta = (4:ℝ)^beta*(r/tau)^beta := by
      rw [mul_div_assoc, Real.mul_rpow (by norm_num) (div_nonneg hr.le ht.le)]
    simpa only [Q,hid] using hh
  · have hempty : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQne
    change (Q.card : ℝ) ≤ _
    rw [hempty,Finset.card_empty,Nat.cast_zero]
    positivity

/-- Finite saturation of disjoint good pieces. If a good nonempty piece exists
in every remainder larger than half the original, an actual disjoint collection
covers at least half. The collection is obtained by finite maximization. -/
theorem finite_disjoint_saturation {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (original : Finset α) (candidates : Finset ι) (support : ι → Finset α)
    (hsub : ∀ i ∈ candidates, support i ⊆ original)
    (hstep : ∀ remaining ⊆ original, (original.card : ℝ)/2 < (remaining.card : ℝ) →
      ∃ i ∈ candidates, (support i).Nonempty ∧ support i ⊆ remaining) :
    ∃ pieces : Finset ι, pieces ⊆ candidates ∧
      (↑pieces : Set ι).PairwiseDisjoint support ∧
      (original.card : ℝ)/2 ≤ ∑ i ∈ pieces, ((support i).card : ℝ) := by
  classical
  let collections : Finset (Finset ι) := candidates.powerset.filter
    (fun (pieces : Finset ι) => (↑pieces : Set ι).PairwiseDisjoint support)
  have hne : collections.Nonempty := ⟨∅,by simp [collections]⟩
  obtain ⟨pieces,hpieces,hmax⟩ := Finset.exists_max_image collections
    (fun (pieces : Finset ι) => ∑ i ∈ pieces, (support i).card) hne
  have hpc : pieces ⊆ candidates := Finset.mem_powerset.mp (Finset.mem_filter.mp hpieces).1
  have hpd : (↑pieces : Set ι).PairwiseDisjoint support := (Finset.mem_filter.mp hpieces).2
  refine ⟨pieces,hpc,hpd,?_⟩
  by_contra hsmall
  let covered := pieces.biUnion support
  have hcover : covered ⊆ original := by
    intro x hx
    obtain ⟨i,hi,hx⟩ := Finset.mem_biUnion.mp hx
    exact hsub i (hpc hi) hx
  let remaining := original \ covered
  have hremaining : remaining ⊆ original := Finset.sdiff_subset
  have hcard : (remaining.card : ℝ) + ∑ i ∈ pieces, ((support i).card : ℝ) = original.card := by
    have heq := Finset.card_sdiff_add_card_eq_card hcover
    rw [Finset.card_biUnion hpd] at heq
    exact_mod_cast heq
  have hlarge : (original.card : ℝ)/2 < (remaining.card : ℝ) := by linarith
  obtain ⟨i,hic,hiNe,hiSub⟩ := hstep remaining hremaining hlarge
  have hdis (j : ι) (hj : j ∈ pieces) : Disjoint (support i) (support j) := by
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    have hxnot := (Finset.mem_sdiff.mp (hiSub hxi)).2
    exact hxnot (Finset.mem_biUnion.mpr ⟨j,hj,hxj⟩)
  have hinot : i ∉ pieces := by
    intro hi
    obtain ⟨x,hx⟩ := hiNe
    exact Finset.disjoint_left.mp (hdis i hi) hx hx
  have hnew : insert i pieces ∈ collections := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.insert_subset hic hpc),?_⟩
    simpa only [Finset.coe_insert] using hpd.insert_of_notMem hinot hdis
  have hmore := hmax (insert i pieces) hnew
  rw [Finset.sum_insert hinot] at hmore
  have hiPos := hiNe.card_pos
  omega

/-- Precise good-piece property used in the finite angular saturation. -/
def GoodPiece {k M : ℕ} (F : TubeFamily k M) (original : Finset (Fin M))
    (δ beta : ℝ) (J : ℕ) (p : Fin (J+1) × Finset (Fin M)) : Prop :=
  p.2.Nonempty ∧ p.2 ⊆ original ∧
    (∃ i ∈ original, ∀ a ∈ p.2,
      projectiveDistance (F.tube a).direction (F.tube i).direction ≤ 2*radius J p.1) ∧
    (radius J p.1)^beta*(original.card : ℝ)/2 ≤ (p.2.card : ℝ) ∧
    ∀ center : Space k, ∀ r : ℝ, δ ≤ r →
      ((cap F p.2 center r).card : ℝ) ≤
        (4:ℝ)^beta*(r/radius J p.1)^beta*(p.2.card : ℝ)

/-- Actual finite angular decomposition before scale pigeonholing: disjoint
internally broad pieces retain at least half the original indexed directions,
and each piece has a scale-dependent proportion of the original population. -/
theorem disjoint_broad_decomposition {k M : ℕ} (F : TubeFamily k M)
    (original : Finset (Fin M)) {δ beta : ℝ} (hδ : 0 < δ) (hb : 0 ≤ beta)
    (J : ℕ) (hbottom : radius J 0 ≤ 2*δ) :
    ∃ pieces : Finset (Fin (J+1) × Finset (Fin M)),
      (↑pieces : Set (Fin (J+1) × Finset (Fin M))).PairwiseDisjoint Prod.snd ∧
      (∀ p ∈ pieces, GoodPiece F original δ beta J p) ∧
      (original.card : ℝ)/2 ≤ ∑ p ∈ pieces, (p.2.card : ℝ) := by
  classical
  let candidates := ((Finset.univ : Finset (Fin (J+1))) ×ˢ original.powerset).filter
    (GoodPiece F original δ beta J)
  have hsub : ∀ p ∈ candidates, p.2 ⊆ original := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.2.1
  have hstep : ∀ remaining ⊆ original, (original.card : ℝ)/2 < (remaining.card : ℝ) →
      ∃ p ∈ candidates, p.2.Nonempty ∧ p.2 ⊆ remaining := by
    intro remaining hrsub hrlarge
    have hrpos : 0 < (remaining.card : ℝ) := by
      have ho : (0:ℝ) ≤ original.card := by positivity
      linarith
    have hrne : remaining.Nonempty := Finset.card_pos.mp (by exact_mod_cast hrpos)
    obtain ⟨j,hj,i,hi,W,hW,hWne,hWeq,hpop,hbroad⟩ :=
      maximizing_broad_subset F remaining hrne hδ hb J hbottom
    let p : Fin (J+1) × Finset (Fin M) := (⟨j,by omega⟩,W)
    have hgood : GoodPiece F original δ beta J p := by
      refine ⟨hWne,hW.trans hrsub,⟨i,hrsub hi,?_⟩,?_,hbroad⟩
      · intro a ha
        change a ∈ W at ha
        rw [hWeq] at ha
        exact (Finset.mem_filter.mp ha).2
      · have hmul := mul_le_mul_of_nonneg_left hrlarge.le
          (Real.rpow_nonneg (radius_pos J j).le beta)
        change (radius J j)^beta*(original.card : ℝ)/2 ≤ _
        calc
          _ ≤ (radius J j)^beta*(remaining.card : ℝ) := by simpa only [mul_div_assoc] using hmul
          _ ≤ _ := hpop
    refine ⟨p,Finset.mem_filter.mpr ⟨?_,hgood⟩,hWne,hW⟩
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_powerset.mpr (hW.trans hrsub)⟩
  obtain ⟨pieces,hpc,hpd,hmass⟩ := finite_disjoint_saturation original candidates Prod.snd hsub hstep
  exact ⟨pieces,hpd,fun p hp => (Finset.mem_filter.mp (hpc hp)).2,hmass⟩

/-- A finite weighted pigeonhole step retains at least the average mass of a
color class. This counts piece population rather than merely counting pieces. -/
theorem weighted_color_pigeonhole {α β : Type*} [Fintype β] [Nonempty β] [DecidableEq β]
    (pieces : Finset α) (color : α → β) (weight : α → ℝ) :
    ∃ b : β, (∑ p ∈ pieces, weight p)/(Fintype.card β : ℝ) ≤
      ∑ p ∈ pieces with color p = b, weight p := by
  classical
  have hpos : 0 < (Fintype.card β : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : (∑ b : β, (∑ p ∈ pieces, weight p)/(Fintype.card β : ℝ)) ≤
      ∑ b : β, ∑ p ∈ pieces with color p = b, weight p := by
    rw [Finset.sum_fiberwise]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    exact le_of_eq (mul_div_cancel₀ _ hpos.ne')
  obtain ⟨b,_,hb⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨b,hb⟩

/-- At a common scale, the actual number of disjoint broad pieces is at most
2*tau^(-beta). No geometric disjointness of their containing caps is needed. -/
theorem common_scale_piece_count {k M J : ℕ} (F : TubeFamily k M)
    (original : Finset (Fin M)) (hne : original.Nonempty) {δ beta : ℝ}
    (pieces : Finset (Fin (J+1) × Finset (Fin M)))
    (hdis : (↑pieces : Set (Fin (J+1) × Finset (Fin M))).PairwiseDisjoint Prod.snd)
    (hgood : ∀ p ∈ pieces, GoodPiece F original δ beta J p)
    (j : Fin (J+1)) (hscale : ∀ p ∈ pieces, p.1 = j) :
    (pieces.card : ℝ) ≤ 2*(radius J j)^(-beta) := by
  classical
  have ho : 0 < (original.card : ℝ) := by exact_mod_cast hne.card_pos
  have ht : 0 < (radius J j)^beta := Real.rpow_pos_of_pos (radius_pos J j) beta
  have hcover : pieces.biUnion Prod.snd ⊆ original := by
    intro a ha
    obtain ⟨p,hp,ha⟩ := Finset.mem_biUnion.mp ha
    exact (hgood p hp).2.1 ha
  have htotal : ∑ p ∈ pieces, (p.2.card : ℝ) ≤ original.card := by
    have hcard := Finset.card_le_card hcover
    rw [Finset.card_biUnion hdis] at hcard
    exact_mod_cast hcard
  have hlower : (pieces.card : ℝ)*((radius J j)^beta*(original.card : ℝ)/2) ≤
      ∑ p ∈ pieces, (p.2.card : ℝ) := by
    have h : (∑ _p ∈ pieces, (radius J j)^beta*(original.card : ℝ)/2) ≤
        ∑ p ∈ pieces, (p.2.card : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      simpa only [hscale p hp] using (hgood p hp).2.2.2.1
    simpa only [Finset.sum_const,nsmul_eq_mul] using h
  have hc : (pieces.card : ℝ)*(radius J j)^beta ≤ 2 := by
    nlinarith [hlower.trans htotal]
  rw [Real.rpow_neg (radius_pos J j).le]
  have := (le_div_iff₀ ht).mpr hc
  simpa only [div_eq_mul_inv] using this

/-- Pointwise angular decomposition at one actual common scale. It retains an
explicit logarithmic fraction, consists of disjoint original index sets, each
piece is internally broad, and the number of pieces is O(tau^(-beta)). -/
theorem common_scale_broad_decomposition {k M : ℕ} (F : TubeFamily k M)
    (original : Finset (Fin M)) (hne : original.Nonempty) {δ beta : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) :
    ∃ J : ℕ, ∃ j : Fin (J+1), ∃ pieces : Finset (Fin (J+1) × Finset (Fin M)),
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      δ ≤ radius J j ∧ radius J j ≤ 1 ∧
      (↑pieces : Set (Fin (J+1) × Finset (Fin M))).PairwiseDisjoint Prod.snd ∧
      (∀ p ∈ pieces, p.1 = j ∧ GoodPiece F original δ beta J p) ∧
      (original.card : ℝ)/(2*((J:ℝ)+1)) ≤ ∑ p ∈ pieces, (p.2.card : ℝ) ∧
      (pieces.card : ℝ) ≤ 2*(radius J j)^(-beta) := by
  classical
  obtain ⟨J,hbottom,hbottom2,hdepth⟩ := ScaleChoice.dyadic_depth hδ hδ1
  obtain ⟨allpieces,hdis,hgood,hmass⟩ := disjoint_broad_decomposition F original hδ hb J hbottom2.le
  obtain ⟨j,hjmass⟩ := weighted_color_pigeonhole allpieces Prod.fst
    (fun p => (p.2.card : ℝ))
  let pieces := allpieces.filter (fun p => p.1 = j)
  have hsub : pieces ⊆ allpieces := Finset.filter_subset _ _
  have hpdis : (↑pieces : Set (Fin (J+1) × Finset (Fin M))).PairwiseDisjoint Prod.snd := by
    intro p hp q hq hne
    exact hdis (hsub hp) (hsub hq) hne
  have hpgood : ∀ p ∈ pieces, GoodPiece F original δ beta J p := fun p hp => hgood p (hsub hp)
  have hpscale : ∀ p ∈ pieces, p.1 = j := fun p hp => (Finset.mem_filter.mp hp).2
  have hmass' : (original.card : ℝ)/(2*((J:ℝ)+1)) ≤ ∑ p ∈ pieces, (p.2.card : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hmass (by positivity : (0:ℝ) ≤ J+1)
    have heq : (original.card : ℝ)/(2*((J:ℝ)+1)) = ((original.card : ℝ)/2)/((J:ℝ)+1) := by rw [div_div]
    rw [heq]
    exact hdiv.trans (by simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one] using hjmass)
  refine ⟨J,j,pieces,hdepth,hbottom.trans (radius_mono J (Nat.zero_le j)),?_,hpdis,
    fun p hp => ⟨hpscale p hp,hpgood p hp⟩,hmass',?_⟩
  · simpa only [radius_top] using radius_mono J (show j.val ≤ J by omega)
  · exact common_scale_piece_count F original hne pieces hpdis hpgood j hpscale

/-- Broadness for the actual projective cap counts of an indexed direction set. -/
def Broad {k M : ℕ} (F : TubeFamily k M) (points : Finset (Fin M))
    (δ beta tau K : ℝ) : Prop :=
  ∀ center : Space k, ∀ r : ℝ, δ ≤ r →
    ((cap F points center r).card : ℝ) ≤ K*(r/tau)^beta*(points.card : ℝ)

/-- Restricting a finite union to a cap commutes with taking its finite pieces. -/
theorem cap_biUnion {k M : ℕ} {ι : Type*} (F : TubeFamily k M)
    (pieces : Finset ι) (support : ι → Finset (Fin M)) (center : Space k) (r : ℝ) :
    cap F (pieces.biUnion support) center r = pieces.biUnion (fun p => cap F (support p) center r) := by
  classical
  ext i
  simp only [cap,Finset.mem_filter,Finset.mem_biUnion]
  aesop

/-- Disjoint broad subsets at one scale remain broad when united. This is the
actual cap-count version of the summation used after angular cap assignment. -/
theorem broad_biUnion {k M : ℕ} {ι : Type*} (F : TubeFamily k M)
    (pieces : Finset ι) (support : ι → Finset (Fin M))
    (hdis : (↑pieces : Set ι).PairwiseDisjoint support) {δ beta tau K : ℝ}
    (hbroad : ∀ p ∈ pieces, Broad F (support p) δ beta tau K) :
    Broad F (pieces.biUnion support) δ beta tau K := by
  classical
  intro center r hr
  have hcapdis : (↑pieces : Set ι).PairwiseDisjoint (fun p => cap F (support p) center r) := by
    intro p hp q hq hpq
    exact (hdis hp hq hpq).mono (cap_subset F _ _ _) (cap_subset F _ _ _)
  have hsum := Finset.sum_le_sum (s := pieces) (fun p hp => hbroad p hp center r hr)
  rw [cap_biUnion,Finset.card_biUnion hcapdis,Finset.card_biUnion hdis]
  push_cast
  simpa only [Finset.mul_sum] using hsum

/-- A proportional subset preserves actual broadness with the reciprocal
retention loss in its error constant. -/
theorem broad_proportional_subset {k M : ℕ} (F : TubeFamily k M)
    {small large : Finset (Fin M)} (hsub : small ⊆ large)
    {δ beta tau K D : ℝ} (hδ : 0 ≤ δ) (htau : 0 < tau) (hK : 0 ≤ K)
    (hpop : (large.card : ℝ) ≤ D*(small.card : ℝ))
    (hbroad : Broad F large δ beta tau K) : Broad F small δ beta tau (K*D) := by
  classical
  intro center r hr
  have hcap : cap F small center r ⊆ cap F large center r := Finset.filter_subset_filter _ hsub
  have hcount : ((cap F small center r).card : ℝ) ≤ (cap F large center r).card := by
    exact_mod_cast Finset.card_le_card hcap
  have hcoef : 0 ≤ K*(r/tau)^beta :=
    mul_nonneg hK (Real.rpow_nonneg (div_nonneg (hδ.trans hr) htau.le) beta)
  have hm := mul_le_mul_of_nonneg_left hpop hcoef
  exact hcount.trans ((hbroad center r hr).trans (by convert hm using 1; ring))

end
end KakeyaFormal.AngularDecomposition
