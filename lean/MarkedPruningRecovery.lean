import DensityBroadnessRecovery
import MarkedSubsetSamples

/-! Recovery after arbitrary full-shading deletion, with original marks kept
separate throughout. Density selection removes whole tubes only; the final
cell filter removes marks only, never further full-shading cells. -/
namespace KakeyaFormal.MarkedPruningRecovery
open Finset DensityBroadnessRecovery TransverseAngles
open scoped BigOperators
noncomputable section
open Classical

variable {k M : ℕ}

def goodTubes (Y O : Fin M → Finset (Cell k)) : Finset (Fin M) :=
  univ.filter (fun i => (Y i).card ≤ 2*(O i).card)

def currentMarks (marks O : Fin M → Finset (Cell k)) (i : Fin M) : Finset (Cell k) :=
  marks i ∩ O i

def markedMass (marks : Fin M → Finset (Cell k)) (T : Finset (Fin M)) : ℝ :=
  ∑ i ∈ T, ((marks i).card : ℝ)

def deletionMass (Y O : Fin M → Finset (Cell k)) : ℝ :=
  ∑ i, ((Y i \ O i).card : ℝ)

/-- A bad tube's original full shading is at most twice its actual deleted
shading. Good tubes keep all their surviving full cells. -/
theorem pointwise_full_loss (Y O : Fin M → Finset (Cell k))
    (hsub : ∀ i, O i ⊆ Y i) (i : Fin M) :
    ((Y i).card : ℝ) ≤
      (if i ∈ goodTubes Y O then ((O i).card : ℝ) else 0)+2*((Y i \ O i).card : ℝ) := by
  have hpartition := card_sdiff_add_card_eq_card (hsub i)
  by_cases hi : i ∈ goodTubes Y O
  · rw [if_pos hi]
    have hp : ((Y i \ O i).card : ℝ)+((O i).card : ℝ)=((Y i).card : ℝ) := by exact_mod_cast hpartition
    linarith [Nat.cast_nonneg (α := ℝ) (Y i \ O i).card]
  · rw [if_neg hi]
    have hbad : ¬(Y i).card ≤ 2*(O i).card := by simpa only [goodTubes,mem_filter,mem_univ,true_and] using hi
    have hn : (Y i).card ≤ 2*(Y i \ O i).card := by omega
    simpa only [zero_add] using (show ((Y i).card : ℝ) ≤ 2*((Y i \ O i).card : ℝ) by exact_mod_cast hn)

/-- Marks lost through full-cell deletion and whole bad-tube removal have
actual total mass at most twice the deleted full incidence mass. -/
theorem good_marked_mass (Y O marks : Fin M → Finset (Cell k))
    (hsub : ∀ i, O i ⊆ Y i) (hmarks : ∀ i, marks i ⊆ Y i) :
    markedMass marks univ-2*deletionMass Y O ≤
      markedMass (currentMarks marks O) (goodTubes Y O) := by
  have hpoint (i : Fin M) : ((marks i).card : ℝ) ≤
      (if i ∈ goodTubes Y O then ((currentMarks marks O i).card : ℝ) else 0)+
        2*((Y i \ O i).card : ℝ) := by
    by_cases hi : i ∈ goodTubes Y O
    · rw [if_pos hi]
      have hs : marks i \ O i ⊆ Y i \ O i := by
        intro z hz
        exact mem_sdiff.mpr ⟨hmarks i (mem_sdiff.mp hz).1,(mem_sdiff.mp hz).2⟩
      have hp := card_sdiff_add_card_inter (marks i) (O i)
      have hp' : ((marks i \ O i).card : ℝ)+((marks i ∩ O i).card : ℝ)=((marks i).card : ℝ) := by exact_mod_cast hp
      have hc : ((marks i \ O i).card : ℝ) ≤ ((Y i \ O i).card : ℝ) := by exact_mod_cast card_le_card hs
      dsimp [currentMarks]
      linarith [Nat.cast_nonneg (α := ℝ) (Y i \ O i).card]
    · rw [if_neg hi]
      have hm : ((marks i).card : ℝ) ≤ ((Y i).card : ℝ) := by exact_mod_cast card_le_card (hmarks i)
      have hf := pointwise_full_loss Y O hsub i
      rw [if_neg hi] at hf
      exact hm.trans hf
  have hh := sum_le_sum (s := univ) (fun i _ => hpoint i)
  rw [sum_add_distrib,← mul_sum,← sum_filter] at hh
  have hfilter : (univ : Finset (Fin M)).filter (fun i => i ∈ goodTubes Y O)=goodTubes Y O := by ext i; simp
  rw [hfilter] at hh
  change markedMass marks univ ≤ markedMass (currentMarks marks O) (goodTubes Y O)+2*deletionMass Y O at hh
  linarith

/-- Whole-tube selection into one of the two density intervals preserves at
least half of the surviving marks. It makes no further full-cell deletions. -/
theorem two_density_bins (F : TubeFamily k M) (O marks : Fin M → Finset (Cell k))
    {δ lam : ℝ} (_hδ : 0 < δ) (hcomp : F.Comparable δ lam)
    (hsub : ∀ i, O i ⊆ F.shade i) :
    ∃ lam' : ℝ, (lam'=lam/2 ∨ lam'=lam) ∧ ∃ T : Finset (Fin M), T ⊆ goodTubes F.shade O ∧
      markedMass (currentMarks marks O) (goodTubes F.shade O)/2 ≤ markedMass (currentMarks marks O) T ∧
      (∀ i ∈ T, lam'/δ ≤ ((O i).card : ℝ) ∧ ((O i).card : ℝ) ≤ 2*lam'/δ) := by
  let G := goodTubes F.shade O
  let low := G.filter (fun i => ((O i).card : ℝ) ≤ lam/δ)
  let high := G.filter (fun i => ¬((O i).card : ℝ) ≤ lam/δ)
  have hsplit : markedMass (currentMarks marks O) low+markedMass (currentMarks marks O) high=
      markedMass (currentMarks marks O) G := by
    exact sum_filter_add_sum_filter_not (s := G) (fun i => ((O i).card : ℝ) ≤ lam/δ)
      (fun i => ((currentMarks marks O i).card : ℝ))
  have hbounds (i) (hi : i ∈ G) : (lam/2)/δ ≤ ((O i).card : ℝ) ∧
      ((O i).card : ℝ) ≤ 2*lam/δ := by
    have hgood : ((F.shade i).card : ℝ) ≤ 2*((O i).card : ℝ) := by
      exact_mod_cast (mem_filter.mp hi).2
    have hlo := (hcomp i).1
    have hhi := (Nat.cast_le.mpr (card_le_card (hsub i))).trans (hcomp i).2
    refine ⟨?_,hhi⟩
    rw [show (lam/2)/δ=(lam/δ)/2 by ring]
    linarith
  by_cases hlow : markedMass (currentMarks marks O) high ≤ markedMass (currentMarks marks O) low
  · refine ⟨lam/2,Or.inl rfl,low,filter_subset _ _,by linarith,?_⟩
    intro i hi
    obtain ⟨hi,hsize⟩ := mem_filter.mp hi
    exact ⟨(hbounds i hi).1,by convert hsize using 1; ring⟩
  · refine ⟨lam,Or.inr rfl,high,filter_subset _ _,by linarith,?_⟩
    intro i hi
    obtain ⟨hi,hsize⟩ := mem_filter.mp hi
    exact ⟨(lt_of_not_ge hsize).le,(hbounds i hi).2⟩


def keptCells (marks O : Fin M → Finset (Cell k)) (T : Finset (Fin M)) : Finset (Cell k) :=
  (cells marks).filter (fun z => ((row marks univ z).card : ℝ) ≤
    4*((row (currentMarks marks O) T z).card : ℝ))

def retainedMarks (marks O : Fin M → Finset (Cell k)) (T : Finset (Fin M))
    (i : Fin M) : Finset (Cell k) := currentMarks marks O i ∩ keptCells marks O T

/-- The actual marked-cell filter removes at most one quarter of the original
marked incidence mass, regardless of the chosen density bin. -/
theorem cell_filter_mass (marks O : Fin M → Finset (Cell k)) (T : Finset (Fin M)) :
    markedMass (currentMarks marks O) T-markedMass marks univ/4 ≤
      ∑ z ∈ keptCells marks O T, ((row (currentMarks marks O) T z).card : ℝ) := by
  let U := cells marks
  let N := currentMarks marks O
  have hmarks (i : Fin M) : marks i ⊆ U := fun z hz => mem_biUnion.mpr ⟨i,mem_univ _,hz⟩
  have hcurrent (i : Fin M) : N i ⊆ U := fun z hz => hmarks i (mem_inter.mp hz).1
  have horiginal : (∑ z ∈ U, ((row marks univ z).card : ℝ))=markedMass marks univ := by
    dsimp [markedMass]
    exact_mod_cast incidence_sum marks univ U (fun i _ => hmarks i)
  have htotal : (∑ z ∈ U, ((row N T z).card : ℝ))=markedMass N T := by
    dsimp [markedMass]
    exact_mod_cast incidence_sum N T U (fun i _ => hcurrent i)
  have hbad : (∑ z ∈ U.filter (fun z => ¬((row marks univ z).card : ℝ) ≤ 4*((row N T z).card : ℝ)),
      ((row N T z).card : ℝ)) ≤ markedMass marks univ/4 := by
    calc
      _ ≤ ∑ z ∈ U.filter (fun z => ¬((row marks univ z).card : ℝ) ≤ 4*((row N T z).card : ℝ)),
          ((row marks univ z).card : ℝ)/4 := by
        apply sum_le_sum
        intro z hz
        have hh := lt_of_not_ge (mem_filter.mp hz).2
        linarith
      _ ≤ ∑ z ∈ U, ((row marks univ z).card : ℝ)/4 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ = _ := by rw [← sum_div,horiginal]
  have hsplit := sum_filter_add_sum_filter_not (s := U)
    (fun z => ((row marks univ z).card : ℝ) ≤ 4*((row N T z).card : ℝ))
    (fun z => ((row N T z).card : ℝ))
  rw [htotal] at hsplit
  change (∑ z ∈ keptCells marks O T, ((row N T z).card : ℝ))+_=markedMass N T at hsplit
  linarith

/-- The final marked-shading mass is exactly the marked row sum over the
kept cells. The full shadings are not intersected with this marked-cell filter. -/
theorem retained_marked_mass (marks O : Fin M → Finset (Cell k)) (T : Finset (Fin M)) :
    markedMass (retainedMarks marks O T) T =
      ∑ z ∈ keptCells marks O T, ((row (currentMarks marks O) T z).card : ℝ) := by
  have hh := incidence_sum (retainedMarks marks O T) T (keptCells marks O T)
    (fun i _ => inter_subset_right)
  have hrow (z) (hz : z ∈ keptCells marks O T) :
      row (retainedMarks marks O T) T z=row (currentMarks marks O) T z := by
    ext i
    simp only [row,retainedMarks,mem_filter,mem_inter,hz,and_true]
  have hh' : (∑ z ∈ keptCells marks O T, ((row (retainedMarks marks O T) T z).card : ℝ))=
      markedMass (retainedMarks marks O T) T := by
    dsimp [markedMass]
    exact_mod_cast hh
  rw [← hh']
  exact sum_congr rfl fun z hz => by rw [hrow z hz]

/-- Full deletion, whole-tube density selection, and actual cell marking
leave at least W/4-R marks; this implies the requested coarser W/4-2R bound. -/
theorem select_marked_density (F : TubeFamily k M) (O marks : Fin M → Finset (Cell k))
    {δ lam : ℝ} (hδ : 0 < δ) (hcomp : F.Comparable δ lam)
    (hsub : ∀ i, O i ⊆ F.shade i) (hmarks : ∀ i, marks i ⊆ F.shade i) :
    ∃ lam' : ℝ, (lam'=lam/2 ∨ lam'=lam) ∧ ∃ T : Finset (Fin M), T ⊆ goodTubes F.shade O ∧
      (∀ i ∈ T, lam'/δ ≤ ((O i).card : ℝ) ∧ ((O i).card : ℝ) ≤ 2*lam'/δ) ∧
      markedMass marks univ/4-deletionMass F.shade O ≤ markedMass (retainedMarks marks O T) T := by
  obtain ⟨lam',hlam',T,hT,hmass,hsize⟩ := two_density_bins F O marks hδ hcomp hsub
  have hgood := good_marked_mass F.shade O marks hsub hmarks
  have hfilter := cell_filter_mass marks O T
  rw [← retained_marked_mass] at hfilter
  exact ⟨lam',hlam',T,hT,hsize,by linarith⟩

/-- One-radius marked broadness transfers only to the actual retained marks.
The stronger two-fifths conclusion leaves room below one half. -/
theorem retained_broadness (F : TubeFamily k M) (O marks : Fin M → Finset (Cell k))
    (T : Finset (Fin M)) {theta : ℝ}
    (hbroad : ∀ z ∈ cells marks, ∀ v : Space k, ‖v‖=1 →
      (((row marks univ z).filter (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
        ((row marks univ z).card : ℝ)/10)
    {z : Cell k} (hz : z ∈ keptCells marks O T) (v : Space k) (hv : ‖v‖=1) :
    (((row (retainedMarks marks O T) T z).filter
      (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
      (2/5 : ℝ)*((row (retainedMarks marks O T) T z).card : ℝ) := by
  have hrow : row (retainedMarks marks O T) T z=row (currentMarks marks O) T z := by
    ext i
    simp only [row,retainedMarks,mem_filter,mem_inter,hz,and_true]
  rw [hrow]
  have hsub : row (currentMarks marks O) T z ⊆ row marks univ z := by
    intro i hi
    exact mem_filter.mpr ⟨mem_univ _,(mem_inter.mp (mem_filter.mp hi).2).1⟩
  have hc : (((row (currentMarks marks O) T z).filter
      (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
      (((row marks univ z).filter (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) := by
    exact_mod_cast card_le_card (filter_subset_filter _ hsub)
  have hm := (mem_filter.mp hz).2
  have hb := hbroad z (mem_filter.mp hz).1 v hv
  linarith


def selectedIndex (T : Finset (Fin M)) : Fin T.card → Fin M :=
  fun i => (T.equivFin.symm i).val

def selectedFamily (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    (T : Finset (Fin M)) : TubeFamily k T.card :=
  ⟨fun i => F.tube (selectedIndex T i),fun i => O (selectedIndex T i)⟩

def selectedMarks (marks O : Fin M → Finset (Cell k)) (T : Finset (Fin M))
    (i : Fin T.card) : Finset (Cell k) := retainedMarks marks O T (selectedIndex T i)

theorem selectedIndex_injective (T : Finset (Fin M)) : Function.Injective (selectedIndex T) :=
  Subtype.val_injective.comp T.equivFin.symm.injective

theorem selectedIndex_mem (T : Finset (Fin M)) (i : Fin T.card) : selectedIndex T i ∈ T :=
  (T.equivFin.symm i).property

/-- Injective reindexing preserves every selected tube and its full shading. -/
theorem reindex_mass (marks : Fin M → Finset (Cell k)) (T : Finset (Fin M)) :
    (∑ i, ((marks (selectedIndex T i)).card : ℝ))=markedMass marks T := by
  have hh := T.equivFin.symm.sum_comp (fun i : ↥T => ((marks i.val).card : ℝ))
  exact hh.trans (Finset.sum_subtype T (fun _ => Iff.rfl) (fun i => ((marks i).card : ℝ))).symm

theorem reindex_predicate_card (T : Finset (Fin M)) (P : Fin M → Prop) [DecidablePred P] :
    ((univ : Finset (Fin T.card)).filter (fun i => P (selectedIndex T i))).card=(T.filter P).card := by
  have hid : ((univ : Finset (Fin T.card)).filter (fun i => P (selectedIndex T i))).image
      (selectedIndex T)=T.filter P := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      exact mem_filter.mpr ⟨selectedIndex_mem T j,(mem_filter.mp hj).2⟩
    · intro hi
      obtain ⟨hiT,hiP⟩ := mem_filter.mp hi
      let j := T.equivFin ⟨i,hiT⟩
      have hj : selectedIndex T j=i := by simp [selectedIndex,j]
      exact mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,by rwa [hj]⟩,hj⟩
  rw [← hid,card_image_of_injective _ (selectedIndex_injective T)]

/-- Original full-shading two ends transfers with exactly the factor two.
The marked-cell filter plays no role in the full shadings. -/
theorem selected_two_ends (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    (T : Finset (Fin M)) {δ B alpha : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hsub : ∀ i, O i ⊆ F.shade i) (hT : T ⊆ goodTubes F.shade O)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
        B*r^alpha*((F.shade i).card : ℝ)) :
    ∀ i x r, δ ≤ r → r ≤ 1 →
      ((((selectedFamily F O T).shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
        (2*B)*r^alpha*(((selectedFamily F O T).shade i).card : ℝ) := by
  intro i x r hr hr1
  let j := selectedIndex T i
  have hcard : ((F.shade j).card : ℝ) ≤ 2*((O j).card : ℝ) := by
    exact_mod_cast (mem_filter.mp (hT (selectedIndex_mem T i))).2
  have hcount : (((O j).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
      (((F.shade j).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) := by
    exact_mod_cast card_le_card (filter_subset_filter _ (hsub j))
  have hh := mul_le_mul_of_nonneg_left hcard (mul_nonneg hB (Real.rpow_nonneg (hδ.le.trans hr) alpha))
  exact (hcount.trans (hends j x r hr hr1)).trans (by
    simpa only [selectedFamily,j,mul_assoc,mul_comm,mul_left_comm] using hh)

/-- Same-radius broadness holds for the actual reindexed marked family at
all cells; outside the retained marked-cell set its row is empty. -/
theorem selected_broadness (F : TubeFamily k M) (O marks : Fin M → Finset (Cell k))
    (T : Finset (Fin M)) {theta : ℝ}
    (hbroad : ∀ z ∈ cells marks, ∀ v : Space k, ‖v‖=1 →
      (((row marks univ z).filter (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
        ((row marks univ z).card : ℝ)/10) :
    ∀ z : Cell k, ∀ v : Space k, ‖v‖=1 →
      (((incident (MarkedSubsetSamples.markedFamily (selectedFamily F O T) (selectedMarks marks O T)) z).filter
        (fun i => projectiveDistance ((selectedFamily F O T).tube i).direction v < theta)).card : ℝ) ≤
          (2/5 : ℝ)*((incident (MarkedSubsetSamples.markedFamily (selectedFamily F O T)
            (selectedMarks marks O T)) z).card : ℝ) := by
  intro z v hv
  have hleft : incident (MarkedSubsetSamples.markedFamily (selectedFamily F O T)
      (selectedMarks marks O T)) z=(univ : Finset (Fin T.card)).filter
        (fun i => z ∈ retainedMarks marks O T (selectedIndex T i)) := by
    ext i
    constructor
    · intro hi
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
    · intro hi
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
  have hright : row (retainedMarks marks O T) T z=T.filter (fun i => z ∈ retainedMarks marks O T i) := rfl
  have hrow : (incident (MarkedSubsetSamples.markedFamily (selectedFamily F O T)
      (selectedMarks marks O T)) z).card=(row (retainedMarks marks O T) T z).card := by
    rw [hleft,hright]
    exact reindex_predicate_card T (fun i => z ∈ retainedMarks marks O T i)
  have hcap : ((incident (MarkedSubsetSamples.markedFamily (selectedFamily F O T)
      (selectedMarks marks O T)) z).filter
      (fun i => projectiveDistance ((selectedFamily F O T).tube i).direction v < theta)).card=
      ((row (retainedMarks marks O T) T z).filter
        (fun i => projectiveDistance (F.tube i).direction v < theta)).card := by
    rw [hleft,hright]
    have hboth : ((univ : Finset (Fin T.card)).filter
        (fun i => z ∈ retainedMarks marks O T (selectedIndex T i))).filter
        (fun i => projectiveDistance ((selectedFamily F O T).tube i).direction v < theta)=
        univ.filter (fun i => z ∈ retainedMarks marks O T (selectedIndex T i) ∧
          projectiveDistance (F.tube (selectedIndex T i)).direction v < theta) := by
      ext i
      constructor
      · intro hi
        obtain ⟨hi,hdir⟩ := mem_filter.mp hi
        exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2,hdir⟩
      · intro hi
        obtain ⟨_,hmark,hdir⟩ := mem_filter.mp hi
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hmark⟩,hdir⟩
    rw [hboth,filter_filter]
    exact reindex_predicate_card T (fun i => z ∈ retainedMarks marks O T i ∧
      projectiveDistance (F.tube i).direction v < theta)
  rw [hrow,hcap]
  by_cases hz : z ∈ keptCells marks O T
  · exact retained_broadness F O marks T hbroad hz v hv
  · have he : row (retainedMarks marks O T) T z=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hz (mem_inter.mp (mem_filter.mp hi).2).2
    simp only [he,filter_empty,card_empty,Nat.cast_zero,mul_zero,le_refl]

/-- The selected full family inherits every geometric count predicate by an
actual injective tube restriction, and its union stays inside the original one. -/
theorem selected_geometry (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    (T : Finset (Fin M)) {δ width sep R m A : ℝ}
    (hsub : ∀ i, O i ⊆ F.shade i) (hadm : F.Admissible width δ)
    (hsep : F.Separated sep) (hbounded : F.Bounded R) (hcap : F.CapBound δ m A) :
    (selectedFamily F O T).Admissible width δ ∧ (selectedFamily F O T).Separated sep ∧
      (selectedFamily F O T).Bounded R ∧ (selectedFamily F O T).CapBound δ m A ∧
      (selectedFamily F O T).unionCells ⊆ F.unionCells := by
  obtain ⟨hs,hb,hc⟩ := DiscreteMeasurable.injective_tube_restriction F (selectedFamily F O T)
    (selectedIndex T) (selectedIndex_injective T) (fun _ => rfl) hsep hbounded hcap
  refine ⟨fun i z hz => hadm _ z (hsub _ hz),hs,hb,hc,?_⟩
  intro z hz
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
  exact F.shade_subset_union _ (hsub _ hi)


/-- Complete actual marked recovery. The density changes only by choosing one
of two whole-tube bins; the final marking leaves its full shadings unchanged.
The geometric inheritance theorem above applies to exactly this selected family. -/
theorem recover (F : TubeFamily k M) (O marks : Fin M → Finset (Cell k))
    {δ lam theta B alpha : ℝ} (hδ : 0 < δ) (hlam : 0 < lam) (hB : 0 ≤ B)
    (hcomp : F.Comparable δ lam) (hsub : ∀ i, O i ⊆ F.shade i)
    (hmarks : ∀ i, marks i ⊆ F.shade i)
    (hbroad : ∀ z ∈ cells marks, ∀ v : Space k, ‖v‖=1 →
      (((row marks univ z).filter (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
        ((row marks univ z).card : ℝ)/10)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
        B*r^alpha*((F.shade i).card : ℝ)) :
    ∃ lam' : ℝ, 0 < lam' ∧ (lam'=lam/2 ∨ lam'=lam) ∧ ∃ T : Finset (Fin M),
      T ⊆ goodTubes F.shade O ∧ T.card ≤ M ∧
      (selectedFamily F O T).Comparable δ lam' ∧
      markedMass marks univ/4-2*deletionMass F.shade O ≤
        ∑ i, ((selectedMarks marks O T i).card : ℝ) ∧
      (∀ i, selectedMarks marks O T i ⊆ (selectedFamily F O T).shade i ∧
        selectedMarks marks O T i ⊆ marks (selectedIndex T i)) ∧
      (∀ z : Cell k, ∀ v : Space k, ‖v‖=1 →
        (((incident (MarkedSubsetSamples.markedFamily (selectedFamily F O T) (selectedMarks marks O T)) z).filter
          (fun i => projectiveDistance ((selectedFamily F O T).tube i).direction v < theta)).card : ℝ) ≤
            (2/5 : ℝ)*((incident (MarkedSubsetSamples.markedFamily (selectedFamily F O T)
              (selectedMarks marks O T)) z).card : ℝ)) ∧
      (∀ i x r, δ ≤ r → r ≤ 1 →
        ((((selectedFamily F O T).shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
          (2*B)*r^alpha*(((selectedFamily F O T).shade i).card : ℝ)) := by
  obtain ⟨lam',hlam',T,hT,hsize,hmass⟩ := select_marked_density F O marks hδ hcomp hsub hmarks
  have hpos : 0 < lam' := by rcases hlam' with h | h <;> rw [h] <;> positivity
  refine ⟨lam',hpos,hlam',T,hT,by simpa using card_le_card (subset_univ T),
    fun i => hsize _ (selectedIndex_mem T i),?_,?_,selected_broadness F O marks T hbroad,
    selected_two_ends F O T hδ hB hsub hT hends⟩
  · have hnonneg : 0 ≤ deletionMass F.shade O := by dsimp [deletionMass]; positivity
    change _ ≤ ∑ i, ((retainedMarks marks O T (selectedIndex T i)).card : ℝ)
    rw [reindex_mass]
    linarith
  · intro i
    constructor
    · exact fun z hz => (mem_inter.mp (mem_inter.mp hz).1).2
    · exact fun z hz => (mem_inter.mp (mem_inter.mp hz).1).1

end
end KakeyaFormal.MarkedPruningRecovery

#print axioms KakeyaFormal.MarkedPruningRecovery.good_marked_mass
#print axioms KakeyaFormal.MarkedPruningRecovery.two_density_bins

#print axioms KakeyaFormal.MarkedPruningRecovery.select_marked_density
#print axioms KakeyaFormal.MarkedPruningRecovery.retained_broadness

#print axioms KakeyaFormal.MarkedPruningRecovery.selected_broadness
#print axioms KakeyaFormal.MarkedPruningRecovery.selected_two_ends
#print axioms KakeyaFormal.MarkedPruningRecovery.selected_geometry

#print axioms KakeyaFormal.MarkedPruningRecovery.recover
