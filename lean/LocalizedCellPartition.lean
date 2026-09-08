import LocalizedGridTubes
import OccupancySelection

/-! Actual global bins of OLD cell labels for the two-ends reduction.
Each localized tube keeps one bin. Distinct bin unions are disjoint, and
their origins are snapped to the original fine grid for exact rescaling. -/
namespace KakeyaFormal.LocalizedCellPartition
open Finset GridCells GridGeometry LocalizedGridTubes
noncomputable section
open Classical

def cellLabel {k : ℕ} (δ rho : ℝ) (z : Cell k) : Cell k := label rho (cellCenter δ z)
def slice {k : ℕ} (δ rho : ℝ) (S : Finset (Cell k)) (q : Cell k) : Finset (Cell k) :=
  S.filter (fun z => cellLabel δ rho z=q)
def binCount (k : ℕ) : ℕ := (2*Nat.ceil (1+(k:ℝ)/2)+3)^k

theorem binCount_pos (k : ℕ) : 0 < binCount k := by unfold binCount; positivity

theorem occupied_bin_count {k : ℕ} (S : Finset (Cell k)) (center : Space k)
    {δ rho : ℝ} (hrho : 0 < rho)
    (hball : ∀ z ∈ S, dist (cellCenter δ z) center ≤ rho) :
    (S.image (cellLabel δ rho)).card ≤ binCount k := by
  apply ball_grid_count (R:=1+(k:ℝ)/2) hrho center
  intro q hq
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hq
  have hc := cell_center_distance (gridCell_covers hrho (cellCenter δ z))
  have ht := dist_triangle (cellCenter rho (cellLabel δ rho z)) (cellCenter δ z) center
  have hd := hball z hz
  change dist (cellCenter δ z) (cellCenter rho (cellLabel δ rho z)) ≤ (k:ℝ)*rho/2 at hc
  rw [dist_comm (cellCenter rho (cellLabel δ rho z)) (cellCenter δ z)] at ht
  nlinarith

/-- Maximum cardinality among the actual occupied bins supplies fixed retention. -/
theorem best_bin {k : ℕ} (S : Finset (Cell k)) (center : Space k)
    {δ rho : ℝ} (hrho : 0 < rho) (hne : S.Nonempty)
    (hball : ∀ z ∈ S, dist (cellCenter δ z) center ≤ rho) :
    ∃ q : Cell k, (slice δ rho S q).Nonempty ∧
      S.card ≤ binCount k*(slice δ rho S q).card := by
  let labels := S.image (cellLabel δ rho)
  obtain ⟨q,hq,hmax⟩ := labels.exists_max_image (fun q => (slice δ rho S q).card) (hne.image _)
  have hne' : (slice δ rho S q).Nonempty := by
    obtain ⟨z,hz,hlabel⟩ := mem_image.mp hq
    exact ⟨z,mem_filter.mpr ⟨hz,hlabel⟩⟩
  have hsum : S.card = ∑ q ∈ labels, (slice δ rho S q).card :=
    card_eq_sum_card_fiberwise (fun z hz => mem_image.mpr ⟨z,hz,rfl⟩)
  have hc := occupied_bin_count S center hrho hball
  refine ⟨q,hne',?_⟩
  calc
    _ = ∑ p ∈ labels, (slice δ rho S p).card := hsum
    _ ≤ ∑ _p ∈ labels, (slice δ rho S q).card := sum_le_sum (fun p hp => hmax p hp)
    _ = labels.card*(slice δ rho S q).card := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hc

/-- The original localization center is uniformly near the bin's snapped
fine-grid origin. No divisibility relation between rho and delta is needed. -/
theorem center_near_origin {k : ℕ} (S : Finset (Cell k)) (center : Space k)
    (q : Cell k) {δ rho : ℝ} (hδ : 0 < δ) (hδrho : δ ≤ rho) (hne : S.Nonempty)
    (hball : ∀ z ∈ S, dist (cellCenter δ z) center ≤ rho)
    (hlabel : ∀ z ∈ S, cellLabel δ rho z=q) :
    dist center (cellCenter δ (fineOrigin δ rho q)) ≤ (1+(k:ℝ))*rho := by
  have hrho := hδ.trans_le hδrho
  obtain ⟨z,hz⟩ := hne
  have hc := cell_center_distance (gridCell_covers hrho (cellCenter δ z))
  have hs := cell_center_distance (gridCell_covers hδ (cellCenter rho q))
  have hl := hlabel z hz
  change dist (cellCenter δ z) (cellCenter rho (cellLabel δ rho z)) ≤ (k:ℝ)*rho/2 at hc
  rw [hl] at hc
  change dist (cellCenter rho q) (cellCenter δ (fineOrigin δ rho q)) ≤ (k:ℝ)*δ/2 at hs
  have h1 := dist_triangle center (cellCenter δ z) (cellCenter rho q)
  have h2 := dist_triangle center (cellCenter rho q) (cellCenter δ (fineOrigin δ rho q))
  have hb := hball z hz
  rw [dist_comm center (cellCenter δ z)] at h1
  nlinarith [mul_le_mul_of_nonneg_left hδrho (Nat.cast_nonneg k)]

theorem proportional_two_ends {k : ℕ} (S T : Finset (Cell k)) {δ rho B alpha cost : ℝ}
    (hδ : 0 < δ) (hrho : 0 < rho) (hB : 0 ≤ B) (hsub : T ⊆ S)
    (hret : (S.card:ℝ) ≤ cost*(T.card:ℝ))
    (hends : ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ rho →
      ((S.filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*(r/rho)^alpha*(S.card:ℝ)) :
    ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ rho →
      ((T.filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        (cost*B)*(r/rho)^alpha*(T.card:ℝ) := by
  intro x r hr hr1
  have hcard : ((T.filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
      ((S.filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) :=
    Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hsub))
  have hcoef : 0 ≤ B*(r/rho)^alpha := by positivity [hδ.trans_le hr]
  exact (hcard.trans (hends x r hr hr1)).trans
    ((mul_le_mul_of_nonneg_left hret hcoef).trans_eq (by ring))

def groupIndices {M k : ℕ} (assign : Fin M → Cell k) (q : Cell k) : Finset (Fin M) :=
  univ.filter (fun i => assign i=q)

def groupCells {M k : ℕ} (Z : Fin M → Finset (Cell k)) (assign : Fin M → Cell k)
    (q : Cell k) : Finset (Cell k) := (groupIndices assign q).biUnion Z

theorem group_label {M k : ℕ} (Z : Fin M → Finset (Cell k)) (assign : Fin M → Cell k)
    {δ rho : ℝ} (hlabel : ∀ i z, z ∈ Z i → cellLabel δ rho z=assign i)
    (q : Cell k) {z : Cell k} (hz : z ∈ groupCells Z assign q) : cellLabel δ rho z=q := by
  obtain ⟨i,hi,hzi⟩ := mem_biUnion.mp hz
  exact (hlabel i z hzi).trans (mem_filter.mp hi).2

theorem groups_disjoint {M k : ℕ} (Z : Fin M → Finset (Cell k)) (assign : Fin M → Cell k)
    {δ rho : ℝ} (hlabel : ∀ i z, z ∈ Z i → cellLabel δ rho z=assign i) :
    Pairwise (fun q r => Disjoint (groupCells Z assign q) (groupCells Z assign r)) := by
  intro q r hqr
  exact disjoint_left.mpr (fun z hz hz' => hqr ((group_label Z assign hlabel q hz).symm.trans
    (group_label Z assign hlabel r hz')))

/-- Every selected old cell belongs to one global bin, so its group is counted
at most once. The summation is over arbitrary finite sets of spatial bins. -/
theorem group_card_sum {M k : ℕ} (F : TubeFamily k M) (Z : Fin M → Finset (Cell k))
    (assign : Fin M → Cell k) (Q : Finset (Cell k)) {δ rho : ℝ}
    (hsub : ∀ i, Z i ⊆ F.shade i)
    (hlabel : ∀ i z, z ∈ Z i → cellLabel δ rho z=assign i) :
    (∑ q ∈ Q, (groupCells Z assign q).card) ≤ F.unionCells.card := by
  have hdis : (Q:Set (Cell k)).PairwiseDisjoint (groupCells Z assign) :=
    fun q _ r _ hqr => groups_disjoint Z assign hlabel hqr
  rw [← card_biUnion hdis]
  apply card_le_card
  intro z hz
  obtain ⟨q,_,hzq⟩ := mem_biUnion.mp hz
  obtain ⟨i,_,hzi⟩ := mem_biUnion.mp hzq
  exact F.shade_subset_union i (hsub i hzi)


/-- One actual bin per original tube and an equal positive retained cardinality.
All indices and original directions survive. -/
structure Partition {k M : ℕ} (F : TubeFamily k M) (δ rho s : ℝ) where
  assignment : Fin M → Cell k
  shade : Fin M → Finset (Cell k)
  commonCard : ℕ
  commonCard_pos : 0 < commonCard
  subset : ∀ i, shade i ⊆ F.shade i
  card_eq : ∀ i, (shade i).card=commonCard
  label_eq : ∀ i z, z ∈ shade i → cellLabel δ rho z=assignment i
  density_lower : s/(binCount k:ℝ) ≤ δ*(commonCard:ℝ)
  density_upper : δ*(commonCard:ℝ) ≤ 2*s
  full_retention : ∀ i, ((F.shade i).card:ℝ) ≤
    (2*(binCount k:ℝ))*((shade i).card:ℝ)

/-- Select a most populous occupied bin, then trim to the smallest retained
cardinality. The only inputs are actual localization and original comparability. -/
theorem construct {k M : ℕ} (F : TubeFamily k M) {δ rho s : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hrho : 0 < rho) (hs : 0 < s)
    (hcomp : F.Comparable δ s) (centers : Fin M → Space k)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho) :
    Nonempty (Partition F δ rho s) := by
  have hK : (0:ℝ) < binCount k := Nat.cast_pos.mpr (binCount_pos k)
  have hne (i : Fin M) : (F.shade i).Nonempty := by
    apply card_pos.mp
    exact_mod_cast ((div_pos hs hδ).trans_le (hcomp i).1)
  have hex (i : Fin M) := best_bin (F.shade i) (centers i) hrho (hne i) (hball i)
  choose assignment hnonempty hbest using hex
  let W : Fin M → Finset (Cell k) := fun i => slice δ rho (F.shade i) (assignment i)
  have hW (i : Fin M) : s/(δ*(binCount k:ℝ)) ≤ ((W i).card:ℝ) := by
    have hh : ((F.shade i).card:ℝ) ≤ (binCount k:ℝ)*((W i).card:ℝ) := by
      exact_mod_cast hbest i
    have h1 := (hcomp i).1.trans hh
    apply (div_le_iff₀ (mul_pos hδ hK)).mpr
    have h2 := (div_le_iff₀ hδ).mp h1
    nlinarith
  have hu : (univ : Finset (Fin M)).Nonempty := ⟨⟨0,hM⟩,mem_univ _⟩
  obtain ⟨N,hN,hNl,Z,hZ,_⟩ := OccupancySelection.uniform_integer_trim univ hu W
    (div_pos hs (mul_pos hδ hK)) (fun i _ => hW i)
  have hsub (i : Fin M) : Z i ⊆ F.shade i :=
    (hZ i (mem_univ _)).1.trans (filter_subset _ _)
  have hcard (i : Fin M) : (Z i).card=N := (hZ i (mem_univ _)).2
  have hlow : s/(binCount k:ℝ) ≤ δ*(N:ℝ) := by
    have hh := (div_le_iff₀ (mul_pos hδ hK)).mp hNl
    apply (div_le_iff₀ hK).mpr
    nlinarith
  have hupp : δ*(N:ℝ) ≤ 2*s := by
    let i : Fin M := ⟨0,hM⟩
    have hc : (N:ℝ) ≤ ((F.shade i).card:ℝ) := by
      rw [← hcard i]
      exact Nat.cast_le.mpr (card_le_card (hsub i))
    have hh := (le_div_iff₀ hδ).mp (hc.trans (hcomp i).2)
    nlinarith
  refine ⟨⟨assignment,Z,N,hN,hsub,hcard,?_,hlow,hupp,?_⟩⟩
  · intro i z hz
    exact (mem_filter.mp ((hZ i (mem_univ _)).1 hz)).2
  · intro i
    rw [hcard i]
    have hlo := (div_le_iff₀ hK).mp hlow
    have hhi := (le_div_iff₀ hδ).mp (hcomp i).2
    apply (mul_le_mul_iff_of_pos_right hδ).mp
    nlinarith

def Partition.family {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) : TubeFamily k M where
  tube := F.tube
  shade := P.shade

def Partition.density {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) : ℝ := δ*(P.commonCard:ℝ)

theorem Partition.nonempty {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) (i : Fin M) : (P.shade i).Nonempty :=
  card_pos.mp (by rw [P.card_eq i]; exact P.commonCard_pos)

theorem Partition.comparable {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) (hδ : 0 < δ) : P.family.Comparable δ P.density := by
  intro i
  change δ*(P.commonCard:ℝ)/δ ≤ ((P.shade i).card:ℝ) ∧
    ((P.shade i).card:ℝ) ≤ 2*(δ*(P.commonCard:ℝ))/δ
  rw [P.card_eq i]
  have h1 : δ*(P.commonCard:ℝ)/δ = (P.commonCard:ℝ) := by field_simp
  have h2 : 2*(δ*(P.commonCard:ℝ))/δ = 2*(P.commonCard:ℝ) := by field_simp
  rw [h1,h2]
  constructor
  · exact le_refl _
  · nlinarith [Nat.cast_nonneg (α:=ℝ) P.commonCard]

theorem Partition.admissible {k M : ℕ} {F : TubeFamily k M} {δ rho s width : ℝ}
    (P : Partition F δ rho s) (h : F.Admissible width δ) : P.family.Admissible width δ :=
  fun i z hz => h i z (P.subset i hz)

theorem Partition.two_ends {k M : ℕ} {F : TubeFamily k M} {δ rho s B alpha : ℝ}
    (P : Partition F δ rho s) (hδ : 0 < δ) (hrho : 0 < rho) (hB : 0 ≤ B)
    (hends : ∀ i x r, δ ≤ r → r ≤ rho →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*(r/rho)^alpha*((F.shade i).card:ℝ)) :
    ∀ i x r, δ ≤ r → r ≤ rho →
      (((P.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        (2*(binCount k:ℝ)*B)*(r/rho)^alpha*((P.shade i).card:ℝ) :=
  fun i => proportional_two_ends (F.shade i) (P.shade i) hδ hrho hB
    (P.subset i) (P.full_retention i) (hends i)

theorem Partition.origin_bound {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) (hδ : 0 < δ) (hδrho : δ ≤ rho)
    (centers : Fin M → Space k)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho) :
    ∀ i, dist (centers i) (cellCenter δ (fineOrigin δ rho (P.assignment i))) ≤
      (1+(k:ℝ))*rho := by
  intro i
  exact center_near_origin (P.shade i) (centers i) (P.assignment i) hδ hδrho
    (P.nonempty i) (fun z hz => hball i z (P.subset i hz)) (P.label_eq i)


def Partition.bins {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) : Finset (Cell k) := univ.image P.assignment

def Partition.index {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) (q : Cell k)
    (i : Fin (groupIndices P.assignment q).card) : Fin M :=
  (groupIndices P.assignment q).equivFin.symm i

theorem Partition.index_injective {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) (q : Cell k) : Function.Injective (P.index q) :=
  Subtype.val_injective.comp (groupIndices P.assignment q).equivFin.symm.injective

theorem Partition.index_assignment {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) (q : Cell k) (i : Fin (groupIndices P.assignment q).card) :
    P.assignment (P.index q i)=q :=
  (mem_filter.mp ((groupIndices P.assignment q).equivFin.symm i).property).2

def Partition.groupFamily {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) (q : Cell k) : TubeFamily k (groupIndices P.assignment q).card where
  tube i := F.tube (P.index q i)
  shade i := P.shade (P.index q i)

theorem Partition.group_union {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) (q : Cell k) :
    (P.groupFamily q).unionCells = groupCells P.shade P.assignment q := by
  ext z
  constructor
  · intro hz
    obtain ⟨i,_,hzi⟩ := mem_biUnion.mp hz
    exact mem_biUnion.mpr ⟨P.index q i,((groupIndices P.assignment q).equivFin.symm i).property,hzi⟩
  · intro hz
    obtain ⟨i,hi,hzi⟩ := mem_biUnion.mp hz
    refine mem_biUnion.mpr ⟨(groupIndices P.assignment q).equivFin ⟨i,hi⟩,mem_univ _,?_⟩
    simpa only [groupFamily,index,Equiv.symm_apply_apply] using hzi

theorem Partition.group_comparable {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) (hδ : 0 < δ) (q : Cell k) :
    (P.groupFamily q).Comparable δ P.density := fun i => P.comparable hδ (P.index q i)

theorem Partition.group_admissible {k M : ℕ} {F : TubeFamily k M} {δ rho s width : ℝ}
    (P : Partition F δ rho s) (h : F.Admissible width δ) (q : Cell k) :
    (P.groupFamily q).Admissible width δ := fun _i z hz => h _ z (P.subset _ hz)

theorem Partition.group_separated {k M : ℕ} {F : TubeFamily k M} {δ rho s r : ℝ}
    (P : Partition F δ rho s) (h : F.Separated r) (q : Cell k) :
    (P.groupFamily q).Separated r :=
  fun _i _j hij => h _ _ (fun heq => hij (P.index_injective q heq))

theorem Partition.group_cap_bound {k M : ℕ} {F : TubeFamily k M} {δ rho s m A : ℝ}
    (P : Partition F δ rho s) (h : F.CapBound δ m A) (q : Cell k) :
    (P.groupFamily q).CapBound δ m A := by
  intro v hv r hr hr1
  have hc : (univ.filter (fun i => projectiveDistance ((P.groupFamily q).tube i).direction v ≤ r)).card ≤
      (univ.filter (fun i => projectiveDistance (F.tube i).direction v ≤ r)).card := by
    apply card_le_card_of_injOn (P.index q)
    · intro i hi
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
    · exact fun _ _ _ _ hh => P.index_injective q hh
  exact (Nat.cast_le.mpr hc).trans (h v hv r hr hr1)

/-- Every original tube occurs in exactly one spatial group. -/
theorem Partition.population_sum {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) :
    ∑ q ∈ P.bins, (groupIndices P.assignment q).card = M := by
  have hh : (univ : Finset (Fin M)).card =
      ∑ q ∈ P.bins, (groupIndices P.assignment q).card :=
    card_eq_sum_card_fiberwise (fun i hi => mem_image.mpr ⟨i,hi,rfl⟩)
  simpa only [card_univ,Fintype.card_fin] using hh.symm

/-- Exact disjoint old-cell summation, after both bin selection and trimming. -/
theorem Partition.union_sum {k M : ℕ} {F : TubeFamily k M} {δ rho s : ℝ}
    (P : Partition F δ rho s) :
    (∑ q ∈ P.bins, (P.groupFamily q).unionCells.card) ≤ F.unionCells.card := by
  simp_rw [P.group_union]
  exact group_card_sum F P.shade P.assignment P.bins P.subset P.label_eq

/-- Each actual spatial group has one common snapped fine-grid origin.
The genuine rescaled unit axes have a uniform dimension/width base bound;
all retained OLD labels, shading cardinalities, and union counts are exact. -/
theorem Partition.normalized_group {k M : ℕ} {F : TubeFamily k M} {δ rho s width : ℝ}
    (P : Partition F δ rho s) (hδ : 0 < δ) (hδrho : δ ≤ rho)
    (hadm : F.Admissible width δ) (centers : Fin M → Space k)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho)
    (q : Cell k) :
    ∃ a : Fin (groupIndices P.assignment q).card → ℝ,
      let L := 8*localWidth width*rho
      let G := Rescaling.family (P.groupFamily q) L δ (fineOrigin δ rho q) a
      G.Admissible (localWidth width) (δ/L) ∧
      G.Bounded ((6*localWidth width+(1+(k:ℝ)))/(8*localWidth width)) ∧
      (∀ i, (G.shade i).card=P.commonCard) ∧
      G.unionCells.card=(groupCells P.shade P.assignment q).card ∧
      ∀ i, (G.tube i).direction=(F.tube (P.index q i)).direction := by
  obtain ⟨a,ha,hb,hcard,hunion,hdir⟩ := normalized_localized_family (P.groupFamily q)
    (fun i => centers (P.index q i)) (fineOrigin δ rho q) hδ hδrho
    (fun i => P.nonempty _) (P.group_admissible hadm q)
    (fun i z hz => hball _ z (P.subset _ hz)) (R:=1+(k:ℝ)) (by
      intro i
      have hh := P.origin_bound hδ hδrho centers hball (P.index q i)
      rw [P.index_assignment q i] at hh
      exact hh)
  refine ⟨a,ha,hb,fun i => (hcard i).trans (P.card_eq _),?_,hdir⟩
  exact hunion.trans (congrArg card (P.group_union q))

end
end KakeyaFormal.LocalizedCellPartition
