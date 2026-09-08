import ProjectiveGeometry

/-!
# Full finite separation normalization by actual greedy coloring

The conflict graph joins distinct original tube indices whose projective
separation is less than the target mesh. Its actual local population is bounded
by the proved projective cap packing theorem. Finite greedy coloring partitions
all original tubes, retaining every tube exactly once, with a palette independent
of the mesh, tube count, positions, density and real-cap coefficient.
-/
namespace KakeyaFormal.SeparationColoring
open KakeyaFormal.ProjectiveGeometry
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Finite greedy coloring is proved directly from an actual neighbor-count
bound. The palette is selected by avoiding the actual already-used neighbor
colors, not supplied as an existence or integrality assumption. -/
theorem finite_greedy_coloring {ι : Type*} [DecidableEq ι]
    (R : ι → ι → Prop) (hsym : ∀ a b, R a b → R b a) (hirr : ∀ a, ¬R a a)
    (S : Finset ι) {n : ℕ} (hn : 0 < n)
    (hdegree : ∀ a ∈ S, (S.filter (R a)).card < n) :
    ∃ color : ι → Fin n, ∀ a ∈ S, ∀ b ∈ S, R a b → color a ≠ color b := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => ⟨0,hn⟩,by simp⟩
  | @insert a S ha ih =>
    have hdegS : ∀ b ∈ S, (S.filter (R b)).card < n := by
      intro b hb
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))).trans_lt
        (hdegree b (Finset.mem_insert_of_mem hb))
    obtain ⟨color,hcolor⟩ := ih hdegS
    let used := (S.filter (R a)).image color
    have hused : used.card < n := by
      have hcard : (S.filter (R a)).card ≤ ((insert a S).filter (R a)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert _ _))
      exact (Finset.card_image_le).trans_lt (hcard.trans_lt (hdegree a (Finset.mem_insert_self _ _)))
    have hnot : ∃ c : Fin n, c ∉ used := by
      by_contra h
      have hfull : (Finset.univ : Finset (Fin n)) ⊆ used := by
        intro c _
        by_contra hc
        exact h ⟨c,hc⟩
      have hh := Finset.card_le_card hfull
      simp only [Finset.card_univ,Fintype.card_fin] at hh
      omega
    obtain ⟨c,hc⟩ := hnot
    let newColor := Function.update color a c
    refine ⟨newColor,?_⟩
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hxEq | hxOld
    · subst x
      rcases Finset.mem_insert.mp hy with hyEq | hyOld
      · subst y
        exact False.elim (hirr a hxy)
      · have hya : y ≠ a := fun he => ha (he ▸ hyOld)
        have husedY : color y ∈ used := Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨hyOld,hxy⟩,rfl⟩
        simpa only [newColor,Function.update_self,Function.update_of_ne hya] using
          (fun he : c = color y => hc (he ▸ husedY))
    · rcases Finset.mem_insert.mp hy with hyEq | hyOld
      · subst y
        have hxa : x ≠ a := fun he => ha (he ▸ hxOld)
        have husedX : color x ∈ used := Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hxOld,hsym _ _ hxy⟩,rfl⟩
        simpa only [newColor,Function.update_self,Function.update_of_ne hxa] using
          (fun he : color x = c => hc (he ▸ husedX))
      · have hxa : x ≠ a := fun he => ha (he ▸ hxOld)
        have hya : y ≠ a := fun he => ha (he ▸ hyOld)
        simpa only [newColor,Function.update_of_ne hxa,Function.update_of_ne hya] using hcolor x hxOld y hyOld hxy

/-- Positive clipped separation ratio, used only to make the packing scale
admissible when the original separation exceeds the target separation. -/
def clippedSeparation (sigma : ℝ) : ℝ := min sigma 1

def neighborBound (k : ℕ) (sigma : ℝ) : ℝ :=
  packingConstant k*(1/clippedSeparation sigma)^k

def paletteSize (k : ℕ) (sigma : ℝ) : ℕ := Nat.ceil (neighborBound k sigma)+1

theorem clippedSeparation_pos {sigma : ℝ} (hσ : 0 < sigma) : 0 < clippedSeparation sigma :=
  lt_min hσ (by norm_num)

theorem paletteSize_pos (k : ℕ) (sigma : ℝ) : 0 < paletteSize k sigma := Nat.succ_pos _

/-- Explicit constant-palette size, with no mesh or family-cardinality term. -/
theorem paletteSize_bound (k : ℕ) {sigma : ℝ} (hσ : 0 < sigma) :
    (paletteSize k sigma:ℝ) ≤ neighborBound k sigma+2 := by
  have hq := clippedSeparation_pos hσ
  have hP := packingConstant_ge_one k
  have hnonneg : 0 ≤ neighborBound k sigma := by unfold neighborBound; positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  unfold paletteSize
  push_cast
  linarith

/-- The actual conflict relation on original indices. -/
def Conflict {k M : ℕ} (F : TubeFamily (k+1) M) (δ : ℝ) (i j : Fin M) : Prop :=
  i ≠ j ∧ projectiveDistance (F.tube i).direction (F.tube j).direction < δ

theorem conflict_symmetric {k M : ℕ} (F : TubeFamily (k+1) M) (δ : ℝ) : ∀ i j, Conflict F δ i j → Conflict F δ j i := by
  intro i j hij
  exact ⟨hij.1.symm,by simpa only [projective_symm] using hij.2⟩

theorem conflict_irreflexive {k M : ℕ} (F : TubeFamily (k+1) M) (δ : ℝ) : ∀ i, ¬Conflict F δ i i :=
  fun _ h => h.1 rfl

/-- Projective cap packing gives the actual degree bound in the conflict graph.
The original σδ separation is the only local-population input. -/
theorem conflict_population_bound {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ sigma : ℝ} (hδ : 0 < δ) (hσ : 0 < sigma) (hsep : F.Separated (sigma*δ)) (i : Fin M) :
    (((Finset.univ.filter (Conflict F δ i)).card):ℝ) ≤ neighborBound k sigma := by
  let q := clippedSeparation sigma
  have hq : 0 < q := clippedSeparation_pos hσ
  have hq1 : q ≤ 1 := min_le_right _ _
  have hqσ : q ≤ sigma := min_le_left _ _
  have h := indexed_projective_cap_packing (Finset.univ.filter (Conflict F δ i))
    (fun j => (F.tube j).direction) (F.tube i).direction
    (by positivity : 0 < q*δ) (by nlinarith : q*δ ≤ δ)
    (fun j _ => (F.tube j).unit_direction)
    (fun j hj => by
      have ha := (Finset.mem_filter.mp hj).2.2
      rw [projective_symm]
      exact ha.le)
    (fun a _ b _ hab => (mul_le_mul_of_nonneg_right hqσ hδ.le).trans (hsep a b hab))
  have hid : δ/(q*δ) = 1/q := by field_simp
  rw [hid] at h
  exact h

/-- The computed finite palette is larger than every actual conflict degree. -/
theorem conflict_degree_lt {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ sigma : ℝ} (hδ : 0 < δ) (hσ : 0 < sigma) (hsep : F.Separated (sigma*δ)) (i : Fin M) :
    (Finset.univ.filter (Conflict F δ i)).card < paletteSize k sigma := by
  have h := (conflict_population_bound F hδ hσ hsep i).trans (Nat.le_ceil (neighborBound k sigma))
  have hn : (Finset.univ.filter (Conflict F δ i)).card ≤ Nat.ceil (neighborBound k sigma) := by exact_mod_cast h
  exact Nat.lt_succ_of_le hn

/-- A full coloring of all original tubes into a fixed palette. Every same-color
class has the target δ separation; the theorem selects no subfamily. -/
theorem full_separation_coloring {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ sigma : ℝ} (hδ : 0 < δ) (hσ : 0 < sigma) (hsep : F.Separated (sigma*δ)) :
    ∃ color : Fin M → Fin (paletteSize k sigma), ∀ i j, color i = color j → i ≠ j →
      δ ≤ projectiveDistance (F.tube i).direction (F.tube j).direction := by
  obtain ⟨color,hcolor⟩ := finite_greedy_coloring (Conflict F δ) (conflict_symmetric F δ)
    (conflict_irreflexive F δ) Finset.univ (paletteSize_pos k sigma)
    (fun i _ => conflict_degree_lt F hδ hσ hsep i)
  refine ⟨color,?_⟩
  intro i j hcol hij
  by_contra hdist
  exact hcolor i (Finset.mem_univ _) j (Finset.mem_univ _) ⟨hij,lt_of_not_ge hdist⟩ hcol

/-- The actual finite fiber of one color. -/
def colorClass {M n : ℕ} (color : Fin M → Fin n) (c : Fin n) : Finset (Fin M) :=
  Finset.univ.filter (fun i => color i = c)

/-- Every original index belongs to exactly its assigned color class. -/
theorem mem_colorClass {M n : ℕ} (color : Fin M → Fin n) (c : Fin n) (i : Fin M) :
    i ∈ colorClass color c ↔ color i = c := by simp [colorClass]

theorem colorClasses_disjoint {M n : ℕ} (color : Fin M → Fin n) :
    Pairwise (fun c d => Disjoint (colorClass color c) (colorClass color d)) := by
  intro c d hcd
  apply Finset.disjoint_left.mpr
  intro i hic hid
  exact hcd ((mem_colorClass color c i).mp hic |>.symm.trans ((mem_colorClass color d i).mp hid))

theorem colorClasses_cover {M n : ℕ} (color : Fin M → Fin n) :
    Finset.univ.biUnion (colorClass color) = Finset.univ := by
  ext i
  simp [Finset.mem_biUnion,mem_colorClass]

/-- Every real weight is retained exactly once. This includes density-weighted
incidence masses and does not require their being equal or nonnegative. -/
theorem color_weight_sum {M n : ℕ} (color : Fin M → Fin n) (weight : Fin M → ℝ) :
    (∑ c, ∑ i ∈ colorClass color c, weight i) = ∑ i, weight i := by
  exact Finset.sum_fiberwise Finset.univ color weight

/-- Enumerate an actual color fiber by a finite standard index type. -/
def classIndex {M n : ℕ} (color : Fin M → Fin n) (c : Fin n)
    (i : Fin (colorClass color c).card) : Fin M := (colorClass color c).equivFin.symm i

theorem classIndex_injective {M n : ℕ} (color : Fin M → Fin n) (c : Fin n) :
    Function.Injective (classIndex color c) :=
  Subtype.val_injective.comp (colorClass color c).equivFin.symm.injective

theorem classIndex_color {M n : ℕ} (color : Fin M → Fin n) (c : Fin n)
    (i : Fin (colorClass color c).card) : color (classIndex color c i) = c :=
  (mem_colorClass color c _).mp ((colorClass color c).equivFin.symm i).2

theorem classIndex_covers {M n : ℕ} (color : Fin M → Fin n) (i : Fin M) :
    ∃ j, classIndex color (color i) j = i := by
  refine ⟨(colorClass color (color i)).equivFin ⟨i,(mem_colorClass color (color i) i).mpr rfl⟩,?_⟩
  simp [classIndex]

/-- Actual class families retain the original tubes and their complete shadings. -/
def classFamily {k M n : ℕ} (F : TubeFamily k M) (color : Fin M → Fin n) (c : Fin n) :
    TubeFamily k (colorClass color c).card where
  tube i := F.tube (classIndex color c i)
  shade i := F.shade (classIndex color c i)

theorem classFamily_separated {k M n : ℕ} (F : TubeFamily k M) (color : Fin M → Fin n) {δ : ℝ}
    (hcolor : ∀ i j, color i = color j → i ≠ j →
      δ ≤ projectiveDistance (F.tube i).direction (F.tube j).direction) (c : Fin n) :
    (classFamily F color c).Separated δ := by
  intro i j hij
  exact hcolor _ _ ((classIndex_color color c i).trans (classIndex_color color c j).symm)
    (fun he => hij (classIndex_injective color c he))

/-- Real-m cap bounds pass to every actual color family with no coefficient loss. -/
theorem classFamily_cap_bound {k M n : ℕ} (F : TubeFamily k M) (color : Fin M → Fin n)
    {δ m A : ℝ} (hcap : F.CapBound δ m A) (c : Fin n) : (classFamily F color c).CapBound δ m A := by
  intro center hunit r hr hr1
  have hcard : (Finset.univ.filter (fun i =>
      projectiveDistance ((classFamily F color c).tube i).direction center ≤ r)).card ≤
      (Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction center ≤ r)).card := by
    apply Finset.card_le_card_of_injOn (classIndex color c)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · exact fun i _ j _ hij => classIndex_injective color c hij
  apply le_trans ?_ (hcap center hunit r hr hr1)
  exact_mod_cast hcard

/-- Admissibility of all original shade cells passes to every actual class. -/
theorem classFamily_admissible {k M n : ℕ} (F : TubeFamily k M) (color : Fin M → Fin n)
    {width δ : ℝ} (hadm : F.Admissible width δ) (c : Fin n) :
    (classFamily F color c).Admissible width δ := fun i => hadm (classIndex color c i)

/-- Reindexing each class keeps its complete actual weighted mass. -/
theorem classIndex_weight_sum {M n : ℕ} (color : Fin M → Fin n) (c : Fin n) (weight : Fin M → ℝ) :
    (∑ i, weight (classIndex color c i)) = ∑ i ∈ colorClass color c, weight i := by
  have h₁ := (colorClass color c).equivFin.symm.sum_comp (fun i : colorClass color c => weight i.1)
  have h₂ : (∑ i ∈ colorClass color c, weight i) = ∑ i : colorClass color c, weight i.1 :=
    Finset.sum_subtype (colorClass color c) (fun _ => Iff.rfl) weight
  exact h₁.trans h₂.symm

/-- The reindexed families preserve all original real weights across all colors. -/
theorem classFamilies_weight_sum {M n : ℕ} (color : Fin M → Fin n) (weight : Fin M → ℝ) :
    (∑ c, ∑ i, weight (classIndex color c i)) = ∑ i, weight i := by
  simp_rw [classIndex_weight_sum]
  exact color_weight_sum color weight

/-- The actual unions of all class shadings equal the original finite cell union. -/
theorem classFamilies_union {k M n : ℕ} (F : TubeFamily k M) (color : Fin M → Fin n) :
    Finset.univ.biUnion (fun c => (classFamily F color c).unionCells) = F.unionCells := by
  ext z
  constructor
  · intro hz
    obtain ⟨c,_,hc⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_biUnion.mpr ⟨classIndex color c i,Finset.mem_univ _,hi⟩
  · intro hz
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨j,hj⟩ := classIndex_covers color i
    refine Finset.mem_biUnion.mpr ⟨color i,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,?_⟩⟩
    change z ∈ F.shade (classIndex color (color i) j)
    rwa [hj]

/-- Complete actual partition into target-separated finite tube families. The
palette depends only on dimension and σ. Every original tube, shade cell and
arbitrary real tube weight is retained exactly once in the indexed partition. -/
theorem full_separation_partition {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ sigma : ℝ} (hδ : 0 < δ) (hσ : 0 < sigma) (hsep : F.Separated (sigma*δ)) :
    ∃ color : Fin M → Fin (paletteSize k sigma),
      (∀ c, (classFamily F color c).Separated δ) ∧
      (∀ weight : Fin M → ℝ, (∑ c, ∑ i, weight (classIndex color c i)) = ∑ i, weight i) ∧
      Finset.univ.biUnion (fun c => (classFamily F color c).unionCells) = F.unionCells := by
  obtain ⟨color,hcolor⟩ := full_separation_coloring F hδ hσ hsep
  exact ⟨color,classFamily_separated F color hcolor,classFamilies_weight_sum color,classFamilies_union F color⟩

end
end KakeyaFormal.SeparationColoring

#print axioms KakeyaFormal.SeparationColoring.full_separation_partition
