import SpatialSplitting
import MeasurableMarkedSelection

/-! Spatial partitions of actual measurable full/marked angular shadings.
Every actual base label is kept. Full sets are unchanged on their label fiber;
only marks undergo a proved proportional restoration against the original row. -/
namespace KakeyaFormal.SpatialMarkedPartition
open Finset MeasureTheory MeasurableEnergy HairbrushSelection HairbrushKernel
open SpatialAngular SpatialSplitting AngularDecomposition
open scoped BigOperators ENNReal
noncomputable section
open Classical

variable {M : ℕ} {γ : Type*} [DecidableEq γ]

def labels (label : Fin M → γ) : Finset γ := univ.image label
def indices (label : Fin M → γ) (q : γ) : Finset (Fin M) := univ.filter (fun i => label i=q)

def Full {X : Type*} (Y : Fin M → Set X) (label : Fin M → γ) (q : γ) :
    Fin (indices label q).card → Set X := MeasurableMarkedSelection.reindex Y (indices label q)

def Marks {X : Type*} (G : Fin M → Set X) (label : Fin M → γ) (B : ℝ) (q : γ) :
    Fin (indices label q).card → Set X :=
  MeasurableMarkedSelection.marks G G (indices label q) (4*B)

def family {k : ℕ} (F : TubeFamily k M) (label : Fin M → γ) (q : γ) :
    TubeFamily k (indices label q).card := MeasurableMarkedSelection.family F (indices label q)

theorem index_label (label : Fin M → γ) (q : γ) (i : Fin (indices label q).card) :
    label (MeasurableMarkedSelection.index (indices label q) i)=q :=
  (mem_filter.mp (MeasurableMarkedSelection.index_mem (indices label q) i)).2

theorem sum_reindex (w : Fin M → ℝ) (T : Finset (Fin M)) :
    (∑ i, w (MeasurableMarkedSelection.index T i)) = ∑ i ∈ T, w i := by
  have h₁ := T.equivFin.symm.sum_comp (fun i : T => w i.val)
  have h₂ : (∑ i ∈ T, w i) = ∑ i : T, w i.val := sum_subtype T (fun _ => Iff.rfl) (fun i => w i)
  exact h₁.trans h₂.symm

/-- The reindexed row has exactly the original label-fiber cardinality. -/
theorem full_multiplicity {X : Type*} (Y : Fin M → Set X)
    (label : Fin M → γ) (q : γ) (x : X) :
    MeasurableEnergy.multiplicity (Full Y label q) x =
      ((fiber (univ.filter (fun i => x ∈ Y i)) label q).card:ℝ) := by
  unfold MeasurableEnergy.multiplicity Full MeasurableMarkedSelection.reindex
  rw [sum_reindex (fun i => oneIndicator (Y i) x) (indices label q)]
  simp [indices,fiber,oneIndicator,Set.indicator_apply,Finset.filter_filter,and_comm]

/-- The actual marked MeasurableEnergy.multiplicity is exactly the restored spatial fiber. -/
theorem marked_multiplicity {X : Type*} (G : Fin M → Set X)
    (label : Fin M → γ) (B : ℝ) (q : γ) (x : X) :
    MeasurableEnergy.multiplicity (Marks G label B q) x =
      ((restore (univ.filter (fun i => x ∈ G i)) label B q).card:ℝ) := by
  by_cases hx : x ∈ MeasurableMarkedSelection.keep G G (indices label q) (4*B)
  · have heq : MeasurableEnergy.multiplicity (Marks G label B q) x = MeasurableEnergy.multiplicity (Full G label q) x := by
      simp [Marks,Full,MeasurableMarkedSelection.marks,MeasurableEnergy.multiplicity,oneIndicator,Set.indicator_apply,hx]
    have hh := hx
    change MeasurableEnergy.multiplicity G x ≤ 4*B*MeasurableEnergy.multiplicity (Full G label q) x at hh
    rw [multiplicity_eq_card,full_multiplicity] at hh
    dsimp only [overlapCount] at hh
    rw [heq,full_multiplicity,restore,if_pos hh]
  · have heq : MeasurableEnergy.multiplicity (Marks G label B q) x = 0 := by
      simp [Marks,MeasurableMarkedSelection.marks,MeasurableEnergy.multiplicity,oneIndicator,hx]
    have hh := hx
    change ¬MeasurableEnergy.multiplicity G x ≤ 4*B*MeasurableEnergy.multiplicity (Full G label q) x at hh
    rw [multiplicity_eq_card,full_multiplicity] at hh
    dsimp only [overlapCount] at hh
    rw [heq,restore,if_neg hh,card_empty,Nat.cast_zero]

/-- Retention is pointwise across all actual labels, with no single-box choice. -/
theorem marked_pointwise {X : Type*} (G : Fin M → Set X)
    (label : Fin M → γ) {B : ℝ} (hB : 0 < B)
    (hcount : ∀ x, (((univ.filter (fun i => x ∈ G i)).image label).card:ℝ) ≤ B) :
    ∀ x, (3/4:ℝ)*MeasurableEnergy.multiplicity G x ≤ ∑ q ∈ labels label, MeasurableEnergy.multiplicity (Marks G label B q) x := by
  intro x
  simp_rw [marked_multiplicity]
  rw [multiplicity_eq_card]
  exact pointwise_restoration_mass_on _ label (labels label)
    (image_subset_image (filter_subset _ _)) hB (hcount x)

/-- Every selected full set is exactly one original full set. -/
theorem full_exact {X : Type*} (Y : Fin M → Set X) (label : Fin M → γ) (q : γ)
    (i : Fin (indices label q).card) :
    Full Y label q i = Y (MeasurableMarkedSelection.index (indices label q) i) := rfl

theorem marks_subset_full {X : Type*} (Y G : Fin M → Set X) (label : Fin M → γ)
    (B : ℝ) (q : γ) (hsub : ∀ i, G i ⊆ Y i) : ∀ i,
    Marks G label B q i ⊆ Full Y label q i :=
  fun i => Set.inter_subset_left.trans (hsub (MeasurableMarkedSelection.index (indices label q) i))

/-- Retained marks are measurable, including the proportional row condition. -/
theorem marks_measurable {X : Type*} [MeasurableSpace X] (G : Fin M → Set X)
    (label : Fin M → γ) (B : ℝ) (q : γ) (hG : ∀ i, MeasurableSet (G i)) :
    ∀ i, MeasurableSet (Marks G label B q i) :=
  MeasurableMarkedSelection.marks_measurable G G _ _ hG hG

/-- The pointwise retention integrates to genuine summed marked volume. -/
theorem marked_mass {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (G : Fin M → Set X) (label : Fin M → γ) {B : ℝ} (hB : 0 < B)
    (hG : ∀ i, MeasurableSet (G i)) (hf : ∀ i, ν (G i) ≠ ∞)
    (hcount : ∀ x, (((univ.filter (fun i => x ∈ G i)).image label).card:ℝ) ≤ B) :
    (3/4:ℝ)*(∑ i, ν.real (G i)) ≤
      ∑ q ∈ labels label, ∑ i, ν.real (Marks G label B q i) := by
  have hm (q) := marks_measurable G label B q hG
  have hfin (q) (i) : ν (Marks G label B q i) ≠ ∞ :=
    measure_ne_top_of_subset ((marks_subset_full G G label B q (fun _ => Set.Subset.rfl)) i) (hf _)
  have hi (q) : Integrable (MeasurableEnergy.multiplicity (Marks G label B q)) ν :=
    memLp_one_iff_integrable.mp (multiplicity_memLp _ (hm q) (hfin q) 1)
  have hh := integral_mono
    ((memLp_one_iff_integrable.mp (multiplicity_memLp G hG hf 1)).const_mul (3/4:ℝ))
    (integrable_finsetSum _ (fun q _ => hi q)) (marked_pointwise G label hB hcount)
  rw [integral_const_mul,multiplicity_integral G hG hf,integral_finsetSum _ (fun q _ => hi q)] at hh
  simpa only [multiplicity_integral _ (hm _) (hfin _)] using hh

/-- Label fibers partition the original tube population exactly. -/
theorem population_partition (label : Fin M → γ) :
    (∑ q ∈ labels label, (indices label q).card) = M := by
  have hh := card_eq_sum_card_fiberwise (s:=univ) (t:=labels label) (f:=label)
    (fun i _ => mem_image.mpr ⟨i,mem_univ _,rfl⟩)
  simpa only [indices,card_univ,Fintype.card_fin] using hh.symm

/-- All original full mass is counted once across the spatial fibers. -/
theorem full_mass_partition {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (Y : Fin M → Set X) (label : Fin M → γ) :
    (∑ q ∈ labels label, ∑ i, ν.real (Full Y label q i)) = ∑ i, ν.real (Y i) := by
  simp_rw [Full,MeasurableMarkedSelection.reindex_mass,indices]
  exact sum_fiberwise_of_maps_to (s:=univ) (t:=labels label) (g:=label)
    (fun i _ => mem_image.mpr ⟨i,mem_univ _,rfl⟩) (fun i => ν.real (Y i))

/-- Exact union partition; no old full shading is replaced or discarded. -/
theorem full_union_eq {X : Type*} (Y : Fin M → Set X) (label : Fin M → γ) :
    (⋃ q : ↥(labels label), ⋃ i, Full Y label q.val i) = ⋃ i, Y i := by
  ext x
  constructor
  · intro hx
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hq
    exact Set.mem_iUnion.mpr ⟨_,hi⟩
  · intro hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    let q : ↥(labels label) := ⟨label i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩
    have hiq : i ∈ indices label q.val := mem_filter.mpr ⟨mem_univ _,rfl⟩
    let j := (indices label q.val).equivFin ⟨i,hiq⟩
    have hj : MeasurableMarkedSelection.index (indices label q.val) j=i := by
      simp [MeasurableMarkedSelection.index,j]
    exact Set.mem_iUnion.mpr ⟨q,Set.mem_iUnion.mpr ⟨j,by simpa only [full_exact,hj] using hi⟩⟩

/-- A full spatial subunion stays in the identical old full union. -/
theorem full_union_subset {X : Type*} (Y : Fin M → Set X) (label : Fin M → γ) (q : γ) :
    (⋃ i, Full Y label q i) ⊆ ⋃ i, Y i := by
  intro x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨_,hi⟩

/-- Whole full-subunion overlap is bounded by occupied original label count. -/
theorem full_overlap {X : Type*} (Y : Fin M → Set X) (label : Fin M → γ) (x : X) :
    overlapCount (fun q : ↥(labels label) => ⋃ i, Full Y label q.val i) x ≤
      ((univ.filter (fun i => x ∈ Y i)).image label).card := by
  unfold overlapCount
  apply card_le_card_of_injOn Subtype.val
  · intro q hq
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (mem_filter.mp hq).2
    exact mem_image.mpr ⟨_,mem_filter.mpr ⟨mem_univ _,hi⟩,index_label label q.val i⟩
  · exact fun _ _ _ _ h => Subtype.val_injective h

/-- Bounded full-subunion overlap integrates without replacing the union by
an unrelated full family. -/
theorem full_union_volume {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (Y : Fin M → Set X) (label : Fin M → γ) {B : ℝ}
    (hY : ∀ i, MeasurableSet (Y i)) (hf : ∀ i, ν (Y i) ≠ ∞)
    (hcount : ∀ x, (((univ.filter (fun i => x ∈ Y i)).image label).card:ℝ) ≤ B) :
    (∑ q : ↥(labels label), ν.real (⋃ i, Full Y label q.val i)) ≤ B*ν.real (⋃ i, Y i) := by
  have hm (q : ↥(labels label)) : MeasurableSet (⋃ i, Full Y label q.val i) :=
    MeasurableSet.iUnion (fun _ => hY _)
  have hfin (q : ↥(labels label)) : ν (⋃ i, Full Y label q.val i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ:=ν)
      (s:=Set.univ) (f:=Full Y label q.val) (Set.toFinite _) (fun i _ => hf _)
  have hh := finite_union_overlap (fun q : ↥(labels label) => ⋃ i, Full Y label q.val i)
    hm hfin (fun x => (Nat.cast_le.mpr (full_overlap Y label x)).trans (hcount x))
  rwa [full_union_eq] at hh

/-- Broadness is restored on literal reindexed marked rows; the full shadings
are not thinned to pay for this proportional marking. -/
theorem marked_broad {k : ℕ} (F : TubeFamily k M) (G : Fin M → Set (Space k))
    (label : Fin M → γ) (B : ℝ) (q : γ) {δ beta tau K : ℝ}
    (hδ : 0 ≤ δ) (htau : 0 < tau) (hK : 0 ≤ K)
    (hbroad : ∀ x, Broad F (univ.filter (fun i => x ∈ G i)) δ beta tau K) :
    ∀ x, Broad (family F label q) (univ.filter (fun i => x ∈ Marks G label B q i))
      δ beta tau (K*(4*B)) := by
  intro x center r hr
  by_cases hx : x ∈ MeasurableMarkedSelection.keep G G (indices label q) (4*B)
  · have hcap : (cap (family F label q) (univ.filter (fun i => x ∈ Marks G label B q i)) center r).card ≤
        (cap F (univ.filter (fun i => x ∈ G i)) center r).card := by
      apply card_le_card_of_injOn (MeasurableMarkedSelection.index (indices label q))
      · intro i hi
        obtain ⟨hi,hangle⟩ := mem_filter.mp hi
        have hG : x ∈ G (MeasurableMarkedSelection.index (indices label q) i) :=
          ((mem_filter.mp hi).2).1
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hG⟩,hangle⟩
      · exact fun _ _ _ _ h => MeasurableMarkedSelection.index_injective _ h
    have hratio : ((univ.filter (fun i => x ∈ G i)).card:ℝ) ≤
        4*B*((univ.filter (fun i => x ∈ Marks G label B q i)).card:ℝ) := by
      have hh := hx
      change MeasurableEnergy.multiplicity G x ≤ 4*B*MeasurableEnergy.multiplicity (Full G label q) x at hh
      have hm : MeasurableEnergy.multiplicity (Marks G label B q) x =
          MeasurableEnergy.multiplicity (Full G label q) x := by
        simp [Marks,Full,MeasurableMarkedSelection.marks,MeasurableEnergy.multiplicity,
          oneIndicator,Set.indicator_apply,hx]
      rw [← hm,multiplicity_eq_card,multiplicity_eq_card] at hh
      exact hh
    have hh := (Nat.cast_le.mpr hcap).trans (hbroad x center r hr)
    have hp := mul_le_mul_of_nonneg_left hratio
      (mul_nonneg hK (Real.rpow_nonneg (div_nonneg (hδ.trans hr) htau.le) beta))
    exact hh.trans (hp.trans_eq (by ring))
  · have he : (univ.filter (fun i => x ∈ Marks G label B q i)) = ∅ := by
      simp [Marks,MeasurableMarkedSelection.marks,hx]
    rw [he]
    simp [cap]

end
end KakeyaFormal.SpatialMarkedPartition
