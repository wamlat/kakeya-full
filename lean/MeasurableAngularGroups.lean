import MeasurableMarkedSelection
import MeasurableIncidenceAtoms
import AngularDecomposition

/-! Exact nonempty-family compression for actual measurable angular shadings.
Original full sets and retained sets use the same injective index map. -/
namespace KakeyaFormal.MeasurableAngularGroups
open MeasureTheory Set AngularDecomposition
open scoped ENNReal
noncomputable section
open Classical

def active {X : Type*} {M : ℕ} (S : Fin M → Set X) : Finset (Fin M) :=
  Finset.univ.filter (fun i => (S i).Nonempty)

def index {X : Type*} {M : ℕ} (S : Fin M → Set X) (i : Fin (active S).card) : Fin M :=
  MeasurableMarkedSelection.index (active S) i

def compressed {X : Type*} {M : ℕ} (Y S : Fin M → Set X) : Fin (active S).card → Set X :=
  fun i => Y (index S i)

def family {X : Type*} {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Set X) :
    TubeFamily k (active S).card := MeasurableMarkedSelection.family F (active S)

theorem index_injective {X : Type*} {M : ℕ} (S : Fin M → Set X) : Function.Injective (index S) :=
  MeasurableMarkedSelection.index_injective _

theorem index_mem {X : Type*} {M : ℕ} (S : Fin M → Set X) (i : Fin (active S).card) :
    index S i ∈ active S := MeasurableMarkedSelection.index_mem _ _

theorem index_nonempty {X : Type*} {M : ℕ} (S : Fin M → Set X) (i : Fin (active S).card) :
    (S (index S i)).Nonempty := (Finset.mem_filter.mp (index_mem S i)).2

theorem index_surjective_on {X : Type*} {M : ℕ} (S : Fin M → Set X) {i : Fin M}
    (hi : i ∈ active S) : ∃ j : Fin (active S).card, index S j = i := by
  refine ⟨(active S).equivFin ⟨i,hi⟩,?_⟩
  simp [index,MeasurableMarkedSelection.index]

theorem compressed_measurable {X : Type*} [MeasurableSpace X] {M : ℕ}
    (Y S : Fin M → Set X) (hY : ∀ i, MeasurableSet (Y i)) :
    ∀ i, MeasurableSet (compressed Y S i) := fun i => hY (index S i)

theorem compressed_finite {X : Type*} [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (Y S : Fin M → Set X) (hY : ∀ i, μ (Y i) ≠ ∞) :
    ∀ i, μ (compressed Y S i) ≠ ∞ := fun i => hY (index S i)

theorem compressed_subset {X : Type*} {M : ℕ} (Y S : Fin M → Set X)
    (hsub : ∀ i, S i ⊆ Y i) : ∀ i, compressed S S i ⊆ compressed Y S i :=
  fun i => hsub (index S i)

theorem mass_eq {X : Type*} [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (S : Fin M → Set X) :
    (∑ i, μ.real (compressed S S i)) = ∑ i, μ.real (S i) := by
  change (∑ i, μ.real (MeasurableMarkedSelection.reindex S (active S) i)) = _
  rw [MeasurableMarkedSelection.reindex_mass]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have he : S i = ∅ := Set.not_nonempty_iff_eq_empty.mp
    (fun hh => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩))
  simp [he]

/-- Every occupied predicate supported in the active set has exactly the same
cardinality under the actual reindexing. -/
theorem filter_card_eq {X : Type*} {M : ℕ} (S : Fin M → Set X) (P : Fin M → Prop)
    (hP : ∀ i, P i → i ∈ active S) :
    (Finset.univ.filter (fun i : Fin (active S).card => P (index S i))).card =
      ((Finset.univ : Finset (Fin M)).filter P).card := by
  let A := Finset.univ.filter (fun i : Fin (active S).card => P (index S i))
  have himage : A.image (index S) = Finset.univ.filter P := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
    · intro hi
      have hPi := (Finset.mem_filter.mp hi).2
      obtain ⟨j,rfl⟩ := index_surjective_on S (hP i hPi)
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hPi⟩,rfl⟩
  rw [← himage,Finset.card_image_of_injective _ (index_injective S)]


theorem pointwise_card {X : Type*} {M : ℕ} (S : Fin M → Set X) (x : X) :
    (Finset.univ.filter (fun i => x ∈ compressed S S i)).card =
      (Finset.univ.filter (fun i => x ∈ S i)).card :=
  filter_card_eq S (fun i => x ∈ S i)
    (fun _i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨x,hi⟩⟩)

theorem family_broad {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Set (Space k))
    {δ beta tau K : ℝ}
    (hbroad : ∀ x, Broad F (Finset.univ.filter (fun i => x ∈ S i)) δ beta tau K) :
    ∀ x, Broad (family F S) (Finset.univ.filter (fun i => x ∈ compressed S S i)) δ beta tau K := by
  intro x center r hr
  have hcard : (cap (family F S) (Finset.univ.filter (fun i => x ∈ compressed S S i)) center r).card ≤
      (cap F (Finset.univ.filter (fun i => x ∈ S i)) center r).card := by
    apply Finset.card_le_card_of_injOn (index S)
    · intro i hi
      obtain ⟨hiP,hiAngle⟩ := Finset.mem_filter.mp hi
      obtain ⟨_,hiX⟩ := Finset.mem_filter.mp hiP
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hiX⟩,hiAngle⟩
    · exact fun i _ j _ hij => index_injective S hij
  exact (Nat.cast_le.mpr hcard).trans ((hbroad x center r hr).trans_eq (by rw [pointwise_card]))

theorem family_separated {X : Type*} {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Set X)
    {δ : ℝ} (hsep : F.Separated δ) : (family F S).Separated δ :=
  MeasurableMarkedSelection.family_separated F _ hsep

theorem family_cap_bound {X : Type*} {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Set X)
    {δ m A : ℝ} (hcap : F.CapBound δ m A) : (family F S).CapBound δ m A :=
  MeasurableMarkedSelection.family_cap_bound F _ hcap

theorem family_local_cap {X : Type*} {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Set X)
    (u : Space k) {r : ℝ} (hcap : ∀ i, (S i).Nonempty → projectiveDistance (F.tube i).direction u ≤ r) :
    ∀ i, projectiveDistance ((family F S).tube i).direction u ≤ r :=
  fun i => hcap _ (index_nonempty S i)

theorem union_eq {X : Type*} {M : ℕ} (S : Fin M → Set X) :
    (⋃ i, compressed S S i) = ⋃ i, S i := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨index S i,hi⟩
  · intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨j,rfl⟩ := index_surjective_on S (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨x,hi⟩⟩)
    exact Set.mem_iUnion.mpr ⟨j,hi⟩

theorem total_active_count {X γ : Type*} [DecidableEq γ] {M : ℕ}
    (groups : Finset γ) (S : γ → Fin M → Set X) (assign : Fin M → γ)
    (hunique : ∀ g i, (S g i).Nonempty → assign i = g) :
    (∑ g ∈ groups, (active (S g)).card) ≤ M := by
  have hdis : (↑groups : Set γ).PairwiseDisjoint (fun g => active (S g)) := by
    intro g _ h _ hgh
    apply Finset.disjoint_left.mpr
    intro i hig hih
    exact hgh ((hunique g i (Finset.mem_filter.mp hig).2).symm.trans
      (hunique h i (Finset.mem_filter.mp hih).2))
  rw [← Finset.card_biUnion hdis]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)

theorem mass_upper {X : Type*} [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (Y S : Fin M → Set X) (hfin : ∀ i, μ (Y i) ≠ ∞)
    (hsub : ∀ i, S i ⊆ Y i) {U : ℝ} (hupper : ∀ i, μ.real (Y i) ≤ U) :
    (∑ i, μ.real (S i)) ≤ U*((active S).card:ℝ) := by
  rw [← mass_eq μ S]
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (active S).card)))
    (fun i _ => (measureReal_mono (hsub (index S i)) (hfin (index S i))).trans (hupper _))
  simpa only [compressed,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh

end
end KakeyaFormal.MeasurableAngularGroups
