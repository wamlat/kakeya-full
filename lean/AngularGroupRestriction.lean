import AngularAssignment

/-! Actual compression of each assigned angular group to its participating
nonempty original tube indices. Counts and incidence patterns are exact. -/
namespace KakeyaFormal.AngularGroupRestriction
open AngularDecomposition AngularAssignment AngularIncidence
noncomputable section
open Classical

/-- Original indices actually present in one finite shading group. -/
def active {α : Type*} {M : ℕ} (S : Fin M → Finset α) : Finset (Fin M) :=
  Finset.univ.filter (fun i => (S i).Nonempty)

/-- Explicit finite enumeration of those actual original indices. -/
def index {α : Type*} {M : ℕ} (S : Fin M → Finset α) (i : Fin (active S).card) : Fin M :=
  (active S).equivFin.symm i

theorem index_injective {α : Type*} {M : ℕ} (S : Fin M → Finset α) :
    Function.Injective (index S) := Subtype.val_injective.comp (active S).equivFin.symm.injective

theorem index_mem {α : Type*} {M : ℕ} (S : Fin M → Finset α) (i : Fin (active S).card) :
    index S i ∈ active S := ((active S).equivFin.symm i).2

theorem index_nonempty {α : Type*} {M : ℕ} (S : Fin M → Finset α) (i : Fin (active S).card) :
    (S (index S i)).Nonempty := (Finset.mem_filter.mp (index_mem S i)).2

theorem index_surjective_on {α : Type*} {M : ℕ} (S : Fin M → Finset α) {i : Fin M}
    (hi : i ∈ active S) : ∃ j : Fin (active S).card, index S j = i := by
  refine ⟨(active S).equivFin ⟨i,hi⟩,?_⟩
  simp [index]

/-- The compressed family has exactly those tubes and actual group shadings. -/
def family {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Finset (Cell k)) :
    TubeFamily k (active S).card where
  tube i := F.tube (index S i)
  shade i := S (index S i)

/-- Exact sum preservation under finite reindexing. -/
theorem reindexed_sum {α : Type*} {M : ℕ} (S : Fin M → Finset α) (w : Fin M → ℝ) :
    (∑ i : Fin (active S).card, w (index S i)) = ∑ i ∈ active S, w i := by
  have h₁ := (active S).equivFin.symm.sum_comp (fun i : active S => w i.1)
  have h₂ : (∑ i ∈ active S, w i) = ∑ i : active S, w i.1 :=
    Finset.sum_subtype (active S) (fun _ => Iff.rfl) w
  exact h₁.trans h₂.symm

/-- Excluded indices have empty shadings, so no incidence mass is lost. -/
theorem mass_eq {α : Type*} {M : ℕ} (S : Fin M → Finset α) :
    (∑ i : Fin (active S).card, ((S (index S i)).card:ℝ)) = ∑ i : Fin M, ((S i).card:ℝ) := by
  rw [reindexed_sum S (fun i => ((S i).card:ℝ))]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hnone : ¬(S i).Nonempty := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i,h⟩)
  simp only [Finset.not_nonempty_iff_eq_empty.mp hnone,Finset.card_empty,Nat.cast_zero]

/-- Every occupied predicate supported in the active set has exactly the same
cardinality under the actual reindexing. -/
theorem filter_card_eq {α : Type*} {M : ℕ} (S : Fin M → Finset α) (P : Fin M → Prop)
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

/-- Full pointwise cell incidence is unchanged by compression. -/
theorem pointwise_card {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Finset (Cell k))
    (z : Cell k) :
    (Finset.univ.filter (fun i => z ∈ (family F S).shade i)).card =
      (Finset.univ.filter (fun i => z ∈ S i)).card := by
  convert filter_card_eq S (fun i => z ∈ S i)
    (fun i hi => Finset.mem_filter.mpr ⟨Finset.mem_univ i,⟨z,hi⟩⟩) using 1 <;> congr

/-- Actual broadness is preserved with precisely the same coefficient. -/
theorem family_broad {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Finset (Cell k))
    {δ beta tau K : ℝ}
    (hbroad : ∀ z, Broad F (Finset.univ.filter (fun i => z ∈ S i)) δ beta tau K) :
    ∀ z, Broad (family F S) (Finset.univ.filter (fun i => z ∈ (family F S).shade i)) δ beta tau K := by
  intro z center r hr
  have hcard : (cap (family F S) (Finset.univ.filter (fun i => z ∈ (family F S).shade i)) center r).card ≤
      (cap F (Finset.univ.filter (fun i => z ∈ S i)) center r).card := by
    apply Finset.card_le_card_of_injOn (index S)
    · intro i hi
      obtain ⟨hiP,hiAngle⟩ := Finset.mem_filter.mp hi
      obtain ⟨_,hiZ⟩ := Finset.mem_filter.mp hiP
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hiZ⟩,hiAngle⟩
    · exact fun i _ j _ hij => index_injective S hij
  have hpop := pointwise_card F S z
  calc
    _ ≤ ((cap F (Finset.univ.filter (fun i => z ∈ S i)) center r).card:ℝ) := Nat.cast_le.mpr hcard
    _ ≤ K*(r/tau)^beta*((Finset.univ.filter (fun i => z ∈ S i)).card:ℝ) := hbroad z center r hr
    _ = _ := by rw [hpop]

/-- Admissibility passes from original finite tube shadings to their actual restrictions. -/
theorem family_admissible {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Finset (Cell k))
    {width δ : ℝ} (hsub : ∀ i, S i ⊆ F.shade i) (hadm : F.Admissible width δ) :
    (family F S).Admissible width δ := fun i z hz => hadm (index S i) z (hsub _ hz)

theorem family_separated {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Finset (Cell k))
    {δ : ℝ} (hsep : F.Separated δ) : (family F S).Separated δ := by
  intro i j hij
  exact hsep _ _ (fun he => hij (index_injective S he))

theorem family_cap_bound {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Finset (Cell k))
    {δ m A : ℝ} (hcap : F.CapBound δ m A) : (family F S).CapBound δ m A := by
  intro center hunit r hr hr1
  have hcard : (Finset.univ.filter (fun i =>
      projectiveDistance ((family F S).tube i).direction center ≤ r)).card ≤
      (Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction center ≤ r)).card := by
    apply Finset.card_le_card_of_injOn (index S)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · exact fun i _ j _ hij => index_injective S hij
  exact (Nat.cast_le.mpr hcard).trans (hcap center hunit r hr hr1)

/-- The local cap premise now holds for every compressed tube, not merely the
nonempty indices of a larger family. -/
theorem family_local_cap {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Finset (Cell k))
    (u : Space k) {r : ℝ} (hcap : ∀ i, (S i).Nonempty → projectiveDistance (F.tube i).direction u ≤ r) :
    ∀ i, projectiveDistance ((family F S).tube i).direction u ≤ r :=
  fun i => hcap _ (index_nonempty S i)

/-- A per-original-tube mass upper bound remains uniform in every compressed group. -/
theorem mass_upper {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Finset (Cell k))
    {U : ℝ} (hsub : ∀ i, S i ⊆ F.shade i) (hupper : ∀ i, ((F.shade i).card:ℝ) ≤ U) :
    (∑ i, (((family F S).shade i).card:ℝ)) ≤ U*((active S).card:ℝ) := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (active S).card)))
    (fun i _ => (Nat.cast_le.mpr (Finset.card_le_card (hsub (index S i)))).trans (hupper _))
  simpa only [family,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hsum

/-- One assignment per original tube gives genuinely disjoint active index sets. -/
theorem active_disjoint {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (S : γ → Fin M → Finset α) (assign : Fin M → γ)
    (hunique : ∀ g i, (S g i).Nonempty → assign i = g) {g h : γ} (hgh : g ≠ h) :
    Disjoint (active (S g)) (active (S h)) := by
  apply Finset.disjoint_left.mpr
  intro i hig hih
  have h1 := hunique g i (Finset.mem_filter.mp hig).2
  have h2 := hunique h i (Finset.mem_filter.mp hih).2
  exact hgh (h1.symm.trans h2)

/-- Exact total active tube count is at most the original population. -/
theorem total_active_count {α γ : Type*} [DecidableEq γ] {M : ℕ}
    (groups : Finset γ) (S : γ → Fin M → Finset α) (assign : Fin M → γ)
    (hunique : ∀ g i, (S g i).Nonempty → assign i = g) :
    (∑ g ∈ groups, (active (S g)).card) ≤ M := by
  have hdis : (↑groups : Set γ).PairwiseDisjoint (fun g => active (S g)) :=
    fun _ _ _ _ hne => active_disjoint S assign hunique hne
  rw [← Finset.card_biUnion hdis]
  exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)

/-- Each original cell occurs in a compressed group exactly when it occurred
in that group before reindexing. -/
theorem occupied_iff {k M : ℕ} (F : TubeFamily k M) (S : Fin M → Finset (Cell k)) (z : Cell k) :
    (∃ i, z ∈ (family F S).shade i) ↔ ∃ i, z ∈ S i := by
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨index S i,hi⟩
  · rintro ⟨i,hi⟩
    obtain ⟨j,rfl⟩ := index_surjective_on S (Finset.mem_filter.mpr ⟨Finset.mem_univ i,⟨z,hi⟩⟩)
    exact ⟨j,hi⟩

/-- Pointwise overlap of actual group unions is unchanged. -/
theorem group_overlap {γ : Type*} [DecidableEq γ] {k M : ℕ} (F : TubeFamily k M)
    (groups : Finset γ) (S : γ → Fin M → Finset (Cell k)) (z : Cell k) :
    (groups.filter (fun g => ∃ i, z ∈ (family F (S g)).shade i)).card =
      (groups.filter (fun g => ∃ i, z ∈ S g i)).card := by
  congr 1
  ext g
  simp only [Finset.mem_filter,occupied_iff]

/-- The original full-union incidence sum is the exact sum of tube shading sizes. -/
theorem incidenceMass_union {k M : ℕ} (F : TubeFamily k M) :
    incidenceMass F F.unionCells = ∑ i, ((F.shade i).card:ℝ) := by
  have hrow := sum_row_cards F.unionCells (incident F)
  have hfilter (i : Fin M) : F.unionCells.filter (fun z => i ∈ incident F z) = F.shade i := by
    ext z
    simp only [Finset.mem_filter,mem_incident]
    exact ⟨fun h => h.2,fun h => ⟨F.shade_subset_union i h,h⟩⟩
  simp_rw [hfilter] at hrow
  unfold incidenceMass
  exact_mod_cast hrow

end
end KakeyaFormal.AngularGroupRestriction
