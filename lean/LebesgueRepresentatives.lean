import MeasurableIncidenceAtoms

/-! Finite nested shadings measurable for the completed measure admit actual
measurable subset representatives. One common almost-everywhere event identifies
all original full and marked incidence rows. No mass is lost, and the ambient
measure need not be finite or complete. -/
namespace KakeyaFormal.LebesgueRepresentatives
open MeasureTheory Set
open scoped ENNReal BigOperators
noncomputable section
open Classical

variable {X : Type*} [MeasurableSpace X] {M : ℕ}

structure Output (μ : Measure X) (Full G : Fin M → Set X) where
  full : Fin M → Set X
  marks : Fin M → Set X
  full_measurable : ∀ i, MeasurableSet (full i)
  marks_measurable : ∀ i, MeasurableSet (marks i)
  full_subset : ∀ i, full i ⊆ Full i
  marks_subset : ∀ i, marks i ⊆ G i
  nested : ∀ i, marks i ⊆ full i
  full_ae : ∀ i, full i =ᵐ[μ] Full i
  marks_ae : ∀ i, marks i =ᵐ[μ] G i

/-- Choose measurable subsets of both families and impose actual nestedness
using the SAME full representative. The intersection changes no marked mass. -/
theorem construct (μ : Measure X) (Full G : Fin M → Set X)
    (hFull : ∀ i, NullMeasurableSet (Full i) μ)
    (hG : ∀ i, NullMeasurableSet (G i) μ) (hsub : ∀ i, G i ⊆ Full i) :
    Nonempty (Output μ Full G) := by
  choose Y hYsub hYm hYae using fun i => (hFull i).exists_measurable_subset_ae_eq
  choose Z hZsub hZm hZae using fun i => (hG i).exists_measurable_subset_ae_eq
  refine ⟨{
    full := Y
    marks := fun i => Z i ∩ Y i
    full_measurable := hYm
    marks_measurable := fun i => (hZm i).inter (hYm i)
    full_subset := hYsub
    marks_subset := fun i => Set.inter_subset_left.trans (hZsub i)
    nested := fun _ => Set.inter_subset_right
    full_ae := hYae
    marks_ae := ?_ }⟩
  intro i
  simpa only [Set.inter_eq_left.mpr (hsub i)] using (hZae i).inter (hYae i)

namespace Output
variable {μ : Measure X} {Full G : Fin M → Set X} (O : Output μ Full G)

/-- All membership identities hold simultaneously outside ONE null set. -/
theorem membership : ∀ᵐ x ∂μ,
    (∀ i, x ∈ O.full i ↔ x ∈ Full i) ∧ (∀ i, x ∈ O.marks i ↔ x ∈ G i) := by
  have hF : ∀ᵐ x ∂μ, ∀ i, (x ∈ O.full i) = (x ∈ Full i) := ae_all_iff.mpr O.full_ae
  have hG : ∀ᵐ x ∂μ, ∀ i, (x ∈ O.marks i) = (x ∈ G i) := ae_all_iff.mpr O.marks_ae
  filter_upwards [hF,hG] with x hx hy
  exact ⟨fun i => iff_of_eq (hx i), fun i => iff_of_eq (hy i)⟩

theorem full_union_subset : (⋃ i, O.full i) ⊆ ⋃ i, Full i :=
  iUnion_mono O.full_subset

theorem marks_union_subset : (⋃ i, O.marks i) ⊆ ⋃ i, G i :=
  iUnion_mono O.marks_subset

theorem full_union_ae : (⋃ i, O.full i) =ᵐ[μ] ⋃ i, Full i := by
  filter_upwards [O.membership] with x hx
  apply propext
  change (x ∈ ⋃ i, O.full i) ↔ x ∈ ⋃ i, Full i
  simp only [Set.mem_iUnion]
  exact exists_congr (fun i => hx.1 i)

theorem marks_union_ae : (⋃ i, O.marks i) =ᵐ[μ] ⋃ i, G i := by
  filter_upwards [O.membership] with x hx
  apply propext
  change (x ∈ ⋃ i, O.marks i) ↔ x ∈ ⋃ i, G i
  simp only [Set.mem_iUnion]
  exact exists_congr (fun i => hx.2 i)

theorem full_measure (i : Fin M) : μ (O.full i) = μ (Full i) := measure_congr (O.full_ae i)
theorem marks_measure (i : Fin M) : μ (O.marks i) = μ (G i) := measure_congr (O.marks_ae i)
theorem full_real (i : Fin M) : μ.real (O.full i) = μ.real (Full i) := measureReal_congr (O.full_ae i)
theorem marks_real (i : Fin M) : μ.real (O.marks i) = μ.real (G i) := measureReal_congr (O.marks_ae i)

theorem full_inter_measure (i : Fin M) (E : Set X) :
    μ (O.full i ∩ E) = μ (Full i ∩ E) := measure_congr ((O.full_ae i).inter Filter.EventuallyEq.rfl)
theorem marks_inter_measure (i : Fin M) (E : Set X) :
    μ (O.marks i ∩ E) = μ (G i ∩ E) := measure_congr ((O.marks_ae i).inter Filter.EventuallyEq.rfl)
theorem full_inter_real (i : Fin M) (E : Set X) :
    μ.real (O.full i ∩ E) = μ.real (Full i ∩ E) := measureReal_congr ((O.full_ae i).inter Filter.EventuallyEq.rfl)
theorem marks_inter_real (i : Fin M) (E : Set X) :
    μ.real (O.marks i ∩ E) = μ.real (G i ∩ E) := measureReal_congr ((O.marks_ae i).inter Filter.EventuallyEq.rfl)

theorem full_union_measure : μ (⋃ i, O.full i) = μ (⋃ i, Full i) := measure_congr O.full_union_ae
theorem marks_union_measure : μ (⋃ i, O.marks i) = μ (⋃ i, G i) := measure_congr O.marks_union_ae
theorem full_union_real : μ.real (⋃ i, O.full i) = μ.real (⋃ i, Full i) := measureReal_congr O.full_union_ae
theorem marks_union_real : μ.real (⋃ i, O.marks i) = μ.real (⋃ i, G i) := measureReal_congr O.marks_union_ae

theorem full_total_real : (∑ i, μ.real (O.full i)) = ∑ i, μ.real (Full i) :=
  Finset.sum_congr rfl (fun i _ => O.full_real i)
theorem marks_total_real : (∑ i, μ.real (O.marks i)) = ∑ i, μ.real (G i) :=
  Finset.sum_congr rfl (fun i _ => O.marks_real i)

/-- The original finite incidence rows are identical almost everywhere, not
merely bounded by each other. Hence any old pointwise cap test transfers. -/
theorem rows_ae : ∀ᵐ x ∂μ,
    MeasurableIncidenceAtoms.pattern O.full x = MeasurableIncidenceAtoms.pattern Full x ∧
    MeasurableIncidenceAtoms.pattern O.marks x = MeasurableIncidenceAtoms.pattern G x := by
  filter_upwards [O.membership] with x hx
  constructor
  · ext i
    simp only [MeasurableIncidenceAtoms.mem_pattern]
    exact hx.1 i
  · ext i
    simp only [MeasurableIncidenceAtoms.mem_pattern]
    exact hx.2 i

/-- Transfer an arbitrary a.e. statement about BOTH full and marked rows;
this includes all angular centers and radii at once. -/
theorem transfer_ae (P : X → Finset (Fin M) → Finset (Fin M) → Prop)
    (hP : ∀ᵐ x ∂μ, P x (MeasurableIncidenceAtoms.pattern Full x) (MeasurableIncidenceAtoms.pattern G x)) :
    ∀ᵐ x ∂μ, P x (MeasurableIncidenceAtoms.pattern O.full x) (MeasurableIncidenceAtoms.pattern O.marks x) := by
  filter_upwards [O.rows_ae,hP] with x hx hp
  rwa [hx.1,hx.2]

end Output
end
end KakeyaFormal.LebesgueRepresentatives
