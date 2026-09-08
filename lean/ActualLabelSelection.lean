import LegalSampleSelection
import LegalOutputDirections

/-! Actual geometric samples produce a whole-edge most-frequent-second-tube
selection and one exact dyadic-size sample fiber per distinct retained output.
No geometric label-count or collision-count premise is assumed. -/
namespace KakeyaFormal.ActualLabelSelection
open Finset LegalAngleSamples LegalSampleOutputs LegalSampleSelection TransverseAngles
open AngleFiberSelection LegalOutputDirections ProjectiveGeometry
open scoped BigOperators
noncomputable section
open Classical

/-- The proved actual original-second-index budget, rounded upward once. -/
def labelBudget (k : ℕ) (width kappa : ℝ) : ℕ :=
  Nat.ceil (packingConstant k*(4*roundingConstant (k+1) width*(1+2*width)/kappa^2)^k)

theorem labelBudget_pos (k : ℕ) {width kappa : ℝ} (hw : 0 ≤ width) (hk : 0 < kappa) :
    0 < labelBudget k width kappa := by
  have hP := packingConstant_ge_one k
  have hC := roundingConstant_ge_one (k+1) hw
  unfold labelBudget
  apply Nat.ceil_pos.mpr
  positivity

/-- A constructed selection retains the actual angle/output edges, their
whole most-frequent second-tube classes, and exact original-label samples. -/
structure Selection {k M : ℕ} {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) where
  level : ℕ
  source : Finset (↥(angles F H kappa) × (Cell (k+1) × Cell (k+1)))
  retained : Finset (↥(angles F H kappa) × (Cell (k+1) × Cell (k+1)))
  level_upper : level ≤ Nat.log 2 (fiberBudget (k+1) width kappa δ)
  source_eq : source =
    (goodEdges univ S.samples (fun a => output S a hkappa hwidth hadm) (cutoff (k+1) width lam δ)).filter
      (fun e => 2^level ≤ size S.samples (fun a => output S a hkappa hwidth hadm) e ∧
        size S.samples (fun a => output S a hkappa hwidth hadm) e < 2*(2^level))
  source_nonempty : source.Nonempty
  retained_nonempty : retained.Nonempty
  retained_subset_source : retained ⊆ source
  source_subset_actual : source ⊆ edges univ S.samples (fun a => output S a hkappa hwidth hadm)
  retained_subset_actual : retained ⊆ edges univ S.samples (fun a => output S a hkappa hwidth hadm)
  same_support : outputSupport retained = outputSupport source
  dyadic_pos : 1 ≤ (2^level:ℕ)
  dyadic_lower : cutoff (k+1) width lam δ/2 < (2^level:ℕ)
  dyadic_upper : (2^level:ℕ) ≤ fiberBudget (k+1) width kappa δ
  sample_mass_lower :
    sampleBudget lam δ*((angles F H kappa).card:ℝ)/(2*(Nat.log 2 (fiberBudget (k+1) width kappa δ)+1:ℕ)) ≤
      ∑ e ∈ source, (size S.samples (fun a => output S a hkappa hwidth hadm) e:ℝ)
  source_count_lower :
    sampleBudget lam δ*((angles F H kappa).card:ℝ)/
      (4*(2^level:ℕ)*(Nat.log 2 (fiberBudget (k+1) width kappa δ)+1:ℕ)) ≤ (source.card:ℝ)
  integer_retention : source.card ≤ labelBudget k width kappa*retained.card
  retained_count_lower :
    sampleBudget lam δ*((angles F H kappa).card:ℝ)/
      (4*(2^level:ℕ)*(Nat.log 2 (fiberBudget (k+1) width kappa δ)+1:ℕ)*labelBudget k width kappa) ≤
      (retained.card:ℝ)
  same_second : ∀ e ∈ retained, ∀ e' ∈ retained, e.2=e'.2 → e.1.val.2.2=e'.1.val.2.2
  whole_label_class : ∀ e ∈ retained, ∀ e' ∈ source,
    e'.2=e.2 → e'.1.val.2.2=e.1.val.2.2 → e' ∈ retained
  maximal_label_class : ∀ f, ∀ l : Fin M,
    ((outputEdges source f).filter (fun e => e.1.val.2.2=l)).card ≤ (outputEdges retained f).card
  support_of_energy : ∀ E : ℝ, 0 < E → collisionEnergy retained ≤ E →
    (sampleBudget lam δ*((angles F H kappa).card:ℝ)/
      (4*(2^level:ℕ)*(Nat.log 2 (fiberBudget (k+1) width kappa δ)+1:ℕ)*labelBudget k width kappa))^2/E ≤
      ((outputSupport retained).card:ℝ)
  chosen_output : Fin (outputSupport retained).card → Cell (k+1) × Cell (k+1)
  chosen_angle : Fin (outputSupport retained).card → ↥(angles F H kappa)
  chosen_samples : Fin (outputSupport retained).card → Finset (Triple (k+1))
  chosen_output_injective : Function.Injective chosen_output
  chosen_output_cover : univ.image chosen_output = outputSupport retained
  chosen_fiber : ∀ i, (chosen_angle i,chosen_output i) ∈ retained ∧
    chosen_samples i ⊆ fiber S.samples (fun a => output S a hkappa hwidth hadm) (chosen_angle i) (chosen_output i) ∧
    (chosen_samples i).card = 2^level
  chosen_mass : (∑ i, (chosen_samples i).card) = (2^level)*(outputSupport retained).card

/-- All scalar budgets and geometric label counts are instantiated by proved
facts about the actual family. The selection choices are then constructed by
the finite theorem, including exact representatives from just one angle per output. -/
theorem construct {k M : ℕ} {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (hA : (angles F H kappa).Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1) (hwidth : 0 ≤ width)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam) (hsep : F.Separated δ) :
    Nonempty (Selection S hkappa hwidth hadm) := by
  have hA' : (univ : Finset ↥(angles F H kappa)).Nonempty := by
    obtain ⟨a,ha⟩ := hA
    exact ⟨⟨a,ha⟩,mem_univ _⟩
  have hmu : 0 < sampleBudget lam δ := by dsimp [sampleBudget]; positivity
  have ht : 0 ≤ cutoff (k+1) width lam δ := by
    have := outputConstant_pos (k+1) hwidth
    dsimp [cutoff]
    positivity
  have hsamples : ∀ a ∈ (univ : Finset ↥(angles F H kappa)),
      sampleBudget lam δ ≤ ((S.samples a).card:ℝ) := fun a _ => S.card_lower a
  have houtputs : ∀ a ∈ (univ : Finset ↥(angles F H kappa)),
      ((outputs S.samples (fun a => output S a hkappa hwidth hadm) a).card:ℝ) ≤
        outputBudget (k+1) width lam δ := by
    intro a _
    have hh := density_output_count S a hδ hδ1 hkappa hwidth hadm hcomp
    unfold AngleFiberSelection.outputs outputBudget
    convert hh using 1
    congr 3
    exact Subsingleton.elim _ _
  have hfiber : ∀ e ∈ edges univ S.samples (fun a => output S a hkappa hwidth hadm),
      size S.samples (fun a => output S a hkappa hwidth hadm) e ≤ fiberBudget (k+1) width kappa δ := by
    intro e _
    simpa only [size,fiber,fiberBudget] using
      integer_fiber_count S e.1 e.2 hδ hδ1 hkappa hkappa1 hwidth hadm
  have hlabels : ∀ f, ((outputEdges (edges univ S.samples (fun a => output S a hkappa hwidth hadm)) f).image
      (fun e => e.1.val.2.2)).card ≤ labelBudget k width kappa := by
    intro f
    exact second_indices_integer_count S hδ hkappa hkappa1 hwidth hadm hsep f
  obtain ⟨j,hj,Ω,Ωstar,hΩ,hΩne,hstarne,hstarsub,hsupport,hpos,hlo,hhi,hmass,hedges,
    hnat,hretained,hconstant,hwhole,hmax,henergy,f,a,R,hfinj,hcover,hfiberR,hRmass⟩ :=
    select_angle_fibers univ S.samples (fun a => output S a hkappa hwidth hadm)
      (fun a => a.val.2.2) hA' hmu ht (labelBudget_pos k hwidth hkappa)
      hsamples houtputs (cutoff_calibration hwidth hδ).le hfiber (by
        intro f
        convert hlabels f using 1
        congr 2
        exact Subsingleton.elim _ _)
  have hΩsub : Ω ⊆ edges univ S.samples (fun a => output S a hkappa hwidth hadm) := by
    rw [hΩ]
    exact (filter_subset _ _).trans (filter_subset _ _)
  refine ⟨{
    level := j
    source := Ω
    retained := Ωstar
    level_upper := hj
    source_eq := hΩ
    source_nonempty := hΩne
    retained_nonempty := hstarne
    retained_subset_source := hstarsub
    source_subset_actual := hΩsub
    retained_subset_actual := hstarsub.trans hΩsub
    same_support := hsupport
    dyadic_pos := hpos
    dyadic_lower := hlo
    dyadic_upper := hhi
    sample_mass_lower := ?_
    source_count_lower := ?_
    integer_retention := hnat
    retained_count_lower := ?_
    same_second := hconstant
    whole_label_class := hwhole
    maximal_label_class := by
      intro f l
      convert hmax f l using 1
      congr 2
    support_of_energy := ?_
    chosen_output := f
    chosen_angle := a
    chosen_samples := R
    chosen_output_injective := hfinj
    chosen_output_cover := by
      convert hcover using 1
      congr 1
      exact Subsingleton.elim _ _
    chosen_fiber := fun i => (hfiberR i).2
    chosen_mass := hRmass }⟩
  · simpa only [card_univ,Fintype.card_coe] using hmass
  · simpa only [card_univ,Fintype.card_coe] using hedges
  · simpa only [card_univ,Fintype.card_coe] using hretained
  · simpa only [card_univ,Fintype.card_coe] using henergy


/-- Whole retained edges still have their original dyadic fiber sizes. -/
theorem Selection.retained_fiber_range {k M : ℕ} {F : TubeFamily (k+1) M}
    {H : Finset (Cell (k+1))} {δ lam kappa width : ℝ}
    {S : SampleSystem F H δ lam kappa width} {hkappa : 0 < kappa}
    {hwidth : 0 ≤ width} {hadm : F.Admissible width δ}
    (P : Selection S hkappa hwidth hadm)
    (e : ↥(angles F H kappa) × (Cell (k+1) × Cell (k+1))) (he : e ∈ P.retained) :
    2^P.level ≤ size S.samples (fun a => output S a hkappa hwidth hadm) e ∧
      size S.samples (fun a => output S a hkappa hwidth hadm) e < 2*(2^P.level) := by
  have hh := P.retained_subset_source he
  rw [P.source_eq] at hh
  exact (mem_filter.mp hh).2

/-- Every chosen representative is an original legal label triple producing
its own indexed output, rather than a sample taken from another incident angle. -/
theorem Selection.chosen_samples_actual {k M : ℕ} {F : TubeFamily (k+1) M}
    {H : Finset (Cell (k+1))} {δ lam kappa width : ℝ}
    {S : SampleSystem F H δ lam kappa width} {hkappa : 0 < kappa}
    {hwidth : 0 ≤ width} {hadm : F.Admissible width δ}
    (P : Selection S hkappa hwidth hadm) (i : Fin (outputSupport P.retained).card)
    (p : Triple (k+1)) (hp : p ∈ P.chosen_samples i) :
    p ∈ S.samples (P.chosen_angle i) ∧
      output S (P.chosen_angle i) hkappa hwidth hadm p=P.chosen_output i := by
  simpa only [fiber,mem_filter] using (P.chosen_fiber i).2.1 hp

end
end KakeyaFormal.ActualLabelSelection
