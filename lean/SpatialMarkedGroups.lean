import ActualSpatialMarked

/-! Retain every sufficiently marked spatial fiber. The density of each full
shading is unchanged, and the mass/count losses are fixed fractions, not the
number of spatial boxes. -/
namespace KakeyaFormal.SpatialMarkedGroups
open Finset MeasureTheory SpatialMarkedPartition
open scoped BigOperators ENNReal
noncomputable section
open Classical

variable {X : Type*} [MeasurableSpace X] {M : ℕ} {γ : Type*} [DecidableEq γ]

def markedMass (ν : Measure X) (G : Fin M → Set X) (label : Fin M → γ) (B : ℝ) (q : γ) : ℝ :=
  ∑ i, ν.real (Marks G label B q i)

def good (ν : Measure X) (G : Fin M → Set X) (label : Fin M → γ) (B eta lam : ℝ) : Finset γ :=
  (labels label).filter (fun q => eta*lam*((indices label q).card:ℝ)/4 ≤ markedMass ν G label B q)

/-- A genuine original spatial label always has a nonempty tube fiber. -/
theorem population_pos (label : Fin M → γ) (q : γ) (hq : q ∈ labels label) :
    0 < (indices label q).card := by
  obtain ⟨i,_,hi⟩ := mem_image.mp hq
  exact card_pos.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩

/-- The good boxes carry a fixed marked fraction with respect to their
original per-tube full mass scale. -/
theorem group_mass (ν : Measure X) (G : Fin M → Set X) (label : Fin M → γ)
    (B eta lam : ℝ) (q : γ) (hq : q ∈ good ν G label B eta lam) :
    (eta/4)*lam*((indices label q).card:ℝ) ≤ markedMass ν G label B q := by
  have hh := (mem_filter.mp hq).2
  convert hh using 1; ring

/-- Summing ALL insufficient boxes costs at most one quarter of the original
marked budget. No single spatial box is selected. -/
theorem retained_mass (ν : Measure X) (G : Fin M → Set X) (label : Fin M → γ)
    {B eta lam : ℝ} (heta : 0 ≤ eta) (hlam : 0 ≤ lam)
    (hmass : (3/4:ℝ)*(eta*lam*(M:ℝ)) ≤ ∑ q ∈ labels label, markedMass ν G label B q) :
    eta*lam*(M:ℝ)/2 ≤ ∑ q ∈ good ν G label B eta lam, markedMass ν G label B q := by
  let bad := (labels label).filter (fun q => ¬eta*lam*((indices label q).card:ℝ)/4 ≤ markedMass ν G label B q)
  have hbad : (∑ q ∈ bad, markedMass ν G label B q) ≤ eta*lam*(M:ℝ)/4 := by
    calc
      _ ≤ ∑ q ∈ bad, eta*lam*((indices label q).card:ℝ)/4 :=
        sum_le_sum (fun q hq => (lt_of_not_ge (mem_filter.mp hq).2).le)
      _ = (eta*lam/4)*(∑ q ∈ bad, ((indices label q).card:ℝ)) := by rw [mul_sum]; congr 1; ext q; ring
      _ ≤ (eta*lam/4)*(∑ q ∈ labels label, ((indices label q).card:ℝ)) :=
        mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)) (by positivity)
      _ = eta*lam*(M:ℝ)/4 := by
        rw [← Nat.cast_sum,population_partition]
        ring
  have hsplit := sum_filter_add_sum_filter_not (s:=labels label)
    (fun q => eta*lam*((indices label q).card:ℝ)/4 ≤ markedMass ν G label B q)
    (markedMass ν G label B)
  change (∑ q ∈ good ν G label B eta lam, markedMass ν G label B q)+
    (∑ q ∈ bad, markedMass ν G label B q)=_ at hsplit
  linarith

/-- Original full upper density bounds every actual spatial marked mass. -/
theorem marked_mass_upper (ν : Measure X) (Y G : Fin M → Set X) (label : Fin M → γ)
    (B : ℝ) {lam : ℝ} (hsub : ∀ i, G i ⊆ Y i)
    (hf : ∀ i, ν (Y i) ≠ ∞) (hupper : ∀ i, ν.real (Y i) ≤ 2*lam) (q : γ) :
    markedMass ν G label B q ≤ 2*lam*((indices label q).card:ℝ) := by
  calc
    _ ≤ ∑ i, (2*lam) := sum_le_sum (fun i _ =>
      (measureReal_mono (marks_subset_full Y G label B q hsub i) (hf _)).trans (hupper _))
    _ = _ := by simp [mul_comm]

/-- The retained spatial fibers carry a fixed fraction of the original tube
population, summed across every good box. -/
theorem retained_population (ν : Measure X) (Y G : Fin M → Set X) (label : Fin M → γ)
    {B eta lam : ℝ} (heta : 0 ≤ eta) (hlam : 0 < lam)
    (hsub : ∀ i, G i ⊆ Y i) (hf : ∀ i, ν (Y i) ≠ ∞) (hupper : ∀ i, ν.real (Y i) ≤ 2*lam)
    (hmass : (3/4:ℝ)*(eta*lam*(M:ℝ)) ≤ ∑ q ∈ labels label, markedMass ν G label B q) :
    eta*(M:ℝ)/4 ≤ ∑ q ∈ good ν G label B eta lam, ((indices label q).card:ℝ) := by
  have hl := retained_mass ν G label heta hlam.le hmass
  have hu : (∑ q ∈ good ν G label B eta lam, markedMass ν G label B q) ≤
      2*lam*(∑ q ∈ good ν G label B eta lam, ((indices label q).card:ℝ)) := by
    rw [mul_sum]
    exact sum_le_sum (fun q _ => marked_mass_upper ν Y G label B hsub hf hupper q)
  apply le_of_mul_le_mul_left (a:=lam) _ hlam
  nlinarith

/-- Each retained group has a quantitative marked/full fraction; no
individual-tube marked lower bound is added. -/
theorem group_fraction (ν : Measure X) (Y G : Fin M → Set X) (label : Fin M → γ)
    {B eta lam : ℝ} (heta : 0 ≤ eta) (hupper : ∀ i, ν.real (Y i) ≤ 2*lam)
    (q : γ) (hq : q ∈ good ν G label B eta lam) :
    (eta/8)*(∑ i, ν.real (Full Y label q i)) ≤ markedMass ν G label B q := by
  have hu : (∑ i, ν.real (Full Y label q i)) ≤ 2*lam*((indices label q).card:ℝ) :=
    (sum_le_sum (fun i _ => hupper (MeasurableMarkedSelection.index (indices label q) i))).trans_eq (by simp [mul_comm])
  have hh := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ eta/8)
  have heq : (eta/8)*(2*lam*((indices label q).card:ℝ)) = eta*lam*((indices label q).card:ℝ)/4 := by ring
  exact hh.trans (heq.le.trans (mem_filter.mp hq).2)

/-- Construct the actual sufficiently marked spatial groups from one original
measurable angular piece. All retained groups are kept, their total population
and marks obey fixed losses, and their common boxes follow from actual bases.
The original Full sets are unchanged on each injective group index. -/
theorem construct {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (Y G : Fin M → Set (Space (k+1))) {δ tau width angular R eta lam beta K : ℝ}
    (hu : ‖u‖=1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (hδ1 : δ ≤ 1)
    (hw : 0 ≤ width) (ha : 0 ≤ angular) (hbounded : F.Bounded R)
    (heta : 0 < eta) (hlam : 0 < lam) (hK : 0 ≤ K) (hM : 0 < M)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcarrier : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ))
    (hsub : ∀ i, G i ⊆ Y i) (hG : ∀ i, MeasurableSet (G i))
    (hupper : ∀ i, (volume : Measure (Space (k+1))).real (Y i) ≤ 2*lam)
    (hmass : eta*lam*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+1))).real (G i))
    (hbroad : ∀ x, AngularDecomposition.Broad F (univ.filter (fun i => x ∈ G i)) δ beta tau K) :
    let lab := ActualSpatialMarked.label F u tau
    let C : ℝ := ActualSpatialMarked.overlapConstant k width angular
    let Q := good volume G lab C eta lam
    Q.Nonempty ∧
      eta*(M:ℝ)/4 ≤ ∑ q ∈ Q, ((indices lab q).card:ℝ) ∧
      eta*lam*(M:ℝ)/2 ≤ ∑ q ∈ Q, markedMass volume G lab C q ∧
      (∀ q ∈ Q, 0 < (indices lab q).card ∧
        (eta/4)*lam*((indices lab q).card:ℝ) ≤ markedMass volume G lab C q ∧
        (eta/8)*(∑ i, (volume : Measure (Space (k+1))).real (Full Y lab q i)) ≤ markedMass volume G lab C q ∧
        (∀ i, Marks G lab C q i ⊆ Full Y lab q i) ∧
        (∀ i, ((SpatialMarkedPartition.family F lab q).tube i).base ∈
          SpatialAngular.parallelBox u tau q (R+1+width) ((k:ℝ)+width+angular)) ∧
        (∀ x, AngularDecomposition.Broad (SpatialMarkedPartition.family F lab q)
          (univ.filter (fun i => x ∈ Marks G lab C q i)) δ beta tau (K*(4*C))) ∧
        (⋃ i, Full Y lab q i) ⊆ ⋃ i, Y i) := by
  intro lab C Q
  have htau : 0 < tau := hδ.trans_le hδtau
  have hf (i) : volume (Y i) ≠ ∞ := measure_ne_top_of_subset (hcarrier i) (TubeVolume.carrier_finite _ _)
  have hret := ActualSpatialMarked.marked_mass F u Y G hu htau hδtau hw ha hlocal hcarrier hsub hG
  have hbudget : (3/4:ℝ)*(eta*lam*(M:ℝ)) ≤ ∑ q ∈ labels lab, markedMass volume G lab C q :=
    (mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ)≤3/4)).trans hret
  have hpop := retained_population volume Y G lab heta.le hlam hsub hf hupper hbudget
  have hmarked := retained_mass volume G lab heta.le hlam.le hbudget
  have hQ : Q.Nonempty := by
    by_contra hn
    have hz : Q=∅ := not_nonempty_iff_eq_empty.mp hn
    change eta*(M:ℝ)/4 ≤ ∑ q ∈ Q, ((indices lab q).card:ℝ) at hpop
    rw [hz,sum_empty] at hpop
    exact (by positivity : 0 < eta*(M:ℝ)/4).not_ge hpop
  refine ⟨hQ,hpop,hmarked,?_⟩
  intro q hq
  refine ⟨population_pos lab q (mem_filter.mp hq).1,group_mass volume G lab C eta lam q hq,
    group_fraction volume Y G lab heta.le hupper q hq,
    marks_subset_full Y G lab C q hsub,?_,?_,full_union_subset Y lab q⟩
  · exact ActualSpatialMarked.common_base_box F u hu hδ htau hδtau hδ1 hw ha hbounded hlocal q
  · exact SpatialMarkedPartition.marked_broad F G lab C q hδ.le htau hK hbroad

end
end KakeyaFormal.SpatialMarkedGroups
