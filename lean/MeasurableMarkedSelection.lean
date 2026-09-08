import MeasurableDensityRecovery
import ScaleChoice
import OccupancySelection

/-! Measurable full-density classes selected by marked mass. Every tube and
mark is an actual restriction of the supplied sets. Proportional marking is
proved by integrating finite multiplicities, not assumed to survive thinning. -/
namespace KakeyaFormal.MeasurableMarkedSelection
open Finset MeasureTheory MeasurableEnergy HairbrushSelection HairbrushKernel
open scoped ENNReal BigOperators
noncomputable section
open Classical

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {M : ℕ}

def index (T : Finset (Fin M)) (i : Fin T.card) : Fin M := (T.equivFin.symm i).val

def reindex (Y : Fin M → Set X) (T : Finset (Fin M)) : Fin T.card → Set X :=
  fun i => Y (index T i)

def keep (Ref O : Fin M → Set X) (T : Finset (Fin M)) (L : ℝ) : Set X :=
  {x | multiplicity Ref x ≤ L*multiplicity (reindex O T) x}

def marks (Ref O : Fin M → Set X) (T : Finset (Fin M)) (L : ℝ) : Fin T.card → Set X :=
  fun i => reindex O T i ∩ keep Ref O T L

theorem index_injective (T : Finset (Fin M)) : Function.Injective (index T) :=
  Subtype.val_injective.comp T.equivFin.symm.injective

theorem index_mem (T : Finset (Fin M)) (i : Fin T.card) : index T i ∈ T :=
  (T.equivFin.symm i).property

theorem reindex_mass (Y : Fin M → Set X) (T : Finset (Fin M)) :
    (∑ i, ν.real (reindex Y T i)) = ∑ i ∈ T, ν.real (Y i) := by
  have h₁ := T.equivFin.symm.sum_comp (fun i : T => ν.real (Y i.val))
  have h₂ : (∑ i ∈ T, ν.real (Y i)) = ∑ i : T, ν.real (Y i.val) :=
    sum_subtype T (fun _ => Iff.rfl) (fun i => ν.real (Y i))
  exact h₁.trans h₂.symm

theorem keep_measurable (Ref O : Fin M → Set X) (T : Finset (Fin M)) (L : ℝ)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hO : ∀ i, MeasurableSet (O i)) :
    MeasurableSet (keep Ref O T L) :=
  measurableSet_le (multiplicity_measurable Ref hRef)
    ((multiplicity_measurable (reindex O T) (fun i => hO (index T i))).const_mul L)

theorem marks_measurable (Ref O : Fin M → Set X) (T : Finset (Fin M)) (L : ℝ)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hO : ∀ i, MeasurableSet (O i)) :
    ∀ i, MeasurableSet (marks Ref O T L i) :=
  fun i => (hO (index T i)).inter (keep_measurable Ref O T L hRef hO)

omit [MeasurableSpace X] in
/-- Pointwise discarded marked incidences are paid for by the complete reference
population. This comparison uses every original reference index. -/
theorem discarded_pointwise (Ref O : Fin M → Set X) (T : Finset (Fin M)) (L : ℝ) (x : X) :
    L*multiplicity (fun i => reindex O T i \ keep Ref O T L) x ≤ multiplicity Ref x := by
  by_cases hx : x ∈ keep Ref O T L
  · have hz : multiplicity (fun i => reindex O T i \ keep Ref O T L) x = 0 := by
      simp [MeasurableEnergy.multiplicity,oneIndicator,hx]
    rw [hz,mul_zero]
    exact MeasurableDensityRecovery.multiplicity_nonneg Ref x
  · have hid : multiplicity (fun i => reindex O T i \ keep Ref O T L) x =
        multiplicity (reindex O T) x := by
      simp [MeasurableEnergy.multiplicity,oneIndicator,Set.indicator_apply,hx]
    rw [hid]
    exact (lt_of_not_ge hx).le

/-- The actual proportional mark retains at least half the chosen mass. -/
theorem marks_mass_lower (Ref O : Fin M → Set X) (T : Finset (Fin M)) {L : ℝ}
    (hL : 0 < L) (hRef : ∀ i, MeasurableSet (Ref i)) (hO : ∀ i, MeasurableSet (O i))
    (hReff : ∀ i, ν (Ref i) ≠ ∞) (hOf : ∀ i, ν (O i) ≠ ∞)
    (hbudget : 2*(∑ i, ν.real (Ref i)) ≤ L*(∑ i ∈ T, ν.real (O i))) :
    (∑ i ∈ T, ν.real (O i))/2 ≤ ∑ i, ν.real (marks Ref O T L i) := by
  have hkeep := keep_measurable Ref O T L hRef hO
  have hbad (i) : MeasurableSet (reindex O T i \ keep Ref O T L) := (hO _).diff hkeep
  have hbadf (i) : ν (reindex O T i \ keep Ref O T L) ≠ ∞ :=
    measure_ne_top_of_subset Set.sdiff_subset (hOf _)
  have hh := integral_mono
    ((memLp_one_iff_integrable.mp (multiplicity_memLp _ hbad hbadf 1)).const_mul L)
    (memLp_one_iff_integrable.mp (multiplicity_memLp Ref hRef hReff 1))
    (discarded_pointwise Ref O T L)
  rw [integral_const_mul,multiplicity_integral _ hbad hbadf,multiplicity_integral Ref hRef hReff] at hh
  have hsplit : (∑ i, ν.real (reindex O T i \ keep Ref O T L))+
      (∑ i, ν.real (marks Ref O T L i)) = ∑ i ∈ T, ν.real (O i) := by
    rw [← reindex_mass O T,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    exact measureReal_sdiff_add_inter hkeep (hOf _)
  nlinarith

def family {k : ℕ} (F : TubeFamily k M) (T : Finset (Fin M)) : TubeFamily k T.card where
  tube i := F.tube (index T i)
  shade i := F.shade (index T i)

/-- The retained marked row is broad at every point, including empty rows.
The complete reference broadness is transferred through an actual injective
original-index map and the explicit measurable proportional mark. -/
theorem marks_broad {k : ℕ} (F : TubeFamily k M) (Ref O : Fin M → Set (Space k))
    (T : Finset (Fin M)) {δ beta K L : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hORef : ∀ i, O i ⊆ Ref i) (hbroad : PointwiseBroad F Ref Set.univ δ beta K) :
    PointwiseBroad (family F T) (marks Ref O T L) Set.univ δ beta (K*L) := by
  intro x _ center r hr
  by_cases hx : x ∈ keep Ref O T L
  · have heq : (univ.filter (fun i => x ∈ marks Ref O T L i ∧
        projectiveDistance ((family F T).tube i).direction center ≤ r)) =
        (univ.filter (fun i => x ∈ reindex O T i ∧
        projectiveDistance ((family F T).tube i).direction center ≤ r)) := by
      ext i; simp [marks,hx]
    rw [heq]
    have hcard : (univ.filter (fun i => x ∈ reindex O T i ∧
        projectiveDistance ((family F T).tube i).direction center ≤ r)).card ≤
        (univ.filter (fun i => x ∈ Ref i ∧ projectiveDistance (F.tube i).direction center ≤ r)).card := by
      apply card_le_card_of_injOn (index T)
      · intro i hi
        exact mem_filter.mpr ⟨mem_univ _,hORef _ (mem_filter.mp hi).2.1,(mem_filter.mp hi).2.2⟩
      · exact fun i _ j _ hij => index_injective T hij
    have hratio : (overlapCount Ref x:ℝ) ≤ L*(overlapCount (marks Ref O T L) x:ℝ) := by
      have hh := hx
      change multiplicity Ref x ≤ L*multiplicity (reindex O T) x at hh
      have heq' : marks Ref O T L = fun i => reindex O T i ∩ keep Ref O T L := rfl
      have hm : multiplicity (marks Ref O T L) x = multiplicity (reindex O T) x := by
        simp [marks,MeasurableEnergy.multiplicity,oneIndicator,Set.indicator_apply,hx]
      rw [← hm,multiplicity_eq_card,multiplicity_eq_card] at hh
      exact hh
    have hh := (Nat.cast_le.mpr hcard).trans (hbroad x (Set.mem_univ _) center r hr)
    have hp := mul_le_mul_of_nonneg_left hratio (mul_nonneg hK (Real.rpow_nonneg (hδ.trans hr) beta))
    exact hh.trans (hp.trans_eq (by ring))
  · have hempty : (univ.filter (fun i => x ∈ marks Ref O T L i ∧
        projectiveDistance ((family F T).tube i).direction center ≤ r)) = ∅ := by
      simp [marks,hx]
    have hzero : overlapCount (marks Ref O T L) x = 0 := by
      simp [overlapCount,marks,hx]
    rw [hempty,card_empty,Nat.cast_zero,hzero,Nat.cast_zero,mul_zero]

/-- A dyadic actual full-mass class is selected by retained marked mass after
removing only tubes with very small marks. The marks are then proportionally
restored against all original Ref indices. Neither a marked density per tube
nor any preservation of broadness by arbitrary selection is assumed. -/
theorem select (Full Ref Y O : Fin M → Set X) {eta lam : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hlam : 0 < lam)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hO : ∀ i, MeasurableSet (O i))
    (hFullf : ∀ i, ν (Full i) ≠ ∞)
    (hRefFull : ∀ i, Ref i ⊆ Full i) (hYFull : ∀ i, Y i ⊆ Full i)
    (hOY : ∀ i, O i ⊆ Y i) (hupper : ∀ i, ν.real (Full i) ≤ 2*lam)
    (hmass : eta*lam*(M:ℝ) ≤ ∑ i, ν.real (O i)) (hM : 0 < M) :
    ∃ D ell : ℕ, ell ≤ D ∧ (D:ℝ)+1 ≤ Real.log (4/eta)/Real.log 2+2 ∧
    ∃ T : Finset (Fin M), T.Nonempty ∧
      (∀ i ∈ T, eta*lam/2*(2:ℝ)^ell ≤ ν.real (Y i) ∧
        ν.real (Y i) < 2*(eta*lam/2*(2:ℝ)^ell)) ∧
      (∀ i ∈ T, eta*lam/2 ≤ ν.real (Y i)) ∧
      eta*lam*(M:ℝ)/(2*(D+1:ℕ)) ≤ ∑ i ∈ T, ν.real (O i) ∧
      (∑ i ∈ T, ν.real (O i))/2 ≤ ∑ i, ν.real (marks Ref O T (8*(D+1:ℕ)/eta) i) ∧
      eta*lam*(M:ℝ)/(4*(D+1:ℕ)) ≤ ∑ i, ν.real (marks Ref O T (8*(D+1:ℕ)/eta) i) := by
  let S := MeasurableDensityRecovery.good ν O eta lam
  have hYf (i) := measure_ne_top_of_subset (hYFull i) (hFullf i)
  have hOf (i) := measure_ne_top_of_subset (hOY i) (hYf i)
  have hReff (i) := measure_ne_top_of_subset (hRefFull i) (hFullf i)
  have hOupper (i) : ν.real (O i) ≤ 2*lam :=
    (measureReal_mono ((hOY i).trans (hYFull i)) (hFullf i)).trans (hupper i)
  have hgood := (MeasurableDensityRecovery.good_mass_and_count O heta hlam hOupper hmass).1
  have hlo : 0 < eta*lam/2 := by positivity
  have hlu : eta*lam/2 ≤ 2*lam := by nlinarith
  obtain ⟨D,hD,hDlog⟩ := ScaleChoice.dyadic_class_budget hlo hlu
  obtain ⟨ell,hell,T,hTS,hrange,hclass⟩ := OccupancySelection.weighted_dyadic_selection S
    (fun i => ν.real (Y i)) (fun i => ν.real (O i)) hlo D
    (fun i hi => ((mem_filter.mp hi).2).trans (measureReal_mono (hOY i) (hYf i)))
    (fun i _ => ((measureReal_mono (hYFull i) (hFullf i)).trans (hupper i)).trans
      (by simpa only [mul_comm] using hD))
  have hret : eta*lam*(M:ℝ)/(2*(D+1:ℕ)) ≤ ∑ i ∈ T, ν.real (O i) := by
    have hh := (div_le_div_of_nonneg_right hgood (by positivity : (0:ℝ)≤(D+1:ℕ))).trans hclass
    simpa only [div_div] using hh
  have hT : T.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn,sum_empty] at hret
    exact (by positivity : 0 < eta*lam*(M:ℝ)/(2*(D+1:ℕ))).not_ge hret
  have hRefsum : (∑ i, ν.real (Ref i)) ≤ 2*lam*(M:ℝ) :=
    (sum_le_sum (fun i _ => (measureReal_mono (hRefFull i) (hFullf i)).trans (hupper i))).trans_eq (by simp [mul_comm])
  have hbudget : 2*(∑ i, ν.real (Ref i)) ≤ (8*(D+1:ℕ)/eta)*(∑ i ∈ T, ν.real (O i)) := by
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<2*(D+1:ℕ))).mp hret
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ heta).mpr
    nlinarith
  have hhalf := marks_mass_lower Ref O T (by positivity : (0:ℝ)<8*(D+1:ℕ)/eta)
    hRef hO hReff hOf hbudget
  refine ⟨D,ell,hell,?_,T,hT,hrange,?_,hret,hhalf,?_⟩
  · convert hDlog using 2
    congr 2
    field_simp
    norm_num
  · intro i hi
    exact ((mem_filter.mp (hTS hi)).2).trans (measureReal_mono (hOY i) (hYf i))
  · have hh := (div_le_div_of_nonneg_right hret (by norm_num : (0:ℝ)≤2)).trans hhalf
    simpa only [div_div,show (2*(D+1:ℕ):ℝ)*2 = 4*(D+1:ℕ) by ring] using hh

/-- Two ends passes to the actual selected full sets using their measured
lower density. This does not replace those full sets by their marks. -/
theorem reindexed_two_ends {k : ℕ} (ν : Measure (Space k))
    (Full Y : Fin M → Set (Space k)) (T : Finset (Fin M)) {δ eta lam alpha B : ℝ}
    (hδ : 0 ≤ δ) (heta : 0 < eta) (hB : 0 ≤ B)
    (hFullf : ∀ i, ν (Full i) ≠ ∞) (hYFull : ∀ i, Y i ⊆ Full i)
    (hupper : ∀ i, ν.real (Full i) ≤ 2*lam)
    (hlower : ∀ i ∈ T, eta*lam/2 ≤ ν.real (Y i))
    (hends : ∀ i p r, δ ≤ r → ν.real (Full i ∩ Metric.closedBall p r) ≤
      B*r^alpha*ν.real (Full i)) :
    ∀ i p r, δ ≤ r → ν.real (reindex Y T i ∩ Metric.closedBall p r) ≤
      (B*(4/eta))*r^alpha*ν.real (reindex Y T i) := by
  intro i p r hr
  have hsub : reindex Y T i ∩ Metric.closedBall p r ⊆
      Full (index T i) ∩ Metric.closedBall p r := Set.inter_subset_inter_left _ (hYFull _)
  have hm := measureReal_mono hsub (measure_ne_top_of_subset Set.inter_subset_left (hFullf _))
  have hratio : ν.real (Full (index T i)) ≤ (4/eta)*ν.real (reindex Y T i) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ heta).mpr
    have hlo := hlower _ (index_mem T i)
    have hhi := mul_le_mul_of_nonneg_left (hupper (index T i)) heta.le
    change _ ≤ 4*ν.real (Y (index T i))
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hratio (mul_nonneg hB (Real.rpow_nonneg (hδ.trans hr) alpha))
  exact (hm.trans (hends _ p r hr)).trans (hh.trans_eq (by ring))

/-- All actual selected full mass has a quantitative marked fraction derived
from the retained marked budget, even when individual tubes have sparse marks. -/
theorem marked_fraction (Full Y : Fin M → Set X) (T : Finset (Fin M))
    {eta lam Z : ℝ} {D : ℕ} (heta : 0 ≤ eta)
    (hFullf : ∀ i, ν (Full i) ≠ ∞) (hYFull : ∀ i, Y i ⊆ Full i)
    (hupper : ∀ i, ν.real (Full i) ≤ 2*lam)
    (hmass : eta*lam*(M:ℝ)/(4*(D+1:ℕ)) ≤ Z) :
    (eta/(8*(D+1:ℕ)))*(∑ i, ν.real (reindex Y T i)) ≤ Z := by
  have htotal : (∑ i, ν.real (reindex Y T i)) ≤ 2*lam*(M:ℝ) := by
    rw [reindex_mass]
    have hh : (∑ i ∈ T, ν.real (Y i)) ≤ ∑ i, ν.real (Y i) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => measureReal_nonneg)
    exact hh.trans ((sum_le_sum (fun i _ =>
      (measureReal_mono (hYFull i) (hFullf i)).trans (hupper i))).trans_eq (by simp [mul_comm]))
  have hh := mul_le_mul_of_nonneg_left htotal
    (div_nonneg heta (by positivity : (0:ℝ)≤8*(D+1:ℕ)))
  have hid : (eta/(8*(D+1:ℕ)))*(2*lam*(M:ℝ)) = eta*lam*(M:ℝ)/(4*(D+1:ℕ)) := by
    field_simp
    ring
  exact hh.trans (hid.le.trans hmass)

/-- Reindexing the measured class preserves actual original separation. -/
theorem family_separated {k : ℕ} (F : TubeFamily k M) (T : Finset (Fin M))
    {δ : ℝ} (hsep : F.Separated δ) : (family F T).Separated δ := by
  intro i j hij
  exact hsep _ _ (fun he => hij (index_injective T he))

/-- Every actual real-cap bound is inherited with unchanged coefficient. -/
theorem family_cap_bound {k : ℕ} (F : TubeFamily k M) (T : Finset (Fin M))
    {δ m A : ℝ} (hcap : F.CapBound δ m A) : (family F T).CapBound δ m A := by
  intro center hunit r hr hr1
  have hc : (univ.filter (fun i => projectiveDistance ((family F T).tube i).direction center ≤ r)).card ≤
      (univ.filter (fun i => projectiveDistance (F.tube i).direction center ≤ r)).card := by
    apply card_le_card_of_injOn (index T)
    · intro i hi
      exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hi).2⟩
    · exact fun i _ j _ hij => index_injective T hij
  exact (Nat.cast_le.mpr hc).trans (hcap center hunit r hr hr1)

/-- Measured selection also retains the original fixed base bound. -/
theorem family_bounded {k : ℕ} (F : TubeFamily k M) (T : Finset (Fin M))
    {R : ℝ} (hbounded : F.Bounded R) : (family F T).Bounded R := fun i => hbounded (index T i)

end
end KakeyaFormal.MeasurableMarkedSelection
