import MarkedPruningRecovery
import ScaleChoice

/-! Dyadic full-density selection by actual marked incidence mass, followed by
proportional marking. Full shadings are retained whole; arbitrary tube thinning
is never claimed to preserve marked broadness. -/
namespace KakeyaFormal.MarkedDensityClass
open Finset DensityBroadnessRecovery AngularDecomposition
open scoped BigOperators
noncomputable section
open Classical

variable {k M : ℕ}

def keptCells (H : Fin M → Finset (Cell k)) (T : Finset (Fin M)) (L : ℝ) : Finset (Cell k) :=
  (cells H).filter fun z => ((row H univ z).card:ℝ) ≤ L*((row H T z).card:ℝ)

def retained (H : Fin M → Finset (Cell k)) (T : Finset (Fin M)) (L : ℝ) (i : Fin M) : Finset (Cell k) :=
  H i ∩ keptCells H T L

abbrev index (T : Finset (Fin M)) := MarkedPruningRecovery.selectedIndex T

def family (F : TubeFamily k M) (T : Finset (Fin M)) : TubeFamily k T.card :=
  MarkedPruningRecovery.selectedFamily F F.shade T

def marks (H : Fin M → Finset (Cell k)) (T : Finset (Fin M)) (L : ℝ)
    (i : Fin T.card) : Finset (Cell k) := retained H T L (index T i)

theorem marked_mass_eq (H : Fin M → Finset (Cell k)) (T : Finset (Fin M)) (L : ℝ) :
    (∑ i ∈ T, ((retained H T L i).card:ℝ)) =
      ∑ z ∈ keptCells H T L, ((row H T z).card:ℝ) := by
  have hh := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s:=T) (t:=keptCells H T L) (fun i z => z ∈ H i)
  have hid (i : Fin M) : (keptCells H T L).filter (fun z => z ∈ H i) = retained H T L i := by
    ext z
    simp [retained,and_comm]
  simp only [bipartiteAbove,bipartiteBelow,hid] at hh
  exact_mod_cast hh

/-- The actual cell filter loses at most half the selected marked mass once
its proportional threshold is calibrated to the class's retained mass. -/
theorem recover_half (H : Fin M → Finset (Cell k)) (T : Finset (Fin M)) {L : ℝ}
    (hL : 0 < L)
    (hbudget : 2*(∑ i, ((H i).card:ℝ)) ≤ L*(∑ i ∈ T, ((H i).card:ℝ))) :
    (∑ i ∈ T, ((H i).card:ℝ))/2 ≤ ∑ i ∈ T, ((retained H T L i).card:ℝ) := by
  let U := cells H
  have hU (i : Fin M) : H i ⊆ U := fun z hz => mem_biUnion.mpr ⟨i,mem_univ _,hz⟩
  have hall : (∑ z ∈ U, ((row H univ z).card:ℝ)) = ∑ i, ((H i).card:ℝ) := by
    exact_mod_cast incidence_sum H univ U (fun i _ => hU i)
  have hsel : (∑ z ∈ U, ((row H T z).card:ℝ)) = ∑ i ∈ T, ((H i).card:ℝ) := by
    exact_mod_cast incidence_sum H T U (fun i _ => hU i)
  let bad := U.filter fun z => ¬((row H univ z).card:ℝ) ≤ L*((row H T z).card:ℝ)
  have hbad : L*(∑ z ∈ bad, ((row H T z).card:ℝ)) ≤ ∑ i, ((H i).card:ℝ) := by
    calc
      _ = ∑ z ∈ bad, L*((row H T z).card:ℝ) := mul_sum _ _ _
      _ ≤ ∑ z ∈ bad, ((row H univ z).card:ℝ) :=
        sum_le_sum fun z hz => (lt_of_not_ge (mem_filter.mp hz).2).le
      _ ≤ ∑ z ∈ U, ((row H univ z).card:ℝ) :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
      _ = _ := hall
  have hsplit := sum_filter_add_sum_filter_not (s:=U)
    (fun z => ((row H univ z).card:ℝ) ≤ L*((row H T z).card:ℝ))
    (fun z => ((row H T z).card:ℝ))
  rw [hsel] at hsplit
  change (∑ z ∈ keptCells H T L, ((row H T z).card:ℝ)) +
    (∑ z ∈ bad, ((row H T z).card:ℝ)) = _ at hsplit
  rw [marked_mass_eq]
  nlinarith

theorem reindexed_sum (H : Fin M → Finset (Cell k)) (T : Finset (Fin M)) :
    (∑ i : Fin T.card, ((H (index T i)).card:ℝ)) = ∑ i ∈ T, ((H i).card:ℝ) :=
  MarkedPruningRecovery.reindex_mass H T

/-- Power broadness is transferred by the verified proportional ratio at kept
cells. At every other cell the actual retained marked row is empty. -/
theorem retained_broad {δ beta tau K L : ℝ} (F : TubeFamily k M)
    (H : Fin M → Finset (Cell k)) (T : Finset (Fin M))
    (hδ : 0 ≤ δ) (htau : 0 < tau) (hK : 0 ≤ K) (_hL : 0 ≤ L)
    (hbroad : ∀ z, Broad F (row H univ z) δ beta tau K) :
    ∀ z, Broad F (row (retained H T L) T z) δ beta tau (K*L) := by
  intro z
  by_cases hz : z ∈ keptCells H T L
  · have heq : row (retained H T L) T z = row H T z := by
      ext i
      simp only [row,retained,mem_filter,mem_inter,hz,and_true]
    rw [heq]
    exact broad_proportional_subset F (filter_subset_filter _ (subset_univ _)) hδ htau hK
      (mem_filter.mp hz).2 (hbroad z)
  · have heq : row (retained H T L) T z = ∅ := by simp [row,retained,hz]
    rw [heq]
    intro v r _
    simp [cap]

theorem selected_row_image (H : Fin M → Finset (Cell k)) (T : Finset (Fin M)) (L : ℝ) (z : Cell k) :
    (row (marks H T L) univ z).image (index T) = row (retained H T L) T z := by
  ext i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
    exact mem_filter.mpr ⟨((T.equivFin.symm j).property),(mem_filter.mp hj).2⟩
  · intro hi
    let j := T.equivFin ⟨i,(mem_filter.mp hi).1⟩
    have hj : index T j = i := by simp [index,MarkedPruningRecovery.selectedIndex,j]
    exact mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,by simpa only [marks,hj] using (mem_filter.mp hi).2⟩,hj⟩

/-- Exact tube reindexing preserves the broad marked rows, with no new labels. -/
theorem selected_broad {δ beta tau K L : ℝ} (F : TubeFamily k M)
    (H : Fin M → Finset (Cell k)) (T : Finset (Fin M))
    (hδ : 0 ≤ δ) (htau : 0 < tau) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hbroad : ∀ z, Broad F (row H univ z) δ beta tau K) :
    ∀ z, Broad (family F T) (row (marks H T L) univ z) δ beta tau (K*L) := by
  intro z v r hr
  have he : Function.Injective (index T) := MarkedPruningRecovery.selectedIndex_injective T
  have hrow := congrArg card (selected_row_image H T L z)
  rw [card_image_of_injective _ he] at hrow
  have hcap : (cap (family F T) (row (marks H T L) univ z) v r).image (index T) =
      cap F (row (retained H T L) T z) v r := by
    ext i
    constructor
    · intro hi
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hi
      exact mem_filter.mpr ⟨(selected_row_image H T L z) ▸ mem_image.mpr
        ⟨j,(mem_filter.mp hj).1,rfl⟩,(mem_filter.mp hj).2⟩
    · intro hi
      obtain ⟨j,hj,hji⟩ := mem_image.mp ((selected_row_image H T L z).symm ▸ (mem_filter.mp hi).1)
      refine mem_image.mpr ⟨j,mem_filter.mpr ⟨hj,?_⟩,hji⟩
      simpa only [family,MarkedPruningRecovery.selectedFamily,hji] using (mem_filter.mp hi).2
  have hc := congrArg card hcap
  rw [card_image_of_injective _ he] at hc
  rw [hc,hrow]
  exact retained_broad F H T hδ htau hK hL hbroad z v r hr

/-- Construct a genuine dyadic full-density class using marked mass, then keep
only marks satisfying the proportional row test. -/
theorem select (F : TubeFamily k M) (H : Fin M → Finset (Cell k))
    {δ lo upper beta tau K : ℝ}
    (hδ : 0 ≤ δ) (hlo : 0 < lo) (hlu : lo ≤ upper) (htau : 0 < tau) (hK : 0 ≤ K)
    (hlower : ∀ i, lo ≤ δ*((F.shade i).card:ℝ))
    (hupper : ∀ i, δ*((F.shade i).card:ℝ) ≤ upper)
    (hmarked : 0 < ∑ i, ((H i).card:ℝ))
    (hbroad : ∀ z, Broad F (row H univ z) δ beta tau K) :
    ∃ D ell : ℕ, ell ≤ D ∧ (D:ℝ)+1 ≤ Real.log (upper/lo)/Real.log 2+2 ∧
    ∃ T : Finset (Fin M), T.Nonempty ∧
      (∀ i ∈ T, lo*(2:ℝ)^ell ≤ δ*((F.shade i).card:ℝ) ∧
        δ*((F.shade i).card:ℝ) < 2*(lo*(2:ℝ)^ell)) ∧
      (∑ i, ((H i).card:ℝ))/(D+1:ℕ) ≤ ∑ i ∈ T, ((H i).card:ℝ) ∧
      (∑ i ∈ T, ((H i).card:ℝ))/2 ≤ ∑ i, ((marks H T (2*(D+1:ℕ)) i).card:ℝ) ∧
      (∑ i, ((H i).card:ℝ))/(2*(D+1:ℕ)) ≤ ∑ i, ((marks H T (2*(D+1:ℕ)) i).card:ℝ) ∧
      (∀ z, Broad (family F T) (row (marks H T (2*(D+1:ℕ))) univ z)
        δ beta tau (K*(2*(D+1:ℕ)))) := by
  obtain ⟨D,hD,hDlog⟩ := ScaleChoice.dyadic_class_budget hlo hlu
  obtain ⟨ell,hell,T,_,hrange,hmass⟩ := OccupancySelection.weighted_dyadic_selection univ
    (fun i => δ*((F.shade i).card:ℝ)) (fun i => ((H i).card:ℝ)) hlo D
    (fun i _ => hlower i) (fun i _ => (hupper i).trans (by simpa only [mul_comm] using hD))
  have hT : T.Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn,sum_empty] at hmass
    exact (div_pos hmarked (by positivity : (0:ℝ)<(D+1:ℕ))).not_ge hmass
  have hbudget : 2*(∑ i, ((H i).card:ℝ)) ≤ (2*(D+1:ℕ))*(∑ i ∈ T, ((H i).card:ℝ)) := by
    have hh := (div_le_iff₀ (by positivity : (0:ℝ)<(D+1:ℕ))).mp hmass
    nlinarith
  have hhalf := recover_half H T (by positivity : (0:ℝ)<2*(D+1:ℕ)) hbudget
  have hmarkedEq : (∑ i, ((marks H T (2*(D+1:ℕ)) i).card:ℝ)) =
      ∑ i ∈ T, ((retained H T (2*(D+1:ℕ)) i).card:ℝ) :=
    reindexed_sum _ _
  rw [← hmarkedEq] at hhalf
  refine ⟨D,ell,hell,hDlog,T,hT,hrange,hmass,hhalf,?_,?_⟩
  · have hh := (div_le_div_of_nonneg_right hmass (by norm_num : (0:ℝ)≤2)).trans hhalf
    simpa only [div_div,mul_comm] using hh
  · exact selected_broad F H T hδ htau hK (by positivity) hbroad

end
end KakeyaFormal.MarkedDensityClass

#print axioms KakeyaFormal.MarkedDensityClass.select
