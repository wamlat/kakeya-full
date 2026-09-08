import SourceGoodMass

/-! Section 3.3 on the same original measurable rows and assigned pieces.
The exact deletion threshold, good sets and retained pieces are constructed. -/
namespace KakeyaFormal.SourceDensityPruning
open MeasureTheory SourceGoodMass
open scoped ENNReal
noncomputable section
open Classical

variable {X : Type*} [MeasurableSpace X] {M J : ℕ}

def survives (μ : Measure X) (Full Y : Fin M → Set X) (a : ℝ) (i : Fin M) : Prop :=
  a*μ.real (Full i) ≤ μ.real (Y i)

def survivors (μ : Measure X) (Full Y : Fin M → Set X) (a : ℝ) : Fin M → Set X :=
  fun i => if survives μ Full Y a i then Y i else ∅

def piece (assign : Fin M → Fin J) (Y : Fin M → Set X) (g : Fin J) : Fin M → Set X :=
  fun i => if assign i = g then Y i else ∅

def retained (μ : Measure X) (Ref Surv : Fin J → Fin M → Set X) : Finset (Fin J) :=
  Finset.univ.filter (fun g => mass μ (Surv g)/2 ≤ mass μ (goodRows (Ref g) (Surv g)))

theorem survivors_subset (μ : Measure X) (Full Y : Fin M → Set X) (a : ℝ) (i : Fin M) :
    survivors μ Full Y a i ⊆ Y i := by
  unfold survivors
  split_ifs <;> simp

theorem survivors_measurable (μ : Measure X) (Full Y : Fin M → Set X) (a : ℝ)
    (hY : ∀ i, MeasurableSet (Y i)) : ∀ i, MeasurableSet (survivors μ Full Y a i) := by
  intro i
  unfold survivors
  split_ifs
  · exact hY i
  · exact MeasurableSet.empty

omit [MeasurableSpace X] in
theorem piece_subset (assign : Fin M → Fin J) (Y : Fin M → Set X) (g : Fin J) (i : Fin M) :
    piece assign Y g i ⊆ Y i := by
  unfold piece
  split_ifs <;> simp

theorem piece_measurable (assign : Fin M → Fin J) (Y : Fin M → Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (g : Fin J) : ∀ i, MeasurableSet (piece assign Y g i) := by
  intro i
  unfold piece
  split_ifs
  · exact hY i
  · exact MeasurableSet.empty

omit [MeasurableSpace X] in
theorem piece_mono (assign : Fin M → Fin J) (Ref Surv : Fin M → Set X)
    (hsub : ∀ i, Surv i ⊆ Ref i) (g : Fin J) :
    ∀ i, piece assign Surv g i ⊆ piece assign Ref g i := by
  intro i
  unfold piece
  split_ifs
  · exact hsub i
  · exact Set.Subset.rfl

/-- Every original tube has exactly one piece; there is no piece-count loss. -/
theorem piece_mass_sum (μ : Measure X) (assign : Fin M → Fin J) (Y : Fin M → Set X) :
    (∑ g, mass μ (piece assign Y g)) = mass μ Y := by
  unfold mass piece
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (∑ g, μ.real (if assign i = g then Y i else ∅)) =
        ∑ g, if assign i = g then μ.real (Y i) else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      split_ifs <;> simp
    _ = μ.real (Y i) := by simp

/-- Literal (3.5), before substituting a=kappa/8. -/
theorem deleted_mass_le (μ : Measure X) (Full Y : Fin M → Set X) {a : ℝ} (ha : 0 ≤ a) :
    mass μ Y-mass μ (survivors μ Full Y a) ≤ a*mass μ Full := by
  unfold mass
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : survives μ Full Y a i
  · simp only [survivors,hi,ite_true,sub_self]
    exact mul_nonneg ha measureReal_nonneg
  · simp only [survivors,hi,ite_false,measureReal_empty,sub_zero]
    exact (lt_of_not_ge hi).le

/-- Rejecting a piece costs at most that piece's actual bad surviving mass. -/
theorem retained_good_lower (μ : Measure X) (Ref Surv : Fin J → Fin M → Set X)
    (hRef : ∀ g i, MeasurableSet (Ref g i)) (hSurv : ∀ g i, MeasurableSet (Surv g i))
    (hfin : ∀ g i, μ (Ref g i) ≠ ∞) (hsub : ∀ g i, Surv g i ⊆ Ref g i) :
    (∑ g, mass μ (Ref g))-3*((∑ g, mass μ (Ref g))-(∑ g, mass μ (Surv g))) ≤
      ∑ g ∈ retained μ Ref Surv, mass μ (goodRows (Ref g) (Surv g)) := by
  let R : Fin J → ℝ := fun g => mass μ (badRows (Ref g) (Surv g))
  let G : Fin J → ℝ := fun g => mass μ (goodRows (Ref g) (Surv g))
  have hRnonneg (g) : 0 ≤ R g := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hR : (∑ g, R g) ≤ (∑ g, mass μ (Ref g))-(∑ g, mass μ (Surv g)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun g _ => bad_mass_le_deleted μ (Ref g) (Surv g)
      (hRef g) (hSurv g) (hfin g) (hsub g))
  have hsplit (g) : R g+G g=mass μ (Surv g) :=
    mass_split μ (Ref g) (Surv g) (hRef g) (hSurv g)
      (fun i => measure_ne_top_of_subset (hsub g i) (hfin g i))
  have htotal : (∑ g, R g)+(∑ g, G g)=∑ g, mass μ (Surv g) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun g _ => hsplit g)
  have hreject : (∑ g ∈ Finset.univ.filter (fun g => g ∉ retained μ Ref Surv), G g) ≤ ∑ g, R g := by
    apply (Finset.sum_le_sum (fun g hg => ?_)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun g _ _ => hRnonneg g))
    have hn := (Finset.mem_filter.mp hg).2
    have hbad : ¬mass μ (Surv g)/2 ≤ G g := by
      intro hh
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩)
    linarith [hsplit g]
  have hparts := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin J)))
    (fun g => g ∈ retained μ Ref Surv) G
  have heq : Finset.univ.filter (fun g => g ∈ retained μ Ref Surv) = retained μ Ref Surv := by
    ext g
    simp
  rw [heq] at hparts
  change (∑ g, mass μ (Ref g))-3*((∑ g, mass μ (Ref g))-(∑ g, mass μ (Surv g))) ≤
    ∑ g ∈ retained μ Ref Surv, G g
  linarith

/-- Literal (3.5), (3.9), (3.10) on the same original assigned shadings.
The full surviving rows are unchanged on every retained tube; the good sets
mark those rows rather than replacing them. Empty input is included. -/
theorem source_fractions (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) {kappa : ℝ} (hk : 0 ≤ kappa)
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, μ (Y i) ≠ ∞)
    (hmass : kappa*mass μ Full ≤ mass μ Y) :
    let S := survivors μ Full Y (kappa/8)
    let Ref := piece assign Y
    let Surv := piece assign S
    mass μ Y-mass μ S ≤ mass μ Y/8 ∧
      3*mass μ Y/4 ≤ ∑ g, mass μ (goodRows (Ref g) (Surv g)) ∧
      5*mass μ Y/8 ≤ ∑ g ∈ retained μ Ref Surv, mass μ (goodRows (Ref g) (Surv g)) := by
  let S := survivors μ Full Y (kappa/8)
  have hsub := survivors_subset μ Full Y (kappa/8)
  have hS := survivors_measurable μ Full Y (kappa/8) hY
  have hRef := piece_measurable assign Y hY
  have hSurv := piece_measurable assign S hS
  have hpsub := piece_mono assign Y S hsub
  have hpfin g i := measure_ne_top_of_subset (piece_subset assign Y g i) (hfin i)
  have hD : mass μ Y-mass μ S ≤ mass μ Y/8 := by
    have hh := deleted_mass_le μ Full Y (by positivity : 0 ≤ kappa/8)
    change mass μ Y-mass μ S ≤ _ at hh
    linarith
  have hgood := Finset.sum_le_sum (fun g (_ : g ∈ (Finset.univ : Finset (Fin J))) =>
    good_mass_lower μ (piece assign Y g) (piece assign S g) (hRef g) (hSurv g) (hpfin g) (hpsub g))
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum,piece_mass_sum] at hgood
  have hkeep := retained_good_lower μ (piece assign Y) (piece assign S) hRef hSurv hpfin hpsub
  rw [piece_mass_sum,piece_mass_sum] at hkeep
  exact ⟨hD,by linarith,by linarith⟩

end
end KakeyaFormal.SourceDensityPruning
