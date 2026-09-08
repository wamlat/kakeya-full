import SourceDensityPruning
import AngularDecomposition

/-! Geometry of the exact Section 3.3 deletion masks and half-multiplicity
good sets. Full surviving rows, separate marks, and retained piece labels all
use the same original indices and assignment as SourceDensityPruning. -/
namespace KakeyaFormal.SourceDensityPruningGeometry
open MeasureTheory SourceGoodMass SourceDensityPruning MeasurableEnergy AngularDecomposition
open scoped ENNReal
noncomputable section
open Classical

variable {X : Type*} [MeasurableSpace X] {M J : ℕ}

def survivingPiece (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (g : Fin J) : Fin M → Set X :=
  piece assign (survivors μ Full Y a) g

def markedPiece (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (g : Fin J) : Fin M → Set X :=
  goodRows (piece assign Y g) (survivingPiece μ Full Y assign a g)

def kept (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) : Finset (Fin J) :=
  retained μ (piece assign Y) (survivingPiece μ Full Y assign a)

theorem surviving_piece_eq (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (g : Fin J) (i : Fin M)
    (hg : assign i = g) (hi : survives μ Full Y a i) :
    survivingPiece μ Full Y assign a g i = Y i := by
  simp only [survivingPiece,piece,survivors,hg,hi,ite_true]

theorem surviving_piece_nonempty (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (g : Fin J) (i : Fin M)
    (hne : (survivingPiece μ Full Y assign a g i).Nonempty) :
    assign i = g ∧ survives μ Full Y a i := by
  by_cases hg : assign i = g
  · refine ⟨hg,?_⟩
    by_contra hi
    simp [survivingPiece,piece,survivors,hg,hi] at hne
  · simp [survivingPiece,piece,hg] at hne

theorem surviving_piece_subset (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (g : Fin J) :
    ∀ i, survivingPiece μ Full Y assign a g i ⊆ piece assign Y g i :=
  piece_mono assign Y _ (survivors_subset μ Full Y a) g

theorem surviving_piece_subset_original (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (g : Fin J) (i : Fin M) :
    survivingPiece μ Full Y assign a g i ⊆ Y i :=
  (surviving_piece_subset μ Full Y assign a g i).trans (piece_subset assign Y g i)

theorem marked_piece_subset (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (g : Fin J) (i : Fin M) :
    markedPiece μ Full Y assign a g i ⊆ survivingPiece μ Full Y assign a g i :=
  Set.inter_subset_left

theorem pieces_measurable (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (hY : ∀ i, MeasurableSet (Y i)) (g : Fin J) :
    (∀ i, MeasurableSet (survivingPiece μ Full Y assign a g i)) ∧
      (∀ i, MeasurableSet (markedPiece μ Full Y assign a g i)) := by
  have hs := piece_measurable assign _ (survivors_measurable μ Full Y a hY) g
  exact ⟨hs,goodRows_measurable _ _ (piece_measurable assign Y hY g) hs⟩

theorem pieces_finite (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (hfin : ∀ i, μ (Y i) ≠ ∞) (g : Fin J) :
    (∀ i, μ (survivingPiece μ Full Y assign a g i) ≠ ∞) ∧
      (∀ i, μ (markedPiece μ Full Y assign a g i) ≠ ∞) := by
  have hs i := measure_ne_top_of_subset
    (surviving_piece_subset_original μ Full Y assign a g i) (hfin i)
  exact ⟨hs,fun i => measure_ne_top_of_subset (marked_piece_subset μ Full Y assign a g i) (hs i)⟩

/-- Literal surviving full-row density bounds (3.6). The good-set restriction
does not replace the full rows to which this statement applies. -/
theorem surviving_density (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) {a lower upper : ℝ} (ha : 0 ≤ a)
    (hsub : ∀ i, Y i ⊆ Full i) (hfin : ∀ i, μ (Full i) ≠ ∞)
    (hlower : ∀ i, lower ≤ μ.real (Full i)) (hupper : ∀ i, μ.real (Full i) ≤ upper)
    (g : Fin J) (i : Fin M) (hg : assign i = g) (hi : survives μ Full Y a i) :
    a*lower ≤ μ.real (survivingPiece μ Full Y assign a g i) ∧
      μ.real (survivingPiece μ Full Y assign a g i) ≤ upper := by
  rw [surviving_piece_eq μ Full Y assign a g i hg hi]
  exact ⟨(mul_le_mul_of_nonneg_left (hlower i) ha).trans hi,
    (measureReal_mono (hsub i) (hfin i)).trans (hupper i)⟩

/-- Every actual nonempty output row supplies its own assigned-survivor
certificate; no separate population or row-selection premise is needed. -/
theorem active_density (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) {a lower upper : ℝ} (ha : 0 ≤ a)
    (hsub : ∀ i, Y i ⊆ Full i) (hfin : ∀ i, μ (Full i) ≠ ∞)
    (hlower : ∀ i, lower ≤ μ.real (Full i)) (hupper : ∀ i, μ.real (Full i) ≤ upper)
    (g : Fin J) (i : Fin M) (hne : (survivingPiece μ Full Y assign a g i).Nonempty) :
    a*lower ≤ μ.real (survivingPiece μ Full Y assign a g i) ∧
      μ.real (survivingPiece μ Full Y assign a g i) ≤ upper := by
  obtain ⟨hg,hi⟩ := surviving_piece_nonempty μ Full Y assign a g i hne
  exact surviving_density μ Full Y assign ha hsub hfin hlower hupper g i hg hi

/-- Literal (3.7), on the actual unchanged full surviving row. Its only loss
is a inverse, with no extra factor from pieces or marked restriction. -/
theorem surviving_two_ends {n : ℕ} (μ : Measure (Space n))
    (Full Y : Fin M → Set (Space n)) (assign : Fin M → Fin J)
    {a δ B alpha : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hsub : ∀ i, Y i ⊆ Full i) (hfin : ∀ i, μ (Full i) ≠ ∞)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 → μ.real (Full i ∩ Metric.closedBall x r) ≤
      B*r^alpha*μ.real (Full i))
    (g : Fin J) (i : Fin M) (hg : assign i = g) (hi : survives μ Full Y a i) :
    ∀ x r, δ ≤ r → r ≤ 1 →
      μ.real (survivingPiece μ Full Y assign a g i ∩ Metric.closedBall x r) ≤
        (B/a)*r^alpha*μ.real (survivingPiece μ Full Y assign a g i) := by
  rw [surviving_piece_eq μ Full Y assign a g i hg hi]
  intro x r hr hr1
  have hratio : μ.real (Full i) ≤ μ.real (Y i)/a :=
    (le_div_iff₀ ha).mpr (by simpa only [survives,mul_comm] using hi)
  have hmono := measureReal_mono (Set.inter_subset_inter_left (Metric.closedBall x r) (hsub i))
    (measure_ne_top_of_subset Set.inter_subset_left (hfin i))
  have hmul := mul_le_mul_of_nonneg_left hratio
    (mul_nonneg hB (Real.rpow_nonneg (hδ.trans hr) alpha))
  exact (hmono.trans (hends i x r hr hr1)).trans (hmul.trans_eq (by ring))

/-- The full-two-ends statement holds on every actual mask row, including
the empty rows of unassigned or deleted original indices. -/
theorem all_rows_two_ends {n : ℕ} (μ : Measure (Space n))
    (Full Y : Fin M → Set (Space n)) (assign : Fin M → Fin J)
    {a δ B alpha : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hsub : ∀ i, Y i ⊆ Full i) (hfin : ∀ i, μ (Full i) ≠ ∞)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 → μ.real (Full i ∩ Metric.closedBall x r) ≤
      B*r^alpha*μ.real (Full i)) :
    ∀ g i x r, δ ≤ r → r ≤ 1 →
      μ.real (survivingPiece μ Full Y assign a g i ∩ Metric.closedBall x r) ≤
        (B/a)*r^alpha*μ.real (survivingPiece μ Full Y assign a g i) := by
  intro g i
  by_cases hne : (survivingPiece μ Full Y assign a g i).Nonempty
  · obtain ⟨hg,hi⟩ := surviving_piece_nonempty μ Full Y assign a g i hne
    exact surviving_two_ends μ Full Y assign ha hδ hB hsub hfin hends g i hg hi
  · have hz := Set.not_nonempty_iff_eq_empty.mp hne
    simp only [hz,Set.empty_inter,measureReal_empty,mul_zero,le_refl,implies_true]

omit [MeasurableSpace X] in
theorem good_row_eq (Ref Surv : Fin M → Set X) {x : X} (hx : x ∈ good Ref Surv) :
    Finset.univ.filter (fun i => x ∈ goodRows Ref Surv i) =
      Finset.univ.filter (fun i => x ∈ Surv i) := by
  ext i
  simp only [goodRows,Finset.mem_filter,Set.mem_inter_iff,hx,and_true]

/-- The exact half-multiplicity good set gives factor TWO on the actual
surviving direction row, at every original tested radius. -/
theorem surviving_broad_on_good {n : ℕ} (F : TubeFamily n M)
    (Ref Surv : Fin M → Set (Space n)) {δ beta tau K : ℝ}
    (hδ : 0 ≤ δ) (htau : 0 < tau) (hK : 0 ≤ K)
    (hsub : ∀ i, Surv i ⊆ Ref i)
    (hbroad : ∀ x, Broad F (Finset.univ.filter (fun i => x ∈ Ref i)) δ beta tau K)
    (x : Space n) (hx : x ∈ good Ref Surv) :
    Broad F (Finset.univ.filter (fun i => x ∈ Surv i)) δ beta tau (2*K) := by
  have hpop : ((Finset.univ.filter (fun i => x ∈ Ref i)).card:ℝ) ≤
      2*((Finset.univ.filter (fun i => x ∈ Surv i)).card:ℝ) := by
    simpa only [good,Set.mem_ofPred_eq,multiplicity_eq_card,overlapCount] using hx
  have hs : Finset.univ.filter (fun i => x ∈ Surv i) ⊆
      Finset.univ.filter (fun i => x ∈ Ref i) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsub i (Finset.mem_filter.mp hi).2⟩
  simpa only [mul_comm] using broad_proportional_subset F hs hδ htau hK hpop (hbroad x)

/-- The separate marked rows are broad everywhere; outside the good set they
are empty. Full surviving shadings remain unchanged. -/
theorem goodRows_broad {n : ℕ} (F : TubeFamily n M)
    (Ref Surv : Fin M → Set (Space n)) {δ beta tau K : ℝ}
    (hδ : 0 ≤ δ) (htau : 0 < tau) (hK : 0 ≤ K)
    (hsub : ∀ i, Surv i ⊆ Ref i)
    (hbroad : ∀ x, Broad F (Finset.univ.filter (fun i => x ∈ Ref i)) δ beta tau K) :
    ∀ x, Broad F (Finset.univ.filter (fun i => x ∈ goodRows Ref Surv i)) δ beta tau (2*K) := by
  intro x
  by_cases hx : x ∈ good Ref Surv
  · rw [good_row_eq Ref Surv hx]
    exact surviving_broad_on_good F Ref Surv hδ htau hK hsub hbroad x hx
  · simp [goodRows,hx,Broad,cap]

theorem marked_piece_broad {n : ℕ} (F : TubeFamily n M) (μ : Measure (Space n))
    (Full Y : Fin M → Set (Space n)) (assign : Fin M → Fin J) (a : ℝ)
    {δ beta tau K : ℝ} (hδ : 0 ≤ δ) (htau : 0 < tau) (hK : 0 ≤ K)
    (hbroad : ∀ g x, Broad F (Finset.univ.filter (fun i => x ∈ piece assign Y g i)) δ beta tau K) :
    ∀ g x, Broad F (Finset.univ.filter (fun i => x ∈ markedPiece μ Full Y assign a g i))
      δ beta tau (2*K) := by
  intro g
  exact goodRows_broad F _ _ hδ htau hK (surviving_piece_subset μ Full Y assign a g) (hbroad g)

/-- Retained pieces have the literal one-half good-mass condition by their
actual threshold definition, with the original full surviving rows. -/
theorem retained_half_mass (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (g : Fin J) (hg : g ∈ kept μ Full Y assign a) :
    mass μ (survivingPiece μ Full Y assign a g)/2 ≤ mass μ (markedPiece μ Full Y assign a g) :=
  (Finset.mem_filter.mp hg).2

/-- Pointwise overlap of retained FULL piece unions is no larger than the
original overlap. Both deletion and piece rejection are actual masks. -/
theorem retained_overlap (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (x : X) :
    ((kept μ Full Y assign a).filter (fun g => ∃ i, x ∈ survivingPiece μ Full Y assign a g i)).card ≤
      (Finset.univ.filter (fun g => ∃ i, x ∈ piece assign Y g i)).card := by
  apply Finset.card_le_card
  intro g hg
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hg).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,surviving_piece_subset μ Full Y assign a g i hi⟩

theorem retained_marked_overlap (μ : Measure X) (Full Y : Fin M → Set X)
    (assign : Fin M → Fin J) (a : ℝ) (x : X) :
    ((kept μ Full Y assign a).filter (fun g => ∃ i, x ∈ markedPiece μ Full Y assign a g i)).card ≤
      (Finset.univ.filter (fun g => ∃ i, x ∈ piece assign Y g i)).card := by
  apply Finset.card_le_card
  intro g hg
  obtain ⟨i,hi⟩ := (Finset.mem_filter.mp hg).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,
    surviving_piece_subset μ Full Y assign a g i (marked_piece_subset μ Full Y assign a g i hi)⟩

end
end KakeyaFormal.SourceDensityPruningGeometry
