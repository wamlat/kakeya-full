import SamplingGeometry

/-! Exact raw sampling support and mean identities for arbitrary bounded
measurable shadings. No unit-length tube hypothesis enters this cell bookkeeping. -/
namespace KakeyaFormal.SamplingBoundedSupport
open Finset GridCells GridGeometry GridShadingMeasure SamplingSupport SamplingMeans MeasureTheory
open scoped BigOperators
noncomputable section
open Classical

def candidates (n : ℕ) (δ R : ℝ) : Finset (Cell n) :=
  gridBox (fun _ => 0) (Nat.ceil (R/δ+(n:ℝ)/2)+1)

def support {n M : ℕ} (Full : Fin M → Set (Space n)) (δ R : ℝ) : Finset (Cell n) :=
  (candidates n δ R).filter (fun z => ∃ i, 0 < (volume : Measure (Space n)).real (Full i ∩ gridCell δ z))

theorem positive_mem_candidates {n : ℕ} {Y : Set (Space n)} {δ R : ℝ}
    (hδ : 0 < δ) (hY : ∀ x ∈ Y, ‖x‖ ≤ R) {z : Cell n}
    (hpos : 0 < (volume : Measure (Space n)).real (Y ∩ gridCell δ z)) :
    z ∈ candidates n δ R := by
  obtain ⟨x,hx,hcell⟩ := positive_intersection_nonempty hpos
  exact touching_bounded_set_label hδ hY ⟨x,hcell,hx⟩

theorem mem_support {n M : ℕ} (Full : Fin M → Set (Space n)) {δ R : ℝ}
    (hδ : 0 < δ) (hFull : ∀ i x, x ∈ Full i → ‖x‖ ≤ R) (z : Cell n) :
    z ∈ support Full δ R ↔ ∃ i, 0 < (volume : Measure (Space n)).real (Full i ∩ gridCell δ z) := by
  constructor
  · intro hz
    exact (mem_filter.mp hz).2
  · rintro ⟨i,hi⟩
    exact mem_filter.mpr ⟨positive_mem_candidates hδ (hFull i) hi,⟨i,hi⟩⟩

theorem candidates_cover {n : ℕ} {Y : Set (Space n)} {δ R : ℝ}
    (hδ : 0 < δ) (hY : ∀ x ∈ Y, ‖x‖ ≤ R) :
    Y ⊆ cellUnion δ (candidates n δ R) := by
  intro x hx
  apply (mem_cellUnion hδ _ x).mpr
  exact touching_bounded_set_label hδ hY ⟨x,gridCell_covers hδ x,hx⟩

/-- Omitting zero full intersections loses no full or marked mass. -/
theorem support_mass {n M : ℕ} (Full : Fin M → Set (Space n)) {δ R : ℝ}
    (hδ : 0 < δ) (hFull : ∀ i x, x ∈ Full i → ‖x‖ ≤ R)
    (i : Fin M) {Y : Set (Space n)} (hY : MeasurableSet Y) (hsub : Y ⊆ Full i) :
    (∑ z ∈ support Full δ R, weight Y δ z) = (volume : Measure (Space n)).real Y/δ^n := by
  have hSc : support Full δ R ⊆ candidates n δ R := filter_subset _ _
  have hsum : (∑ z ∈ support Full δ R, weight Y δ z) =
      ∑ z ∈ candidates n δ R, weight Y δ z := by
    apply sum_subset hSc
    intro z _ hn
    apply le_antisymm _ (weight_nonneg Y hδ z)
    by_contra hp
    have hpos : 0 < weight Y δ z := lt_of_not_ge hp
    have hf : 0 < weight (Full i) δ z := hpos.trans_le (weight_mono hsub hδ z)
    have hf' : 0 < (volume : Measure (Space n)).real (Full i ∩ gridCell δ z) :=
      (div_pos_iff_of_pos_right (pow_pos hδ n)).mp hf
    exact hn ((mem_support Full hδ hFull z).mpr ⟨i,hf'⟩)
  rw [hsum,weight_sum hδ _ hY]
  have hcover := candidates_cover hδ (fun x hx => hFull i x (hsub hx))
  rw [Set.inter_eq_left.mpr hcover]

theorem full_mean_eq {n M : ℕ} (Full : Fin M → Set (Space n)) {δ R : ℝ}
    (hδ : 0 < δ) (hFull : ∀ i x, x ∈ Full i → ‖x‖ ≤ R)
    (Y : Fin M → Set (Space n)) (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ Full i)
    (i : Fin M) :
    KakeyaSamplingApplication.fullMean (weights Y δ (support Full δ R)) i =
      (volume : Measure (Space n)).real (Y i)/δ^n := by
  change (∑ z : support Full δ R, weight (Y i) δ z.val) = _
  rw [← sum_subtype (support Full δ R) (fun _ => Iff.rfl) (fun z => weight (Y i) δ z)]
  exact support_mass Full hδ hFull i (hY i) (hsub i)

theorem marked_mean_eq {n M : ℕ} (Full G : Fin M → Set (Space n)) {δ R : ℝ}
    (hδ : 0 < δ) (hFull : ∀ i x, x ∈ Full i → ‖x‖ ≤ R)
    (hG : ∀ i, MeasurableSet (G i)) (hsub : ∀ i, G i ⊆ Full i) :
    (∑ z : support Full δ R, KakeyaSamplingApplication.markedMean (weights G δ (support Full δ R)) z) =
      (∑ i, (volume : Measure (Space n)).real (G i))/δ^n := by
  change (∑ z, ∑ i, weights G δ (support Full δ R) i z) = _
  rw [sum_comm]
  change (∑ i, KakeyaSamplingApplication.fullMean (weights G δ (support Full δ R)) i) = _
  simp_rw [full_mean_eq Full hδ hFull G hG hsub]
  rw [sum_div]

/-- Every positive support label lies near an actual bounded shading point. -/
theorem support_bounded {n M : ℕ} (Full : Fin M → Set (Space n)) {δ R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hFull : ∀ i x, x ∈ Full i → ‖x‖ ≤ R) :
    ∀ z ∈ support Full δ R, ‖cellCenter δ z‖ ≤ R+(n:ℝ)/2 := by
  intro z hz
  obtain ⟨i,hi⟩ := (mem_support Full hδ hFull z).mp hz
  obtain ⟨x,hx,hcell⟩ := positive_intersection_nonempty hi
  have hd := cell_center_distance hcell
  have htri := dist_triangle (cellCenter δ z) x 0
  rw [dist_comm (cellCenter δ z) x,dist_zero_right,dist_zero_right] at htri
  have hdim : (0:ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith [hFull i x hx]

/-- All physical ball means, with the original mesh and the original full mean. -/
theorem ball_mean_two_ends {n M J : ℕ} (Full : Fin M → Set (Space n)) {δ R B alpha : ℝ}
    (hδ : 0 < δ) (hFull : ∀ i x, x ∈ Full i → ‖x‖ ≤ R)
    (hmeas : ∀ i, MeasurableSet (Full i)) (hfinite : ∀ i, (volume : Measure (Space n)) (Full i) ≠ ⊤)
    (hB : 1 ≤ B) (ha : 0 ≤ alpha) (hbottom : δ ≤ Localization.radius J 0)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (volume : Measure (Space n)).real (Full i ∩ Metric.closedBall x r) ≤
        B*r^alpha*(volume : Measure (Space n)).real (Full i))
    (i : Fin M) (t : SamplingBallTests.Test (support Full δ R) J) :
    KakeyaSamplingApplication.ballMean (weights Full δ (support Full δ R)) (SamplingBallTests.mask δ) i t ≤
      B*(1+(n:ℝ)/2)^alpha*(SamplingBallTests.testRadius t)^alpha*
        KakeyaSamplingApplication.fullMean (weights Full δ (support Full δ R)) i := by
  rw [SamplingMeans.ballMean_eq,full_mean_eq Full hδ hFull Full hmeas (fun _ => Set.Subset.rfl)]
  exact SamplingMeans.ball_weight_two_ends _ hδ
    (by linarith [(SamplingBallTests.radius_bounds hbottom t).1]) hB ha _ (hmeas i) (hfinite i) (hends i)

end
end KakeyaFormal.SamplingBoundedSupport
