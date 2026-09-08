import SamplingSupport
import GridShadingMeasure
import SamplingCapTests

/-! Actual measurable cell-intersection means for the coupled sampling law.
The identities use disjoint half-open cells; ball estimates come from the
original physical two ends, including a total-mass fallback above radius one. -/
namespace KakeyaFormal.SamplingMeans
open Finset GridCells GridShadingMeasure SamplingSupport MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
open Classical

/-- Exact mass on any finite collection of the actual disjoint grid cells. -/
theorem cell_mass_sum {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Cell n)) {Y : Set (Space n)} (hY : MeasurableSet Y) :
    (∑ z ∈ S, (volume : Measure (Space n)).real (Y ∩ gridCell δ z)) =
      (volume : Measure (Space n)).real (Y ∩ cellUnion δ S) := by
  have hh := measureReal_biUnion_finset (μ := (volume : Measure (Space n)))
    (s := S) (f := fun z => Y ∩ gridCell δ z)
    (fun z _ w _ hzw => (gridCell_disjoint hδ hzw).mono Set.inter_subset_right Set.inter_subset_right)
    (fun z _ => hY.inter (measurable_gridCell δ z))
    (fun z _ => measure_ne_top_of_subset Set.inter_subset_right (finite_gridCell δ z))
  have heq : (⋃ z ∈ S, Y ∩ gridCell δ z) = Y ∩ cellUnion δ S := by
    ext x
    simp only [cellUnion,Set.mem_iUnion,Set.mem_inter_iff]
    aesop
  rw [heq] at hh
  exact hh.symm

theorem weight_sum {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Cell n)) {Y : Set (Space n)} (hY : MeasurableSet Y) :
    (∑ z ∈ S, weight Y δ z) =
      (volume : Measure (Space n)).real (Y ∩ cellUnion δ S)/δ^n := by
  simp only [weight,← sum_div]
  rw [cell_mass_sum hδ S hY]

/-- Bounded original carriers supply a finite grid cover of every full or
marked subset, rather than assuming a cell decomposition. -/
theorem candidates_cover {n : ℕ} (T : UnitTube n) {Y : Set (Space n)}
    {δ width R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ‖T.base‖ ≤ R) (hY : Y ⊆ T.carrier (width*δ)) :
    Y ⊆ cellUnion δ (candidates n δ width R) := by
  intro x hx
  apply (mem_cellUnion hδ _ x).mpr
  exact touching_bounded_set_label hδ (fun y hy => shading_point_bound T hδ1 hw hbase hY hy)
    ⟨x,gridCell_covers hδ x,hx⟩

/-- Removing all zero full incidences loses no marked or full measurable mass.
The support is the finite set constructed from the original full carriers. -/
theorem support_mass {n M : ℕ} (tube : Fin M → UnitTube n)
    (Full : Fin M → Set (Space n)) {δ width R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ∀ i, ‖(tube i).base‖ ≤ R)
    (hFull : ∀ i, Full i ⊆ (tube i).carrier (width*δ))
    (i : Fin M) {Y : Set (Space n)} (hY : MeasurableSet Y) (hsub : Y ⊆ Full i) :
    (∑ z ∈ support tube Full δ width R, weight Y δ z) =
      (volume : Measure (Space n)).real Y/δ^n := by
  have hSc : support tube Full δ width R ⊆ candidates n δ width R := by
    intro z hz
    obtain ⟨j,hj⟩ := (mem_support tube Full hδ hδ1 hw hbase hFull z).mp hz
    exact positive_mem_candidates (tube j) hδ hδ1 hw (hbase j) (hFull j) hj
  have hsum : (∑ z ∈ support tube Full δ width R, weight Y δ z) =
      ∑ z ∈ candidates n δ width R, weight Y δ z := by
    apply sum_subset hSc
    intro z _ hn
    apply le_antisymm _ (weight_nonneg Y hδ z)
    by_contra hp
    have hpos : 0 < weight Y δ z := lt_of_not_ge hp
    have hf : 0 < weight (Full i) δ z := hpos.trans_le (weight_mono hsub hδ z)
    have hf' : 0 < (volume : Measure (Space n)).real (Full i ∩ gridCell δ z) := by
      have hh := (div_pos_iff_of_pos_right (pow_pos hδ n)).mp hf
      exact hh
    exact hn ((mem_support tube Full hδ hδ1 hw hbase hFull z).mpr ⟨i,hf'⟩)
  rw [hsum,weight_sum hδ _ hY]
  have hcover := candidates_cover (tube i) hδ hδ1 hw (hbase i) (hsub.trans (hFull i))
  rw [Set.inter_eq_left.mpr hcover]

/-- The same exact mass identity on the cell subtype used by the finite
probability law. -/
theorem support_mean {n M : ℕ} (tube : Fin M → UnitTube n)
    (Full : Fin M → Set (Space n)) {δ width R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ∀ i, ‖(tube i).base‖ ≤ R)
    (hFull : ∀ i, Full i ⊆ (tube i).carrier (width*δ))
    (i : Fin M) {Y : Set (Space n)} (hY : MeasurableSet Y) (hsub : Y ⊆ Full i) :
    (∑ z : support tube Full δ width R, weight Y δ z.val) =
      (volume : Measure (Space n)).real Y/δ^n := by
  rw [← sum_subtype (support tube Full δ width R) (fun _ => Iff.rfl) (fun z => weight Y δ z)]
  exact support_mass tube Full hδ hδ1 hw hbase hFull i hY hsub

/-- A center-ball mask includes only physical cell points in its explicitly
enlarged ball. -/
theorem ball_cells_subset {n : ℕ} (S : Finset (Cell n)) {δ r : ℝ}
    (x : Space n) :
    cellUnion δ (S.filter (fun z => dist (cellCenter δ z) x ≤ r)) ⊆
      Metric.closedBall x (r+(n:ℝ)*δ/2) := by
  intro y hy
  obtain ⟨z,hz,hyz⟩ := Set.mem_iUnion₂.mp hy
  have hdist := (mem_filter.mp hz).2
  have hcell := cell_center_distance hyz
  exact (dist_triangle y (cellCenter δ z) x).trans (by linarith)

/-- The actual expected count in any finite ball mask is bounded by the
normalized intersection mass in the enlarged physical ball. -/
theorem ball_weight_le {n : ℕ} (S : Finset (Cell n)) {δ r : ℝ}
    (hδ : 0 < δ) (x : Space n) {Y : Set (Space n)} (hY : MeasurableSet Y)
    (hfin : (volume : Measure (Space n)) Y ≠ ∞) :
    (∑ z ∈ S.filter (fun z => dist (cellCenter δ z) x ≤ r), weight Y δ z) ≤
      (volume : Measure (Space n)).real (Y ∩ Metric.closedBall x (r+(n:ℝ)*δ/2))/δ^n := by
  rw [weight_sum hδ _ hY]
  apply div_le_div_of_nonneg_right _ (pow_pos hδ n).le
  exact measureReal_mono (Set.inter_subset_inter_right _ (ball_cells_subset S x))
    (measure_ne_top_of_subset Set.inter_subset_left hfin)

/-- Actual full two ends controls every ball-mask mean. If the enlarged
radius exceeds one, total mass gives the same bound; no sub-mesh or above-one
two-ends assumption is used. -/
theorem ball_weight_two_ends {n : ℕ} (S : Finset (Cell n)) {δ r B alpha : ℝ}
    (hδ : 0 < δ) (hr : δ ≤ r) (hB : 1 ≤ B) (ha : 0 ≤ alpha)
    (x : Space n) {Y : Set (Space n)} (hY : MeasurableSet Y)
    (hfin : (volume : Measure (Space n)) Y ≠ ∞)
    (hends : ∀ y t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space n)).real (Y ∩ Metric.closedBall y t) ≤
        B*t^alpha*(volume : Measure (Space n)).real Y) :
    (∑ z ∈ S.filter (fun z => dist (cellCenter δ z) x ≤ r), weight Y δ z) ≤
      B*(1+(n:ℝ)/2)^alpha*r^alpha*((volume : Measure (Space n)).real Y/δ^n) := by
  let g : ℝ := 1+(n:ℝ)/2
  have hg1 : 1 ≤ g := by
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [g]
    linarith
  have hr0 : 0 < r := hδ.trans_le hr
  have hrg : r ≤ g*r := le_mul_of_one_le_left hr0.le hg1
  have hexpand : r+(n:ℝ)*δ/2 ≤ g*r := by
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    dsimp [g]
    nlinarith
  have hball : (volume : Measure (Space n)).real (Y ∩ Metric.closedBall x (r+(n:ℝ)*δ/2)) ≤
      (volume : Measure (Space n)).real (Y ∩ Metric.closedBall x (g*r)) :=
    measureReal_mono (Set.inter_subset_inter_right _ (Metric.closedBall_subset_closedBall hexpand))
      (measure_ne_top_of_subset Set.inter_subset_left hfin)
  have hbound : (volume : Measure (Space n)).real (Y ∩ Metric.closedBall x (g*r)) ≤
      B*(g*r)^alpha*(volume : Measure (Space n)).real Y := by
    by_cases hsmall : g*r ≤ 1
    · exact hends x (g*r) (hr.trans hrg) hsmall
    · have hone : 1 ≤ (g*r)^alpha := Real.one_le_rpow (le_of_not_ge hsmall) ha
      have hcoef : 1 ≤ B*(g*r)^alpha := by nlinarith
      exact (measureReal_mono Set.inter_subset_left hfin).trans
        (le_mul_of_one_le_left measureReal_nonneg hcoef)
  have hh := (ball_weight_le S hδ x hY hfin).trans
    (div_le_div_of_nonneg_right (hball.trans hbound) (pow_pos hδ n).le)
  rw [Real.mul_rpow (zero_le_one.trans hg1) hr0.le] at hh
  exact hh.trans_eq (by dsimp [g]; ring)

/-- Finite indicator sums are the literal incidence populations. -/
theorem indicator_sum_count {n M : ℕ} (G : Fin M → Set (Space n))
    (indices : Finset (Fin M)) (x : Space n) :
    (∑ i ∈ indices, MeasurableEnergy.oneIndicator (G i) x) =
      ((indices.filter (fun i => x ∈ G i)).card : ℝ) := by
  simp [MeasurableEnergy.oneIndicator,Set.indicator_apply,Finset.sum_boole]

/-- Integrating actual pointwise incidence domination over one cell gives
actual cell-mass domination. All integrability comes from the finite cell. -/
theorem cell_incidence_mass_le {n M : ℕ} (G : Fin M → Set (Space n))
    (indices : Finset (Fin M)) {C δ : ℝ} (z : Cell n)
    (hG : ∀ i, MeasurableSet (G i))
    (hpoint : ∀ᵐ x ∂(volume : Measure (Space n)),
      ((indices.filter (fun i => x ∈ G i)).card : ℝ) ≤
        C*((univ.filter (fun i => x ∈ G i)).card : ℝ)) :
    (∑ i ∈ indices, (volume : Measure (Space n)).real (G i ∩ gridCell δ z)) ≤
      C*∑ i, (volume : Measure (Space n)).real (G i ∩ gridCell δ z) := by
  have hint : ∀ i, Integrable (MeasurableEnergy.oneIndicator (G i ∩ gridCell δ z)) volume :=
    fun i => MeasurableEnergy.indicator_integrable ((hG i).inter (measurable_gridCell δ z))
      (measure_ne_top_of_subset Set.inter_subset_right (finite_gridCell δ z))
  have hfg : ∀ᵐ x ∂(volume : Measure (Space n)),
      (∑ i ∈ indices, MeasurableEnergy.oneIndicator (G i ∩ gridCell δ z) x) ≤
        C*∑ i, MeasurableEnergy.oneIndicator (G i ∩ gridCell δ z) x := by
    filter_upwards [hpoint] with x hx
    by_cases hz : x ∈ gridCell δ z
    · have he : ∀ i, MeasurableEnergy.oneIndicator (G i ∩ gridCell δ z) x =
          MeasurableEnergy.oneIndicator (G i) x := by
        intro i
        simp [MeasurableEnergy.oneIndicator,Set.indicator_apply,hz]
      simp_rw [he,indicator_sum_count]
      exact hx
    · simp [MeasurableEnergy.oneIndicator,hz]
  have hh := integral_mono_ae (integrable_finsetSum indices (fun i _ => hint i))
    ((integrable_finsetSum univ (fun i _ => hint i)).const_mul C) hfg
  rw [integral_finsetSum _ (fun i _ => hint i),integral_const_mul,
    integral_finsetSum _ (fun i _ => hint i)] at hh
  simp_rw [MeasurableEnergy.indicator_integral ((hG _).inter (measurable_gridCell δ z))] at hh
  exact hh

/-- The same integrated bound for the literal probabilities in (6.5). -/
theorem cell_incidence_weight_le {n M : ℕ} (G : Fin M → Set (Space n))
    (indices : Finset (Fin M)) {C δ : ℝ} (hδ : 0 < δ) (z : Cell n)
    (hG : ∀ i, MeasurableSet (G i))
    (hpoint : ∀ᵐ x ∂(volume : Measure (Space n)),
      ((indices.filter (fun i => x ∈ G i)).card : ℝ) ≤
        C*((univ.filter (fun i => x ∈ G i)).card : ℝ)) :
    (∑ i ∈ indices, weight (G i) δ z) ≤ C*∑ i, weight (G i) δ z := by
  have hh := div_le_div_of_nonneg_right (cell_incidence_mass_le G indices (δ := δ) z hG hpoint)
    (pow_pos hδ n).le
  simp only [weight,← sum_div]
  exact hh.trans_eq (by ring)

/-- The original finite direction tests use open radius-2theta caps. The
pointwise hypothesis is only at that tested radius and may hold almost everywhere. -/
theorem cap_mean_le {n M : ℕ} (F : TubeFamily n M) (G : Fin M → Set (Space n))
    {C δ theta : ℝ} (hδ : 0 < δ) (z : Cell n) (hG : ∀ i, MeasurableSet (G i))
    (hpoint : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ a : Fin M,
      ((univ.filter (fun i => x ∈ G i ∧
        projectiveDistance (F.tube a).direction (F.tube i).direction < 2*theta)).card : ℝ) ≤
          C*((univ.filter (fun i => x ∈ G i)).card : ℝ)) (a : Fin M) :
    (∑ i, if SamplingCapTests.cap F theta a i then weight (G i) δ z else 0) ≤
      C*∑ i, weight (G i) δ z := by
  let indices := univ.filter (fun i => SamplingCapTests.cap F theta a i = true)
  have hpoint' : ∀ᵐ x ∂(volume : Measure (Space n)),
      ((indices.filter (fun i => x ∈ G i)).card : ℝ) ≤
        C*((univ.filter (fun i => x ∈ G i)).card : ℝ) := by
    filter_upwards [hpoint] with x hx
    have he : indices.filter (fun i => x ∈ G i) = univ.filter (fun i => x ∈ G i ∧
        projectiveDistance (F.tube a).direction (F.tube i).direction < 2*theta) := by
      ext i
      simp [indices,SamplingCapTests.cap,and_comm]
    rw [he]
    exact hx a
  have hh := cell_incidence_weight_le G indices hδ z hG hpoint'
  simpa only [indices,sum_filter,Bool.coe_iff_coe] using hh

/-- Actual angular broadness, integrated over cells, supplies the radius-2theta
mean bound. The open test is a subset of the closed cap used by Broad. -/
theorem cap_mean_from_broad {n M : ℕ} (F : TubeFamily n M) (G : Fin M → Set (Space n))
    {K beta δ theta : ℝ} (hδ : 0 < δ) (htest : δ ≤ 2*theta) (z : Cell n)
    (hG : ∀ i, MeasurableSet (G i))
    (hbroad : ∀ᵐ x ∂(volume : Measure (Space n)),
      AngularDecomposition.Broad F (univ.filter (fun i => x ∈ G i)) δ beta 1 K)
    (a : Fin M) :
    (∑ i, if SamplingCapTests.cap F theta a i then weight (G i) δ z else 0) ≤
      K*(2*theta)^beta*∑ i, weight (G i) δ z := by
  apply cap_mean_le F G hδ z hG _ a
  filter_upwards [hbroad] with x hx
  intro a
  have hh := hx (F.tube a).direction (2*theta) htest
  have hsub : univ.filter (fun i => x ∈ G i ∧
      projectiveDistance (F.tube a).direction (F.tube i).direction < 2*theta) ⊆
      AngularDecomposition.cap F (univ.filter (fun i => x ∈ G i)) (F.tube a).direction (2*theta) := by
    intro i hi
    obtain ⟨_,hi,hcap⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,hi⟩,?_⟩
    rw [ProjectiveGeometry.projective_symm]
    exact hcap.le
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans (by simpa only [div_one] using hh)

/-- Probabilities on the unchanged tube indices and actual finite cell subtype. -/
def weights {n M : ℕ} (Y : Fin M → Set (Space n)) (δ : ℝ) (S : Finset (Cell n)) :
    Fin M → ↥S → ℝ := fun i z => weight (Y i) δ z.val

theorem fullMean_eq {n M : ℕ} (tube : Fin M → UnitTube n)
    (Full Y : Fin M → Set (Space n)) {δ width R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ∀ i, ‖(tube i).base‖ ≤ R)
    (hFull : ∀ i, Full i ⊆ (tube i).carrier (width*δ))
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ Full i) (i : Fin M) :
    KakeyaSamplingApplication.fullMean (weights Y δ (support tube Full δ width R)) i =
      (volume : Measure (Space n)).real (Y i)/δ^n :=
  support_mean tube Full hδ hδ1 hw hbase hFull i (hY i) (hsub i)

/-- The total expected marked population equals the normalized actual marked
mass, including marks in all original cells and all unchanged tube indices. -/
theorem marked_total_mean {n M : ℕ} (tube : Fin M → UnitTube n)
    (Full G : Fin M → Set (Space n)) {δ width R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ∀ i, ‖(tube i).base‖ ≤ R)
    (hFull : ∀ i, Full i ⊆ (tube i).carrier (width*δ))
    (hG : ∀ i, MeasurableSet (G i)) (hsub : ∀ i, G i ⊆ Full i) :
    (∑ z : support tube Full δ width R,
      KakeyaSamplingApplication.markedMean (weights G δ (support tube Full δ width R)) z) =
        (∑ i, (volume : Measure (Space n)).real (G i))/δ^n := by
  simp only [KakeyaSamplingApplication.markedMean,weights]
  rw [sum_comm]
  simp_rw [support_mean tube Full hδ hδ1 hw hbase hFull _ (hG _) (hsub _)]
  exact (sum_div ..).symm

/-- The Boolean ball-mask expectation is literally the corresponding weighted
sum on original cell labels. -/
theorem ballMean_eq {n M J : ℕ} (Y : Fin M → Set (Space n))
    (S : Finset (Cell n)) (δ : ℝ) (i : Fin M) (t : SamplingBallTests.Test S J) :
    KakeyaSamplingApplication.ballMean (weights Y δ S) (SamplingBallTests.mask δ) i t =
      ∑ z ∈ SamplingBallTests.testCells S δ t, weight (Y i) δ z := by
  simp only [KakeyaSamplingApplication.ballMean,weights,SamplingBallTests.mask,decide_eq_true_eq]
  rw [← sum_subtype S (fun _ => Iff.rfl)
    (fun z => if dist (cellCenter δ z) (cellCenter δ t.1.val) ≤ SamplingBallTests.testRadius t
      then weight (Y i) δ z else 0)]
  simp only [SamplingBallTests.testCells,sum_filter]

/-- The genuine finite ball tests satisfy the geometric expectation bound
required by SamplingApplication, relative to the exact original tube mean. -/
theorem ballMean_two_ends {n M J : ℕ} (tube : Fin M → UnitTube n)
    (Full : Fin M → Set (Space n)) {δ width R B alpha : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (hB : 1 ≤ B) (ha : 0 ≤ alpha)
    (hbottom : δ ≤ Localization.radius J 0)
    (hbase : ∀ i, ‖(tube i).base‖ ≤ R)
    (hFull : ∀ i, Full i ⊆ (tube i).carrier (width*δ))
    (hmeas : ∀ i, MeasurableSet (Full i))
    (hends : ∀ i y r, δ ≤ r → r ≤ 1 →
      (volume : Measure (Space n)).real (Full i ∩ Metric.closedBall y r) ≤
        B*r^alpha*(volume : Measure (Space n)).real (Full i))
    (i : Fin M) (t : SamplingBallTests.Test (support tube Full δ width R) J) :
    KakeyaSamplingApplication.ballMean (weights Full δ (support tube Full δ width R))
      (SamplingBallTests.mask δ) i t ≤
        B*(1+(n:ℝ)/2)^alpha*(SamplingBallTests.testRadius t)^alpha*
          KakeyaSamplingApplication.fullMean (weights Full δ (support tube Full δ width R)) i := by
  rw [ballMean_eq,fullMean_eq tube Full Full hδ hδ1 hw hbase hFull hmeas (fun _ => Set.Subset.rfl)]
  exact ball_weight_two_ends _ hδ (by linarith [(SamplingBallTests.radius_bounds hbottom t).1])
    hB ha _ (hmeas i) (measure_ne_top_of_subset (hFull i) (TubeVolume.carrier_finite _ _)) (hends i)

/-- Source (6.4) only needs to hold almost everywhere and only between delta
and one. The finite mean uses precisely the open doubled-radius test. -/
theorem cap_mean_from_bounded_radii {n M : ℕ} (F : TubeFamily n M)
    (G : Fin M → Set (Space n)) {K beta δ theta : ℝ}
    (hδ : 0 < δ) (htest : δ ≤ 2*theta) (htest1 : 2*theta ≤ 1) (z : Cell n)
    (hG : ∀ i, MeasurableSet (G i))
    (hbroad : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ v : Space n, ‖v‖=1 → ∀ r : ℝ,
      δ ≤ r → r ≤ 1 →
      ((univ.filter (fun i => x ∈ G i ∧ projectiveDistance (F.tube i).direction v ≤ r)).card : ℝ) ≤
        K*r^beta*((univ.filter (fun i => x ∈ G i)).card : ℝ)) (a : Fin M) :
    (∑ i, if SamplingCapTests.cap F theta a i then weight (G i) δ z else 0) ≤
      K*(2*theta)^beta*∑ i, weight (G i) δ z := by
  apply cap_mean_le F G hδ z hG _ a
  filter_upwards [hbroad] with x hx
  intro a
  have hh := hx (F.tube a).direction (F.tube a).unit_direction (2*theta) htest htest1
  apply le_trans _ hh
  apply Nat.cast_le.mpr
  apply card_le_card
  intro i hi
  obtain ⟨_,hi,hcap⟩ := mem_filter.mp hi
  exact mem_filter.mpr ⟨mem_univ _,hi,by rw [ProjectiveGeometry.projective_symm]; exact hcap.le⟩

/-- The integrated geometric cap estimate discharges the exact factor-1000
expectation premise in the coupled sampling theorem. -/
theorem capMean_admissible {n M : ℕ} (F : TubeFamily n M)
    (G : Fin M → Set (Space n)) (S : Finset (Cell n)) {K beta δ theta : ℝ}
    (hδ : 0 < δ) (htest : δ ≤ 2*theta) (htest1 : 2*theta ≤ 1)
    (hcoef : 1000*(K*(2*theta)^beta) ≤ 1)
    (hG : ∀ i, MeasurableSet (G i))
    (hbroad : ∀ᵐ x ∂(volume : Measure (Space n)), ∀ v : Space n, ‖v‖=1 → ∀ r : ℝ,
      δ ≤ r → r ≤ 1 →
      ((univ.filter (fun i => x ∈ G i ∧ projectiveDistance (F.tube i).direction v ≤ r)).card : ℝ) ≤
        K*r^beta*((univ.filter (fun i => x ∈ G i)).card : ℝ))
    (z : ↥S) (a : Fin M) :
    1000*KakeyaSamplingApplication.capMean (weights G δ S) (SamplingCapTests.cap F theta) z a ≤
      KakeyaSamplingApplication.markedMean (weights G δ S) z := by
  have hh := cap_mean_from_bounded_radii F G hδ htest htest1 z.val hG hbroad a
  have hn : 0 ≤ ∑ i, weight (G i) δ z.val := sum_nonneg (fun i _ => weight_nonneg (G i) hδ z.val)
  have hmul := mul_le_mul_of_nonneg_right hcoef hn
  change 1000*(∑ i, if SamplingCapTests.cap F theta a i then weight (G i) δ z.val else 0) ≤
    ∑ i, weight (G i) δ z.val
  nlinarith

/-- Comparable actual physical full masses give the two expected density
bounds without any missing cell contribution. -/
theorem fullMean_density {n M : ℕ} (tube : Fin M → UnitTube (n+1))
    (Full : Fin M → Set (Space (n+1))) {δ width R lam c₀ C₀ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hbase : ∀ i, ‖(tube i).base‖ ≤ R)
    (hFull : ∀ i, Full i ⊆ (tube i).carrier (width*δ))
    (hmeas : ∀ i, MeasurableSet (Full i))
    (hmass : ∀ i, c₀*lam*δ^n ≤ (volume : Measure (Space (n+1))).real (Full i) ∧
      (volume : Measure (Space (n+1))).real (Full i) ≤ C₀*lam*δ^n) (i : Fin M) :
    c₀*lam/δ ≤ KakeyaSamplingApplication.fullMean
      (weights Full δ (support tube Full δ width R)) i ∧
      KakeyaSamplingApplication.fullMean (weights Full δ (support tube Full δ width R)) i ≤ C₀*lam/δ := by
  rw [fullMean_eq tube Full Full hδ hδ1 hw hbase hFull hmeas (fun _ => Set.Subset.rfl)]
  have hid (a : ℝ) : (a*lam*δ^n)/δ^(n+1) = a*lam/δ := by
    rw [pow_succ]
    field_simp
  constructor
  · exact (hid c₀).symm.trans_le (div_le_div_of_nonneg_right (hmass i).1 (pow_pos hδ (n+1)).le)
  · exact (div_le_div_of_nonneg_right (hmass i).2 (pow_pos hδ (n+1)).le).trans_eq (hid C₀)

end
end KakeyaFormal.SamplingMeans
