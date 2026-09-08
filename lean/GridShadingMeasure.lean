import GridCells
import AngularDecomposition
import MeasurableEnergy

/-! Exact finite-grid shading realization by measurable half-open cell unions.
Pointwise membership, mass, union support and angular broadness are preserved;
physical carrier width changes by only a fixed dimension factor. -/
namespace KakeyaFormal.GridShadingMeasure
open GridCells MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Classical

/-- The actual union of the indicated half-open grid cells. -/
def cellUnion {k : ℕ} (δ : ℝ) (S : Finset (Cell k)) : Set (Space k) :=
  ⋃ q ∈ S, gridCell δ q

lemma cellUnion_measurable {k : ℕ} (δ : ℝ) (S : Finset (Cell k)) :
    MeasurableSet (cellUnion δ S) :=
  Finset.measurableSet_biUnion _ (fun q _ => measurable_gridCell δ q)

lemma cellUnion_finite {k : ℕ} (δ : ℝ) (S : Finset (Cell k)) :
    (volume : Measure (Space k)) (cellUnion δ S) ≠ ∞ :=
  measure_biUnion_ne_top S.finite_toSet (fun q _ => finite_gridCell δ q)

/-- Exact pointwise membership uses the unique actual cell label. -/
lemma mem_cellUnion {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (S : Finset (Cell k)) (x : Space k) :
    x ∈ cellUnion δ S ↔ label δ x ∈ S := by
  simp only [cellUnion,Set.mem_iUnion]
  constructor
  · rintro ⟨q,hq,hx⟩
    rw [(mem_gridCell_iff_label hδ q x).mp hx]
    exact hq
  · intro hx
    exact ⟨label δ x,hx,gridCell_covers hδ x⟩

/-- Exact measure, including all shared boundaries by the half-open convention. -/
theorem cellUnion_volume {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (S : Finset (Cell k)) :
    (volume : Measure (Space k)).real (cellUnion δ S) = δ^k*(S.card:ℝ) := by
  have hh := measureReal_biUnion_finset (μ := (volume : Measure (Space k)))
    (s := S) (f := gridCell δ)
    (fun q _ z _ hqz => gridCell_disjoint hδ hqz)
    (fun q _ => measurable_gridCell δ q) (fun q _ => finite_gridCell δ q)
  simpa only [cellUnion,real_volume_gridCell hδ.le,Finset.sum_const,nsmul_eq_mul,mul_comm] using hh

lemma cellUnion_mono {k : ℕ} (δ : ℝ) {S T : Finset (Cell k)} (hST : S ⊆ T) :
    cellUnion δ S ⊆ cellUnion δ T := by
  intro x hx
  obtain ⟨q,hq,hxq⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨q,hST hq,hxq⟩

lemma cellUnion_biUnion {k : ℕ} {I : Type*} (δ : ℝ) (S : Finset I)
    (shading : I → Finset (Cell k)) :
    cellUnion δ (S.biUnion shading) = ⋃ i ∈ S, cellUnion δ (shading i) := by
  ext x
  simp only [cellUnion,Set.mem_iUnion,Finset.mem_biUnion]
  aesop

/-- Realizing all shadings does not enlarge the union beyond the realization of
the original finite union; in fact the two actual measurable sets are equal. -/
theorem family_union {M k : ℕ} (F : TubeFamily k M) (δ : ℝ) :
    (⋃ i, cellUnion δ (F.shade i)) = cellUnion δ F.unionCells := by
  simpa only [Finset.mem_univ,Set.iUnion_true,TubeFamily.unionCells] using
    (cellUnion_biUnion δ (Finset.univ : Finset (Fin M)) F.shade).symm

/-- Actual admissible fine-cell centers realize a measurable shading in a tube
with only the dimension-dependent physical width enlargement. -/
theorem cellUnion_carrier {k : ℕ} (T : UnitTube k) (S : Finset (Cell k))
    {δ width : ℝ} (hδ : 0 < δ)
    (hadm : ∀ q ∈ S, ∃ t ∈ Icc (0:ℝ) 1,
      dist (cellCenter δ q) (T.axisPoint t) ≤ width*δ) :
    cellUnion δ S ⊆ T.carrier ((width+(k:ℝ)/2)*δ) := by
  intro x hx
  have hq := (mem_cellUnion hδ S x).mp hx
  obtain ⟨t,ht,hqt⟩ := hadm (label δ x) hq
  have hc := cell_center_distance (gridCell_covers hδ x)
  have htri := dist_triangle x (cellCenter δ (label δ x)) (T.axisPoint t)
  exact ⟨t,ht,by nlinarith⟩

/-- Equality of actual pointwise tube index sets and finite grid incidences. -/
lemma pointwise_incidence {M k : ℕ} (shading : Fin M → Finset (Cell k))
    {δ : ℝ} (hδ : 0 < δ) (x : Space k) :
    Finset.univ.filter (fun i => x ∈ cellUnion δ (shading i)) =
      Finset.univ.filter (fun i => label δ x ∈ shading i) := by
  ext i
  simp only [Finset.mem_filter,mem_cellUnion hδ]

/-- Exact pointwise multiplicity; there is no null boundary exception. -/
lemma pointwise_multiplicity {M k : ℕ} (shading : Fin M → Finset (Cell k))
    {δ : ℝ} (hδ : 0 < δ) (x : Space k) :
    MeasurableEnergy.overlapCount (fun i => cellUnion δ (shading i)) x =
      (Finset.univ.filter (fun i => label δ x ∈ shading i)).card := by
  rw [MeasurableEnergy.overlapCount,pointwise_incidence shading hδ x]

/-- Finite angular broadness becomes literal measurable pointwise broadness
for every center and every radius, with exactly the same constants. -/
theorem pointwise_broadness {M k : ℕ} (F : TubeFamily k M)
    (shading : Fin M → Finset (Cell k)) {δ beta tau K : ℝ} (hδ : 0 < δ)
    (hbroad : ∀ q : Cell k,
      AngularDecomposition.Broad F (Finset.univ.filter (fun i => q ∈ shading i)) δ beta tau K) :
    ∀ x : Space k, ∀ center : Space k, ∀ r : ℝ, δ ≤ r →
      ((Finset.univ.filter (fun i => x ∈ cellUnion δ (shading i) ∧
        projectiveDistance (F.tube i).direction center ≤ r)).card:ℝ) ≤
      K*(r/tau)^beta*(MeasurableEnergy.overlapCount (fun i => cellUnion δ (shading i)) x:ℝ) := by
  intro x center r hr
  have hh := hbroad (label δ x) center r hr
  simpa only [AngularDecomposition.cap,Finset.filter_filter,mem_cellUnion hδ,
    pointwise_multiplicity shading hδ x] using hh

/-- Finite pointwise overlap between groups is preserved literally as well. -/
theorem group_overlap {I : Type*} {M k : ℕ} (groups : Finset I)
    (shading : I → Fin M → Finset (Cell k)) {δ K : ℝ} (hδ : 0 < δ)
    (hover : ∀ q : Cell k, ((groups.filter (fun g => ∃ i, q ∈ shading g i)).card:ℝ) ≤ K) :
    ∀ x : Space k, ((groups.filter (fun g => ∃ i, x ∈ cellUnion δ (shading g i))).card:ℝ) ≤ K := by
  intro x
  simpa only [mem_cellUnion hδ] using hover (label δ x)

/-- The total incidence mass is the cell volume times the actual incidence count. -/
theorem total_mass {M k : ℕ} (shading : Fin M → Finset (Cell k))
    {δ : ℝ} (hδ : 0 < δ) :
    (∑ i, (volume : Measure (Space k)).real (cellUnion δ (shading i))) =
      δ^k * ∑ i, ((shading i).card:ℝ) := by
  simp only [cellUnion_volume hδ,Finset.mul_sum]

/-- Every cell meeting a physical ball has its center in the explicitly
enlarged ball; no assertion about boundary measure is needed. -/
theorem ball_subset {k : ℕ} (S : Finset (Cell k)) {δ r : ℝ} (hδ : 0 < δ)
    (x : Space k) :
    cellUnion δ S ∩ Metric.closedBall x r ⊆
      cellUnion δ (S.filter (fun q => dist (cellCenter δ q) x ≤ r+(k:ℝ)*δ/2)) := by
  intro y hy
  apply (mem_cellUnion hδ _ y).mpr
  refine Finset.mem_filter.mpr ⟨(mem_cellUnion hδ S y).mp hy.1,?_⟩
  have hc := cell_center_distance (gridCell_covers hδ y)
  have ht := dist_triangle (cellCenter δ (label δ y)) y x
  have hb : dist y x ≤ r := hy.2
  rw [dist_comm (cellCenter δ (label δ y)) y] at ht
  linarith

/-- An actual finite center count controls the physical ball intersection. -/
theorem ball_volume_le {k : ℕ} (S : Finset (Cell k)) {δ r : ℝ} (hδ : 0 < δ)
    (x : Space k) :
    (volume : Measure (Space k)).real (cellUnion δ S ∩ Metric.closedBall x r) ≤
      δ^k * ((S.filter (fun q => dist (cellCenter δ q) x ≤ r+(k:ℝ)*δ/2)).card:ℝ) := by
  exact (measureReal_mono (ball_subset S hδ x) (cellUnion_finite δ _)).trans_eq
    (cellUnion_volume hδ _)

/-- All finite-grid two-ends tests imply all physical two-ends tests. The
dimension factor accounts for cell diameter, and tests above unit radius use
the finite total mass rather than an unavailable discrete premise. -/
theorem two_ends {k : ℕ} (S : Finset (Cell k)) {δ B alpha : ℝ}
    (hδ : 0 < δ) (hB : 1 ≤ B) (ha : 0 ≤ alpha)
    (hends : ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((S.filter (fun q => dist (cellCenter δ q) x ≤ r)).card:ℝ) ≤
        B*r^alpha*(S.card:ℝ)) :
    ∀ x : Space k, ∀ r : ℝ, δ ≤ r →
      (volume : Measure (Space k)).real (cellUnion δ S ∩ Metric.closedBall x r) ≤
        (B*(1+(k:ℝ)/2)^alpha)*r^alpha*(volume : Measure (Space k)).real (cellUnion δ S) := by
  intro x r hrδ
  have hr : 0 < r := hδ.trans_le hrδ
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hC : 0 < 1+(k:ℝ)/2 := by positivity
  have hsmall : r+(k:ℝ)*δ/2 ≤ (1+(k:ℝ)/2)*r := by nlinarith
  have hlo : δ ≤ (1+(k:ℝ)/2)*r := by nlinarith
  have hfactor : (B*(1+(k:ℝ)/2)^alpha)*r^alpha = B*((1+(k:ℝ)/2)*r)^alpha := by
    rw [Real.mul_rpow hC.le hr.le,mul_assoc]
  rw [hfactor]
  by_cases htop : (1+(k:ℝ)/2)*r ≤ 1
  · have hcard : ((S.filter (fun q => dist (cellCenter δ q) x ≤ r+(k:ℝ)*δ/2)).card:ℝ) ≤
        ((S.filter (fun q => dist (cellCenter δ q) x ≤ (1+(k:ℝ)/2)*r)).card:ℝ) := by
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro q hq
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hq).1,(Finset.mem_filter.mp hq).2.trans hsmall⟩
    have hb := hcard.trans (hends x ((1+(k:ℝ)/2)*r) hlo htop)
    have hm := (ball_volume_le S hδ x).trans (mul_le_mul_of_nonneg_left hb (pow_pos hδ k).le)
    rw [cellUnion_volume hδ]
    nlinarith [hm]
  · have hp : (1:ℝ) ≤ ((1+(k:ℝ)/2)*r)^alpha := Real.one_le_rpow (le_of_lt (lt_of_not_ge htop)) ha
    have hb : (1:ℝ) ≤ B*((1+(k:ℝ)/2)*r)^alpha := by nlinarith
    have hm : (volume : Measure (Space k)).real (cellUnion δ S ∩ Metric.closedBall x r) ≤
        (volume : Measure (Space k)).real (cellUnion δ S) :=
      measureReal_mono Set.inter_subset_left (cellUnion_finite δ S)
    exact hm.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hb (measureReal_nonneg : (0:ℝ) ≤ (volume : Measure (Space k)).real (cellUnion δ S)))

end
end KakeyaFormal.GridShadingMeasure
