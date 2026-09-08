import GridShadingMeasure
import MeasurableRescaling

/-! Common homotheties turn realized grid shadings into unit-width measurable
shadings without changing their directions or their actual overlap pattern. -/
namespace KakeyaFormal.WidthNormalization
open MeasureTheory Set Rescaling MeasurableRescaling GridShadingMeasure
open scoped BigOperators ENNReal
noncomputable section
open Classical

/-- One shared spatial map, with the shortened axis extended to a unit segment. -/
def normalizedTube {k : ℕ} (T : UnitTube k) (W : ℝ) : UnitTube k :=
  Rescaling.tube T W 0 0

def normalizedSet {k : ℕ} (W : ℝ) (Y : Set (Space k)) : Set (Space k) :=
  rescale W 0 '' Y

lemma normalized_direction {k : ℕ} (T : UnitTube k) (W : ℝ) :
    (normalizedTube T W).direction = T.direction := rfl

/-- Physical widths shrink by W, while the shortened original unit segment
is contained in the new actual unit segment. -/
theorem normalized_carrier {k : ℕ} (T : UnitTube k) {W δ : ℝ} (hW : 1 ≤ W)
    (Y : Set (Space k)) (hsub : Y ⊆ T.carrier (W*δ)) :
    normalizedSet W Y ⊆ (normalizedTube T W).carrier δ := by
  have hW0 : 0 < W := by linarith
  rintro x ⟨y,hy,rfl⟩
  obtain ⟨t,ht,hyt⟩ := hsub hy
  have haxis := rescale_axisPoint T hW0.ne' (0:Space k) 0 (t/W)
  have heq : (0:ℝ)+W*(t/W) = t := by field_simp; ring
  rw [heq] at haxis
  refine ⟨t/W,⟨div_nonneg ht.1 hW0.le,(div_le_one hW0).mpr (ht.2.trans hW)⟩,?_⟩
  change dist (rescale W 0 y) ((Rescaling.tube T W 0 0).axisPoint (t/W)) ≤ δ
  rw [← haxis,rescale_distance hW0]
  exact (div_le_iff₀ hW0).mpr (by simpa only [mul_comm] using hyt)

lemma normalized_measurable {k : ℕ} {W : ℝ} (hW : 0 < W)
    {Y : Set (Space k)} (hY : MeasurableSet Y) : MeasurableSet (normalizedSet W Y) :=
  image_measurable hW.ne' 0 hY

lemma normalized_finite {k : ℕ} {W : ℝ} (hW : 0 < W)
    {Y : Set (Space k)} (hY : (volume : Measure (Space k)) Y ≠ ∞) :
    (volume : Measure (Space k)) (normalizedSet W Y) ≠ ∞ :=
  image_finite hW 0 hY

/-- Exact mass scaling under the common map. -/
theorem normalized_volume {k : ℕ} {W : ℝ} (hW : 0 < W) (Y : Set (Space k)) :
    (volume : Measure (Space k)).real (normalizedSet W Y) =
      (volume : Measure (Space k)).real Y/W^k := image_volume hW 0 Y

theorem normalized_union_volume {k : ℕ} {I : Type*} {W : ℝ} (hW : 0 < W)
    (Y : I → Set (Space k)) :
    (volume : Measure (Space k)).real (⋃ i, normalizedSet W (Y i)) =
      (volume : Measure (Space k)).real (⋃ i, Y i)/W^k := union_volume hW 0 Y

/-- Pointwise membership is transported by one explicit inverse map. -/
theorem normalized_membership {k : ℕ} {W : ℝ} (hW : 0 < W)
    (Y : Set (Space k)) (x : Space k) :
    x ∈ normalizedSet W Y ↔ inverse W 0 x ∈ Y := by
  rw [normalizedSet,image_eq_preimage hW.ne']
  rfl

/-- All two-ends ball tests transport. The input allows radii above one, as
provided by the finite-grid realization theorem using its total-mass branch. -/
theorem normalized_two_ends {k : ℕ} {W δ B alpha : ℝ} (hW : 0 < W) (hδ : 0 < δ)
    (Y : Set (Space k))
    (hends : ∀ x : Space k, ∀ r : ℝ, δ ≤ r →
      (volume : Measure (Space k)).real (Y ∩ Metric.closedBall x r) ≤
        B*r^alpha*(volume : Measure (Space k)).real Y) :
    ∀ x : Space k, ∀ r : ℝ, δ/W ≤ r →
      (volume : Measure (Space k)).real (normalizedSet W Y ∩ Metric.closedBall x r) ≤
        (B*W^alpha)*r^alpha*(volume : Measure (Space k)).real (normalizedSet W Y) := by
  intro x r hr
  have hr0 : 0 < r := (div_pos hδ hW).trans_le hr
  have hlo : δ ≤ W*r := by simpa only [mul_comm] using (div_le_iff₀ hW).mp hr
  have hh := div_le_div_of_nonneg_right (hends (inverse W 0 x) (W*r) hlo) (pow_pos hW k).le
  change (volume : Measure (Space k)).real ((rescale W 0 '' Y) ∩ Metric.closedBall x r) ≤ _
  rw [← image_inter_ball hW,image_volume hW,normalized_volume hW]
  rw [Real.mul_rpow hW.le hr0.le] at hh
  simpa only [mul_div_assoc,mul_assoc] using hh

/-- The fixed dimension/width factor used for grid realization. -/
def widthFactor (k : ℕ) (width : ℝ) : ℝ := max 1 (width+(k:ℝ)/2)

lemma widthFactor_ge_one (k : ℕ) (width : ℝ) : 1 ≤ widthFactor k width := le_max_left _ _

lemma widthFactor_pos (k : ℕ) (width : ℝ) : 0 < widthFactor k width :=
  zero_lt_one.trans_le (widthFactor_ge_one k width)

/-- Actual grid-cell unions become measurable shadings of physical radius δ
under a single common transform. -/
theorem grid_carrier {M k : ℕ} (F : TubeFamily k M) {δ width : ℝ}
    (hδ : 0 < δ) (hadm : F.Admissible width δ) (i : Fin M) :
    normalizedSet (widthFactor k width) (cellUnion δ (F.shade i)) ⊆
      (normalizedTube (F.tube i) (widthFactor k width)).carrier δ := by
  apply normalized_carrier _ (widthFactor_ge_one k width)
  intro x hx
  obtain ⟨t,ht,hd⟩ := cellUnion_carrier (F.tube i) (F.shade i) hδ (hadm i) hx
  refine ⟨t,ht,hd.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le

/-- The realized density has an exact fixed-factor expression. -/
theorem grid_mass {k : ℕ} (S : Finset (Cell k)) {δ W : ℝ} (hδ : 0 < δ) (hW : 0 < W) :
    (volume : Measure (Space k)).real (normalizedSet W (cellUnion δ S)) =
      δ^k*(S.card:ℝ)/W^k := by rw [normalized_volume hW,cellUnion_volume hδ]

/-- The original finite union and its measurable realization retain exactly
one common volume factor, irrespective of tube overlaps. -/
theorem grid_union_mass {M k : ℕ} (F : TubeFamily k M) {δ W : ℝ}
    (hδ : 0 < δ) (hW : 0 < W) :
    (volume : Measure (Space k)).real (⋃ i, normalizedSet W (cellUnion δ (F.shade i))) =
      δ^k*(F.unionCells.card:ℝ)/W^k := by
  rw [normalized_union_volume hW,family_union,cellUnion_volume hδ]

/-- Literal finite incidence patterns, including angular subsets, survive the
common width normalization at every point. -/
theorem grid_membership {k : ℕ} (S : Finset (Cell k)) {δ W : ℝ}
    (hδ : 0 < δ) (hW : 0 < W) (x : Space k) :
    x ∈ normalizedSet W (cellUnion δ S) ↔ GridCells.label δ (inverse W 0 x) ∈ S := by
  rw [normalized_membership hW,mem_cellUnion hδ]

end
end KakeyaFormal.WidthNormalization
