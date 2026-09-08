import TubeVolume
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-! The actual Kakeya averaging operator on Euclidean unit directions.
Indicator averages have a finite positive denominator and a bounded real
supremum. General nonnegative averages and suprema remain ENNReal-valued;
no finiteness or measurability of an uncountable supremum is asserted here. -/
namespace KakeyaFormal.KakeyaOperator
open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section

abbrev Direction (n : ℕ) := ↥(Metric.sphere (0 : Space n) 1)

def sphereMeasure (n : ℕ) : Measure (Direction n) :=
  (volume : Measure (Space n)).toSphere

theorem direction_norm {n : ℕ} (v : Direction n) : ‖v.val‖ = 1 := by
  simpa only [Metric.mem_sphere,dist_zero_right] using v.property

def tube {n : ℕ} (v : Direction n) (b : Space n) : UnitTube n where
  base := b
  direction := v.val
  unit_direction := direction_norm v

/-- The average of a nonnegative extended-real function on an actual carrier. -/
def average {n : ℕ} (δ : ℝ) (f : Space n → ℝ≥0∞) (b : Space n) (v : Direction n) : ℝ≥0∞ :=
  (∫⁻ x in (tube v b).carrier δ, f x ∂(volume : Measure (Space n))) /
    (volume : Measure (Space n)) ((tube v b).carrier δ)

/-- Extended-real supremum over every original tube position. -/
def maximal {n : ℕ} (δ : ℝ) (f : Space n → ℝ≥0∞) (v : Direction n) : ℝ≥0∞ :=
  ⨆ b : Space n, average δ f b v

/-- Real functions enter the nonnegative operator by their absolute value. -/
def normAverage {n : ℕ} (δ : ℝ) (f : Space n → ℝ) (b : Space n) (v : Direction n) : ℝ≥0∞ :=
  average δ (fun x => ENNReal.ofReal |f x|) b v

def normMaximal {n : ℕ} (δ : ℝ) (f : Space n → ℝ) (v : Direction n) : ℝ≥0∞ :=
  maximal δ (fun x => ENNReal.ofReal |f x|) v

/-- The numerator is always finite because the actual tube carrier is finite. -/
def indicatorDensity {n : ℕ} (δ : ℝ) (E : Set (Space n)) (b : Space n) (v : Direction n) : ℝ :=
  (volume : Measure (Space n)).real (E ∩ (tube v b).carrier δ) /
    (volume : Measure (Space n)).real ((tube v b).carrier δ)

def indicatorMaximal {n : ℕ} (δ : ℝ) (E : Set (Space n)) (v : Direction n) : ℝ :=
  ⨆ b : Space n, indicatorDensity δ E b v

def indicatorLevel {n : ℕ} (δ : ℝ) (E : Set (Space n)) (lam : ℝ) : Set (Direction n) :=
  {v | lam < indicatorMaximal δ E v}

theorem carrier_finite {n : ℕ} (v : Direction n) (b : Space n) (δ : ℝ) :
    (volume : Measure (Space n)) ((tube v b).carrier δ) ≠ ∞ :=
  TubeVolume.carrier_finite _ _

theorem carrier_real_pos {n : ℕ} (v : Direction n) (b : Space n) {δ : ℝ} (hδ : 0 < δ) :
    0 < (volume : Measure (Space n)).real ((tube v b).carrier δ) := by
  have hu := TubeVolume.unitBallVolume_pos n
  exact (by positivity : 0 < (TubeVolume.unitBallVolume n/((2:ℝ)^(n+1)))*δ^n/δ).trans_le
    (TubeVolume.carrier_volume_lower _ hδ)

theorem carrier_pos {n : ℕ} (v : Direction n) (b : Space n) {δ : ℝ} (hδ : 0 < δ) :
    0 < (volume : Measure (Space n)) ((tube v b).carrier δ) :=
  (ENNReal.toReal_pos_iff.mp (carrier_real_pos v b hδ)).1

theorem intersection_finite {n : ℕ} (v : Direction n) (b : Space n) (δ : ℝ) (E : Set (Space n)) :
    (volume : Measure (Space n)) (E ∩ (tube v b).carrier δ) ≠ ∞ :=
  measure_ne_top_of_subset inter_subset_right (carrier_finite v b δ)

theorem indicatorDensity_nonneg {n : ℕ} (δ : ℝ) (E : Set (Space n)) (b : Space n) (v : Direction n) :
    0 ≤ indicatorDensity δ E b v := div_nonneg measureReal_nonneg measureReal_nonneg

theorem indicatorDensity_le_one {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (b : Space n) (v : Direction n) : indicatorDensity δ E b v ≤ 1 := by
  apply (div_le_one (carrier_real_pos v b hδ)).mpr
  exact measureReal_mono inter_subset_right (carrier_finite v b δ)

theorem indicatorDensity_bddAbove {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (v : Direction n) :
    BddAbove (Set.range (fun b : Space n => indicatorDensity δ E b v)) := by
  refine ⟨1,?_⟩
  rintro _ ⟨b,rfl⟩
  exact indicatorDensity_le_one hδ E b v

theorem indicatorDensity_le_maximal {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (b : Space n) (v : Direction n) :
    indicatorDensity δ E b v ≤ indicatorMaximal δ E v :=
  le_ciSup (indicatorDensity_bddAbove hδ E v) b

theorem indicatorMaximal_nonneg {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (v : Direction n) : 0 ≤ indicatorMaximal δ E v :=
  (indicatorDensity_nonneg δ E 0 v).trans (indicatorDensity_le_maximal hδ E 0 v)

theorem indicatorMaximal_le_one {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (v : Direction n) : indicatorMaximal δ E v ≤ 1 :=
  ciSup_le (fun b => indicatorDensity_le_one hδ E b v)

/-- A strict real supremum level has an actual tube witness at an original position. -/
theorem indicatorMaximal_gt_iff {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (v : Direction n) (lam : ℝ) :
    lam < indicatorMaximal δ E v ↔ ∃ b : Space n, lam < indicatorDensity δ E b v :=
  lt_ciSup_iff (indicatorDensity_bddAbove hδ E v)

/-- The finite positive denominator turns strict average witnesses into
strict actual shading-mass witnesses with no approximation. -/
theorem indicatorDensity_gt_iff {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (b : Space n) (v : Direction n) (lam : ℝ) :
    lam < indicatorDensity δ E b v ↔
      lam*(volume : Measure (Space n)).real ((tube v b).carrier δ) <
        (volume : Measure (Space n)).real (E ∩ (tube v b).carrier δ) :=
  lt_div_iff₀ (carrier_real_pos v b hδ)

theorem mem_indicatorLevel_iff {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (v : Direction n) (lam : ℝ) :
    v ∈ indicatorLevel δ E lam ↔ ∃ b : Space n,
      lam*(volume : Measure (Space n)).real ((tube v b).carrier δ) <
        (volume : Measure (Space n)).real (E ∩ (tube v b).carrier δ) := by
  change (lam < indicatorMaximal δ E v) ↔ _
  rw [indicatorMaximal_gt_iff hδ]
  simp_rw [indicatorDensity_gt_iff hδ]

theorem indicatorLevel_empty {n : ℕ} {δ lam : ℝ} (hδ : 0 < δ) (hlam : 1 ≤ lam)
    (E : Set (Space n)) : indicatorLevel δ E lam = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro v hv
  exact not_lt_of_ge ((indicatorMaximal_le_one hδ E v).trans hlam) hv

end
end KakeyaFormal.KakeyaOperator
