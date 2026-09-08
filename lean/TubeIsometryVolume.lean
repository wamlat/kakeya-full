import EuclideanSplit
import KakeyaOperator
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Actual tube volume is independent of its base and unit direction.  An
explicit translation and orthogonal reflection identify every carrier with a
single reference carrier, including at zero or negative radius. -/
namespace KakeyaFormal.TubeIsometryVolume
open MeasureTheory Set
open scoped ENNReal
noncomputable section

def referenceTube (k : ℕ) : UnitTube (k+1) where
  base := 0
  direction := EuclideanSplit.axisUnit k
  unit_direction := EuclideanSplit.axisUnit_norm k

def normalize {k : ℕ} (T : UnitTube (k+1)) (x : Space (k+1)) : Space (k+1) :=
  EuclideanSplit.alignStem T.direction (x-T.base)

theorem normalize_axis {k : ℕ} (T : UnitTube (k+1)) (t : ℝ) :
    normalize T (T.axisPoint t) = (referenceTube k).axisPoint t := by
  simp [normalize,UnitTube.axisPoint,referenceTube,
    EuclideanSplit.alignStem_apply T.direction T.unit_direction]

theorem normalize_dist {k : ℕ} (T : UnitTube (k+1)) (x : Space (k+1)) (t : ℝ) :
    dist (normalize T x) ((referenceTube k).axisPoint t) = dist x (T.axisPoint t) := by
  rw [← normalize_axis T t]
  exact (EuclideanSplit.alignStem T.direction).dist_map _ _ |>.trans
    (by simp only [dist_eq_norm]; congr 1; abel)

theorem carrier_eq_preimage {k : ℕ} (T : UnitTube (k+1)) (δ : ℝ) :
    T.carrier δ = normalize T ⁻¹' (referenceTube k).carrier δ := by
  ext x
  simp only [UnitTube.carrier,mem_preimage,mem_ofPred_eq,normalize_dist]

theorem normalize_measurePreserving {k : ℕ} (T : UnitTube (k+1)) :
    MeasurePreserving (normalize T) := by
  exact (EuclideanSplit.alignStem T.direction).measurePreserving.comp
    (measurePreserving_add_right volume (-T.base))

theorem carrier_volume_reference {k : ℕ} (T : UnitTube (k+1)) (δ : ℝ) :
    (volume : Measure (Space (k+1))) (T.carrier δ) =
      volume ((referenceTube k).carrier δ) := by
  rw [carrier_eq_preimage]
  exact (normalize_measurePreserving T).measure_preimage
    (TubeVolume.carrier_measurable (referenceTube k) δ).nullMeasurableSet

/-- The equality concerns actual ENNReal carrier measures for every real radius. -/
theorem carrier_volume_eq {k : ℕ} (T U : UnitTube (k+1)) (δ : ℝ) :
    (volume : Measure (Space (k+1))) (T.carrier δ) = volume (U.carrier δ) :=
  (carrier_volume_reference T δ).trans (carrier_volume_reference U δ).symm

theorem carrier_real_volume_eq {k : ℕ} (T U : UnitTube (k+1)) (δ : ℝ) :
    (volume : Measure (Space (k+1))).real (T.carrier δ) = volume.real (U.carrier δ) :=
  congrArg ENNReal.toReal (carrier_volume_eq T U δ)

def referenceVolume (k : ℕ) (δ : ℝ) : ℝ≥0∞ :=
  (volume : Measure (Space (k+1))) ((referenceTube k).carrier δ)

theorem operator_carrier_volume {k : ℕ} (v : KakeyaOperator.Direction (k+1))
    (b : Space (k+1)) (δ : ℝ) :
    (volume : Measure (Space (k+1))) ((KakeyaOperator.tube v b).carrier δ) =
      referenceVolume k δ := carrier_volume_reference _ δ

theorem referenceVolume_finite (k : ℕ) (δ : ℝ) : referenceVolume k δ ≠ ∞ :=
  TubeVolume.carrier_finite _ _

theorem referenceVolume_pos (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < referenceVolume k δ := by
  let v : KakeyaOperator.Direction (k+1) :=
    ⟨EuclideanSplit.axisUnit k,by simp⟩
  rw [← operator_carrier_volume v 0 δ]
  exact KakeyaOperator.carrier_pos v 0 hδ

theorem average_fixed_denominator {k : ℕ} (δ : ℝ) (f : Space (k+1) → ℝ≥0∞)
    (b : Space (k+1)) (v : KakeyaOperator.Direction (k+1)) :
    KakeyaOperator.average δ f b v =
      (∫⁻ x in (KakeyaOperator.tube v b).carrier δ, f x ∂volume) /
        referenceVolume k δ := by
  rw [KakeyaOperator.average,operator_carrier_volume]

end
end KakeyaFormal.TubeIsometryVolume
