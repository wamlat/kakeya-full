import MainEndpoint
import MeasurableLengthEstimates
import SourceAnalyticInputs

/-! Real-cap measurable estimates on the completed Lebesgue measurable space.
Actual Borel subsets preserve each shading's mass and the complete union;
all scale, density, cap, separation, tube and position data remain identical. -/
namespace KakeyaFormal.LebesgueRealCap
open MeasureTheory Finset SamplingGeometry
open scoped BigOperators
noncomputable section
open Classical

structure Configuration (n : ℕ) (geom : MeasurableNormalization) (m : ℝ) where
  M : ℕ
  δ : ℝ
  lam : ℝ
  A : ℝ
  family : TubeFamily n M
  shading : Fin M → Set (Space n)
  scale_pos : 0 < δ
  scale_le_one : δ ≤ 1
  density_pos : 0 < lam
  density_le_one : lam ≤ 1
  cap_ge_one : 1 ≤ A
  shading_nullMeasurable : ∀ i, NullMeasurableSet (shading i) (volume : Measure (Space n))
  shading_subset : ∀ i, shading i ⊆ (family.tube i).carrier δ
  shading_mass : ∀ i, lam*(volume : Measure (Space n)).real ((family.tube i).carrier δ) ≤
    (volume : Measure (Space n)).real (shading i)
  separated : family.Separated (geom.separation*δ)
  bounded : family.Bounded geom.radius
  cap_bound : family.CapBound δ m A

namespace Configuration
variable {n : ℕ} {geom : MeasurableNormalization} {m : ℝ}

def unionSet (F : Configuration n geom m) : Set (Space n) := ⋃ i, F.shading i

def core (F : Configuration n geom m) (i : Fin F.M) : Set (Space n) :=
  (F.shading_nullMeasurable i).exists_measurable_subset_ae_eq.choose

theorem core_subset (F : Configuration n geom m) (i : Fin F.M) : F.core i ⊆ F.shading i :=
  (F.shading_nullMeasurable i).exists_measurable_subset_ae_eq.choose_spec.1

theorem core_measurable (F : Configuration n geom m) (i : Fin F.M) : MeasurableSet (F.core i) :=
  (F.shading_nullMeasurable i).exists_measurable_subset_ae_eq.choose_spec.2.1

theorem core_ae_eq (F : Configuration n geom m) (i : Fin F.M) :
    F.core i =ᵐ[(volume : Measure (Space n))] F.shading i :=
  (F.shading_nullMeasurable i).exists_measurable_subset_ae_eq.choose_spec.2.2

/-- The only changed data are actual Borel subsets of the original shadings. -/
def borel (F : Configuration n geom m) : MeasurableConfiguration n geom m where
  M := F.M
  δ := F.δ
  lam := F.lam
  A := F.A
  family := F.family
  shading := F.core
  scale_pos := F.scale_pos
  scale_le_one := F.scale_le_one
  density_pos := F.density_pos
  density_le_one := F.density_le_one
  cap_ge_one := F.cap_ge_one
  shading_measurable := F.core_measurable
  shading_subset i := (F.core_subset i).trans (F.shading_subset i)
  shading_mass i := by rw [measureReal_congr (F.core_ae_eq i)]; exact F.shading_mass i
  separated := F.separated
  bounded := F.bounded
  cap_bound := F.cap_bound

theorem borel_union_ae_eq (F : Configuration n geom m) :
    F.borel.unionSet =ᵐ[(volume : Measure (Space n))] F.unionSet :=
  .countable_iUnion F.core_ae_eq

theorem borel_union_volume (F : Configuration n geom m) :
    (volume : Measure (Space n)).real F.borel.unionSet = volume.real F.unionSet :=
  measureReal_congr F.borel_union_ae_eq

def ofBorel (F : MeasurableConfiguration n geom m) : Configuration n geom m where
  M := F.M
  δ := F.δ
  lam := F.lam
  A := F.A
  family := F.family
  shading := F.shading
  scale_pos := F.scale_pos
  scale_le_one := F.scale_le_one
  density_pos := F.density_pos
  density_le_one := F.density_le_one
  cap_ge_one := F.cap_ge_one
  shading_nullMeasurable i := (F.shading_measurable i).nullMeasurableSet
  shading_subset := F.shading_subset
  shading_mass := F.shading_mass
  separated := F.separated
  bounded := F.bounded
  cap_bound := F.cap_bound

end Configuration

/-- The full real-cap bound for completed-measurable original shadings. -/
def Estimate (n : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : MeasurableNormalization, ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ F : Configuration n geom m,
      c*F.A⁻¹*F.δ^((n:ℝ)+m-d+ε)*F.lam^p*F.M ≤
        (volume : Measure (Space n)).real F.unionSet

def VolumeEstimate (n : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : MeasurableNormalization, ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ F : Configuration n geom m,
      c*F.A⁻¹*F.δ^(m+1-d+ε)*F.lam^p*
        (∑ i, (volume : Measure (Space n)).real ((F.family.tube i).carrier F.δ)) ≤
          (volume : Measure (Space n)).real F.unionSet

theorem of_borel {n : ℕ} {m d p : ℝ} (h : MeasurableEstimate n m d p) : Estimate n m d p := by
  intro geom ε hε
  obtain ⟨c,hc,hbound⟩ := h geom ε hε
  exact ⟨c,hc,fun F => (hbound F.borel).trans_eq F.borel_union_volume⟩

theorem to_borel {n : ℕ} {m d p : ℝ} (h : Estimate n m d p) : MeasurableEstimate n m d p := by
  intro geom ε hε
  obtain ⟨c,hc,hbound⟩ := h geom ε hε
  exact ⟨c,hc,fun F => hbound (Configuration.ofBorel F)⟩

theorem estimate_iff_borel {n : ℕ} {m d p : ℝ} :
    Estimate n m d p ↔ MeasurableEstimate n m d p := ⟨to_borel,of_borel⟩

theorem volume_of_borel {n : ℕ} {m d p : ℝ} (h : VolumeMeasurableEstimate n m d p) :
    VolumeEstimate n m d p := by
  intro geom ε hε
  obtain ⟨c,hc,hbound⟩ := h geom ε hε
  exact ⟨c,hc,fun F => (hbound F.borel).trans_eq F.borel_union_volume⟩

theorem volume_to_borel {n : ℕ} {m d p : ℝ} (h : VolumeEstimate n m d p) :
    VolumeMeasurableEstimate n m d p := by
  intro geom ε hε
  obtain ⟨c,hc,hbound⟩ := h geom ε hε
  exact ⟨c,hc,fun F => hbound (Configuration.ofBorel F)⟩

theorem volume_estimate_iff_borel {n : ℕ} {m d p : ℝ} :
    VolumeEstimate n m d p ↔ VolumeMeasurableEstimate n m d p :=
  ⟨volume_to_borel,volume_of_borel⟩

/-- The actual unrestricted real-cap endpoint, including its density envelope,
now quantified over all Lebesgue measurable shading representatives. -/
theorem real_cap_endpoint {n : ℕ} {m : ℝ} (hm : 3 < m)
    (hn : 0 < n) (hdim : m ≤ (n:ℝ)-1) :
    Estimate n m (KakeyaScalar.limitProfile m) (max (KakeyaScalar.limitProfile m) 4) :=
  of_borel (MainEndpoint.real_cap_measurable hm n hn hdim)

theorem diagonal_endpoint {n : ℕ} (hn : 6 ≤ n) :
    Estimate n ((n:ℝ)-1) (KakeyaScalar.limitProfile ((n:ℝ)-1))
      (KakeyaScalar.limitProfile ((n:ℝ)-1)) := of_borel (MainEndpoint.diagonal_measurable hn)

theorem diagonal_volume {n : ℕ} (hn : 6 ≤ n) :
    VolumeEstimate n ((n:ℝ)-1) (KakeyaScalar.limitProfile ((n:ℝ)-1))
      (KakeyaScalar.limitProfile ((n:ℝ)-1)) := volume_of_borel (MainEndpoint.diagonal_volume hn)

/-- The source absolute-cap two-ends premise gives the completed-measurable
conclusion without adding any regularity requirement on the original shadings. -/
theorem globalize {k : ℕ} {m D C : ℝ}
    (h : SourceAnalyticInputs.TwoEnds (k+1) m D C) (hm : 0 ≤ m) (hD : 1 ≤ D) :
    VolumeEstimate (k+1) m D (max D C) :=
  volume_of_borel (h.globalize_measurable hm hD)

def LengthEstimate (n : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : MeasurableNormalization, ∀ lengthLower lengthUpper width : ℝ,
    0 < lengthLower → 0 < width → ∀ eps : ℝ, 0 < eps →
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily n M)
      (lengths : Fin M → ℝ) (Y : Fin M → Set (Space n)) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      (∀ i, lengthLower ≤ lengths i ∧ lengths i ≤ lengthUpper) →
      (∀ i, NullMeasurableSet (Y i) (volume : Measure (Space n))) →
      (∀ i, Y i ⊆ lengthCarrier (F.tube i) (lengths i) (width*δ)) →
      (∀ i, lam*(volume : Measure (Space n)).real
        (lengthCarrier (F.tube i) (lengths i) (width*δ)) ≤ volume.real (Y i)) →
      F.Separated (geom.separation*δ) → F.Bounded geom.radius → F.CapBound δ m A →
      c*A⁻¹*δ^(m+1-d+eps)*lam^p*
        (∑ i, (volume : Measure (Space n)).real
          (lengthCarrier (F.tube i) (lengths i) (width*δ))) ≤ volume.real (⋃ i,Y i)

theorem lengths_of_borel {n : ℕ} {m d p : ℝ} (h : MeasurableLengthEstimates.Estimate n m d p) :
    LengthEstimate n m d p := by
  intro geom l u w hl hw eps heps
  obtain ⟨c,hc,hbound⟩ := h geom l u w hl hw eps heps
  refine ⟨c,hc,?_⟩
  intro M F lengths Y δ lam A hδ hδ1 hlam hlam1 hA hlength hY hsub hmass hdir hbase hcap
  choose Z hZY hZ hsame using fun i => (hY i).exists_measurable_subset_ae_eq
  have hmass' : ∀ i, lam*(volume : Measure (Space n)).real
      (lengthCarrier (F.tube i) (lengths i) (w*δ)) ≤ volume.real (Z i) := by
    intro i
    rw [measureReal_congr (hsame i)]
    exact hmass i
  have hb := hbound F lengths Z hδ hδ1 hlam hlam1 hA hlength hZ
    (fun i => (hZY i).trans (hsub i)) hmass' hdir hbase hcap
  exact hb.trans_eq (measureReal_congr (.countable_iUnion hsame))

theorem lengths_to_borel {n : ℕ} {m d p : ℝ} (h : LengthEstimate n m d p) :
    MeasurableLengthEstimates.Estimate n m d p := by
  intro geom l u w hl hw eps heps
  obtain ⟨c,hc,hbound⟩ := h geom l u w hl hw eps heps
  refine ⟨c,hc,?_⟩
  intro M F lengths Y δ lam A hδ hδ1 hlam hlam1 hA hlength hY hsub hmass hdir hbase hcap
  exact hbound F lengths Y hδ hδ1 hlam hlam1 hA hlength
    (fun i => (hY i).nullMeasurableSet) hsub hmass hdir hbase hcap

theorem length_estimate_iff_borel {n : ℕ} {m d p : ℝ} :
    LengthEstimate n m d p ↔ MeasurableLengthEstimates.Estimate n m d p :=
  ⟨lengths_to_borel,lengths_of_borel⟩

theorem length_real_cap_endpoint {k : ℕ} {m : ℝ} (hm : 3 < m) (hdim : m ≤ (k:ℝ)) :
    LengthEstimate (k+1) m (KakeyaScalar.limitProfile m) (max (KakeyaScalar.limitProfile m) 4) :=
  lengths_of_borel (MeasurableLengthEstimates.real_cap_endpoint hm hdim)

theorem length_diagonal_endpoint {n : ℕ} (hn : 6 ≤ n) :
    LengthEstimate n ((n:ℝ)-1) (KakeyaScalar.limitProfile ((n:ℝ)-1))
      (KakeyaScalar.limitProfile ((n:ℝ)-1)) := lengths_of_borel (MeasurableLengthEstimates.diagonal_endpoint hn)

end
end KakeyaFormal.LebesgueRealCap
