import GridCells
import GridGeometry
import MeasurableRescaling
import MeasurableEnergy

/-! Actual spatial grouping of common-radius localized shadings, with a
uniform overlap bound and safe summation of different cluster-origin images. -/
namespace KakeyaFormal.LocalizedClusters
open MeasureTheory Set GridCells GridGeometry MeasurableRescaling
open scoped BigOperators ENNReal
noncomputable section
open Classical

variable {I : Type*} [Fintype I] {k : ℕ}

def indices (centers : I → Space k) (rho : ℝ) (q : Cell k) : Finset I :=
  Finset.univ.filter fun i => label rho (centers i) = q

def labels (centers : I → Space k) (rho : ℝ) : Finset (Cell k) :=
  Finset.univ.image (fun i => label rho (centers i))

def cluster (Y : I → Set (Space k)) (centers : I → Space k) (rho : ℝ) (q : Cell k) : Set (Space k) :=
  ⋃ i ∈ indices centers rho q, Y i

lemma mem_cluster (Y : I → Set (Space k)) (centers : I → Space k)
    (rho : ℝ) (q : Cell k) (x : Space k) :
    x ∈ cluster Y centers rho q ↔ ∃ i, label rho (centers i) = q ∧ x ∈ Y i := by
  simp only [cluster,indices,Set.mem_iUnion,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [exists_prop]

lemma cluster_measurable (Y : I → Set (Space k)) (centers : I → Space k)
    (rho : ℝ) (q : Cell k) (hY : ∀ i, MeasurableSet (Y i)) :
    MeasurableSet (cluster Y centers rho q) :=
  Finset.measurableSet_biUnion _ (fun i _ => hY i)

lemma cluster_finite (Y : I → Set (Space k)) (centers : I → Space k)
    (rho : ℝ) (q : Cell k) (hfin : ∀ i, (volume : Measure (Space k)) (Y i) ≠ ∞) :
    (volume : Measure (Space k)) (cluster Y centers rho q) ≠ ∞ :=
  measure_biUnion_ne_top (indices centers rho q).finite_toSet (fun i _ => hfin i)

/-- The actual cell label of each localization center gives the fixed common
origin needed by localized tube rescaling. -/
theorem center_near_origin (centers : I → Space k) {rho : ℝ} (hrho : 0 < rho)
    (q : Cell k) (i : I) (hi : i ∈ indices centers rho q) :
    dist (centers i) (cellCenter rho q) ≤ (k:ℝ)/2*rho := by
  have hc := cell_center_distance (gridCell_covers hrho (centers i))
  have hlabel := (Finset.mem_filter.mp hi).2
  rw [hlabel] at hc
  nlinarith

/-- Every actual cluster union lies in one controlled ball about its grid origin. -/
theorem cluster_ball (Y : I → Set (Space k)) (centers : I → Space k)
    {rho : ℝ} (hrho : 0 < rho)
    (hball : ∀ i, Y i ⊆ Metric.closedBall (centers i) rho) (q : Cell k) :
    cluster Y centers rho q ⊆ Metric.closedBall (cellCenter rho q) ((1+(k:ℝ)/2)*rho) := by
  intro x hx
  obtain ⟨i,hi,hxi⟩ := (mem_cluster Y centers rho q x).mp hx
  have hc := center_near_origin centers hrho q i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  have hxb : dist x (centers i) ≤ rho := hball i hxi
  have ht := dist_triangle x (centers i) (cellCenter rho q)
  change dist x (cellCenter rho q) ≤ _
  nlinarith

/-- The actual finite cluster unions cover exactly the original localized union. -/
theorem cluster_union (Y : I → Set (Space k)) (centers : I → Space k) (rho : ℝ) :
    (⋃ q : {q // q ∈ labels centers rho}, cluster Y centers rho q.1) = ⋃ i, Y i := by
  ext x
  constructor
  · intro hx
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i,_,hi⟩ := (mem_cluster Y centers rho q.1 x).mp hq
    exact Set.mem_iUnion.mpr ⟨i,hi⟩
  · intro hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    let q : {q // q ∈ labels centers rho} :=
      ⟨label rho (centers i),Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
    exact Set.mem_iUnion.mpr ⟨q,(mem_cluster Y centers rho q.1 x).mpr ⟨i,rfl,hi⟩⟩

/-- A fixed dimensional cluster overlap constant. -/
def overlapConstant (k : ℕ) : ℝ := (5:ℝ)^k*(2+(k:ℝ)/2)^k

/-- Actual lattice packing bounds pointwise spatial cluster overlap, independently
of the number of tubes and the chosen common localization radius. -/
theorem cluster_overlap (Y : I → Set (Space k)) (centers : I → Space k)
    {rho : ℝ} (hrho : 0 < rho) (hball : ∀ i, Y i ⊆ Metric.closedBall (centers i) rho)
    (x : Space k) :
    (MeasurableEnergy.overlapCount (fun q : {q // q ∈ labels centers rho} => cluster Y centers rho q.1) x:ℝ) ≤
      overlapConstant k := by
  let S := (labels centers rho).filter fun q => x ∈ cluster Y centers rho q
  have hcount : MeasurableEnergy.overlapCount
      (fun q : {q // q ∈ labels centers rho} => cluster Y centers rho q.1) x = S.card := by
    unfold MeasurableEnergy.overlapCount
    apply Finset.card_bij (fun q _ => q.1)
    · intro q hq
      exact Finset.mem_filter.mpr ⟨q.2,(Finset.mem_filter.mp hq).2⟩
    · intro q _ z _ hqz
      exact Subtype.ext hqz
    · intro q hq
      exact ⟨⟨q,(Finset.mem_filter.mp hq).1⟩,by simpa using (Finset.mem_filter.mp hq).2,rfl⟩
  have hpack := ball_grid_count_real hrho (by positivity : 0 ≤ 1+(k:ℝ)/2) x S
    (fun q hq => by
      have hh := cluster_ball Y centers hrho hball q (Finset.mem_filter.mp hq).2
      simpa only [Metric.mem_closedBall,dist_comm] using hh)
  rw [hcount]
  simpa only [overlapConstant,show (1:ℝ)+(1+(k:ℝ)/2) = 2+(k:ℝ)/2 by ring] using hpack

/-- Spatial grouping supplies the actual bounded-overlap measure assembly. -/
theorem cluster_volume_sum (Y : I → Set (Space k)) (centers : I → Space k)
    {rho : ℝ} (hrho : 0 < rho) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, (volume : Measure (Space k)) (Y i) ≠ ∞)
    (hball : ∀ i, Y i ⊆ Metric.closedBall (centers i) rho) :
    (∑ q : {q // q ∈ labels centers rho}, (volume : Measure (Space k)).real (cluster Y centers rho q.1)) ≤
      overlapConstant k*(volume : Measure (Space k)).real (⋃ i, Y i) := by
  have hh := MeasurableEnergy.finite_union_overlap
    (fun q : {q // q ∈ labels centers rho} => cluster Y centers rho q.1)
    (fun q => cluster_measurable Y centers rho q.1 hY)
    (fun q => cluster_finite Y centers rho q.1 hfin) (cluster_overlap Y centers hrho hball)
  rwa [cluster_union] at hh

/-- Different origins across clusters are handled by exact individual volume
scaling followed by the proved cluster-overlap sum in the original space. -/
theorem rescaled_cluster_volume_sum (Y : I → Set (Space k)) (centers : I → Space k)
    {rho : ℝ} (hrho : 0 < rho) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, (volume : Measure (Space k)) (Y i) ≠ ∞)
    (hball : ∀ i, Y i ⊆ Metric.closedBall (centers i) rho) :
    (∑ q : {q // q ∈ labels centers rho}, (volume : Measure (Space k)).real
      (Rescaling.rescale (8*rho) (cellCenter rho q.1) '' cluster Y centers rho q.1)) ≤
      overlapConstant k*(volume : Measure (Space k)).real (⋃ i, Y i)/(8*rho)^k := by
  simp_rw [image_volume (by positivity : 0 < 8*rho)]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (cluster_volume_sum Y centers hrho hY hfin hball)
    (by positivity)

/-- Arbitrary tube weights partition exactly across the actual spatial labels. -/
theorem grouped_weight (centers : I → Space k) (rho : ℝ) (a : I → ℝ) :
    (∑ q ∈ labels centers rho, ∑ i ∈ indices centers rho q, a i) = ∑ i, a i := by
  exact Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := labels centers rho) (g := fun i => label rho (centers i))
    (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩) a

/-- Every actual spatial group supplies its own uniformly bounded, shared-origin
unit-tube family. The required center bound is derived from its grid label. -/
theorem normalized_cluster_family (T : I → UnitTube k) (Y : I → Set (Space k))
    (centers : I → Space k) {δ rho alpha : ℝ} (hδ : 0 < δ) (hδrho : δ ≤ rho)
    (ha : 0 ≤ alpha) (hne : ∀ i, (Y i).Nonempty)
    (hYT : ∀ i, Y i ⊆ (T i).carrier δ)
    (hball : ∀ i, Y i ⊆ Metric.closedBall (centers i) rho)
    (hY : ∀ i, MeasurableSet (Y i))
    (hends : ∀ i, ∀ y : Space k, ∀ r : ℝ, δ ≤ r → r ≤ rho →
      (volume : Measure (Space k)).real (Y i ∩ Metric.closedBall y r) ≤
        (4:ℝ)^alpha*(r/rho)^alpha*(volume : Measure (Space k)).real (Y i))
    (q : Cell k) :
    ∃ a : {i // i ∈ indices centers rho q} → ℝ,
      (∀ i : {i // i ∈ indices centers rho q},
        (Rescaling.tube (T i.1) (8*rho) (cellCenter rho q) (a i)).direction = (T i.1).direction ∧
        ‖(Rescaling.tube (T i.1) (8*rho) (cellCenter rho q) (a i)).base‖ ≤ ((k:ℝ)/2+6)/8 ∧
        Rescaling.rescale (8*rho) (cellCenter rho q) '' Y i.1 ⊆
          (Rescaling.tube (T i.1) (8*rho) (cellCenter rho q) (a i)).carrier (δ/(8*rho))) ∧
      (∀ i : {i // i ∈ indices centers rho q},
        MeasurableSet (Rescaling.rescale (8*rho) (cellCenter rho q) '' Y i.1)) ∧
      (∀ i : {i // i ∈ indices centers rho q},
        (volume : Measure (Space k)).real (Rescaling.rescale (8*rho) (cellCenter rho q) '' Y i.1) =
          (volume : Measure (Space k)).real (Y i.1)/(8*rho)^k) ∧
      (volume : Measure (Space k)).real
        (⋃ i : {i // i ∈ indices centers rho q}, Rescaling.rescale (8*rho) (cellCenter rho q) '' Y i.1) =
        (volume : Measure (Space k)).real (⋃ i : {i // i ∈ indices centers rho q}, Y i.1)/(8*rho)^k ∧
      (∀ i : {i // i ∈ indices centers rho q}, ∀ y : Space k, ∀ r : ℝ, δ/(8*rho) ≤ r → r ≤ 1 →
        (volume : Measure (Space k)).real
          ((Rescaling.rescale (8*rho) (cellCenter rho q) '' Y i.1) ∩ Metric.closedBall y r) ≤
            (32:ℝ)^alpha*r^alpha*(volume : Measure (Space k)).real
              (Rescaling.rescale (8*rho) (cellCenter rho q) '' Y i.1)) := by
  exact shared_origin_family (fun i : {i // i ∈ indices centers rho q} => T i.1)
    (fun i => Y i.1) hδ hδrho ha (fun i => centers i.1) (cellCenter rho q)
    (fun i => hne i.1) (fun i => hYT i.1) (fun i => hball i.1)
    (fun i => center_near_origin centers (hδ.trans_le hδrho) q i.1 i.2)
    (fun i => hY i.1) (fun i => hends i.1)

end
end KakeyaFormal.LocalizedClusters
