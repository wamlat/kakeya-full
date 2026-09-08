import WidthNormalization
import HairbrushKernel

/-! Actual marked measurable inputs built from finite grid shadings, with
exact common volume factors and literal pointwise cap counts. -/
namespace KakeyaFormal.GridMarked
open MeasureTheory Set GridShadingMeasure WidthNormalization MeasurableRescaling
open scoped BigOperators ENNReal
noncomputable section
open Classical

/-- Only the tube bases are changed; the finite labels are bookkeeping for the
original grid and are used to construct the measurable shadings below. -/
def family {M k : ℕ} (F : TubeFamily k M) (W : ℝ) : TubeFamily k M where
  tube i := normalizedTube (F.tube i) W
  shade := F.shade

def shading {M k : ℕ} (F : TubeFamily k M) (δ W : ℝ) (i : Fin M) : Set (Space k) :=
  normalizedSet W (cellUnion δ (F.shade i))

def marked {k : ℕ} (H : Finset (Cell k)) (δ W : ℝ) : Set (Space k) :=
  normalizedSet W (cellUnion δ H)

lemma separated {M k : ℕ} (F : TubeFamily k M) (W δ : ℝ) (h : F.Separated δ) :
    (family F W).Separated δ := h

lemma cap_bound {M k : ℕ} (F : TubeFamily k M) (W δ m A : ℝ) (h : F.CapBound δ m A) :
    (family F W).CapBound δ m A := h

lemma shading_measurable {M k : ℕ} (F : TubeFamily k M) {δ W : ℝ}
    (hW : 0 < W) (i : Fin M) : MeasurableSet (shading F δ W i) :=
  normalized_measurable hW (cellUnion_measurable δ _)

lemma marked_measurable {k : ℕ} (H : Finset (Cell k)) {δ W : ℝ}
    (hW : 0 < W) : MeasurableSet (marked H δ W) :=
  normalized_measurable hW (cellUnion_measurable δ H)

/-- Marking by a grid cell set commutes exactly with the common realization. -/
theorem marked_inter {M k : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ W : ℝ} (hδ : 0 < δ) (hW : 0 < W) (i : Fin M) :
    shading F δ W i ∩ marked H δ W =
      normalizedSet W (cellUnion δ (F.shade i ∩ H)) := by
  ext x
  simp only [shading,marked,Set.mem_inter_iff,grid_membership _ hδ hW,Finset.mem_inter]

/-- The exact actual marked incidence mass, including boundary points. -/
theorem marked_mass {M k : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ W : ℝ} (hδ : 0 < δ) (hW : 0 < W) :
    HairbrushSelection.markedMass (ν := volume) (shading F δ W) (marked H δ W) =
      (δ^k/W^k)*∑ i, ((F.shade i ∩ H).card:ℝ) := by
  unfold HairbrushSelection.markedMass
  simp_rw [marked_inter F H hδ hW,grid_mass _ hδ hW]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact full incidence mass in the same volume units. -/
theorem full_mass {M k : ℕ} (F : TubeFamily k M)
    {δ W : ℝ} (hδ : 0 < δ) (hW : 0 < W) :
    (∑ i, (volume : Measure (Space k)).real (shading F δ W i)) =
      (δ^k/W^k)*∑ i, ((F.shade i).card:ℝ) := by
  simp_rw [shading,grid_mass _ hδ hW]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A genuine finite marked-half-incidence bound supplies the measurable
marked-half-mass hypothesis of the geometric hairbrush theorem. -/
theorem marked_half {M k : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ W : ℝ} (hδ : 0 < δ) (hW : 0 < W)
    (hhalf : (∑ i, ((F.shade i).card:ℝ))/2 ≤ ∑ i, ((F.shade i ∩ H).card:ℝ)) :
    (∑ i, (volume : Measure (Space k)).real (shading F δ W i))/2 ≤
      HairbrushSelection.markedMass (ν := volume) (shading F δ W) (marked H δ W) := by
  rw [full_mass F hδ hW,marked_mass F H hδ hW]
  have hh := mul_le_mul_of_nonneg_left hhalf (by positivity : 0 ≤ δ^k/W^k)
  simpa only [mul_div_assoc] using hh

/-- Exact measurable multiplicity at the inverse image's actual fine label. -/
theorem multiplicity {M k : ℕ} (F : TubeFamily k M) {δ W : ℝ}
    (hδ : 0 < δ) (hW : 0 < W) (x : Space k) :
    MeasurableEnergy.multiplicity (shading F δ W) x =
      ((Finset.univ.filter (fun i => GridCells.label δ (inverse W 0 x) ∈ F.shade i)).card:ℝ) := by
  rw [MeasurableEnergy.multiplicity_eq_card]
  simp only [MeasurableEnergy.overlapCount,shading,grid_membership _ hδ hW]

/-- Literal broadness supplies the actual stem-cap count on all marked points.
The strict stem angle is contained in the finite closed cap used by Broad. -/
theorem broad_near_count {M k : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ W beta tau K theta : ℝ} (hδ : 0 < δ) (hW : 0 < W) (htheta : δ ≤ theta)
    (hbroad : ∀ q ∈ H,
      AngularDecomposition.Broad F (Finset.univ.filter (fun i => q ∈ F.shade i)) δ beta tau K)
    (hsmall : K*(theta/tau)^beta ≤ 1/2) :
    ∀ x ∈ marked H δ W, ∀ i : Fin M,
      (HairbrushBroad.nearCount (family F W).tube (shading F δ W) i theta x:ℝ) ≤
        MeasurableEnergy.multiplicity (shading F δ W) x/2 := by
  intro x hx i
  have hxH : GridCells.label δ (inverse W 0 x) ∈ H := (grid_membership H hδ hW x).mp hx
  let q := GridCells.label δ (inverse W 0 x)
  have hb := hbroad q hxH (F.tube i).direction theta htheta
  have hsub : (Finset.univ.filter (fun j => x ∈ shading F δ W j)).filter
      (fun j => projectiveDistance ((family F W).tube i).direction ((family F W).tube j).direction < theta) ⊆
      AngularDecomposition.cap F (Finset.univ.filter (fun j => q ∈ F.shade j)) (F.tube i).direction theta := by
    intro j hj
    obtain ⟨hjY,hjangle⟩ := Finset.mem_filter.mp hj
    have hy : q ∈ F.shade j := (grid_membership _ hδ hW x).mp (Finset.mem_filter.mp hjY).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,?_⟩
    rw [ProjectiveGeometry.projective_symm]
    exact hjangle.le
  have hc : (HairbrushBroad.nearCount (family F W).tube (shading F δ W) i theta x:ℝ) ≤
      ((AngularDecomposition.cap F (Finset.univ.filter (fun j => q ∈ F.shade j)) (F.tube i).direction theta).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  have hp := mul_le_mul_of_nonneg_right hsmall
    (show (0:ℝ) ≤ (Finset.univ.filter (fun j => q ∈ F.shade j)).card by positivity)
  rw [multiplicity F hδ hW x]
  have hh := hc.trans (hb.trans hp)
  simpa only [one_div,one_mul,mul_comm (2:ℝ)⁻¹,div_eq_mul_inv] using hh

/-- Original finite two-ends bounds give every normalized measurable ball test,
with fixed width and cell-size factors only. -/
theorem shading_two_ends {M k : ℕ} (F : TubeFamily k M) {δ W B alpha : ℝ}
    (hδ : 0 < δ) (hW : 1 ≤ W) (hB : 1 ≤ B) (ha : 0 ≤ alpha)
    (hends : ∀ i, ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun q => dist (cellCenter δ q) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ)) :
    ∀ i, ∀ x : Space k, ∀ r : ℝ, δ ≤ r →
      (volume : Measure (Space k)).real (shading F δ W i ∩ Metric.closedBall x r) ≤
        (B*(1+(k:ℝ)/2)^alpha*W^alpha)*r^alpha*(volume : Measure (Space k)).real (shading F δ W i) := by
  have hW0 : 0 < W := by linarith
  intro i x r hr
  have hlo : δ/W ≤ r := (div_le_self hδ.le hW).trans hr
  exact normalized_two_ends hW0 hδ (cellUnion δ (F.shade i))
    (two_ends (F.shade i) hδ hB ha (hends i)) x r hlo

/-- The complete pointwise cap premise of the chosen-radius hairbrush follows
from actual finite marked broadness. Its angular-scale factor is explicit. -/
theorem pointwise_broad {M k : ℕ} (F : TubeFamily k M) (H : Finset (Cell k))
    {δ W beta tau K : ℝ} (hδ : 0 < δ) (hW : 0 < W) (htau : 0 < tau)
    (hbroad : ∀ q ∈ H,
      AngularDecomposition.Broad F (Finset.univ.filter (fun i => q ∈ F.shade i)) δ beta tau K) :
    HairbrushKernel.PointwiseBroad (family F W) (shading F δ W) (marked H δ W)
      δ beta (K*tau^(-beta)) := by
  intro x hx center t ht
  have hxH : GridCells.label δ (inverse W 0 x) ∈ H := (grid_membership H hδ hW x).mp hx
  have hh := hbroad _ hxH center t ht
  have ht0 : 0 < t := hδ.trans_le ht
  have hid : K*(t/tau)^beta = (K*tau^(-beta))*t^beta := by
    rw [Real.div_rpow ht0.le htau.le,Real.rpow_neg htau.le]
    ring
  rw [hid] at hh
  simpa only [AngularDecomposition.cap,Finset.filter_filter,shading,family,
    normalized_direction,grid_membership _ hδ hW,MeasurableEnergy.overlapCount] using hh

end
end KakeyaFormal.GridMarked
