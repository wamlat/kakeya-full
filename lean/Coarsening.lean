import GridCells
import TubeLocalCount
import ScaleChoice

/-! Actual spatial grid coarsening for the heavy-cube step. Coarse labels are
constructed from physical fine-cell centers; incidence and fiber bounds are
proved from genuine tube geometry. -/
namespace KakeyaFormal.Coarsening
open GridCells TubeLocalCount
open scoped BigOperators
noncomputable section
open Classical

/-- The unique half-open coarse cell containing a fine-cell center. -/
def coarseLabel {k : ℕ} (δ r : ℝ) (q : Cell k) : Cell k := label r (cellCenter δ q)

lemma coarse_center_distance {k : ℕ} {δ r : ℝ} (hr : 0 < r) (q : Cell k) :
    dist (cellCenter δ q) (cellCenter r (coarseLabel δ r q)) ≤ (k:ℝ)*r/2 :=
  cell_center_distance (gridCell_covers hr (cellCenter δ q))

/-- All original directions and bases remain the same under spatial coarsening. -/
def family {M k : ℕ} (F : TubeFamily k M) (δ r : ℝ) : TubeFamily k M where
  tube := F.tube
  shade i := (F.shade i).image (coarseLabel δ r)

/-- Coarse shadings have actual tube admissibility with a fixed width enlargement. -/
theorem family_admissible {M k : ℕ} (F : TubeFamily k M) {δ r width : ℝ}
    (hδ : 0 < δ) (hr : δ ≤ r) (hw : 0 ≤ width)
    (hadm : F.Admissible width δ) :
    (family F δ r).Admissible (width+(k:ℝ)/2) r := by
  intro i q hq
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨t,ht,hzt⟩ := hadm i z hz
  have hcenter := coarse_center_distance (δ := δ) (hδ.trans_le hr) z
  have htri := dist_triangle (cellCenter r (coarseLabel δ r z))
    (cellCenter δ z) ((F.tube i).axisPoint t)
  rw [dist_comm (cellCenter r (coarseLabel δ r z)) (cellCenter δ z)] at htri
  refine ⟨t,ht,?_⟩
  have hwidth := mul_le_mul_of_nonneg_left hr hw
  change dist (cellCenter r (coarseLabel δ r z)) ((F.tube i).axisPoint t) ≤ _
  nlinarith

lemma family_union {M k : ℕ} (F : TubeFamily k M) (δ r : ℝ) :
    (family F δ r).unionCells = F.unionCells.image (coarseLabel δ r) := by
  simp only [TubeFamily.unionCells,family,Finset.biUnion_image]

/-- Fixed local-count constant; the extra dimension factor encloses a coarse cell. -/
def fiberConstant (k : ℕ) (width : ℝ) : ℝ :=
  ((k:ℝ)+1)*(6+4*width)*((2*Nat.ceil (width+1)+3:ℕ):ℝ)^k

lemma fiberConstant_pos (k : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    0 < fiberConstant k width := by
  dsimp [fiberConstant]
  have hbase : (0:ℝ) < ((2*Nat.ceil (width+1)+3:ℕ):ℝ) := by positivity
  positivity

/-- Every coarse cell contains only C*r/δ of an actual fine tube's incidences. -/
theorem coarse_fiber_count {k : ℕ} (T : UnitTube k) (S : Finset (Cell k))
    {δ r width : ℝ} (hδ : 0 < δ) (hr : δ ≤ r) (hw : 0 ≤ width)
    (hadm : ∀ q ∈ S, ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ q) (T.axisPoint t) ≤ width*δ) (z : Cell k) :
    (((S.filter (fun q => coarseLabel δ r q = z)).card):ℝ) ≤
      fiberConstant k width * (r/δ) := by
  let points := S.filter (fun q => coarseLabel δ r q = z)
  have hrpos : 0 < r := hδ.trans_le hr
  have hrbig : δ ≤ ((k:ℝ)+1)*r := hr.trans (by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
  have hinc : ∀ q ∈ points, ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ q) (T.axisPoint t) ≤ width*δ :=
    fun q hq => hadm q (Finset.mem_filter.mp hq).1
  have hball : ∀ q ∈ points, dist (cellCenter δ q) (cellCenter r z) ≤ ((k:ℝ)+1)*r := by
    intro q hq
    have hc := coarse_center_distance (δ := δ) hrpos q
    rw [(Finset.mem_filter.mp hq).2] at hc
    nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have h := tube_ball_grid_count_real T hδ hw hrbig (cellCenter r z) points hinc hball
  change (points.card:ℝ) ≤ _
  convert h using 1
  dsimp [fiberConstant]
  ring

/-- The coarse count is large because all fine incidences lie in the constructed
fibers, whose cardinalities have just been bounded geometrically. -/
theorem coarse_count_lower {k : ℕ} (T : UnitTube k) (S : Finset (Cell k))
    {δ r width : ℝ} (hδ : 0 < δ) (hr : δ ≤ r) (hw : 0 ≤ width)
    (hadm : ∀ q ∈ S, ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ q) (T.axisPoint t) ≤ width*δ) :
    (S.card:ℝ)*δ/(fiberConstant k width*r) ≤ ((S.image (coarseLabel δ r)).card:ℝ) := by
  have hsum : (S.card:ℝ) = ∑ z ∈ S.image (coarseLabel δ r),
      (((S.filter (fun q => coarseLabel δ r q = z)).card):ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image (coarseLabel δ r))
      (g := coarseLabel δ r) (fun q hq => Finset.mem_image.mpr ⟨q,hq,rfl⟩) (fun _ => (1:ℝ))
    simpa using hh.symm
  have hbound : (S.card:ℝ) ≤ ((S.image (coarseLabel δ r)).card:ℝ)*
      (fiberConstant k width*(r/δ)) := by
    rw [hsum]
    have hh := Finset.sum_le_sum (s := S.image (coarseLabel δ r))
      (fun z _ => coarse_fiber_count T S hδ hr hw hadm z)
    simpa only [Finset.sum_const,nsmul_eq_mul] using hh
  have hK := fiberConstant_pos k hw
  have hrpos := hδ.trans_le hr
  apply (div_le_iff₀ (mul_pos hK hrpos)).mpr
  have hm := mul_le_mul_of_nonneg_right hbound hδ.le
  have hid : (((S.image (coarseLabel δ r)).card:ℝ)*(fiberConstant k width*(r/δ)))*δ =
      ((S.image (coarseLabel δ r)).card:ℝ)*(fiberConstant k width*r) := by field_simp
  rwa [hid] at hm

/-- Heavy coarse cells consume their disjoint actual fine fibers. -/
theorem heavy_cell_mass {k : ℕ} (E H : Finset (Cell k)) (δ r threshold : ℝ)
    (hsub : H ⊆ E.image (coarseLabel δ r))
    (hheavy : ∀ z ∈ H, threshold ≤ (((E.filter (fun q => coarseLabel δ r q = z)).card):ℝ)) :
    threshold*(H.card:ℝ) ≤ (E.card:ℝ) := by
  have hsum : (∑ z ∈ E.image (coarseLabel δ r),
      (((E.filter (fun q => coarseLabel δ r q = z)).card):ℝ)) = (E.card:ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to (s := E) (t := E.image (coarseLabel δ r))
      (g := coarseLabel δ r) (fun q hq => Finset.mem_image.mpr ⟨q,hq,rfl⟩) (fun _ => (1:ℝ))
    simpa using hh
  calc
    _ = ∑ _z ∈ H, threshold := by simp [mul_comm]
    _ ≤ ∑ z ∈ H, (((E.filter (fun q => coarseLabel δ r q = z)).card):ℝ) :=
      Finset.sum_le_sum hheavy
    _ ≤ ∑ z ∈ E.image (coarseLabel δ r), (((E.filter (fun q => coarseLabel δ r q = z)).card):ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := hsum

/-- The constructed coarse union is contained in the actual selected heavy labels. -/
theorem family_union_subset {M k : ℕ} (F : TubeFamily k M) (δ r : ℝ) (H : Finset (Cell k))
    (hH : ∀ i q, q ∈ F.shade i → coarseLabel δ r q ∈ H) :
    (family F δ r).unionCells ⊆ H := by
  intro z hz
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hi
  exact hH i q hq

end
end KakeyaFormal.Coarsening
