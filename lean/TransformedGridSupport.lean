import AnisotropicGrid
import WidthNormalization
import SamplingSupport

/-! Actual new-grid cells meeting transformed whole old cells. Unlike rounded
center images, this finite support contains every touching cell and has an upper
count bounded by the original cell population, with no inverse tau loss. -/
namespace KakeyaFormal.TransformedGridSupport
open GridGeometry GridCells GridShadingMeasure AnisotropicRescaling SpatialAngular
open MeasureTheory
open scoped BigOperators
noncomputable section
open Classical

/-- One explicit integer box for each actual old cell. -/
def cellBox {n : ℕ} (f : Space n → Space n) (δ tau : ℝ) (z : Cell n) : Finset (Cell n) :=
  gridBox (fun i => ⌊WithLp.ofLp (f (cellCenter δ z)) i/(δ/tau)⌋) (n+1)

def cover {n : ℕ} (f : Space n → Space n) (δ tau : ℝ) (S : Finset (Cell n)) : Finset (Cell n) :=
  S.biUnion (cellBox f δ tau)

/-- Filter the explicit finite cover by actual intersection, including boundary
contacts. No chosen representatives or center-projection injectivity is used. -/
def touched {n : ℕ} (f : Space n → Space n) (δ tau : ℝ) (S : Finset (Cell n)) : Finset (Cell n) :=
  (cover f δ tau S).filter (fun z => ((f '' cellUnion δ S) ∩ gridCell (δ/tau) z).Nonempty)

/-- Both half-cell errors are at the target mesh; thus one old cell meets only
a bounded target-grid neighborhood even after the anisotropic stretch. -/
theorem touching_center_bound {n : ℕ} (f : Space n → Space n) {δ tau : ℝ}
    (_hδ : 0 < δ) (htau : 0 < tau)
    (hmap : ∀ x y, dist (f x) (f y) ≤ dist x y/tau)
    {z w : Cell n} {x : Space n} (hx : x ∈ gridCell δ z)
    (hfx : f x ∈ gridCell (δ/tau) w) :
    dist (cellCenter (δ/tau) w) (f (cellCenter δ z)) ≤ (n:ℝ)*(δ/tau) := by
  have hold := cell_center_distance hx
  have hnew := cell_center_distance hfx
  have hdist := (hmap x (cellCenter δ z)).trans (div_le_div_of_nonneg_right hold htau.le)
  have htri := dist_triangle (cellCenter (δ/tau) w) (f x) (f (cellCenter δ z))
  rw [dist_comm (cellCenter (δ/tau) w) (f x)] at htri
  have hid : ((n:ℝ)*δ/2)/tau = (n:ℝ)*(δ/tau)/2 := by ring
  rw [hid] at hdist
  linarith

theorem touching_mem_cellBox {n : ℕ} (f : Space n → Space n) {δ tau : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau)
    (hmap : ∀ x y, dist (f x) (f y) ≤ dist x y/tau)
    {z w : Cell n} {x : Space n} (hx : x ∈ gridCell δ z)
    (hfx : f x ∈ gridCell (δ/tau) w) : w ∈ cellBox f δ tau z := by
  have hh := ball_subset_gridBox (div_pos hδ htau) (f (cellCenter δ z))
    (touching_center_bound f hδ htau hmap hx hfx)
  simpa only [cellBox,Nat.ceil_natCast] using hh

/-- Exact completeness: no new cell touching the transformed old union is
excluded by the finite cover construction. -/
theorem mem_touched {n : ℕ} (f : Space n → Space n) {δ tau : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau)
    (hmap : ∀ x y, dist (f x) (f y) ≤ dist x y/tau)
    (S : Finset (Cell n)) (w : Cell n) :
    w ∈ touched f δ tau S ↔ ((f '' cellUnion δ S) ∩ gridCell (δ/tau) w).Nonempty := by
  constructor
  · intro hw; exact (Finset.mem_filter.mp hw).2
  · intro hw
    have hkeep := hw
    obtain ⟨_,⟨x,hx,rfl⟩,hfx⟩ := hw
    obtain ⟨z,hz,hxz⟩ := Set.mem_iUnion₂.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr
      ⟨z,hz,touching_mem_cellBox f hδ htau hmap hxz hfx⟩,hkeep⟩

theorem cellBox_card {n : ℕ} (f : Space n → Space n) (δ tau : ℝ) (z : Cell n) :
    (cellBox f δ tau z).card = (2*n+3)^n := by
  rw [cellBox,gridBox_card]
  congr 1

/-- Actual upper count. This concerns whole touching cells, not only rounded
old centers, and its constant is independent of tau and delta. -/
theorem touched_card {n : ℕ} (f : Space n → Space n) (δ tau : ℝ) (S : Finset (Cell n)) :
    (touched f δ tau S).card ≤ S.card*(2*n+3)^n := by
  calc
    _ ≤ (cover f δ tau S).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ ∑ z ∈ S, (cellBox f δ tau z).card := Finset.card_biUnion_le
    _ = _ := by simp [cellBox_card]

/-- Every point of the exact transformed union is covered by these actual
half-open target cells. -/
theorem image_covered {n : ℕ} (f : Space n → Space n) {δ tau : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau)
    (hmap : ∀ x y, dist (f x) (f y) ≤ dist x y/tau) (S : Finset (Cell n)) :
    f '' cellUnion δ S ⊆ cellUnion (δ/tau) (touched f δ tau S) := by
  intro x hx
  apply (mem_cellUnion (div_pos hδ htau) _ x).mpr
  apply (mem_touched f hδ htau hmap S _).mpr
  exact ⟨x,hx,gridCell_covers (div_pos hδ htau) x⟩

/-- The actual common map used for a spatially localized angular piece,
including its fixed preliminary width normalization. -/
def pieceMap {k : ℕ} (u : Space (k+1)) (tau W : ℝ) (q : Cell k) (x : Space (k+1)) : Space (k+1) :=
  normalizeBox u tau q (Rescaling.rescale W 0 x)

/-- Its required distance upper bound follows from the constructed geometric
maps; it is not a new anisotropic Lipschitz assumption. -/
theorem pieceMap_distance {k : ℕ} (u : Space (k+1)) {tau W : ℝ}
    (htau : 0 < tau) (htau1 : tau ≤ 1) (hW : 1 ≤ W) (q : Cell k)
    (x y : Space (k+1)) : dist (pieceMap u tau W q x) (pieceMap u tau W q y) ≤ dist x y/tau := by
  have hWp : 0 < W := zero_lt_one.trans_le hW
  have hh := (normalizeBox_distance_bounds u htau htau1 q (Rescaling.rescale W 0 x)
    (Rescaling.rescale W 0 y)).2
  rw [Rescaling.rescale_distance hWp] at hh
  exact hh.trans (div_le_div_of_nonneg_right (div_le_self dist_nonneg hW) htau.le)

/-- Actual anisotropic-grid upper comparison in Section 7, including the fixed
common width map and every target-grid boundary intersection. -/
theorem piece_support {k : ℕ} (u : Space (k+1)) {δ tau W : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (hW : 1 ≤ W)
    (q : Cell k) (S : Finset (Cell (k+1))) :
    (∀ z, z ∈ touched (pieceMap u tau W q) δ tau S ↔
      (((pieceMap u tau W q) '' cellUnion δ S) ∩ gridCell (δ/tau) z).Nonempty) ∧
    (pieceMap u tau W q) '' cellUnion δ S ⊆
      cellUnion (δ/tau) (touched (pieceMap u tau W q) δ tau S) ∧
    (touched (pieceMap u tau W q) δ tau S).card ≤ S.card*(2*(k+1)+3)^(k+1) :=
  ⟨mem_touched _ hδ htau (pieceMap_distance u htau htau1 hW q) S,
    image_covered _ hδ htau (pieceMap_distance u htau htau1 hW q) S,touched_card _ _ _ _⟩

/-- Positive-measure sampling support of any actual restrictions of the image
lies in the full touching-cell set, with no count supplied by the caller. -/
theorem positive_support_subset {n M : ℕ} (f : Space n → Space n) {δ tau width R : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau)
    (hmap : ∀ x y, dist (f x) (f y) ≤ dist x y/tau)
    (S : Finset (Cell n)) (tube : Fin M → UnitTube n) (Y : Fin M → Set (Space n))
    (hY : ∀ i, Y i ⊆ f '' cellUnion δ S) :
    SamplingSupport.support tube Y (δ/tau) width R ⊆ touched f δ tau S := by
  intro z hz
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨x,hx,hcell⟩ := SamplingSupport.positive_intersection_nonempty (Finset.mem_filter.mp hi).2
  exact (mem_touched f hδ htau hmap S z).mpr ⟨x,hY i hx,hcell⟩

/-- Thus the actual positive sampling support has the correct original-cell
upper population, with no tau factor and no replacement by normalized volume. -/
theorem positive_support_card {k M : ℕ} (u : Space (k+1)) {δ tau W width R : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (hW : 1 ≤ W)
    (q : Cell k) (S : Finset (Cell (k+1)))
    (tube : Fin M → UnitTube (k+1)) (Y : Fin M → Set (Space (k+1)))
    (hY : ∀ i, Y i ⊆ (pieceMap u tau W q) '' cellUnion δ S) :
    (SamplingSupport.support tube Y (δ/tau) width R).card ≤ S.card*(2*(k+1)+3)^(k+1) :=
  (Finset.card_le_card (positive_support_subset _ hδ htau
    (pieceMap_distance u htau htau1 hW q) S tube Y hY)).trans (touched_card _ _ _ _)

end
end KakeyaFormal.TransformedGridSupport

#print axioms KakeyaFormal.TransformedGridSupport.piece_support
#print axioms KakeyaFormal.TransformedGridSupport.positive_support_card
