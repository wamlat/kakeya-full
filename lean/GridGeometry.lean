import Configurations

/-!
# Quantitative counting for the actual scaled integer grid

The centers and Euclidean unit tubes are those in `Configurations.lean`.
Finite grid populations in balls and short longitudinal intervals are counted
using explicit integer boxes. No grid counting or geometric covering estimate
is assumed as a premise.
-/
namespace KakeyaFormal.GridGeometry
open KakeyaFormal

noncomputable section

/-- The integer box of coordinate radius n about an integer lattice cell. -/
def gridBox {k : ℕ} (anchor : Cell k) (n : ℕ) : Finset (Cell k) :=
  Fintype.piFinset fun i => Finset.Icc (anchor i - (n:ℤ)) (anchor i + (n:ℤ))

theorem mem_gridBox {k : ℕ} {anchor z : Cell k} {n : ℕ} :
    z ∈ gridBox anchor n ↔ ∀ i, anchor i - (n:ℤ) ≤ z i ∧ z i ≤ anchor i + (n:ℤ) := by
  simp [gridBox, Fintype.mem_piFinset]

theorem gridBox_card {k : ℕ} (anchor : Cell k) (n : ℕ) :
    (gridBox anchor n).card = (2*n+1)^k := by
  rw [gridBox, Fintype.card_piFinset]
  have hcount (i : Fin k) :
      (Finset.Icc (anchor i - (n:ℤ)) (anchor i + (n:ℤ))).card = 2*n+1 := by
    rw [Int.card_Icc]
    have hid : anchor i + (n:ℤ) + 1 - (anchor i - (n:ℤ)) = (2*n+1 : ℕ) := by omega
    rw [hid, Int.toNat_natCast]
  simp_rw [hcount]
  simp

/-- Euclidean distance controls each coordinate difference. -/
theorem coordinate_dist_le {k : ℕ} (x y : Space k) (i : Fin k) :
    |WithLp.ofLp x i - WithLp.ofLp y i| ≤ dist x y := by
  simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-y) i

/-- Divide the physical coordinate distance by the positive mesh size. -/
theorem scaled_coordinate_bound {k : ℕ} {δ R : ℝ} (hδ : 0 < δ)
    {z : Cell k} {x : Space k} (hball : dist (cellCenter δ z) x ≤ R*δ)
    (i : Fin k) : |(z i : ℝ) - WithLp.ofLp x i / δ| ≤ R := by
  have hcoord := (coordinate_dist_le (cellCenter δ z) x i).trans hball
  change |δ * (z i : ℝ) - WithLp.ofLp x i| ≤ R*δ at hcoord
  have heq : δ * ((z i : ℝ) - WithLp.ofLp x i / δ) =
      δ * (z i : ℝ) - WithLp.ofLp x i := by field_simp
  rw [← heq, abs_mul, abs_of_pos hδ] at hcoord
  nlinarith

/-- An arbitrary real-centered scaled ball is contained in one explicit integer box. -/
theorem ball_subset_gridBox {k : ℕ} {δ R : ℝ} (hδ : 0 < δ)
    (x : Space k) {z : Cell k} (hz : dist (cellCenter δ z) x ≤ R*δ) :
    z ∈ gridBox (fun i => ⌊WithLp.ofLp x i / δ⌋) (Nat.ceil R + 1) := by
  rw [mem_gridBox]
  intro i
  have hc := scaled_coordinate_bound hδ hz i
  have hlo := Int.floor_le (WithLp.ofLp x i / δ)
  have hhi := Int.lt_floor_add_one (WithLp.ofLp x i / δ)
  have hceil := Nat.le_ceil R
  have ha := abs_le.mp hc
  constructor
  · have h : (⌊WithLp.ofLp x i / δ⌋ : ℝ) - ((Nat.ceil R:ℝ)+1) ≤ (z i : ℝ) := by linarith
    exact_mod_cast h
  · have h : (z i : ℝ) ≤ (⌊WithLp.ofLp x i / δ⌋ : ℝ) + ((Nat.ceil R:ℝ)+1) := by linarith
    exact_mod_cast h

/-- Exact finite cardinality bound for grid centers in a Euclidean ball of radius R*δ. -/
theorem ball_grid_count {k : ℕ} {δ R : ℝ} (hδ : 0 < δ)
    (x : Space k) (cells : Finset (Cell k))
    (hball : ∀ z ∈ cells, dist (cellCenter δ z) x ≤ R*δ) :
    cells.card ≤ (2*Nat.ceil R+3)^k := by
  have hs : cells ⊆ gridBox (fun i => ⌊WithLp.ofLp x i / δ⌋) (Nat.ceil R+1) := by
    intro z hz
    exact ball_subset_gridBox hδ x (hball z hz)
  have h := Finset.card_le_card hs
  rw [gridBox_card] at h
  simpa [Nat.mul_add, Nat.add_assoc] using h

/-- A radius-only constant of the customary C_k*(1+R)^k form. -/
theorem ball_grid_count_real {k : ℕ} {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (x : Space k) (cells : Finset (Cell k))
    (hball : ∀ z ∈ cells, dist (cellCenter δ z) x ≤ R*δ) :
    (cells.card : ℝ) ≤ (5:ℝ)^k * (1+R)^k := by
  have h := ball_grid_count hδ x cells hball
  have hcast : (cells.card : ℝ) ≤ ((2*Nat.ceil R+3 : ℕ):ℝ)^k := by exact_mod_cast h
  have hceil := Nat.ceil_lt_add_one hR
  have hbase : ((2*Nat.ceil R+3 : ℕ):ℝ) ≤ 5*(1+R) := by push_cast; linarith
  calc
    _ ≤ ((2*Nat.ceil R+3 : ℕ):ℝ)^k := hcast
    _ ≤ (5*(1+R))^k := pow_le_pow_left₀ (by positivity) hbase k
    _ = _ := mul_pow _ _ _

/-- A portion of a unit-direction tube over a parameter interval of length L*δ
lies in a ball of radius (width+L)*δ. -/
theorem longitudinal_ball_bound {k : ℕ} (T : UnitTube k)
    {δ width L a t : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    {z : Cell k} (ht : t ∈ Set.Icc a (a+L*δ))
    (hz : dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ) :
    dist (cellCenter δ z) (T.axisPoint a) ≤ (width+L)*δ := by
  have htgap : |t-a| ≤ L*δ := abs_le.mpr ⟨by nlinarith [ht.1], by linarith [ht.2]⟩
  have htriangle := dist_triangle (cellCenter δ z) (T.axisPoint t) (T.axisPoint a)
  rw [T.axisPoint_distance] at htriangle
  nlinarith

/-- There are at most a dimension/width/length constant many cells in every
longitudinal interval of length L*δ; no tube-grid alignment is required. -/
theorem longitudinal_grid_count {k : ℕ} (T : UnitTube k)
    {δ width L a : ℝ} (hδ : 0 < δ) (hL : 0 ≤ L)
    (cells : Finset (Cell k))
    (hinc : ∀ z ∈ cells, ∃ t ∈ Set.Icc a (a+L*δ),
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ) :
    cells.card ≤ (2*Nat.ceil (width+L)+3)^k := by
  apply ball_grid_count hδ (T.axisPoint a) cells
  intro z hz
  obtain ⟨t, ht, hdist⟩ := hinc z hz
  exact longitudinal_ball_bound T hδ hL ht hdist

/-- The manuscript's fixed-longitudinal-δ-interval bound, with an explicit constant. -/
theorem one_mesh_interval_grid_count {k : ℕ} (T : UnitTube k)
    {δ width a : ℝ} (hδ : 0 < δ) (cells : Finset (Cell k))
    (hinc : ∀ z ∈ cells, ∃ t ∈ Set.Icc a (a+δ),
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ) :
    cells.card ≤ (2*Nat.ceil (width+1)+3)^k := by
  apply longitudinal_grid_count T hδ (show (0:ℝ) ≤ 1 by norm_num) cells
  simpa using hinc

/-- Every point of [0,1] is within δ of one of at most ceil(1/δ)+1 mesh parameters. -/
theorem unit_parameter_mesh {δ t : ℝ} (hδ : 0 < δ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ j ∈ Finset.range (Nat.ceil (1/δ)+1), |t-(j:ℝ)*δ| ≤ δ := by
  let j := Nat.floor (t/δ)
  have hjlo : (j:ℝ) ≤ t/δ := Nat.floor_le (div_nonneg ht.1 hδ.le)
  have hjhi : t/δ < (j:ℝ)+1 := Nat.lt_floor_add_one (t/δ)
  have hjbound : (j:ℝ) ≤ (Nat.ceil (1/δ):ℝ) :=
    hjlo.trans ((div_le_div_of_nonneg_right ht.2 hδ.le).trans (Nat.le_ceil (1/δ)))
  have hjnat : j ≤ Nat.ceil (1/δ) := by exact_mod_cast hjbound
  refine ⟨j, Finset.mem_range_succ_iff.mpr hjnat, ?_⟩
  have hlower := (le_div_iff₀ hδ).mp hjlo
  have hupper := (div_lt_iff₀ hδ).mp hjhi
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- Explicit finite boxes covering the grid cells of a unit tube. -/
def tubeGridCover {k : ℕ} (T : UnitTube k) (δ width : ℝ) : Finset (Cell k) :=
  (Finset.range (Nat.ceil (1/δ)+1)).biUnion fun j =>
    gridBox (fun i => ⌊WithLp.ofLp (T.axisPoint ((j:ℝ)*δ)) i / δ⌋)
      (Nat.ceil (width+1)+1)

theorem tube_cell_mem_cover {k : ℕ} (T : UnitTube k) {δ width : ℝ}
    (hδ : 0 < δ) {z : Cell k}
    (hinc : ∃ t ∈ Set.Icc (0:ℝ) 1, dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ) :
    z ∈ tubeGridCover T δ width := by
  obtain ⟨t, ht, hz⟩ := hinc
  obtain ⟨j, hj, htj⟩ := unit_parameter_mesh hδ ht
  apply Finset.mem_biUnion.mpr
  refine ⟨j, hj, ball_subset_gridBox hδ (T.axisPoint ((j:ℝ)*δ)) ?_⟩
  have htriangle := dist_triangle (cellCenter δ z) (T.axisPoint t) (T.axisPoint ((j:ℝ)*δ))
  rw [T.axisPoint_distance] at htriangle
  nlinarith

/-- Exact O((1+1/δ)) grid-cell count for the actual Euclidean unit tube. -/
theorem unit_tube_grid_count {k : ℕ} (T : UnitTube k) {δ width : ℝ}
    (hδ : 0 < δ) (cells : Finset (Cell k))
    (hinc : ∀ z ∈ cells, ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ) :
    cells.card ≤ (Nat.ceil (1/δ)+1) * (2*Nat.ceil (width+1)+3)^k := by
  have hs : cells ⊆ tubeGridCover T δ width := fun _ hz => tube_cell_mem_cover T hδ (hinc _ hz)
  have hcover := (Finset.card_le_card hs).trans
    (Finset.card_biUnion_le (s := Finset.range (Nat.ceil (1/δ)+1))
      (t := fun j => gridBox (fun i => ⌊WithLp.ofLp (T.axisPoint ((j:ℝ)*δ)) i / δ⌋)
        (Nat.ceil (width+1)+1)))
  simpa [gridBox_card, Nat.mul_add, Nat.add_assoc] using hcover

/-- A real-valued form whose constant depends only on dimension and tube width. -/
theorem unit_tube_grid_count_real {k : ℕ} (T : UnitTube k) {δ width : ℝ}
    (hδ : 0 < δ) (cells : Finset (Cell k))
    (hinc : ∀ z ∈ cells, ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ) :
    (cells.card : ℝ) ≤
      2 * ((2*Nat.ceil (width+1)+3 : ℕ):ℝ)^k * (1+1/δ) := by
  have h := unit_tube_grid_count T hδ cells hinc
  have hcast : (cells.card : ℝ) ≤
      ((Nat.ceil (1/δ):ℝ)+1) * ((2*Nat.ceil (width+1)+3 : ℕ):ℝ)^k := by exact_mod_cast h
  have hc := Nat.ceil_lt_add_one (one_div_nonneg.mpr hδ.le)
  have hfactor : (Nat.ceil (1/δ):ℝ)+1 ≤ 2*(1+1/δ) := by
    have hpos := one_div_pos.mpr hδ
    linarith
  have hpow : (0:ℝ) ≤ ((2*Nat.ceil (width+1)+3 : ℕ):ℝ)^k := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hfactor hpow]

/-- The concrete admissibility definition immediately supplies the per-tube count. -/
theorem admissible_shade_card_bound {k M : ℕ} (F : TubeFamily k M)
    {width δ : ℝ} (hδ : 0 < δ) (hF : F.Admissible width δ) (i : Fin M) :
    (F.shade i).card ≤ (Nat.ceil (1/δ)+1) * (2*Nat.ceil (width+1)+3)^k :=
  unit_tube_grid_count (F.tube i) hδ (F.shade i) (hF i)


/-- A physical-arclength mesh for any segment, including coincident endpoints. -/
theorem segment_parameter_mesh {k : ℕ} (x y : Space k) {δ t : ℝ}
    (hδ : 0 < δ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∃ j ∈ Finset.range (Nat.ceil (dist x y / δ)+1),
      dist (AffineMap.lineMap x y t)
        (AffineMap.lineMap x y ((j:ℝ)*(δ / dist x y))) ≤ δ := by
  by_cases hxy : x = y
  · subst y
    refine ⟨0, by simp, ?_⟩
    simpa using hδ.le
  · have hdist : 0 < dist x y := dist_pos.mpr hxy
    obtain ⟨j, hj, hgap⟩ := unit_parameter_mesh (div_pos hδ hdist) ht
    refine ⟨j, ?_, ?_⟩
    · simpa only [one_div_div] using hj
    · rw [dist_lineMap_lineMap, Real.dist_eq]
      have hmul := mul_le_mul_of_nonneg_right hgap hdist.le
      simpa only [div_mul_cancel₀ _ (ne_of_gt hdist)] using hmul

/-- Explicit finite boxes covering all grid centers near an arbitrary segment. -/
def segmentGridCover {k : ℕ} (x y : Space k) (δ width : ℝ) : Finset (Cell k) :=
  (Finset.range (Nat.ceil (dist x y / δ)+1)).biUnion fun j =>
    gridBox (fun i => ⌊WithLp.ofLp
      (AffineMap.lineMap x y ((j:ℝ)*(δ / dist x y))) i / δ⌋)
      (Nat.ceil (width+1)+1)

theorem segment_cell_mem_cover {k : ℕ} (x y : Space k) {δ width : ℝ}
    (hδ : 0 < δ) {z : Cell k}
    (hinc : ∃ p ∈ segment ℝ x y, dist (cellCenter δ z) p ≤ width*δ) :
    z ∈ segmentGridCover x y δ width := by
  obtain ⟨p, hp, hz⟩ := hinc
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  obtain ⟨j, hj, htj⟩ := segment_parameter_mesh x y hδ ht
  apply Finset.mem_biUnion.mpr
  refine ⟨j, hj, ball_subset_gridBox hδ
    (AffineMap.lineMap x y ((j:ℝ)*(δ / dist x y))) ?_⟩
  have htriangle := dist_triangle (cellCenter δ z) (AffineMap.lineMap x y t)
    (AffineMap.lineMap x y ((j:ℝ)*(δ / dist x y)))
  nlinarith

/-- The number of grid centers within width*δ of an arbitrary endpoint segment.
The bound is linear in 1+length/δ and also covers the zero-length segment. -/
theorem segment_grid_count {k : ℕ} (x y : Space k) {δ width : ℝ}
    (hδ : 0 < δ) (cells : Finset (Cell k))
    (hinc : ∀ z ∈ cells, ∃ p ∈ segment ℝ x y, dist (cellCenter δ z) p ≤ width*δ) :
    cells.card ≤ (Nat.ceil (dist x y / δ)+1) * (2*Nat.ceil (width+1)+3)^k := by
  have hs : cells ⊆ segmentGridCover x y δ width :=
    fun _ hz => segment_cell_mem_cover x y hδ (hinc _ hz)
  have hcover := (Finset.card_le_card hs).trans
    (Finset.card_biUnion_le (s := Finset.range (Nat.ceil (dist x y / δ)+1))
      (t := fun j => gridBox (fun i => ⌊WithLp.ofLp
        (AffineMap.lineMap x y ((j:ℝ)*(δ / dist x y))) i / δ⌋)
        (Nat.ceil (width+1)+1)))
  simpa [gridBox_card, Nat.mul_add, Nat.add_assoc] using hcover

/-- Fixed upper segment-length version, convenient when only a bounded-region
normalization is available. -/
theorem segment_grid_count_of_length_le {k : ℕ} (x y : Space k) {δ width D : ℝ}
    (hδ : 0 < δ) (hD : dist x y ≤ D) (cells : Finset (Cell k))
    (hinc : ∀ z ∈ cells, ∃ p ∈ segment ℝ x y, dist (cellCenter δ z) p ≤ width*δ) :
    cells.card ≤ (Nat.ceil (D / δ)+1) * (2*Nat.ceil (width+1)+3)^k := by
  have h := segment_grid_count x y hδ cells hinc
  have hc := Nat.ceil_mono (div_le_div_of_nonneg_right hD hδ.le)
  exact h.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right hc 1))


end
end KakeyaFormal.GridGeometry
