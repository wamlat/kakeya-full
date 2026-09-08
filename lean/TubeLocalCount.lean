import GridGeometry

/-! The linear-in-radius cell bound for the intersection of an actual tube with
a ball. This is the geometric density upper bound used after localization. -/
namespace KakeyaFormal.TubeLocalCount
open KakeyaFormal.GridGeometry

theorem axisPoint_mem_segment {k : ℕ} (T : UnitTube k) {a b t : ℝ}
    (hab : a < b) (hta : a ≤ t) (htb : t ≤ b) :
    T.axisPoint t ∈ segment ℝ (T.axisPoint a) (T.axisPoint b) := by
  have hd : 0 < b-a := sub_pos.mpr hab
  refine ⟨(b-t)/(b-a), (t-a)/(b-a), div_nonneg (sub_nonneg.mpr htb) hd.le,
    div_nonneg (sub_nonneg.mpr hta) hd.le, ?_, ?_⟩
  · field_simp
    ring
  · have hsum : (b-t)/(b-a)+(t-a)/(b-a) = 1 := by field_simp; ring
    have hparam : ((b-t)/(b-a))*a+((t-a)/(b-a))*b = t := by field_simp; ring
    dsimp [UnitTube.axisPoint]
    rw [smul_add,smul_add,smul_smul,smul_smul]
    calc
      _ = (((b-t)/(b-a)+(t-a)/(b-a)) • T.base) +
          ((((b-t)/(b-a))*a+((t-a)/(b-a))*b) • T.direction) := by module
      _ = _ := by rw [hsum,hparam,one_smul]

/-- All axis parameters associated with cells in one ball lie in a short interval. -/
theorem tube_ball_parameter_gap {k : ℕ} (T : UnitTube k) {δ width r t t₀ : ℝ}
    (x : Space k) (z z₀ : Cell k)
    (hz : dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ)
    (hz₀ : dist (cellCenter δ z₀) (T.axisPoint t₀) ≤ width*δ)
    (hball : dist (cellCenter δ z) x ≤ r)
    (hball₀ : dist (cellCenter δ z₀) x ≤ r) :
    |t-t₀| ≤ 2*(r+width*δ) := by
  have hcent := dist_triangle (cellCenter δ z) x (cellCenter δ z₀)
  rw [dist_comm x] at hcent
  have hleft := dist_triangle (T.axisPoint t) (cellCenter δ z) (T.axisPoint t₀)
  have hright := dist_triangle (cellCenter δ z) (cellCenter δ z₀) (T.axisPoint t₀)
  rw [T.axisPoint_distance, dist_comm (T.axisPoint t)] at hleft
  linarith

/-- Exact finite-cell bound, linear in ceil(r/δ), for a tube intersected with a ball. -/
theorem tube_ball_grid_count {k : ℕ} (T : UnitTube k) {δ width r : ℝ}
    (hδ : 0 < δ) (hw : 0 ≤ width) (hr : 0 < r)
    (x : Space k) (cells : Finset (Cell k))
    (hinc : ∀ z ∈ cells, ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ)
    (hball : ∀ z ∈ cells, dist (cellCenter δ z) x ≤ r) :
    cells.card ≤ (Nat.ceil (4*(r+width*δ)/δ)+1)*(2*Nat.ceil (width+1)+3)^k := by
  classical
  by_cases hne : cells.Nonempty
  · obtain ⟨z₀,hz₀⟩ := hne
    obtain ⟨t₀,_,ht₀⟩ := hinc z₀ hz₀
    let R := r+width*δ
    have hR : 0 < R := add_pos_of_pos_of_nonneg hr (mul_nonneg hw hδ.le)
    have hab : t₀-2*R < t₀+2*R := by linarith
    apply segment_grid_count_of_length_le (T.axisPoint (t₀-2*R)) (T.axisPoint (t₀+2*R)) hδ
      (show dist (T.axisPoint (t₀-2*R)) (T.axisPoint (t₀+2*R)) ≤ 4*(r+width*δ) by
        rw [T.axisPoint_distance, abs_of_nonpos (by linarith : t₀-2*R-(t₀+2*R) ≤ 0)]
        dsimp [R]
        linarith)
    intro z hz
    obtain ⟨t,_,ht⟩ := hinc z hz
    have hgap := tube_ball_parameter_gap T x z z₀ ht ht₀ (hball z hz) (hball z₀ hz₀)
    obtain ⟨hlo,hhi⟩ := abs_le.mp hgap
    exact ⟨T.axisPoint t, axisPoint_mem_segment T hab (by dsimp [R]; linarith)
      (by dsimp [R]; linarith),ht⟩
  · have hempty : cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

/-- At radii r≥δ the bound is C(k,width)*r/δ, with a fully explicit constant. -/
theorem tube_ball_grid_count_real {k : ℕ} (T : UnitTube k) {δ width r : ℝ}
    (hδ : 0 < δ) (hw : 0 ≤ width) (hr : δ ≤ r)
    (x : Space k) (cells : Finset (Cell k))
    (hinc : ∀ z ∈ cells, ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ)
    (hball : ∀ z ∈ cells, dist (cellCenter δ z) x ≤ r) :
    (cells.card : ℝ) ≤
      ((6+4*width)*((2*Nat.ceil (width+1)+3 : ℕ):ℝ)^k) * (r/δ) := by
  have hrpos := hδ.trans_le hr
  have hcount := tube_ball_grid_count T hδ hw hrpos x cells hinc hball
  have hcast : (cells.card : ℝ) ≤
      ((Nat.ceil (4*(r+width*δ)/δ):ℝ)+1)*((2*Nat.ceil (width+1)+3 : ℕ):ℝ)^k := by
    exact_mod_cast hcount
  have hceil := Nat.ceil_lt_add_one (by positivity : 0 ≤ 4*(r+width*δ)/δ)
  have hratio : 1 ≤ r/δ := (le_div_iff₀ hδ).mpr (by simpa using hr)
  have hid : 4*(r+width*δ)/δ = 4*(r/δ)+4*width := by field_simp
  have hfactor : (Nat.ceil (4*(r+width*δ)/δ):ℝ)+1 ≤ (6+4*width)*(r/δ) := by
    rw [hid] at hceil
    rw [hid]
    nlinarith [mul_le_mul_of_nonneg_left hratio hw]
  have hpow : 0 ≤ ((2*Nat.ceil (width+1)+3 : ℕ):ℝ)^k := by positivity
  exact hcast.trans (by nlinarith [mul_le_mul_of_nonneg_right hfactor hpow])

end KakeyaFormal.TubeLocalCount
