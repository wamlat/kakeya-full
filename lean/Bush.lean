import PivotDirections
import TubeLocalCount
import CapCover

/-!
# The cumulative finite bush argument for actual Euclidean tube shadings

All incidence counts below are counts of the actual `TubeFamily` data. Local
ball removal and distant-cell multiplicity are derived from tube geometry.
-/
namespace KakeyaFormal.Bush

open KakeyaFormal.GridGeometry KakeyaFormal.TubeLocalCount KakeyaFormal.PivotDirections

noncomputable section

def incidenceMass {k M : ℕ} (F : TubeFamily k M) (tubes : Finset (Fin M)) : ℝ :=
  ∑ i ∈ tubes, ((F.shade i).card:ℝ)

def degree {k M : ℕ} (F : TubeFamily k M) (tubes : Finset (Fin M)) (x : Cell k) : ℝ := by
  classical
  exact ((tubes.filter fun i => x ∈ F.shade i).card:ℝ)

/-- Double counting uses the actual finite shading relation. -/
theorem incidenceMass_eq_sum_degree {k M : ℕ} (F : TubeFamily k M)
    (tubes : Finset (Fin M)) :
    incidenceMass F tubes = ∑ x ∈ F.unionCells, degree F tubes x := by
  classical
  have hfilter (i : Fin M) : F.unionCells.filter (fun x => x ∈ F.shade i) = F.shade i := by
    ext x
    simp only [Finset.mem_filter,and_iff_right_iff_imp]
    exact fun hx => F.shade_subset_union i hx
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := tubes) (t := F.unionCells) (fun i x => x ∈ F.shade i)
  simp only [Finset.bipartiteAbove,Finset.bipartiteBelow,hfilter] at h
  dsimp [incidenceMass,degree]
  exact_mod_cast h

/-- Positive cumulative incidence mass guarantees an actual occupied cell. -/
theorem union_nonempty_of_mass_pos {k M : ℕ} (F : TubeFamily k M)
    (tubes : Finset (Fin M)) (h : 0 < incidenceMass F tubes) : F.unionCells.Nonempty := by
  classical
  by_contra hempty
  have he : F.unionCells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  rw [incidenceMass_eq_sum_degree,he,Finset.sum_empty] at h
  linarith

/-- A largest actual cell degree is at least the mean incidence degree. -/
theorem exists_bush_cell {k M : ℕ} (F : TubeFamily k M)
    (tubes : Finset (Fin M)) (h : 0 < incidenceMass F tubes) :
    ∃ x ∈ F.unionCells, incidenceMass F tubes ≤ (F.unionCells.card:ℝ)*degree F tubes x := by
  classical
  obtain ⟨x,hx,hmax⟩ := F.unionCells.exists_max_image (degree F tubes) (union_nonempty_of_mass_pos F tubes h)
  refine ⟨x,hx,?_⟩
  rw [incidenceMass_eq_sum_degree]
  calc
    _ ≤ ∑ y ∈ F.unionCells, degree F tubes x := Finset.sum_le_sum (fun y hy => hmax y hy)
    _ = _ := by simp

def retainedTubes {k M : ℕ} (F : TubeFamily k M) (threshold : ℝ) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter (fun i => threshold ≤ ((F.shade i).card:ℝ))

/-- Deleting tubes below a fixed actual cardinality threshold loses at most
threshold times the original number of tubes. -/
theorem retained_incidence_mass {k M : ℕ} (F : TubeFamily k M) {threshold : ℝ}
    (hthreshold : 0 ≤ threshold) :
    incidenceMass F Finset.univ - threshold*M ≤ incidenceMass F (retainedTubes F threshold) := by
  classical
  have hpoint (i : Fin M) : ((F.shade i).card:ℝ)-threshold ≤
      if threshold ≤ ((F.shade i).card:ℝ) then ((F.shade i).card:ℝ) else 0 := by
    split_ifs with h
    · linarith
    · linarith
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) (fun i _ => hpoint i)
  simpa [incidenceMass,retainedTubes,Finset.sum_filter,Finset.sum_sub_distrib,mul_comm] using hsum

/-- Explicit tube-ball grid constant from the previously proved geometric count. -/
def localConstant (k : ℕ) (width : ℝ) : ℝ :=
  (6+4*width)*((2*Nat.ceil (width+1)+3 : ℕ):ℝ)^k

theorem localConstant_ge_one (k : ℕ) {width : ℝ} (hw : 1 ≤ width) :
    1 ≤ localConstant k width := by
  have hp : (1:ℝ) ≤ ((2*Nat.ceil (width+1)+3 : ℕ):ℝ)^k :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ 2*Nat.ceil (width+1)+3 by omega))
  dsimp [localConstant]
  nlinarith

def nearCells {k M : ℕ} (F : TubeFamily k M) (δ r : ℝ) (x : Cell k) (i : Fin M) : Finset (Cell k) := by
  classical
  exact (F.shade i).filter (fun y => dist (cellCenter δ y) (cellCenter δ x) ≤ r)

def farCells {k M : ℕ} (F : TubeFamily k M) (δ r : ℝ) (x : Cell k) (i : Fin M) : Finset (Cell k) := by
  classical
  exact (F.shade i).filter (fun y => r < dist (cellCenter δ y) (cellCenter δ x))

/-- The geometric tube-ball bound controls the actual deleted cells. -/
theorem nearCells_bound {k M : ℕ} (F : TubeFamily k M) {δ width r : ℝ}
    (hF : F.Admissible width δ) (hδ : 0 < δ) (hw : 0 ≤ width) (hr : δ ≤ r)
    (x : Cell k) (i : Fin M) :
    ((nearCells F δ r x i).card:ℝ) ≤ localConstant k width*(r/δ) := by
  classical
  apply tube_ball_grid_count_real (F.tube i) hδ hw hr (cellCenter δ x) (nearCells F δ r x i)
  · intro y hy
    exact hF i y (Finset.mem_filter.mp hy).1
  · intro y hy
    exact (Finset.mem_filter.mp hy).2

/-- Near and far cells partition the original finite shading exactly. -/
theorem near_far_card {k M : ℕ} (F : TubeFamily k M) (δ r : ℝ) (x : Cell k) (i : Fin M) :
    (nearCells F δ r x i).card + (farCells F δ r x i).card = (F.shade i).card := by
  classical
  simpa only [nearCells,farCells,not_le] using
    Finset.card_filter_add_card_filter_not (s := F.shade i)
      (p := fun y => dist (cellCenter δ y) (cellCenter δ x) ≤ r)

/-- Every retained tube keeps a quantitatively large actual far-cell population. -/
theorem farCells_lower {k M : ℕ} (F : TubeFamily k M) {δ width r threshold : ℝ}
    (hF : F.Admissible width δ) (hδ : 0 < δ) (hw : 0 ≤ width) (hr : δ ≤ r)
    (x : Cell k) (i : Fin M) (hi : i ∈ retainedTubes F threshold) :
    threshold-localConstant k width*(r/δ) ≤ ((farCells F δ r x i).card:ℝ) := by
  have hnear := nearCells_bound F hF hδ hw hr x i
  have hsum : ((nearCells F δ r x i).card:ℝ)+((farCells F δ r x i).card:ℝ) = (F.shade i).card := by
    exact_mod_cast near_far_card F δ r x i
  have hret : threshold ≤ ((F.shade i).card:ℝ) := (Finset.mem_filter.mp hi).2
  linarith

def bushTubes {k M : ℕ} (F : TubeFamily k M) (threshold : ℝ) (x : Cell k) : Finset (Fin M) := by
  classical
  exact (retainedTubes F threshold).filter (fun i => x ∈ F.shade i)

/-- Outside incidences from an actual bush are bounded by actual occupied-cell
count times the geometrically derived common-cell multiplicity. -/
theorem bush_far_incidence_bound {k M : ℕ} (F : TubeFamily k M)
    {δ width r m A threshold : ℝ} (hF : F.Admissible width δ) (hcap : F.CapBound δ m A)
    (hδ : 0 < δ) (hw : 0 ≤ width) (hr : δ ≤ r) (hA : 0 ≤ A)
    (hsmall : 4*(width*δ) ≤ r) (hcaplo : δ ≤ 8*(width*δ)/r)
    (hcaphi : 8*(width*δ)/r ≤ 1) (x : Cell k) :
    degree F (retainedTubes F threshold) x * (threshold-localConstant k width*(r/δ)) ≤
      (F.unionCells.card:ℝ)*(A*(8*width/r)^m) := by
  classical
  have hr0 : 0 < r := hδ.trans_le hr
  have hb : 0 ≤ A*(8*width/r)^m := mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
  have h := Finset.card_nsmul_le_card_nsmul
    (s := bushTubes F threshold x) (t := F.unionCells)
    (r := fun i y => y ∈ farCells F δ r x i)
    (m := threshold-localConstant k width*(r/δ)) (n := A*(8*width/r)^m) ?_ ?_
  · simpa only [degree,bushTubes,nsmul_eq_mul] using h
  · intro i hi
    have hid : F.unionCells.bipartiteAbove (fun i y => y ∈ farCells F δ r x i) i =
        farCells F δ r x i := by
      ext y
      simp only [Finset.mem_bipartiteAbove,and_iff_right_iff_imp]
      exact fun hy => F.shade_subset_union i (Finset.mem_filter.mp hy).1
    rw [hid]
    exact farCells_lower F hF hδ hw hr x i (Finset.mem_filter.mp hi).1
  · intro y hy
    by_cases hfar : r < dist (cellCenter δ y) (cellCenter δ x)
    · have hcount := two_cell_cap_multiplicity F hF hcap hδ (hδ.trans_le hr) hsmall hcaplo hcaphi
        x y (by simpa only [dist_comm] using hfar.le)
      have hsub : (bushTubes F threshold x).bipartiteBelow
          (fun i y => y ∈ farCells F δ r x i) y ⊆
          Finset.univ.filter (fun i => x ∈ F.shade i ∧ y ∈ F.shade i) := by
        intro i hi
        obtain ⟨hib,hiy⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hib).2,
          (Finset.mem_filter.mp hiy).1⟩
      have hc : (((bushTubes F threshold x).bipartiteBelow
          (fun i y => y ∈ farCells F δ r x i) y).card:ℝ) ≤
          ((Finset.univ.filter fun i => x ∈ F.shade i ∧ y ∈ F.shade i).card:ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hc.trans hcount
    · have he : (bushTubes F threshold x).bipartiteBelow
          (fun i y => y ∈ farCells F δ r x i) y = ∅ := by
        ext i
        simp [Finset.bipartiteBelow,farCells,hfar]
      simpa only [he,Finset.card_empty,Nat.cast_zero] using hb

/-- The complete bush double count before choosing numerical radius/threshold
constants. The hypotheses are primitive geometry and actual cumulative mass. -/
theorem cumulative_bush_product {k M : ℕ} (F : TubeFamily k M)
    {δ width r m A threshold mass : ℝ} (hF : F.Admissible width δ) (hcap : F.CapBound δ m A)
    (hδ : 0 < δ) (hw : 0 ≤ width) (hr : δ ≤ r) (hA : 0 ≤ A)
    (hsmall : 4*(width*δ) ≤ r) (hcaplo : δ ≤ 8*(width*δ)/r)
    (hcaphi : 8*(width*δ)/r ≤ 1) (hthreshold : 0 ≤ threshold)
    (hmass : mass ≤ incidenceMass F Finset.univ)
    (hretain : 0 < mass-threshold*M)
    (houtside : 0 ≤ threshold-localConstant k width*(r/δ)) :
    (mass-threshold*M)*(threshold-localConstant k width*(r/δ)) ≤
      (F.unionCells.card:ℝ)^2 * (A*(8*width/r)^m) := by
  have hret := retained_incidence_mass F hthreshold
  have hlower : mass-threshold*M ≤ incidenceMass F (retainedTubes F threshold) := by linarith
  obtain ⟨x,hx,hmean⟩ := exists_bush_cell F (retainedTubes F threshold) (hretain.trans_le hlower)
  have hfar := bush_far_incidence_bound (threshold := threshold) F hF hcap hδ hw hr hA hsmall hcaplo hcaphi x
  have hfirst := mul_le_mul_of_nonneg_right (hlower.trans hmean) houtside
  have hsecond := mul_le_mul_of_nonneg_left hfar (Nat.cast_nonneg F.unionCells.card)
  nlinarith

/-- The only density threshold needed to make the fixed bush radius work. -/
def densityThreshold (k : ℕ) (width : ℝ) : ℝ := 64*width*localConstant k width

theorem densityThreshold_pos (k : ℕ) {width : ℝ} (hw : 1 ≤ width) :
    0 < densityThreshold k width := by
  have hL := localConstant_ge_one k hw
  dsimp [densityThreshold]
  positivity

/-- Cumulative bush square bound above the explicit bounded-density cutoff.
The shade counts may be unequal or zero; their total is the only mass hypothesis. -/
theorem dense_bush_square_ratio {k M : ℕ} (F : TubeFamily k M)
    {δ width s m A : ℝ} (hF : F.Admissible width δ) (hcap : F.CapBound δ m A)
    (hδ : 0 < δ) (hw : 1 ≤ width) (hs : 0 < s) (hs1 : s ≤ 1) (hA : 0 ≤ A)
    (hM : 0 < M) (hmass : (s/δ)*M ≤ incidenceMass F Finset.univ)
    (hdense : densityThreshold k width*δ ≤ s) :
    s^2*(M:ℝ) ≤ 8*δ^2*(F.unionCells.card:ℝ)^2 *
      (A*(densityThreshold k width/s)^m) := by
  let L := localConstant k width
  let r := s/(8*L)
  have hL1 : 1 ≤ L := localConstant_ge_one k hw
  have hL : 0 < L := by linarith
  have hw0 : 0 ≤ width := by linarith
  have hM0 : (0:ℝ) < M := by exact_mod_cast hM
  have hrad : 8*(width*δ) ≤ r := by
    apply (le_div_iff₀ (by positivity : 0 < 8*L)).mpr
    dsimp [densityThreshold] at hdense
    dsimp [L]
    nlinarith
  have hr : δ ≤ r := by nlinarith
  have hr0 : 0 < r := hδ.trans_le hr
  have hsmall : 4*(width*δ) ≤ r := by nlinarith
  have hcaphi : 8*(width*δ)/r ≤ 1 := (div_le_iff₀ hr0).mpr (by simpa using hrad)
  have hrupper : r ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 8*L)).mpr
    nlinarith
  have hcaplo : δ ≤ 8*(width*δ)/r := (le_div_iff₀ hr0).mpr (by nlinarith)
  have hretain : 0 < (s/δ)*(M:ℝ)-(s/(2*δ))*M := by
    have heq : (s/δ)*(M:ℝ)-(s/(2*δ))*M = (s/(2*δ))*M := by ring
    rw [heq]
    positivity
  have hlocal : L*(r/δ) = s/(8*δ) := by dsimp [r]; field_simp
  have houtside : 0 ≤ s/(2*δ)-L*(r/δ) := by
    rw [hlocal]
    have hid : s/(2*δ)-s/(8*δ) = 3*s/(8*δ) := by ring
    rw [hid]
    positivity
  have h := cumulative_bush_product F hF hcap hδ hw0 hr hA hsmall hcaplo hcaphi
    (by positivity : 0 ≤ s/(2*δ)) hmass hretain houtside
  have hlocal' : localConstant k width*(r/δ) = s/(8*δ) := hlocal
  rw [hlocal'] at h
  have hratio : 8*width/r = densityThreshold k width/s := by
    dsimp [r,L,densityThreshold]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  rw [hratio] at h
  have hleft : s^2*(M:ℝ)/(8*δ^2) ≤
      ((s/δ)*(M:ℝ)-(s/(2*δ))*M)*(s/(2*δ)-s/(8*δ)) := by
    have hid : ((s/δ)*(M:ℝ)-(s/(2*δ))*M)*(s/(2*δ)-s/(8*δ)) =
        3*s^2*(M:ℝ)/(16*δ^2) := by ring
    rw [hid]
    have hp : 0 ≤ s^2*(M:ℝ)/δ^2 := by positivity
    calc
      _ = (1/8)*(s^2*(M:ℝ)/δ^2) := by ring
      _ ≤ (3/16)*(s^2*(M:ℝ)/δ^2) :=
        mul_le_mul_of_nonneg_right (show (1/8:ℝ) ≤ 3/16 by norm_num) hp
      _ = _ := by ring
  have hb := (div_le_iff₀ (by positivity : 0 < 8*δ^2)).mp (hleft.trans h)
  nlinarith

/-- The exact real-exponent square form of the dense cumulative bush estimate. -/
theorem dense_bush_square {k M : ℕ} (F : TubeFamily k M)
    {δ width s m A : ℝ} (hF : F.Admissible width δ) (hcap : F.CapBound δ m A)
    (hδ : 0 < δ) (hw : 1 ≤ width) (hs : 0 < s) (hs1 : s ≤ 1) (hA : 0 ≤ A)
    (hM : 0 < M) (hmass : (s/δ)*M ≤ incidenceMass F Finset.univ)
    (hdense : densityThreshold k width*δ ≤ s) :
    s^(m+2)*(M:ℝ) ≤
      (8*(densityThreshold k width)^m)*A*δ^2*(F.unionCells.card:ℝ)^2 := by
  have h := dense_bush_square_ratio F hF hcap hδ hw hs hs1 hA hM hmass hdense
  have hD := densityThreshold_pos k hw
  have hpow : 0 < s^m := Real.rpow_pos_of_pos hs m
  have hmul := mul_le_mul_of_nonneg_left h hpow.le
  have hratio : (densityThreshold k width/s)^m = (densityThreshold k width)^m/s^m :=
    Real.div_rpow hD.le hs.le m
  rw [hratio] at hmul
  have hsplus : s^(m+2) = s^m*s^2 := by
    rw [Real.rpow_add hs,Real.rpow_two]
  rw [hsplus]
  have hid : s^m*(8*δ^2*(F.unionCells.card:ℝ)^2*(A*((densityThreshold k width)^m/s^m))) =
      (8*(densityThreshold k width)^m)*A*δ^2*(F.unionCells.card:ℝ)^2 := by field_simp
  rw [hid] at hmul
  nlinarith

/-- A fixed constant covering both bounded-density and dense bush cases.
Here the actual ambient dimension is k+1. -/
def squareConstant (k : ℕ) (width m : ℝ) : ℝ :=
  8*(densityThreshold (k+1) width)^m +
    KakeyaFormal.ProjectiveGeometry.packingConstant k*(densityThreshold (k+1) width)^(m+2)+1

theorem squareConstant_pos (k : ℕ) {width m : ℝ} (hw : 1 ≤ width) :
    0 < squareConstant k width m := by
  have hD := densityThreshold_pos (k+1) hw
  have hP := KakeyaFormal.ProjectiveGeometry.packingConstant_ge_one k
  dsimp [squareConstant]
  positivity

/-- A positive cumulative mass gives at least one actual occupied grid cell. -/
theorem union_card_ge_one {k M : ℕ} (F : TubeFamily k M) {δ s : ℝ}
    (hδ : 0 < δ) (hs : 0 < s) (hM : 0 < M)
    (hmass : (s/δ)*M ≤ incidenceMass F Finset.univ) : 1 ≤ (F.unionCells.card:ℝ) := by
  have hMp : (0:ℝ) < M := by exact_mod_cast hM
  have hp : 0 < incidenceMass F Finset.univ := (mul_pos (div_pos hs hδ) hMp).trans_le hmass
  exact_mod_cast Finset.card_pos.mpr (union_nonempty_of_mass_pos F Finset.univ hp)

/-- The bounded-density case follows from the actual finite cap cover and the
nonempty union, with no assumed total-tube count. -/
theorem sparse_bush_square {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ width s m A : ℝ} (hcap : F.CapBound δ m A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 1 ≤ width) (hs : 0 < s) (hm : 0 < m)
    (hA : 0 ≤ A) (hM : 0 < M) (hmass : (s/δ)*M ≤ incidenceMass F Finset.univ)
    (hsparse : s ≤ densityThreshold (k+1) width*δ) :
    s^(m+2)*(M:ℝ) ≤
      (KakeyaFormal.ProjectiveGeometry.packingConstant k*(densityThreshold (k+1) width)^(m+2))*
        A*δ^2*(F.unionCells.card:ℝ)^2 := by
  have htotal := KakeyaFormal.CapCover.cap_bound_total_count_scale F hδ hδ1 hA hcap
  have hD := densityThreshold_pos (k+1) hw
  have hP := KakeyaFormal.ProjectiveGeometry.packingConstant_ge_one k
  have hE := union_card_ge_one F hδ hs hM hmass
  have hpow := Real.rpow_le_rpow hs.le hsparse (by linarith : 0 ≤ m+2)
  have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg M
  have hp : 0 ≤ (densityThreshold (k+1) width*δ)^(m+2) := by positivity
  have hstep := mul_le_mul hpow htotal hM0 hp
  have hid : (densityThreshold (k+1) width*δ)^(m+2)*
      (KakeyaFormal.ProjectiveGeometry.packingConstant k*A*δ^(-m)) =
      (KakeyaFormal.ProjectiveGeometry.packingConstant k*(densityThreshold (k+1) width)^(m+2))*A*δ^2 := by
    rw [Real.mul_rpow hD.le hδ.le]
    have he : δ^(m+2)*δ^(-m) = δ^2 := by
      rw [← Real.rpow_add hδ]
      have he : m+2+-m = (2:ℝ) := by ring
      rw [he,Real.rpow_two]
    calc
      _ = (KakeyaFormal.ProjectiveGeometry.packingConstant k*(densityThreshold (k+1) width)^(m+2))*A*
          (δ^(m+2)*δ^(-m)) := by ring
      _ = _ := by rw [he]
  rw [hid] at hstep
  have hcoef : 0 ≤
      (KakeyaFormal.ProjectiveGeometry.packingConstant k*(densityThreshold (k+1) width)^(m+2))*A*δ^2 := by
    positivity
  exact hstep.trans (by nlinarith [mul_nonneg hcoef (show 0 ≤ (F.unionCells.card:ℝ)^2-1 by nlinarith)])

/-- Cumulative bush square bound at every density, for arbitrary positive real
cap exponent m. Empty individual shadings and highly unequal densities are allowed. -/
theorem cumulative_bush_square {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ width s m A : ℝ} (hF : F.Admissible width δ) (hcap : F.CapBound δ m A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 1 ≤ width) (hs : 0 < s) (hs1 : s ≤ 1)
    (hm : 0 < m) (hA : 0 ≤ A) (hM : 0 < M)
    (hmass : (s/δ)*M ≤ incidenceMass F Finset.univ) :
    s^(m+2)*(M:ℝ) ≤ squareConstant k width m*A*δ^2*(F.unionCells.card:ℝ)^2 := by
  have hD := densityThreshold_pos (k+1) hw
  have hP := KakeyaFormal.ProjectiveGeometry.packingConstant_ge_one k
  have hfactor : 0 ≤ A*δ^2*(F.unionCells.card:ℝ)^2 := by positivity
  by_cases hdense : densityThreshold (k+1) width*δ ≤ s
  · have h := dense_bush_square F hF hcap hδ hw hs hs1 hA hM hmass hdense
    have hC : 8*(densityThreshold (k+1) width)^m ≤ squareConstant k width m := by
      dsimp [squareConstant]
      have ha : 0 ≤ 8*(densityThreshold (k+1) width)^m := by positivity
      have hb : 0 ≤ KakeyaFormal.ProjectiveGeometry.packingConstant k*
          (densityThreshold (k+1) width)^(m+2) := by positivity
      linarith
    have hc := mul_le_mul_of_nonneg_right hC hfactor
    exact h.trans (by nlinarith)
  · have h := sparse_bush_square F hcap hδ hδ1 hw hs hm hA hM hmass (le_of_not_ge hdense)
    have hC : KakeyaFormal.ProjectiveGeometry.packingConstant k*(densityThreshold (k+1) width)^(m+2) ≤
        squareConstant k width m := by
      dsimp [squareConstant]
      have ha : 0 ≤ 8*(densityThreshold (k+1) width)^m := by positivity
      have hb : 0 ≤ KakeyaFormal.ProjectiveGeometry.packingConstant k*
          (densityThreshold (k+1) width)^(m+2) := by positivity
      linarith
    have hc := mul_le_mul_of_nonneg_right hC hfactor
    exact h.trans (by nlinarith)

/-- Fixed reciprocal constant in the linear-in-number-of-tubes bush theorem. -/
def bushConstant (k : ℕ) (width m : ℝ) : ℝ :=
  (Real.sqrt (squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k))⁻¹

theorem bushConstant_pos (k : ℕ) {width m : ℝ} (hw : 1 ≤ width) :
    0 < bushConstant k width m := by
  have hK := squareConstant_pos (m := m) k hw
  have hP := KakeyaFormal.ProjectiveGeometry.packingConstant_ge_one k
  dsimp [bushConstant]
  positivity

/-- Taking square roots and using the actual cap-cover total count gives the
linear-in-M cumulative bush bound before reciprocal factors are distributed. -/
theorem cumulative_bush_linear_product {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ width s m A : ℝ} (hF : F.Admissible width δ) (hcap : F.CapBound δ m A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 1 ≤ width) (hs : 0 < s) (hs1 : s ≤ 1)
    (hm : 0 < m) (hA : 0 < A) (hM : 0 < M)
    (hmass : (s/δ)*M ≤ incidenceMass F Finset.univ) :
    s^((m+2)/2)*(M:ℝ) ≤
      Real.sqrt (squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k)*
        A*δ^(1-m/2)*(F.unionCells.card:ℝ) := by
  have hK := squareConstant_pos (m := m) k hw
  have hP := KakeyaFormal.ProjectiveGeometry.packingConstant_ge_one k
  have hsq := cumulative_bush_square F hF hcap hδ hδ1 hw hs hs1 hm hA.le hM hmass
  have htotal := KakeyaFormal.CapCover.cap_bound_total_count_scale F hδ hδ1 hA.le hcap
  have hfirst := mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg M)
  have hcoef : 0 ≤ squareConstant k width m*A*δ^2*(F.unionCells.card:ℝ)^2 := by positivity
  have hsecond := mul_le_mul_of_nonneg_left htotal hcoef
  have hpowδ : δ^2*δ^(-m) = δ^(2-m) := by
    rw [← Real.rpow_two,← Real.rpow_add hδ]
    congr 1
  have hid : (squareConstant k width m*A*δ^2*(F.unionCells.card:ℝ)^2)*
      (KakeyaFormal.ProjectiveGeometry.packingConstant k*A*δ^(-m)) =
      (squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k)*
        A^2*δ^(2-m)*(F.unionCells.card:ℝ)^2 := by
    calc
      _ = (squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k)*
          A^2*(δ^2*δ^(-m))*(F.unionCells.card:ℝ)^2 := by ring
      _ = _ := by rw [hpowδ]
  rw [hid] at hsecond
  have hbound : s^(m+2)*(M:ℝ)^2 ≤
      (squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k)*
        A^2*δ^(2-m)*(F.unionCells.card:ℝ)^2 := by nlinarith
  have hsquare : (s^((m+2)/2))^2 = s^(m+2) := by
    rw [← Real.rpow_mul_natCast hs.le]
    congr 1
    norm_num
  have hδsquare : (δ^(1-m/2))^2 = δ^(2-m) := by
    rw [← Real.rpow_mul_natCast hδ.le]
    congr 1
    norm_num
    ring
  have hsqrt : (Real.sqrt (squareConstant k width m*
      KakeyaFormal.ProjectiveGeometry.packingConstant k))^2 =
      squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k :=
    Real.sq_sqrt (by positivity)
  have hleftsq : (s^((m+2)/2)*(M:ℝ))^2 = s^(m+2)*(M:ℝ)^2 := by rw [mul_pow,hsquare]
  have hrightsq :
      (Real.sqrt (squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k)*
        A*δ^(1-m/2)*(F.unionCells.card:ℝ))^2 =
      (squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k)*
        A^2*δ^(2-m)*(F.unionCells.card:ℝ)^2 := by
    simp only [mul_pow,hsqrt,hδsquare]
  have hnleft : 0 ≤ s^((m+2)/2)*(M:ℝ) := by positivity
  have hnright : 0 ≤ Real.sqrt (squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k)*
      A*δ^(1-m/2)*(F.unionCells.card:ℝ) := by positivity
  nlinarith

/-- Appendix A.1 for actual finite Euclidean tube shadings, with an explicit
positive constant fixed before scale, density, cap coefficient and tube count.
The N-form is δ^(m/2−1)=N^(1−m/2). -/
theorem cumulative_bush_lower_bound {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ width s m A : ℝ} (hF : F.Admissible width δ) (hcap : F.CapBound δ m A)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 1 ≤ width) (hs : 0 < s) (hs1 : s ≤ 1)
    (hm : 0 < m) (hA : 0 < A) (hM : 0 < M)
    (hmass : (s/δ)*M ≤ incidenceMass F Finset.univ) :
    bushConstant k width m*A⁻¹*δ^(m/2-1)*s^((m+2)/2)*(M:ℝ) ≤
      (F.unionCells.card:ℝ) := by
  have h := cumulative_bush_linear_product F hF hcap hδ hδ1 hw hs hs1 hm hA hM hmass
  have hK := squareConstant_pos (m := m) k hw
  have hP := KakeyaFormal.ProjectiveGeometry.packingConstant_ge_one k
  have hden : 0 < Real.sqrt (squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k)*
      A*δ^(1-m/2) := by positivity
  have hdiv := (div_le_iff₀ hden).mpr (by nlinarith : s^((m+2)/2)*(M:ℝ) ≤
      (F.unionCells.card:ℝ)*(Real.sqrt (squareConstant k width m*KakeyaFormal.ProjectiveGeometry.packingConstant k)*
        A*δ^(1-m/2)))
  have hinv : δ^(m/2-1) = (δ^(1-m/2))⁻¹ := by
    have he : m/2-1 = -(1-m/2) := by ring
    rw [he,Real.rpow_neg hδ.le]
  calc
    _ = (s^((m+2)/2)*(M:ℝ))/(Real.sqrt (squareConstant k width m*
        KakeyaFormal.ProjectiveGeometry.packingConstant k)*A*δ^(1-m/2)) := by
      rw [hinv]
      dsimp [bushConstant]
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := hdiv

/-- Increasing the fixed tube-width normalization preserves actual admissibility. -/
theorem admissible_width_mono {k M : ℕ} (F : TubeFamily k M) {δ width wide : ℝ}
    (hF : F.Admissible width δ) (hδ : 0 ≤ δ) (hw : width ≤ wide) : F.Admissible wide δ := by
  intro i x hx
  obtain ⟨t,ht,hclose⟩ := hF i x hx
  exact ⟨t,ht,hclose.trans (mul_le_mul_of_nonneg_right hw hδ)⟩

/-- Fully quantified Appendix A.1 with arbitrary fixed width normalization.
The positive constant depends only on actual ambient dimension, width, and m. -/
theorem cumulative_bush_estimate (k : ℕ) (width m : ℝ) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) (F : TubeFamily (k+1) M) (δ s A : ℝ),
      F.Admissible width δ → F.CapBound δ m A → 0 < δ → δ ≤ 1 →
      0 < s → s ≤ 1 → 1 ≤ A → 0 < M →
      (s/δ)*M ≤ incidenceMass F Finset.univ →
      c*A⁻¹*δ^(m/2-1)*s^((m+2)/2)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  refine ⟨bushConstant k (max width 1) m,bushConstant_pos k (le_max_right _ _),?_⟩
  intro M F δ s A hF hcap hδ hδ1 hs hs1 hA hM hmass
  exact cumulative_bush_lower_bound F (admissible_width_mono F hF hδ.le (le_max_left _ _))
    hcap hδ hδ1 (le_max_right _ _) hs hs1 hm (by linarith) hM hmass

/-- The bush estimate supplies the actual discrete real-cap seed for every
positive-dimensional ambient space, including the full scale-loss quantifier. -/
theorem bush_discrete_estimate (k : ℕ) {m : ℝ} (hm : 0 < m) :
    DiscreteEstimate (k+1) m ((m+2)/2) ((m+2)/2) := by
  intro geom ε hε
  obtain ⟨c,hc,estimate⟩ := cumulative_bush_estimate k geom.width m hm
  refine ⟨c,hc,?_⟩
  intro F
  by_cases hM : 0 < F.M
  · have hmass : (F.lam/F.δ)*F.M ≤ incidenceMass F.family Finset.univ := by
      have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin F.M)))
        (fun i _ => (F.comparable i).1)
      simpa [incidenceMass,mul_comm] using h
    have h := estimate F.M F.family F.δ F.lam F.A F.admissible F.cap_bound F.scale_pos F.scale_le_one
      F.density_pos F.density_le_one F.cap_ge_one hM hmass
    have hexp : m-(m+2)/2+ε = (m/2-1)+ε := by ring
    have hpε : F.δ^ε ≤ 1 := Real.rpow_le_one F.scale_pos.le F.scale_le_one hε.le
    have hpow : F.δ^(m-(m+2)/2+ε) ≤ F.δ^(m/2-1) := by
      rw [hexp,Real.rpow_add F.scale_pos]
      exact mul_le_of_le_one_right (Real.rpow_nonneg F.scale_pos.le _) hpε
    have hcoef : 0 ≤ c*F.A⁻¹*F.lam^((m+2)/2)*(F.M:ℝ) := by
      have hA : 0 < F.A := by linarith [F.cap_ge_one]
      have hs : 0 < F.lam := F.density_pos
      positivity
    have hgain := mul_le_mul_of_nonneg_left hpow hcoef
    exact (show c*F.A⁻¹*F.δ^(m-(m+2)/2+ε)*F.lam^((m+2)/2)*(F.M:ℝ) ≤
        c*F.A⁻¹*F.δ^(m/2-1)*F.lam^((m+2)/2)*(F.M:ℝ) by nlinarith).trans h
  · have hzero : F.M = 0 := Nat.eq_zero_of_not_pos hM
    simp only [hzero,Nat.cast_zero,mul_zero]
    exact Nat.cast_nonneg _

/-- The fully defined real-cap predicate K(m,(m+2)/2,(m+2)/2) follows from
actual finite Euclidean tube geometry; no analytic input is assumed. -/
theorem bush_real_cap_estimate {m : ℝ} (hm : 0 < m) :
    RealCapEstimate m ((m+2)/2) ((m+2)/2) := by
  intro dimension hdim
  cases dimension with
  | zero => norm_num at hdim; linarith
  | succ k => exact bush_discrete_estimate k hm

end
end KakeyaFormal.Bush

#print axioms KakeyaFormal.Bush.cumulative_bush_square
#print axioms KakeyaFormal.Bush.cumulative_bush_lower_bound

#print axioms KakeyaFormal.Bush.bush_real_cap_estimate
