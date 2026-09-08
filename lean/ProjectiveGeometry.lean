import Configurations
import GridGeometry

/-!
# Projective chord geometry and dimension-reduced spherical chart packing

`projectiveDistance` is the actual minimum of the two unoriented chord lengths.
Metric laws here are pseudometric laws on vector representatives; antipodal
vectors have distance zero. The finite packing arguments below work with actual
unit vectors, not an assumed packing or cap theorem.
-/
namespace KakeyaFormal.ProjectiveGeometry
open KakeyaFormal
open KakeyaFormal.GridGeometry

noncomputable section

theorem projective_symm {k : ℕ} (v w : Space k) :
    projectiveDistance v w = projectiveDistance w v := by
  simp [projectiveDistance, norm_sub_rev, add_comm]

theorem projective_neg_left {k : ℕ} (v w : Space k) :
    projectiveDistance (-v) w = projectiveDistance v w := by
  rw [projective_symm, projectiveDistance_neg_right, projective_symm]

theorem projective_le_chord {k : ℕ} (v w : Space k) :
    projectiveDistance v w ≤ ‖v-w‖ := min_le_left _ _

theorem projective_le_antipodal_chord {k : ℕ} (v w : Space k) :
    projectiveDistance v w ≤ ‖v+w‖ := min_le_right _ _

theorem projective_triangle {k : ℕ} (u v w : Space k) :
    projectiveDistance u w ≤ projectiveDistance u v + projectiveDistance v w := by
  unfold projectiveDistance
  by_cases h1 : ‖u-v‖ ≤ ‖u+v‖ <;> by_cases h2 : ‖v-w‖ ≤ ‖v+w‖
  · rw [min_eq_left h1, min_eq_left h2]
    apply (min_le_left _ _).trans
    have h := norm_add_le (u-v) (v-w)
    have heq : (u-v)+(v-w) = u-w := by abel
    rwa [heq] at h
  · rw [min_eq_left h1, min_eq_right (le_of_not_ge h2)]
    apply (min_le_right _ _).trans
    have h := norm_add_le (u-v) (v+w)
    have heq : (u-v)+(v+w) = u+w := by abel
    rwa [heq] at h
  · rw [min_eq_right (le_of_not_ge h1), min_eq_left h2]
    apply (min_le_right _ _).trans
    have h := norm_sub_le (u+v) (v-w)
    have heq : (u+v)-(v-w) = u+w := by abel
    simpa only [heq] using h
  · rw [min_eq_right (le_of_not_ge h1), min_eq_right (le_of_not_ge h2)]
    apply (min_le_left _ _).trans
    have h := norm_sub_le (u+v) (v+w)
    have heq : (u+v)-(v+w) = u-w := by abel
    simpa only [heq] using h

theorem projective_zero_iff {k : ℕ} (v w : Space k) :
    projectiveDistance v w = 0 ↔ v = w ∨ v = -w := by
  constructor
  · intro h
    unfold projectiveDistance at h
    rcases le_total ‖v-w‖ ‖v+w‖ with hle | hle
    · rw [min_eq_left hle] at h
      exact Or.inl (sub_eq_zero.mp (norm_eq_zero.mp h))
    · rw [min_eq_right hle] at h
      exact Or.inr (eq_neg_iff_add_eq_zero.mpr (norm_eq_zero.mp h))
  · rintro (rfl | rfl)
    · exact projectiveDistance_self _
    · simp [projectiveDistance]

/-- A projective cap permits a choice of one of the two unit-vector representatives
lying in the corresponding ordinary Euclidean ball. -/
theorem cap_representative {k : ℕ} (v w : Space k) {r : ℝ}
    (h : projectiveDistance v w ≤ r) :
    ∃ u : Space k, (u = v ∨ u = -v) ∧ dist u w ≤ r := by
  rcases min_le_iff.mp h with hminus | hplus
  · exact ⟨v, Or.inl rfl, by simpa only [dist_eq_norm] using hminus⟩
  · refine ⟨-v, Or.inr rfl, ?_⟩
    have heq : -v-w = -(v+w) := by abel
    simpa only [dist_eq_norm, heq, norm_neg] using hplus

/-- Euclidean l2 norm is bounded by the sum of coordinate absolute values. -/
theorem norm_le_coordinate_sum {k : ℕ} (v : Space k) :
    ‖v‖ ≤ ∑ i, |WithLp.ofLp v i| := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Fin k))) (f := fun i => |WithLp.ofLp v i|)
    (fun i _ => abs_nonneg _)
  simp only [sq_abs, ← EuclideanSpace.real_norm_sq_eq] at hs
  have hp : (0:ℝ) ≤ ∑ i, |WithLp.ofLp v i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  nlinarith [norm_nonneg v]

/-- An actual unit vector has a coordinate of size at least 1/k.
This loose bound avoids square roots and suffices for finite coordinate charts. -/
theorem unit_has_large_coordinate {k : ℕ} (v : Space k) (hv : ‖v‖ = 1) :
    ∃ i : Fin k, (1:ℝ) ≤ (k:ℝ) * |WithLp.ofLp v i| := by
  classical
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    have hn := norm_le_coordinate_sum v
    norm_num [hv] at hn
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  have hsum : (1:ℝ) ≤ ∑ i, |WithLp.ofLp v i| := by simpa [hv] using norm_le_coordinate_sum v
  by_contra hn
  push Not at hn
  have hlt : ∑ i : Fin k, (k:ℝ) * |WithLp.ofLp v i| < ∑ _i : Fin k, (1:ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.univ_nonempty
    · intro i _
      exact hn i
  have hid : ∑ i : Fin k, (k:ℝ) * |WithLp.ofLp v i| =
      (k:ℝ) * (∑ i, |WithLp.ofLp v i|) := by rw [Finset.mul_sum]
  rw [hid] at hlt
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hlt
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  nlinarith

/-- The hemisphere coordinate is controlled by the other k coordinates. This is
the geometric dimension drop from a sphere in R^(k+1) to a k-coordinate chart. -/
theorem sphere_chart_distance {k : ℕ} {v w : Space (k+1)}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) {c h : ℝ} (hc : 0 < c) (hh : 0 ≤ h)
    (hvc : c ≤ WithLp.ofLp v 0) (hwc : c ≤ WithLp.ofLp w 0)
    (hrest : ∀ i : Fin k, |WithLp.ofLp v i.succ - WithLp.ofLp w i.succ| ≤ h) :
    dist v w ≤ ((k:ℝ)+1)*(1+1/c)*h := by
  have hvsum : WithLp.ofLp v 0 ^ 2 + ∑ i : Fin k, WithLp.ofLp v i.succ ^ 2 = 1 := by
    simpa [hv, Fin.sum_univ_succ] using (EuclideanSpace.real_norm_sq_eq v).symm
  have hwsum : WithLp.ofLp w 0 ^ 2 + ∑ i : Fin k, WithLp.ofLp w i.succ ^ 2 = 1 := by
    simpa [hw, Fin.sum_univ_succ] using (EuclideanSpace.real_norm_sq_eq w).symm
  have hterm (i : Fin k) :
      |WithLp.ofLp w i.succ ^ 2 - WithLp.ofLp v i.succ ^ 2| ≤ 2*h := by
    have hvcoord : |WithLp.ofLp v i.succ| ≤ 1 := by
      simpa [Real.norm_eq_abs, hv] using PiLp.norm_apply_le v i.succ
    have hwcoord : |WithLp.ofLp w i.succ| ≤ 1 := by
      simpa [Real.norm_eq_abs, hw] using PiLp.norm_apply_le w i.succ
    have hsumcoord : |WithLp.ofLp w i.succ + WithLp.ofLp v i.succ| ≤ 2 :=
      (abs_add_le _ _).trans (by linarith)
    have hid : WithLp.ofLp w i.succ ^ 2 - WithLp.ofLp v i.succ ^ 2 =
        (WithLp.ofLp w i.succ - WithLp.ofLp v i.succ) *
        (WithLp.ofLp w i.succ + WithLp.ofLp v i.succ) := by ring
    rw [hid, abs_mul]
    have hdiff : |WithLp.ofLp w i.succ - WithLp.ofLp v i.succ| ≤ h := by
      simpa only [abs_sub_comm] using hrest i
    nlinarith [mul_le_mul hdiff hsumcoord (abs_nonneg _) hh]
  have hdiffsum : WithLp.ofLp v 0 ^ 2 - WithLp.ofLp w 0 ^ 2 =
      ∑ i : Fin k, (WithLp.ofLp w i.succ ^ 2 - WithLp.ofLp v i.succ ^ 2) := by
    rw [Finset.sum_sub_distrib]
    linarith
  have hsqdiff : |WithLp.ofLp v 0 ^ 2 - WithLp.ofLp w 0 ^ 2| ≤ 2*(k:ℝ)*h := by
    rw [hdiffsum]
    calc
      _ ≤ ∑ i : Fin k, |WithLp.ofLp w i.succ ^ 2 - WithLp.ofLp v i.succ ^ 2| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin k, 2*h := Finset.sum_le_sum (fun i _ => hterm i)
      _ = _ := by simp; ring
  have hprod : |WithLp.ofLp v 0 - WithLp.ofLp w 0| *
      (WithLp.ofLp v 0 + WithLp.ofLp w 0) ≤ 2*(k:ℝ)*h := by
    have hid : WithLp.ofLp v 0 ^ 2 - WithLp.ofLp w 0 ^ 2 =
        (WithLp.ofLp v 0 - WithLp.ofLp w 0) *
        (WithLp.ofLp v 0 + WithLp.ofLp w 0) := by ring
    simpa only [hid, abs_mul, abs_of_pos (show 0 < WithLp.ofLp v 0 + WithLp.ofLp w 0 by linarith)]
      using hsqdiff
  have hfirst : |WithLp.ofLp v 0 - WithLp.ofLp w 0| ≤ (k:ℝ)*h/c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith [abs_nonneg (WithLp.ofLp v 0 - WithLp.ofLp w 0)]
  have hothers : (∑ i : Fin k, |WithLp.ofLp v i.succ - WithLp.ofLp w i.succ|) ≤ (k:ℝ)*h := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrest i)
  have hnorm := norm_le_coordinate_sum (v-w)
  rw [Fin.sum_univ_succ] at hnorm
  simp only [PiLp.sub_apply] at hnorm
  have hC : (k:ℝ)*h/c + (k:ℝ)*h ≤ ((k:ℝ)+1)*(1+1/c)*h := by
    have hpos : 0 ≤ (1+1/c)*h := mul_nonneg (by positivity) hh
    have hid : (k:ℝ)*h/c + (k:ℝ)*h + (1+1/c)*h = ((k:ℝ)+1)*(1+1/c)*h := by ring
    linarith
  rw [dist_eq_norm]
  exact hnorm.trans ((add_le_add hfirst hothers).trans hC)

/-- Two real coordinates in the same scaled integer interval are at distance at most h. -/
theorem same_floor_distance {a b h : ℝ} (hh : 0 < h) (heq : ⌊a/h⌋ = ⌊b/h⌋) :
    |a-b| ≤ h := by
  have ha := Int.floor_le (a/h)
  have hb := Int.floor_le (b/h)
  have hau := Int.lt_floor_add_one (a/h)
  have hbu := Int.lt_floor_add_one (b/h)
  rw [← heq] at hb hbu
  have h1 := (le_div_iff₀ hh).mp ha
  have h2 := (le_div_iff₀ hh).mp hb
  have h3 := (div_lt_iff₀ hh).mp hau
  have h4 := (div_lt_iff₀ hh).mp hbu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Positive constant for the inverse chart bound. -/
def chartConstant (k : ℕ) (c : ℝ) : ℝ := ((k:ℝ)+1)*(1+1/c)

theorem chartConstant_pos (k : ℕ) {c : ℝ} (hc : 0 < c) : 0 < chartConstant k c := by
  dsimp [chartConstant]
  positivity

/-- k-dimensional integer coordinates for a spherical chart in ambient R^(k+1). -/
def chartBin {k : ℕ} (h : ℝ) (v : Space (k+1)) : Cell k :=
  fun i => ⌊WithLp.ofLp v i.succ / h⌋

/-- A small k-coordinate bin contains at most one separated unit direction in the chart. -/
theorem chartBin_injective {k : ℕ} (directions : Finset (Space (k+1)))
    {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hunit : ∀ v ∈ directions, ‖v‖ = 1)
    (hchart : ∀ v ∈ directions, c ≤ WithLp.ofLp v 0)
    (hsep : ∀ v ∈ directions, ∀ w ∈ directions, v ≠ w → δ ≤ projectiveDistance v w) :
    Set.InjOn (chartBin (δ/(2*chartConstant k c))) (directions : Set (Space (k+1))) := by
  intro v hv w hw heq
  by_contra hvw
  have hC := chartConstant_pos k hc
  have hmesh : 0 < δ/(2*chartConstant k c) := div_pos hδ (by positivity)
  have hdist := sphere_chart_distance (hunit v hv) (hunit w hw) hc hmesh.le
    (hchart v hv) (hchart w hw)
    (fun i => same_floor_distance hmesh (congrFun heq i))
  have hid : ((k:ℝ)+1)*(1+1/c)*(δ/(2*chartConstant k c)) = δ/2 := by
    change chartConstant k c * (δ/(2*chartConstant k c)) = δ/2
    field_simp
  rw [hid] at hdist
  have hlow := (hsep v hv w hw hvw).trans (projective_le_chord v w)
  rw [← dist_eq_norm] at hlow
  linarith


/-- Quantizing a real coordinate within r of a center produces only O(1+r/h)
integer labels, uniformly in the center. -/
theorem floor_distance_bounds {a b r h : ℝ} (hh : 0 < h) (hab : |a-b| ≤ r) :
    ⌊b/h⌋ - (Nat.ceil (r/h)+1 : ℕ) ≤ ⌊a/h⌋ ∧
    ⌊a/h⌋ ≤ ⌊b/h⌋ + (Nat.ceil (r/h)+1 : ℕ) := by
  have hal := Int.floor_le (a/h)
  have hau := Int.lt_floor_add_one (a/h)
  have hbl := Int.floor_le (b/h)
  have hbu := Int.lt_floor_add_one (b/h)
  have hceil := Nat.le_ceil (r/h)
  have hupper := div_le_div_of_nonneg_right (abs_le.mp hab).2 hh.le
  have hlower := div_le_div_of_nonneg_right (abs_le.mp hab).1 hh.le
  rw [sub_div] at hupper hlower
  rw [neg_div] at hlower
  constructor
  · have hreal : (⌊b/h⌋:ℝ) - ((Nat.ceil (r/h):ℝ)+1) ≤ (⌊a/h⌋:ℝ) := by linarith
    exact_mod_cast hreal
  · have hreal : (⌊a/h⌋:ℝ) ≤ (⌊b/h⌋:ℝ) + ((Nat.ceil (r/h):ℝ)+1) := by linarith
    exact_mod_cast hreal

/-- Finite packing on an actual spherical chart. The exponent is k in ambient
R^(k+1), rather than the ambient exponent k+1. -/
theorem spherical_chart_packing {k : ℕ} (directions : Finset (Space (k+1)))
    (center : Space (k+1)) {c δ r : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hunit : ∀ v ∈ directions, ‖v‖ = 1)
    (hchart : ∀ v ∈ directions, c ≤ WithLp.ofLp v 0)
    (hcap : ∀ v ∈ directions, dist v center ≤ r)
    (hsep : ∀ v ∈ directions, ∀ w ∈ directions, v ≠ w → δ ≤ projectiveDistance v w) :
    directions.card ≤ (2*Nat.ceil (r/(δ/(2*chartConstant k c)))+3)^k := by
  classical
  let h := δ/(2*chartConstant k c)
  have hh : 0 < h := div_pos hδ (by have := chartConstant_pos k hc; positivity)
  have hi := chartBin_injective directions hc hδ hunit hchart hsep
  have himage : (directions.image (chartBin h)).card = directions.card :=
    Finset.card_image_of_injOn hi
  have hs : directions.image (chartBin h) ⊆
      gridBox (fun i => ⌊WithLp.ofLp center i.succ / h⌋) (Nat.ceil (r/h)+1) := by
    intro z hz
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hz
    rw [mem_gridBox]
    intro i
    exact floor_distance_bounds hh ((coordinate_dist_le v center i.succ).trans (hcap v hv))
  have hb := Finset.card_le_card hs
  rw [himage, gridBox_card] at hb
  simpa [h, Nat.mul_add, Nat.add_assoc] using hb

/-- The chart cap estimate in the usual scale-ratio form, for r≥δ. -/
theorem spherical_chart_packing_real {k : ℕ} (directions : Finset (Space (k+1)))
    (center : Space (k+1)) {c δ r : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hr : δ ≤ r)
    (hunit : ∀ v ∈ directions, ‖v‖ = 1)
    (hchart : ∀ v ∈ directions, c ≤ WithLp.ofLp v 0)
    (hcap : ∀ v ∈ directions, dist v center ≤ r)
    (hsep : ∀ v ∈ directions, ∀ w ∈ directions, v ≠ w → δ ≤ projectiveDistance v w) :
    (directions.card : ℝ) ≤ (4*chartConstant k c+5)^k * (r/δ)^k := by
  have hb := spherical_chart_packing directions center hc hδ hunit hchart hcap hsep
  have hC := chartConstant_pos k hc
  have hratio : 1 ≤ r/δ := (le_div_iff₀ hδ).mpr (by simpa using hr)
  have hrpos : 0 < r := hδ.trans_le hr
  have hscale : 0 < r/(δ/(2*chartConstant k c)) := by positivity
  have hceil := Nat.ceil_lt_add_one hscale.le
  have hid : r/(δ/(2*chartConstant k c)) = 2*chartConstant k c*(r/δ) := by field_simp
  rw [hid] at hceil
  have hbase : ((2*Nat.ceil (r/(δ/(2*chartConstant k c)))+3 : ℕ):ℝ) ≤
      (4*chartConstant k c+5)*(r/δ) := by rw [hid]; push_cast; nlinarith
  have hbR : (directions.card : ℝ) ≤
      (((2*Nat.ceil (r/(δ/(2*chartConstant k c)))+3 : ℕ):ℝ))^k := by exact_mod_cast hb
  calc
    _ ≤ (((2*Nat.ceil (r/(δ/(2*chartConstant k c)))+3 : ℕ):ℝ))^k := hbR
    _ ≤ ((4*chartConstant k c+5)*(r/δ))^k := pow_le_pow_left₀ (by positivity) hbase k
    _ = _ := mul_pow _ _ _


/-- Coordinate permutations act isometrically on the actual Euclidean space. -/
def reindex {k : ℕ} (e : Fin k ≃ Fin k) (v : Space k) : Space k :=
  WithLp.toLp 2 (fun i => WithLp.ofLp v (e i))

theorem reindex_norm {k : ℕ} (e : Fin k ≃ Fin k) (v : Space k) :
    ‖reindex e v‖ = ‖v‖ := by
  have hsq : ‖reindex e v‖^2 = ‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    exact e.sum_comp (fun i => WithLp.ofLp v i ^ 2)
  nlinarith [norm_nonneg (reindex e v), norm_nonneg v]

theorem reindex_sub {k : ℕ} (e : Fin k ≃ Fin k) (v w : Space k) :
    reindex e (v-w) = reindex e v - reindex e w := by rfl

theorem reindex_add {k : ℕ} (e : Fin k ≃ Fin k) (v w : Space k) :
    reindex e (v+w) = reindex e v + reindex e w := by rfl

theorem reindex_dist {k : ℕ} (e : Fin k ≃ Fin k) (v w : Space k) :
    dist (reindex e v) (reindex e w) = dist v w := by
  rw [dist_eq_norm, ← reindex_sub, reindex_norm, dist_eq_norm]

theorem reindex_projective {k : ℕ} (e : Fin k ≃ Fin k) (v w : Space k) :
    projectiveDistance (reindex e v) (reindex e w) = projectiveDistance v w := by
  simp only [projectiveDistance, ← reindex_sub, ← reindex_add, reindex_norm]

/-- Move a chosen signed coordinate to the positive zeroth-coordinate chart. -/
def chartMove {k : ℕ} (i : Fin (k+1)) (sign : Bool) (v : Space (k+1)) : Space (k+1) :=
  if sign then reindex (Equiv.swap 0 i) v else -(reindex (Equiv.swap 0 i) v)

theorem chartMove_norm {k : ℕ} (i : Fin (k+1)) (sign : Bool) (v : Space (k+1)) :
    ‖chartMove i sign v‖ = ‖v‖ := by cases sign <;> simp [chartMove, reindex_norm]

theorem chartMove_dist {k : ℕ} (i : Fin (k+1)) (sign : Bool) (v w : Space (k+1)) :
    dist (chartMove i sign v) (chartMove i sign w) = dist v w := by
  cases sign <;> simp [chartMove, reindex_dist]

theorem chartMove_projective {k : ℕ} (i : Fin (k+1)) (sign : Bool) (v w : Space (k+1)) :
    projectiveDistance (chartMove i sign v) (chartMove i sign w) = projectiveDistance v w := by
  cases sign <;> simp [chartMove, projective_neg_left, projectiveDistance_neg_right, reindex_projective]

theorem chartMove_injective {k : ℕ} (i : Fin (k+1)) (sign : Bool) :
    Function.Injective (chartMove i sign) := by
  intro v w h
  have hd := chartMove_dist i sign v w
  rw [h, dist_self] at hd
  exact dist_eq_zero.mp hd.symm

theorem chartMove_zero {k : ℕ} (i : Fin (k+1)) (sign : Bool) (v : Space (k+1)) :
    WithLp.ofLp (chartMove i sign v) 0 = if sign then WithLp.ofLp v i else -WithLp.ofLp v i := by
  cases sign <;> simp [chartMove, reindex]

/-- Every unit vector lies in one of the 2(k+1) signed coordinate charts. -/
theorem unit_in_signed_chart {k : ℕ} (v : Space (k+1)) (hv : ‖v‖ = 1) :
    ∃ i : Fin (k+1), ∃ sign : Bool,
      1/((k:ℝ)+1) ≤ WithLp.ofLp (chartMove i sign v) 0 := by
  obtain ⟨i, hi⟩ := unit_has_large_coordinate v hv
  have hdim : (0:ℝ) < (k:ℝ)+1 := by positivity
  have hlarge : 1/((k:ℝ)+1) ≤ |WithLp.ofLp v i| :=
    (div_le_iff₀ hdim).mpr (by simpa [mul_comm] using hi)
  by_cases hp : 0 ≤ WithLp.ofLp v i
  · exact ⟨i, true, by simpa [chartMove_zero, abs_of_nonneg hp] using hlarge⟩
  · exact ⟨i, false, by simpa [chartMove_zero, abs_of_neg (lt_of_not_ge hp)] using hlarge⟩

/-- Full spherical cap packing in an ordinary Euclidean ball, after the proved
finite signed-coordinate chart covering. Its exponent is ambient dimension minus one. -/
theorem spherical_cap_packing {k : ℕ} (directions : Finset (Space (k+1)))
    (center : Space (k+1)) {δ r : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hunit : ∀ v ∈ directions, ‖v‖ = 1)
    (hcap : ∀ v ∈ directions, dist v center ≤ r)
    (hsep : ∀ v ∈ directions, ∀ w ∈ directions, v ≠ w → δ ≤ projectiveDistance v w) :
    (directions.card : ℝ) ≤ 2*((k:ℝ)+1) *
      (4*chartConstant k (1/((k:ℝ)+1))+5)^k * (r/δ)^k := by
  classical
  let c : ℝ := 1/((k:ℝ)+1)
  have hc : 0 < c := by dsimp [c]; positivity
  let blocks : (Fin (k+1) × Bool) → Finset (Space (k+1)) :=
    fun label => directions.filter (fun v => c ≤ WithLp.ofLp (chartMove label.1 label.2 v) 0)
  have hcover : directions ⊆ Finset.univ.biUnion blocks := by
    intro v hv
    obtain ⟨i, sign, hi⟩ := unit_in_signed_chart v (hunit v hv)
    exact Finset.mem_biUnion.mpr ⟨(i,sign), Finset.mem_univ _, Finset.mem_filter.mpr ⟨hv,hi⟩⟩
  have hblock (label : Fin (k+1) × Bool) :
      ((blocks label).card : ℝ) ≤ (4*chartConstant k c+5)^k*(r/δ)^k := by
    let moved := (blocks label).image (chartMove label.1 label.2)
    have hcard : moved.card = (blocks label).card :=
      Finset.card_image_of_injective _ (chartMove_injective _ _)
    have hu : ∀ v ∈ moved, ‖v‖ = 1 := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      rw [chartMove_norm]
      exact hunit w (Finset.mem_filter.mp hw).1
    have hchart : ∀ v ∈ moved, c ≤ WithLp.ofLp v 0 := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hw).2
    have hdist : ∀ v ∈ moved, dist v (chartMove label.1 label.2 center) ≤ r := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      rw [chartMove_dist]
      exact hcap w (Finset.mem_filter.mp hw).1
    have hsepm : ∀ v ∈ moved, ∀ w ∈ moved, v ≠ w → δ ≤ projectiveDistance v w := by
      intro v hv w hw hvw
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
      rw [chartMove_projective]
      apply hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      intro hab
      exact hvw (congrArg _ hab)
    simpa only [hcard] using spherical_chart_packing_real moved
      (chartMove label.1 label.2 center) hc hδ hr hu hchart hdist hsepm
  have hcount := (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)
  have hcountR : (directions.card : ℝ) ≤ ∑ label : Fin (k+1) × Bool, ((blocks label).card : ℝ) := by
    exact_mod_cast hcount
  calc
    _ ≤ ∑ label : Fin (k+1) × Bool, ((blocks label).card : ℝ) := hcountR
    _ ≤ ∑ _label : Fin (k+1) × Bool, (4*chartConstant k c+5)^k*(r/δ)^k :=
      Finset.sum_le_sum (fun label _ => hblock label)
    _ = _ := by simp [c]; ring


/-- Choose the sign nearest a projective cap center, using an explicit distance test. -/
def nearRepresentative {k : ℕ} (center : Space k) (r : ℝ) (v : Space k) : Space k :=
  if dist v center ≤ r then v else -v

theorem nearRepresentative_norm {k : ℕ} (center v : Space k) (r : ℝ) :
    ‖nearRepresentative center r v‖ = ‖v‖ := by
  dsimp [nearRepresentative]
  split <;> simp

theorem nearRepresentative_projective {k : ℕ} (center v w : Space k) (r : ℝ) :
    projectiveDistance (nearRepresentative center r v) (nearRepresentative center r w) =
      projectiveDistance v w := by
  dsimp [nearRepresentative]
  split <;> split <;> simp [projective_neg_left, projectiveDistance_neg_right]

theorem nearRepresentative_in_cap {k : ℕ} (center v : Space k) {r : ℝ}
    (hcap : projectiveDistance v center ≤ r) :
    dist (nearRepresentative center r v) center ≤ r := by
  unfold nearRepresentative
  split
  · assumption
  · rename_i hnot
    have hplus : ‖v+center‖ ≤ r := by
      rcases min_le_iff.mp hcap with hm | hp
      · exact False.elim (hnot (by simpa only [dist_eq_norm] using hm))
      · exact hp
    have heq : -v-center = -(v+center) := by abel
    simpa only [dist_eq_norm, heq, norm_neg] using hplus

/-- Choosing representatives cannot identify distinct positively separated directions. -/
theorem nearRepresentative_injective {k : ℕ} (directions : Finset (Space k))
    (center : Space k) (r : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ v ∈ directions, ∀ w ∈ directions, v ≠ w → δ ≤ projectiveDistance v w) :
    Set.InjOn (nearRepresentative center r) (directions : Set (Space k)) := by
  intro v hv w hw heq
  by_contra hne
  have hlo := hsep v hv w hw hne
  have hid := nearRepresentative_projective center v w r
  rw [heq, projectiveDistance_self] at hid
  rw [← hid] at hlo
  linarith

/-- Actual full-dimensional projective cap packing: in ambient R^(k+1), the
exponent is k. Constants are explicit, and no packing or covering theorem is a premise. -/
theorem projective_cap_packing {k : ℕ} (directions : Finset (Space (k+1)))
    (center : Space (k+1)) {δ r : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hunit : ∀ v ∈ directions, ‖v‖ = 1)
    (hcap : ∀ v ∈ directions, projectiveDistance v center ≤ r)
    (hsep : ∀ v ∈ directions, ∀ w ∈ directions, v ≠ w → δ ≤ projectiveDistance v w) :
    (directions.card : ℝ) ≤ 2*((k:ℝ)+1) *
      (4*chartConstant k (1/((k:ℝ)+1))+5)^k * (r/δ)^k := by
  classical
  let reps := directions.image (nearRepresentative center r)
  have hcard : reps.card = directions.card :=
    Finset.card_image_of_injOn (nearRepresentative_injective directions center r hδ hsep)
  have hu : ∀ v ∈ reps, ‖v‖ = 1 := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    rw [nearRepresentative_norm]
    exact hunit w hw
  have hcapr : ∀ v ∈ reps, dist v center ≤ r := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact nearRepresentative_in_cap center w (hcap w hw)
  have hsepr : ∀ v ∈ reps, ∀ w ∈ reps, v ≠ w → δ ≤ projectiveDistance v w := by
    intro v hv w hw hne
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hw
    rw [nearRepresentative_projective]
    apply hsep a ha b hb
    intro hab
    exact hne (congrArg _ hab)
  simpa only [hcard] using spherical_cap_packing reps center hδ hr hu hcapr hsepr

/-- Indexed families, retaining their original index cardinality. Positive projective
separation proves direction-map injectivity, so no multiplicity assumption is hidden. -/
theorem indexed_projective_cap_packing {k : ℕ} {ι : Type*}
    (indices : Finset ι) (direction : ι → Space (k+1)) (center : Space (k+1))
    {δ r : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hunit : ∀ i ∈ indices, ‖direction i‖ = 1)
    (hcap : ∀ i ∈ indices, projectiveDistance (direction i) center ≤ r)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      δ ≤ projectiveDistance (direction i) (direction j)) :
    (indices.card : ℝ) ≤ 2*((k:ℝ)+1) *
      (4*chartConstant k (1/((k:ℝ)+1))+5)^k * (r/δ)^k := by
  classical
  have hinj : Set.InjOn direction (indices : Set ι) := by
    intro i hi j hj heq
    by_contra hne
    have h := hsep i hi j hj hne
    rw [heq, projectiveDistance_self] at h
    linarith
  have hcard : (indices.image direction).card = indices.card := Finset.card_image_of_injOn hinj
  have hu : ∀ v ∈ indices.image direction, ‖v‖ = 1 := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact hunit i hi
  have hcapv : ∀ v ∈ indices.image direction, projectiveDistance v center ≤ r := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact hcap i hi
  have hsepv : ∀ v ∈ indices.image direction, ∀ w ∈ indices.image direction,
      v ≠ w → δ ≤ projectiveDistance v w := by
    intro v hv w hw hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
    apply hsep i hi j hj
    intro hij
    exact hne (congrArg _ hij)
  simpa only [hcard] using projective_cap_packing (indices.image direction) center
    hδ hr hu hcapv hsepv


/-- Explicit ambient-(k+1) sphere packing constant. -/
def packingConstant (k : ℕ) : ℝ :=
  2*((k:ℝ)+1)*(4*chartConstant k (1/((k:ℝ)+1))+5)^k

theorem packingConstant_formula (k : ℕ) :
    packingConstant k = 2*((k:ℝ)+1)*(4*((k:ℝ)+1)*((k:ℝ)+2)+5)^k := by
  simp only [packingConstant, chartConstant, one_div_one_div]
  congr 2
  ring

theorem packingConstant_ge_one (k : ℕ) : 1 ≤ packingConstant k := by
  have hc := chartConstant_pos k (show 0 < 1/((k:ℝ)+1) by positivity)
  have hp : (1:ℝ) ≤ (4*chartConstant k (1/((k:ℝ)+1))+5)^k :=
    one_le_pow₀ (by linarith)
  dsimp [packingConstant]
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- Full-direction cap coefficient for a fixed positive separation normalization. -/
def fullDirectionCoefficient (k : ℕ) (separation : ℝ) : ℝ :=
  packingConstant k * (1/(min separation 1))^k

theorem fullDirectionCoefficient_ge_one (k : ℕ) {separation : ℝ} (hs : 0 < separation) :
    1 ≤ fullDirectionCoefficient k separation := by
  have hq : 0 < min separation 1 := lt_min hs (by norm_num)
  have hqi : 1 ≤ 1/(min separation 1) := (le_div_iff₀ hq).mpr (by simp)
  have hp : (1:ℝ) ≤ (1/(min separation 1))^k := one_le_pow₀ hqi
  have hC := packingConstant_ge_one k
  dsimp [fullDirectionCoefficient]
  nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hp)]

/-- Actual direction-separated tube families satisfy the full ambient cap bound,
with exponent (ambient dimension minus one) and a constant independent of scale. -/
theorem separated_tube_family_cap_bound {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ separation : ℝ} (hδ : 0 < δ) (hs : 0 < separation)
    (hsep : F.Separated (separation*δ)) :
    F.CapBound δ (k:ℝ) (fullDirectionCoefficient k separation) := by
  classical
  intro center _ r hr _
  let q := min separation 1
  have hq : 0 < q := lt_min hs (by norm_num)
  have hqδ : 0 < q*δ := mul_pos hq hδ
  have hqr : q*δ ≤ r := by
    have h := mul_le_mul_of_nonneg_right (min_le_right separation 1) hδ.le
    dsimp [q]
    nlinarith
  let indices := Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction center ≤ r)
  have hcount := indexed_projective_cap_packing indices (fun i => (F.tube i).direction)
    center hqδ hqr (fun i _ => (F.tube i).unit_direction)
    (fun i hi => (Finset.mem_filter.mp hi).2)
    (fun i _ j _ hij =>
      (mul_le_mul_of_nonneg_right (min_le_left separation 1) hδ.le).trans (hsep i j hij))
  have hid : r/(q*δ) = (1/q)*(r/δ) := by ring
  rw [hid, mul_pow] at hcount
  rw [Real.rpow_natCast]
  simpa only [fullDirectionCoefficient, packingConstant, q, mul_assoc] using hcount

/-- Total-count bound for a full-dimensional separated family. The center zero
has chord distance exactly one from every unit direction, so no sphere cover is assumed. -/
theorem separated_total_tube_count {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hsep : F.Separated δ) :
    (M:ℝ) ≤ packingConstant k * (1/δ)^k := by
  have h := indexed_projective_cap_packing (Finset.univ : Finset (Fin M))
    (fun i => (F.tube i).direction) (0 : Space (k+1)) hδ hδ1
    (fun i _ => (F.tube i).unit_direction)
    (fun i _ => by simp [projectiveDistance, (F.tube i).unit_direction])
    (fun i _ j _ hij => hsep i j hij)
  simpa [packingConstant] using h


/-- Exact relation of the unoriented chord distance to the absolute inner product. -/
theorem projective_chord_sq {k : ℕ} (v w : Space k) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    projectiveDistance v w ^ 2 = 2 - 2*|inner ℝ v w| := by
  have hm := norm_sub_sq_real v w
  have hp := norm_add_sq_real v w
  simp only [hv, hw, one_pow] at hm hp
  by_cases hi : 0 ≤ inner ℝ v w
  · have horder : ‖v-w‖ ≤ ‖v+w‖ := by nlinarith [norm_nonneg (v-w), norm_nonneg (v+w)]
    rw [projectiveDistance, min_eq_left horder, abs_of_nonneg hi]
    linarith
  · have horder : ‖v+w‖ ≤ ‖v-w‖ := by nlinarith [norm_nonneg (v-w), norm_nonneg (v+w)]
    rw [projectiveDistance, min_eq_right horder, abs_of_neg (lt_of_not_ge hi)]
    linarith

/-- The actual angle's squared sine and projective chord squared differ by at most
factor two. Sine is unchanged by passing to the unoriented angle. -/
theorem projective_angle_sine_sq {k : ℕ} (v w : Space k) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    projectiveDistance v w ^ 2 / 2 ≤ (Real.sin (InnerProductGeometry.angle v w))^2 ∧
    (Real.sin (InnerProductGeometry.angle v w))^2 ≤ projectiveDistance v w ^ 2 := by
  have hc : Real.cos (InnerProductGeometry.angle v w) = inner ℝ v w := by
    simpa [hv,hw] using InnerProductGeometry.cos_angle v w
  have htrig := Real.sin_sq_add_cos_sq (InnerProductGeometry.angle v w)
  rw [hc] at htrig
  have habs : |inner ℝ v w| ≤ 1 := by simpa [hv,hw] using abs_real_inner_le_norm v w
  have hn := abs_nonneg (inner ℝ v w)
  have hid := projective_chord_sq v w hv hw
  have hsq := sq_abs (inner ℝ v w)
  constructor
  · nlinarith [mul_nonneg hn (sub_nonneg.mpr habs)]
  · nlinarith [sq_nonneg (|inner ℝ v w|-1)]

/-- The largest projective chord distance between unit representatives is at most sqrt2. -/
theorem projective_distance_le_sqrt_two {k : ℕ} (v w : Space k)
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) : projectiveDistance v w ≤ Real.sqrt 2 := by
  have hid := projective_chord_sq v w hv hw
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  nlinarith [Real.sqrt_nonneg (2:ℝ), projectiveDistance_nonneg v w, abs_nonneg (inner ℝ v w)]


end
end KakeyaFormal.ProjectiveGeometry
