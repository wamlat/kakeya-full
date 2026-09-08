import ThickCircle
import TubeIntersection
import MeasurableEnergy

/-! Actual finite dyadic inverse-angle sums and planar tube-intersection energy. -/
namespace KakeyaFormal.PlanarEnergy
open KakeyaFormal.ThickCircle KakeyaFormal.HairbrushPlanes KakeyaFormal.ProjectiveGeometry
open KakeyaFormal.TubeIntersection KakeyaFormal.TubeVolume
open MeasureTheory
noncomputable section

def shellCondition (δ d : ℝ) (j : ℕ) : Prop :=
  if j = 0 then d ≤ δ else δ*(2:ℝ)^(j-1) < d ∧ d ≤ δ*(2:ℝ)^j

/-- The finite dyadic shells cover every value below the chosen terminal scale. -/
theorem exists_shell {δ d : ℝ} (n : ℕ) (h : d ≤ δ*(2:ℝ)^n) :
    ∃ j ∈ Finset.range (n+1), shellCondition δ d j := by
  induction n with
  | zero => exact ⟨0,by simp,by simpa [shellCondition] using h⟩
  | succ n ih =>
    by_cases hn : d ≤ δ*(2:ℝ)^n
    · obtain ⟨j,hj,hcond⟩ := ih hn
      exact ⟨j,Finset.mem_range.mpr (by have := Finset.mem_range.mp hj; omega),hcond⟩
    · refine ⟨n+1,by simp,?_⟩
      simp only [shellCondition,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,Nat.add_sub_cancel]
      exact ⟨lt_of_not_ge hn,h⟩

/-- An inverse angle truncated at the mesh is bounded on each actual shell. -/
theorem shell_inverse_bound {δ d : ℝ} (hδ : 0 < δ) {j : ℕ}
    (hj : shellCondition δ d j) : 1/max d δ ≤ 2/(δ*(2:ℝ)^j) := by
  have hmax : 0 < max d δ := lt_of_lt_of_le hδ (le_max_right _ _)
  have hscale : 0 < δ*(2:ℝ)^j := by positivity
  apply (div_le_div_iff₀ hmax hscale).mpr
  by_cases hz : j = 0
  · subst j
    simp only [pow_zero,mul_one,one_mul]
    linarith [le_max_right d δ]
  · obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
    simp only [shellCondition,Nat.succ_ne_zero,↓reduceIte,Nat.succ_sub_one] at hj
    rw [pow_succ]
    nlinarith [le_max_left d δ]

/-- Linear cap population gives the logarithmic inverse-angle sum through an
actual finite shell cover; no row-sum bound is assumed. -/
theorem inverse_angle_sum_of_linear_caps {ι : Type*} (indices : Finset ι) (angle : ι → ℝ)
    {δ C : ℝ} (hδ : 0 < δ) (n : ℕ)
    (htop : ∀ i ∈ indices, angle i ≤ δ*(2:ℝ)^n)
    (hcap : ∀ r : ℝ, δ ≤ r →
      ((indices.filter fun i => angle i ≤ r).card:ℝ) ≤ C*(r/δ)) :
    (∑ i ∈ indices, 1/max (angle i) δ) ≤ 2*C*((n:ℝ)+1)/δ := by
  classical
  let shells : ℕ → Finset ι := fun j => indices.filter (fun i => shellCondition δ (angle i) j)
  let weight := fun i => 1/max (angle i) δ
  have hw : ∀ i, 0 ≤ weight i := by
    intro i
    exact one_div_nonneg.mpr ((le_max_right _ _).trans' hδ.le)
  have hcover : ∀ i ∈ indices, ∃ j ∈ Finset.range (n+1), i ∈ shells j := by
    intro i hi
    obtain ⟨j,hj,hcond⟩ := exists_shell n (htop i hi)
    exact ⟨j,hj,Finset.mem_filter.mpr ⟨hi,hcond⟩⟩
  have hsumcover : (∑ i ∈ indices, weight i) ≤
      ∑ j ∈ Finset.range (n+1), ∑ i ∈ shells j, weight i := by
    have hpoint (i) (hi : i ∈ indices) : weight i ≤
        ∑ j ∈ Finset.range (n+1), if shellCondition δ (angle i) j then weight i else 0 := by
      obtain ⟨j,hj,hij⟩ := hcover i hi
      have hcond := (Finset.mem_filter.mp hij).2
      have hs := Finset.single_le_sum (s := Finset.range (n+1))
        (f := fun l => if shellCondition δ (angle i) l then weight i else 0)
        (fun l _ => by split_ifs <;> positivity) hj
      simpa only [if_pos hcond] using hs
    have hs := Finset.sum_le_sum (fun i hi => hpoint i hi)
    rw [Finset.sum_comm] at hs
    simpa only [shells,Finset.sum_filter] using hs
  have hshell (j : ℕ) : (∑ i ∈ shells j, weight i) ≤ 2*C/δ := by
    have hrad : δ ≤ δ*(2:ℝ)^j := by
      have hpow : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
      nlinarith
    have hscale : 0 < δ*(2:ℝ)^j := by positivity
    have hsubset : shells j ⊆ indices.filter (fun i => angle i ≤ δ*(2:ℝ)^j) := by
      intro i hi
      obtain ⟨hi,hcond⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨hi,?_⟩
      by_cases hz : j = 0
      · simpa [shellCondition,hz] using hcond
      · simp only [shellCondition,if_neg hz] at hcond
        exact hcond.2
    have hcast : ((shells j).card:ℝ) ≤
        ((indices.filter fun i => angle i ≤ δ*(2:ℝ)^j).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hcount := hcast.trans (hcap _ hrad)
    have hweight : ∀ i ∈ shells j, weight i ≤ 2/(δ*(2:ℝ)^j) := by
      intro i hi
      exact shell_inverse_bound hδ (Finset.mem_filter.mp hi).2
    calc
      _ ≤ ∑ _i ∈ shells j, 2/(δ*(2:ℝ)^j) := Finset.sum_le_sum hweight
      _ = ((shells j).card:ℝ)*(2/(δ*(2:ℝ)^j)) := by simp
      _ ≤ (C*((δ*(2:ℝ)^j)/δ))*(2/(δ*(2:ℝ)^j)) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ∑ i ∈ shells j, weight i := hsumcover
    _ ≤ ∑ _j ∈ Finset.range (n+1), 2*C/δ := Finset.sum_le_sum (fun j _ => hshell j)
    _ = _ := by simp; ring

def dyadicDepth (δ : ℝ) : ℕ := Nat.ceil (Real.logb 2 (2/δ))

/-- A concrete logarithmic terminal shell covers every possible unit chord. -/
theorem dyadicDepth_covers {δ : ℝ} (hδ : 0 < δ) :
    (2:ℝ) ≤ δ*(2:ℝ)^(dyadicDepth δ) := by
  have hc := Nat.le_ceil (Real.logb 2 (2/δ))
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hc
  rw [Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    (by positivity : 0 < 2/δ),Real.rpow_natCast] at hp
  have h := (div_le_iff₀ hδ).mp hp
  simpa only [dyadicDepth,mul_comm] using h

theorem dyadicDepth_log_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((dyadicDepth δ:ℕ):ℝ)+1 ≤ Real.logb 2 (2/δ)+2 := by
  have hratio : (1:ℝ) ≤ 2/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hlog := Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hratio
  have hceil := Nat.ceil_lt_add_one hlog
  dsimp [dyadicDepth]
  linarith

theorem circleConstant_pos (k : ℕ) : 0 < circleConstant k 1 := by
  have hQ := chartConstant_pos (k+1) (show (0:ℝ) < 1/2 by norm_num)
  dsimp [circleConstant]
  positivity

/-- The geometric inverse-angle sum in an actual assigned plane bin is logarithmic. -/
theorem plane_inverse_angle_sum {ι : Type*} {k : ℕ} (stem center : UnitTube (k+2))
    (indices : Finset ι) (bristle : ι → UnitTube (k+2)) (w : Space (k+1))
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/2) (hw : ‖w‖ = 1)
    (hbin : ∀ i ∈ indices, projectiveDistance (bristleNormal stem (bristle i)) w ≤ δ)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      δ ≤ projectiveDistance (bristle i).direction (bristle j).direction) :
    (∑ i ∈ indices, 1/max (projectiveDistance center.direction (bristle i).direction) δ) ≤
      2*circleConstant k 1*(Real.logb 2 (2/δ)+2)/δ := by
  classical
  have hC := circleConstant_pos k
  have h := inverse_angle_sum_of_linear_caps (C := circleConstant k 1) indices
    (fun i => projectiveDistance center.direction (bristle i).direction)
    hδ (dyadicDepth δ) ?_ ?_
  · have hdepth := dyadicDepth_log_bound hδ (by linarith : δ ≤ 1)
    have hm := mul_le_mul_of_nonneg_left hdepth (by positivity : 0 ≤ 2*circleConstant k 1)
    exact h.trans (div_le_div_of_nonneg_right hm hδ.le)
  · intro i hi
    exact (unit_projective_le_two _ _ center.unit_direction (bristle i).unit_direction).trans (dyadicDepth_covers hδ)
  · intro r hr
    apply plane_bin_direction_count stem
      (indices.filter fun i => projectiveDistance center.direction (bristle i).direction ≤ r)
      bristle w center.direction hδ hδsmall hr hw
    · intro i hi
      exact hbin i (Finset.mem_filter.mp hi).1
    · intro i hi
      rw [projective_symm]
      exact (Finset.mem_filter.mp hi).2
    · intro i hi j hj hne
      exact hsep i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne

def rowConstant (k : ℕ) : ℝ :=
  88*(2:ℝ)^(k+2)*unitBallVolume (k+2)*circleConstant k 1

theorem rowConstant_pos (k : ℕ) : 0 < rowConstant k := by
  have hv := unitBallVolume_pos (k+2)
  have hc := circleConstant_pos k
  dsimp [rowConstant]
  positivity

/-- Equation (4.13): the actual tube-intersection volume row is bounded by
C_d log(2/δ) δ^(d−1), with a concrete logarithmic expression. -/
theorem planar_intersection_row {ι : Type*} {k : ℕ} (stem center : UnitTube (k+2))
    (indices : Finset ι) (bristle : ι → UnitTube (k+2)) (w : Space (k+1))
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/2) (hw : ‖w‖ = 1)
    (hbin : ∀ i ∈ indices, projectiveDistance (bristleNormal stem (bristle i)) w ≤ δ)
    (hsep : ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
      δ ≤ projectiveDistance (bristle i).direction (bristle j).direction) :
    (∑ i ∈ indices, (volume : Measure (Space (k+2))).real
      (center.carrier δ ∩ (bristle i).carrier δ)) ≤
      rowConstant k*(Real.logb 2 (2/δ)+2)*δ^(k+1) := by
  have hδ1 : δ ≤ 1 := by linarith
  have hsum := Finset.sum_le_sum (s := indices)
    (fun i _ => intersection_volume_upper center (bristle i) hδ hδ1)
  let K := 44*(2:ℝ)^(k+2)*unitBallVolume (k+2)
  have hK : 0 ≤ K*δ^(k+2) := by
    have hv := unitBallVolume_pos (k+2)
    dsimp [K]
    positivity
  have hid : (∑ i ∈ indices, (44*(2:ℝ)^(k+2)*unitBallVolume (k+2))*δ^(k+2)/
      max (projectiveDistance center.direction (bristle i).direction) δ) =
      (K*δ^(k+2))*(∑ i ∈ indices, 1/max (projectiveDistance center.direction (bristle i).direction) δ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [K]
    ring
  rw [hid] at hsum
  have hrow := plane_inverse_angle_sum stem center indices bristle w hδ hδsmall hw hbin hsep
  have hmul := mul_le_mul_of_nonneg_left hrow hK
  have hlast : (K*δ^(k+2))*(2*circleConstant k 1*(Real.logb 2 (2/δ)+2)/δ) =
      rowConstant k*(Real.logb 2 (2/δ)+2)*δ^(k+1) := by
    have hpow : δ^(k+2) = δ^(k+1)*δ := by rw [pow_succ]
    rw [hpow]
    dsimp [K,rowConstant]
    field_simp
    ring
  exact hsum.trans (hmul.trans_eq hlast)

/-- Actual measurable shadings inherit the geometric planar intersection row. -/
theorem planar_shading_row {ι : Type*} [Fintype ι] {k : ℕ} (stem : UnitTube (k+2))
    (bristle : ι → UnitTube (k+2)) (Y : ι → Set (Space (k+2))) (w : Space (k+1))
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/2) (hw : ‖w‖ = 1)
    (hbin : ∀ i, projectiveDistance (bristleNormal stem (bristle i)) w ≤ δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ projectiveDistance (bristle i).direction (bristle j).direction)
    (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ) (i : ι) :
    (∑ j, (volume : Measure (Space (k+2))).real (Y i ∩ Y j)) ≤
      rowConstant k*(Real.logb 2 (2/δ)+2)*δ^(k+1) := by
  have hrow := planar_intersection_row stem (bristle i) Finset.univ bristle w hδ hδsmall hw
    (fun j _ => hbin j) (fun a _ b _ hab => hsep a b hab)
  have hterm (j : ι) : (volume : Measure (Space (k+2))).real (Y i ∩ Y j) ≤
      (volume : Measure (Space (k+2))).real ((bristle i).carrier δ ∩ (bristle j).carrier δ) := by
    apply measureReal_mono
    · exact Set.inter_subset_inter (hsub i) (hsub j)
    · exact measure_ne_top_of_subset Set.inter_subset_left (carrier_finite (bristle i) δ)
  exact (Finset.sum_le_sum (fun j _ => hterm j)).trans hrow

/-- The actual per-bin union lower bound follows from the proved geometric row
and measurable L2 inequality, not an assumed row estimate. -/
theorem planar_shading_union_lower {ι : Type*} [Fintype ι] {k : ℕ} (stem : UnitTube (k+2))
    (bristle : ι → UnitTube (k+2)) (Y : ι → Set (Space (k+2))) (w : Space (k+1))
    {δ lam : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/2) (hw : ‖w‖ = 1) (hlam : 0 ≤ lam)
    (hbin : ∀ i, projectiveDistance (bristleNormal stem (bristle i)) w ≤ δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ projectiveDistance (bristle i).direction (bristle j).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hmass : ∀ i, lam ≤ (volume : Measure (Space (k+2))).real (Y i)) :
    (Fintype.card ι:ℝ)*lam^2/(rowConstant k*(Real.logb 2 (2/δ)+2)*δ^(k+1)) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  have hlog := Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    ((le_div_iff₀ hδ).mpr (by linarith) : (1:ℝ) ≤ 2/δ)
  have hC := rowConstant_pos k
  apply KakeyaFormal.MeasurableEnergy.finite_shading_union_lower Y hY
    (fun i => measure_ne_top_of_subset (hsub i) (carrier_finite (bristle i) δ)) hlam
    (by positivity) hmass
  exact planar_shading_row stem bristle Y w hδ hδsmall hw hbin hsep hsub

/-- Equation (4.14) with explicit constants: shadings of mass at least
λ δ^(d−1)/L in one actual plane bin have union at least c_d λ²δ^(d−1)#bin/L³. -/
theorem planar_density_union_lower {ι : Type*} [Fintype ι] {k : ℕ} (stem : UnitTube (k+2))
    (bristle : ι → UnitTube (k+2)) (Y : ι → Set (Space (k+2))) (w : Space (k+1))
    {δ lam L : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1/2) (hw : ‖w‖ = 1)
    (hlam : 0 ≤ lam) (hL : 0 < L) (hlogL : Real.logb 2 (2/δ)+2 ≤ L)
    (hbin : ∀ i, projectiveDistance (bristleNormal stem (bristle i)) w ≤ δ)
    (hsep : ∀ i j, i ≠ j → δ ≤ projectiveDistance (bristle i).direction (bristle j).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hmass : ∀ i, lam*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real (Y i)) :
    (Fintype.card ι:ℝ)*lam^2*δ^(k+1)/(rowConstant k*L^3) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  have hC := rowConstant_pos k
  have hrow (i : ι) : (∑ j, (volume : Measure (Space (k+2))).real (Y i ∩ Y j)) ≤
      rowConstant k*L*δ^(k+1) := by
    have h := planar_shading_row stem bristle Y w hδ hδsmall hw hbin hsep hsub i
    have hm := mul_le_mul_of_nonneg_left hlogL (by positivity : 0 ≤ rowConstant k*δ^(k+1))
    exact h.trans (by nlinarith)
  have h := KakeyaFormal.MeasurableEnergy.finite_shading_union_lower Y hY
    (fun i => measure_ne_top_of_subset (hsub i) (carrier_finite (bristle i) δ))
    (by positivity : 0 ≤ lam*δ^(k+1)/L) (by positivity : 0 < rowConstant k*L*δ^(k+1)) hmass hrow
  have hid : (Fintype.card ι:ℝ)*(lam*δ^(k+1)/L)^2/(rowConstant k*L*δ^(k+1)) =
      (Fintype.card ι:ℝ)*lam^2*δ^(k+1)/(rowConstant k*L^3) := by field_simp
  rwa [hid] at h

end
end KakeyaFormal.PlanarEnergy

#print axioms KakeyaFormal.PlanarEnergy.planar_intersection_row

#print axioms KakeyaFormal.PlanarEnergy.planar_density_union_lower
