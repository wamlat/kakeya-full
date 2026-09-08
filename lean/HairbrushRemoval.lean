import HairbrushUnion

/-!
# Actual crossing-ball removal in a transverse hairbrush

Points on a bristle outside a ball about a genuine common point are quantitatively
far from the stem axis. A measured concentration bound on that actual ball
retains the required shading mass and instantiates the geometric hairbrush union.
-/
namespace KakeyaFormal.HairbrushRemoval
open KakeyaFormal.HairbrushPlanes KakeyaFormal.EuclideanSplit
open KakeyaFormal.HairbrushUnion KakeyaFormal.TubeIntersection
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Any two points of the actual unit-tube carrier are at distance at most 1+2δ. -/
theorem carrier_diameter_bound {k : ℕ} (T : UnitTube k) {δ : ℝ} {x y : Space k}
    (hx : x ∈ T.carrier δ) (hy : y ∈ T.carrier δ) : dist x y ≤ 1+2*δ := by
  obtain ⟨s,hs,hxs⟩ := hx
  obtain ⟨t,ht,hyt⟩ := hy
  have hst : |s-t| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
  have h₁ := dist_triangle x (T.axisPoint s) y
  have h₂ := dist_triangle (T.axisPoint s) (T.axisPoint t) y
  rw [T.axisPoint_distance] at h₂
  rw [dist_comm (T.axisPoint t) y] at h₂
  linarith

/-- The actual carrier is contained in the ball of radius 1+δ about its base. -/
theorem carrier_base_bound {k : ℕ} (T : UnitTube k) {δ : ℝ} {x : Space k}
    (hx : x ∈ T.carrier δ) : dist x T.base ≤ 1+δ := by
  obtain ⟨t,ht,hxt⟩ := hx
  have htb : dist (T.axisPoint t) T.base = t := by
    rw [dist_eq_norm]
    simp only [UnitTube.axisPoint,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      T.unit_direction,mul_one,abs_of_nonneg ht.1]
  have h := dist_triangle x (T.axisPoint t) T.base
  rw [htb] at h
  linarith [ht.2]

/-- Bristles meeting a unit stem lie in a fixed physical ball, with no location
hypothesis on the tube bases. -/
theorem bristle_stem_base_bound {k : ℕ} (stem T : UnitTube k) {δ : ℝ}
    (hδ1 : δ ≤ 1) (hmeet : (stem.carrier δ ∩ T.carrier δ).Nonempty)
    {x : Space k} (hx : x ∈ T.carrier δ) : ‖x-stem.base‖ ≤ 5 := by
  obtain ⟨p,hpstem,hpT⟩ := hmeet
  have h₁ := carrier_diameter_bound T hx hpT
  have h₂ := carrier_base_bound stem hpstem
  have h₃ := dist_triangle x p stem.base
  change dist x stem.base ≤ 5
  linarith

/-- The stem's actual tube carrier has transverse radius at most δ. -/
theorem stem_carrier_transverse {k : ℕ} (stem : UnitTube (k+1)) {δ : ℝ}
    {p : Space (k+1)} (hp : p ∈ stem.carrier δ) :
    ‖transverseCoordinate (alignStem stem.direction) (p-stem.base)‖ ≤ δ := by
  obtain ⟨t,_,ht⟩ := hp
  have hid : p-stem.base = (p-stem.axisPoint t)+t • stem.direction := by
    dsimp [UnitTube.axisPoint]
    abel
  rw [hid,transverseCoordinate_add,transverseCoordinate_smul,stem_transverse_zero,smul_zero,add_zero]
  exact (transverseCoordinate_norm_le _ _).trans ht

/-- Crossing-point removal produces actual distance from the entire stem axis.
The scalar hypothesis compares the genuine tube thickness with radius times
projective angle; no far-from-axis conclusion is supplied as input. -/
theorem crossing_ball_escape {k : ℕ} (stem T : UnitTube (k+1)) {δ theta r : ℝ}
    (hδ : 0 < δ) (htheta : 0 < theta)
    (hangle : theta ≤ projectiveDistance stem.direction T.direction)
    (hscale : 20*δ ≤ r*theta) {p x : Space (k+1)}
    (hpstem : p ∈ stem.carrier δ) (hpT : p ∈ T.carrier δ)
    (hx : x ∈ T.carrier δ) (hfar : r ≤ dist x p) :
    r*theta/4 ≤ ‖transverseCoordinate (alignStem stem.direction) (x-stem.base)‖ := by
  let f := alignStem stem.direction
  obtain ⟨t₀,_,ht₀⟩ := hpT
  obtain ⟨t,_,ht⟩ := hx
  have herror : ‖(x-p)-(t-t₀) • T.direction‖ ≤ 2*δ := by
    have hid : (x-p)-(t-t₀) • T.direction = (x-T.axisPoint t)-(p-T.axisPoint t₀) := by
      dsimp [UnitTube.axisPoint]
      module
    rw [hid]
    exact (norm_sub_le _ _).trans (by
      linarith [show ‖x-T.axisPoint t‖ ≤ δ from ht,show ‖p-T.axisPoint t₀‖ ≤ δ from ht₀])
  have hpara : r ≤ |t-t₀|+2*δ := by
    have h₁ := dist_triangle x (T.axisPoint t) p
    have h₂ := dist_triangle (T.axisPoint t) (T.axisPoint t₀) p
    rw [T.axisPoint_distance,dist_comm (T.axisPoint t₀) p] at h₂
    linarith
  have he := (transverseCoordinate_norm_le f _).trans herror
  have hid : (x-p)-(t-t₀) • T.direction =
      ((x-stem.base)-(p-stem.base))-(t-t₀) • T.direction := by abel
  rw [hid,transverseCoordinate_sub,transverseCoordinate_sub,transverseCoordinate_smul] at he
  have hn := norm_sub_le
    (transverseCoordinate f (x-stem.base)-transverseCoordinate f (p-stem.base))
    ((transverseCoordinate f (x-stem.base)-transverseCoordinate f (p-stem.base))-
      (t-t₀) • transverseCoordinate f T.direction)
  rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs] at hn
  have hn₂ := norm_sub_le (transverseCoordinate f (x-stem.base)) (transverseCoordinate f (p-stem.base))
  have hp := stem_carrier_transverse stem hpstem
  have httrans : theta/2 ≤ ‖transverseCoordinate f T.direction‖ :=
    (div_le_div_of_nonneg_right hangle (by norm_num)).trans (stem_transverse_lower stem T)
  have hm₁ := mul_le_mul_of_nonneg_left httrans (abs_nonneg (t-t₀))
  have hm₂ := mul_le_mul_of_nonneg_right hpara (by positivity : 0 ≤ theta/2)
  have ht₂ := hangle.trans (unit_projective_le_two _ _ stem.unit_direction T.unit_direction)
  have hm₃ := mul_le_mul_of_nonneg_left ht₂ hδ.le
  change r*theta/4 ≤ ‖transverseCoordinate f (x-stem.base)‖
  change ‖transverseCoordinate f (p-stem.base)‖ ≤ δ at hp
  nlinarith

/-- Remove the actual closed crossing ball. -/
def outsideCrossing {k : ℕ} (Y : Set (Space k)) (p : Space k) (r : ℝ) : Set (Space k) :=
  Y \ Metric.closedBall p r

/-- A genuine measured ball concentration bound preserves at least half of the
original shading mass after crossing-ball removal. -/
theorem outsideCrossing_half_mass {k : ℕ} (Y : Set (Space k)) (p : Space k) (r : ℝ)
    (hfin : (volume : Measure (Space k)) Y ≠ ∞)
    (hball : (volume : Measure (Space k)).real (Y ∩ Metric.closedBall p r) ≤
      (volume : Measure (Space k)).real Y/2) :
    (volume : Measure (Space k)).real Y/2 ≤
      (volume : Measure (Space k)).real (outsideCrossing Y p r) := by
  have h := measureReal_sdiff_add_inter (μ := (volume : Measure (Space k)))
    (s := Y) (t := Metric.closedBall p r) (Metric.isClosed_closedBall.measurableSet) hfin
  change (volume : Measure (Space k)).real Y/2 ≤
    (volume : Measure (Space k)).real (Y \ Metric.closedBall p r)
  linarith

/-- The explicit constant from the factor-two retained mass and factor-four
transverse escape distance. -/
def removalConstant (k : ℕ) : ℝ := (4:ℝ)^(k+1)*hairbrushConstant k 5

theorem removalConstant_pos (k : ℕ) : 0 < removalConstant k := by
  have h := hairbrushConstant_pos k (by norm_num : (0:ℝ) ≤ 5)
  unfold removalConstant
  positivity

/-- Actual crossing-ball removal and finite plane geometry prove the hairbrush
union bound. Neither bounded location nor distance from the stem is assumed;
both are derived from actual unit-tube geometry. -/
theorem crossing_hairbrush_union_lower {ι : Type*} [Fintype ι] {k : ℕ}
    (stem : UnitTube (k+2)) (bristle : ι → UnitTube (k+2))
    (Y : ι → Set (Space (k+2))) (crossing : ι → Space (k+2))
    {δ theta r lam L : ℝ} (hδ : 0 < δ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hscale : 88*δ ≤ r*theta)
    (hlam : 0 ≤ lam) (hL : 0 < L) (hlogL : Real.logb 2 (2/δ)+2 ≤ L)
    (hangle : ∀ i, theta ≤ projectiveDistance stem.direction (bristle i).direction)
    (hcross : ∀ i, crossing i ∈ stem.carrier δ ∩ (bristle i).carrier δ)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (bristle i).direction (bristle j).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hmass : ∀ i, lam*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hball : ∀ i, (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall (crossing i) r) ≤
      (volume : Measure (Space (k+2))).real (Y i)/2) :
    (Fintype.card ι:ℝ)*lam^2*δ^(k+1)*(r*theta)^k/(removalConstant k*L^3) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  let Z := fun i => outsideCrossing (Y i) (crossing i) r
  have hrt : r*theta ≤ 1 := (mul_le_mul_of_nonneg_left htheta1 hr.le).trans (by simpa using hr1)
  have hδsmall : δ ≤ 1/2 := by linarith
  have hZsub (i : ι) : Z i ⊆ (bristle i).carrier δ := fun _ hx => hsub i hx.1
  have hfin (i : ι) : (volume : Measure (Space (k+2))) (Y i) ≠ ∞ :=
    measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite (bristle i) δ)
  have hZmass (i : ι) : (lam/2)*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real (Z i) := by
    have h := outsideCrossing_half_mass (Y i) (crossing i) r (hfin i) (hball i)
    change (lam/2)*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real (outsideCrossing (Y i) (crossing i) r)
    have hm := div_le_div_of_nonneg_right (hmass i) (by norm_num : (0:ℝ) ≤ 2)
    calc
      _ = (lam*δ^(k+1)/L)/2 := by ring
      _ ≤ _ := hm.trans h
  have h := far_hairbrush_union_lower stem bristle Z hδ hδsmall (by norm_num : (0:ℝ) ≤ 5)
    (by positivity : 0 < r*theta/4) (by linarith : r*theta/4 ≤ 1)
    (by linarith : 2*((6+5)*δ) ≤ r*theta/4) (by positivity : 0 ≤ lam/2) hL hlogL
    (fun i => htheta.trans_le (hangle i)) (fun i => ⟨crossing i,hcross i⟩) hdir
    (fun i => (hY i).diff Metric.isClosed_closedBall.measurableSet) hZsub
    (fun i _ hx => bristle_stem_base_bound stem (bristle i) (by linarith) ⟨crossing i,hcross i⟩ (hZsub i hx))
    (fun i x hx => crossing_ball_escape stem (bristle i) hδ htheta (hangle i)
      (by linarith) (hcross i).1 (hcross i).2 (hZsub i hx)
      (le_of_lt (lt_of_not_ge hx.2))) hZmass
  have hid : (Fintype.card ι:ℝ)*(lam/2)^2*δ^(k+1)*(r*theta/4)^k/(hairbrushConstant k 5*L^3) =
      (Fintype.card ι:ℝ)*lam^2*δ^(k+1)*(r*theta)^k/(removalConstant k*L^3) := by
    unfold removalConstant
    simp only [div_pow,pow_succ]
    field_simp
    ring
  rw [hid] at h
  apply h.trans
  refine measureReal_mono (Set.iUnion_mono (fun i => Set.sdiff_subset)) ?_
  simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ := (volume : Measure (Space (k+2))))
    (s := Set.univ) (f := Y) (Set.toFinite _) (fun i _ => hfin i)

/-- The full two-ends tests at the actual tube scale imply the crossing-ball
concentration premise used above. The chosen radius is independent of density. -/
theorem two_ends_crossing_hairbrush {ι : Type*} [Fintype ι] {k : ℕ}
    (stem : UnitTube (k+2)) (bristle : ι → UnitTube (k+2))
    (Y : ι → Set (Space (k+2))) (crossing : ι → Space (k+2))
    {δ theta r lam L B alpha : ℝ} (hδ : 0 < δ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hscale : 88*δ ≤ r*theta)
    (hlam : 0 ≤ lam) (hL : 0 < L) (hlogL : Real.logb 2 (2/δ)+2 ≤ L)
    (hangle : ∀ i, theta ≤ projectiveDistance stem.direction (bristle i).direction)
    (hcross : ∀ i, crossing i ∈ stem.carrier δ ∩ (bristle i).carrier δ)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (bristle i).direction (bristle j).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hmass : ∀ i, lam*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hsmall : B*r^alpha ≤ 1/2) :
    (Fintype.card ι:ℝ)*lam^2*δ^(k+1)*(r*theta)^k/(removalConstant k*L^3) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  have hδr : δ ≤ r := by nlinarith [mul_le_mul_of_nonneg_left htheta1 hr.le]
  apply crossing_hairbrush_union_lower stem bristle Y crossing hδ htheta htheta1 hr hr1 hscale
    hlam hL hlogL hangle hcross hdir hY hsub hmass
  intro i
  have h := hends i (crossing i) r hδr hr1
  have hm := mul_le_mul_of_nonneg_right hsmall
    (measureReal_nonneg : 0 ≤ (volume : Measure (Space (k+2))).real (Y i))
  exact h.trans (by linarith)

end
end KakeyaFormal.HairbrushRemoval

#print axioms KakeyaFormal.HairbrushRemoval.two_ends_crossing_hairbrush
