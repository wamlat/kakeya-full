import Coarsening

/-! Concrete dyadic heavy-cell deletion implies actual all-center spatial ball
bounds. Integer-grid geometry supplies the covering; no shifted-grid oracle or
assumed ball-cover cardinality appears. -/
namespace KakeyaFormal.BallPruning
open Coarsening KakeyaFormal.Localization GridGeometry
open scoped BigOperators
noncomputable section
open Classical

def ballCells {k : ℕ} (E : Finset (Cell k)) (δ : ℝ) (x : Space k) (rho : ℝ) : Finset (Cell k) :=
  E.filter (fun q => dist (cellCenter δ q) x ≤ rho)

def coverConstant (k : ℕ) (R : ℝ) : ℝ := (5:ℝ)^k*(1+R+(k:ℝ)/2)^k

lemma coverConstant_nonneg (k : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ coverConstant k R := by
  dsimp [coverConstant]
  positivity

/-- The coarse centers meeting an actual ball lie in a concrete slightly larger
ball and hence obey the already proved integer-grid packing bound. -/
theorem ball_coarse_cover_count {k : ℕ} (E : Finset (Cell k)) (x : Space k)
    {δ r rho R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hrho : rho ≤ R*r) :
    (((ballCells E δ x rho).image (coarseLabel δ r)).card:ℝ) ≤ coverConstant k R := by
  unfold coverConstant
  rw [add_assoc]
  apply GridGeometry.ball_grid_count_real hr
    (show 0 ≤ R+(k:ℝ)/2 by positivity) x
  intro z hz
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  have hqball := (Finset.mem_filter.mp hq).2
  have hc := coarse_center_distance (δ := δ) hr q
  have ht := dist_triangle (cellCenter r (coarseLabel δ r q)) (cellCenter δ q) x
  rw [dist_comm (cellCenter r (coarseLabel δ r q)) (cellCenter δ q)] at ht
  nlinarith

/-- Uniform actual coarse-cell fiber bounds imply a bound for every fine ball. -/
theorem ball_count_from_fibers {k : ℕ} (E : Finset (Cell k)) (x : Space k)
    {δ r rho R B : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hrho : rho ≤ R*r) (hB : 0 ≤ B)
    (hfiber : ∀ z, (((E.filter (fun q => coarseLabel δ r q = z)).card):ℝ) ≤ B) :
    ((ballCells E δ x rho).card:ℝ) ≤ coverConstant k R*B := by
  let S := ballCells E δ x rho
  have hsum : (S.card:ℝ) = ∑ z ∈ S.image (coarseLabel δ r),
      (((S.filter (fun q => coarseLabel δ r q = z)).card):ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image (coarseLabel δ r))
      (g := coarseLabel δ r) (fun q hq => Finset.mem_image.mpr ⟨q,hq,rfl⟩) (fun _ => (1:ℝ))
    simpa using hh.symm
  have hcount : (S.card:ℝ) ≤ ((S.image (coarseLabel δ r)).card:ℝ)*B := by
    rw [hsum]
    have hh := Finset.sum_le_sum (s := S.image (coarseLabel δ r)) (fun z _ =>
      (show (((S.filter (fun q => coarseLabel δ r q = z)).card):ℝ) ≤
          (((E.filter (fun q => coarseLabel δ r q = z)).card):ℝ) by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.filter_subset _ _ : S ⊆ E))).trans (hfiber z))
    simpa only [Finset.sum_const,nsmul_eq_mul] using hh
  exact hcount.trans (mul_le_mul_of_nonneg_right (ball_coarse_cover_count E x hr hR hrho) hB)

/-- One finite list of nonheavy scales controls every physical radius δ≤rho≤1. -/
theorem dyadic_ball_bound {k J : ℕ} (E : Finset (Cell k))
    {δ F d : ℝ} (hδ : 0 < δ)
    (hbottom2 : radius J 0 ≤ 2*δ) (hF : 0 ≤ F) (hd : 0 ≤ d)
    (hfiber : ∀ j ≤ J, ∀ z,
      (((E.filter (fun q => coarseLabel δ (radius J j) q = z)).card):ℝ) ≤
        F*(radius J j/δ)^d) (x : Space k) {rho : ℝ} (hrho : δ ≤ rho) (hrho1 : rho ≤ 1) :
    ((ballCells E δ x rho).card:ℝ) ≤ (coverConstant k 1*(2:ℝ)^d*F)*(rho/δ)^d := by
  have hex : ∃ j ≤ J, rho ≤ radius J j ∧ radius J j ≤ 2*rho := by
    by_cases hb : radius J 0 ≤ rho
    · exact dyadic_round hb hrho1
    · exact ⟨0,Nat.zero_le J,(le_of_not_ge hb),hbottom2.trans (by linarith)⟩
  obtain ⟨j,hj,hlo,hhi⟩ := hex
  have hr : 0 < radius J j := radius_pos J j
  have hscale : 0 ≤ radius J j/δ := div_nonneg hr.le hδ.le
  have hbound := ball_count_from_fibers E x hr (show (0:ℝ) ≤ 1 by norm_num)
    (by simpa using hlo) (mul_nonneg hF (Real.rpow_nonneg hscale d)) (hfiber j hj)
  have hp := Real.rpow_le_rpow hscale (div_le_div_of_nonneg_right hhi hδ.le) hd
  have hid : (2*rho/δ)^d = (2:ℝ)^d*(rho/δ)^d := by
    rw [mul_div_assoc,Real.mul_rpow (by norm_num) (div_nonneg (hδ.le.trans hrho) hδ.le)]
  rw [hid] at hp
  have hc := coverConstant_nonneg k (show (0:ℝ) ≤ 1 by norm_num)
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hF) hc
  exact hbound.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hm)

/-- The survivor set is constructed by removing every cell lying in any heavy
coarse cell at any of the finitely many selected scales. -/
def survivors {k : ℕ} (E : Finset (Cell k)) (δ F d : ℝ) (J : ℕ) : Finset (Cell k) :=
  E.filter (fun q => ∀ j ≤ J,
    (((E.filter (fun p => coarseLabel δ (radius J j) p = coarseLabel δ (radius J j) q)).card):ℝ) ≤
      F*(radius J j/δ)^d)

lemma survivors_subset {k : ℕ} (E : Finset (Cell k)) (δ F d : ℝ) (J : ℕ) :
    survivors E δ F d J ⊆ E := Finset.filter_subset _ _

/-- Actual surviving fibers obey the nonheavy capacity, including empty fibers. -/
theorem survivors_fiber_bound {k J : ℕ} (E : Finset (Cell k))
    {δ F d : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (j : ℕ) (hj : j ≤ J) (z : Cell k) :
    ((((survivors E δ F d J).filter (fun q => coarseLabel δ (radius J j) q = z)).card):ℝ) ≤
      F*(radius J j/δ)^d := by
  let S := (survivors E δ F d J).filter (fun q => coarseLabel δ (radius J j) q = z)
  by_cases hne : S.Nonempty
  · obtain ⟨q,hq⟩ := hne
    have hsurv := (Finset.mem_filter.mp hq).1
    have hlabel := (Finset.mem_filter.mp hq).2
    have hh := (Finset.mem_filter.mp hsurv).2 j hj
    rw [hlabel] at hh
    have hsub : S ⊆ E.filter (fun q => coarseLabel δ (radius J j) q = z) :=
      Finset.filter_subset_filter _ (survivors_subset E δ F d J)
    exact (show (S.card:ℝ) ≤ ((E.filter (fun q => coarseLabel δ (radius J j) q = z)).card:ℝ) by
      exact_mod_cast Finset.card_le_card hsub).trans hh
  · change (S.card:ℝ) ≤ _
    rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    have hr := radius_pos J j
    positivity

/-- Concrete heavy-cell deletion gives a spatial cap bound with a logarithmic
number of tested scales, uniformly over all actual ball centers and radii. -/
theorem construct_spatial_pruning {k : ℕ} (E : Finset (Cell k))
    {δ F d : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hF : 0 ≤ F) (hd : 0 ≤ d) :
    ∃ J : ℕ, (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      survivors E δ F d J ⊆ E ∧
      ∀ x : Space k, ∀ rho : ℝ, δ ≤ rho → rho ≤ 1 →
        ((ballCells (survivors E δ F d J) δ x rho).card:ℝ) ≤
          (coverConstant k 1*(2:ℝ)^d*F)*(rho/δ)^d := by
  obtain ⟨J,_,hbottom2,hdepth⟩ := ScaleChoice.dyadic_depth hδ hδ1
  exact ⟨J,hdepth,survivors_subset E δ F d J,
    fun x rho hr hr1 => dyadic_ball_bound (survivors E δ F d J) hδ hbottom2.le hF hd
      (fun j hj z => survivors_fiber_bound E hδ hF j hj z) x hr hr1⟩


/-- A fixed bounded-region condition supplies the unit-scale total count, which
extends the pruned ball estimate beyond radius one without a new hypothesis. -/
theorem dyadic_all_ball_bound {k J : ℕ} (E : Finset (Cell k)) (x₀ : Space k)
    {δ F d R : ℝ} (hδ : 0 < δ)
    (hbottom2 : radius J 0 ≤ 2*δ) (hF : 0 ≤ F) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hbounded : ∀ q ∈ E, dist (cellCenter δ q) x₀ ≤ R)
    (hfiber : ∀ j ≤ J, ∀ z,
      (((E.filter (fun q => coarseLabel δ (radius J j) q = z)).card):ℝ) ≤
        F*(radius J j/δ)^d) (x : Space k) {rho : ℝ} (hrho : δ ≤ rho) :
    ((ballCells E δ x rho).card:ℝ) ≤
      (max (coverConstant k 1*(2:ℝ)^d) (coverConstant k R)*F)*(rho/δ)^d := by
  have hrhopos : 0 < rho := hδ.trans_le hrho
  let K := max (coverConstant k 1*(2:ℝ)^d) (coverConstant k R)
  have hCK : coverConstant k R ≤ K := le_max_right _ _
  have hsmallK : coverConstant k 1*(2:ℝ)^d ≤ K := le_max_left _ _
  have hK : 0 ≤ K := (coverConstant_nonneg k hR).trans hCK
  have htotal : (E.card:ℝ) ≤ coverConstant k R*(F*(1/δ)^d) := by
    have hf1 : ∀ z, (((E.filter (fun q => coarseLabel δ 1 q = z)).card):ℝ) ≤ F*(1/δ)^d := by
      simpa only [radius_top] using hfiber J le_rfl
    have hball := ball_count_from_fibers E x₀ (show (0:ℝ) < 1 by norm_num) hR
      (show R ≤ R*1 by simp) (mul_nonneg hF (Real.rpow_nonneg (by positivity) d)) hf1
    have heq : ballCells E δ x₀ R = E := Finset.filter_eq_self.mpr hbounded
    rwa [heq] at hball
  by_cases hr1 : rho ≤ 1
  · have hh := dyadic_ball_bound E hδ hbottom2 hF hd hfiber x hrho hr1
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsmallK hF) (Real.rpow_nonneg (by positivity : 0 ≤ rho/δ) d)
    exact hh.trans hmul
  · have hrlarge : 1 ≤ rho := le_of_not_ge hr1
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1/δ)
      (div_le_div_of_nonneg_right hrlarge hδ.le) hd
    have hsub : ((ballCells E δ x rho).card:ℝ) ≤ (E.card:ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    have hcoef := mul_le_mul_of_nonneg_right hCK hF
    have hscale := mul_le_mul_of_nonneg_left hp (mul_nonneg hK hF)
    calc
      _ ≤ (E.card:ℝ) := hsub
      _ ≤ coverConstant k R*(F*(1/δ)^d) := htotal
      _ = (coverConstant k R*F)*(1/δ)^d := by ring
      _ ≤ (K*F)*(1/δ)^d := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by positivity) d)
      _ ≤ _ := hscale

/-- The actual survivor set satisfies the all-radii input required by the
lifted graph cap theorem, with constants depending only on the fixed region. -/
theorem construct_all_scale_pruning {k : ℕ} (E : Finset (Cell k)) (x₀ : Space k)
    {δ F d R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hF : 0 ≤ F) (hd : 0 ≤ d) (hR : 0 ≤ R)
    (hbounded : ∀ q ∈ E, dist (cellCenter δ q) x₀ ≤ R) :
    ∃ J : ℕ, (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      survivors E δ F d J ⊆ E ∧
      ∀ x : Space k, ∀ rho : ℝ, δ ≤ rho →
        ((ballCells (survivors E δ F d J) δ x rho).card:ℝ) ≤
          (max (coverConstant k 1*(2:ℝ)^d) (coverConstant k R)*F)*(rho/δ)^d := by
  obtain ⟨J,_,hbottom2,hdepth⟩ := ScaleChoice.dyadic_depth hδ hδ1
  exact ⟨J,hdepth,survivors_subset E δ F d J,
    fun x rho hr => dyadic_all_ball_bound (survivors E δ F d J) x₀ hδ hbottom2.le hF hd hR
      (fun q hq => hbounded q (survivors_subset E δ F d J hq))
      (fun j hj z => survivors_fiber_bound E hδ hF j hj z) x hr⟩

end
end KakeyaFormal.BallPruning
