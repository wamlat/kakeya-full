import Configurations

/-! Exact spatial dilation and grid reindexing for localized tube configurations.
The rescaled tube has an actual unit direction; finite sets and cap coefficients
are transformed explicitly. Selection of a coarse separated subfamily is separate. -/
namespace KakeyaFormal.Rescaling

noncomputable def rescale {k : ℕ} (rho : ℝ) (origin x : Space k) : Space k :=
  rho⁻¹ • (x-origin)

def shiftLabel {k : ℕ} (origin z : Cell k) : Cell k := fun i => z i-origin i

theorem shiftLabel_injective {k : ℕ} (origin : Cell k) :
    Function.Injective (shiftLabel origin) := by
  intro z w h
  funext i
  have hi := congrFun h i
  dsimp [shiftLabel] at hi
  omega

theorem rescale_distance {k : ℕ} {rho : ℝ} (hrho : 0 < rho)
    (origin x y : Space k) :
    dist (rescale rho origin x) (rescale rho origin y) = dist x y / rho := by
  unfold rescale
  rw [dist_smul₀,dist_sub_right,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hrho)]
  ring

theorem rescale_grid {k : ℕ} (rho δ : ℝ) (origin z : Cell k) :
    rescale rho (cellCenter δ origin) (cellCenter δ z) =
      cellCenter (δ/rho) (shiftLabel origin z) := by
  apply WithLp.ofLp_injective
  funext i
  change rho⁻¹*(δ*(z i:ℝ)-δ*(origin i:ℝ)) = (δ/rho)*((z i-origin i:ℤ):ℝ)
  push_cast
  ring

noncomputable def tube {k : ℕ} (T : UnitTube k) (rho : ℝ)
    (origin : Space k) (a : ℝ) : UnitTube k where
  base := rescale rho origin (T.axisPoint a)
  direction := T.direction
  unit_direction := T.unit_direction

theorem rescale_axisPoint {k : ℕ} (T : UnitTube k) {rho : ℝ}
    (hrho : rho ≠ 0) (origin : Space k) (a t : ℝ) :
    rescale rho origin (T.axisPoint (a+rho*t)) = (tube T rho origin a).axisPoint t := by
  have hcoeff : rho⁻¹*(rho*t) = t := by field_simp
  dsimp [rescale,tube,UnitTube.axisPoint]
  rw [add_smul]
  calc
    _ = rho⁻¹ • (T.base+a•T.direction-origin) + (rho⁻¹*(rho*t)) • T.direction := by module
    _ = _ := by rw [hcoeff]

theorem localized_parameter {rho a t : ℝ} (hrho : 0 < rho)
    (ht : t ∈ Set.Icc a (a+rho)) : (t-a)/rho ∈ Set.Icc (0:ℝ) 1 := by
  exact ⟨div_nonneg (sub_nonneg.mpr ht.1) hrho.le,
    (div_le_one hrho).mpr (by linarith [ht.2])⟩

noncomputable def family {k M : ℕ} (F : TubeFamily k M) (rho δ : ℝ)
    (origin : Cell k) (a : Fin M → ℝ) : TubeFamily k M where
  tube i := tube (F.tube i) rho (cellCenter δ origin) (a i)
  shade i := (F.shade i).image (shiftLabel origin)

theorem rescaled_card {k M : ℕ} (F : TubeFamily k M) (rho δ : ℝ)
    (origin : Cell k) (a : Fin M → ℝ) (i : Fin M) :
    ((family F rho δ origin a).shade i).card = (F.shade i).card := by
  classical
  exact Finset.card_image_of_injective _ (shiftLabel_injective origin)

theorem rescaled_union {k M : ℕ} (F : TubeFamily k M) (rho δ : ℝ)
    (origin : Cell k) (a : Fin M → ℝ) :
    (family F rho δ origin a).unionCells = F.unionCells.image (shiftLabel origin) := by
  classical
  simp only [TubeFamily.unionCells,family,Finset.biUnion_image]

theorem rescaled_union_card {k M : ℕ} (F : TubeFamily k M) (rho δ : ℝ)
    (origin : Cell k) (a : Fin M → ℝ) :
    (family F rho δ origin a).unionCells.card = F.unionCells.card := by
  rw [rescaled_union]
  exact Finset.card_image_of_injective _ (shiftLabel_injective origin)

/-- Admissibility follows from an actual parameter interval of the localized tube. -/
theorem rescaled_admissible {k M : ℕ} (F : TubeFamily k M)
    {rho δ width : ℝ} (hrho : 0 < rho) (origin : Cell k) (a : Fin M → ℝ)
    (hlocal : ∀ i z, z ∈ F.shade i → ∃ t ∈ Set.Icc (a i) (a i+rho),
      dist (cellCenter δ z) ((F.tube i).axisPoint t) ≤ width*δ) :
    (family F rho δ origin a).Admissible width (δ/rho) := by
  classical
  intro i z hz
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨t,ht,hdist⟩ := hlocal i w hw
  refine ⟨(t-a i)/rho,localized_parameter hrho ht,?_⟩
  have heq : a i+rho*((t-a i)/rho) = t := by field_simp; ring
  have haxis := rescale_axisPoint (F.tube i) hrho.ne' (cellCenter δ origin) (a i) ((t-a i)/rho)
  rw [heq] at haxis
  change dist (cellCenter (δ/rho) (shiftLabel origin w))
    ((tube (F.tube i) rho (cellCenter δ origin) (a i)).axisPoint ((t-a i)/rho)) ≤ width*(δ/rho)
  rw [← rescale_grid,← haxis,rescale_distance hrho]
  have h := div_le_div_of_nonneg_right hdist hrho.le
  simpa only [mul_div_assoc] using h

/-- Exact relative-density transformation, before optional density clamping. -/
theorem rescaled_comparable {k M : ℕ} (F : TubeFamily k M)
    {rho δ lam : ℝ} (hrho : rho ≠ 0) (origin : Cell k) (a : Fin M → ℝ)
    (h : F.Comparable δ lam) :
    (family F rho δ origin a).Comparable (δ/rho) (lam/rho) := by
  intro i
  rw [rescaled_card]
  have hlo : (lam/rho)/(δ/rho) = lam/δ := by field_simp
  have hhi : 2*(lam/rho)/(δ/rho) = 2*lam/δ := by field_simp
  rw [hlo,hhi]
  exact h i

/-- Direction separation itself is unchanged by spatial dilation. -/
theorem rescaled_separated {k M : ℕ} (F : TubeFamily k M)
    {rho δ sep : ℝ} (origin : Cell k) (a : Fin M → ℝ)
    (h : F.Separated sep) : (family F rho δ origin a).Separated sep := h

/-- The exact cap-coefficient cost before any coarse-direction thinning. -/
theorem rescaled_cap_bound {k M : ℕ} (F : TubeFamily k M)
    {rho δ m A : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) (hδ : 0 < δ)
    (origin : Cell k) (a : Fin M → ℝ) (hcap : F.CapBound δ m A) :
    (family F rho δ origin a).CapBound (δ/rho) m (A*rho^(-m)) := by
  classical
  intro v hv r hr hr1
  have hδnew : δ ≤ δ/rho := (le_div_iff₀ hrho).mpr
    (by nlinarith [mul_le_mul_of_nonneg_left hrho1 hδ.le])
  have hold := hcap v hv r (hδnew.trans hr) hr1
  change ((Finset.univ.filter fun i => projectiveDistance (F.tube i).direction v ≤ r).card:ℝ) ≤ _
  have hrpos : 0 < r := (div_pos hδ hrho).trans_le hr
  have hid : r/δ = rho⁻¹*(r/(δ/rho)) := by field_simp
  have hp : A*(r/δ)^m = (A*rho^(-m))*(r/(δ/rho))^m := by
    rw [hid,Real.mul_rpow (inv_nonneg.mpr hrho.le)
      (div_nonneg hrpos.le (div_nonneg hδ.le hrho.le)),
      Real.inv_rpow hrho.le,Real.rpow_neg hrho.le]
    ring
  exact hold.trans_eq hp

/-- A bounded localized axis base remains uniformly bounded after dilation. -/
theorem rescaled_bounded {k M : ℕ} (F : TubeFamily k M)
    {rho δ R : ℝ} (hrho : 0 < rho) (origin : Cell k) (a : Fin M → ℝ)
    (hbase : ∀ i, dist ((F.tube i).axisPoint (a i)) (cellCenter δ origin) ≤ rho*R) :
    (family F rho δ origin a).Bounded R := by
  intro i
  have hdist := rescale_distance hrho (cellCenter δ origin)
    ((F.tube i).axisPoint (a i)) (cellCenter δ origin)
  simp only [rescale,sub_self,smul_zero,dist_zero_right] at hdist
  change ‖rescale rho (cellCenter δ origin) ((F.tube i).axisPoint (a i))‖ ≤ R
  rw [rescale,hdist]
  exact (div_le_iff₀ hrho).mpr (by simpa only [mul_comm] using hbase i)

end KakeyaFormal.Rescaling
