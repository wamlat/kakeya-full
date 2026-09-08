import Rescaling
import CommonDensityLocalization
import TubeIntersection

/-! Exact measurable spatial rescaling and the physical parameter intervals of
localized tube shadings. One origin is shared throughout a family, so union
measure is transformed by a single affine bijection. -/
namespace KakeyaFormal.MeasurableRescaling
open MeasureTheory Set Rescaling
open scoped BigOperators ENNReal
noncomputable section

/-- Inverse of the common translation and positive spatial dilation. -/
def inverse {k : ℕ} (rho : ℝ) (origin x : Space k) : Space k := rho • x + origin

theorem inverse_rescale {k : ℕ} {rho : ℝ} (hrho : rho ≠ 0) (origin x : Space k) :
    inverse rho origin (rescale rho origin x) = x := by
  simp only [inverse,rescale,smul_smul,mul_inv_cancel₀ hrho,one_smul,sub_add_cancel]

theorem rescale_inverse {k : ℕ} {rho : ℝ} (hrho : rho ≠ 0) (origin x : Space k) :
    rescale rho origin (inverse rho origin x) = x := by
  simp only [inverse,rescale,add_sub_cancel_right,smul_smul,inv_mul_cancel₀ hrho,one_smul]

theorem rescale_injective {k : ℕ} {rho : ℝ} (hrho : rho ≠ 0) (origin : Space k) :
    Function.Injective (rescale rho origin) :=
  Function.LeftInverse.injective (inverse_rescale hrho origin)

/-- Images of measurable sets are measurable because the dilation is a genuine
continuous bijection, with the explicit continuous inverse above. -/
theorem image_eq_preimage {k : ℕ} {rho : ℝ} (hrho : rho ≠ 0)
    (origin : Space k) (Y : Set (Space k)) :
    rescale rho origin '' Y = inverse rho origin ⁻¹' Y := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    simpa only [Set.mem_preimage,inverse_rescale hrho] using hy
  · intro hx
    exact ⟨inverse rho origin x,hx,rescale_inverse hrho origin x⟩

theorem image_measurable {k : ℕ} {rho : ℝ} (hrho : rho ≠ 0)
    (origin : Space k) {Y : Set (Space k)} (hY : MeasurableSet Y) :
    MeasurableSet (rescale rho origin '' Y) := by
  rw [image_eq_preimage hrho]
  exact hY.preimage (show Measurable (inverse rho origin) from (by unfold inverse; fun_prop : Continuous (inverse rho origin)).measurable)

/-- Exact Lebesgue volume scaling, including all finite-union applications. -/
theorem image_volume {k : ℕ} {rho : ℝ} (hrho : 0 < rho)
    (origin : Space k) (Y : Set (Space k)) :
    (volume : Measure (Space k)).real (rescale rho origin '' Y) =
      (volume : Measure (Space k)).real Y / rho^k := by
  have hmeasure : (volume : Measure (Space k)) (rescale rho origin '' Y) =
      ENNReal.ofReal ((rho^k)⁻¹) * (volume : Measure (Space k)) Y := by
    rw [image_eq_preimage hrho.ne']
    change (volume : Measure (Space k)) ((fun x : Space k => rho • x) ⁻¹' ((fun x => x+origin) ⁻¹' Y)) = _
    rw [Measure.addHaar_preimage_smul volume hrho.ne',measure_preimage_add_right]
    simp only [finrank_euclideanSpace,Fintype.card_fin,abs_of_pos (inv_pos.mpr (pow_pos hrho k))]
  have h := congrArg ENNReal.toReal hmeasure
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos hrho k).le),div_eq_mul_inv,mul_comm] using h

theorem image_finite {k : ℕ} {rho : ℝ} (hrho : 0 < rho)
    (origin : Space k) {Y : Set (Space k)} (hY : (volume : Measure (Space k)) Y ≠ ∞) :
    (volume : Measure (Space k)) (rescale rho origin '' Y) ≠ ∞ := by
  rw [image_eq_preimage hrho.ne']
  change (volume : Measure (Space k)) ((fun x : Space k => rho • x) ⁻¹' ((fun x => x+origin) ⁻¹' Y)) ≠ ∞
  rw [Measure.addHaar_preimage_smul volume hrho.ne',measure_preimage_add_right]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY

/-- Ball tests transform exactly under the same affine bijection. -/
theorem image_inter_ball {k : ℕ} {rho : ℝ} (hrho : 0 < rho)
    (origin y : Space k) (Y : Set (Space k)) (r : ℝ) :
    rescale rho origin '' (Y ∩ Metric.closedBall (inverse rho origin y) (rho*r)) =
      (rescale rho origin '' Y) ∩ Metric.closedBall y r := by
  have hdist (x : Space k) : dist (rescale rho origin x) y = dist x (inverse rho origin y)/rho := by
    conv_lhs => rw [← rescale_inverse hrho.ne' origin y]
    exact rescale_distance hrho origin x (inverse rho origin y)
  ext z
  constructor
  · rintro ⟨x,⟨hx,hball⟩,rfl⟩
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    change dist (rescale rho origin x) y ≤ r
    rw [hdist]
    change dist x (inverse rho origin y) ≤ rho*r at hball
    exact (div_le_iff₀ hrho).mpr (by simpa only [mul_comm] using hball)
  · rintro ⟨⟨x,hx,rfl⟩,hball⟩
    refine ⟨x,⟨hx,?_⟩,rfl⟩
    change dist x (inverse rho origin y) ≤ rho*r
    change dist (rescale rho origin x) y ≤ r at hball
    rw [hdist] at hball
    simpa only [mul_comm] using (div_le_iff₀ hrho).mp hball

/-- All measurable two-ends ball tests transport to the correctly rescaled
interval, preserving the original relative-radius constant exactly. -/
theorem rescaled_two_ends {k : ℕ} {δ rho L alpha : ℝ} (hL : 0 < L)
    (origin : Space k) (Y : Set (Space k))
    (hends : ∀ y : Space k, ∀ r : ℝ, δ ≤ r → r ≤ rho →
      (volume : Measure (Space k)).real (Y ∩ Metric.closedBall y r) ≤
        (4:ℝ)^alpha*(r/rho)^alpha*(volume : Measure (Space k)).real Y) :
    ∀ y : Space k, ∀ r : ℝ, δ/L ≤ r → r ≤ rho/L →
      (volume : Measure (Space k)).real ((rescale L origin '' Y) ∩ Metric.closedBall y r) ≤
        (4:ℝ)^alpha*(r/(rho/L))^alpha*(volume : Measure (Space k)).real (rescale L origin '' Y) := by
  intro y r hrδ hrρ
  have hlo : δ ≤ L*r := by simpa only [mul_comm] using (div_le_iff₀ hL).mp hrδ
  have hhi : L*r ≤ rho := by simpa only [mul_comm] using (le_div_iff₀ hL).mp hrρ
  have hh := div_le_div_of_nonneg_right (hends (inverse L origin y) (L*r) hlo hhi) (pow_pos hL k).le
  rw [← image_inter_ball hL,image_volume hL,image_volume hL]
  have hratio : (L*r)/rho = r/(rho/L) := by field_simp
  rw [hratio] at hh
  simpa only [mul_div_assoc] using hh

/-- With the physical interval dilation 8rho, all rescaled tests up to unit
radius obey two ends with the fixed constant 32^alpha. -/
theorem unit_two_ends {k : ℕ} {δ rho alpha : ℝ} (hδ : 0 < δ) (hδrho : δ ≤ rho)
    (ha : 0 ≤ alpha) (origin : Space k) (Y : Set (Space k))
    (hfinite : (volume : Measure (Space k)) Y ≠ ∞)
    (hends : ∀ y : Space k, ∀ r : ℝ, δ ≤ r → r ≤ rho →
      (volume : Measure (Space k)).real (Y ∩ Metric.closedBall y r) ≤
        (4:ℝ)^alpha*(r/rho)^alpha*(volume : Measure (Space k)).real Y) :
    ∀ y : Space k, ∀ r : ℝ, δ/(8*rho) ≤ r → r ≤ 1 →
      (volume : Measure (Space k)).real ((rescale (8*rho) origin '' Y) ∩ Metric.closedBall y r) ≤
        (32:ℝ)^alpha*r^alpha*(volume : Measure (Space k)).real (rescale (8*rho) origin '' Y) := by
  have hrho : 0 < rho := hδ.trans_le hδrho
  have hL : 0 < 8*rho := by positivity
  intro y r hrδ hr1
  have hr : 0 < r := (div_pos hδ hL).trans_le hrδ
  by_cases hsmall : r ≤ rho/(8*rho)
  · have hh := rescaled_two_ends hL origin Y hends y r hrδ hsmall
    have htop : rho/(8*rho) = 1/8 := by field_simp
    rw [htop] at hh
    have hfactor : (4:ℝ)^alpha*(r/(1/8))^alpha = (32:ℝ)^alpha*r^alpha := by
      rw [← Real.mul_rpow (by norm_num) (by positivity),← Real.mul_rpow (by norm_num) hr.le]
      congr 1
      ring
    rwa [hfactor] at hh
  · have hmono : (volume : Measure (Space k)).real ((rescale (8*rho) origin '' Y) ∩ Metric.closedBall y r) ≤
        (volume : Measure (Space k)).real (rescale (8*rho) origin '' Y) :=
      measureReal_mono Set.inter_subset_left (image_finite hL origin hfinite)
    have htop : rho/(8*rho) = 1/8 := by field_simp
    rw [htop] at hsmall
    have hpow : (1:ℝ) ≤ (32*r)^alpha := Real.one_le_rpow (by linarith) ha
    rw [Real.mul_rpow (by norm_num) hr.le] at hpow
    exact hmono.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hpow (measureReal_nonneg : (0:ℝ)≤(volume : Measure (Space k)).real (rescale (8*rho) origin '' Y)))

/-- A single common spatial transform preserves the union exactly. -/
theorem image_union {k : ℕ} {I : Type*} (rho : ℝ) (origin : Space k) (Y : I → Set (Space k)) :
    (⋃ i, rescale rho origin '' Y i) = rescale rho origin '' (⋃ i, Y i) := by
  exact Set.image_iUnion.symm

/-- The actual union volume uses one common origin; individual unrelated
translations of shadings are deliberately absent from this statement. -/
theorem union_volume {k : ℕ} {I : Type*} {rho : ℝ} (hrho : 0 < rho)
    (origin : Space k) (Y : I → Set (Space k)) :
    (volume : Measure (Space k)).real (⋃ i, rescale rho origin '' Y i) =
      (volume : Measure (Space k)).real (⋃ i, Y i) / rho^k := by
  rw [image_union,image_volume hrho]

/-- A physical tube shading inside a radius-rho ball has all its axis parameters
inside one interval of length 8rho. The interval and its bounded base are produced
from an actual shading point, not supplied as localization hypotheses. -/
theorem localized_parameter_interval {k : ℕ} (T : UnitTube k) {δ rho : ℝ}
    (hδ : 0 < δ) (hδrho : δ ≤ rho) (center : Space k) (Y : Set (Space k))
    (hne : Y.Nonempty) (hYT : Y ⊆ T.carrier δ) (hball : Y ⊆ Metric.closedBall center rho) :
    ∃ a : ℝ, dist (T.axisPoint a) center ≤ 6*rho ∧
      ∀ x ∈ Y, ∃ t ∈ Set.Icc a (a+8*rho), dist x (T.axisPoint t) ≤ δ := by
  obtain ⟨x₀,hx₀⟩ := hne
  obtain ⟨t₀,ht₀,hxt₀⟩ := hYT hx₀
  have hx₀ball : dist x₀ center ≤ rho := hball hx₀
  let a := t₀-4*rho
  have hbase : dist (T.axisPoint a) center ≤ 6*rho := by
    have h1 := dist_triangle (T.axisPoint a) (T.axisPoint t₀) center
    have h2 := dist_triangle (T.axisPoint t₀) x₀ center
    rw [T.axisPoint_distance,dist_comm (T.axisPoint t₀) x₀] at *
    have habs : |a-t₀| = 4*rho := by dsimp [a]; rw [abs_of_nonpos (by linarith)]; ring
    rw [habs] at h1
    linarith
  refine ⟨a,hbase,?_⟩
  intro x hx
  obtain ⟨t,ht,hxt⟩ := hYT hx
  have hxball : dist x center ≤ rho := hball hx
  have h1 := dist_triangle (T.axisPoint t) x (T.axisPoint t₀)
  have h2 := dist_triangle x x₀ (T.axisPoint t₀)
  have h3 := dist_triangle x center x₀
  rw [T.axisPoint_distance,dist_comm (T.axisPoint t) x] at h1
  rw [dist_comm center x₀] at h3
  have hgap : |t-t₀| ≤ 4*rho := by linarith
  obtain ⟨hlo,hhi⟩ := abs_le.mp hgap
  exact ⟨t,⟨by dsimp [a]; linarith,by dsimp [a]; linarith⟩,hxt⟩

/-- The rescaled shading lies in an actual unit tube with the correctly rescaled
thickness, and that tube's new base is bounded relative to the shared origin. -/
theorem localized_tube_image {k : ℕ} (T : UnitTube k) {δ rho R : ℝ}
    (hδ : 0 < δ) (hδrho : δ ≤ rho) (center origin : Space k) (Y : Set (Space k))
    (hne : Y.Nonempty) (hYT : Y ⊆ T.carrier δ) (hball : Y ⊆ Metric.closedBall center rho)
    (hcenter : dist center origin ≤ R*rho) :
    ∃ a : ℝ, ‖(Rescaling.tube T (8*rho) origin a).base‖ ≤ (R+6)/8 ∧
      rescale (8*rho) origin '' Y ⊆ (Rescaling.tube T (8*rho) origin a).carrier (δ/(8*rho)) := by
  have hrho : 0 < rho := hδ.trans_le hδrho
  have hscale : 0 < 8*rho := by positivity
  obtain ⟨a,hbase,hinterval⟩ := localized_parameter_interval T hδ hδrho center Y hne hYT hball
  refine ⟨a,?_,?_⟩
  · have hd := dist_triangle (T.axisPoint a) center origin
    have hpos := rescale_distance hscale origin (T.axisPoint a) origin
    simp only [rescale,sub_self,smul_zero,dist_zero_right] at hpos
    change ‖rescale (8*rho) origin (T.axisPoint a)‖ ≤ (R+6)/8
    rw [rescale,hpos]
    apply (div_le_iff₀ hscale).mpr
    nlinarith
  · rintro z ⟨x,hx,rfl⟩
    obtain ⟨t,ht,hxt⟩ := hinterval x hx
    refine ⟨(t-a)/(8*rho),localized_parameter hscale ht,?_⟩
    have heq : a+(8*rho)*((t-a)/(8*rho)) = t := by field_simp; ring
    have haxis := rescale_axisPoint T hscale.ne' origin a ((t-a)/(8*rho))
    rw [heq] at haxis
    rw [← haxis,rescale_distance hscale]
    exact div_le_div_of_nonneg_right hxt hscale.le

/-- All localized members in one spatial cluster are rescaled with one shared
origin. Unit tubes, comparable mass scaling, union volume, and all unit-radius
two-ends tests are actual consequences of the constructed transformation. -/
theorem shared_origin_family {k : ℕ} {I : Type*} [Fintype I]
    (T : I → UnitTube k) (Y : I → Set (Space k)) {δ rho R alpha : ℝ}
    (hδ : 0 < δ) (hδrho : δ ≤ rho) (ha : 0 ≤ alpha)
    (centers : I → Space k) (origin : Space k)
    (hne : ∀ i, (Y i).Nonempty) (hYT : ∀ i, Y i ⊆ (T i).carrier δ)
    (hball : ∀ i, Y i ⊆ Metric.closedBall (centers i) rho)
    (hcenter : ∀ i, dist (centers i) origin ≤ R*rho)
    (hY : ∀ i, MeasurableSet (Y i))
    (hends : ∀ i, ∀ y : Space k, ∀ r : ℝ, δ ≤ r → r ≤ rho →
      (volume : Measure (Space k)).real (Y i ∩ Metric.closedBall y r) ≤
        (4:ℝ)^alpha*(r/rho)^alpha*(volume : Measure (Space k)).real (Y i)) :
    ∃ a : I → ℝ,
      (∀ i, (Rescaling.tube (T i) (8*rho) origin (a i)).direction = (T i).direction ∧
        ‖(Rescaling.tube (T i) (8*rho) origin (a i)).base‖ ≤ (R+6)/8 ∧
        rescale (8*rho) origin '' Y i ⊆
          (Rescaling.tube (T i) (8*rho) origin (a i)).carrier (δ/(8*rho))) ∧
      (∀ i, MeasurableSet (rescale (8*rho) origin '' Y i)) ∧
      (∀ i, (volume : Measure (Space k)).real (rescale (8*rho) origin '' Y i) =
        (volume : Measure (Space k)).real (Y i)/(8*rho)^k) ∧
      (volume : Measure (Space k)).real (⋃ i, rescale (8*rho) origin '' Y i) =
        (volume : Measure (Space k)).real (⋃ i, Y i)/(8*rho)^k ∧
      (∀ i, ∀ y : Space k, ∀ r : ℝ, δ/(8*rho) ≤ r → r ≤ 1 →
        (volume : Measure (Space k)).real ((rescale (8*rho) origin '' Y i) ∩ Metric.closedBall y r) ≤
          (32:ℝ)^alpha*r^alpha*(volume : Measure (Space k)).real (rescale (8*rho) origin '' Y i)) := by
  have hrho : 0 < rho := hδ.trans_le hδrho
  have hL : 0 < 8*rho := by positivity
  choose a hbase hsub using fun i => localized_tube_image (T i) hδ hδrho (centers i) origin
    (Y i) (hne i) (hYT i) (hball i) (hcenter i)
  refine ⟨a,fun i => ⟨rfl,hbase i,hsub i⟩,fun i => image_measurable hL.ne' origin (hY i),
    fun i => image_volume hL origin (Y i),union_volume hL origin Y,?_⟩
  intro i
  exact unit_two_ends hδ hδrho ha origin (Y i)
    (measure_ne_top_of_subset (hYT i) (TubeVolume.carrier_finite _ _)) (hends i)

/-- The geometric localized mass upper bound follows from the constructed
rescaled unit tube and its actual volume. Thus localized density is O(rho). -/
theorem localized_volume_upper {k : ℕ} (T : UnitTube k) {δ rho : ℝ}
    (hδ : 0 < δ) (hδrho : δ ≤ rho) (center : Space k) (Y : Set (Space k))
    (hYT : Y ⊆ T.carrier δ) (hball : Y ⊆ Metric.closedBall center rho) :
    (volume : Measure (Space k)).real Y ≤
      (24*(2:ℝ)^k*TubeVolume.unitBallVolume k)*rho*δ^k/δ := by
  have hrho : 0 < rho := hδ.trans_le hδrho
  have hL : 0 < 8*rho := by positivity
  by_cases hne : Y.Nonempty
  · obtain ⟨a,hbase,hsub⟩ := localized_tube_image T hδ hδrho center center Y hne hYT hball
      (show dist center center ≤ (0:ℝ)*rho by simp)
    have hnew : 0 < δ/(8*rho) := div_pos hδ hL
    have hnew1 : δ/(8*rho) ≤ 1 := (div_le_one hL).mpr (by linarith)
    have hm := measureReal_mono hsub (TubeVolume.carrier_finite _ _)
    have hv := TubeVolume.carrier_volume_upper (Rescaling.tube T (8*rho) center a) hnew hnew1
    rw [image_volume hL] at hm
    have hh := (div_le_iff₀ (pow_pos hL k)).mp (hm.trans hv)
    have hid : (3*(2:ℝ)^k*TubeVolume.unitBallVolume k)*(δ/(8*rho))^k/(δ/(8*rho))*(8*rho)^k =
        (24*(2:ℝ)^k*TubeVolume.unitBallVolume k)*rho*δ^k/δ := by
      rw [div_pow]
      field_simp
      ring
    exact hh.trans_eq hid
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,measureReal_empty]
    positivity [TubeVolume.unitBallVolume_pos k]

end
end KakeyaFormal.MeasurableRescaling

-- Kernel dependency audit.
#print axioms KakeyaFormal.MeasurableRescaling.inverse_rescale
#print axioms KakeyaFormal.MeasurableRescaling.rescale_inverse
#print axioms KakeyaFormal.MeasurableRescaling.rescale_injective
#print axioms KakeyaFormal.MeasurableRescaling.image_eq_preimage
#print axioms KakeyaFormal.MeasurableRescaling.image_measurable
#print axioms KakeyaFormal.MeasurableRescaling.image_volume
#print axioms KakeyaFormal.MeasurableRescaling.image_finite
#print axioms KakeyaFormal.MeasurableRescaling.image_inter_ball
#print axioms KakeyaFormal.MeasurableRescaling.rescaled_two_ends
#print axioms KakeyaFormal.MeasurableRescaling.unit_two_ends
#print axioms KakeyaFormal.MeasurableRescaling.image_union
#print axioms KakeyaFormal.MeasurableRescaling.union_volume
#print axioms KakeyaFormal.MeasurableRescaling.localized_parameter_interval
#print axioms KakeyaFormal.MeasurableRescaling.localized_tube_image
#print axioms KakeyaFormal.MeasurableRescaling.shared_origin_family
#print axioms KakeyaFormal.MeasurableRescaling.localized_volume_upper
