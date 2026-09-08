import AnisotropicRescaling

/-! Exact Lebesgue scaling under the actual transverse dilation, with its
orthogonal frame and spatial translation. -/
namespace KakeyaFormal.AnisotropicVolume
open EuclideanSplit SpatialAngular AnisotropicRescaling MeasureTheory
open scoped ENNReal
noncomputable section

/-- The actual transverse dilation as a linear map. -/
def stretchLinearMap {k : ℕ} (tau : ℝ) : Space (k+1) →ₗ[ℝ] Space (k+1) where
  toFun := stretch tau
  map_add' := stretch_add tau
  map_smul' := stretch_smul tau

/-- The linear map is the diagonal matrix with one longitudinal eigenvalue1
and k transverse eigenvalues tau inverse. -/
theorem stretchLinearMap_diagonal {k : ℕ} (tau : ℝ) :
    stretchLinearMap (k:=k) tau =
      (Matrix.diagonal (Fin.cases 1 (fun _ : Fin k => tau⁻¹))).toLpLin 2 2 := by
  ext x i
  cases i using Fin.cases <;>
    simp [stretchLinearMap,stretch,cons,head,tail,Matrix.toLpLin_apply,Matrix.mulVec_diagonal]

/-- The transverse dimension, rather than the ambient dimension, is the
Jacobian exponent. -/
theorem stretch_determinant {k : ℕ} (tau : ℝ) :
    LinearMap.det (stretchLinearMap (k:=k) tau) = tau⁻¹^k := by
  rw [stretchLinearMap_diagonal,LinearMap.det_toLpLin,Matrix.det_diagonal,Fin.prod_univ_succ]
  simp

/-- The explicit inverse yields a genuine continuous linear equivalence. -/
def stretchEquiv {k : ℕ} {tau : ℝ} (htau : tau ≠ 0) :
    Space (k+1) ≃ₗ[ℝ] Space (k+1) where
  toLinearMap := stretchLinearMap tau
  invFun := compress tau
  left_inv := compress_stretch htau
  right_inv := stretch_compress htau

/-- Exact outer-measure scaling for arbitrary sets under transverse dilation. -/
theorem stretch_volume {k : ℕ} {tau : ℝ} (htau : 0 < tau) (Y : Set (Space (k+1))) :
    volume (stretch tau '' Y) = ENNReal.ofReal (tau⁻¹^k)*volume Y := by
  have h := (volume : Measure (Space (k+1))).addHaar_image_linearMap (stretchLinearMap tau) Y
  rw [stretch_determinant,abs_of_nonneg (pow_nonneg (inv_nonneg.mpr htau.le) k)] at h
  exact h

/-- The frame is an actual measure-preserving orthogonal transformation. -/
theorem frame_volume {k : ℕ} (u : Space (k+1)) (Y : Set (Space (k+1))) :
    volume (alignStem u '' Y) = volume Y := by
  change volume ((alignStem u).toLinearEquiv '' Y) = volume Y
  rw [(alignStem u).toLinearEquiv.image_eq_preimage_symm]
  exact (alignStem u).symm.measurePreserving.measure_preimage_emb
    (alignStem u).symm.toHomeomorph.measurableEmbedding Y

/-- Translation preserves outer measure without any measurability premise. -/
theorem translation_volume {k : ℕ} (c : Space k) (Y : Set (Space k)) :
    volume ((fun x => x-c) '' Y) = volume Y := by
  have heq : (fun x => x-c) '' Y = (fun x => x+c) ⁻¹' Y := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      simpa only [Set.mem_preimage,sub_add_cancel] using hy
    · intro hx
      exact ⟨x+c,hx,add_sub_cancel_right x c⟩
  rw [heq,measure_preimage_add_right]

/-- Exact decomposition of the actual spatial map into its three transformations. -/
theorem normalizeBox_image {k : ℕ} (u : Space (k+1)) (tau : ℝ)
    (q : Cell k) (Y : Set (Space (k+1))) :
    normalizeBox u tau q '' Y =
      (fun x => x-cons 0 (tau⁻¹ • cellCenter (2*tau) q)) ''
        (stretch tau '' (alignStem u '' Y)) := by
  simp only [Set.image_image,normalizeBox_affine]

/-- The full spatial normalization is a genuine homeomorphism. -/
def boxHomeomorph {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) : Space (k+1) ≃ₜ Space (k+1) :=
  (alignStem u).toHomeomorph.trans
    ((stretchEquiv htau).toContinuousLinearEquiv.toHomeomorph.trans
      (Homeomorph.addRight (-cons 0 (tau⁻¹ • cellCenter (2*tau) q))))

theorem boxHomeomorph_apply {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (x : Space (k+1)) :
    boxHomeomorph u htau q x = normalizeBox u tau q x := by
  change stretch tau (alignStem u x)+(-cons 0 (tau⁻¹ • cellCenter (2*tau) q)) = _
  rw [normalizeBox_affine,sub_eq_add_neg]

/-- Measurability is preserved by the actual affine bijection. -/
theorem normalizeBox_image_measurable {k : ℕ} (u : Space (k+1)) {tau : ℝ}
    (htau : tau ≠ 0) (q : Cell k) {Y : Set (Space (k+1))} (hY : MeasurableSet Y) :
    MeasurableSet (normalizeBox u tau q '' Y) := by
  have heq : normalizeBox u tau q = boxHomeomorph u htau q := by
    funext x; exact (boxHomeomorph_apply u htau q x).symm
  rw [heq]
  exact (boxHomeomorph u htau q).measurableEmbedding.measurableSet_image' hY

/-- Exact volume factor tau to the minus transverse dimension. -/
theorem normalizeBox_volume {k : ℕ} (u : Space (k+1)) {tau : ℝ}
    (htau : 0 < tau) (q : Cell k) (Y : Set (Space (k+1))) :
    volume (normalizeBox u tau q '' Y) = ENNReal.ofReal (tau⁻¹^k)*volume Y := by
  rw [normalizeBox_image,translation_volume,stretch_volume htau,frame_volume]

/-- The corresponding exact real-volume identity. -/
theorem normalizeBox_realVolume {k : ℕ} (u : Space (k+1)) {tau : ℝ}
    (htau : 0 < tau) (q : Cell k) (Y : Set (Space (k+1))) :
    (volume : Measure (Space (k+1))).real (normalizeBox u tau q '' Y) =
      (volume : Measure (Space (k+1))).real Y/tau^k := by
  have h := congrArg ENNReal.toReal (normalizeBox_volume u htau q Y)
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_nonneg (inv_nonneg.mpr htau.le) k)] at h
  simpa only [measureReal_def,inv_pow,div_eq_mul_inv,mul_comm] using h

/-- Finite original volume remains finite. -/
theorem normalizeBox_volume_finite {k : ℕ} (u : Space (k+1)) {tau : ℝ}
    (htau : 0 < tau) (q : Cell k) {Y : Set (Space (k+1))} (hY : volume Y ≠ ∞) :
    volume (normalizeBox u tau q '' Y) ≠ ∞ := by
  rw [normalizeBox_volume u htau]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY

/-- The same map is applied to the whole family, so union volume has exactly
the same factor as each individual shading. -/
theorem normalizeBox_union_realVolume {k : ℕ} {I : Type*} (u : Space (k+1)) {tau : ℝ}
    (htau : 0 < tau) (q : Cell k) (Y : I → Set (Space (k+1))) :
    (volume : Measure (Space (k+1))).real (⋃ i, normalizeBox u tau q '' Y i) =
      (volume : Measure (Space (k+1))).real (⋃ i, Y i)/tau^k := by
  rw [← Set.image_iUnion,normalizeBox_realVolume u htau]

end
end KakeyaFormal.AnisotropicVolume
