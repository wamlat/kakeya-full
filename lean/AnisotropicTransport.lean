import AnisotropicShading
import AngularDecomposition

/-! Actual two-ends and pointwise angular broadness transport for exact
anisotropic image shadings. No isotropic-grid replacement is used. -/
namespace KakeyaFormal.AnisotropicTransport
open EuclideanSplit SpatialAngular AnisotropicRescaling AnisotropicVolume AnisotropicDirections
open ProjectiveGeometry AngularDecomposition MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- Actual inverse-map identity for an arbitrary physical center. -/
theorem normalizeBox_inverse_apply {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (y : Space (k+1)) :
    normalizeBox u tau q ((boxHomeomorph u htau q).symm y) = y := by
  rw [← boxHomeomorph_apply u htau]
  exact (boxHomeomorph u htau q).apply_symm_apply y

/-- Pointwise membership is exactly transported, without a null-set exception. -/
theorem image_membership {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (Y : Set (Space (k+1))) (y : Space (k+1)) :
    y ∈ normalizeBox u tau q '' Y ↔ (boxHomeomorph u htau q).symm y ∈ Y := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    rw [← boxHomeomorph_apply u htau,(boxHomeomorph u htau q).symm_apply_apply]
    exact hx
  · intro hy
    exact ⟨(boxHomeomorph u htau q).symm y,hy,normalizeBox_inverse_apply u htau q y⟩

/-- Expansion of distances makes the preimage of a physical ball lie in an
old ball of the same radius. The center is the explicit actual inverse image. -/
theorem image_inter_ball_subset {k : ℕ} (u : Space (k+1)) {tau : ℝ}
    (htau : 0 < tau) (htau1 : tau ≤ 1) (q : Cell k)
    (Y : Set (Space (k+1))) (y : Space (k+1)) (r : ℝ) :
    (normalizeBox u tau q '' Y) ∩ Metric.closedBall y r ⊆
      normalizeBox u tau q '' (Y ∩ Metric.closedBall ((boxHomeomorph u htau.ne' q).symm y) r) := by
  rintro x ⟨⟨z,hz,rfl⟩,hball⟩
  refine ⟨z,⟨hz,?_⟩,rfl⟩
  have h := (normalizeBox_distance_bounds u htau htau1 q z ((boxHomeomorph u htau.ne' q).symm y)).1
  rw [normalizeBox_inverse_apply u htau.ne'] at h
  exact h.trans hball

/-- Exact image shadings retain every two-ends test with the same coefficient;
the volume factor cancels and the new bottom radius is at least the old one. -/
theorem image_two_ends {k : ℕ} (u : Space (k+1)) {tau δ B alpha : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (q : Cell k)
    (Y : Set (Space (k+1))) (hY : volume Y ≠ ∞)
    (hends : ∀ x : Space (k+1), ∀ r : ℝ, δ ≤ r →
      (volume : Measure (Space (k+1))).real (Y ∩ Metric.closedBall x r) ≤
        B*r^alpha*(volume : Measure (Space (k+1))).real Y) :
    ∀ x : Space (k+1), ∀ r : ℝ, δ/tau ≤ r →
      (volume : Measure (Space (k+1))).real ((normalizeBox u tau q '' Y) ∩ Metric.closedBall x r) ≤
        B*r^alpha*(volume : Measure (Space (k+1))).real (normalizeBox u tau q '' Y) := by
  intro x r hr
  have hδnew : δ ≤ δ/tau := (le_div_iff₀ htau).mpr (by nlinarith)
  have hfinite : volume (Y ∩ Metric.closedBall ((boxHomeomorph u htau.ne' q).symm x) r) ≠ ∞ :=
    measure_ne_top_of_subset Set.inter_subset_left hY
  have hm := measureReal_mono (image_inter_ball_subset u htau htau1 q Y x r)
    (normalizeBox_volume_finite u htau q hfinite)
  rw [normalizeBox_realVolume u htau] at hm
  have he := div_le_div_of_nonneg_right
    (hends ((boxHomeomorph u htau.ne' q).symm x) r (hδnew.trans hr)) (pow_pos htau k).le
  rw [normalizeBox_realVolume u htau]
  exact hm.trans (by simpa only [mul_div_assoc] using he)

/-- Broadness of any actual occupied direction set transports to unit angular
scale. Only members of that occupied set need satisfy the local angular cap. -/
theorem broad_transformed {k M : ℕ} (F : TubeFamily (k+1) M) (points : Finset (Fin M))
    (u : Space (k+1)) {tau δ angular beta K : ℝ} (hu : ‖u‖ = 1)
    (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (ha : 0 ≤ angular) (hK : 0 ≤ K)
    (hlocal : ∀ i ∈ points, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hbroad : Broad F points δ beta tau K) (q : Cell k) (j : Fin M → ℕ)
    (shading : Fin M → Finset (Cell (k+1))) :
    Broad (AnisotropicCap.family F u htau.ne' q j shading) points (δ/tau) beta 1
      (K*(8*(1+2*angular)^2)^beta) := by
  let G := AnisotropicCap.family F u htau.ne' q j shading
  let C := 4*(1+2*angular)^2
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg angular]
  intro center r hr
  let S := cap G points center r
  change (S.card:ℝ) ≤ _
  have hr0 : 0 < r := (div_pos hδ htau).trans_le hr
  by_cases hne : S.Nonempty
  · obtain ⟨i0,hi0⟩ := hne
    have hi0P := (Finset.mem_filter.mp hi0).1
    let R := 2*C*tau*r
    have hRδ : δ ≤ R := by
      have hdr : δ ≤ r*tau := (div_le_iff₀ htau).mp hr
      dsimp [R]
      nlinarith
    have hsub : S ⊆ cap F points (F.tube i0).direction R := by
      intro i hi
      have hiP := (Finset.mem_filter.mp hi).1
      refine Finset.mem_filter.mpr ⟨hiP,?_⟩
      have htri := projective_triangle (G.tube i).direction center (G.tube i0).direction
      have hi' := (Finset.mem_filter.mp hi).2
      have hi0' := (Finset.mem_filter.mp hi0).2
      rw [projective_symm center (G.tube i0).direction] at htri
      have hang : projectiveDistance (G.tube i).direction (G.tube i0).direction ≤ 2*r := by linarith
      have hinv : projectiveDistance (F.tube i).direction (F.tube i0).direction ≤
          C*tau*projectiveDistance (G.tube i).direction (G.tube i0).direction :=
        transformed_projective_inverse u (F.tube i).direction (F.tube i0).direction hu
          (F.tube i).unit_direction (F.tube i0).unit_direction htau htau1 ha
          (hlocal i hiP) (hlocal i0 hi0P)
      exact hinv.trans (by dsimp [R]; nlinarith)
    have hcard : (S.card:ℝ) ≤ ((cap F points (F.tube i0).direction R).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hbound := hcard.trans (hbroad (F.tube i0).direction R hRδ)
    have heq : R/tau = (8*(1+2*angular)^2)*r := by
      dsimp [R,C]
      field_simp
      ring
    rw [heq,Real.mul_rpow (by positivity) hr0.le] at hbound
    simpa only [div_one,mul_assoc] using hbound
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    positivity

/-- Exact image membership preserves the finite index set at the common
inverse point, including indices whose original shading is empty. -/
theorem image_incidence {k M : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (Y : Fin M → Set (Space (k+1))) (x : Space (k+1)) :
    Finset.univ.filter (fun i => x ∈ normalizeBox u tau q '' Y i) =
      Finset.univ.filter (fun i => (boxHomeomorph u htau q).symm x ∈ Y i) := by
  ext i
  simp only [Finset.mem_filter,image_membership u htau q]

/-- Genuine measurable pointwise broadness for the exact image family. The
new coefficient is independent of tau, delta and the original cardinality. -/
theorem image_broadness {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (Y : Fin M → Set (Space (k+1))) {tau δ angular beta K : ℝ} (hu : ‖u‖ = 1)
    (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (ha : 0 ≤ angular) (hK : 0 ≤ K)
    (hlocal : ∀ i, (Y i).Nonempty → projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hbroad : ∀ x : Space (k+1), Broad F (Finset.univ.filter (fun i => x ∈ Y i)) δ beta tau K)
    (q : Cell k) (j : Fin M → ℕ) (shading : Fin M → Finset (Cell (k+1))) :
    ∀ x : Space (k+1),
      Broad (AnisotropicCap.family F u htau.ne' q j shading)
        (Finset.univ.filter (fun i => x ∈ normalizeBox u tau q '' Y i)) (δ/tau) beta 1
        (K*(8*(1+2*angular)^2)^beta) := by
  intro x
  rw [image_incidence u htau.ne']
  apply broad_transformed F _ u hu hδ htau htau1 ha hK
  · intro i hi
    exact hlocal i ⟨(boxHomeomorph u htau.ne' q).symm x,(Finset.mem_filter.mp hi).2⟩
  · exact hbroad _

end
end KakeyaFormal.AnisotropicTransport
