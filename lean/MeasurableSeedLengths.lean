import MeasurableSeedGeometry
import SamplingGeometry

/-! Literal finite tube axes of variable length in the continuous hairbrush
seed. The upper length, carrier width and separation are fixed before every
actual family; all shadings remain exact images of original measurable sets. -/
namespace KakeyaFormal.MeasurableSeedLengths
open MeasureTheory Set SeparationColoring WidthNormalization SamplingGeometry MeasurableSeedGeometry
open scoped ENNReal
noncomputable section
open Classical

/-- Every finite axis-length carrier is bounded by an explicit physical ball,
independently of other tube positions. No positivity assumption is needed for
this containment: an impossible negative interval/width simply has no points. -/
theorem lengthCarrier_subset_closedBall {k : ℕ} (T : UnitTube k) (length width : ℝ) :
    lengthCarrier T length width ⊆ Metric.closedBall T.base (length+width) := by
  rintro x ⟨t,ht,hd⟩
  have haxis : dist (T.axisPoint t) T.base = t := by
    simpa only [UnitTube.axisPoint,zero_smul,add_zero,sub_zero,abs_of_nonneg ht.1]
      using T.axisPoint_distance t 0
  have hh := dist_triangle x (T.axisPoint t) T.base
  rw [haxis] at hh
  exact (Metric.mem_closedBall).mpr (by linarith [ht.2])

theorem lengthCarrier_finite {k : ℕ} (T : UnitTube k) (length width : ℝ) :
    volume (lengthCarrier T length width) ≠ ∞ :=
  measure_ne_top_of_subset (lengthCarrier_subset_closedBall T length width) measure_closedBall_lt_top.ne

/-- Arbitrary fixed width, finite axis-length upper bound and positive direction separation are permitted for
actual comparable measurable full shadings. The positive constant and finite
logarithmic power precede all original scales, densities, positions and families. -/
theorem natural_logarithmic_seed (k : ℕ) {width upperLength sigma alpha B₀ b m : ℝ}
    (_hLength : 0 < upperLength) (hsigma : 0 < sigma) (halpha : 0 < alpha) (hB₀ : 1 ≤ B₀) (hb : 0 ≤ b) (hm : 1 < m) :
    ∃ c P : ℝ, 0 < c ∧ 0 ≤ P ∧
      ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ Y : Fin M → Set (Space (k+2)), ∀ length : Fin M → ℝ,
      ∀ δ lam B A : ℝ, 0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ B → 1 ≤ A →
      B ≤ B₀*(Real.log (2/δ))^b →
      (∀ i, length i ≤ upperLength) → (∀ i, MeasurableSet (Y i)) →
      (∀ i, Y i ⊆ lengthCarrier (F.tube i) (length i) (width*δ)) →
      (∀ i, lam*δ^(k+1) ≤ volume.real (Y i)) →
      (∀ i, volume.real (Y i) ≤ 2*lam*δ^(k+1)) →
      F.Separated (sigma*δ) → F.CapBound δ m A →
      (∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
        B*r^alpha*volume.real (Y i)) →
      c*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*lam^2*(M:ℝ)*δ^((m-3)/2) ≤
        volume.real (⋃ i, Y i)/δ^(k+2) := by
  let W : ℝ := max 1 (max width upperLength)
  have hW : 1 ≤ W := le_max_left _ _
  have hwW : width ≤ W := (le_max_left _ _).trans (le_max_right _ _)
  have hLW : upperLength ≤ W := (le_max_right _ _).trans (le_max_right _ _)
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hWa : 1 ≤ W^alpha := Real.one_le_rpow hW halpha.le
  have hBfixed : 1 ≤ B₀*W^alpha := one_le_mul_of_one_le_of_one_le hB₀ hWa
  obtain ⟨c,P,hc,hP,hmain⟩ := MeasurableSeedEstimate.natural_logarithmic_seed k halpha hBfixed hb hm
  let palette := paletteSize (k+1) sigma
  have hpalette : 0 < palette := paletteSize_pos _ _
  have hpR : (0:ℝ) < palette := by exact_mod_cast hpalette
  have hWn : 0 < W^(k+2) := pow_pos hW0 _
  refine ⟨c/((palette:ℝ)*W^(k+2)),P,div_pos hc (mul_pos hpR hWn),hP,?_⟩
  intro M F Y length δ lam B A hδ hδ1 hlam hlam1 hB hA hBB hlength hY hsub hlower hupper hsep hcap hends
  obtain ⟨color,hcolor⟩ := full_separation_coloring F hδ hsigma hsep
  obtain ⟨chosen,hcount⟩ := exists_large_color hpalette color
  let F₀ := classFamily F color chosen
  let Y₀ := fun i => Y (classIndex color chosen i)
  let G := normalizedFamily F₀ W
  let Z := fun i => normalizedSet W (Y₀ i)
  have hfin (i) : volume (Y i) ≠ ∞ := measure_ne_top_of_subset (hsub i) (lengthCarrier_finite _ _ _)
  have hZmeas (i) : MeasurableSet (Z i) := normalized_measurable hW0 (hY _)
  have hZsub (i) : Z i ⊆ (G.tube i).carrier δ := by
    intro x hx
    obtain ⟨t,ht,hd⟩ := normalized_length_carrier (F.tube (classIndex color chosen i)) hW0
      ((hlength (classIndex color chosen i)).trans hLW) (Y₀ i) (hsub (classIndex color chosen i)) hx
    refine ⟨t,ht,hd.trans ?_⟩
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hW0).mpr (by nlinarith)
  have hlamNew : 0 < lam/W^(k+2) := div_pos hlam hWn
  have hlamNew1 : lam/W^(k+2) ≤ 1 :=
    (div_le_one hWn).mpr (hlam1.trans (one_le_pow₀ hW))
  have hZlower (i) : (lam/W^(k+2))*δ^(k+1) ≤ volume.real (Z i) := by
    rw [normalized_volume hW0]
    simpa only [div_mul_eq_mul_div] using
      div_le_div_of_nonneg_right (hlower (classIndex color chosen i)) hWn.le
  have hZupper (i) : volume.real (Z i) ≤ 2*(lam/W^(k+2))*δ^(k+1) := by
    rw [normalized_volume hW0]
    convert div_le_div_of_nonneg_right (hupper (classIndex color chosen i)) hWn.le using 1 <;> first | rfl | ring
  have hZends : ∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Z i ∩ Metric.closedBall x r) ≤
      (B*W^alpha)*r^alpha*volume.real (Z i) := by
    intro i x r hr _
    apply normalized_two_ends hW0 hδ (Y₀ i)
      (all_radius_two_ends _ (hfin _) hB halpha.le (hends _)) x r
    exact (div_le_self hδ.le hW).trans hr
  have hBnew : 1 ≤ B*W^alpha := one_le_mul_of_one_le_of_one_le hB hWa
  have hBBnew : B*W^alpha ≤ (B₀*W^alpha)*(Real.log (2/δ))^b :=
    (mul_le_mul_of_nonneg_right hBB (Real.rpow_pos_of_pos hW0 alpha).le).trans_eq (by ring)
  have hbound := hmain (colorClass color chosen).card G Z δ (lam/W^(k+2)) (B*W^alpha) A
    hδ hδ1 hlamNew hlamNew1 hBnew hA hBBnew hZmeas hZsub hZlower hZupper
    (normalizedFamily_separated F₀ W (classFamily_separated F color hcolor chosen))
    (normalizedFamily_cap F₀ W (classFamily_cap_bound F color hcap chosen)) hZends
  have hysub : (⋃ i, Y₀ i) ⊆ ⋃ i, Y i := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨classIndex color chosen i,hi⟩
  have hyf : volume (⋃ i, Y i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ:=volume)
      (s:=Set.univ) (f:=Y) (Set.toFinite _) (fun i _ => hfin i)
  have hvol : volume.real (⋃ i, Z i) ≤ volume.real (⋃ i, Y i)/W^(k+2) := by
    rw [normalized_union_volume hW0]
    exact div_le_div_of_nonneg_right (measureReal_mono hysub hyf) hWn.le
  have hbound' := hbound.trans (div_le_div_of_nonneg_right hvol (pow_pos hδ (k+2)).le)
  have hscaled := mul_le_mul_of_nonneg_right hbound' hWn.le
  have hfactor : 0 ≤ (c/((palette:ℝ)*W^(k+2)))*(Real.sqrt A)⁻¹*
      (Real.log (2/δ))^(-P)*lam^2*δ^((m-3)/2) := by
    have hlog : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
    positivity
  have hpop := mul_le_mul_of_nonneg_left hcount hfactor
  calc
    _ = ((c/((palette:ℝ)*W^(k+2)))*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*lam^2*δ^((m-3)/2))*(M:ℝ) := by ring
    _ ≤ _ := hpop
    _ = (c*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*(lam/W^(k+2))^2*
        ((colorClass color chosen).card:ℝ)*δ^((m-3)/2))*W^(k+2) := by
      field_simp
    _ ≤ (volume.real (⋃ i, Y i)/W^(k+2)/δ^(k+2))*W^(k+2) := hscaled
    _ = _ := by field_simp


end
end KakeyaFormal.MeasurableSeedLengths
