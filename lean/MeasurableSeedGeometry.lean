import MeasurableSeedEstimate
import SeparationColoring
import WidthNormalization

/-! Fixed physical width and direction-separation normalization for the
continuous square-root-cap seed. A genuine finite color class and one common
spatial homothety preserve original measurable support and linear population. -/
namespace KakeyaFormal.MeasurableSeedGeometry
open MeasureTheory Set SeparationColoring WidthNormalization
open scoped ENNReal
noncomputable section
open Classical

/-- A largest actual color class costs only its fixed palette. -/
theorem exists_large_color {M n : ℕ} (hn : 0 < n) (color : Fin M → Fin n) :
    ∃ c : Fin n, (M:ℝ) ≤ (n:ℝ)*((colorClass color c).card:ℝ) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,Finset.mem_univ _⟩
  obtain ⟨c,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun c => ((colorClass color c).card:ℝ)) hne
  have hsum := color_weight_sum color (fun _ => (1:ℝ))
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_univ,Fintype.card_fin] at hsum
  have hle := Finset.sum_le_sum (fun i (hi : i ∈ (Finset.univ : Finset (Fin n))) => hmax i hi)
  simp only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin] at hle
  exact ⟨c,hsum.symm.trans_le hle⟩

/-- Above radius one the actual total shading mass supplies every missing
physical-ball test, without a bounded-position hypothesis. -/
theorem all_radius_two_ends {k : ℕ} {δ B alpha : ℝ} (Y : Set (Space k))
    (hfin : volume Y ≠ ∞) (hB : 1 ≤ B) (ha : 0 ≤ alpha)
    (hends : ∀ x r, δ ≤ r → r ≤ 1 → volume.real (Y ∩ Metric.closedBall x r) ≤
      B*r^alpha*volume.real Y) :
    ∀ x r, δ ≤ r → volume.real (Y ∩ Metric.closedBall x r) ≤ B*r^alpha*volume.real Y := by
  intro x r hr
  by_cases hr1 : r ≤ 1
  · exact hends x r hr hr1
  · have hp : 1 ≤ r^alpha := Real.one_le_rpow (le_of_lt (lt_of_not_ge hr1)) ha
    have hcoef : 1 ≤ B*r^alpha := one_le_mul_of_one_le_of_one_le hB hp
    exact (measureReal_mono Set.inter_subset_left hfin).trans
      (by nlinarith [measureReal_nonneg (μ:=volume) (s:=Y)])

def normalizedFamily {k M : ℕ} (F : TubeFamily k M) (W : ℝ) : TubeFamily k M where
  tube i := normalizedTube (F.tube i) W
  shade _ := ∅

theorem normalizedFamily_separated {k M : ℕ} (F : TubeFamily k M) (W : ℝ)
    {δ : ℝ} (hsep : F.Separated δ) : (normalizedFamily F W).Separated δ := hsep

theorem normalizedFamily_cap {k M : ℕ} (F : TubeFamily k M) (W : ℝ)
    {δ m A : ℝ} (hcap : F.CapBound δ m A) : (normalizedFamily F W).CapBound δ m A := hcap

/-- Arbitrary fixed width and positive direction separation are permitted for
actual comparable measurable full shadings. The positive constant and finite
logarithmic power precede all original scales, densities, positions and families. -/
theorem natural_logarithmic_seed (k : ℕ) {width sigma alpha B₀ b m : ℝ}
    (hsigma : 0 < sigma) (halpha : 0 < alpha) (hB₀ : 1 ≤ B₀) (hb : 0 ≤ b) (hm : 1 < m) :
    ∃ c P : ℝ, 0 < c ∧ 0 ≤ P ∧
      ∀ M : ℕ, ∀ F : TubeFamily (k+2) M, ∀ Y : Fin M → Set (Space (k+2)),
      ∀ δ lam B A : ℝ, 0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ B → 1 ≤ A →
      B ≤ B₀*(Real.log (2/δ))^b →
      (∀ i, MeasurableSet (Y i)) → (∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) →
      (∀ i, lam*δ^(k+1) ≤ volume.real (Y i)) →
      (∀ i, volume.real (Y i) ≤ 2*lam*δ^(k+1)) →
      F.Separated (sigma*δ) → F.CapBound δ m A →
      (∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
        B*r^alpha*volume.real (Y i)) →
      c*(Real.sqrt A)⁻¹*(Real.log (2/δ))^(-P)*lam^2*(M:ℝ)*δ^((m-3)/2) ≤
        volume.real (⋃ i, Y i)/δ^(k+2) := by
  let W : ℝ := max 1 width
  have hW : 1 ≤ W := le_max_left _ _
  have hwW : width ≤ W := le_max_right _ _
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hWa : 1 ≤ W^alpha := Real.one_le_rpow hW halpha.le
  have hBfixed : 1 ≤ B₀*W^alpha := one_le_mul_of_one_le_of_one_le hB₀ hWa
  obtain ⟨c,P,hc,hP,hmain⟩ := MeasurableSeedEstimate.natural_logarithmic_seed k halpha hBfixed hb hm
  let palette := paletteSize (k+1) sigma
  have hpalette : 0 < palette := paletteSize_pos _ _
  have hpR : (0:ℝ) < palette := by exact_mod_cast hpalette
  have hWn : 0 < W^(k+2) := pow_pos hW0 _
  refine ⟨c/((palette:ℝ)*W^(k+2)),P,div_pos hc (mul_pos hpR hWn),hP,?_⟩
  intro M F Y δ lam B A hδ hδ1 hlam hlam1 hB hA hBB hY hsub hlower hupper hsep hcap hends
  obtain ⟨color,hcolor⟩ := full_separation_coloring F hδ hsigma hsep
  obtain ⟨chosen,hcount⟩ := exists_large_color hpalette color
  let F₀ := classFamily F color chosen
  let Y₀ := fun i => Y (classIndex color chosen i)
  let G := normalizedFamily F₀ W
  let Z := fun i => normalizedSet W (Y₀ i)
  have hfin (i) : volume (Y i) ≠ ∞ := measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite _ _)
  have hZmeas (i) : MeasurableSet (Z i) := normalized_measurable hW0 (hY _)
  have hZsub (i) : Z i ⊆ (G.tube i).carrier δ := by
    apply normalized_carrier _ hW
    intro x hx
    obtain ⟨t,ht,hd⟩ := hsub (classIndex color chosen i) hx
    exact ⟨t,ht,hd.trans (mul_le_mul_of_nonneg_right hwW hδ.le)⟩
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
end KakeyaFormal.MeasurableSeedGeometry
