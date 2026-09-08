import AnisotropicTransport
import MeasurableEstimate

/-! Configuration-facing anisotropic normalization: actual selected unit tubes,
fixed bounded bases, relative shading density, and uniform direction constants. -/
namespace KakeyaFormal.AnisotropicConfiguration
open EuclideanSplit SpatialAngular AnisotropicRescaling AnisotropicVolume AnisotropicShading
open ProjectiveGeometry TubeVolume MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- Fixed two-sided unit-tube volume coefficients, in ambient dimension k+1. -/
def lowerCoeff (k : ℕ) : ℝ := unitBallVolume (k+1)/(2:ℝ)^(k+2)
def upperCoeff (k : ℕ) : ℝ := 3*(2:ℝ)^(k+1)*unitBallVolume (k+1)

theorem lowerCoeff_pos (k : ℕ) : 0 < lowerCoeff k := by
  dsimp [lowerCoeff]
  exact div_pos (unitBallVolume_pos _) (by positivity)

theorem upperCoeff_pos (k : ℕ) : 0 < upperCoeff k := by
  dsimp [upperCoeff]
  positivity [unitBallVolume_pos (k+1)]

/-- A fixed positive density factor, deliberately bounded by one. -/
def densityFactor (k : ℕ) (angular : ℝ) : ℝ :=
  lowerCoeff k/((upperCoeff k+lowerCoeff k)*(segmentCount angular:ℝ))

theorem densityFactor_pos (k : ℕ) (angular : ℝ) : 0 < densityFactor k angular := by
  dsimp [densityFactor]
  exact div_pos (lowerCoeff_pos k)
    (mul_pos (add_pos (upperCoeff_pos k) (lowerCoeff_pos k)) (Nat.cast_pos.mpr (segmentCount_pos angular)))

theorem densityFactor_le_one (k : ℕ) (angular : ℝ) : densityFactor k angular ≤ 1 := by
  have hc := lowerCoeff_pos k
  have hC := upperCoeff_pos k
  have hN : (1:ℝ) ≤ segmentCount angular := by exact_mod_cast (segmentCount_pos angular)
  dsimp [densityFactor]
  apply (div_le_one (by positivity)).mpr
  nlinarith

/-- Multiplying by the new tube-volume upper coefficient costs no more than
the original lower coefficient divided by the number of segments. -/
theorem densityFactor_upperCoeff (k : ℕ) (angular : ℝ) :
    densityFactor k angular*upperCoeff k ≤ lowerCoeff k/(segmentCount angular:ℝ) := by
  have hc := lowerCoeff_pos k
  have hC := upperCoeff_pos k
  have hN : (0:ℝ) < segmentCount angular := Nat.cast_pos.mpr (segmentCount_pos angular)
  have hr : upperCoeff k/(upperCoeff k+lowerCoeff k) ≤ 1 :=
    (div_le_one (add_pos hC hc)).mpr (by linarith)
  calc
    _ = (lowerCoeff k/(segmentCount angular:ℝ))*(upperCoeff k/(upperCoeff k+lowerCoeff k)) := by
      dsimp [densityFactor]
      field_simp
    _ ≤ (lowerCoeff k/(segmentCount angular:ℝ))*1 :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := mul_one _

/-- The lower tube volume written with the transverse power delta^k. -/
theorem tube_lower {k : ℕ} (T : UnitTube (k+1)) {δ : ℝ} (hδ : 0 < δ) :
    lowerCoeff k*δ^k ≤ (volume : Measure (Space (k+1))).real (T.carrier δ) := by
  have h := carrier_volume_lower T hδ
  rw [mul_div_assoc,pow_succ δ,mul_div_cancel_right₀ _ hδ.ne'] at h
  exact h

/-- The upper tube volume written with the transverse power delta^k. -/
theorem tube_upper {k : ℕ} (T : UnitTube (k+1)) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (volume : Measure (Space (k+1))).real (T.carrier δ) ≤ upperCoeff k*δ^k := by
  have h := carrier_volume_upper T hδ hδ1
  rw [mul_div_assoc,pow_succ δ,mul_div_cancel_right₀ _ hδ.ne'] at h
  exact h

/-- Individual relative tube density survives actual best-segment selection
with a fixed factor depending only on dimension and angular width. -/
theorem selected_relative_density {k : ℕ} (u : Space (k+1)) {tau angular δ lam : ℝ}
    (hu : ‖u‖ = 1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1) (hlam : 0 ≤ lam)
    (q : Cell k) (T : UnitTube (k+1)) (Y : Set (Space (k+1)))
    (hcap : projectiveDistance T.direction u ≤ angular*tau) (hYT : Y ⊆ T.carrier δ)
    (hmass : lam*(volume : Measure (Space (k+1))).real (T.carrier δ) ≤
      (volume : Measure (Space (k+1))).real Y) :
    (lam*densityFactor k angular)*
        (volume : Measure (Space (k+1))).real
          ((transformedTube u (ne_of_gt (hδ.trans_le hδtau)) q T
            (bestSegment u (ne_of_gt (hδ.trans_le hδtau)) q T angular 1 δ Y)).carrier (δ/tau)) ≤
      (volume : Measure (Space (k+1))).real
        (selectedSet u (ne_of_gt (hδ.trans_le hδtau)) q T angular 1 δ Y) := by
  have htau := hδ.trans_le hδtau
  have hnew := div_pos hδ htau
  have hnew1 : δ/tau ≤ 1 := (div_le_one htau).mpr hδtau
  have hN : (0:ℝ) < segmentCount angular := Nat.cast_pos.mpr (segmentCount_pos angular)
  have hlower := (mul_le_mul_of_nonneg_left (tube_lower T hδ) hlam).trans hmass
  have hselected := selected_mass_lower u (width:=1) (δ:=δ) hu htau htau1 q T Y hcap
    (by simpa only [one_mul] using hYT)
  have hlower' := div_le_div_of_nonneg_right hlower
    (mul_pos (pow_pos htau k) hN).le
  have halg : (lam*(lowerCoeff k*δ^k))/(tau^k*(segmentCount angular:ℝ)) =
      (lam*lowerCoeff k/(segmentCount angular:ℝ))*(δ/tau)^k := by
    rw [div_pow]
    field_simp
  rw [halg] at hlower'
  have hfactor := mul_le_mul_of_nonneg_left (densityFactor_upperCoeff k angular) hlam
  have hupper := mul_le_mul_of_nonneg_left
    (tube_upper (transformedTube u htau.ne' q T (bestSegment u htau.ne' q T angular 1 δ Y)) hnew hnew1)
    (mul_nonneg hlam (densityFactor_pos k angular).le)
  have hcoef : (lam*densityFactor k angular)*(upperCoeff k*(δ/tau)^k) ≤
      (lam*lowerCoeff k/(segmentCount angular:ℝ))*(δ/tau)^k := by
    have h := mul_le_mul_of_nonneg_right hfactor (pow_pos hnew k).le
    simpa only [mul_assoc,mul_div_assoc] using h
  exact (hupper.trans hcoef).trans (hlower'.trans hselected)

/-- An original base in its genuine parallel box becomes bounded after the
actual map, and the selected unit segment moves it by at most N. -/
theorem selected_base_bound {k : ℕ} (u : Space (k+1)) {tau R W : ℝ}
    (htau : 0 < tau) (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    (Y : Set (Space (k+1))) (hbox : T.base ∈ parallelBox u tau q R W) :
    ‖(transformedTube u htau.ne' q T (bestSegment u htau.ne' q T angular width δ Y)).base‖ ≤
      1+|R|+|W|+(segmentCount angular:ℝ) := by
  have hcoords := normalizeBox_width u htau q hbox
  have hnorm := norm_cons_le (head (normalizeBox u tau q T.base)) (tail (normalizeBox u tau q T.base))
  rw [cons_head_tail] at hnorm
  have hj := (bestSegment_spec u htau.ne' q T angular width δ Y).1
  have hj' : (bestSegment u htau.ne' q T angular width δ Y:ℝ) ≤ (segmentCount angular:ℝ) := by
    exact_mod_cast (Finset.mem_range.mp hj).le
  have htri := norm_add_le (normalizeBox u tau q T.base)
    ((bestSegment u htau.ne' q T angular width δ Y:ℝ) • transformedDirection u tau T.direction)
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _),
    transformedDirection_unit u htau.ne' T.direction T.unit_direction,mul_one] at htri
  change ‖normalizeBox u tau q T.base+
    (bestSegment u htau.ne' q T angular width δ Y:ℝ) • transformedDirection u tau T.direction‖ ≤ _
  linarith [le_abs_self R,le_abs_self W]

/-- The fixed target normalization is chosen before delta, tau, density and
tube count; only original fixed geometry and the fixed box widths occur. -/
def targetGeometry (geom : MeasurableNormalization) (angular R W : ℝ) : MeasurableNormalization where
  separation := geom.separation/(4*(1+2*|angular|)^2)
  radius := 1+|R|+|W|+(segmentCount angular:ℝ)
  separation_pos := div_pos geom.separation_pos (by positivity)
  radius_pos := by positivity

/-- Cap normalization multiplies A by a fixed factor at least one. -/
theorem cap_coefficient_ge_one (k : ℕ) {angular m A : ℝ}
    (ha : 0 ≤ angular) (hm : 0 ≤ m) (hA : 1 ≤ A) :
    1 ≤ packingConstant k*A*(8*(1+2*angular)^2)^m := by
  have hbase : (1:ℝ) ≤ 8*(1+2*angular)^2 := by nlinarith [sq_nonneg angular]
  have hpow := Real.one_le_rpow hbase hm
  have hP := packingConstant_ge_one k
  have hPA : 1 ≤ packingConstant k*A := by nlinarith
  have h := mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ packingConstant k*A)
  exact hPA.trans (by simpa only [mul_one] using h)

/-- The actual transformed family, retaining exactly one tube per original
index and the selected measurable shading for that tube. -/
def selectedFamily {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1)) {tau : ℝ}
    (htau : tau ≠ 0) (q : Cell k) (angular δ : ℝ) (Y : Fin M → Set (Space (k+1))) :
    TubeFamily (k+1) M :=
  AnisotropicCap.family F u htau q
    (fun i => bestSegment u htau q (F.tube i) angular 1 δ (Y i)) (fun _ => ∅)

/-- A complete actual measurable configuration after one angular/spatial-box
normalization. The only box premise is membership in the concrete parallelBox. -/
def normalize {k : ℕ} {geom : MeasurableNormalization} {m : ℝ}
    (F : MeasurableConfiguration (k+1) geom m) (u : Space (k+1))
    {tau angular R W : ℝ} (hu : ‖u‖ = 1) (hδtau : F.δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (hm : 0 ≤ m) (q : Cell k)
    (hlocal : ∀ i, projectiveDistance (F.family.tube i).direction u ≤ angular*tau)
    (hbox : ∀ i, (F.family.tube i).base ∈ parallelBox u tau q R W) :
    MeasurableConfiguration (k+1) (targetGeometry geom angular R W) m where
  M := F.M
  δ := F.δ/tau
  lam := F.lam*densityFactor k angular
  A := packingConstant k*F.A*(8*(1+2*angular)^2)^m
  family := selectedFamily F.family u (ne_of_gt (F.scale_pos.trans_le hδtau)) q angular F.δ F.shading
  shading i := selectedSet u (ne_of_gt (F.scale_pos.trans_le hδtau)) q (F.family.tube i) angular 1 F.δ (F.shading i)
  scale_pos := div_pos F.scale_pos (F.scale_pos.trans_le hδtau)
  scale_le_one := (div_le_one (F.scale_pos.trans_le hδtau)).mpr hδtau
  density_pos := mul_pos F.density_pos (densityFactor_pos k angular)
  density_le_one := by
    exact (mul_le_mul_of_nonneg_left (densityFactor_le_one k angular) F.density_pos.le).trans
      (by simpa only [mul_one] using F.density_le_one)
  cap_ge_one := cap_coefficient_ge_one k ha hm F.cap_ge_one
  shading_measurable i := selected_measurable u _ q (F.family.tube i) angular 1 F.δ (F.shading_measurable i)
  shading_subset i := by
    simpa only [one_mul,selectedFamily,AnisotropicCap.family] using
      (selected_subset u (ne_of_gt (F.scale_pos.trans_le hδtau)) q (F.family.tube i) angular 1 F.δ (F.shading i)).2
  shading_mass i := selected_relative_density u hu F.scale_pos hδtau htau1 F.density_pos.le
    q (F.family.tube i) (F.shading i) (hlocal i) (F.shading_subset i) (F.shading_mass i)
  separated := by
    have h := AnisotropicCap.family_separated F.family u hu (F.scale_pos.trans_le hδtau) htau1 ha hlocal
      F.separated q (fun i => bestSegment u (ne_of_gt (F.scale_pos.trans_le hδtau)) q (F.family.tube i) angular 1 F.δ (F.shading i))
      (fun _ => ∅)
    have heq : (targetGeometry geom angular R W).separation*(F.δ/tau) =
        (geom.separation*F.δ)/(4*(1+2*angular)^2*tau) := by
      simp only [targetGeometry,abs_of_nonneg ha]
      rw [div_mul_div_comm]
    rw [heq]
    exact h
  bounded i := selected_base_bound u (F.scale_pos.trans_le hδtau) q (F.family.tube i)
    angular 1 F.δ (F.shading i) (hbox i)
  cap_bound := AnisotropicCap.family_cap_bound F.family u hu F.scale_pos hδtau htau1 ha hm
    (by linarith [F.cap_ge_one]) hlocal F.cap_bound q
    (fun i => bestSegment u (ne_of_gt (F.scale_pos.trans_le hδtau)) q (F.family.tube i) angular 1 F.δ (F.shading i))
    (fun _ => ∅)

/-- The complete normalized configuration has the exact common-image union
comparison, although a different unit segment is chosen for each tube. -/
theorem normalize_union_volume {k : ℕ} {geom : MeasurableNormalization} {m : ℝ}
    (F : MeasurableConfiguration (k+1) geom m) (u : Space (k+1))
    {tau angular R W : ℝ} (hu : ‖u‖ = 1) (hδtau : F.δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (hm : 0 ≤ m) (q : Cell k)
    (hlocal : ∀ i, projectiveDistance (F.family.tube i).direction u ≤ angular*tau)
    (hbox : ∀ i, (F.family.tube i).base ∈ parallelBox u tau q R W) :
    (volume : Measure (Space (k+1))).real (normalize F u hu hδtau htau1 ha hm q hlocal hbox).unionSet ≤
      (volume : Measure (Space (k+1))).real F.unionSet/tau^k := by
  apply selected_union_volume u (F.scale_pos.trans_le hδtau) q F.family.tube angular 1 F.δ F.shading
  intro i
  exact measure_ne_top_of_subset (F.shading_subset i) (carrier_finite _ _)

/-- An existing measurable estimate gives the full angular-box estimate with
its exact tau exponent. All constants precede the variable configurations,
scales, directions, translations, densities and tube counts. -/
theorem estimate_on_box {k : ℕ} {m d p : ℝ}
    (hestimate : MeasurableEstimate (k+1) m d p) (geom : MeasurableNormalization)
    {angular R W ε : ℝ} (ha : 0 ≤ angular) (hm : 0 ≤ m) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : MeasurableConfiguration (k+1) geom m,
      ∀ u : Space (k+1), ∀ tau : ℝ, ‖u‖ = 1 → F.δ ≤ tau → tau ≤ 1 → ∀ q : Cell k,
      (∀ i, projectiveDistance (F.family.tube i).direction u ≤ angular*tau) →
      (∀ i, (F.family.tube i).base ∈ parallelBox u tau q R W) →
      c*F.A⁻¹*F.δ^(((k+1:ℕ):ℝ)+m-d+ε)*F.lam^p*(F.M:ℝ)*tau^(d-m-1-ε) ≤
        (volume : Measure (Space (k+1))).real F.unionSet := by
  obtain ⟨c0,hc0,hbound⟩ := hestimate (targetGeometry geom angular R W) ε hε
  let D := packingConstant k*(8*(1+2*angular)^2)^m
  let f := densityFactor k angular
  have hP : 0 < packingConstant k := zero_lt_one.trans_le (packingConstant_ge_one k)
  have hbase : 0 < 8*(1+2*angular)^2 := by positivity
  have hD : 0 < D := mul_pos hP (Real.rpow_pos_of_pos hbase m)
  have hf : 0 < f := densityFactor_pos k angular
  let c := c0*D⁻¹*f^p
  have hc : 0 < c := mul_pos (mul_pos hc0 (inv_pos.mpr hD)) (Real.rpow_pos_of_pos hf p)
  refine ⟨c,hc,?_⟩
  intro F u tau hu hδtau htau1 q hlocal hbox
  have htau : 0 < tau := F.scale_pos.trans_le hδtau
  let e : ℝ := ((k+1:ℕ):ℝ)+m-d+ε
  have hN := hbound (normalize F u hu hδtau htau1 ha hm q hlocal hbox)
  have hU := normalize_union_volume F u hu hδtau htau1 ha hm q hlocal hbox
  have hh := (le_div_iff₀ (pow_pos htau k)).mp (hN.trans hU)
  change c0*(packingConstant k*F.A*(8*(1+2*angular)^2)^m)⁻¹*
      (F.δ/tau)^e*(F.lam*f)^p*(F.M:ℝ)*tau^k ≤
      (volume : Measure (Space (k+1))).real F.unionSet at hh
  have htpow : tau^k/tau^e = tau^(d-m-1-ε) := by
    rw [← Real.rpow_natCast,← Real.rpow_sub htau]
    congr 1
    dsimp [e]
    push_cast
    ring
  have halg : c*F.A⁻¹*F.δ^e*F.lam^p*(F.M:ℝ)*tau^(d-m-1-ε) =
      c0*(packingConstant k*F.A*(8*(1+2*angular)^2)^m)⁻¹*
        (F.δ/tau)^e*(F.lam*f)^p*(F.M:ℝ)*tau^k := by
    rw [Real.div_rpow F.scale_pos.le htau.le,Real.mul_rpow F.density_pos.le hf.le,← htpow]
    dsimp [c,D]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  change c*F.A⁻¹*F.δ^e*F.lam^p*(F.M:ℝ)*tau^(d-m-1-ε) ≤ _
  rw [halg]
  exact hh

end
end KakeyaFormal.AnisotropicConfiguration
