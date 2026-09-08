import LegalSampleOutputs
import PivotDirections

/-! Fixed outputs of actual original-label samples determine only polynomially
many original second tubes. Grid errors, cap location and noncollapse are derived
from the legal endpoint formula and actual rounding. -/
namespace KakeyaFormal.LegalOutputDirections
open Finset PivotWitnesses PivotDirections ProjectiveGeometry
open LegalAngleSamples LegalAngleNormalization LegalLabeledSamples TransverseAngles
noncomputable section
open Classical

/-- An actual fiber's observed displacement differs from its nonzero legal
second-axis displacement by at most the two rounding errors. -/
theorem fiber_displacement_error {k : ℕ} {δ kap C : ℝ} (f : Fiber k δ kap C) :
    ‖(cellCenter δ f.pivotLabel-cellCenter δ f.intermediateLabel)-
      f.reference.coefficient • f.angle.second‖ ≤ 2*C*δ := by
  have hp : ‖cellCenter δ f.intermediateLabel-
      (f.angle.vertex+f.angle.intermediate • f.angle.first+(0:ℝ) • f.angle.second)‖ ≤ C*δ := by
    simpa only [zero_smul,add_zero] using f.intermediate_close
  have hh := two_point_axis_displacement (cellCenter δ f.intermediateLabel)
    (cellCenter δ f.pivotLabel) (f.angle.vertex+f.angle.intermediate • f.angle.first)
    f.angle.second hp f.reference_close
  simpa only [sub_zero,mul_assoc] using hh

/-- Quantitative observed separation is obtained from the legal coefficient's
kappa-squared lower bound, not postulated as a property of an output. -/
theorem fiber_displacement_lower {k : ℕ} {δ kap C : ℝ} (f : Fiber k δ kap C)
    (hk : 0 < kap) :
    kap^2-2*C*δ ≤ ‖cellCenter δ f.pivotLabel-cellCenter δ f.intermediateLabel‖ := by
  have hp : ‖cellCenter δ f.intermediateLabel-
      (f.angle.vertex+f.angle.intermediate • f.angle.first+(0:ℝ) • f.angle.second)‖ ≤ C*δ := by
    simpa only [zero_smul,add_zero] using f.intermediate_close
  have hh := two_point_observation_separated (cellCenter δ f.intermediateLabel)
    (cellCenter δ f.pivotLabel) (f.angle.vertex+f.angle.intermediate • f.angle.first)
    f.angle.second f.angle.second_unit
    (show kap^2 ≤ |f.reference.coefficient-0| by simpa using f.reference.coefficient_lower hk)
    hp f.reference_close
  simpa only [mul_assoc] using hh

/-- The same actual displacement supplies the projective cap center. -/
theorem fiber_direction_cap {k : ℕ} {δ kap C : ℝ} (f : Fiber k δ kap C)
    (hk : 0 < kap) :
    projectiveDistance f.angle.second
      (unitize (cellCenter δ f.pivotLabel-cellCenter δ f.intermediateLabel)) ≤ 4*C*δ/kap^2 := by
  have hh := projective_direction_of_displacement_any
    (cellCenter δ f.pivotLabel-cellCenter δ f.intermediateLabel) f.angle.second
    f.angle.second_unit (sq_pos_of_pos hk) (f.reference.coefficient_lower hk)
    (fiber_displacement_error f)
  convert hh using 1; ring

/-- A sufficient physical scale test makes the observed cap center a genuine
unit direction; the cap inequality above also covers larger mesh sizes. -/
theorem fiber_displacement_ne_zero {k : ℕ} {δ kap C : ℝ} (f : Fiber k δ kap C)
    (hk : 0 < kap) (hscale : 4*C*δ ≤ kap^2) :
    cellCenter δ f.pivotLabel-cellCenter δ f.intermediateLabel ≠ 0 := by
  intro heq
  have hh := fiber_displacement_lower f hk
  rw [heq,norm_zero] at hh
  nlinarith [sq_pos_of_pos hk]

/-- One fixed constant dominates both the actual pivot-cell rounding radius
and the twice-width projection error of the original intermediate cell. -/
def roundingConstant (k : ℕ) (width : ℝ) : ℝ := 1+2*width+(k:ℝ)/2

theorem roundingConstant_ge_one (k : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    1 ≤ roundingConstant k width := by
  unfold roundingConstant
  have := Nat.cast_nonneg (α:=ℝ) k
  linarith

variable {k M : ℕ} {F : TubeFamily k M} {H : Finset (Cell k)} {δ lam kappa width : ℝ}

/-- The common intermediate label has the actual projected-center error,
after the same homothety as every endpoint and pivot. -/
theorem intermediate_rounding (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (i : ↥(intermediates S a))
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) :
    dist (cellCenter (δ/(1+2*width)) i.val)
      ((angle S a i hkappa hwidth).vertex+
        (angle S a i hkappa hwidth).intermediate • (angle S a i hkappa hwidth).first) ≤
      (2*width)*(δ/(1+2*width)) := by
  obtain ⟨p,hp,hi⟩ := mem_image.mp i.property
  have hshade : i.val ∈ F.shade a.val.2.1 := by simpa only [hi] using (S.legal a p hp).1
  have hv1 := (angle_geometry F H hkappa hadm a.val a.property).2.1
  have hR : 0 < 1+2*width := by linarith
  have hclose := (LegalTubeSamples.shifted_tube_projection (F.tube a.val.2.1)
    (cellCenter δ a.val.1) (cellCenter δ i.val) hv1 (hadm _ _ hshade)).1
  have haxis : (1+2*width)⁻¹ • (cellCenter δ a.val.1+
      firstCoordinate F δ a.val i.val • (F.tube a.val.2.1).direction) =
      (angle S a i hkappa hwidth).vertex+
        (angle S a i hkappa hwidth).intermediate • (angle S a i hkappa hwidth).first := by
    dsimp [angle,LegalSampleNormalization.normalizeAngle]
    rcases S.sign_valid a with hs | hs
    · rw [hs,one_mul,one_smul]
      module
    · rw [hs,neg_one_mul,neg_one_smul]
      module
  rw [← haxis,LegalSampleNormalization.normalized_center_distance _ _ hR]
  convert div_le_div_of_nonneg_right hclose hR.le using 1 <;> first | rfl | ring

/-- Every actual original sample constructs the legal fiber record. All its
rounding proof fields come from deterministic grid labels and projection. -/
def sampleFiber (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hδ : 0 < δ) (hkappa : 0 < kappa)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) (p : ↥(S.samples a)) :
    Fiber k (δ/(1+2*width)) (kappa/(1+2*width)) (roundingConstant k width) := by
  let enc := encode S a hkappa hwidth hadm p
  have hR : 0 < 1+2*width := by linarith
  have hd := div_pos hδ hR
  refine ⟨angle S a enc.1 hkappa hwidth,enc.2.endpoints,enc.2.pivotLabel,enc.1.val,?_,?_⟩
  · have hh := enc.2.pivot_rounding hd
    rw [dist_comm,dist_eq_norm] at hh
    have hconst : (k:ℝ)/2 ≤ roundingConstant k width := by
      unfold roundingConstant
      linarith
    have hb := mul_le_mul_of_nonneg_right hconst hd.le
    exact hh.trans (by nlinarith)
  · have hh := intermediate_rounding S a enc.1 hkappa hwidth hadm
    rw [dist_eq_norm] at hh
    have hconst : 2*width ≤ roundingConstant k width := by
      unfold roundingConstant
      have := Nat.cast_nonneg (α:=ℝ) k
      linarith
    exact hh.trans (mul_le_mul_of_nonneg_right hconst hd.le)

theorem sampleFiber_second (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hδ : 0 < δ) (hkappa : 0 < kappa)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) (p : ↥(S.samples a)) :
    (sampleFiber S a hδ hkappa hwidth hadm p).angle.second = (F.tube a.val.2.2).direction := rfl

theorem sampleFiber_output (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hδ : 0 < δ) (hkappa : 0 < kappa)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) (p : ↥(S.samples a)) :
    ((sampleFiber S a hδ hkappa hwidth hadm p).pivotLabel,
      (sampleFiber S a hδ hkappa hwidth hadm p).intermediateLabel) =
      LegalSampleOutputs.output S a hkappa hwidth hadm p.val :=
  (LegalSampleOutputs.output_encode S a hkappa hwidth hadm p).symm

/-- Distinct original second-tube indices represented at one complete output.
The image removes all repetitions from multiple angles or multiple samples. -/
def secondIndices (S : SampleSystem F H δ lam kappa width)
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ)
    (f : Cell k × Cell k) : Finset (Fin M) :=
  (AngleFiberSelection.outputEdges
    (AngleFiberSelection.edges univ S.samples (fun a => LegalSampleOutputs.output S a hkappa hwidth hadm)) f).image
      (fun e => e.1.val.2.2)

theorem mem_secondIndices (S : SampleSystem F H δ lam kappa width)
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ)
    (f : Cell k × Cell k) (j : Fin M) :
    j ∈ secondIndices S hkappa hwidth hadm f ↔
      ∃ a : ↥(angles F H kappa), ∃ p ∈ S.samples a,
        LegalSampleOutputs.output S a hkappa hwidth hadm p=f ∧ a.val.2.2=j := by
  simp only [secondIndices,AngleFiberSelection.outputEdges,mem_image,mem_filter,
    AngleFiberSelection.mem_edges,mem_univ,true_and,AngleFiberSelection.outputs]
  constructor
  · rintro ⟨⟨a,g⟩,⟨⟨p,hp,hpg⟩,hgf⟩,haj⟩
    exact ⟨a,p,hp,hpg.trans hgf,haj⟩
  · rintro ⟨a,p,hp,hpf,haj⟩
    exact ⟨(a,f),⟨⟨p,hp,hpf⟩,rfl⟩,haj⟩


/-- Positive common spatial scaling does not change the observed direction,
including the zero-vector case. -/
theorem unitize_pos_scale {n : ℕ} (x : Space n) {r : ℝ} (hr : 0 < r) :
    unitize (r • x) = unitize x := by
  simp only [unitize,norm_smul,Real.norm_eq_abs,abs_of_pos hr,mul_inv_rev,smul_smul]
  rw [mul_assoc,inv_mul_cancel₀ hr.ne',mul_one]

/-- The unchanged pair of original integer labels has exactly the same
observed direction at the original mesh and at the common normalized mesh. -/
theorem normalized_output_direction {n : ℕ} (z i : Cell n) {d R : ℝ} (hR : 0 < R) :
    unitize (cellCenter (d/R) z-cellCenter (d/R) i) =
      unitize (cellCenter d z-cellCenter d i) := by
  rw [LegalSampleNormalization.normalized_cell,LegalSampleNormalization.normalized_cell,← smul_sub]
  exact unitize_pos_scale _ (inv_pos.mpr hR)

/-- Every original sample at a fixed complete output places its original
second-tube direction in the cap derived from the two output cells. -/
theorem sample_output_cap (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hδ : 0 < δ) (hkappa : 0 < kappa)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) (p : ↥(S.samples a))
    (f : Cell k × Cell k)
    (hout : LegalSampleOutputs.output S a hkappa hwidth hadm p.val=f) :
    projectiveDistance (F.tube a.val.2.2).direction
      (unitize (cellCenter δ f.1-cellCenter δ f.2)) ≤
      4*roundingConstant k width*(1+2*width)*δ/kappa^2 := by
  have hR : 0 < 1+2*width := by linarith
  have hh := fiber_direction_cap (sampleFiber S a hδ hkappa hwidth hadm p) (div_pos hkappa hR)
  have heq := (sampleFiber_output S a hδ hkappa hwidth hadm p).trans hout
  have hp := congrArg Prod.fst heq
  have hi := congrArg Prod.snd heq
  dsimp only [Prod.fst,Prod.snd] at hp hi
  rw [sampleFiber_second,hp,hi,normalized_output_direction _ _ hR] at hh
  convert hh using 1
  field_simp

/-- Membership in the actual set of second indices supplies a real sample
witness. No cap localization assumption is added to the finite index set. -/
theorem second_indices_cap (S : SampleSystem F H δ lam kappa width)
    (hδ : 0 < δ) (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ)
    (f : Cell k × Cell k) (j : Fin M) (hj : j ∈ secondIndices S hkappa hwidth hadm f) :
    projectiveDistance (F.tube j).direction
      (unitize (cellCenter δ f.1-cellCenter δ f.2)) ≤
      4*roundingConstant k width*(1+2*width)*δ/kappa^2 := by
  obtain ⟨a,p,hp,hpf,haj⟩ := (mem_secondIndices S hkappa hwidth hadm f j).mp hj
  have hh := sample_output_cap S a hδ hkappa hwidth hadm ⟨p,hp⟩ f hpf
  rwa [haj] at hh

/-- An actually represented output has a nonzero observed displacement under
the explicit scale test; this follows from a genuine legal sample. -/
theorem second_indices_displacement_ne_zero (S : SampleSystem F H δ lam kappa width)
    (hδ : 0 < δ) (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ)
    (f : Cell k × Cell k) (hf : (secondIndices S hkappa hwidth hadm f).Nonempty)
    (hscale : 4*roundingConstant k width*(1+2*width)*δ ≤ kappa^2) :
    cellCenter δ f.1-cellCenter δ f.2 ≠ 0 := by
  obtain ⟨j,hj⟩ := hf
  obtain ⟨a,p,hp,hpf,_⟩ := (mem_secondIndices S hkappa hwidth hadm f j).mp hj
  have hR : 0 < 1+2*width := by linarith
  have hscale' : 4*roundingConstant k width*(δ/(1+2*width)) ≤ (kappa/(1+2*width))^2 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hR)).mp
    convert hscale using 1 <;> first | rfl | field_simp [hR.ne']
  have hh := fiber_displacement_ne_zero (sampleFiber S a hδ hkappa hwidth hadm ⟨p,hp⟩)
    (div_pos hkappa hR) hscale'
  have heq := (sampleFiber_output S a hδ hkappa hwidth hadm ⟨p,hp⟩).trans hpf
  have hz := congrArg Prod.fst heq
  have hi := congrArg Prod.snd heq
  dsimp only [Prod.fst,Prod.snd] at hz hi
  rw [hz,hi,LegalSampleNormalization.normalized_cell,
    LegalSampleNormalization.normalized_cell,← smul_sub] at hh
  intro hzero
  exact hh (by rw [hzero,smul_zero])

/-- At small scales the common cap center is literally a unit direction. -/
theorem second_indices_center_unit (S : SampleSystem F H δ lam kappa width)
    (hδ : 0 < δ) (hkappa : 0 < kappa) (hwidth : 0 ≤ width) (hadm : F.Admissible width δ)
    (f : Cell k × Cell k) (hf : (secondIndices S hkappa hwidth hadm f).Nonempty)
    (hscale : 4*roundingConstant k width*(1+2*width)*δ ≤ kappa^2) :
    ‖unitize (cellCenter δ f.1-cellCenter δ f.2)‖=1 :=
  unitize_unit _ (second_indices_displacement_ne_zero S hδ hkappa hwidth hadm f hf hscale)

/-- Sphere packing counts the distinct ORIGINAL tube indices represented at
one output. The bound is independent of delta, M, density, and cap constant A.
Its kappa power is exactly 2k in ambient dimension k+1. -/
theorem second_indices_count {k M : ℕ} {F : TubeFamily (k+1) M}
    {H : Finset (Cell (k+1))} {δ lam kappa width : ℝ}
    (S : SampleSystem F H δ lam kappa width)
    (hδ : 0 < δ) (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) (hsep : F.Separated δ)
    (f : Cell (k+1) × Cell (k+1)) :
    ((secondIndices S hkappa hwidth hadm f).card:ℝ) ≤
      packingConstant k*(4*roundingConstant (k+1) width*(1+2*width)/kappa^2)^k := by
  have hC := roundingConstant_ge_one (k+1) hwidth
  have hR : 1 ≤ 1+2*width := by linarith
  have hCR : 1 ≤ roundingConstant (k+1) width*(1+2*width) := by
    have hh := mul_le_mul hC hR (by norm_num : (0:ℝ) ≤ 1) (by linarith : 0 ≤ roundingConstant (k+1) width)
    simpa only [one_mul] using hh
  have hk2 : kappa^2 ≤ 1 := pow_le_one₀ hkappa.le hkappa1
  have hrad : δ ≤ 4*roundingConstant (k+1) width*(1+2*width)*δ/kappa^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hkappa)).mpr
    have h₁ := mul_le_mul_of_nonneg_right hCR hδ.le
    have h₂ := mul_le_mul_of_nonneg_left hk2 hδ.le
    nlinarith
  have hh := indexed_projective_cap_packing (secondIndices S hkappa hwidth hadm f)
    (fun j => (F.tube j).direction) (unitize (cellCenter δ f.1-cellCenter δ f.2)) hδ hrad
    (fun j _ => (F.tube j).unit_direction)
    (fun j hj => second_indices_cap S hδ hkappa hwidth hadm f j hj)
    (fun i _ j _ hij => hsep i j hij)
  have hid : (4*roundingConstant (k+1) width*(1+2*width)*δ/kappa^2)/δ =
      4*roundingConstant (k+1) width*(1+2*width)/kappa^2 := by field_simp
  rw [hid] at hh
  exact hh

/-- The integer label budget required by AngleFiberSelection is therefore an
actual theorem about its very edge/output image, rather than an assumed count. -/
theorem second_indices_integer_count {k M : ℕ} {F : TubeFamily (k+1) M}
    {H : Finset (Cell (k+1))} {δ lam kappa width : ℝ}
    (S : SampleSystem F H δ lam kappa width)
    (hδ : 0 < δ) (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) (hsep : F.Separated δ)
    (f : Cell (k+1) × Cell (k+1)) :
    (secondIndices S hkappa hwidth hadm f).card ≤
      Nat.ceil (packingConstant k*(4*roundingConstant (k+1) width*(1+2*width)/kappa^2)^k) := by
  exact_mod_cast (second_indices_count S hδ hkappa hkappa1 hwidth hadm hsep f).trans
    (Nat.le_ceil (packingConstant k*(4*roundingConstant (k+1) width*(1+2*width)/kappa^2)^k))


/-- The exact kappa exponent can be exposed with all geometric constants in a
prefactor fixed before scale, density, and family size. -/
theorem second_indices_count_polynomial {k M : ℕ} {F : TubeFamily (k+1) M}
    {H : Finset (Cell (k+1))} {δ lam kappa width : ℝ}
    (S : SampleSystem F H δ lam kappa width)
    (hδ : 0 < δ) (hkappa : 0 < kappa) (hkappa1 : kappa ≤ 1)
    (hwidth : 0 ≤ width) (hadm : F.Admissible width δ) (hsep : F.Separated δ)
    (f : Cell (k+1) × Cell (k+1)) :
    ((secondIndices S hkappa hwidth hadm f).card:ℝ) ≤
      (packingConstant k*(4*roundingConstant (k+1) width*(1+2*width))^k)/kappa^(2*k) := by
  have hh := second_indices_count S hδ hkappa hkappa1 hwidth hadm hsep f
  rw [div_pow,← pow_mul] at hh
  exact hh.trans_eq (by ring)


/-- The already closed twentieth-power small-scale condition implies the
explicit noncollapse/cap-radius test for actual outputs. -/
theorem output_scale_of_twentieth_power {n : ℕ} {d kap w : ℝ}
    (hd : 0 < d) (hk : 0 ≤ kap) (hk1 : kap ≤ 1)
    (hlarge : 4*roundingConstant n w*(1+2*w) ≤ (1/d)*kap^20) :
    4*roundingConstant n w*(1+2*w)*d ≤ kap^2 := by
  have hp : kap^20 ≤ kap^2 := pow_le_pow_of_le_one hk hk1 (by norm_num : (2:ℕ) ≤ 20)
  have hh := mul_le_mul_of_nonneg_right hlarge hd.le
  have hid : ((1/d)*kap^20)*d = kap^20 := by field_simp
  rw [hid] at hh
  exact hh.trans hp

end
end KakeyaFormal.LegalOutputDirections
