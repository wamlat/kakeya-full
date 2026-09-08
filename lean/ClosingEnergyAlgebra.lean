import SelectedLiftWitness
import GroupedCumulative
import Reduction
import PivotOutputLowerBound

/-! Closing pivot energy with the exact actual witness counts and the exact
threshold of GroupedCumulative.discrete_pruning. In the scalar density lemmas,
`n` denotes projective direction dimension, one less than the original ambient
dimension used by the geometric count lemmas. -/
namespace KakeyaFormal.ClosingEnergyAlgebra
open Finset PivotSupport PivotWitnesses SelectedLiftWitness
open scoped BigOperators
noncomputable section
open Classical

/-- Fixed coefficients of the actual endpoint-pivot and lifted-cell counts. -/
def pivotCoefficient (k : ℕ) (C : ℝ) : ℝ :=
  (4+2*C)*((2*Nat.ceil (4*C+1)+3:ℕ):ℝ)^k

def liftCoefficient (k : ℕ) (C : ℝ) : ℝ :=
  174*C*((2*Nat.ceil (4*C)+3:ℕ):ℝ)^k

theorem pivotCoefficient_pos (k : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 < pivotCoefficient k C := by unfold pivotCoefficient; positivity

theorem liftCoefficient_pos (k : ℕ) {C : ℝ} (hC : 0 < C) :
    0 < liftCoefficient k C := by unfold liftCoefficient; positivity

/-- These are the literal count arguments used by the attached-sample witness. -/
theorem actual_count_bounds (k : ℕ) {δ C kappa : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : (1:ℝ)/2 ≤ C)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) :
    (pivotCount k δ (4*C) (2+2*C):ℝ) ≤ pivotCoefficient k C/δ ∧
    (liftCount k δ (2*C*δ) (4*(2*C*δ)/kappa^2) (kappa^3) (2/kappa):ℝ) ≤
      liftCoefficient k C/kappa^5 := by
  constructor
  · have hh := pivotCount_scale_bound k (width := 4*C) hδ hδ1 (by linarith : 0 ≤ 2+2*C)
    convert hh using 1
    unfold pivotCoefficient
    ring
  · have hh := normalized_liftCount_bound k hδ (by linarith : 1 ≤ 2*C) hk hk1
    rw [show 2*(2*C) = 4*C by ring] at hh
    have hid : 4*(2*C*δ)/kappa^2 = 4*(2*C)*δ/kappa^2 := by ring
    rw [hid]
    convert hh using 1
    unfold liftCoefficient
    ring

/-- The actual geometric witness gives the sharper κ^-5 energy factor. The
slab label causes no further cost. -/
theorem grouped_witness_bound {I : Type*} {k : ℕ} {δ kappa C : ℝ}
    (S : Finset I) (sample : I → AttachedSample k δ kappa C)
    (position : I → GroupPosition k) (occupied : Finset (Cell k))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : (1:ℝ)/2 ≤ C)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hscale : 2*C*δ ≤ kappa^5/4)
    (hend : ∀ i ∈ S, (sample i).firstLabel ∈ occupied ∧ (sample i).secondLabel ∈ occupied)
    (hlegal : ∀ i ∈ S, LegalPosition δ (position i))
    (hposition : ∀ i ∈ S, energyPosition (sample i).label=originalPosition δ (position i)) :
    (S.card:ℝ)^2 ≤ (occupied.card:ℝ)^2*(pivotCoefficient k C/δ)*(liftCoefficient k C/kappa^5)*
      ∑ p ∈ S.image position, ((S.filter (fun i => position i=p)).card:ℝ)^2 := by
  have hh := grouped_attached_sample_energy S sample position occupied hδ hδ1
    (by linarith : 0 ≤ C) hk hk1 hscale hend hlegal hposition
  refine hh.trans ?_
  obtain ⟨hp,hl⟩ := actual_count_bounds k hδ hδ1 hC hk hk1
  have hCp := pivotCoefficient_pos k (by linarith : 0 ≤ C)
  gcongr

/-- The exact positive scalar coefficient after half-mass retention. J is the
actual fixed direction-color count; no pivot/slab group count appears. -/
def closingCoefficient (c Cp Cl J r : ℝ) : ℝ :=
  c/(2*Cp*Cl*(2:ℝ)^(r+1)*J)

theorem closingCoefficient_pos {c Cp Cl J r : ℝ}
    (hc : 0 < c) (hCp : 0 < Cp) (hCl : 0 < Cl) (hJ : 0 < J) :
    0 < closingCoefficient c Cp Cl J r := by unfold closingCoefficient; positivity

/-- The exact (5.33) implication from the actual high-cell threshold and
actual endpoint-pivot witness. All density and scale exponents are real. -/
theorem closing_energy {I E energy rho Q δ kappa c Cp Cl J A d d' eps r : ℝ}
    (hrho : 0 < rho) (hQ : 0 < Q) (hδ : 0 < δ) (hk : 0 < kappa)
    (hc : 0 < c) (hCp : 0 < Cp) (hCl : 0 < Cl) (hJ : 0 < J) (hA : 0 < A)
    (hmass : rho*(1/δ)*Q/2 ≤ I)
    (hupper : energy ≤ ((2:ℝ)^(r+1)*J*(1/δ)/
      ((c*A⁻¹*δ^(d-d'+eps))*rho^(r-1)))*I)
    (hwitness : I^2 ≤ E^2*(Cp/δ)*(Cl/kappa^5)*energy) :
    closingCoefficient c Cp Cl J r*kappa^5*A⁻¹*rho^r*δ^(d-d'+1+eps)*Q ≤ E^2 := by
  let H := (2:ℝ)^(r+1)*J*(1/δ)/((c*A⁻¹*δ^(d-d'+eps))*rho^(r-1))
  let R := (Cp/δ)*(Cl/kappa^5)*H
  have hH : 0 < H := by dsimp [H]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hI : 0 < I := (by positivity : 0 < rho*(1/δ)*Q/2).trans_le hmass
  have hcombined : I*I ≤ (E^2*R)*I := by
    have hh := hwitness.trans (mul_le_mul_of_nonneg_left hupper
      (by positivity : 0 ≤ E^2*(Cp/δ)*(Cl/kappa^5)))
    convert hh using 1 <;> first | rfl | ring
  have hcancel : I ≤ E^2*R := (mul_le_mul_iff_left₀ hI).mp hcombined
  have hh := (div_le_iff₀ hR).mpr (hmass.trans hcancel)
  have hid : (rho*(1/δ)*Q/2)/R =
      closingCoefficient c Cp Cl J r*kappa^5*A⁻¹*rho^r*δ^(d-d'+1+eps)*Q := by
    dsimp [R,H,closingCoefficient]
    rw [show d-d'+1+eps = (d-d'+eps)+1 by ring, Real.rpow_add_one hδ.ne',
      Real.rpow_sub_one hrho.ne']
    field_simp
  rwa [hid] at hh

/-- The paper weakens the proved κ^5 gain to κ^6 for 0<κ≤1. -/
theorem closing_energy_six {I E energy rho Q δ kappa c Cp Cl J A d d' eps r : ℝ}
    (hrho : 0 < rho) (hQ : 0 < Q) (hδ : 0 < δ) (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hc : 0 < c) (hCp : 0 < Cp) (hCl : 0 < Cl) (hJ : 0 < J) (hA : 0 < A)
    (hmass : rho*(1/δ)*Q/2 ≤ I)
    (hupper : energy ≤ ((2:ℝ)^(r+1)*J*(1/δ)/
      ((c*A⁻¹*δ^(d-d'+eps))*rho^(r-1)))*I)
    (hwitness : I^2 ≤ E^2*(Cp/δ)*(Cl/kappa^5)*energy) :
    closingCoefficient c Cp Cl J r*kappa^6*A⁻¹*rho^r*δ^(d-d'+1+eps)*Q ≤ E^2 := by
  have hh := closing_energy hrho hQ hδ hk hc hCp hCl hJ hA hmass hupper hwitness
  have hC := closingCoefficient_pos (r := r) hc hCp hCl hJ
  have hp : kappa^6 ≤ kappa^5 := by
    calc
      _ = kappa^5*kappa := by ring
      _ ≤ kappa^5*1 := mul_le_mul_of_nonneg_left hk1 (by positivity)
      _ = _ := mul_one _
  refine le_trans ?_ hh
  gcongr

/-- Exact power identity for combining the output-count κ loss, the κ^6
closing gain, and the κ^6 density-transfer loss. -/
theorem kappa_power_identity (n : ℕ) {kappa r : ℝ} (hk : 0 < kappa) :
    kappa^(5*(n:ℝ)+6*r+6) = kappa^6*(kappa^6)^r*kappa^(5*n) := by
  calc
    _ = kappa^((6:ℝ)+6*r+((5*n:ℕ):ℝ)) := by congr 1; push_cast; ring
    _ = kappa^(6:ℝ)*(kappa^(6:ℝ))^r*kappa^((5*n:ℕ):ℝ) := by
      rw [Real.rpow_add hk,Real.rpow_add hk,Real.rpow_mul hk.le]
    _ = _ := by norm_cast

/-- The density step in (5.34), using the actual (5.19) convention σ=hδ.
The closing lower bound here is precisely the conclusion just proved above. -/
theorem density_combination (n : ℕ)
    {E Q rho sigma lam δ kappa A angles L cE cQ cR cS t r : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hk : 0 < kappa) (hA : 0 < A) (hL : 0 < L)
    (hAngles : 0 ≤ angles) (hcE : 0 < cE) (hcQ : 0 < cQ) (hcR : 0 < cR) (hcS : 0 < cS)
    (hr : 2 ≤ r) (hSigma : cS*lam^(2:ℝ) ≤ sigma)
    (hRho : cR*kappa^6*sigma ≤ rho)
    (hOutput : cQ*kappa^(5*n)*lam^6*angles/(sigma^2*δ^2*L^3) ≤ Q)
    (hClosing : cE*kappa^6*A⁻¹*rho^r*δ^t*Q ≤ E^2) :
    (cE*cQ*cR^r*cS^(r-2))*kappa^(5*(n:ℝ)+6*r+6)*A⁻¹*
      δ^(t-2)*lam^(2*r+2)*angles/L^3 ≤ E^2 := by
  have hsigma : 0 < sigma := (by positivity : 0 < cS*lam^(2:ℝ)).trans_le hSigma
  have hrho : 0 < rho := (by positivity : 0 < cR*kappa^6*sigma).trans_le hRho
  have hr0 : 0 ≤ r := by linarith
  have hRpow := Real.rpow_le_rpow (by positivity : 0 ≤ cR*kappa^6*sigma) hRho hr0
  let U := cE*kappa^6*A⁻¹
  let V := cQ*kappa^(5*n)*lam^6*angles/(sigma^2*δ^2*L^3)
  have hU : 0 < U := by dsimp [U]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hprod : U*(cR*kappa^6*sigma)^r*δ^t*V ≤ U*rho^r*δ^t*Q := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRpow hU.le)
        (Real.rpow_nonneg hδ.le t)
    · exact hOutput
    · exact hV
    · positivity
  have htotal := hprod.trans hClosing
  let B := cE*cQ*cR^r*kappa^(5*(n:ℝ)+6*r+6)*A⁻¹*δ^(t-2)*angles/L^3
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hden : cS^(r-2)*lam^(2*r+2) ≤ lam^6*sigma^(r-2) := by
    simpa using KakeyaAudit.Reduction.fiber_density_gain
      (q := r) (e := 0) hlam hcS hr (by norm_num) hSigma
  have hid : U*(cR*kappa^6*sigma)^r*δ^t*V = B*(lam^6*sigma^(r-2)) := by
    dsimp [U,V,B]
    rw [Real.mul_rpow (by positivity : 0 ≤ cR*kappa^6) hsigma.le,
      Real.mul_rpow hcR.le (pow_nonneg hk.le 6),kappa_power_identity n hk,
      show t-2 = t-(2:ℕ) by norm_num,show r-2 = r-(2:ℕ) by norm_num,
      Real.rpow_sub_natCast hδ.ne',Real.rpow_sub_natCast hsigma.ne']
    field_simp
  calc
    _ = B*(cS^(r-2)*lam^(2*r+2)) := by dsimp [B]; ring
    _ ≤ B*(lam^6*sigma^(r-2)) := mul_le_mul_of_nonneg_left hden hB
    _ = U*(cR*kappa^6*sigma)^r*δ^t*V := hid.symm
    _ ≤ _ := htotal

/-- The literal exponents in source (5.34), with r=q+ε and scale error ε. -/
theorem source_density_combination (n : ℕ)
    {E Q rho sigma lam δ kappa A angles L cE cQ cR cS d d' q eps : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hk : 0 < kappa) (hA : 0 < A) (hL : 0 < L)
    (hAngles : 0 ≤ angles) (hcE : 0 < cE) (hcQ : 0 < cQ) (hcR : 0 < cR) (hcS : 0 < cS)
    (hq : 2 ≤ q) (heps : 0 ≤ eps) (hSigma : cS*lam^(2:ℝ) ≤ sigma)
    (hRho : cR*kappa^6*sigma ≤ rho)
    (hOutput : cQ*kappa^(5*n)*lam^6*angles/(sigma^2*δ^2*L^3) ≤ Q)
    (hClosing : cE*kappa^6*A⁻¹*rho^(q+eps)*δ^(d-d'+1+eps)*Q ≤ E^2) :
    (cE*cQ*cR^(q+eps)*cS^(q+eps-2))*kappa^(5*(n:ℝ)+6*(q+eps)+6)*A⁻¹*
      δ^(d-d'-1+eps)*lam^(2*q+2+2*eps)*angles/L^3 ≤ E^2 := by
  have hh := density_combination n hlam hδ hk hA hL hAngles hcE hcQ hcR hcS
    (by linarith : 2 ≤ q+eps) hSigma hRho hOutput hClosing
  rw [show d-d'+1+eps-2 = d-d'-1+eps by ring,
    show 2*(q+eps)+2 = 2*q+2+2*eps by ring] at hh
  exact hh

/-- Apply the closing implication to the actual retained incidences and their
attached endpoint samples. The only energy input is the exact upper bound
returned by grouped high-cell pruning; the geometric lower bound is derived. -/
theorem retained_grouped_closing {X : Type*} {k : ℕ}
    {δ kappa C Q c J A d d' eps r : ℝ}
    (S T : Finset X) (sample : X → AttachedSample k δ kappa C)
    (position : X → GroupPosition k) (occupied : Finset (Cell k))
    (hS : S.Nonempty) (hQ : 0 < Q) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : (1:ℝ)/2 ≤ C) (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hc : 0 < c) (hJ : 0 < J) (hA : 0 < A)
    (hscale : 2*C*δ ≤ kappa^5/4)
    (hretain : (S.card:ℝ)/2 ≤ (T.card:ℝ))
    (hend : ∀ i ∈ T, (sample i).firstLabel ∈ occupied ∧ (sample i).secondLabel ∈ occupied)
    (hlegal : ∀ i ∈ T, LegalPosition δ (position i))
    (hposition : ∀ i ∈ T, energyPosition (sample i).label=originalPosition δ (position i))
    (hupper : (∑ p ∈ T.image position, ((T.filter (fun i => position i=p)).card:ℝ)^2) ≤
      ((2:ℝ)^(r+1)*J*(1/δ)/((c*A⁻¹*δ^(d-d'+eps))*(δ*(S.card:ℝ)/Q)^(r-1)))*(T.card:ℝ)) :
    closingCoefficient c (pivotCoefficient k C) (liftCoefficient k C) J r*
      kappa^5*A⁻¹*(δ*(S.card:ℝ)/Q)^r*δ^(d-d'+1+eps)*Q ≤ (occupied.card:ℝ)^2 := by
  have hcard : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hS
  have hrho : 0 < δ*(S.card:ℝ)/Q := by positivity
  have hmass : (δ*(S.card:ℝ)/Q)*(1/δ)*Q/2 ≤ (T.card:ℝ) := by
    have hid : (δ*(S.card:ℝ)/Q)*(1/δ)*Q/2 = (S.card:ℝ)/2 := by field_simp
    rwa [hid]
  exact closing_energy hrho hQ hδ hk hc (pivotCoefficient_pos k (C := C) (by linarith))
    (liftCoefficient_pos k (C := C) (by linarith)) hJ hA hmass hupper
    (grouped_witness_bound T sample position occupied hδ hδ1 hC hk hk1 hscale hend hlegal hposition)

/-- Equation (5.34) directly from the pruning mass/energy outputs and the
actual-form output population bound. In particular (5.33) is not supplied. -/
theorem source_from_energy (n : ℕ)
    {I E energy Q rho sigma lam δ kappa A angles L c Cp Cl J cQ cR cS d d' q eps : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hA : 0 < A) (hL : 0 < L) (hQ : 0 < Q) (hAngles : 0 ≤ angles)
    (hc : 0 < c) (hCp : 0 < Cp) (hCl : 0 < Cl) (hJ : 0 < J)
    (hcQ : 0 < cQ) (hcR : 0 < cR) (hcS : 0 < cS)
    (hq : 2 ≤ q) (heps : 0 ≤ eps) (hSigma : cS*lam^(2:ℝ) ≤ sigma)
    (hRho : cR*kappa^6*sigma ≤ rho)
    (hOutput : cQ*kappa^(5*n)*lam^6*angles/(sigma^2*δ^2*L^3) ≤ Q)
    (hmass : rho*(1/δ)*Q/2 ≤ I)
    (hupper : energy ≤ ((2:ℝ)^(q+eps+1)*J*(1/δ)/
      ((c*A⁻¹*δ^(d-d'+eps))*rho^(q+eps-1)))*I)
    (hwitness : I^2 ≤ E^2*(Cp/δ)*(Cl/kappa^5)*energy) :
    (closingCoefficient c Cp Cl J (q+eps)*cQ*cR^(q+eps)*cS^(q+eps-2))*
      kappa^(5*(n:ℝ)+6*(q+eps)+6)*A⁻¹*δ^(d-d'-1+eps)*
      lam^(2*q+2+2*eps)*angles/L^3 ≤ E^2 := by
  have hsigma : 0 < sigma := (by positivity : 0 < cS*lam^(2:ℝ)).trans_le hSigma
  have hrho : 0 < rho := (by positivity : 0 < cR*kappa^6*sigma).trans_le hRho
  have hclose := closing_energy_six hrho hQ hδ hk hk1 hc hCp hCl hJ hA hmass hupper hwitness
  exact source_density_combination n hlam hδ hk hA hL hAngles
    (closingCoefficient_pos hc hCp hCl hJ) hcQ hcR hcS hq heps hSigma hRho hOutput hclose

/-- The final κ exponent weakening used immediately after (5.34). -/
theorem error_kappa_weakening (n : ℕ) {kappa q eps : ℝ}
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (heps : eps ≤ 1) :
    kappa^(5*(n:ℝ)+6*q+12) ≤ kappa^(5*(n:ℝ)+6*(q+eps)+6) := by
  apply Real.rpow_le_rpow_of_exponent_ge hk hk1
  linarith

end
end KakeyaFormal.ClosingEnergyAlgebra
