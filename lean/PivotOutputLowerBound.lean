import ActualCollisionSelection
import PivotSelectionBudgets

/-! The explicit (5.19) population bound for the actual geometric pivot
selection. No energy, packing, or dyadic-retention estimate is an input. -/
namespace KakeyaFormal.PivotOutputLowerBound
open Finset TransverseAngles LegalAngleSamples LegalSampleSelection
open AngleFiberSelection ActualLabelSelection PivotSelectionBudgets
noncomputable section

/-- The constant depends only on ambient dimension and fixed tube width. -/
def outputCoefficient (k : ℕ) (width : ℝ) : ℝ :=
  1/(262144*CollisionEnergy.rowConstant k width*
    (labelConstant (k+1) width)^2*(fiberLogCoefficient (k+2) width)^2)

theorem outputCoefficient_pos (k : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    0 < outputCoefficient k width := by
  have hR := CollisionEnergy.rowConstant_pos k hw
  have hC := labelConstant_ge_one (k+1) hw
  have hJ := fiberLogCoefficient_ge_one (k+2) width
  unfold outputCoefficient
  positivity

/-- The exact rational calculation: two label losses and one collision gain
produce κ^(5d), with three logarithms and six powers of density. -/
theorem support_algebra (d : ℕ) {lam δ kappa h B D A R C J L L₀ Q : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) (hk : 0 < kappa) (hh : 0 < h)
    (hB : 0 < B) (hD : 0 < D) (hA : 0 < A) (hR : 0 < R)
    (hC : 0 < C) (hJ : 0 < J) (hL : 0 < L) (hL₀ : 0 < L₀)
    (hBins : B ≤ J*L) (hLabels : D ≤ C/kappa^(2*d)) (hLogs : L₀ ≤ L)
    (hQ : ((lam/δ)^3/128*A/(4*h*B*D))^2/(R*L₀*A/(kappa^d*δ^2)) ≤ Q) :
    (1/(262144*R*C^2*J^2))*kappa^(5*d)*lam^6*A/(h^2*δ^4*L^3) ≤ Q := by
  have hn : 0 ≤ (lam/δ)^3/128*A := by positivity
  have hden : 4*h*B*D ≤ 4*h*(J*L)*(C/kappa^(2*d)) := by gcongr
  have hquot := div_le_div_of_nonneg_left hn (by positivity : 0 < 4*h*B*D) hden
  have hsquare := pow_le_pow_left₀
    (by positivity : 0 ≤ (lam/δ)^3/128*A/(4*h*(J*L)*(C/kappa^(2*d)))) hquot 2
  have hE : R*L₀*A/(kappa^d*δ^2) ≤ R*L*A/(kappa^d*δ^2) := by gcongr
  have hEpos : 0 < R*L₀*A/(kappa^d*δ^2) := by positivity
  have hstep := (div_le_div_of_nonneg_left
    (sq_nonneg ((lam/δ)^3/128*A/(4*h*(J*L)*(C/kappa^(2*d))))) hEpos hE).trans
      (div_le_div_of_nonneg_right hsquare hEpos.le)
  have hid : ((lam/δ)^3/128*A/(4*h*(J*L)*(C/kappa^(2*d))))^2/
      (R*L*A/(kappa^d*δ^2)) =
      (1/(262144*R*C^2*J^2))*kappa^(5*d)*lam^6*A/(h^2*δ^4*L^3) := by
    rw [show 2*d = d*2 by omega,show 5*d = d*5 by omega]
    simp only [pow_mul]
    field_simp
    ring
  rw [hid] at hstep
  exact hstep.trans hQ

/-- Equation (5.19), with the fiber logarithm left explicit. Here the actual
ambient dimension is k+2 and the projective direction dimension is k+1. -/
theorem construct {k M : ℕ} {F : TubeFamily (k+2) M} {H : Finset (Cell (k+2))}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (hA : (angles F H kappa).Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hw : 0 ≤ width)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam) (hsep : F.Separated δ)
    (hsmall : (6*width/kappa)*δ ≤ 1/2) :
    ∃ P : Selection S hk hw hadm,
      outputCoefficient k width*kappa^(5*(k+1))*lam^6*((angles F H kappa).card:ℝ)/
        (((2^P.level:ℕ):ℝ)^2*δ^4*(pivotLog (kappa*δ))^3) ≤
      ((outputSupport P.retained).card:ℝ) := by
  obtain ⟨P,henergy,hraw⟩ := ActualCollisionSelection.construct S hA hδ hδ1 hlam hk hk1 hw
    hadm hcomp hsep hsmall
  refine ⟨P,?_⟩
  have hcard : (0:ℝ) < (angles F H kappa).card := by exact_mod_cast card_pos.mpr hA
  have hh : (0:ℝ) < (2^P.level:ℕ) := by exact_mod_cast (zero_lt_one.trans_le P.dyadic_pos)
  have hB : (0:ℝ) < (Nat.log 2 (fiberBudget (k+2) width kappa δ)+1:ℕ) := by positivity
  have hD : (0:ℝ) < labelBudget (k+1) width kappa := by exact_mod_cast labelBudget_pos (k+1) hw hk
  have hC := zero_lt_one.trans_le (labelConstant_ge_one (k+1) hw)
  have hJ := zero_lt_one.trans_le (fiberLogCoefficient_ge_one (k+2) width)
  have hL₀ := zero_lt_one.trans_le (pivotLog_ge_one hδ hδ1)
  have hL := hL₀.trans_le (pivotLog_mul_lower hk hk1 hδ)
  have hb := fiber_log_upper (k+2) hw hk hk1 hδ hδ1
  have hd := labelBudget_upper (k+1) hw hk hk1
  exact support_algebra (k+1) hlam hδ hk hh hB hD hcard
    (CollisionEnergy.rowConstant_pos k hw) hC hJ hL hL₀ hb hd
    (pivotLog_mul_lower hk hk1 hδ) hraw

/-- The original geometric smallness assumption already provides δ≤κ at
ordinary fixed widths. -/
theorem scale_le_kappa {width kappa δ : ℝ}
    (hk : 0 < kappa) (hδ : 0 < δ) (hw : (1:ℝ)/12 ≤ width)
    (hsmall : (6*width/kappa)*δ ≤ 1/2) : δ ≤ kappa := by
  have heq : (6*width/kappa)*δ = (6*width*δ)/kappa := by ring
  rw [heq] at hsmall
  have hh := (div_le_iff₀ hk).mp hsmall
  have hwδ := mul_le_mul_of_nonneg_right hw hδ.le
  nlinarith

/-- A fixed polynomial lower bound for κ gives exactly three powers of the
ordinary logarithm, with a fixed (q+1)^3 coefficient loss. -/
theorem construct_polynomial {k M : ℕ} {F : TubeFamily (k+2) M} {H : Finset (Cell (k+2))}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (hA : (angles F H kappa).Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hw : 0 ≤ width)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam) (hsep : F.Separated δ)
    (hsmall : (6*width/kappa)*δ ≤ 1/2) (q : ℕ) (hpoly : δ^q ≤ kappa) :
    ∃ P : Selection S hk hw hadm,
      (outputCoefficient k width/(q+1:ℝ)^3)*kappa^(5*(k+1))*lam^6*((angles F H kappa).card:ℝ)/
        (((2^P.level:ℕ):ℝ)^2*δ^4*(pivotLog δ)^3) ≤
      ((outputSupport P.retained).card:ℝ) := by
  obtain ⟨P,hQ⟩ := construct S hA hδ hδ1 hlam hk hk1 hw hadm hcomp hsep hsmall
  refine ⟨P,?_⟩
  have hC := outputCoefficient_pos k hw
  have hh : (0:ℝ) < (2^P.level:ℕ) := by exact_mod_cast (zero_lt_one.trans_le P.dyadic_pos)
  have hL₀ := zero_lt_one.trans_le (pivotLog_ge_one hδ hδ1)
  have hL := hL₀.trans_le (pivotLog_mul_lower hk hk1 hδ)
  have hlog := pivotLog_mul_upper q hk hδ hpoly
  calc
    _ = outputCoefficient k width*kappa^(5*(k+1))*lam^6*((angles F H kappa).card:ℝ)/
        (((2^P.level:ℕ):ℝ)^2*δ^4*((q+1:ℝ)*pivotLog δ)^3) := by field_simp
    _ ≤ outputCoefficient k width*kappa^(5*(k+1))*lam^6*((angles F H kappa).card:ℝ)/
        (((2^P.level:ℕ):ℝ)^2*δ^4*(pivotLog (kappa*δ))^3) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      gcongr
    _ ≤ _ := hQ

/-- For width≥1/12 no extra κ-versus-δ assumption is needed to obtain the
usual three logarithms in (5.19). -/
theorem construct_standard_log {k M : ℕ} {F : TubeFamily (k+2) M} {H : Finset (Cell (k+2))}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (hA : (angles F H kappa).Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hw : (1:ℝ)/12 ≤ width)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam) (hsep : F.Separated δ)
    (hsmall : (6*width/kappa)*δ ≤ 1/2) :
    ∃ P : Selection S hk (by linarith : 0 ≤ width) hadm,
      (outputCoefficient k width/8)*kappa^(5*(k+1))*lam^6*((angles F H kappa).card:ℝ)/
        (((2^P.level:ℕ):ℝ)^2*δ^4*(pivotLog δ)^3) ≤
      ((outputSupport P.retained).card:ℝ) := by
  have hpoly : δ^1 ≤ kappa := by simpa using scale_le_kappa hk hδ hw hsmall
  simpa only [Nat.cast_one, show ((1:ℝ)+1)^3 = 8 by norm_num] using construct_polynomial S hA hδ hδ1 hlam hk hk1 (by linarith : 0 ≤ width)
    hadm hcomp hsep hsmall 1 hpoly

/-- The selected integer fiber mass gives the stated two bounds on σ=hδ. -/
theorem sigma_bounds {k M : ℕ} {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
    {δ lam kappa width : ℝ} {S : SampleSystem F H δ lam kappa width}
    {hk : 0 < kappa} {hw : 0 ≤ width} {hadm : F.Admissible width δ}
    (P : Selection S hk hw hadm) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk1 : kappa ≤ 1) :
    lam^2/(512*LegalSampleOutputs.outputConstant (k+1) width) < ((2^P.level:ℕ):ℝ)*δ ∧
    ((2^P.level:ℕ):ℝ)*δ ≤ fiberCoefficient (k+1) width/kappa := by
  have hC := LegalSampleOutputs.outputConstant_pos (k+1) hw
  constructor
  · have hh := mul_lt_mul_of_pos_right P.dyadic_lower hδ
    have hid : (cutoff (k+1) width lam δ/2)*δ =
        lam^2/(512*LegalSampleOutputs.outputConstant (k+1) width) := by
      unfold cutoff
      field_simp
      ring
    rwa [hid] at hh
  · have hj : ((2^P.level:ℕ):ℝ) ≤ (fiberBudget (k+1) width kappa δ:ℝ) := by
      exact_mod_cast P.dyadic_upper
    have hu := hj.trans (fiberBudget_upper (k+1) hk hk1 hδ hδ1)
    have hh := mul_le_mul_of_nonneg_right hu hδ.le
    have hid : (fiberCoefficient (k+1) width/(kappa*δ))*δ =
        fiberCoefficient (k+1) width/kappa := by field_simp
    rwa [hid] at hh

/-- The same actual output theorem in the PDF's σ=hδ convention. -/
theorem construct_sigma {k M : ℕ} {F : TubeFamily (k+2) M} {H : Finset (Cell (k+2))}
    {δ lam kappa width : ℝ} (S : SampleSystem F H δ lam kappa width)
    (hA : (angles F H kappa).Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hw : (1:ℝ)/12 ≤ width)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam) (hsep : F.Separated δ)
    (hsmall : (6*width/kappa)*δ ≤ 1/2) :
    ∃ P : Selection S hk (by linarith : 0 ≤ width) hadm,
      let σ := ((2^P.level:ℕ):ℝ)*δ
      lam^2/(512*LegalSampleOutputs.outputConstant (k+2) width) < σ ∧
      σ ≤ fiberCoefficient (k+2) width/kappa ∧
      (outputCoefficient k width/8)*kappa^(5*(k+1))*lam^6*((angles F H kappa).card:ℝ)/
        (σ^2*δ^2*(pivotLog δ)^3) ≤ ((outputSupport P.retained).card:ℝ) := by
  obtain ⟨P,hQ⟩ := construct_standard_log S hA hδ hδ1 hlam hk hk1 hw hadm hcomp hsep hsmall
  refine ⟨P,(sigma_bounds P hδ hδ1 hk1).1,(sigma_bounds P hδ hδ1 hk1).2,?_⟩
  convert hQ using 1
  ring

/-- The complete population bound directly from the original two-ends family:
legal sample populations are constructed here, rather than supplied. -/
theorem construct_from_two_ends {k M : ℕ} (F : TubeFamily (k+2) M) (H : Finset (Cell (k+2)))
    {δ lam kappa width B alpha : ℝ}
    (hA : (angles F H kappa).Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hw : (1:ℝ)/12 ≤ width)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ lam) (hsep : F.Separated δ)
    (hsmall : (6*width/kappa)*δ ≤ 1/2)
    (hends : ∀ i, ∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ))
    (hradius : (2*width+1)*kappa ≤ 1)
    (hsmallEnds : B*((2*width+1)*kappa)^alpha ≤ 1/16) :
    ∃ S : SampleSystem F H δ lam kappa width,
    ∃ P : Selection S hk (by linarith : 0 ≤ width) hadm,
      let σ := ((2^P.level:ℕ):ℝ)*δ
      lam^2/(512*LegalSampleOutputs.outputConstant (k+2) width) < σ ∧
      σ ≤ fiberCoefficient (k+2) width/kappa ∧
      (outputCoefficient k width/8)*kappa^(5*(k+1))*lam^6*((angles F H kappa).card:ℝ)/
        (σ^2*δ^2*(pivotLog δ)^3) ≤ ((outputSupport P.retained).card:ℝ) := by
  obtain ⟨S⟩ := LegalAngleSamples.construct F H hδ hδ1 hlam (by linarith : 0 ≤ width)
    (scale_le_kappa hk hδ hw hsmall) hadm (fun i => (hcomp i).1) hends hradius hsmallEnds
  exact ⟨S,construct_sigma S hA hδ hδ1 hlam hk hk1 hw hadm hcomp hsep hsmall⟩

end
end KakeyaFormal.PivotOutputLowerBound
