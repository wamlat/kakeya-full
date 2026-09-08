import AngularSeedLogLoss
import LowCellAbsorption
import AnisotropicSamplingRetention

/-! The sparse-density local angular case from the actual constructed
hairbrush bound and exact old-grid volume. No sampled-count or hairbrush
estimate is assumed by the final geometric theorem. -/
namespace KakeyaFormal.LocalAngularLowDensity
open MeasureTheory AngularSeedLogLoss AngularBoxLogLoss HairbrushScales WidthNormalization
open scoped BigOperators ENNReal
noncomputable section
open Classical

/-- Natural-log conditioning can be used in the existing base-two hairbrush
interface, without changing any selected sets. -/
theorem natural_le_seedLog {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Real.log (2/δ) ≤ seedLog δ := by
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlog21 : Real.log (2:ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hL : 0 ≤ Real.log (2/δ) := (Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))).le
  have hh : Real.log (2/δ) ≤ Real.log (2/δ)/Real.log 2 :=
    (le_div_iff₀ hlog2).mpr (by nlinarith)
  change Real.log (2/δ) ≤ Real.log (2/δ)/Real.log 2+2
  linarith

/-- Fixed logarithmic loss is absorbed at the transformed mesh under the
explicit complement of the coarse eccentricity case. -/
theorem inverse_seedLog_uniform {P margin a : ℝ} (hP : 0 ≤ P)
    (hm : 0 < margin) (ha : 1 ≤ a) :
    ∃ ell : ℝ, 0 < ell ∧ ∀ {δ s : ℝ}, 0 < δ → δ ≤ 1 → 0 < s → s ≤ 1 →
      s^a ≤ δ → ell*s^margin ≤ (seedLog δ)^(-P) := by
  obtain ⟨ell,hell,hlog⟩ := PivotLossAbsorption.inverse_log_delta hP hm
  let C := (3/Real.log 2)*a
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C^(-P)*ell,by positivity,?_⟩
  intro δ s hδ hδ1 hs hs1 hscale
  have hL : 0 < Real.log (2/s) := Real.log_pos ((lt_div_iff₀ hs).mpr (by linarith))
  have hseed : 0 < seedLog δ := zero_lt_one.trans_le (seedLog_ge_one hδ hδ1)
  have hle : seedLog δ ≤ C*Real.log (2/s) := by
    have h₁ := PivotLossAbsorption.pivotLog_natural_upper hδ hδ1
    have h₂ := mul_le_mul_of_nonneg_left
      (LowCellAbsorption.log_scale_transport hδ hs ha hscale)
      (by positivity : (0:ℝ)≤3/Real.log 2)
    exact h₁.trans (by convert h₂ using 1; first | rfl | (dsimp [C]; ring))
  have hp := Real.rpow_le_rpow_of_nonpos hseed hle (by linarith : -P ≤ 0)
  rw [Real.mul_rpow hC.le hL.le] at hp
  have hh := mul_le_mul_of_nonneg_left (hlog s hs hs1) (Real.rpow_nonneg hC.le (-P))
  calc
    _ = C^(-P)*(ell*s^margin) := by ring
    _ ≤ C^(-P)*(Real.log (2/s))^(-P) := hh
    _ ≤ _ := hp

/-- The density cutoff supplies precisely the positive exponent
`(m+3)/2-D+(C-2)/3`; no favorable sign is assumed implicitly. -/
theorem sparse_power {s lam m D C eps : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hlam : 0 < lam)
    (hC : 2 ≤ C) (heps : 0 ≤ eps) (hsmall : lam ≤ s^((1:ℝ)/3)) :
    s^(m-D+eps)*lam^C ≤
      s^((m-3)/2)*s^((m+3)/2-D+(C-2)/3)*lam^2 := by
  have hp := Real.rpow_le_rpow hlam.le hsmall (by linarith : 0 ≤ C-2)
  rw [← Real.rpow_mul hs.le] at hp
  have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg lam)
  have heq : lam^2*lam^(C-2) = lam^C := by
    rw [← Real.rpow_two,← Real.rpow_add hlam]
    congr 1
    ring
  rw [heq] at hh
  have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hs.le (m-D+eps))
  have hsExp : s^(m-D+eps+(C-2)/3) ≤ s^(m-D+(C-2)/3) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  calc
    _ ≤ s^(m-D+eps)*(lam^2*s^((1/3:ℝ)*(C-2))) := hm
    _ = s^(m-D+eps+(C-2)/3)*lam^2 := by
      rw [Real.rpow_add hs (m-D+eps) ((C-2)/3),show (1/3:ℝ)*(C-2)=(C-2)/3 by ring]
      ring
    _ ≤ s^(m-D+(C-2)/3)*lam^2 := mul_le_mul_of_nonneg_right hsExp (sq_nonneg lam)
    _ = _ := by rw [← Real.rpow_add hs]; congr 1; congr 1; ring

/-- Uniform numerical conversion of the proved quadratic hairbrush bound.
The geometric theorem below supplies its actual old-cell lower bound. -/
theorem uniform_sparse {cHair P a m D C eps : ℝ}
    (hc : 0 < cHair) (hP : 0 ≤ P) (ha : 1 ≤ a) (hC : 2 ≤ C) (heps : 0 ≤ eps)
    (hmargin : 0 < (m+3)/2-D+(C-2)/3) :
    ∃ c : ℝ, 0 < c ∧ ∀ {δ s lam N E A : ℝ},
      0 < δ → δ ≤ 1 → 0 < s → s ≤ 1 → s^a ≤ δ →
      0 < lam → lam ≤ s^((1:ℝ)/3) → 0 ≤ N → 0 < A →
      cHair*A⁻¹*(seedLog δ)^(-P)*s^((m-3)/2)*lam^2*N ≤ E →
      c*A⁻¹*s^(m-D+eps)*lam^C*N ≤ E := by
  obtain ⟨ell,hell,hlog⟩ := inverse_seedLog_uniform hP hmargin ha
  refine ⟨cHair*ell,by positivity,?_⟩
  intro δ s lam N E A hδ hδ1 hs hs1 hscale hlam hsmall hN hA hraw
  have hp := sparse_power (m:=m) (D:=D) hs hs1 hlam hC heps hsmall
  have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ cHair*ell*A⁻¹*N)
  have hl := mul_le_mul_of_nonneg_left (hlog hδ hδ1 hs hs1 hscale)
    (by positivity : 0 ≤ cHair*A⁻¹*s^((m-3)/2)*lam^2*N)
  calc
    _ ≤ (cHair*ell*A⁻¹*N)*(s^((m-3)/2)*s^((m+3)/2-D+(C-2)/3)*lam^2) := by
      convert hm using 1 <;> first | rfl | ring
    _ = (cHair*A⁻¹*s^((m-3)/2)*lam^2*N)*(ell*s^((m+3)/2-D+(C-2)/3)) := by ring
    _ ≤ (cHair*A⁻¹*s^((m-3)/2)*lam^2*N)*(seedLog δ)^(-P) := hl
    _ ≤ E := by convert hraw using 1; first | rfl | ring


/-- Exact old-grid volume, followed by the favorable δ≤δ/τ comparison.
The set support is literal; no cell-count bound is supplied. -/
theorem volume_to_old_cells {k M : ℕ} (Ref : Fin M → Set (Space (k+2)))
    (S : Finset (Cell (k+2))) {δ tau W c lam m : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (hW : 1 ≤ W)
    (hsub : (⋃ i, Ref i) ⊆ normalizedSet W (GridShadingMeasure.cellUnion δ S))
    (hvol : c*lam^2*(M:ℝ)*δ^(k+1)*(δ/tau)^((m-1)/2) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Ref i)) :
    c*(δ/tau)^((m-3)/2)*lam^2*(M:ℝ) ≤ (S.card:ℝ) := by
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hu := measureReal_mono hsub (normalized_finite hW0 (GridShadingMeasure.cellUnion_finite δ S))
  rw [grid_mass S hδ hW0] at hu
  have hdiv : δ^(k+2)*(S.card:ℝ)/W^(k+2) ≤ δ^(k+2)*(S.card:ℝ) :=
    div_le_self (by positivity) (one_le_pow₀ hW)
  have hh := hvol.trans (hu.trans hdiv)
  have hcancel : c*lam^2*(M:ℝ)*(δ/tau)^((m-1)/2) ≤ δ*(S.card:ℝ) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hδ (k+1))).mp
    convert hh using 1 <;> first | rfl | ring
  have hδs : δ ≤ δ/tau := (le_div_iff₀ htau).mpr (by nlinarith)
  have hfinal := hcancel.trans (mul_le_mul_of_nonneg_right hδs (Nat.cast_nonneg S.card))
  apply (mul_le_mul_iff_right₀ (div_pos hδ htau)).mp
  convert hfinal using 1
  rw [show (m-1)/2=(m-3)/2+1 by ring,Real.rpow_add (div_pos hδ htau),Real.rpow_one]
  ring


/-- The actual retained index is injective into the same original box, and
its proved density upper bound controls the quadratic population directly. -/
theorem retained_quadratic {k M : ℕ} {Full : Fin M → Set (Space (k+1))}
    {u : Space (k+1)} {q : Cell k} {δ tau width R angular lam e B alpha beta K m A : ℝ}
    (O : AnisotropicSamplingRetention.Output Full u q δ tau width R angular lam e B alpha beta K m A) :
    O.density^2*(O.N:ℝ) ≤ lam^2*(M:ℝ) := by
  have hN : O.N ≤ M := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective O.index O.index_injective
  have hd := pow_le_pow_left₀ O.input.density_pos.le O.density_upper 2
  exact (mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg O.N)).trans
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hN) (sq_nonneg lam))

/-- Section 7's actual local low-density alternative. The constant precedes
all tube families, scales, densities, sets, cap constants and retained outputs.
The hairbrush is applied to the ORIGINAL box Full/Ref, whose old support is
literal. Natural-log conditioning and the complementary coarse-scale test
are explicit; no lower cell count, expectation or energy estimate is assumed. -/
theorem retained_low_density (k : ℕ)
    {angular eta₀ alpha beta B₀ K₀ bLog kLog qLog a m D C eps : ℝ}
    (ha : 0 ≤ angular) (heta₀ : 0 < eta₀) (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hbLog : 0 ≤ bLog) (hkLog : 0 ≤ kLog)
    (hqLog : 0 ≤ qLog) (haScale : 1 ≤ a) (hm : 1 ≤ m) (hC : 2 ≤ C) (heps : 0 ≤ eps)
    (hmargin : 0 < (m+3)/2-D+(C-2)/3) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+2) M)
      (Full Ref : Fin M → Set (Space (k+2))) (u : Space (k+2)) (label : Cell (k+1))
      (S : Finset (Cell (k+2))) {δ tau eta lam B K A W R e Anew : ℝ},
      0 < M → ‖u‖=1 → 0 < δ → δ ≤ tau → tau ≤ 1 → 0 < eta → eta ≤ 1 →
      0 < lam → lam ≤ 1 → 1 ≤ B → 1 ≤ K → 1 ≤ A → 1 ≤ W →
      (δ/tau)^a ≤ δ →
      (∀ i, MeasurableSet (Full i)) → (∀ i, MeasurableSet (Ref i)) →
      (∀ i, Ref i ⊆ Full i) → (∀ i, Full i ⊆ (F.tube i).carrier δ) →
      (∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau) →
      F.Separated δ → F.CapBound δ m A →
      (∀ i, (volume : Measure (Space (k+2))).real (Full i) ≤ 2*lam*δ^(k+1)) →
      eta*lam*δ^(k+1)*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+2))).real (Ref i) →
      (∀ x, AngularDecomposition.Broad F (Finset.univ.filter (fun i => x ∈ Ref i)) δ beta tau K) →
      (∀ i x r, δ ≤ r → r ≤ 1 →
        (volume : Measure (Space (k+2))).real (Full i ∩ Metric.closedBall x r) ≤
          B*r^alpha*(volume : Measure (Space (k+2))).real (Full i)) →
      B ≤ B₀*(Real.log (2/δ))^bLog → K ≤ K₀*(Real.log (2/δ))^kLog →
      eta₀*(Real.log (2/δ))^(-qLog) ≤ eta →
      (⋃ i, Full i) ⊆ normalizedSet W (GridShadingMeasure.cellUnion δ S) →
      ∀ O : AnisotropicSamplingRetention.Output Full u label δ tau 1 R angular lam e B alpha beta K m Anew,
      O.density ≤ (δ/tau)^((1:ℝ)/3) →
      c*A⁻¹*(δ/tau)^(m-D+eps)*O.density^C*(O.N:ℝ) ≤ (S.card:ℝ) := by
  let cHair := logarithmicConstant k angular eta₀ alpha beta B₀ K₀ m 1
  let P := logarithmicLoss k alpha beta bLog kLog qLog
  have hcap₁ : 0 < AngularBoxRecovery.capCoefficient k angular m 1 :=
    zero_lt_one.trans_le (AngularBoxHairbrush.capCoefficient_ge_one k ha (by linarith) le_rfl)
  have hcHair : 0 < cHair := logarithmicConstant_pos k ha heta₀ hB₀ hK₀ hcap₁
  have hP : 0 ≤ P := logarithmicLoss_nonneg k halpha hbeta hbLog hkLog hqLog
  obtain ⟨c,hc,hbound⟩ := uniform_sparse hcHair hP haScale hC heps hmargin
  refine ⟨c,hc,?_⟩
  intro M F Full Ref u label S δ tau eta lam B K A W R e Anew hM hu hδ hδtau htau1
    heta heta1 hlam hlam1 hB hK hA hW hscale hFull hRef hRefFull hsub hlocal hsep hcap
    hupper hmass hbroad hends hBB hKK hetabudget hsupport O hsmall
  have htau : 0 < tau := hδ.trans_le hδtau
  have hδ1 : δ ≤ 1 := hδtau.trans htau1
  have hs : 0 < δ/tau := div_pos hδ htau
  have hs1 : δ/tau ≤ 1 := (div_le_one htau).mpr hδtau
  have hLn : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hL : 0 < seedLog δ := zero_lt_one.trans_le (seedLog_ge_one hδ hδ1)
  have hcomp := natural_le_seedLog hδ hδ1
  have hBB' : B ≤ B₀*(seedLog δ)^bLog := hBB.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hLn.le hcomp hbLog) hB₀.le)
  have hKK' : K ≤ K₀*(seedLog δ)^kLog := hKK.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hLn.le hcomp hkLog) hK₀.le)
  have heta' : eta₀*(seedLog δ)^(-qLog) ≤ eta :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hLn hcomp (by linarith)) heta₀.le).trans hetabudget
  have hvol := single_box_logarithmic F Full Ref u label hM hu hδ hδtau htau1 ha heta heta1 hlam hlam1
    hB halpha hK hbeta hm hA hFull hRef hRefFull hsub hlocal hsep hcap hupper hmass hbroad hends
    heta₀ hB₀ hK₀ hL hBB' hKK' heta' (le_refl _)
  have hrefsupport : (⋃ i, Ref i) ⊆ normalizedSet W (GridShadingMeasure.cellUnion δ S) := by
    apply Set.Subset.trans ?_ hsupport
    exact Set.iUnion_mono hRefFull
  have hold := volume_to_old_cells Ref S hδ htau htau1 hW hrefsupport hvol
  have hcapconst : cHair/A ≤ logarithmicConstant k angular eta₀ alpha beta B₀ K₀ m A :=
    logarithmicConstant_cap_lower k hcHair.le hA
  have hfactor : 0 ≤ (seedLog δ)^(-P)*(δ/tau)^((m-3)/2)*lam^2*(M:ℝ) := by positivity
  have hcoeff := mul_le_mul_of_nonneg_right hcapconst hfactor
  have hraw : cHair*A⁻¹*(seedLog δ)^(-P)*(δ/tau)^((m-3)/2)*lam^2*(M:ℝ) ≤ (S.card:ℝ) := by
    apply le_trans ?_ hold
    convert hcoeff using 1 <;> first | rfl | (dsimp [P]; simp only [div_eq_mul_inv]; ring)
  have hret := mul_le_mul_of_nonneg_left (retained_quadratic O)
    (by positivity : 0 ≤ cHair*A⁻¹*(seedLog δ)^(-P)*(δ/tau)^((m-3)/2))
  apply hbound hδ hδ1 hs hs1 hscale O.input.density_pos hsmall (Nat.cast_nonneg O.N)
    (zero_lt_one.trans_le hA)
  have hret' : cHair*A⁻¹*(seedLog δ)^(-P)*(δ/tau)^((m-3)/2)*O.density^2*(O.N:ℝ) ≤
      cHair*A⁻¹*(seedLog δ)^(-P)*(δ/tau)^((m-3)/2)*lam^2*(M:ℝ) := by
    simpa only [mul_assoc] using hret
  exact hret'.trans hraw

end
end KakeyaFormal.LocalAngularLowDensity
