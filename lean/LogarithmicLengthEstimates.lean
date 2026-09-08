import WideLogarithmicTwoEnds
import UnmarkedLengthEstimates

/-! Original bounded-length rows with a logarithmic two-ends budget. One
common spatial dilation preserves every old integer label; the original log
budget is compared with the log at the genuinely rescaled mesh. -/
namespace KakeyaFormal.LogarithmicLengthEstimates
open MarkedLengthNormalization UnmarkedLengthEstimates
noncomputable section

def logFactor (b : ℝ) : ℝ := max 1 ((Real.log 2)^(-b))

theorem logFactor_ge_one (b : ℝ) : 1 ≤ logFactor b := le_max_left _ _

/-- The fixed inflation also handles delta near one, where log(2/delta)
can be smaller than one. -/
theorem factor_budget {δ b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ b) :
    1 ≤ logFactor b*(Real.log (2/δ))^b := by
  have hl : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have harg : (2:ℝ) ≤ 2/δ := (le_div_iff₀ hδ).mpr (by linarith)
  have hlog : Real.log (2:ℝ) ≤ Real.log (2/δ) := Real.log_le_log (by norm_num) harg
  have hpow := Real.rpow_le_rpow hl.le hlog hb
  have hfac : (Real.log (2:ℝ))^(-b) ≤ logFactor b := le_max_right _ _
  have hid : (Real.log (2:ℝ))^(-b)*(Real.log (2:ℝ))^b = 1 := by
    rw [← Real.rpow_add hl]
    simp
  rw [← hid]
  exact mul_le_mul hfac hpow (Real.rpow_nonneg hl.le _) (zero_le_one.trans (logFactor_ge_one b))

theorem log_dilation {δ W : ℝ} (hδ : 0 < δ) (hW : 1 ≤ W) :
    Real.log (2/δ) ≤ Real.log (2/(δ/W)) := by
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hscale : δ/W ≤ δ := (div_le_iff₀ hW0).mpr (by nlinarith)
  apply Real.log_le_log (by positivity)
  exact div_le_div_of_nonneg_left (by norm_num) (div_pos hδ hW0) hscale

theorem full_ends_mono {n M : ℕ} (F : TubeFamily n M) {δ B B' alpha : ℝ}
    (hδ : 0 < δ) (hBB : B ≤ B') (h : F.FullTwoEnds δ B alpha) :
    F.FullTwoEnds δ B' alpha := by
  intro i x r hr hr1
  have hc : 0 ≤ r^alpha*((F.shade i).card:ℝ) := by positivity [(hδ.trans_le hr).le]
  have hh := mul_le_mul_of_nonneg_right hBB hc
  exact (h i x r hr hr1).trans (by simpa only [mul_assoc] using hh)

/-- Full original fixed-convention estimate: arbitrary fixed row-density
multiples, bounded individual lengths, unchanged old cells, and the ORIGINAL
logarithmic two-ends coefficient. All constants precede the original data. -/
theorem estimate {k : ℕ} {m D C : ℝ}
    (hestimate : TwoEndsDiscreteEstimate (k+1) m D C) (hm : 0 ≤ m) (hC : 1 ≤ C)
    (geom : Normalization) (lengthUpper c₀ C₀ B₀ alpha b eps : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB₀ : 1 ≤ B₀)
    (halpha : 0 < alpha) (hb : 0 ≤ b) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) (lengths : Fin M → ℝ)
      {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      (∀ i, lengths i ≤ lengthUpper) →
      (∀ i z, z ∈ F.shade i → cellCenter δ z ∈
        SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (geom.width*δ)) →
      F.Separated (geom.separation*δ) → F.Bounded geom.radius → F.CapBound δ m A →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      (∀ i, ((F.shade i).card:ℝ) ≤ C₀*lam/δ) →
      F.FullTwoEnds δ (B₀*(Real.log (2/δ))^b) alpha →
      c*A⁻¹*δ^(m-D+eps)*lam^C*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let W := dilation lengthUpper
  let alpha₀ := min alpha 1
  let Bstar := B₀*logFactor b
  have hW : 1 ≤ W := dilation_ge_one _
  have hW0 : 0 < W := dilation_pos _
  have ha₀ : 0 < alpha₀ := lt_min halpha (by norm_num)
  have hB₀p : 0 < B₀ := zero_lt_one.trans_le hB₀
  have hfactor : 1 ≤ logFactor b := logFactor_ge_one _
  have hBstar : 1 ≤ Bstar := by dsimp [Bstar]; nlinarith
  have hBstar0 : 0 < Bstar := zero_lt_one.trans_le hBstar
  have hBnew : 1 ≤ Bstar*W := by nlinarith
  obtain ⟨c,hc,hbound⟩ := WideLogarithmicTwoEnds.estimate hestimate hm hC
    (geometry geom lengthUpper) c₀ C₀ (Bstar*W) alpha₀ b eps
    hc₀ hC₀ hBnew ha₀ hb heps
  refine ⟨c*factor lengthUpper (m-D+eps) C,mul_pos hc (factor_pos _ _ _),?_⟩
  intro M F lengths δ lam A hδ hδ1 hlam hlam1 hA hL hadm hsep hbounded hcap hlower hupper hends
  have hs : δ/W ≤ 1 := (div_le_one hW0).mpr (hδ1.trans hW)
  have hl : lam/W ≤ 1 := (div_le_one hW0).mpr (hlam1.trans hW)
  have hlog : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hBfull : 1 ≤ Bstar*(Real.log (2/δ))^b := by
    have hh := factor_budget hδ hδ1 hb
    have hprod : 1 ≤ B₀*(logFactor b*(Real.log (2/δ))^b) := by nlinarith
    simpa only [Bstar,mul_assoc] using hprod
  have hBdom : B₀*(Real.log (2/δ))^b ≤ Bstar*(Real.log (2/δ))^b := by
    have hh : B₀ ≤ Bstar := by dsimp [Bstar]; nlinarith
    exact mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hlog.le _)
  have hends₀ := two_ends_weaken F hδ (by positivity : 0 ≤ Bstar*(Real.log (2/δ))^b)
    (min_le_left alpha 1) (full_ends_mono F hδ hBdom hends)
  have hendsNew := MarkedLengthNormalization.two_ends F hW hδ hBfull ha₀.le
    (min_le_right alpha 1) hends₀
  have hbudget : (Bstar*(Real.log (2/δ))^b)*W ≤
      (Bstar*W)*(Real.log (2/(δ/W)))^b := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hlog.le (log_dilation hδ hW) hb)
      (show 0 ≤ Bstar*W by positivity)
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hh
  have hendsFinal := full_ends_mono (normalizedFamily F W) (div_pos hδ hW0) hbudget hendsNew
  have hdensity (a : ℝ) : a*(lam/W)/(δ/W)=a*lam/δ := by field_simp
  have hh := hbound (normalizedFamily F W) (div_pos hδ hW0) hs (div_pos hlam hW0) hl hA
    (MarkedLengthNormalization.admissible F lengths hW0
      (fun i => (hL i).trans (le_max_right _ _)) hadm)
    (MarkedLengthNormalization.separated F hW hδ.le geom.separation_pos.le hsep)
    (MarkedLengthNormalization.bounded F hW0 hbounded)
    (MarkedLengthNormalization.cap_bound F hW hδ hδ1 hm (by linarith) hcap)
    (fun i => by rw [hdensity]; exact hlower i)
    (fun i => by rw [hdensity]; exact hupper i) hendsFinal
  have hid := power_identity (U:=m-D+eps) (p:=C) hδ.le hlam.le hW0.le
  change c*A⁻¹*(δ/W)^(m-D+eps)*(lam/W)^C*(M:ℝ) ≤ (F.unionCells.card:ℝ) at hh
  calc
    _ = (c*A⁻¹)*(((W⁻¹)^(m-D+eps)*(W⁻¹)^C)*(δ^(m-D+eps)*lam^C))*(M:ℝ) := by
      unfold factor
      ring
    _ = c*A⁻¹*(δ/W)^(m-D+eps)*(lam/W)^C*(M:ℝ) := by rw [← hid]; ring
    _ ≤ _ := hh

end
end KakeyaFormal.LogarithmicLengthEstimates
