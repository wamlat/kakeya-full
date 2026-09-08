import MarkedNormalizationAlgebra

/-! Fixed common length dilation costs inside the literal minimum kappa.
The concentration term is exactly the same after B becomes B*W; only the
outside factor decreases by W. No alpha-dependent constant is extracted. -/
namespace KakeyaFormal.MarkedLengthAlgebra
open MarkedNormalizationKappa MarkedNormalizationAlgebra
noncomputable section

theorem choice_identity {width C W B alpha theta : ℝ}
    (hC : 0 < C) (hW : 0 < W) (hB : 0 < B) :
    choice width (C*W) B alpha theta = choice width C (B*W) alpha theta/W := by
  have hi : sourceConstant width (C*W)/B = sourceConstant width C/(B*W) := by
    unfold sourceConstant
    field_simp
  have ho : sourceConstant width (C*W) = sourceConstant width C/W := by
    unfold sourceConstant
    field_simp
  unfold choice
  rw [hi,ho]
  ring

theorem choice_le_rescaled {width C W B alpha theta : ℝ}
    (hw : 0 ≤ width) (hC : 1 ≤ C) (hW : 1 ≤ W)
    (hB : 0 < B) (htheta : 0 < theta) :
    choice width (C*W) B alpha theta ≤ choice width C (B*W) alpha theta := by
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  rw [choice_identity hC0 hW0 hB]
  have hk := choice_pos (alpha:=alpha) hw hC (mul_pos hB hW0) htheta
  apply (div_le_iff₀ hW0).mpr
  nlinarith

/-- The original twentieth-power premise supplies the finer-scale premise
at the actual rescaled source minimum. -/
theorem rescaled_cutoff {δ W T kap kapNew : ℝ}
    (hδ : 0 < δ) (hW : 1 ≤ W) (hk : 0 ≤ kap) (hle : kap ≤ kapNew)
    (hcut : T ≤ (1/δ)*kap^20) : T ≤ (1/(δ/W))*kapNew^20 := by
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hs : δ/W ≤ δ := (div_le_iff₀ hW0).mpr (by nlinarith)
  have hi : (1:ℝ)/δ ≤ 1/(δ/W) := by gcongr
  have hp := pow_le_pow_left₀ hk hle 20
  exact hcut.trans (mul_le_mul hi hp (pow_nonneg hk _) (by positivity))

end
end KakeyaFormal.MarkedLengthAlgebra
