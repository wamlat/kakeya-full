import MarkedGridNormalization
import MinPivotKappa
import PivotGeometryScale

/-! The fixed normalization loss belongs INSIDE the source minimum's
1/alpha power. No alpha-uniform comparison with the old source constant or the
product radius is asserted. -/
namespace KakeyaFormal.MarkedNormalizationKappa
noncomputable section

/-- Both occurrences of the small source constant include the actual fixed
full-two-ends normalization coefficient. -/
def sourceConstant (width C : ℝ) : ℝ := MinPivotKappa.sourceConstant width/C

def choice (width C B alpha theta : ℝ) : ℝ :=
  sourceConstant width C*min theta (min (1/100) ((sourceConstant width C/B)^(1/alpha)))

theorem sourceConstant_bounds {width C : ℝ} (hw : 0 ≤ width) (hC : 1 ≤ C) :
    0 < sourceConstant width C ∧ sourceConstant width C ≤ MinPivotKappa.sourceConstant width := by
  have hc := (MinPivotKappa.sourceConstant_bounds hw).1
  have hC0 : 0 < C := by linarith
  refine ⟨by unfold sourceConstant; positivity,?_⟩
  unfold sourceConstant
  apply (div_le_iff₀ hC0).mpr
  nlinarith

theorem choice_pos {width C B alpha theta : ℝ}
    (hw : 0 ≤ width) (hC : 1 ≤ C) (hB : 0 < B) (ht : 0 < theta) :
    0 < choice width C B alpha theta := by
  have hc := (sourceConstant_bounds hw hC).1
  unfold choice
  positivity

/-- The inner concentration quantities are IDENTICAL after replacing B by C*B;
only the nonnegative outside geometric factor is made smaller. -/
theorem choice_le_normalized_source {width C B alpha theta : ℝ}
    (hw : 0 ≤ width) (hC : 1 ≤ C) (hB : 0 < B) (ht : 0 < theta) :
    choice width C B alpha theta ≤ MinPivotKappa.sourceChoice width (C*B) alpha theta := by
  obtain ⟨hc,hcle⟩ := sourceConstant_bounds hw hC
  have hc0 := (MinPivotKappa.sourceConstant_bounds hw).1
  have hinner : sourceConstant width C/B=MinPivotKappa.sourceConstant width/(C*B) := by
    unfold sourceConstant
    ring
  unfold choice MinPivotKappa.sourceChoice
  rw [hinner]
  apply mul_le_mul_of_nonneg_right hcle
  positivity [show 0 < C by linarith]

/-- Exact source minimum admissibility for the actual normalized coefficient,
including its later factor-two deterioration during pruning recovery. -/
theorem admissible {width C B alpha theta : ℝ}
    (hw : 0 ≤ width) (hC : 1 ≤ C) (hB : 1 ≤ B) (ha : 0 < alpha) (ht : 0 < theta) :
    0 < choice width C B alpha theta ∧ choice width C B alpha theta ≤ 1/100 ∧
      2*choice width C B alpha theta ≤ theta ∧
      (2*width+1)*choice width C B alpha theta ≤ 1 ∧
      (2*(C*B))*((2*width+1)*choice width C B alpha theta)^alpha ≤ 1/16 := by
  have hCB : 1 ≤ C*B := by nlinarith
  obtain ⟨_,hk100,hangle,hradius,hlegal⟩ := MinPivotKappa.source_admissible hw hCB ha ht
  have hk := choice_pos (alpha := alpha) hw hC (by linarith : 0 < B) ht
  have hle := choice_le_normalized_source (alpha := alpha) hw hC (by linarith : 0 < B) ht
  have hphys := mul_le_mul_of_nonneg_left hle (by linarith : 0 ≤ 2*width+1)
  refine ⟨hk,hle.trans hk100,?_,hphys.trans hradius,?_⟩
  · linarith
  · exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hphys ha.le)
      (by positivity : 0 ≤ 2*(C*B))).trans hlegal

/-- The original twentieth-power cutoff implies every actual perturbation test
at the finer common mesh. No stronger hidden small-scale premise is needed. -/
theorem refined_tests (n : ℕ) {δ q width kap : ℝ}
    (hδ : 0 < δ) (hq : 1 ≤ q) (hw : 0 ≤ width) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hcut : PivotGeometryScale.geometryConstant n width*(1+2*width)^20 ≤ (1/δ)*kap^20) :
    PivotGeometryScale.Tests n (δ/q) kap width := by
  have hq0 : 0 < q := by linarith
  have hscale : δ/q ≤ δ := (div_le_iff₀ hq0).mpr (by nlinarith)
  apply PivotGeometryScale.tests_of_original_twentieth n (div_pos hδ hq0) hk hk1 hw
  apply hcut.trans
  gcongr

end
end KakeyaFormal.MarkedNormalizationKappa
