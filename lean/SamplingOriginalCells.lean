import SamplingHighDensity
import TransformedGridSupport

/-! Actual high-density measurable sampling returns a lower bound for the
original restricted piece's cell count. The support comparison is proved from
the literal anisotropic image of those cells, with no overlap assertion about
pulled-back new cubes and no identification with normalized volume. -/
namespace KakeyaFormal.SamplingOriginalCells
open Finset SamplingNormalizedMeans SamplingSupport TransformedGridSupport
noncomputable section

theorem construct {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 0 ≤ m) (hpExp : 1 ≤ pExp) (hd : 0 ≤ d) (hqExp : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m+1)
    (width R c₀ C₀ B₀ K₀ xi₀ alpha beta bLog kLog xLog eps : ℝ)
    (hw : 0 ≤ width) (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (horder : c₀ ≤ C₀)
    (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hxi₀ : 0 < xi₀)
    (ha : 0 < alpha) (hbeta : 0 < beta)
    (hbLog : 0 ≤ bLog) (hkLog : 0 ≤ kLog) (hxLog : 0 ≤ xLog) (heps : 0 < eps) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (Full G : Fin M → Set (Space (k+2)))
      (u : Space (k+2)) (q : Cell (k+1)) (S : Finset (Cell (k+2)))
      {δ tau W lam xi B K A : ℝ},
      0 < δ → 0 < tau → tau ≤ 1 → 1 ≤ W →
      (∀ i, Full i ⊆ (pieceMap u tau W q) '' GridShadingMeasure.cellUnion δ S) →
      Input F Full G (δ/tau) width R lam c₀ C₀ xi B alpha K beta →
      F.Separated (δ/tau) → F.CapBound (δ/tau) m A → 1 ≤ A → δ/tau ≤ δ₀ →
      (1/(δ/tau))^(-(1:ℝ)/3) ≤ lam → xi ≤ 1 →
      B ≤ B₀*(Real.log (2/(δ/tau)))^bLog → K ≤ K₀*(Real.log (2/(δ/tau)))^kLog →
      xi₀*(Real.log (2/(δ/tau)))^(-xLog) ≤ xi →
      c*A⁻¹*(δ/tau)^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤ (S.card:ℝ) := by
  obtain ⟨δ₀,hδ₀,hδ₀1,c,hc,hmain⟩ := SamplingHighDensity.all_exponents hbase hlift hm hpExp hd hqExp hD
    width R c₀ C₀ B₀ K₀ xi₀ alpha beta bLog kLog xLog eps
    hw hc₀ hC₀ horder hB₀ hK₀ hxi₀ ha hbeta hbLog hkLog hxLog heps
  let cellFactor : ℝ := (((2*(k+2)+3)^(k+2):ℕ):ℝ)
  have hfactor : 0 < cellFactor := by dsimp [cellFactor]; positivity
  refine ⟨δ₀,hδ₀,hδ₀1,c/cellFactor,div_pos hc hfactor,?_⟩
  intro M F Full G u q S δ tau W lam xi B K A hδ htau htau1 hW hFull
    h hsep hcap hA hscale hlam hxi1 hB hK hxi
  have hbound := hmain F Full G h hsep hcap hA hscale hlam hxi1 hB hK hxi
  have hsupport := positive_support_card u (width:=width) (R:=R)
    hδ htau htau1 hW q S F.tube Full hFull
  have hcard : ((support F.tube Full (δ/tau) width R).card:ℝ) ≤ (S.card:ℝ)*cellFactor := by
    have hn : (support F.tube Full (δ/tau) width R).card ≤ S.card*(2*(k+2)+3)^(k+2) := by
      simpa only [Nat.add_assoc] using hsupport
    simpa only [Nat.cast_mul,cellFactor] using (Nat.cast_le (α:=ℝ)).mpr hn
  apply le_of_mul_le_mul_right ?_ hfactor
  calc
    _ = c*A⁻¹*(δ/tau)^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) := by
      field_simp
    _ ≤ _ := hbound.trans hcard

end
end KakeyaFormal.SamplingOriginalCells
