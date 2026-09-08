import TransformedGridSupport
import SamplingRealization
import SamplingDichotomy

/-! Actual sampled and low-cell populations compared with original angular-piece
cell counts. The available support and its size are constructed from the exact
transformed sets; no occupied-grid comparison is assumed. -/
namespace KakeyaFormal.TransformedSamplingPopulation
open TransformedGridSupport GridShadingMeasure SamplingSupport
open SamplingRealization KakeyaSamplingApplication KakeyaSamplingDichotomy
open MeasureTheory
open scoped BigOperators
noncomputable section
open Classical

/-- Every actual sampled union is bounded by the old piece count. This needs
no probability estimate because the outcome is literally indexed by that support. -/
theorem sampled_union_card {k M : ℕ} (u : Space (k+1)) {δ tau W width R : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (hW : 1 ≤ W)
    (q : Cell k) (S : Finset (Cell (k+1)))
    (tube : Fin M → UnitTube (k+1)) (Y : Fin M → Set (Space (k+1)))
    (hY : ∀ i, Y i ⊆ (pieceMap u tau W q) '' cellUnion δ S)
    (omega : Outcome (Fin M) ↥(support tube Y (δ/tau) width R)) :
    (full tube (support tube Y (δ/tau) width R) omega).unionCells.card ≤
      S.card*(2*(k+1)+3)^(k+1) :=
  (Finset.card_le_card (support_and_marks tube _ ∅ omega).1).trans
    (positive_support_card u hδ htau htau1 hW q S tube Y hY)

/-- The deterministic low-cell branch already implies a bound for the original
piece population. Otherwise the actual high cells carry half the marked mean.
Both probabilities are the literal measurable cell-intersection weights. -/
theorem low_count_or_high {k M : ℕ} (u : Space (k+1)) {δ tau W width R cutoff : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau) (htau1 : tau ≤ 1) (hW : 1 ≤ W)
    (hcut : 0 < cutoff) (q : Cell k) (S : Finset (Cell (k+1)))
    (tube : Fin M → UnitTube (k+1)) (Y G : Fin M → Set (Space (k+1)))
    (hGY : ∀ i, G i ⊆ Y i)
    (hY : ∀ i, Y i ⊆ (pieceMap u tau W q) '' cellUnion δ S) :
    let E := support tube Y (δ/tau) width R
    let markWeight : Fin M → ↥E → ℝ := fun i z => weight (G i) (δ/tau) z.val
    let mu := markedMean markWeight
    ((∑ z, mu z)/2 ≤ ∑ z ∈ low mu cutoff, mu z ∧
      (∑ z, mu z)/(2*cutoff) ≤ ((low mu cutoff).card:ℝ) ∧
      ((low mu cutoff).card:ℝ) ≤ (S.card:ℝ)*(((2*(k+1)+3)^(k+1):ℕ):ℝ)) ∨
    (∑ z, mu z)/2 ≤ ∑ z ∈ high mu cutoff, mu z := by
  dsimp only
  let E := support tube Y (δ/tau) width R
  let markWeight : Fin M → ↥E → ℝ := fun i z => weight (G i) (δ/tau) z.val
  have hvalid : ∀ i z, 0 ≤ markWeight i z := fun i z =>
    (coupled_weights (hGY i) (div_pos hδ htau) z.val).1
  obtain hlow | hhigh := marked_dichotomy markWeight hvalid hcut
  · refine Or.inl ⟨hlow.1,hlow.2,?_⟩
    have hsubset : (low (markedMean markWeight) cutoff).card ≤ E.card := by
      exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)
    have hc := hsubset.trans (positive_support_card u hδ htau htau1 hW q S tube Y hY)
    exact_mod_cast hc
  · exact Or.inr hhigh

end
end KakeyaFormal.TransformedSamplingPopulation

#print axioms KakeyaFormal.TransformedSamplingPopulation.sampled_union_card
#print axioms KakeyaFormal.TransformedSamplingPopulation.low_count_or_high
