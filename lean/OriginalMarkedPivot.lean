import OriginalPivotEnergy
import OriginalPivotScalar
import Endpoint

/-! Complete marked transverse pivot fourth-power estimate on original actual
configurations. The kappa used here is the explicit product choice and the
uniform threshold assumes fixed logarithmic concentration budgets. -/
namespace KakeyaFormal.OriginalMarkedPivot
open Finset OriginalPivotSlabs
noncomputable section
open Classical

/-- All finite selection, original spatial pruning, recovered markings,
selected lift cells, normalized colored families, high-cell pruning, actual
endpoint witnesses and final fourth-power substitutions are constructed inside
this theorem. Only the two explicit DiscreteEstimate inputs and the original
marked geometric hypotheses remain. This uses the formal product-kappa choice;
it does not assert equivalence with the manuscript's minimum-kappa convention. -/
theorem construct {k : ℕ} {m d d' p q : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p)
    (hlift : DiscreteEstimate (k+3) d d' q)
    (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d) (hq : 2 ≤ q)
    (width baseRadius : ℝ) (hw : (1:ℝ)/12 ≤ width)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (B₀ K₀ alpha bLog qLog : ℝ) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 ≤ bLog) (hlogq : 0 ≤ qLog) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta : ℝ},
      Hypotheses F E marks δ₀ δ A lam xi B theta width baseRadius m alpha B₀ K₀ bLog qLog →
      lam ≤ 1 → xi ≤ 1 →
      c*(kappa width B theta alpha)^(5*((k+1:ℕ):ℝ)+6*q+12)*A⁻¹*xi^(p+3)*
        (PivotSelectionBudgets.pivotLog δ)^(-(p+4))*δ^(-2*m-3-d'+3*eps)*
        lam^(p+2*q+4+2*eps)*((M:ℝ)*δ^m)^3 ≤ (E.card:ℝ)^4 := by
  have hw0 : 0 ≤ width := by linarith
  have hwp : 0 < width := by linarith
  obtain ⟨K,hK,δ₀,hδ₀,hδ₀1,hpackage⟩ := OriginalPivotSlabs.construct
    hbase hm hp hd width baseRadius hw eps heps B₀ K₀ alpha bLog qLog hB₀ hK₀ ha hb hlogq
  let geom : Normalization := {
    width := width
    separation := 1
    radius := max 1 baseRadius
    width_pos := hwp
    separation_pos := by norm_num
    radius_pos := zero_lt_one.trans_le (le_max_left _ _) }
  obtain ⟨cBase,hBase,hbaseBound⟩ := hbase geom eps heps
  have hlift' : DiscreteEstimate (k+3) d d' (q+eps) :=
    hlift.weaken_density (by linarith)
  obtain ⟨cClose,hClose,henergy⟩ := OriginalPivotEnergy.construct width baseRadius hw0 hd
    hlift' (by linarith : 1 ≤ q+eps) heps
  refine ⟨δ₀,hδ₀,hδ₀1,OriginalPivotScalar.coefficient k width K cBase cClose p q eps,
    OriginalPivotScalar.coefficient_pos k hw0 hK hBase hClose,?_⟩
  intro M F E marks δ A lam xi B theta h hlam1 hxi1
  obtain ⟨U⟩ := hpackage F E marks h
  obtain ⟨rho,hrho,hRho,hCloseBound⟩ := henergy K F E marks U
  let V : ShadedConfiguration (k+2) geom m := {
    M := M
    δ := δ
    lam := lam
    A := A
    family := F
    scale_pos := h.scale_pos
    scale_le_one := h.scale_small.trans hδ₀1
    density_pos := h.density_pos
    density_le_one := hlam1
    cap_ge_one := h.cap_coefficient
    admissible := h.admissible
    separated := by simpa only [geom,one_mul] using h.separated
    bounded := fun i => (h.bounded i).trans (le_max_right _ _)
    cap_bound := h.cap_bound
    comparable := h.comparable }
  have hUE : F.unionCells ⊆ E := by
    intro z hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    exact h.cover i hi
  have hbaseOriginal : cBase*A⁻¹*δ^(m-d+eps)*lam^p*(M:ℝ) ≤ (E.card:ℝ) :=
    (hbaseBound V).trans (by exact_mod_cast card_le_card hUE)
  exact OriginalPivotScalar.fourth_power U hK hBase hClose
    (zero_lt_one.trans_le h.cap_coefficient) h.density_pos h.marked_fraction_pos hxi1 h.count_pos
    hp hq heps.le heps1 hbaseOriginal hRho hCloseBound

end
end KakeyaFormal.OriginalMarkedPivot
