import MarkedPruningAssembly
import PrunedScaleTransport

/-! The actual recovered family inherits the normalized all-radius spatial
bound from the literal original pruning output. -/
namespace KakeyaFormal.RecoveredNormalizedBall
open Finset BallPruning PrunedGraphLift MarkedPruningAssembly
noncomputable section
open Classical

/-- The sparse-mark recovery changes neither integer labels nor the mesh.
Its literal full-union inclusion supplies the exact spatial input needed by
the selected normalized graph families. -/
theorem recovered_ball_bound {n M J : ℕ} (F : TubeFamily n M)
    (E : Finset (Cell n)) (marks : Fin M → Finset (Cell n))
    {δ L d width baseRadius lam xi m A B alpha theta : ℝ}
    (G : RecoveredInput F (PrunedIncidence.family F E δ L d J) marks E
      δ lam xi width baseRadius m A B alpha theta)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hadm : F.Admissible width δ) (hbounded : F.Bounded baseRadius)
    (hsmall : ∀ x : Space n, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((ballCells (PrunedIncidence.family F E δ L d J).unionCells δ x r).card:ℝ) ≤
        (coverConstant n 1*(2:ℝ)^d*L)*(r/δ)^d) :
    ∀ x : Space n, ∀ r : ℝ, δ/(1+2*width) ≤ r →
      ((G.family.unionCells.filter
        (fun z => dist (cellCenter (δ/(1+2*width)) z) x ≤ r)).card:ℝ) ≤
        (spatialConstant n width baseRadius d*L)*(r/(δ/(1+2*width)))^d := by
  have hall := PrunedScaleTransport.pruned_normalized_ball_bound F E
    hδ hδ1 hw hL hd (by positivity : 0 < 1+2*width) hadm hbounded hsmall
  intro x r hr
  have hsub := filter_subset_filter (p:=fun z => dist (cellCenter (δ/(1+2*width)) z) x ≤ r)
    G.union_subset_pruned
  have hh : ((G.family.unionCells.filter
        (fun z => dist (cellCenter (δ/(1+2*width)) z) x ≤ r)).card:ℝ) ≤
      ((ballCells (PrunedIncidence.family F E δ L d J).unionCells (δ/(1+2*width)) x r).card:ℝ) := by
    exact_mod_cast card_le_card hsub
  exact hh.trans (hall x r hr)

/-- The exact graph cap coefficient built from this recovered spatial bound
meets the normalized discrete estimate's A≥1 requirement. -/
theorem recovered_cap_coefficient_ge_one (n : ℕ) {width baseRadius d L : ℝ}
    (hw : 0 ≤ width) (hd : 0 ≤ d) (hL : 1 ≤ L) :
    1 ≤ (spatialConstant n width baseRadius d*L)*(16+2*(2*width+(n:ℝ)/2))^d := by
  have hh := lifted_cap_coefficient_ge_one (k:=n) (width:=width) (R:=baseRadius)
    (V:=1) (C:=2*width+(n:ℝ)/2) hd hL (by norm_num) (by positivity)
  norm_num at hh
  exact hh

end
end KakeyaFormal.RecoveredNormalizedBall
