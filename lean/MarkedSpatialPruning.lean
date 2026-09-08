import PrunedIncidence

/-! Spatial pruning with an arbitrary prescribed incidence loss. The loss can
be chosen as a fixed fraction of the actual marked mass, rather than consuming
half the full incidence when the marks may be much sparser. -/
namespace KakeyaFormal.MarkedSpatialPruning
open Finset Coarsening HeavyIncidence PrunedIncidence KakeyaFormal.Localization
open scoped BigOperators
noncomputable section
open Classical

/-- The base estimate constructs the actual survivor family with any positive
full-incidence deletion budget. The constant is fixed before that budget and
before the actual family. Its cutoff has the precise inverse-budget power. -/
theorem discrete_spatial_pruning_budget {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (width R : ℝ) (hw : 0 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) (E : Finset (Cell (k+1)))
      {δ A lam loss : ℝ}, 0 < δ → δ ≤ 1 → 1 ≤ A → 0 < lam → 0 < loss →
      (∀ i, F.shade i ⊆ E) → F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, δ*((F.shade i).card:ℝ) ≤ 2*lam) →
      ∃ J : ℕ, (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
        let eta := loss/((J:ℝ)+1)
        let L := max 1 (K*(E.card:ℝ)*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/(M:ℝ))
        let G := PrunedIncidence.family F E δ L d J
        G.tube=F.tube ∧ (∀ i, G.shade i ⊆ F.shade i) ∧ G.unionCells ⊆ E ∧
        δ*∑ i, (((F.shade i) \ G.shade i).card:ℝ) ≤ loss*lam*(M:ℝ) ∧
        ∀ x : Space (k+1), ∀ rho : ℝ, δ ≤ rho → rho ≤ 1 →
          ((BallPruning.ballCells G.unionCells δ x rho).card:ℝ) ≤
            (BallPruning.coverConstant (k+1) 1*(2:ℝ)^d*L)*(rho/δ)^d := by
  obtain ⟨K,hK,hheavy⟩ := discrete_heavy_mass_bound hbase hm hp width R hw eps heps
  refine ⟨K,hK,?_⟩
  intro M F E δ A lam loss hδ hδ1 hA hlam hloss hE hadm hbounded hcap hupper
  obtain ⟨J,hbottom,hbottom2,hlog⟩ := ScaleChoice.dyadic_depth hδ hδ1
  refine ⟨J,hlog,?_⟩
  intro eta L G
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hL : 0 ≤ L := (show (0:ℝ) ≤ 1 by norm_num).trans (le_max_left _ _)
  have hmass (j : ℕ) (hj : j ≤ J) :
      δ*∑ i, ((heavyShade F E δ (radius J j) L d i).card:ℝ) ≤ eta*lam*M := by
    apply hheavy F E hδ (hbottom.trans (radius_mono J (Nat.zero_le j)))
      (by simpa using radius_mono J hj) hL hA heta hlam hadm hbounded hcap hupper
    exact le_max_right _ _
  have hdel := deletion_mass F E hδ.le hE hmass
  have hid : ((J:ℝ)+1)*eta*lam*M = loss*lam*M := by dsimp [eta]; field_simp
  rw [hid] at hdel
  have hGS : G.unionCells ⊆ BallPruning.survivors E δ L d J := by
    intro q hq
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
    exact (mem_inter.mp hi).2
  refine ⟨rfl,fun _ => inter_subset_left,hGS.trans (BallPruning.survivors_subset E δ L d J),hdel,?_⟩
  intro x rho hr hr1
  have hball := BallPruning.dyadic_ball_bound (BallPruning.survivors E δ L d J) hδ hbottom2.le hL hd
    (fun j hj z => BallPruning.survivors_fiber_bound E hδ hL j hj z) x hr hr1
  have hsub : BallPruning.ballCells G.unionCells δ x rho ⊆
      BallPruning.ballCells (BallPruning.survivors E δ L d J) δ x rho := filter_subset_filter _ hGS
  exact (Nat.cast_le.mpr (card_le_card hsub)).trans hball

/-- The displayed cutoff's loss dependence is exact, including losses that
depend on the original marked fraction. No new analytic estimate is needed. -/
theorem cutoff_budget_identity {loss p : ℝ} (hloss : 0 < loss) (J : ℕ) :
    (loss/((J:ℝ)+1))^(-(p+1)) = loss^(-(p+1))*((J:ℝ)+1)^(p+1) := by
  rw [Real.div_rpow hloss.le (by positivity : (0:ℝ) ≤ (J:ℝ)+1),
    Real.rpow_neg (by positivity : (0:ℝ) ≤ (J:ℝ)+1),div_inv_eq_mul]

end
end KakeyaFormal.MarkedSpatialPruning
