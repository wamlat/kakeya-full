import HeavyIncidence

/-! Finite simultaneous deletion across the actual selected scales, preserving
total shading incidence while obtaining the constructed spatial ball bounds. -/
namespace KakeyaFormal.PrunedIncidence
open Finset Coarsening HeavyIncidence KakeyaFormal.Localization
open scoped BigOperators
noncomputable section
open Classical

def family {k M : ℕ} (F : TubeFamily k M) (E : Finset (Cell k))
    (δ L d : ℝ) (J : ℕ) : TubeFamily k M :=
  ⟨F.tube,fun i => F.shade i ∩ BallPruning.survivors E δ L d J⟩

/-- Every deleted incidence belongs to a heavy cell at an actual tested scale. -/
theorem deleted_subset {k M : ℕ} (F : TubeFamily k M) (E : Finset (Cell k))
    (δ L d : ℝ) (J : ℕ) (hE : ∀ i, F.shade i ⊆ E) (i : Fin M) :
    F.shade i \ (family F E δ L d J).shade i ⊆
      (range (J+1)).biUnion (fun j => heavyShade F E δ (radius J j) L d i) := by
  intro q hq
  have hqi := (mem_sdiff.mp hq).1
  have hnot : q ∉ BallPruning.survivors E δ L d J := by
    intro hh
    exact (mem_sdiff.mp hq).2 (mem_inter.mpr ⟨hqi,hh⟩)
  have hfail : ¬ ∀ j ≤ J,
      ((E.filter (fun p => coarseLabel δ (radius J j) p = coarseLabel δ (radius J j) q)).card : ℝ) ≤
        L*(radius J j/δ)^d := by
    intro hall
    exact hnot (mem_filter.mpr ⟨hE i hqi,hall⟩)
  push Not at hfail
  obtain ⟨j,hj,hheavy⟩ := hfail
  refine mem_biUnion.mpr ⟨j,mem_range.mpr (by omega),mem_filter.mpr ⟨hqi,?_⟩⟩
  exact mem_filter.mpr ⟨mem_image.mpr ⟨q,hE i hqi,rfl⟩,hheavy⟩

/-- Finite union counting bounds actual incidence deletion by the sum of the
individual scale losses; no independence or disjointness is assumed. -/
theorem deletion_mass {k M : ℕ} (F : TubeFamily k M) (E : Finset (Cell k))
    {δ L d eta lam : ℝ} {J : ℕ} (hδ : 0 ≤ δ) (hE : ∀ i, F.shade i ⊆ E)
    (hmass : ∀ j ≤ J,
      δ*∑ i, ((heavyShade F E δ (radius J j) L d i).card : ℝ) ≤ eta*lam*M) :
    δ*∑ i, (((F.shade i) \ (family F E δ L d J).shade i).card : ℝ) ≤
      ((J : ℝ)+1)*eta*lam*M := by
  have hcard (i : Fin M) : (((F.shade i) \ (family F E δ L d J).shade i).card : ℝ) ≤
      ∑ j ∈ range (J+1), ((heavyShade F E δ (radius J j) L d i).card : ℝ) := by
    exact_mod_cast (card_le_card (deleted_subset F E δ L d J hE i)).trans card_biUnion_le
  calc
    _ ≤ δ*∑ i, ∑ j ∈ range (J+1), ((heavyShade F E δ (radius J j) L d i).card : ℝ) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => hcard i) hδ
    _ = ∑ j ∈ range (J+1), δ*∑ i, ((heavyShade F E δ (radius J j) L d i).card : ℝ) := by
      rw [sum_comm,mul_sum]
    _ ≤ ∑ j ∈ range (J+1), eta*lam*M := sum_le_sum fun j hj => hmass j (by have := mem_range.mp hj; omega)
    _ = ((J : ℝ)+1)*eta*lam*M := by simp; ring

/-- Half the original normalized total incidence survives after summing the
scale budgets eta=1/(2(J+1)). -/
theorem retains_half {k M : ℕ} (F : TubeFamily k M) (E : Finset (Cell k))
    {δ L d lam : ℝ} {J : ℕ} (hδ : 0 ≤ δ) (hE : ∀ i, F.shade i ⊆ E)
    (hlower : lam*(M : ℝ) ≤ δ*∑ i, ((F.shade i).card : ℝ))
    (hmass : ∀ j ≤ J,
      δ*∑ i, ((heavyShade F E δ (radius J j) L d i).card : ℝ) ≤
        (1/(2*((J : ℝ)+1)))*lam*M) :
    lam*(M : ℝ)/2 ≤ δ*∑ i, (((family F E δ L d J).shade i).card : ℝ) := by
  have hdel := deletion_mass F E hδ hE hmass
  have hpart (i : Fin M) : (((F.shade i) \ (family F E δ L d J).shade i).card : ℝ) +
      (((family F E δ L d J).shade i).card : ℝ) = (F.shade i).card := by
    exact_mod_cast card_sdiff_add_card_eq_card (inter_subset_left : (family F E δ L d J).shade i ⊆ F.shade i)
  have hsum : (∑ i, (((F.shade i) \ (family F E δ L d J).shade i).card : ℝ)) +
      (∑ i, (((family F E δ L d J).shade i).card : ℝ)) = ∑ i, ((F.shade i).card : ℝ) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun i _ => hpart i
  have hid : ((J : ℝ)+1)*(1/(2*((J : ℝ)+1)))*lam*M = lam*(M : ℝ)/2 := by field_simp
  rw [hid] at hdel
  nlinarith


/-- The full spatial pruning construction from the base estimate. A single
explicit cutoff retains half total incidence and controls every ball at every
radius δ≤rho≤1. All scales and actual survivor shadings are constructed. -/
theorem discrete_spatial_pruning {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (width R : ℝ) (hw : 0 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) (E : Finset (Cell (k+1)))
      {δ A lam : ℝ}, 0 < δ → δ ≤ 1 → 1 ≤ A → 0 < lam →
      (∀ i, F.shade i ⊆ E) → F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, lam ≤ δ*((F.shade i).card : ℝ)) →
      (∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam) →
      ∃ J : ℕ, (J : ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
        let eta := 1/(2*((J : ℝ)+1))
        let L := max 1 (K*(E.card : ℝ)*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/(M : ℝ))
        let G := family F E δ L d J
        G.tube = F.tube ∧ (∀ i, G.shade i ⊆ F.shade i) ∧ G.unionCells ⊆ E ∧
        lam*(M : ℝ)/2 ≤ δ*∑ i, ((G.shade i).card : ℝ) ∧
        ∀ x : Space (k+1), ∀ rho : ℝ, δ ≤ rho → rho ≤ 1 →
          ((BallPruning.ballCells G.unionCells δ x rho).card : ℝ) ≤
            (BallPruning.coverConstant (k+1) 1*(2:ℝ)^d*L)*(rho/δ)^d := by
  obtain ⟨K,hK,hheavy⟩ := discrete_heavy_mass_bound hbase hm hp width R hw eps heps
  refine ⟨K,hK,?_⟩
  intro M F E δ A lam hδ hδ1 hA hlam hE hadm hbounded hcap hlower hupper
  obtain ⟨J,hbottom,hbottom2,hlog⟩ := ScaleChoice.dyadic_depth hδ hδ1
  refine ⟨J,hlog,?_⟩
  intro eta L G
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hL : 0 ≤ L := (show (0 : ℝ) ≤ 1 by norm_num).trans (le_max_left _ _)
  have hmass (j : ℕ) (hj : j ≤ J) :
      δ*∑ i, ((heavyShade F E δ (radius J j) L d i).card : ℝ) ≤ eta*lam*M := by
    apply hheavy F E hδ (hbottom.trans (radius_mono J (Nat.zero_le j)))
      (by simpa using radius_mono J hj) hL hA heta hlam hadm hbounded hcap hupper
    exact le_max_right _ _
  have htotal : lam*(M : ℝ) ≤ δ*∑ i, ((F.shade i).card : ℝ) := by
    have hh := sum_le_sum (s := univ) (fun i _ => hlower i)
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,← mul_sum,mul_comm] using hh
  have hGS : G.unionCells ⊆ BallPruning.survivors E δ L d J := by
    intro q hq
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
    exact (mem_inter.mp hi).2
  refine ⟨rfl,fun _ => inter_subset_left,hGS.trans (BallPruning.survivors_subset E δ L d J),
    retains_half F E hδ.le hE htotal hmass,?_⟩
  intro x rho hr hr1
  have hball := BallPruning.dyadic_ball_bound (BallPruning.survivors E δ L d J) hδ hbottom2.le hL hd
    (fun j hj z => BallPruning.survivors_fiber_bound E hδ hL j hj z) x hr hr1
  have hsub : BallPruning.ballCells G.unionCells δ x rho ⊆
      BallPruning.ballCells (BallPruning.survivors E δ L d J) δ x rho := filter_subset_filter _ hGS
  exact (show ((BallPruning.ballCells G.unionCells δ x rho).card : ℝ) ≤
      ((BallPruning.ballCells (BallPruning.survivors E δ L d J) δ x rho).card : ℝ) by
      exact_mod_cast card_le_card hsub).trans hball

end
end KakeyaFormal.PrunedIncidence

#print axioms KakeyaFormal.PrunedIncidence.deleted_subset
#print axioms KakeyaFormal.PrunedIncidence.deletion_mass
#print axioms KakeyaFormal.PrunedIncidence.retains_half
#print axioms KakeyaFormal.PrunedIncidence.discrete_spatial_pruning
