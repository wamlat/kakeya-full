import LowerDensityEstimate
import AdmissiblePivotSlabs

/-! Actual coarse families and original spatial/marked pruning for every p>0.
The per-tube lower-density adapter replaces Jensen; all original geometric
constructions and the exact cutoff powers are retained without new log losses. -/
namespace KakeyaFormal.PositiveDensityPruning
open Finset Coarsening CapThinningGeometry CoarseFamily HeavyIncidence
open PrunedIncidence KakeyaFormal.Localization MarkedPruningAssembly TransverseAngles MarkedSubsetSamples
open scoped BigOperators
noncomputable section
open Classical

/-- The genuine coarse family has a lower density on every tube, so positive
powers suffice. No average-density Jensen argument is used. -/
theorem coarse_union_estimate {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) (hp : 0 < p)
    (width R : ℝ) (hw : 0 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) {δ r s A : ℝ},
      0 < δ → δ ≤ r → r ≤ 1 → 0 ≤ s → 1 ≤ A →
      F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, s ≤ δ*((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^m*r^(-d+eps)*s^p*M ≤ ((F.unionCells.image (coarseLabel δ r)).card:ℝ) := by
  let W := width+(k+1:ℕ)/2
  let geom : Normalization := {
    width := max 1 W
    separation := 2/((k:ℝ)+1)
    radius := max 1 R
    width_pos := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    separation_pos := by positivity
    radius_pos := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  }
  let K := fiberConstant (k+1) width
  let T := thinningRetentionConstant k m
  let B := max 1 (thinningCapConstant k m)
  have hK : 0 < K := fiberConstant_pos (k+1) hw
  have hT : 0 < T := by
    have hpack := ProjectiveGeometry.packingConstant_ge_one k
    dsimp [T,thinningRetentionConstant]
    positivity
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  obtain ⟨c,hc,hestimate⟩ := LowerDensityEstimate.lower_density hbase hp geom eps heps
  refine ⟨c*B⁻¹/(K^p*T),by positivity,?_⟩
  intro M F δ r s A hδ hdr hr1 hs hA hadm hbounded hcap hdense
  have hr := hδ.trans_le hdr
  obtain ⟨N,e,_,G,hN,_,hshades,hGadm,hGsep,hGbound,hGcap,hU⟩ :=
    thinned_coarse_family F hδ hdr hr1 hm hA hw hadm hbounded hcap
  have hdensity := selected_coarse_density F G e hδ hdr hw hadm hshades hdense
  have hGadmissible : G.Admissible geom.width r := by
    intro i q hq
    obtain ⟨t,ht,hqt⟩ := hGadm i q hq
    refine ⟨t,ht,hqt.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right 1 W) hr.le
  have hGbounded : G.Bounded geom.radius := fun i => (hGbound i).trans (le_max_right _ _)
  have hcum : (s/K)*N ≤ r*∑ i, ((G.shade i).card:ℝ) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hdensity i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      ← Finset.mul_sum,mul_comm] using hh
  let H : CumulativeConfiguration (k+1) geom m := {
    M := N
    δ := r
    s := s/K
    A := B
    family := G
    scale_pos := hr
    scale_le_one := hr1
    density_nonneg := div_nonneg hs hK.le
    cap_ge_one := le_max_left _ _
    admissible := hGadmissible
    separated := hGsep
    bounded := hGbounded
    cap_bound := hGcap
    cumulative := hcum
  }
  have hh := hestimate H hdensity
  change c*B⁻¹*r^(m-d+eps)*(s/K)^p*N ≤ (G.unionCells.card:ℝ) at hh
  have hcoef : 0 ≤ c*B⁻¹*r^(m-d+eps)*(s/K)^p := by positivity
  have hNbound := mul_le_mul_of_nonneg_left hN hcoef
  have hid := coarse_estimate_identity (m := m) (d := d) (eps := eps) (p := p)
    (c := c) (A := A) (B := B) (T := T) (M := (M:ℝ)) hδ hr hs hK
  rw [hid] at hNbound
  exact (hNbound.trans hh).trans (by exact_mod_cast Finset.card_le_card hU)


/-- The actual heavy-cell excess contradiction with unchanged cutoff power. -/
theorem discrete_heavy_mass_bound {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) (hp : 0 < p)
    (width R : ℝ) (hw : 0 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) (E : Finset (Cell (k+1)))
      {δ r L A eta lam : ℝ}, 0 < δ → δ ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ A →
      0 < eta → 0 < lam → F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam) →
      K*(E.card : ℝ)*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/(M : ℝ) ≤ L →
      δ*∑ i, ((heavyShade F E δ r L d i).card : ℝ) ≤ eta*lam*M := by
  obtain ⟨c,hc,hcoarse⟩ := coarse_union_estimate hbase hm hp width R hw eps heps
  refine ⟨2/(c/(4*(2:ℝ)^p)),by positivity,?_⟩
  intro M F E δ r L A eta lam hδ hdr hr1 hL0 hA heta hlam hadm hbounded hcap hupper hL
  exact calibrated_mass_bound hc heps.le hcoarse F E hδ hdr hr1 hL0 hA heta hlam hadm hbounded hcap hupper hL


/-- Literal all-scale original survivors with any marked-fraction loss budget. -/
theorem discrete_spatial_pruning_budget {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d)
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



/-- Actual original marked recovery, valid for every positive base density power. -/
theorem marked_recovery {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) (hp : 0 < p) (hd : 0 ≤ d)
    (width R : ℝ) (hw : 0 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) (E : Finset (Cell (k+1)))
      (marks : Fin M → Finset (Cell (k+1))) {δ A lam xi B alpha theta : ℝ},
      0 < δ → δ ≤ 1 → 1 ≤ A → 0 < lam → 0 < xi → 0 < M → 0 ≤ B →
      (∀ i, F.shade i ⊆ E) → F.Admissible width δ → F.Separated δ → F.Bounded R →
      F.CapBound δ m A → F.Comparable δ lam → (∀ i, marks i ⊆ F.shade i) →
      xi*lam*(M : ℝ)/δ ≤ ∑ i, ((marks i).card : ℝ) →
      (∀ z ∈ DensityBroadnessRecovery.cells marks, ∀ v : Space (k+1), ‖v‖=1 →
        (((incident (markedFamily F marks) z).filter
          (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
            ((incident (markedFamily F marks) z).card : ℝ)/10) →
      (∀ i x r, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
          B*r^alpha*((F.shade i).card : ℝ)) →
      ∃ J : ℕ, (J : ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
        let eta := (xi/100)/((J : ℝ)+1)
        let L := max 1 (K*(E.card : ℝ)*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/(M : ℝ))
        let O := PrunedIncidence.family F E δ L d J
        O.tube=F.tube ∧ (∀ i, O.shade i ⊆ F.shade i) ∧ O.unionCells ⊆ E ∧
        δ*∑ i, ((F.shade i \ O.shade i).card : ℝ) ≤ (xi/100)*lam*(M : ℝ) ∧
        (∀ x : Space (k+1), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
          ((BallPruning.ballCells O.unionCells δ x r).card : ℝ) ≤
            (BallPruning.coverConstant (k+1) 1*(2:ℝ)^d*L)*(r/δ)^d) ∧
        Nonempty (RecoveredInput F O marks E δ lam xi width R m A B alpha theta) := by
  obtain ⟨K,hK,hprune⟩ := discrete_spatial_pruning_budget hbase hm hp hd width R hw eps heps
  refine ⟨K,hK,?_⟩
  intro M F E marks δ A lam xi B alpha theta hδ hδ1 hA hlam hxi hM hB hE hadm hsep hbounded hcap hcomp hmarks hW hbroad hends
  have hupper (i) : δ*((F.shade i).card : ℝ) ≤ 2*lam := by
    have hh := (mul_le_mul_of_nonneg_left (hcomp i).2 hδ.le)
    have hid : δ*(2*lam/δ)=2*lam := by field_simp
    simpa only [hid] using hh
  obtain ⟨J,hlog,htube,hsub,hOE,hdel,hball⟩ := hprune F E hδ hδ1 hA hlam
    (by positivity : 0 < xi/100) hE hadm hbounded hcap hupper
  refine ⟨J,hlog,?_⟩
  intro eta L O
  exact ⟨htube,hsub,hOE,hdel,hball,recover_pruned F O marks E hδ hlam hxi hM hB
    hcomp hadm hsep hbounded hcap hsub hOE hmarks hW hdel hbroad hends⟩


end
end KakeyaFormal.PositiveDensityPruning
