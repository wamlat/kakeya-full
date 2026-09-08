import MarkedPruningAssembly
import MarkedPivotSelection
import PivotGeometryScale

/-! Actual output selection from the original marked configuration after the
literal spatial pruning and marked recovery. Original comparison parameters,
pruned union, injective tube map, legal samples and selected fibers stay linked. -/
namespace KakeyaFormal.PrunedPivotSelection
open Finset TransverseAngles LegalAngleSamples ActualLabelSelection AngleFiberSelection
open MarkedPruningAssembly PivotSelectionBudgets PivotOutputLowerBound
open scoped BigOperators
noncomputable section
open Classical

/-- Apply the genuine legal-sample and collision selection theorem to an actual
recovered input, then express both density losses in the ORIGINAL parameters. -/
theorem recovered_selection {k M : ℕ} {F O : TubeFamily (k+2) M}
    {marks : Fin M → Finset (Cell (k+2))} {E : Finset (Cell (k+2))}
    {δ lam xi width R m A B alpha theta : ℝ}
    (G : RecoveredInput F O marks E δ lam xi width R m A B alpha theta)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hxi : 0 < xi) (hM : 0 < M)
    (hw : (1:ℝ)/12 ≤ width) (hB : 1 ≤ B) (ha : 0 < alpha)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hsmall : (6*width/(PivotKappa.choice width (2*B) theta⁻¹ alpha 1))*δ ≤ 1/2) :
    let kappa := PivotKappa.choice width (2*B) theta⁻¹ alpha 1
    let hk := (MarkedSubsetSamples.fixed_radius_choice (by linarith : 0 ≤ width)
      (by linarith : 1 ≤ 2*B) ha htheta htheta1).1
    ∃ S : SampleSystem G.family G.family.unionCells δ G.density kappa width,
    ∃ P : Selection S hk (by linarith : 0 ≤ width) G.admissible,
      let σ := ((2^P.level:ℕ):ℝ)*δ
      lam^2/(2048*LegalSampleOutputs.outputConstant (k+2) width) < σ ∧
      σ ≤ fiberCoefficient (k+2) width/kappa ∧
      (outputCoefficient k width/65536)*kappa^(5*(k+1))*xi^2*lam^8*(M : ℝ)^2/
        (σ^2*δ^4*(pivotLog δ)^3*(E.card : ℝ)) ≤ ((outputSupport P.retained).card : ℝ) := by
  intro kappa hk
  have hw0 : 0 ≤ width := by linarith
  have hB' : 1 ≤ 2*B := by linarith
  have hI : 0 < xi*lam*(M : ℝ)/(8*δ) := by positivity
  have hH : (G.family.unionCells.card : ℝ) ≤ E.card := by exact_mod_cast card_le_card G.union_subset_E
  obtain ⟨S,P,hlo,hhi,hQ⟩ := MarkedPivotSelection.construct G.family G.marks G.family.unionCells
    hδ G.density_pos hw hB' ha htheta htheta1 hI G.comparison_pos G.admissible G.comparable
    G.separated G.marks_subset G.marked_mass hH (fun z _ v hv => G.marked_broad z v hv) G.two_ends hsmall
  have hdensity : lam/2 ≤ G.density := by
    rcases G.density_choice with h | h
    · rw [h]
    · rw [h]; linarith
  let σ := ((2^P.level:ℕ):ℝ)*δ
  have hσ : 0 < σ := by
    have hh : (0:ℝ) < (2^P.level:ℕ) := by exact_mod_cast pow_pos (by omega : 0 < (2:ℕ)) P.level
    dsimp [σ]
    positivity
  have hlog := zero_lt_one.trans_le (pivotLog_ge_one hδ hδ1)
  have hC := LegalSampleOutputs.outputConstant_pos (k+2) hw0
  have hQcoef := outputCoefficient_pos k hw0
  refine ⟨S,P,?_,hhi,?_⟩
  · have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ lam/2) hdensity 2
    have hh := div_le_div_of_nonneg_right hpow (by positivity : 0 ≤ 512*LegalSampleOutputs.outputConstant (k+2) width)
    have hid : lam^2/(2048*LegalSampleOutputs.outputConstant (k+2) width)=
        (lam/2)^2/(512*LegalSampleOutputs.outputConstant (k+2) width) := by field_simp; ring
    exact (hid ▸ hh).trans_lt hlo
  · calc
      _ = (outputCoefficient k width/16)*kappa^(5*(k+1))*(lam/2)^6*
          (xi*lam*(M : ℝ)/(8*δ))^2/(σ^2*δ^2*(pivotLog δ)^3*(E.card : ℝ)) := by
        field_simp
        ring
      _ ≤ (outputCoefficient k width/16)*kappa^(5*(k+1))*G.density^6*
          (xi*lam*(M : ℝ)/(8*δ))^2/(σ^2*δ^2*(pivotLog δ)^3*(E.card : ℝ)) := by
        gcongr
      _ ≤ _ := hQ

/-- End-to-end original marked input to the actual sample system and selected
whole fibers. The constant precedes all original configurations and marked
fractions; no angle count, sample population, or collision estimate is assumed. -/
theorem construct {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (width R : ℝ) (hw : (1:ℝ)/12 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B alpha theta : ℝ},
      0 < δ → δ ≤ 1 → 1 ≤ A → 0 < lam → 0 < xi → 0 < M → 1 ≤ B →
      0 < alpha → 0 < theta → theta ≤ 1 →
      (∀ i, F.shade i ⊆ E) → F.Admissible width δ → F.Separated δ → F.Bounded R →
      F.CapBound δ m A → F.Comparable δ lam → (∀ i, marks i ⊆ F.shade i) →
      xi*lam*(M : ℝ)/δ ≤ ∑ i, ((marks i).card : ℝ) →
      (∀ z ∈ DensityBroadnessRecovery.cells marks, ∀ v : Space (k+2), ‖v‖=1 →
        (((incident (MarkedSubsetSamples.markedFamily F marks) z).filter
          (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
            ((incident (MarkedSubsetSamples.markedFamily F marks) z).card : ℝ)/10) →
      (∀ i x r, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
          B*r^alpha*((F.shade i).card : ℝ)) →
      (6*width/(PivotKappa.choice width (2*B) theta⁻¹ alpha 1))*δ ≤ 1/2 →
      ∃ J : ℕ, (J : ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
        let eta := (xi/100)/((J : ℝ)+1)
        let L := max 1 (K*(E.card : ℝ)*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/(M : ℝ))
        let O := PrunedIncidence.family F E δ L d J
        O.tube=F.tube ∧ (∀ i, O.shade i ⊆ F.shade i) ∧ O.unionCells ⊆ E ∧
        δ*∑ i, ((F.shade i \ O.shade i).card : ℝ) ≤ (xi/100)*lam*(M : ℝ) ∧
        (∀ x : Space (k+2), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
          ((BallPruning.ballCells O.unionCells δ x r).card : ℝ) ≤
            (BallPruning.coverConstant (k+2) 1*(2:ℝ)^d*L)*(r/δ)^d) ∧
        ∃ G : RecoveredInput F O marks E δ lam xi width R m A B alpha theta,
          let kappa := PivotKappa.choice width (2*B) theta⁻¹ alpha 1
          ∃ hk : 0 < kappa,
          ∃ S : SampleSystem G.family G.family.unionCells δ G.density kappa width,
          ∃ P : Selection S hk (by linarith : 0 ≤ width) G.admissible,
            let σ := ((2^P.level:ℕ):ℝ)*δ
            lam^2/(2048*LegalSampleOutputs.outputConstant (k+2) width) < σ ∧
            σ ≤ fiberCoefficient (k+2) width/kappa ∧
            (outputCoefficient k width/65536)*kappa^(5*(k+1))*xi^2*lam^8*(M : ℝ)^2/
              (σ^2*δ^4*(pivotLog δ)^3*(E.card : ℝ)) ≤ ((outputSupport P.retained).card : ℝ) := by
  have hw0 : 0 ≤ width := by linarith
  obtain ⟨K,hK,hprune⟩ := MarkedPruningAssembly.construct hbase hm hp hd width R hw0 eps heps
  refine ⟨K,hK,?_⟩
  intro M F E marks δ A lam xi B alpha theta hδ hδ1 hA hlam hxi hM hB ha htheta htheta1 hE hadm hsep hbounded hcap hcomp hmarks hW hbroad hends hsmall
  obtain ⟨J,hlog,htube,hsub,hOE,hdel,hball,⟨G⟩⟩ := hprune F E marks hδ hδ1 hA hlam hxi hM
    (by linarith : 0 ≤ B) hE hadm hsep hbounded hcap hcomp hmarks hW hbroad hends
  refine ⟨J,hlog,?_⟩
  intro eta L O
  refine ⟨htube,hsub,hOE,hdel,hball,G,?_⟩
  intro kappa
  let hk := (MarkedSubsetSamples.fixed_radius_choice hw0 (by linarith : 1 ≤ 2*B) ha htheta htheta1).1
  refine ⟨hk,?_⟩
  exact recovered_selection G hδ hδ1 hlam hxi hM hw hB ha htheta htheta1 hsmall


/-- An optional single original-scale cutoff supplies the precise collision
condition in `construct` and all subsequent normalized-lift perturbation tests.
Its kappa uses the recovered full two-ends constant 2B at the original radius. -/
theorem geometry_tests (n : ℕ) {δ width B alpha theta : ℝ}
    (hδ : 0 < δ) (hw : 0 ≤ width) (hB : 1 ≤ B) (ha : 0 < alpha)
    (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hscale : PivotGeometryScale.geometryConstant n width*(1+2*width)^20 ≤
      (1/δ)*(PivotKappa.choice width (2*B) theta⁻¹ alpha 1)^20) :
    PivotGeometryScale.Tests n δ (PivotKappa.choice width (2*B) theta⁻¹ alpha 1) width := by
  obtain ⟨hk,hk100,_⟩ := MarkedSubsetSamples.fixed_radius_choice hw
    (by linarith : 1 ≤ 2*B) ha htheta htheta1
  exact PivotGeometryScale.tests_of_original_twentieth n hδ hk (by linarith) hw hscale

end
end KakeyaFormal.PrunedPivotSelection

#print axioms KakeyaFormal.PrunedPivotSelection.recovered_selection
#print axioms KakeyaFormal.PrunedPivotSelection.construct

#print axioms KakeyaFormal.PrunedPivotSelection.geometry_tests
