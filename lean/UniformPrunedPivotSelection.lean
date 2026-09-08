import PrunedPivotSelection

/-! Uniform small-scale original marked pruning and actual output selection.
Quantitative polylogarithmic budgets replace every explicit geometric smallness
hypothesis; the scale threshold precedes the later family and coefficients. -/
namespace KakeyaFormal.UniformPrunedPivotSelection
open Finset TransverseAngles LegalAngleSamples ActualLabelSelection AngleFiberSelection
open MarkedPruningAssembly PivotSelectionBudgets PivotOutputLowerBound
open scoped BigOperators
noncomputable section
open Classical

/-- The full two-ends coefficient doubles during marked recovery. The same
fixed scale threshold still controls every normalized geometric test. -/
theorem recovered_geometry (n : ℕ) {width B₀ K₀ alpha b q : ℝ}
    (hw : 0 ≤ width) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧ ∀ δ B theta : ℝ, 0 < δ → δ ≤ δ₀ →
      1 ≤ B → 0 < theta → theta ≤ 1 →
      B ≤ B₀*(Real.log (2/δ))^b → theta⁻¹ ≤ K₀*(Real.log (2/δ))^q →
      PivotGeometryScale.Tests n δ (PivotKappa.choice width (2*B) theta⁻¹ alpha 1) width := by
  obtain ⟨δ₀,hδ₀,hδ₀1,huniform⟩ := PivotGeometryScale.uniform_choice_tests n
    (B₀:=2*B₀) (K₀:=K₀) (beta:=1) hw (by positivity) hK₀ ha (by norm_num) hb hq
  refine ⟨δ₀,hδ₀,hδ₀1,?_⟩
  intro δ B theta hδ hsmall hB htheta htheta1 hBB hKK
  have hK : 1 ≤ theta⁻¹ := (one_le_inv₀ htheta).mpr htheta1
  have hBB' : 2*B ≤ (2*B₀)*(Real.log (2/δ))^b := by nlinarith
  exact huniform δ (2*B) theta⁻¹ hδ hsmall (by linarith) hK hBB' hKK

/-- Uniform original-input construction. Both the pruning constant and the
positive scale threshold are fixed before the original configuration, marked
fraction, B and theta. Actual sample and whole-fiber selection data is returned. -/
theorem construct {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+2) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (width R : ℝ) (hw : (1:ℝ)/12 ≤ width) (eps : ℝ) (heps : 0 < eps)
    (B₀ K₀ alpha b q : ℝ) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀)
    (ha : 0 < alpha) (hb : 0 ≤ b) (hq : 0 ≤ q) :
    ∃ K : ℝ, 0 < K ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {M : ℕ} (F : TubeFamily (k+2) M) (E : Finset (Cell (k+2)))
      (marks : Fin M → Finset (Cell (k+2))) {δ A lam xi B theta : ℝ},
      0 < δ → δ ≤ δ₀ → 1 ≤ A → 0 < lam → 0 < xi → 0 < M → 1 ≤ B →
      0 < theta → theta ≤ 1 →
      B ≤ B₀*(Real.log (2/δ))^b → theta⁻¹ ≤ K₀*(Real.log (2/δ))^q →
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
      PivotGeometryScale.Tests (k+2) δ (PivotKappa.choice width (2*B) theta⁻¹ alpha 1) width ∧
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
  obtain ⟨K,hK,hconstruct⟩ := PrunedPivotSelection.construct hbase hm hp hd width R hw eps heps
  obtain ⟨δ₀,hδ₀,hδ₀1,hgeometry⟩ := recovered_geometry (k+2)
    (by linarith : 0 ≤ width) hB₀ hK₀ ha hb hq
  refine ⟨K,hK,δ₀,hδ₀,hδ₀1,?_⟩
  intro M F E marks δ A lam xi B theta hδ hsmall hA hlam hxi hM hB htheta htheta1 hBB hKK hE hadm hsep hbounded hcap hcomp hmarks hW hbroad hends
  have htests := hgeometry δ B theta hδ hsmall hB htheta htheta1 hBB hKK
  exact ⟨htests,hconstruct F E marks hδ htests.original_scale_le_one hA hlam hxi hM hB
    ha htheta htheta1 hE hadm hsep hbounded hcap hcomp hmarks hW hbroad hends htests.collision_small⟩

end
end KakeyaFormal.UniformPrunedPivotSelection

#print axioms KakeyaFormal.UniformPrunedPivotSelection.recovered_geometry
#print axioms KakeyaFormal.UniformPrunedPivotSelection.construct
