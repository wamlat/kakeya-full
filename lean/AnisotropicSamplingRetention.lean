import AnisotropicSamplingInput

/-! Quantitative population retention and a compact record for the actual
constructed anisotropic sampling input. Population is deduced from measured
marked mass and the full density upper bound, not supplied as an assumption. -/
namespace KakeyaFormal.AnisotropicSamplingRetention
open Finset MeasureTheory AnisotropicSamplingInput AnisotropicJointGeometry AnisotropicShading
open AnisotropicRescaling SpatialAngular AngularDecomposition
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- The actual marked mass, with each mark inside its actual full shading,
forces the density-weighted final population. -/
theorem density_population {k M N D : ℕ} (F : TubeFamily (k+1) N)
    (Z H : Fin N → Set (Space (k+1))) {δ width R lam lamNew e xi B alpha K beta : ℝ}
    (h : SamplingNormalizedMeans.Input F Z H δ width R lamNew 2 4 xi B alpha K beta)
    (hret : e*lam*δ^k*(M:ℝ)/(4*(D+1:ℕ)) ≤
      ∑ i, (volume : Measure (Space (k+1))).real (H i)) :
    e*lam*(M:ℝ)/(16*(D+1:ℕ)) ≤ lamNew*(N:ℝ) := by
  have hZf (i) : volume (Z i) ≠ ∞ := measure_ne_top_of_subset (h.full_subset i) (TubeVolume.carrier_finite _ _)
  have hupper : (∑ i, (volume : Measure (Space (k+1))).real (H i)) ≤ 4*lamNew*δ^k*(N:ℝ) :=
    (sum_le_sum (fun i _ => (measureReal_mono (h.marked_subset i) (hZf i)).trans (h.full_mass i).2)).trans_eq
      (by simp [mul_comm])
  have hh := (div_le_iff₀ (by positivity : (0:ℝ)<4*(D+1:ℕ))).mp (hret.trans hupper)
  apply (div_le_iff₀ (by positivity : (0:ℝ)<16*(D+1:ℕ))).mpr
  apply (mul_le_mul_iff_right₀ (pow_pos h.scale_pos k)).mp
  convert hh using 1 <;> first | rfl | ring

/-- Since the constructed new density is at most the original density, the
same measured budget yields a quantitative number of original retained tubes. -/
theorem population {k M N D : ℕ} (F : TubeFamily (k+1) N)
    (Z H : Fin N → Set (Space (k+1))) {δ width R lam lamNew e xi B alpha K beta : ℝ}
    (h : SamplingNormalizedMeans.Input F Z H δ width R lamNew 2 4 xi B alpha K beta)
    (hlam : 0 < lam) (hnew : lamNew ≤ lam)
    (hret : e*lam*δ^k*(M:ℝ)/(4*(D+1:ℕ)) ≤
      ∑ i, (volume : Measure (Space (k+1))).real (H i)) :
    e*(M:ℝ)/(16*(D+1:ℕ)) ≤ (N:ℝ) := by
  have hh := (density_population F Z H h hret).trans (mul_le_mul_of_nonneg_right hnew (Nat.cast_nonneg N))
  apply (mul_le_mul_iff_left₀ hlam).mp
  calc
    (e*(M:ℝ)/(16*(D+1:ℕ)))*lam = e*lam*(M:ℝ)/(16*(D+1:ℕ)) := by ring
    _ ≤ lam*(N:ℝ) := hh
    _ = (N:ℝ)*lam := mul_comm _ _

/-- Actual final data, with original-index provenance and measured population
retention. The named conditioning constants are the same literal ones used by
AnisotropicSamplingInput and the later uniform logarithmic budget interface. -/
structure Output {k M : ℕ} (originalFull : Fin M → Set (Space (k+1)))
    (u : Space (k+1)) (q : Cell k)
    (δ tau width R angular lam e B alpha beta K m A : ℝ) where
  N : ℕ
  family : TubeFamily (k+1) N
  full : Fin N → Set (Space (k+1))
  marks : Fin N → Set (Space (k+1))
  density : ℝ
  depth : ℕ
  depth_bound : (depth:ℝ)+1 ≤ Real.log (4/e)/Real.log 2+2
  effective_pos : 0 < e
  effective_le_one : e ≤ 1
  index : Fin N → Fin M
  index_injective : Function.Injective index
  input : SamplingNormalizedMeans.Input family full marks (δ/tau) width R density 2 4
    (markedFraction e depth) (endsConstant B e) alpha (broadConstant angular beta K e depth) beta
  density_lower : e*lam/4 ≤ density
  density_upper : density ≤ lam
  xi_le_one : markedFraction e depth ≤ 1
  density_population_lower : e*lam*(M:ℝ)/(16*(depth+1:ℕ)) ≤ density*(N:ℝ)
  population_lower : e*(M:ℝ)/(16*(depth+1:ℕ)) ≤ (N:ℝ)
  separated : family.Separated (δ/tau)
  cap_bound : family.CapBound (δ/tau) m A
  contained : ∀ i, full i ⊆ normalizeBox u tau q '' originalFull (index i)
  marked_retention : e*lam*(δ/tau)^k*(M:ℝ)/(4*(depth+1:ℕ)) ≤
    ∑ i, (volume : Measure (Space (k+1))).real (marks i)
  union_volume : (volume : Measure (Space (k+1))).real (⋃ i, full i) ≤
    (volume : Measure (Space (k+1))).real (⋃ i, originalFull i)/tau^k

/-- End-to-end compact packaging of the SAME actual objects produced by the
frozen sampling-input theorem. No new tube, set, color or class selection is
made by this adapter. -/
theorem construct {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (Full G : Fin M → Set (Space (k+1))) {tau δ angular width R W eta lam B alpha beta K m A : ℝ}
    (hu : ‖u‖=1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (hw : 0 ≤ width) (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hB : 1 ≤ B) (halpha : 0 ≤ alpha)
    (hbeta : 0 < beta) (hK : 0 < K) (hm : 0 ≤ m) (hA : 0 ≤ A) (hM : 0 < M)
    (q : Cell k) (hFull : ∀ i, MeasurableSet (Full i)) (hG : ∀ i, MeasurableSet (G i))
    (hGT : ∀ i, G i ⊆ Full i) (hcarrier : ∀ i, Full i ⊆ (F.tube i).carrier (width*δ))
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hbox : ∀ i, (F.tube i).base ∈ parallelBox u tau q R W)
    (hupper : ∀ i, (volume : Measure (Space (k+1))).real (Full i) ≤ 2*(lam*δ^k))
    (hmass : eta*(lam*δ^k)*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+1))).real (G i))
    (hends : ∀ i x r, δ ≤ r →
      (volume : Measure (Space (k+1))).real (Full i ∩ Metric.closedBall x r) ≤
        B*r^alpha*(volume : Measure (Space (k+1))).real (Full i))
    (hbroad : ∀ x : Space (k+1), Broad F (univ.filter (fun i => x ∈ G i)) δ beta tau K) :
    Nonempty (Output Full u q δ tau width (baseBound angular R W) angular lam
      (retention k angular eta) B alpha beta K m (capFactor k angular m*A)) := by
  obtain ⟨color,c,D,ell,hell,hD,T,hT,hlo,hhi,hxi,hinput,hs,hc,hsub,hret,hunion⟩ :=
    AnisotropicSamplingInput.construct F u Full G hu hδ hδtau htau1 ha hw heta heta1 hlam hlam1 hB halpha
      hbeta hK hm hA hM q hFull hG hGT hcarrier hlocal hsep hcap hbox hupper hmass hends hbroad
  let e := retention k angular eta
  have hnorm : lam*δ^k/tau^k = lam*(δ/tau)^k := by rw [div_pow]; ring
  rw [hnorm] at hret
  have hret' := hret
  simp only [← mul_assoc] at hret'
  have hdp := density_population _ _ _ hinput hret'
  have hp := population _ _ _ hinput hlam hhi hret'
  exact ⟨{
    N := T.card
    family := _
    full := _
    marks := _
    density := _
    depth := D
    depth_bound := hD
    effective_pos := retention_pos k angular heta
    effective_le_one := retention_le_one k angular heta1
    index := MeasurableMarkedSelection.index T
    index_injective := MeasurableMarkedSelection.index_injective T
    input := hinput
    density_lower := hlo
    density_upper := hhi
    xi_le_one := hxi
    density_population_lower := hdp
    population_lower := hp
    separated := hs
    cap_bound := hc
    contained := hsub
    marked_retention := hret'
    union_volume := hunion
  }⟩

end
end KakeyaFormal.AnisotropicSamplingRetention
