import AnisotropicJointGeometry
import SamplingNormalizedMeans

/-! Actual fixed-density sampling input after one genuine angular/spatial box.
The marked-mass color is chosen BEFORE measured full-density selection and
proportional marking. The reference denominator retains ALL original image
marks. No probability, density, or broadness-preserving selection is assumed. -/
namespace KakeyaFormal.AnisotropicSamplingInput
open Finset MeasureTheory AnisotropicShading AnisotropicRescaling SpatialAngular AnisotropicVolume
open AnisotropicJointGeometry AnisotropicJointRecovery AngularDecomposition MeasurableEnergy HairbrushKernel
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- Fixed segment and palette cost in the retained marked fraction. -/
def retention (k : ℕ) (angular eta : ℝ) : ℝ :=
  eta/((segmentCount angular:ℝ)*(SeparationColoring.paletteSize k (separationFactor angular):ℝ))
def markedFraction (e : ℝ) (D : ℕ) : ℝ := e/(4*(D+1:ℕ))
def endsConstant (B e : ℝ) : ℝ := B*(4/e)
def broadConstant (angular beta K e : ℝ) (D : ℕ) : ℝ :=
  broadFactor angular beta K*(8*(D+1:ℕ)/e)

theorem retention_pos (k : ℕ) (angular : ℝ) {eta : ℝ} (heta : 0 < eta) :
    0 < retention k angular eta := by
  have hN : (0:ℝ) < segmentCount angular := Nat.cast_pos.mpr (segmentCount_pos angular)
  have hP : (0:ℝ) < SeparationColoring.paletteSize k (separationFactor angular) :=
    Nat.cast_pos.mpr (SeparationColoring.paletteSize_pos _ _)
  exact div_pos heta (mul_pos hN hP)

theorem retention_le_one (k : ℕ) (angular : ℝ) {eta : ℝ} (heta : eta ≤ 1) :
    retention k angular eta ≤ 1 := by
  have hN : (1:ℝ) ≤ segmentCount angular := by exact_mod_cast segmentCount_pos angular
  have hP : (1:ℝ) ≤ SeparationColoring.paletteSize k (separationFactor angular) := by
    exact_mod_cast SeparationColoring.paletteSize_pos k (separationFactor angular)
  apply (div_le_one (by positivity)).mpr
  nlinarith

/-- Complete actual measurable input, with fixed density constants 2 and4.
The existential objects are original-index restrictions of the marked-best
segments and their exact measurable image shadings. A genuine common spatial
box remains an explicit geometric premise. -/
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
    let htau := hδ.trans_le hδtau
    let J := AnisotropicJointShading.family F u htau.ne' q angular width δ G
    let Y := fun i => AnisotropicJointShading.full u htau.ne' q (F.tube i) angular width δ (Full i) (G i)
    let O := fun i => AnisotropicJointShading.marks u htau.ne' q (F.tube i) angular width δ (G i)
    let Ref := fun i => normalizeBox u tau q '' G i
    let e := retention k angular eta
    ∃ color : Fin M → Fin (SeparationColoring.paletteSize k (separationFactor angular)),
    ∃ c : Fin (SeparationColoring.paletteSize k (separationFactor angular)),
    ∃ D ell : ℕ, ell ≤ D ∧ (D:ℝ)+1 ≤ Real.log (4/e)/Real.log 2+2 ∧
    ∃ T : Finset (Fin M), T.Nonempty ∧
      let Fnew := MeasurableMarkedSelection.family J T
      let Z := MeasurableMarkedSelection.reindex (onColor color c Y) T
      let H := MeasurableMarkedSelection.marks Ref (onColor color c O) T (8*(D+1:ℕ)/e)
      let lamNew := (e*(lam*δ^k/tau^k)/2*(2:ℝ)^ell)/(2*(δ/tau)^k)
      e*lam/4 ≤ lamNew ∧ lamNew ≤ lam ∧ markedFraction e D ≤ 1 ∧
      SamplingNormalizedMeans.Input Fnew Z H (δ/tau) width (baseBound angular R W)
        lamNew 2 4 (markedFraction e D) (endsConstant B e) alpha (broadConstant angular beta K e D) beta ∧
      Fnew.Separated (δ/tau) ∧ Fnew.CapBound (δ/tau) m (capFactor k angular m*A) ∧
      (∀ i, Z i ⊆ normalizeBox u tau q '' Full (MeasurableMarkedSelection.index T i)) ∧
      e*(lam*δ^k/tau^k)*(M:ℝ)/(4*(D+1:ℕ)) ≤ ∑ i, (volume : Measure (Space (k+1))).real (H i) ∧
      (volume : Measure (Space (k+1))).real (⋃ i, Z i) ≤
        (volume : Measure (Space (k+1))).real (⋃ i, Full i)/tau^k := by
  intro htau J Y O Ref e
  let Full' := fun i => normalizeBox u tau q '' Full i
  let lam' := lam*δ^k/tau^k
  have he : 0 < e := retention_pos k angular heta
  have he1 : e ≤ 1 := retention_le_one k angular heta1
  have hlamp : 0 < lam' := div_pos (mul_pos hlam (pow_pos hδ k)) (pow_pos htau k)
  have hP : (0:ℝ) < SeparationColoring.paletteSize k (separationFactor angular) :=
    Nat.cast_pos.mpr (SeparationColoring.paletteSize_pos _ _)
  obtain ⟨color,c,hcolorMass,hcolorNested,hgeometry⟩ :=
    joint_colored_selection F u Full G hu hδ hδtau htau1 ha hm hA hlocal hsep hcap q hbox hGT
  let Yc := onColor color c Y
  let Oc := onColor color c O
  have hFullf (i) : volume (Full i) ≠ ∞ := measure_ne_top_of_subset (hcarrier i) (TubeVolume.carrier_finite _ _)
  have hFull'f (i) : volume (Full' i) ≠ ∞ := normalizeBox_volume_finite u htau q (hFullf i)
  have hRef (i) : MeasurableSet (Ref i) := normalizeBox_image_measurable u htau.ne' q (hG i)
  have hY (i) : MeasurableSet (Y i) := AnisotropicJointShading.full_measurable u htau.ne' q (F.tube i) angular width δ (G i) (hFull i)
  have hO (i) : MeasurableSet (O i) := AnisotropicJointShading.marks_measurable u htau.ne' q (F.tube i) angular width δ (hG i)
  have hYc := onColor_measurable color c Y hY
  have hOc := onColor_measurable color c O hO
  have hRefFull (i) : Ref i ⊆ Full' i := Set.image_mono (hGT i)
  have hYFull (i) : Yc i ⊆ Full' i := (onColor_subset color c Y i).trans
    (AnisotropicJointShading.full_subset u htau.ne' q (F.tube i) angular width δ (Full i) (G i)).1
  have hOY (i) : Oc i ⊆ Yc i := hcolorNested i
  have hORef (i) : Oc i ⊆ Ref i := (onColor_subset color c O i).trans
    (AnisotropicJointShading.marks_subset u htau.ne' q (F.tube i) angular width δ (G i))
  have hupper' (i) : (volume : Measure (Space (k+1))).real (Full' i) ≤ 2*lam' := by
    change (volume : Measure (Space (k+1))).real (normalizeBox u tau q '' Full i) ≤ _
    rw [normalizeBox_realVolume u htau]
    exact (div_le_div_of_nonneg_right (hupper i) (pow_pos htau k).le).trans_eq (by dsimp [lam']; ring)
  have hmarks := AnisotropicJointShading.total_marks_budget u hu htau htau1 q F.tube Full G hlocal hcarrier hGT hmass
  have hmass' : e*lam'*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+1))).real (Oc i) := by
    have hh := (div_le_div_of_nonneg_right hmarks hP.le).trans hcolorMass
    convert hh using 1 <;> first | rfl | (dsimp [e,retention,lam']; simp only [div_eq_mul_inv,mul_inv_rev]; ring)
  obtain ⟨D,ell,hell,hD,T,hT,hrange,hlower,hclass,hhalf,hret⟩ :=
    MeasurableMarkedSelection.select Full' Ref Yc Oc he he1 hlamp hRef hOc hFull'f hRefFull hYFull hOY hupper' hmass' hM
  let density := e*lam'/2*(2:ℝ)^ell
  let lamNew := density/(2*(δ/tau)^k)
  let Fnew := MeasurableMarkedSelection.family J T
  let Z := MeasurableMarkedSelection.reindex Yc T
  let H := MeasurableMarkedSelection.marks Ref Oc T (8*(D+1:ℕ)/e)
  have hdlo : e*lam'/2 ≤ density := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  have hdhi : density ≤ 2*lam' := by
    obtain ⟨i,hi⟩ := hT
    exact (hrange i hi).1.trans ((measureReal_mono (hYFull i) (hFull'f i)).trans (hupper' i))
  obtain ⟨hln,hlnlo,hlnhi,hln1,hdeq,hdeq2⟩ := density_parameter hδ htau he hlam hlam1 hdlo hdhi
  have hpositive : ∀ i ∈ T, 0 < (volume : Measure (Space (k+1))).real (Yc i) :=
    fun i hi => (by positivity : 0 < e*lam'/2).trans_le (hlower i hi)
  obtain ⟨hsepNew,hcapNew,hboundedNew⟩ := hgeometry T hpositive
  have hZmeas (i) : MeasurableSet (Z i) := hYc (MeasurableMarkedSelection.index T i)
  have hHmeas := MeasurableMarkedSelection.marks_measurable Ref Oc T (8*(D+1:ℕ)/e) hRef hOc
  have hHZ (i) : H i ⊆ Z i := Set.inter_subset_left.trans (hOY _)
  have hZcarrier (i) : Z i ⊆ (Fnew.tube i).carrier (width*(δ/tau)) :=
    (onColor_subset color c Y _).trans
      (AnisotropicJointShading.full_subset u htau.ne' q (F.tube _) angular width δ (Full _) (G _)).2
  have hper (i) : 2*lamNew*(δ/tau)^k ≤ (volume : Measure (Space (k+1))).real (Z i) ∧
      (volume : Measure (Space (k+1))).real (Z i) ≤ 4*lamNew*(δ/tau)^k := by
    have hh := hrange _ (MeasurableMarkedSelection.index_mem T i)
    exact ⟨hdeq.symm.le.trans hh.1,hh.2.le.trans_eq hdeq2⟩
  have hfraction := MeasurableMarkedSelection.marked_fraction Full' Yc T he.le hFull'f hYFull hupper' hret
  have hmarked : markedFraction e D*lamNew*(δ/tau)^k*(T.card:ℝ) ≤
      ∑ i, (volume : Measure (Space (k+1))).real (H i) := by
    have hsum : 2*lamNew*(δ/tau)^k*(T.card:ℝ) ≤ ∑ i, (volume : Measure (Space (k+1))).real (Z i) :=
      (by simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using
        sum_le_sum (s:=univ) (fun i _ => (hper i).1))
    have hh := mul_le_mul_of_nonneg_left hsum (div_nonneg he.le (by positivity : (0:ℝ)≤8*(D+1:ℕ)))
    apply le_trans ?_ hfraction
    convert hh using 1
    first | rfl | (simp only [markedFraction,div_eq_mul_inv,mul_inv_rev]; ring)
  have hBnew : 1 ≤ endsConstant B e := by
    have hf : (1:ℝ) ≤ 4/e := (le_div_iff₀ he).mpr (by linarith)
    unfold endsConstant
    nlinarith
  have hKnew : 0 < broadConstant angular beta K e D := by
    unfold broadConstant broadFactor
    have hc : 0 < (8:ℝ)*(1+2*angular)^2 := by positivity
    exact mul_pos (mul_pos hK (Real.rpow_pos_of_pos hc beta)) (by positivity)
  have hxi : 0 < markedFraction e D := div_pos he (by positivity)
  have hxi1 : markedFraction e D ≤ 1 := (div_le_one (by positivity)).mpr (by
    have hD1 : (1:ℝ) ≤ (D+1:ℕ) := by exact_mod_cast Nat.succ_pos D
    linarith)
  have hbr : PointwiseBroad Fnew H Set.univ (δ/tau) beta (broadConstant angular beta K e D) := by
    have htrans := AnisotropicTransport.image_broadness F u G hu hδ htau htau1 ha hK.le
      (fun i _ => hlocal i) hbroad q
      (fun i => bestSegment u htau.ne' q (F.tube i) angular width δ (G i)) (fun _ => ∅)
    have hbrRef : PointwiseBroad J Ref Set.univ (δ/tau) beta (broadFactor angular beta K) := by
      intro x _ center r hr
      have hh := htrans x center r hr
      simpa only [cap,filter_filter,div_one,overlapCount,broadFactor,J,Ref,AnisotropicJointShading.family] using hh
    exact MeasurableMarkedSelection.marks_broad J Ref Oc T (div_pos hδ htau).le
      (mul_nonneg hK.le (Real.rpow_nonneg (by positivity) beta)) hORef hbrRef
  have hendsNew : ∀ i x r, δ/tau ≤ r →
      (volume : Measure (Space (k+1))).real (Z i ∩ Metric.closedBall x r) ≤
        endsConstant B e*r^alpha*(volume : Measure (Space (k+1))).real (Z i) := by
    apply MeasurableMarkedSelection.reindexed_two_ends volume Full' Yc T (div_pos hδ htau).le he
      (zero_le_one.trans hB) hFull'f hYFull hupper' hlower
    intro i x r hr
    exact AnisotropicTransport.image_two_ends u hδ htau htau1 q (Full i) (hFullf i) (hends i) x r hr
  have hInput : SamplingNormalizedMeans.Input Fnew Z H (δ/tau) width (baseBound angular R W)
      lamNew 2 4 (markedFraction e D) (endsConstant B e) alpha (broadConstant angular beta K e D) beta := {
    scale_pos := div_pos hδ htau
    scale_le_one := (div_le_one htau).mpr hδtau
    width_nonneg := hw
    density_pos := hln
    density_le_one := hln1
    lower_constant_pos := by norm_num
    upper_constant_pos := by norm_num
    count_pos := card_pos.mpr hT
    marked_fraction_pos := hxi
    bounded := hboundedNew
    full_subset := hZcarrier
    full_measurable := hZmeas
    marked_measurable := hHmeas
    marked_subset := hHZ
    full_mass := hper
    marked_mass := hmarked
    two_ends_constant := hBnew
    two_ends_exponent := halpha
    broadness_constant := hKnew
    broadness_exponent := hbeta
    two_ends := fun i x r hr _ => hendsNew i x r hr
    broadness := Filter.Eventually.of_forall (fun x v _ r hr _ => hbr x (Set.mem_univ _) v r hr)
  }
  refine ⟨color,c,D,ell,hell,hD,T,hT,hlnlo,hlnhi,hxi1,hInput,hsepNew,hcapNew,?_,hret,?_⟩
  · intro i
    exact hYFull (MeasurableMarkedSelection.index T i)
  · have hsub : (⋃ i, Z i) ⊆ normalizeBox u tau q '' (⋃ i, Full i) := by
      intro x hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y,hy,rfl⟩ := hYFull (MeasurableMarkedSelection.index T i) hi
      exact ⟨y,Set.mem_iUnion.mpr ⟨MeasurableMarkedSelection.index T i,hy⟩,rfl⟩
    have hU : volume (⋃ i, Full i) ≠ ∞ := by
      simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ:=volume)
        (s:=Set.univ) (f:=Full) (Set.toFinite _) (fun i _ => hFullf i)
    have hh := measureReal_mono hsub (normalizeBox_volume_finite u htau q hU)
    rwa [normalizeBox_realVolume u htau] at hh

end
end KakeyaFormal.AnisotropicSamplingInput
