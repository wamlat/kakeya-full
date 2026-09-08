import AnisotropicJointShading
import MeasurableMarkedSelection

/-! The actual joint full/marked anisotropic normalization. Segments are chosen
by marks, full mass classes are chosen by marks, and one proportional marked
filter restores broadness. Full shadings remain inside the original restricted
full union throughout. -/
namespace KakeyaFormal.AnisotropicJointRecovery
open Finset MeasureTheory SpatialAngular AnisotropicRescaling AnisotropicVolume AnisotropicShading
open AngularDecomposition HairbrushKernel HairbrushSelection MeasurableEnergy
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- The class/recovery parameters have no dependence on individual tube mass. -/
def retainedFraction (eta angular : ℝ) : ℝ := eta/(segmentCount angular:ℝ)
def broadFactor (angular beta K : ℝ) : ℝ := K*(8*(1+2*angular)^2)^beta

/-- Source marks need only have a total mass budget. Every choice and the
resulting comparable full density, marked mass, broadness and two ends are
constructed from the actual measurable sets. -/
theorem construct {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (Full G : Fin M → Set (Space (k+1))) {tau δ angular width eta lam B alpha beta K : ℝ}
    (hu : ‖u‖=1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (heta : 0 < eta) (heta1 : eta ≤ 1) (hlam : 0 < lam)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hM : 0 < M) (q : Cell k)
    (hFull : ∀ i, MeasurableSet (Full i)) (hG : ∀ i, MeasurableSet (G i))
    (hGT : ∀ i, G i ⊆ Full i) (hcarrier : ∀ i, Full i ⊆ (F.tube i).carrier (width*δ))
    (hcap : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hupper : ∀ i, (volume : Measure (Space (k+1))).real (Full i) ≤ 2*lam)
    (hmass : eta*lam*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+1))).real (G i))
    (hends : ∀ i x r, δ ≤ r →
      (volume : Measure (Space (k+1))).real (Full i ∩ Metric.closedBall x r) ≤
        B*r^alpha*(volume : Measure (Space (k+1))).real (Full i))
    (hbroad : ∀ x : Space (k+1), Broad F (univ.filter (fun i => x ∈ G i)) δ beta tau K) :
    let htau := hδ.trans_le hδtau
    let F' := AnisotropicJointShading.family F u htau.ne' q angular width δ G
    let Y := fun i => AnisotropicJointShading.full u htau.ne' q (F.tube i) angular width δ (Full i) (G i)
    let O := fun i => AnisotropicJointShading.marks u htau.ne' q (F.tube i) angular width δ (G i)
    let Ref := fun i => normalizeBox u tau q '' G i
    let eta' := retainedFraction eta angular
    let lam' := lam/tau^k
    ∃ D ell : ℕ, ell ≤ D ∧ (D:ℝ)+1 ≤ Real.log (4/eta')/Real.log 2+2 ∧
    ∃ T : Finset (Fin M), T.Nonempty ∧
      let Z := MeasurableMarkedSelection.reindex Y T
      let H := MeasurableMarkedSelection.marks Ref O T (8*(D+1:ℕ)/eta')
      let density := eta'*lam'/2*(2:ℝ)^ell
      0 < density ∧ eta'*lam'/2 ≤ density ∧ density ≤ 2*lam' ∧
      (∀ i, MeasurableSet (Z i) ∧ MeasurableSet (H i) ∧ H i ⊆ Z i ∧
        Z i ⊆ ((MeasurableMarkedSelection.family F' T).tube i).carrier (width*(δ/tau)) ∧
        density ≤ (volume : Measure (Space (k+1))).real (Z i) ∧
        (volume : Measure (Space (k+1))).real (Z i) < 2*density) ∧
      eta'*lam'*(M:ℝ)/(4*(D+1:ℕ)) ≤ ∑ i, (volume : Measure (Space (k+1))).real (H i) ∧
      (eta'/(8*(D+1:ℕ)))*(∑ i, (volume : Measure (Space (k+1))).real (Z i)) ≤
        ∑ i, (volume : Measure (Space (k+1))).real (H i) ∧
      PointwiseBroad (MeasurableMarkedSelection.family F' T) H Set.univ
        (δ/tau) beta (broadFactor angular beta K*(8*(D+1:ℕ)/eta')) ∧
      (∀ i x r, δ/tau ≤ r →
        (volume : Measure (Space (k+1))).real (Z i ∩ Metric.closedBall x r) ≤
          (B*(4/eta'))*r^alpha*(volume : Measure (Space (k+1))).real (Z i)) ∧
      (⋃ i, Z i) ⊆ normalizeBox u tau q '' (⋃ i, Full i) ∧
      (volume : Measure (Space (k+1))).real (⋃ i, Z i) ≤
        (volume : Measure (Space (k+1))).real (⋃ i, Full i)/tau^k := by
  intro htau F' Y O Ref eta' lam'
  let Full' := fun i => normalizeBox u tau q '' Full i
  have hN : (0:ℝ) < segmentCount angular := Nat.cast_pos.mpr (segmentCount_pos angular)
  have hN1 : (1:ℝ) ≤ segmentCount angular := by exact_mod_cast segmentCount_pos angular
  have heta' : 0 < eta' := div_pos heta hN
  have heta1' : eta' ≤ 1 := (div_le_one hN).mpr (heta1.trans hN1)
  have hlam' : 0 < lam' := div_pos hlam (pow_pos htau k)
  have hFullf (i) : volume (Full i) ≠ ∞ := measure_ne_top_of_subset (hcarrier i) (TubeVolume.carrier_finite _ _)
  have hFull'f (i) : volume (Full' i) ≠ ∞ := normalizeBox_volume_finite u htau q (hFullf i)
  have hRef (i) : MeasurableSet (Ref i) := normalizeBox_image_measurable u htau.ne' q (hG i)
  have hO (i) : MeasurableSet (O i) := AnisotropicJointShading.marks_measurable u htau.ne' q (F.tube i) angular width δ (hG i)
  have hRefFull (i) : Ref i ⊆ Full' i := Set.image_mono (hGT i)
  have hYFull (i) : Y i ⊆ Full' i := (AnisotropicJointShading.full_subset u htau.ne' q (F.tube i) angular width δ (Full i) (G i)).1
  have hOY (i) : O i ⊆ Y i := AnisotropicJointShading.nested u htau.ne' q (F.tube i) angular width δ (hGT i)
  have hORef (i) : O i ⊆ Ref i := AnisotropicJointShading.marks_subset u htau.ne' q (F.tube i) angular width δ (G i)
  have hupper' (i) : (volume : Measure (Space (k+1))).real (Full' i) ≤ 2*lam' := by
    change (volume : Measure (Space (k+1))).real (normalizeBox u tau q '' Full i) ≤ _
    rw [normalizeBox_realVolume u htau]
    exact (div_le_div_of_nonneg_right (hupper i) (pow_pos htau k).le).trans_eq (by dsimp [lam']; ring)
  have hmass' : eta'*lam'*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+1))).real (O i) :=
    AnisotropicJointShading.total_marks_budget u hu htau htau1 q F.tube Full G hcap hcarrier hGT hmass
  obtain ⟨D,ell,hell,hD,T,hT,hrange,hlower,hclass,hhalf,hret⟩ :=
    MeasurableMarkedSelection.select Full' Ref Y O heta' heta1' hlam'
      hRef hO hFull'f hRefFull hYFull hOY hupper' hmass' hM
  refine ⟨D,ell,hell,hD,T,hT,?_,?_,?_,?_,hret,?_,?_,?_,?_⟩
  · exact mul_pos (by positivity) (by positivity)
  · exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  · obtain ⟨i,hi⟩ := hT
    exact (hrange i hi).1.trans ((measureReal_mono (hYFull i) (hFull'f i)).trans (hupper' i))
  · intro i
    have hi := MeasurableMarkedSelection.index_mem T i
    refine ⟨AnisotropicJointShading.full_measurable u htau.ne' q (F.tube _) angular width δ (G _) (hFull _),
      MeasurableMarkedSelection.marks_measurable Ref O T _ hRef hO i,
      Set.inter_subset_left.trans (hOY _),?_,(hrange _ hi).1,(hrange _ hi).2⟩
    exact (AnisotropicJointShading.full_subset u htau.ne' q (F.tube _) angular width δ (Full _) (G _)).2
  · exact MeasurableMarkedSelection.marked_fraction Full' Y T heta'.le hFull'f hYFull hupper' hret
  · have htrans := AnisotropicTransport.image_broadness F u G hu hδ htau htau1 ha hK
      (fun i _ => hcap i) hbroad q
      (fun i => bestSegment u htau.ne' q (F.tube i) angular width δ (G i)) (fun _ => ∅)
    have hbr : PointwiseBroad F' Ref Set.univ (δ/tau) beta (broadFactor angular beta K) := by
      intro x _ center r hr
      have hh := htrans x center r hr
      simpa only [cap,filter_filter,div_one,overlapCount,broadFactor,F',Ref,AnisotropicJointShading.family] using hh
    exact MeasurableMarkedSelection.marks_broad F' Ref O T (div_pos hδ htau).le
      (mul_nonneg hK (Real.rpow_nonneg (by positivity) beta)) hORef hbr
  · apply MeasurableMarkedSelection.reindexed_two_ends volume Full' Y T (div_pos hδ htau).le
      heta' hB hFull'f hYFull hupper' hlower
    intro i x r hr
    exact AnisotropicTransport.image_two_ends u hδ htau htau1 q (Full i) (hFullf i) (hends i) x r hr
  · have hsub : (⋃ i, MeasurableMarkedSelection.reindex Y T i) ⊆
        normalizeBox u tau q '' (⋃ i, Full i) := by
      intro x hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y,hy,rfl⟩ := hYFull (MeasurableMarkedSelection.index T i) hi
      exact ⟨y,Set.mem_iUnion.mpr ⟨MeasurableMarkedSelection.index T i,hy⟩,rfl⟩
    refine ⟨hsub,?_⟩
    have hU : volume (⋃ i, Full i) ≠ ∞ := by
      simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ:=volume)
        (s:=Set.univ) (f:=Full) (Set.toFinite _) (fun i _ => hFullf i)
    have hm := measureReal_mono hsub (normalizeBox_volume_finite u htau q hU)
    rwa [normalizeBox_realVolume u htau] at hm

/-- The actual mass class gives fixed sampling density constants 2 and4,
independent of eta and the selected class. The density loss eta/4 remains
explicit while the new density parameter is still at most one. -/
theorem density_parameter {k : ℕ} {δ tau eta lam density : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau) (heta : 0 < eta) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hlo : eta*(lam*δ^k/tau^k)/2 ≤ density)
    (hhi : density ≤ 2*(lam*δ^k/tau^k)) :
    let newLam := density/(2*(δ/tau)^k)
    0 < newLam ∧ eta*lam/4 ≤ newLam ∧ newLam ≤ lam ∧ newLam ≤ 1 ∧
      density = 2*newLam*(δ/tau)^k ∧ 2*density = 4*newLam*(δ/tau)^k := by
  intro newLam
  have hs : 0 < (δ/tau)^k := pow_pos (div_pos hδ htau) k
  have hid : lam*δ^k/tau^k = lam*(δ/tau)^k := by rw [div_pow]; ring
  rw [hid] at hlo hhi
  have hd : 0 < density := (by positivity : 0 < eta*(lam*(δ/tau)^k)/2).trans_le hlo
  have hp : 0 < newLam := div_pos hd (by positivity)
  have hlower : eta*lam/4 ≤ newLam := (le_div_iff₀ (by positivity : 0 < 2*(δ/tau)^k)).mpr (by nlinarith)
  have hupper : newLam ≤ lam := (div_le_iff₀ (by positivity : 0 < 2*(δ/tau)^k)).mpr (by nlinarith)
  have heq : density = 2*newLam*(δ/tau)^k := by dsimp [newLam]; field_simp
  exact ⟨hp,hlower,hupper,hupper.trans hlam1,heq,by nlinarith [heq]⟩

end
end KakeyaFormal.AnisotropicJointRecovery
