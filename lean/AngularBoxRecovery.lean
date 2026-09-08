import AngularBoxSelection

/-! An actual angular box is converted to a separated, uniformly dense,
measurable marked hairbrush family. All unit segments and the mass color are
constructed from the original shadings. -/
namespace KakeyaFormal.AngularBoxRecovery
open MeasureTheory SpatialAngular AnisotropicRescaling AnisotropicVolume AnisotropicShading
open AnisotropicTransport AngularBoxSelection HairbrushKernel HairbrushSelection
open MeasurableDensityRecovery ProjectiveGeometry SeparationColoring
open scoped ENNReal BigOperators
noncomputable section
open Classical

def directionLoss (angular : ℝ) : ℝ := 4*(1+2*angular)^2
def angularLoss (angular : ℝ) : ℝ := 8*(1+2*angular)^2
def retention (k : ℕ) (angular eta : ℝ) : ℝ :=
  eta/((segmentCount angular:ℝ)*(paletteSize (k+1) (1/directionLoss angular):ℝ))
def capCoefficient (k : ℕ) (angular m A : ℝ) : ℝ :=
  packingConstant (k+1)*A*(angularLoss angular)^m
def broadCoefficient (k : ℕ) (angular beta K eta : ℝ) : ℝ :=
  (K*(angularLoss angular)^beta)*(8/retention k angular eta)
def endsCoefficient (k : ℕ) (angular B eta : ℝ) : ℝ :=
  B*(4/retention k angular eta)

theorem directionLoss_pos {angular : ℝ} (ha : 0 ≤ angular) : 0 < directionLoss angular := by
  unfold directionLoss
  positivity

theorem retention_pos (k : ℕ) {angular eta : ℝ} (heta : 0 < eta) :
    0 < retention k angular eta := by
  have hS : (0:ℝ) < segmentCount angular := Nat.cast_pos.mpr (segmentCount_pos angular)
  have hP : (0:ℝ) < paletteSize (k+1) (1/directionLoss angular) :=
    Nat.cast_pos.mpr (paletteSize_pos _ _)
  unfold retention
  positivity

theorem retention_le (k : ℕ) {angular eta : ℝ} (heta : 0 ≤ eta) :
    retention k angular eta ≤ eta := by
  have hS : (1:ℝ) ≤ segmentCount angular := Nat.one_le_cast.mpr (segmentCount_pos angular)
  have hP : (1:ℝ) ≤ paletteSize (k+1) (1/directionLoss angular) :=
    Nat.one_le_cast.mpr (paletteSize_pos _ _)
  have hD : 1 ≤ (segmentCount angular:ℝ)*(paletteSize (k+1) (1/directionLoss angular):ℝ) := by nlinarith
  exact div_le_self heta hD

/-- Exact images, best unit segments, a genuine maximum-mass separation color,
and measurable marking produce every geometric input of the broad hairbrush.
The reference population includes every original index throughout recovery. -/
theorem single_box_recovery {k M : ℕ} (F : TubeFamily (k+2) M)
    (Full Ref : Fin M → Set (Space (k+2))) (u : Space (k+2)) (q : Cell (k+1))
    {δ tau angular eta lam alpha beta B K m A : ℝ}
    (hM : 0 < M) (hu : ‖u‖ = 1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (heta : 0 < eta) (hlam : 0 < lam) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hm : 0 ≤ m) (hA : 0 ≤ A)
    (_hFull : ∀ i, MeasurableSet (Full i)) (hRef : ∀ i, MeasurableSet (Ref i))
    (hRefFull : ∀ i, Ref i ⊆ Full i) (hsub : ∀ i, Full i ⊆ (F.tube i).carrier δ)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hupper : ∀ i, (volume : Measure (Space (k+2))).real (Full i) ≤ 2*lam*δ^(k+1))
    (hmass : eta*lam*δ^(k+1)*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+2))).real (Ref i))
    (hbroad : ∀ x, AngularDecomposition.Broad F (Finset.univ.filter (fun i => x ∈ Ref i)) δ beta tau K)
    (hends : ∀ i p r, δ ≤ r → (volume : Measure (Space (k+2))).real (Full i ∩ Metric.closedBall p r) ≤
      B*r^alpha*(volume : Measure (Space (k+2))).real (Full i)) :
    ∃ N : ℕ, ∃ H : TubeFamily (k+2) N, ∃ Y : Fin N → Set (Space (k+2)), ∃ G : Set (Space (k+2)),
      0 < N ∧ H.Separated (δ/tau) ∧ H.CapBound (δ/tau) m (capCoefficient k angular m A) ∧
      (∀ i, MeasurableSet (Y i) ∧ Y i ⊆ (H.tube i).carrier (δ/tau) ∧
        (retention k angular eta*lam/2)*(δ/tau)^(k+1) ≤ (volume : Measure (Space (k+2))).real (Y i) ∧
        (volume : Measure (Space (k+2))).real (Y i) ≤ (2*lam)*(δ/tau)^(k+1)) ∧
      MeasurableSet G ∧
      (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 ≤ markedMass (ν := volume) Y G ∧
      PointwiseBroad H Y G (δ/tau) beta (broadCoefficient k angular beta K eta) ∧
      (∀ i p r, δ/tau ≤ r → r ≤ 1 → (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p r) ≤
        endsCoefficient k angular B eta*r^alpha*(volume : Measure (Space (k+2))).real (Y i)) ∧
      retention k angular eta*lam*(δ/tau)^(k+1)*(M:ℝ)/4 ≤ markedMass (ν := volume) Y G ∧
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) ≤
        (volume : Measure (Space (k+2))).real (⋃ i, Ref i)/tau^(k+1) := by
  have htau : 0 < tau := hδ.trans_le hδtau
  let d := δ/tau
  have hd : 0 < d := div_pos hδ htau
  let e := retention k angular eta
  have he : 0 < e := retention_pos k heta
  let l := lam*d^(k+1)
  have hl : 0 < l := by dsimp [l]; positivity
  let j : Fin M → ℕ := fun i => bestSegment u htau.ne' q (F.tube i) angular 1 δ (Ref i)
  let T := AnisotropicCap.family F u htau.ne' q j (fun _ => ∅)
  let R : Fin M → Set (Space (k+2)) := fun i => normalizeBox u tau q '' Ref i
  let U : Fin M → Set (Space (k+2)) := fun i => normalizeBox u tau q '' Full i
  let S : Fin M → Set (Space (k+2)) := fun i => selectedSet u htau.ne' q (F.tube i) angular 1 δ (Ref i)
  have hFullf (i) : volume (Full i) ≠ ∞ := measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite _ _)
  have hReff (i) : volume (Ref i) ≠ ∞ := measure_ne_top_of_subset (hRefFull i) (hFullf i)
  have hUf (i) : volume (U i) ≠ ∞ := normalizeBox_volume_finite u htau q (hFullf i)
  have hRmeas (i) : MeasurableSet (R i) := normalizeBox_image_measurable u htau.ne' q (hRef i)
  have hSmeas (i) : MeasurableSet (S i) := AnisotropicShading.selected_measurable u htau.ne' q (F.tube i) angular 1 δ (hRef i)
  have hSU (i) : S i ⊆ R i := (selected_subset u htau.ne' q (F.tube i) angular 1 δ (Ref i)).1
  have hRU (i) : R i ⊆ U i := Set.image_mono (hRefFull i)
  have hST (i) : S i ⊆ (T.tube i).carrier d := by
    simpa only [S,T,j,d,AnisotropicCap.family,one_mul] using (selected_subset u htau.ne' q (F.tube i) angular 1 δ (Ref i)).2
  have hUupper (i) : (volume : Measure (Space (k+2))).real (U i) ≤ 2*l := by
    have hh := div_le_div_of_nonneg_right (hupper i) (pow_pos htau (k+1)).le
    dsimp only [U]
    rw [normalizeBox_realVolume u htau]
    simpa only [l,d,div_pow,mul_div_assoc,mul_assoc] using hh
  have hSmass : eta*lam*d^(k+1)*(M:ℝ)/(segmentCount angular:ℝ) ≤
      ∑ i, (volume : Measure (Space (k+2))).real (S i) := by
    have hSl (i) := AnisotropicShading.selected_mass_lower u hu htau htau1 q (F.tube i) (Ref i)
      (hlocal i) (show Ref i ⊆ (F.tube i).carrier (1*δ) by simpa only [one_mul] using (hRefFull i).trans (hsub i))
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hSl i)
    rw [← Finset.sum_div] at hsum
    have hden : 0 ≤ tau^(k+1)*(segmentCount angular:ℝ) := by positivity
    have htotal := div_le_div_of_nonneg_right hmass hden
    have hid : eta*lam*δ^(k+1)*(M:ℝ)/(tau^(k+1)*(segmentCount angular:ℝ)) =
      eta*lam*d^(k+1)*(M:ℝ)/(segmentCount angular:ℝ) := by dsimp [d]; rw [div_pow]; ring
    rw [hid] at htotal
    exact htotal.trans hsum
  have hTsep : T.Separated ((1/directionLoss angular)*d) := by
    have hh := AnisotropicCap.family_separated F u hu htau htau1 ha hlocal hsep q j (fun _ => ∅)
    convert hh using 1
    dsimp only [directionLoss,d]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  obtain ⟨color,hcolor⟩ := full_separation_coloring T hd (one_div_pos.mpr (directionLoss_pos ha)) hTsep
  obtain ⟨c,hc⟩ := exists_mass_color (volume : Measure (Space (k+2))) (paletteSize_pos (k+1) (1/directionLoss angular)) S color
  let O := colorOutput S color c
  have hOmeas : ∀ i, MeasurableSet (O i) := colorOutput_measurable S color c hSmeas
  have hOR (i) : O i ⊆ R i := (colorOutput_subset S color c i).trans (hSU i)
  have hOmass : e*l*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+2))).real (O i) := by
    have hP : (0:ℝ) ≤ paletteSize (k+1) (1/directionLoss angular) := Nat.cast_nonneg _
    have hh := (div_le_div_of_nonneg_right hSmass hP).trans hc
    have hid : (eta*lam*d^(k+1)*(M:ℝ)/(segmentCount angular:ℝ))/
      (paletteSize (k+1) (1/directionLoss angular):ℝ) = e*l*(M:ℝ) := by
      dsimp [e,l,retention]
      ring
    rwa [hid] at hh
  have hRbro : PointwiseBroad T R (⋃ i, R i) d beta (K*(angularLoss angular)^beta) := by
    apply pointwiseBroad_of_angular
    exact image_broadness F u Ref hu hδ htau htau1 ha hK (fun i _ => hlocal i) hbroad q j (fun _ => ∅)
  have hUends : ∀ i p r, d ≤ r → r ≤ 1 →
      (volume : Measure (Space (k+2))).real (U i ∩ Metric.closedBall p r) ≤
        B*r^alpha*(volume : Measure (Space (k+2))).real (U i) := by
    intro i p r hr _
    exact image_two_ends u hδ htau htau1 q (Full i) (hFullf i) (hends i) p r hr
  have hKnew : 0 ≤ K*(angularLoss angular)^beta := mul_nonneg hK (Real.rpow_nonneg (by unfold angularLoss; positivity) _)
  obtain ⟨hcount,htotal,hYi,hGmeas,_hGf,_hGsub,hgood,hbroadY,hendsY⟩ :=
    recover T volume U R O hd.le he hl hB hKnew hRmeas hOmeas hUf hRU hOR hUupper hOmass hRbro hUends
  let H := selectedFamily T volume O e l
  let Y := selected volume O e l
  let G := marked volume R O e l
  have hN : 0 < (good volume O e l).card := by
    have hp : 0 < e*(M:ℝ)/4 := by positivity
    exact_mod_cast hp.trans_le hcount
  have hHsep : H.Separated d := recovered_separated T volume S color c he hl hcolor
  have hTcap : T.CapBound d m (capCoefficient k angular m A) :=
    AnisotropicCap.family_cap_bound F u hu hδ hδtau htau1 ha hm hA hlocal hcap q j (fun _ => ∅)
  have hHcap := selectedFamily_cap_bound T volume O e l hTcap
  have hYsub (i) : Y i ⊆ (H.tube i).carrier d :=
    (colorOutput_subset S color c _).trans (hST _)
  have hYunion : (⋃ i, Y i) ⊆ ⋃ i, S i := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨selectedIndex volume O e l i,colorOutput_subset S color c _ hi⟩
  have hSfinite : volume (⋃ i, S i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ := (volume : Measure (Space (k+2))))
      (s := Set.univ) (f := S) (Set.toFinite _) (fun i _ => AnisotropicShading.selected_finite u htau.ne' q (F.tube i) angular 1 δ (Ref i))
  have hUnion := (measureReal_mono hYunion hSfinite).trans
    (selected_union_volume u htau q F.tube angular 1 δ Ref hReff)
  refine ⟨_,H,Y,G,hN,hHsep,hHcap,?_,hGmeas,hgood,hbroadY,hendsY,?_,hUnion⟩
  · intro i
    refine ⟨(hYi i).1,hYsub i,?_,?_⟩
    · have hh := (hYi i).2.2.1
      change e*l/2 ≤ _ at hh
      convert hh using 1
      dsimp [e,l,d]
      ring
    · have hh := (hYi i).2.2.2
      change _ ≤ 2*l at hh
      exact hh.trans_eq (by dsimp [l,d]; ring)
  · change _ ≤ ∑ i, (volume : Measure (Space (k+2))).real (Y i ∩ G)
    have hh : e*lam*d^(k+1)*(M:ℝ)/4 ≤ (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 := by
      change e*l*(M:ℝ)/2 ≤ _ at htotal
      dsimp [l] at htotal
      linarith
    exact hh.trans hgood

end
end KakeyaFormal.AngularBoxRecovery

#print axioms KakeyaFormal.AngularBoxRecovery.single_box_recovery
