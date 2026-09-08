import LocalizedClusters

/-! Actual localized finite-grid tube intervals and lattice-preserving common
rescaling. No physical interval or bounded rescaled base is supplied as input. -/
namespace KakeyaFormal.LocalizedGridTubes
open MeasureTheory Set GridCells GridGeometry MeasurableRescaling Rescaling
open scoped BigOperators
noncomputable section
open Classical

/-- A width enlargement chosen before all configurations. -/
def localWidth (width : ℝ) : ℝ := max 1 width

lemma localWidth_pos (width : ℝ) : 0 < localWidth width := zero_lt_one.trans_le (le_max_left _ _)

/-- A common spatial cluster origin snapped to the original fine grid. -/
def fineOrigin {k : ℕ} (δ rho : ℝ) (q : Cell k) : Cell k := label δ (cellCenter rho q)

/-- Snapping the coarse origin to the fine grid keeps a dimension-only bound
on every center in that actual spatial cluster. -/
theorem center_near_fine_origin {I : Type*} [Fintype I] {k : ℕ} (centers : I → Space k)
    {δ rho : ℝ} (hδ : 0 < δ) (hδrho : δ ≤ rho) (q : Cell k) (i : I)
    (hi : i ∈ LocalizedClusters.indices centers rho q) :
    dist (centers i) (cellCenter δ (fineOrigin δ rho q)) ≤ (k:ℝ)*rho := by
  have hc := LocalizedClusters.center_near_origin centers (hδ.trans_le hδrho) q i hi
  have hs := cell_center_distance (gridCell_covers hδ (cellCenter rho q))
  have ht := dist_triangle (centers i) (cellCenter rho q) (cellCenter δ (fineOrigin δ rho q))
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  change dist (cellCenter rho q) (cellCenter δ (fineOrigin δ rho q)) ≤ (k:ℝ)*δ/2 at hs
  nlinarith

/-- Original fine cells remain an exact translated lattice after the common
cluster rescaling, even when the coarse and fine scales are unrelated reals. -/
theorem fine_grid_rescale {k : ℕ} (δ rho L : ℝ) (q z : Cell k) :
    rescale L (cellCenter δ (fineOrigin δ rho q)) (cellCenter δ z) =
      cellCenter (δ/L) (shiftLabel (fineOrigin δ rho q) z) := rescale_grid L δ _ z

/-- Actual localized grid centers determine a short axis interval, from an
actual shading point. The enlarged width depends only on the fixed geometry. -/
theorem localized_grid_interval {k : ℕ} (T : UnitTube k) (S : Finset (Cell k))
    {δ rho width : ℝ} (hδ : 0 < δ) (hδrho : δ ≤ rho) (center : Space k)
    (hne : S.Nonempty)
    (hadm : ∀ z ∈ S, ∃ t ∈ Icc (0:ℝ) 1, dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ)
    (hball : ∀ z ∈ S, dist (cellCenter δ z) center ≤ rho) :
    ∃ a : ℝ, dist (T.axisPoint a) center ≤ 6*localWidth width*rho ∧
      ∀ z ∈ S, ∃ t ∈ Icc a (a+8*localWidth width*rho),
        dist (cellCenter δ z) (T.axisPoint t) ≤ localWidth width*δ := by
  let Y : Set (Space k) := cellCenter δ '' (S : Set (Cell k))
  have hW := localWidth_pos width
  have hW1 : 1 ≤ localWidth width := le_max_left _ _
  have hrho := hδ.trans_le hδrho
  have hYne : Y.Nonempty := by
    obtain ⟨z,hz⟩ := hne
    exact ⟨cellCenter δ z,⟨z,hz,rfl⟩⟩
  have hYT : Y ⊆ T.carrier (localWidth width*δ) := by
    rintro x ⟨z,hz,rfl⟩
    obtain ⟨t,ht,hd⟩ := hadm z hz
    exact ⟨t,ht,hd.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le)⟩
  have hYball : Y ⊆ Metric.closedBall center (localWidth width*rho) := by
    rintro x ⟨z,hz,rfl⟩
    change dist (cellCenter δ z) center ≤ _
    exact (hball z hz).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hW1 hrho.le)
  obtain ⟨a,ha,hlocal⟩ := localized_parameter_interval T (mul_pos hW hδ)
    (mul_le_mul_of_nonneg_left hδrho hW.le) center Y hYne hYT hYball
  refine ⟨a,by simpa only [mul_assoc] using ha,?_⟩
  intro z hz
  simpa only [mul_assoc] using hlocal (cellCenter δ z) ⟨z,hz,rfl⟩

/-- An actual localized finite-grid family has a genuine uniformly bounded
unit-tube rescaling. All fine shading and union cardinalities are preserved. -/
theorem normalized_localized_family {k M : ℕ} (F : TubeFamily k M)
    (centers : Fin M → Space k) (origin : Cell k) {δ rho width R : ℝ}
    (hδ : 0 < δ) (hδrho : δ ≤ rho)
    (hne : ∀ i, (F.shade i).Nonempty) (hadm : F.Admissible width δ)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho)
    (hcenter : ∀ i, dist (centers i) (cellCenter δ origin) ≤ R*rho) :
    ∃ a : Fin M → ℝ,
      let L := 8*localWidth width*rho
      let G := Rescaling.family F L δ origin a
      G.Admissible (localWidth width) (δ/L) ∧
      G.Bounded ((6*localWidth width+R)/(8*localWidth width)) ∧
      (∀ i, (G.shade i).card = (F.shade i).card) ∧
      G.unionCells.card = F.unionCells.card ∧
      ∀ i, (G.tube i).direction = (F.tube i).direction := by
  have hW := localWidth_pos width
  have hrho := hδ.trans_le hδrho
  have hL : 0 < 8*localWidth width*rho := by positivity
  choose a ha hlocal using fun i => localized_grid_interval (F.tube i) (F.shade i)
    hδ hδrho (centers i) (hne i) (hadm i) (hball i)
  refine ⟨a,rescaled_admissible F hL origin a hlocal,?_,?_,rescaled_union_card F _ δ origin a,fun _ => rfl⟩
  · apply rescaled_bounded F hL origin a
    intro i
    have ht := dist_triangle ((F.tube i).axisPoint (a i)) (centers i) (cellCenter δ origin)
    have hid : (8*localWidth width*rho)*((6*localWidth width+R)/(8*localWidth width)) =
        (6*localWidth width+R)*rho := by field_simp
    rw [hid]
    nlinarith [ha i,hcenter i]
  · intro i
    exact rescaled_card F _ δ origin a i

end
end KakeyaFormal.LocalizedGridTubes
