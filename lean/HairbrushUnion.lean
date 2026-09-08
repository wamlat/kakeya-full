import PlanarEnergy

/-!
# Actual measurable plane-bin overlap and hairbrush union summation

The finite partition is an actual map from bristles to separated transverse
plane representatives. Geometric plank containment supplies the pointwise
multiplicity bound; per-bin energy then supplies the union lower bound.
-/
namespace KakeyaFormal.HairbrushUnion

open KakeyaFormal.HairbrushPlanes KakeyaFormal.EuclideanSplit KakeyaFormal.PlanarEnergy
open KakeyaFormal.ProjectiveGeometry KakeyaFormal.MeasurableEnergy
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]

def binUnion {X : Type*} (assignment : ι → β) (Y : ι → Set X) (j : β) : Set X :=
  ⋃ i : {i : ι // assignment i = j}, Y i.1

omit [Fintype ι] [Fintype β] [DecidableEq β] in
/-- The actual fibers of the assignment partition the original shading union. -/
theorem union_binUnion {X : Type*} (assignment : ι → β) (Y : ι → Set X) :
    (⋃ j, binUnion assignment Y j) = ⋃ i, Y i := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hj
    exact Set.mem_iUnion.mpr ⟨i.1,hi⟩
  · intro hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨assignment i,Set.mem_iUnion.mpr ⟨⟨i,rfl⟩,hi⟩⟩

/-- The assignment fibers account for all original bristles exactly. -/
theorem sum_bin_card (assignment : ι → β) :
    (∑ j : β, (Fintype.card {i : ι // assignment i = j}:ℝ)) = (Fintype.card ι:ℝ) := by
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv assignment)
  rw [Fintype.card_sigma] at h
  exact_mod_cast h

omit [Fintype ι] [Fintype β] [DecidableEq β] in
/-- Actual bristle intersection, bounded location and plane assignment derive
shading containment in the assigned thickened plane. -/
theorem assigned_shading_plank {k : ℕ} (stem : UnitTube (k+2))
    (bristle : ι → UnitTube (k+2)) (Y : ι → Set (Space (k+2)))
    (assignment : ι → β) (normal : β → Space (k+1)) {δ R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hangle : ∀ i, 0 < projectiveDistance stem.direction (bristle i).direction)
    (hmeet : ∀ i, (stem.carrier δ ∩ (bristle i).carrier δ).Nonempty)
    (hbin : ∀ i, projectiveDistance (bristleNormal stem (bristle i)) (normal (assignment i)) ≤ δ)
    (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hball : ∀ i x, x ∈ Y i → ‖x-stem.base‖ ≤ R) (i : ι) :
    Y i ⊆ plank (alignStem stem.direction) stem.base (normal (assignment i)) ((6+R)*δ) := by
  intro x hx
  have hp := bristle_in_stem_plank stem (bristle i) (hmeet i) (hsub i hx)
  obtain ⟨b,hb⟩ := plank_normal_change (alignStem stem.direction) stem.base x
    (bristleNormal stem (bristle i)) (normal (assignment i))
    (bristleNormal_unit stem (bristle i) (hangle i)) hδ.le (hbin i) (hball i x hx) hp
  refine ⟨b,hb.trans ?_⟩
  nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)]

omit [Fintype ι] [DecidableEq β] in
/-- The actual finite bin union has the geometrically proved ambient-minus-two
pointwise multiplicity bound away from the stem. -/
theorem bin_union_overlap_count {k : ℕ} (stem : UnitTube (k+2))
    (bristle : ι → UnitTube (k+2)) (Y : ι → Set (Space (k+2)))
    (assignment : ι → β) (normal : β → Space (k+1)) {δ R s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsmall : 2*((6+R)*δ) ≤ s)
    (hangle : ∀ i, 0 < projectiveDistance stem.direction (bristle i).direction)
    (hmeet : ∀ i, (stem.carrier δ ∩ (bristle i).carrier δ).Nonempty)
    (hunit : ∀ j, ‖normal j‖ = 1)
    (hsep : ∀ a b, a ≠ b → δ ≤ projectiveDistance (normal a) (normal b))
    (hbin : ∀ i, projectiveDistance (bristleNormal stem (bristle i)) (normal (assignment i)) ≤ δ)
    (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hball : ∀ i x, x ∈ Y i → ‖x-stem.base‖ ≤ R)
    (hfar : ∀ i x, x ∈ Y i → s ≤ ‖transverseCoordinate (alignStem stem.direction) (x-stem.base)‖)
    (x : Space (k+2)) :
    (overlapCount (binUnion assignment Y) x:ℝ) ≤ packingConstant k*(4*(6+R)/s)^k := by
  classical
  let active := Finset.univ.filter (fun j => x ∈ binUnion assignment Y j)
  by_cases ha : active.Nonempty
  · obtain ⟨j,hj⟩ := ha
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (Finset.mem_filter.mp hj).2
    have hdist := hfar i.1 x hi
    apply plane_bin_overlap (alignStem stem.direction) stem.base x active normal hδ
      (by linarith : 1 ≤ 6+R) hs hs1 hdist hsmall
      (fun j _ => hunit j) ?_ (fun a _ b _ hab => hsep a b hab)
    intro j hj
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (Finset.mem_filter.mp hj).2
    have hp := assigned_shading_plank stem bristle Y assignment normal hδ hδ1 hangle hmeet hbin hsub hball i.1 hi
    rwa [i.property] at hp
  · have he : active = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    have hc := packingConstant_ge_one k
    change (active.card:ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

omit [DecidableEq β] in
/-- Equation (4.12) as an actual measurable union inequality, with the overlap
bound derived from bristle and plane geometry. -/
theorem bin_union_volume_overlap {k : ℕ} (stem : UnitTube (k+2))
    (bristle : ι → UnitTube (k+2)) (Y : ι → Set (Space (k+2)))
    (assignment : ι → β) (normal : β → Space (k+1)) {δ R s : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsmall : 2*((6+R)*δ) ≤ s)
    (hangle : ∀ i, 0 < projectiveDistance stem.direction (bristle i).direction)
    (hmeet : ∀ i, (stem.carrier δ ∩ (bristle i).carrier δ).Nonempty)
    (hunit : ∀ j, ‖normal j‖ = 1)
    (hsep : ∀ a b, a ≠ b → δ ≤ projectiveDistance (normal a) (normal b))
    (hbin : ∀ i, projectiveDistance (bristleNormal stem (bristle i)) (normal (assignment i)) ≤ δ)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hball : ∀ i x, x ∈ Y i → ‖x-stem.base‖ ≤ R)
    (hfar : ∀ i x, x ∈ Y i → s ≤ ‖transverseCoordinate (alignStem stem.direction) (x-stem.base)‖) :
    (∑ j, (volume : Measure (Space (k+2))).real (binUnion assignment Y j)) ≤
      (packingConstant k*(4*(6+R)/s)^k)*(volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  have hmeas (j : β) : MeasurableSet (binUnion assignment Y j) := MeasurableSet.iUnion (fun i => hY i.1)
  have hfin (j : β) : (volume : Measure (Space (k+2))) (binUnion assignment Y j) ≠ ∞ := by
    simpa only [binUnion,Set.biUnion_univ] using
      measure_biUnion_ne_top (μ := (volume : Measure (Space (k+2))))
        (s := (Set.univ : Set {i : ι // assignment i = j})) (f := fun i => Y i.1)
        (Set.toFinite _) (fun i _ => measure_ne_top_of_subset (hsub i.1) (TubeVolume.carrier_finite (bristle i.1) δ))
  have h := finite_union_overlap (binUnion assignment Y) hmeas hfin
    (bin_union_overlap_count stem bristle Y assignment normal hδ hδ1 hR hs hs1 hsmall
      hangle hmeet hunit hsep hbin hsub hball hfar)
  rwa [union_binUnion] at h

/-- The explicit dimensional and location constant after combining plane-bin
packing with the actual planar intersection energy. -/
def hairbrushConstant (k : ℕ) (R : ℝ) : ℝ :=
  packingConstant k*(4*(6+R))^k*rowConstant k

omit [Fintype ι] [Fintype β] [DecidableEq β] in
 theorem hairbrushConstant_pos (k : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 < hairbrushConstant k R := by
  have hp := packingConstant_ge_one k
  have hr := rowConstant_pos k
  unfold hairbrushConstant
  positivity

/-- Sum the actual per-bin union estimates and the actual geometric multiplicity.
This is the geometric and measurable part of (4.15), before estimating the
number of bristles by stem incidences. -/
theorem assigned_hairbrush_union_lower {k : ℕ} (stem : UnitTube (k+2))
    (bristle : ι → UnitTube (k+2)) (Y : ι → Set (Space (k+2)))
    (assignment : ι → β) (normal : β → Space (k+1)) {δ R s lam L : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1/2) (hR : 0 ≤ R) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsmall : 2*((6+R)*δ) ≤ s) (hlam : 0 ≤ lam) (hL : 0 < L)
    (hlogL : Real.logb 2 (2/δ)+2 ≤ L)
    (hangle : ∀ i, 0 < projectiveDistance stem.direction (bristle i).direction)
    (hmeet : ∀ i, (stem.carrier δ ∩ (bristle i).carrier δ).Nonempty)
    (hunit : ∀ j, ‖normal j‖ = 1)
    (hsep : ∀ a b, a ≠ b → δ ≤ projectiveDistance (normal a) (normal b))
    (hbin : ∀ i, projectiveDistance (bristleNormal stem (bristle i)) (normal (assignment i)) ≤ δ)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (bristle i).direction (bristle j).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hball : ∀ i x, x ∈ Y i → ‖x-stem.base‖ ≤ R)
    (hfar : ∀ i x, x ∈ Y i → s ≤ ‖transverseCoordinate (alignStem stem.direction) (x-stem.base)‖)
    (hmass : ∀ i, lam*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real (Y i)) :
    (Fintype.card ι:ℝ)*lam^2*δ^(k+1)*s^k/(hairbrushConstant k R*L^3) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  classical
  have hbinlower (j : β) :
      (Fintype.card {i : ι // assignment i = j}:ℝ)*lam^2*δ^(k+1)/(rowConstant k*L^3) ≤
        (volume : Measure (Space (k+2))).real (binUnion assignment Y j) := by
    apply planar_density_union_lower stem (fun i : {i : ι // assignment i = j} => bristle i.1)
      (fun i => Y i.1) (normal j) hδ hδsmall (hunit j) hlam hL hlogL
    · intro i
      simpa only [i.property] using hbin i.1
    · intro i l hil
      exact hdir i.1 l.1 (fun he => hil (Subtype.ext he))
    · exact fun i => hY i.1
    · exact fun i => hsub i.1
    · exact fun i => hmass i.1
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset β)) => hbinlower j)
  rw [← Finset.sum_div,← Finset.sum_mul,← Finset.sum_mul,sum_bin_card] at hsum
  have hover := bin_union_volume_overlap stem bristle Y assignment normal hδ
    (by linarith) hR hs hs1 hsmall hangle hmeet hunit hsep hbin hY hsub hball hfar
  have htot := hsum.trans hover
  have hp := packingConstant_ge_one k
  have hr := rowConstant_pos k
  have hK : 0 < packingConstant k*(4*(6+R)/s)^k := by positivity
  have hdiv : ((Fintype.card ι:ℝ)*lam^2*δ^(k+1)/(rowConstant k*L^3))/
      (packingConstant k*(4*(6+R)/s)^k) ≤
        (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
    apply (div_le_iff₀ hK).mpr
    simpa only [mul_comm (packingConstant k*(4*(6+R)/s)^k)] using htot
  have hid : (Fintype.card ι:ℝ)*lam^2*δ^(k+1)*s^k/(hairbrushConstant k R*L^3) =
      ((Fintype.card ι:ℝ)*lam^2*δ^(k+1)/(rowConstant k*L^3))/
        (packingConstant k*(4*(6+R)/s)^k) := by
    unfold hairbrushConstant
    rw [div_pow]
    field_simp
  rwa [← hid] at hdiv

omit [Fintype β] [DecidableEq β] in
/-- Construct the plane bins from the actual finite bristle directions and obtain
the hairbrush union lower bound. No bin assignment, packing bound, overlap
estimate, or planar energy inequality is assumed. -/
theorem far_hairbrush_union_lower {k : ℕ} (stem : UnitTube (k+2))
    (bristle : ι → UnitTube (k+2)) (Y : ι → Set (Space (k+2))) {δ R s lam L : ℝ}
    (hδ : 0 < δ) (hδsmall : δ ≤ 1/2) (hR : 0 ≤ R) (hs : 0 < s) (hs1 : s ≤ 1)
    (hsmall : 2*((6+R)*δ) ≤ s) (hlam : 0 ≤ lam) (hL : 0 < L)
    (hlogL : Real.logb 2 (2/δ)+2 ≤ L)
    (hangle : ∀ i, 0 < projectiveDistance stem.direction (bristle i).direction)
    (hmeet : ∀ i, (stem.carrier δ ∩ (bristle i).carrier δ).Nonempty)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (bristle i).direction (bristle j).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (bristle i).carrier δ)
    (hball : ∀ i x, x ∈ Y i → ‖x-stem.base‖ ≤ R)
    (hfar : ∀ i x, x ∈ Y i → s ≤ ‖transverseCoordinate (alignStem stem.direction) (x-stem.base)‖)
    (hmass : ∀ i, lam*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real (Y i)) :
    (Fintype.card ι:ℝ)*lam^2*δ^(k+1)*s^k/(hairbrushConstant k R*L^3) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  classical
  let normals := fun i => bristleNormal stem (bristle i)
  obtain ⟨net,_,hsep,hcover⟩ := CapCover.finite_projective_net Finset.univ normals hδ
  have hchoose (i : ι) : ∃ j : {j : ι // j ∈ net}, projectiveDistance (normals i) (normals j.1) ≤ δ := by
    obtain ⟨j,hj,hij⟩ := hcover i (Finset.mem_univ i)
    exact ⟨⟨j,hj⟩,hij.le⟩
  let assignment := fun i => Classical.choose (hchoose i)
  apply assigned_hairbrush_union_lower stem bristle Y assignment (fun j => normals j.1)
    hδ hδsmall hR hs hs1 hsmall hlam hL hlogL hangle hmeet
  · exact fun j => bristleNormal_unit stem (bristle j.1) (hangle j.1)
  · intro a b hab
    exact hsep a.1 a.2 b.1 b.2 (fun he => hab (Subtype.ext he))
  · exact fun i => Classical.choose_spec (hchoose i)
  · exact hdir
  · exact hY
  · exact hsub
  · exact hball
  · exact hfar
  · exact hmass

end
end KakeyaFormal.HairbrushUnion
