import ProjectiveGeometry

/-!
# A finite radius-one projective cap cover and the real-cap total tube count

The covering centers are selected from the original finite indexed family.
Maximality and the full-dimensional packing theorem give a dimension-only
number of centers, while the original (possibly fractional-m) cap estimate is
used to count each covered block. No fractional packing theorem is assumed.
-/
namespace KakeyaFormal.CapCover
open KakeyaFormal.ProjectiveGeometry
noncomputable section

/-- An actual finite indexed subfamily with pairwise projective separation. -/
def SeparatedOn {k : ℕ} {ι : Type*} (direction : ι → Space k)
    (radius : ℝ) (indices : Finset ι) : Prop :=
  ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j → radius ≤ projectiveDistance (direction i) (direction j)

/-- A maximum-cardinality separated subset is an actual covering net. -/
theorem finite_projective_net {k : ℕ} {ι : Type*} (points : Finset ι)
    (direction : ι → Space k) {radius : ℝ} (hr : 0 < radius) :
    ∃ net ⊆ points, SeparatedOn direction radius net ∧
      ∀ i ∈ points, ∃ j ∈ net, projectiveDistance (direction i) (direction j) < radius := by
  classical
  let candidates := points.powerset.filter (SeparatedOn direction radius)
  have hne : candidates.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _), ?_⟩⟩
    intro i hi
    exact False.elim (Finset.notMem_empty _ hi)
  obtain ⟨net, hn, hmax⟩ := candidates.exists_max_image Finset.card hne
  have hsub : net ⊆ points := Finset.mem_powerset.mp (Finset.mem_filter.mp hn).1
  have hsep : SeparatedOn direction radius net := (Finset.mem_filter.mp hn).2
  refine ⟨net,hsub,hsep,?_⟩
  intro i hi
  by_contra hcover
  have hnew : ∀ j ∈ net, radius ≤ projectiveDistance (direction i) (direction j) := by
    intro j hj
    exact le_of_not_gt (fun hlt => hcover ⟨j,hj,hlt⟩)
  have hin : i ∉ net := by
    intro hmem
    have hz := hnew i hmem
    rw [projectiveDistance_self] at hz
    linarith
  have hins : SeparatedOn direction radius (insert i net) := by
    intro a ha b hb hab
    rcases Finset.mem_insert.mp ha with haeq | hanet
    · subst a
      rcases Finset.mem_insert.mp hb with hbeq | hbnet
      · exact False.elim (hab hbeq.symm)
      · exact hnew b hbnet
    · rcases Finset.mem_insert.mp hb with hbeq | hbnet
      · subst b
        rw [projective_symm]
        exact hnew a hanet
      · exact hsep a hanet b hbnet hab
  have hmem : insert i net ∈ candidates := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset hi hsub), hins⟩
  have hcard := hmax (insert i net) hmem
  rw [Finset.card_insert_of_notMem hin] at hcard
  omega

/-- A uniformly bounded finite radius-one projective cap cover of actual unit directions.
The original family need not itself be separated. -/
theorem unit_direction_cap_cover {k : ℕ} {ι : Type*} (points : Finset ι)
    (direction : ι → Space (k+1)) (hunit : ∀ i ∈ points, ‖direction i‖ = 1) :
    ∃ net ⊆ points, (net.card : ℝ) ≤ packingConstant k ∧
      ∀ i ∈ points, ∃ j ∈ net, projectiveDistance (direction i) (direction j) ≤ 1 := by
  obtain ⟨net,hsub,hsep,hcover⟩ := finite_projective_net points direction (show (0:ℝ) < 1 by norm_num)
  refine ⟨net,hsub,?_,?_⟩
  · have h := indexed_projective_cap_packing net direction (0 : Space (k+1))
      (show (0:ℝ) < 1 by norm_num) (show (1:ℝ) ≤ 1 by rfl)
      (fun i hi => hunit i (hsub hi))
      (fun i hi => by simp [projectiveDistance,hunit i (hsub hi)]) hsep
    simpa [packingConstant] using h
  · intro i hi
    obtain ⟨j,hj,hij⟩ := hcover i hi
    exact ⟨j,hj,hij.le⟩

/-- A real direction-cap hypothesis implies total count with the *same real m*.
The only packing used is for the radius-one covering net, whose size is dimensional. -/
theorem cap_bound_total_count {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ m A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A)
    (hcap : F.CapBound δ m A) :
    (M:ℝ) ≤ packingConstant k * A * (1/δ)^m := by
  classical
  obtain ⟨net,_,hnet,hcover⟩ := unit_direction_cap_cover
    (Finset.univ : Finset (Fin M)) (fun i => (F.tube i).direction)
    (fun i _ => (F.tube i).unit_direction)
  let caps : Fin M → Finset (Fin M) := fun j =>
    Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction (F.tube j).direction ≤ 1)
  have hsub : (Finset.univ : Finset (Fin M)) ⊆ net.biUnion caps := by
    intro i hi
    obtain ⟨j,hj,hij⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩⟩
  have hcount := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  simp only [Finset.card_univ,Fintype.card_fin] at hcount
  have hcountR : (M:ℝ) ≤ ∑ j ∈ net, ((caps j).card : ℝ) := by
    exact_mod_cast hcount
  have hcapj (j : Fin M) : ((caps j).card : ℝ) ≤ A*(1/δ)^m :=
    hcap (F.tube j).direction (F.tube j).unit_direction 1 hδ1 (by rfl)
  have hcoef : (0:ℝ) ≤ A*(1/δ)^m := mul_nonneg hA (Real.rpow_nonneg (by positivity) _)
  calc
    _ ≤ ∑ j ∈ net, ((caps j).card : ℝ) := hcountR
    _ ≤ ∑ _j ∈ net, A*(1/δ)^m := Finset.sum_le_sum (fun j _ => hcapj j)
    _ = (net.card : ℝ)*(A*(1/δ)^m) := by simp
    _ ≤ packingConstant k*(A*(1/δ)^m) := mul_le_mul_of_nonneg_right hnet hcoef
    _ = _ := by ring

/-- Equivalent inverse-scale notation, convenient for the bush estimate. -/
theorem cap_bound_total_count_scale {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ m A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A)
    (hcap : F.CapBound δ m A) :
    (M:ℝ) ≤ packingConstant k * A * δ^(-m) := by
  have h := cap_bound_total_count F hδ hδ1 hA hcap
  simpa only [one_div,Real.inv_rpow hδ.le,Real.rpow_neg hδ.le] using h

end
end KakeyaFormal.CapCover
