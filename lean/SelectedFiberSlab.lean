import SelectedFiberLift
import OccupancySelection

/-! Actual fullest-unit-slab selection and nonempty common integer trimming for
the populated lifted graph cells of one selected original angle-output fiber. -/
namespace KakeyaFormal.SelectedFiberSlab
open Finset PivotOutputCount PivotWitnesses SelectedFiberLift EuclideanSplit
open scoped BigOperators
noncomputable section
open Classical

variable {k : ℕ} {kap δ width : ℝ} {a : Angle k kap} {fc sc : Cell k → ℝ}

/-- The legal time range follows from actual common-pivot rounding, provided
only the explicit scalar perturbation room required by the existing theorem. -/
theorem lift_time_bounds (reference s : LabeledPair a δ width fc sc)
    (hδ : 0 < δ) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hpivot : s.pivotLabel = reference.pivotLabel) (hscale : (k : ℝ)*δ ≤ kap^5/4) :
    1+kap/2 ≤ s.endpoints.secondCoord/reference.endpoints.coefficient ∧
      s.endpoints.secondCoord/reference.endpoints.coefficient ≤ 2/kap := by
  have hh := rounded_coefficient_gap reference s hδ hpivot.symm
  exact KakeyaAudit.TubeGeometry.normalized_perturbed_lift_range hk hk1 a.intermediate_lower
    s.gap s.first_upper s.second_lower s.second_upper hh hscale

/-- The chosen grid-cell center height is nonnegative and at most 3/kappa. -/
theorem lifted_center_height (reference s : LabeledPair a δ width fc sc)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hpivot : s.pivotLabel = reference.pivotLabel) (hscale : (k : ℝ)*δ ≤ kap^5/4) :
    0 ≤ δ*((liftedCell reference s 0 : ℤ) : ℝ) ∧
      δ*((liftedCell reference s 0 : ℤ) : ℝ) ≤ 3/kap := by
  have ht := lift_time_bounds reference s hδ hk hk1 hpivot hscale
  have hg := (GridCells.mem_gridCell δ (liftedCell reference s) (liftedPoint reference s)).mp
    (GridCells.gridCell_covers hδ _) 0
  change δ*(((liftedCell reference s 0 : ℤ) : ℝ)-1/2) ≤
      s.endpoints.secondCoord/reference.endpoints.coefficient ∧
    s.endpoints.secondCoord/reference.endpoints.coefficient <
      δ*(((liftedCell reference s 0 : ℤ) : ℝ)+1/2) at hg
  have hr : (1:ℝ) ≤ 1/kap := (le_div_iff₀ hk).mpr (by simpa using hk1)
  constructor
  · linarith [ht.1,hg.2]
  · simp only [div_eq_mul_inv] at ht hg hr ⊢
    linarith [hg.1]

/-- Unit-slab selection on actual grid centers, with the full finite slab
classification constructed and at most 5/kappa available classes. -/
theorem unit_slab_selection (V : Finset (Cell (k+1))) (hV : V.Nonempty)
    (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hheight : ∀ z ∈ V, 0 ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) ≤ 3/kap) :
    ∃ j ≤ Nat.ceil (3/kap), ∃ R : Finset (Cell (k+1)), R ⊆ V ∧ R.Nonempty ∧
      (∀ z ∈ R, (j : ℝ) ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) < (j : ℝ)+1) ∧
      kap*(V.card : ℝ)/5 ≤ (R.card : ℝ) := by
  let J := Nat.ceil (3/kap)+1
  have hJ : 0 < J := Nat.succ_pos _
  have hbound (z) (hz : z ∈ V) : Nat.floor (δ*(z 0 : ℝ)) < J := by
    have hh := (Nat.floor_le (hheight z hz).1).trans ((hheight z hz).2.trans (Nat.le_ceil (3/kap)))
    have hn : Nat.floor (δ*(z 0 : ℝ)) ≤ Nat.ceil (3/kap) := by exact_mod_cast hh
    dsimp [J]
    omega
  let slab : Cell (k+1) → Fin J := fun z => if hz : z ∈ V then
    ⟨Nat.floor (δ*(z 0 : ℝ)),hbound z hz⟩ else ⟨0,hJ⟩
  obtain ⟨j,hj⟩ := OccupancySelection.weighted_class_selection V (fun _ => (1:ℝ)) hJ slab
  let R := V.filter (fun z => slab z = j)
  have hsel : (V.card : ℝ)/(J : ℝ) ≤ (R.card : ℝ) := by simpa only [sum_const,nsmul_eq_mul,mul_one] using hj
  have hR : R.Nonempty := by
    have hcardV : 0 < (V.card : ℝ) := by exact_mod_cast card_pos.mpr hV
    have hh : 0 < (R.card : ℝ) := (div_pos hcardV (by positivity)).trans_le hsel
    exact card_pos.mp (by exact_mod_cast hh)
  have hJupper : (J : ℝ) ≤ 5/kap := by
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ 3/kap by positivity)
    have hr : (1:ℝ) ≤ 1/kap := (le_div_iff₀ hk).mpr (by simpa using hk1)
    dsimp [J]
    push_cast
    simp only [div_eq_mul_inv] at hceil hr ⊢
    linarith
  have hmass : kap*(V.card : ℝ)/5 ≤ (R.card : ℝ) := by
    have hh := (div_le_div_of_nonneg_left (Nat.cast_nonneg V.card) (show (0:ℝ) < J by positivity) hJupper).trans hsel
    convert hh using 1 <;> first | rfl | field_simp
  refine ⟨j.val,by have := j.isLt; dsimp [J] at this; omega,R,filter_subset _ _,hR,?_,hmass⟩
  intro z hz
  obtain ⟨hzV,hzj⟩ := mem_filter.mp hz
  have heq : Nat.floor (δ*(z 0 : ℝ)) = j.val := by
    simpa only [slab,dif_pos hzV] using congrArg Fin.val hzj
  have hlo := Nat.floor_le (hheight z hzV).1
  have hhi := Nat.lt_floor_add_one (δ*(z 0 : ℝ))
  exact ⟨by simpa only [heq] using hlo,by simpa only [heq] using hhi⟩

/-- One actual unit slab retains c*kappa^5 of the original selected sample mass
as distinct lifted grid cells. -/
theorem populated_slab (reference : LabeledPair a δ width fc sc)
    (S : Finset (LabeledPair a δ width fc sc)) (hS : S.Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hpivot : ∀ s ∈ S, s.pivotLabel = reference.pivotLabel)
    (hscale : (k : ℝ)*δ ≤ kap^5/4) :
    ∃ j ≤ Nat.ceil (3/kap), ∃ R : Finset (Cell (k+1)), R ⊆ liftedCells reference S ∧ R.Nonempty ∧
      (∀ z ∈ R, (j : ℝ) ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) < (j : ℝ)+1) ∧
      kap^5*(S.card : ℝ)/(5*multiplicityConstant k width) ≤ (R.card : ℝ) := by
  have hV : (liftedCells reference S).Nonempty := hS.image (liftedCell reference)
  have hheight (z) (hz : z ∈ liftedCells reference S) :
      0 ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) ≤ 3/kap := by
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
    exact lifted_center_height reference s hδ hδ1 hk hk1 (hpivot s hs) hscale
  obtain ⟨j,hj,R,hRsub,hR,hslab,hmass⟩ := unit_slab_selection (liftedCells reference S) hV hk hk1 hheight
  have hp := lifted_population reference S reference.pivotLabel hδ hk hk1 hpivot
  have hh := (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hk.le) (by norm_num : (0:ℝ) ≤ 5)).trans hmass
  refine ⟨j,hj,R,hRsub,hR,hslab,?_⟩
  convert hh using 1 <;> first | rfl | ring

/-- One common nonzero integer depends only on kappa and the original sample
fiber cardinality, so equal-cardinality fibers use precisely the same K. -/
def commonCount (k : ℕ) (width kap : ℝ) (h : ℕ) : ℕ :=
  max 1 (Nat.floor (kap^6*(h : ℝ)/(10*multiplicityConstant k width)))

/-- Full actual slab selection, common integer trimming, and one original
sample representative per retained lifted cell. -/
theorem common_integer_slab (reference : LabeledPair a δ width fc sc)
    (S : Finset (LabeledPair a δ width fc sc)) (hS : S.Nonempty)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hpivot : ∀ s ∈ S, s.pivotLabel = reference.pivotLabel)
    (hscale : (k : ℝ)*δ ≤ kap^5/4) :
    let K := commonCount k width kap S.card
    1 ≤ K ∧ kap^6*(S.card : ℝ)/(20*multiplicityConstant k width) ≤ (K : ℝ) ∧
      (K : ℝ) ≤ kap^6*(S.card : ℝ)/(10*multiplicityConstant k width)+1 ∧
    ∃ j ≤ Nat.ceil (3/kap), ∃ V0 : Finset (Cell (k+1)), V0 ⊆ liftedCells reference S ∧ V0.card = K ∧
      (∀ z ∈ V0, (j : ℝ) ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) < (j : ℝ)+1) ∧
      ∃ representative : ↥V0 → LabeledPair a δ width fc sc,
        Function.Injective representative ∧
        ∀ z, representative z ∈ S ∧ liftedCell reference (representative z) = z.val := by
  intro K
  have hC := multiplicityConstant_pos k width
  let x := kap^6*(S.card : ℝ)/(10*multiplicityConstant k width)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hfloor := KakeyaFinite.nonempty_floor_truncation hx
  have hKlower : kap^6*(S.card : ℝ)/(20*multiplicityConstant k width) ≤ (K : ℝ) := by
    change _ ≤ ((max 1 (Nat.floor x) : ℕ) : ℝ)
    convert hfloor.1 using 1
    dsimp [x]
    ring
  have hKupper : (K : ℝ) ≤ kap^6*(S.card : ℝ)/(10*multiplicityConstant k width)+1 := hfloor.2
  obtain ⟨j,hj,R,hRsub,hR,hslab,hmass⟩ := populated_slab reference S hS hδ hδ1 hk hk1 hpivot hscale
  have hxbound : x ≤ kap^5*(S.card : ℝ)/(5*multiplicityConstant k width) := by
    have hp : kap^6 ≤ kap^5 := by
      have hh := mul_le_mul_of_nonneg_right hk1 (pow_pos hk 5).le
      nlinarith
    have hh := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg S.card)
    dsimp [x]
    have hc := div_le_div_of_nonneg_right hh (show 0 ≤ 10*multiplicityConstant k width by positivity)
    have ht : kap^5*(S.card : ℝ)/(10*multiplicityConstant k width) ≤ kap^5*(S.card : ℝ)/(5*multiplicityConstant k width) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    exact hc.trans ht
  have hKcard : K ≤ R.card := by
    apply max_le (card_pos.mpr hR)
    have hh := (Nat.floor_le hx).trans (hxbound.trans hmass)
    exact_mod_cast hh
  obtain ⟨V0,hV0,hcard⟩ := exists_subset_card_eq hKcard
  have hVsub : V0 ⊆ liftedCells reference S := hV0.trans hRsub
  have hrep (z : ↥V0) : ∃ s ∈ S, liftedCell reference s = z.val := mem_image.mp (hVsub z.property)
  choose representative hrepMem hrepEq using hrep
  refine ⟨le_max_left _ _,hKlower,hKupper,j,hj,V0,hVsub,hcard,fun z hz => hslab z (hV0 hz),
    representative,?_,fun z => ⟨hrepMem z,hrepEq z⟩⟩
  intro z w heq
  apply Subtype.val_injective
  exact (hrepEq z).symm.trans ((congrArg (liftedCell reference) heq).trans (hrepEq w))


/-- The common integer density also has a uniform upper bound, derived from
the actual original pivot-fiber count rather than a separate size assumption. -/
theorem common_density_upper (reference : LabeledPair a δ width fc sc)
    (S : Finset (LabeledPair a δ width fc sc))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hpivot : ∀ s ∈ S, s.pivotLabel = reference.pivotLabel) :
    δ*(commonCount k width kap S.card : ℝ) ≤
      1+fiberConstant k width/(10*multiplicityConstant k width) := by
  have hC := multiplicityConstant_pos k width
  have hF : 0 ≤ fiberConstant k width := by
    have := (boxConstant_pos k width).le
    dsimp [fiberConstant]
    positivity
  have hf := pivot_fiber_count S reference.pivotLabel hδ hδ1 hk hk1
  rw [filter_eq_self.mpr hpivot] at hf
  have hmass := (le_div_iff₀ (mul_pos hk hδ)).mp hf
  have hk5 : kap^5 ≤ 1 := pow_le_one₀ hk.le hk1
  have hh := (mul_le_mul_of_nonneg_left hmass (pow_pos hk 5).le).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hk5 hF)
  have hscaled : kap^6*(S.card : ℝ)*δ ≤ fiberConstant k width := by
    convert hh using 1 <;> first | rfl | ring
  have hx : 0 ≤ kap^6*(S.card : ℝ)/(10*multiplicityConstant k width) := by positivity
  have hK := (KakeyaFinite.nonempty_floor_truncation hx).2
  change (commonCount k width kap S.card : ℝ) ≤ _ at hK
  have hm := mul_le_mul_of_nonneg_left hK hδ.le
  calc
    _ ≤ δ*(kap^6*(S.card : ℝ)/(10*multiplicityConstant k width)+1) := hm
    _ = kap^6*(S.card : ℝ)*δ/(10*multiplicityConstant k width)+δ := by ring
    _ ≤ fiberConstant k width/(10*multiplicityConstant k width)+1 :=
      add_le_add (div_le_div_of_nonneg_right hscaled (by positivity)) hδ1
    _ = _ := by ring

end
end KakeyaFormal.SelectedFiberSlab

#print axioms KakeyaFormal.SelectedFiberSlab.lift_time_bounds
#print axioms KakeyaFormal.SelectedFiberSlab.unit_slab_selection
#print axioms KakeyaFormal.SelectedFiberSlab.populated_slab
#print axioms KakeyaFormal.SelectedFiberSlab.common_integer_slab
#print axioms KakeyaFormal.SelectedFiberSlab.common_density_upper
