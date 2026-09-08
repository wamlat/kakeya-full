import HairbrushStem

/-!
# Actual measurable dyadic multiplicity and stem selection

The shell and stem are constructed from genuine measurable shadings and marked
mass. All level-set measurability, finite measure, incidence summation, and
weighted averaging are proved rather than supplied as selection hypotheses.
-/
namespace KakeyaFormal.HairbrushSelection
open MeasureTheory
open scoped ENNReal
open KakeyaFormal.MeasurableEnergy KakeyaFormal.PlanarEnergy
noncomputable section
variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {ι : Type*} [Fintype ι]

def markedMass (Y : ι → Set X) (G : Set X) : ℝ := ∑ i, ν.real (Y i ∩ G)

def multiplicityShell (Y : ι → Set X) (G : Set X) (j : ℕ) : Set X :=
  G ∩ {x | shellCondition 1 (MeasurableEnergy.multiplicity Y x) j}

theorem multiplicity_measurable (Y : ι → Set X) (hY : ∀ i, MeasurableSet (Y i)) :
    Measurable (MeasurableEnergy.multiplicity Y) := by
  exact Finset.measurable_sum Finset.univ (fun i _ => measurable_const.indicator (hY i))

theorem shell_measurable (Y : ι → Set X) (G : Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (hG : MeasurableSet G) (j : ℕ) :
    MeasurableSet (multiplicityShell Y G j) := by
  apply hG.inter
  by_cases hj : j = 0
  · simpa only [shellCondition,if_pos hj] using measurableSet_le (multiplicity_measurable Y hY) measurable_const
  · simpa only [shellCondition,if_neg hj,Set.ofPred_and] using
      (measurableSet_lt measurable_const (multiplicity_measurable Y hY)).inter
        (measurableSet_le (multiplicity_measurable Y hY) measurable_const)

omit [MeasurableSpace X] in
 theorem multiplicity_le_card (Y : ι → Set X) (x : X) :
    MeasurableEnergy.multiplicity Y x ≤ (Fintype.card ι:ℝ) := by
  classical
  rw [multiplicity_eq_card]
  exact_mod_cast (Finset.card_filter_le (s := (Finset.univ : Finset ι)) (p := fun i => x ∈ Y i))

omit [MeasurableSpace X] in
 theorem multiplicity_ge_one (Y : ι → Set X) {x : X} (hx : x ∈ ⋃ i, Y i) :
    1 ≤ MeasurableEnergy.multiplicity Y x := by
  classical
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  rw [multiplicity_eq_card]
  have hne : (Finset.univ.filter fun j => x ∈ Y j).Nonempty := ⟨i,by simp [hi]⟩
  exact_mod_cast Finset.card_pos.mpr hne

omit [MeasurableSpace X] in
 theorem shell_bounds (Y : ι → Set X) (G : Set X) {x : X} {j : ℕ}
    (hx : x ∈ multiplicityShell Y G j) (hpos : x ∈ ⋃ i, Y i) :
    (2:ℝ)^j/2 ≤ MeasurableEnergy.multiplicity Y x ∧
      MeasurableEnergy.multiplicity Y x ≤ (2:ℝ)^j := by
  have h := hx.2
  by_cases hj : j = 0
  · subst j
    have hlow := multiplicity_ge_one Y hpos
    simp only [shellCondition,↓reduceIte] at h
    exact ⟨by norm_num; linarith,by simpa using h⟩
  · obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
    simp only [shellCondition,Nat.succ_ne_zero,↓reduceIte,Nat.succ_sub_one,one_mul] at h
    rw [pow_succ]
    exact ⟨by linarith [h.1],h.2⟩

/-- Actual finitely many dyadic shells cover every original marked incidence. -/
theorem shell_mass_cover (Y : ι → Set X) (G : Set X)
    (hfin : ∀ i, ν (Y i) ≠ ∞) (J : ℕ) (htop : (Fintype.card ι:ℝ) ≤ (2:ℝ)^J) :
    markedMass (ν := ν) Y G ≤
      ∑ j ∈ Finset.range (J+1), markedMass (ν := ν) Y (multiplicityShell Y G j) := by
  have hterm (i : ι) : ν.real (Y i ∩ G) ≤
      ∑ j ∈ Finset.range (J+1), ν.real (Y i ∩ multiplicityShell Y G j) := by
    have hcover : Y i ∩ G ⊆ ⋃ j ∈ Finset.range (J+1), Y i ∩ multiplicityShell Y G j := by
      intro x hx
      obtain ⟨j,hj,hcond⟩ := exists_shell (δ := (1:ℝ)) J
        (by simpa using (multiplicity_le_card Y x).trans htop)
      exact Set.mem_iUnion₂.mpr ⟨j,hj,hx.1,hx.2,hcond⟩
    have hf : ν (⋃ j ∈ Finset.range (J+1), Y i ∩ multiplicityShell Y G j) ≠ ∞ :=
      measure_ne_top_of_subset (by intro x hx; obtain ⟨j,_,hj⟩ := Set.mem_iUnion₂.mp hx; exact hj.1) (hfin i)
    exact (measureReal_mono hcover hf).trans
      (measureReal_biUnion_finset_le (Finset.range (J+1)) (fun j => Y i ∩ multiplicityShell Y G j))
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hterm i)
  rw [Finset.sum_comm] at h
  exact h

/-- One actual dyadic multiplicity shell retains a reciprocal-logarithmic
fraction of the original marked incidence measure. -/
theorem exists_mass_shell (Y : ι → Set X) (G : Set X)
    (hfin : ∀ i, ν (Y i) ≠ ∞) (J : ℕ) (htop : (Fintype.card ι:ℝ) ≤ (2:ℝ)^J) :
    ∃ j ∈ Finset.range (J+1), markedMass (ν := ν) Y G/((J:ℝ)+1) ≤
      markedMass (ν := ν) Y (multiplicityShell Y G j) := by
  have hsum : (∑ _j ∈ Finset.range (J+1), markedMass (ν := ν) Y G/((J:ℝ)+1)) ≤
      ∑ j ∈ Finset.range (J+1), markedMass (ν := ν) Y (multiplicityShell Y G j) := by
    simp only [Finset.sum_const,Finset.card_range,Nat.cast_add,Nat.cast_one,nsmul_eq_mul]
    have hid : ((J:ℝ)+1)*(markedMass (ν := ν) Y G/((J:ℝ)+1)) = markedMass (ν := ν) Y G := by
      field_simp
    rw [hid]
    exact shell_mass_cover Y G hfin J htop

  exact Finset.exists_le_of_sum_le (by simp : (Finset.range (J+1)).Nonempty) hsum

/-- A selected shell's marked mass is bounded by its actual maximum
multiplicity times the original physical union volume. -/
theorem shell_mass_union_upper (Y : ι → Set X) (G : Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (hG : MeasurableSet G)
    (hfin : ∀ i, ν (Y i) ≠ ∞) (j : ℕ) :
    markedMass (ν := ν) Y (multiplicityShell Y G j) ≤ (2:ℝ)^j*ν.real (⋃ i, Y i) := by
  let Z := fun i => Y i ∩ multiplicityShell Y G j
  have hZ (i : ι) := (hY i).inter (shell_measurable Y G hY hG j)
  have hf (i : ι) : ν (Z i) ≠ ∞ := measure_ne_top_of_subset Set.inter_subset_left (hfin i)
  have hpoint (x : X) : (overlapCount Z x:ℝ) ≤ (2:ℝ)^j := by
    classical
    rw [← multiplicity_eq_card]
    by_cases hx : x ∈ multiplicityShell Y G j
    · have hid : MeasurableEnergy.multiplicity Z x = MeasurableEnergy.multiplicity Y x := by
        simp [MeasurableEnergy.multiplicity,Z,oneIndicator,Set.indicator_apply,hx]
      rw [hid]
      have h := hx.2
      by_cases hj : j = 0
      · simpa [shellCondition,hj] using h
      · have hh : (2:ℝ)^(j-1) < MeasurableEnergy.multiplicity Y x ∧
            MeasurableEnergy.multiplicity Y x ≤ (2:ℝ)^j := by
          simpa only [shellCondition,if_neg hj,one_mul,Set.mem_ofPred_eq] using h
        exact hh.2
    · simp [MeasurableEnergy.multiplicity,Z,oneIndicator,hx]
  have h := finite_union_overlap Z hZ hf hpoint
  have hUf : ν (⋃ i, Y i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ := ν)
      (s := Set.univ) (f := Y) (Set.toFinite _) (fun i _ => hfin i)
  exact h.trans (mul_le_mul_of_nonneg_left
    (measureReal_mono (Set.iUnion_mono fun i => Set.inter_subset_left) hUf) (by positivity))

/-- Weighted averaging constructs an actual stem with the required marked
portion. No assumption about a retained stem is introduced. -/
theorem exists_stem_in_shell [Nonempty ι] (Y : ι → Set X) (G : Set X) {J j : ℕ}
    (hgood : (∑ i, ν.real (Y i))/2 ≤ markedMass (ν := ν) Y G)
    (hshell : markedMass (ν := ν) Y G/((J:ℝ)+1) ≤
      markedMass (ν := ν) Y (multiplicityShell Y G j)) :
    ∃ i : ι, ν.real (Y i)/(2*((J:ℝ)+1)) ≤ ν.real (Y i ∩ multiplicityShell Y G j) := by
  have hm := div_le_div_of_nonneg_right hgood (by positivity : 0 ≤ (J:ℝ)+1)
  have hsum : (∑ i, ν.real (Y i)/(2*((J:ℝ)+1))) ≤
      ∑ i, ν.real (Y i ∩ multiplicityShell Y G j) := by
    rw [← Finset.sum_div]
    calc
      _ = ((∑ i, ν.real (Y i))/2)/((J:ℝ)+1) := by field_simp
      _ ≤ _ := hm.trans hshell
  obtain ⟨i,_,hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨i,hi⟩

end
end KakeyaFormal.HairbrushSelection
