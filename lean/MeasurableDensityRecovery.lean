import HairbrushKernel

/-!
# Actual measurable density, marking and broadness recovery

Full, Ref and output shadings are actual finite measurable sets with
O_i ⊆ Ref_i ⊆ Full_i. Broadness is inherited from Ref, not assumed for O.
All tube selection, multiplicity marking, integration and mass recovery are
proved for actual measures before specializing to Euclidean tube directions.
-/
namespace KakeyaFormal.MeasurableDensityRecovery
open MeasureTheory
open scoped ENNReal
open KakeyaFormal.MeasurableEnergy KakeyaFormal.HairbrushSelection KakeyaFormal.HairbrushKernel
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {M : ℕ}

def good (ν : Measure X) (O : Fin M → Set X) (eta lam : ℝ) : Finset (Fin M) :=
  Finset.univ.filter (fun i => eta*lam/2 ≤ ν.real (O i))

def selectedIndex (ν : Measure X) (O : Fin M → Set X) (eta lam : ℝ)
    (i : Fin (good ν O eta lam).card) : Fin M := (good ν O eta lam).equivFin.symm i

def selected (ν : Measure X) (O : Fin M → Set X) (eta lam : ℝ) :
    Fin (good ν O eta lam).card → Set X := fun i => O (selectedIndex ν O eta lam i)

/-- An actual measurable mark: only points of a retained output can be marked. -/
def marked (ν : Measure X) (Ref O : Fin M → Set X) (eta lam : ℝ) : Set X :=
  (⋃ i, selected ν O eta lam i) ∩
    {x | (eta/8)*MeasurableEnergy.multiplicity Ref x ≤ MeasurableEnergy.multiplicity (selected ν O eta lam) x}

theorem selectedIndex_injective (ν : Measure X) (O : Fin M → Set X) (eta lam : ℝ) :
    Function.Injective (selectedIndex ν O eta lam) :=
  Subtype.val_injective.comp (good ν O eta lam).equivFin.symm.injective

theorem selectedIndex_mem (ν : Measure X) (O : Fin M → Set X) (eta lam : ℝ)
    (i : Fin (good ν O eta lam).card) : selectedIndex ν O eta lam i ∈ good ν O eta lam :=
  ((good ν O eta lam).equivFin.symm i).2

/-- Actual measure selection keeps at least half the retained mass budget and
at least ηM/4 original tubes. -/
theorem good_mass_and_count (O : Fin M → Set X) {eta lam : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam)
    (hupper : ∀ i, ν.real (O i) ≤ 2*lam)
    (hmass : eta*lam*M ≤ ∑ i, ν.real (O i)) :
    eta*lam*(M:ℝ)/2 ≤ ∑ i ∈ good ν O eta lam, ν.real (O i) ∧
      eta*(M:ℝ)/4 ≤ ((good ν O eta lam).card:ℝ) := by
  let a := eta*lam/2
  have hbad : (∑ i ∈ (Finset.univ : Finset (Fin M)).filter (fun i => ¬a ≤ ν.real (O i)), ν.real (O i)) ≤ a*M := by
    calc
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin M)).filter (fun i => ¬a ≤ ν.real (O i)), a :=
        Finset.sum_le_sum (fun i hi => (lt_of_not_ge (Finset.mem_filter.mp hi).2).le)
      _ = a*(((Finset.univ : Finset (Fin M)).filter (fun i => ¬a ≤ ν.real (O i))).card:ℝ) := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by exact_mod_cast (show ((Finset.univ : Finset (Fin M)).filter (fun i => ¬a ≤ ν.real (O i))).card ≤ M by
          simpa using Finset.card_filter_le (Finset.univ : Finset (Fin M)) (fun i => ¬a ≤ ν.real (O i))))
        (by dsimp [a]; positivity)
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin M)))
    (fun i => a ≤ ν.real (O i)) (fun i => ν.real (O i))
  have hgood : eta*lam*(M:ℝ)/2 ≤ ∑ i ∈ good ν O eta lam, ν.real (O i) := by
    change (∑ i ∈ good ν O eta lam, ν.real (O i))+_ = _ at hsplit
    dsimp [a] at hbad
    linarith
  have htotal : (∑ i ∈ good ν O eta lam, ν.real (O i)) ≤ 2*lam*((good ν O eta lam).card:ℝ) := by
    exact (Finset.sum_le_sum (fun i _ => hupper i)).trans_eq (by simp [mul_comm])
  refine ⟨hgood,?_⟩
  have hh := hgood.trans htotal
  nlinarith

/-- Reindexing leaves the exact selected measure sum unchanged. -/
theorem selected_mass (O : Fin M → Set X) (eta lam : ℝ) :
    (∑ i, ν.real (selected ν O eta lam i)) = ∑ i ∈ good ν O eta lam, ν.real (O i) := by
  have h₁ := (good ν O eta lam).equivFin.symm.sum_comp (fun i : good ν O eta lam => ν.real (O i.1))
  have h₂ : (∑ i ∈ good ν O eta lam, ν.real (O i)) = ∑ i : good ν O eta lam, ν.real (O i.1) :=
    Finset.sum_subtype (good ν O eta lam) (fun _ => Iff.rfl) (fun i => ν.real (O i))
  exact h₁.trans h₂.symm

theorem selected_measurable (O : Fin M → Set X) (eta lam : ℝ)
    (hO : ∀ i, MeasurableSet (O i)) : ∀ i, MeasurableSet (selected ν O eta lam i) :=
  fun i => hO (selectedIndex ν O eta lam i)

theorem marked_measurable (Ref O : Fin M → Set X) (eta lam : ℝ)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hO : ∀ i, MeasurableSet (O i)) :
    MeasurableSet (marked ν Ref O eta lam) := by
  have hY := selected_measurable (ν := ν) O eta lam hO
  exact (MeasurableSet.iUnion hY).inter (measurableSet_le
    ((multiplicity_measurable Ref hRef).const_mul (eta/8)) (multiplicity_measurable _ hY))

omit [MeasurableSpace X] in
 theorem multiplicity_nonneg {I : Type*} [Fintype I] (Y : I → Set X) (x : X) :
    0 ≤ MeasurableEnergy.multiplicity Y x := by
  rw [multiplicity_eq_card]
  positivity

/-- Outside the actual marked set the selected-output incidence is controlled
by η/8 of the actual Ref incidence, including points outside the selected union. -/
theorem discarded_pointwise (Ref O : Fin M → Set X) {eta lam : ℝ} (heta : 0 ≤ eta) (x : X) :
    MeasurableEnergy.multiplicity (fun i => selected ν O eta lam i \ marked ν Ref O eta lam) x ≤
      (eta/8)*MeasurableEnergy.multiplicity Ref x := by
  classical
  by_cases hx : x ∈ marked ν Ref O eta lam
  · have hz : MeasurableEnergy.multiplicity (fun i => selected ν O eta lam i \ marked ν Ref O eta lam) x = 0 := by
      simp [MeasurableEnergy.multiplicity,oneIndicator,hx]
    rw [hz]
    exact mul_nonneg (by positivity) (multiplicity_nonneg Ref x)
  · by_cases hu : x ∈ ⋃ i, selected ν O eta lam i
    · have hnot : ¬(eta/8)*MeasurableEnergy.multiplicity Ref x ≤ MeasurableEnergy.multiplicity (selected ν O eta lam) x :=
        fun hh => hx ⟨hu,hh⟩
      have hid : MeasurableEnergy.multiplicity (fun i => selected ν O eta lam i \ marked ν Ref O eta lam) x =
          MeasurableEnergy.multiplicity (selected ν O eta lam) x := by
        simp [MeasurableEnergy.multiplicity,oneIndicator,Set.indicator_apply,hx]
      rw [hid]
      exact (lt_of_not_ge hnot).le
    · have hnone : ∀ i, x ∉ selected ν O eta lam i := fun i hi => hu (Set.mem_iUnion.mpr ⟨i,hi⟩)
      have hz : MeasurableEnergy.multiplicity (fun i => selected ν O eta lam i \ marked ν Ref O eta lam) x = 0 := by
        simp [MeasurableEnergy.multiplicity,oneIndicator,hnone]
      rw [hz]
      exact mul_nonneg (by positivity) (multiplicity_nonneg Ref x)

/-- Integrating the actual discarded multiplicities bounds all removed selected
mass by η/8 of the original Ref mass. -/
theorem discarded_mass_upper (Ref O : Fin M → Set X) {eta lam : ℝ} (heta : 0 ≤ eta)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hO : ∀ i, MeasurableSet (O i))
    (hReff : ∀ i, ν (Ref i) ≠ ∞) (hOf : ∀ i, ν (O i) ≠ ∞) :
    (∑ i, ν.real (selected ν O eta lam i \ marked ν Ref O eta lam)) ≤ (eta/8)*∑ i, ν.real (Ref i) := by
  have hG := marked_measurable (ν := ν) Ref O eta lam hRef hO
  have hY := selected_measurable (ν := ν) O eta lam hO
  have hbad (i) := (hY i).diff hG
  have hbadf (i) : ν (selected ν O eta lam i \ marked ν Ref O eta lam) ≠ ∞ :=
    measure_ne_top_of_subset Set.sdiff_subset (hOf (selectedIndex ν O eta lam i))
  have h := integral_mono
    (memLp_one_iff_integrable.mp (multiplicity_memLp _ hbad hbadf 1))
    ((memLp_one_iff_integrable.mp (multiplicity_memLp Ref hRef hReff 1)).const_mul (eta/8))
    (discarded_pointwise (ν := ν) Ref O heta)
  rw [multiplicity_integral _ hbad hbadf,integral_const_mul,multiplicity_integral Ref hRef hReff] at h
  exact h

/-- At least half the full selected-output mass lies in the actual marked set.
The controlling multiplicity is that of Ref, not that of the possibly sparse O. -/
theorem marked_mass_lower (Full Ref O : Fin M → Set X) {eta lam : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hO : ∀ i, MeasurableSet (O i))
    (hFullf : ∀ i, ν (Full i) ≠ ∞)
    (hRefFull : ∀ i, Ref i ⊆ Full i) (hORef : ∀ i, O i ⊆ Ref i)
    (hupper : ∀ i, ν.real (Full i) ≤ 2*lam)
    (hmass : eta*lam*M ≤ ∑ i, ν.real (O i)) :
    (∑ i, ν.real (selected ν O eta lam i))/2 ≤
      ∑ i, ν.real (selected ν O eta lam i ∩ marked ν Ref O eta lam) := by
  have hReff (i) := measure_ne_top_of_subset (hRefFull i) (hFullf i)
  have hOf (i) := measure_ne_top_of_subset (hORef i) (hReff i)
  have hOupper (i) : ν.real (O i) ≤ 2*lam :=
    (measureReal_mono ((hORef i).trans (hRefFull i)) (hFullf i)).trans (hupper i)
  have hgood := (good_mass_and_count O heta hlam hOupper hmass).1
  rw [← selected_mass] at hgood
  have hRefupper : (∑ i, ν.real (Ref i)) ≤ 2*lam*M := by
    exact (Finset.sum_le_sum (fun i _ => (measureReal_mono (hRefFull i) (hFullf i)).trans (hupper i))).trans_eq
      (by simp [mul_comm])
  have hbad := discarded_mass_upper (lam := lam) Ref O heta.le hRef hO hReff hOf
  have hscale := mul_le_mul_of_nonneg_left hRefupper (by positivity : 0 ≤ eta/8)
  have hG := marked_measurable (ν := ν) Ref O eta lam hRef hO
  have hsplit : (∑ i, ν.real (selected ν O eta lam i \ marked ν Ref O eta lam))+
      (∑ i, ν.real (selected ν O eta lam i ∩ marked ν Ref O eta lam)) =
        ∑ i, ν.real (selected ν O eta lam i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact measureReal_sdiff_add_inter hG (hOf (selectedIndex ν O eta lam i))
  nlinarith

/-- Every selected full output has the constructed positive lower density. -/
theorem selected_mass_lower (O : Fin M → Set X) (eta lam : ℝ)
    (i : Fin (good ν O eta lam).card) : eta*lam/2 ≤ ν.real (selected ν O eta lam i) :=
  (Finset.mem_filter.mp (selectedIndex_mem ν O eta lam i)).2

/-- Selected outputs inherit the actual original upper measure. -/
theorem selected_mass_upper (Full Ref O : Fin M → Set X) {eta lam : ℝ}
    (hFullf : ∀ i, ν (Full i) ≠ ∞) (hRefFull : ∀ i, Ref i ⊆ Full i) (hORef : ∀ i, O i ⊆ Ref i)
    (hupper : ∀ i, ν.real (Full i) ≤ 2*lam) (i : Fin (good ν O eta lam).card) :
    ν.real (selected ν O eta lam i) ≤ 2*lam :=
  (measureReal_mono ((hORef _).trans (hRefFull _)) (hFullf _)).trans (hupper _)

/-- The original full shading measure is at most 4/η of its selected output;
this ratio is derived from the actual selection threshold and original upper bound. -/
theorem full_selected_ratio (Full O : Fin M → Set X) {eta lam : ℝ} (heta : 0 < eta)
    (hupper : ∀ i, ν.real (Full i) ≤ 2*lam) (i : Fin (good ν O eta lam).card) :
    ν.real (Full (selectedIndex ν O eta lam i)) ≤ (4/eta)*ν.real (selected ν O eta lam i) := by
  have hlo := selected_mass_lower (ν := ν) O eta lam i
  have hhi := hupper (selectedIndex ν O eta lam i)
  have hm := mul_le_mul_of_nonneg_left hhi heta.le
  have hh : eta*ν.real (Full (selectedIndex ν O eta lam i)) ≤ 4*ν.real (selected ν O eta lam i) := by nlinarith
  have h := (le_div_iff₀ heta).mpr (by nlinarith : ν.real (Full (selectedIndex ν O eta lam i))*eta ≤
    4*ν.real (selected ν O eta lam i))
  simpa only [div_mul_eq_mul_div] using h

/-- The actual marked set is contained in the selected union. -/
theorem marked_subset_selected (Ref O : Fin M → Set X) (eta lam : ℝ) :
    marked ν Ref O eta lam ⊆ ⋃ i, selected ν O eta lam i := Set.inter_subset_left

/-- Every marked point also lies in the actual reference union. -/
theorem marked_subset_reference (Ref O : Fin M → Set X) (eta lam : ℝ)
    (hORef : ∀ i, O i ⊆ Ref i) : marked ν Ref O eta lam ⊆ ⋃ i, Ref i := by
  intro x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx.1
  exact Set.mem_iUnion.mpr ⟨selectedIndex ν O eta lam i,hORef _ hi⟩

/-- Pointwise Ref multiplicity is quantitatively controlled on the constructed mark. -/
theorem marked_population_ratio (Ref O : Fin M → Set X) {eta lam : ℝ} (heta : 0 < eta)
    {x : X} (hx : x ∈ marked ν Ref O eta lam) :
    (overlapCount Ref x:ℝ) ≤ (8/eta)*(overlapCount (selected ν O eta lam) x:ℝ) := by
  have h := hx.2
  simp only [multiplicity_eq_card] at h
  change (eta/8)*(overlapCount Ref x:ℝ) ≤ (overlapCount (selected ν O eta lam) x:ℝ) at h
  have hh := (le_div_iff₀ heta).mpr (by nlinarith : (overlapCount Ref x:ℝ)*eta ≤
    8*(overlapCount (selected ν O eta lam) x:ℝ))
  simpa only [div_mul_eq_mul_div] using hh

/-- Reindex the actual original tube directions using the measured good outputs.
The independent finite-cell field is also retained literally. -/
def selectedFamily {k M : ℕ} (F : TubeFamily k M) (ν : Measure (Space k))
    (O : Fin M → Set (Space k)) (eta lam : ℝ) : TubeFamily k (good ν O eta lam).card where
  tube i := F.tube (selectedIndex ν O eta lam i)
  shade i := F.shade (selectedIndex ν O eta lam i)

/-- Reference pointwise cap bounds transfer to selected output directions on
marked points with the exact factor8/η, even when O itself was not broad. -/
theorem selected_broad {k M : ℕ} (F : TubeFamily k M) (ν : Measure (Space k))
    (Ref O : Fin M → Set (Space k)) {δ eta lam beta K : ℝ}
    (hδ : 0 ≤ δ) (heta : 0 < eta) (hK : 0 ≤ K) (hORef : ∀ i, O i ⊆ Ref i)
    (hbroad : PointwiseBroad F Ref (⋃ i, Ref i) δ beta K) :
    PointwiseBroad (selectedFamily F ν O eta lam) (selected ν O eta lam) (marked ν Ref O eta lam)
      δ beta (K*(8/eta)) := by
  intro x hx center t ht
  have hRefx := marked_subset_reference (ν := ν) Ref O eta lam hORef hx
  have hbr := hbroad x hRefx center t ht
  have hratio := marked_population_ratio (ν := ν) Ref O heta hx
  have hcard : (Finset.univ.filter (fun i => x ∈ selected ν O eta lam i ∧
      projectiveDistance ((selectedFamily F ν O eta lam).tube i).direction center ≤ t)).card ≤
      (Finset.univ.filter (fun i => x ∈ Ref i ∧ projectiveDistance (F.tube i).direction center ≤ t)).card := by
    apply Finset.card_le_card_of_injOn (selectedIndex ν O eta lam)
    · intro i hi
      obtain ⟨_,hi,hangle⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hORef _ hi,hangle⟩
    · exact fun i _ j _ hij => selectedIndex_injective ν O eta lam hij
  have hcast : ((Finset.univ.filter (fun i => x ∈ selected ν O eta lam i ∧
      projectiveDistance ((selectedFamily F ν O eta lam).tube i).direction center ≤ t)).card:ℝ) ≤
      ((Finset.univ.filter (fun i => x ∈ Ref i ∧ projectiveDistance (F.tube i).direction center ≤ t)).card:ℝ) := by
    exact_mod_cast hcard
  have hm := mul_le_mul_of_nonneg_left hratio (mul_nonneg hK (Real.rpow_nonneg (hδ.trans ht) beta))
  have hid : (K*t^beta)*((8/eta)*(overlapCount (selected ν O eta lam) x:ℝ)) =
      (K*(8/eta))*t^beta*(overlapCount (selected ν O eta lam) x:ℝ) := by ring
  exact (hcast.trans hbr).trans (hm.trans_eq hid)

/-- Original actual physical-ball tests pass from Full to the selected measurable
outputs with the factor4B/η derived from measured density, without a grid cover. -/
theorem selected_two_ends {k M : ℕ} (ν : Measure (Space k))
    (Full Ref O : Fin M → Set (Space k)) {δ eta lam alpha B : ℝ}
    (hδ : 0 ≤ δ) (heta : 0 < eta) (hB : 0 ≤ B)
    (hFullf : ∀ i, ν (Full i) ≠ ∞) (hRefFull : ∀ i, Ref i ⊆ Full i) (hORef : ∀ i, O i ⊆ Ref i)
    (hupper : ∀ i, ν.real (Full i) ≤ 2*lam)
    (hends : ∀ i p r, δ ≤ r → r ≤ 1 → ν.real (Full i ∩ Metric.closedBall p r) ≤ B*r^alpha*ν.real (Full i)) :
    ∀ i p r, δ ≤ r → r ≤ 1 → ν.real (selected ν O eta lam i ∩ Metric.closedBall p r) ≤
      (B*(4/eta))*r^alpha*ν.real (selected ν O eta lam i) := by
  intro i p r hr hr1
  have hsub : selected ν O eta lam i ∩ Metric.closedBall p r ⊆
      Full (selectedIndex ν O eta lam i) ∩ Metric.closedBall p r :=
    Set.inter_subset_inter_left _ ((hORef _).trans (hRefFull _))
  have hmono := measureReal_mono hsub (measure_ne_top_of_subset Set.inter_subset_left (hFullf _))
  have hh := full_selected_ratio (ν := ν) Full O heta hupper i
  have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg hB (Real.rpow_nonneg (hδ.trans hr) alpha))
  have hid : (B*r^alpha)*((4/eta)*ν.real (selected ν O eta lam i)) =
      (B*(4/eta))*r^alpha*ν.real (selected ν O eta lam i) := by ring
  exact (hmono.trans (hends _ p r hr hr1)).trans (hm.trans_eq hid)

/-- Nonempty original retained mass produces a nonempty selected family. -/
theorem good_card_pos (O : Fin M → Set X) {eta lam : ℝ}
    (hM : 0 < M) (heta : 0 < eta) (hlam : 0 < lam)
    (hupper : ∀ i, ν.real (O i) ≤ 2*lam)
    (hmass : eta*lam*M ≤ ∑ i, ν.real (O i)) : 0 < (good ν O eta lam).card := by
  have h := (good_mass_and_count O heta hlam hupper hmass).2
  have hp : 0 < eta*(M:ℝ)/4 := by positivity
  exact_mod_cast hp.trans_le h

/-- The mark has finite actual measure because it is inside the finite selected union. -/
theorem marked_finite (Ref O : Fin M → Set X) (eta lam : ℝ)
    (hOf : ∀ i, ν (O i) ≠ ∞) : ν (marked ν Ref O eta lam) ≠ ∞ := by
  apply measure_ne_top_of_subset Set.inter_subset_left
  simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ := ν)
    (s := Set.univ) (f := selected ν O eta lam) (Set.toFinite _) (fun i _ => hOf (selectedIndex ν O eta lam i))

/-- The exact selected original directions preserve every separation bound. -/
theorem selectedFamily_separated {k M : ℕ} (F : TubeFamily k M) (ν : Measure (Space k))
    (O : Fin M → Set (Space k)) (eta lam : ℝ) {δ : ℝ} (hsep : F.Separated δ) :
    (selectedFamily F ν O eta lam).Separated δ := by
  intro i j hij
  exact hsep _ _ (fun he => hij (selectedIndex_injective ν O eta lam he))

/-- Every original real-m cap bound survives the actual measured selection
with unchanged coefficient, by injection into the original cap population. -/
theorem selectedFamily_cap_bound {k M : ℕ} (F : TubeFamily k M) (ν : Measure (Space k))
    (O : Fin M → Set (Space k)) (eta lam : ℝ) {δ m A : ℝ} (hcap : F.CapBound δ m A) :
    (selectedFamily F ν O eta lam).CapBound δ m A := by
  intro center hunit r hr hr1
  have hcard : (Finset.univ.filter (fun i =>
      projectiveDistance ((selectedFamily F ν O eta lam).tube i).direction center ≤ r)).card ≤
      (Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction center ≤ r)).card := by
    apply Finset.card_le_card_of_injOn (selectedIndex ν O eta lam)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · exact fun i _ j _ hij => selectedIndex_injective ν O eta lam hij
  apply le_trans ?_ (hcap center hunit r hr hr1)
  exact_mod_cast hcard

/-- Complete actual measurable recovery. The original reference broadness is
kept distinct from the selected output, and the marked set is constructed by
actual multiplicity comparison. All integral and cardinal estimates are derived. -/
theorem recover {k M : ℕ} (F : TubeFamily k M) (ν : Measure (Space k))
    (Full Ref O : Fin M → Set (Space k)) {δ eta lam alpha beta B K : ℝ}
    (hδ : 0 ≤ δ) (heta : 0 < eta) (hlam : 0 < lam) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hRef : ∀ i, MeasurableSet (Ref i)) (hO : ∀ i, MeasurableSet (O i))
    (hFullf : ∀ i, ν (Full i) ≠ ∞)
    (hRefFull : ∀ i, Ref i ⊆ Full i) (hORef : ∀ i, O i ⊆ Ref i)
    (hupper : ∀ i, ν.real (Full i) ≤ 2*lam)
    (hmass : eta*lam*M ≤ ∑ i, ν.real (O i))
    (hbroad : PointwiseBroad F Ref (⋃ i, Ref i) δ beta K)
    (hends : ∀ i p r, δ ≤ r → r ≤ 1 → ν.real (Full i ∩ Metric.closedBall p r) ≤ B*r^alpha*ν.real (Full i)) :
    eta*(M:ℝ)/4 ≤ ((good ν O eta lam).card:ℝ) ∧
    eta*lam*(M:ℝ)/2 ≤ ∑ i, ν.real (selected ν O eta lam i) ∧
    (∀ i, MeasurableSet (selected ν O eta lam i) ∧ ν (selected ν O eta lam i) ≠ ∞ ∧
      eta*lam/2 ≤ ν.real (selected ν O eta lam i) ∧ ν.real (selected ν O eta lam i) ≤ 2*lam) ∧
    MeasurableSet (marked ν Ref O eta lam) ∧ ν (marked ν Ref O eta lam) ≠ ∞ ∧
    marked ν Ref O eta lam ⊆ ⋃ i, selected ν O eta lam i ∧
    (∑ i, ν.real (selected ν O eta lam i))/2 ≤
      ∑ i, ν.real (selected ν O eta lam i ∩ marked ν Ref O eta lam) ∧
    PointwiseBroad (selectedFamily F ν O eta lam) (selected ν O eta lam) (marked ν Ref O eta lam)
      δ beta (K*(8/eta)) ∧
    (∀ i p r, δ ≤ r → r ≤ 1 → ν.real (selected ν O eta lam i ∩ Metric.closedBall p r) ≤
      (B*(4/eta))*r^alpha*ν.real (selected ν O eta lam i)) := by
  have hOf (i) := measure_ne_top_of_subset ((hORef i).trans (hRefFull i)) (hFullf i)
  have hOupper (i) := (measureReal_mono ((hORef i).trans (hRefFull i)) (hFullf i)).trans (hupper i)
  have hg := good_mass_and_count O heta hlam hOupper hmass
  refine ⟨hg.2,?_,?_,marked_measurable Ref O eta lam hRef hO,marked_finite Ref O eta lam hOf,
    marked_subset_selected Ref O eta lam,marked_mass_lower Full Ref O heta hlam hRef hO hFullf hRefFull hORef hupper hmass,
    selected_broad F ν Ref O hδ heta hK hORef hbroad,
    selected_two_ends ν Full Ref O hδ heta hB hFullf hRefFull hORef hupper hends⟩
  · rw [selected_mass]
    exact hg.1
  · intro i
    exact ⟨hO _,hOf _,selected_mass_lower O eta lam i,
      selected_mass_upper Full Ref O hFullf hRefFull hORef hupper i⟩

end
end KakeyaFormal.MeasurableDensityRecovery

#print axioms KakeyaFormal.MeasurableDensityRecovery.recover
