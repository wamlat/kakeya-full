import RestrictedInterpolation

/-! Actual increasing finite dyadic approximants. A terminal upper band
includes infinite values, so the pointwise approximation theorem needs no
almost-everywhere finiteness or input-integral assumption. -/
namespace KakeyaFormal.DyadicApproximation
open MeasureTheory Set Finset RestrictedInterpolation
open scoped ENNReal NNReal
noncomputable section
open Classical

def indices (N : ℕ) : Finset ℤ := Icc (-(N:ℤ)) (N:ℤ)

def bands {X : Type*} (f : X → ℝ≥0∞) (N : ℕ) (j : ℤ) : Set X :=
  {x | (dyadicHeight j : ℝ≥0∞) ≤ f x ∧
    (f x < (dyadicHeight (j+1) : ℝ≥0∞) ∨ j = (N:ℤ))}

def approx {X : Type*} (f : X → ℝ≥0∞) (N : ℕ) : X → ℝ≥0∞ :=
  bandSum (indices N) dyadicHeight (bands f N)

theorem indices_mono {N M : ℕ} (hNM : N ≤ M) : indices N ⊆ indices M := by
  intro j hj
  simp only [indices,Finset.mem_Icc] at hj ⊢
  omega

theorem bands_measurable {X : Type*} [MeasurableSpace X]
    {f : X → ℝ≥0∞} (hf : Measurable f) (N : ℕ) (j : ℤ) : MeasurableSet (bands f N j) := by
  by_cases hj : j = (N:ℤ)
  · simpa only [bands,hj,or_true,and_true] using measurableSet_le measurable_const hf
  · simpa only [bands,hj,or_false,Set.ofPred_and] using
      (measurableSet_le measurable_const hf).inter (measurableSet_lt hf measurable_const)

theorem bands_disjoint_of_lt {X : Type*} (f : X → ℝ≥0∞) (N : ℕ)
    {i j : ℤ} (hij : i < j) (hjN : j ≤ (N:ℤ)) : Disjoint (bands f N i) (bands f N j) := by
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hiN : i ≠ (N:ℤ) := by omega
  have hupper := hxi.2.resolve_right hiN
  have hheight : (dyadicHeight (i+1):ℝ≥0∞) ≤ (dyadicHeight j:ℝ≥0∞) :=
    ENNReal.coe_le_coe.mpr (dyadicHeight_mono (by omega))
  exact (not_lt_of_ge (hheight.trans hxj.1)) hupper

theorem bands_disjoint {X : Type*} (f : X → ℝ≥0∞) (N : ℕ) :
    (↑(indices N) : Set ℤ).Pairwise (fun i j => Disjoint (bands f N i) (bands f N j)) := by
  intro i hi j hj hij
  have hiN := (Finset.mem_Icc.mp hi).2
  have hjN := (Finset.mem_Icc.mp hj).2
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact bands_disjoint_of_lt f N hlt hjN
  · exact (bands_disjoint_of_lt f N hgt hiN).symm

theorem approx_measurable {X : Type*} [MeasurableSpace X]
    {f : X → ℝ≥0∞} (hf : Measurable f) (N : ℕ) : Measurable (approx f N) :=
  bandSum_measurable _ _ _ (fun j _ => bands_measurable hf N j)

/-- At a point in a band, the entire actual finite sum equals that height. -/
theorem approx_eq_height {X : Type*} (f : X → ℝ≥0∞) (N : ℕ)
    {j : ℤ} (hj : j ∈ indices N) {x : X} (hx : x ∈ bands f N j) :
    approx f N x = (dyadicHeight j : ℝ≥0∞) := by
  unfold approx bandSum
  rw [sum_eq_single j]
  · simp only [RestrictedInterpolation.indicator,hx,Set.indicator_of_mem,mul_one]
  · intro i hi hij
    have hxi : x ∉ bands f N i := by
      intro hxi
      exact Set.disjoint_left.mp (bands_disjoint f N hi hj hij) hxi hx
    simp only [RestrictedInterpolation.indicator,Set.indicator_of_notMem hxi,mul_zero]
  · exact fun hn => (hn hj).elim

theorem approx_eq_zero_of_no_band {X : Type*} (f : X → ℝ≥0∞) (N : ℕ) (x : X)
    (hx : ∀ j ∈ indices N, x ∉ bands f N j) : approx f N x = 0 := by
  unfold approx bandSum
  exact sum_eq_zero (fun j hj => by simp [RestrictedInterpolation.indicator,hx j hj])

theorem approx_le {X : Type*} (f : X → ℝ≥0∞) (N : ℕ) : approx f N ≤ f := by
  intro x
  by_cases hx : ∃ j ∈ indices N, x ∈ bands f N j
  · obtain ⟨j,hj,hx⟩ := hx
    rw [approx_eq_height f N hj hx]
    exact hx.1
  · rw [approx_eq_zero_of_no_band f N x (by simpa using hx)]
    exact bot_le

/-- Any dyadic threshold below the input appears below the actual finite
sum. A largest qualifying index constructs the relevant band, including the
terminal tail band, without assuming a logarithmic index witness. -/
theorem height_le_approx {X : Type*} (f : X → ℝ≥0∞) (N : ℕ)
    {j : ℤ} (hj : j ∈ indices N) {x : X} (hx : (dyadicHeight j:ℝ≥0∞) ≤ f x) :
    (dyadicHeight j:ℝ≥0∞) ≤ approx f N x := by
  let valid := (indices N).filter (fun i => (dyadicHeight i:ℝ≥0∞) ≤ f x)
  have hne : valid.Nonempty := ⟨j,mem_filter.mpr ⟨hj,hx⟩⟩
  obtain ⟨i,hi,hmax⟩ := valid.exists_max_image (fun i : ℤ => i) hne
  have hi' := mem_filter.mp hi
  have hji : j ≤ i := hmax j (mem_filter.mpr ⟨hj,hx⟩)
  have hband : x ∈ bands f N i := by
    refine ⟨hi'.2,?_⟩
    by_cases hiN : i = (N:ℤ)
    · exact Or.inr hiN
    · apply Or.inl
      apply lt_of_not_ge
      intro hnext
      have hnextmem : i+1 ∈ indices N := by
        have hiI := Finset.mem_Icc.mp hi'.1
        apply Finset.mem_Icc.mpr
        omega
      have hn := hmax (i+1) (mem_filter.mpr ⟨hnextmem,hnext⟩)
      omega
  rw [approx_eq_height f N hi'.1 hband]
  exact ENNReal.coe_le_coe.mpr (dyadicHeight_mono hji)

theorem approx_mono {X : Type*} (f : X → ℝ≥0∞) : Monotone (approx f) := by
  intro N M hNM x
  by_cases hx : ∃ j ∈ indices N, x ∈ bands f N j
  · obtain ⟨j,hj,hx⟩ := hx
    rw [approx_eq_height f N hj hx]
    exact height_le_approx f M (indices_mono hNM hj) hx.1
  · rw [approx_eq_zero_of_no_band f N x (by simpa using hx)]
    exact bot_le

theorem iSup_approx_le {X : Type*} (f : X → ℝ≥0∞) (x : X) :
    (⨆ N, approx f N x) ≤ f x := iSup_le (fun N => approx_le f N x)

theorem index_mem_at_natAbs (j : ℤ) : j ∈ indices j.natAbs := by
  simp only [indices,Finset.mem_Icc,Int.natCast_natAbs]
  exact ⟨neg_abs_le j,le_abs_self j⟩

theorem height_succ (j : ℤ) :
    (dyadicHeight (j+1):ℝ≥0∞) = 2*(dyadicHeight j:ℝ≥0∞) := by
  have h : dyadicHeight (j+1) = 2*dyadicHeight j := by
    simp only [dyadicHeight,zpow_add₀ (by norm_num : (2:ℝ≥0) ≠ 0),zpow_one]
    exact mul_comm _ _
  exact_mod_cast h

/-- A terminal band captures an infinite input value at every finite height. -/
theorem approx_at_top {X : Type*} (f : X → ℝ≥0∞) {x : X} (hx : f x = ∞) (N : ℕ) :
    approx f N x = (dyadicHeight (N:ℤ):ℝ≥0∞) := by
  apply approx_eq_height f N
  · simp only [indices,Finset.mem_Icc]
    omega
  · exact ⟨hx ▸ le_top,Or.inr rfl⟩

theorem iSup_approx_at_top {X : Type*} (f : X → ℝ≥0∞) {x : X} (hx : f x = ∞) :
    (⨆ N, approx f N x) = ∞ := by
  apply iSup_eq_top.mpr
  intro b hb
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt b.toNNReal (by norm_num : (1:ℝ≥0)<2)
  refine ⟨N,?_⟩
  rw [approx_at_top f hx N,← ENNReal.coe_toNNReal (ne_of_lt hb)]
  apply ENNReal.coe_lt_coe.mpr
  simpa only [dyadicHeight,zpow_natCast] using hN

/-- The actual increasing finite sums recover every extended nonnegative
input within a factor two. Infinite values are handled pointwise by the
terminal bands; no integrability or a.e.-finite premise is needed. -/
theorem le_two_iSup_approx {X : Type*} (f : X → ℝ≥0∞) (x : X) :
    f x ≤ 2*(⨆ N, approx f N x) := by
  by_cases htop : f x = ∞
  · rw [htop,iSup_approx_at_top f htop]
    simp
  by_cases hz : f x = 0
  · rw [hz]
    exact bot_le
  let y := (f x).toNNReal
  have hcoe : (y:ℝ≥0∞) = f x := ENNReal.coe_toNNReal htop
  have hy : 0 < y := by
    apply ENNReal.coe_pos.mp
    rw [hcoe]
    exact bot_lt_iff_ne_bot.mpr hz
  obtain ⟨j,hlo,hhi⟩ := exists_mem_Ico_zpow hy (by norm_num : (1:ℝ≥0)<2)
  have hlo' : (dyadicHeight j:ℝ≥0∞) ≤ f x := by
    rw [← hcoe]
    exact ENNReal.coe_le_coe.mpr hlo
  have hhi' : f x < (dyadicHeight (j+1):ℝ≥0∞) := by
    rw [← hcoe]
    exact ENNReal.coe_lt_coe.mpr hhi
  have hpoint := height_le_approx f j.natAbs (index_mem_at_natAbs j) hlo'
  calc
    f x ≤ (dyadicHeight (j+1):ℝ≥0∞) := hhi'.le
    _ = 2*(dyadicHeight j:ℝ≥0∞) := height_succ j
    _ ≤ 2*approx f j.natAbs x := mul_le_mul' le_rfl hpoint
    _ ≤ 2*(⨆ N, approx f N x) := mul_le_mul' le_rfl (le_iSup (fun N : ℕ => approx f N x) j.natAbs)

end
end KakeyaFormal.DyadicApproximation
