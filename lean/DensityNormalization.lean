import Configurations

/-! Constant-factor density normalization for actual equal-cardinality tube
shadings. Counts above 1/δ are clamped by choosing actual subsets; neither the
upper-density condition nor existence of trimming is assumed. -/
namespace KakeyaFormal.DensityNormalization

theorem floor_ge_half {N : ℝ} (hN : 1 ≤ N) : N/2 ≤ (Nat.floor N : ℝ) := by
  have hf : 1 ≤ Nat.floor N := Nat.le_floor (by simpa using hN)
  have hfr : (1 : ℝ) ≤ Nat.floor N := by exact_mod_cast hf
  have hupper := Nat.lt_floor_add_one N
  linarith

theorem clamped_count_bounds {δ C : ℝ} {K : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C) (hK : 0 < K)
    (hupper : (K:ℝ) ≤ C/δ) :
    let K₀ := min K (Nat.floor (1/δ))
    0 < K₀ ∧ (K₀:ℝ) ≤ 1/δ ∧ (K:ℝ)/(2*C) ≤ (K₀:ℝ) := by
  have hN : (1:ℝ) ≤ 1/δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hf : 1 ≤ Nat.floor (1/δ) := Nat.le_floor (by simpa using hN)
  have hCpos : 0 < C := by linarith
  refine ⟨by omega, ?_, ?_⟩
  · have hmin : ((min K (Nat.floor (1/δ)) : ℕ):ℝ) ≤ Nat.floor (1/δ) := by
      exact_mod_cast Nat.min_le_right K (Nat.floor (1/δ))
    exact hmin.trans (Nat.floor_le (by positivity))
  · rw [Nat.cast_min]
    apply le_min
    · apply (div_le_iff₀ (by positivity : 0 < 2*C)).mpr
      nlinarith [show (0:ℝ) ≤ K by positivity]
    · have hfloor := floor_ge_half hN
      apply (div_le_iff₀ (by positivity : 0 < 2*C)).mpr
      have hmul := mul_le_mul_of_nonneg_right hfloor (by positivity : 0 ≤ 2*C)
      have hid : (1/δ)/2*(2*C) = C/δ := by ring
      rw [hid] at hmul
      exact hupper.trans (by simpa only [mul_comm] using hmul)

/-- Actual simultaneous trimming, preserving every tube and taking each shading
inside its original cells. All constants and the density are explicit. -/
theorem trim_equal_cardinality {k M K : ℕ} (F : TubeFamily k M)
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 1 ≤ C)
    (hK : 0 < K) (hupper : (K:ℝ) ≤ C/δ)
    (hcard : ∀ i, (F.shade i).card = K) :
    ∃ G : TubeFamily k M, ∃ lam : ℝ,
      0 < lam ∧ lam ≤ 1 ∧ δ*(K:ℝ)/(2*C) ≤ lam ∧
      G.tube = F.tube ∧ (∀ i, G.shade i ⊆ F.shade i) ∧
      G.Comparable δ lam ∧ G.unionCells ⊆ F.unionCells := by
  classical
  let K₀ := min K (Nat.floor (1/δ))
  obtain ⟨hK₀,hK₀upper,hK₀lower⟩ := clamped_count_bounds hδ hδ1 hC hK hupper
  have hsubcount : ∀ i : Fin M, K₀ ≤ (F.shade i).card := by
    intro i
    rw [hcard i]
    exact Nat.min_le_left _ _
  choose selected hsub hselected using (fun i => Finset.exists_subset_card_eq (hsubcount i))
  let G : TubeFamily k M := ⟨F.tube,selected⟩
  let lam : ℝ := δ*K₀
  have hrealpos : 0 < (K₀:ℝ) := by exact_mod_cast hK₀
  refine ⟨G,lam,mul_pos hδ hrealpos,?_,?_,rfl,hsub,?_,?_⟩
  · have hh := (le_div_iff₀ hδ).mp hK₀upper
    dsimp [lam]
    nlinarith
  · have hh := mul_le_mul_of_nonneg_left hK₀lower hδ.le
    simpa only [lam,K₀,mul_div_assoc] using hh
  · intro i
    have hdiv : lam/δ = (K₀:ℝ) := by dsimp [lam]; field_simp
    have htwodiv : 2*lam/δ = 2*(K₀:ℝ) := by dsimp [lam]; field_simp
    change lam/δ ≤ (selected i).card ∧ ((selected i).card:ℝ) ≤ 2*lam/δ
    rw [hselected i,hdiv,htwodiv]
    constructor
    · exact le_rfl
    · linarith
  · intro z hz
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hsub i hi⟩

end KakeyaFormal.DensityNormalization
