import CumulativeEstimate

/-! Literal fixed-error, one-log cumulative consequence (combined Corollary 1.1).
The input is required at only one fixed error and one fixed cap coefficient.
Actual finite integer bins handle empty, tiny and unequal shadings. -/
namespace KakeyaFormal.CumulativeFixedError
open Finset Cumulative DiscreteMeasurable
open scoped BigOperators
noncomputable section

/-- Actual restriction and equal-cardinality normalization preserve the exact
cap coefficient supplied to the single-error analytic input. -/
theorem subfamily_bound_fixed_cap {k : ℕ} {geom : Normalization} {m d p ε c : ℝ}
    (hc : 0 < c) (hp : 0 ≤ p)
    (F : CumulativeConfiguration k geom m)
    (hestimate : ∀ H : ShadedConfiguration k geom m, H.A = F.A → H.δ = F.δ →
      c * H.A⁻¹ * H.δ ^ (m-d+ε) * H.lam ^ p * H.M ≤ (H.family.unionCells.card : ℝ))
    (S : Finset (Fin F.M)) {K : ℕ}
    (hS : S.Nonempty) (hK : 0 < K) (hcard : ∀ i ∈ S, K ≤ (F.family.shade i).card) :
    c * F.A⁻¹ * F.δ ^ (m-d+ε) *
      (F.δ * (K : ℝ) / (2 * gridCountConstant k geom.width)) ^ p * S.card ≤
        (F.family.unionCells.card : ℝ) := by
  classical
  let e : Fin S.card → Fin F.M := fun i => (S.equivFin.symm i).val
  have he : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have hemem (i : Fin S.card) : e i ∈ S := (S.equivFin.symm i).property
  have hex (i : Fin S.card) : ∃ Z ⊆ F.family.shade (e i), Z.card = K :=
    Finset.exists_subset_card_eq (hcard _ (hemem i))
  choose Z hZ hZcard using hex
  let G : TubeFamily k S.card := ⟨fun i => F.family.tube (e i), Z⟩
  have hGadm : G.Admissible geom.width F.δ := by
    intro i z hz
    exact F.admissible (e i) z (hZ i hz)
  obtain ⟨hsep,hbounded,hcap⟩ := injective_tube_restriction F.family G e he
    (fun _ => rfl) F.separated F.bounded F.cap_bound
  obtain ⟨H,hHM,hHδ,hHA,hHlam,hHU⟩ := normalize_family G geom F.scale_pos F.scale_le_one
    F.cap_ge_one hGadm hsep hbounded hcap (card_pos.mpr hS) hK hZcard
  have hGU : G.unionCells ⊆ F.family.unionCells := by
    intro z hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    exact F.family.shade_subset_union (e i) (hZ i hi)
  have hU : (H.family.unionCells.card : ℝ) ≤ (F.family.unionCells.card : ℝ) := by
    exact_mod_cast card_le_card (hHU.trans hGU)
  have hh := hestimate H hHA hHδ
  conv_lhs at hh => rw [hHM,hHδ,hHA]
  have hC : 0 < gridCountConstant k geom.width := lt_of_lt_of_le zero_lt_one (gridCountConstant_ge_one _ _)
  have hpow := Real.rpow_le_rpow (by have := F.scale_pos; positivity : 0 ≤ F.δ * (K : ℝ) / (2 * gridCountConstant k geom.width)) hHlam hp
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg hc.le (inv_nonneg.mpr (by linarith [F.cap_ge_one]))) (Real.rpow_nonneg F.scale_pos.le _))) (Nat.cast_nonneg _)).trans (hh.trans hU)

/-- Finite bins with the original cap coefficient and unchanged input error. -/
theorem finite_bin_bound_fixed_cap {k : ℕ} {geom : Normalization} {m d p ε c : ℝ}
    (hc : 0 < c) (hp : 1 ≤ p)
    (F : CumulativeConfiguration k geom m)
    (hestimate : ∀ H : ShadedConfiguration k geom m, H.A = F.A → H.δ = F.δ →
      c * H.A⁻¹ * H.δ ^ (m-d+ε) * H.lam ^ p * H.M ≤ (H.family.unionCells.card : ℝ))
    (hM : 0 < F.M) {J : ℕ}
    (hJ : gridCountConstant k geom.width / F.δ ≤ (2 : ℝ) ^ J) :
    c * F.A⁻¹ * F.δ ^ (m-d+ε) *
      (F.s / (4 * gridCountConstant k geom.width)) ^ p * F.M ≤
        ((J : ℝ)+2) * (F.family.unionCells.card : ℝ) := by
  classical
  let C := gridCountConstant k geom.width
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (gridCountConstant_ge_one _ _)
  let n : Fin F.M → ℕ := fun i => (F.family.shade i).card
  have hn (i : Fin F.M) : n i ≤ 2^J := by
    exact_mod_cast (admissible_count_bound F.family F.scale_pos F.scale_le_one F.admissible i).trans hJ
  let label := binLabel n hn
  let bins : Finset (Option (Fin (J+1))) := univ
  let S : Option (Fin (J+1)) → Finset (Fin F.M) := fun j => univ.filter (label · = j)
  let w : Option (Fin (J+1)) → ℝ := fun j => (S j).card
  let den : Option (Fin (J+1)) → ℝ := binDensity F.δ C
  have hw (j) (_ : j ∈ bins) : 0 ≤ w j := Nat.cast_nonneg _
  have hd (j) (_ : j ∈ bins) : 0 ≤ den j := by
    cases j <;> dsimp [den,binDensity]
    · rfl
    · have := F.scale_pos; positivity
  have hsum : ∑ j ∈ bins, w j = (F.M : ℝ) := by
    have hh := card_eq_sum_card_fiberwise (s := (univ : Finset (Fin F.M)))
      (t := bins) (f := label) (fun _ _ => mem_univ _)
    dsimp [w,S]
    simpa only [Nat.cast_sum,card_univ,Fintype.card_fin] using congrArg (Nat.cast : ℕ → ℝ) hh.symm
  have hfiber : ∑ j ∈ bins, w j * den j = ∑ i, den (label i) := by
    simpa [bins,w,S] using (sum_fiberwise' (univ : Finset (Fin F.M)) label den)
  have hmass : F.s / (4*C) * F.M ≤ ∑ j ∈ bins, w j * den j := by
    rw [hfiber]
    calc
      F.s / (4*C) * F.M = (F.s * F.M)/(4*C) := by ring
      _ ≤ (F.δ * ∑ i, (n i : ℝ))/(4*C) := div_le_div_of_nonneg_right F.cumulative (by positivity)
      _ = ∑ i, F.δ * (n i : ℝ)/(4*C) := by rw [mul_sum,sum_div]
      _ ≤ ∑ i, den (label i) := sum_le_sum fun i _ => binDensity_lower n hn F.scale_pos.le hC i
  have hbound (j) (_ : j ∈ bins) :
      (c * F.A⁻¹ * F.δ ^ (m-d+ε)) * (w j * den j ^ p) ≤ (F.family.unionCells.card : ℝ) := by
    cases j with
    | none => simp [den,binDensity,Real.zero_rpow (by linarith : p ≠ 0)]
    | some j =>
      by_cases hs : (S (some j)).Nonempty
      · have hcards (i) (hi : i ∈ S (some j)) : 2^j.val ≤ (F.family.shade i).card :=
          (binLabel_some n hn (mem_filter.mp hi).2).1
        have hh := subfamily_bound_fixed_cap hc (by linarith : 0 ≤ p) F hestimate (S (some j)) hs
          (pow_pos (by norm_num : 0 < (2 : ℕ)) _) hcards
        have hcast : ((2 ^ j.val : ℕ) : ℝ) = (2 : ℝ) ^ j.val := by norm_cast
        rw [hcast] at hh
        convert hh using 1
        dsimp [w,den,binDensity,C]
        ring
      · have hz : S (some j) = ∅ := not_nonempty_iff_eq_empty.mp hs
        simp [w,hz]
  have ha : 0 ≤ c * F.A⁻¹ * F.δ ^ (m-d+ε) := by
    exact mul_nonneg (mul_nonneg hc.le (inv_nonneg.mpr (by linarith [F.cap_ge_one])))
      (Real.rpow_nonneg F.scale_pos.le _)
  have hh := KakeyaFinite.cumulative_from_bins bins w den (by exact_mod_cast hM)
    (div_nonneg F.density_nonneg (by positivity)) hp ha hw hd hsum hmass hbound
  have hbincard : (bins.card : ℝ) = (J : ℝ)+2 := by simp [bins]; ring
  rw [hbincard] at hh
  convert hh using 1
  ring


/-- A single logarithm controls the actual number of integer cardinality bins,
with a fixed constant before the scale and no density dependence. -/
theorem linear_bin_budget {C : ℝ} (hC : 1 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ J : ℕ,
      C / δ ≤ (2 : ℝ)^J ∧ (J : ℝ)+2 ≤ B * Real.log (2/δ) := by
  have hC0 : 0 < C := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  let B := (Real.log C / Real.log 2 + 4) / Real.log 2
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro δ hδ hδ1
  have hN : 1 ≤ 1/δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hCδ : 1 ≤ C/δ := (le_div_iff₀ hδ).mpr (by linarith)
  obtain ⟨J,hJ,hJlog⟩ := ScaleChoice.dyadic_class_budget (lower := 1) (by norm_num) hCδ
  simp only [mul_one,div_one] at hJ hJlog
  refine ⟨J,hJ,?_⟩
  let L := Real.log (2*(1/δ))
  have hL : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith)
  have hlogid : Real.log (C/δ) = Real.log C + Real.log (1/δ) := by
    rw [Real.log_div hC0.ne' hδ.ne',Real.log_div one_ne_zero hδ.ne',Real.log_one]
    ring
  have hNlog : Real.log (1/δ) ≤ L := Real.log_le_log (by positivity) (by linarith [show (0 : ℝ) < 1/δ by positivity])
  have hD : 0 ≤ Real.log C / Real.log 2 + 3 := by positivity
  have hconst : Real.log C / Real.log 2 + 3 ≤
      ((Real.log C / Real.log 2 + 3) / Real.log 2) * L := by
    have hh1 : 1 ≤ L / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hL)
    have hh := mul_le_mul_of_nonneg_left hh1 hD
    calc
      Real.log C / Real.log 2 + 3 = (Real.log C / Real.log 2 + 3) * 1 := by ring
      _ ≤ (Real.log C / Real.log 2 + 3) * (L / Real.log 2) := hh
      _ = ((Real.log C / Real.log 2 + 3) / Real.log 2) * L := by ring
  have hlinear : (J : ℝ)+2 ≤ B*L := by
    rw [hlogid,add_div] at hJlog
    have hh := div_le_div_of_nonneg_right hNlog hl2.le
    calc
      (J : ℝ)+2 ≤ (Real.log C / Real.log 2 + 3) + Real.log (1/δ) / Real.log 2 := by linarith
      _ ≤ ((Real.log C / Real.log 2 + 3) / Real.log 2) * L + L / Real.log 2 := add_le_add hconst hh
      _ = B*L := by dsimp [B]; ring
  simpa only [L, show 2*(1/δ) = 2/δ by ring] using hlinear

/-- One fixed analytic error yields exactly one logarithmic loss. The input is
needed only at the specified cap coefficient and scale cutoff. In particular,
`δmax = 1/2` implements the source convention `N ≥ 2` without a large-scale
extension. The factor `cr` depends only on dimension, fixed geometry and `p`.
Neither an every-error input nor a uniform-in-A input is assumed. -/
theorem from_fixed_input (k : ℕ) (geom : Normalization) {p : ℝ} (hp : 1 ≤ p) :
    ∃ cr : ℝ, 0 < cr ∧ ∀ (m d ε c A δmax : ℝ), 0 < c →
      (∀ H : ShadedConfiguration k geom m, H.A = A → H.δ ≤ δmax →
        c * A⁻¹ * H.δ ^ (m-d+ε) * H.lam ^ p * H.M ≤
          (H.family.unionCells.card : ℝ)) →
      ∀ F : CumulativeConfiguration k geom m, F.A = A → F.δ ≤ δmax →
        cr * c * A⁻¹ * F.δ ^ (m-d+ε) * F.s ^ p * F.M /
          Real.log (2/F.δ) ≤ (F.family.unionCells.card : ℝ) := by
  let C := gridCountConstant k geom.width
  have hC1 : 1 ≤ C := gridCountConstant_ge_one _ _
  have hC : 0 < C := by linarith
  obtain ⟨B,hB,hbudget⟩ := linear_bin_budget hC1
  let D := (4*C)^p
  have hD : 0 < D := Real.rpow_pos_of_pos (by positivity) _
  let cr := 1/(D*B)
  have hcr : 0 < cr := by dsimp [cr]; positivity
  refine ⟨cr,hcr,?_⟩
  intro m d ε c A δmax hc hestimate F hFA hscale
  by_cases hM : F.M = 0
  · simp [hM]
  have hMpos : 0 < F.M := Nat.pos_of_ne_zero hM
  have hinput (H : ShadedConfiguration k geom m) (hA : H.A = F.A)
      (hδ : H.δ = F.δ) :
      c * H.A⁻¹ * H.δ ^ (m-d+ε) * H.lam ^ p * H.M ≤
        (H.family.unionCells.card : ℝ) := by
    simpa only [hA,hFA] using hestimate H (hA.trans hFA) (hδ ▸ hscale)
  obtain ⟨J,hJ,hJB⟩ := hbudget F.δ F.scale_pos F.scale_le_one
  have hh := finite_bin_bound_fixed_cap hc hp F hinput hMpos hJ
  have hscaled := hh.trans (mul_le_mul_of_nonneg_right hJB
    (Nat.cast_nonneg F.family.unionCells.card))
  have hL : 0 < Real.log (2/F.δ) := Real.log_pos
    ((lt_div_iff₀ F.scale_pos).mpr (by linarith [F.scale_le_one]))
  have hdiv :
      (c * F.A⁻¹ * F.δ ^ (m-d+ε) * (F.s/(4*C))^p * F.M) /
        (B * Real.log (2/F.δ)) ≤ (F.family.unionCells.card : ℝ) := by
    apply (div_le_iff₀ (mul_pos hB hL)).mpr
    convert hscaled using 1
    ring
  have hpow : (F.s/(4*C))^p = F.s^p/D :=
    Real.div_rpow F.density_nonneg (by positivity) p
  rw [hpow,hFA] at hdiv
  convert hdiv using 1
  dsimp [cr]
  field_simp

/-- The identical fixed-input statement in the manuscript's notation
`N = 1/δ`, with unchanged error and the literal denominator `log (2*N)`. -/
theorem source_notation (k : ℕ) (geom : Normalization) {p : ℝ} (hp : 1 ≤ p) :
    ∃ cr : ℝ, 0 < cr ∧ ∀ (m b η c A δmax : ℝ), 0 < c →
      (∀ H : ShadedConfiguration k geom m, H.A = A → H.δ ≤ δmax →
        c * A⁻¹ * (1/H.δ) ^ (b-m-η) * H.lam ^ p * H.M ≤
          (H.family.unionCells.card : ℝ)) →
      ∀ F : CumulativeConfiguration k geom m, F.A = A → F.δ ≤ δmax →
        cr * c * A⁻¹ * (1/F.δ) ^ (b-m-η) * F.s ^ p * F.M /
          Real.log (2*(1/F.δ)) ≤ (F.family.unionCells.card : ℝ) := by
  obtain ⟨cr,hcr,hbound⟩ := from_fixed_input k geom hp
  refine ⟨cr,hcr,?_⟩
  intro m b η c A δmax hc hestimate F hFA hscale
  have hpow (t : ℝ) (ht : 0 < t) : (1/t)^(b-m-η) = t^(m-b+η) := by
    rw [one_div,Real.inv_rpow ht.le,← Real.rpow_neg ht.le]
    congr 1
    ring
  have hinput (H : ShadedConfiguration k geom m) (hA : H.A = A)
      (hδ : H.δ ≤ δmax) :
      c * A⁻¹ * H.δ^(m-b+η) * H.lam^p * H.M ≤
        (H.family.unionCells.card : ℝ) := by
    simpa only [hpow H.δ H.scale_pos] using hestimate H hA hδ
  have hh := hbound m b η c A δmax hc hinput F hFA hscale
  simpa only [hpow F.δ F.scale_pos, show 2*(1/F.δ) = 2/F.δ by ring] using hh

end
end KakeyaFormal.CumulativeFixedError
