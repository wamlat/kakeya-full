import DiscreteMeasurable
import Finite
import LogLoss

/-! The genuine cumulative-density consequence of the normalized discrete
estimate. Individual shadings may be empty. Dyadic classes are indexed by actual
positive integer cardinalities and their number depends only on the scale. -/
namespace KakeyaFormal
open Finset
open scoped BigOperators
noncomputable section

structure CumulativeConfiguration (k : ℕ) (geom : Normalization) (m : ℝ) where
  M : ℕ
  δ : ℝ
  s : ℝ
  A : ℝ
  family : TubeFamily k M
  scale_pos : 0 < δ
  scale_le_one : δ ≤ 1
  density_nonneg : 0 ≤ s
  cap_ge_one : 1 ≤ A
  admissible : family.Admissible geom.width δ
  separated : family.Separated (geom.separation * δ)
  bounded : family.Bounded geom.radius
  cap_bound : family.CapBound δ m A
  cumulative : s * M ≤ δ * ∑ i, ((family.shade i).card : ℝ)

def CumulativeEstimate (k : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : Normalization, ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ F : CumulativeConfiguration k geom m,
      c * F.A⁻¹ * F.δ ^ (m-d+ε) * F.s ^ p * F.M ≤ (F.family.unionCells.card : ℝ)

namespace Cumulative
open DiscreteMeasurable

/-- Construct an actual equal-cardinality subfamily, normalize it and apply the
analytic estimate. This includes cardinalities greater than 1/δ. -/
theorem subfamily_bound {k : ℕ} {geom : Normalization} {m d p ε c : ℝ}
    (hc : 0 < c) (hp : 0 ≤ p)
    (hestimate : ∀ H : ShadedConfiguration k geom m,
      c * H.A⁻¹ * H.δ ^ (m-d+ε) * H.lam ^ p * H.M ≤ (H.family.unionCells.card : ℝ))
    (F : CumulativeConfiguration k geom m) (S : Finset (Fin F.M)) {K : ℕ}
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
  have hh := hestimate H
  conv_lhs at hh => rw [hHM,hHδ,hHA]
  have hC : 0 < gridCountConstant k geom.width := lt_of_lt_of_le zero_lt_one (gridCountConstant_ge_one _ _)
  have hpow := Real.rpow_le_rpow (by have := F.scale_pos; positivity : 0 ≤ F.δ * (K : ℝ) / (2 * gridCountConstant k geom.width)) hHlam hp
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (mul_nonneg hc.le (inv_nonneg.mpr (by linarith [F.cap_ge_one]))) (Real.rpow_nonneg F.scale_pos.le _))) (Nat.cast_nonneg _)).trans (hh.trans hU)

/-- A finite dyadic assignment includes the empty bin explicitly. -/
def binLabel {M J : ℕ} (n : Fin M → ℕ) (hn : ∀ i, n i ≤ 2 ^ J) (i : Fin M) :
    Option (Fin (J+1)) :=
  if h : n i = 0 then none else some ⟨Nat.log 2 (n i), by
    have hh := Nat.log_mono_right (hn i) (b := 2)
    rw [Nat.log_pow (by norm_num : 1 < 2)] at hh
    omega⟩

def binDensity (δ C : ℝ) {J : ℕ} : Option (Fin (J+1)) → ℝ
  | none => 0
  | some j => δ * (2 : ℝ) ^ j.val / (2*C)

theorem binLabel_some {M J : ℕ} (n : Fin M → ℕ) (hn : ∀ i, n i ≤ 2 ^ J)
    {i : Fin M} {j : Fin (J+1)} (h : binLabel n hn i = some j) :
    2 ^ j.val ≤ n i ∧ n i < 2 ^ (j.val+1) := by
  classical
  unfold binLabel at h
  split_ifs at h with hz
  have hj : Nat.log 2 (n i) = j.val := congrArg Fin.val (Option.some.inj h)
  rw [← hj]
  exact ⟨(KakeyaFinite.dyadic_bin_membership (Nat.pos_of_ne_zero hz) (hn i)).1,
      (KakeyaFinite.dyadic_bin_membership (Nat.pos_of_ne_zero hz) (hn i)).2.1⟩

theorem binDensity_lower {M J : ℕ} (n : Fin M → ℕ) (hn : ∀ i, n i ≤ 2 ^ J)
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 < C) (i : Fin M) :
    δ * (n i : ℝ) / (4*C) ≤ binDensity δ C (binLabel n hn i) := by
  classical
  by_cases hz : n i = 0
  · simp [binLabel,hz,binDensity]
  · have hh := (KakeyaFinite.dyadic_bin_membership (Nat.pos_of_ne_zero hz) (hn i)).2.1
    have hnr : (n i : ℝ) ≤ 2 * (2 : ℝ) ^ Nat.log 2 (n i) := by
      exact_mod_cast (show n i ≤ 2 * 2 ^ Nat.log 2 (n i) by simpa [pow_succ, Nat.mul_comm] using hh.le)
    simp only [binLabel,hz,↓reduceDIte,binDensity]
    apply (div_le_div_iff₀ (by positivity : 0 < 4*C) (by positivity : 0 < 2*C)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hnr hδ]


/-- The actual integer classes cost J+2, with one explicit zero-density class.
The count budget is solely the geometric upper bound on each tube's cells. -/
theorem finite_bin_bound {k : ℕ} {geom : Normalization} {m d p ε c : ℝ}
    (hc : 0 < c) (hp : 1 ≤ p)
    (hestimate : ∀ H : ShadedConfiguration k geom m,
      c * H.A⁻¹ * H.δ ^ (m-d+ε) * H.lam ^ p * H.M ≤ (H.family.unionCells.card : ℝ))
    (F : CumulativeConfiguration k geom m) (hM : 0 < F.M) {J : ℕ}
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
        have hh := subfamily_bound hc (by linarith : 0 ≤ p) hestimate F (S (some j)) hs
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


/-- The class count is bounded uniformly by an arbitrarily small scale power.
The constant is fixed before δ; no cumulative-density term enters the budget. -/
theorem uniform_bin_budget {C η : ℝ} (hC : 1 ≤ C) (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∃ J : ℕ,
      C / δ ≤ (2 : ℝ)^J ∧ (J : ℝ)+2 ≤ K * (1/δ)^η := by
  have hC0 : 0 < C := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlC : 0 ≤ Real.log C := Real.log_nonneg hC
  let B := (Real.log C / Real.log 2 + 4) / Real.log 2
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨K,hK,hlog⟩ := log_power_uniform_bound (P := 1) (by norm_num) hη
  refine ⟨B*K,mul_pos hB hK,?_⟩
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
  have hh := hlog (1/δ) hN
  rw [Real.rpow_one] at hh
  calc
    (J : ℝ)+2 ≤ B*L := hlinear
    _ ≤ B*(K*(1/δ)^η) := mul_le_mul_of_nonneg_left hh hB.le
    _ = B*K*(1/δ)^η := by ring

end Cumulative

/-- The normalized estimate implies its cumulative arbitrary-shading version.
All constants precede scale, cumulative density, cap coefficient and tube count. -/
theorem DiscreteEstimate.to_cumulative {k : ℕ} {m d p : ℝ}
    (hestimate : DiscreteEstimate k m d p) (hp : 1 ≤ p) :
    CumulativeEstimate k m d p := by
  classical
  intro geom ε hε
  let C := DiscreteMeasurable.gridCountConstant k geom.width
  have hC1 : 1 ≤ C := DiscreteMeasurable.gridCountConstant_ge_one _ _
  have hC : 0 < C := by linarith
  obtain ⟨c,hc,hbound⟩ := hestimate geom (ε/2) (by linarith)
  obtain ⟨K,hK,hbudget⟩ := Cumulative.uniform_bin_budget hC1 (show 0 < ε/2 by linarith)
  let D := (4*C)^p
  have hD : 0 < D := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨c/(D*K),div_pos hc (mul_pos hD hK),?_⟩
  intro F
  by_cases hM : F.M = 0
  · simp [hM]
  have hMpos : 0 < F.M := Nat.pos_of_ne_zero hM
  obtain ⟨J,hJ,hJB⟩ := hbudget F.δ F.scale_pos F.scale_le_one
  have hh := Cumulative.finite_bin_bound hc hp hbound F hMpos hJ
  have hU : 0 ≤ (F.family.unionCells.card : ℝ) := Nat.cast_nonneg _
  have hscaled := hh.trans (mul_le_mul_of_nonneg_right hJB hU)
  have hδp : 0 < F.δ ^ (ε/2) := Real.rpow_pos_of_pos F.scale_pos _
  have hmul := mul_le_mul_of_nonneg_left hscaled (div_nonneg hδp.le hK.le)
  have hcancel : (F.δ ^ (ε/2)/K) * (K * (1/F.δ)^(ε/2) * (F.family.unionCells.card : ℝ)) =
      (F.family.unionCells.card : ℝ) := by
    rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 1) F.scale_pos.le,Real.one_rpow]
    field_simp
  have hpow : F.δ ^ (m-d+ε) = F.δ ^ (m-d+ε/2) * F.δ ^ (ε/2) := by
    rw [← Real.rpow_add F.scale_pos]
    congr 1
    ring
  have hs : (F.s/(4*C))^p = F.s^p / D := Real.div_rpow F.density_nonneg (by positivity) _
  rw [hcancel] at hmul
  calc
    c/(D*K) * F.A⁻¹ * F.δ^(m-d+ε) * F.s^p * F.M =
        (F.δ^(ε/2)/K) * (c * F.A⁻¹ * F.δ^(m-d+ε/2) * (F.s/(4*C))^p * F.M) := by
      rw [hpow,hs]
      ring
    _ ≤ (F.family.unionCells.card : ℝ) := hmul

/-- Every ambient-dimensional real-cap instance gains the same cumulative
extension, with no lower bound on the cumulative density. -/
theorem RealCapEstimate.to_cumulative {m d p : ℝ} (h : RealCapEstimate m d p)
    (hp : 1 ≤ p) : ∀ k : ℕ, m ≤ (k : ℝ)-1 → CumulativeEstimate k m d p :=
  fun k hk => (h k hk).to_cumulative hp

end
end KakeyaFormal

#print axioms KakeyaFormal.Cumulative.subfamily_bound
#print axioms KakeyaFormal.Cumulative.finite_bin_bound
#print axioms KakeyaFormal.Cumulative.uniform_bin_budget
#print axioms KakeyaFormal.DiscreteEstimate.to_cumulative
#print axioms KakeyaFormal.RealCapEstimate.to_cumulative
