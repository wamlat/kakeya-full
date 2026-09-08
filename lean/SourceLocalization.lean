import FiniteLocalizedFamily

/-! Standalone original-cell smallest-scale localization, displaying BOTH
quantitative density comparisons and the actual c M/log(2/delta)^2 population.
This is Lemma3.1 / first-step Lemma7 under the explicitly permitted fixed
unit-top-ball normalization. No endpoint estimate or desired selection is used. -/
namespace KakeyaFormal.SourceLocalization
open FiniteGridLocalization FiniteLocalizedFamily AngularSeedLogLoss LocalizedSeedNormalization
open KakeyaFormal.Localization
noncomputable section

/-- The actual common-radius and density selection, retaining its dyadic
index in the public conclusion instead of discarding it from the record. -/
theorem dyadic_selection {k M : ℕ} (F : TubeFamily k M) {δ alpha lam : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ alpha) (hlam : 0 < lam)
    (hcomp : F.Comparable δ lam) (x₀ : Fin M → Space k)
    (hcover : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (x₀ i) ≤ 1) :
    ∃ S : Selection F δ alpha lam, ∃ j : ℕ, j ≤ S.J ∧ S.rho = KakeyaFormal.Localization.radius S.J j := by
  obtain ⟨J,j,x,S,hj,hJ,hcount,hlo,hhi,hlocal⟩ := common_radius F hδ hδ1 ha x₀ hcover
  let rho := radius J j
  let Z := fun i => restrictCells δ (F.shade i) (x i) rho
  let b := rho^alpha*(lam/δ)
  have hrho : 0 < rho := hδ.trans_le hlo
  have hb : 0 < b := mul_pos (Real.rpow_pos_of_pos hrho alpha) (div_pos hlam hδ)
  have hS : S.Nonempty := Finset.card_pos.mp (by
    have hh := (div_pos (by exact_mod_cast hM) (by positivity : (0:ℝ) < (J+1:ℕ))).trans_le hcount
    exact_mod_cast hh)
  have hlow (i : Fin M) (hi : i ∈ S) : b ≤ ((Z i).card:ℝ) :=
    (mul_le_mul_of_nonneg_left (hcomp i).1 (Real.rpow_pos_of_pos hrho alpha).le).trans (hlocal i hi).1
  have hupp (i : Fin M) : ((Z i).card:ℝ) ≤ 2*lam/δ :=
    (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (hcomp i).2
  obtain ⟨i₀,hi₀⟩ := hS
  obtain ⟨D,hD,hDlog⟩ := ScaleChoice.dyadic_class_budget hb ((hlow i₀ hi₀).trans (hupp i₀))
  obtain ⟨ell,hell,R,hRS,hrange,hret⟩ := OccupancySelection.weighted_dyadic_selection S
    (fun i => ((Z i).card:ℝ)) (fun _ => (1:ℝ)) hb D hlow
    (fun i _ => (hupp i).trans (by simpa only [mul_comm] using hD))
  have hRcard : (S.card:ℝ)/(D+1:ℕ) ≤ (R.card:ℝ) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hret
  have htotal : (M:ℝ)/((J+1:ℕ)*(D+1:ℕ)) ≤ (R.card:ℝ) := by
    have hh := (div_le_div_of_nonneg_right hcount (by positivity : (0:ℝ) ≤ (D+1:ℕ))).trans hRcard
    simpa only [div_div] using hh
  have hRne : R.Nonempty := Finset.card_pos.mp (by
    have hh := (div_pos (by exact_mod_cast hM) (by positivity : (0:ℝ) < (J+1:ℕ)*(D+1:ℕ))).trans_le htotal
    exact_mod_cast hh)
  let s := δ*(b*(2:ℝ)^ell)
  have hs : 0 < s := by dsimp [s]; positivity
  have hslo : rho^alpha*lam ≤ s := by
    have hp : (1:ℝ) ≤ (2:ℝ)^ell := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hp (mul_pos (Real.rpow_pos_of_pos hrho alpha) hlam).le
    calc
      _ ≤ rho^alpha*lam*(2:ℝ)^ell := by simpa only [mul_one] using hh
      _ = s := by dsimp [s,b]; field_simp
  have hDfinal : (D:ℝ)+1 ≤ alpha*(Real.log (1/δ)/Real.log 2)+3 := by
    have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    have hratio : (2*lam/δ)/b = 2/rho^alpha := by dsimp [b]; field_simp
    have hlogrho := Real.log_le_log hδ hlo
    have hmul := mul_le_mul_of_nonneg_left hlogrho ha
    rw [hratio,Real.log_div (by norm_num : (2:ℝ) ≠ 0) (Real.rpow_pos_of_pos hrho alpha).ne',Real.log_rpow hrho] at hDlog
    rw [one_div,Real.log_inv]
    apply le_trans hDlog
    apply (mul_le_mul_iff_right₀ hlog2).mp
    field_simp
    linarith
  refine ⟨⟨J,D,rho,s,x,R,hRne,hlo,hhi,hJ,hDfinal,htotal,hs,hslo,?_,?_⟩,j,hj,rfl⟩
  · intro i hi
    have hh := hrange i hi
    have hlo' : s/δ = b*(2:ℝ)^ell := by dsimp [s]; field_simp
    rw [hlo']
    refine ⟨hh.1,?_⟩
    have hhi' : 2*s/δ = 2*(b*(2:ℝ)^ell) := by dsimp [s]; field_simp
    rw [hhi']
    exact hh.2.le
  · intro i hi
    exact (hlocal i (hRS hi)).2


/-- All constants precede the actual family, scale and original density. The
returned Selection retains literal old-cell restrictions and its all-radius
4^alpha relative two-ends inequality. -/
theorem construct (k : ℕ) (width alpha : ℝ) (ha : 0 ≤ alpha) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ {M : ℕ} (F : TubeFamily k M) {δ lam : ℝ},
      0 < M → 0 < δ → δ ≤ 1 → 0 < lam →
      F.Admissible width δ → F.Comparable δ lam →
      ∀ x₀ : Fin M → Space k,
      (∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (x₀ i) ≤ 1) →
      ∃ S : Selection F δ alpha lam,
        (∃ j : ℕ, j ≤ S.J ∧ S.rho = radius S.J j) ∧
        c*(M:ℝ)/(Real.log (2/δ))^2 ≤ (S.selected.card:ℝ) ∧
        S.rho^alpha*lam ≤ S.s ∧ S.s ≤ C*S.rho := by
  let a := (3:ℝ)/Real.log 2
  have ha0 : 0 < a := div_pos (by norm_num) (Real.log_pos (by norm_num))
  have hC : 0 < countConstant k width := by
    unfold countConstant
    positivity [LocalizedGridTubes.localWidth_pos width]
  refine ⟨1/((alpha+3)*a^2), countConstant k width, by positivity, hC, ?_⟩
  intro M F δ lam hM hδ hδ1 hlam hadm hcomp x₀ hcover
  obtain ⟨S,hdyadic⟩ := dyadic_selection F hM hδ hδ1 ha hlam hcomp x₀ hcover
  refine ⟨S, hdyadic, ?_, S.density_lower, selected_density_upper S hδ hadm⟩
  have hlog : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlogmin : Real.log 2 ≤ Real.log (2/δ) :=
    Real.log_le_log (by norm_num) ((le_div_iff₀ hδ).mpr (by linarith))
  have hSlog : seedLog δ ≤ a*Real.log (2/δ) := by
    unfold seedLog Real.logb
    dsimp [a]
    calc
      Real.log (2/δ)/Real.log 2+2 = (Real.log (2/δ)+2*Real.log 2)/Real.log 2 := by field_simp
      _ ≤ (3*Real.log (2/δ))/Real.log 2 :=
        (div_le_div_iff_of_pos_right hlog2).mpr (by linarith)
      _ = _ := by ring
  have hden : (alpha+3)*(seedLog δ)^2 ≤ (alpha+3)*(a*Real.log (2/δ))^2 := by
    gcongr
    exact (seedLog_ge_one hδ hδ1).trans' (by norm_num)
  have hc := (div_le_div_of_nonneg_left (Nat.cast_nonneg M)
    (by positivity [seedLog_ge_one hδ hδ1] : 0 < (alpha+3)*(seedLog δ)^2) hden).trans
      (selected_count_log S hδ ha)
  convert hc using 1 <;> first | rfl | field_simp

end
end KakeyaFormal.SourceLocalization
