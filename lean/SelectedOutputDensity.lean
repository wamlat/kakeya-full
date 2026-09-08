import SelectedOutputSlabs
import ActualGroupedIncidence

/-! The cumulative density used by grouped pruning is computed from its actual
normalized incidence set. Its lower bound pays the unit-segment factor three,
and its upper bound follows from the original geometric fiber count. -/
namespace KakeyaFormal.SelectedOutputDensity
open Finset ActualLabelSelection AngleFiberSelection LegalAngleSamples
open SelectedOutputPairs SelectedOutputSlabs SelectedFiberLift SlabNormalization
open ActualGroupedIncidence
open scoped BigOperators
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
    {δ lam kappa width : ℝ} {S : SampleSystem F H δ lam kappa width}
    {hkappa : 0 < kappa} {hwidth : 0 ≤ width} {hadm : F.Admissible width δ}
    (P : Selection S hkappa hwidth hadm)
    (D : ∀ q : Index P, LineData P q)
    {C : Type*} (color : Index P → C) (shading : Index P → Finset (Cell (k+2)))

def rho : ℝ := (δ/(1+2*width))*
  ((incidences (fun q => (D q).base P) color shading).card:ℝ)/(outputSupport P.retained).card

def lowerCoefficient (k : ℕ) (width : ℝ) : ℝ :=
  1/(60*multiplicityConstant (k+1) (2*width)*(1+2*width)^7)

theorem lowerCoefficient_pos (k : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    0 < lowerCoefficient k width := by
  have hC := multiplicityConstant_pos (k+1) (2*width)
  dsimp [lowerCoefficient]
  positivity

theorem output_card_pos : (0:ℝ) < (outputSupport P.retained).card := by
  obtain ⟨q⟩ := index_nonempty P
  exact_mod_cast (show 0 < (outputSupport P.retained).card from lt_of_le_of_lt (Nat.zero_le q.val) q.isLt)

/-- The same original output count is the denominator of actual cumulative
density. Every output retains at least K/3 actual normalized cells. -/
theorem rho_lower (hδ : 0 < δ)
    (hmass : ∀ q, (commonK P:ℝ)/3 ≤ ((shading q).card:ℝ)) :
    lowerCoefficient k width*kappa^6*((2^P.level:ℕ)*δ) ≤ rho P D color shading := by
  have hR : 0 < 1+2*width := by linarith
  have hC := multiplicityConstant_pos (k+1) (2*width)
  have hQ := output_card_pos P
  have hm := incidence_mass_lower (fun q => (D q).base P) color shading hmass
  simp only [Fintype.card_fin] at hm
  have hmult := mul_le_mul_of_nonneg_left hm (div_pos hδ hR).le
  have hdiv := div_le_div_of_nonneg_right hmult hQ.le
  have hh := (commonK_bounds P).1
  have hlow := mul_le_mul_of_nonneg_left hh (show 0 ≤ (δ/(1+2*width))/3 by positivity)
  have hidentity : (δ/(1+2*width))*((commonK P:ℝ)*(outputSupport P.retained).card/3)/
      (outputSupport P.retained).card = ((δ/(1+2*width))/3)*(commonK P:ℝ) := by
    field_simp
  rw [hidentity] at hdiv
  have hleft : ((δ/(1+2*width))/3)*
      ((kappa/(1+2*width))^6*(2^P.level:ℕ)/(20*multiplicityConstant (k+1) (2*width))) =
      lowerCoefficient k width*kappa^6*((2^P.level:ℕ)*δ) := by
    dsimp [lowerCoefficient]
    field_simp
    ring
  rw [hleft] at hlow
  exact hlow.trans hdiv

theorem rho_pos (hδ : 0 < δ)
    (hmass : ∀ q, (commonK P:ℝ)/3 ≤ ((shading q).card:ℝ)) :
    0 < rho P D color shading := by
  have hc := lowerCoefficient_pos k hwidth
  have hh := rho_lower P D color shading hδ hmass
  exact (by positivity : 0 < lowerCoefficient k width*kappa^6*((2^P.level:ℕ)*δ)).trans_le hh

/-- Original selected cells bound the size of every normalized shading; the
common lattice shift is injective, so no translated-cell multiplicity is paid. -/
theorem shading_card_le
    (hsub : ∀ q, shading q ⊆ (D q).cells.image (shiftCell (δ/(1+2*width)) (D q).slab))
    (q : Index P) : (shading q).card ≤ commonK P := by
  have hh := card_le_card (hsub q)
  rw [card_image_of_injective _ (shiftCell_injective _ _),(D q).cells_card] at hh
  exact hh

/-- The actual incidence density stays below a fixed geometric constant,
including the nonempty-floor branch of the selected cell count. -/
theorem rho_upper (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hkappa1 : kappa ≤ 1)
    (hsub : ∀ q, shading q ⊆ (D q).cells.image (shiftCell (δ/(1+2*width)) (D q).slab)) :
    rho P D color shading ≤ 1+PivotOutputCount.fiberConstant (k+1) (2*width)/
      (10*multiplicityConstant (k+1) (2*width)) := by
  have hR : 0 < 1+2*width := by linarith
  have hQ := output_card_pos P
  have hcards : ((incidences (fun q => (D q).base P) color shading).card:ℝ) ≤
      (outputSupport P.retained).card*(commonK P:ℝ) := by
    rw [incidence_card,Nat.cast_sum]
    have hh := sum_le_sum (fun q (_ : q ∈ (univ:Finset (Index P))) =>
      (show ((shading q).card:ℝ) ≤ (commonK P:ℝ) by exact_mod_cast shading_card_le P D shading hsub q))
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hh := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcards (div_pos hδ hR).le) hQ.le
  have hid : (δ/(1+2*width))*((outputSupport P.retained).card*(commonK P:ℝ))/
      (outputSupport P.retained).card = (δ/(1+2*width))*(commonK P:ℝ) := by field_simp
  rw [hid] at hh
  exact hh.trans (common_density_upper P hδ hδ1 hkappa1 (Classical.choice (index_nonempty P)))

end
end KakeyaFormal.SelectedOutputDensity
