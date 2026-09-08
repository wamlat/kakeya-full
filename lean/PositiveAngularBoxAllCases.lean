import AngularBoxCoarse
import AngularBoxLowDensity
import PositiveAngularBoxHighDensity

/-! Positive-base-density extension (p>0), reusing the constructed geometry.
 All local angular cases on the SAME actual spatial package and old cells.
Each positive case constant is fixed before the original family, angular
pieces, measured refinement, output choices and spatial-box index. -/
namespace KakeyaFormal.PositiveAngularBoxAllCases
open Finset AngularSeedPieces AngularRestrictedRefinement AngularSpatialSampling
open WidthNormalization SpatialMarkedPartition
noncomputable section
open Classical

/-- The two density-cutoff conventions in the constructive low and high
branches coincide at every positive normalized mesh. -/
theorem inverse_density_cutoff {s : ℝ} (hs : 0 < s) :
    (1/s)^(-(1:ℝ)/3) = s^((1:ℝ)/3) := by
  rw [one_div,Real.inv_rpow hs.le,← Real.rpow_neg hs.le]
  congr 1
  ring

/-- The complement of the source coarse scale supplies the literal power
comparison needed by BOTH normalized low and high estimates. -/
theorem fine_power_comparison {δ s a : ℝ} (hδ : 0 < δ) (hs : 0 < s) (ha : 0 < a)
    (hnot : ¬δ^(1/a) ≤ s) : s^a ≤ δ := by
  have hh := Real.rpow_le_rpow hs.le (le_of_lt (lt_of_not_ge hnot)) ha.le
  rw [← Real.rpow_mul hδ.le,one_div_mul_cancel ha.ne',Real.rpow_one] at hh
  exact hh

/-- No branch test, chosen threshold, logarithmic budget, population bound,
Input record, or desired old-cell bound remains among the local hypotheses.
The SAME U.output q is tested in the exhaustive case split. -/
theorem construct {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 0 < pExp) (hd : 0 ≤ d) (hq : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m+1)
    (width R B alpha beta eps : ℝ)
    (hR : 0 ≤ R) (hB : 1 ≤ B) (halpha : 0 < alpha) (hbeta : 0 < beta) (heps : 0 < eps)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+(KakeyaScalar.pivotDensity pExp qExp-2)/3)
    (hW : 2 ≤ (widthFactor (k+2) width)^(k+2)) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} {δ lam A : ℝ} (F : TubeFamily (k+2) M)
      (P : Pieces F δ beta) {g : Fin M} (V : Refinement P lam B alpha g)
      (_U : Package V width R m A),
      g ∈ P.groups → 0 < δ → lam ≤ 1 → 1 ≤ Real.log (2/δ) → 1 ≤ A →
      F.Admissible width δ → F.Separated δ → F.Bounded R → F.CapBound δ m A →
      ∀ q : ↥(boxes V width),
      c*A⁻¹*(δ/P.tau)^(m-KakeyaScalar.pivotSet m d'+eps)*
        (physicalDensity V width)^(KakeyaScalar.pivotDensity pExp qExp)*
        ((indices (SpatialGridPopulation.refinedLabel V width) q.val).card:ℝ) ≤
          ((SpatialGridPopulation.refinedCells V width q.val).card:ℝ) := by
  let a : ℝ := 2*(((k+1:ℕ):ℝ)+1)
  have ha : 1 ≤ a := by dsimp [a]; have := Nat.cast_nonneg (α:=ℝ) (k+1); linarith
  have hC : 2 ≤ KakeyaScalar.pivotDensity pExp qExp := by
    dsimp [KakeyaScalar.pivotDensity]
    linarith
  have hmn' : m+1 ≤ ((k+1:ℕ):ℝ)+1 := by
    norm_num only [Nat.cast_add,Nat.cast_one]
    linarith
  obtain ⟨δh,hδh,_hδh1,cH,hcH,hHigh⟩ := PositiveAngularBoxHighDensity.construct hbase hlift
    (zero_le_one.trans hm) hp hd hq hD width R B alpha beta eps a hB halpha hbeta heps ha
  obtain ⟨cB,hcB,hBounded⟩ := AngularBoxCoarse.bounded_scale (k:=k)
    (D:=KakeyaScalar.pivotSet m d') (C:=KakeyaScalar.pivotDensity pExp qExp) (eps:=eps)
    width R B alpha beta δh hR (zero_le_one.trans hm) (by linarith) hδh
  obtain ⟨cC,hcC,hCoarse⟩ := AngularBoxCoarse.coarse (k:=k)
    (D:=KakeyaScalar.pivotSet m d') (C:=KakeyaScalar.pivotDensity pExp qExp) (eps:=eps)
    width R B alpha beta hR (zero_le_one.trans hm) hD hmn' (by linarith) heps.le
  obtain ⟨cL,hcL,hLow⟩ := AngularBoxLowDensity.construct k width R B alpha beta m
    (KakeyaScalar.pivotSet m d') (KakeyaScalar.pivotDensity pExp qExp) eps a
    hR hB halpha hbeta hm hC heps ha hmargin hW
  let c := min (min cH cB) (min cC cL)
  have hc : 0 < c := lt_min (lt_min hcH hcB) (lt_min hcC hcL)
  refine ⟨c,hc,?_⟩
  intro M δ lam A F P g V U hg hδ hlam hL hA hadm hsep hbounded hcap q
  have htau : 0 < P.tau := hδ.trans_le P.lower_scale
  have hs : 0 < δ/P.tau := div_pos hδ htau
  have hfactor : 0 ≤ A⁻¹*(δ/P.tau)^(m-KakeyaScalar.pivotSet m d'+eps)*
      (physicalDensity V width)^(KakeyaScalar.pivotDensity pExp qExp)*
      ((indices (SpatialGridPopulation.refinedLabel V width) q.val).card:ℝ) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hA)) (Real.rpow_nonneg hs.le _))
        (Real.rpow_nonneg (physicalDensity_pos V width).le _)) (Nat.cast_nonneg _)
  have weaken (b : ℝ) (hcb : c ≤ b)
      (hh : b*A⁻¹*(δ/P.tau)^(m-KakeyaScalar.pivotSet m d'+eps)*
        (physicalDensity V width)^(KakeyaScalar.pivotDensity pExp qExp)*
        ((indices (SpatialGridPopulation.refinedLabel V width) q.val).card:ℝ) ≤
          ((SpatialGridPopulation.refinedCells V width q.val).card:ℝ)) :
      c*A⁻¹*(δ/P.tau)^(m-KakeyaScalar.pivotSet m d'+eps)*
        (physicalDensity V width)^(KakeyaScalar.pivotDensity pExp qExp)*
        ((indices (SpatialGridPopulation.refinedLabel V width) q.val).card:ℝ) ≤
          ((SpatialGridPopulation.refinedCells V width q.val).card:ℝ) := by
    have hmono := mul_le_mul_of_nonneg_right hcb hfactor
    simp only [← mul_assoc] at hmono
    exact hmono.trans hh
  by_cases hlarge : δh ≤ δ/P.tau
  · apply weaken cB ((min_le_left _ _).trans (min_le_right _ _))
    exact hBounded P g V U q hg hδ hlam hA hsep hbounded hcap hlarge
  have hsmall : δ/P.tau ≤ δh := (lt_of_not_ge hlarge).le
  by_cases hcoarse : δ^(1/a) ≤ δ/P.tau
  · apply weaken cC ((min_le_right _ _).trans (min_le_left _ _))
    exact hCoarse P g V U q hg hδ hlam hA hsep hbounded hcap hcoarse
  have hcompare : (δ/P.tau)^a ≤ δ := fine_power_comparison hδ hs (zero_lt_one.trans_le ha) hcoarse
  by_cases hlow : (U.output q).density ≤ (δ/P.tau)^((1:ℝ)/3)
  · apply weaken cL ((min_le_right _ _).trans (min_le_right _ _))
    exact hLow F P V U hg hδ hlam hL hA hadm hsep hbounded hcap hcompare q hlow
  apply weaken cH ((min_le_left _ _).trans (min_le_left _ _))
  apply hHigh P g V U q hδ hA hsmall hcompare
  rw [inverse_density_cutoff hs]
  exact (lt_of_not_ge hlow).le

end
end KakeyaFormal.PositiveAngularBoxAllCases
