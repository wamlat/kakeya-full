import AngularBoxAllCases
import AngularSpatialSummation
import CoarseBounds

/-! The unrestricted angular pivot under full two ends. Every angular piece,
refined reference, spatial box, retained measurable output and local case is
constructed from the original finite family. Full two ends remains explicit. -/
namespace KakeyaFormal.AllAnglePivot
open Finset AngularSeedPieces AngularRestrictedRefinement AngularSpatialSampling
open WidthNormalization
noncomputable section
open Classical

/-- All angular cases and original-cell sums are assembled from the original
family. No marked rows, angular decomposition, sampling outcome, box estimate,
conditioning budget or analytic conclusion is assumed. -/
theorem logarithmic_range {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 1 ≤ pExp) (hd : 0 ≤ d) (hq : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m)
    (width R B alpha eps : ℝ)
    (hR : 0 ≤ R) (hB : 1 ≤ B) (halpha : 0 < alpha) (heps : 0 < eps)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+(KakeyaScalar.pivotDensity pExp qExp-2)/3)
    (hW : 2 ≤ (widthFactor (k+2) width)^(k+2)) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+2) M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A → 1 ≤ Real.log (2/δ) →
      F.Admissible width δ → F.Separated δ → F.Bounded R → F.CapBound δ m A →
      F.Comparable δ lam →
      (∀ i x r, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          B*r^alpha*((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let beta := min 1 (m-KakeyaScalar.pivotSet m d')/2
  have hbeta : 0 < beta := div_pos (lt_min zero_lt_one (sub_pos.mpr hD)) (by norm_num)
  have hbetas : beta ≤ m-KakeyaScalar.pivotSet m d'+eps/2 := by
    have hh : min 1 (m-KakeyaScalar.pivotSet m d') ≤ m-KakeyaScalar.pivotSet m d' := min_le_right _ _
    dsimp [beta]
    linarith
  have hC : 0 ≤ KakeyaScalar.pivotDensity pExp qExp := by
    dsimp [KakeyaScalar.pivotDensity]
    linarith
  obtain ⟨cP,hcP,hpiece⟩ := AngularBoxAllCases.construct hbase hlift hm hmn hp hd hq
    (by linarith : KakeyaScalar.pivotSet m d' < m+1) width R B alpha beta (eps/2)
    hR hB halpha hbeta (by positivity) hmargin hW
  obtain ⟨c,hc,hsum⟩ := AngularSpatialSummation.from_piece_estimates (k+1) width beta
    (KakeyaScalar.pivotDensity pExp qExp) (m-KakeyaScalar.pivotSet m d'+eps/2) (eps/2) cP
    hC hbetas (by positivity) hcP
  refine ⟨c,hc,?_⟩
  intro M F δ lam A hδ hδ1 hlam hlam1 hA hL hadm hsep hbounded hcap hcomp hends
  by_cases hM : M=0
  · simp only [hM,Nat.cast_zero,mul_zero]
    positivity
  obtain ⟨P⟩ := AngularSeedPieces.exists_pieces F (Nat.pos_of_ne_zero hM) hδ hδ1 hbeta.le
  have hkept := (P.pruning hδ hlam hcomp).1
  let V (g : ↥(P.keptGroups lam)) : Refinement P lam B alpha g.val :=
    Classical.choice (AngularRestrictedRefinement.construct F P hδ hlam (zero_le_one.trans hB)
      hcomp hends g.val g.property)
  let U (g : ↥(P.keptGroups lam)) : Package (V g) width R m A :=
    Classical.choice (AngularSpatialSampling.construct (V g) (hkept g.property) hδ hR hlam1 hW
      hB halpha.le hbeta (zero_le_one.trans hm) (zero_le_one.trans hA) hadm hsep hbounded hcap)
  have hh := hsum F P hδ hlam hA hcomp hadm hL V (fun g => (U g).spatial)
    (fun g q hq => hpiece F P (V g) (U g) (hkept g.property) hδ hlam1 hL hA
      hadm hsep hbounded hcap ⟨q,hq⟩)
  simpa only [show (m-KakeyaScalar.pivotSet m d'+eps/2)+eps/2 =
    m-KakeyaScalar.pivotSet m d'+eps by ring] using hh

/-- A fixed enlargement of the original width supplies the physical density
 normalization in every ambient dimension used by the pivot. -/
theorem fixed_width_test (k : ℕ) (width : ℝ) :
    2 ≤ (widthFactor (k+2) (max width 1))^(k+2) := by
  have hdim : (1:ℝ) ≤ ((k+2:ℕ):ℝ)/2 := by
    norm_num only [Nat.cast_add,Nat.cast_ofNat]
    have := Nat.cast_nonneg (α:=ℝ) k
    linarith
  have hw : 2 ≤ widthFactor (k+2) (max width 1) := by
    have hh : 2 ≤ max width 1+((k+2:ℕ):ℝ)/2 := by linarith [le_max_right width 1]
    exact hh.trans (le_max_right _ _)
  have hp : 1 ≤ (widthFactor (k+2) (max width 1))^(k+1) :=
    one_le_pow₀ (by linarith : 1 ≤ widthFactor (k+2) (max width 1))
  calc
    _ ≤ widthFactor (k+2) (max width 1) := hw
    _ ≤ (widthFactor (k+2) (max width 1))^(k+1)*widthFactor (k+2) (max width 1) :=
      le_mul_of_one_le_left (by linarith) hp
    _ = _ := (pow_succ _ (k+1)).symm

/-- Every original scale and fixed width/base normalization is allowed.
Only the original full two-ends condition and the two analytic inputs remain;
all marked broadness, angular, density and case hypotheses are discharged. -/
theorem all_scales {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 1 ≤ pExp) (hd : 0 ≤ d) (hq : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m)
    (width R B alpha eps : ℝ) (hB : 1 ≤ B) (halpha : 0 < alpha) (heps : 0 < eps)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+(KakeyaScalar.pivotDensity pExp qExp-2)/3) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+2) M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      F.Admissible width δ → F.Separated δ → F.Bounded R → F.CapBound δ m A →
      F.Comparable δ lam →
      (∀ i x r, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          B*r^alpha*((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  have hR : 0 < max R 1 := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨cS,hcS,hsmall⟩ := logarithmic_range hbase hlift hm hmn hp hd hq hD
    (max width 1) (max R 1) B alpha eps hR.le hB halpha heps hmargin (fixed_width_test k width)
  let cutoff : ℝ := 2/Real.exp 1
  have hcutoff : 0 < cutoff := by dsimp [cutoff]; positivity
  let cB := 1/(ProjectiveGeometry.packingConstant (k+1)*
    max 1 (cutoff^(1-KakeyaScalar.pivotSet m d'+eps)))
  have hpacking : 0 < ProjectiveGeometry.packingConstant (k+1) :=
    zero_lt_one.trans_le (ProjectiveGeometry.packingConstant_ge_one _)
  have hcB : 0 < cB := by dsimp [cB]; positivity
  have hC : 1 ≤ KakeyaScalar.pivotDensity pExp qExp := by
    dsimp [KakeyaScalar.pivotDensity]
    linarith
  refine ⟨min cS cB,lt_min hcS hcB,?_⟩
  intro M F δ lam A hδ hδ1 hlam hlam1 hA hadm hsep hbounded hcap hcomp hends
  have hadm' : F.Admissible (max width 1) δ := by
    intro i z hz
    obtain ⟨t,ht,hdist⟩ := hadm i z hz
    exact ⟨t,ht,hdist.trans (mul_le_mul_of_nonneg_right (le_max_left width 1) hδ.le)⟩
  have hbounded' : F.Bounded (max R 1) := fun i => (hbounded i).trans (le_max_left _ _)
  have hfactor : 0 ≤ A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
      lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) := by positivity
  by_cases hfine : δ ≤ cutoff
  · have hL : 1 ≤ Real.log (2/δ) := by
      apply (Real.le_log_iff_exp_le (div_pos (by norm_num) hδ)).mpr
      apply (le_div_iff₀ hδ).mpr
      simpa only [mul_comm] using (le_div_iff₀ (Real.exp_pos 1)).mp hfine
    have hh := mul_le_mul_of_nonneg_right (min_le_left cS cB) hfactor
    have hb := hsmall F hδ hδ1 hlam hlam1 hA hL hadm' hsep hbounded' hcap hcomp hends
    have hle : (min cS cB)*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤
        cS*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
          lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) := by simpa only [mul_assoc] using hh
    exact hle.trans hb
  · let geom : Normalization := ⟨max width 1,1,max R 1,
      zero_lt_one.trans_le (le_max_right _ _),by norm_num,hR⟩
    let V : ShadedConfiguration (k+2) geom m := {
      M := M, δ := δ, lam := lam, A := A, family := F,
      scale_pos := hδ, scale_le_one := hδ1, density_pos := hlam, density_le_one := hlam1,
      cap_ge_one := hA, admissible := hadm', separated := by simpa [geom] using hsep,
      bounded := hbounded', cap_bound := hcap, comparable := hcomp }
    have hb := CoarseBounds.coarse_configuration_bound
      (d:=KakeyaScalar.pivotSet m d') (eps:=eps) hcutoff hC geom V (lt_of_not_ge hfine).le
    have hh := mul_le_mul_of_nonneg_right (min_le_right cS cB) hfactor
    have hle : (min cS cB)*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤
        cB*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
          lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) := by simpa only [mul_assoc] using hh
    exact hle.trans hb

end
end KakeyaFormal.AllAnglePivot
