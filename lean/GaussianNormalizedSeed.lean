import GaussianProjectionSeed
import AllAngleSeparation
import CumulativeEstimate
import Endpoint

/-! The original Gaussian projection route in every fixed geometric
normalization, followed by the actual arbitrary-shading cumulative adapter.
The seven-dimensional estimate is obtained through the actual projected
five-dimensional family, rather than the direct ambient-seven fractional seed. -/
namespace KakeyaFormal.GaussianNormalizedSeed
open SeparationColoring AllAngleSeparation
open scoped BigOperators
noncomputable section
open Classical

/-- A largest actual color class pays a fixed separation factor only. Every
selected tube keeps its complete original shading and original cap bound. -/
theorem normalized_rows (geom : Normalization) {eps : ℝ} (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily 7 M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → 1 ≤ A →
      F.Admissible geom.width δ → F.Separated (geom.separation*δ) →
      F.Bounded geom.radius → F.CapBound δ 4 A →
      (∀ i, lam/δ ≤ ((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^((1:ℝ)/2+eps)*lam^((7:ℝ)/2)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hmain⟩ := GaussianProjectionSeed.original_rows geom.width geom.radius eps
    geom.width_pos geom.radius_pos heps
  let palette := paletteSize 6 geom.separation
  have hp : 0 < palette := paletteSize_pos _ _
  have hpR : (0:ℝ) < palette := by exact_mod_cast hp
  refine ⟨c/palette,div_pos hc hpR,?_⟩
  intro M F δ lam A hδ hδ1 hlam hA hadm hsep hbase hcap hrows
  obtain ⟨color,hcolor⟩ := full_separation_coloring F hδ geom.separation_pos hsep
  obtain ⟨chosen,hcount⟩ := exists_large_color hp color
  let G := classFamily F color chosen
  have hGadm : G.Admissible geom.width δ := classFamily_admissible F color hadm chosen
  have hGsep : G.Separated δ := classFamily_separated F color hcolor chosen
  have hGbase : G.Bounded geom.radius := fun i => hbase (classIndex color chosen i)
  have hGcap : G.CapBound δ 4 A := classFamily_cap_bound F color hcap chosen
  have hGrows : ∀ i, lam/δ ≤ ((G.shade i).card:ℝ) := fun i => hrows (classIndex color chosen i)
  have hbound := hmain G hδ hδ1 hlam hA hGadm hGsep hGbase hGcap hGrows
  have hfactor : 0 ≤ (c/palette)*A⁻¹*δ^((1:ℝ)/2+eps)*lam^((7:ℝ)/2) := by positivity
  have hpop := mul_le_mul_of_nonneg_left hcount hfactor
  have hcard : (G.unionCells.card:ℝ) ≤ (F.unionCells.card:ℝ) := by
    exact_mod_cast Finset.card_le_card (class_union_subset F color chosen)
  apply le_trans ?_ (hbound.trans hcard)
  calc
    _ ≤ ((c/palette)*A⁻¹*δ^((1:ℝ)/2+eps)*lam^((7:ℝ)/2))*
        ((palette:ℝ)*((colorClass color chosen).card:ℝ)) := hpop
    _ = _ := by field_simp

/-- The full normalized seven-dimensional estimate now follows by THIS
actual Gaussian route; no ambient-seven estimate is a premise. -/
theorem discrete_seed : DiscreteEstimate 7 4 (7/2) (7/2) := by
  intro geom eps heps
  obtain ⟨c,hc,hbound⟩ := normalized_rows geom heps
  refine ⟨c,hc,?_⟩
  intro F
  have hh := hbound F.family F.scale_pos F.scale_le_one F.density_pos F.cap_ge_one
    F.admissible F.separated F.bounded F.cap_bound (fun i => (F.comparable i).1)
  have he : (4:ℝ)-7/2+eps=1/2+eps := by ring
  simpa only [he] using hh

/-- Actual unequal/empty shadings are obtained by the proved cumulative
construction, with no positive lower cutoff on cumulative density. -/
theorem cumulative_seed : CumulativeEstimate 7 4 (7/2) (7/2) :=
  discrete_seed.to_cumulative (by norm_num)

/-- Exact source (2.2), including the density epsilon, derived by weakening
the normalized density exponent BEFORE the actual cumulative construction. -/
theorem source_cumulative (geom : Normalization) {eps : ℝ} (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : CumulativeConfiguration 7 geom 4,
      c*F.A⁻¹*F.δ^((1:ℝ)/2+eps)*F.s^((7:ℝ)/2+eps)*(F.M:ℝ) ≤
        (F.family.unionCells.card:ℝ) := by
  have h := discrete_seed.weaken_density (P:=(7:ℝ)/2+eps) (by linarith)
  have hc := h.to_cumulative (by linarith)
  obtain ⟨c,hcpos,hbound⟩ := hc geom eps heps
  refine ⟨c,hcpos,?_⟩
  intro F
  have he : (4:ℝ)-7/2+eps=1/2+eps := by ring
  simpa only [he] using hbound F

/-- Literal N-notation for the original family, obtained through the Gaussian
projection route. The actual total incidence is the only density premise. -/
theorem source_count (geom : Normalization) {eps : ℝ} (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ M : ℕ, ∀ F : TubeFamily 7 M, ∀ N A s : ℝ,
      1 ≤ N → 1 ≤ A → 0 ≤ s →
      F.Admissible geom.width (1/N) → F.Separated (geom.separation*(1/N)) →
      F.Bounded geom.radius → F.CapBound (1/N) 4 A →
      s*N*(M:ℝ) ≤ ∑ i, ((F.shade i).card:ℝ) →
      c*A⁻¹*N^(-(1:ℝ)/2-eps)*s^((7:ℝ)/2+eps)*(M:ℝ) ≤
        (F.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hbound⟩ := source_cumulative geom heps
  refine ⟨c,hc,?_⟩
  intro M F N A s hN hA hs hadm hsep hbounded hcap hinc
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hcum : s*(M:ℝ) ≤ (1/N)*∑ i, ((F.shade i).card:ℝ) := by
    rw [one_div,mul_comm N⁻¹]
    apply (le_div_iff₀ hN0).mpr
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hinc
  let G : CumulativeConfiguration 7 geom 4 :=
    { M:=M, δ:=1/N, s:=s, A:=A, family:=F,
      scale_pos:=one_div_pos.mpr hN0, scale_le_one:=(div_le_one hN0).mpr hN,
      density_nonneg:=hs, cap_ge_one:=hA, admissible:=hadm, separated:=hsep,
      bounded:=hbounded, cap_bound:=hcap, cumulative:=hcum }
  have hh := hbound G
  have hp : (1/N)^((1:ℝ)/2+eps) = N^(-(1:ℝ)/2-eps) := by
    rw [one_div,← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  simpa only [G,hp] using hh

end
end KakeyaFormal.GaussianNormalizedSeed
