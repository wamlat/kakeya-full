import GaussianProjectedFamily
import FiveDimensionalLengthSeed
import GaussianProjectionAlgebra

/-! The original seven-to-five Gaussian projection argument, completed on
actual projected shadings. Its five-dimensional input is itself proved. -/
namespace KakeyaFormal.GaussianProjectionSeed
open GaussianProjectedFamily GaussianProjectedSelection ProjectedGrid
noncomputable section

def targetGeometry (width R : ℝ) (hw : 0 < width) (hR : 0 < R) : Normalization where
  width := 20*width+(5:ℝ)/2
  separation := 2/Real.pi
  radius := 20*R
  width_pos := by positivity
  separation_pos := div_pos (by norm_num) Real.pi_pos
  radius_pos := by positivity

/-- Original separated cap-four tubes in dimension seven obtain the source
set/density powers THROUGH the actual Gaussian-selected five-dimensional
family. Only lower original row density is required; M=0 is included. -/
theorem original_rows (width R eps : ℝ) (hw : 0 < width) (hR : 0 < R)
    (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily 7 M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → 1 ≤ A →
      F.Admissible width δ → F.Separated δ → F.Bounded R → F.CapBound δ 4 A →
      (∀ i, lam/δ ≤ ((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^((1:ℝ)/2+eps)*lam^((7:ℝ)/2)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let C : ℝ := (fiberConstant 7 5 (1/4) 20 width:ℝ)
  have hC : 0 < C := by
    dsimp [C]
    exact_mod_cast fiberConstant_pos 7 5 (1/4) 20 width
  have heta : 0 < eps/2 := half_pos heps
  obtain ⟨c,hc,hseed⟩ := FiveDimensionalLengthSeed.original_length_bound
    (targetGeometry width R hw hR) 20 (1/C) (eps/2) (one_div_pos.mpr hC) heta
  obtain ⟨ell,hell,hlog⟩ := GaussianProjectionAlgebra.inverse_log_delta heta
  refine ⟨c*retainedConstant*ell,mul_pos (mul_pos hc retainedConstant_pos) hell,?_⟩
  intro M F δ lam A hδ hδ1 hlam hA hadm hsep hbounded hcap hrows
  obtain ⟨U⟩ := construct F hδ hδ1 hA hsep hcap hadm hbounded
  have hrow : ∀ i, (1/C)*lam/δ ≤ ((U.family.shade i).card:ℝ) := by
    intro i
    have hh := (div_le_div_of_nonneg_right (hrows (indexMap U.selected i)) hC.le).trans
      (U.row_bounds i).1
    calc
      (1/C)*lam/δ = (lam/δ)/C := by ring
      _ ≤ _ := hh
  have htarget := hseed U.family (lengths F U.selected U.omega) hδ hδ1 hlam
    (fun i => (U.length_bounds i).2) U.carrier U.separated U.bounded hrow
  have htarget' := htarget.trans (show ((U.family.unionCells.card:ℝ)) ≤ F.unionCells.card by
    exact_mod_cast U.union_card_le)
  have hlogpos : 0 < Real.log (2/δ) :=
    Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hh := GaussianProjectionAlgebra.closing hδ hlam.le (zero_lt_one.trans_le hA)
    (Nat.cast_nonneg M) hc.le retainedConstant_pos.le hlogpos
    (hlog δ hδ hδ1) U.population htarget'
  have he : (1:ℝ)/2+2*(eps/2)=1/2+eps := by ring
  simpa only [he] using hh

end
end KakeyaFormal.GaussianProjectionSeed
