import DensityBroadnessRecovery
import GridHairbrush

/-! The actual broad-grid hairbrush estimate after arbitrary shading deletion,
with every density, marking and two-ends recovery factor explicit. -/
namespace KakeyaFormal.RecoveredHairbrush
open Finset DensityBroadnessRecovery AngularDecomposition
open WidthNormalization HairbrushScales HairbrushAllScales
open scoped BigOperators
noncomputable section
open Classical

/-- A positive retained-density parameter is automatically at most two under
the original normalized upper density bound; it is not assumed additionally. -/
theorem eta_le_two {k M : ℕ} (F : TubeFamily k M) (O : Fin M → Finset (Cell k))
    {δ eta lam : ℝ} (hM : 0 < M) (hδ : 0 < δ) (hlam : 0 < lam)
    (hsub : ∀ i, O i ⊆ F.shade i)
    (hupper : ∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam)
    (hmass : eta*lam*M ≤ δ*∑ i, ((O i).card : ℝ)) : eta ≤ 2 := by
  have htotal : δ*∑ i, ((O i).card : ℝ) ≤ 2*lam*M := by
    rw [mul_sum]
    have hpoint (i : Fin M) : δ*((O i).card : ℝ) ≤ 2*lam :=
      (mul_le_mul_of_nonneg_left (by exact_mod_cast card_le_card (hsub i)) hδ.le).trans (hupper i)
    exact (sum_le_sum (fun i _ => hpoint i)).trans_eq (by simp [mul_comm])
  have hpos : 0 < lam*(M : ℝ) := mul_pos hlam (by exact_mod_cast hM)
  apply (mul_le_mul_iff_left₀ hpos).mp
  nlinarith [hmass.trans htotal]

/-- A direct estimate for the original actual union after a retained-incidence
output. All recovered subsets and marking choices are constructed internally. -/
theorem retained_output_hairbrush {k M : ℕ} (F : TubeFamily (k+2) M)
    (O : Fin M → Finset (Cell (k+2)))
    {δ width lam eta B alpha beta K tau m A : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (heta : 0 < eta) (hB : 1 ≤ B) (ha : 0 < alpha) (hK : 1 ≤ K) (hb : 0 < beta)
    (htau : 0 < tau) (htau1 : tau ≤ 1) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hadm : F.Admissible width δ) (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hsub : ∀ i, O i ⊆ F.shade i)
    (hupper : ∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam)
    (hmass : eta*lam*M ≤ δ*∑ i, ((O i).card : ℝ))
    (hbroad : ∀ q ∈ cells O, Broad F (row O univ q) δ beta tau K)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun q => dist (cellCenter δ q) x ≤ r)).card : ℝ) ≤
        B*r^alpha*((F.shade i).card : ℝ)) :
    let W := widthFactor (k+2) width
    let B' := (B*(4/eta))*(1+((k+2:ℕ):ℝ)/2)^alpha*W^alpha
    let K' := (K*(8/eta))*tau^(-beta)
    (concentrationRadius B' alpha*concentrationRadius K' beta)^(k+1)*
        (eta*lam*(M : ℝ)/(4*δ))*((eta*lam/2)/W^(k+2))^((3:ℝ)/2)*δ^((m-1)/2)/
      (allScaleConstant k*Real.sqrt (A*((2*lam)/W^(k+2)))*(hairbrushLog k δ)^((5:ℝ)/2)) ≤
        (F.unionCells.card : ℝ) := by
  intro W B' K'
  let e := selectedIndex O δ eta lam
  let G := selectedFamily F O δ eta lam
  let Z := marked O δ eta lam
  obtain ⟨he,hN,hpoint,hfull,hZ,hhalf,hbroadG,hendsG⟩ :=
    recover F O hδ heta hlam htau (by linarith) (by linarith) hsub hupper hmass hbroad hends
  have hη2 := eta_le_two F O hM hδ hlam hsub hupper hmass
  have hMreal : (0:ℝ) < M := by exact_mod_cast hM
  have hNpos : 0 < (good O δ eta lam).card := by
    exact_mod_cast (lt_of_lt_of_le (show 0 < eta*(M : ℝ)/4 by positivity) hN)
  have hlamrec : 0 ≤ eta*lam/2 := by positivity
  have hlamrec1 : eta*lam/2 ≤ 1 := by nlinarith
  have hlamrecu : eta*lam/2 ≤ 2*lam := by nlinarith
  have hBr : 1 ≤ B*(4/eta) := by
    have hh : 1 ≤ 4/eta := (le_div_iff₀ heta).mpr (by linarith)
    nlinarith
  have hKr : 1 ≤ K*(8/eta) := by
    have hh : 1 ≤ 8/eta := (le_div_iff₀ heta).mpr (by linarith)
    nlinarith
  have hGa : G.Admissible width δ := by
    intro i q hq
    exact hadm _ q (hsub _ hq)
  have hGs : G.Separated δ := by
    intro i j hij
    exact hsep _ _ (fun hh => hij (he hh))
  have hGb : G.CapBound δ m A := by
    obtain ⟨_,_,hc⟩ := DiscreteMeasurable.injective_tube_restriction F G e he (fun _ => rfl)
      hsep (show F.Bounded (∑ i, ‖(F.tube i).base‖) from fun i =>
        single_le_sum (f := fun j => ‖(F.tube j).base‖) (fun j _ => norm_nonneg _) (mem_univ i)) hcap
    exact hc
  have hh := GridHairbrush.finite_broad_hairbrush G Z hNpos hδ hδ1 hlamrec hlamrec1 hlamrecu
    (show 0 < 2*lam by positivity) hBr ha hKr hb htau htau1 hm hA hGa hGs hGb
    (fun i => (hpoint i).2.2.1) (fun i => (hpoint i).2.2.2) hhalf hbroadG hendsG
  have hmarklower : eta*lam*(M : ℝ)/(4*δ) ≤ ∑ i, ((G.shade i ∩ Z).card : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 4*δ)).mpr
    have hh := mul_le_mul_of_nonneg_left hhalf hδ.le
    nlinarith
  have hGU : G.unionCells ⊆ F.unionCells := by
    intro q hq
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
    exact F.shade_subset_union _ (hsub _ hi)
  have hBpos : 0 < B' := by
    have hW := widthFactor_pos (k+2) width
    dsimp [B',W]
    positivity
  have hKpos : 0 < K' := by dsimp [K']; positivity
  have hlog := hairbrushLog_pos (k := k) hδ hδ1
  have hC := allScaleConstant_pos k
  have hrB := concentrationRadius_pos (alpha := alpha) hBpos
  have hrK := concentrationRadius_pos (alpha := beta) hKpos
  have hcoef : 0 ≤ (concentrationRadius B' alpha*concentrationRadius K' beta)^(k+1)*
      ((eta*lam/2)/W^(k+2))^((3:ℝ)/2)*δ^((m-1)/2)/
      (allScaleConstant k*Real.sqrt (A*((2*lam)/W^(k+2)))*(hairbrushLog k δ)^((5:ℝ)/2)) := by
    have hW := widthFactor_pos (k+2) width
    have hApos : 0 < A := by linarith
    positivity
  have hlower := mul_le_mul_of_nonneg_left hmarklower hcoef
  have hfinal := (by convert hlower using 1 <;> first | rfl | ring :
    (concentrationRadius B' alpha*concentrationRadius K' beta)^(k+1)*
        (eta*lam*(M : ℝ)/(4*δ))*((eta*lam/2)/W^(k+2))^((3:ℝ)/2)*δ^((m-1)/2)/
      (allScaleConstant k*Real.sqrt (A*((2*lam)/W^(k+2)))*(hairbrushLog k δ)^((5:ℝ)/2)) ≤
    (concentrationRadius B' alpha*concentrationRadius K' beta)^(k+1)*
        (∑ i, ((G.shade i ∩ Z).card : ℝ))*((eta*lam/2)/W^(k+2))^((3:ℝ)/2)*δ^((m-1)/2)/
      (allScaleConstant k*Real.sqrt (A*((2*lam)/W^(k+2)))*(hairbrushLog k δ)^((5:ℝ)/2)))
  exact (hfinal.trans hh).trans (by exact_mod_cast card_le_card hGU)

end
end KakeyaFormal.RecoveredHairbrush

#print axioms KakeyaFormal.RecoveredHairbrush.eta_le_two
#print axioms KakeyaFormal.RecoveredHairbrush.retained_output_hairbrush
