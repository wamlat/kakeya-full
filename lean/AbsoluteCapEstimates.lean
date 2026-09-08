import LocalizedDirectionThinning
import TwoEndsDiscreteEstimate

/-! Source-faithful absolute-cap inputs and their full inverse-cap consequences.
The actual unchanged-scale direction selection retains entire original shadings.
The fixed cap ceiling precedes all configurations; it is not a full-A estimate
hidden inside an absolute-cap premise. -/
namespace KakeyaFormal
open Finset
open scoped BigOperators
noncomputable section
open Classical

/-- For each fixed cap ceiling Q, the estimate constant may depend on Q.
The conclusion has no inverse-A factor; the actual configuration only needs A<=Q. -/
def AbsoluteDiscreteEstimate (n : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : Normalization, ∀ Q eps : ℝ, 1 ≤ Q → 0 < eps →
    ∃ c : ℝ, 0 < c ∧ ∀ F : ShadedConfiguration n geom m, F.A ≤ Q →
      c*F.δ^(m-d+eps)*F.lam^p*(F.M:ℝ) ≤ (F.family.unionCells.card:ℝ)

/-- The corresponding absolute-cap input with literal original full-shading
ball counts. Q, geometry, B, alpha and eps precede every actual configuration. -/
def AbsoluteTwoEndsDiscreteEstimate (n : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : Normalization, ∀ Q B alpha eps : ℝ, 1 ≤ Q → 1 ≤ B → 0 < alpha → 0 < eps →
    ∃ c : ℝ, 0 < c ∧ ∀ F : ShadedConfiguration n geom m, F.A ≤ Q →
      F.family.FullTwoEnds F.δ B alpha →
      c*F.δ^(m-d+eps)*F.lam^p*(F.M:ℝ) ≤ (F.family.unionCells.card:ℝ)

namespace AbsoluteCapReduction
open LocalizedDirectionThinning

/-- Actual complete-tube selection at the same delta, density and normalization.
Its fixed cap coefficient and population loss depend only on dimension and m. -/
structure Selection {k : ℕ} {geom : Normalization} {m : ℝ}
    (F : ShadedConfiguration (k+1) geom m) where
  selected : ShadedConfiguration (k+1) geom m
  index : Fin selected.M → Fin F.M
  injective : Function.Injective index
  scale_eq : selected.δ=F.δ
  density_eq : selected.lam=F.lam
  cap_eq : selected.A=capConstant k m
  tube_eq : ∀ i, selected.family.tube i=F.family.tube (index i)
  shade_eq : ∀ i, selected.family.shade i=F.family.shade (index i)
  population : (F.M:ℝ)/(retentionConstant k m*F.A) ≤ (selected.M:ℝ)
  union_subset : selected.family.unionCells ⊆ F.family.unionCells

/-- No cap-selection, cardinality or unchanged-shading premise is supplied:
the concrete hierarchy/geometry theorem constructs all of them. -/
theorem construct {k : ℕ} {geom : Normalization} {m : ℝ} (hm : 0 ≤ m)
    (F : ShadedConfiguration (k+1) geom m) : Nonempty (Selection F) := by
  obtain ⟨N,e,he,G,hN,htubes,hshades,_hsep,hcap,hU⟩ :=
    thin_to_scale F.family F.scale_pos F.scale_le_one F.scale_pos F.scale_le_one
      hm F.cap_ge_one F.cap_bound
  have hN' : (F.M:ℝ)/(retentionConstant k m*F.A) ≤ (N:ℝ) := by
    simpa only [max_self,div_self F.scale_pos.ne',Real.one_rpow,mul_one] using hN
  have hadm : G.Admissible geom.width F.δ := by
    intro i z hz
    rw [hshades i] at hz
    simpa only [htubes i] using F.admissible (e i) z hz
  have hsep : G.Separated (geom.separation*F.δ) := by
    intro i j hij
    rw [htubes i,htubes j]
    exact F.separated (e i) (e j) (fun hh => hij (he hh))
  have hbounded : G.Bounded geom.radius := by
    intro i
    simpa only [htubes i] using F.bounded (e i)
  have hcomp : G.Comparable F.δ F.lam := by
    intro i
    simpa only [hshades i] using F.comparable (e i)
  let H : ShadedConfiguration (k+1) geom m :=
    { M:=N, δ:=F.δ, lam:=F.lam, A:=capConstant k m, family:=G,
      scale_pos:=F.scale_pos, scale_le_one:=F.scale_le_one,
      density_pos:=F.density_pos, density_le_one:=F.density_le_one,
      cap_ge_one:=capConstant_ge_one k m, admissible:=hadm, separated:=hsep,
      bounded:=hbounded, cap_bound:=hcap, comparable:=hcomp }
  exact ⟨⟨H,e,he,rfl,rfl,rfl,htubes,hshades,hN',hU⟩⟩

namespace Selection
variable {k : ℕ} {geom : Normalization} {m : ℝ}
  {F : ShadedConfiguration (k+1) geom m}

/-- The same B and alpha survive because every selected row is the entire
original full shading at the same original mesh. -/
theorem full_two_ends (O : Selection F) {B alpha : ℝ}
    (hends : F.family.FullTwoEnds F.δ B alpha) :
    O.selected.family.FullTwoEnds O.selected.δ B alpha := by
  intro i x r hr hr1
  rw [O.scale_eq] at hr ⊢
  rw [O.shade_eq i]
  exact hends (O.index i) x r hr hr1

/-- Apply any actual selected-family bound and return to the original union,
paying exactly one inverse original cap coefficient and a fixed geometric loss. -/
theorem transfer_bound (O : Selection F) {c d p eps : ℝ} (hc : 0 < c)
    (hbound : c*O.selected.δ^(m-d+eps)*O.selected.lam^p*(O.selected.M:ℝ) ≤
      (O.selected.family.unionCells.card:ℝ)) :
    (c/retentionConstant k m)*F.A⁻¹*F.δ^(m-d+eps)*F.lam^p*(F.M:ℝ) ≤
      (F.family.unionCells.card:ℝ) := by
  have hf : 0 ≤ c*F.δ^(m-d+eps)*F.lam^p := by
    have hd := F.scale_pos
    have hl := F.density_pos
    positivity
  have hh := mul_le_mul_of_nonneg_left O.population hf
  have hU : (O.selected.family.unionCells.card:ℝ) ≤ (F.family.unionCells.card:ℝ) :=
    Nat.cast_le.mpr (card_le_card O.union_subset)
  rw [O.scale_eq,O.density_eq] at hbound
  calc
    _ = (c*F.δ^(m-d+eps)*F.lam^p)*((F.M:ℝ)/(retentionConstant k m*F.A)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    _ ≤ _ := hh
    _ ≤ _ := hbound.trans hU

end Selection
end AbsoluteCapReduction

/-- Source absolute-cap estimates suffice for full linear inverse-cap control.
The fixed selected cap coefficient is chosen before the estimate constant and
before every original scale, density, A, tube count and configuration. -/
theorem AbsoluteDiscreteEstimate.to_discrete {k : ℕ} {m d p : ℝ}
    (h : AbsoluteDiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) :
    DiscreteEstimate (k+1) m d p := by
  intro geom eps heps
  obtain ⟨c,hc,hbound⟩ := h geom (LocalizedDirectionThinning.capConstant k m) eps
    (LocalizedDirectionThinning.capConstant_ge_one k m) heps
  refine ⟨c/LocalizedDirectionThinning.retentionConstant k m,
    div_pos hc (LocalizedDirectionThinning.retentionConstant_pos k m),?_⟩
  intro F
  obtain ⟨O⟩ := AbsoluteCapReduction.construct hm F
  exact O.transfer_bound hc (hbound O.selected (by rw [O.cap_eq]))

/-- Absolute-cap full-two-ends estimates likewise suffice, with unchanged
B, alpha, original scale, original full rows and normalization. -/
theorem AbsoluteTwoEndsDiscreteEstimate.to_two_ends {k : ℕ} {m d p : ℝ}
    (h : AbsoluteTwoEndsDiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) :
    TwoEndsDiscreteEstimate (k+1) m d p := by
  intro geom B alpha eps hB halpha heps
  obtain ⟨c,hc,hbound⟩ := h geom (LocalizedDirectionThinning.capConstant k m) B alpha eps
    (LocalizedDirectionThinning.capConstant_ge_one k m) hB halpha heps
  refine ⟨c/LocalizedDirectionThinning.retentionConstant k m,
    div_pos hc (LocalizedDirectionThinning.retentionConstant_pos k m),?_⟩
  intro F hends
  obtain ⟨O⟩ := AbsoluteCapReduction.construct hm F
  exact O.transfer_bound hc (hbound O.selected (by rw [O.cap_eq]) (O.full_two_ends hends))

end
end KakeyaFormal
