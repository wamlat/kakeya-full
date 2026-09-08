import OccupancySelection
import GridCells
import DensityNormalization
import TubeVolume
import Reduction
import ScaleChoice

/-! Actual passage from selected measurable cell incidences to a normalized
ShadedConfiguration, followed by the conditional discrete estimate. Quantitative
class losses remain explicit; no analytic Kakeya estimate is asserted here. -/
namespace KakeyaFormal.DiscreteMeasurable
open MeasureTheory Set Finset
open scoped BigOperators ENNReal
noncomputable section

/-- Restriction to an injectively indexed collection of original tubes preserves
all direction, location and cap conditions, independently of the new shadings. -/
theorem injective_tube_restriction {k M N : ℕ} (F : TubeFamily k M) (G : TubeFamily k N)
    (e : Fin N → Fin M) (he : Function.Injective e) (htube : ∀ i, G.tube i = F.tube (e i))
    {sep R δ m A : ℝ} (hsep : F.Separated sep) (hbounded : F.Bounded R)
    (hcap : F.CapBound δ m A) : G.Separated sep ∧ G.Bounded R ∧ G.CapBound δ m A := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro i j hij
    simpa only [htube] using hsep (e i) (e j) (fun hh => hij (he hh))
  · intro i
    simpa only [htube] using hbounded (e i)
  · intro v hv r hδ hr
    let selected := (univ : Finset (Fin N)).filter (fun i => projectiveDistance (G.tube i).direction v ≤ r)
    have hsub : selected.image e ⊆ (univ : Finset (Fin M)).filter
        (fun i => projectiveDistance (F.tube i).direction v ≤ r) := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
      exact mem_filter.mpr ⟨mem_univ _, by simpa only [htube] using (mem_filter.mp hi).2⟩
    have hcard : (selected.card : ℝ) ≤ ((univ : Finset (Fin M)).filter
        (fun i => projectiveDistance (F.tube i).direction v ≤ r)).card := by
      have hh := Finset.card_le_card hsub
      rw [card_image_of_injective _ he] at hh
      exact_mod_cast hh
    exact hcard.trans (hcap v hv r hδ hr)

/-- A fixed dimension/width constant controls every actual admissible tube's
number of cells by C/δ, uniformly for 0<δ≤1. -/
def gridCountConstant (k : ℕ) (width : ℝ) : ℝ :=
  max 1 (4 * ((2 * Nat.ceil (width + 1) + 3 : ℕ) : ℝ) ^ k)

theorem gridCountConstant_ge_one (k : ℕ) (width : ℝ) :
    1 ≤ gridCountConstant k width := le_max_left _ _

theorem admissible_count_bound {k M : ℕ} (F : TubeFamily k M) {δ width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hadm : F.Admissible width δ) (i : Fin M) :
    ((F.shade i).card : ℝ) ≤ gridCountConstant k width / δ := by
  have hh := GridGeometry.unit_tube_grid_count_real (F.tube i) hδ (F.shade i) (hadm i)
  have hN : (1 : ℝ) ≤ 1 / δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hpow : (0 : ℝ) ≤ ((2 * Nat.ceil (width + 1) + 3 : ℕ) : ℝ) ^ k := by positivity
  have hfixed : 4 * ((2 * Nat.ceil (width + 1) + 3 : ℕ) : ℝ) ^ k ≤ gridCountConstant k width := le_max_right _ _
  have hmul := mul_le_mul_of_nonneg_left (show 1 + 1 / δ ≤ 2 * (1 / δ) by linarith) (show 0 ≤ 2 * ((2 * Nat.ceil (width + 1) + 3 : ℕ) : ℝ) ^ k by positivity)
  have hscale := div_le_div_of_nonneg_right hfixed hδ.le
  exact hh.trans (hmul.trans (by convert hscale using 1; ring))

/-- Normalize actual equal-cardinality shadings while preserving geometric
conditions. The width-dependent constant is obtained from tube geometry. -/
theorem normalize_family {k M K : ℕ} (F : TubeFamily k M) (geom : Normalization)
    {δ m A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    (hadm : F.Admissible geom.width δ) (hsep : F.Separated (geom.separation * δ))
    (hbounded : F.Bounded geom.radius) (hcap : F.CapBound δ m A)
    (hM : 0 < M) (hK : 0 < K) (hcard : ∀ i, (F.shade i).card = K) :
    ∃ H : ShadedConfiguration k geom m,
      H.M = M ∧ H.δ = δ ∧ H.A = A ∧
      δ * (K : ℝ) / (2 * gridCountConstant k geom.width) ≤ H.lam ∧
      H.family.unionCells ⊆ F.unionCells := by
  let i : Fin M := ⟨0,hM⟩
  have hupper : (K : ℝ) ≤ gridCountConstant k geom.width / δ := by
    simpa only [hcard i] using admissible_count_bound F hδ hδ1 hadm i
  obtain ⟨G,lam,hlam,hlam1,hlower,htube,hshade,hcomp,hunion⟩ :=
    DensityNormalization.trim_equal_cardinality F hδ hδ1 (gridCountConstant_ge_one _ _) hK hupper hcard
  have hGadm : G.Admissible geom.width δ := by
    intro j z hz
    simpa only [htube] using hadm j z (hshade j hz)
  obtain ⟨hGsep,hGbounded,hGcap⟩ := injective_tube_restriction F G id Function.injective_id
    (fun _ => congrFun htube _) hsep hbounded hcap
  exact ⟨{
    M := M
    δ := δ
    lam := lam
    A := A
    family := G
    scale_pos := hδ
    scale_le_one := hδ1
    density_pos := hlam
    density_le_one := hlam1
    cap_ge_one := hA
    admissible := hGadm
    separated := hGsep
    bounded := hGbounded
    cap_bound := hGcap
    comparable := hcomp
  },rfl,rfl,rfl,hlower,hunion⟩

open Occupancy OccupancySelection

section Selection
variable {k M Q : ℕ} {δ : ℝ} (hδ : 0 < δ)
variable (labels : Fin Q → Cell k) (hinj : Function.Injective labels)
variable (F : TubeFamily k M) (U : Set (Space k)) (Y : Fin M → Set (Space k))
variable (S : Finset (Fin Q)) {V lo upper : ℝ} {Jocc Jtube : ℕ}
variable (s : CommonIntegerSelection (GridCells.cellSystem hδ labels hinj) U Y S V lo upper Jocc Jtube)

def selectedIndex : Fin s.selected.card → Fin M := fun i => (s.selected.equivFin.symm i).val

def selectedFamily : TubeFamily k s.selected.card where
  tube i := F.tube (selectedIndex hδ labels hinj U Y S s i)
  shade i := (s.shades (selectedIndex hδ labels hinj U Y S s i)).image labels

theorem selectedIndex_injective : Function.Injective (selectedIndex hδ labels hinj U Y S s) :=
  Subtype.val_injective.comp s.selected.equivFin.symm.injective

theorem selectedIndex_mem (i : Fin s.selected.card) :
    selectedIndex hδ labels hinj U Y S s i ∈ s.selected := (s.selected.equivFin.symm i).property

theorem selectedFamily_card (i : Fin s.selected.card) :
    ((selectedFamily hδ labels hinj F U Y S s).shade i).card = s.count := by
  dsimp [selectedFamily]
  rw [card_image_of_injective _ hinj]
  exact s.shades_card _ (selectedIndex_mem hδ labels hinj U Y S s i)

/-- Positive measurable incidence supplies physical touching and thus the actual
center-admissibility condition; it is not replaced by an abstract incidence rule. -/
theorem selectedFamily_admissible {width : ℝ}
    (hphysical : ∀ t, Y t ⊆ (F.tube t).carrier (width * δ)) :
    (selectedFamily hδ labels hinj F U Y S s).Admissible (width + (k : ℝ) / 2) δ := by
  intro i z hz
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hz
  have hpositive := (mem_filter.mp (s.shades_subset _ (selectedIndex_mem hδ labels hinj U Y S s i) hq)).2
  have hne : (Y (selectedIndex hδ labels hinj U Y S s i) ∩ GridCells.gridCell δ (labels q)).Nonempty := by
    by_contra hn
    have hempty := Set.not_nonempty_iff_eq_empty.mp hn
    change 0 < (volume : Measure (Space k)).real
      (Y (selectedIndex hδ labels hinj U Y S s i) ∩ GridCells.gridCell δ (labels q)) at hpositive
    simp only [hempty,measureReal_empty,lt_self_iff_false] at hpositive
  obtain ⟨x,hY,hcell⟩ := hne
  exact GridCells.touching_tube_center _ ⟨x,hcell,hphysical _ hY⟩

/-- Mapping the finite cell indices into genuine Euclidean labels cannot inflate
the measurable-union comparison. Injectivity identifies the cardinalities. -/
theorem selectedFamily_union_volume (hv : 0 ≤ (lo * (2 : ℝ) ^ s.occupancyIndex.val) * V) :
    ((lo * (2 : ℝ) ^ s.occupancyIndex.val) * V) *
      (((selectedFamily hδ labels hinj F U Y S s).unionCells).card : ℝ) ≤
        (volume : Measure (Space k)).real U := by
  have hsub : (selectedFamily hδ labels hinj F U Y S s).unionCells ⊆
      (s.selected.biUnion s.shades).image labels := by
    intro z hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hi
    exact mem_image.mpr ⟨q,mem_biUnion.mpr ⟨_,selectedIndex_mem hδ labels hinj U Y S s i,hq⟩,rfl⟩
  have hcard := Finset.card_le_card hsub
  rw [card_image_of_injective _ hinj] at hcard
  exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hv).trans s.union_volume

/-- The measurable selection creates a genuine normalized configuration with
actual tubes and Euclidean grid cells. No configuration-existence premise is used. -/
theorem selection_configuration (geom : Normalization) {m A width : ℝ}
    (hδ1 : δ ≤ 1) (hA : 1 ≤ A) (hwidth : width + (k : ℝ) / 2 ≤ geom.width)
    (hphysical : ∀ t, Y t ⊆ (F.tube t).carrier (width * δ))
    (hsep : F.Separated (geom.separation * δ)) (hbounded : F.Bounded geom.radius)
    (hcap : F.CapBound δ m A) (hv : 0 ≤ (lo * (2 : ℝ) ^ s.occupancyIndex.val) * V) :
    ∃ H : ShadedConfiguration k geom m,
      H.M = s.selected.card ∧ H.δ = δ ∧ H.A = A ∧
      δ * (s.count : ℝ) / (2 * gridCountConstant k geom.width) ≤ H.lam ∧
      ((lo * (2 : ℝ) ^ s.occupancyIndex.val) * V) * (H.family.unionCells.card : ℝ) ≤
        (volume : Measure (Space k)).real U := by
  let G := selectedFamily hδ labels hinj F U Y S s
  have hGadm : G.Admissible geom.width δ := by
    intro i z hz
    obtain ⟨t,ht,hdt⟩ := selectedFamily_admissible hδ labels hinj F U Y S s hphysical i z hz
    exact ⟨t,ht,hdt.trans (mul_le_mul_of_nonneg_right hwidth hδ.le)⟩
  obtain ⟨hGsep,hGbounded,hGcap⟩ := injective_tube_restriction F G
    (selectedIndex hδ labels hinj U Y S s) (selectedIndex_injective hδ labels hinj U Y S s)
    (fun _ => rfl) hsep hbounded hcap
  obtain ⟨H,hHM,hHδ,hHA,hlam,hunion⟩ := normalize_family G geom hδ hδ1 hA hGadm
    hGsep hGbounded hGcap (Finset.card_pos.mpr s.selected_nonempty) s.count_positive
    (selectedFamily_card hδ labels hinj F U Y S s)
  refine ⟨H,hHM,hHδ,hHA,hlam,?_⟩
  exact (mul_le_mul_of_nonneg_left (by exact_mod_cast Finset.card_le_card hunion) hv).trans
    (selectedFamily_union_volume hδ labels hinj F U Y S s hv)

/-- Apply a proved discrete estimate to the constructed normalized configuration.
The resulting bound is for actual Lebesgue measure of the original measurable
union, with the selected integer count and tube count explicitly visible. -/
theorem selection_measurable_bound (geom : Normalization) {m A width c d p ε : ℝ}
    (hδ1 : δ ≤ 1) (hA : 1 ≤ A) (hwidth : width + (k : ℝ) / 2 ≤ geom.width)
    (hphysical : ∀ t, Y t ⊆ (F.tube t).carrier (width * δ))
    (hsep : F.Separated (geom.separation * δ)) (hbounded : F.Bounded geom.radius)
    (hcap : F.CapBound δ m A) (hv : 0 ≤ (lo * (2 : ℝ) ^ s.occupancyIndex.val) * V)
    (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hestimate : ∀ H : ShadedConfiguration k geom m,
      c * H.A⁻¹ * H.δ ^ (m-d+ε) * H.lam ^ p * H.M ≤ (H.family.unionCells.card : ℝ)) :
    c * A⁻¹ * δ ^ (m-d+ε) *
      (δ * (s.count : ℝ) / (2 * gridCountConstant k geom.width)) ^ p * s.selected.card *
      ((lo * (2 : ℝ) ^ s.occupancyIndex.val) * V) ≤ (volume : Measure (Space k)).real U := by
  obtain ⟨H,hHM,hHδ,hHA,hlam,hvol⟩ := selection_configuration hδ labels hinj F U Y S s geom
    hδ1 hA hwidth hphysical hsep hbounded hcap hv
  have hlower : 0 ≤ δ * (s.count : ℝ) / (2 * gridCountConstant k geom.width) :=
    div_nonneg (mul_nonneg hδ.le (by positivity))
      (mul_nonneg (by norm_num) (le_trans (by norm_num) (gridCountConstant_ge_one _ _)))
  have hpow := Real.rpow_le_rpow hlower hlam hp
  have hcoef : 0 ≤ c * A⁻¹ * δ ^ (m-d+ε) := by positivity
  have hmass := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hcoef)
    (show (0 : ℝ) ≤ s.selected.card by positivity)
  have hbound := hestimate H
  conv_lhs at hbound => rw [hHM,hHδ,hHA]
  have hh := mul_le_mul_of_nonneg_right (hmass.trans hbound) hv
  nlinarith

include s in
/-- Eliminate occupancy from the bound using p≥1 and substitute the proved
integer-count and selected-tube lower bounds. Only explicit class-count losses
remain; this is the quantitative finite heart of Section 8.1. -/
theorem selection_measure_class_losses (geom : Normalization) {m A width c d p ε base : ℝ}
    (hδ1 : δ ≤ 1) (hA : 1 ≤ A) (hwidth : width + (k : ℝ) / 2 ≤ geom.width)
    (hphysical : ∀ t, Y t ⊆ (F.tube t).carrier (width * δ))
    (hsep : F.Separated (geom.separation * δ)) (hbounded : F.Bounded geom.radius)
    (hcap : F.CapBound δ m A) (hV : 0 < V) (hlo : 0 < lo) (hM : 0 < M)
    (hbase : 0 < base) (hupper : 0 < upper)
    (hvol : ∀ q, (volume : Measure (Space k)).real ((GridCells.cellSystem hδ labels hinj).cell q) = V)
    (hret : (M : ℝ) * base / 2 ≤ incidenceMass (GridCells.cellSystem hδ labels hinj) Y S)
    (hc : 0 ≤ c) (hp : 1 ≤ p)
    (hestimate : ∀ H : ShadedConfiguration k geom m,
      c * H.A⁻¹ * H.δ ^ (m-d+ε) * H.lam ^ p * H.M ≤ (H.family.unionCells.card : ℝ)) :
    c * A⁻¹ * δ ^ (m-d+ε) *
      (δ * base / (16 * gridCountConstant k geom.width * (Jocc + 1 : ℕ) * V)) ^ p *
      ((M : ℝ) * base / (4 * (Jocc + 1 : ℕ) * (Jtube + 1 : ℕ) * upper)) * V ≤
        (volume : Measure (Space k)).real U := by
  let w := lo * (2 : ℝ) ^ s.occupancyIndex.val
  let v := w * V
  let B : ℝ := (Jocc + 1 : ℕ)
  let Bt : ℝ := (Jtube + 1 : ℕ)
  let C := gridCountConstant k geom.width
  let b := δ * base / (16 * C * B * V)
  let L := δ * (s.count : ℝ) / (2 * C)
  have hw : 0 < w := mul_pos hlo (pow_pos (by norm_num) _)
  have hv : 0 < v := mul_pos hw hV
  have hB : 0 < B := by dsimp [B]; positivity
  have hBt : 0 < Bt := by dsimp [Bt]; positivity
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (gridCountConstant_ge_one _ _)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hw1 : w ≤ 1 := by
    obtain ⟨t,ht⟩ := s.selected_nonempty
    have hcard : 0 < (s.shades t).card := by rw [s.shades_card t ht]; exact s.count_positive
    obtain ⟨q,hq⟩ := Finset.card_pos.mp hcard
    have hqR := (mem_filter.mp (s.shades_subset t ht hq)).1
    have hcell := (GridCells.cellSystem hδ labels hinj).cellMass_le_volume U q
    rw [hvol q] at hcell
    have hh := (s.occupancy_range q hqR).1
    change w * V ≤ _ at hh
    nlinarith
  have hK : base / (8 * B * v) ≤ (s.count : ℝ) := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * v)).mp s.count_lower
    have hh' := (div_le_iff₀ (by simpa only [Fintype.card_fin] using mul_pos (by norm_num : (0 : ℝ) < 2) hMr)).mp hh
    have hh'' := (div_le_iff₀ hB).mp hh'
    simp only [Fintype.card_fin] at hh''
    have hcanc : (M : ℝ) * (base / 2) ≤ (M : ℝ) * (4 * B * v * (s.count : ℝ)) := by
      nlinarith
    have hk := le_of_mul_le_mul_left hcanc hMr
    apply (div_le_iff₀ (by positivity : 0 < 8 * B * v)).mpr
    nlinarith
  have hN : (M : ℝ) * base / (4 * B * Bt * upper) ≤ (s.selected.card : ℝ) := by
    have hh := s.tube_count_lower
    change incidenceMass _ _ _ ≤ 2 * B * Bt * upper * (s.selected.card : ℝ) at hh
    apply (div_le_iff₀ (by positivity : 0 < 4 * B * Bt * upper)).mpr
    nlinarith
  have hL : b / w ≤ L := by
    have hh := mul_le_mul_of_nonneg_left hK (div_nonneg hδ.le (by positivity : 0 ≤ 2 * C))
    have hleft : b / w = (δ / (2 * C)) * (base / (8 * B * v)) := by
      dsimp [b,v]
      ring
    have hright : L = (δ / (2 * C)) * (s.count : ℝ) := by dsimp [L]; ring
    rw [hleft,hright]
    exact hh
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hg := KakeyaAudit.Reduction.occupancy_gain hw hw1 hb hp
  have hlpow := Real.rpow_le_rpow (div_nonneg hb hw.le) hL (by linarith : 0 ≤ p)
  have hgain : b ^ p ≤ w * L ^ p := hg.trans (mul_le_mul_of_nonneg_left hlpow hw.le)
  let coef := c * A⁻¹ * δ ^ (m-d+ε)
  have hcoef : 0 ≤ coef := by dsimp [coef]; positivity
  have hbound := selection_measurable_bound hδ labels hinj F U Y S s geom hδ1 hA hwidth
    hphysical hsep hbounded hcap hv.le hc (by linarith : 0 ≤ p) hestimate
  change coef * L ^ p * s.selected.card * v ≤ _ at hbound
  have hfirst := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hN (mul_nonneg hcoef (Real.rpow_nonneg hb p))) hV.le
  have hsecond := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgain hcoef)
      (show (0 : ℝ) ≤ s.selected.card by positivity)) hV.le
  have hlast : coef * (w * L ^ p) * s.selected.card * V = coef * L ^ p * s.selected.card * v := by
    dsimp [v]
    ring
  rw [hlast] at hsecond
  exact hfirst.trans (hsecond.trans hbound)

end Selection
/-- The discrete constant is chosen before the scale, density, cap coefficient,
tube family, measurable shadings and actual selected classes. This preserves the
uniform quantifier order in the measurable conversion. -/
theorem discrete_estimate_measurable (k : ℕ) (m d p : ℝ)
    (hdiscrete : DiscreteEstimate k m d p) (hp : 0 ≤ p)
    (geom : Normalization) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {M Q : ℕ} {δ : ℝ} (hδ : 0 < δ) (labels : Fin Q → Cell k)
        (hinj : Function.Injective labels) (F : TubeFamily k M)
        (U : Set (Space k)) (Y : Fin M → Set (Space k)) (S : Finset (Fin Q))
        {V lo upper : ℝ} {Jocc Jtube : ℕ}
        (s : CommonIntegerSelection (GridCells.cellSystem hδ labels hinj) U Y S V lo upper Jocc Jtube)
        {A width : ℝ}, δ ≤ 1 → 1 ≤ A → width + (k : ℝ) / 2 ≤ geom.width →
        (∀ t, Y t ⊆ (F.tube t).carrier (width * δ)) →
        F.Separated (geom.separation * δ) → F.Bounded geom.radius → F.CapBound δ m A →
        0 ≤ (lo * (2 : ℝ) ^ s.occupancyIndex.val) * V →
        c * A⁻¹ * δ ^ (m-d+ε) *
          (δ * (s.count : ℝ) / (2 * gridCountConstant k geom.width)) ^ p * s.selected.card *
          ((lo * (2 : ℝ) ^ s.occupancyIndex.val) * V) ≤ (volume : Measure (Space k)).real U := by
  obtain ⟨c,hc,hestimate⟩ := hdiscrete geom ε hε
  refine ⟨c,hc,?_⟩
  intro M Q δ hδ labels hinj F U Y S V lo upper Jocc Jtube s A width hδ1 hA hwidth hphysical hsep hbounded hcap hv
  exact selection_measurable_bound hδ labels hinj F U Y S s geom hδ1 hA hwidth hphysical
    hsep hbounded hcap hv hc.le hp hestimate

/-- Class coverage budgets with explicit logarithmic bounds. In particular,
finite existence is not silently promoted to a uniform logarithmic loss. -/
theorem logarithmic_class_budgets {lo base upper : ℝ}
    (hlo : 0 < lo) (hlo1 : lo ≤ 1) (hbase : 0 < base) (hupper : base ≤ upper) :
    ∃ Jocc Jtube : ℕ,
      1 ≤ lo * (2 : ℝ) ^ Jocc ∧
      upper ≤ (base / (4 * (Jocc + 1 : ℕ))) * (2 : ℝ) ^ Jtube ∧
      (Jocc : ℝ) + 1 ≤ Real.log (1 / lo) / Real.log 2 + 2 ∧
      (Jtube : ℝ) + 1 ≤ Real.log (upper / (base / (4 * (Jocc + 1 : ℕ)))) / Real.log 2 + 2 := by
  obtain ⟨Jocc,hocc,hocclog⟩ := ScaleChoice.dyadic_class_budget hlo hlo1
  have hlower : 0 < base / (4 * (Jocc + 1 : ℕ)) := div_pos hbase (by positivity)
  have hsmall : base / (4 * (Jocc + 1 : ℕ)) ≤ upper := by
    apply le_trans ?_ hupper
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (Jocc + 1 : ℕ))).mpr
    have hB : (1 : ℝ) ≤ (Jocc + 1 : ℕ) := by exact_mod_cast (show 1 ≤ Jocc + 1 by omega)
    nlinarith
  obtain ⟨Jtube,htube,htubelog⟩ := ScaleChoice.dyadic_class_budget hlower hsmall
  exact ⟨Jocc,Jtube,by simpa only [mul_comm] using hocc,
    by simpa only [mul_comm] using htube,hocclog,htubelog⟩

/-- The positive-cell count needed for the low-occupancy cutoff follows from
actual physical tube containment, including for an arbitrary injective finite
list of grid labels. No cell-count hypothesis is retained. -/
theorem positive_incidence_count {k Q : ℕ} (T : UnitTube k) {δ width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (labels : Fin Q → Cell k)
    (hinj : Function.Injective labels) {Y : Set (Space k)}
    (hphysical : Y ⊆ T.carrier (width * δ)) :
    (((GridCells.cellSystem hδ labels hinj).positiveCells Y univ).card : ℝ) ≤
      gridCountConstant k (width + (k : ℝ) / 2) / δ := by
  classical
  let cells := (GridCells.cellSystem hδ labels hinj).positiveCells Y univ
  let F : TubeFamily k 1 := ⟨fun _ => T, fun _ => cells.image labels⟩
  have hadm : F.Admissible (width + (k : ℝ) / 2) δ := by
    intro i z hz
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hz
    have hpos : 0 < (volume : Measure (Space k)).real (Y ∩ GridCells.gridCell δ (labels q)) :=
      (mem_filter.mp hq).2
    have hne : (Y ∩ GridCells.gridCell δ (labels q)).Nonempty := by
      by_contra hn
      simp only [Set.not_nonempty_iff_eq_empty.mp hn,measureReal_empty,lt_self_iff_false] at hpos
    obtain ⟨x,hY,hcell⟩ := hne
    exact GridCells.touching_tube_center T ⟨x,hcell,hphysical hY⟩
  have hh := admissible_count_bound F hδ hδ1 hadm 0
  simpa only [F,card_image_of_injective _ hinj] using hh

/-- Original measurable shadings produce actual occupancy/tube classes with
logarithmically bounded class budgets and a genuine common integer selection.
Geometry supplies the positive-incidence count and the grid supplies δ^k volume. -/
theorem actual_occupancy_selection {k M Q : ℕ} {δ width lo base upper : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (labels : Fin Q → Cell k)
    (hinj : Function.Injective labels) (F : TubeFamily k M)
    (U : Set (Space k)) (Y : Fin M → Set (Space k))
    (hU : MeasurableSet U) (hcover : U ⊆ (GridCells.cellSystem hδ labels hinj).covered)
    (hY : ∀ t, MeasurableSet (Y t)) (hYU : ∀ t, Y t ⊆ U)
    (hphysical : ∀ t, Y t ⊆ (F.tube t).carrier (width * δ))
    (hM : 0 < M) (hlo : 0 < lo) (hlo1 : lo ≤ 1) (hbase : 0 < base)
    (hmass : ∀ t, base ≤ (volume : Measure (Space k)).real (Y t))
    (hupper : ∀ t, (volume : Measure (Space k)).real (Y t) ≤ upper)
    (hcutoff : lo * δ ^ k * (gridCountConstant k (width + (k : ℝ) / 2) / δ) ≤ base / 2) :
    ∃ Jocc Jtube : ℕ,
      (Jocc : ℝ) + 1 ≤ Real.log (1 / lo) / Real.log 2 + 2 ∧
      (Jtube : ℝ) + 1 ≤ Real.log (upper / (base / (4 * (Jocc + 1 : ℕ)))) / Real.log 2 + 2 ∧
      (∀ t, base / 2 ≤ restrictedMass (GridCells.cellSystem hδ labels hinj) Y
        (highOccupancyCells (GridCells.cellSystem hδ labels hinj) U lo (δ ^ k)) t) ∧
      (M : ℝ) * base / 2 ≤ incidenceMass (GridCells.cellSystem hδ labels hinj) Y
        (highOccupancyCells (GridCells.cellSystem hδ labels hinj) U lo (δ ^ k)) ∧
      Nonempty (CommonIntegerSelection (GridCells.cellSystem hδ labels hinj) U Y
        (highOccupancyCells (GridCells.cellSystem hδ labels hinj) U lo (δ ^ k))
          (δ ^ k) lo upper Jocc Jtube) := by
  have hbaseupper : base ≤ upper := (hmass ⟨0,hM⟩).trans (hupper ⟨0,hM⟩)
  obtain ⟨Jocc,Jtube,htop,hclasses,hocclog,htubelog⟩ := logarithmic_class_budgets hlo hlo1 hbase hbaseupper
  have hvol (q : Fin Q) : (volume : Measure (Space k)).real ((GridCells.cellSystem hδ labels hinj).cell q) = δ ^ k :=
    GridCells.real_volume_gridCell hδ.le (labels q)
  have hcount (t : Fin M) := positive_incidence_count (F.tube t) hδ hδ1 labels hinj (hphysical t)
  obtain ⟨hret,htotal,hselection⟩ := high_occupancy_integer_selection
    (GridCells.cellSystem hδ labels hinj) U hU hcover Y hY hYU (pow_pos hδ k) hlo hbase hvol
    (by simpa only [Fintype.card_fin] using hM) hmass hupper hcount hcutoff Jocc Jtube htop hclasses
  exact ⟨Jocc,Jtube,hocclog,htubelog,hret,by simpa only [Fintype.card_fin] using htotal,hselection⟩

/-- The scale/density comparison used by the one-tube branch, in the precise
form needed for a volume lower bound. -/
theorem small_density_scale {δ lam d p k : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hsmall : lam ≤ δ)
    (hp : 1 ≤ p) (hdp : d ≤ p) :
    δ ^ (k-d) * lam ^ p ≤ lam * δ ^ (k-1) := by
  have hh := KakeyaAudit.Reduction.small_density_one_tube hδ hδ1 hlam hsmall hp hdp
  have hid : (δ ^ (k-d) * lam ^ p) * (δ ^ (d-1) * lam ^ (1-p)) = lam * δ ^ (k-1) := by
    calc
      _ = (δ ^ (k-d) * δ ^ (d-1)) * (lam ^ p * lam ^ (1-p)) := by ring
      _ = _ := by
        rw [← Real.rpow_add hδ, ← Real.rpow_add hlam]
        have he1 : k-d+(d-1) = k-1 := by ring
        have he2 : p+(1-p) = 1 := by ring
        rw [he1,he2,Real.rpow_one,mul_comm]
  have hm := mul_le_mul_of_nonneg_left hh
    (mul_nonneg (Real.rpow_nonneg hδ.le (k-d)) (Real.rpow_nonneg hlam.le p))
  simpa only [mul_one,hid] using hm

/-- A total cap-count bound and one actual measurable shading close the
small-density branch. The statement keeps the cap and volume constants explicit. -/
theorem small_density_measurable {k M : ℕ} {δ lam m d p A C c₀ : ℝ}
    {U Y : Set (Space k)} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hlam : 0 < lam) (hsmall : lam ≤ δ) (hp : 1 ≤ p) (hdp : d ≤ p)
    (hA : 0 < A) (hC : 0 < C) (hc₀ : 0 ≤ c₀)
    (hcap : (M : ℝ) ≤ C * A * δ ^ (-m))
    (hYU : Y ⊆ U) (hfinite : (volume : Measure (Space k)) U ≠ ∞)
    (hmass : c₀ * lam * δ ^ ((k : ℝ)-1) ≤ (volume : Measure (Space k)).real Y) :
    (c₀ / C) * A⁻¹ * δ ^ ((k : ℝ)+m-d) * lam ^ p * M ≤
      (volume : Measure (Space k)).real U := by
  have hscale := small_density_scale hδ hδ1 hlam hsmall hp hdp (k := (k : ℝ))
  have hcoef : 0 ≤ (c₀ / C) * A⁻¹ * δ ^ ((k : ℝ)+m-d) * lam ^ p := by positivity
  have hm := mul_le_mul_of_nonneg_left hcap hcoef
  have hid : (c₀ / C) * A⁻¹ * δ ^ ((k : ℝ)+m-d) * lam ^ p * (C*A*δ^(-m)) =
      c₀ * (δ ^ ((k : ℝ)-d) * lam ^ p) := by
    have hpows : δ ^ ((k : ℝ)+m-d) * δ ^ (-m) = δ ^ ((k : ℝ)-d) := by
      rw [← Real.rpow_add hδ]
      congr 1
      ring
    calc
      _ = c₀ * ((δ ^ ((k : ℝ)+m-d) * δ ^ (-m)) * lam ^ p) := by field_simp
      _ = _ := by rw [hpows]
  rw [hid] at hm
  have hbound := (hm.trans (mul_le_mul_of_nonneg_left hscale hc₀)).trans
    (by simpa only [mul_assoc] using hmass)
  exact hbound.trans (measureReal_mono hYU hfinite)

/-- The one-tube input itself follows from the volume of an actual UnitTube,
with its proved dimensional constant. Only the shading-density and total-count
hypotheses remain, exactly as in the small-density branch of Section 8.1. -/
theorem small_density_actual_tube {k M : ℕ} (T : UnitTube k)
    {δ lam m d p A C : ℝ} {U Y : Set (Space k)}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hsmall : lam ≤ δ)
    (hp : 1 ≤ p) (hdp : d ≤ p) (hA : 0 < A) (hC : 0 < C)
    (hcap : (M : ℝ) ≤ C * A * δ ^ (-m)) (hYU : Y ⊆ U)
    (hfinite : (volume : Measure (Space k)) U ≠ ∞)
    (hshading : lam * (volume : Measure (Space k)).real (T.carrier δ) ≤
      (volume : Measure (Space k)).real Y) :
    ((TubeVolume.unitBallVolume k / (2 : ℝ) ^ (k+1)) / C) * A⁻¹ *
      δ ^ ((k : ℝ)+m-d) * lam ^ p * M ≤ (volume : Measure (Space k)).real U := by
  have hlower := TubeVolume.carrier_volume_lower T hδ
  have hpow : δ ^ k / δ = δ ^ ((k : ℝ)-1) := by
    rw [Real.rpow_sub hδ, Real.rpow_natCast, Real.rpow_one]
  have hmass : (TubeVolume.unitBallVolume k / (2 : ℝ) ^ (k+1)) * lam * δ ^ ((k : ℝ)-1) ≤
      (volume : Measure (Space k)).real Y := by
    apply le_trans ?_ hshading
    have hh := mul_le_mul_of_nonneg_left hlower hlam.le
    calc
      _ = lam * ((TubeVolume.unitBallVolume k / (2 : ℝ) ^ (k+1)) * δ ^ k / δ) := by
        rw [← hpow]
        ring
      _ ≤ _ := hh
  exact small_density_measurable hδ hδ1 hlam hsmall hp hdp hA hC
    (by positivity [TubeVolume.unitBallVolume_pos k]) hcap hYU hfinite hmass

end
end KakeyaFormal.DiscreteMeasurable

-- Kernel dependency audit.
#print axioms KakeyaFormal.DiscreteMeasurable.injective_tube_restriction
#print axioms KakeyaFormal.DiscreteMeasurable.gridCountConstant_ge_one
#print axioms KakeyaFormal.DiscreteMeasurable.admissible_count_bound
#print axioms KakeyaFormal.DiscreteMeasurable.normalize_family
#print axioms KakeyaFormal.DiscreteMeasurable.selectedIndex_injective
#print axioms KakeyaFormal.DiscreteMeasurable.selectedIndex_mem
#print axioms KakeyaFormal.DiscreteMeasurable.selectedFamily_card
#print axioms KakeyaFormal.DiscreteMeasurable.selectedFamily_admissible
#print axioms KakeyaFormal.DiscreteMeasurable.selectedFamily_union_volume
#print axioms KakeyaFormal.DiscreteMeasurable.selection_configuration
#print axioms KakeyaFormal.DiscreteMeasurable.selection_measurable_bound
#print axioms KakeyaFormal.DiscreteMeasurable.selection_measure_class_losses
#print axioms KakeyaFormal.DiscreteMeasurable.discrete_estimate_measurable
#print axioms KakeyaFormal.DiscreteMeasurable.logarithmic_class_budgets
#print axioms KakeyaFormal.DiscreteMeasurable.positive_incidence_count
#print axioms KakeyaFormal.DiscreteMeasurable.actual_occupancy_selection
#print axioms KakeyaFormal.DiscreteMeasurable.small_density_scale
#print axioms KakeyaFormal.DiscreteMeasurable.small_density_measurable
#print axioms KakeyaFormal.DiscreteMeasurable.small_density_actual_tube
