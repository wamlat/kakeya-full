import AnisotropicJointRecovery
import AnisotropicConfiguration
import SeparationColoring

/-! Geometry of the actual marked-chosen unit segments and their measured
index restrictions. A genuine common parallel-box hypothesis is explicit.
Coloring is a full finite partition; no broadness preservation by color thinning
is asserted. -/
namespace KakeyaFormal.AnisotropicJointGeometry
open Finset MeasureTheory AnisotropicShading AnisotropicRescaling SpatialAngular
open AnisotropicJointShading MeasurableMarkedSelection SeparationColoring ProjectiveGeometry
open scoped ENNReal BigOperators
noncomputable section
open Classical

def separationFactor (angular : ℝ) : ℝ := 1/(4*(1+2*angular)^2)
def baseBound (angular R W : ℝ) : ℝ := 1+|R|+|W|+(segmentCount angular:ℝ)
def capFactor (k : ℕ) (angular m : ℝ) : ℝ := packingConstant k*(8*(1+2*angular)^2)^m

theorem separationFactor_pos {angular : ℝ} (ha : 0 ≤ angular) : 0 < separationFactor angular := by
  unfold separationFactor
  positivity

theorem baseBound_pos (angular R W : ℝ) : 0 < baseBound angular R W := by unfold baseBound; positivity

theorem capFactor_ge_one (k : ℕ) {angular m : ℝ} (ha : 0 ≤ angular) (hm : 0 ≤ m) :
    1 ≤ capFactor k angular m := by
  have hb : (1:ℝ) ≤ 8*(1+2*angular)^2 := by nlinarith [sq_nonneg angular]
  have hp := Real.one_le_rpow hb hm
  have hP := packingConstant_ge_one k
  unfold capFactor
  nlinarith

/-- Marked-best unit-segment axes have the same proved transformed directions. -/
theorem joint_separated {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (G : Fin M → Set (Space (k+1))) {tau angular δ width : ℝ}
    (hu : ‖u‖=1) (htau : 0 < tau) (htau1 : tau ≤ 1) (ha : 0 ≤ angular)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hsep : F.Separated δ) (q : Cell k) :
    (AnisotropicJointShading.family F u htau.ne' q angular width δ G).Separated
      (separationFactor angular*(δ/tau)) := by
  have hh := AnisotropicCap.family_separated F u hu htau htau1 ha hlocal hsep q
    (fun i => bestSegment u htau.ne' q (F.tube i) angular width δ (G i)) (fun _ => ∅)
  have hid : separationFactor angular*(δ/tau) = δ/(4*(1+2*angular)^2*tau) := by
    simp only [separationFactor,div_eq_mul_inv,mul_inv_rev]
    ring
  rw [hid]
  exact hh

/-- The actual common marked segment choice retains the transformed real-cap
bound, uniformly in scale, population, and each individual shading. -/
theorem joint_cap_bound {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (G : Fin M → Set (Space (k+1))) {tau angular δ width m A : ℝ}
    (hu : ‖u‖=1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcap : F.CapBound δ m A) (q : Cell k) :
    (AnisotropicJointShading.family F u (hδ.trans_le hδtau).ne' q angular width δ G).CapBound
      (δ/tau) m (capFactor k angular m*A) := by
  have hh := AnisotropicCap.family_cap_bound F u hu hδ hδtau htau1 ha hm hA hlocal hcap q
    (fun i => bestSegment u (hδ.trans_le hδtau).ne' q (F.tube i) angular width δ (G i)) (fun _ => ∅)
  have hid : capFactor k angular m*A = packingConstant k*A*(8*(1+2*angular)^2)^m := by
    unfold capFactor
    ring
  rw [hid]
  exact hh

/-- A genuine common spatial box gives a fixed transformed base bound.
This hypothesis concerns the actual original base, not an angular cap alone. -/
theorem joint_base_bound {k : ℕ} (u : Space (k+1)) {tau R W : ℝ} (htau : 0 < tau)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ) (G : Set (Space (k+1)))
    (hbox : T.base ∈ parallelBox u tau q R W) :
    ‖(transformedTube u htau.ne' q T (bestSegment u htau.ne' q T angular width δ G)).base‖ ≤
      baseBound angular R W :=
  AnisotropicConfiguration.selected_base_bound u htau q T angular width δ G hbox

/-- The actual measured restriction inherits direction geometry. Its bounded
base conclusion requires every retained original index to lie in the SAME
explicit spatial box. No global angular-group box assumption is inferred. -/
theorem measured_geometry {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (G : Fin M → Set (Space (k+1))) (T : Finset (Fin M)) {tau angular δ width m A R W : ℝ}
    (hu : ‖u‖=1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A) (q : Cell k)
    (hbox : ∀ i ∈ T, (F.tube i).base ∈ parallelBox u tau q R W) :
    let J := AnisotropicJointShading.family F u (hδ.trans_le hδtau).ne' q angular width δ G
    (MeasurableMarkedSelection.family J T).Separated (separationFactor angular*(δ/tau)) ∧
    (MeasurableMarkedSelection.family J T).CapBound (δ/tau) m (capFactor k angular m*A) ∧
    (MeasurableMarkedSelection.family J T).Bounded (baseBound angular R W) := by
  intro J
  refine ⟨MeasurableMarkedSelection.family_separated J T
    (joint_separated F u G hu (hδ.trans_le hδtau) htau1 ha hlocal hsep q),
    MeasurableMarkedSelection.family_cap_bound J T
      (joint_cap_bound F u G hu hδ hδtau htau1 ha hm hA hlocal hcap q),?_⟩
  intro i
  exact joint_base_bound u (hδ.trans_le hδtau) q (F.tube _) angular width δ (G _)
    (hbox _ (MeasurableMarkedSelection.index_mem T i))

/-- Full fixed-palette normalization of the actual measured family. Every
original retained tube weight is counted exactly once across its color classes. -/
theorem measured_coloring {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (G : Fin M → Set (Space (k+1))) (T : Finset (Fin M)) {tau angular δ width m A R W : ℝ}
    (hu : ‖u‖=1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A) (q : Cell k)
    (hbox : ∀ i ∈ T, (F.tube i).base ∈ parallelBox u tau q R W) :
    let J := AnisotropicJointShading.family F u (hδ.trans_le hδtau).ne' q angular width δ G
    let H := MeasurableMarkedSelection.family J T
    ∃ color : Fin T.card → Fin (paletteSize k (separationFactor angular)),
      (∀ c, (classFamily H color c).Separated (δ/tau) ∧
        (classFamily H color c).CapBound (δ/tau) m (capFactor k angular m*A) ∧
        (classFamily H color c).Bounded (baseBound angular R W)) ∧
      (∀ weight : Fin T.card → ℝ, (∑ c, ∑ i, weight (classIndex color c i)) = ∑ i, weight i) := by
  intro J H
  obtain ⟨hs,hc,hb⟩ := measured_geometry F u G T hu hδ hδtau htau1 ha hm hA hlocal hsep hcap q hbox
  obtain ⟨color,hcolor,hsum,_⟩ := full_separation_partition H (div_pos hδ (hδ.trans_le hδtau))
    (separationFactor_pos ha) hs
  exact ⟨color,fun c => ⟨hcolor c,classFamily_cap_bound H color hc c,fun i => hb (classIndex color c i)⟩,hsum⟩

/-- Keep both full and marked sets on a single common color. -/
def onColor {X : Type*} {M P : ℕ} (color : Fin M → Fin P) (c : Fin P)
    (Y : Fin M → Set X) : Fin M → Set X := fun i => if color i=c then Y i else ∅

theorem onColor_subset {X : Type*} {M P : ℕ} (color : Fin M → Fin P) (c : Fin P)
    (Y : Fin M → Set X) (i : Fin M) : onColor color c Y i ⊆ Y i := by
  by_cases hi : color i=c <;> simp [onColor,hi]

theorem onColor_nested {X : Type*} {M P : ℕ} (color : Fin M → Fin P) (c : Fin P)
    (Full G : Fin M → Set X) (hsub : ∀ i, G i ⊆ Full i) :
    ∀ i, onColor color c G i ⊆ onColor color c Full i := by
  intro i
  by_cases hi : color i=c <;> simp [onColor,hi,hsub]

theorem onColor_measurable {X : Type*} [MeasurableSpace X] {M P : ℕ}
    (color : Fin M → Fin P) (c : Fin P) (Y : Fin M → Set X)
    (hY : ∀ i, MeasurableSet (Y i)) : ∀ i, MeasurableSet (onColor color c Y i) := by
  intro i
  by_cases hi : color i=c <;> simp [onColor,hi,hY]

/-- Actual color-restricted mass is the finite fiber sum. -/
theorem onColor_mass {X : Type*} [MeasurableSpace X] (ν : Measure X) {M P : ℕ}
    (color : Fin M → Fin P) (c : Fin P) (Y : Fin M → Set X) :
    (∑ i, ν.real (onColor color c Y i)) = ∑ i ∈ colorClass color c, ν.real (Y i) := by
  simp [onColor,colorClass,sum_filter,apply_ite]

/-- An actual marked-mass maximizing color is constructed. This finite choice
must precede marked broadness recovery, not be mistaken for preserving it. -/
theorem marked_color {X : Type*} [MeasurableSpace X] (ν : Measure X) {M P : ℕ}
    (hP : 0 < P) (color : Fin M → Fin P) (G : Fin M → Set X) :
    ∃ c : Fin P, (∑ i, ν.real (G i))/(P:ℝ) ≤ ∑ i, ν.real (onColor color c G i) := by
  obtain ⟨c,hc⟩ := OccupancySelection.weighted_class_selection univ (fun i => ν.real (G i)) hP color
  refine ⟨c,?_⟩
  rw [onColor_mass]
  exact hc

/-- Positive selected full mass forces the one selected color. Later measured
full-density selection therefore proves monochromaticity rather than assuming it. -/
theorem positive_onColor {X : Type*} [MeasurableSpace X] (ν : Measure X) {M P : ℕ}
    (color : Fin M → Fin P) (c : Fin P) (Y : Fin M → Set X) (i : Fin M)
    (hpos : 0 < ν.real (onColor color c Y i)) : color i=c := by
  by_contra hi
  simp [onColor,hi] at hpos

/-- Actual positive full-mass restriction of a color-normalized family has the
required exact target separation, with no extra loss or duplicated indices. -/
theorem measured_onColor_separated {k M P : ℕ} (F : TubeFamily k M)
    (color : Fin M → Fin P) (c : Fin P) (Y : Fin M → Set (Space k))
    (ν : Measure (Space k)) (T : Finset (Fin M)) {δ : ℝ}
    (hcolor : ∀ i j, color i=color j → i≠j → δ ≤ projectiveDistance (F.tube i).direction (F.tube j).direction)
    (hpositive : ∀ i ∈ T, 0 < ν.real (onColor color c Y i)) :
    (MeasurableMarkedSelection.family F T).Separated δ := by
  intro i j hij
  apply hcolor _ _
  · exact (positive_onColor ν color c Y _ (hpositive _ (MeasurableMarkedSelection.index_mem T i))).trans
      (positive_onColor ν color c Y _ (hpositive _ (MeasurableMarkedSelection.index_mem T j))).symm
  · exact fun he => hij (MeasurableMarkedSelection.index_injective T he)

/-- Actual single-color preparation for measured marked recovery. A color is
chosen by the marked mass of the actual marked-best segments. Both full and
marked outputs are masked by that same color; every subsequent positive full
mass class is then exactly delta/tau-separated. The unchanged ALL-reference
marks can be used in MeasurableMarkedSelection.select/marks_broad afterward. -/
theorem joint_colored_selection {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    (Full G : Fin M → Set (Space (k+1))) {tau angular δ width m A R W : ℝ}
    (hu : ‖u‖=1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A) (q : Cell k)
    (hbox : ∀ i, (F.tube i).base ∈ parallelBox u tau q R W)
    (hsub : ∀ i, G i ⊆ Full i) :
    let htau := hδ.trans_le hδtau
    let J := AnisotropicJointShading.family F u htau.ne' q angular width δ G
    let Y := fun i => AnisotropicJointShading.full u htau.ne' q (F.tube i) angular width δ (Full i) (G i)
    let O := fun i => AnisotropicJointShading.marks u htau.ne' q (F.tube i) angular width δ (G i)
    ∃ color : Fin M → Fin (paletteSize k (separationFactor angular)),
    ∃ c : Fin (paletteSize k (separationFactor angular)),
      (∑ i, (volume : Measure (Space (k+1))).real (O i))/(paletteSize k (separationFactor angular):ℝ) ≤
        ∑ i, (volume : Measure (Space (k+1))).real (onColor color c O i) ∧
      (∀ i, onColor color c O i ⊆ onColor color c Y i) ∧
      (∀ T : Finset (Fin M),
        (∀ i ∈ T, 0 < (volume : Measure (Space (k+1))).real (onColor color c Y i)) →
        (MeasurableMarkedSelection.family J T).Separated (δ/tau) ∧
        (MeasurableMarkedSelection.family J T).CapBound (δ/tau) m (capFactor k angular m*A) ∧
        (MeasurableMarkedSelection.family J T).Bounded (baseBound angular R W)) := by
  intro htau J Y O
  have hs := joint_separated F u G (width:=width) hu htau htau1 ha hlocal hsep q
  obtain ⟨color,hcolor⟩ := full_separation_coloring J (div_pos hδ htau) (separationFactor_pos ha) hs
  obtain ⟨c,hc⟩ := marked_color volume (paletteSize_pos k (separationFactor angular)) color O
  refine ⟨color,c,hc,onColor_nested color c Y O
    (fun i => AnisotropicJointShading.nested u htau.ne' q (F.tube i) angular width δ (hsub i)),?_⟩
  intro T hpositive
  refine ⟨measured_onColor_separated J color c Y volume T hcolor hpositive,?_,?_⟩
  · exact MeasurableMarkedSelection.family_cap_bound J T
      (joint_cap_bound F u G hu hδ hδtau htau1 ha hm hA hlocal hcap q)
  · intro i
    exact joint_base_bound u htau q (F.tube _) angular width δ (G _) (hbox _)

/-- Explicit fixed palette bound; there is no delta, tau, population or
real-cap coefficient dependence in the number of colors. -/
theorem palette_bound (k : ℕ) {angular : ℝ} (ha : 0 ≤ angular) :
    (paletteSize k (separationFactor angular):ℝ) ≤
      packingConstant k*(4*(1+2*angular)^2)^k+2 := by
  have hC : (1:ℝ) ≤ 4*(1+2*angular)^2 := by nlinarith [sq_nonneg angular]
  have hs1 : separationFactor angular ≤ 1 :=
    (div_le_one (zero_lt_one.trans_le hC)).mpr hC
  have hh := paletteSize_bound k (separationFactor_pos ha)
  have hclip : clippedSeparation (separationFactor angular) = separationFactor angular := min_eq_left hs1
  rw [neighborBound,hclip] at hh
  simpa only [separationFactor,one_div_one_div] using hh

end
end KakeyaFormal.AnisotropicJointGeometry
