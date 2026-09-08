import MarkedGridPadding
import AdmissiblePivotSlabs

/-! Fixed density multiples and fixed direction separation are normalized by
one common refinement. Every tube and every original marked incidence survive;
only the full rows are padded inside their disjoint original-cell children. -/
namespace KakeyaFormal.MarkedGridNormalization
open Finset MarkedGridRefinement MarkedGridPadding TransverseAngles MarkedSubsetSamples
open scoped BigOperators
noncomputable section
open Classical

/-- Chosen before every scale, density and actual marked configuration. -/
def depth (a b sep : ℝ) : ℕ := Nat.ceil (max (1/sep) (max (2*b) (b/a+1)))

theorem depth_bounds {n : ℕ} (hn : 1 ≤ n) (a b sep : ℝ) :
    1/sep ≤ (factor (depth a b sep):ℝ) ∧
    2*b ≤ (factor (depth a b sep):ℝ) ∧
    b/a+1 ≤ (factor (depth a b sep):ℝ)^n := by
  have hceil := Nat.le_ceil (max (1/sep) (max (2*b) (b/a+1)))
  have hjq : (depth a b sep:ℝ) ≤ factor (depth a b sep) := by
    have hh : depth a b sep ≤ factor (depth a b sep) := by unfold factor; omega
    exact_mod_cast hh
  have hq : (1:ℝ) ≤ factor (depth a b sep) := by exact_mod_cast factor_pos (depth a b sep)
  have hpow : (factor (depth a b sep):ℝ) ≤ (factor (depth a b sep):ℝ)^n := by
    simpa only [pow_one] using pow_le_pow_right₀ hq hn
  have hb : max (1/sep) (max (2*b) (b/a+1)) ≤ (factor (depth a b sep):ℝ) := hceil.trans hjq
  exact ⟨(le_max_left _ _).trans hb,
    ((le_max_left _ _).trans (le_max_right _ _)).trans hb,
    (((le_max_right _ _).trans (le_max_right _ _)).trans hb).trans hpow⟩

def rowTarget (δ lam b : ℝ) : ℕ := Nat.ceil (b*lam/δ)

def newDensity (j : ℕ) (δ lam b : ℝ) : ℝ := δ*(rowTarget δ lam b:ℝ)/(factor j:ℝ)

def newFraction (xi b : ℝ) : ℝ := xi/(2*max 1 b)

def newWidth (n j : ℕ) (width : ℝ) : ℝ := (factor j:ℝ)*(width+(n:ℝ)/2)

/-- Integer padding capacities are derived from the actual nonempty original
family and fixed density interval, not assumed as geometric counting data. -/
theorem row_target_bounds {n M : ℕ} (F : TubeFamily n M) {j : ℕ} {δ lam a b : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (ha : 0 < a) (hb : 0 < b) (hM : 0 < M)
    (hcapacity : b/a+1 ≤ (factor j:ℝ)^n)
    (hlower : ∀ i, a*lam/δ ≤ ((F.shade i).card : ℝ))
    (hupper : ∀ i, ((F.shade i).card : ℝ) ≤ b*lam/δ) :
    0 < rowTarget δ lam b ∧
    b*lam/δ ≤ (rowTarget δ lam b:ℝ) ∧
    (rowTarget δ lam b:ℝ) ≤ 2*b*lam/δ ∧
    (∀ i, (F.shade i).card ≤ rowTarget δ lam b) ∧
    (∀ i, rowTarget δ lam b ≤ (factor j)^n*(F.shade i).card) := by
  have ht : 0 < b*lam/δ := by positivity
  have hceil : b*lam/δ ≤ (rowTarget δ lam b:ℝ) := Nat.le_ceil _
  have hpos : 0 < rowTarget δ lam b := by exact_mod_cast ht.trans_le hceil
  have hrowpos (i : Fin M) : (1:ℝ) ≤ (F.shade i).card := by
    have hp : 0 < (F.shade i).card := by exact_mod_cast (div_pos (mul_pos ha hlam) hδ).trans_le (hlower i)
    exact_mod_cast hp
  have ht1 : (1:ℝ) ≤ b*lam/δ := (hrowpos ⟨0,hM⟩).trans (hupper ⟨0,hM⟩)
  have hceilUp : (rowTarget δ lam b:ℝ) < b*lam/δ+1 := Nat.ceil_lt_add_one ht.le
  refine ⟨hpos,hceil,?_,?_,?_⟩
  · calc
      _ ≤ 2*(b*lam/δ) := by linarith
      _ = _ := by ring
  · intro i
    exact_mod_cast (hupper i).trans hceil
  · intro i
    have hscaled : b*lam/δ ≤ (b/a)*((F.shade i).card : ℝ) := by
      calc
        _ = (b/a)*(a*lam/δ) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hlower i) (by positivity)
    have hp := mul_le_mul_of_nonneg_right hcapacity (Nat.cast_nonneg (α := ℝ) (F.shade i).card)
    have hh : (rowTarget δ lam b:ℝ) ≤ (factor j:ℝ)^n*((F.shade i).card : ℝ) := by
      nlinarith [hrowpos i]
    exact_mod_cast hh

/-- Density and marking conversion has fixed losses only. -/
theorem parameter_bounds {n M : ℕ} (F : TubeFamily n M) {j : ℕ} {δ lam xi a b : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hxi : 0 < xi) (hxi1 : xi ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hM : 0 < M)
    (hcapacity : b/a+1 ≤ (factor j:ℝ)^n) (hqb : 2*b ≤ (factor j:ℝ))
    (hlower : ∀ i, a*lam/δ ≤ ((F.shade i).card : ℝ))
    (hupper : ∀ i, ((F.shade i).card : ℝ) ≤ b*lam/δ) :
    0 < newDensity j δ lam b ∧ (b/(factor j:ℝ))*lam ≤ newDensity j δ lam b ∧
      newDensity j δ lam b ≤ (2*b/(factor j:ℝ))*lam ∧ newDensity j δ lam b ≤ 1 ∧
      0 < newFraction xi b ∧ newFraction xi b ≤ 1 ∧
      newFraction xi b*newDensity j δ lam b/(δ/(factor j:ℝ)) ≤ xi*lam/δ := by
  obtain ⟨hK,hlo,hhi,_,_⟩ := row_target_bounds F hδ hlam ha hb hM hcapacity hlower hupper
  have hq : (0:ℝ) < factor j := by exact_mod_cast factor_pos j
  have hD : (0:ℝ) < 2*max 1 b := by positivity
  have hK0 : (0:ℝ) < rowTarget δ lam b := by exact_mod_cast hK
  have hnlo : (b/(factor j:ℝ))*lam ≤ newDensity j δ lam b := by
    unfold newDensity
    apply (le_div_iff₀ hq).mpr
    have hh := (div_le_iff₀ hδ).mp hlo
    field_simp
    nlinarith
  have hnhi : newDensity j δ lam b ≤ (2*b/(factor j:ℝ))*lam := by
    unfold newDensity
    apply (div_le_iff₀ hq).mpr
    have hh := (le_div_iff₀ hδ).mp hhi
    field_simp
    nlinarith
  have hratio : 2*b/(factor j:ℝ) ≤ 1 := (div_le_one hq).mpr hqb
  have hnp : 0 < newDensity j δ lam b := by unfold newDensity; positivity
  have hfl : newFraction xi b ≤ 1 := by
    unfold newFraction
    apply (div_le_one hD).mpr
    linarith [le_max_left (1:ℝ) b]
  refine ⟨hnp,hnlo,hnhi,(hnhi.trans (by nlinarith)).trans hlam1,
    by unfold newFraction; positivity,hfl,?_⟩
  have hid : newFraction xi b*newDensity j δ lam b/(δ/(factor j:ℝ))=
      xi*(rowTarget δ lam b:ℝ)/(2*max 1 b) := by
    unfold newFraction newDensity
    field_simp
  rw [hid]
  apply (div_le_iff₀ hD).mpr
  have hh := mul_le_mul_of_nonneg_left hhi hxi.le
  have hmax : b ≤ max 1 b := le_max_right _ _
  have hh2 := mul_le_mul_of_nonneg_left hmax (by positivity : 0 ≤ 2*xi*lam/δ)
  calc
    _ ≤ xi*(2*b*lam/δ) := hh
    _ = (2*xi*lam/δ)*b := by ring
    _ ≤ (2*xi*lam/δ)*max 1 b := hh2
    _ = _ := by ring

/-- Original marked configurations with arbitrary fixed positive density
multiples and fixed positive separation. This does not strengthen broadness. -/
structure Input {n M : ℕ} (F : TubeFamily n M) (E : Finset (Cell n))
    (marks : Fin M → Finset (Cell n))
    (δ A lam xi B theta width R m alpha a b sep : ℝ) : Prop where
  scale_pos : 0 < δ
  scale_le_one : δ ≤ 1
  cap_ge_one : 1 ≤ A
  density_pos : 0 < lam
  density_le_one : lam ≤ 1
  fraction_pos : 0 < xi
  fraction_le_one : xi ≤ 1
  count_pos : 0 < M
  ends_ge_one : 1 ≤ B
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  cover : ∀ i, F.shade i ⊆ E
  admissible : F.Admissible width δ
  separated : F.Separated (sep*δ)
  bounded : F.Bounded R
  cap_bound : F.CapBound δ m A
  lower : ∀ i, a*lam/δ ≤ ((F.shade i).card : ℝ)
  upper : ∀ i, ((F.shade i).card : ℝ) ≤ b*lam/δ
  marks_subset : ∀ i, marks i ⊆ F.shade i
  marked_mass : xi*lam*(M:ℝ)/δ ≤ ∑ i, ((marks i).card : ℝ)
  marked_broad : ∀ z ∈ DensityBroadnessRecovery.cells marks, ∀ v : Space n, ‖v‖=1 →
    (((incident (markedFamily F marks) z).filter (fun i =>
      projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
      ((incident (markedFamily F marks) z).card : ℝ)/10
  two_ends : ∀ i x r, δ ≤ r → r ≤ 1 →
    (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
      B*r^alpha*((F.shade i).card : ℝ)

/-- The resulting hypotheses are those consumed by the already constructed
actual marked pivot core. All constants and new parameters are explicit. -/
structure Output {n M : ℕ} (F : TubeFamily n M) (E : Finset (Cell n))
    (marks : Fin M → Finset (Cell n))
    (δ A lam xi B theta width R m alpha a b sep : ℝ) where
  padding : Padding F (depth a b sep) (rowTarget δ lam b)
  normalized : AdmissiblePivotSlabs.Hypotheses padding.family (refine (depth a b sep) E)
    (marked (depth a b sep) marks)
    (δ/(factor (depth a b sep):ℝ)) A (newDensity (depth a b sep) δ lam b)
    (newFraction xi b) (endsFactor n (depth a b sep)*B) theta
    (newWidth n (depth a b sep) width) R m alpha
  density_lower : (b/(factor (depth a b sep):ℝ))*lam ≤ newDensity (depth a b sep) δ lam b
  density_upper : newDensity (depth a b sep) δ lam b ≤ (2*b/(factor (depth a b sep):ℝ))*lam
  density_le_one : newDensity (depth a b sep) δ lam b ≤ 1
  fraction_le_one : newFraction xi b ≤ 1
  marks_mass_exact : (∑ i, ((marked (depth a b sep) marks i).card : ℝ))=∑ i, ((marks i).card : ℝ)
  union_card : padding.family.unionCells.card ≤ (factor (depth a b sep))^n*E.card

/-- Actual normalization, with no selected-row, cap, broadness or support oracle. -/
theorem construct {n M : ℕ} {F : TubeFamily n M} {E : Finset (Cell n)}
    {marks : Fin M → Finset (Cell n)} {δ A lam xi B theta width R m alpha a b sep : ℝ}
    (hn : 1 ≤ n) (ha : 0 < a) (hb : 0 < b) (hsep : 0 < sep)
    (hm : 0 ≤ m) (halpha : 0 ≤ alpha) (halpha1 : alpha ≤ 1)
    (h : Input F E marks δ A lam xi B theta width R m alpha a b sep) :
    Nonempty (Output F E marks δ A lam xi B theta width R m alpha a b sep) := by
  let j := depth a b sep
  obtain ⟨hjsep,hjb,hjcap⟩ := depth_bounds hn a b sep
  obtain ⟨_,_,_,hlo,hhi⟩ := row_target_bounds F h.scale_pos h.density_pos ha hb h.count_pos hjcap h.lower h.upper
  obtain ⟨P⟩ := MarkedGridPadding.construct F j (rowTarget δ lam b) hlo hhi
  obtain ⟨hnp,hnlo,hnhi,hn1,hfp,hf1,hfbound⟩ := parameter_bounds F h.scale_pos h.density_pos
    h.density_le_one h.fraction_pos h.fraction_le_one ha hb h.count_pos hjcap hjb h.lower h.upper
  have hq : (1:ℝ) ≤ factor j := by exact_mod_cast factor_pos j
  have hq0 : (0:ℝ) < factor j := by positivity
  have hjsep' : 1/(factor j:ℝ) ≤ sep := by
    apply (div_le_iff₀ hq0).mpr
    have hh := (div_le_iff₀ hsep).mp hjsep
    nlinarith
  have hnew : δ/(factor j:ℝ) ≤ δ := (div_le_iff₀ hq0).mpr (by nlinarith [h.scale_pos])
  have hB : 1 ≤ endsFactor n j*B := by nlinarith [endsFactor_ge_one n j,h.ends_ge_one]
  have hmass : newFraction xi b*newDensity j δ lam b*(M:ℝ)/(δ/(factor j:ℝ)) ≤
      ∑ i, ((marked j marks i).card : ℝ) := by
    rw [MarkedGridPadding.marked_mass]
    have hh := mul_le_mul_of_nonneg_right hfbound (Nat.cast_nonneg (α := ℝ) M)
    have hh' : newFraction xi b*newDensity j δ lam b*(M:ℝ)/(δ/(factor j:ℝ)) ≤ xi*lam*(M:ℝ)/δ := by
      simpa only [j,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
    exact hh'.trans h.marked_mass
  have hbroad := P.marked_broad marks (theta := theta) (fraction := (1/10:ℝ)) (by
    intro z hz v hv
    simpa only [div_eq_mul_inv,mul_comm,one_mul] using h.marked_broad z hz v hv)
  refine ⟨{
    padding := P
    normalized := {
      scale_pos := div_pos h.scale_pos hq0
      scale_le_one := hnew.trans h.scale_le_one
      cap_coefficient := h.cap_ge_one
      density_pos := hnp
      marked_fraction_pos := hfp
      count_pos := h.count_pos
      two_ends_coefficient := hB
      angular_radius_pos := h.theta_pos
      angular_radius_le_one := h.theta_le_one
      cover := fun i => (P.child_subset i).trans (refine_mono j (h.cover i))
      admissible := P.admissible h.scale_pos h.admissible
      separated := P.separated h.scale_pos.le hjsep' h.separated
      bounded := P.bounded h.bounded
      cap_bound := P.cap_bound h.scale_pos h.scale_le_one hm (by linarith [h.cap_ge_one]) h.cap_bound
      comparable := P.comparable h.scale_pos
      marks_subset := P.marks_subset marks h.marks_subset
      marked_mass := hmass
      marked_broad := by
        intro z hz v hv
        simpa only [div_eq_mul_inv,mul_comm,one_mul] using hbroad z hz v hv
      two_ends := P.two_ends_fixed h.scale_pos h.ends_ge_one halpha halpha1 h.two_ends }
    density_lower := hnlo
    density_upper := hnhi
    density_le_one := hn1
    fraction_le_one := hf1
    marks_mass_exact := MarkedGridPadding.marked_mass j marks
    union_card := P.union_card E h.cover }⟩

end
end KakeyaFormal.MarkedGridNormalization
