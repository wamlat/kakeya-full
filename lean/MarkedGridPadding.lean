import MarkedGridRefinement
import LocalizedDirectionThinning
import DensityBroadnessRecovery

/-! Actual common-grid padding of all full shadings, without any tube selection
or loss of original marked incidences. All geometric statements use the literal
original axes and the common refined grid. -/
namespace KakeyaFormal.MarkedGridPadding
open Finset MarkedGridRefinement TransverseAngles MarkedSubsetSamples
open scoped BigOperators
noncomputable section
open Classical

structure Padding {n M : ℕ} (F : TubeFamily n M) (j K : ℕ) where
  shade : Fin M → Finset (Cell n)
  anchors_subset : ∀ i, anchors j (F.shade i) ⊆ shade i
  child_subset : ∀ i, shade i ⊆ refine j (F.shade i)
  card_eq : ∀ i, (shade i).card=K

def Padding.family {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K) : TubeFamily n M :=
  ⟨F.tube,P.shade⟩

def marked {n M : ℕ} (j : ℕ) (marks : Fin M → Finset (Cell n)) : Fin M → Finset (Cell n) :=
  fun i => anchors j (marks i)

/-- Simultaneous actual finite choices. Every old full-cell anchor survives. -/
theorem construct {n M : ℕ} (F : TubeFamily n M) (j K : ℕ)
    (hlo : ∀ i, (F.shade i).card ≤ K)
    (hhi : ∀ i, K ≤ (factor j)^n*(F.shade i).card) : Nonempty (Padding F j K) := by
  have hrow := fun i => pad_row j (F.shade i) (hlo i) (hhi i)
  choose shade ha hs hc using hrow
  exact ⟨⟨shade,ha,hs,hc⟩⟩

theorem Padding.original_card_le {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K) (i : Fin M) :
    (F.shade i).card ≤ K := by
  simpa only [MarkedGridRefinement.anchors_card,P.card_eq] using card_le_card (P.anchors_subset i)

theorem Padding.marks_subset {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    (marks : Fin M → Finset (Cell n)) (hs : ∀ i, marks i ⊆ F.shade i) :
    ∀ i, marked j marks i ⊆ P.family.shade i := by
  intro i
  exact (image_subset_image (hs i)).trans (P.anchors_subset i)

theorem marked_card {n M : ℕ} (j : ℕ) (marks : Fin M → Finset (Cell n)) (i : Fin M) :
    (marked j marks i).card=(marks i).card := anchors_card j (marks i)

theorem marked_mass {n M : ℕ} (j : ℕ) (marks : Fin M → Finset (Cell n)) :
    (∑ i, ((marked j marks i).card : ℝ)) = ∑ i, ((marks i).card : ℝ) := by
  simp_rw [marked_card]

theorem Padding.union_subset {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    (E : Finset (Cell n)) (hE : ∀ i, F.shade i ⊆ E) : P.family.unionCells ⊆ refine j E := by
  intro z hz
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
  exact refine_mono j (hE i) (P.child_subset i hi)

theorem Padding.union_card {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    (E : Finset (Cell n)) (hE : ∀ i, F.shade i ⊆ E) :
    P.family.unionCells.card ≤ (factor j)^n*E.card := by
  rw [← refine_card]
  exact card_le_card (P.union_subset E hE)

/-- The full rows are exactly equal, not just within a factor two. -/
theorem Padding.comparable {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    {δ : ℝ} (hδ : 0 < δ) :
    P.family.Comparable (δ/(factor j:ℝ)) (δ*(K:ℝ)/(factor j:ℝ)) := by
  have hq : (0:ℝ) < factor j := by exact_mod_cast factor_pos j
  intro i
  change _ ≤ ((P.shade i).card : ℝ) ∧ ((P.shade i).card : ℝ) ≤ _
  rw [P.card_eq]
  have h1 : (δ*(K:ℝ)/(factor j:ℝ))/(δ/(factor j:ℝ))=(K:ℝ) := by field_simp
  have h2 : 2*(δ*(K:ℝ)/(factor j:ℝ))/(δ/(factor j:ℝ))=2*(K:ℝ) := by field_simp
  rw [h1,h2]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) K]

/-- Unit axes and their original positions are unchanged. -/
theorem Padding.admissible {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    {δ width : ℝ} (hδ : 0 < δ) (hadm : F.Admissible width δ) :
    P.family.Admissible ((factor j:ℝ)*(width+(n:ℝ)/2)) (δ/(factor j:ℝ)) := by
  have hq : (factor j:ℝ) ≠ 0 := by exact_mod_cast (factor_pos j).ne'
  intro i w hw
  obtain ⟨z,hz,hwz⟩ := mem_biUnion.mp (P.child_subset i hw)
  obtain ⟨t,ht,hd⟩ := hadm i z hz
  refine ⟨t,ht,?_⟩
  have hh := child_center_distance j hδ hwz
  have htri := dist_triangle (cellCenter (δ/(factor j:ℝ)) w) (cellCenter δ z) ((F.tube i).axisPoint t)
  change _ ≤ (factor j:ℝ)*(width+(n:ℝ)/2)*(δ/(factor j:ℝ))
  have heq : (factor j:ℝ)*(width+(n:ℝ)/2)*(δ/(factor j:ℝ))=width*δ+(n:ℝ)*δ/2 := by
    field_simp
  rw [heq]
  change dist _ ((F.tube i).axisPoint t) ≤ _
  linarith

theorem Padding.separated {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    {δ sep : ℝ} (hδ : 0 ≤ δ) (hqsep : 1/(factor j:ℝ) ≤ sep)
    (hsep : F.Separated (sep*δ)) : P.family.Separated (δ/(factor j:ℝ)) := by
  intro i l hil
  apply le_trans _ (hsep i l hil)
  simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_right hqsep hδ

theorem Padding.bounded {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    {R : ℝ} (h : F.Bounded R) : P.family.Bounded R := h

theorem Padding.cap_bound {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    {δ m A : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hcap : F.CapBound δ m A) : P.family.CapBound (δ/(factor j:ℝ)) m A := by
  have hq : (1:ℝ) ≤ factor j := by exact_mod_cast factor_pos j
  have hq0 : (0:ℝ) < factor j := by positivity
  have hnew : δ/(factor j:ℝ) ≤ δ := (div_le_iff₀ hq0).mpr (by nlinarith)
  exact LocalizedDirectionThinning.cap_bound_smaller_scale F (div_pos hδ hq0) hnew hδ1 hm hA hcap

/-- Full two ends survive every actual padding choice, with a fixed geometric
factor only. Radii beyond the old unit scale use the literal total row count. -/
theorem Padding.two_ends {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    {δ B alpha : ℝ} (hδ : 0 < δ) (hB : 1 ≤ B) (ha : 0 ≤ alpha)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
        B*r^alpha*((F.shade i).card : ℝ)) :
    ∀ i x r, δ/(factor j:ℝ) ≤ r → r ≤ 1 →
      (((P.family.shade i).filter (fun z => dist (cellCenter (δ/(factor j:ℝ)) z) x ≤ r)).card : ℝ) ≤
        ((factor j:ℝ)^n*B*(((n:ℝ)+1)*(factor j:ℝ))^alpha)*r^alpha*
          ((P.family.shade i).card : ℝ) := by
  intro i x r hr _
  have hq : (1:ℝ) ≤ factor j := by exact_mod_cast factor_pos j
  have hq0 : (0:ℝ) < factor j := by positivity
  have hr0 : 0 < r := (div_pos hδ hq0).trans_le hr
  let R := ((n:ℝ)+1)*(factor j:ℝ)*r
  have hdq := (div_le_iff₀ hq0).mp hr
  have hdR : δ ≤ R := by dsimp [R]; nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (mul_pos hq0 hr0).le]
  have hR0 : 0 < R := hδ.trans_le hdR
  have hrow : (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ R)).card : ℝ) ≤
      B*R^alpha*((F.shade i).card : ℝ) := by
    by_cases hR : R ≤ 1
    · exact hends i x R hdR hR
    · have hp := Real.one_le_rpow (le_of_not_ge hR) ha
      have hc : (1:ℝ) ≤ B*R^alpha := by nlinarith
      exact (Nat.cast_le.mpr (card_filter_le _ _)).trans (by nlinarith [Nat.cast_nonneg (α := ℝ) (F.shade i).card])
  have hcount := refined_ball_count j hδ hr (F.shade i) (P.shade i) (P.child_subset i) x
  have hcount' : (((P.shade i).filter (fun z => dist (cellCenter (δ/(factor j:ℝ)) z) x ≤ r)).card : ℝ) ≤
      (factor j:ℝ)^n*(((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ R)).card : ℝ) := by
    have hh : (↑((P.shade i).filter (fun z => dist (cellCenter (δ/(factor j:ℝ)) z) x ≤ r)).card : ℝ) ≤
      ((factor j)^n*(((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ R)).card) : ℕ) := Nat.cast_le.mpr hcount
    simpa only [Nat.cast_mul,Nat.cast_pow] using hh
  have hcard : ((F.shade i).card : ℝ) ≤ (P.shade i).card := by exact_mod_cast (P.original_card_le i).trans_eq (P.card_eq i).symm
  change (((P.shade i).filter (fun z => dist (cellCenter (δ/(factor j:ℝ)) z) x ≤ r)).card : ℝ) ≤ _*r^alpha*((P.shade i).card : ℝ)
  calc
    _ ≤ (factor j:ℝ)^n*(B*R^alpha*((F.shade i).card : ℝ)) := hcount'.trans (mul_le_mul_of_nonneg_left hrow (by positivity))
    _ ≤ (factor j:ℝ)^n*(B*R^alpha*((P.shade i).card : ℝ)) := by gcongr
    _ = _ := by rw [show R=(((n:ℝ)+1)*(factor j:ℝ))*r from rfl,Real.mul_rpow (by positivity) hr0.le]; ring

/-- At every occupied marked child, the exact old row and directions are used.
The angular radius and fraction are unchanged. -/
theorem Padding.marked_broad {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    (marks : Fin M → Finset (Cell n)) {theta fraction : ℝ}
    (hbroad : ∀ z ∈ DensityBroadnessRecovery.cells marks, ∀ v : Space n, ‖v‖=1 →
      (((incident (markedFamily F marks) z).filter (fun i =>
        projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
        fraction*((incident (markedFamily F marks) z).card : ℝ)) :
    ∀ z ∈ DensityBroadnessRecovery.cells (marked j marks), ∀ v : Space n, ‖v‖=1 →
      (((incident (markedFamily P.family (marked j marks)) z).filter (fun i =>
        projectiveDistance (P.family.tube i).direction v < theta)).card : ℝ) ≤
        fraction*((incident (markedFamily P.family (marked j marks)) z).card : ℝ) := by
  intro z hz v hv
  obtain ⟨i,_,hiz⟩ := mem_biUnion.mp hz
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hiz
  have hrow : incident (markedFamily P.family (marked j marks)) (anchor j w)=
      incident (markedFamily F marks) w := anchor_marked_row j marks w
  rw [hrow]
  exact hbroad w (mem_biUnion.mpr ⟨i,mem_univ _,hw⟩) v hv

def endsFactor (n j : ℕ) : ℝ := (factor j:ℝ)^n*(((n:ℝ)+1)*(factor j:ℝ))

theorem endsFactor_ge_one (n j : ℕ) : 1 ≤ endsFactor n j := by
  have hq : (1:ℝ) ≤ factor j := by exact_mod_cast factor_pos j
  have hpow : (1:ℝ) ≤ (factor j:ℝ)^n := one_le_pow₀ hq
  have hd : (1:ℝ) ≤ ((n:ℝ)+1)*(factor j:ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  unfold endsFactor
  nlinarith

/-- In the source range alpha≤1, the coefficient is a fixed multiple of B,
independent of alpha. Its effect inside the later 1/alpha power stays explicit. -/
theorem Padding.two_ends_fixed {n M j K : ℕ} {F : TubeFamily n M} (P : Padding F j K)
    {δ B alpha : ℝ} (hδ : 0 < δ) (hB : 1 ≤ B) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
        B*r^alpha*((F.shade i).card : ℝ)) :
    ∀ i x r, δ/(factor j:ℝ) ≤ r → r ≤ 1 →
      (((P.family.shade i).filter (fun z => dist (cellCenter (δ/(factor j:ℝ)) z) x ≤ r)).card : ℝ) ≤
        (endsFactor n j*B)*r^alpha*((P.family.shade i).card : ℝ) := by
  intro i x r hr hr1
  have hq : (1:ℝ) ≤ factor j := by exact_mod_cast factor_pos j
  have hr0 : 0 ≤ r := (div_pos hδ (by positivity : 0 < (factor j:ℝ))).le.trans hr
  have hd : (1:ℝ) ≤ ((n:ℝ)+1)*(factor j:ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hp : (((n:ℝ)+1)*(factor j:ℝ))^alpha ≤ ((n:ℝ)+1)*(factor j:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd ha1
  apply (P.two_ends hδ hB ha hends i x r hr hr1).trans
  unfold endsFactor
  calc
    _ ≤ ((factor j:ℝ)^n*B*(((n:ℝ)+1)*(factor j:ℝ)))*r^alpha*((P.family.shade i).card : ℝ) := by gcongr
    _ = _ := by ring

end
end KakeyaFormal.MarkedGridPadding
