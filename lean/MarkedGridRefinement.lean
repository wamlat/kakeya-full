import GridCells
import MarkedSubsetSamples

/-! One common odd-integer grid refinement for marked-family normalization.
Every original mark is sent to the same anchor child, preserving its entire
incident direction row. Full rows may be padded inside their actual child cells. -/
namespace KakeyaFormal.MarkedGridRefinement
open Finset GridGeometry GridCells
open scoped BigOperators
noncomputable section
open Classical

def factor (j : ℕ) : ℕ := 2*j+1

theorem factor_pos (j : ℕ) : 0 < factor j := by unfold factor; omega

def anchor {n : ℕ} (j : ℕ) (z : Cell n) : Cell n := fun i => (factor j:ℤ)*z i

def children {n : ℕ} (j : ℕ) (z : Cell n) : Finset (Cell n) := gridBox (anchor j z) j

theorem anchor_injective {n : ℕ} (j : ℕ) : Function.Injective (@anchor n j) := by
  intro z w h
  funext i
  have hh := congrFun h i
  change (factor j:ℤ)*z i=(factor j:ℤ)*w i at hh
  exact mul_left_cancel₀ (by exact_mod_cast (factor_pos j).ne') hh

theorem anchor_mem_children {n : ℕ} (j : ℕ) (z : Cell n) : anchor j z ∈ children j z := by
  rw [children,mem_gridBox]
  intro i
  omega

theorem children_card {n : ℕ} (j : ℕ) (z : Cell n) : (children j z).card=(factor j)^n := by
  exact gridBox_card _ _

/-- Actual child boxes of different original cells are disjoint. -/
theorem children_unique {n : ℕ} (j : ℕ) {a b z : Cell n}
    (ha : z ∈ children j a) (hb : z ∈ children j b) : a=b := by
  have ha' := mem_gridBox.mp ha
  have hb' := mem_gridBox.mp hb
  funext i
  have h1 := ha' i
  have h2 := hb' i
  change (factor j:ℤ)*a i-(j:ℤ) ≤ z i ∧ z i ≤ (factor j:ℤ)*a i+(j:ℤ) at h1
  change (factor j:ℤ)*b i-(j:ℤ) ≤ z i ∧ z i ≤ (factor j:ℤ)*b i+(j:ℤ) at h2
  have hq : (factor j:ℤ)=2*(j:ℤ)+1 := by simp [factor]
  have hqp : 0 ≤ (factor j:ℤ) := by positivity
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · have hstep : a i+1 ≤ b i := by omega
    have hh := mul_le_mul_of_nonneg_left hstep hqp
    nlinarith
  · have hstep : b i+1 ≤ a i := by omega
    have hh := mul_le_mul_of_nonneg_left hstep hqp
    nlinarith

theorem children_disjoint {n : ℕ} (j : ℕ) : Pairwise (fun a b : Cell n => Disjoint (children j a) (children j b)) := by
  intro a b hab
  exact disjoint_left.mpr (fun _ ha hb => hab (children_unique j ha hb))

def refine {n : ℕ} (j : ℕ) (S : Finset (Cell n)) : Finset (Cell n) := S.biUnion (children j)

theorem refine_card {n : ℕ} (j : ℕ) (S : Finset (Cell n)) :
    (refine j S).card=(factor j)^n*S.card := by
  have hdis : (S:Set (Cell n)).PairwiseDisjoint (children j) :=
    fun _ _ _ _ hne => children_disjoint j hne
  rw [refine,card_biUnion hdis]
  simp [children_card,Nat.mul_comm]

theorem refine_mono {n : ℕ} (j : ℕ) {S T : Finset (Cell n)} (h : S ⊆ T) :
    refine j S ⊆ refine j T := by
  intro z hz
  obtain ⟨w,hw,hz⟩ := mem_biUnion.mp hz
  exact mem_biUnion.mpr ⟨w,h hw,hz⟩

def anchors {n : ℕ} (j : ℕ) (S : Finset (Cell n)) : Finset (Cell n) := S.image (anchor j)

theorem anchors_card {n : ℕ} (j : ℕ) (S : Finset (Cell n)) : (anchors j S).card=S.card :=
  card_image_of_injective S (anchor_injective j)

theorem anchors_subset {n : ℕ} (j : ℕ) (S : Finset (Cell n)) : anchors j S ⊆ refine j S := by
  rintro z hz
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
  exact mem_biUnion.mpr ⟨w,hw,anchor_mem_children j w⟩

/-- Pad an actual row to any intermediate integer cardinality, keeping EVERY
anchor and staying inside that row's actual refined children. -/
theorem pad_row {n : ℕ} (j : ℕ) (S : Finset (Cell n)) {K : ℕ}
    (hlo : S.card ≤ K) (hhi : K ≤ (factor j)^n*S.card) :
    ∃ T : Finset (Cell n), anchors j S ⊆ T ∧ T ⊆ refine j S ∧ T.card=K := by
  apply exists_subsuperset_card_eq (anchors_subset j S)
  · rwa [anchors_card]
  · rwa [refine_card]

/-- Anchor centers are the exact original centers, at the common finer mesh. -/
theorem center_anchor {n : ℕ} (j : ℕ) (δ : ℝ) (z : Cell n) :
    cellCenter (δ/(factor j:ℝ)) (anchor j z)=cellCenter δ z := by
  have hq : (factor j:ℝ) ≠ 0 := by exact_mod_cast (factor_pos j).ne'
  apply WithLp.ofLp_injective
  funext i
  change (δ/(factor j:ℝ))*(((factor j:ℤ)*z i:ℤ):ℝ)=δ*(z i:ℝ)
  push_cast
  field_simp

/-- Every child center is genuinely inside its original half-open grid cell. -/
theorem child_center_mem {n : ℕ} (j : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {z w : Cell n} (hw : w ∈ children j z) :
    cellCenter (δ/(factor j:ℝ)) w ∈ gridCell δ z := by
  rw [mem_gridCell]
  intro i
  have hh := mem_gridBox.mp hw i
  have hlo : (factor j:ℝ)*(z i:ℝ)-(j:ℝ) ≤ (w i:ℝ) := by exact_mod_cast hh.1
  have hhi : (w i:ℝ) ≤ (factor j:ℝ)*(z i:ℝ)+(j:ℝ) := by exact_mod_cast hh.2
  have hq : (factor j:ℝ)=2*(j:ℝ)+1 := by simp [factor]
  have hqp : 0 < (factor j:ℝ) := by exact_mod_cast factor_pos j
  have h1 : (z i:ℝ)-1/2 ≤ (w i:ℝ)/(factor j:ℝ) :=
    (le_div_iff₀ hqp).mpr (by nlinarith)
  have h2 : (w i:ℝ)/(factor j:ℝ) < (z i:ℝ)+1/2 :=
    (div_lt_iff₀ hqp).mpr (by nlinarith)
  change δ*((z i:ℝ)-1/2) ≤ (δ/(factor j:ℝ))*(w i:ℝ) ∧
    (δ/(factor j:ℝ))*(w i:ℝ) < δ*((z i:ℝ)+1/2)
  constructor
  · simpa only [mul_div_assoc,div_mul_eq_mul_div] using mul_le_mul_of_nonneg_left h1 hδ.le
  · simpa only [mul_div_assoc,div_mul_eq_mul_div] using mul_lt_mul_of_pos_left h2 hδ

/-- The physical parent-distance bound is independent of the refinement factor. -/
theorem child_center_distance {n : ℕ} (j : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {z w : Cell n} (hw : w ∈ children j z) :
    dist (cellCenter (δ/(factor j:ℝ)) w) (cellCenter δ z) ≤ (n:ℝ)*δ/2 :=
  cell_center_distance (child_center_mem j hδ hw)

/-- A ball of child centers has only parents in this enlarged original ball.
The enlargement is valid down to the actual new mesh. -/
theorem parent_ball {n : ℕ} (j : ℕ) {δ r : ℝ} (hδ : 0 < δ)
    (hr : δ/(factor j:ℝ) ≤ r) {z w : Cell n} (hw : w ∈ children j z)
    (x : Space n) (hx : dist (cellCenter (δ/(factor j:ℝ)) w) x ≤ r) :
    dist (cellCenter δ z) x ≤ ((n:ℝ)+1)*(factor j:ℝ)*r := by
  have hq : (1:ℝ) ≤ factor j := by exact_mod_cast factor_pos j
  have hq0 : (0:ℝ) < factor j := by positivity
  have hdq : δ ≤ r*(factor j:ℝ) := (div_le_iff₀ hq0).mp hr
  have hr0 : 0 ≤ r := (div_pos hδ hq0).le.trans hr
  have hdist := child_center_distance j hδ hw
  have hdist' : dist (cellCenter δ z) (cellCenter (δ/(factor j:ℝ)) w) ≤ (n:ℝ)*δ/2 := by
    simpa only [dist_comm] using hdist
  have htri := dist_triangle (cellCenter δ z) (cellCenter (δ/(factor j:ℝ)) w) x
  have hnr := mul_le_mul_of_nonneg_left hdq (by positivity : 0 ≤ (n:ℝ)/2)
  have hqr : r ≤ (factor j:ℝ)*r := by nlinarith
  have hnn : (0:ℝ) ≤ n := by positivity
  have hprod : 0 ≤ (n:ℝ)*(factor j:ℝ)*r := by positivity
  nlinarith

/-- A literal finite ball count, with no assumed fiber-count or covering bound. -/
theorem refined_ball_count {n : ℕ} (j : ℕ) {δ r : ℝ} (hδ : 0 < δ)
    (hr : δ/(factor j:ℝ) ≤ r) (S T : Finset (Cell n)) (hT : T ⊆ refine j S)
    (x : Space n) :
    (T.filter (fun w => dist (cellCenter (δ/(factor j:ℝ)) w) x ≤ r)).card ≤
      (factor j)^n*(S.filter (fun z => dist (cellCenter δ z) x ≤
        ((n:ℝ)+1)*(factor j:ℝ)*r)).card := by
  rw [← refine_card]
  apply card_le_card
  intro w hw
  obtain ⟨z,hz,hwz⟩ := mem_biUnion.mp (hT (mem_filter.mp hw).1)
  exact mem_biUnion.mpr ⟨z,mem_filter.mpr ⟨hz,parent_ball j hδ hr hwz x
    (mem_filter.mp hw).2⟩,hwz⟩

/-- Original marked rows are copied exactly at the common anchors. -/
theorem anchor_marked_row {n M : ℕ} (j : ℕ) (marks : Fin M → Finset (Cell n)) (z : Cell n) :
    univ.filter (fun i => anchor j z ∈ anchors j (marks i)) = univ.filter (fun i => z ∈ marks i) := by
  ext i
  simp [anchors,(anchor_injective j).mem_finset_image]

/-- No non-anchor cell gains any marked incidences. -/
theorem nonanchor_marked_row {n M : ℕ} (j : ℕ) (marks : Fin M → Finset (Cell n))
    (w : Cell n) (hw : w ∉ Set.range (@anchor n j)) :
    univ.filter (fun i => w ∈ anchors j (marks i)) = ∅ := by
  apply filter_eq_empty_iff.mpr
  intro i _ hi
  obtain ⟨z,_,hz⟩ := mem_image.mp hi
  exact hw ⟨z,hz⟩

end
end KakeyaFormal.MarkedGridRefinement
