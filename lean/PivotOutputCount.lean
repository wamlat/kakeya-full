import PivotWitnesses
import GridCells
import TubeLocalCount
import GroupedIncidence

/-! Actual geometric output and fiber counts for normalized legal samples.
Endpoint labels are not identified with their projections; their local packing
is derived from actual Euclidean grid bounds. -/
namespace KakeyaFormal.PivotOutputCount
open Finset PivotWitnesses GridGeometry TubeLocalCount
open scoped BigOperators
noncomputable section
open Classical

/-- Fixed projection coordinates and two distinct endpoint labels determine the
sample. All further fields are propositions, so no sample multiplicity is hidden. -/
structure LabeledPair {k : ℕ} {kap : ℝ} (a : Angle k kap)
    (δ width : ℝ) (firstCoord secondCoord : Cell k → ℝ) where
  firstLabel : Cell k
  secondLabel : Cell k
  gap : kap ≤ firstCoord firstLabel-a.intermediate
  first_upper : firstCoord firstLabel ≤ 1
  second_lower : kap ≤ |secondCoord secondLabel|
  second_upper : |secondCoord secondLabel| ≤ 1
  first_close : dist (cellCenter δ firstLabel) (a.vertex+firstCoord firstLabel • a.first) ≤ width*δ
  second_close : dist (cellCenter δ secondLabel) (a.vertex+secondCoord secondLabel • a.second) ≤ width*δ

namespace LabeledPair
variable {k : ℕ} {kap δ width : ℝ} {a : Angle k kap} {fc sc : Cell k → ℝ}

def endpoints (s : LabeledPair a δ width fc sc) : Endpoints a :=
  ⟨fc s.firstLabel,sc s.secondLabel,s.gap,s.first_upper,s.second_lower,s.second_upper⟩

def pivotLabel (s : LabeledPair a δ width fc sc) : Cell k :=
  GridCells.label δ s.endpoints.pivot

theorem labels_injective : Function.Injective
    (fun s : LabeledPair a δ width fc sc => (s.firstLabel,s.secondLabel)) := by
  intro s t heq
  cases s
  cases t
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl,rfl⟩ := heq
  rfl

/-- Rounded pivot labels are actual half-open grid labels. -/
theorem pivot_rounding (s : LabeledPair a δ width fc sc) (hδ : 0 < δ) :
    dist s.endpoints.pivot (cellCenter δ s.pivotLabel) ≤ (k : ℝ)*δ/2 :=
  GridCells.cell_center_distance (GridCells.gridCell_covers hδ _)

end LabeledPair

/-- A fixed constant per one-mesh longitudinal interval. -/
def boxConstant (k : ℕ) (width : ℝ) : ℝ := ((2*Nat.ceil (width+1)+3 : ℕ) : ℝ)^k

theorem boxConstant_pos (k : ℕ) (width : ℝ) : 0 < boxConstant k width := by
  dsimp [boxConstant]
  positivity

/-- Physical intervals of arbitrary length have a linear grid-count bound,
including intervals shorter than one mesh. -/
theorem interval_grid_count {k : ℕ} (T : UnitTube k) {δ width a b : ℝ}
    (hδ : 0 < δ) (hab : a < b) (cells : Finset (Cell k))
    (hinc : ∀ z ∈ cells, ∃ t ∈ Set.Icc a b,
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ) :
    (cells.card : ℝ) ≤ boxConstant k width*((b-a)/δ+2) := by
  have hh := segment_grid_count_of_length_le (T.axisPoint a) (T.axisPoint b) hδ
    (show dist (T.axisPoint a) (T.axisPoint b) ≤ b-a by
      rw [T.axisPoint_distance,abs_of_nonpos (by linarith : a-b ≤ 0)]; linarith) cells
    (fun z hz => by
      obtain ⟨t,ht,hz⟩ := hinc z hz
      exact ⟨T.axisPoint t,axisPoint_mem_segment T hab ht.1 ht.2,hz⟩)
  have hcast : (cells.card : ℝ) ≤ ((Nat.ceil ((b-a)/δ) : ℝ)+1)*boxConstant k width := by
    dsimp [boxConstant]
    exact_mod_cast hh
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ (b-a)/δ)
  have hmul := mul_le_mul_of_nonneg_right (by linarith : (Nat.ceil ((b-a)/δ) : ℝ)+1 ≤ (b-a)/δ+2)
    (boxConstant_pos k width).le
  exact hcast.trans (by simpa only [mul_comm] using hmul)

/-- The legal coefficient multiplying the second direction is in [-1,1]. -/
theorem coefficient_abs_le_one {k : ℕ} {kap : ℝ} {a : Angle k kap}
    (p : Endpoints a) (hk : 0 < kap) : |p.coefficient| ≤ 1 := by
  have ha : 0 < a.intermediate := hk.trans_le a.intermediate_lower
  have hb : 0 < p.firstCoord := by linarith [p.gap]
  have hratio : 0 ≤ a.intermediate/p.firstCoord := div_nonneg ha.le hb.le
  have hratio1 : a.intermediate/p.firstCoord ≤ 1 := (div_le_one hb).mpr (by linarith [p.gap])
  rw [Endpoints.coefficient,abs_mul,abs_of_nonneg (by linarith : 0 ≤ 1-a.intermediate/p.firstCoord)]
  have hh := mul_le_mul p.second_upper (by linarith : 1-a.intermediate/p.firstCoord ≤ 1)
    (by linarith : 0 ≤ 1-a.intermediate/p.firstCoord) (by norm_num : (0:ℝ) ≤ 1)
  simpa using hh

/-- With the intermediate fixed, all actual rounded pivots lie along a bounded
second-axis segment. The count has no inverse-kappa factor. -/
theorem pivot_output_count {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (S : Finset (LabeledPair a δ width fc sc))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) :
    ((S.image LabeledPair.pivotLabel).card : ℝ) ≤ 4*boxConstant k ((k : ℝ)/2)/δ := by
  let T : UnitTube k := ⟨a.vertex+a.intermediate • a.first,a.second,a.second_unit⟩
  have hinc : ∀ z ∈ S.image LabeledPair.pivotLabel, ∃ t ∈ Set.Icc (-1:ℝ) 1,
      dist (cellCenter δ z) (T.axisPoint t) ≤ ((k : ℝ)/2)*δ := by
    intro z hz
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
    have hc := coefficient_abs_le_one s.endpoints hk
    refine ⟨s.endpoints.coefficient,abs_le.mp hc,?_⟩
    have hh := s.pivot_rounding hδ
    change dist s.endpoints.pivot (cellCenter δ s.pivotLabel) ≤ _ at hh
    change dist (cellCenter δ s.pivotLabel) s.endpoints.pivot ≤ _
    rw [dist_comm]
    linarith
  have hc := interval_grid_count T hδ (by norm_num : (-1:ℝ) < 1) _ hinc
  have hratio : (1:ℝ) ≤ 1/δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hfactor : ((1:ℝ)-(-1))/δ+2 ≤ 4/δ := by
    simp only [div_eq_mul_inv] at hratio ⊢
    linarith
  have hh := hc.trans (mul_le_mul_of_nonneg_left hfactor (boxConstant_pos k ((k : ℝ)/2)).le)
  convert hh using 1 <;> first | rfl | ring

/-- The first endpoint labels occupy an actual unit tube, irrespective of the
number of samples sharing each endpoint. -/
theorem first_label_count {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (S : Finset (LabeledPair a δ width fc sc))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) :
    ((S.image LabeledPair.firstLabel).card : ℝ) ≤ 3*boxConstant k width/δ := by
  let T : UnitTube k := ⟨a.vertex,a.first,a.first_unit⟩
  have hinc : ∀ z ∈ S.image LabeledPair.firstLabel, ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ := by
    intro z hz
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
    refine ⟨fc s.firstLabel,⟨by linarith [s.gap,a.intermediate_lower],s.first_upper⟩,s.first_close⟩
  have hc := interval_grid_count T hδ (by norm_num : (0:ℝ) < 1) _ hinc
  have hratio : (1:ℝ) ≤ 1/δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hfactor : ((1:ℝ)-0)/δ+2 ≤ 3/δ := by
    simp only [div_eq_mul_inv] at hratio ⊢
    linarith
  have hh := hc.trans (mul_le_mul_of_nonneg_left hfactor (boxConstant_pos k width).le)
  convert hh using 1 <;> first | rfl | ring


/-- Coincidence of actual rounded labels bounds the difference of exact pivot
coefficients along the unit second direction. -/
theorem rounded_coefficient_gap {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (s t : LabeledPair a δ width fc sc) (hδ : 0 < δ)
    (hlabel : s.pivotLabel = t.pivotLabel) :
    |s.endpoints.coefficient-t.endpoints.coefficient| ≤ (k : ℝ)*δ := by
  have hid : s.endpoints.pivot-t.endpoints.pivot =
      (s.endpoints.coefficient-t.endpoints.coefficient) • a.second := by
    dsimp [Endpoints.pivot]
    module
  have hh := dist_triangle s.endpoints.pivot (cellCenter δ s.pivotLabel) t.endpoints.pivot
  have hs := s.pivot_rounding hδ
  have ht := t.pivot_rounding hδ
  rw [hlabel,dist_comm (cellCenter δ t.pivotLabel)] at hh
  rw [hlabel] at hs
  rw [dist_eq_norm,hid,norm_smul,Real.norm_eq_abs,a.second_unit,mul_one] at hh
  linarith

/-- A fixed first endpoint means the first projection coordinate is literally
fixed. Legal separation therefore converts the coefficient gap into a linear
inverse-kappa interval for the second projection coordinate. -/
theorem same_first_second_gap {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (s t : LabeledPair a δ width fc sc)
    (hδ : 0 < δ) (hk : 0 < kap)
    (hfirst : s.firstLabel = t.firstLabel) (hlabel : s.pivotLabel = t.pivotLabel) :
    |sc s.secondLabel-sc t.secondLabel| ≤ (k : ℝ)*δ/kap := by
  have hlo : kap ≤ 1-a.intermediate/fc s.firstLabel := by
    simpa using (KakeyaAudit.TubeGeometry.legal_fraction_lower_bounds hk
      a.intermediate_lower s.gap s.first_upper).2
  have hgap := rounded_coefficient_gap s t hδ hlabel
  have hid : s.endpoints.coefficient-t.endpoints.coefficient =
      (sc s.secondLabel-sc t.secondLabel)*(1-a.intermediate/fc s.firstLabel) := by
    dsimp [Endpoints.coefficient,LabeledPair.endpoints]
    rw [hfirst]
    ring
  rw [hid,abs_mul,abs_of_nonneg (hk.le.trans hlo)] at hgap
  apply (le_div_iff₀ hk).mpr
  exact (mul_le_mul_of_nonneg_left hlo (abs_nonneg _)).trans hgap

/-- All samples with one first label and one rounded pivot are counted by their
actual second labels. Linear longitudinal grid packing supplies the bound. -/
theorem fixed_first_fiber_count {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (S : Finset (LabeledPair a δ width fc sc))
    (first pivot : Cell k) (hδ : 0 < δ) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hfirst : ∀ s ∈ S, s.firstLabel = first) (hpivot : ∀ s ∈ S, s.pivotLabel = pivot) :
    (S.card : ℝ) ≤ ((2*(k : ℝ)+4)*boxConstant k width)/kap := by
  by_cases hS : S.Nonempty
  · obtain ⟨s0,hs0⟩ := hS
    let T : UnitTube k := ⟨a.vertex,a.second,a.second_unit⟩
    let rad := ((k : ℝ)+1)*δ/kap
    have hrad : 0 < rad := by dsimp [rad]; positivity
    have hinc : ∀ z ∈ S.image LabeledPair.secondLabel,
        ∃ u ∈ Set.Icc (sc s0.secondLabel-rad) (sc s0.secondLabel+rad),
        dist (cellCenter δ z) (T.axisPoint u) ≤ width*δ := by
      intro z hz
      obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
      have hgap := same_first_second_gap s s0 hδ hk ((hfirst s hs).trans (hfirst s0 hs0).symm)
        ((hpivot s hs).trans (hpivot s0 hs0).symm)
      have hgap' : |sc s.secondLabel-sc s0.secondLabel| ≤ rad := hgap.trans (by
        dsimp [rad]
        apply div_le_div_of_nonneg_right _ hk.le
        nlinarith)
      obtain ⟨hlo,hhi⟩ := abs_le.mp hgap'
      exact ⟨sc s.secondLabel,⟨by linarith,by linarith⟩,s.second_close⟩
    have hc := interval_grid_count T hδ (by linarith : sc s0.secondLabel-rad < sc s0.secondLabel+rad)
      (S.image LabeledPair.secondLabel) hinc
    have hfactor : (sc s0.secondLabel+rad-(sc s0.secondLabel-rad))/δ+2 ≤ (2*(k : ℝ)+4)/kap := by
      have hratio : (1:ℝ) ≤ 1/kap := (le_div_iff₀ hk).mpr (by simpa using hk1)
      have hid : (sc s0.secondLabel+rad-(sc s0.secondLabel-rad))/δ = 2*((k : ℝ)+1)/kap := by
        dsimp [rad]
        field_simp
        ring
      rw [hid]
      simp only [div_eq_mul_inv] at hratio ⊢
      nlinarith
    have hinj : Set.InjOn LabeledPair.secondLabel (S : Set (LabeledPair a δ width fc sc)) := by
      intro s hs t ht hst
      apply LabeledPair.labels_injective
      exact Prod.ext ((hfirst s hs).trans (hfirst t ht).symm) hst
    have hcard := card_image_of_injOn hinj
    rw [hcard] at hc
    have hh := hc.trans (mul_le_mul_of_nonneg_left hfactor (boxConstant_pos k width).le)
    convert hh using 1 <;> first | rfl | ring
  · have hh : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    rw [hh,card_empty,Nat.cast_zero]
    have := (boxConstant_pos k width).le
    positivity

def fiberConstant (k : ℕ) (width : ℝ) : ℝ := 3*(2*(k : ℝ)+4)*(boxConstant k width)^2

/-- The actual fixed-pivot fiber has at most C(k,width)/(kappa*delta) distinct
endpoint-label pairs. Both geometric counting inputs are derived above. -/
theorem pivot_fiber_count {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (S : Finset (LabeledPair a δ width fc sc)) (pivot : Cell k)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) (hk1 : kap ≤ 1) :
    ((S.filter (fun s => s.pivotLabel = pivot)).card : ℝ) ≤ fiberConstant k width/(kap*δ) := by
  let F := S.filter (fun s => s.pivotLabel = pivot)
  have hsum : (F.card : ℝ) = ∑ first ∈ F.image LabeledPair.firstLabel,
      ((F.filter (fun s => s.firstLabel = first)).card : ℝ) := by
    have hh := sum_fiberwise_of_maps_to (s := F) (t := F.image LabeledPair.firstLabel)
      (g := LabeledPair.firstLabel) (fun s hs => mem_image.mpr ⟨s,hs,rfl⟩) (fun _ => (1:ℕ))
    simp only [sum_const,nsmul_eq_mul,mul_one] at hh
    exact_mod_cast hh.symm
  have hlocal (first) (_ : first ∈ F.image LabeledPair.firstLabel) :
      ((F.filter (fun s => s.firstLabel = first)).card : ℝ) ≤ ((2*(k : ℝ)+4)*boxConstant k width)/kap := by
    apply fixed_first_fiber_count _ first pivot hδ hk hk1
    · intro s hs
      exact (mem_filter.mp hs).2
    · intro s hs
      exact (mem_filter.mp (mem_filter.mp hs).1).2
  have hh := sum_le_sum hlocal
  simp only [sum_const,nsmul_eq_mul,← hsum] at hh
  have hfirst := first_label_count F hδ hδ1 hk
  have hconst : 0 ≤ ((2*(k : ℝ)+4)*boxConstant k width)/kap := by
    have := (boxConstant_pos k width).le
    positivity
  have hc := hh.trans (mul_le_mul_of_nonneg_right hfirst hconst)
  change (F.card : ℝ) ≤ _
  convert hc using 1 <;> first | rfl | (dsimp [fiberConstant]; ring)


/-- A dependent sample retains its actual intermediate-label index. -/
def sampleOutput {Index : Type*} {k : ℕ} {kap δ width : ℝ}
    {a : Index → Angle k kap} {fc sc : Index → Cell k → ℝ}
    (s : (i : Index) × LabeledPair (a i) δ width (fc i) (sc i)) : Cell k × Index :=
  (s.2.pivotLabel,s.1)

/-- Distinct sample records are distinct intermediate/first/second label
triples. Proof fields and projection choices create no multiplicity. -/
theorem sample_labels_injective {Index : Type*} {k : ℕ} {kap δ width : ℝ}
    {a : Index → Angle k kap} {fc sc : Index → Cell k → ℝ} :
    Function.Injective (fun s : (i : Index) × LabeledPair (a i) δ width (fc i) (sc i) =>
      (s.1,s.2.firstLabel,s.2.secondLabel)) := by
  intro s t heq
  rcases s with ⟨i,s⟩
  rcases t with ⟨j,t⟩
  obtain ⟨hij,hlabels⟩ := Prod.mk.inj heq
  dsimp only at hij
  subst j
  have hh : s = t := LabeledPair.labels_injective hlabels
  subst t
  rfl

/-- Actual output counting over all intermediate labels: only one factor equal
to the intermediate-label count is paid. -/
theorem all_output_count {Index : Type*} {k : ℕ} {kap δ width : ℝ}
    {a : Index → Angle k kap} {fc sc : Index → Cell k → ℝ}
    (I : Finset Index) (S : ∀ i, Finset (LabeledPair (a i) δ width (fc i) (sc i)))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) :
    (((I.sigma S).image sampleOutput).card : ℝ) ≤
      4*boxConstant k ((k : ℝ)/2)*(I.card : ℝ)/δ := by
  have hsub : (I.sigma S).image sampleOutput ⊆
      I.biUnion (fun i => (S i).image (fun s => (s.pivotLabel,i))) := by
    intro f hf
    obtain ⟨⟨i,s⟩,hs,rfl⟩ := mem_image.mp hf
    obtain ⟨hi,hs⟩ := mem_sigma.mp hs
    exact mem_biUnion.mpr ⟨i,hi,mem_image.mpr ⟨s,hs,rfl⟩⟩
  have hcount (i) : (((S i).image (fun s => (s.pivotLabel,i))).card : ℝ) ≤
      4*boxConstant k ((k : ℝ)/2)/δ := by
    have himage : (S i).image (fun s => (s.pivotLabel,i)) =
        ((S i).image LabeledPair.pivotLabel).image (fun z => (z,i)) := by
      rw [image_image]
      rfl
    rw [himage,card_image_of_injective _ (fun z w heq => (Prod.mk.inj heq).1)]
    exact pivot_output_count (S i) hδ hδ1 hk
  have hcard : (((I.sigma S).image sampleOutput).card : ℝ) ≤
      ∑ i ∈ I, (((S i).image (fun s => (s.pivotLabel,i))).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans (card_biUnion_le)
  have hh := hcard.trans (sum_le_sum (fun i _ => hcount i))
  simp only [sum_const,nsmul_eq_mul] at hh
  convert hh using 1 <;> first | rfl | ring

/-- A complete output fixes exactly one intermediate index. Its sample count
is the corresponding one-angle endpoint fiber, or zero for an absent index. -/
theorem output_fiber_card {Index : Type*} {k : ℕ} {kap δ width : ℝ}
    {a : Index → Angle k kap} {fc sc : Index → Cell k → ℝ}
    (I : Finset Index) (S : ∀ i, Finset (LabeledPair (a i) δ width (fc i) (sc i)))
    (pivot : Cell k) (i : Index) :
    (((I.sigma S).filter (fun s => sampleOutput s = (pivot,i))).card) =
      if i ∈ I then ((S i).filter (fun s => s.pivotLabel = pivot)).card else 0 := by
  rw [filter_sigma,card_sigma]
  have hterm (j) : ((S j).filter (fun s => sampleOutput ⟨j,s⟩ = (pivot,i))).card =
      if j = i then ((S i).filter (fun s => s.pivotLabel = pivot)).card else 0 := by
    by_cases hji : j = i
    · subst j
      simp [sampleOutput]
    · simp [sampleOutput,hji]
  simp_rw [hterm]
  simp

/-- The geometric bound for every actual complete output fiber. The sample set
is a finite set of distinct endpoint-label triples, not a multiset of witnesses. -/
theorem all_output_fiber_count {Index : Type*} {k : ℕ} {kap δ width : ℝ}
    {a : Index → Angle k kap} {fc sc : Index → Cell k → ℝ}
    (I : Finset Index) (S : ∀ i, Finset (LabeledPair (a i) δ width (fc i) (sc i)))
    (f : Cell k × Index) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) (hk1 : kap ≤ 1) :
    (((I.sigma S).filter (fun s => sampleOutput s = f)).card : ℝ) ≤ fiberConstant k width/(kap*δ) := by
  rcases f with ⟨pivot,i⟩
  rw [output_fiber_card]
  split_ifs with hi
  · exact pivot_fiber_count (S i) pivot hδ hδ1 hk hk1
  · rw [Nat.cast_zero]
    have := (boxConstant_pos k width).le
    dsimp [fiberConstant]
    positivity


/-- The intermediate labels are actual original shading labels, so their count
can be replaced by that original shading's cardinality. -/
theorem all_output_count_of_subset {Index : Type*} {k : ℕ} {kap δ width : ℝ}
    {a : Index → Angle k kap} {fc sc : Index → Cell k → ℝ}
    (I Sfirst : Finset Index) (hI : I ⊆ Sfirst)
    (S : ∀ i, Finset (LabeledPair (a i) δ width (fc i) (sc i)))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) :
    (((I.sigma S).image sampleOutput).card : ℝ) ≤
      4*boxConstant k ((k : ℝ)/2)*(Sfirst.card : ℝ)/δ := by
  have hc : (I.card : ℝ) ≤ Sfirst.card := by exact_mod_cast card_le_card hI
  have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*boxConstant k ((k : ℝ)/2) by
    have := (boxConstant_pos k ((k : ℝ)/2)).le
    positivity)
  exact (all_output_count I S hδ hδ1 hk).trans (div_le_div_of_nonneg_right hh hδ.le)

/-- An actual integer fiber budget for the finite dyadic selection module.
It is derived from geometric grid packing, not supplied as a count premise. -/
theorem integer_output_fiber_bound {Index : Type*} {k : ℕ} {kap δ width : ℝ}
    {a : Index → Angle k kap} {fc sc : Index → Cell k → ℝ}
    (I : Finset Index) (S : ∀ i, Finset (LabeledPair (a i) δ width (fc i) (sc i)))
    (f : Cell k × Index) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kap) (hk1 : kap ≤ 1) :
    ((I.sigma S).filter (fun s => sampleOutput s = f)).card ≤
      Nat.ceil (fiberConstant k width/(kap*δ)) := by
  have hh := (all_output_fiber_count I S f hδ hδ1 hk hk1).trans
    (Nat.le_ceil (fiberConstant k width/(kap*δ)))
  exact_mod_cast hh

end
end KakeyaFormal.PivotOutputCount

#print axioms KakeyaFormal.PivotOutputCount.LabeledPair.labels_injective
#print axioms KakeyaFormal.PivotOutputCount.pivot_output_count
#print axioms KakeyaFormal.PivotOutputCount.same_first_second_gap
#print axioms KakeyaFormal.PivotOutputCount.pivot_fiber_count
#print axioms KakeyaFormal.PivotOutputCount.sample_labels_injective
#print axioms KakeyaFormal.PivotOutputCount.all_output_count
#print axioms KakeyaFormal.PivotOutputCount.output_fiber_card
#print axioms KakeyaFormal.PivotOutputCount.all_output_fiber_count
#print axioms KakeyaFormal.PivotOutputCount.integer_output_fiber_bound
