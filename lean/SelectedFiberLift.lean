import PivotOutputCount
import LiftSegments

/-! Actual selected endpoint-pair fibers populate grid-rounded lifted graphs.
The cell multiplicity is derived from endpoint recovery and linear longitudinal
grid counts, preserving the distinction between labels and projection points. -/
namespace KakeyaFormal.SelectedFiberLift
open Finset PivotOutputCount PivotWitnesses EuclideanSplit LiftSegments
open scoped BigOperators
noncomputable section
open Classical

variable {k : ℕ} {kap δ width : ℝ} {a : Angle k kap} {fc sc : Cell k → ℝ}

/-- Exact first-endpoint recovery from the legal pivot coefficient. -/
theorem endpoint_recovery (p : Endpoints a) (hk : 0 < kap) :
    p.firstCoord = a.intermediate*p.secondCoord/(p.secondCoord-p.coefficient) := by
  have hb : 0 < p.firstCoord := by linarith [p.gap,a.intermediate_lower]
  have hden : kap^2 ≤ |p.secondCoord-p.coefficient| := by
    simpa [Endpoints.coefficient] using
      (KakeyaAudit.TubeGeometry.legal_pivot_coefficient_bounds hk a.intermediate_lower
        p.gap p.first_upper p.second_lower).2
  have hden0 : p.secondCoord-p.coefficient ≠ 0 := by
    intro hh
    rw [hh,abs_zero] at hden
    nlinarith [sq_pos_of_pos hk]
  apply (eq_div_iff hden0).mpr
  dsimp [Endpoints.coefficient]
  field_simp
  ring

/-- Two-input continuity of endpoint recovery, with both true denominators
bounded below. The inverse-fourth-power loss is explicit. -/
theorem recovery_difference {aa c c' u u' r ec eu : ℝ}
    (ha : |aa| ≤ 1) (hc : |c'| ≤ 1) (hr : 0 < r)
    (hden : r ≤ |c-u|) (hden' : r ≤ |c'-u'|)
    (hcdiff : |c-c'| ≤ ec) (hudiff : |u-u'| ≤ eu) :
    |aa*c/(c-u)-aa*c'/(c'-u')| ≤ ec/r+(ec+eu)/r^2 := by
  have hec : 0 ≤ ec := (abs_nonneg _).trans hcdiff
  have heu : 0 ≤ eu := (abs_nonneg _).trans hudiff
  have hdenDiff : |(c'-u')-(c-u)| ≤ ec+eu := by
    have hid : (c'-u')-(c-u) = (c'-c)+(u-u') := by ring
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add (by simpa only [abs_sub_comm] using hcdiff) hudiff)
  have hquot := KakeyaAudit.TubeGeometry.quotient_perturbation_bound
    (c := c') hr hr hden hden' hdenDiff
  have hsecond : |c'/(c-u)-c'/(c'-u')| ≤ (ec+eu)/r^2 := by
    rw [abs_sub_comm]
    have hh : |c'| *(ec+eu)/(r*r) ≤ (ec+eu)/r^2 := by
      rw [pow_two]
      apply div_le_div_of_nonneg_right _ (mul_pos hr hr).le
      nlinarith
    exact hquot.trans hh
  have hfirst : |c/(c-u)-c'/(c-u)| ≤ ec/r := by
    rw [← sub_div,abs_div]
    exact div_le_div₀ hec hcdiff hr hden
  have htri := abs_add_le (c/(c-u)-c'/(c-u)) (c'/(c-u)-c'/(c'-u'))
  have hid : (c/(c-u)-c'/(c-u))+(c'/(c-u)-c'/(c'-u')) = c/(c-u)-c'/(c'-u') := by ring
  rw [hid] at htri
  have htotal := htri.trans (add_le_add hfirst hsecond)
  have hmul := mul_le_mul_of_nonneg_left htotal (abs_nonneg aa)
  have hright : |aa| *(ec/r+(ec+eu)/r^2) ≤ ec/r+(ec+eu)/r^2 := by
    have hh : 0 ≤ ec/r+(ec+eu)/r^2 := by positivity
    nlinarith
  calc
    _ = |aa| *|c/(c-u)-c'/(c'-u')| := by rw [← abs_mul]; congr 1; ring
    _ ≤ _ := hmul.trans hright

/-- The exact lifted point uses the same reference coefficient for the entire
one-angle fiber. The distinguished coordinate is first, matching graphPoint. -/
def liftedPoint (reference s : LabeledPair a δ width fc sc) : Space (k+1) :=
  cons (s.endpoints.secondCoord/reference.endpoints.coefficient) s.endpoints.secondPoint

/-- The actual centered half-open grid label of the lifted point. -/
def liftedCell (reference s : LabeledPair a δ width fc sc) : Cell (k+1) :=
  GridCells.label δ (liftedPoint reference s)

/-- Every exact lifted point lies on its actual fixed graph line. -/
theorem liftedPoint_on_graph (reference s : LabeledPair a δ width fc sc) (hk : 0 < kap) :
    liftedPoint reference s = graphPoint a.vertex (reference.endpoints.coefficient • a.second)
      (s.endpoints.secondCoord/reference.endpoints.coefficient) := by
  have hu : reference.endpoints.coefficient ≠ 0 := by
    intro hh
    have hlo := reference.endpoints.coefficient_lower hk
    rw [hh,abs_zero] at hlo
    nlinarith [sq_pos_of_pos hk]
  unfold liftedPoint graphPoint Endpoints.secondPoint
  congr 1
  rw [smul_smul,div_mul_cancel₀ _ hu]

/-- Actual cell rounding supplies the graph-incidence width. -/
theorem liftedCell_graph_incidence (reference s : LabeledPair a δ width fc sc)
    (hδ : 0 < δ) (hk : 0 < kap) :
    dist (cellCenter δ (liftedCell reference s))
      (graphPoint a.vertex (reference.endpoints.coefficient • a.second)
        (s.endpoints.secondCoord/reference.endpoints.coefficient)) ≤ ((k : ℝ)+1)*δ/2 := by
  have hh := GridCells.cell_center_distance (GridCells.gridCell_covers hδ (liftedPoint reference s))
  change dist (liftedPoint reference s) (cellCenter δ (liftedCell reference s)) ≤ _ at hh
  rw [← liftedPoint_on_graph reference s hk]
  simpa only [Nat.cast_add,Nat.cast_one,dist_comm] using hh

/-- Coincidence of full lifted grid cells confines the second projection points;
the horizontal coordinate projection is an actual Euclidean contraction. -/
theorem same_lift_second_gap (reference s t : LabeledPair a δ width fc sc)
    (hδ : 0 < δ) (hcell : liftedCell reference s = liftedCell reference t) :
    |sc s.secondLabel-sc t.secondLabel| ≤ ((k : ℝ)+1)*δ := by
  have hs := GridCells.cell_center_distance (GridCells.gridCell_covers hδ (liftedPoint reference s))
  have ht := GridCells.cell_center_distance (GridCells.gridCell_covers hδ (liftedPoint reference t))
  change dist (liftedPoint reference s) (cellCenter δ (liftedCell reference s)) ≤ _ at hs
  change dist (liftedPoint reference t) (cellCenter δ (liftedCell reference t)) ≤ _ at ht
  rw [hcell] at hs
  have htri := dist_triangle (liftedPoint reference s) (cellCenter δ (liftedCell reference t)) (liftedPoint reference t)
  rw [dist_comm (cellCenter δ (liftedCell reference t))] at htri
  have hdist : dist (liftedPoint reference s) (liftedPoint reference t) ≤ ((k : ℝ)+1)*δ := by
    push_cast at hs ht
    linarith
  have htail := tail_norm_le (liftedPoint reference s-liftedPoint reference t)
  rw [tail_sub] at htail
  simp only [liftedPoint,tail_cons] at htail
  have hid : s.endpoints.secondPoint-t.endpoints.secondPoint =
      (sc s.secondLabel-sc t.secondLabel) • a.second := by
    dsimp [Endpoints.secondPoint,LabeledPair.endpoints]
    module
  rw [hid,norm_smul,Real.norm_eq_abs,a.second_unit,mul_one] at htail
  exact htail.trans hdist

/-- Two actual sample pairs in one original pivot fiber and one lifted cell
have first projection coordinates in an inverse-fourth-power short interval. -/
theorem same_lift_first_gap (reference s t : LabeledPair a δ width fc sc)
    (hδ : 0 < δ) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hpivot : s.pivotLabel = t.pivotLabel) (hcell : liftedCell reference s = liftedCell reference t) :
    |fc s.firstLabel-fc t.firstLabel| ≤ 4*((k : ℝ)+1)*δ/kap^4 := by
  have ha0 : 0 < a.intermediate := hk.trans_le a.intermediate_lower
  have ha : |a.intermediate| ≤ 1 := by
    rw [abs_of_pos ha0]
    linarith [s.gap,s.first_upper]
  have hden (p : Endpoints a) : kap^2 ≤ |p.secondCoord-p.coefficient| := by
    simpa [Endpoints.coefficient] using
      (KakeyaAudit.TubeGeometry.legal_pivot_coefficient_bounds hk a.intermediate_lower
        p.gap p.first_upper p.second_lower).2
  have hc := same_lift_second_gap reference s t hδ hcell
  have hu := rounded_coefficient_gap s t hδ hpivot
  have hh := recovery_difference (c := s.endpoints.secondCoord) (c' := t.endpoints.secondCoord) ha t.second_upper (sq_pos_of_pos hk) (hden s.endpoints) (hden t.endpoints) hc hu
  rw [← endpoint_recovery s.endpoints hk,← endpoint_recovery t.endpoints hk] at hh
  change |fc s.firstLabel-fc t.firstLabel| ≤ _ at hh
  have hkpow : kap^4 ≤ kap^2 := by
    have h2 : kap^2 ≤ 1 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right h2 (sq_nonneg kap)
    nlinarith
  have hscale : (((k : ℝ)+1)*δ)/kap^2 ≤ (((k : ℝ)+1)*δ)/kap^4 :=
    div_le_div_of_nonneg_left (by positivity) (pow_pos hk _) hkpow
  have hright : (((k : ℝ)+1)*δ)/kap^2+(((k : ℝ)+1)*δ+(k : ℝ)*δ)/(kap^2)^2 ≤
      4*((k : ℝ)+1)*δ/kap^4 := by
    have hid : (kap^2)^2 = kap^4 := by ring
    rw [hid]
    have hb : (((k : ℝ)+1)*δ+(k : ℝ)*δ) ≤ 3*((k : ℝ)+1)*δ := by
      have hkn : (0:ℝ) ≤ k := Nat.cast_nonneg _
      nlinarith
    have hb' := div_le_div_of_nonneg_right hb (pow_pos hk 4).le
    calc
      _ ≤ (((k : ℝ)+1)*δ)/kap^4+3*((k : ℝ)+1)*δ/kap^4 := add_le_add hscale hb'
      _ = _ := by ring
  exact hh.trans hright


/-- Actual label count for a coordinate interval, obtained from the physical
axis and the finite grid theorem. -/
theorem projected_label_count (T : UnitTube k) (cells : Finset (Cell k))
    (coord : Cell k → ℝ) {center rad : ℝ} (hδ : 0 < δ) (hrad : 0 < rad)
    (hclose : ∀ z ∈ cells, dist (cellCenter δ z) (T.axisPoint (coord z)) ≤ width*δ)
    (hgap : ∀ z ∈ cells, |coord z-center| ≤ rad) :
    (cells.card : ℝ) ≤ boxConstant k width*(2*rad/δ+2) := by
  have hh := interval_grid_count T hδ (show center-rad < center+rad by linarith) cells (by
    intro z hz
    obtain ⟨hlo,hhi⟩ := abs_le.mp (hgap z hz)
    exact ⟨coord z,⟨by linarith,by linarith⟩,hclose z hz⟩)
  convert hh using 1
  ring

/-- Dimension and projection-width constant, with no dependence on scale,
kappa, sample count or selected reference. -/
def multiplicityConstant (k : ℕ) (width : ℝ) : ℝ :=
  (8*(k : ℝ)+10)*(2*(k : ℝ)+4)*(boxConstant k width)^2

theorem multiplicityConstant_pos (k : ℕ) (width : ℝ) : 0 < multiplicityConstant k width := by
  have := boxConstant_pos k width
  dsimp [multiplicityConstant]
  positivity

/-- A finite set of distinct endpoint pairs sharing one original pivot and one
lifted cell has the required inverse-fourth-power multiplicity bound. -/
theorem single_lift_cell_count (reference : LabeledPair a δ width fc sc)
    (S : Finset (LabeledPair a δ width fc sc)) (pivot : Cell k) (cell : Cell (k+1))
    (hδ : 0 < δ) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hpivot : ∀ s ∈ S, s.pivotLabel = pivot)
    (hcell : ∀ s ∈ S, liftedCell reference s = cell) :
    (S.card : ℝ) ≤ multiplicityConstant k width/kap^4 := by
  by_cases hS : S.Nonempty
  · obtain ⟨s0,hs0⟩ := hS
    let T1 : UnitTube k := ⟨a.vertex,a.first,a.first_unit⟩
    let T2 : UnitTube k := ⟨a.vertex,a.second,a.second_unit⟩
    let rad1 := 4*((k : ℝ)+1)*δ/kap^4
    let rad2 := ((k : ℝ)+1)*δ
    have hrad1 : 0 < rad1 := by dsimp [rad1]; positivity
    have hrad2 : 0 < rad2 := by dsimp [rad2]; positivity
    have hfirst := projected_label_count T1 (S.image LabeledPair.firstLabel) fc
      (center := fc s0.firstLabel) hδ hrad1
      (by
        intro z hz
        obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
        exact s.first_close)
      (by
        intro z hz
        obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
        exact same_lift_first_gap reference s s0 hδ hk hk1
          ((hpivot s hs).trans (hpivot s0 hs0).symm) ((hcell s hs).trans (hcell s0 hs0).symm))
    have hsecond := projected_label_count T2 (S.image LabeledPair.secondLabel) sc
      (center := sc s0.secondLabel) hδ hrad2
      (by
        intro z hz
        obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
        exact s.second_close)
      (by
        intro z hz
        obtain ⟨s,hs,rfl⟩ := mem_image.mp hz
        exact same_lift_second_gap reference s s0 hδ ((hcell s hs).trans (hcell s0 hs0).symm))
    have hid1 : 2*rad1/δ = 8*((k : ℝ)+1)/kap^4 := by dsimp [rad1]; field_simp; ring
    have hid2 : 2*rad2/δ+2 = 2*(k : ℝ)+4 := by dsimp [rad2]; field_simp; ring
    have hk4 : kap^4 ≤ 1 := pow_le_one₀ hk.le hk1
    have hfactor : 8*((k : ℝ)+1)/kap^4+2 ≤ (8*(k : ℝ)+10)/kap^4 := by
      apply (le_div_iff₀ (pow_pos hk 4)).mpr
      rw [add_mul,div_mul_cancel₀ _ (pow_ne_zero _ hk.ne')]
      nlinarith
    rw [hid1] at hfirst
    rw [hid2] at hsecond
    have hfirst' := hfirst.trans (mul_le_mul_of_nonneg_left hfactor (boxConstant_pos k width).le)
    have hpairs : S.card ≤ (S.image LabeledPair.firstLabel).card*(S.image LabeledPair.secondLabel).card := by
      have hh := card_le_card_of_injOn (fun s : LabeledPair a δ width fc sc => (s.firstLabel,s.secondLabel))
        (t := (S.image LabeledPair.firstLabel).product (S.image LabeledPair.secondLabel))
        (by
          intro s hs
          exact mem_product.mpr ⟨mem_image.mpr ⟨s,hs,rfl⟩,mem_image.mpr ⟨s,hs,rfl⟩⟩)
        LabeledPair.labels_injective.injOn
      have hcard : ((S.image LabeledPair.firstLabel).product (S.image LabeledPair.secondLabel)).card =
          (S.image LabeledPair.firstLabel).card*(S.image LabeledPair.secondLabel).card :=
        Multiset.card_product _ _
      exact hh.trans_eq hcard
    have hpairsR : (S.card : ℝ) ≤
        ((S.image LabeledPair.firstLabel).card : ℝ)*((S.image LabeledPair.secondLabel).card : ℝ) := by
      exact_mod_cast hpairs
    have hmul := mul_le_mul hfirst' hsecond (Nat.cast_nonneg _) (by
      have := (boxConstant_pos k width).le
      positivity)
    have hh := hpairsR.trans hmul
    convert hh using 1 <;> first | rfl | (dsimp [multiplicityConstant]; ring)
  · have hz : S = ∅ := not_nonempty_iff_eq_empty.mp hS
    rw [hz,card_empty,Nat.cast_zero]
    exact div_nonneg (multiplicityConstant_pos k width).le (pow_pos hk 4).le

/-- The finite image is the actual set of occupied lifted cell labels. -/
def liftedCells (reference : LabeledPair a δ width fc sc)
    (S : Finset (LabeledPair a δ width fc sc)) : Finset (Cell (k+1)) := S.image (liftedCell reference)

/-- Every actual cell fiber satisfies the derived geometric multiplicity bound. -/
theorem lifted_cell_multiplicity (reference : LabeledPair a δ width fc sc)
    (S : Finset (LabeledPair a δ width fc sc)) (pivot : Cell k)
    (hδ : 0 < δ) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hpivot : ∀ s ∈ S, s.pivotLabel = pivot) (cell : Cell (k+1)) :
    ((S.filter (fun s => liftedCell reference s = cell)).card : ℝ) ≤ multiplicityConstant k width/kap^4 := by
  apply single_lift_cell_count reference _ pivot cell hδ hk hk1
  · intro s hs
    exact hpivot s (mem_filter.mp hs).1
  · intro s hs
    exact (mem_filter.mp hs).2

/-- Selected samples genuinely populate at least c*kappa^4 times their number
of distinct lifted cells. No multiplicity or projection injectivity is assumed. -/
theorem lifted_population (reference : LabeledPair a δ width fc sc)
    (S : Finset (LabeledPair a δ width fc sc)) (pivot : Cell k)
    (hδ : 0 < δ) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hpivot : ∀ s ∈ S, s.pivotLabel = pivot) :
    kap^4*(S.card : ℝ)/multiplicityConstant k width ≤ ((liftedCells reference S).card : ℝ) := by
  have hsum : (S.card : ℝ) = ∑ cell ∈ liftedCells reference S,
      ((S.filter (fun s => liftedCell reference s = cell)).card : ℝ) := by
    have hh := sum_fiberwise_of_maps_to (s := S) (t := liftedCells reference S)
      (g := liftedCell reference) (fun s hs => mem_image.mpr ⟨s,hs,rfl⟩) (fun _ => (1:ℕ))
    simp only [sum_const,nsmul_eq_mul,mul_one] at hh
    exact_mod_cast hh.symm
  have hh := sum_le_sum (s := liftedCells reference S)
    (fun cell _ => lifted_cell_multiplicity reference S pivot hδ hk hk1 hpivot cell)
  simp only [sum_const,nsmul_eq_mul,← hsum] at hh
  have hmult := mul_le_mul_of_nonneg_right hh (pow_pos hk 4).le
  rw [mul_assoc,div_mul_cancel₀ _ (pow_ne_zero _ hk.ne')] at hmult
  apply (div_le_iff₀ (multiplicityConstant_pos k width)).mpr
  simpa only [mul_comm] using hmult

end
end KakeyaFormal.SelectedFiberLift

#print axioms KakeyaFormal.SelectedFiberLift.endpoint_recovery
#print axioms KakeyaFormal.SelectedFiberLift.recovery_difference
#print axioms KakeyaFormal.SelectedFiberLift.liftedPoint_on_graph
#print axioms KakeyaFormal.SelectedFiberLift.same_lift_first_gap
#print axioms KakeyaFormal.SelectedFiberLift.single_lift_cell_count
#print axioms KakeyaFormal.SelectedFiberLift.lifted_cell_multiplicity
#print axioms KakeyaFormal.SelectedFiberLift.lifted_population
