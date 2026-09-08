import LiftGraph
import OccupancySelection

/-! Actual unit-length covers of graph segments, including slab-boundary errors.
The number of unit pieces and their geometry depend only on the bounded slopes. -/
namespace KakeyaFormal.LiftSegments
open EuclideanSplit LiftGraph Set
noncomputable section

/-- A graph line in a slab after translation of its distinguished coordinate. -/
def graphPoint {k : ℕ} (a v : Space k) (t : ℝ) : Space (k+1) := cons t (a+t • v)

lemma graphPoint_formula {k : ℕ} (a v : Space k) (t : ℝ) :
    graphPoint a v t = cons 0 a+t • cons 1 v := by
  ext i
  cases i using Fin.cases <;> simp [graphPoint,cons]

lemma graphPoint_distance {k : ℕ} (a v : Space k) (s t : ℝ) :
    dist (graphPoint a v s) (graphPoint a v t) = |s-t| *‖cons 1 v‖ := by
  rw [graphPoint_formula,graphPoint_formula,dist_add_left,dist_eq_norm,← sub_smul,
    norm_smul,Real.norm_eq_abs]

/-- A genuine unit tube, directed along the normalized graph direction. -/
def graphTube {k : ℕ} (a v : Space k) (j : ℕ) : UnitTube (k+1) where
  base := cons 0 a+(j:ℝ) • graphDirection v
  direction := graphDirection v
  unit_direction := graphDirection_unit v

/-- A graph slab of parameter length one is covered by at most ceil(1+V)+1
actual Euclidean unit segments, with no comparable-length convention assumed. -/
theorem graph_unit_cover {k : ℕ} (a v : Space k) {V t : ℝ}
    (hv : ‖v‖ ≤ V) (ht : t ∈ Icc (0:ℝ) 1) :
    ∃ j ≤ Nat.ceil (1+V), ∃ s ∈ Icc (0:ℝ) 1,
      graphPoint a v t = (graphTube a v j).axisPoint s := by
  let n := ‖cons 1 v‖
  let j := Nat.floor (t*n)
  have hn : 0 < n := lt_of_lt_of_le zero_lt_one (graph_norm_ge_one v)
  have hnL : n ≤ 1+V := (graph_norm_upper v).trans (by linarith)
  have htn : 0 ≤ t*n := mul_nonneg ht.1 hn.le
  have hjlo : (j:ℝ) ≤ t*n := Nat.floor_le htn
  have hjhi : t*n < (j:ℝ)+1 := Nat.lt_floor_add_one _
  have hjbound : j ≤ Nat.ceil (1+V) := by
    have hceil := Nat.le_ceil (1+V)
    have hh : (j:ℝ) ≤ (Nat.ceil (1+V):ℝ) := by nlinarith [ht.2]
    exact_mod_cast hh
  refine ⟨j,hjbound,t*n-j,⟨by linarith,by linarith⟩,?_⟩
  rw [graphPoint_formula]
  change cons 0 a+t • cons 1 v = cons 0 a+(j:ℝ) • graphDirection v+(t*n-j) • graphDirection v
  have hrecover : n • graphDirection v = cons 1 v := by
    rw [graphDirection,PivotDirections.unitize,smul_smul]
    change (n*n⁻¹) • cons 1 v = cons 1 v
    rw [mul_inv_cancel₀ hn.ne',one_smul]
  rw [← hrecover,smul_smul]
  module

/-- Clamping a slab-boundary parameter only enlarges physical width by the fixed
slope bound times its parameter error. -/
theorem graph_slab_clamp {k : ℕ} (a v : Space k) {V t eta : ℝ}
    (hv : ‖v‖ ≤ V) (heta : 0 ≤ eta) (ht : t ∈ Icc (-eta) (1+eta)) :
    ∃ s ∈ Icc (0:ℝ) 1,
      dist (graphPoint a v t) (graphPoint a v s) ≤ eta*(1+V) := by
  let s := max 0 (min 1 t)
  have hs : s ∈ Icc (0:ℝ) 1 := ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩
  have hts : |t-s| ≤ eta := by
    by_cases ht0 : t ≤ 0
    · simp only [s,min_eq_right (by linarith : t ≤ 1),max_eq_left ht0]
      rw [sub_zero,abs_of_nonpos ht0]
      linarith [ht.1]
    · by_cases ht1 : t ≤ 1
      · simp [s,min_eq_right ht1,max_eq_right (le_of_not_ge ht0),heta]
      · simp only [s,min_eq_left (le_of_not_ge ht1),max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
        rw [abs_of_nonneg (by linarith : 0 ≤ t-1)]
        linarith [ht.2]
  refine ⟨s,hs,?_⟩
  rw [graphPoint_distance]
  have hn : ‖cons 1 v‖ ≤ 1+V := (graph_norm_upper v).trans (by linarith)
  exact mul_le_mul hts hn (norm_nonneg _) heta

/-- Every actual thick graph incidence near a possibly crossing slab boundary
lies near one of the actual unit segments with a uniform enlarged width. -/
theorem thick_graph_unit_cover {k : ℕ} (a v : Space k) (x : Space (k+1))
    {V t width b δ : ℝ} (hv : ‖v‖ ≤ V) (hb : 0 ≤ b) (hδ : 0 ≤ δ)
    (ht : t ∈ Icc (-(b*δ)) (1+b*δ))
    (hx : dist x (graphPoint a v t) ≤ width*δ) :
    ∃ j ≤ Nat.ceil (1+V), ∃ s ∈ Icc (0:ℝ) 1,
      dist x ((graphTube a v j).axisPoint s) ≤ (width+b*(1+V))*δ := by
  obtain ⟨u,hu,hclamp⟩ := graph_slab_clamp a v hv (mul_nonneg hb hδ) ht
  obtain ⟨j,hj,s,hs,heq⟩ := graph_unit_cover a v hv hu
  refine ⟨j,hj,s,hs,?_⟩
  have htri := dist_triangle x (graphPoint a v t) (graphPoint a v u)
  rw [heq] at htri hclamp
  nlinarith

/-- A single retained point in the fixed horizontal region controls the graph
intercept in its translated slab. -/
theorem graph_base_from_incidence {k : ℕ} (a v : Space k) (x : Space (k+1))
    {V R t err : ℝ} (hv : ‖v‖ ≤ V) (ht : t ∈ Icc (0:ℝ) 1)
    (hx : ‖x‖ ≤ R) (herr : dist x (graphPoint a v t) ≤ err) :
    ‖a‖ ≤ R+(1+V)+err := by
  have hn := (graph_norm_upper v).trans (by linarith : 1+‖v‖ ≤ 1+V)
  have hdist : dist (graphPoint a v t) (cons 0 a) ≤ 1+V := by
    rw [graphPoint_formula,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    nlinarith [norm_nonneg (cons 1 v),ht.2]
  have htri := dist_triangle (cons 0 a) (graphPoint a v t) x
  have hxtri := norm_le_norm_add_norm_sub x (cons 0 a)
  rw [norm_cons_zero,← dist_eq_norm,dist_comm x (cons 0 a)] at hxtri
  rw [dist_comm (cons 0 a) (graphPoint a v t),dist_comm (graphPoint a v t) x] at htri
  linarith

/-- Every unit piece is in a fixed bounded region; the slab index is absent. -/
theorem graphTube_base_bound {k : ℕ} (a v : Space k) {R V : ℝ} {j : ℕ}
    (ha : ‖a‖ ≤ R) (hV : 0 ≤ V) (hj : j ≤ Nat.ceil (1+V)) :
    ‖(graphTube a v j).base‖ ≤ R+V+2 := by
  have hjR : (j:ℝ) ≤ (Nat.ceil (1+V):ℝ) := by exact_mod_cast hj
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 1+V by positivity)
  have h := norm_add_le (cons 0 a) ((j:ℝ) • graphDirection v)
  rw [norm_cons_zero,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg j),graphDirection_unit,mul_one] at h
  change ‖cons 0 a+(j:ℝ) • graphDirection v‖ ≤ _
  linarith


/-- Actual finite graph shadings are assigned to unit pieces separately on each
line. All lines remain, union support decreases, and the per-line count loses
only the fixed number of unit pieces. -/
theorem normalize_graph_family {M k : ℕ}
    (a v : Fin M → Space k) (shading : Fin M → Finset (Cell (k+1)))
    {δ V R width b : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V) (hb : 0 ≤ b)
    (hbase : ∀ i, ‖a i‖ ≤ R) (hslope : ∀ i, ‖v i‖ ≤ V)
    (hpoint : ∀ i q, q ∈ shading i → ∃ t ∈ Icc (-(b*δ)) (1+b*δ),
      dist (cellCenter δ q) (graphPoint (a i) (v i) t) ≤ width*δ) :
    ∃ G : TubeFamily (k+1) M,
      (∀ i, (G.tube i).direction = graphDirection (v i)) ∧
      (∀ i, G.shade i ⊆ shading i) ∧
      (∀ i, ((shading i).card:ℝ)/(Nat.ceil (1+V)+1:ℕ) ≤ ((G.shade i).card:ℝ)) ∧
      G.Admissible (width+b*(1+V)) δ ∧ G.Bounded (R+V+2) ∧
      G.unionCells ⊆ Finset.univ.biUnion shading := by
  classical
  let J := Nat.ceil (1+V)+1
  have hJ : 0 < J := Nat.succ_pos _
  have hex (i : Fin M) (q : Cell (k+1)) (hq : q ∈ shading i) :
      ∃ j : Fin J, ∃ s ∈ Icc (0:ℝ) 1,
        dist (cellCenter δ q) ((graphTube (a i) (v i) j.val).axisPoint s) ≤
          (width+b*(1+V))*δ := by
    obtain ⟨t,ht,hqt⟩ := hpoint i q hq
    obtain ⟨j,hj,s,hs,hqs⟩ := thick_graph_unit_cover (a i) (v i) (cellCenter δ q)
      (hslope i) hb hδ.le ht hqt
    exact ⟨⟨j,by dsimp [J]; omega⟩,s,hs,hqs⟩
  let label (i : Fin M) (q : Cell (k+1)) : Fin J :=
    if hq : q ∈ shading i then Classical.choose (hex i q hq) else ⟨0,hJ⟩
  have hlabel (i : Fin M) (q : Cell (k+1)) (hq : q ∈ shading i) :
      ∃ s ∈ Icc (0:ℝ) 1,
        dist (cellCenter δ q) ((graphTube (a i) (v i) (label i q).val).axisPoint s) ≤
          (width+b*(1+V))*δ := by
    simpa only [label,dif_pos hq] using Classical.choose_spec (hex i q hq)
  have hsel (i : Fin M) : ∃ j : Fin J,
      ((shading i).card:ℝ)/(J:ℝ) ≤
        (((shading i).filter (fun q => label i q = j)).card:ℝ) := by
    simpa using OccupancySelection.weighted_class_selection (shading i) (fun _ => (1:ℝ)) hJ (label i)
  choose chosen hchosen using hsel
  let G : TubeFamily (k+1) M := {
    tube := fun i => graphTube (a i) (v i) (chosen i).val
    shade := fun i => (shading i).filter (fun q => label i q = chosen i)
  }
  have hsub : ∀ i, G.shade i ⊆ shading i := fun i => Finset.filter_subset _ _
  refine ⟨G,fun _ => rfl,hsub,hchosen,?_,?_,?_⟩
  · intro i q hq
    have hmem := (Finset.mem_filter.mp hq).1
    have heq := (Finset.mem_filter.mp hq).2
    obtain ⟨s,hs,hqs⟩ := hlabel i q hmem
    rw [heq] at hqs
    exact ⟨s,hs,hqs⟩
  · intro i
    apply graphTube_base_bound (a i) (v i) (hbase i) hV
    have hj := (chosen i).isLt
    dsimp [J] at hj
    omega
  · exact Finset.biUnion_mono (fun i _ => hsub i)

end
end KakeyaFormal.LiftSegments
