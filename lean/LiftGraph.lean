import EuclideanSplit
import PivotDirections

/-! The genuine normalized graph-direction chart for lifted slopes. Its constants
depend only on the fixed slope range and do not depend on the pivot conditioning. -/
namespace KakeyaFormal.LiftGraph
open EuclideanSplit PivotDirections ProjectiveGeometry
noncomputable section
open Classical

/-- The distinguished graph coordinate comes first; this is an orthogonal
permutation of the manuscript's last-coordinate convention. -/
def graphDirection {k : ℕ} (v : Space k) : Space (k+1) := unitize (cons 1 v)

lemma graph_norm_ge_one {k : ℕ} (v : Space k) : 1 ≤ ‖cons 1 v‖ := by
  have h := norm_sq_split (cons 1 v)
  simp only [head_cons,tail_cons,one_pow] at h
  nlinarith [norm_nonneg (cons 1 v), sq_nonneg ‖v‖]

lemma graph_nonzero {k : ℕ} (v : Space k) : cons 1 v ≠ 0 := by
  intro h
  have hh := graph_norm_ge_one v
  simp only [h,norm_zero] at hh
  norm_num at hh

lemma graph_norm_upper {k : ℕ} (v : Space k) : ‖cons 1 v‖ ≤ 1+‖v‖ := by
  have h := norm_sq_split (cons 1 v)
  simp only [head_cons,tail_cons,one_pow] at h
  nlinarith [norm_nonneg (cons 1 v), norm_nonneg v]

@[simp] theorem graphDirection_unit {k : ℕ} (v : Space k) : ‖graphDirection v‖ = 1 :=
  unitize_unit _ (graph_nonzero v)

@[simp] theorem graphDirection_head {k : ℕ} (v : Space k) :
    head (graphDirection v) = ‖cons 1 v‖⁻¹ := by simp [graphDirection,unitize]

@[simp] theorem graphDirection_tail {k : ℕ} (v : Space k) :
    tail (graphDirection v) = ‖cons 1 v‖⁻¹ • v := by simp [graphDirection,unitize]

lemma graphDirection_recover {k : ℕ} (v : Space k) :
    ‖cons 1 v‖ • tail (graphDirection v) = v := by
  rw [graphDirection_tail,smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (graph_nonzero v)),one_smul]

lemma head_abs_le_norm {k : ℕ} (x : Space (k+1)) : |head x| ≤ ‖x‖ := by
  have h := norm_sq_split x
  nlinarith [sq_nonneg ‖tail x‖,norm_nonneg x,abs_nonneg (head x),sq_abs (head x)]

/-- Forward Lipschitz estimate, independent of any slope bound. -/
theorem graphDirection_forward {k : ℕ} (v w : Space k) :
    projectiveDistance (graphDirection v) (graphDirection w) ≤ 2*‖v-w‖ := by
  have hh := unitize_perturbation (cons 1 v) (cons 1 w) (graph_nonzero v) (graph_nonzero w)
  have heq : cons 1 v-cons 1 w = cons 0 (v-w) := by
    ext i
    cases i using Fin.cases <;> simp [cons]
  rw [heq,norm_cons_zero] at hh
  have hdiv : 2*‖v-w‖/‖cons 1 w‖ ≤ 2*‖v-w‖ :=
    (div_le_self (by positivity) (graph_norm_ge_one w))
  exact (projective_le_chord _ _).trans (hh.trans hdiv)

/-- Normalized graph vectors in a bounded slope range determine their slopes
with a uniform inverse Lipschitz bound for the ordinary chord. -/
theorem graphDirection_chord_inverse {k : ℕ} (v w : Space k) {V : ℝ}
    (hV : 0 ≤ V) (hv : ‖v‖ ≤ V) (hw : ‖w‖ ≤ V) :
    ‖v-w‖ ≤ 2*(1+V)^2 * ‖graphDirection v-graphDirection w‖ := by
  let nv := ‖cons 1 v‖
  let nw := ‖cons 1 w‖
  let e := ‖graphDirection v-graphDirection w‖
  have hnv : 0 < nv := lt_of_lt_of_le zero_lt_one (graph_norm_ge_one v)
  have hnw : 0 < nw := lt_of_lt_of_le zero_lt_one (graph_norm_ge_one w)
  have hnvL : nv ≤ 1+V := (graph_norm_upper v).trans (by linarith)
  have hnwL : nw ≤ 1+V := (graph_norm_upper w).trans (by linarith)
  have hhead : |nv⁻¹-nw⁻¹| ≤ e := by
    simpa only [head_sub,graphDirection_head] using
      head_abs_le_norm (graphDirection v-graphDirection w)
  have hid : |nv-nw| = nv*nw*|nv⁻¹-nw⁻¹| := by
    have hi : nv*nw*(nv⁻¹-nw⁻¹) = nw-nv := by field_simp
    calc
      _ = |nv*nw*(nv⁻¹-nw⁻¹)| := by rw [hi,abs_sub_comm]
      _ = _ := by rw [abs_mul,abs_of_pos (mul_pos hnv hnw)]
  have hndiff : |nv-nw| ≤ (1+V)^2*e := by
    rw [hid]
    have hh := mul_le_mul_of_nonneg_left hhead (mul_pos hnv hnw).le
    have hnprod : nv*nw ≤ (1+V)^2 := by nlinarith
    exact hh.trans (mul_le_mul_of_nonneg_right hnprod (norm_nonneg _))
  have htail : ‖tail (graphDirection v)-tail (graphDirection w)‖ ≤ e := by
    simpa only [tail_sub] using tail_norm_le (graphDirection v-graphDirection w)
  have htailw : ‖tail (graphDirection w)‖ ≤ 1 := by
    simpa only [graphDirection_unit] using tail_norm_le (graphDirection w)
  have heq : v-w = nv • (tail (graphDirection v)-tail (graphDirection w))+
      (nv-nw) • tail (graphDirection w) := by
    rw [smul_sub,sub_smul]
    simp only [nv,nw,graphDirection_recover]
    module
  rw [heq]
  have h := norm_add_le (nv • (tail (graphDirection v)-tail (graphDirection w)))
    ((nv-nw) • tail (graphDirection w))
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos hnv] at h
  have hfirst := mul_le_mul hnvL htail (norm_nonneg _) (by linarith : 0 ≤ 1+V)
  have hsecond := mul_le_mul hndiff htailw (norm_nonneg _) (by positivity : 0 ≤ (1+V)^2*e)
  have hL : (1+V) ≤ (1+V)^2 := by nlinarith
  have he0 : 0 ≤ e := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hL he0]


/-- The inverse chart is valid for unoriented projective chord distance, including
the branch where the closer representatives have opposite signs. -/
theorem graphDirection_inverse {k : ℕ} (v w : Space k) {V : ℝ}
    (hV : 0 ≤ V) (hv : ‖v‖ ≤ V) (hw : ‖w‖ ≤ V) :
    ‖v-w‖ ≤ 2*(1+V)^2 * projectiveDistance (graphDirection v) (graphDirection w) := by
  let L := 1+V
  have hL : 0 < L := by dsimp [L]; linarith
  by_cases hchord : ‖graphDirection v-graphDirection w‖ ≤ ‖graphDirection v+graphDirection w‖
  · rw [projectiveDistance,min_eq_left hchord]
    exact graphDirection_chord_inverse v w hV hv hw
  · rw [projectiveDistance,min_eq_right (le_of_not_ge hchord)]
    have hhead (z : Space k) (hz : ‖z‖ ≤ V) : 1 ≤ L*head (graphDirection z) := by
      rw [graphDirection_head]
      have hn : 0 < ‖cons 1 z‖ := lt_of_lt_of_le zero_lt_one (graph_norm_ge_one z)
      have hh : ‖cons 1 z‖ ≤ L := (graph_norm_upper z).trans (by dsimp [L]; linarith)
      simpa only [div_eq_mul_inv] using (le_div_iff₀ hn).mpr (by simpa using hh)
    have hh := (le_abs_self (head (graphDirection v+graphDirection w))).trans
      (head_abs_le_norm (graphDirection v+graphDirection w))
    rw [head_add] at hh
    have hsum := mul_le_mul_of_nonneg_left hh hL.le
    have hbound : 2 ≤ L*‖graphDirection v+graphDirection w‖ := by
      nlinarith [hhead v hv,hhead w hw]
    have hmul := mul_le_mul_of_nonneg_left hbound hL.le
    have hvw := (norm_sub_le v w).trans (add_le_add hv hw)
    change ‖v-w‖ ≤ 2*L^2*‖graphDirection v+graphDirection w‖
    have hVL : V ≤ L := by dsimp [L]; linarith
    have hpos : 0 ≤ L^2*‖graphDirection v+graphDirection w‖ := by positivity
    nlinarith

/-- Thus a graph-direction cap centered at one graph direction confines the
original slopes to a genuine Euclidean ball. -/
theorem graph_cap_to_slope_ball {k : ℕ} (v w : Space k) {V r : ℝ}
    (hV : 0 ≤ V) (hv : ‖v‖ ≤ V) (hw : ‖w‖ ≤ V)
    (hcap : projectiveDistance (graphDirection v) (graphDirection w) ≤ r) :
    dist v w ≤ 2*(1+V)^2*r := by
  rw [dist_eq_norm]
  exact (graphDirection_inverse v w hV hv hw).trans
    (mul_le_mul_of_nonneg_left hcap (by positivity))


/-- Two approximations to the common-pivot slope formula recover the actual
horizontal label separation with only twice the rounding error. -/
theorem residual_label_distance {k : ℕ} (z x y v w : Space k) {err : ℝ}
    (hv : ‖v-(z-x)‖ ≤ err) (hw : ‖w-(z-y)‖ ≤ err) :
    dist x y ≤ ‖v-w‖+2*err := by
  have heq : x-y = -(v-w)+(v-(z-x))-(w-(z-y)) := by module
  rw [dist_eq_norm,heq]
  have h1 := norm_sub_le (-(v-w)+(v-(z-x))) (w-(z-y))
  have h2 := norm_add_le (-(v-w)) (v-(z-x))
  rw [norm_neg] at h2
  linarith

/-- Every graph cap is confined to an actual ball of original grid labels by
the pivot formula. The cap may be centered at any vector, not just a graph vector. -/
theorem fixed_pivot_cap_labels {I : Type*} [Fintype I] {k : ℕ}
    (v : I → Space k) (label : I → Cell k) (z : Space k)
    {δ r V C : ℝ} (hr : δ ≤ r) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbound : ∀ i, ‖v i‖ ≤ V)
    (hres : ∀ i, ‖v i-(z-cellCenter δ (label i))‖ ≤ C*δ)
    (center : Space (k+1)) (j : I)
    (hj : projectiveDistance (graphDirection (v j)) center ≤ r) :
    ∀ i, projectiveDistance (graphDirection (v i)) center ≤ r →
      dist (cellCenter δ (label i)) (cellCenter δ (label j)) ≤
        (4*(1+V)^2+2*C)*r := by
  intro i hi
  have hang : projectiveDistance (graphDirection (v i)) (graphDirection (v j)) ≤ 2*r := by
    have htri := projective_triangle (graphDirection (v i)) center (graphDirection (v j))
    have hj' : projectiveDistance center (graphDirection (v j)) ≤ r := by
      simpa only [projective_symm] using hj
    linarith
  have hsl := (graphDirection_inverse (v i) (v j) hV (hbound i) (hbound j)).trans
    (mul_le_mul_of_nonneg_left hang (by positivity))
  have hp := residual_label_distance z (cellCenter δ (label i)) (cellCenter δ (label j))
    (v i) (v j) (hres i) (hres j)
  have herr := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*C by positivity)
  nlinarith

/-- The pruned spatial ball bound supplies the graph-direction cap bound with
no conditioning loss: all constants involve only the fixed slope/error range. -/
theorem fixed_pivot_cap_count {I : Type*} [Fintype I] {k : ℕ}
    (v : I → Space k) (label : I → Cell k) (z : Space k) (E : Finset (Cell k))
    (hinj : Function.Injective label) (hE : ∀ i, label i ∈ E)
    {δ r V C F d : ℝ} (hδ : 0 < δ) (hr : δ ≤ r) (hV : 0 ≤ V)
    (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hbound : ∀ i, ‖v i‖ ≤ V)
    (hres : ∀ i, ‖v i-(z-cellCenter δ (label i))‖ ≤ C*δ)
    (hball : ∀ x : Space k, ∀ R : ℝ, δ ≤ R →
      ((E.filter (fun q => dist (cellCenter δ q) x ≤ R)).card : ℝ) ≤ F*(R/δ)^d)
    (center : Space (k+1)) :
    ((Finset.univ.filter (fun i => projectiveDistance (graphDirection (v i)) center ≤ r)).card : ℝ) ≤
      F*((4*(1+V)^2+2*C)*r/δ)^d := by
  classical
  let S := Finset.univ.filter (fun i => projectiveDistance (graphDirection (v i)) center ≤ r)
  let K := 4*(1+V)^2+2*C
  have hK : 1 ≤ K := by dsimp [K]; nlinarith [sq_nonneg V]
  have hrpos : 0 < r := hδ.trans_le hr
  have hKr : δ ≤ K*r := hr.trans (by nlinarith)
  by_cases hne : S.Nonempty
  · obtain ⟨j,hj⟩ := hne
    let B := E.filter (fun q => dist (cellCenter δ q) (cellCenter δ (label j)) ≤ K*r)
    have hsub : S.image label ⊆ B := by
      intro q hq
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      refine Finset.mem_filter.mpr ⟨hE i,?_⟩
      exact fixed_pivot_cap_labels v label z hr hV hC hbound hres center j
        (Finset.mem_filter.mp hj).2 i (Finset.mem_filter.mp hi).2
    have hc : (S.card : ℝ) ≤ (B.card : ℝ) := by
      have hh := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hinj] at hh
      exact_mod_cast hh
    exact hc.trans (hball (cellCenter δ (label j)) (K*r) hKr)
  · have heq := Finset.not_nonempty_iff_eq_empty.mp hne
    change (S.card : ℝ) ≤ _
    rw [heq,Finset.card_empty,Nat.cast_zero]
    have hpos : 0 < K*r/δ := by positivity
    exact mul_nonneg hF (Real.rpow_pos_of_pos hpos d).le


/-- General modular lattice coloring, with an explicit arbitrary modulus. -/
theorem coordinate_gap {Q : ℕ} {a b : ℤ} (hne : a ≠ b)
    (hc : (a : ZMod Q) = (b : ZMod Q)) : (Q:ℤ) ≤ |a-b| := by
  have hdvd : (Q:ℤ) ∣ a-b := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (a-b) Q).mp
    push_cast
    exact sub_eq_zero.mpr hc
  obtain ⟨n,hn⟩ := hdvd
  have hn0 : n ≠ 0 := by
    intro hz
    have hh : a-b = 0 := by simp [hz] at hn; exact hn
    exact hne (sub_eq_zero.mp hh)
  rw [hn,abs_mul,abs_of_nonneg (Nat.cast_nonneg Q)]
  nlinarith [Int.one_le_abs hn0]

/-- Equal colors force well-separated actual grid centers. -/
theorem modular_grid_separation {I : Type*} {k Q : ℕ}
    (label : I → Cell k) (hinj : Function.Injective label)
    {δ : ℝ} (hδ : 0 < δ) {i j : I} (hij : i ≠ j)
    (hc : (fun l => (label i l : ZMod Q)) = (fun l => (label j l : ZMod Q))) :
    δ*Q ≤ dist (cellCenter δ (label i)) (cellCenter δ (label j)) := by
  have hlabels : label i ≠ label j := fun h => hij (hinj h)
  obtain ⟨l,hl⟩ := Function.ne_iff.mp hlabels
  have hgap := coordinate_gap hl (congrFun hc l)
  have hgapR : (Q:ℝ) ≤ |(label i l:ℝ)-(label j l:ℝ)| := by exact_mod_cast hgap
  have hcoord := GridGeometry.coordinate_dist_le (cellCenter δ (label i)) (cellCenter δ (label j)) l
  have heq : |WithLp.ofLp (cellCenter δ (label i)) l-
      WithLp.ofLp (cellCenter δ (label j)) l| = δ*|(label i l:ℝ)-(label j l:ℝ)| := by
    change |δ*(label i l:ℝ)-δ*(label j l:ℝ)| = _
    rw [← mul_sub,abs_mul,abs_of_pos hδ]
  rw [heq] at hcoord
  exact (mul_le_mul_of_nonneg_left hgapR hδ.le).trans hcoord

/-- Keeping every residue color partitions the complete lifted family into a
fixed number of separated graph-direction families, without losing any lines. -/
theorem fixed_pivot_coloring {I : Type*} {k : ℕ}
    (v : I → Space k) (label : I → Cell k) (z : Space k)
    (hinj : Function.Injective label) {δ V C : ℝ}
    (hδ : 0 < δ) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hbound : ∀ i, ‖v i‖ ≤ V)
    (hres : ∀ i, ‖v i-(z-cellCenter δ (label i))‖ ≤ C*δ) :
    ∃ Q : ℕ, 0 < Q ∧ (Q:ℝ) ≤ 2*C+2 ∧
      ∃ color : I → (Fin k → ZMod Q),
        ∀ i j, i ≠ j → color i = color j →
          δ/(2*(1+V)^2) ≤ projectiveDistance (graphDirection (v i)) (graphDirection (v j)) := by
  let Q := Nat.ceil (2*C+1)
  have hQ : 2*C+1 ≤ (Q:ℝ) := Nat.le_ceil _
  have hQpos : 0 < Q := by
    have : (0:ℝ) < Q := by linarith
    exact_mod_cast this
  have hQupper : (Q:ℝ) ≤ 2*C+2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 2*C+1 by positivity)
    dsimp [Q]
    linarith
  refine ⟨Q,hQpos,hQupper,(fun i l => (label i l : ZMod Q)),?_⟩
  intro i j hij hc
  have hsep := modular_grid_separation label hinj hδ hij hc
  have hresdist := residual_label_distance z (cellCenter δ (label i)) (cellCenter δ (label j))
    (v i) (v j) (hres i) (hres j)
  have hinverse := graphDirection_inverse (v i) (v j) hV (hbound i) (hbound j)
  apply (div_le_iff₀ (by positivity : 0 < 2*(1+V)^2)).mpr
  have hQδ := mul_le_mul_of_nonneg_left hQ hδ.le
  nlinarith


/-- Direct bridge to the actual cap predicate of a lifted tube family. -/
theorem lifted_family_cap_bound {M k : ℕ} (T : TubeFamily (k+1) M)
    (v : Fin M → Space k) (label : Fin M → Cell k) (z : Space k) (E : Finset (Cell k))
    (hinj : Function.Injective label) (hE : ∀ i, label i ∈ E)
    {δ V C F d : ℝ} (hδ : 0 < δ) (hV : 0 ≤ V) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hbound : ∀ i, ‖v i‖ ≤ V)
    (hres : ∀ i, ‖v i-(z-cellCenter δ (label i))‖ ≤ C*δ)
    (hdir : ∀ i, (T.tube i).direction = graphDirection (v i))
    (hball : ∀ x : Space k, ∀ R : ℝ, δ ≤ R →
      ((E.filter (fun q => dist (cellCenter δ q) x ≤ R)).card : ℝ) ≤ F*(R/δ)^d) :
    T.CapBound δ d (F*(4*(1+V)^2+2*C)^d) := by
  intro center _ r hr _
  simp_rw [hdir]
  have hh := fixed_pivot_cap_count v label z E hinj hE hδ hr hV hC hF hbound hres hball center
  have hK : 0 ≤ 4*(1+V)^2+2*C := by positivity
  have hr0 : 0 ≤ r/δ := div_nonneg (hδ.le.trans hr) hδ.le
  rw [show (4*(1+V)^2+2*C)*r/δ = (4*(1+V)^2+2*C)*(r/δ) by ring,
    Real.mul_rpow hK hr0] at hh
  simpa only [mul_assoc] using hh

end
end KakeyaFormal.LiftGraph
