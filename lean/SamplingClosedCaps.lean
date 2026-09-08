import SamplingRawRealization

/-! The existing open doubled tests control closed caps at the exact source
radius. Curvature of the unit sphere supplies strict diameter<2theta, so no
radius change and no change to the actual raw sample is necessary. -/
namespace KakeyaFormal.SamplingClosedCaps
open Finset ProjectiveGeometry SamplingCapTests KakeyaSamplingApplication
noncomputable section
open Classical

/-- A closed small spherical chord cap has diameter strictly less than twice
its radius. The strict inequality is geometric, not a boundary convention. -/
theorem chord_cap_diameter {k : ℕ} (a b v : Space k) {theta : ℝ}
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hv : ‖v‖=1)
    (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hva : ‖a-v‖ ≤ theta) (hvb : ‖b-v‖ ≤ theta) : ‖a-b‖ < 2*theta := by
  have hsa := norm_sub_sq_real a v
  have hsb := norm_sub_sq_real b v
  have hsum := norm_add_sq_real a b
  have hdiff := norm_sub_sq_real a b
  simp only [ha,hb,hv,one_pow] at hsa hsb hsum hdiff
  have hsa' : ‖a-v‖^2 ≤ theta^2 := (sq_le_sq₀ (norm_nonneg _) ht.le).mpr hva
  have hsb' : ‖b-v‖^2 ≤ theta^2 := (sq_le_sq₀ (norm_nonneg _) ht.le).mpr hvb
  have hin := (le_abs_self (inner ℝ (a+b) v)).trans (abs_real_inner_le_norm (a+b) v)
  rw [hv,mul_one,inner_add_left] at hin
  have hlower : 2-theta^2 ≤ ‖a+b‖ := by nlinarith
  have htheta : theta^2 ≤ 1 := by nlinarith
  have hlow0 : 0 ≤ 2-theta^2 := by linarith
  have hlowSq : (2-theta^2)^2 ≤ ‖a+b‖^2 :=
    (sq_le_sq₀ hlow0 (norm_nonneg _)).mpr hlower
  have htheta4 : 0 < (theta^2)^2 := sq_pos_of_pos (sq_pos_of_pos ht)
  by_contra hn
  have hdist := le_of_not_gt hn
  have hdistSq : (2*theta)^2 ≤ ‖a-b‖^2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hdist
  nlinarith

/-- The same strict diameter property for unoriented unit directions. -/
theorem projective_cap_diameter {k : ℕ} (a b v : Space k) {theta : ℝ}
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hv : ‖v‖=1)
    (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hva : projectiveDistance v a ≤ theta) (hvb : projectiveDistance v b ≤ theta) :
    projectiveDistance a b < 2*theta := by
  obtain ⟨a',hra,hda⟩ := cap_representative a v (by simpa only [projective_symm] using hva)
  obtain ⟨b',hrb,hdb⟩ := cap_representative b v (by simpa only [projective_symm] using hvb)
  have ha' : ‖a'‖=1 := by rcases hra with rfl | rfl <;> simpa using ha
  have hb' : ‖b'‖=1 := by rcases hrb with rfl | rfl <;> simpa using hb
  have hchord := chord_cap_diameter a' b' v ha' hb' hv ht ht1
    (by simpa only [dist_eq_norm] using hda) (by simpa only [dist_eq_norm] using hdb)
  have hle : projectiveDistance a b ≤ ‖a'-b'‖ := by
    have hh := projective_le_chord a' b'
    rcases hra with rfl | rfl <;> rcases hrb with rfl | rfl <;>
      simpa only [projective_neg_left,projectiveDistance_neg_right] using hh
  exact hle.trans_lt hchord

/-- An actual member of a closed cap centers one of the already sampled open
doubled tests containing that entire closed cap. -/
theorem cap_containment {k M : ℕ} (F : TubeFamily k M) {theta : ℝ}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (S : Finset (Fin M)) (v : Space k) (hv : ‖v‖=1)
    (hne : (S.filter (fun i => projectiveDistance v (F.tube i).direction ≤ theta)).Nonempty) :
    ∃ a ∈ S, S.filter (fun i => projectiveDistance v (F.tube i).direction ≤ theta) ⊆
      S.filter (fun i => cap F theta a i = true) := by
  obtain ⟨a,ha⟩ := hne
  obtain ⟨has,ha⟩ := mem_filter.mp ha
  refine ⟨a,has,?_⟩
  intro i hi
  obtain ⟨his,hi⟩ := mem_filter.mp hi
  refine mem_filter.mpr ⟨his,?_⟩
  simp only [cap,decide_eq_true_eq]
  exact projective_cap_diameter _ _ v (F.tube a).unit_direction (F.tube i).unit_direction hv ht ht1 ha hi

theorem all_closed_caps {k M : ℕ} (F : TubeFamily k M) {theta : ℝ}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (S : Finset (Fin M))
    (hcap : ∀ a, ((S.filter (fun i => cap F theta a i = true)).card:ℝ) ≤ (S.card:ℝ)/10) :
    ∀ v : Space k, ‖v‖=1 →
      ((S.filter (fun i => projectiveDistance v (F.tube i).direction ≤ theta)).card:ℝ) ≤
        (S.card:ℝ)/10 := by
  intro v hv
  by_cases hne : (S.filter (fun i => projectiveDistance v (F.tube i).direction ≤ theta)).Nonempty
  · obtain ⟨a,_,ha⟩ := cap_containment F ht ht1 S v hv hne
    exact (Nat.cast_le.mpr (card_le_card ha)).trans (hcap a)
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp only [card_empty,Nat.cast_zero]
    positivity

/-- Closed-cap broadness at the exact theta for the same original outcome. -/
theorem sampled_closed_broadness {k M : ℕ} {C B : Type*}
    [Fintype C] [DecidableEq C] [Fintype B]
    (F : TubeFamily k M) {theta : ℝ} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (p q : Fin M → C → ℝ) (high : Finset C) (ball : B → C → Bool) (cutoff : Fin M → B → ℝ)
    (omega : Outcome (Fin M) C)
    (hgood : SampleGood p q high ball (cap F theta) cutoff omega) :
    ∀ (c : C) (v : Space k), ‖v‖=1 →
      (((row high omega c).filter (fun i => projectiveDistance v (F.tube i).direction ≤ theta)).card:ℝ) ≤
        ((row high omega c).card:ℝ)/10 := by
  intro c v hv
  by_cases hc : c ∈ high
  · apply all_closed_caps F ht ht1 (row high omega c) _ v hv
    intro a
    rw [row_cap_card F theta high omega hc a,row_card high omega hc]
    exact hgood.angular c hc a
  · have hrow : row high omega c = ∅ := by simp [row,markedShading,hc]
    simp [hrow]

/-- The frozen raw realization already proves closed-cap broadness; it needs
no new outcome and no change of its source theta. -/
theorem raw_output_closed_broadness {n M : ℕ} {F : TubeFamily (n+1) M}
    {Full G : Fin M → Set (Space (n+1))} {δ width R B alpha theta : ℝ}
    (O : SamplingRawRealization.Output F Full G δ width R B alpha theta)
    (ht : 0 < theta) (ht1 : theta ≤ 1) :
    ∀ (z : Cell (n+1)) (v : Space (n+1)), ‖v‖=1 →
      (((univ.filter (fun i => z ∈ O.marks i)).filter (fun i =>
        projectiveDistance v (O.family.tube i).direction ≤ theta)).card:ℝ) ≤
          ((univ.filter (fun i => z ∈ O.marks i)).card:ℝ)/10 := by
  intro z v hv
  let E := SamplingSupport.support F.tube Full δ width R
  let high := KakeyaSamplingDichotomy.high
    (markedMean (SamplingNormalizedMeans.rawMarked F Full G δ width R))
    (SamplingMeasurableAssembly.threshold n δ)
  by_cases hz : z ∈ E
  · let c : ↥E := ⟨z,hz⟩
    have heq : univ.filter (fun i => z ∈ O.marks i) = row high O.omega c := by
      ext i
      simp only [row,mem_filter,mem_univ,true_and]
      exact SamplingRealization.mem_unlabel E _ c
    rw [heq]
    exact sampled_closed_broadness F ht ht1 _ _ high _ _ O.omega O.good c v hv
  · have heq : univ.filter (fun i => z ∈ O.marks i) = ∅ := by
      apply filter_eq_empty_iff.mpr
      intro i _ hi
      exact hz (SamplingRealization.unlabel_subset E _ hi)
    simp [heq]

end
end KakeyaFormal.SamplingClosedCaps
