import MarkedLengthNormalization

/-! Literal original marked data on axes of arbitrary fixed bounded lengths.
The same-label common dilation supplies the unit-axis marked input, without
any selected marks, sampled outcome or normalization oracle. -/
namespace KakeyaFormal.MarkedLengthInput
open Finset MarkedLengthNormalization TransverseAngles MarkedSubsetSamples
open scoped BigOperators
noncomputable section
open Classical

structure Input {n M : ℕ} (F : TubeFamily n M) (E : Finset (Cell n))
    (marks : Fin M → Finset (Cell n)) (lengths : Fin M → ℝ)
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
  admissible : ∀ i z, z ∈ F.shade i → cellCenter δ z ∈
    SamplingGeometry.lengthCarrier (F.tube i) (lengths i) (width*δ)
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


/-- All full and marked integer rows are unchanged. Only one common spatial
scale is changed, with the fixed full-two-ends coefficient B*W. -/
theorem to_unit_input {n M : ℕ} {F : TubeFamily n M} {E : Finset (Cell n)}
    {marks : Fin M → Finset (Cell n)} {lengths : Fin M → ℝ}
    {W δ A lam xi B theta width R m alpha a b sep : ℝ}
    (hW : 1 ≤ W) (hL : ∀ i, lengths i ≤ W) (hm : 0 ≤ m)
    (hsep : 0 ≤ sep) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (h : Input F E marks lengths δ A lam xi B theta width R m alpha a b sep) :
    MarkedGridNormalization.Input (normalizedFamily F W) E marks
      (δ/W) A (lam/W) xi (B*W) theta width (R/W) m alpha a b sep := by
  have hW0 : 0 < W := zero_lt_one.trans_le hW
  have hs : δ/W ≤ δ := (div_le_iff₀ hW0).mpr (by nlinarith [h.scale_pos])
  have hl : lam/W ≤ lam := (div_le_iff₀ hW0).mpr (by nlinarith [h.density_pos])
  have hdensity (c : ℝ) : c*(lam/W)/(δ/W) = c*lam/δ := by
    field_simp
  have hmass : xi*(lam/W)*(M:ℝ)/(δ/W) = xi*lam*(M:ℝ)/δ := by
    field_simp
  refine {
    scale_pos := div_pos h.scale_pos hW0
    scale_le_one := hs.trans h.scale_le_one
    cap_ge_one := h.cap_ge_one
    density_pos := div_pos h.density_pos hW0
    density_le_one := hl.trans h.density_le_one
    fraction_pos := h.fraction_pos
    fraction_le_one := h.fraction_le_one
    count_pos := h.count_pos
    ends_ge_one := by nlinarith [h.ends_ge_one]
    theta_pos := h.theta_pos
    theta_le_one := h.theta_le_one
    cover := h.cover
    admissible := MarkedLengthNormalization.admissible F lengths hW0 hL h.admissible
    separated := MarkedLengthNormalization.separated F hW h.scale_pos.le hsep h.separated
    bounded := MarkedLengthNormalization.bounded F hW0 h.bounded
    cap_bound := MarkedLengthNormalization.cap_bound F hW h.scale_pos h.scale_le_one hm
      (by linarith [h.cap_ge_one]) h.cap_bound
    lower := ?_
    upper := ?_
    marks_subset := h.marks_subset
    marked_mass := ?_
    marked_broad := h.marked_broad
    two_ends := MarkedLengthNormalization.two_ends F hW h.scale_pos h.ends_ge_one ha ha1 h.two_ends }
  · intro i
    rw [hdensity]
    exact h.lower i
  · intro i
    rw [hdensity]
    exact h.upper i
  · rw [hmass]
    exact h.marked_mass

/-- The dilation is fixed from the single original length ceiling, before any
scale, density, population, axes, rows or marks are supplied. -/
theorem bounded_lengths {n M : ℕ} {F : TubeFamily n M} {E : Finset (Cell n)}
    {marks : Fin M → Finset (Cell n)} {lengths : Fin M → ℝ}
    {lengthUpper δ A lam xi B theta width R m alpha a b sep : ℝ}
    (hL : ∀ i, lengths i ≤ lengthUpper) (hm : 0 ≤ m)
    (hsep : 0 ≤ sep) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (h : Input F E marks lengths δ A lam xi B theta width R m alpha a b sep) :
    MarkedGridNormalization.Input (normalizedFamily F (dilation lengthUpper)) E marks
      (δ/dilation lengthUpper) A (lam/dilation lengthUpper) xi
      (B*dilation lengthUpper) theta width (R/dilation lengthUpper) m alpha a b sep :=
  to_unit_input (dilation_ge_one _) (fun i => (hL i).trans (le_max_right _ _)) hm hsep ha ha1 h

end
end KakeyaFormal.MarkedLengthInput
