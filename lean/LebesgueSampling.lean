import SamplingSourceRealization
import LebesgueRepresentatives

/-! Exact completed-measure input and raw sampling data. Nested Borel subset
representatives preserve every original cell weight and the actual finite
support. No scale, density, axis, mark, or probability normalization is used. -/
namespace KakeyaFormal.LebesgueSampling
open Finset MeasureTheory SamplingSupport SamplingLengthInput KakeyaSamplingApplication
  SamplingMeasurableAssembly
open scoped BigOperators
noncomputable section
open Classical

structure Input {n M : ℕ} (F : TubeFamily (n+1) M)
    (length : Fin M → ℝ) (Full G : Fin M → Set (Space (n+1)))
    (δ width R L lam c₀ C₀ xi B alpha K beta : ℝ) : Prop where
  scale_pos : 0 < δ
  scale_le_one : δ ≤ 1
  width_nonneg : 0 ≤ width
  density_pos : 0 < lam
  density_le_one : lam ≤ 1
  lower_constant_pos : 0 < c₀
  upper_constant_pos : 0 < C₀
  count_pos : 0 < M
  marked_fraction_pos : 0 < xi
  bounded : F.Bounded R
  length_upper : ∀ i, length i ≤ L
  full_subset : ∀ i, Full i ⊆ SamplingGeometry.lengthCarrier (F.tube i) (length i) (width*δ)
  full_measurable : ∀ i, NullMeasurableSet (Full i) (volume : Measure (Space (n+1)))
  marked_measurable : ∀ i, NullMeasurableSet (G i) (volume : Measure (Space (n+1)))
  marked_subset : ∀ i, G i ⊆ Full i
  full_mass : ∀ i, c₀*lam*δ^n ≤ (volume : Measure (Space (n+1))).real (Full i) ∧
    (volume : Measure (Space (n+1))).real (Full i) ≤ C₀*lam*δ^n
  marked_mass : xi*lam*δ^n*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (n+1))).real (G i)
  two_ends_constant : 1 ≤ B
  two_ends_exponent : 0 ≤ alpha
  broadness_constant : 0 < K
  broadness_exponent : 0 < beta
  two_ends : ∀ i x r, δ ≤ r → r ≤ 1 →
    (volume : Measure (Space (n+1))).real (Full i ∩ Metric.closedBall x r) ≤
      B*r^alpha*(volume : Measure (Space (n+1))).real (Full i)
  broadness : ∀ᵐ x ∂(volume : Measure (Space (n+1))),
    ∀ v : Space (n+1), ‖v‖=1 → ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((univ.filter (fun i => x ∈ G i ∧ projectiveDistance (F.tube i).direction v ≤ r)).card : ℝ) ≤
        K*r^beta*((univ.filter (fun i => x ∈ G i)).card : ℝ)

variable {n M : ℕ} {F : TubeFamily (n+1) M} {length : Fin M → ℝ}
variable {Full G : Fin M → Set (Space (n+1))}
variable {δ width R L lam c₀ C₀ xi B alpha K beta : ℝ}

namespace Input
variable (h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta)
include h

/-- Exact nested Borel subsets exist for the original completed-measurable data. -/
theorem representatives : Nonempty (LebesgueRepresentatives.Output
    (volume : Measure (Space (n+1))) Full G) :=
  LebesgueRepresentatives.construct volume Full G h.full_measurable h.marked_measurable h.marked_subset

/-- All physical hypotheses hold for the same nested representatives with
exactly the original numerical parameters and original tube family. -/
theorem to_borel (O : LebesgueRepresentatives.Output
    (volume : Measure (Space (n+1))) Full G) :
    SamplingLengthInput.Input F length O.full O.marks δ width R L lam c₀ C₀ xi B alpha K beta := by
  refine {
    scale_pos := h.scale_pos
    scale_le_one := h.scale_le_one
    width_nonneg := h.width_nonneg
    density_pos := h.density_pos
    density_le_one := h.density_le_one
    lower_constant_pos := h.lower_constant_pos
    upper_constant_pos := h.upper_constant_pos
    count_pos := h.count_pos
    marked_fraction_pos := h.marked_fraction_pos
    bounded := h.bounded
    length_upper := h.length_upper
    full_subset := fun i => (O.full_subset i).trans (h.full_subset i)
    full_measurable := O.full_measurable
    marked_measurable := O.marks_measurable
    marked_subset := O.nested
    full_mass := ?_
    marked_mass := ?_
    two_ends_constant := h.two_ends_constant
    two_ends_exponent := h.two_ends_exponent
    broadness_constant := h.broadness_constant
    broadness_exponent := h.broadness_exponent
    two_ends := ?_
    broadness := ?_ }
  · intro i
    simpa only [O.full_real i] using h.full_mass i
  · simpa only [O.marks_total_real] using h.marked_mass
  · intro i x r hr hr1
    simpa only [O.full_inter_real i, O.full_real i] using h.two_ends i x r hr hr1
  · filter_upwards [h.broadness,O.membership] with x hx hmem
    intro v hv r hr hr1
    simpa only [hmem.2] using hx v hv r hr hr1

theorem probabilities (i : Fin M)
    (z : ↥(SamplingBoundedSupport.support Full δ (pointRadius width R L))) :
    0 ≤ SamplingLengthInput.rawMarked Full G δ width R L i z ∧
      SamplingLengthInput.rawMarked Full G δ width R L i z ≤
        SamplingLengthInput.rawFull Full δ width R L i z ∧
      SamplingLengthInput.rawFull Full δ width R L i z ≤ 1 :=
  coupled_weights (h.marked_subset i) h.scale_pos z.val

end Input

namespace Representative
variable (O : LebesgueRepresentatives.Output (volume : Measure (Space (n+1))) Full G)

/-- Positive original full intersections define exactly the same finite support. -/
theorem support_eq (δ r : ℝ) : SamplingBoundedSupport.support O.full δ r =
    SamplingBoundedSupport.support Full δ r := by
  ext z
  simp only [SamplingBoundedSupport.support,mem_filter]
  simp_rw [O.full_inter_real]

/-- The entire raw full array is unchanged, with only the equal support types transported. -/
theorem full_heq (δ width R L : ℝ) :
    HEq (SamplingLengthInput.rawFull O.full δ width R L)
      (SamplingLengthInput.rawFull Full δ width R L) := by
  unfold SamplingLengthInput.rawFull
  rw [support_eq O]
  apply heq_of_eq
  funext i z
  exact congrArg (fun t : ℝ => t / δ^(n+1)) (O.full_inter_real i (GridCells.gridCell δ z.val))

theorem marked_heq (δ width R L : ℝ) :
    HEq (SamplingLengthInput.rawMarked O.full O.marks δ width R L)
      (SamplingLengthInput.rawMarked Full G δ width R L) := by
  unfold SamplingLengthInput.rawMarked
  rw [support_eq O]
  apply heq_of_eq
  funext i z
  exact congrArg (fun t : ℝ => t / δ^(n+1)) (O.marks_inter_real i (GridCells.gridCell δ z.val))

end Representative

/-- Actual original support and its two raw arrays, with their proved probability bounds. -/
structure Data (n M : ℕ) where
  cells : Finset (Cell (n+1))
  full : Fin M → ↥cells → ℝ
  marked : Fin M → ↥cells → ℝ
  marked_nonneg : ∀ i z, 0 ≤ marked i z
  marked_le_full : ∀ i z, marked i z ≤ full i z
  full_le_one : ∀ i z, full i z ≤ 1

namespace Data
@[ext] theorem ext {D E : Data n M} (hc : D.cells=E.cells)
    (hf : HEq D.full E.full) (hm : HEq D.marked E.marked) : D=E := by
  cases D
  cases E
  cases hc
  cases hf
  cases hm
  rfl

def law (D : Data n M) : KakeyaSampling.FiniteLaw (Outcome (Fin M) ↥D.cells) :=
  SphereNetFailure.law D.full D.marked D.marked_nonneg D.marked_le_full D.full_le_one

end Data

/-- No representative appears in these original-data definitions. -/
def data (h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta) : Data n M := {
  cells := SamplingBoundedSupport.support Full δ (pointRadius width R L)
  full := SamplingLengthInput.rawFull Full δ width R L
  marked := SamplingLengthInput.rawMarked Full G δ width R L
  marked_nonneg := fun i z => (h.probabilities i z).1
  marked_le_full := fun i z => (h.probabilities i z).2.1
  full_le_one := fun i z => (h.probabilities i z).2.2 }

def borelData (h : SamplingLengthInput.Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta) : Data n M := {
  cells := SamplingBoundedSupport.support Full δ (pointRadius width R L)
  full := SamplingLengthInput.rawFull Full δ width R L
  marked := SamplingLengthInput.rawMarked Full G δ width R L
  marked_nonneg := fun i z => (h.probabilities i z).1
  marked_le_full := fun i z => (h.probabilities i z).2.1
  full_le_one := fun i z => (h.probabilities i z).2.2 }

/-- Equality of actual supports, arrays and finite-law data, not just equality of means. -/
theorem data_eq (h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta)
    (O : LebesgueRepresentatives.Output (volume : Measure (Space (n+1))) Full G) :
    borelData (h.to_borel O) = data h :=
  Data.ext (Representative.support_eq O δ _) (Representative.full_heq O δ width R L)
    (Representative.marked_heq O δ width R L)

/-- The actual product laws are equal after transporting their identical cell support. -/
theorem law_heq (h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta)
    (O : LebesgueRepresentatives.Output (volume : Measure (Space (n+1))) Full G) :
    HEq (SphereNetSourceFailure.rawLaw (h.to_borel O)) (data h).law := by
  change HEq (borelData (h.to_borel O)).law (data h).law
  rw [data_eq h O]

namespace Input
variable (h : Input F length Full G δ width R L lam c₀ C₀ xi B alpha K beta)
include h

/-- Exact original full means, including completed-measurable representatives. -/
theorem full_mean_eq (i : Fin M) : fullMean (data h).full i =
    (volume : Measure (Space (n+1))).real (Full i)/δ^(n+1) := by
  obtain ⟨O⟩ := h.representatives
  have hd := congrArg (fun D : Data n M => fullMean D.full i) (data_eq h O)
  rw [←hd]
  change fullMean (SamplingLengthInput.rawFull O.full δ width R L) i = _
  rw [(h.to_borel O).full_mean_eq, O.full_real]

/-- Literal original Wg is the sum of the unchanged marked raw means. -/
theorem marked_mean_eq : (∑ z, markedMean (data h).marked z) =
    (∑ i, (volume : Measure (Space (n+1))).real (G i))/δ^(n+1) := by
  obtain ⟨O⟩ := h.representatives
  have hd := congrArg (fun D : Data n M => ∑ z, markedMean D.marked z) (data_eq h O)
  rw [←hd]
  change (∑ z, markedMean (SamplingLengthInput.rawMarked O.full O.marks δ width R L) z) = _
  rw [(h.to_borel O).marked_mean_eq, O.marks_total_real]

theorem full_mean_bounds (i : Fin M) : c₀*lam/δ ≤ fullMean (data h).full i ∧
    fullMean (data h).full i ≤ C₀*lam/δ := by
  obtain ⟨O⟩ := h.representatives
  have hd := congrArg (fun D : Data n M => fullMean D.full i) (data_eq h O)
  rw [←hd]
  exact (h.to_borel O).full_mean_bounds i

theorem marked_mean_lower : xi*lam*(M:ℝ)/δ ≤ ∑ z, markedMean (data h).marked z := by
  obtain ⟨O⟩ := h.representatives
  have hd := congrArg (fun D : Data n M => ∑ z, markedMean D.marked z) (data_eq h O)
  rw [←hd]
  exact (h.to_borel O).marked_mean_lower

end Input

end
end KakeyaFormal.LebesgueSampling
