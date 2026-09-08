import MaximalLengths

/-! Completion of the maximal-shading predicates to arbitrary Lebesgue
measurable representatives. Borel subsets of each original shading preserve
all individual and union volumes and remain inside the original carriers.
No completion or representative-transfer axiom is added. -/
namespace KakeyaFormal.LebesgueMaximal
open MeasureTheory Finset SamplingGeometry
open scoped BigOperators
noncomputable section

/-- The arbitrary-position maximal assertion for Lebesgue measurable shadings,
including representatives which are not Borel sets. -/
def Estimate (n : ℕ) (d : ℝ) : Prop :=
  ∀ separation : ℝ, 0 < separation → ∀ eps : ℝ, 0 < eps → ∃ c : ℝ, 0 < c ∧
    ∀ {M : ℕ} (F : TubeFamily n M) {δ lam : ℝ} (Y : Fin M → Set (Space n)),
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 →
      (∀ i, NullMeasurableSet (Y i) (volume : Measure (Space n))) →
      (∀ i, Y i ⊆ (F.tube i).carrier δ) →
      (∀ i, lam*(volume : Measure (Space n)).real ((F.tube i).carrier δ) ≤
        (volume : Measure (Space n)).real (Y i)) →
      F.Separated (separation*δ) →
      c*δ^((n:ℝ)-d+eps)*lam^d*
        (∑ i, (volume : Measure (Space n)).real ((F.tube i).carrier δ)) ≤
          (volume : Measure (Space n)).real (⋃ i, Y i)

/-- The exact same constant works for arbitrary Lebesgue measurable shadings. -/
theorem of_borel {n : ℕ} {d : ℝ} (h : MaximalShading.Estimate n d) : Estimate n d := by
  intro separation hsep eps heps
  obtain ⟨c,hc,hbound⟩ := h separation hsep eps heps
  refine ⟨c,hc,?_⟩
  intro M F δ lam Y hδ hδ1 hlam hlam1 hY hsub hmass hdir
  choose Z hZY hZ hsame using fun i => (hY i).exists_measurable_subset_ae_eq
  have hmass' : ∀ i, lam*(volume : Measure (Space n)).real ((F.tube i).carrier δ) ≤
      volume.real (Z i) := by
    intro i
    rw [measureReal_congr (hsame i)]
    exact hmass i
  have hb := hbound F Z hδ hδ1 hlam hlam1 hZ (fun i => (hZY i).trans (hsub i)) hmass' hdir
  exact hb.trans_eq (measureReal_congr (.countable_iUnion hsame))

theorem to_borel {n : ℕ} {d : ℝ} (h : Estimate n d) : MaximalShading.Estimate n d := by
  intro separation hsep eps heps
  obtain ⟨c,hc,hbound⟩ := h separation hsep eps heps
  refine ⟨c,hc,?_⟩
  intro M F δ lam Y hδ hδ1 hlam hlam1 hY hsub hmass hdir
  exact hbound F Y hδ hδ1 hlam hlam1 (fun i => (hY i).nullMeasurableSet) hsub hmass hdir

theorem estimate_iff_borel {n : ℕ} {d : ℝ} : Estimate n d ↔ MaximalShading.Estimate n d :=
  ⟨to_borel,of_borel⟩

theorem endpoint {n : ℕ} (hn : 6 ≤ n) :
    Estimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) := of_borel (MainMaximal.endpoint hn)

theorem endpoint_formula {n : ℕ} (hn : 6 ≤ n) :
    Estimate n (3+(2-Real.sqrt 2)*((n:ℝ)-4)) := of_borel (MainMaximal.endpoint_formula hn)

theorem six_first : Estimate 6 (33/8) := of_borel MainMaximal.six_first

theorem six_first_step (_base : Estimate 6 4) : Estimate 6 (33/8) := six_first

theorem six_endpoint : Estimate 6 (7-2*Real.sqrt 2) := of_borel MainMaximal.six_endpoint
theorem eight_endpoint : Estimate 8 (11-4*Real.sqrt 2) := of_borel MainMaximal.eight_endpoint
theorem six_diagonal_limit : Estimate 6 (29/7) := of_borel MainMaximal.six_diagonal_limit
theorem eight_diagonal_limit : Estimate 8 (37/7) := of_borel MainMaximal.eight_diagonal_limit

/-- Fixed positive geometric conventions, with the actual individual carrier
volumes and arbitrary Lebesgue measurable shadings at arbitrary positions. -/
def LengthEstimate (n : ℕ) (d : ℝ) : Prop :=
  ∀ lengthLower lengthUpper width separation : ℝ,
    0 < lengthLower → 0 < width → 0 < separation →
    ∀ eps : ℝ, 0 < eps → ∃ c : ℝ, 0 < c ∧
      ∀ {M : ℕ} (F : TubeFamily n M) (lengths : Fin M → ℝ)
        (Y : Fin M → Set (Space n)) {δ lam : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 →
      (∀ i, lengthLower ≤ lengths i ∧ lengths i ≤ lengthUpper) →
      (∀ i, NullMeasurableSet (Y i) (volume : Measure (Space n))) →
      (∀ i, Y i ⊆ lengthCarrier (F.tube i) (lengths i) (width*δ)) →
      (∀ i, lam*(volume : Measure (Space n)).real
        (lengthCarrier (F.tube i) (lengths i) (width*δ)) ≤ volume.real (Y i)) →
      F.Separated (separation*δ) →
      c*δ^((n:ℝ)-d+eps)*lam^d*
        (∑ i, (volume : Measure (Space n)).real
          (lengthCarrier (F.tube i) (lengths i) (width*δ))) ≤
        volume.real (⋃ i,Y i)

theorem lengths_of_borel {n : ℕ} {d : ℝ} (h : MaximalLengths.Estimate n d) :
    LengthEstimate n d := by
  intro l u w s hl hw hs eps heps
  obtain ⟨c,hc,hbound⟩ := h l u w s hl hw hs eps heps
  refine ⟨c,hc,?_⟩
  intro M F lengths Y δ lam hδ hδ1 hlam hlam1 hlength hY hsub hmass hdir
  choose Z hZY hZ hsame using fun i => (hY i).exists_measurable_subset_ae_eq
  have hmass' : ∀ i, lam*(volume : Measure (Space n)).real
      (lengthCarrier (F.tube i) (lengths i) (w*δ)) ≤ volume.real (Z i) := by
    intro i
    rw [measureReal_congr (hsame i)]
    exact hmass i
  have hb := hbound F lengths Z hδ hδ1 hlam hlam1 hlength hZ
    (fun i => (hZY i).trans (hsub i)) hmass' hdir
  exact hb.trans_eq (measureReal_congr (.countable_iUnion hsame))

theorem lengths_to_borel {n : ℕ} {d : ℝ} (h : LengthEstimate n d) :
    MaximalLengths.Estimate n d := by
  intro l u w s hl hw hs eps heps
  obtain ⟨c,hc,hbound⟩ := h l u w s hl hw hs eps heps
  refine ⟨c,hc,?_⟩
  intro M F lengths Y δ lam hδ hδ1 hlam hlam1 hlength hY hsub hmass hdir
  exact hbound F lengths Y hδ hδ1 hlam hlam1 hlength
    (fun i => (hY i).nullMeasurableSet) hsub hmass hdir

theorem length_estimate_iff_borel {n : ℕ} {d : ℝ} :
    LengthEstimate n d ↔ MaximalLengths.Estimate n d := ⟨lengths_to_borel,lengths_of_borel⟩

theorem length_endpoint {n : ℕ} (hn : 6 ≤ n) :
    LengthEstimate n (KakeyaScalar.limitProfile ((n:ℝ)-1)) := lengths_of_borel (MaximalLengths.endpoint hn)

theorem length_endpoint_formula {n : ℕ} (hn : 6 ≤ n) :
    LengthEstimate n (3+(2-Real.sqrt 2)*((n:ℝ)-4)) := lengths_of_borel (MaximalLengths.endpoint_formula hn)

theorem length_six_first : LengthEstimate 6 (33/8) := lengths_of_borel MaximalLengths.six_first
theorem length_six_endpoint : LengthEstimate 6 (7-2*Real.sqrt 2) := lengths_of_borel MaximalLengths.six_endpoint
theorem length_eight_endpoint : LengthEstimate 8 (11-4*Real.sqrt 2) := lengths_of_borel MaximalLengths.eight_endpoint
theorem length_six_diagonal_limit : LengthEstimate 6 (29/7) := lengths_of_borel MaximalLengths.six_diagonal_limit
theorem length_eight_diagonal_limit : LengthEstimate 8 (37/7) := lengths_of_borel MaximalLengths.eight_diagonal_limit

end
end KakeyaFormal.LebesgueMaximal
