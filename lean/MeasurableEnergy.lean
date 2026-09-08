import TubeIntersection

/-! The actual measurable Cauchy--Schwarz energy inequality for finite families
of measurable finite-volume shadings, and its geometric tube specialization. -/

open MeasureTheory Set
open scoped BigOperators ENNReal
namespace KakeyaFormal.MeasurableEnergy

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem integral_cauchy_schwarz {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ)^2 ≤ (∫ x, f x * f x ∂μ) * (∫ x, g x * g x ∂μ) := by
  have inner_eq {a b : X → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
      inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hax hbx
    simp [hax, hbx, mul_comm]
  have h := real_inner_mul_inner_self_le (hf.toLp f) (hg.toLp g)
  rw [inner_eq hf hg, inner_eq hf hf, inner_eq hg hg] at h
  simpa only [pow_two] using h


noncomputable def oneIndicator (Y : Set X) : X → ℝ := Y.indicator (fun _ => 1)

omit [MeasurableSpace X] in
lemma indicator_mul (Y Z : Set X) (x : X) :
    oneIndicator Y x * oneIndicator Z x = oneIndicator (Y ∩ Z) x := by
  classical
  by_cases hy : x ∈ Y <;> by_cases hz : x ∈ Z <;>
    simp [oneIndicator, hy, hz]

lemma indicator_integrable {Y : Set X} (hY : MeasurableSet Y) (hfin : μ Y ≠ ∞) :
    Integrable (oneIndicator Y) μ := by
  exact memLp_one_iff_integrable.mp (memLp_indicator_const 1 hY (1:ℝ) (Or.inr hfin))

lemma indicator_integral {Y : Set X} (hY : MeasurableSet Y) :
    (∫ x, oneIndicator Y x ∂μ) = μ.real Y := by
  simpa [oneIndicator] using (integral_indicator_const (μ := μ) (1:ℝ) hY)

variable {I : Type*} [Fintype I]

noncomputable def multiplicity (Y : I → Set X) (x : X) : ℝ := ∑ i, oneIndicator (Y i) x

lemma multiplicity_memLp (Y : I → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) (p : ℝ≥0∞) : MemLp (multiplicity Y) p μ := by
  exact memLp_finsetSum Finset.univ (fun i _ =>
    memLp_indicator_const p (hY i) (1:ℝ) (Or.inr (hfin i)))

lemma multiplicity_integral (Y : I → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) :
    (∫ x, multiplicity Y x ∂μ) = ∑ i, μ.real (Y i) := by
  simp only [multiplicity]
  rw [integral_finsetSum _ (fun i _ => indicator_integrable (hY i) (hfin i))]
  simp_rw [indicator_integral (hY _)]

omit [MeasurableSpace X] in
lemma multiplicity_square (Y : I → Set X) (x : X) :
    multiplicity Y x * multiplicity Y x = ∑ i, ∑ j, oneIndicator (Y i ∩ Y j) x := by
  simp only [multiplicity, Finset.sum_mul, Finset.mul_sum, indicator_mul]
  exact Finset.sum_comm

lemma multiplicity_square_integral (Y : I → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) :
    (∫ x, multiplicity Y x * multiplicity Y x ∂μ) =
      ∑ i, ∑ j, μ.real (Y i ∩ Y j) := by
  have hint : ∀ i j, Integrable (oneIndicator (Y i ∩ Y j)) μ := fun i j =>
    indicator_integrable ((hY i).inter (hY j))
      (measure_ne_top_of_subset Set.inter_subset_left (hfin i))
  simp_rw [multiplicity_square]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
  congr 1
  funext i
  rw [integral_finsetSum _ (fun j _ => hint i j)]
  congr 1
  funext j
  exact indicator_integral ((hY i).inter (hY j))

/-- Cauchy--Schwarz for genuine measurable shadings. Both the union and energy
are actual measures; no incidence-energy or integrability premise is assumed. -/
theorem finite_shading_energy (Y : I → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) :
    (∑ i, μ.real (Y i))^2 ≤ μ.real (⋃ i, Y i) *
      (∑ i, ∑ j, μ.real (Y i ∩ Y j)) := by
  have hU : MeasurableSet (⋃ i, Y i) := MeasurableSet.iUnion hY
  have hUf : μ (⋃ i, Y i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ := μ)
      (s := Set.univ) (f := Y) (Set.toFinite _) (fun i _ => hfin i)
  have hprod : ∀ x, multiplicity Y x * oneIndicator (⋃ i, Y i) x = multiplicity Y x := by
    intro x
    classical
    by_cases hx : x ∈ ⋃ i, Y i
    · simp [oneIndicator, hx]
    · have hnone : ∀ i, x ∉ Y i := fun i hi => hx (Set.mem_iUnion.mpr ⟨i,hi⟩)
      simp [multiplicity, oneIndicator, hx, hnone]
  have hsq : ∀ x, oneIndicator (⋃ i, Y i) x * oneIndicator (⋃ i, Y i) x =
      oneIndicator (⋃ i, Y i) x := by
    intro x
    rw [indicator_mul, Set.inter_self]
  have h := integral_cauchy_schwarz (multiplicity_memLp Y hY hfin 2)
    (memLp_indicator_const 2 hU (1:ℝ) (Or.inr hUf))
  change (∫ x, multiplicity Y x * oneIndicator (⋃ i, Y i) x ∂μ)^2 ≤
    (∫ x, multiplicity Y x * multiplicity Y x ∂μ) *
    (∫ x, oneIndicator (⋃ i, Y i) x * oneIndicator (⋃ i, Y i) x ∂μ) at h
  simp_rw [hprod, hsq, multiplicity_integral Y hY hfin,
    multiplicity_square_integral Y hY hfin, indicator_integral hU] at h
  simpa only [mul_comm] using h


/-- Pairwise geometric majorants can be inserted without changing the actual
union or shading mass in the Cauchy--Schwarz inequality. -/
theorem finite_shading_energy_majorant (Y : I → Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, μ (Y i) ≠ ∞)
    (B : I → I → ℝ) (hB : ∀ i j, μ.real (Y i ∩ Y j) ≤ B i j) :
    (∑ i, μ.real (Y i))^2 ≤ μ.real (⋃ i, Y i) * (∑ i, ∑ j, B i j) := by
  exact (finite_shading_energy Y hY hfin).trans
    (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hB i j)))
      measureReal_nonneg)

/-- A common positive lower shading mass and row energy upper bound give an
actual union lower bound, including the empty index type. -/
theorem finite_shading_union_lower (Y : I → Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, μ (Y i) ≠ ∞)
    {lam B : ℝ} (hlam : 0 ≤ lam) (hB : 0 < B)
    (hlower : ∀ i, lam ≤ μ.real (Y i))
    (hrow : ∀ i, ∑ j, μ.real (Y i ∩ Y j) ≤ B) :
    (Fintype.card I : ℝ)*lam^2/B ≤ μ.real (⋃ i, Y i) := by
  have hmass : (Fintype.card I : ℝ)*lam ≤ ∑ i, μ.real (Y i) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hlower i)
  have henergy : (∑ i, ∑ j, μ.real (Y i ∩ Y j)) ≤ (Fintype.card I : ℝ)*B := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  have hmass0 : 0 ≤ (Fintype.card I : ℝ)*lam := by positivity
  have hsq := pow_le_pow_left₀ hmass0 hmass 2
  have h := hsq.trans ((finite_shading_energy Y hY hfin).trans
    (mul_le_mul_of_nonneg_left henergy measureReal_nonneg))
  by_cases hn : Fintype.card I = 0
  · simp only [hn, Nat.cast_zero, zero_mul, zero_div]
    exact measureReal_nonneg
  · have hnpos : (0:ℝ) < Fintype.card I := by exact_mod_cast Nat.pos_of_ne_zero hn
    apply (div_le_iff₀ hB).mpr
    have hh : (Fintype.card I : ℝ)*((Fintype.card I : ℝ)*lam^2) ≤
        (Fintype.card I : ℝ)*(μ.real (⋃ i, Y i)*B) := by nlinarith [h]
    exact (mul_le_mul_iff_right₀ hnpos).mp hh

/-- The pair majorants are now the proved geometric two-tube intersection
bounds, with actual projective chord distance and a scale cutoff. -/
theorem tube_shading_energy {k : ℕ} (T : I → UnitTube k) (Y : I → Set (Space k))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (T i).carrier δ) :
    (∑ i, (volume : Measure (Space k)).real (Y i))^2 ≤
      (volume : Measure (Space k)).real (⋃ i, Y i) *
      (∑ i, ∑ j, (44*(2:ℝ)^k*TubeVolume.unitBallVolume k)*δ^k /
        max (projectiveDistance (T i).direction (T j).direction) δ) := by
  apply finite_shading_energy_majorant Y hY
    (fun i => measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite _ _))
  intro i j
  have hpair : Y i ∩ Y j ⊆ (T i).carrier δ ∩ (T j).carrier δ :=
    Set.inter_subset_inter (hsub i) (hsub j)
  exact (measureReal_mono hpair (measure_ne_top_of_subset Set.inter_subset_left
    (TubeVolume.carrier_finite _ _))).trans
      (TubeIntersection.intersection_volume_upper (T i) (T j) hδ hδ1)


noncomputable def overlapCount (Y : I → Set X) (x : X) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => x ∈ Y i)).card

omit [MeasurableSpace X] in
lemma multiplicity_eq_card (Y : I → Set X) (x : X) :
    multiplicity Y x = (overlapCount Y x : ℝ) := by
  classical
  simp [multiplicity, oneIndicator, Set.indicator_apply, Finset.sum_boole, overlapCount]

/-- Actual pointwise overlap bounds the sum of the bin union volumes, without
an unstated measure-theoretic bounded-overlap principle. -/
theorem finite_union_overlap (Y : I → Set X)
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, μ (Y i) ≠ ∞)
    {K : ℝ}
    (hover : ∀ x, (overlapCount Y x : ℝ) ≤ K) :
    (∑ i, μ.real (Y i)) ≤ K * μ.real (⋃ i, Y i) := by
  have hU : MeasurableSet (⋃ i, Y i) := MeasurableSet.iUnion hY
  have hUf : μ (⋃ i, Y i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ := μ)
      (s := Set.univ) (f := Y) (Set.toFinite _) (fun i _ => hfin i)
  have hpoint : ∀ x, multiplicity Y x ≤ K * oneIndicator (⋃ i, Y i) x := by
    intro x
    classical
    by_cases hx : x ∈ ⋃ i, Y i
    · simpa [oneIndicator, hx, multiplicity_eq_card] using hover x
    · have hnone : ∀ i, x ∉ Y i := fun i hi => hx (Set.mem_iUnion.mpr ⟨i,hi⟩)
      simp [multiplicity, oneIndicator, hx, hnone]
  have hm := integral_mono (memLp_one_iff_integrable.mp (multiplicity_memLp Y hY hfin 1))
    ((indicator_integrable hU hUf).const_mul K) hpoint
  rw [multiplicity_integral Y hY hfin, integral_const_mul, indicator_integral hU] at hm
  exact hm

end KakeyaFormal.MeasurableEnergy
