import LebesgueRepresentatives
import HairbrushFractional

/-! The literal fine-scale marked hairbrush formulas for completed-Lebesgue
shadings. A common measurable null exceptional set is removed from EVERY
representative and the good set, so the original pointwise broadness survives.
Original full, marked, ball-intersection and union measures are unchanged. -/
namespace KakeyaFormal.LebesgueHairbrush
open MeasureTheory Set
open scoped ENNReal BigOperators
open KakeyaFormal.HairbrushBroad KakeyaFormal.HairbrushSelection
open KakeyaFormal.HairbrushFractional KakeyaFormal.MeasurableEnergy
noncomputable section
open Classical

variable {X : Type*} [MeasurableSpace X] {M : ℕ}

structure Representative (μ : Measure X) (Y : Fin M → Set X) (G : Set X) where
  full : Fin M → Set X
  good : Set X
  full_measurable : ∀ i, MeasurableSet (full i)
  good_measurable : MeasurableSet good
  full_subset : ∀ i, full i ⊆ Y i
  good_subset : good ⊆ G
  full_ae : ∀ i, full i =ᵐ[μ] Y i
  good_ae : good =ᵐ[μ] G
  membership : ∀ x ∈ good, ∀ i, x ∈ full i ↔ x ∈ Y i

/-- One common null locus is removed before transferring POINTWISE broadness.
In particular, separate a.e. representatives are not silently treated as
pointwise equal at the original good points. -/
theorem representatives (μ : Measure X) (Y : Fin M → Set X) (G : Set X)
    (hY : ∀ i, NullMeasurableSet (Y i) μ) (hG : NullMeasurableSet G μ) :
    Nonempty (Representative μ Y G) := by
  obtain ⟨O⟩ := LebesgueRepresentatives.construct μ Y Y hY hY (fun _ => Set.Subset.rfl)
  obtain ⟨H,hHsub,hHm,hHae⟩ := hG.exists_measurable_subset_ae_eq
  have hrow : ∀ᵐ x ∂μ, ∀ i, x ∈ O.full i ↔ x ∈ Y i := O.membership.mono (fun _ h => h.1)
  obtain ⟨E,hEsub,hEm,hEzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hrow)
  have hEae : ∀ᵐ x ∂μ, x ∉ E := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hEzero
  have hclean (x : X) (hx : x ∉ E) : ∀ i, x ∈ O.full i ↔ x ∈ Y i := by
    by_contra h
    exact hx (hEsub h)
  refine ⟨{
    full := fun i => O.full i \ E
    good := H \ E
    full_measurable := fun i => (O.full_measurable i).diff hEm
    good_measurable := hHm.diff hEm
    full_subset := fun i => Set.sdiff_subset.trans (O.full_subset i)
    good_subset := Set.sdiff_subset.trans hHsub
    full_ae := ?_
    good_ae := ?_
    membership := ?_ }⟩
  · intro i
    filter_upwards [hEae, O.full_ae i] with x hx hi
    apply propext
    change (x ∈ O.full i ∧ x ∉ E) ↔ x ∈ Y i
    exact ⟨fun h => (iff_of_eq hi).mp h.1, fun h => ⟨(iff_of_eq hi).mpr h, hx⟩⟩
  · filter_upwards [hEae, hHae] with x hx hg
    apply propext
    change (x ∈ H ∧ x ∉ E) ↔ x ∈ G
    exact ⟨fun h => (iff_of_eq hg).mp h.1, fun h => ⟨(iff_of_eq hg).mpr h, hx⟩⟩
  · intro x hx i
    change (x ∈ O.full i ∧ x ∉ E) ↔ x ∈ Y i
    exact ⟨fun h => (hclean x hx.2 i).mp h.1, fun h => ⟨(hclean x hx.2 i).mpr h, hx.2⟩⟩

namespace Representative
variable {μ : Measure X} {Y : Fin M → Set X} {G : Set X} (O : Representative μ Y G)

theorem full_real (i : Fin M) : μ.real (O.full i) = μ.real (Y i) := measureReal_congr (O.full_ae i)
theorem inter_real (i : Fin M) (E : Set X) :
    μ.real (O.full i ∩ E) = μ.real (Y i ∩ E) :=
  measureReal_congr ((O.full_ae i).inter Filter.EventuallyEq.rfl)
theorem total_real : (∑ i, μ.real (O.full i)) = ∑ i, μ.real (Y i) :=
  Finset.sum_congr rfl (fun i _ => O.full_real i)
theorem marked_real : markedMass (ν := μ) O.full O.good = markedMass (ν := μ) Y G := by
  apply Finset.sum_congr rfl
  intro i _
  exact measureReal_congr ((O.full_ae i).inter O.good_ae)
theorem union_real : μ.real (⋃ i, O.full i) = μ.real (⋃ i, Y i) := by
  apply measureReal_congr
  have h := ae_all_iff.mpr O.full_ae
  filter_upwards [h] with x hx
  apply propext
  change (x ∈ ⋃ i, O.full i) ↔ x ∈ ⋃ i, Y i
  simp only [Set.mem_iUnion]
  exact exists_congr (fun i => iff_of_eq (hx i))

theorem broadness {k : ℕ} {Y : Fin M → Set (Space k)} {G : Set (Space k)}
    (O : Representative volume Y G) (T : Fin M → UnitTube k) (theta : ℝ)
    (hbroad : ∀ x ∈ G, ∀ i, x ∈ Y i →
      (nearCount T Y i theta x:ℝ) ≤ multiplicity Y x/2) :
    ∀ x ∈ O.good, ∀ i, x ∈ O.full i →
      (nearCount T O.full i theta x:ℝ) ≤ multiplicity O.full x/2 := by
  intro x hx i hi
  have hrow : (Finset.univ.filter (fun j => x ∈ O.full j)) =
      Finset.univ.filter (fun j => x ∈ Y j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact O.membership x hx j
  have hh := hbroad x (O.good_subset hx) i (O.full_subset i hi)
  simpa only [nearCount, multiplicity_eq_card, overlapCount, hrow] using hh

end Representative

/-- Formula (4.8) in its exact squared form, for ORIGINAL completed-measurable
full rows and good set. The original pointwise broadness is the only angular
incidence hypothesis, and all original measures appear in the conclusion. -/
theorem broad_hairbrush_squared {k : ℕ}
    (T : Fin M → UnitTube (k+2)) (Y : Fin M → Set (Space (k+2))) (G : Set (Space (k+2)))
    {δ theta r lam L B alpha : ℝ} (J : ℕ) (hM : 0 < M)
    (hδ : 0 < δ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hscale : 88*δ ≤ r*theta)
    (hlam : 0 ≤ lam) (hL : 0 < L) (hJL : (J:ℝ)+1 ≤ L)
    (hlogL : Real.logb 2 (2/δ)+2 ≤ L) (htop : (M:ℝ) ≤ (2:ℝ)^J)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (T i).direction (T j).direction)
    (hY : ∀ i, NullMeasurableSet (Y i) volume) (hsub : ∀ i, Y i ⊆ (T i).carrier δ)
    (hG : NullMeasurableSet G volume)
    (hgood : (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 ≤ markedMass (ν := volume) Y G)
    (hbroad : ∀ x ∈ G, ∀ i, x ∈ Y i →
      (nearCount T Y i theta x:ℝ) ≤ MeasurableEnergy.multiplicity Y x/2)
    (hmass : ∀ i, lam*δ^(k+1) ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hsmall : B*r^alpha ≤ 1/2) :
    markedMass (ν := volume) Y G*lam^3*δ^k*(r*theta)^(k+1)/(broadConstant k*L^5) ≤
      ((volume : Measure (Space (k+2))).real (⋃ i, Y i))^2 := by
  have : Nonempty (Fin M) := Fin.pos_iff_nonempty.mp hM
  obtain ⟨O⟩ := representatives volume Y G hY hG
  have hh := HairbrushBroad.broad_hairbrush_squared T O.full O.good J
    hδ htheta htheta1 hr hr1 hscale hlam hL hJL hlogL
    (by simpa only [Fintype.card_fin] using htop) hdir
    O.full_measurable (fun i => (O.full_subset i).trans (hsub i)) O.good_measurable
    (by rw [O.total_real,O.marked_real]; exact hgood)
    (O.broadness T theta hbroad)
    (fun i => by rw [O.full_real]; exact hmass i)
    (fun i p t ht ht1 => by rw [O.inter_real,O.full_real]; exact hends i p t ht ht1)
    hsmall
  simpa only [O.marked_real,O.union_real] using hh


/-- The unsquared displayed formula (4.8), with its exact square-root
marked mass and dimension-dependent coefficient. -/
theorem broad_hairbrush_linear {k : ℕ}
    (T : Fin M → UnitTube (k+2)) (Y : Fin M → Set (Space (k+2))) (G : Set (Space (k+2)))
    {δ theta r lam L B alpha : ℝ} (J : ℕ) (hM : 0 < M)
    (hδ : 0 < δ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hscale : 88*δ ≤ r*theta)
    (hlam : 0 ≤ lam) (hL : 0 < L) (hJL : (J:ℝ)+1 ≤ L)
    (hlogL : Real.logb 2 (2/δ)+2 ≤ L) (htop : (M:ℝ) ≤ (2:ℝ)^J)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (T i).direction (T j).direction)
    (hY : ∀ i, NullMeasurableSet (Y i) volume) (hsub : ∀ i, Y i ⊆ (T i).carrier δ)
    (hG : NullMeasurableSet G volume)
    (hgood : (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 ≤ markedMass (ν := volume) Y G)
    (hbroad : ∀ x ∈ G, ∀ i, x ∈ Y i →
      (nearCount T Y i theta x:ℝ) ≤ MeasurableEnergy.multiplicity Y x/2)
    (hmass : ∀ i, lam*δ^(k+1) ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hsmall : B*r^alpha ≤ 1/2) :
    (r*theta)^((k+1:ℕ)/2:ℝ) * Real.sqrt (markedMass (ν := volume) Y G*lam^3*δ^k) /
        (Real.sqrt (broadConstant k)*L^((5:ℝ)/2)) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  have hsq := broad_hairbrush_squared T Y G J hM hδ htheta htheta1 hr hr1 hscale
    hlam hL hJL hlogL htop hdir hY hsub hG hgood hbroad hmass hends hsmall
  have hW : 0 ≤ markedMass (ν := volume) Y G :=
    Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hC := broadConstant_pos k
  have hrt : ((r*theta)^((k+1:ℕ)/2:ℝ))^2 = (r*theta)^(k+1) := by
    simpa only [Real.rpow_natCast] using half_power_square (by positivity : 0 ≤ r*theta) (k+1:ℕ)
  have hLpow : (L^((5:ℝ)/2))^2 = L^5 := by simpa using half_power_square hL.le 5
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ markedMass (ν := volume) Y G*lam^3*δ^k)
  have hCroot := Real.sq_sqrt hC.le
  have hleft : ((r*theta)^((k+1:ℕ)/2:ℝ) * Real.sqrt (markedMass (ν := volume) Y G*lam^3*δ^k))^2 =
      markedMass (ν := volume) Y G*lam^3*δ^k*(r*theta)^(k+1) := by
    rw [mul_pow,hrt,hroot]
    ring
  have hright : ((volume : Measure (Space (k+2))).real (⋃ i, Y i) *
      (Real.sqrt (broadConstant k)*L^((5:ℝ)/2)))^2 =
      ((volume : Measure (Space (k+2))).real (⋃ i, Y i))^2 * (broadConstant k*L^5) := by
    simp only [mul_pow,hCroot,hLpow]
  have hh := (div_le_iff₀ (by positivity : 0 < broadConstant k*L^5)).mp hsq
  apply (div_le_iff₀ (by positivity : 0 < Real.sqrt (broadConstant k)*L^((5:ℝ)/2))).mpr
  have hn : 0 ≤ (volume : Measure (Space (k+2))).real (⋃ i, Y i) *
      (Real.sqrt (broadConstant k)*L^((5:ℝ)/2)) := by positivity
  nlinarith

/-- The displayed linear marked real-cap estimate (4.16), with the exact
physical exponents and coefficient of the Borel theorem, now for original
completed-measurable input sets. -/
theorem real_cap_hairbrush_linear {k : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) (G : Set (Space (k+2)))
    {δ theta r lam L B alpha m A upper : ℝ} (J : ℕ) (hM : 0 < M)
    (hδ : 0 < δ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hscale : 88*δ ≤ r*theta)
    (hlam : 0 ≤ lam) (hL : 0 < L) (hJL : (J:ℝ)+1 ≤ L)
    (hlogL : Real.logb 2 (2/δ)+2 ≤ L) (htop : (M:ℝ) ≤ (2:ℝ)^J)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (F.tube i).direction (F.tube j).direction)
    (hY : ∀ i, NullMeasurableSet (Y i) volume) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hG : NullMeasurableSet G volume)
    (hgood : (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 ≤ markedMass (ν := volume) Y G)
    (hbroad : ∀ x ∈ G, ∀ i, x ∈ Y i →
      (nearCount F.tube Y i theta x:ℝ) ≤ MeasurableEnergy.multiplicity Y x/2)
    (hmass : ∀ i, lam*δ^(k+1) ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hsmall : B*r^alpha ≤ 1/2) (hA : 0 < A) (hu : 0 < upper)
    (hcap : F.CapBound δ m A)
    (hupper : ∀ i, (volume : Measure (Space (k+2))).real (Y i) ≤ upper*δ^(k+1)) :
    markedMass (ν := volume) Y G*lam^((3:ℝ)/2)*δ^((m-1)/2)*(r*theta)^((k+1:ℕ)/2:ℝ)/
        (Real.sqrt (fractionalConstant k*A*upper)*L^((5:ℝ)/2)) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
  obtain ⟨O⟩ := representatives volume Y G hY hG
  have hh := HairbrushFractional.real_cap_hairbrush_linear F O.full O.good J hM
    hδ htheta htheta1 hr hr1 hscale hlam hL hJL hlogL htop hdir
    O.full_measurable (fun i => (O.full_subset i).trans (hsub i)) O.good_measurable
    (by rw [O.total_real,O.marked_real]; exact hgood)
    (O.broadness F.tube theta hbroad)
    (fun i => by rw [O.full_real]; exact hmass i)
    (fun i p t ht ht1 => by rw [O.inter_real,O.full_real]; exact hends i p t ht ht1)
    hsmall hA hu hcap (fun i => by rw [O.full_real]; exact hupper i)
  simpa only [O.marked_real,O.union_real] using hh

end
end KakeyaFormal.LebesgueHairbrush
