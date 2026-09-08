import DiscreteMeasurable
import CapCover
import LogLoss

/-! Uniform measurable real-cap estimates for actual tube shadings. All
configuration parameters vary after the estimate constant has been chosen. -/
namespace KakeyaFormal
open MeasureTheory Set Finset
open scoped BigOperators ENNReal
noncomputable section

structure MeasurableNormalization where
  separation : ℝ
  radius : ℝ
  separation_pos : 0 < separation
  radius_pos : 0 < radius

structure MeasurableConfiguration (k : ℕ) (geom : MeasurableNormalization) (m : ℝ) where
  M : ℕ
  δ : ℝ
  lam : ℝ
  A : ℝ
  family : TubeFamily k M
  shading : Fin M → Set (Space k)
  scale_pos : 0 < δ
  scale_le_one : δ ≤ 1
  density_pos : 0 < lam
  density_le_one : lam ≤ 1
  cap_ge_one : 1 ≤ A
  shading_measurable : ∀ i, MeasurableSet (shading i)
  shading_subset : ∀ i, shading i ⊆ (family.tube i).carrier δ
  shading_mass : ∀ i, lam * (volume : Measure (Space k)).real ((family.tube i).carrier δ) ≤
    (volume : Measure (Space k)).real (shading i)
  separated : family.Separated (geom.separation * δ)
  bounded : family.Bounded geom.radius
  cap_bound : family.CapBound δ m A

def MeasurableConfiguration.unionSet {k geom m} (F : MeasurableConfiguration k geom m) : Set (Space k) :=
  ⋃ i, F.shading i

def MeasurableEstimate (k : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : MeasurableNormalization, ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ F : MeasurableConfiguration k geom m,
      c * F.A⁻¹ * F.δ ^ ((k : ℝ)+m-d+ε) * F.lam ^ p * F.M ≤
        (volume : Measure (Space k)).real F.unionSet

/-- The manuscript's equivalent formulation using the sum of actual tube
volumes, rather than a fixed-dimensional normalization times tube count. -/
def VolumeMeasurableEstimate (k : ℕ) (m d p : ℝ) : Prop :=
  ∀ geom : MeasurableNormalization, ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
    ∀ F : MeasurableConfiguration k geom m,
      c * F.A⁻¹ * F.δ ^ (m+1-d+ε) * F.lam ^ p *
        (∑ i, (volume : Measure (Space k)).real ((F.family.tube i).carrier F.δ)) ≤
          (volume : Measure (Space k)).real F.unionSet

def RealCapMeasurableEstimate (m d p : ℝ) : Prop :=
  ∀ k : ℕ, 0 < k → m ≤ (k : ℝ)-1 → MeasurableEstimate k m d p

namespace MeasurableConversion
open Occupancy OccupancySelection DiscreteMeasurable

/-- Finite threshold crossing constructs a mass-comparable subset. -/
theorem finite_mass_trim {Q : Type*} (S : Finset Q) (w : Q → ℝ) {a : ℝ}
    (ha : 0 < a) (hupper : ∀ q ∈ S, w q ≤ a) (htotal : a ≤ ∑ q ∈ S, w q) :
    ∃ R ⊆ S, a ≤ ∑ q ∈ R, w q ∧ (∑ q ∈ R, w q) ≤ 2*a := by
  classical
  let candidates := S.powerset.filter (fun R => a ≤ ∑ q ∈ R, w q)
  have hne : candidates.Nonempty := ⟨S,mem_filter.mpr ⟨mem_powerset.mpr (by rfl),htotal⟩⟩
  obtain ⟨R,hR,hmin⟩ := candidates.exists_min_image card hne
  have hRS : R ⊆ S := mem_powerset.mp (mem_filter.mp hR).1
  have hmass : a ≤ ∑ q ∈ R, w q := (mem_filter.mp hR).2
  have hRne : R.Nonempty := by
    by_contra hn
    simp only [Finset.not_nonempty_iff_eq_empty.mp hn,sum_empty] at hmass
    linarith
  obtain ⟨q,hq⟩ := hRne
  have herase : (∑ z ∈ R.erase q, w z) < a := by
    by_contra hn
    have hcan : R.erase q ∈ candidates := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset _ _).trans hRS),le_of_not_gt hn⟩
    have hh := hmin (R.erase q) hcan
    have he := card_erase_lt_of_mem hq
    omega
  refine ⟨R,hRS,hmass,?_⟩
  have hsum := sum_erase_add R w hq
  linarith [hupper q (hRS hq)]

/-- Bounded measurable shadings are actually shrunk to the required comparable
mass using a fine finite half-open grid and finite threshold crossing. -/
theorem measurable_mass_trim {k : ℕ} (hk : 0 < k) {Y : Set (Space k)}
    (hY : MeasurableSet Y) {R a : ℝ} (hbounded : ∀ x ∈ Y, ‖x‖ ≤ R)
    (ha : 0 < a) (hmass : a ≤ (volume : Measure (Space k)).real Y) :
    ∃ Z ⊆ Y, MeasurableSet Z ∧ a ≤ (volume : Measure (Space k)).real Z ∧
      (volume : Measure (Space k)).real Z ≤ 2*a := by
  let η := min 1 a
  have hη : 0 < η := lt_min (by norm_num) ha
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηa : η ≤ a := min_le_right _ _
  have hηpow : η ^ k ≤ a := by
    apply le_trans ?_ hηa
    calc
      η ^ k ≤ η ^ 1 := pow_le_pow_of_le_one hη.le hη1 (by omega)
      _ = η := pow_one _
  let labels := GridGeometry.gridBox (fun _ : Fin k => 0) (Nat.ceil (R/η+(k:ℝ)/2)+1)
  let C := GridCells.finiteCellSystem hη labels
  have hcover : Y ⊆ C.covered := GridCells.bounded_set_covered hη hbounded
  have htotal : a ≤ ∑ q, C.cellMass Y q := by rw [← C.mass_decomposition hY hcover]; exact hmass
  have hupper (q : Fin labels.card) (_ : q ∈ (univ : Finset (Fin labels.card))) : C.cellMass Y q ≤ a := by
    apply le_trans (C.cellMass_le_volume Y q)
    change (volume : Measure (Space k)).real (GridCells.gridCell η (labels.equivFin.symm q).val) ≤ a
    rw [GridCells.real_volume_gridCell hη.le]
    exact hηpow
  obtain ⟨cells,hcells,hlower,hupper⟩ := finite_mass_trim univ (C.cellMass Y) ha hupper htotal
  refine ⟨Y ∩ ⋃ q ∈ cells, C.cell q,inter_subset_left,?_,?_,?_⟩
  · exact hY.inter (MeasurableSet.biUnion cells.countable_toSet (fun q _ => C.measurable q))
  · rwa [C.class_mass cells hY]
  · rwa [C.class_mass cells hY]

/-- Uniformly bounded bases and unit tube lengths bound the actual measurable
union, supplying a finite grid cover and finite Lebesgue measure. -/
theorem carrier_norm_bound {k : ℕ} (T : UnitTube k) {R δ : ℝ}
    (hbase : ‖T.base‖ ≤ R) (hδ1 : δ ≤ 1) {x : Space k} (hx : x ∈ T.carrier δ) :
    ‖x‖ ≤ R+2 := by
  obtain ⟨t,ht,hxt⟩ := hx
  have htpos : 0 ≤ t := ht.1
  have haxis : ‖T.axisPoint t‖ ≤ R+1 := by
    calc
      _ ≤ ‖T.base‖ + ‖t • T.direction‖ := norm_add_le _ _
      _ = ‖T.base‖ + t := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg htpos,T.unit_direction,mul_one]
      _ ≤ R+1 := add_le_add hbase ht.2
  have htri := dist_triangle x (T.axisPoint t) (0 : Space k)
  simp only [dist_zero_right] at htri
  linarith

/-- The occupancy and tube class budgets are bounded by one scale logarithm,
with constants depending only on the fixed occupancy cutoff coefficient. -/
theorem class_log_bounds {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ KB KT : ℝ, 0 < KB ∧ 0 < KT ∧
      ∀ {δ lam B Bt : ℝ}, 0 < δ → δ ≤ 1 → δ < lam → 0 < lam → 1 ≤ B →
        B ≤ Real.log (1 / (t*lam)) / Real.log 2 + 2 →
        Bt ≤ Real.log (8*B) / Real.log 2 + 2 →
        B ≤ KB * Real.log (2 / δ) ∧ Bt ≤ KT * B := by
  let l2 := Real.log 2
  let A := Real.log (1/t) / l2 + 2
  have hl2 : 0 < l2 := Real.log_pos (by norm_num)
  have hlogt : 0 ≤ Real.log (1/t) := Real.log_nonneg ((le_div_iff₀ ht).mpr (by simpa using ht1))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨(A+1)/l2,8/l2+2,by positivity,by positivity,?_⟩
  intro δ lam B Bt hδ hδ1 hδlam hlam hB1 hB hBt
  have hL : l2 ≤ Real.log (2/δ) := Real.log_le_log (by norm_num)
    ((le_div_iff₀ hδ).mpr (by linarith))
  have hloglam : Real.log (1/lam) ≤ Real.log (1/δ) :=
    Real.log_le_log (one_div_pos.mpr hlam) ((one_div_le_one_div_of_le hδ hδlam.le))
  have hlogδ : Real.log (1/δ) ≤ Real.log (2/δ) :=
    Real.log_le_log (one_div_pos.mpr hδ) (div_le_div_of_nonneg_right (by norm_num) hδ.le)
  have hlogs : Real.log (1/(t*lam)) ≤ Real.log (1/t) + Real.log (2/δ) := by
    rw [one_div,Real.log_inv,Real.log_mul ht.ne' hlam.ne']
    have hlt : Real.log (1/t) = -Real.log t := by rw [one_div,Real.log_inv]
    rw [hlt]
    have hh := hloglam.trans hlogδ
    rw [one_div,Real.log_inv] at hh
    linarith
  have hB' : B ≤ A + Real.log (2/δ)/l2 := by
    have hh := div_le_div_of_nonneg_right hlogs hl2.le
    rw [add_div] at hh
    dsimp [A,l2] at *
    linarith
  constructor
  · have hb := (le_div_iff₀ hl2).mp (show B - A ≤ Real.log (2/δ)/l2 by linarith)
    have hfixed := mul_le_mul_of_nonneg_left hL hA
    have hid : (A+1)/l2 * Real.log (2/δ) = ((A+1)*Real.log (2/δ))/l2 := by ring
    rw [hid]
    apply (le_div_iff₀ hl2).mpr
    nlinarith
  · have hlogB := Real.log_le_sub_one_of_pos (by positivity : 0 < 8*B)
    have hh := (le_div_iff₀ hl2).mp (show Bt-2 ≤ Real.log (8*B)/l2 by exact sub_le_iff_le_add.mpr hBt)
    have hid : (8/l2+2)*B = (8*B+2*B*l2)/l2 := by field_simp
    rw [hid]
    apply (le_div_iff₀ hl2).mpr
    nlinarith

/-- Uniform absorption of the actual two class losses. The constant is chosen
before the scale, density and selected class depths. -/
theorem uniform_class_loss {t p ε : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ {δ lam B Bt : ℝ},
      0 < δ → δ ≤ 1 → δ < lam → 0 < lam → 1 ≤ B →
      B ≤ Real.log (1 / (t*lam)) / Real.log 2 + 2 →
      Bt ≤ Real.log (8*B) / Real.log 2 + 2 →
      B ^ (p+1) * Bt ≤ K * (1/δ) ^ ε := by
  obtain ⟨KB,KT,hKB,hKT,hbounds⟩ := class_log_bounds ht ht1
  obtain ⟨KL,hKL,hlog⟩ := log_power_uniform_bound (by linarith : 0 ≤ p+2) hε
  refine ⟨KT * KB^(p+2) * KL,by positivity,?_⟩
  intro δ lam B Bt hδ hδ1 hδlam hlam hB hocc htube
  obtain ⟨hBB,hBt⟩ := hbounds hδ hδ1 hδlam hlam hB hocc htube
  have hBpos : 0 < B := by linarith
  have hLpos : 0 < Real.log (2/δ) := Real.log_pos ((lt_div_iff₀ hδ).mpr (by linarith))
  have hfirst := mul_le_mul_of_nonneg_left hBt (Real.rpow_nonneg hBpos.le (p+1))
  have hid : B^(p+1)*(KT*B) = KT*B^(p+2) := by
    have heq : B^(p+2) = B^(p+1)*B := by
      calc
        B^(p+2) = B^((p+1)+1) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hBpos,Real.rpow_one]
    rw [heq]
    ring
  rw [hid] at hfirst
  have hpower := Real.rpow_le_rpow hBpos.le hBB (by linarith : 0 ≤ p+2)
  rw [Real.mul_rpow hKB.le hLpos.le] at hpower
  have hN : (1 : ℝ) ≤ 1/δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
  have hlog' : Real.log (2/δ)^(p+2) ≤ KL*(1/δ)^ε := by
    simpa only [mul_one_div] using hlog (1/δ) hN
  have hsecond := mul_le_mul_of_nonneg_left hpower hKT.le
  have hthird := mul_le_mul_of_nonneg_left hlog'
    (mul_nonneg hKT.le (Real.rpow_nonneg hKB.le (p+2)))
  calc
    B^(p+1)*Bt ≤ KT*B^(p+2) := hfirst
    _ ≤ KT*(KB^(p+2)*Real.log (2/δ)^(p+2)) := hsecond
    _ = (KT*KB^(p+2))*Real.log (2/δ)^(p+2) := by ring
    _ ≤ (KT*KB^(p+2))*(KL*(1/δ)^ε) := hthird
    _ = _ := by ring

/-- Exact specialization of the finite occupancy inequality to comparable
measurable shading masses; the class loss is displayed as B^(p+1)Bt. -/
theorem specialized_expression {k : ℕ} {δ lam c₀ C B Bt c A m d p ε M : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hc₀ : 0 < c₀) (hC : 0 < C)
    (hB : 0 < B) (hBt : 0 < Bt) :
    let V := δ ^ k
    let base := c₀ * lam * V / δ
    c * A⁻¹ * δ^(m-d+ε) * (δ*base/(16*C*B*V))^p * (M*base/(4*B*Bt*(2*base))) * V =
      (c * (c₀/(16*C))^p / 8) * A⁻¹ * δ^((k:ℝ)+m-d+ε) * lam^p * M / (B^(p+1)*Bt) := by
  intro V base
  have hV : 0 < V := pow_pos hδ k
  have hbase : 0 < base := div_pos (mul_pos (mul_pos hc₀ hlam) hV) hδ
  have hfirst : δ*base/(16*C*B*V) = (c₀/(16*C))*lam/B := by
    dsimp [base]
    field_simp
  have hsecond : M*base/(4*B*Bt*(2*base)) = M/(8*B*Bt) := by field_simp; ring
  rw [hfirst,hsecond,Real.div_rpow (by positivity) hB.le,
    Real.mul_rpow (by positivity) hlam.le]
  have hscale : δ^(m-d+ε)*V = δ^((k:ℝ)+m-d+ε) := by
    dsimp [V]
    rw [← Real.rpow_natCast,← Real.rpow_add hδ]
    congr 1
    ring
  have hBpow : B^(p+1) = B^p*B := by rw [Real.rpow_add hB,Real.rpow_one]
  rw [hBpow]
  calc
    _ = (c * (c₀/(16*C))^p / 8) * A⁻¹ * (δ^(m-d+ε)*V) * lam^p * M / ((B^p*B)*Bt) := by ring
    _ = _ := by rw [hscale]

/-- Convert a uniform upper bound on the class loss into the requested extra
scale power, with all exponents and positive factors accounted for. -/
theorem absorb_class_loss {δ lam c A D p M B Bt K ε : ℝ}
    (hδ : 0 < δ) (hlam : 0 ≤ lam) (hc : 0 ≤ c) (hA : 0 < A)
    (hM : 0 ≤ M) (hB : 0 < B) (hBt : 0 < Bt) (hK : 0 < K)
    (hloss : B^(p+1)*Bt ≤ K*(1/δ)^ε) :
    (c/K)*A⁻¹*δ^(D+ε)*lam^p*M ≤ c*A⁻¹*δ^D*lam^p*M/(B^(p+1)*Bt) := by
  have hL : 0 < B^(p+1)*Bt := mul_pos (Real.rpow_pos_of_pos hB _) hBt
  have hinv := one_div_le_one_div_of_le hL hloss
  have hid : 1/(K*(1/δ)^ε) = δ^ε/K := by
    have hpow : (1/δ)^ε = (δ^ε)⁻¹ := by rw [one_div,Real.inv_rpow hδ.le]
    have hne : δ^ε ≠ 0 := (Real.rpow_pos_of_pos hδ ε).ne'
    rw [hpow]
    field_simp
  rw [hid] at hinv
  have hcoef : 0 ≤ c*A⁻¹*δ^D*lam^p*M := by positivity
  have hh := mul_le_mul_of_nonneg_left hinv hcoef
  calc
    _ = (c*A⁻¹*δ^D*lam^p*M)*(δ^ε/K) := by rw [Real.rpow_add hδ]; ring
    _ ≤ (c*A⁻¹*δ^D*lam^p*M)*(1/(B^(p+1)*Bt)) := hh
    _ = _ := by ring

theorem union_measurable {k geom m} (F : MeasurableConfiguration k geom m) :
    MeasurableSet F.unionSet := MeasurableSet.iUnion F.shading_measurable

theorem union_norm_bound {k geom m} (F : MeasurableConfiguration k geom m) :
    ∀ x ∈ F.unionSet, ‖x‖ ≤ geom.radius+2 := by
  intro x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  exact carrier_norm_bound (F.family.tube i) (F.bounded i) F.scale_le_one (F.shading_subset i hi)

theorem union_finite {k geom m} (F : MeasurableConfiguration k geom m) :
    (volume : Measure (Space k)) F.unionSet ≠ ∞ := by
  apply measure_ne_top_of_subset (μ := (volume : Measure (Space k))) (s := Metric.closedBall (0 : Space k) (geom.radius+2)) ?_
    (isCompact_closedBall (0 : Space k) (geom.radius+2)).measure_lt_top.ne
  intro x hx
  simpa only [Metric.mem_closedBall,dist_zero_right] using union_norm_bound F x hx

def discreteNormalization (k : ℕ) (geom : MeasurableNormalization) : Normalization where
  width := 1 + (k : ℝ)/2
  separation := geom.separation
  radius := geom.radius
  width_pos := by positivity
  separation_pos := geom.separation_pos
  radius_pos := geom.radius_pos

/-- The high-density branch with its fully uniform constants. Every measurable
trimming, grid cover, cutoff, class and normalized configuration is constructed. -/
theorem high_density_bound {k : ℕ} (hk : 0 < k) (geom : MeasurableNormalization)
    {m d p ε c c₀ t K : ℝ} (hp : 1 ≤ p) (hc : 0 < c) (hc₀ : 0 < c₀)
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : 0 < K)
    (hvolume : ∀ T : UnitTube k, ∀ δ : ℝ, 0 < δ →
      c₀*δ^k/δ ≤ (volume : Measure (Space k)).real (T.carrier δ))
    (hcut : 4*t*gridCountConstant k (discreteNormalization k geom).width ≤ c₀)
    (hestimate : ∀ H : ShadedConfiguration k (discreteNormalization k geom) m,
      c*H.A⁻¹*H.δ^(m-d+ε/2)*H.lam^p*H.M ≤ (H.family.unionCells.card : ℝ))
    (hbudget : ∀ {δ lam B Bt : ℝ}, 0 < δ → δ ≤ 1 → δ < lam → 0 < lam → 1 ≤ B →
      B ≤ Real.log (1/(t*lam))/Real.log 2+2 → Bt ≤ Real.log (8*B)/Real.log 2+2 →
      B^(p+1)*Bt ≤ K*(1/δ)^(ε/2))
    (F : MeasurableConfiguration k geom m) (hM : 0 < F.M) (hsmall : F.δ < F.lam) :
    (c*(c₀/(16*gridCountConstant k (discreteNormalization k geom).width))^p/(8*K)) *
      F.A⁻¹ * F.δ^((k:ℝ)+m-d+ε) * F.lam^p * F.M ≤
        (volume : Measure (Space k)).real F.unionSet := by
  classical
  let C := gridCountConstant k (discreteNormalization k geom).width
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (gridCountConstant_ge_one _ _)
  let V := F.δ^k
  let base := c₀*F.lam*V/F.δ
  let lo := t*F.lam
  have hV : 0 < V := pow_pos F.scale_pos k
  have hbase : 0 < base := div_pos (mul_pos (mul_pos hc₀ F.density_pos) hV) F.scale_pos
  have hlo : 0 < lo := mul_pos ht F.density_pos
  have hlo1 : lo ≤ 1 := by
    calc
      lo ≤ 1*1 := mul_le_mul ht1 F.density_le_one F.density_pos.le (by norm_num)
      _ = 1 := one_mul _
  have hmass (i : Fin F.M) : base ≤ (volume : Measure (Space k)).real (F.shading i) := by
    have hh := mul_le_mul_of_nonneg_left (hvolume (F.family.tube i) F.δ F.scale_pos) F.density_pos.le
    apply le_trans ?_ (F.shading_mass i)
    convert hh using 1
    dsimp [base,V]
    ring
  have hbounded (i : Fin F.M) : ∀ x ∈ F.shading i, ‖x‖ ≤ geom.radius+2 := by
    intro x hx
    exact carrier_norm_bound _ (F.bounded i) F.scale_le_one (F.shading_subset i hx)
  choose Z hZY hZmeas hZlower hZupper using (fun i => measurable_mass_trim hk
    (F.shading_measurable i) (hbounded i) hbase (hmass i))
  have hZU (i : Fin F.M) : Z i ⊆ F.unionSet := fun _ hx =>
    Set.mem_iUnion.mpr ⟨i,hZY i hx⟩
  have hphysical (i : Fin F.M) : Z i ⊆ (F.family.tube i).carrier (1*F.δ) := by
    simpa only [one_mul] using (hZY i).trans (F.shading_subset i)
  let cells := GridGeometry.gridBox (fun _ : Fin k => 0)
    (Nat.ceil ((geom.radius+2)/F.δ+(k:ℝ)/2)+1)
  let labels : Fin cells.card → Cell k := fun i => (cells.equivFin.symm i).val
  have hinj : Function.Injective labels := Subtype.val_injective.comp cells.equivFin.symm.injective
  have hcover : F.unionSet ⊆ (GridCells.cellSystem F.scale_pos labels hinj).covered :=
    GridCells.bounded_set_covered F.scale_pos (union_norm_bound F)
  have hcutoff : lo*F.δ^k*(gridCountConstant k (1+(k:ℝ)/2)/F.δ) ≤ base/2 := by
    have hh := mul_le_mul_of_nonneg_right hcut
      (div_nonneg (mul_nonneg F.density_pos.le hV.le) F.scale_pos.le)
    change 4*t*C*(F.lam*V/F.δ) ≤ c₀*(F.lam*V/F.δ) at hh
    change lo*V*(C/F.δ) ≤ base/2
    have hb : 0 ≤ c₀*F.lam*V/F.δ := hbase.le
    dsimp [lo,base]
    ring_nf at hh hb ⊢
    nlinarith
  obtain ⟨Jocc,Jtube,hocclog,htubelog,hretTube,hret,hselection⟩ := actual_occupancy_selection
    F.scale_pos F.scale_le_one labels hinj F.family F.unionSet Z (union_measurable F) hcover
    hZmeas hZU hphysical hM hlo hlo1 hbase hZlower hZupper hcutoff
  obtain ⟨s⟩ := hselection
  let B : ℝ := (Jocc+1 : ℕ)
  let Bt : ℝ := (Jtube+1 : ℕ)
  have hB : 0 < B := by dsimp [B]; positivity
  have hBt : 0 < Bt := by dsimp [Bt]; positivity
  have hB1 : 1 ≤ B := by dsimp [B]; exact_mod_cast (show 1 ≤ Jocc+1 by omega)
  have hocc : B ≤ Real.log (1/(t*F.lam))/Real.log 2+2 := by
    simpa only [Nat.cast_add,Nat.cast_one,lo,B] using hocclog
  have hratio : (2*base)/(base/(4*B)) = 8*B := by field_simp; ring
  have htube : Bt ≤ Real.log (8*B)/Real.log 2+2 := by
    change (Jtube:ℝ)+1 ≤ Real.log ((2*base)/(base/(4*B)))/Real.log 2+2 at htubelog
    rw [hratio] at htubelog
    simpa only [Bt,Nat.cast_add,Nat.cast_one] using htubelog
  have hloss := hbudget F.scale_pos F.scale_le_one hsmall F.density_pos hB1 hocc htube
  have hvol (q : Fin cells.card) : (volume : Measure (Space k)).real
      ((GridCells.cellSystem F.scale_pos labels hinj).cell q) = V :=
    GridCells.real_volume_gridCell F.scale_pos.le (labels q)
  have hm := selection_measure_class_losses F.scale_pos labels hinj F.family F.unionSet Z
    (highOccupancyCells (GridCells.cellSystem F.scale_pos labels hinj) F.unionSet lo V) s
    (discreteNormalization k geom) F.scale_le_one F.cap_ge_one (by rfl) hphysical
    F.separated F.bounded F.cap_bound hV hlo hM hbase (by positivity : 0 < 2*base)
    hvol hret hc.le hp hestimate
  have hid := specialized_expression (k := k) (δ := F.δ) (lam := F.lam) (c₀ := c₀)
    (C := C) (B := B) (Bt := Bt) (c := c) (A := F.A) (m := m) (d := d) (p := p)
    (ε := ε/2) (M := (F.M:ℝ)) F.scale_pos F.density_pos hc₀ hC hB hBt
  change _ = (c*(c₀/(16*C))^p/8)*F.A⁻¹*F.δ^((k:ℝ)+m-d+ε/2)*F.lam^p*F.M/(B^(p+1)*Bt) at hid
  rw [hid] at hm
  have ha := absorb_class_loss (A := F.A) (D := (k:ℝ)+m-d+ε/2)
    (c := c*(c₀/(16*C))^p/8) F.scale_pos F.density_pos.le (by positivity)
    (by linarith [F.cap_ge_one]) (Nat.cast_nonneg F.M) hB hBt hK hloss
  have heq : (k:ℝ)+m-d+ε/2+ε/2 = (k:ℝ)+m-d+ε := by ring
  rw [heq] at ha
  change (c*(c₀/(16*C))^p/(8*K))*F.A⁻¹*F.δ^((k:ℝ)+m-d+ε)*F.lam^p*F.M ≤ _
  simpa only [div_div] using ha.trans hm

/-- Full uniform measurable conversion, including actual measurable trimming,
the high-density class construction and logarithmic absorption, and the actual
one-tube low-density branch. No geometric realization hypotheses remain. -/
theorem discrete_to_measurable_succ {k : ℕ} {m d p : ℝ}
    (hdiscrete : DiscreteEstimate (k+1) m d p) (hd : 1 ≤ d) (hdp : d ≤ p) :
    MeasurableEstimate (k+1) m d p := by
  intro geom ε hε
  let discGeom := discreteNormalization (k+1) geom
  let C := gridCountConstant (k+1) discGeom.width
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) (gridCountConstant_ge_one _ _)
  let c₀ := TubeVolume.unitBallVolume (k+1) / (2 : ℝ)^((k+1)+1)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity [TubeVolume.unitBallVolume_pos (k+1)]
  let t := min 1 (c₀/(4*C))
  have ht : 0 < t := lt_min (by norm_num) (div_pos hc₀ (by positivity))
  have ht1 : t ≤ 1 := min_le_left _ _
  have hcut : 4*t*C ≤ c₀ := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*C)).mp (min_le_right 1 (c₀/(4*C)))
    dsimp [t]
    nlinarith
  have hp : 1 ≤ p := hd.trans hdp
  obtain ⟨K,hK,hbudget⟩ := uniform_class_loss ht ht1 hp (by linarith : 0 < ε/2)
  obtain ⟨c,hc,hestimate⟩ := hdiscrete discGeom (ε/2) (by linarith)
  let capC := ProjectiveGeometry.packingConstant k
  have hcapC : 0 < capC := lt_of_lt_of_le (by norm_num) (ProjectiveGeometry.packingConstant_ge_one k)
  let csmall := c₀/capC
  let clarge := c*(c₀/(16*C))^p/(8*K)
  have hcsmall : 0 < csmall := div_pos hc₀ hcapC
  have hclarge : 0 < clarge := by dsimp [clarge]; positivity
  refine ⟨min csmall clarge,lt_min hcsmall hclarge,?_⟩
  intro F
  have hA : 0 < F.A := lt_of_lt_of_le (by norm_num) F.cap_ge_one
  have hδ : 0 < F.δ := F.scale_pos
  have hlam : 0 < F.lam := F.density_pos
  have hfactor : 0 ≤ F.A⁻¹ * F.δ^((k+1:ℕ)+m-d+ε) * F.lam^p * F.M := by positivity
  by_cases hM : 0 < F.M
  · by_cases hsmall : F.lam ≤ F.δ
    · let i : Fin F.M := ⟨0,hM⟩
      have hcap := CapCover.cap_bound_total_count_scale F.family F.scale_pos F.scale_le_one hA.le F.cap_bound
      have hYU : F.shading i ⊆ F.unionSet := fun _ hx => Set.mem_iUnion.mpr ⟨i,hx⟩
      have hbound := small_density_actual_tube (M := F.M) (F.family.tube i)
        F.scale_pos F.scale_le_one F.density_pos hsmall hp hdp hA hcapC hcap hYU
        (union_finite F) (F.shading_mass i)
      have hpow : F.δ^((k+1:ℕ)+m-d+ε) ≤ F.δ^((k+1:ℕ)+m-d) :=
        Real.rpow_le_rpow_of_exponent_ge F.scale_pos F.scale_le_one (by linarith)
      have hpowmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg hcsmall.le (inv_nonneg.mpr hA.le)))
          (Real.rpow_nonneg F.density_pos.le p)) (Nat.cast_nonneg F.M)
      have hfirst := mul_le_mul_of_nonneg_right (min_le_left csmall clarge) hfactor
      have hfirst' : min csmall clarge * F.A⁻¹ * F.δ^((k+1:ℕ)+m-d+ε) * F.lam^p * F.M ≤
          csmall*F.A⁻¹*F.δ^((k+1:ℕ)+m-d+ε)*F.lam^p*F.M := by
        simpa only [mul_assoc] using hfirst
      exact hfirst'.trans (hpowmul.trans hbound)
    · have hbound := high_density_bound (by omega : 0 < k+1) geom hp hc hc₀ ht ht1 hK
        (fun T δ hδ => TubeVolume.carrier_volume_lower T hδ) hcut hestimate hbudget F hM (lt_of_not_ge hsmall)
      have hfirst := mul_le_mul_of_nonneg_right (min_le_right csmall clarge) hfactor
      have hfirst' : min csmall clarge * F.A⁻¹ * F.δ^((k+1:ℕ)+m-d+ε) * F.lam^p * F.M ≤
          clarge*F.A⁻¹*F.δ^((k+1:ℕ)+m-d+ε)*F.lam^p*F.M := by
        simpa only [mul_assoc] using hfirst
      exact hfirst'.trans hbound
  · have hzero : (F.M : ℝ) = 0 := by exact_mod_cast (show F.M = 0 by omega)
    rw [hzero,mul_zero]
    exact measureReal_nonneg

end MeasurableConversion

/-- Uniform conversion in every positive integer ambient dimension. -/
theorem DiscreteEstimate.to_measurable {k : ℕ} {m d p : ℝ}
    (h : DiscreteEstimate k m d p) (hk : 0 < k) (hd : 1 ≤ d) (hdp : d ≤ p) :
    MeasurableEstimate k m d p := by
  cases k with
  | zero => omega
  | succ k => exact MeasurableConversion.discrete_to_measurable_succ h hd hdp

/-- The normalized count estimate implies the exact tube-volume form of the
manuscript, with a uniform dimensional constant supplied by actual tube geometry. -/
theorem MeasurableEstimate.volume_form {k : ℕ} {m d p : ℝ}
    (h : MeasurableEstimate k m d p) : VolumeMeasurableEstimate k m d p := by
  intro geom ε hε
  obtain ⟨c,hc,hbound⟩ := h geom ε hε
  obtain ⟨cT,CT,hcT,hCT,hvolume⟩ := TubeVolume.carrier_volume_comparison k
  refine ⟨c/CT,div_pos hc hCT,?_⟩
  intro F
  have hδ := F.scale_pos
  have hlam := F.density_pos
  have hA : 0 < F.A := lt_of_lt_of_le (by norm_num) F.cap_ge_one
  have hsum : (∑ i, (volume : Measure (Space k)).real ((F.family.tube i).carrier F.δ)) ≤
      (F.M:ℝ)*CT*F.δ^k/F.δ := by
    have hh := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin F.M))) =>
      (hvolume (F.family.tube i) F.δ F.scale_pos F.scale_le_one).2)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
    calc
      _ ≤ (F.M:ℝ)*(CT*F.δ^k/F.δ) := hh
      _ = _ := by ring
  have hcoef : 0 ≤ (c/CT)*F.A⁻¹*F.δ^(m+1-d+ε)*F.lam^p := by positivity
  have hm := mul_le_mul_of_nonneg_left hsum hcoef
  have hpow : F.δ^k/F.δ = F.δ^((k:ℝ)-1) := by
    rw [Real.rpow_sub F.scale_pos,Real.rpow_natCast,Real.rpow_one]
  have hscale : F.δ^(m+1-d+ε)*F.δ^k/F.δ = F.δ^((k:ℝ)+m-d+ε) := by
    calc
      _ = F.δ^(m+1-d+ε)*(F.δ^k/F.δ) := by ring
      _ = F.δ^((m+1-d+ε)+((k:ℝ)-1)) := by rw [hpow,← Real.rpow_add F.scale_pos]
      _ = _ := by congr 1; ring
  have hid : (c/CT)*F.A⁻¹*F.δ^(m+1-d+ε)*F.lam^p*((F.M:ℝ)*CT*F.δ^k/F.δ) =
      c*F.A⁻¹*F.δ^((k:ℝ)+m-d+ε)*F.lam^p*F.M := by
    calc
      _ = c*F.A⁻¹*(F.δ^(m+1-d+ε)*F.δ^k/F.δ)*F.lam^p*F.M := by field_simp
      _ = _ := by rw [hscale]
  rw [hid] at hm
  exact hm.trans (hbound F)

/-- Complete uniform conversion in the manuscript's actual tube-volume form. -/
theorem DiscreteEstimate.to_measurable_volume {k : ℕ} {m d p : ℝ}
    (h : DiscreteEstimate k m d p) (hk : 0 < k) (hd : 1 ≤ d) (hdp : d ≤ p) :
    VolumeMeasurableEstimate k m d p := (h.to_measurable hk hd hdp).volume_form

/-- The real-cap measurable consequence, in its adequate positive integer
ambient dimensions. No additional restriction on the real cap exponent is used. -/
theorem RealCapEstimate.to_measurable {m d p : ℝ}
    (h : RealCapEstimate m d p) (hd : 1 ≤ d) (hdp : d ≤ p) :
    RealCapMeasurableEstimate m d p :=
  fun k hk hm => (h k hm).to_measurable hk hd hdp

end
end KakeyaFormal

-- Kernel dependency audit.
#print axioms KakeyaFormal.MeasurableConversion.finite_mass_trim
#print axioms KakeyaFormal.MeasurableConversion.measurable_mass_trim
#print axioms KakeyaFormal.MeasurableConversion.carrier_norm_bound
#print axioms KakeyaFormal.MeasurableConversion.class_log_bounds
#print axioms KakeyaFormal.MeasurableConversion.uniform_class_loss
#print axioms KakeyaFormal.MeasurableConversion.specialized_expression
#print axioms KakeyaFormal.MeasurableConversion.absorb_class_loss
#print axioms KakeyaFormal.MeasurableConversion.union_measurable
#print axioms KakeyaFormal.MeasurableConversion.union_norm_bound
#print axioms KakeyaFormal.MeasurableConversion.union_finite
#print axioms KakeyaFormal.MeasurableConversion.high_density_bound
#print axioms KakeyaFormal.MeasurableConversion.discrete_to_measurable_succ
#print axioms KakeyaFormal.DiscreteEstimate.to_measurable
#print axioms KakeyaFormal.MeasurableEstimate.volume_form
#print axioms KakeyaFormal.DiscreteEstimate.to_measurable_volume
#print axioms KakeyaFormal.RealCapEstimate.to_measurable
