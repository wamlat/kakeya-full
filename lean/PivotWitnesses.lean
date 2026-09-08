import PivotSupport

/-!
# Constructing support witnesses from actual legal pivot samples

This module defines normalized Euclidean angle and endpoint-pair records,
chooses one actual legal reference pair for each rounded pivot fiber, and derives
its metric lift witnesses. Cell-rounding conditions are actual geometric inputs;
segment membership, coefficient perturbation, separation, and vector residual
bounds are proved rather than included among those inputs.
-/

namespace KakeyaFormal.PivotWitnesses

open KakeyaFormal KakeyaAudit.TubeGeometry KakeyaFormal.PivotSupport

noncomputable section

/-- One transverse angle and its common intermediate point on the first axis. -/
structure Angle (k : ℕ) (kap : ℝ) where
  vertex : Space k
  first : Space k
  second : Space k
  first_unit : ‖first‖ = 1
  second_unit : ‖second‖ = 1
  transverse_lower : kap ≤ ‖transverse first second‖
  intermediate : ℝ
  intermediate_lower : kap ≤ intermediate

/-- A legal endpoint pair in this angle, with normalized bounded lengths.
The sign of the second-axis endpoint is unrestricted. -/
structure Endpoints {k : ℕ} {kap : ℝ} (angle : Angle k kap) where
  firstCoord : ℝ
  secondCoord : ℝ
  gap : kap ≤ firstCoord-angle.intermediate
  first_upper : firstCoord ≤ 1
  second_lower : kap ≤ |secondCoord|
  second_upper : |secondCoord| ≤ 1

def Endpoints.firstPoint {k : ℕ} {kap : ℝ} {a : Angle k kap} (p : Endpoints a) : Space k :=
  a.vertex+p.firstCoord • a.first

def Endpoints.secondPoint {k : ℕ} {kap : ℝ} {a : Angle k kap} (p : Endpoints a) : Space k :=
  a.vertex+p.secondCoord • a.second

def Endpoints.coefficient {k : ℕ} {kap : ℝ} {a : Angle k kap} (p : Endpoints a) : ℝ :=
  p.secondCoord*(1-a.intermediate/p.firstCoord)

def Endpoints.pivot {k : ℕ} {kap : ℝ} {a : Angle k kap} (p : Endpoints a) : Space k :=
  a.vertex+a.intermediate • a.first+p.coefficient • a.second

/-- Each legal sample really produces a pivot on the endpoint segment. -/
theorem Endpoints.pivot_between {k : ℕ} {kap : ℝ} {a : Angle k kap}
    (p : Endpoints a) (hk : 0 < kap) :
    p.pivot ∈ segment ℝ p.firstPoint p.secondPoint := by
  exact legal_pivot_mem_segment a.vertex a.first a.second
    (lt_of_lt_of_le hk a.intermediate_lower) (by linarith [p.gap])

/-- Both reference and target sample coefficients are noncollapsed. -/
theorem Endpoints.coefficient_lower {k : ℕ} {kap : ℝ} {a : Angle k kap}
    (p : Endpoints a) (hk : 0 < kap) : kap^2 ≤ |p.coefficient| := by
  simpa [Endpoints.coefficient] using
    (legal_pivot_coefficient_bounds hk a.intermediate_lower p.gap p.first_upper p.second_lower).1

/-- Genuine endpoint separation of every legal pivot from its first endpoint. -/
theorem Endpoints.pivot_separation {k : ℕ} {kap : ℝ} {a : Angle k kap}
    (p : Endpoints a) (hk : 0 < kap) : kap^3 ≤ ‖p.pivot-p.firstPoint‖ := by
  simpa [Endpoints.pivot,Endpoints.firstPoint,Endpoints.coefficient] using
    legal_pivot_stem_separation a.vertex a.first a.second (s := p.firstCoord)
      a.first_unit hk a.intermediate_lower p.gap p.first_upper p.second_lower a.transverse_lower

/-- Bounded endpoint distance follows from normalized coordinates and unit axes. -/
theorem Endpoints.endpoint_distance {k : ℕ} {kap : ℝ} {a : Angle k kap}
    (p : Endpoints a) (hk : 0 < kap) : dist p.firstPoint p.secondPoint ≤ 2 := by
  have hb0 : 0 < p.firstCoord := by linarith [p.gap,a.intermediate_lower]
  have hid : p.firstPoint-p.secondPoint = p.firstCoord • a.first-p.secondCoord • a.second := by
    dsimp [Endpoints.firstPoint,Endpoints.secondPoint]
    abel
  rw [dist_eq_norm,hid]
  calc
    ‖p.firstCoord • a.first-p.secondCoord • a.second‖ ≤
        ‖p.firstCoord • a.first‖+‖p.secondCoord • a.second‖ := norm_sub_le _ _
    _ = p.firstCoord+|p.secondCoord| := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        a.first_unit,a.second_unit,abs_of_pos hb0]
      ring
    _ ≤ 2 := by linarith [p.first_upper,p.second_upper]

/-- One common angle-output fiber, with one actual legal reference pair fixing
its exact graph-line coefficient. The intermediate label is retained to record
the complete original output, even though it is not needed for support counting. -/
structure Fiber (k : ℕ) (δ kap C : ℝ) where
  angle : Angle k kap
  reference : Endpoints angle
  pivotLabel : Cell k
  intermediateLabel : Cell k
  reference_close : ‖cellCenter δ pivotLabel-reference.pivot‖ ≤ C*δ
  intermediate_close :
    ‖cellCenter δ intermediateLabel-(angle.vertex+angle.intermediate • angle.first)‖ ≤ C*δ

/-- An endpoint pair attached to one actual lifted grid cell of a chosen fiber. -/
structure AttachedSample (k : ℕ) (δ kap C : ℝ) where
  fiber : Fiber k δ kap C
  endpoints : Endpoints fiber.angle
  firstLabel : Cell k
  secondLabel : Cell k
  liftLabel : LiftCell k
  first_close : ‖cellCenter δ firstLabel-endpoints.firstPoint‖ ≤ C*δ
  second_close : ‖cellCenter δ secondLabel-endpoints.secondPoint‖ ≤ C*δ
  pivot_close : ‖cellCenter δ fiber.pivotLabel-endpoints.pivot‖ ≤ C*δ
  horizontal_close : ‖cellCenter δ liftLabel.1-endpoints.secondPoint‖ ≤ C*δ
  vertical_close :
    |δ*(liftLabel.2:ℝ)-endpoints.secondCoord/fiber.reference.coefficient| ≤ C*δ

/-- Coincidence of rounded pivot labels derives the coefficient perturbation;
no perturbation-size hypothesis is added to an attached sample record. -/
theorem AttachedSample.coefficient_perturbation {k : ℕ} {δ kap C : ℝ}
    (s : AttachedSample k δ kap C) :
    |s.fiber.reference.coefficient-s.endpoints.coefficient| ≤ 2*C*δ := by
  have hid : s.fiber.reference.pivot-s.endpoints.pivot =
      (s.fiber.reference.coefficient-s.endpoints.coefficient) • s.fiber.angle.second := by
    dsimp [Endpoints.pivot]
    module
  have hnorm : ‖s.fiber.reference.pivot-s.endpoints.pivot‖ ≤ 2*C*δ := by
    have hsplit : s.fiber.reference.pivot-s.endpoints.pivot =
        (s.fiber.reference.pivot-cellCenter δ s.fiber.pivotLabel)+
          (cellCenter δ s.fiber.pivotLabel-s.endpoints.pivot) := by abel
    rw [hsplit]
    have href : ‖s.fiber.reference.pivot-cellCenter δ s.fiber.pivotLabel‖ ≤ C*δ := by
      simpa only [norm_sub_rev] using s.fiber.reference_close
    exact (norm_add_le _ _).trans (by linarith [s.pivot_close])
  rw [hid,norm_smul,Real.norm_eq_abs,s.fiber.angle.second_unit,mul_one] at hnorm
  exact hnorm

/-- The exact graph-line parameter is positive with quantitative room from one. -/
theorem AttachedSample.lift_range {k : ℕ} {δ kap C : ℝ}
    (s : AttachedSample k δ kap C) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hscale : 2*C*δ ≤ kap^5/4) :
    1+kap/2 ≤ s.endpoints.secondCoord/s.fiber.reference.coefficient ∧
      s.endpoints.secondCoord/s.fiber.reference.coefficient ≤ 2/kap := by
  exact normalized_perturbed_lift_range hk hk1 s.fiber.angle.intermediate_lower
    s.endpoints.gap s.endpoints.first_upper s.endpoints.second_lower s.endpoints.second_upper
    s.coefficient_perturbation hscale

/-- The lift-vector residual is derived from the legal sample and common-fiber
rounding. Its inverse-square loss is explicit. -/
theorem AttachedSample.residual {k : ℕ} {δ kap C : ℝ}
    (s : AttachedSample k δ kap C) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hscale : 2*C*δ ≤ kap^5/4) :
    let t := s.endpoints.secondCoord/s.fiber.reference.coefficient
    ‖t • s.endpoints.pivot-s.endpoints.secondPoint-(t-1) • s.endpoints.firstPoint‖ ≤
      4*(2*C*δ)/kap^2 := by
  dsimp only
  have hb0 : 0 < s.endpoints.firstCoord := by
    linarith [s.endpoints.gap,s.fiber.angle.intermediate_lower]
  have hc := s.fiber.reference.coefficient_lower hk
  have htime := s.lift_range hk hk1 hscale
  have ht0 : 0 < s.endpoints.secondCoord/s.fiber.reference.coefficient := by linarith
  have ht : |s.endpoints.secondCoord/s.fiber.reference.coefficient| ≤ 2/kap := by
    rw [abs_of_pos ht0]
    exact htime.2
  have hdiff : |s.endpoints.coefficient-s.fiber.reference.coefficient| ≤ 2*C*δ := by
    simpa only [abs_sub_comm] using s.coefficient_perturbation
  have hbase := pivot_residual_bound (B := (1:ℝ)) s.fiber.angle.first s.fiber.angle.second
    hb0.ne' (sq_pos_of_pos hk) hc
    (by rw [s.fiber.angle.first_unit]) (by rw [s.fiber.angle.second_unit])
    (by rw [abs_of_pos hb0]; exact s.endpoints.first_upper) ht hdiff
  have hid : (s.endpoints.secondCoord/s.fiber.reference.coefficient) • s.endpoints.pivot-
      s.endpoints.secondPoint-(s.endpoints.secondCoord/s.fiber.reference.coefficient-1) •
      s.endpoints.firstPoint =
      (s.endpoints.secondCoord/s.fiber.reference.coefficient) •
        (s.fiber.angle.intermediate • s.fiber.angle.first+s.endpoints.coefficient • s.fiber.angle.second)-
      s.endpoints.secondCoord • s.fiber.angle.second-
        (s.endpoints.secondCoord/s.fiber.reference.coefficient-1) •
          (s.endpoints.firstCoord • s.fiber.angle.first) := by
    dsimp [Endpoints.pivot,Endpoints.firstPoint,Endpoints.secondPoint]
    module
  rw [hid]
  have heta0 : 0 ≤ 2*C*δ := (abs_nonneg _).trans s.coefficient_perturbation
  have hcoef : 1/kap^2+2/kap ≤ 4/kap^2 := by
    have hpos : 0 < kap^2 := sq_pos_of_pos hk
    apply (le_div_iff₀ hpos).mpr
    have hdiv1 : (1/kap^2)*kap^2 = 1 := by field_simp
    have hdiv2 : (2/kap)*kap^2 = 2*kap := by field_simp
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hcoef heta0
  have hlast : (2*C*δ)*(1/kap^2+2/kap) ≤ 4*(2*C*δ)/kap^2 := by
    calc
      _ ≤ (2*C*δ)*(4/kap^2) := hmul
      _ = _ := by ring
  exact hbase.trans hlast

/-- The full support witness is constructed from an actual attached legal sample.
No segment-membership, coefficient-perturbation, separation, lift-range, or
rounded-residual conclusion is required as an additional input. -/
def AttachedSample.toWitness {k : ℕ} {δ kap C : ℝ}
    (s : AttachedSample k δ kap C) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hk : 0 < kap) (hk1 : kap ≤ 1) (hscale : 2*C*δ ≤ kap^5/4) :
    RoundedLiftWitness k δ (2*C*δ) (4*(2*C*δ)/kap^2) (kap^3) (2/kap)
      s.firstLabel s.secondLabel s.fiber.pivotLabel s.liftLabel := by
  have hround : C*δ ≤ 2*C*δ := by nlinarith [mul_nonneg hC hδ.le]
  have ht := s.lift_range hk hk1 hscale
  have ht0 : 0 < s.endpoints.secondCoord/s.fiber.reference.coefficient := by linarith
  exact {
    y1 := s.endpoints.firstPoint
    y2 := s.endpoints.secondPoint
    z := s.endpoints.pivot
    time := s.endpoints.secondCoord/s.fiber.reference.coefficient
    pivot_between := s.endpoints.pivot_between hk
    first_close := s.first_close.trans hround
    second_close := s.second_close.trans hround
    pivot_close := s.pivot_close.trans hround
    separated := s.endpoints.pivot_separation hk
    time_bound := by rw [abs_of_pos ht0]; exact ht.2
    residual_bound := s.residual hk hk1 hscale
    horizontal_close := s.horizontal_close.trans hround
    vertical_close := s.vertical_close.trans hround
  }

/-- Original endpoint labels inherit a fixed bounded-distance normalization. -/
theorem AttachedSample.endpoint_label_distance {k : ℕ} {δ kap C : ℝ}
    (s : AttachedSample k δ kap C) (hδ1 : δ ≤ 1) (hC : 0 ≤ C) (hk : 0 < kap) :
    dist (cellCenter δ s.firstLabel) (cellCenter δ s.secondLabel) ≤ 2+2*C := by
  have ht1 := dist_triangle (cellCenter δ s.firstLabel) s.endpoints.firstPoint
    (cellCenter δ s.secondLabel)
  have ht2 := dist_triangle s.endpoints.firstPoint s.endpoints.secondPoint
    (cellCenter δ s.secondLabel)
  have hf : dist (cellCenter δ s.firstLabel) s.endpoints.firstPoint ≤ C*δ := by
    exact s.first_close
  have hs : dist s.endpoints.secondPoint (cellCenter δ s.secondLabel) ≤ C*δ := by
    simpa only [dist_eq_norm,norm_sub_rev] using s.second_close
  have he := s.endpoints.endpoint_distance hk
  nlinarith [mul_le_mul_of_nonneg_left hδ1 hC]

def AttachedSample.label {k : ℕ} {δ kap C : ℝ}
    (s : AttachedSample k δ kap C) : SupportLabel k :=
  ((s.firstLabel,s.secondLabel,s.fiber.pivotLabel),s.liftLabel)

/-- Assign one actual representative incidence to each occupied support label.
Choice is used only to select from an existing finite nonempty fiber. -/
def imageWitness {ι : Type*} {k : ℕ} {δ kap C : ℝ}
    (samples : Finset ι) (sample : ι → AttachedSample k δ kap C)
    (hδ : 0 < δ) (hC : 0 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hscale : 2*C*δ ≤ kap^5/4)
    (p : SupportLabel k) (hp : p ∈ samples.image (fun i => (sample i).label)) :
    RoundedLiftWitness k δ (2*C*δ) (4*(2*C*δ)/kap^2) (kap^3) (2/kap)
      p.1.1 p.1.2.1 p.1.2.2 p.2 := by
  classical
  have hex : ∃ i ∈ samples, (sample i).label = p := Finset.mem_image.mp hp
  let i := Classical.choose hex
  have hi : i ∈ samples ∧ (sample i).label = p := Classical.choose_spec hex
  have hw := (sample i).toWitness hδ hC hk hk1 hscale
  change RoundedLiftWitness k δ (2*C*δ) (4*(2*C*δ)/kap^2) (kap^3) (2/kap)
    (sample i).label.1.1 (sample i).label.1.2.1 (sample i).label.1.2.2
    (sample i).label.2 at hw
  rw [hi.2] at hw
  exact hw

/-- Explicit scale room needed by the rounded-triple recovery interface. -/
theorem scale_gives_rounding_separation {δ kap C : ℝ}
    (hk : 0 < kap) (hk1 : kap ≤ 1) (hscale : 2*C*δ ≤ kap^5/4) :
    2*C*δ ≤ kap^3/4 := by
  have hp2 : kap^2 ≤ 1 := pow_le_one₀ hk.le hk1
  have hp5 : kap^5 ≤ kap^3 := by
    nlinarith [mul_le_mul_of_nonneg_left hp2 (pow_nonneg hk.le 3)]
  linarith

/-- Finite support is derived from the actual attached-sample map and original
endpoint occupancy. All geometric support witnesses are constructed internally. -/
theorem finite_sample_support_count {ι : Type*} {k : ℕ} {δ kap C : ℝ}
    (samples : Finset ι) (sample : ι → AttachedSample k δ kap C)
    (occupied : Finset (Cell k)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 0 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1) (hscale : 2*C*δ ≤ kap^5/4)
    (hend : ∀ i ∈ samples, (sample i).firstLabel ∈ occupied ∧ (sample i).secondLabel ∈ occupied) :
    (samples.image (fun i => (sample i).label)).card ≤
      occupied.card^2 * pivotCount k δ (4*C) (2+2*C) *
        liftCount k δ (2*C*δ) (4*(2*C*δ)/kap^2) (kap^3) (2/kap) := by
  classical
  let labels := samples.image (fun i => (sample i).label)
  have hend' : ∀ p ∈ labels, p.1.1 ∈ occupied ∧ p.1.2.1 ∈ occupied := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact hend i hi
  have hlen' : ∀ p ∈ labels,
      dist (cellCenter δ p.1.1) (cellCenter δ p.1.2.1) ≤ 2+2*C := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hp
    exact (sample i).endpoint_label_distance hδ1 hC hk
  have hcount := support_count_from_legal_witnesses hδ (pow_pos hk 3)
    (scale_gives_rounding_separation hk hk1 hscale) occupied labels hend' hlen'
    (imageWitness samples sample hδ hC hk hk1 hscale)
  have hwidth : 2*(2*C*δ)/δ = 4*C := by field_simp; ring
  rwa [hwidth] at hcount

/-- Actual incidence multiplicity of a finite support label. -/
def incidenceWeight {ι : Type*} {k : ℕ} {δ kap C : ℝ}
    (samples : Finset ι) (sample : ι → AttachedSample k δ kap C)
    (p : SupportLabel k) : ℝ := by
  classical
  exact ((samples.filter fun i => (sample i).label = p).card:ℝ)

/-- The weights are actual incidence counts, so their mass equals sample count. -/
theorem incidenceWeight_total {ι : Type*} {k : ℕ} {δ kap C : ℝ}
    (samples : Finset ι) (sample : ι → AttachedSample k δ kap C) :
    (∑ p ∈ samples.image (fun i => (sample i).label), incidenceWeight samples sample p) =
      (samples.card:ℝ) := by
  classical
  have hmap : ∀ i ∈ samples, (sample i).label ∈ samples.image (fun i => (sample i).label) := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  have h := Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1:ℝ))
  simpa [incidenceWeight] using h

/-- End-to-end lower energy for actual finite attached samples. Incidence mass
and all geometric support witnesses are obtained from the actual finite map. -/
theorem finite_sample_energy {ι : Type*} {k : ℕ} {δ kap C : ℝ}
    (samples : Finset ι) (sample : ι → AttachedSample k δ kap C)
    (occupied : Finset (Cell k)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : 0 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1) (hscale : 2*C*δ ≤ kap^5/4)
    (hend : ∀ i ∈ samples, (sample i).firstLabel ∈ occupied ∧ (sample i).secondLabel ∈ occupied) :
    (samples.card:ℝ)^2 ≤
      ((occupied.card:ℝ)^2 * (pivotCount k δ (4*C) (2+2*C):ℝ) *
        (liftCount k δ (2*C*δ) (4*(2*C*δ)/kap^2) (kap^3) (2/kap):ℝ)) *
      ∑ pos ∈ (samples.image (fun i => (sample i).label)).image energyPosition,
        (∑ p ∈ samples.image (fun i => (sample i).label) with energyPosition p = pos,
          incidenceWeight samples sample p)^2 := by
  classical
  let labels := samples.image (fun i => (sample i).label)
  have hcount := finite_sample_support_count samples sample occupied hδ hδ1 hC hk hk1 hscale hend
  have hB : (labels.card:ℝ) ≤ (occupied.card:ℝ)^2 * (pivotCount k δ (4*C) (2+2*C):ℝ) *
      (liftCount k δ (2*C*δ) (4*(2*C*δ)/kap^2) (kap^3) (2/kap):ℝ) := by
    exact_mod_cast hcount
  have hweight : ∀ p ∈ labels, 0 ≤ incidenceWeight samples sample p := by
    intro p hp
    exact Nat.cast_nonneg _
  have h := finite_image_support_energy labels energyPosition (incidenceWeight samples sample) hweight hB
  rw [incidenceWeight_total] at h
  exact h

/-- The deterministic lower-corner grid label of an actual Euclidean point. -/
def gridRound {k : ℕ} (δ : ℝ) (x : Space k) : Cell k :=
  fun i => ⌊WithLp.ofLp x i / δ⌋

/-- One-dimensional floor rounding has one-mesh error. -/
theorem scalar_floor_round_bound {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |δ*(⌊t/δ⌋:ℝ)-t| ≤ δ := by
  have hlo := (le_div_iff₀ hδ).mp (Int.floor_le (t/δ))
  have hhi := (div_lt_iff₀ hδ).mp (Int.lt_floor_add_one (t/δ))
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- The Euclidean grid-rounding error is bounded by the coordinate l1 error.
The harmless dimension constant k avoids square roots and covers dimension zero. -/
theorem grid_round_bound {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (x : Space k) :
    ‖cellCenter δ (gridRound δ x)-x‖ ≤ (k:ℝ)*δ := by
  let v := cellCenter δ (gridRound δ x)-x
  have hc (i : Fin k) : |WithLp.ofLp v i| ≤ δ := by
    exact scalar_floor_round_bound hδ (WithLp.ofLp x i)
  have hsum : (∑ i : Fin k, |WithLp.ofLp v i|) ≤ (k:ℝ)*δ := by
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
      (f := fun i => |WithLp.ofLp v i|) (g := fun _ => δ) (fun i _ => hc i)
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := (Finset.univ : Finset (Fin k))) (f := fun i => |WithLp.ofLp v i|)
    (fun i _ => abs_nonneg _)
  simp only [sq_abs, ← EuclideanSpace.real_norm_sq_eq] at hs
  have hp : (0:ℝ) ≤ ∑ i, |WithLp.ofLp v i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hnorm : ‖v‖ ≤ ∑ i, |WithLp.ofLp v i| := by nlinarith [norm_nonneg v]
  exact hnorm.trans hsum

/-- Deterministic rounding of both coordinates of an actual lifted point. -/
def liftRound {k : ℕ} (δ : ℝ) (y : Space k) (t : ℝ) : LiftCell k :=
  (gridRound δ y, ⌊t/δ⌋)

theorem lift_round_bound {k : ℕ} {δ C : ℝ} (hδ : 0 < δ)
    (hC : (k:ℝ)+1 ≤ C) (y : Space k) (t : ℝ) :
    ‖cellCenter δ (liftRound δ y t).1-y‖ ≤ C*δ ∧
      |δ*((liftRound δ y t).2:ℝ)-t| ≤ C*δ := by
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · exact (grid_round_bound hδ y).trans (by nlinarith)
  · exact (scalar_floor_round_bound hδ t).trans (by nlinarith)

/-- The actual reference pair constructs its own rounded pivot fiber. -/
def Fiber.rounded {k : ℕ} {δ kap C : ℝ} (a : Angle k kap) (reference : Endpoints a)
    (hδ : 0 < δ) (hC : (k:ℝ) ≤ C) : Fiber k δ kap C where
  angle := a
  reference := reference
  pivotLabel := gridRound δ reference.pivot
  intermediateLabel := gridRound δ (a.vertex+a.intermediate • a.first)
  reference_close := (grid_round_bound hδ reference.pivot).trans
    (mul_le_mul_of_nonneg_right hC hδ.le)
  intermediate_close := (grid_round_bound hδ _).trans
    (mul_le_mul_of_nonneg_right hC hδ.le)

/-- Original shaded endpoint labels and exact legal axis samples. Closeness is
required only for the original labels supplied by the shading configuration. -/
structure ShadedPair {k : ℕ} {kap : ℝ} (a : Angle k kap) (δ C : ℝ) where
  endpoints : Endpoints a
  firstLabel : Cell k
  secondLabel : Cell k
  first_close : ‖cellCenter δ firstLabel-endpoints.firstPoint‖ ≤ C*δ
  second_close : ‖cellCenter δ secondLabel-endpoints.secondPoint‖ ≤ C*δ

/-- Attach a shaded endpoint pair to the deterministic lift of an actual reference
fiber. The equality premise is exactly membership in that rounded pivot fiber;
all pivot/intermediate/lift rounding bounds are derived from floor rounding. -/
def ShadedPair.attachRounded {k : ℕ} {δ kap C : ℝ} {a : Angle k kap}
    (reference : Endpoints a) (s : ShadedPair a δ C)
    (hδ : 0 < δ) (hC : (k:ℝ)+1 ≤ C)
    (hfiber : gridRound δ s.endpoints.pivot = gridRound δ reference.pivot) :
    AttachedSample k δ kap C := by
  have hkC : (k:ℝ) ≤ C := by linarith
  let fiber : Fiber k δ kap C := Fiber.rounded a reference hδ hkC
  let t := s.endpoints.secondCoord/reference.coefficient
  have hlift := lift_round_bound hδ hC s.endpoints.secondPoint t
  refine {
    fiber := fiber
    endpoints := s.endpoints
    firstLabel := s.firstLabel
    secondLabel := s.secondLabel
    liftLabel := liftRound δ s.endpoints.secondPoint t
    first_close := s.first_close
    second_close := s.second_close
    pivot_close := ?_
    horizontal_close := hlift.1
    vertical_close := hlift.2
  }
  change ‖cellCenter δ (gridRound δ reference.pivot)-s.endpoints.pivot‖ ≤ C*δ
  rw [← hfiber]
  exact (grid_round_bound hδ _).trans (mul_le_mul_of_nonneg_right hkC hδ.le)

/-- Data for one actual rounded-output fiber incidence. This record assumes only
legal axis samples, original shading closeness, and equality of rounded pivots. -/
structure RoundedSampleInput (k : ℕ) (δ kap C : ℝ) where
  angle : Angle k kap
  reference : Endpoints angle
  pair : ShadedPair angle δ C
  same_pivot : gridRound δ pair.endpoints.pivot = gridRound δ reference.pivot

def RoundedSampleInput.attach {k : ℕ} {δ kap C : ℝ}
    (s : RoundedSampleInput k δ kap C) (hδ : 0 < δ) (hC : (k:ℝ)+1 ≤ C) :
    AttachedSample k δ kap C :=
  s.pair.attachRounded s.reference hδ hC s.same_pivot

/-- Support bound for finite original samples after actual deterministic rounding,
with no assumed pivot/intermediate/lift errors, residuals, or support counts. -/
theorem rounded_sample_support_count {ι : Type*} {k : ℕ} {δ kap C : ℝ}
    (samples : Finset ι) (sample : ι → RoundedSampleInput k δ kap C)
    (occupied : Finset (Cell k)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : (k:ℝ)+1 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hscale : 2*C*δ ≤ kap^5/4)
    (hend : ∀ i ∈ samples, (sample i).pair.firstLabel ∈ occupied ∧
      (sample i).pair.secondLabel ∈ occupied) :
    (samples.image (fun i => ((sample i).attach hδ hC).label)).card ≤
      occupied.card^2 * pivotCount k δ (4*C) (2+2*C) *
        liftCount k δ (2*C*δ) (4*(2*C*δ)/kap^2) (kap^3) (2/kap) := by
  have hC0 : 0 ≤ C := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  exact finite_sample_support_count samples (fun i => (sample i).attach hδ hC)
    occupied hδ hδ1 hC0 hk hk1 hscale hend

/-- Energy of the concrete rounded samples: the left side is the square of their
actual finite count, not a separately hypothesized mass lower bound. -/
theorem rounded_sample_energy {ι : Type*} {k : ℕ} {δ kap C : ℝ}
    (samples : Finset ι) (sample : ι → RoundedSampleInput k δ kap C)
    (occupied : Finset (Cell k)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hC : (k:ℝ)+1 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hscale : 2*C*δ ≤ kap^5/4)
    (hend : ∀ i ∈ samples, (sample i).pair.firstLabel ∈ occupied ∧
      (sample i).pair.secondLabel ∈ occupied) :
    let attached := fun i => (sample i).attach hδ hC
    (samples.card:ℝ)^2 ≤
      ((occupied.card:ℝ)^2 * (pivotCount k δ (4*C) (2+2*C):ℝ) *
        (liftCount k δ (2*C*δ) (4*(2*C*δ)/kap^2) (kap^3) (2/kap):ℝ)) *
      ∑ pos ∈ (samples.image (fun i => (attached i).label)).image energyPosition,
        (∑ p ∈ samples.image (fun i => (attached i).label) with energyPosition p = pos,
          incidenceWeight samples attached p)^2 := by
  have hC0 : 0 ≤ C := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  exact finite_sample_energy samples (fun i => (sample i).attach hδ hC)
    occupied hδ hδ1 hC0 hk hk1 hscale hend

end
end KakeyaFormal.PivotWitnesses

#print axioms KakeyaFormal.PivotWitnesses.AttachedSample.toWitness
#print axioms KakeyaFormal.PivotWitnesses.finite_sample_support_count
#print axioms KakeyaFormal.PivotWitnesses.finite_sample_energy

#print axioms KakeyaFormal.PivotWitnesses.rounded_sample_energy
