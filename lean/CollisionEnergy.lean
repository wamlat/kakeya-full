import CollisionRows
import PlanarEnergy

/-! The actual collision energy in the pivot construction. Original direction
packing, intermediate labels, pivot cells and vertices are all counted by the
proved geometric statements, and the bottom angular shell is included. -/
namespace KakeyaFormal.CollisionEnergy
open Finset CollisionRows CollisionPlane TransverseAngles LegalAngleSamples
open LegalSampleOutputs AngleFiberSelection
open scoped BigOperators
noncomputable section
open Classical

def rowConstant (k : ℕ) (width : ℝ) : ℝ :=
  2*fixedFirstConstant (k+2) width*ThickCircle.circleConstant k (6*width)

theorem rowConstant_pos (k : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    0 < rowConstant k width := by
  have hQ := ProjectiveGeometry.chartConstant_pos (k+1) (by norm_num : (0:ℝ) < 1/2)
  unfold rowConstant ThickCircle.circleConstant
  positivity [fixedFirstConstant_pos (k+2) hw]

variable {k M : ℕ} {F : TubeFamily (k+2) M} {H : Finset (Cell (k+2))}
variable {δ lam kappa width : ℝ}

/-- The complete actual collision row is summed across all angular shells,
including identical first tubes. No row-count or collision premise is supplied. -/
theorem row_count (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hw : 0 ≤ width)
    (hadm : F.Admissible width δ) (hsep : F.Separated δ)
    (hsmall : (6*width/kappa)*δ ≤ 1/2) :
    ((row S hk hw hadm a).card:ℝ) ≤
      rowConstant k width*(Real.logb 2 (2/δ)+2)/(kappa^(k+1)*δ^2) := by
  classical
  let I := firstIndices S a hk hw hadm
  let d := fun i : Fin M => projectiveDistance (F.tube i).direction (F.tube a.val.2.1).direction
  let R := row S hk hw hadm a
  let C := fixedFirstConstant (k+2) width
  have hC : 0 < C := fixedFirstConstant_pos (k+2) hw
  have hsum : (R.card:ℝ) = ∑ i ∈ I, ((R.filter (fun e => e.1.val.2.1=i)).card:ℝ) := by
    simpa only [card_eq_sum_ones,Nat.cast_sum,Nat.cast_one] using
      (sum_fiberwise_of_maps_to (s := R) (t := I) (g := fun e => e.1.val.2.1)
        (fun e he => row_first_index S hk hw hadm a e he) (fun _ => (1:ℝ))).symm
  have hrow : (R.card:ℝ) ≤ C/(kappa*δ)*(∑ i ∈ I, 1/max (d i) δ) := by
    rw [hsum,mul_sum]
    exact sum_le_sum fun i _ => fixed_first_count S hδ hδ1 hk hw hadm a i
  have hinverse := PlanarEnergy.inverse_angle_sum_of_linear_caps I d hδ
    (PlanarEnergy.dyadicDepth δ)
    (fun i _ => (TubeIntersection.unit_projective_le_two _ _ (F.tube i).unit_direction
      (F.tube a.val.2.1).unit_direction).trans (PlanarEnergy.dyadicDepth_covers hδ))
    (fun r hr => collision_cap_count S a hδ hr hk hw hadm hsep hsmall)
  have hcircle := circleConstant_div_le k (by positivity : 0 ≤ 6*width) hk hk1
  have hJ := PlanarEnergy.dyadicDepth_log_bound hδ hδ1
  have hcirclepos : 0 < ThickCircle.circleConstant k (6*width) := by
    have hQ := ProjectiveGeometry.chartConstant_pos (k+1) (by norm_num : (0:ℝ) < 1/2)
    unfold ThickCircle.circleConstant
    positivity
  have hinverse' : (∑ i ∈ I, 1/max (d i) δ) ≤
      2*(ThickCircle.circleConstant k (6*width)/kappa^k)*(Real.logb 2 (2/δ)+2)/δ := by
    apply hinverse.trans
    apply div_le_div_of_nonneg_right _ hδ.le
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hcircle (by norm_num)
    · exact hJ
    · positivity
    · positivity
  have hh := hrow.trans (mul_le_mul_of_nonneg_left hinverse' (by positivity))
  exact hh.trans_eq (by unfold rowConstant; dsimp [C]; rw [pow_succ]; ring)

/-- A same-output ordered collision with fixed retained second label belongs
to the actual all-output row of its first angle. -/
theorem collision_row_membership (S : SampleSystem F H δ lam kappa width)
    (hk : 0 < kappa) (hw : 0 ≤ width) (hadm : F.Admissible width δ)
    (Ω : Finset (↥(angles F H kappa) × (Cell (k+2) × Cell (k+2))))
    (hsub : Ω ⊆ edges univ S.samples (fun a => output S a hk hw hadm))
    (hsecond : ∀ e ∈ Ω, ∀ e' ∈ Ω, e.2=e'.2 → e.1.val.2.2=e'.1.val.2.2)
    (c : (↥(angles F H kappa) × (Cell (k+2) × Cell (k+2))) ×
      (↥(angles F H kappa) × (Cell (k+2) × Cell (k+2))))
    (hc : c ∈ collisionPairs Ω) : c.2 ∈ row S hk hw hadm c.1.1 := by
  obtain ⟨h1,h2,hout⟩ : c.1 ∈ Ω ∧ c.2 ∈ Ω ∧ c.1.2=c.2.2 := by
    simpa only [Finset.mem_coe,collisionPairs,mem_filter,Finset.product_eq_sprod,mem_product,and_assoc] using hc
  apply (mem_row S hk hw hadm c.1.1 c.2).mpr
  refine ⟨(mem_edges.mp (hsub h2)).2,?_,(hsecond c.1 h1 c.2 h2 hout).symm⟩
  rw [← hout]
  exact (mem_edges.mp (hsub h1)).2


/-- The number of actual ordered collisions is bounded by the sum of the
all-output rows over original angles. The encoding is injective because the
shared output determines the first edge from its angle. -/
theorem energy_le_sum_rows (S : SampleSystem F H δ lam kappa width)
    (hk : 0 < kappa) (hw : 0 ≤ width) (hadm : F.Admissible width δ)
    (Ω : Finset (↥(angles F H kappa) × (Cell (k+2) × Cell (k+2))))
    (hsub : Ω ⊆ edges univ S.samples (fun a => output S a hk hw hadm))
    (hsecond : ∀ e ∈ Ω, ∀ e' ∈ Ω, e.2=e'.2 → e.1.val.2.2=e'.1.val.2.2) :
    collisionEnergy Ω ≤ ∑ a : ↥(angles F H kappa), ((row S hk hw hadm a).card:ℝ) := by
  classical
  let A := ↥(angles F H kappa)
  let O := Cell (k+2) × Cell (k+2)
  let encode : ((A×O)×(A×O)) → Σ _a : A, A×O := fun c => ⟨c.1.1,c.2⟩
  have hmap : Set.MapsTo encode (collisionPairs Ω) (univ.sigma (row S hk hw hadm)) := by
    intro c hc
    exact mem_sigma.mpr ⟨mem_univ _,collision_row_membership S hk hw hadm Ω hsub hsecond c hc⟩
  have hinj : Set.InjOn encode (collisionPairs Ω) := by
    intro c hc d hd heq
    have ha : c.1.1=d.1.1 := congrArg Sigma.fst heq
    have hb : c.2=d.2 := congrArg (fun s : Σ _a : A, A×O => s.2) heq
    have hc' : c.1.2=c.2.2 := by
      have hh : c.1 ∈ Ω ∧ c.2 ∈ Ω ∧ c.1.2=c.2.2 := by
        simpa only [Finset.mem_coe,collisionPairs,mem_filter,Finset.product_eq_sprod,mem_product,and_assoc] using hc
      exact hh.2.2
    have hd' : d.1.2=d.2.2 := by
      have hh : d.1 ∈ Ω ∧ d.2 ∈ Ω ∧ d.1.2=d.2.2 := by
        simpa only [Finset.mem_coe,collisionPairs,mem_filter,Finset.product_eq_sprod,mem_product,and_assoc] using hd
      exact hh.2.2
    exact Prod.ext (Prod.ext ha (hc'.trans ((congrArg Prod.snd hb).trans hd'.symm))) hb
  have hc := card_le_card_of_injOn encode hmap hinj
  rw [card_sigma] at hc
  rw [collision_energy_count]
  exact_mod_cast hc

/-- The geometric collision energy bound (5.18), for any actual retained
edge set whose original second-tube label is constant at each output.
The finite most-frequent-label selection provides exactly this premise. -/
theorem collision_energy_bound (S : SampleSystem F H δ lam kappa width)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hw : 0 ≤ width) (hadm : F.Admissible width δ) (hsep : F.Separated δ)
    (hsmall : (6*width/kappa)*δ ≤ 1/2)
    (Ω : Finset (↥(angles F H kappa) × (Cell (k+2) × Cell (k+2))))
    (hsub : Ω ⊆ edges univ S.samples (fun a => output S a hk hw hadm))
    (hsecond : ∀ e ∈ Ω, ∀ e' ∈ Ω, e.2=e'.2 → e.1.val.2.2=e'.1.val.2.2) :
    collisionEnergy Ω ≤ rowConstant k width*(Real.logb 2 (2/δ)+2)*
      ((angles F H kappa).card:ℝ)/(kappa^(k+1)*δ^2) := by
  have hh := (energy_le_sum_rows S hk hw hadm Ω hsub hsecond).trans
    (sum_le_sum (fun a _ => row_count S a hδ hδ1 hk hk1 hw hadm hsep hsmall))
  simpa only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul] using
    hh.trans_eq (by simp only [sum_const,card_univ,Fintype.card_coe,nsmul_eq_mul]; ring)

end
end KakeyaFormal.CollisionEnergy
