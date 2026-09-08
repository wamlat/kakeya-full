import CapCover
import CoarseBounds
import LowCellAbsorption

/-! Section 7's coarse angular branch on actual old finite shadings.
The angular population estimate is derived from the original complete cap
condition, and the union lower bound comes from one actual old shading. -/
namespace KakeyaFormal.LocalAngularCoarse
open ProjectiveGeometry
noncomputable section

def populationCoefficient (k : ℕ) (angular m : ℝ) : ℝ :=
  packingConstant k*(max 1 angular)^m

theorem populationCoefficient_pos (k : ℕ) (angular m : ℝ) :
    0 < populationCoefficient k angular m :=
  mul_pos (zero_lt_one.trans_le (packingConstant_ge_one k))
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le (le_max_left _ _)) _)

/-- An actual local cap controls the population at the normalized mesh.
The large-cap case uses the proved finite radius-one projective cover. -/
theorem local_cap_population {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    {δ tau angular m A : ℝ} (hu : ‖u‖=1)
    (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hcap : F.CapBound δ m A)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau) :
    (M:ℝ) ≤ populationCoefficient k angular m*A*(δ/tau)^(-m) := by
  classical
  have htau : 0 < tau := hδ.trans_le hδtau
  have hδ1 := hδtau.trans htau1
  let a := max 1 angular
  have ha : 0 < a := zero_lt_one.trans_le (le_max_left _ _)
  have hangle : ∀ i, projectiveDistance (F.tube i).direction u ≤ a*tau :=
    fun i => (hlocal i).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) htau.le)
  have hscale : δ ≤ a*tau := hδtau.trans (le_mul_of_one_le_left htau.le (le_max_left _ _))
  have hnorm : (a*tau/δ)^m = a^m*(δ/tau)^(-m) := by
    have hid : a*tau/δ = a*(δ/tau)⁻¹ := by field_simp
    rw [hid,Real.mul_rpow ha.le (by positivity),Real.inv_rpow (div_pos hδ htau).le,
      ← Real.rpow_neg (div_pos hδ htau).le]
  by_cases hsmall : a*tau ≤ 1
  · have hfilter : (Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction u ≤ a*tau)) =
        (Finset.univ : Finset (Fin M)) := Finset.filter_eq_self.mpr (fun i _ => hangle i)
    have hh := hcap u hu (a*tau) hscale hsmall
    rw [hfilter,Finset.card_univ,Fintype.card_fin,hnorm] at hh
    have hpack := mul_le_mul_of_nonneg_right (packingConstant_ge_one k)
      (by positivity : (0:ℝ)≤A*(a^m*(δ/tau)^(-m)))
    exact hh.trans (by simpa only [populationCoefficient,a,mul_assoc,mul_comm,mul_left_comm,one_mul] using hpack)
  · have hh := CapCover.cap_bound_total_count F hδ hδ1 hA hcap
    have hratio : 1/δ ≤ a*tau/δ :=
      div_le_div_of_nonneg_right (le_of_lt (lt_of_not_ge hsmall)) hδ.le
    have hp := Real.rpow_le_rpow (by positivity : (0:ℝ)≤1/δ) hratio hm
    have hmul := mul_le_mul_of_nonneg_left hp
      (mul_nonneg (zero_le_one.trans (packingConstant_ge_one k)) hA)
    rw [hnorm] at hmul
    exact hh.trans (by simpa only [populationCoefficient,a,mul_assoc,mul_comm,mul_left_comm] using hmul)

/-- The coarse scale condition gives the source's stronger old-scale square-root bound. -/
theorem coarse_power {δ deltaNew n D eps : ℝ}
    (hδ : 0 < δ) (hn : 0 < n) (hnew1 : deltaNew ≤ 1)
    (hD : D ≤ n) (heps : 0 ≤ eps) (hcoarse : δ^(1/(2*n)) ≤ deltaNew) :
    deltaNew^(-D+eps) ≤ δ^(-(1:ℝ)/2) := by
  have hroot : 0 < δ^(1/(2*n)) := Real.rpow_pos_of_pos hδ _
  have hnew : 0 < deltaNew := hroot.trans_le hcoarse
  have h1 := Real.rpow_le_rpow_of_exponent_ge hnew hnew1 (by linarith : -n ≤ -D+eps)
  have h2 := Real.rpow_le_rpow_of_nonpos hroot hcoarse (by linarith : -n ≤ 0)
  rw [← Real.rpow_mul hδ.le] at h2
  have hid : 1/(2*n)*(-n) = -(1:ℝ)/2 := by field_simp
  rw [hid] at h2
  exact h1.trans h2

theorem coarse_power_old_shade {δ deltaNew n D eps : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hn : 0 < n) (hnew1 : deltaNew ≤ 1)
    (hD : D ≤ n) (heps : 0 ≤ eps) (hcoarse : δ^(1/(2*n)) ≤ deltaNew) :
    deltaNew^(-D+eps) ≤ 1/δ := by
  have hh := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by norm_num : (-1:ℝ) ≤ -(1:ℝ)/2)
  rw [Real.rpow_neg_one] at hh
  simpa only [one_div] using (coarse_power hδ hn hnew1 hD heps hcoarse).trans hh

/-- Scalar use of the population bound is isolated here; the public family
theorems below derive that population bound from actual direction geometry. -/
theorem bounded_density_power {lam lamMax C : ℝ}
    (hlam : 0 < lam) (hmax : 0 < lamMax) (hlamMax : lam ≤ lamMax) (hC : 1 ≤ C) :
    lamMax^(1-C)*lam^C ≤ lam := by
  have hp := Real.rpow_le_rpow hlam.le hlamMax (by linarith : 0 ≤ C-1)
  have hh := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤lamMax^(1-C)*lam)
  have hpow : lam^C = lam*lam^(C-1) := by
    have hr := Real.rpow_add hlam 1 (C-1)
    rw [show (1:ℝ)+(C-1)=C by ring,Real.rpow_one] at hr
    exact hr
  have hcancel : lamMax^(1-C)*lamMax^(C-1) = 1 := by
    rw [← Real.rpow_add hmax]
    ring_nf
    exact Real.rpow_zero _
  calc
    _ = (lamMax^(1-C)*lam)*lam^(C-1) := by rw [hpow]; ring
    _ ≤ (lamMax^(1-C)*lam)*lamMax^(C-1) := hh
    _ = lam*(lamMax^(1-C)*lamMax^(C-1)) := by ring
    _ = _ := by rw [hcancel,mul_one]

theorem target_from_population {Kpop A deltaNew δ lam lamMax M m D C eps H : ℝ}
    (hKpop : 0 < Kpop) (hA : 0 < A) (hnew : 0 < deltaNew) (hδ : 0 < δ)
    (hlam : 0 < lam) (hmax : 0 < lamMax) (hlamMax : lam ≤ lamMax) (hC : 1 ≤ C) (hH : 0 < H)
    (hcount : M ≤ Kpop*A*deltaNew^(-m))
    (hpower : deltaNew^(-D+eps) ≤ H/δ) :
    (lamMax^(1-C)/(Kpop*H))*A⁻¹*deltaNew^(m-D+eps)*lam^C*M ≤ lam/δ := by
  have hmul := mul_le_mul_of_nonneg_left hcount
    (by positivity : (0:ℝ)≤lamMax^(1-C)*A⁻¹*deltaNew^(m-D+eps)*lam^C)
  have hpowid : deltaNew^(m-D+eps)*deltaNew^(-m) = deltaNew^(-D+eps) := by
    rw [← Real.rpow_add hnew]
    congr 1
    ring
  have hid : (lamMax^(1-C)*A⁻¹*deltaNew^(m-D+eps)*lam^C)*(Kpop*A*deltaNew^(-m)) =
      Kpop*deltaNew^(-D+eps)*(lamMax^(1-C)*lam^C) := by
    calc
      _ = Kpop*(deltaNew^(m-D+eps)*deltaNew^(-m))*(lamMax^(1-C)*lam^C) := by field_simp
      _ = _ := by rw [hpowid]
  rw [hid] at hmul
  have hld := bounded_density_power hlam hmax hlamMax hC
  have hboth := mul_le_mul hpower hld (by positivity) (by positivity)
  have hboth' : Kpop*deltaNew^(-D+eps)*(lamMax^(1-C)*lam^C) ≤ Kpop*(H/δ*lam) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hboth hKpop.le
  have hbound := hmul.trans hboth'
  have hh := div_le_div_of_nonneg_right hbound (mul_pos hKpop hH).le
  calc
    _ = (lamMax^(1-C)*A⁻¹*deltaNew^(m-D+eps)*lam^C*M)/(Kpop*H) := by ring
    _ ≤ (Kpop*(H/δ*lam))/(Kpop*H) := hh
    _ = _ := by field_simp

/-- Actual old finite shadings prove Section 7 case 1, with no population
oracle or desired lower-count premise. The constant is independent of all
meshes, radii, densities, cap coefficients, and actual families. -/
theorem coarse_family_bound {k M : ℕ} (F : TubeFamily (k+1) M)
    (u : Space (k+1)) (S : Finset (Cell (k+1)))
    {δ tau angular m D C eps lam lamMax A : ℝ}
    (hu : ‖u‖=1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (hm : 0 ≤ m) (hD : D < m+1) (hmn : m+1 ≤ (k:ℝ)+1)
    (hC : 1 ≤ C) (heps : 0 ≤ eps) (hlam : 0 < lam)
    (hmax : 0 < lamMax) (hlamMax : lam ≤ lamMax) (hA : 0 < A)
    (hcap : F.CapBound δ m A)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcomparable : F.Comparable δ lam) (hsub : ∀ i, F.shade i ⊆ S)
    (hcoarse : δ^(1/(2*((k:ℝ)+1))) ≤ δ/tau) :
    (lamMax^(1-C)/populationCoefficient k angular m)*A⁻¹*(δ/tau)^(m-D+eps)*lam^C*(M:ℝ) ≤ (S.card:ℝ) := by
  by_cases hM : M=0
  · simp only [hM,Nat.cast_zero,mul_zero]
    positivity
  have htau : 0 < tau := hδ.trans_le hδtau
  let i : Fin M := ⟨0,Nat.pos_of_ne_zero hM⟩
  have hshade : lam/δ ≤ (S.card:ℝ) := (hcomparable i).1.trans (Nat.cast_le.mpr (Finset.card_le_card (hsub i)))
  have hpop := local_cap_population F u hu hδ hδtau htau1 hm hA.le hcap hlocal
  have hpower : (δ/tau)^(-D+eps) ≤ 1/δ := coarse_power_old_shade hδ (hδtau.trans htau1)
    (by positivity : (0:ℝ)<(k:ℝ)+1) ((div_le_one htau).mpr hδtau) (hD.le.trans hmn) heps hcoarse
  have hh := target_from_population (populationCoefficient_pos k angular m) hA (div_pos hδ htau) hδ
    hlam hmax hlamMax hC (by norm_num : (0:ℝ)<1) hpop hpower
  have hh' : (lamMax^(1-C)/populationCoefficient k angular m)*A⁻¹*(δ/tau)^(m-D+eps)*lam^C*(M:ℝ) ≤ lam/δ := by
    simpa only [mul_one] using hh
  exact hh'.trans hshade

/-- A fixed lower normalized mesh is also handled by one actual old shading.
This closes the scale range above any fixed sampling threshold. -/
theorem bounded_scale_family_bound {k M : ℕ} (F : TubeFamily (k+1) M)
    (u : Space (k+1)) (S : Finset (Cell (k+1)))
    {δ tau angular m D C eps lam lamMax A a : ℝ}
    (hu : ‖u‖=1) (hδ : 0 < δ) (hδtau : δ ≤ tau) (htau1 : tau ≤ 1)
    (hm : 0 ≤ m) (hC : 1 ≤ C) (hlam : 0 < lam)
    (hmax : 0 < lamMax) (hlamMax : lam ≤ lamMax) (hA : 0 < A)
    (hcap : F.CapBound δ m A)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcomparable : F.Comparable δ lam) (hsub : ∀ i, F.shade i ⊆ S)
    (ha : 0 < a) (hscale : a ≤ δ/tau) :
    (lamMax^(1-C)/(populationCoefficient k angular m*max 1 (a^(-D+eps))))*
      A⁻¹*(δ/tau)^(m-D+eps)*lam^C*(M:ℝ) ≤ (S.card:ℝ) := by
  by_cases hM : M=0
  · simp only [hM,Nat.cast_zero,mul_zero]
    positivity
  have htau : 0 < tau := hδ.trans_le hδtau
  let i : Fin M := ⟨0,Nat.pos_of_ne_zero hM⟩
  have hshade : lam/δ ≤ (S.card:ℝ) := (hcomparable i).1.trans (Nat.cast_le.mpr (Finset.card_le_card (hsub i)))
  have hpop := local_cap_population F u hu hδ hδtau htau1 hm hA.le hcap hlocal
  let H := max 1 (a^(-D+eps))
  have hH : 0 < H := zero_lt_one.trans_le (le_max_left _ _)
  have hpow : (δ/tau)^(-D+eps) ≤ H :=
    CoarseBounds.scale_power_upper ha hscale ((div_le_one htau).mpr hδtau)
  have hpower : (δ/tau)^(-D+eps) ≤ H/δ := hpow.trans
    ((le_div_iff₀ hδ).mpr (mul_le_of_le_one_right hH.le (hδtau.trans htau1)))
  exact (target_from_population (populationCoefficient_pos k angular m) hA (div_pos hδ htau) hδ
    hlam hmax hlamMax hC hH hpop hpower).trans hshade

/-- Exact source-log transport in the complement of the coarse branch,
including the additive log 2 in the formal logarithmic budgets. -/
theorem complementary_log_comparison (k : ℕ) {δ deltaNew : ℝ}
    (hδ : 0 < δ) (hnew : 0 < deltaNew)
    (hfine : deltaNew ≤ δ^(1/(2*((k:ℝ)+1)))) :
    Real.log (2/δ) ≤ (2*((k:ℝ)+1))*Real.log (2/deltaNew) :=
  LowCellAbsorption.log_scale_transport_of_power_cutoff hδ hnew (by have := Nat.cast_nonneg (α:=ℝ) k; linarith) hfine

theorem not_coarse_log_comparison (k : ℕ) {δ tau : ℝ}
    (hδ : 0 < δ) (htau : 0 < tau)
    (hnot : ¬δ^(1/(2*((k:ℝ)+1))) ≤ δ/tau) :
    Real.log (2/δ) ≤ (2*((k:ℝ)+1))*Real.log (2/(δ/tau)) :=
  complementary_log_comparison k hδ (div_pos hδ htau) (le_of_lt (lt_of_not_ge hnot))

end
end KakeyaFormal.LocalAngularCoarse
