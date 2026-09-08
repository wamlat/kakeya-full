import PlanarEnergy
import CapCover

/-! The actual cap-four inverse-fourth direction kernel. The only population
hypothesis in the final family theorem is its original cap condition; finite
dyadic shells and the dimensional large-cap cover are constructed internally. -/
namespace KakeyaFormal.GaussianCollisionKernel
open Finset PlanarEnergy ProjectiveGeometry
open scoped BigOperators
noncomputable section

def kernel (δ d : ℝ) : ℝ := (δ/max d δ)^4

theorem kernel_nonneg (δ d : ℝ) : 0 ≤ kernel δ d := by unfold kernel; positivity

theorem shell_kernel_bound {δ d : ℝ} (hδ : 0 < δ) {j : ℕ}
    (hj : shellCondition δ d j) : kernel δ d ≤ (2/(2:ℝ)^j)^4 := by
  have hh := mul_le_mul_of_nonneg_left (shell_inverse_bound hδ hj) hδ.le
  have he : δ*(2/(δ*(2:ℝ)^j))=2/(2:ℝ)^j := by field_simp
  rw [he] at hh
  unfold kernel
  have hratio : δ/max d δ ≤ 2/(2:ℝ)^j := by simpa only [mul_one_div] using hh
  exact pow_le_pow_left₀ (div_nonneg hδ.le ((le_max_right _ _).trans' hδ.le)) hratio 4

/-- Finite shell assembly at the critical fourth power. Each nonempty shell
costs at most 16 C; no summation estimate is supplied as an input. -/
theorem quartic_shell_sum {ι : Type*} (indices : Finset ι) (distance : ι → ℝ)
    {δ C : ℝ} (hδ : 0 < δ) (n : ℕ)
    (htop : ∀ i ∈ indices, distance i ≤ δ*(2:ℝ)^n)
    (hcap : ∀ r : ℝ, δ ≤ r →
      ((indices.filter fun i => distance i ≤ r).card:ℝ) ≤ C*(r/δ)^4) :
    (∑ i ∈ indices, kernel δ (distance i)) ≤ 16*C*((n:ℝ)+1) := by
  classical
  let shells : ℕ → Finset ι := fun j => indices.filter (fun i => shellCondition δ (distance i) j)
  have hsumcover : (∑ i ∈ indices, kernel δ (distance i)) ≤
      ∑ j ∈ Finset.range (n+1), ∑ i ∈ shells j, kernel δ (distance i) := by
    have hpoint (i) (hi : i ∈ indices) : kernel δ (distance i) ≤
        ∑ j ∈ Finset.range (n+1),
          if shellCondition δ (distance i) j then kernel δ (distance i) else 0 := by
      obtain ⟨j,hj,hcond⟩ := exists_shell n (htop i hi)
      have hh := Finset.single_le_sum (s := Finset.range (n+1))
        (f := fun j => if shellCondition δ (distance i) j then kernel δ (distance i) else 0)
        (fun j _ => by split_ifs <;> first | exact kernel_nonneg _ _ | exact le_refl 0) hj
      simpa only [if_pos hcond] using hh
    have hh := Finset.sum_le_sum (fun i hi => hpoint i hi)
    rw [Finset.sum_comm] at hh
    simpa only [shells,Finset.sum_filter] using hh
  have hshell (j : ℕ) : (∑ i ∈ shells j, kernel δ (distance i)) ≤ 16*C := by
    have hrad : δ ≤ δ*(2:ℝ)^j := by
      have hp : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
      nlinarith
    have hsub : shells j ⊆ indices.filter (fun i => distance i ≤ δ*(2:ℝ)^j) := by
      intro i hi
      obtain ⟨hi,hcond⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨hi,?_⟩
      by_cases hz : j=0
      · simpa [shellCondition,hz] using hcond
      · exact (by simpa only [shellCondition,if_neg hz] using hcond :
          δ*(2:ℝ)^(j-1)<distance i ∧ distance i≤δ*(2:ℝ)^j).2
    have hcard' : ((shells j).card:ℝ) ≤
        ((indices.filter fun i => distance i ≤ δ*(2:ℝ)^j).card:ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hcard := hcard'.trans (hcap _ hrad)
    calc
      _ ≤ ∑ _i ∈ shells j, (2/(2:ℝ)^j)^4 :=
        Finset.sum_le_sum (fun i hi => shell_kernel_bound hδ (Finset.mem_filter.mp hi).2)
      _ = ((shells j).card:ℝ)*(2/(2:ℝ)^j)^4 := by simp
      _ ≤ (C*((δ*(2:ℝ)^j)/δ)^4)*(2/(2:ℝ)^j)^4 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by field_simp; ring
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ∑ i ∈ shells j, kernel δ (distance i) := hsumcover
    _ ≤ ∑ _j ∈ Finset.range (n+1), 16*C := Finset.sum_le_sum (fun j _ => hshell j)
    _ = _ := by simp; ring

/-- The original cap condition extends to every radius by the actual finite
radius-one cover, rather than a separate assumed total population bound. -/
theorem all_radius_cap {k M : ℕ} (F : TubeFamily (k+1) M) {δ A : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A) (hcap : F.CapBound δ 4 A)
    (v : Space (k+1)) (hv : ‖v‖=1) {r : ℝ} (hr : δ ≤ r) :
    ((Finset.univ.filter fun i => projectiveDistance (F.tube i).direction v ≤ r).card:ℝ) ≤
      (packingConstant k*A)*(r/δ)^4 := by
  have hp : 0 ≤ packingConstant k := zero_le_one.trans (packingConstant_ge_one k)
  by_cases hr1 : r ≤ 1
  · have hh : ((Finset.univ.filter fun i => projectiveDistance (F.tube i).direction v ≤ r).card:ℝ) ≤
        A*(r/δ)^4 := by simpa only [Real.rpow_ofNat] using hcap v hv r hr hr1
    have hpack := mul_le_mul_of_nonneg_right (packingConstant_ge_one k)
      (mul_nonneg hA (pow_nonneg (div_nonneg (hδ.le.trans hr) hδ.le) 4))
    exact hh.trans (by simpa only [one_mul,mul_assoc] using hpack)
  · have htotal : (M:ℝ) ≤ packingConstant k*A*(1/δ)^4 := by
      simpa only [Real.rpow_ofNat] using CapCover.cap_bound_total_count F hδ hδ1 hA hcap
    have hc : ((Finset.univ.filter fun i => projectiveDistance (F.tube i).direction v ≤ r).card:ℝ) ≤ M := by
      have hh := Finset.card_filter_le (s := (Finset.univ : Finset (Fin M)))
        (p := fun i => projectiveDistance (F.tube i).direction v ≤ r)
      simp only [Finset.card_univ,Fintype.card_fin] at hh
      exact_mod_cast hh
    apply (hc.trans htotal).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hp hA)
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right
      (le_of_lt (lt_of_not_ge hr1)) hδ.le) 4

def rowCoefficient (k : ℕ) : ℝ := 48*packingConstant k/Real.log 2

theorem rowCoefficient_pos (k : ℕ) : 0 < rowCoefficient k := by
  unfold rowCoefficient
  exact div_pos (mul_pos (by norm_num) (zero_lt_one.trans_le (packingConstant_ge_one k)))
    (Real.log_pos (by norm_num))

theorem depth_log {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ((dyadicDepth δ:ℕ):ℝ)+1 ≤ (3/Real.log 2)*Real.log (2/δ) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log (2/δ) := Real.log_le_log (by norm_num)
    ((le_div_iff₀ hδ).mpr (by linarith))
  apply (dyadicDepth_log_bound hδ hδ1).trans
  rw [Real.logb]
  calc
    _ ≤ Real.log (2/δ)/Real.log 2+2*Real.log (2/δ)/Real.log 2 :=
      add_le_add (le_refl _) ((le_div_iff₀ hl2).mpr (by linarith))
    _ = _ := by ring

/-- The actual original cap-four family has a uniform logarithmic quartic row
sum. Including the diagonal is harmless and requires no separation premise. -/
theorem family_row_bound {k M : ℕ} (F : TubeFamily (k+1) M) {δ A : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 0 ≤ A) (hcap : F.CapBound δ 4 A)
    (i : Fin M) :
    (∑ j : Fin M, kernel δ (projectiveDistance (F.tube j).direction (F.tube i).direction)) ≤
      rowCoefficient k*A*Real.log (2/δ) := by
  have hh := quartic_shell_sum (Finset.univ : Finset (Fin M))
    (fun j => projectiveDistance (F.tube j).direction (F.tube i).direction) hδ (dyadicDepth δ)
    (fun j _ => (TubeIntersection.unit_projective_le_two _ _ (F.tube j).unit_direction
      (F.tube i).unit_direction).trans (dyadicDepth_covers hδ))
    (fun r hr => all_radius_cap F hδ hδ1 hA hcap _ (F.tube i).unit_direction hr)
  have hd := mul_le_mul_of_nonneg_left (depth_log hδ hδ1)
    (show 0 ≤ 16*(packingConstant k*A) by
      exact mul_nonneg (by norm_num) (mul_nonneg (zero_le_one.trans (packingConstant_ge_one k)) hA))
  exact hh.trans (hd.trans_eq (by unfold rowCoefficient; ring))

end
end KakeyaFormal.GaussianCollisionKernel
