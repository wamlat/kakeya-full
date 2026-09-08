import AnisotropicDirections
import CapCover

/-! Actual family direction separation and cap bounds after anisotropic box
normalization. The large pulled-back cap branch uses the finite global cap cover. -/
namespace KakeyaFormal.AnisotropicCap
open AnisotropicRescaling AnisotropicDirections ProjectiveGeometry
noncomputable section
open Classical

/-- An actual transformed family for a chosen unit-segment color and chosen
new grid shadings. Direction results are independent of the shading choice. -/
def family {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    {tau : ℝ} (htau : tau ≠ 0) (q : Cell k) (j : Fin M → ℕ)
    (shading : Fin M → Finset (Cell (k+1))) : TubeFamily (k+1) M where
  tube i := transformedTube u htau q (F.tube i) (j i)
  shade := shading

/-- The separation loss is a fixed angular-width constant only. -/
theorem family_separated {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    {tau angular δ : ℝ} (hu : ‖u‖ = 1) (htau : 0 < tau) (htau1 : tau ≤ 1)
    (ha : 0 ≤ angular)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hsep : F.Separated δ) (q : Cell k) (j : Fin M → ℕ)
    (shading : Fin M → Finset (Cell (k+1))) :
    (family F u htau.ne' q j shading).Separated (δ/(4*(1+2*angular)^2*tau)) := by
  intro i i' hii'
  exact transformed_direction_separation u (F.tube i).direction (F.tube i').direction hu
    (F.tube i).unit_direction (F.tube i').unit_direction htau htau1 ha
    (hlocal i) (hlocal i') (hsep i i' hii')

/-- Actual arbitrary-center cap counts at the new scale delta/tau, with a
coefficient fixed before either scale is chosen. -/
theorem family_cap_bound {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1))
    {tau angular δ m A : ℝ} (hu : ‖u‖ = 1) (hδ : 0 < δ)
    (hδtau : δ ≤ tau) (htau1 : tau ≤ 1) (ha : 0 ≤ angular) (hm : 0 ≤ m) (hA : 0 ≤ A)
    (hlocal : ∀ i, projectiveDistance (F.tube i).direction u ≤ angular*tau)
    (hcap : F.CapBound δ m A) (q : Cell k) (j : Fin M → ℕ)
    (shading : Fin M → Finset (Cell (k+1))) :
    (family F u (ne_of_gt (hδ.trans_le hδtau)) q j shading).CapBound (δ/tau) m
      (packingConstant k*A*(8*(1+2*angular)^2)^m) := by
  have htau : 0 < tau := hδ.trans_le hδtau
  let C := 4*(1+2*angular)^2
  have hC : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg angular]
  have hC0 : 0 < C := by linarith
  intro center _hcenter r hr _hr1
  let G := family F u htau.ne' q j shading
  let S := Finset.univ.filter (fun i => projectiveDistance (G.tube i).direction center ≤ r)
  change (S.card:ℝ) ≤ _
  have hr0 : 0 < r := (div_pos hδ htau).trans_le hr
  have hratio : 0 < r/(δ/tau) := div_pos hr0 (div_pos hδ htau)
  have hPc : 1 ≤ packingConstant k := packingConstant_ge_one k
  have hP0 : 0 ≤ packingConstant k := by linarith
  have hcoef0 : 0 ≤ packingConstant k*A*(8*(1+2*angular)^2)^m*(r/(δ/tau))^m := by positivity
  by_cases hne : S.Nonempty
  · obtain ⟨i0,hi0⟩ := hne
    let R := 2*C*tau*r
    have hR0 : 0 < R := by dsimp [R]; positivity
    have hRδ : δ ≤ R := by
      have hdr : δ ≤ r*tau := (div_le_iff₀ htau).mp hr
      dsimp [R]
      nlinarith
    have hsub : S ⊆ Finset.univ.filter (fun i =>
        projectiveDistance (F.tube i).direction (F.tube i0).direction ≤ R) := by
      intro i hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ i,?_⟩
      have htri := projective_triangle (G.tube i).direction center (G.tube i0).direction
      have hi' := (Finset.mem_filter.mp hi).2
      have hi0' := (Finset.mem_filter.mp hi0).2
      rw [projective_symm center (G.tube i0).direction] at htri
      have hang : projectiveDistance (G.tube i).direction (G.tube i0).direction ≤ 2*r := by linarith
      have hinv := transformed_projective_inverse u (F.tube i).direction (F.tube i0).direction
        hu (F.tube i).unit_direction (F.tube i0).unit_direction htau htau1 ha (hlocal i) (hlocal i0)
      have hinv' : projectiveDistance (F.tube i).direction (F.tube i0).direction ≤
          C*tau*projectiveDistance (G.tube i).direction (G.tube i0).direction := hinv
      exact hinv'.trans (by dsimp [R]; nlinarith)
    have hsmallcount : (S.card:ℝ) ≤
        ((Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction
          (F.tube i0).direction ≤ R)).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    have hproduct : (R/δ)^m = (8*(1+2*angular)^2)^m*(r/(δ/tau))^m := by
      have halg : R/δ = (8*(1+2*angular)^2)*(r/(δ/tau)) := by
        dsimp [R,C]
        field_simp
        ring
      rw [halg,Real.mul_rpow (by positivity) (le_of_lt hratio)]
    have hcount : (S.card:ℝ) ≤ packingConstant k*A*(R/δ)^m := by
      by_cases hR1 : R ≤ 1
      · have hc := hsmallcount.trans (hcap (F.tube i0).direction (F.tube i0).unit_direction R hRδ hR1)
        have hp : A*(R/δ)^m ≤ packingConstant k*(A*(R/δ)^m) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hPc (by positivity : 0 ≤ A*(R/δ)^m)
        exact hc.trans (by simpa only [mul_assoc] using hp)
      · have hcard : (S.card:ℝ) ≤ M := by
          have hc : S.card ≤ M := by
            simpa only [S,Finset.card_univ,Fintype.card_fin] using
              (Finset.card_filter_le (s := Finset.univ)
                (p := fun i => projectiveDistance (G.tube i).direction center ≤ r))
          exact_mod_cast hc
        have hall := CapCover.cap_bound_total_count F hδ (hδtau.trans htau1) hA hcap
        have hbase : 1/δ ≤ R/δ := div_le_div_of_nonneg_right (le_of_lt (lt_of_not_ge hR1)) hδ.le
        have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1/δ) hbase hm
        exact (hcard.trans hall).trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hP0 hA))
    rw [hproduct] at hcount
    simpa only [mul_assoc] using hcount
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero]
    exact hcoef0

end
end KakeyaFormal.AnisotropicCap
