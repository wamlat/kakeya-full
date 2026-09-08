import FamilyLocalization
import AngularSeedLogLoss

/-! Actual common-radius localization of finite grid shadings through their
physical Euclidean centers. All localized subsets remain original cells. -/
namespace KakeyaFormal.FiniteGridLocalization
open FamilyLocalization KakeyaFormal.Localization UniformLocalization AngularSeedLogLoss
noncomputable section
open Classical

theorem cellCenter_injective {k : ℕ} {δ : ℝ} (hδ : 0 < δ) : Function.Injective (cellCenter (k := k) δ) := by
  intro z w h
  funext i
  have hi := congrArg (fun x : Space k => x i) h
  change δ*(z i:ℝ) = δ*(w i:ℝ) at hi
  have hh := mul_left_cancel₀ hδ.ne' hi
  exact_mod_cast hh

/-- Finite original cells tested at their actual physical centers. -/
def restrictCells {k : ℕ} (δ : ℝ) (S : Finset (Cell k)) (x : Space k) (r : ℝ) : Finset (Cell k) :=
  S.filter (fun z => dist (cellCenter δ z) x ≤ r)

theorem restrict_image {k : ℕ} (δ : ℝ) (S : Finset (Cell k)) (x : Space k) (r : ℝ) :
    Localization.restrict (S.image (cellCenter δ)) x r = (restrictCells δ S x r).image (cellCenter δ) := by
  rw [Localization.restrict,Finset.filter_image]
  rfl

theorem image_mass {k : ℕ} {δ : ℝ} (hδ : 0 < δ) (S : Finset (Cell k)) :
    Localization.mass (fun _ : Space k => (1:ℝ)) (S.image (cellCenter δ)) = (S.card:ℝ) := by
  simp only [Localization.mass,Finset.sum_const,nsmul_eq_mul,mul_one,
    Finset.card_image_of_injective _ (cellCenter_injective hδ)]

/-- Common-radius selection is constructed from the actual physical grid
centers, preserving original cell subsets and all original-scale ball tests. -/
theorem common_radius {k M : ℕ} (F : TubeFamily k M) {δ alpha : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ alpha)
    (x₀ : Fin M → Space k) (hcover : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (x₀ i) ≤ 1) :
    ∃ J j : ℕ, ∃ centers : Fin M → Space k, ∃ selected : Finset (Fin M),
      j ≤ J ∧ (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      (M:ℝ)/(J+1:ℕ) ≤ (selected.card:ℝ) ∧
      δ ≤ radius J j ∧ radius J j ≤ 1 ∧
      ∀ i ∈ selected,
        (radius J j)^alpha*((F.shade i).card:ℝ) ≤ ((restrictCells δ (F.shade i) (centers i) (radius J j)).card:ℝ) ∧
        ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ radius J j →
          (((restrictCells δ (F.shade i) (centers i) (radius J j)).filter
            (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
              (4:ℝ)^alpha*(r/(radius J j))^alpha*
                ((restrictCells δ (F.shade i) (centers i) (radius J j)).card:ℝ) := by
  obtain ⟨J,j,x,S,hj,hdepth,hcount,hlo,hhi,hlocal⟩ := finite_family_localization
    (fun i => (F.shade i).image (cellCenter δ)) (fun _ => (1:ℝ)) (fun _ => by norm_num)
    (fun _ => (1:ℝ)) hδ hδ1 ha x₀ (by
      intro i y hy
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
      exact hcover i z hz)
  refine ⟨J,j,x,S,hj,hdepth,?_,hlo,hhi,?_⟩
  · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hcount
  · intro i hi
    obtain ⟨hmass,hends⟩ := hlocal i hi
    refine ⟨?_,?_⟩
    · simpa only [restrict_image,image_mass hδ] using hmass
    · intro y r hr hr1
      simpa only [restrict_image,image_mass hδ,restrictCells] using hends y r hr hr1

/-- Actual common radius and density class for finite original cells. -/
structure Selection {k M : ℕ} (F : TubeFamily k M) (δ alpha lam : ℝ) where
  J : ℕ
  D : ℕ
  rho : ℝ
  s : ℝ
  centers : Fin M → Space k
  selected : Finset (Fin M)
  nonempty : selected.Nonempty
  radius_lower : δ ≤ rho
  radius_upper : rho ≤ 1
  radius_depth : (J:ℝ) ≤ Real.log (1/δ)/Real.log 2
  density_depth : (D:ℝ)+1 ≤ alpha*(Real.log (1/δ)/Real.log 2)+3
  count_lower : (M:ℝ)/((J+1:ℕ)*(D+1:ℕ)) ≤ (selected.card:ℝ)
  density_pos : 0 < s
  density_lower : rho^alpha*lam ≤ s
  comparable : ∀ i ∈ selected,
    s/δ ≤ ((restrictCells δ (F.shade i) (centers i) rho).card:ℝ) ∧
    ((restrictCells δ (F.shade i) (centers i) rho).card:ℝ) ≤ 2*s/δ
  two_ends : ∀ i ∈ selected, ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ rho →
    (((restrictCells δ (F.shade i) (centers i) rho).filter
      (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        (4:ℝ)^alpha*(r/rho)^alpha*((restrictCells δ (F.shade i) (centers i) rho).card:ℝ)

/-- Construct both actual classes without changing cells or assuming desired
comparability. Both logarithmic depths are bounded independently of lambda. -/
theorem exists_selection {k M : ℕ} (F : TubeFamily k M) {δ alpha lam : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 ≤ alpha) (hlam : 0 < lam)
    (hcomp : F.Comparable δ lam) (x₀ : Fin M → Space k)
    (hcover : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (x₀ i) ≤ 1) :
    Nonempty (Selection F δ alpha lam) := by
  obtain ⟨J,j,x,S,hj,hJ,hcount,hlo,hhi,hlocal⟩ := common_radius F hδ hδ1 ha x₀ hcover
  let rho := radius J j
  let Z := fun i => restrictCells δ (F.shade i) (x i) rho
  let b := rho^alpha*(lam/δ)
  have hrho : 0 < rho := hδ.trans_le hlo
  have hb : 0 < b := mul_pos (Real.rpow_pos_of_pos hrho alpha) (div_pos hlam hδ)
  have hS : S.Nonempty := Finset.card_pos.mp (by
    have hh := (div_pos (by exact_mod_cast hM) (by positivity : (0:ℝ) < (J+1:ℕ))).trans_le hcount
    exact_mod_cast hh)
  have hlow (i : Fin M) (hi : i ∈ S) : b ≤ ((Z i).card:ℝ) :=
    (mul_le_mul_of_nonneg_left (hcomp i).1 (Real.rpow_pos_of_pos hrho alpha).le).trans (hlocal i hi).1
  have hupp (i : Fin M) : ((Z i).card:ℝ) ≤ 2*lam/δ :=
    (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans (hcomp i).2
  obtain ⟨i₀,hi₀⟩ := hS
  obtain ⟨D,hD,hDlog⟩ := ScaleChoice.dyadic_class_budget hb ((hlow i₀ hi₀).trans (hupp i₀))
  obtain ⟨ell,hell,R,hRS,hrange,hret⟩ := OccupancySelection.weighted_dyadic_selection S
    (fun i => ((Z i).card:ℝ)) (fun _ => (1:ℝ)) hb D hlow
    (fun i _ => (hupp i).trans (by simpa only [mul_comm] using hD))
  have hRcard : (S.card:ℝ)/(D+1:ℕ) ≤ (R.card:ℝ) := by
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hret
  have htotal : (M:ℝ)/((J+1:ℕ)*(D+1:ℕ)) ≤ (R.card:ℝ) := by
    have hh := (div_le_div_of_nonneg_right hcount (by positivity : (0:ℝ) ≤ (D+1:ℕ))).trans hRcard
    simpa only [div_div] using hh
  have hRne : R.Nonempty := Finset.card_pos.mp (by
    have hh := (div_pos (by exact_mod_cast hM) (by positivity : (0:ℝ) < (J+1:ℕ)*(D+1:ℕ))).trans_le htotal
    exact_mod_cast hh)
  let s := δ*(b*(2:ℝ)^ell)
  have hs : 0 < s := by dsimp [s]; positivity
  have hslo : rho^alpha*lam ≤ s := by
    have hp : (1:ℝ) ≤ (2:ℝ)^ell := one_le_pow₀ (by norm_num)
    have hh := mul_le_mul_of_nonneg_left hp (mul_pos (Real.rpow_pos_of_pos hrho alpha) hlam).le
    calc
      _ ≤ rho^alpha*lam*(2:ℝ)^ell := by simpa only [mul_one] using hh
      _ = s := by dsimp [s,b]; field_simp
  have hDfinal : (D:ℝ)+1 ≤ alpha*(Real.log (1/δ)/Real.log 2)+3 := by
    have hlog2 : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
    have hratio : (2*lam/δ)/b = 2/rho^alpha := by dsimp [b]; field_simp
    have hlogrho := Real.log_le_log hδ hlo
    have hmul := mul_le_mul_of_nonneg_left hlogrho ha
    rw [hratio,Real.log_div (by norm_num : (2:ℝ) ≠ 0) (Real.rpow_pos_of_pos hrho alpha).ne',Real.log_rpow hrho] at hDlog
    rw [one_div,Real.log_inv]
    apply le_trans hDlog
    apply (mul_le_mul_iff_right₀ hlog2).mp
    field_simp
    linarith
  refine ⟨⟨J,D,rho,s,x,R,hRne,hlo,hhi,hJ,hDfinal,htotal,hs,hslo,?_,?_⟩⟩
  · intro i hi
    have hh := hrange i hi
    have hlo' : s/δ = b*(2:ℝ)^ell := by dsimp [s]; field_simp
    rw [hlo']
    refine ⟨hh.1,?_⟩
    have hhi' : 2*s/δ = 2*(b*(2:ℝ)^ell) := by dsimp [s]; field_simp
    rw [hhi']
    exact hh.2.le
  · intro i hi
    exact (hlocal i (hRS hi)).2

end
end KakeyaFormal.FiniteGridLocalization
