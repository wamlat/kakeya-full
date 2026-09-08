import FiniteGridLocalization
import LocalizedSeedNormalization

/-! Exact finite family from the constructed common localization classes,
with uniform logarithmic population and actual radius-density control. -/
namespace KakeyaFormal.FiniteLocalizedFamily
open FiniteGridLocalization LocalizedSeedNormalization AngularSeedLogLoss
noncomputable section
open Classical

def index {k M : ℕ} {F : TubeFamily k M} {δ alpha lam : ℝ}
    (S : Selection F δ alpha lam) (i : Fin S.selected.card) : Fin M := S.selected.equivFin.symm i

theorem index_injective {k M : ℕ} {F : TubeFamily k M} {δ alpha lam : ℝ}
    (S : Selection F δ alpha lam) : Function.Injective (index S) :=
  Subtype.val_injective.comp S.selected.equivFin.symm.injective

theorem index_mem {k M : ℕ} {F : TubeFamily k M} {δ alpha lam : ℝ}
    (S : Selection F δ alpha lam) (i : Fin S.selected.card) : index S i ∈ S.selected :=
  (S.selected.equivFin.symm i).property

def family {k M : ℕ} {F : TubeFamily k M} {δ alpha lam : ℝ}
    (S : Selection F δ alpha lam) : TubeFamily k S.selected.card where
  tube i := F.tube (index S i)
  shade i := restrictCells δ (F.shade (index S i)) (S.centers (index S i)) S.rho

theorem family_admissible {k M : ℕ} {F : TubeFamily k M} {δ alpha lam width : ℝ}
    (S : Selection F δ alpha lam) (hadm : F.Admissible width δ) : (family S).Admissible width δ := by
  intro i z hz
  exact hadm (index S i) z (Finset.mem_filter.mp hz).1

theorem family_comparable {k M : ℕ} {F : TubeFamily k M} {δ alpha lam : ℝ}
    (S : Selection F δ alpha lam) : (family S).Comparable δ S.s :=
  fun i => S.comparable _ (index_mem S i)

theorem family_ball {k M : ℕ} {F : TubeFamily k M} {δ alpha lam : ℝ}
    (S : Selection F δ alpha lam) : ∀ i z, z ∈ (family S).shade i →
      dist (cellCenter δ z) (S.centers (index S i)) ≤ S.rho :=
  fun _ _ hz => (Finset.mem_filter.mp hz).2

theorem family_two_ends {k M : ℕ} {F : TubeFamily k M} {δ alpha lam : ℝ}
    (S : Selection F δ alpha lam) : ∀ i, ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ S.rho →
      ((((family S).shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        (4:ℝ)^alpha*(r/S.rho)^alpha*(((family S).shade i).card:ℝ) :=
  fun i => S.two_ends _ (index_mem S i)

theorem family_cap_bound {k M : ℕ} {F : TubeFamily k M} {δ alpha lam m A : ℝ}
    (S : Selection F δ alpha lam) (hcap : F.CapBound δ m A) : (family S).CapBound δ m A := by
  intro center hunit r hr hr1
  have hc : (Finset.univ.filter (fun i => projectiveDistance ((family S).tube i).direction center ≤ r)).card ≤
      (Finset.univ.filter (fun i => projectiveDistance (F.tube i).direction center ≤ r)).card := by
    apply Finset.card_le_card_of_injOn (index S)
    · intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hi).2⟩
    · exact fun _ _ _ _ h => index_injective S h
  exact (Nat.cast_le.mpr hc).trans (hcap center hunit r hr hr1)

theorem family_union_subset {k M : ℕ} {F : TubeFamily k M} {δ alpha lam : ℝ}
    (S : Selection F δ alpha lam) : (family S).unionCells ⊆ F.unionCells := by
  intro z hz
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
  exact F.shade_subset_union (index S i) (Finset.mem_filter.mp hi).1

/-- The two actually constructed class budgets lose at most a fixed multiple
of the square of the original-scale logarithm. -/
theorem selected_count_log {k M : ℕ} {F : TubeFamily k M} {δ alpha lam : ℝ}
    (S : Selection F δ alpha lam) (hδ : 0 < δ) (ha : 0 ≤ alpha) :
    (M:ℝ)/((alpha+3)*(seedLog δ)^2) ≤ (S.selected.card:ℝ) := by
  have hδ1 := S.radius_lower.trans S.radius_upper
  have hL : 1 ≤ seedLog δ := seedLog_ge_one hδ hδ1
  have hX : Real.log (1/δ)/Real.log 2 ≤ seedLog δ := by rw [seedLog_identity hδ]; linarith
  have hJ : (S.J:ℝ)+1 ≤ seedLog δ := by rw [seedLog_identity hδ]; linarith [S.radius_depth]
  have hD : (S.D:ℝ)+1 ≤ (alpha+3)*seedLog δ := by
    have hh := mul_le_mul_of_nonneg_left hX ha
    linarith [S.density_depth]
  have hprod : ((S.J+1:ℕ)*(S.D+1:ℕ):ℝ) ≤ (alpha+3)*(seedLog δ)^2 := by
    push_cast
    have hh := mul_le_mul hJ hD (by positivity : (0:ℝ) ≤ (S.D:ℝ)+1) (by linarith : 0 ≤ seedLog δ)
    nlinarith
  exact (div_le_div_of_nonneg_left (Nat.cast_nonneg M) (by positivity) hprod).trans S.count_lower

/-- The actual common density is bounded by the linear local tube count. -/
theorem selected_density_upper {k M : ℕ} {F : TubeFamily k M} {δ alpha lam width : ℝ}
    (S : Selection F δ alpha lam) (hδ : 0 < δ) (hadm : F.Admissible width δ) :
    S.s ≤ countConstant k width*S.rho := by
  let i : Fin S.selected.card := ⟨0,Finset.card_pos.mpr S.nonempty⟩
  have hc := localized_card_upper (family S) hδ S.radius_lower (fun i => S.centers (index S i))
    (family_admissible S hadm) (family_ball S) i
  have hh := (family_comparable S i).1.trans hc
  apply (div_le_div_iff_of_pos_right hδ).mp
  simpa only [← mul_div_assoc] using hh

/-- Localization radius is controlled by the original density. This is the
actual geometric inequality later used to trade radius powers for density. -/
theorem radius_density {k M : ℕ} {F : TubeFamily k M} {δ alpha lam width : ℝ}
    (S : Selection F δ alpha lam) (hδ : 0 < δ) (hadm : F.Admissible width δ) :
    lam ≤ countConstant k width*S.rho^(1-alpha) := by
  have hrho := hδ.trans_le S.radius_lower
  have hh := S.density_lower.trans (selected_density_upper S hδ hadm)
  have hdiv := (le_div_iff₀ (Real.rpow_pos_of_pos hrho alpha)).mpr (by simpa only [mul_comm] using hh)
  exact hdiv.trans_eq (by rw [Real.rpow_sub hrho,Real.rpow_one]; ring)

end
end KakeyaFormal.FiniteLocalizedFamily
