import LocalizedDirectionThinning
import GridTwoEnds
import TubeLocalCount

/-! Actual normalized localized families for the two-ends seed. A single
common homothety works for all localization centers because the seed has
no bounded-base premise. The dilation is chosen large enough to make its
actual comparable density at most one, using the proved local tube count. -/
namespace KakeyaFormal.LocalizedSeedNormalization
open LocalizedDirectionThinning LocalizedGridTubes Rescaling GridTwoEnds
noncomputable section
open Classical

/-- Explicit local shading population coefficient. -/
def countConstant (k : ℕ) (width : ℝ) : ℝ :=
  (6+4*localWidth width)*((2*Nat.ceil (localWidth width+1)+3:ℕ):ℝ)^k

/-- One fixed dilation coefficient handles both unit-axis length and density. -/
def dilationConstant (k : ℕ) (width : ℝ) : ℝ := max (8*localWidth width) (countConstant k width)

theorem dilationConstant_ge_one (k : ℕ) (width : ℝ) : 1 ≤ dilationConstant k width := by
  have hW : 1 ≤ localWidth width := le_max_left _ _
  exact (by linarith : (1:ℝ) ≤ 8*localWidth width).trans (le_max_left _ _)

theorem dilationConstant_pos (k : ℕ) (width : ℝ) : 0 < dilationConstant k width :=
  zero_lt_one.trans_le (dilationConstant_ge_one k width)

theorem localized_card_upper {k M : ℕ} (F : TubeFamily k M) {δ rho width : ℝ}
    (hδ : 0 < δ) (hδrho : δ ≤ rho) (centers : Fin M → Space k)
    (hadm : F.Admissible width δ)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho) (i : Fin M) :
    ((F.shade i).card:ℝ) ≤ countConstant k width*(rho/δ) := by
  apply TubeLocalCount.tube_ball_grid_count_real (F.tube i) hδ (localWidth_pos width).le hδrho (centers i)
  · intro z hz
    obtain ⟨t,ht,hd⟩ := hadm i z hz
    exact ⟨t,ht,hd.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le)⟩
  · exact hball i

/-- The common comparable density is automatically legal after the chosen
fixed dilation. This is derived from geometry rather than assumed or clamped. -/
theorem normalized_density_le_one {k M : ℕ} (F : TubeFamily k M) {δ rho width s : ℝ}
    (hM : 0 < M) (hδ : 0 < δ) (hδrho : δ ≤ rho) (centers : Fin M → Space k)
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ s)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho) :
    s/(dilationConstant k width*rho) ≤ 1 := by
  have hrho := hδ.trans_le hδrho
  have hL := mul_pos (dilationConstant_pos k width) hrho
  have hi := localized_card_upper F hδ hδrho centers hadm hball ⟨0,hM⟩
  have hm := (hcomp ⟨0,hM⟩).1.trans hi
  have hs : s ≤ countConstant k width*rho := by
    apply (div_le_div_iff_of_pos_right hδ).mp
    simpa only [← mul_div_assoc] using hm
  apply (div_le_one hL).mpr
  exact hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hrho.le)

/-- Actual short original axes embed in the one common dilation interval. -/
theorem normalized_axis_intervals {k M : ℕ} (F : TubeFamily k M) {δ rho width : ℝ}
    (hδ : 0 < δ) (hδrho : δ ≤ rho) (centers : Fin M → Space k)
    (hne : ∀ i, (F.shade i).Nonempty) (hadm : F.Admissible width δ)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho) :
    ∃ a : Fin M → ℝ, ∀ i z, z ∈ F.shade i →
      ∃ t ∈ Set.Icc (a i) (a i+dilationConstant k width*rho),
        dist (cellCenter δ z) ((F.tube i).axisPoint t) ≤ localWidth width*δ := by
  have hrho := hδ.trans_le hδrho
  choose a _ hlocal using fun i => localized_grid_interval (F.tube i) (F.shade i)
    hδ hδrho (centers i) (hne i) (hadm i) (hball i)
  refine ⟨a,?_⟩
  intro i z hz
  obtain ⟨t,ht,hd⟩ := hlocal i z hz
  refine ⟨t,⟨ht.1,ht.2.trans ?_⟩,hd⟩
  have hh := mul_le_mul_of_nonneg_right (le_max_left (8*localWidth width) (countConstant k width)) hrho.le
  simpa only [dilationConstant,add_comm] using add_le_add_left hh (a i)

/-- The full actual interface needed to apply the proved two-ends seed after
localization: exact shadings, legal density, standard separation, fixed cap
coefficient, a single inverse original cap loss, and the original union. -/
theorem normalize_localized_family {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ rho width s alpha B m A : ℝ} (hM : 0 < M) (hδ : 0 < δ) (hδrho : δ ≤ rho)
    (hrho1 : rho ≤ 1) (hs : 0 < s) (ha : 0 ≤ alpha) (hB : 1 ≤ B) (hm : 0 ≤ m) (hA : 1 ≤ A)
    (centers : Fin M → Space (k+1)) (hadm : F.Admissible width δ) (hcomp : F.Comparable δ s)
    (hcap : F.CapBound δ m A)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho)
    (hends : ∀ i, ∀ x : Space (k+1), ∀ r : ℝ, δ ≤ r → r ≤ rho →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*(r/rho)^alpha*((F.shade i).card:ℝ)) :
    let L := dilationConstant (k+1) width*rho
    0 < δ/L ∧ δ/L ≤ 1 ∧ 0 < s/L ∧ s/L ≤ 1 ∧
    ∃ N : ℕ, 0 < N ∧ ∃ e : Fin N → Fin M, Function.Injective e ∧
      ∃ G : TubeFamily (k+1) N,
        ((M:ℝ)*rho^m)/(retentionConstant k m*A) ≤ (N:ℝ) ∧
        G.Admissible (localWidth width) (δ/L) ∧ G.Comparable (δ/L) (s/L) ∧
        G.Separated (δ/L) ∧ G.CapBound (δ/L) m (capConstant k m) ∧
        (∀ i, (G.shade i).card = (F.shade (e i)).card) ∧
        G.unionCells.card ≤ F.unionCells.card ∧
        ∀ i x r, δ/L ≤ r →
          (((G.shade i).filter (fun z => dist (cellCenter (δ/L) z) x ≤ r)).card:ℝ) ≤
            (B*(dilationConstant (k+1) width)^alpha)*r^alpha*((G.shade i).card:ℝ) := by
  let L := dilationConstant (k+1) width*rho
  have hrho := hδ.trans_le hδrho
  have hL : 0 < L := mul_pos (dilationConstant_pos _ _) hrho
  have hrhoL : rho ≤ L := le_mul_of_one_le_left hrho.le (dilationConstant_ge_one _ _)
  have hδL := hδrho.trans hrhoL
  have hne : ∀ i, (F.shade i).Nonempty := by
    intro i
    exact Finset.card_pos.mp (by exact_mod_cast ((div_pos hs hδ).trans_le (hcomp i).1))
  obtain ⟨a,hinterval⟩ := normalized_axis_intervals F hδ hδrho centers hne hadm hball
  obtain ⟨N,e,he,H,hN,htubes,hshades,hsep,hcaps,hU⟩ :=
    thin_at_localized_scale F hδ (hδrho.trans hrho1) hrho hrho1 hrhoL hδL hm hA hcap
  have hNpos : 0 < N := by
    have hpos : 0 < ((M:ℝ)*rho^m)/(retentionConstant k m*A) := by
      have hM' : (0:ℝ) < M := by exact_mod_cast hM
      have hC := retentionConstant_pos k m
      positivity
    exact_mod_cast hpos.trans_le hN
  let G := Rescaling.family H L δ (0:Cell (k+1)) (fun i => a (e i))
  have hHcomp : H.Comparable δ s := by
    intro i
    rw [hshades i]
    exact hcomp (e i)
  have hHends : ∀ i, ∀ x : Space (k+1), ∀ r : ℝ, δ ≤ r → r ≤ rho →
      (((H.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*(r/rho)^alpha*((H.shade i).card:ℝ) := by
    intro i x r hr hr1
    simpa only [hshades i] using hends (e i) x r hr hr1
  refine ⟨div_pos hδ hL,(div_le_one hL).mpr hδL,div_pos hs hL,
    normalized_density_le_one F hM hδ hδrho centers hadm hcomp hball,
    N,hNpos,e,he,G,hN,?_,rescaled_comparable H hL.ne' _ _ hHcomp,hsep,hcaps,?_,?_,?_⟩
  · apply rescaled_admissible H hL
    intro i z hz
    rw [htubes i]
    exact hinterval (e i) z (by simpa only [hshades i] using hz)
  · intro i
    exact (rescaled_card H L δ 0 _ i).trans (congrArg Finset.card (hshades i))
  · exact (rescaled_union_card H L δ 0 _).trans_le (Finset.card_le_card hU)
  · have hh := rescaled_two_ends H hL hδ hrho hB ha 0 (fun i => a (e i)) hHends
    have hid : L/rho = dilationConstant (k+1) width := by dsimp [L]; field_simp
    simpa only [hid] using hh

end
end KakeyaFormal.LocalizedSeedNormalization
