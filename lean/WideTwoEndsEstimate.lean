import TwoEndsDiscreteEstimate

/-! Fixed comparable-density normalization for unmarked full two-ends data.
Every original tube remains, and actual old cells are trimmed to a common
integer count. The two-ends coefficient loses only a fixed factor, independent
of delta and lambda. No claim of marked broadness preservation is made. -/
namespace KakeyaFormal.WideTwoEndsEstimate
open Finset
noncomputable section
open Classical

def lowerFactor (c₀ : ℝ) : ℝ := min c₀ (1/2)

theorem lowerFactor_pos {c₀ : ℝ} (hc₀ : 0 < c₀) : 0 < lowerFactor c₀ :=
  lt_min hc₀ (by norm_num)

/-- Actual simultaneous trimming on every original index, including the
single-cell regime. The new density is delta*ceil(a*lambda/delta)/2. -/
theorem normalize_rows {n M : ℕ} (F : TubeFamily n M) {δ lam c₀ C₀ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hlower : ∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ))
    (hupper : ∀ i, ((F.shade i).card:ℝ) ≤ C₀*lam/δ) :
    ∃ G : TubeFamily n M, ∃ nu : ℝ,
      0 < nu ∧ nu ≤ 1 ∧ (lowerFactor c₀/2)*lam ≤ nu ∧
      G.tube=F.tube ∧ (∀ i, G.shade i ⊆ F.shade i) ∧ G.Comparable δ nu ∧
      ∀ i, ((F.shade i).card:ℝ) ≤ (C₀/lowerFactor c₀)*((G.shade i).card:ℝ) := by
  let a := lowerFactor c₀
  have ha : 0 < a := lowerFactor_pos hc₀
  have ha0 : a ≤ c₀ := min_le_left _ _
  have ha1 : a ≤ 1/2 := min_le_right _ _
  let K := Nat.ceil (a*lam/δ)
  have hK : 0 < K := Nat.ceil_pos.mpr (by positivity)
  have hKR : (0:ℝ) < K := by exact_mod_cast hK
  have hKold (i) : K ≤ (F.shade i).card := by
    apply Nat.ceil_le.mpr
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha0 hlam.le) hδ.le).trans (hlower i)
  choose Z hZ hZcard using fun i => Finset.exists_subset_card_eq (hKold i)
  let G : TubeFamily n M := ⟨F.tube,Z⟩
  let nu := δ*(K:ℝ)/2
  have hnu : 0 < nu := by dsimp [nu]; positivity
  have hceil : a*lam ≤ δ*(K:ℝ) := by
    have hh := Nat.le_ceil (a*lam/δ)
    exact ((div_le_iff₀ hδ).mp hh).trans_eq (mul_comm _ _)
  have hceilUpper : δ*(K:ℝ) < a*lam+δ := by
    have hh := mul_lt_mul_of_pos_left (Nat.ceil_lt_add_one (by positivity : 0 ≤ a*lam/δ)) hδ
    change δ*(K:ℝ) < _ at hh
    have hid : δ*(a*lam/δ+1) = a*lam+δ := by field_simp
    simpa only [hid] using hh
  have hnu1 : nu ≤ 1 := by
    have hprod : a*lam ≤ 1/2 := (mul_le_mul_of_nonneg_left hlam1 ha.le).trans (by simpa using ha1)
    dsimp [nu]
    linarith
  refine ⟨G,nu,hnu,hnu1,by dsimp [nu]; dsimp only [a] at hceil; linarith,rfl,hZ,?_,?_⟩
  · intro i
    change nu/δ ≤ (Z i).card ∧ ((Z i).card:ℝ) ≤ 2*nu/δ
    rw [hZcard i]
    dsimp [nu]
    constructor
    · apply (div_le_iff₀ hδ).mpr
      nlinarith
    · apply (le_div_iff₀ hδ).mpr
      nlinarith
  · intro i
    change ((F.shade i).card:ℝ) ≤ (C₀/a)*((Z i).card:ℝ)
    rw [hZcard i]
    apply (hupper i).trans
    apply (div_le_iff₀ hδ).mpr
    have hh := mul_le_mul_of_nonneg_left hceil (div_nonneg hC₀.le ha.le)
    have hid : (C₀/a)*(a*lam)=C₀*lam := by field_simp
    rw [hid] at hh
    nlinarith

/-- A proved normalized two-ends estimate applies to any fixed positive
lower/upper density multiples. Its new B is fixed before configurations. -/
theorem from_two_ends {n : ℕ} {m d p : ℝ}
    (hestimate : TwoEndsDiscreteEstimate n m d p) (hp : 0 ≤ p)
    (geom : Normalization) (c₀ C₀ B alpha eps : ℝ)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀) (hB : 1 ≤ B)
    (halpha : 0 < alpha) (heps : 0 < eps) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily n M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      F.Admissible geom.width δ → F.Separated (geom.separation*δ) →
      F.Bounded geom.radius → F.CapBound δ m A →
      (∀ i, c₀*lam/δ ≤ ((F.shade i).card:ℝ)) →
      (∀ i, ((F.shade i).card:ℝ) ≤ C₀*lam/δ) →
      F.FullTwoEnds δ B alpha →
      c*A⁻¹*δ^(m-d+eps)*lam^p*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  let a := lowerFactor c₀
  have ha : 0 < a := lowerFactor_pos hc₀
  let BN := max 1 (B*C₀/a)
  obtain ⟨c,hc,hbound⟩ := hestimate geom BN alpha eps (le_max_left _ _) halpha heps
  refine ⟨c*(a/2)^p,by positivity,?_⟩
  intro M F δ lam A hδ hδ1 hlam hlam1 hA hadm hsep hbounded hcap hlo hhi hends
  obtain ⟨G,nu,hnu,hnu1,hnuLow,htube,hsub,hcomp,hcounts⟩ :=
    normalize_rows F hδ hδ1 hlam hlam1 hc₀ hC₀ hlo hhi
  have hGends : G.FullTwoEnds δ BN alpha := by
    intro i x r hr hr1
    have hcell : ((G.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card ≤
        ((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card :=
      card_le_card (filter_subset_filter _ (hsub i))
    have hball := hends i x r hr hr1
    have hh := mul_le_mul_of_nonneg_left (hcounts i)
      (mul_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg (hδ.trans_le hr).le alpha))
    have hBN := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (B*C₀/a))
      (mul_nonneg (Real.rpow_nonneg (hδ.trans_le hr).le alpha) (Nat.cast_nonneg (G.shade i).card))
    calc
      _ ≤ (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) := by exact_mod_cast hcell
      _ ≤ B*r^alpha*((F.shade i).card:ℝ) := hball
      _ ≤ B*r^alpha*((C₀/a)*((G.shade i).card:ℝ)) := hh
      _ ≤ BN*r^alpha*((G.shade i).card:ℝ) := by simpa only [BN,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hBN
  let V : ShadedConfiguration n geom m := {
    M:=M, δ:=δ, lam:=nu, A:=A, family:=G,
    scale_pos:=hδ, scale_le_one:=hδ1, density_pos:=hnu, density_le_one:=hnu1,
    cap_ge_one:=hA,
    admissible:=fun i z hz => by rw [htube]; exact hadm i z (hsub i hz),
    separated:=by simpa only [TubeFamily.Separated,htube] using hsep,
    bounded:=by simpa only [TubeFamily.Bounded,htube] using hbounded,
    cap_bound:=by simpa only [TubeFamily.CapBound,htube] using hcap,
    comparable:=hcomp }
  have hGU : G.unionCells ⊆ F.unionCells := by
    intro z hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    exact F.shade_subset_union i (hsub i hi)
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (a/2)*lam) hnuLow hp
  rw [Real.mul_rpow (by positivity : 0 ≤ a/2) hlam.le] at hpow
  have hfactor : 0 ≤ c*A⁻¹*δ^(m-d+eps)*(M:ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hpow hfactor
  have hfinal := hbound V hGends
  have hunion : (G.unionCells.card:ℝ) ≤ (F.unionCells.card:ℝ) := by exact_mod_cast card_le_card hGU
  calc
    _ = (c*A⁻¹*δ^(m-d+eps)*(M:ℝ))*((a/2)^p*lam^p) := by ring
    _ ≤ (c*A⁻¹*δ^(m-d+eps)*(M:ℝ))*nu^p := hscaled
    _ ≤ (G.unionCells.card:ℝ) := by simpa only [V,mul_assoc,mul_left_comm,mul_comm] using hfinal
    _ ≤ _ := hunion

end
end KakeyaFormal.WideTwoEndsEstimate
