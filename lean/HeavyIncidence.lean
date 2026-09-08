import CoarseFamily
import BallPruning

/-! Actual heavy-cell restrictions and their incidence loss, derived from the
base estimate through constructed coarse tube families. -/
namespace KakeyaFormal.HeavyIncidence
open Finset Coarsening
open scoped BigOperators
noncomputable section
open Classical

/-- Heavy labels are defined by the actual cardinalities of disjoint fine-cell
fibers. The strict inequality matches the survivor definition in BallPruning. -/
def heavyLabels {k : ℕ} (E : Finset (Cell k)) (δ r L d : ℝ) : Finset (Cell k) :=
  (E.image (coarseLabel δ r)).filter fun z =>
    L*(r/δ)^d < ((E.filter (fun q => coarseLabel δ r q = z)).card : ℝ)

def heavyShade {k M : ℕ} (F : TubeFamily k M) (E : Finset (Cell k))
    (δ r L d : ℝ) (i : Fin M) : Finset (Cell k) :=
  (F.shade i).filter fun q => coarseLabel δ r q ∈ heavyLabels E δ r L d

/-- Excess total mass forces many tubes above half the average threshold. The
selected finite set is the actual threshold filter. -/
theorem many_large {M : ℕ} (b : Fin M → ℝ) {eta lam : ℝ}
    (heta : 0 < eta) (hlam : 0 < lam)
    (hupper : ∀ i, b i ≤ 2*lam) (hexcess : eta*lam*M < ∑ i, b i) :
    eta*(M : ℝ)/4 ≤ ((univ.filter fun i => eta*lam/2 ≤ b i).card : ℝ) := by
  let a := eta*lam/2
  let S : Finset (Fin M) := univ.filter fun i => a ≤ b i
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hpoint (i : Fin M) : b i ≤ a + if a ≤ b i then 2*lam else 0 := by
    split_ifs with hi
    · linarith [hupper i]
    · simp only [add_zero]
      exact (lt_of_not_ge hi).le
  have hh := sum_le_sum (s := univ) (fun i _ => hpoint i)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  have hid : (∑ i : Fin M, if a ≤ b i then 2*lam else 0) = 2*lam*(S.card : ℝ) := by
    rw [← sum_filter]
    simp [S,mul_comm]
  rw [hid] at hh
  have htarget : eta*(M : ℝ)/4 < (S.card : ℝ) := by
    apply (mul_lt_mul_iff_left₀ hlam).mp
    dsimp [a] at hh
    nlinarith
  exact htarget.le

/-- The selected heavy shadings are an actual injectively indexed tube family;
the cap condition is inherited without assuming original separation. -/
theorem select_heavy {k M : ℕ} (F : TubeFamily k M) (E : Finset (Cell k))
    {δ r L d m A width R eta lam : ℝ}
    (hδ : 0 < δ) (heta : 0 < eta) (hlam : 0 < lam)
    (hadm : F.Admissible width δ) (hbounded : F.Bounded R) (hcap : F.CapBound δ m A)
    (hupper : ∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam)
    (hexcess : eta*lam*M < δ*∑ i, ((heavyShade F E δ r L d i).card : ℝ)) :
    ∃ N : ℕ, ∃ G : TubeFamily k N,
      eta*(M : ℝ)/4 ≤ (N : ℝ) ∧ G.Admissible width δ ∧ G.Bounded R ∧ G.CapBound δ m A ∧
      (∀ i, eta*lam/2 ≤ δ*((G.shade i).card : ℝ)) ∧
      G.unionCells.image (coarseLabel δ r) ⊆ heavyLabels E δ r L d := by
  let b : Fin M → ℝ := fun i => δ*((heavyShade F E δ r L d i).card : ℝ)
  let S : Finset (Fin M) := univ.filter fun i => eta*lam/2 ≤ b i
  have hb (i : Fin M) : b i ≤ 2*lam := by
    apply le_trans (mul_le_mul_of_nonneg_left (show ((heavyShade F E δ r L d i).card : ℝ) ≤ (F.shade i).card by
      exact_mod_cast card_le_card (filter_subset _ _)) hδ.le) (hupper i)
  have hS := many_large b heta hlam hb (by simpa only [b,mul_sum] using hexcess)
  let e : Fin S.card → Fin M := fun i => (S.equivFin.symm i).val
  let G : TubeFamily k S.card := ⟨fun i => F.tube (e i), fun i => heavyShade F E δ r L d (e i)⟩
  have hemem (i : Fin S.card) : e i ∈ S := (S.equivFin.symm i).property
  have he : Function.Injective e := Subtype.val_injective.comp S.equivFin.symm.injective
  have hsep : F.Separated 0 := fun i j _ => projectiveDistance_nonneg _ _
  obtain ⟨_,hGb,hGc⟩ := DiscreteMeasurable.injective_tube_restriction F G e he (fun _ => rfl)
    hsep hbounded hcap
  refine ⟨S.card,G,hS,?_,hGb,hGc,?_,?_⟩
  · intro i q hq
    exact hadm (e i) q (mem_filter.mp hq).1
  · intro i
    exact (mem_filter.mp (hemem i)).2
  · intro z hz
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
    exact (mem_filter.mp hi).2


/-- If deletion at one scale exceeds the allowed incidence mass, the actual
coarse union bound and disjoint heavy fibers force this lower bound for E. -/
theorem excess_forces_union {k : ℕ} {m d p eps c width R : ℝ}
    (hc : 0 < c)
    (hcoarse : ∀ {M : ℕ} (F : TubeFamily (k+1) M) {δ r s A : ℝ},
      0 < δ → δ ≤ r → r ≤ 1 → 0 ≤ s → 1 ≤ A →
      F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, s ≤ δ*((F.shade i).card : ℝ)) →
      c*A⁻¹*δ^m*r^(-d+eps)*s^p*M ≤ ((F.unionCells.image (coarseLabel δ r)).card : ℝ))
    {M : ℕ} (F : TubeFamily (k+1) M) (E : Finset (Cell (k+1)))
    {δ r L A eta lam : ℝ} (hδ : 0 < δ) (hdr : δ ≤ r) (hr1 : r ≤ 1)
    (hL : 0 ≤ L) (hA : 1 ≤ A) (heta : 0 < eta) (hlam : 0 < lam)
    (hadm : F.Admissible width δ) (hbounded : F.Bounded R) (hcap : F.CapBound δ m A)
    (hupper : ∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam)
    (hexcess : eta*lam*M < δ*∑ i, ((heavyShade F E δ r L d i).card : ℝ)) :
    (L*(r/δ)^d) * (c*A⁻¹*δ^m*r^(-d+eps)*(eta*lam/2)^p*(eta*(M : ℝ)/4)) ≤ (E.card : ℝ) := by
  obtain ⟨N,G,hN,hGa,hGb,hGc,hGmass,hGU⟩ := select_heavy F E hδ heta hlam hadm hbounded hcap hupper hexcess
  have hr := hδ.trans_le hdr
  have hbound := hcoarse G hδ hdr hr1 (by positivity) hA hGa hGb hGc hGmass
  have hcoef : 0 ≤ c*A⁻¹*δ^m*r^(-d+eps)*(eta*lam/2)^p := by
    have : 0 < A := by linarith
    positivity
  have hHbound : c*A⁻¹*δ^m*r^(-d+eps)*(eta*lam/2)^p*(eta*(M : ℝ)/4) ≤
      ((heavyLabels E δ r L d).card : ℝ) :=
    ((mul_le_mul_of_nonneg_left hN hcoef).trans hbound).trans (by exact_mod_cast card_le_card hGU)
  have hheavy := heavy_cell_mass E (heavyLabels E δ r L d) δ r (L*(r/δ)^d)
    (filter_subset _ _) (fun z hz => (mem_filter.mp hz).2.le)
  exact (mul_le_mul_of_nonneg_left hHbound (by positivity)).trans hheavy

/-- The exact scalar identity reveals the cutoff's exponents and all finite
selection losses. -/
theorem heavy_identity {c L A δ r eta lam m d p eps N : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (heta : 0 < eta) (hlam : 0 < lam) :
    (L*(r/δ)^d) * (c*A⁻¹*δ^m*r^(-d+eps)*(eta*lam/2)^p*(eta*N/4)) =
      (c/(4*(2:ℝ)^p))*L*A⁻¹*δ^(m-d)*r^eps*eta^(p+1)*lam^p*N := by
  rw [Real.div_rpow hr.le hδ.le,Real.div_rpow (mul_nonneg heta.le hlam.le) (by norm_num : (0:ℝ) ≤ 2),
    Real.mul_rpow heta.le hlam.le,Real.rpow_add heta,Real.rpow_one]
  have hδpow : δ^(m-d) = δ^m/δ^d := Real.rpow_sub hδ _ _
  have hrpow : r^(-d+eps) = r^eps/r^d := by
    rw [show -d+eps = eps-d by ring,Real.rpow_sub hr]
  rw [hδpow,hrpow]
  have hd0 := (Real.rpow_pos_of_pos hδ d).ne'
  have hr0 := (Real.rpow_pos_of_pos hr d).ne'
  field_simp

/-- A convenient normalized form of the heavy-incidence contradiction. -/
theorem excess_forces_union_normalized {k : ℕ} {m d p eps c width R : ℝ}
    (hc : 0 < c)
    (hcoarse : ∀ {M : ℕ} (F : TubeFamily (k+1) M) {δ r s A : ℝ},
      0 < δ → δ ≤ r → r ≤ 1 → 0 ≤ s → 1 ≤ A →
      F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, s ≤ δ*((F.shade i).card : ℝ)) →
      c*A⁻¹*δ^m*r^(-d+eps)*s^p*M ≤ ((F.unionCells.image (coarseLabel δ r)).card : ℝ))
    {M : ℕ} (F : TubeFamily (k+1) M) (E : Finset (Cell (k+1)))
    {δ r L A eta lam : ℝ} (hδ : 0 < δ) (hdr : δ ≤ r) (hr1 : r ≤ 1)
    (hL : 0 ≤ L) (hA : 1 ≤ A) (heta : 0 < eta) (hlam : 0 < lam)
    (hadm : F.Admissible width δ) (hbounded : F.Bounded R) (hcap : F.CapBound δ m A)
    (hupper : ∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam)
    (hexcess : eta*lam*M < δ*∑ i, ((heavyShade F E δ r L d i).card : ℝ)) :
    (c/(4*(2:ℝ)^p))*L*A⁻¹*δ^(m-d)*r^eps*eta^(p+1)*lam^p*M ≤ (E.card : ℝ) := by
  have hh := excess_forces_union hc hcoarse F E hδ hdr hr1 hL hA heta hlam hadm hbounded hcap hupper hexcess
  rwa [heavy_identity hδ (hδ.trans_le hdr) heta hlam] at hh


/-- Exact threshold calibration at the smallest allowed scale. -/
theorem threshold_identity {cp E A δ eta lam M m d p eps : ℝ}
    (hcp : 0 < cp) (hA : 0 < A) (hδ : 0 < δ) (heta : 0 < eta)
    (hlam : 0 < lam) (hM : 0 < M) :
    ((2/cp)*E*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/M) *
      (cp*A⁻¹*δ^(m-d)*δ^eps*eta^(p+1)*lam^p*M) = 2*E := by
  rw [Real.rpow_neg heta.le,Real.rpow_neg hlam.le]
  have hsum : δ^(d-m-eps)*δ^(m-d)*δ^eps = 1 := by
    rw [← Real.rpow_add hδ,← Real.rpow_add hδ,
      show (d-m-eps)+(m-d)+eps = 0 by ring,Real.rpow_zero]
  have hη0 := (Real.rpow_pos_of_pos heta (p+1)).ne'
  have hl0 := (Real.rpow_pos_of_pos hlam p).ne'
  calc
    _ = 2*E*(δ^(d-m-eps)*δ^(m-d)*δ^eps) := by field_simp
    _ = 2*E := by rw [hsum,mul_one]

/-- An excess restriction forces E to be nonempty. This handles the zero-union
edge case without dividing by its cardinality. -/
theorem union_pos_of_excess {k M : ℕ} (F : TubeFamily k M) (E : Finset (Cell k))
    {δ r L d eta lam : ℝ} (_hδ : 0 < δ) (heta : 0 < eta) (hlam : 0 < lam)
    (hexcess : eta*lam*M < δ*∑ i, ((heavyShade F E δ r L d i).card : ℝ)) :
    0 < (E.card : ℝ) := by
  by_contra hn
  have hz : E = ∅ := card_eq_zero.mp (by exact_mod_cast (le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg E.card)))
  have hzero (i : Fin M) : heavyShade F E δ r L d i = ∅ := by simp [heavyShade,heavyLabels,hz]
  simp only [hzero,card_empty,Nat.cast_zero,sum_const_zero,mul_zero] at hexcess
  have hnonneg : 0 ≤ eta*lam*(M : ℝ) := by positivity
  linarith

/-- At every scale δ≤r≤1 the calibrated cutoff bounds the actual heavy
incidence mass. The cutoff includes no r-dependent term. -/
theorem calibrated_mass_bound {k : ℕ} {m d p eps c width R : ℝ}
    (hc : 0 < c) (heps : 0 ≤ eps)
    (hcoarse : ∀ {M : ℕ} (F : TubeFamily (k+1) M) {δ r s A : ℝ},
      0 < δ → δ ≤ r → r ≤ 1 → 0 ≤ s → 1 ≤ A →
      F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, s ≤ δ*((F.shade i).card : ℝ)) →
      c*A⁻¹*δ^m*r^(-d+eps)*s^p*M ≤ ((F.unionCells.image (coarseLabel δ r)).card : ℝ))
    {M : ℕ} (F : TubeFamily (k+1) M) (E : Finset (Cell (k+1)))
    {δ r L A eta lam : ℝ} (hδ : 0 < δ) (hdr : δ ≤ r) (hr1 : r ≤ 1)
    (hL0 : 0 ≤ L) (hA : 1 ≤ A) (heta : 0 < eta) (hlam : 0 < lam)
    (hadm : F.Admissible width δ) (hbounded : F.Bounded R) (hcap : F.CapBound δ m A)
    (hupper : ∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam)
    (hL : (2/(c/(4*(2:ℝ)^p)))*(E.card : ℝ)*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/(M : ℝ) ≤ L) :
    δ*∑ i, ((heavyShade F E δ r L d i).card : ℝ) ≤ eta*lam*M := by
  by_contra hn
  have hexcess := lt_of_not_ge hn
  have hM : 0 < (M : ℝ) := by
    by_contra hh
    have hz : M = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg M))
    subst M
    simp at hexcess
  have hE := union_pos_of_excess F E hδ heta hlam hexcess
  have hA0 : 0 < A := by linarith
  let cp := c/(4*(2:ℝ)^p)
  have hcp : 0 < cp := by dsimp [cp]; positivity
  have hr := hδ.trans_le hdr
  have hforced := excess_forces_union_normalized hc hcoarse F E hδ hdr hr1 hL0 hA heta hlam hadm hbounded hcap hupper hexcess
  have hcoef : 0 ≤ cp*A⁻¹*δ^(m-d)*δ^eps*eta^(p+1)*lam^p*(M : ℝ) := by positivity
  have hcal := mul_le_mul_of_nonneg_right hL hcoef
  rw [threshold_identity hcp hA0 hδ heta hlam hM] at hcal
  have hscale := Real.rpow_le_rpow hδ.le hdr heps
  have hscaled := mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ cp*L*A⁻¹*δ^(m-d)*eta^(p+1)*lam^p*(M : ℝ) by positivity)
  have hcal' : 2*(E.card : ℝ) ≤ cp*L*A⁻¹*δ^(m-d)*δ^eps*eta^(p+1)*lam^p*(M : ℝ) := by
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hcal
  have hscaled' : cp*L*A⁻¹*δ^(m-d)*δ^eps*eta^(p+1)*lam^p*(M : ℝ) ≤
      cp*L*A⁻¹*δ^(m-d)*r^eps*eta^(p+1)*lam^p*(M : ℝ) := by
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hscaled
  have hh := (hcal'.trans hscaled').trans hforced
  linarith

/-- The base discrete estimate provides one cutoff constant before all actual
families, densities, cap coefficients and all testing scales. -/
theorem discrete_heavy_mass_bound {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p)
    (width R : ℝ) (hw : 0 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) (E : Finset (Cell (k+1)))
      {δ r L A eta lam : ℝ}, 0 < δ → δ ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ A →
      0 < eta → 0 < lam → F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam) →
      K*(E.card : ℝ)*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/(M : ℝ) ≤ L →
      δ*∑ i, ((heavyShade F E δ r L d i).card : ℝ) ≤ eta*lam*M := by
  obtain ⟨c,hc,hcoarse⟩ := CoarseFamily.coarse_union_estimate hbase hm hp width R hw eps heps
  refine ⟨2/(c/(4*(2:ℝ)^p)),by positivity,?_⟩
  intro M F E δ r L A eta lam hδ hdr hr1 hL0 hA heta hlam hadm hbounded hcap hupper hL
  exact calibrated_mass_bound hc heps.le hcoarse F E hδ hdr hr1 hL0 hA heta hlam hadm hbounded hcap hupper hL

end
end KakeyaFormal.HeavyIncidence

#print axioms KakeyaFormal.HeavyIncidence.many_large
#print axioms KakeyaFormal.HeavyIncidence.select_heavy
#print axioms KakeyaFormal.HeavyIncidence.excess_forces_union_normalized
#print axioms KakeyaFormal.HeavyIncidence.calibrated_mass_bound
#print axioms KakeyaFormal.HeavyIncidence.discrete_heavy_mass_bound
