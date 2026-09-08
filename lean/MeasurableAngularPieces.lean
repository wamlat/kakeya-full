import WeightedAngularSelection
import MeasurableAngularPruning
import AngularSeedPieces

/-! Actual measurable angular pieces, constructed by weighted selection on
literal incidence-pattern atoms. All retained sets lie in their own original
shading; pointwise angular properties hold everywhere. -/
namespace KakeyaFormal.MeasurableAngularPieces
open MeasureTheory Set AngularDecomposition MeasurableAngularGroups
open MeasurableAngularPruning AngularSeedPieces MeasurableIncidenceAtoms
open scoped ENNReal
noncomputable section
open Classical

structure Pieces {k M : ℕ} (F : TubeFamily (k+1) M)
    (Y : Fin M → Set (Space (k+1))) (δ beta : ℝ) where
  J : ℕ
  tau : ℝ
  groups : Finset (Fin M)
  assign : Fin M → Fin M
  shading : Fin M → Fin M → Set (Space (k+1))
  depth : (J:ℝ) ≤ Real.log (1/δ)/Real.log 2
  lower_scale : δ ≤ tau
  upper_scale : tau ≤ 1
  assign_mem : ∀ i, assign i ∈ groups
  measurable : ∀ g i, MeasurableSet (shading g i)
  finite : ∀ g i, volume (shading g i) ≠ ∞
  subset : ∀ g i, shading g i ⊆ Y i
  unique : ∀ g i, (shading g i).Nonempty → assign i = g
  local_cap : ∀ g ∈ groups, ∀ i, (shading g i).Nonempty →
    projectiveDistance (F.tube i).direction (F.tube g).direction ≤ 3*tau
  retained : retentionRate k J*(∑ i, volume.real (Y i)) ≤
    ∑ g ∈ groups, mass volume (shading g)
  broad : ∀ x, ∀ g ∈ groups,
    Broad F (Finset.univ.filter (fun i => x ∈ shading g i)) δ beta tau
      ((4:ℝ)^beta*(4*angularConstant k))
  overlap : ∀ x, ((groups.filter (fun g => ∃ i, x ∈ shading g i)).card:ℝ) ≤ 2*tau^(-beta)

/-- Arbitrary measurable finite-volume shadings admit exact angular pieces.
The exponentially large atom index set causes no cardinality loss. -/
theorem exists_pieces {k M : ℕ} (F : TubeFamily (k+1) M) (hM : 0 < M)
    (Y : Fin M → Set (Space (k+1))) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, volume (Y i) ≠ ∞) {δ beta : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) : Nonempty (Pieces F Y δ beta) := by
  obtain ⟨J,j,net,assign,kept,hdepth,hlo,hhi,hassign,hsub,hunique,hlocal,hmass,hbroad,hover⟩ :=
    WeightedAngularSelection.actual_angular_assignment F hM (patterns M)
      (fun s => volume.real (atom Y s)) (fun _ _ => measureReal_nonneg)
      id (fun s hs => (mem_patterns s).mp hs) hδ hδ1 hb
  let S := fun g => realize Y (fun s => kept s g)
  have hp (x) (hx : x ∈ ⋃ i, Y i) : pattern Y x ∈ patterns M := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact (mem_patterns _).mpr ⟨i,(mem_pattern Y x i).mpr hi⟩
  refine ⟨⟨J,Localization.radius J j,net,assign,S,hdepth,hlo,hhi,hassign,
    fun g => realize_measurable Y hY _,fun g => realize_finite volume Y hfin _,
    fun g => realize_subset Y _ (fun s hs => hsub s hs g),?_,?_,?_,?_,?_⟩⟩
  · intro g i hi
    obtain ⟨x,hx⟩ := hi
    obtain ⟨s,hs,_hxs⟩ := mem_iUnion₂.mp hx
    exact hunique s g i (Finset.mem_filter.mp hs).2
  · intro g hg i hi
    obtain ⟨x,hx⟩ := hi
    obtain ⟨s,hs,_hxs⟩ := mem_iUnion₂.mp hx
    exact hlocal s (Finset.mem_filter.mp hs).1 g hg i (Finset.mem_filter.mp hs).2
  · have heq : (∑ g ∈ net, mass volume (S g)) =
        ∑ s ∈ patterns M, volume.real (atom Y s)*(∑ g ∈ net, ((kept s g).card:ℝ)) := by
      simp only [S,mass]
      simp_rw [realize_incidence_mass volume Y hY hfin]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.mul_sum]
    rw [heq]
    convert hmass using 1
    simp only [id_eq]
    rw [incidence_mass volume Y hY hfin]
    dsimp [retentionRate,angularConstant]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · intro x g hg
    change Broad F (pattern (realize Y (fun s => kept s g)) x) _ _ _ _
    by_cases hx : x ∈ ⋃ i, Y i
    · rw [realize_pattern Y _ hx]
      exact hbroad (pattern Y x) (hp x hx) g hg
    · rw [realize_pattern_outside Y _ hx]
      intro center r hr
      simp [cap]
  · intro x
    by_cases hx : x ∈ ⋃ i, Y i
    · have heq (g) : (∃ i, x ∈ S g i) ↔ (kept (pattern Y x) g).Nonempty := by
        rw [← realize_pattern Y (fun s => kept s g) hx]
        simp only [S,pattern,Finset.filter_nonempty_iff,Finset.mem_univ,true_and]
      simp_rw [heq]
      exact hover (pattern Y x) (hp x hx)
    · have heq (g) : ¬∃ i, x ∈ S g i := by
        rintro ⟨i,hi⟩
        exact hx (realize_union_subset Y (fun s => kept s g) (mem_iUnion.mpr ⟨i,hi⟩))
      simp only [heq,Finset.filter_false,Finset.card_empty,Nat.cast_zero]
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Localization.radius_pos J j).le _)

/-- Measured low-group deletion, with all original full sets retained on each
compressed group's actual original indices. -/
theorem Pieces.pruning {k M : ℕ} {F : TubeFamily (k+1) M}
    {Y : Fin M → Set (Space (k+1))} {δ beta lam : ℝ} (P : Pieces F Y δ beta)
    (hlam : 0 < lam) (hfin : ∀ i, volume (Y i) ≠ ∞)
    (hlower : ∀ i, lam ≤ volume.real (Y i)) (hupper : ∀ i, volume.real (Y i) ≤ 2*lam) :
    let G := kept volume P.groups P.shading ((retentionRate k P.J/4)*lam)
    G ⊆ P.groups ∧
      (∀ g ∈ G, 0 < (active (P.shading g)).card ∧
        (retentionRate k P.J/4)*lam*((active (P.shading g)).card:ℝ) ≤ mass volume (P.shading g)) ∧
      (3*retentionRate k P.J/4)*lam*(M:ℝ) ≤ ∑ g ∈ G, mass volume (P.shading g) ∧
      (3*retentionRate k P.J/8)*(M:ℝ) ≤ ∑ g ∈ G, ((active (P.shading g)).card:ℝ) ∧
      (∑ g ∈ G, (active (P.shading g)).card) ≤ M := by
  have hm : lam*(M:ℝ) ≤ ∑ i, volume.real (Y i) := by
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm]
      using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) (fun i _ => hlower i)
  have hret := (mul_le_mul_of_nonneg_left hm (retentionRate_pos k P.J).le).trans P.retained
  exact prune_assigned_groups volume Y P.groups P.shading P.assign P.unique P.subset hfin
    hlam (retentionRate_pos k P.J) hupper (by simpa only [mul_assoc] using hret)

end
end KakeyaFormal.MeasurableAngularPieces
