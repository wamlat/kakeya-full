import AngularGroupPruning

/-! Concrete global angular seed pieces from the verified whole-cell assignment:
common scale, actual nonempty indexed families, and deletion of low-mass groups. -/
namespace KakeyaFormal.AngularSeedPieces
open AngularDecomposition AngularAssignment AngularIncidence AngularGroupRestriction AngularGroupPruning
noncomputable section
open Classical

/-- Fixed directional overlap constant in the actual angular assignment. -/
def angularConstant (k : ℕ) : ℝ := ProjectiveGeometry.packingConstant k*(3:ℝ)^k

/-- Explicit retained incidence fraction at a finite depth. -/
def retentionRate (k J : ℕ) : ℝ := 3/(8*angularConstant k*((J:ℝ)+1))

theorem angularConstant_pos (k : ℕ) : 0 < angularConstant k := by
  have hP := ProjectiveGeometry.packingConstant_ge_one k
  dsimp [angularConstant]
  positivity

theorem retentionRate_pos (k J : ℕ) : 0 < retentionRate k J := by
  dsimp [retentionRate]
  positivity [angularConstant_pos k]

theorem retentionRate_le_one (k J : ℕ) : retentionRate k J ≤ 1 := by
  have hP := ProjectiveGeometry.packingConstant_ge_one k
  have hpow : (1:ℝ) ≤ (3:ℝ)^k := one_le_pow₀ (by norm_num)
  have hC : 1 ≤ angularConstant k := by dsimp [angularConstant]; nlinarith
  dsimp [retentionRate]
  apply (div_le_one (by positivity [angularConstant_pos k])).mpr
  nlinarith [show (0:ℝ) ≤ J from Nat.cast_nonneg J]

/-- Actual data returned by the finite assignment, with its precise quantitative
properties. The groups and shadings are constructed, not supplied cap witnesses. -/
structure Pieces {k M : ℕ} (F : TubeFamily (k+1) M) (δ beta : ℝ) where
  J : ℕ
  tau : ℝ
  groups : Finset (Fin M)
  assign : Fin M → Fin M
  shading : Fin M → Fin M → Finset (Cell (k+1))
  depth : (J:ℝ) ≤ Real.log (1/δ)/Real.log 2
  lower_scale : δ ≤ tau
  upper_scale : tau ≤ 1
  assign_mem : ∀ i, assign i ∈ groups
  subset : ∀ g i, shading g i ⊆ F.shade i
  unique : ∀ g i, (shading g i).Nonempty → assign i = g
  local_cap : ∀ g ∈ groups, ∀ i, (shading g i).Nonempty →
    projectiveDistance (F.tube i).direction (F.tube g).direction ≤ 3*tau
  retained : retentionRate k J*(∑ i, ((F.shade i).card:ℝ)) ≤
    ∑ g ∈ groups, mass (shading g)
  broad : ∀ z, ∀ g ∈ groups, Broad F (Finset.univ.filter (fun i => z ∈ shading g i))
    δ beta tau ((4:ℝ)^beta*(4*angularConstant k))
  overlap : ∀ z, ((groups.filter (fun g => ∃ i, z ∈ shading g i)).card:ℝ) ≤ 2*tau^(-beta)

/-- The full original grid union yields actual angular pieces with no spatial
bin overhead; the fixed angular width is three. -/
theorem exists_pieces {k M : ℕ} (F : TubeFamily (k+1) M) (hM : 0 < M)
    {δ beta : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) : Nonempty (Pieces F δ beta) := by
  obtain ⟨J,j,net,assign,S,hdepth,hlo,hhi,hassign,hsub,hunique,hlocal,hmass,hbroad,hover⟩ :=
    actual_angular_shading_assignment F hM F.unionCells (Finset.Subset.refl _) hδ hδ1 hb
  refine ⟨⟨J,Localization.radius J j,net,assign,S,hdepth,hlo,hhi,hassign,
    fun g i => (hsub g i).1,hunique,hlocal,?_,hbroad,hover⟩⟩
  have halg : retentionRate k J*(∑ i, ((F.shade i).card:ℝ)) =
      (3/(4*(ProjectiveGeometry.packingConstant k*(3:ℝ)^k)))*
        (incidenceMass F F.unionCells/(2*((J:ℝ)+1))) := by
    rw [incidenceMass_union]
    dsimp [retentionRate,angularConstant]
    field_simp
    ring
  rw [halg]
  exact hmass

/-- Actual nonempty tube families attached to the constructed groups. -/
def Pieces.family {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (g : Fin M) : TubeFamily (k+1) (active (P.shading g)).card :=
  AngularGroupRestriction.family F (P.shading g)

theorem Pieces.family_cap {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) {g : Fin M} (hg : g ∈ P.groups) :
    ∀ i, projectiveDistance ((P.family g).tube i).direction (F.tube g).direction ≤ 3*P.tau :=
  family_local_cap F (P.shading g) (F.tube g).direction (P.local_cap g hg)

theorem Pieces.family_mass {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (g : Fin M) :
    (∑ i, (((P.family g).shade i).card:ℝ)) = mass (P.shading g) := mass_eq _

theorem Pieces.total_family_count {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) : (∑ g ∈ P.groups, (active (P.shading g)).card) ≤ M :=
  total_active_count P.groups P.shading P.assign P.unique

/-- The fixed loss parameter used by every retained measurable box. -/
def Pieces.eta {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) : ℝ := retentionRate k P.J/4

theorem Pieces.eta_pos {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) : 0 < P.eta := div_pos (retentionRate_pos k P.J) (by norm_num)

theorem Pieces.eta_le_one {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) : P.eta ≤ 1 := by
  have h := retentionRate_le_one k P.J
  dsimp [Pieces.eta]
  linarith

/-- The actual retained groups, defined by their measured finite incidence budget. -/
def Pieces.keptGroups {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (lam : ℝ) : Finset (Fin M) :=
  kept P.groups P.shading (P.eta*(lam/δ))

/-- Actual comparable input supplies the uniform group retained-mass budget. -/
theorem Pieces.pruning {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam : ℝ}
    (P : Pieces F δ beta) (hδ : 0 < δ) (hlam : 0 < lam) (hcomp : F.Comparable δ lam) :
    P.keptGroups lam ⊆ P.groups ∧
      (∀ g ∈ P.keptGroups lam, 0 < (active (P.shading g)).card ∧
        P.eta*(lam/δ)*((active (P.shading g)).card:ℝ) ≤ mass (P.shading g)) ∧
      (3*retentionRate k P.J/4)*(lam/δ)*(M:ℝ) ≤
        ∑ g ∈ P.keptGroups lam, mass (P.shading g) ∧
      (3*retentionRate k P.J/8)*(M:ℝ) ≤
        ∑ g ∈ P.keptGroups lam, ((active (P.shading g)).card:ℝ) ∧
      (∑ g ∈ P.keptGroups lam, (active (P.shading g)).card) ≤ M := by
  have htotal : (lam/δ)*(M:ℝ) ≤ ∑ i, ((F.shade i).card:ℝ) := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin M))) (fun i _ => (hcomp i).1)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using h
  have hm : retentionRate k P.J*(lam/δ)*(M:ℝ) ≤ ∑ g ∈ P.groups, mass (P.shading g) := by
    have h := mul_le_mul_of_nonneg_left htotal (retentionRate_pos k P.J).le
    have hh : retentionRate k P.J*(lam/δ)*(M:ℝ) ≤ retentionRate k P.J*(∑ i, ((F.shade i).card:ℝ)) := by
      simpa only [mul_assoc] using h
    exact hh.trans P.retained
  exact prune_assigned_groups F P.groups P.shading P.assign P.unique P.subset hδ hlam
    (retentionRate_pos k P.J) (fun i => (hcomp i).2) hm

/-- Pointwise overlap is preserved by both exact compression and group deletion. -/
theorem Pieces.kept_overlap {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam : ℝ}
    (P : Pieces F δ beta) (z : Cell (k+1)) :
    (((P.keptGroups lam).filter (fun g => ∃ i, z ∈ (P.family g).shade i)).card:ℝ) ≤ 2*P.tau^(-beta) := by
  unfold Pieces.family
  rw [AngularGroupRestriction.group_overlap]
  apply le_trans ?_ (P.overlap z)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro g hg
  exact Finset.mem_filter.mpr ⟨kept_subset _ _ _ (Finset.mem_filter.mp hg).1,(Finset.mem_filter.mp hg).2⟩

end
end KakeyaFormal.AngularSeedPieces
