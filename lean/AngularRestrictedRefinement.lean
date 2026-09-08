import MarkedDensityClass
import AngularPiecePopulation

/-! Actual full/marked refinement inside the angular reference unions. Full
shadings remain whole reference shadings of the selected original tubes. The
density class is selected by marked mass and broadness is proportionally restored. -/
namespace KakeyaFormal.AngularRestrictedRefinement
open Finset AngularSeedPieces AngularGroupRestriction AngularDecomposition
open DensityBroadnessRecovery
open scoped BigOperators
noncomputable section
open Classical

/-- Original full shadings on the actual active group indices, used only to
inherit original two ends and an upper density. -/
def original {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (g : Fin M) : TubeFamily (k+1) (active (P.shading g)).card :=
  ⟨(P.family g).tube,fun i => F.shade (AngularGroupRestriction.index (P.shading g) i)⟩

def broadCoefficient (k : ℕ) (beta : ℝ) : ℝ := (4:ℝ)^beta*(4*angularConstant k)

theorem broadCoefficient_pos (k : ℕ) (beta : ℝ) : 0 < broadCoefficient k beta := by
  unfold broadCoefficient
  positivity [angularConstant_pos k]

structure Refinement {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta : ℝ}
    (P : Pieces F δ beta) (lam B alpha : ℝ) (g : Fin M) where
  N : ℕ
  population_pos : 0 < N
  index : Fin N → Fin (active (P.shading g)).card
  index_injective : Function.Injective index
  family : TubeFamily (k+1) N
  full_exact : ∀ i, family.tube i = (P.family g).tube (index i) ∧
    family.shade i = (P.family g).shade (index i)
  marks : Fin N → Finset (Cell (k+1))
  marks_subset : ∀ i, marks i ⊆ family.shade i
  density : ℝ
  density_pos : 0 < density
  density_lower : P.eta*lam/2 ≤ density
  density_upper : density ≤ 2*lam
  comparable : family.Comparable δ density
  depth : ℕ
  depth_bound : (depth:ℝ)+1 ≤ Real.log (4/P.eta)/Real.log 2+2
  marked_mass : P.eta*lam*((active (P.shading g)).card:ℝ)/(8*(depth+1:ℕ)) ≤
    δ*∑ i, ((marks i).card:ℝ)
  marked_fraction : (∑ i, ((family.shade i).card:ℝ))/(4*(depth+1:ℕ)) ≤
    ∑ i, ((marks i).card:ℝ)
  broad : ∀ z, Broad family (row marks univ z) δ beta P.tau
    ((broadCoefficient k beta*(8/P.eta))*(2*(depth+1:ℕ)))
  two_ends : ∀ i x r, δ ≤ r → r ≤ 1 →
    (((family.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
      (B*(4/P.eta))*r^alpha*((family.shade i).card:ℝ)
  union_subset : family.unionCells ⊆ (P.family g).unionCells

/-- Complete finite refinement of every actually kept angular group. The
original Full sets are never used as the resulting full shadings. -/
theorem construct {k M : ℕ} (F : TubeFamily (k+1) M) {δ beta lam B alpha : ℝ}
    (P : Pieces F δ beta) (hδ : 0 < δ) (hlam : 0 < lam) (hB : 0 ≤ B)
    (hcomp : F.Comparable δ lam)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F.shade i).card:ℝ))
    (g : Fin M) (hg : g ∈ P.keptGroups lam) : Nonempty (Refinement P lam B alpha g) := by
  let O := (P.family g).shade
  let F₀ := original P g
  have heta := P.eta_pos
  have htau : 0 < P.tau := hδ.trans_le P.lower_scale
  have hK := broadCoefficient_pos k beta
  obtain ⟨hkept,hgroup,_,_,_⟩ := P.pruning hδ hlam hcomp
  have hNg : 0 < (active (P.shading g)).card := (hgroup g hg).1
  have hsub : ∀ i, O i ⊆ F₀.shade i := fun i => P.subset g (AngularGroupRestriction.index (P.shading g) i)
  have hupper : ∀ i, δ*((F₀.shade i).card:ℝ) ≤ 2*lam := by
    intro i
    simpa only [F₀,original,mul_comm] using
      (le_div_iff₀ hδ).mp (hcomp (AngularGroupRestriction.index (P.shading g) i)).2
  have hmass : P.eta*lam*((active (P.shading g)).card:ℝ) ≤ δ*∑ i, ((O i).card:ℝ) := by
    change P.eta*lam*((active (P.shading g)).card:ℝ) ≤ δ*∑ i, (((P.family g).shade i).card:ℝ)
    rw [P.family_mass g]
    calc
      _ = δ*(P.eta*(lam/δ)*((active (P.shading g)).card:ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (hgroup g hg).2 hδ.le
  have hbroad : ∀ z ∈ cells O, Broad F₀ (row O univ z) δ beta P.tau (broadCoefficient k beta) := by
    intro z _
    have hb := AngularGroupRestriction.family_broad F (P.shading g) (fun z => P.broad z g (hkept hg)) z
    exact hb
  have hends₀ : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F₀.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((F₀.shade i).card:ℝ) := fun i => hends _
  let G₀ := selectedFamily F₀ O δ P.eta lam
  let Z := marked O δ P.eta lam
  let H₀ := fun i => G₀.shade i ∩ Z
  obtain ⟨_,_,hper,hgoodmass,_,hhalf,hbroad₀,hends₁⟩ :=
    DensityBroadnessRecovery.recover F₀ O hδ heta hlam htau hK.le hB hsub hupper hmass hbroad hends₀
  have hHpos : 0 < ∑ i, ((H₀ i).card:ℝ) := by
    have hfullpos : 0 < δ*∑ i, ((G₀.shade i).card:ℝ) :=
      (by positivity : 0 < P.eta*lam*((active (P.shading g)).card:ℝ)/2).trans_le hgoodmass
    have hpos : 0 < ∑ i, ((G₀.shade i).card:ℝ) := (mul_pos_iff_of_pos_left hδ).mp hfullpos
    exact (half_pos hpos).trans_le hhalf
  have hmarksBroad : ∀ z, Broad G₀ (row H₀ univ z) δ beta P.tau ((broadCoefficient k beta)*(8/P.eta)) := by
    intro z
    by_cases hz : z ∈ Z
    · have heq : row H₀ univ z = row G₀.shade univ z := by ext i; simp [row,H₀,hz]
      rw [heq]
      exact hbroad₀ z hz
    · have heq : row H₀ univ z = ∅ := by simp [row,H₀,hz]
      rw [heq]
      intro v r _
      simp [cap]
  have hlo : 0 < P.eta*lam/2 := by positivity
  have hlu : P.eta*lam/2 ≤ 2*lam := by
    have hh := mul_le_mul_of_nonneg_right P.eta_le_one hlam.le
    nlinarith
  obtain ⟨D,ell,hell,hD,T,hT,hrange,hclass,hmarkhalf,hmarkall,hbr⟩ :=
    MarkedDensityClass.select G₀ H₀ hδ.le hlo hlu htau (by positivity : 0 ≤ broadCoefficient k beta*(8/P.eta))
      (fun i => (hper i).2.2.1) (fun i => (hper i).2.2.2) hHpos hmarksBroad
  let G := MarkedDensityClass.family G₀ T
  let H := MarkedDensityClass.marks H₀ T (2*(D+1:ℕ))
  let e := fun i => selectedIndex O δ P.eta lam (MarkedDensityClass.index T i)
  let density := (P.eta*lam/2)*(2:ℝ)^ell
  have hindex : Function.Injective e := (selectedIndex_injective O δ P.eta lam).comp
    (MarkedPruningRecovery.selectedIndex_injective T)
  have hfull (i : Fin T.card) : G.tube i = (P.family g).tube (e i) ∧ G.shade i = (P.family g).shade (e i) := ⟨rfl,rfl⟩
  have hHsub : ∀ i, H i ⊆ G.shade i := by
    intro i z hz
    exact (mem_inter.mp (mem_inter.mp hz).1).1
  have hdpos : 0 < density := mul_pos hlo (by positivity)
  have hdlower : P.eta*lam/2 ≤ density := by
    exact le_mul_of_one_le_right hlo.le (one_le_pow₀ (by norm_num))
  have hdensity (i : Fin T.card) : density ≤ δ*((G.shade i).card:ℝ) ∧
      δ*((G.shade i).card:ℝ) < 2*density :=
    hrange _ (MarkedPruningRecovery.selectedIndex_mem T i)
  obtain ⟨t,ht⟩ := hT
  have hdupper : density ≤ 2*lam := (hrange t ht).1.trans (hper t).2.2.2
  have hcompG : G.Comparable δ density := by
    intro i
    constructor
    · exact (div_le_iff₀ hδ).mpr (by simpa only [mul_comm] using (hdensity i).1)
    · exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using (hdensity i).2.le)
  have hdepth : (D:ℝ)+1 ≤ Real.log (4/P.eta)/Real.log 2+2 := by
    convert hD using 2
    congr 2
    field_simp
    norm_num
  have hmarkmass : P.eta*lam*((active (P.shading g)).card:ℝ)/(8*(D+1:ℕ)) ≤
      δ*∑ i, ((H i).card:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hmarkall hδ.le
    have hhalfδ := mul_le_mul_of_nonneg_left hhalf hδ.le
    apply (div_le_iff₀ (by positivity : (0:ℝ)<8*(D+1:ℕ))).mpr
    have ha := (div_le_iff₀ (by positivity : (0:ℝ)<2*(D+1:ℕ))).mp hmarkall
    nlinarith
  have hfullle : (∑ i, ((G.shade i).card:ℝ)) ≤ ∑ i, ((G₀.shade i).card:ℝ) := by
    change (∑ i, ((G₀.shade (MarkedDensityClass.index T i)).card:ℝ)) ≤ _
    rw [MarkedDensityClass.reindexed_sum]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
  have hmarkfrac : (∑ i, ((G.shade i).card:ℝ))/(4*(D+1:ℕ)) ≤ ∑ i, ((H i).card:ℝ) := by
    have hh := (div_le_div_of_nonneg_right hhalf (by positivity : (0:ℝ)≤2*(D+1:ℕ))).trans hmarkall
    have hh' := (div_le_div_of_nonneg_right hfullle (by positivity : (0:ℝ)≤4*(D+1:ℕ)))
    exact hh'.trans (by
      simpa only [div_div,show (2:ℝ)*(2*(D+1:ℕ)) = 4*(D+1:ℕ) by ring] using hh)
  refine ⟨{
    N := T.card
    population_pos := card_pos.mpr ⟨t,ht⟩
    index := e
    index_injective := hindex
    family := G
    full_exact := hfull
    marks := H
    marks_subset := hHsub
    density := density
    density_pos := hdpos
    density_lower := hdlower
    density_upper := hdupper
    comparable := hcompG
    depth := D
    depth_bound := hdepth
    marked_mass := hmarkmass
    marked_fraction := hmarkfrac
    broad := hbr
    two_ends := fun i => hends₁ (MarkedDensityClass.index T i)
    union_subset := ?_
  }⟩
  intro z hz
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
  exact (P.family g).shade_subset_union (e i) hi

/-- The retained original tube population has an explicit logarithmic lower
fraction, derived from actual marked mass and comparable full shading sizes. -/
theorem Refinement.population_lower {k M : ℕ} {F : TubeFamily (k+1) M} {δ beta lam B alpha : ℝ}
    {P : Pieces F δ beta} {g : Fin M} (V : Refinement P lam B alpha g)
    (hδ : 0 < δ) (hlam : 0 < lam) :
    P.eta*((active (P.shading g)).card:ℝ)/(32*(V.depth+1:ℕ)) ≤ (V.N:ℝ) := by
  have hupper : δ*∑ i, ((V.marks i).card:ℝ) ≤ 4*lam*(V.N:ℝ) := by
    rw [mul_sum]
    have hh : (∑ i : Fin V.N, δ*((V.marks i).card:ℝ)) ≤ ∑ _i : Fin V.N, 4*lam := by
      apply sum_le_sum
      intro i _
      have hcard : δ*((V.marks i).card:ℝ) ≤ δ*((V.family.shade i).card:ℝ) :=
        mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card (V.marks_subset i))) hδ.le
      have hfull : δ*((V.family.shade i).card:ℝ) ≤ 2*V.density := by
        simpa only [mul_comm] using (le_div_iff₀ hδ).mp (V.comparable i).2
      exact (hcard.trans hfull).trans (by linarith [V.density_upper])
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_comm] using hh
  have hm := (div_le_iff₀ (by positivity : (0:ℝ)<8*(V.depth+1:ℕ))).mp V.marked_mass
  have hmul := mul_le_mul_of_nonneg_right hupper (by positivity : (0:ℝ)≤8*(V.depth+1:ℕ))
  apply (div_le_iff₀ (by positivity : (0:ℝ)<32*(V.depth+1:ℕ))).mpr
  apply (mul_le_mul_iff_left₀ hlam).mp
  nlinarith

end
end KakeyaFormal.AngularRestrictedRefinement

#print axioms KakeyaFormal.AngularRestrictedRefinement.construct
