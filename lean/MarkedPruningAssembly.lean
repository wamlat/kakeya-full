import MarkedSpatialPruning
import MarkedPruningRecovery

/-! Original marked input, genuine spatial pruning with a marked-fraction
budget, and the concrete recovered full/marked family. The original comparison
M and E and the literal pruned union remain visible throughout. -/
namespace KakeyaFormal.MarkedPruningAssembly
open Finset TransverseAngles MarkedSubsetSamples
open scoped BigOperators
noncomputable section
open Classical

/-- An actual recovered input, indexed injectively by original tubes. The full
shadings are literally those of the original pruned family at those indices;
the marked cell filter affects only the separate marked shadings. -/
structure RecoveredInput {k M : ℕ} (F O : TubeFamily k M)
    (originalMarks : Fin M → Finset (Cell k)) (E : Finset (Cell k))
    (δ lam xi width R m A B alpha theta : ℝ) where
  N : ℕ
  count_pos : 0 < N
  count_le : N ≤ M
  index : Fin N → Fin M
  index_injective : Function.Injective index
  density : ℝ
  density_pos : 0 < density
  density_choice : density=lam/2 ∨ density=lam
  family : TubeFamily k N
  tube_eq : ∀ i, family.tube i=F.tube (index i)
  full_eq : ∀ i, family.shade i=O.shade (index i)
  marks : Fin N → Finset (Cell k)
  marks_subset : ∀ i, marks i ⊆ family.shade i
  original_marks_subset : ∀ i, marks i ⊆ originalMarks (index i)
  comparable : family.Comparable δ density
  admissible : family.Admissible width δ
  separated : family.Separated δ
  bounded : family.Bounded R
  cap_bound : family.CapBound δ m A
  union_subset_pruned : family.unionCells ⊆ O.unionCells
  union_subset_E : family.unionCells ⊆ E
  union_nonempty : family.unionCells.Nonempty
  comparison_pos : 0 < (E.card : ℝ)
  marked_mass : xi*lam*(M : ℝ)/(8*δ) ≤
    ∑ z ∈ family.unionCells, ((incident (markedFamily family marks) z).card : ℝ)
  marked_broad : ∀ z : Cell k, ∀ v : Space k, ‖v‖=1 →
    (((incident (markedFamily family marks) z).filter
      (fun i => projectiveDistance (family.tube i).direction v < theta)).card : ℝ) ≤
        ((incident (markedFamily family marks) z).card : ℝ)/2
  two_ends : ∀ i x r, δ ≤ r → r ≤ 1 →
    (((family.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
      (2*B)*r^alpha*((family.shade i).card : ℝ)

/-- Exact incidence double counting on the literal recovered full union. -/
theorem marked_union_mass {k N : ℕ} (G : TubeFamily k N)
    (marks : Fin N → Finset (Cell k)) (hsub : ∀ i, marks i ⊆ G.shade i) :
    (∑ z ∈ G.unionCells, ((incident (markedFamily G marks) z).card : ℝ))=
      ∑ i, ((marks i).card : ℝ) := by
  have hh := DensityBroadnessRecovery.incidence_sum marks univ G.unionCells
    (fun i _ => (hsub i).trans (G.shade_subset_union i))
  exact_mod_cast hh

/-- The original marked lower bound and literal pruning deletion budget imply
a positive recovered marked mass, without any assumed retained-mass premise. -/
theorem marked_budget {δ xi lam W R V : ℝ} {M : ℕ}
    (hδ : 0 < δ) (hxi : 0 < xi) (hlam : 0 < lam) (hM : 0 < M)
    (hW : xi*lam*(M : ℝ)/δ ≤ W) (hR : δ*R ≤ (xi/100)*lam*(M : ℝ))
    (hV : W/4-2*R ≤ V) : xi*lam*(M : ℝ)/(8*δ) ≤ V := by
  have hWδ := (div_le_iff₀ hδ).mp hW
  have hVδ := mul_le_mul_of_nonneg_left hV hδ.le
  have hpos : 0 < xi*lam*(M : ℝ) := by positivity
  apply (div_le_iff₀ (by positivity : 0 < 8*δ)).mpr
  nlinarith

/-- Local concrete assembly from the literal output of spatial pruning. -/
theorem recover_pruned {k M : ℕ} (F O : TubeFamily k M)
    (originalMarks : Fin M → Finset (Cell k)) (E : Finset (Cell k))
    {δ lam xi width R m A B alpha theta : ℝ}
    (hδ : 0 < δ) (hlam : 0 < lam) (hxi : 0 < xi) (hM : 0 < M) (hB : 0 ≤ B)
    (hcomp : F.Comparable δ lam) (hadm : F.Admissible width δ)
    (hsep : F.Separated δ) (hbounded : F.Bounded R) (hcap : F.CapBound δ m A)
    (hsub : ∀ i, O.shade i ⊆ F.shade i) (hOE : O.unionCells ⊆ E)
    (hmarks : ∀ i, originalMarks i ⊆ F.shade i)
    (hW : xi*lam*(M : ℝ)/δ ≤ ∑ i, ((originalMarks i).card : ℝ))
    (hdel : δ*∑ i, ((F.shade i \ O.shade i).card : ℝ) ≤ (xi/100)*lam*(M : ℝ))
    (hbroad : ∀ z ∈ DensityBroadnessRecovery.cells originalMarks, ∀ v : Space k, ‖v‖=1 →
      (((incident (markedFamily F originalMarks) z).filter
        (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
          ((incident (markedFamily F originalMarks) z).card : ℝ)/10)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
        B*r^alpha*((F.shade i).card : ℝ)) :
    Nonempty (RecoveredInput F O originalMarks E δ lam xi width R m A B alpha theta) := by
  obtain ⟨lam',hlam',hchoice,T,hT,hTcard,hGcomp,hmark,hmarksub,hbroad',hends'⟩ :=
    MarkedPruningRecovery.recover F O.shade originalMarks hδ hlam hB hcomp hsub hmarks hbroad hends
  let G := MarkedPruningRecovery.selectedFamily F O.shade T
  let marks := MarkedPruningRecovery.selectedMarks originalMarks O.shade T
  have hmass : xi*lam*(M : ℝ)/(8*δ) ≤ ∑ i, ((marks i).card : ℝ) :=
    marked_budget hδ hxi hlam hM hW hdel hmark
  have hI : 0 < xi*lam*(M : ℝ)/(8*δ) := by positivity
  have hN : 0 < T.card := by
    by_contra hn
    have hz : T.card=0 := by omega
    let _ : IsEmpty (Fin T.card) := ⟨fun i => by have := i.isLt; omega⟩
    have hzero : (∑ i, ((marks i).card : ℝ))=0 := by simp
    rw [hzero] at hmass
    linarith
  obtain ⟨hGadm,hGsep,hGbounded,hGcap,_⟩ :=
    MarkedPruningRecovery.selected_geometry F O.shade T hsub hadm hsep hbounded hcap
  have hGOp : G.unionCells ⊆ O.unionCells := by
    intro z hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    exact O.shade_subset_union _ hi
  have hGU : G.unionCells.Nonempty := by
    let i : Fin T.card := ⟨0,hN⟩
    have hc : 0 < ((G.shade i).card : ℝ) := (div_pos hlam' hδ).trans_le (hGcomp i).1
    obtain ⟨z,hz⟩ := card_pos.mp (show 0 < (G.shade i).card by exact_mod_cast hc)
    exact ⟨z,G.shade_subset_union i hz⟩
  have hEpos : 0 < (E.card : ℝ) := by exact_mod_cast card_pos.mpr (hGU.mono (hGOp.trans hOE))
  refine ⟨{
    N := T.card
    count_pos := hN
    count_le := hTcard
    index := MarkedPruningRecovery.selectedIndex T
    index_injective := MarkedPruningRecovery.selectedIndex_injective T
    density := lam'
    density_pos := hlam'
    density_choice := hchoice
    family := G
    tube_eq := fun _ => rfl
    full_eq := fun _ => rfl
    marks := marks
    marks_subset := fun i => (hmarksub i).1
    original_marks_subset := fun i => (hmarksub i).2
    comparable := hGcomp
    admissible := hGadm
    separated := hGsep
    bounded := hGbounded
    cap_bound := hGcap
    union_subset_pruned := hGOp
    union_subset_E := hGOp.trans hOE
    union_nonempty := hGU
    comparison_pos := hEpos
    marked_mass := by rw [marked_union_mass G marks (fun i => (hmarksub i).1)]; exact hmass
    marked_broad := ?_
    two_ends := hends'
  }⟩
  intro z v hv
  have hh := hbroad' z v hv
  have hn : (0:ℝ) ≤ (incident (markedFamily G marks) z).card := Nat.cast_nonneg _
  change _ ≤ ((incident (markedFamily G marks) z).card : ℝ)/2
  linarith

/-- Uniform original-input assembly: the base-estimate constant precedes the
marked fraction and every actual family. The original J, L, M, E and literal
pruned union are retained alongside the recovered marked input. -/
theorem construct {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (width R : ℝ) (hw : 0 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) (E : Finset (Cell (k+1)))
      (marks : Fin M → Finset (Cell (k+1))) {δ A lam xi B alpha theta : ℝ},
      0 < δ → δ ≤ 1 → 1 ≤ A → 0 < lam → 0 < xi → 0 < M → 0 ≤ B →
      (∀ i, F.shade i ⊆ E) → F.Admissible width δ → F.Separated δ → F.Bounded R →
      F.CapBound δ m A → F.Comparable δ lam → (∀ i, marks i ⊆ F.shade i) →
      xi*lam*(M : ℝ)/δ ≤ ∑ i, ((marks i).card : ℝ) →
      (∀ z ∈ DensityBroadnessRecovery.cells marks, ∀ v : Space (k+1), ‖v‖=1 →
        (((incident (markedFamily F marks) z).filter
          (fun i => projectiveDistance (F.tube i).direction v < theta)).card : ℝ) ≤
            ((incident (markedFamily F marks) z).card : ℝ)/10) →
      (∀ i x r, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
          B*r^alpha*((F.shade i).card : ℝ)) →
      ∃ J : ℕ, (J : ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
        let eta := (xi/100)/((J : ℝ)+1)
        let L := max 1 (K*(E.card : ℝ)*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/(M : ℝ))
        let O := PrunedIncidence.family F E δ L d J
        O.tube=F.tube ∧ (∀ i, O.shade i ⊆ F.shade i) ∧ O.unionCells ⊆ E ∧
        δ*∑ i, ((F.shade i \ O.shade i).card : ℝ) ≤ (xi/100)*lam*(M : ℝ) ∧
        (∀ x : Space (k+1), ∀ r : ℝ, δ ≤ r → r ≤ 1 →
          ((BallPruning.ballCells O.unionCells δ x r).card : ℝ) ≤
            (BallPruning.coverConstant (k+1) 1*(2:ℝ)^d*L)*(r/δ)^d) ∧
        Nonempty (RecoveredInput F O marks E δ lam xi width R m A B alpha theta) := by
  obtain ⟨K,hK,hprune⟩ := MarkedSpatialPruning.discrete_spatial_pruning_budget hbase hm hp hd width R hw eps heps
  refine ⟨K,hK,?_⟩
  intro M F E marks δ A lam xi B alpha theta hδ hδ1 hA hlam hxi hM hB hE hadm hsep hbounded hcap hcomp hmarks hW hbroad hends
  have hupper (i) : δ*((F.shade i).card : ℝ) ≤ 2*lam := by
    have hh := (mul_le_mul_of_nonneg_left (hcomp i).2 hδ.le)
    have hid : δ*(2*lam/δ)=2*lam := by field_simp
    simpa only [hid] using hh
  obtain ⟨J,hlog,htube,hsub,hOE,hdel,hball⟩ := hprune F E hδ hδ1 hA hlam
    (by positivity : 0 < xi/100) hE hadm hbounded hcap hupper
  refine ⟨J,hlog,?_⟩
  intro eta L O
  exact ⟨htube,hsub,hOE,hdel,hball,recover_pruned F O marks E hδ hlam hxi hM hB
    hcomp hadm hsep hbounded hcap hsub hOE hmarks hW hdel hbroad hends⟩

end
end KakeyaFormal.MarkedPruningAssembly

#print axioms KakeyaFormal.MarkedPruningAssembly.marked_union_mass
#print axioms KakeyaFormal.MarkedPruningAssembly.marked_budget
#print axioms KakeyaFormal.MarkedPruningAssembly.recover_pruned
#print axioms KakeyaFormal.MarkedPruningAssembly.construct
