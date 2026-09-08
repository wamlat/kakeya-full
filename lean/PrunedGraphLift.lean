import PrunedIncidence
import LiftGraph

/-! Actual all-radius spatial pruning and the fixed-pivot graph cap/color
interface. Constants use only fixed dimension, spatial, slope and error bounds. -/
namespace KakeyaFormal.PrunedGraphLift
open Finset Coarsening BallPruning KakeyaFormal.Localization LiftGraph
open scoped BigOperators
noncomputable section
open Classical

def regionRadius (width R : ℝ) : ℝ := max 0 R + 1 + width

def spatialConstant (k : ℕ) (width R d : ℝ) : ℝ :=
  max (coverConstant k 1*(2:ℝ)^d) (coverConstant k (regionRadius width R))

theorem regionRadius_pos {width R : ℝ} (hw : 0 ≤ width) : 0 < regionRadius width R := by
  dsimp [regionRadius]
  have := le_max_left (0:ℝ) R
  linarith

theorem spatialConstant_nonneg (k : ℕ) {width R d : ℝ} (hw : 0 ≤ width) :
    0 ≤ spatialConstant k width R d :=
  (coverConstant_nonneg k (regionRadius_pos hw).le).trans (le_max_right _ _)

/-- The actual admissible cell centers lie in a fixed region determined by the
original tube bases and width. No ambient bounded-grid premise is assumed. -/
theorem union_bounded {k M : ℕ} (F : TubeFamily k M) {δ width R : ℝ}
    (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (hadm : F.Admissible width δ)
    (hbounded : F.Bounded R) :
    ∀ q ∈ F.unionCells, dist (cellCenter δ q) (0 : Space k) ≤ regionRadius width R := by
  intro q hq
  obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
  obtain ⟨t,ht,hqt⟩ := hadm i q hi
  have htub : ‖(F.tube i).axisPoint t‖ ≤ R+1 := by
    have hh := norm_add_le (F.tube i).base (t • (F.tube i).direction)
    rw [norm_smul,Real.norm_eq_abs,(F.tube i).unit_direction,mul_one,abs_of_nonneg ht.1] at hh
    exact hh.trans (by linarith [hbounded i,ht.2])
  have htri := dist_triangle (cellCenter δ q) ((F.tube i).axisPoint t) 0
  simp only [dist_zero_right] at htri ⊢
  have hwidth := mul_le_mul_of_nonneg_left hδ1 hw
  dsimp [regionRadius]
  nlinarith [le_max_right (0:ℝ) R]

/-- Actual unit-scale survivor fibers and the bounded tube region control the
whole survivor union. This supplies the large-radius branch directly. -/
theorem pruned_total_count {k M J : ℕ} (F : TubeFamily k M) (E : Finset (Cell k))
    {δ L d width R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hL : 0 ≤ L) (hadm : F.Admissible width δ) (hbounded : F.Bounded R) :
    (((PrunedIncidence.family F E δ L d J).unionCells).card : ℝ) ≤
      coverConstant k (regionRadius width R)*(L*(1/δ)^d) := by
  let G := PrunedIncidence.family F E δ L d J
  have hGS : G.unionCells ⊆ survivors E δ L d J := by
    intro q hq
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
    exact (mem_inter.mp hi).2
  have hGF : G.unionCells ⊆ F.unionCells := by
    intro q hq
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
    exact F.shade_subset_union i (mem_inter.mp hi).1
  have hfiber (z : Cell k) : ((G.unionCells.filter (fun q => coarseLabel δ 1 q = z)).card : ℝ) ≤ L*(1/δ)^d := by
    have hs := survivors_fiber_bound E (d := d) hδ hL J le_rfl z
    simpa only [radius_top] using
      (show ((G.unionCells.filter (fun q => coarseLabel δ (radius J J) q = z)).card : ℝ) ≤
        (((survivors E δ L d J).filter (fun q => coarseLabel δ (radius J J) q = z)).card : ℝ) by
        exact_mod_cast card_le_card (filter_subset_filter _ hGS)).trans hs
  have hh := ball_count_from_fibers G.unionCells (0 : Space k) (show (0:ℝ) < 1 by norm_num)
    (regionRadius_pos hw).le (show regionRadius width R ≤ regionRadius width R*1 by simp)
    (mul_nonneg hL (Real.rpow_nonneg (by positivity) d)) hfiber
  have hid : ballCells G.unionCells δ 0 (regionRadius width R) = G.unionCells :=
    filter_eq_self.mpr fun q hq => union_bounded F hδ1 hw hadm hbounded q (hGF hq)
  rwa [hid] at hh

/-- Extending the already obtained small-radius estimate uses the actual total
count just proved. The resulting premise covers every radius, as required by the
fixed-pivot graph cap theorem. -/
theorem pruned_all_ball_bound {k M J : ℕ} (F : TubeFamily k M) (E : Finset (Cell k))
    {δ L d width R : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hL : 0 ≤ L) (hd : 0 ≤ d) (hadm : F.Admissible width δ) (hbounded : F.Bounded R)
    (hsmall : ∀ x : Space k, ∀ rho : ℝ, δ ≤ rho → rho ≤ 1 →
      ((ballCells (PrunedIncidence.family F E δ L d J).unionCells δ x rho).card : ℝ) ≤
        (coverConstant k 1*(2:ℝ)^d*L)*(rho/δ)^d) :
    ∀ x : Space k, ∀ rho : ℝ, δ ≤ rho →
      ((ballCells (PrunedIncidence.family F E δ L d J).unionCells δ x rho).card : ℝ) ≤
        (spatialConstant k width R d*L)*(rho/δ)^d := by
  intro x rho hrho
  have hC := spatialConstant_nonneg k (d := d) (R := R) hw
  have hscale : 0 ≤ rho/δ := div_nonneg (hδ.le.trans hrho) hδ.le
  by_cases hr1 : rho ≤ 1
  · exact (hsmall x rho hrho hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hL) (Real.rpow_nonneg hscale d))
  · have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1/δ)
      (div_le_div_of_nonneg_right (le_of_not_ge hr1) hδ.le) hd
    calc
      _ ≤ (((PrunedIncidence.family F E δ L d J).unionCells).card : ℝ) := by
        exact_mod_cast card_le_card (filter_subset _ _)
      _ ≤ coverConstant k (regionRadius width R)*(L*(1/δ)^d) :=
        pruned_total_count F E hδ hδ1 hw hL hadm hbounded
      _ = (coverConstant k (regionRadius width R)*L)*(1/δ)^d := by ring
      _ ≤ (spatialConstant k width R d*L)*(1/δ)^d := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hL) (Real.rpow_nonneg (by positivity) d)
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (mul_nonneg hC hL)


/-- The real graph cap and all-color separation follow from actual legal
fixed-pivot witnesses in the pruned union. No cap or coloring oracle is assumed. -/
theorem pruned_graph_cap_and_colors {k M J N : ℕ} (F : TubeFamily k M)
    (E : Finset (Cell k)) (T : TubeFamily (k+1) N)
    (v : Fin N → Space k) (label : Fin N → Cell k) (pivot : Space k)
    {δ L d width R V C : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width)
    (hL : 0 ≤ L) (hd : 0 ≤ d) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hadm : F.Admissible width δ) (hbounded : F.Bounded R)
    (hsmall : ∀ x : Space k, ∀ rho : ℝ, δ ≤ rho → rho ≤ 1 →
      ((ballCells (PrunedIncidence.family F E δ L d J).unionCells δ x rho).card : ℝ) ≤
        (coverConstant k 1*(2:ℝ)^d*L)*(rho/δ)^d)
    (hinj : Function.Injective label)
    (hlabels : ∀ i, label i ∈ (PrunedIncidence.family F E δ L d J).unionCells)
    (hslope : ∀ i, ‖v i‖ ≤ V)
    (hres : ∀ i, ‖v i-(pivot-cellCenter δ (label i))‖ ≤ C*δ)
    (hdir : ∀ i, (T.tube i).direction = graphDirection (v i)) :
    T.CapBound δ d ((spatialConstant k width R d*L)*(4*(1+V)^2+2*C)^d) ∧
    ∃ Q : ℕ, 0 < Q ∧ (Q : ℝ) ≤ 2*C+2 ∧
      ∃ color : Fin N → (Fin k → ZMod Q),
        ∀ i j, i ≠ j → color i = color j →
          δ/(2*(1+V)^2) ≤ projectiveDistance (T.tube i).direction (T.tube j).direction := by
  have hall := pruned_all_ball_bound F E hδ hδ1 hw hL hd hadm hbounded hsmall
  have hcap := lifted_family_cap_bound T v label pivot (PrunedIncidence.family F E δ L d J).unionCells
    hinj hlabels hδ hV hC (mul_nonneg (spatialConstant_nonneg k hw) hL) hslope hres hdir hall
  refine ⟨hcap,?_⟩
  obtain ⟨Q,hQ,hQupper,color,hcolor⟩ := fixed_pivot_coloring v label pivot hinj hδ hV hC hslope hres
  exact ⟨Q,hQ,hQupper,color,fun i j hij hc => by simpa only [hdir] using hcolor i j hij hc⟩

/-- Every residue color is retained. Its original line count is an exact fiber
count, so the sum of the color-family sizes is the full original line count. -/
theorem color_partition_card {N k Q : ℕ} (hQ : 0 < Q)
    (color : Fin N → (Fin k → ZMod Q)) :
    let _ : NeZero Q := ⟨hQ.ne'⟩
    (∑ c : Fin k → ZMod Q, ((univ : Finset (Fin N)).filter (fun i => color i = c)).card) = N := by
  let _ : NeZero Q := ⟨hQ.ne'⟩
  simpa using sum_card_fiberwise_eq_card_filter (univ : Finset (Fin N))
    (univ : Finset (Fin k → ZMod Q)) color

/-- Number of available colors depends only on fixed dimension and the pivot
error bound, with no loss of any color or line. -/
theorem color_count_bound {k Q : ℕ} {C : ℝ} (hQ : 0 < Q) (hQC : (Q : ℝ) ≤ 2*C+2) :
    let _ : NeZero Q := ⟨hQ.ne'⟩
    (Fintype.card (Fin k → ZMod Q) : ℝ) ≤ (2*C+2)^k := by
  let _ : NeZero Q := ⟨hQ.ne'⟩
  simpa using pow_le_pow_left₀ (Nat.cast_nonneg Q) hQC k

/-- Full pruning-to-pivot package. The base-estimate constant precedes every
configuration. The actual retained incidence lower bound remains in the output,
while arbitrary legal graph witnesses obtain the true lifted cap and all colors. -/
theorem discrete_pruned_graph_lift {k : ℕ} {m d p : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hm : 0 ≤ m) (hp : 1 ≤ p) (hd : 0 ≤ d)
    (width R : ℝ) (hw : 0 ≤ width) (eps : ℝ) (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ {M : ℕ} (F : TubeFamily (k+1) M) {δ A lam : ℝ},
      0 < δ → δ ≤ 1 → 1 ≤ A → 0 < lam →
      F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, lam ≤ δ*((F.shade i).card : ℝ)) →
      (∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam) →
      ∃ J : ℕ, (J : ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
        let eta := 1/(2*((J : ℝ)+1))
        let L := max 1 (K*(F.unionCells.card : ℝ)*A*δ^(d-m-eps)*eta^(-(p+1))*lam^(-p)/(M : ℝ))
        let G := PrunedIncidence.family F F.unionCells δ L d J
        G.tube = F.tube ∧ (∀ i, G.shade i ⊆ F.shade i) ∧ G.unionCells ⊆ F.unionCells ∧
        lam*(M : ℝ)/2 ≤ δ*∑ i, ((G.shade i).card : ℝ) ∧
        (∀ x : Space (k+1), ∀ rho : ℝ, δ ≤ rho →
          ((ballCells G.unionCells δ x rho).card : ℝ) ≤
            (spatialConstant (k+1) width R d*L)*(rho/δ)^d) ∧
        ∀ {N : ℕ} (T : TubeFamily (k+2) N) (v : Fin N → Space (k+1))
          (label : Fin N → Cell (k+1)) (pivot : Space (k+1)) {V C : ℝ},
          0 ≤ V → 0 ≤ C → Function.Injective label → (∀ i, label i ∈ G.unionCells) →
          (∀ i, ‖v i‖ ≤ V) →
          (∀ i, ‖v i-(pivot-cellCenter δ (label i))‖ ≤ C*δ) →
          (∀ i, (T.tube i).direction = graphDirection (v i)) →
          T.CapBound δ d ((spatialConstant (k+1) width R d*L)*(4*(1+V)^2+2*C)^d) ∧
          ∃ Q : ℕ, 0 < Q ∧ (Q : ℝ) ≤ 2*C+2 ∧
            ∃ color : Fin N → (Fin (k+1) → ZMod Q),
              ∀ i j, i ≠ j → color i = color j →
                δ/(2*(1+V)^2) ≤ projectiveDistance (T.tube i).direction (T.tube j).direction := by
  obtain ⟨K,hK,hprune⟩ := PrunedIncidence.discrete_spatial_pruning hbase hm hp hd width R hw eps heps
  refine ⟨K,hK,?_⟩
  intro M F δ A lam hδ hδ1 hA hlam hadm hbounded hcap hlower hupper
  obtain ⟨J,hlog,htubes,hshade,hunion,hmass,hsmall⟩ :=
    hprune F F.unionCells hδ hδ1 hA hlam F.shade_subset_union hadm hbounded hcap hlower hupper
  refine ⟨J,hlog,?_⟩
  intro eta L G
  have hL : 0 ≤ L := (show (0:ℝ) ≤ 1 by norm_num).trans (le_max_left _ _)
  refine ⟨htubes,hshade,hunion,hmass,pruned_all_ball_bound F F.unionCells hδ hδ1 hw hL hd hadm hbounded hsmall,?_⟩
  intro N T v label pivot V C hV hC hinj hlabels hslope hres hdir
  exact pruned_graph_cap_and_colors F F.unionCells T v label pivot hδ hδ1 hw hL hd hV hC
    hadm hbounded hsmall hinj hlabels hslope hres hdir



def colorIndex {N : ℕ} {Γ : Type*} (color : Fin N → Γ) (c : Γ) :
    Fin ((univ : Finset (Fin N)).filter (fun i => color i = c)).card → Fin N :=
  fun i => (((univ : Finset (Fin N)).filter (fun j => color j = c)).equivFin.symm i).val

def colorFamily {k N : ℕ} (T : TubeFamily k N) {Γ : Type*} (color : Fin N → Γ) (c : Γ) :
    TubeFamily k ((univ : Finset (Fin N)).filter (fun i => color i = c)).card :=
  ⟨fun i => T.tube (colorIndex color c i),fun i => T.shade (colorIndex color c i)⟩

/-- All individual color families are genuine injective restrictions, so the
proved within-color separation and cap bound apply directly to their actual
tubes and unchanged finite shadings. -/
theorem color_family_geometry {k N : ℕ} (T : TubeFamily k N) {Γ : Type*}
    (color : Fin N → Γ) {sep δ d A : ℝ}
    (hsep : ∀ i j, i ≠ j → color i = color j →
      sep ≤ projectiveDistance (T.tube i).direction (T.tube j).direction)
    (hcap : T.CapBound δ d A) :
    ∀ c : Γ, (colorFamily T color c).Separated sep ∧ (colorFamily T color c).CapBound δ d A := by
  intro c
  have he : Function.Injective (colorIndex color c) :=
    Subtype.val_injective.comp ((univ.filter (fun i => color i = c)).equivFin.symm.injective)
  have hcolor (i) : color (colorIndex color c i) = c :=
    (mem_filter.mp (((univ : Finset (Fin N)).filter (fun j => color j = c)).equivFin.symm i).property).2
  have hsep0 : T.Separated 0 := fun i j _ => projectiveDistance_nonneg _ _
  have hbound : T.Bounded (∑ i, ‖(T.tube i).base‖) := fun i =>
    single_le_sum (f := fun j => ‖(T.tube j).base‖) (fun j _ => norm_nonneg _) (mem_univ i)
  obtain ⟨_,_,hc⟩ := DiscreteMeasurable.injective_tube_restriction T (colorFamily T color c)
    (colorIndex color c) he (fun _ => rfl) hsep0 hbound hcap
  refine ⟨?_,hc⟩
  intro i j hij
  exact hsep _ _ (fun hh => hij (he hh)) ((hcolor i).trans (hcolor j).symm)

/-- No shading incidence is lost or duplicated by retaining every color. -/
theorem color_family_incidence {k N : ℕ} (T : TubeFamily k N) {Γ : Type*} [Fintype Γ]
    (color : Fin N → Γ) :
    (∑ c : Γ, ∑ i, (((colorFamily T color c).shade i).card : ℝ)) =
      ∑ i, ((T.shade i).card : ℝ) := by
  have hfiber (c : Γ) : (∑ i, (((colorFamily T color c).shade i).card : ℝ)) =
      ∑ i ∈ (univ : Finset (Fin N)).filter (fun j => color j = c), ((T.shade i).card : ℝ) := by
    let S := (univ : Finset (Fin N)).filter (fun j => color j = c)
    have hh := S.equivFin.symm.sum_comp (fun i : {i // i ∈ S} => ((T.shade i.val).card : ℝ))
    exact hh.trans (Finset.sum_subtype S (fun _ => Iff.rfl) (fun i => ((T.shade i).card : ℝ))).symm
  simp_rw [hfiber]
  exact sum_fiberwise (univ : Finset (Fin N)) color (fun i => ((T.shade i).card : ℝ))

/-- The derived cap coefficient also satisfies the normalized input requirement
A≥1 whenever the actual pruning cutoff is at least one. -/
theorem lifted_cap_coefficient_ge_one {k : ℕ} {width R d L V C : ℝ}
    (hd : 0 ≤ d) (hL : 1 ≤ L) (hV : 0 ≤ V) (hC : 0 ≤ C) :
    1 ≤ (spatialConstant k width R d*L)*(4*(1+V)^2+2*C)^d := by
  have hcover : 1 ≤ coverConstant k 1 := by
    have h1 := one_le_pow₀ (n := k) (show (1:ℝ) ≤ 5 by norm_num)
    have h2 := one_le_pow₀ (n := k) (show (1:ℝ) ≤ 1+1+(k:ℝ)/2 by have hk := Nat.cast_nonneg (α := ℝ) k; linarith)
    dsimp [coverConstant]
    nlinarith
  have hpow := Real.one_le_rpow (show (1:ℝ) ≤ 2 by norm_num) hd
  have hsp : 1 ≤ spatialConstant k width R d :=
    (show 1 ≤ coverConstant k 1*(2:ℝ)^d by nlinarith).trans (le_max_left _ _)
  have hchart : 1 ≤ 4*(1+V)^2+2*C := by nlinarith [sq_nonneg V]
  have hchartpow := Real.one_le_rpow hchart hd
  have hspL : 1 ≤ spatialConstant k width R d*L := by nlinarith
  nlinarith

end
end KakeyaFormal.PrunedGraphLift

#print axioms KakeyaFormal.PrunedGraphLift.pruned_all_ball_bound
#print axioms KakeyaFormal.PrunedGraphLift.pruned_graph_cap_and_colors
#print axioms KakeyaFormal.PrunedGraphLift.discrete_pruned_graph_lift
#print axioms KakeyaFormal.PrunedGraphLift.color_family_geometry
#print axioms KakeyaFormal.PrunedGraphLift.color_family_incidence

#print axioms KakeyaFormal.PrunedGraphLift.lifted_cap_coefficient_ge_one
