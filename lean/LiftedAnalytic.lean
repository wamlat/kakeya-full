import PrunedGraphLift
import LiftSegments

/-! The lifted discrete estimate applied to actual graph shadings after unit
segment normalization and an all-color partition. All finite losses are explicit. -/
namespace KakeyaFormal.LiftedAnalytic
open Finset PrunedGraphLift LiftGraph LiftSegments
open scoped BigOperators
noncomputable section
open Classical

/-- The fixed geometry chosen before any lifted scale or incidence data. -/
def graphNormalization (V R width b : ℝ) : Normalization where
  width := max 1 (width+b*(1+V))
  separation := 1/(2*(1+max 0 V)^2)
  radius := max 1 (R+V+2)
  width_pos := zero_lt_one.trans_le (le_max_left _ _)
  separation_pos := by positivity
  radius_pos := zero_lt_one.trans_le (le_max_left _ _)

def colorSize {N : ℕ} {Γ : Type*} (color : Fin N → Γ) (g : Γ) : ℕ :=
  ((univ : Finset (Fin N)).filter (fun i => color i = g)).card

def colorDensity {k N : ℕ} (T : TubeFamily k N) {Γ : Type*} (color : Fin N → Γ)
    (δ : ℝ) (g : Γ) : ℝ :=
  δ*(∑ i, (((colorFamily T color g).shade i).card : ℝ))/colorSize color g

/-- Exact density times original color-family size, including empty colors. -/
theorem color_density_mass {k N : ℕ} (T : TubeFamily k N) {Γ : Type*}
    (color : Fin N → Γ) (δ : ℝ) (g : Γ) :
    (colorSize color g : ℝ)*colorDensity T color δ g =
      δ*(∑ i, (((colorFamily T color g).shade i).card : ℝ)) := by
  by_cases hz : colorSize color g = 0
  · have hh : (∑ i, (((colorFamily T color g).shade i).card : ℝ)) = 0 := by
      apply sum_eq_zero
      intro i _
      have hi := i.isLt
      change i.val < colorSize color g at hi
      omega
    simp only [colorDensity,hz,Nat.cast_zero,mul_zero,div_zero,hh]
  · dsimp [colorDensity]
    field_simp

/-- The normalized cumulative estimate is applied to each actual color family;
Jensen then combines all colors with only their explicit finite count loss. -/
theorem colored_cumulative_bound {k N : ℕ} (T : TubeFamily k N) {Γ : Type*} [Fintype Γ]
    (color : Fin N → Γ) (U : Finset (Cell k))
    {geom : Normalization} {m d p eps c δ s A : ℝ}
    (hc : 0 < c) (hp : 1 ≤ p) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) (hA : 1 ≤ A)
    (hestimate : ∀ H : CumulativeConfiguration k geom m,
      c*H.A⁻¹*H.δ^(m-d+eps)*H.s^p*H.M ≤ (H.family.unionCells.card : ℝ))
    (hadm : T.Admissible geom.width δ) (hbounded : T.Bounded geom.radius)
    (hcap : T.CapBound δ m A)
    (hsep : ∀ i j, i ≠ j → color i = color j →
      geom.separation*δ ≤ projectiveDistance (T.tube i).direction (T.tube j).direction)
    (hmass : s*(N : ℝ) ≤ δ*∑ i, ((T.shade i).card : ℝ)) (hU : T.unionCells ⊆ U) :
    c*A⁻¹*δ^(m-d+eps)*s^p*N ≤ (Fintype.card Γ : ℝ)*(U.card : ℝ) := by
  by_cases hN : N = 0
  · simp only [hN,Nat.cast_zero,mul_zero]
    positivity
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hw (g : Γ) (_ : g ∈ (univ : Finset Γ)) : 0 ≤ (colorSize color g : ℝ) := Nat.cast_nonneg _
  have hx (g : Γ) (_ : g ∈ (univ : Finset Γ)) : 0 ≤ colorDensity T color δ g := by
    dsimp [colorDensity]
    positivity
  have hsum : (∑ g : Γ, (colorSize color g : ℝ)) = N := by
    have hh := sum_card_fiberwise_eq_card_filter (univ : Finset (Fin N)) (univ : Finset Γ) color
    exact_mod_cast (show (∑ g : Γ, colorSize color g) = N by simpa [colorSize] using hh)
  have htotal : (∑ g : Γ, (colorSize color g : ℝ)*colorDensity T color δ g) =
      δ*∑ i, ((T.shade i).card : ℝ) := by
    simp_rw [color_density_mass]
    rw [← mul_sum,color_family_incidence]
  have hbound (g : Γ) (_ : g ∈ (univ : Finset Γ)) :
      (c*A⁻¹*δ^(m-d+eps))*((colorSize color g : ℝ)*(colorDensity T color δ g)^p) ≤ (U.card : ℝ) := by
    have hGadm : (colorFamily T color g).Admissible geom.width δ := fun i q hq => hadm _ q hq
    have hGbound : (colorFamily T color g).Bounded geom.radius := fun i => hbounded _
    obtain ⟨hGs,hGc⟩ := color_family_geometry T color hsep hcap g
    let H : CumulativeConfiguration k geom m := {
      M := colorSize color g
      δ := δ
      s := colorDensity T color δ g
      A := A
      family := colorFamily T color g
      scale_pos := hδ
      scale_le_one := hδ1
      density_nonneg := hx g (mem_univ _)
      cap_ge_one := hA
      admissible := hGadm
      separated := hGs
      bounded := hGbound
      cap_bound := hGc
      cumulative := by rw [mul_comm,color_density_mass]; rfl
    }
    have hh := hestimate H
    have hGU : (colorFamily T color g).unionCells ⊆ U := by
      intro q hq
      obtain ⟨i,_,hi⟩ := mem_biUnion.mp hq
      exact hU (T.shade_subset_union _ hi)
    have hcard : ((colorFamily T color g).unionCells.card : ℝ) ≤ U.card := by exact_mod_cast card_le_card hGU
    change c*A⁻¹*δ^(m-d+eps)*(colorDensity T color δ g)^p*(colorSize color g : ℝ) ≤ _ at hh
    convert hh.trans hcard using 1 <;> first | rfl | ring
  have ha : 0 ≤ c*A⁻¹*δ^(m-d+eps) := by
    have : 0 < A := by linarith
    positivity
  have hh := KakeyaFinite.cumulative_from_bins (univ : Finset Γ)
    (fun g => (colorSize color g : ℝ)) (colorDensity T color δ) hNpos hs hp ha hw hx hsum
    (by rwa [htotal]) hbound
  simpa only [card_univ,mul_assoc,mul_comm,mul_left_comm] using hh

/-- Segment normalization loses at most the stated fixed number of unit pieces
in the actual cumulative incidence mass. -/
theorem segment_mass {k N : ℕ} (S : Fin N → Finset (Cell k)) (T : TubeFamily k N)
    {δ s J : ℝ} (hδ : 0 ≤ δ) (hJ : 0 < J)
    (hmass : s*(N : ℝ) ≤ δ*∑ i, ((S i).card : ℝ))
    (hcount : ∀ i, ((S i).card : ℝ)/J ≤ ((T.shade i).card : ℝ)) :
    (s/J)*(N : ℝ) ≤ δ*∑ i, ((T.shade i).card : ℝ) := by
  have hh := sum_le_sum (s := univ) (fun i _ => hcount i)
  rw [← sum_div] at hh
  have h1 := div_le_div_of_nonneg_right hmass hJ.le
  have h2 := mul_le_mul_of_nonneg_left hh hδ
  calc
    _ = (s*(N : ℝ))/J := by ring
    _ ≤ (δ*∑ i, ((S i).card : ℝ))/J := h1
    _ = δ*((∑ i, ((S i).card : ℝ))/J) := by ring
    _ ≤ _ := h2



def unitPieces (V : ℝ) : ℝ := (Nat.ceil (1+V)+1 : ℕ)

theorem unitPieces_pos (V : ℝ) : 0 < unitPieces V := by dsimp [unitPieces]; positivity

/-- Complete actual pruned lift application. The two analytic constants are
chosen before the original family, both tube counts, scale, densities and cap
coefficient. Every lifted unit family, color, cumulative input, and support bound
is constructed from the displayed graph witnesses. -/
theorem discrete_pruned_lifted_union {k : ℕ} {m d p D q : ℝ}
    (hbase : DiscreteEstimate (k+1) m d p) (hlift : DiscreteEstimate (k+2) d D q)
    (hm : 0 ≤ m) (hd : 0 ≤ d) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (width R V C Rlift widthLift b epsBase epsLift : ℝ)
    (hw : 0 ≤ width) (hV : 0 ≤ V) (hC : 0 ≤ C) (hb : 0 ≤ b)
    (hepsBase : 0 < epsBase) (hepsLift : 0 < epsLift) :
    ∃ Kbase cLift : ℝ, 0 < Kbase ∧ 0 < cLift ∧
      ∀ {M : ℕ} (F : TubeFamily (k+1) M) {δ A lam : ℝ},
      0 < δ → δ ≤ 1 → 1 ≤ A → 0 < lam →
      F.Admissible width δ → F.Bounded R → F.CapBound δ m A →
      (∀ i, lam ≤ δ*((F.shade i).card : ℝ)) →
      (∀ i, δ*((F.shade i).card : ℝ) ≤ 2*lam) →
      ∃ J : ℕ, (J : ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
        let eta := 1/(2*((J : ℝ)+1))
        let L := max 1 (Kbase*(F.unionCells.card : ℝ)*A*δ^(d-m-epsBase)*eta^(-(p+1))*lam^(-p)/(M : ℝ))
        let G := PrunedIncidence.family F F.unionCells δ L d J
        lam*(M : ℝ)/2 ≤ δ*∑ i, ((G.shade i).card : ℝ) ∧
        ∀ {N : ℕ} (a v : Fin N → Space (k+1)) (label : Fin N → Cell (k+1))
          (pivot : Space (k+1)) (S : Fin N → Finset (Cell (k+2))) {s : ℝ},
          0 ≤ s → Function.Injective label → (∀ i, label i ∈ G.unionCells) →
          (∀ i, ‖a i‖ ≤ Rlift) → (∀ i, ‖v i‖ ≤ V) →
          (∀ i, ‖v i-(pivot-cellCenter δ (label i))‖ ≤ C*δ) →
          (∀ i z, z ∈ S i → ∃ t ∈ Set.Icc (-(b*δ)) (1+b*δ),
            dist (cellCenter δ z) (graphPoint (a i) (v i) t) ≤ widthLift*δ) →
          s*(N : ℝ) ≤ δ*∑ i, ((S i).card : ℝ) →
          let Alift := (spatialConstant (k+1) width R d*L)*(4*(1+V)^2+2*C)^d
          cLift*Alift⁻¹*δ^(d-D+epsLift)*(s/unitPieces V)^q*N/((2*C+2)^(k+1)) ≤
            ((univ.biUnion S).card : ℝ) := by
  let geom := graphNormalization V Rlift widthLift b
  obtain ⟨cLift,hcLift,hestimate⟩ := hlift.to_cumulative hq geom epsLift hepsLift
  obtain ⟨Kbase,hKbase,hpruned⟩ := discrete_pruned_graph_lift hbase hm hp hd width R hw epsBase hepsBase
  refine ⟨Kbase,cLift,hKbase,hcLift,?_⟩
  intro M F δ A lam hδ hδ1 hA hlam hadm hbounded hcap hlower hupper
  obtain ⟨J,hlog,_,_,_,hmassG,_,hgraphs⟩ := hpruned F hδ hδ1 hA hlam hadm hbounded hcap hlower hupper
  refine ⟨J,hlog,?_⟩
  intro eta L G
  refine ⟨hmassG,?_⟩
  intro N a v label pivot S s hs hinj hlabels habase hslope hres hpoint hmass Alift
  obtain ⟨T,hdir,hsub,hcount,hTadm,hTbounded,hTU⟩ :=
    normalize_graph_family a v S hδ hV hb habase hslope hpoint
  obtain ⟨hTcap,Q,hQ,hQupper,color,hcolor⟩ := hgraphs T v label pivot hV hC hinj hlabels hslope hres hdir
  have hAlift : 1 ≤ Alift := lifted_cap_coefficient_ge_one hd (le_max_left _ _) hV hC
  have hmassT : (s/unitPieces V)*(N : ℝ) ≤ δ*∑ i, ((T.shade i).card : ℝ) :=
    segment_mass S T hδ.le (unitPieces_pos V) hmass hcount
  have hTadm' : T.Admissible geom.width δ := by
    intro i z hz
    obtain ⟨t,ht,hzt⟩ := hTadm i z hz
    exact ⟨t,ht,hzt.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le)⟩
  have hTbound' : T.Bounded geom.radius := fun i => (hTbounded i).trans (le_max_right _ _)
  have hTsep' : ∀ i j, i ≠ j → color i = color j →
      geom.separation*δ ≤ projectiveDistance (T.tube i).direction (T.tube j).direction := by
    intro i j hij hc
    have hh := hcolor i j hij hc
    convert hh using 1
    dsimp [geom,graphNormalization]
    rw [max_eq_right hV]
    ring
  let _ : NeZero Q := ⟨hQ.ne'⟩
  have hh := colored_cumulative_bound T color (univ.biUnion S) hcLift hq hδ hδ1
    (div_nonneg hs (unitPieces_pos V).le) hAlift hestimate hTadm' hTbound' hTcap hTsep' hmassT hTU
  have hcolors : (Fintype.card (Fin (k+1) → ZMod Q) : ℝ) ≤ (2*C+2)^(k+1) :=
    color_count_bound hQ hQupper
  have hfinal := hh.trans (mul_le_mul_of_nonneg_right hcolors (Nat.cast_nonneg _))
  exact (div_le_iff₀ (by positivity : 0 < (2*C+2)^(k+1))).mpr (by
    simpa only [mul_comm] using hfinal)

end
end KakeyaFormal.LiftedAnalytic

#print axioms KakeyaFormal.LiftedAnalytic.color_density_mass
#print axioms KakeyaFormal.LiftedAnalytic.colored_cumulative_bound
#print axioms KakeyaFormal.LiftedAnalytic.segment_mass
#print axioms KakeyaFormal.LiftedAnalytic.discrete_pruned_lifted_union
