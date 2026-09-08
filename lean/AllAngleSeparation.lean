import AllAnglePivot
import SeparationColoring

/-! Fixed separation normalization for the actual all-angle pivot. A largest
class in the proved finite coloring retains at least a fixed fraction of the
original tubes, with their complete shadings unchanged. -/
namespace KakeyaFormal.AllAngleSeparation
open Finset SeparationColoring
noncomputable section
open Classical

/-- A largest actual color class retains at least the reciprocal-palette
fraction of the original population. No population bound is assumed. -/
theorem exists_large_color {M n : ℕ} (hn : 0 < n) (color : Fin M → Fin n) :
    ∃ c : Fin n, (M:ℝ) ≤ (n:ℝ)*((colorClass color c).card:ℝ) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,mem_univ _⟩
  obtain ⟨c,_,hmax⟩ := Finset.exists_max_image Finset.univ
    (fun c => ((colorClass color c).card:ℝ)) hne
  have hsum := color_weight_sum color (fun _ => (1:ℝ))
  simp only [sum_const,nsmul_eq_mul,mul_one,card_univ,Fintype.card_fin] at hsum
  have hle := Finset.sum_le_sum (fun i (hi : i ∈ (Finset.univ : Finset (Fin n))) => hmax i hi)
  simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin] at hle
  exact ⟨c,hsum.symm.trans_le hle⟩

/-- Each actual class union is contained in the unchanged original cell union. -/
theorem class_union_subset {k M n : ℕ} (F : TubeFamily k M)
    (color : Fin M → Fin n) (c : Fin n) :
    (classFamily F color c).unionCells ⊆ F.unionCells := by
  intro z hz
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hz
  exact Finset.mem_biUnion.mpr ⟨classIndex color c i,mem_univ _,hi⟩

/-- Arbitrary FIXED positive separation is allowed. The computed palette and
positive coefficient precede every original configuration; full shadings and
their two-ends inequalities are inherited literally by the selected class. -/
theorem all_scales {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 1 ≤ pExp) (hd : 0 ≤ d) (hq : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m)
    (width R sigma B alpha eps : ℝ) (hsigma : 0 < sigma)
    (hB : 1 ≤ B) (halpha : 0 < alpha) (heps : 0 < eps)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+
      (KakeyaScalar.pivotDensity pExp qExp-2)/3) :
    ∃ c : ℝ, 0 < c ∧ ∀ {M : ℕ} (F : TubeFamily (k+2) M) {δ lam A : ℝ},
      0 < δ → δ ≤ 1 → 0 < lam → lam ≤ 1 → 1 ≤ A →
      F.Admissible width δ → F.Separated (sigma*δ) → F.Bounded R → F.CapBound δ m A →
      F.Comparable δ lam →
      (∀ i x r, δ ≤ r → r ≤ 1 →
        (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          B*r^alpha*((F.shade i).card:ℝ)) →
      c*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp)*(M:ℝ) ≤ (F.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hmain⟩ := AllAnglePivot.all_scales hbase hlift hm hmn hp hd hq hD
    width R B alpha eps hB halpha heps hmargin
  let palette := paletteSize (k+1) sigma
  have hpalette : 0 < palette := paletteSize_pos _ _
  have hpR : (0:ℝ) < palette := by exact_mod_cast hpalette
  refine ⟨c/palette,div_pos hc hpR,?_⟩
  intro M F δ lam A hδ hδ1 hlam hlam1 hA hadm hsep hbounded hcap hcomp hends
  obtain ⟨color,hcolor⟩ := full_separation_coloring F hδ hsigma hsep
  obtain ⟨chosen,hcount⟩ := exists_large_color hpalette color
  let G := classFamily F color chosen
  have hGadm : G.Admissible width δ := classFamily_admissible F color hadm chosen
  have hGsep : G.Separated δ := classFamily_separated F color hcolor chosen
  have hGbounded : G.Bounded R := fun i => hbounded (classIndex color chosen i)
  have hGcap : G.CapBound δ m A := classFamily_cap_bound F color hcap chosen
  have hGcomp : G.Comparable δ lam := fun i => hcomp (classIndex color chosen i)
  have hGends : ∀ i x r, δ ≤ r → r ≤ 1 →
      (((G.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*r^alpha*((G.shade i).card:ℝ) :=
    fun i => hends (classIndex color chosen i)
  have hbound := hmain G hδ hδ1 hlam hlam1 hA hGadm hGsep hGbounded hGcap hGcomp hGends
  have hfactor : 0 ≤ (c/palette)*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
      lam^(KakeyaScalar.pivotDensity pExp qExp) := by positivity
  have hpop := mul_le_mul_of_nonneg_left hcount hfactor
  have hcard : (G.unionCells.card:ℝ) ≤ (F.unionCells.card:ℝ) := by
    exact_mod_cast Finset.card_le_card (class_union_subset F color chosen)
  apply le_trans ?_ (hbound.trans hcard)
  calc
    _ ≤ ((c/palette)*A⁻¹*δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        lam^(KakeyaScalar.pivotDensity pExp qExp))*
        ((palette:ℝ)*((colorClass color chosen).card:ℝ)) := hpop
    _ = _ := by field_simp

/-- Configuration-facing form for every fixed normalization. Original full
two ends and the analytic base/lift remain the only additional hypotheses. -/
theorem configuration_estimate {k : ℕ} {m d d' pExp qExp : ℝ}
    (hbase : DiscreteEstimate (k+2) m d pExp)
    (hlift : DiscreteEstimate (k+3) d d' qExp)
    (hm : 1 ≤ m) (hmn : m+1 ≤ (k:ℝ)+2)
    (hp : 1 ≤ pExp) (hd : 0 ≤ d) (hq : 2 ≤ qExp)
    (hD : KakeyaScalar.pivotSet m d' < m)
    (geom : Normalization) (B alpha eps : ℝ)
    (hB : 1 ≤ B) (halpha : 0 < alpha) (heps : 0 < eps)
    (hmargin : 0 < (m+3)/2-KakeyaScalar.pivotSet m d'+
      (KakeyaScalar.pivotDensity pExp qExp-2)/3) :
    ∃ c : ℝ, 0 < c ∧ ∀ F : ShadedConfiguration (k+2) geom m,
      (∀ i x r, F.δ ≤ r → r ≤ 1 →
        (((F.family.shade i).filter (fun z => dist (cellCenter F.δ z) x ≤ r)).card:ℝ) ≤
          B*r^alpha*((F.family.shade i).card:ℝ)) →
      c*F.A⁻¹*F.δ^(m-KakeyaScalar.pivotSet m d'+eps)*
        F.lam^(KakeyaScalar.pivotDensity pExp qExp)*F.M ≤ (F.family.unionCells.card:ℝ) := by
  obtain ⟨c,hc,hmain⟩ := all_scales hbase hlift hm hmn hp hd hq hD
    geom.width geom.radius geom.separation B alpha eps geom.separation_pos hB halpha heps hmargin
  exact ⟨c,hc,fun F hends => hmain F.family F.scale_pos F.scale_le_one F.density_pos
    F.density_le_one F.cap_ge_one F.admissible F.separated F.bounded F.cap_bound F.comparable hends⟩

end
end KakeyaFormal.AllAngleSeparation
