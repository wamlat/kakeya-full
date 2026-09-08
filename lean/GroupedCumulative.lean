import CumulativeEstimate
import GroupedIncidence

/-! Actual restricted tube families and lossless convexity across geometric
groups. The analytic input is the normalized DiscreteEstimate, not an assumed
support lower bound for every incidence restriction. -/
namespace KakeyaFormal.GroupedCumulative
universe u v w
open Finset
open scoped BigOperators
noncomputable section
open Classical

variable {G : Type*} [Fintype G] {k : ℕ} (M : G → ℕ)
abbrev Index := (g : G) × Fin (M g)
abbrev Record := Index M × Cell k

def shade (T : Finset (Record (k := k) M)) (g : G) (i : Fin (M g)) : Finset (Cell k) :=
  (T.filter (fun r => r.1 = ⟨g,i⟩)).image Prod.snd

omit [Fintype G] in
theorem mem_shade (T : Finset (Record (k := k) M)) (g : G) (i : Fin (M g)) (z : Cell k) :
    z ∈ shade M T g i ↔ (⟨g,i⟩,z) ∈ T := by
  constructor
  · intro hz
    obtain ⟨r,hr,hrz⟩ := mem_image.mp hz
    have ht := (mem_filter.mp hr).1
    have he := (mem_filter.mp hr).2
    have hrid : r = (⟨g,i⟩,z) := Prod.ext he hrz
    simpa only [hrid] using ht
  · intro hz
    exact mem_image.mpr ⟨(⟨g,i⟩,z),mem_filter.mpr ⟨hz,rfl⟩,rfl⟩

def family (F : ∀ g, TubeFamily k (M g)) (T : Finset (Record (k := k) M))
    (g : G) : TubeFamily k (M g) := ⟨(F g).tube,shade M T g⟩

omit [Fintype G] in
theorem shade_card (T : Finset (Record (k := k) M)) (g : G) (i : Fin (M g)) :
    (shade M T g i).card = (T.filter (fun r => r.1 = ⟨g,i⟩)).card := by
  apply card_image_iff.mpr
  intro a ha b hb he
  exact Prod.ext ((mem_filter.mp ha).2.trans (mem_filter.mp hb).2.symm) he

/-- Every original record is counted exactly once, including zero-size groups. -/
theorem total_incidence (T : Finset (Record (k := k) M)) :
    ∑ g, ∑ i, (shade M T g i).card = T.card := by
  simp_rw [shade_card]
  calc
    _ = ∑ j : Index M, (T.filter (fun r => r.1 = j)).card := (Fintype.sum_sigma _).symm
    _ = T.card := by simpa using sum_card_fiberwise_eq_card_filter T (univ : Finset (Index M)) Prod.fst

def support (r : Record (k := k) M) : G × Cell k := (r.1.1,r.2)

omit [Fintype G] in
theorem union_mem (F : ∀ g, TubeFamily k (M g)) (T : Finset (Record (k := k) M))
    (g : G) (z : Cell k) : z ∈ (family M F T g).unionCells ↔
      (g,z) ∈ T.image (support M) := by
  constructor
  · intro hz
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hz
    exact mem_image.mpr ⟨(⟨g,i⟩,z),(mem_shade M T g i z).mp hi,rfl⟩
  · intro hz
    obtain ⟨⟨⟨h,i⟩,q⟩,hr,he⟩ := mem_image.mp hz
    have hg : h = g := congrArg Prod.fst he
    have hq : q = z := congrArg Prod.snd he
    subst h; subst q
    exact mem_biUnion.mpr ⟨i,mem_univ _,(mem_shade M T g i z).mpr hr⟩

/-- Group support cardinalities sum exactly, rather than costing the number of
groups or discarding empty groups. -/
theorem total_support (F : ∀ g, TubeFamily k (M g)) (T : Finset (Record (k := k) M)) :
    ∑ g, (family M F T g).unionCells.card = (T.image (support M)).card := by
  let U := T.image (support M)
  have hfiber (g : G) : (U.filter (fun x => x.1 = g)).card = (family M F T g).unionCells.card := by
    have hid : U.filter (fun x => x.1 = g) = (family M F T g).unionCells.image (fun z => (g,z)) := by
      ext x
      constructor
      · intro hx
        have h := mem_filter.mp hx
        have he : (g,x.2) = x := Prod.ext h.2.symm rfl
        exact mem_image.mpr ⟨x.2,(union_mem M F T g x.2).mpr (by rw [he]; exact h.1),he⟩
      · intro hx
        obtain ⟨z,hz,rfl⟩ := mem_image.mp hx
        exact mem_filter.mpr ⟨(union_mem M F T g z).mp hz,rfl⟩
    rw [hid,card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
  simp_rw [← hfiber]
  simpa using sum_card_fiberwise_eq_card_filter U (univ : Finset G) Prod.fst

omit [Fintype G] in
/-- Actual subsets of the original incidence set inherit the group's geometric
hypotheses, with no comparable-density requirement. -/
theorem family_geometry (F : ∀ g, TubeFamily k (M g))
    (S T : Finset (Record (k := k) M)) (hTS : T ⊆ S) (geom : Normalization)
    {δ m A : ℝ}
    (hshade : ∀ r ∈ S, r.2 ∈ (F r.1.1).shade r.1.2)
    (hadm : ∀ g, (F g).Admissible geom.width δ)
    (hsep : ∀ g, (F g).Separated (geom.separation*δ))
    (hbounded : ∀ g, (F g).Bounded geom.radius)
    (hcap : ∀ g, (F g).CapBound δ m A) (g : G) :
    (family M F T g).Admissible geom.width δ ∧
    (family M F T g).Separated (geom.separation*δ) ∧
    (family M F T g).Bounded geom.radius ∧
    (family M F T g).CapBound δ m A := by
  refine ⟨?_,hsep g,hbounded g,hcap g⟩
  intro i z hz
  exact hadm g i z (hshade (⟨g,i⟩,z) (hTS ((mem_shade M T g i z).mp hz)))



def density (δ : ℝ) (T : Finset (Record (k := k) M)) (g : G) : ℝ :=
  δ * (∑ i, ((shade M T g i).card : ℝ)) / M g

omit [Fintype G] in
theorem density_mass (δ : ℝ) (T : Finset (Record (k := k) M)) (g : G) :
    (M g : ℝ) * density M δ T g = δ * ∑ i, ((shade M T g i).card : ℝ) := by
  by_cases hz : M g = 0
  · have : IsEmpty (Fin (M g)) := by rw [hz]; infer_instance
    simp [density,hz]
  · dsimp [density]
    field_simp

theorem total_density_mass (δ : ℝ) (T : Finset (Record (k := k) M)) :
    ∑ g, (M g : ℝ) * density M δ T g = δ * (T.card : ℝ) := by
  simp_rw [density_mass]
  rw [← mul_sum]
  congr 1
  exact_mod_cast total_incidence M T

/-- Construct each restricted cumulative configuration and apply weighted Jensen
across all groups. No number-of-groups loss appears. -/
theorem grouped_bound {geom : Normalization} {m d p ε c δ A : ℝ}
    (hc : 0 < c) (hp : 1 ≤ p) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    (hestimate : ∀ H : CumulativeConfiguration k geom m,
      c * H.A⁻¹ * H.δ ^ (m-d+ε) * H.s ^ p * H.M ≤ (H.family.unionCells.card : ℝ))
    (F : ∀ g, TubeFamily k (M g)) (S T : Finset (Record (k := k) M)) (hTS : T ⊆ S)
    (hshade : ∀ r ∈ S, r.2 ∈ (F r.1.1).shade r.1.2)
    (hadm : ∀ g, (F g).Admissible geom.width δ)
    (hsep : ∀ g, (F g).Separated (geom.separation*δ))
    (hbounded : ∀ g, (F g).Bounded geom.radius)
    (hcap : ∀ g, (F g).CapBound δ m A)
    (hQ : 0 < ∑ g, (M g : ℝ)) :
    (c * A⁻¹ * δ^(m-d+ε)) * ((∑ g, (M g : ℝ)) *
      (δ*(T.card : ℝ)/(∑ g, (M g : ℝ)))^p) ≤ ((T.image (support M)).card : ℝ) := by
  have hden (g : G) : 0 ≤ density M δ T g := by dsimp [density]; positivity
  have hgroup (g : G) : (c * A⁻¹ * δ^(m-d+ε)) *
      ((M g : ℝ) * (density M δ T g)^p) ≤ ((family M F T g).unionCells.card : ℝ) := by
    obtain ⟨ha,hs,hb,hc'⟩ := family_geometry M F S T hTS geom hshade hadm hsep hbounded hcap g
    let H : CumulativeConfiguration k geom m := {
      M := M g
      δ := δ
      s := density M δ T g
      A := A
      family := family M F T g
      scale_pos := hδ
      scale_le_one := hδ1
      density_nonneg := hden g
      cap_ge_one := hA
      admissible := ha
      separated := hs
      bounded := hb
      cap_bound := hc'
      cumulative := by rw [mul_comm,density_mass]; rfl
    }
    have hh := hestimate H
    change c * A⁻¹ * δ^(m-d+ε) * (density M δ T g)^p * (M g : ℝ) ≤ _ at hh
    convert hh using 1
    ring
  have hj := KakeyaFinite.weighted_power univ (fun g => (M g : ℝ)) (density M δ T)
    hQ hp (fun _ _ => Nat.cast_nonneg _) (fun g _ => hden g) rfl
  rw [total_density_mass] at hj
  have hcoef : 0 ≤ c * A⁻¹ * δ^(m-d+ε) := by
    have : 0 < A := by linarith
    positivity
  calc
    _ ≤ (c * A⁻¹ * δ^(m-d+ε)) * ∑ g, (M g : ℝ) * (density M δ T g)^p :=
      mul_le_mul_of_nonneg_left hj hcoef
    _ = ∑ g, (c * A⁻¹ * δ^(m-d+ε)) * ((M g : ℝ) * (density M δ T g)^p) := mul_sum ..
    _ ≤ ∑ g, ((family M F T g).unionCells.card : ℝ) := sum_le_sum fun g _ => hgroup g
    _ = ((T.image (support M)).card : ℝ) := by exact_mod_cast total_support M F T


omit [Fintype G] in
/-- Encoding each group by a coarse group and a finite direction color preserves
its actual refined support exactly when the group encoding is injective. -/
theorem colored_support_card {B C : Type*} (base : G → B) (color : G → C)
    (hinj : Function.Injective (fun g => (base g,color g)))
    (T : Finset (Record (k := k) M)) :
    (T.image (fun r => ((base r.1.1,r.2),color r.1.1))).card =
      (T.image (support M)).card := by
  let encode : G × Cell k → (B × Cell k) × C := fun x => ((base x.1,x.2),color x.1)
  have he : Function.Injective encode := by
    intro x y h
    change ((base x.1,x.2),color x.1) = ((base y.1,y.2),color y.1) at h
    have hb : base x.1 = base y.1 := congrArg (fun z : (B × Cell k) × C => z.1.1) h
    have hc : color x.1 = color y.1 := congrArg (fun z : (B × Cell k) × C => z.2) h
    have hg : x.1 = y.1 := hinj (Prod.ext hb hc)
    exact Prod.ext hg (congrArg (fun z : (B × Cell k) × C => z.1.2) h)
  have hid : T.image (fun r => ((base r.1.1,r.2),color r.1.1)) =
      (T.image (support M)).image encode := by rw [image_image]; rfl
  rw [hid,card_image_of_injective _ he]

/-- The actual grouped cumulative estimate supplies the sole analytic premise
of calibrated high-cell pruning. Both the retained set and its energy are actual
finite incidence objects. -/
theorem pruning {B C : Type*} [Fintype C] [Nonempty C]
    (base : G → B) (color : G → C)
    (hinj : Function.Injective (fun g => (base g,color g)))
    {geom : Normalization} {m d p ε c δ A : ℝ}
    (hc : 0 < c) (hp : 1 ≤ p) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA : 1 ≤ A)
    (hestimate : ∀ H : CumulativeConfiguration k geom m,
      c * H.A⁻¹ * H.δ ^ (m-d+ε) * H.s ^ p * H.M ≤ (H.family.unionCells.card : ℝ))
    (F : ∀ g, TubeFamily k (M g)) (S : Finset (Record (k := k) M)) (hS : S.Nonempty)
    (hshade : ∀ r ∈ S, r.2 ∈ (F r.1.1).shade r.1.2)
    (hadm : ∀ g, (F g).Admissible geom.width δ)
    (hsep : ∀ g, (F g).Separated (geom.separation*δ))
    (hbounded : ∀ g, (F g).Bounded geom.radius)
    (hcap : ∀ g, (F g).CapBound δ m A)
    (hQ : 0 < ∑ g, (M g : ℝ)) :
    let Q := ∑ g, (M g : ℝ)
    let rho := δ*(S.card : ℝ)/Q
    let a := c*A⁻¹*δ^(m-d+ε)
    let H := (2:ℝ)^(p+1)*(Fintype.card C:ℝ)*(1/δ)/(a*rho^(p-1))
    let f : Record (k := k) M → B × Cell k := fun r => (base r.1.1,r.2)
    ∃ T ⊆ S, (S.card : ℝ)/2 < (T.card : ℝ) ∧
      (∑ b ∈ T.image f, (GroupedIncidence.degree T f b : ℝ)^2) ≤ H*(T.card : ℝ) := by
  classical
  intro Q rho a H f
  have hN : 0 < 1/δ := by positivity
  have hrho : 0 < rho := div_pos (mul_pos hδ (by exact_mod_cast card_pos.mpr hS)) hQ
  have ha : 0 < a := by
    dsimp [a]
    have : 0 < A := by linarith
    positivity
  have hQ' : 0 < Q := hQ
  have hmass : (S.card : ℝ) = rho*(1/δ)*Q := by
    dsimp [rho]
    field_simp [hQ'.ne',hδ.ne']
  have hanalytic : ∀ T ⊆ S, a*(Q*((T.card : ℝ)/((1/δ)*Q))^p) ≤
      ((T.image (fun r => (f r,color r.1.1))).card : ℝ) := by
    intro T hTS
    have hh := grouped_bound M hc hp hδ hδ1 hA hestimate F S T hTS hshade hadm hsep hbounded hcap hQ
    change a*(Q*((T.card : ℝ)/((1/δ)*Q))^p) ≤
      ((T.image (fun r => ((base r.1.1,r.2),color r.1.1))).card : ℝ)
    rw [colored_support_card M base color hinj]
    have hid : (T.card : ℝ)/((1/δ)*Q) = δ*(T.card : ℝ)/Q := by rw [one_div,inv_mul_eq_div,div_div_eq_mul_div,mul_comm (T.card : ℝ) δ]
    rw [hid]
    exact hh
  have hd : (instDecidableEqProd : DecidableEq (B × Cell k)) = Classical.decEq (B × Cell k) := Subsingleton.elim _ _
  rw [hd] at hanalytic ⊢
  have hh := GroupedIncidence.calibrated_pruning S f (fun r => color r.1.1) hN hQ' hrho hp ha hmass (by simpa only using hanalytic)
  simpa only [H] using hh

/-- Any nonempty incidence set already forces a positive total original tube
count; unused and empty groups cause no difficulty. -/
theorem tube_count_pos (S : Finset (Record (k := k) M)) (hS : S.Nonempty) :
    0 < ∑ g, (M g : ℝ) := by
  obtain ⟨⟨⟨g,i⟩,z⟩,_⟩ := hS
  apply sum_pos' (fun _ _ => Nat.cast_nonneg _)
  exact ⟨g,mem_univ _,by exact_mod_cast (show 0 < M g by have := i.isLt; omega)⟩

omit M [Fintype G] in
/-- The complete actual grouped pruning consequence. Its positive constant is
chosen before the finite group type, group encoding, tube counts, scale, cap
coefficient, actual tube families, and every finite incidence set. -/
theorem discrete_pruning {geom : Normalization} {m d p ε : ℝ}
    (h : DiscreteEstimate k m d p) (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (G : Type u) [Fintype G] (B : Type v) (C : Type w)
      [Fintype C] [Nonempty C] (base : G → B) (color : G → C),
      Function.Injective (fun g => (base g,color g)) →
      ∀ (M : G → ℕ) (δ A : ℝ),
      0 < δ → δ ≤ 1 → 1 ≤ A →
      ∀ (F : ∀ g, TubeFamily k (M g)) (S : Finset (Record (k := k) M)),
      S.Nonempty →
      (∀ r ∈ S, r.2 ∈ (F r.1.1).shade r.1.2) →
      (∀ g, (F g).Admissible geom.width δ) →
      (∀ g, (F g).Separated (geom.separation*δ)) →
      (∀ g, (F g).Bounded geom.radius) →
      (∀ g, (F g).CapBound δ m A) →
      let Q := ∑ g, (M g : ℝ)
      let rho := δ*(S.card : ℝ)/Q
      let a := c*A⁻¹*δ^(m-d+ε)
      let H := (2:ℝ)^(p+1)*(Fintype.card C:ℝ)*(1/δ)/(a*rho^(p-1))
      let f : Record (k := k) M → B × Cell k := fun r => (base r.1.1,r.2)
      ∃ T ⊆ S, (S.card : ℝ)/2 < (T.card : ℝ) ∧
        (∑ b ∈ T.image f, (GroupedIncidence.degree T f b : ℝ)^2) ≤ H*(T.card : ℝ) := by
  obtain ⟨c,hc,hbound⟩ := h.to_cumulative hp geom ε hε
  refine ⟨c,hc,?_⟩
  intro G _ B C _ _ base color hinj M δ A hδ hδ1 hA F S hS hshade hadm hsep hbounded hcap
  exact pruning M base color hinj hc hp hδ hδ1 hA hbound F S hS hshade hadm hsep hbounded hcap
    (tube_count_pos M S hS)

end
end KakeyaFormal.GroupedCumulative

#print axioms KakeyaFormal.GroupedCumulative.total_incidence
#print axioms KakeyaFormal.GroupedCumulative.total_support
#print axioms KakeyaFormal.GroupedCumulative.grouped_bound
#print axioms KakeyaFormal.GroupedCumulative.pruning
#print axioms KakeyaFormal.GroupedCumulative.discrete_pruning
