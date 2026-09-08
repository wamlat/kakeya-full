import Mathlib

/-! Exact independent-set bound used for the projected collision graph.
The numerical conclusion is derived from Mathlib's proved Turan theorem on
the complement; no independent-set size or graph-selection oracle is assumed. -/
namespace KakeyaFormal.CollisionIndependentSet
open SimpleGraph
noncomputable section
open Classical

variable {V : Type*} [Fintype V]

/-- The two actual edge counts partition all unordered pairs of distinct
vertices. The degree-sum formula proves the real polynomial identity. -/
theorem complement_edge_identity (G : SimpleGraph V) :
    2*(G.edgeFinset.card:ℝ)+2*(Gᶜ.edgeFinset.card:ℝ)=
      (Fintype.card V:ℝ)^2-Fintype.card V := by
  by_cases hV : Fintype.card V=0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hV
    have hg : G.edgeFinset.card=0 := by
      have hh := G.sum_degrees_eq_twice_card_edges
      simp only [Finset.univ_eq_empty,Finset.sum_empty] at hh
      omega
    have hc : Gᶜ.edgeFinset.card=0 := by
      have hh := Gᶜ.sum_degrees_eq_twice_card_edges
      simp only [Finset.univ_eq_empty,Finset.sum_empty] at hh
      omega
    simp [hg,hc]
  · have hVpos : 0 < Fintype.card V := Nat.pos_of_ne_zero hV
    have hdeg (v : V) : G.degree v+Gᶜ.degree v=Fintype.card V-1 := by
      rw [G.degree_compl]
      have hh := G.degree_lt_card_verts v
      omega
    have hsum : 2*G.edgeFinset.card+2*Gᶜ.edgeFinset.card=
        Fintype.card V*(Fintype.card V-1) := by
      rw [← G.sum_degrees_eq_twice_card_edges,← Gᶜ.sum_degrees_eq_twice_card_edges,
        ← Finset.sum_add_distrib]
      simp only [hdeg,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
    have hh : 2*(G.edgeFinset.card:ℝ)+2*(Gᶜ.edgeFinset.card:ℝ)=
        (Fintype.card V:ℝ)*((Fintype.card V:ℝ)-1) := by
      have hh := congrArg (fun n : ℕ => (n:ℝ)) hsum
      simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,
        Nat.cast_sub (show 1 ≤ Fintype.card V by omega),Nat.cast_one] using hh
    nlinarith

/-- Clearing the denominator avoids any empty-vertex exception. -/
theorem indepNum_product_bound (G : SimpleGraph V) :
    (Fintype.card V:ℝ)^2 ≤ (G.indepNum:ℝ)*((Fintype.card V:ℝ)+2*G.edgeFinset.card) := by
  by_cases hV : Fintype.card V=0
  · simp only [hV,Nat.cast_zero,zero_pow (by decide : 2≠0),zero_add]
    positivity
  have : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hV)
  obtain ⟨v⟩ := ‹Nonempty V›
  have hr : 1 ≤ G.indepNum := by
    have hh := (show G.IsIndepSet ({v} : Finset V) by simp).card_le_indepNum
    simpa using hh
  have hcf : Gᶜ.CliqueFree (G.indepNum+1) := by
    intro t ht
    have hh := ht.isClique.card_le_cliqueNum
    rw [ht.card_eq,cliqueNum_compl] at hh
    omega
  obtain ⟨H,instH,hmax⟩ := SimpleGraph.exists_isTuranMaximal (V:=V) (by omega : 0 < G.indepNum)
  let := instH
  obtain ⟨e⟩ := hmax.nonempty_iso_turanGraph
  have hE : Gᶜ.edgeFinset.card ≤ (turanGraph (Fintype.card V) G.indepNum).edgeFinset.card :=
    (hmax.2 hcf).trans_eq e.card_edgeFinset_eq
  have hT := SimpleGraph.mul_card_edgeFinset_turanGraph_le (n:=Fintype.card V) (r:=G.indepNum)
  have hhN : 2*G.indepNum*Gᶜ.edgeFinset.card ≤ (G.indepNum-1)*(Fintype.card V)^2 :=
    (Nat.mul_le_mul_left _ hE).trans hT
  have hh : 2*(G.indepNum:ℝ)*(Gᶜ.edgeFinset.card:ℝ) ≤
      ((G.indepNum:ℝ)-1)*(Fintype.card V:ℝ)^2 := by
    exact_mod_cast hhN
  have he := complement_edge_identity G
  nlinarith

/-- The exact V²/(V+2e) conclusion from the source, for an actual independent
set of the supplied finite graph. It includes the empty graph with 0/0=0. -/
theorem exists_independent (G : SimpleGraph V) :
    ∃ S : Finset V, G.IsIndepSet S ∧
      (Fintype.card V:ℝ)^2/((Fintype.card V:ℝ)+2*G.edgeFinset.card) ≤ (S.card:ℝ) := by
  obtain ⟨S,hS⟩ := G.exists_isNIndepSet_indepNum
  refine ⟨S,hS.isIndepSet,?_⟩
  rw [hS.card_eq]
  by_cases hV : Fintype.card V=0
  · simp only [hV,Nat.cast_zero,zero_pow (by decide : 2≠0),zero_div]
    positivity
  · have hVp : (0:ℝ)<Fintype.card V := by exact_mod_cast Nat.pos_of_ne_zero hV
    exact (div_le_iff₀ (by positivity : (0:ℝ)<Fintype.card V+2*G.edgeFinset.card)).mpr
      (indepNum_product_bound G)

def orderedCount (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter (fun p : V × V => G.Adj p.1 p.2)).card

theorem orderedCount_eq (G : SimpleGraph V) : orderedCount G=2*G.edgeFinset.card :=
  G.two_mul_card_edgeFinset.symm

/-- The version directly consumed by an ordered collision counter. -/
theorem exists_independent_ordered (G : SimpleGraph V) :
    ∃ S : Finset V, G.IsIndepSet S ∧
      (Fintype.card V:ℝ)^2/((Fintype.card V:ℝ)+orderedCount G) ≤ (S.card:ℝ) := by
  simpa only [orderedCount_eq,Nat.cast_mul,Nat.cast_ofNat] using exists_independent G

end
end KakeyaFormal.CollisionIndependentSet
