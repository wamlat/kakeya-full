import CollisionPlane
import CollisionIntersection
import AngleFiberSelection
import ActualPivotFiberCount

/-! Actual collision rows, grouped by their competing original first tube.
The row includes every shared output with a fixed angle, with no hidden
multiplicity from a choice of a sample representing that output. -/
namespace KakeyaFormal.CollisionRows
open Finset LegalAngleSamples LegalSampleOutputs TransverseAngles AngleFiberSelection
open scoped BigOperators
noncomputable section
open Classical

variable {n M : ℕ} {F : TubeFamily n M} {H : Finset (Cell n)}
variable {δ lam kappa width : ℝ}

def row (S : SampleSystem F H δ lam kappa width)
    (hk : 0 < kappa) (hw : 0 ≤ width) (hadm : F.Admissible width δ)
    (a : ↥(angles F H kappa)) :
    Finset (↥(angles F H kappa) × (Cell n × Cell n)) :=
  (edges univ S.samples (fun b => output S b hk hw hadm)).filter
    (fun e => e.2 ∈ outputs S.samples (fun b => output S b hk hw hadm) a ∧
      e.1.val.2.2=a.val.2.2)

theorem mem_row (S : SampleSystem F H δ lam kappa width)
    (hk : 0 < kappa) (hw : 0 ≤ width) (hadm : F.Admissible width δ)
    (a : ↥(angles F H kappa)) (e : ↥(angles F H kappa) × (Cell n × Cell n)) :
    e ∈ row S hk hw hadm a ↔
      e.2 ∈ outputs S.samples (fun b => output S b hk hw hadm) e.1 ∧
      e.2 ∈ outputs S.samples (fun b => output S b hk hw hadm) a ∧
      e.1.val.2.2=a.val.2.2 := by
  classical
  simp only [row,mem_filter,mem_edges,mem_univ,true_and]

/-- A shared output's second label is actually occupied on both original
first tubes. This follows from the legal raw samples on each side. -/
theorem row_intermediate (S : SampleSystem F H δ lam kappa width)
    (hk : 0 < kappa) (hw : 0 ≤ width) (hadm : F.Admissible width δ)
    (a : ↥(angles F H kappa)) (e : ↥(angles F H kappa) × (Cell n × Cell n))
    (he : e ∈ row S hk hw hadm a) :
    e.2.2 ∈ F.shade a.val.2.1 ∩ F.shade e.1.val.2.1 := by
  classical
  obtain ⟨hb,ha,_⟩ := (mem_row S hk hw hadm a e).mp he
  obtain ⟨p,hp,hpout⟩ : ∃ p ∈ S.samples a, output S a hk hw hadm p=e.2 := by
    simpa only [outputs,mem_image] using ha
  obtain ⟨q,hq,hqout⟩ : ∃ q ∈ S.samples e.1, output S e.1 hk hw hadm q=e.2 := by
    simpa only [outputs,mem_image] using hb
  have hpint : e.2.2=p.1 := by
    rw [← hpout,CollisionPlane.output_intermediate S a hk hw hadm p hp]
  have hqint : e.2.2=q.1 := by
    rw [← hqout,CollisionPlane.output_intermediate S e.1 hk hw hadm q hq]
  exact mem_inter.mpr ⟨by rw [hpint]; exact (S.legal a p hp).1,
    by rw [hqint]; exact (S.legal e.1 q hq).1⟩

/-- Actual possible first indices from any subset of the row lie in the
all-output direction set already controlled by the thin-plane theorem. -/
theorem row_first_index {k M : ℕ} {F : TubeFamily (k+2) M}
    {H : Finset (Cell (k+2))} {δ lam kappa width : ℝ}
    (S : SampleSystem F H δ lam kappa width)
    (hk : 0 < kappa) (hw : 0 ≤ width) (hadm : F.Admissible width δ)
    (a : ↥(angles F H kappa)) (e : ↥(angles F H kappa) × (Cell (k+2) × Cell (k+2)))
    (he : e ∈ row S hk hw hadm a) :
    e.1.val.2.1 ∈ CollisionPlane.firstIndices S a hk hw hadm := by
  classical
  obtain ⟨hb,ha,hs⟩ := (mem_row S hk hw hadm a e).mp he
  obtain ⟨p,hp,hpout⟩ : ∃ p ∈ S.samples a, output S a hk hw hadm p=e.2 := by
    simpa only [outputs,mem_image] using ha
  obtain ⟨q,hq,hqout⟩ : ∃ q ∈ S.samples e.1, output S e.1 hk hw hadm q=e.2 := by
    simpa only [outputs,mem_image] using hb
  exact mem_image.mpr ⟨e.1,mem_filter.mpr ⟨mem_univ _,hs,
    p,hp,q,hq,hpout.trans hqout.symm⟩,rfl⟩

/-- Counting by actual intermediate labels counts each output only once.
This finite identity will be supplied the proved fixed-label pivot bound. -/
theorem output_subset_count (O : Finset (Cell n × Cell n)) (Z : Finset (Cell n))
    {P : ℝ} (hP : 0 ≤ P)
    (hfiber : ∀ z ∈ Z, ((O.filter (fun f => f.2=z)).card:ℝ) ≤ P) :
    ((O.filter (fun f => f.2 ∈ Z)).card:ℝ) ≤ (Z.card:ℝ)*P := by
  classical
  let E := O.filter (fun f => f.2 ∈ Z)
  have hsum : (E.card:ℝ) = ∑ z ∈ E.image Prod.snd,
      ((E.filter (fun f => f.2=z)).card:ℝ) := by
    simpa only [card_eq_sum_ones,Nat.cast_sum,Nat.cast_one] using
      (sum_fiberwise_of_maps_to (s := E) (t := E.image Prod.snd) (g := Prod.snd)
        (fun f hf => mem_image.mpr ⟨f,hf,rfl⟩) (fun _ => (1:ℝ))).symm
  have hsub : E.image Prod.snd ⊆ Z := by
    intro z hz
    obtain ⟨f,hf,rfl⟩ := mem_image.mp hz
    exact (mem_filter.mp hf).2
  change (E.card:ℝ) ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ _z ∈ E.image Prod.snd, P := by
      apply sum_le_sum
      intro z hz
      have hc : ((E.filter (fun f => f.2=z)).card:ℝ) ≤
          ((O.filter (fun f => f.2=z)).card:ℝ) := by
        exact_mod_cast card_le_card (filter_subset_filter _ (filter_subset _ _ : E ⊆ O))
      exact hc.trans (hfiber z (hsub hz))
    _ = ((E.image Prod.snd).card:ℝ)*P := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hsub)) hP

/-- With the competing first tube fixed, the actual row injects into the
product of its actual marked angles and the shared geometric outputs. -/
theorem fixed_first_product_bound (S : SampleSystem F H δ lam kappa width)
    (hk : 0 < kappa) (hw : 0 ≤ width) (hadm : F.Admissible width δ)
    (a : ↥(angles F H kappa)) (i : Fin M) :
    ((row S hk hw hadm a).filter (fun e => e.1.val.2.1=i)).card ≤
      ((univ : Finset ↥(angles F H kappa)).filter
        (fun b => b.val.2.1=i ∧ b.val.2.2=a.val.2.2)).card *
      ((outputs S.samples (fun b => output S b hk hw hadm) a).filter
        (fun f => f.2 ∈ F.shade a.val.2.1 ∩ F.shade i)).card := by
  classical
  rw [← card_product]
  apply card_le_card
  intro e he
  obtain ⟨he,hi⟩ := mem_filter.mp he
  obtain ⟨_,ha,hs⟩ := (mem_row S hk hw hadm a e).mp he
  refine mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hi,hs⟩,
    mem_filter.mpr ⟨ha,?_⟩⟩
  simpa only [hi] using row_intermediate S hk hw hadm a e he


/-- The geometric fixed-first row constant, independent of scale, density,
conditioning and the number of original angles. -/
def fixedFirstConstant (n : ℕ) (width : ℝ) : ℝ :=
  2*PivotOutputCount.boxConstant n ((n:ℝ)/2)*(1+2*width)*
    (CollisionIntersection.intersectionConstant n width)^2

theorem fixedFirstConstant_pos (n : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    0 < fixedFirstConstant n width := by
  unfold fixedFirstConstant
  positivity [PivotOutputCount.boxConstant_pos n ((n:ℝ)/2),
    CollisionIntersection.intersectionConstant_pos n hw]

/-- Actual fixed-first collisions have the product of the intersection,
pivot-cell and marked-vertex bounds. The max includes the diagonal case. -/
theorem fixed_first_count (S : SampleSystem F H δ lam kappa width)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hk : 0 < kappa) (hw : 0 ≤ width)
    (hadm : F.Admissible width δ) (a : ↥(angles F H kappa)) (i : Fin M) :
    (((row S hk hw hadm a).filter (fun e => e.1.val.2.1=i)).card:ℝ) ≤
      fixedFirstConstant n width/(kappa*δ)*
        (1/max (projectiveDistance (F.tube i).direction (F.tube a.val.2.1).direction) δ) := by
  classical
  let O := outputs S.samples (fun b => output S b hk hw hadm) a
  let Z := F.shade a.val.2.1 ∩ F.shade i
  let P := 4*PivotOutputCount.boxConstant n ((n:ℝ)/2)*(1+2*width)/δ
  let C := CollisionIntersection.intersectionConstant n width
  have hP : 0 ≤ P := by
    dsimp [P]
    positivity [PivotOutputCount.boxConstant_pos n ((n:ℝ)/2)]
  have hC : 0 < C := CollisionIntersection.intersectionConstant_pos n hw
  have hfiber (z) (_hz : z ∈ Z) : ((O.filter (fun f => f.2=z)).card:ℝ) ≤ P := by
    apply ActualPivotFiberCount.restricted_output_count S a z hδ hδ1 hk hw hadm
    · intro f hf
      simpa only [O,outputs,mem_image] using (mem_filter.mp hf).1
    · intro f hf
      exact (mem_filter.mp hf).2
  have hout := output_subset_count O Z hP hfiber
  have hZ := CollisionIntersection.common_shading_count_max F hδ hδ1 hw hadm a.val.2.1 i
  rw [ProjectiveGeometry.projective_symm] at hZ
  have hout' := hout.trans (mul_le_mul_of_nonneg_right hZ hP)
  have hA := CollisionIntersection.fixed_pair_angle_subtype_count F H hδ hw hk hadm i a.val.2.2
  have hprod : (((row S hk hw hadm a).filter (fun e => e.1.val.2.1=i)).card:ℝ) ≤
      (((univ : Finset ↥(angles F H kappa)).filter
        (fun b => b.val.2.1=i ∧ b.val.2.2=a.val.2.2)).card:ℝ)*
      ((O.filter (fun f => f.2 ∈ Z)).card:ℝ) := by
    exact_mod_cast fixed_first_product_bound S hk hw hadm a i
  have hh := hprod.trans (mul_le_mul hA hout' (Nat.cast_nonneg _) (by positivity))
  exact hh.trans_eq (by unfold fixedFirstConstant; dsimp [P]; ring)

end
end KakeyaFormal.CollisionRows
