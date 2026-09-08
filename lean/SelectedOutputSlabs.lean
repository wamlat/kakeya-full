import SelectedOutputPairs
import SlabNormalization
import PrunedGraphLift

/-! Simultaneous actual selected-line slab data from the original selected
output indices.  The common positive integer K is computed once from the exact
dyadic fiber size, normalized kappa, dimension and fixed projection width. -/
namespace KakeyaFormal.SelectedOutputSlabs
open Finset ActualLabelSelection AngleFiberSelection LegalAngleSamples
open LegalLabeledSamples SelectedOutputPairs SelectedFiberLift SelectedFiberSlab
open scoped BigOperators
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily (k+1) M} {H : Finset (Cell (k+1))}
    {δ lam kappa width : ℝ} {S : SampleSystem F H δ lam kappa width}
    {hkappa : 0 < kappa} {hwidth : 0 ≤ width} {hadm : F.Admissible width δ}
    (P : Selection S hkappa hwidth hadm)

/-- The identical integer for every original selected output. -/
def commonK : ℕ := commonCount (k+1) (2*width) (kappa/(1+2*width)) (2^P.level)

theorem commonK_pos : 1 ≤ commonK P := le_max_left _ _

/-- Polynomial retained-population lower bound and the nonempty floor upper
bound, before any particular original output is chosen. -/
theorem commonK_bounds :
    (kappa/(1+2*width))^6*(2^P.level : ℕ)/(20*multiplicityConstant (k+1) (2*width)) ≤
      (commonK P : ℝ) ∧
    (commonK P : ℝ) ≤
      (kappa/(1+2*width))^6*(2^P.level : ℕ)/(10*multiplicityConstant (k+1) (2*width))+1 := by
  have hC := multiplicityConstant_pos (k+1) (2*width)
  have hR : 0 < 1+2*width := by linarith
  have hx : 0 ≤ (kappa/(1+2*width))^6*(2^P.level : ℕ)/
      (10*multiplicityConstant (k+1) (2*width)) := by positivity
  have hh := KakeyaFinite.nonempty_floor_truncation hx
  constructor
  · convert hh.1 using 1 <;> first | rfl | ring
  · exact hh.2

/-- Complete actual slab and representative data for one original output.
The reference and raw endpoints remain the constructed original fiber. -/
structure LineData (q : Index P) where
  slab : ℕ
  slab_upper : slab ≤ Nat.ceil (3/(kappa/(1+2*width)))
  cells : Finset (Cell (k+2))
  cells_subset : cells ⊆ liftedCells (reference P q) (raw P q)
  cells_card : cells.card = commonK P
  center_slab : ∀ z ∈ cells, (slab : ℝ) ≤ (δ/(1+2*width))*(z 0 : ℝ) ∧
    (δ/(1+2*width))*(z 0 : ℝ) < (slab : ℝ)+1
  representative : ↥cells → PivotOutputCount.LabeledPair (normalizedAngle P q)
    (δ/(1+2*width)) (2*width)
    (firstCoord S (P.chosen_angle q)) (secondCoord S (P.chosen_angle q))
  representative_injective : Function.Injective representative
  representative_mem : ∀ z, representative z ∈ raw P q
  representative_cell : ∀ z, liftedCell (reference P q) (representative z) = z.val

/-- The existing actual slab theorem is instantiated with the original exact
sample fiber and its actual reference. Only its explicit perturbation scale
test remains; all cardinality, pivot and nonemptiness premises are discharged. -/
theorem line_exists (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hkappa1 : kappa ≤ 1)
    (hscale : ((k+1 : ℕ) : ℝ)*(δ/(1+2*width)) ≤ (kappa/(1+2*width))^5/4)
    (q : Index P) : Nonempty (LineData P q) := by
  have hR : 0 < 1+2*width := by linarith
  have hδnorm : δ/(1+2*width) ≤ 1 := (div_le_one hR).mpr (by linarith)
  have hknorm : kappa/(1+2*width) ≤ 1 := (div_le_one hR).mpr (by linarith)
  have hpivot (s) (hs : s ∈ raw P q) : s.pivotLabel = (reference P q).pivotLabel :=
    (raw_pivot P q s hs).trans (reference_pivot P q).symm
  obtain ⟨_,_,_,j,hj,V,hsub,hcard,hslab,rep,hinj,hmem⟩ :=
    common_integer_slab (reference P q) (raw P q) (raw_nonempty P q)
      (div_pos hδ hR) hδnorm (div_pos hkappa hR) hknorm hpivot hscale
  refine ⟨{
    slab := j
    slab_upper := hj
    cells := V
    cells_subset := hsub
    cells_card := ?_
    center_slab := hslab
    representative := rep
    representative_injective := hinj
    representative_mem := fun z => (hmem z).1
    representative_cell := fun z => (hmem z).2 }⟩
  simpa only [raw_card,commonK] using hcard

/-- The simultaneous selection is one function on the unchanged original
output index type, so no new multiplicity or output relabeling is introduced. -/
def selectedLine (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hkappa1 : kappa ≤ 1)
    (hscale : ((k+1 : ℕ) : ℝ)*(δ/(1+2*width)) ≤ (kappa/(1+2*width))^5/4)
    (q : Index P) : LineData P q :=
  Classical.choice (line_exists P hδ hδ1 hkappa1 hscale q)

/-- Each selected cell has positive common cardinality. -/
theorem LineData.cells_nonempty {q : Index P} (D : LineData P q) : D.cells.Nonempty := by
  apply card_pos.mp
  rw [D.cells_card]
  exact lt_of_lt_of_le Nat.zero_lt_one (commonK_pos P)

/-- The representative decodes to the original chosen triple in exactly its
original angle-output fiber. -/
theorem LineData.representative_original {q : Index P} (D : LineData P q) (z : ↥D.cells) :
    ((P.chosen_output q).2,(D.representative z).firstLabel,(D.representative z).secondLabel) ∈
      P.chosen_samples q :=
  raw_original_sample P q _ (D.representative_mem z)

/-- Both endpoint labels remain in the original full shaded tube family. -/
theorem LineData.representative_occupied {q : Index P} (D : LineData P q) (z : ↥D.cells) :
    (D.representative z).firstLabel ∈ F.shade (P.chosen_angle q).val.2.1 ∧
      (D.representative z).secondLabel ∈ F.shade (P.chosen_angle q).val.2.2 := by
  have hp := P.chosen_samples_actual q _ (D.representative_original P z)
  have hl := S.legal (P.chosen_angle q) _ hp.1
  exact ⟨hl.2.1,hl.2.2.1⟩

/-- The actual pivot/slab base label associated to one chosen line. -/
def LineData.base {q : Index P} (D : LineData P q) : Cell (k+1) × ℕ :=
  ((P.chosen_output q).1,D.slab)

/-- Choosing unit slabs does not change the injected original output labels. -/
theorem line_output_injective (D : ∀ q, LineData P q) : Function.Injective
    (fun q => ((D q).base P |>.1,(P.chosen_output q).2)) :=
  P.chosen_output_injective

/-- The actual same-K slab cells have total population exactly KQ. -/
theorem total_selected_cells (D : ∀ q, LineData P q) :
    ∑ q, (D q).cells.card = commonK P*(outputSupport P.retained).card := by
  simp only [LineData.cells_card,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  exact Nat.mul_comm _ _

/-- The original retained output population is nonempty, so the simultaneous
line construction and its density bounds are nonvacuous. -/
theorem index_nonempty : Nonempty (Index P) := by
  have he : outputSupport P.retained = P.retained.image Prod.snd := by
    unfold outputSupport
    congr 1
    exact Subsingleton.elim _ _
  have hQ : 0 < (outputSupport P.retained).card := by
    rw [he]
    exact card_pos.mpr (P.retained_nonempty.image Prod.snd)
  exact ⟨⟨0,hQ⟩⟩

/-- Actual projection and original tube incidence supply the intermediate
rounding error at the normalized mesh; no geometric residual is assumed. -/
theorem intermediate_close (q : Index P) :
    dist (cellCenter (δ/(1+2*width)) (P.chosen_output q).2)
      ((normalizedAngle P q).vertex+
        (normalizedAngle P q).intermediate • (normalizedAngle P q).first) ≤
      (2*width)*(δ/(1+2*width)) :=
  LegalOutputDirections.intermediate_rounding S (P.chosen_angle q)
    (intermediate P q) hkappa hwidth hadm

/-- Bounded original tube bases give a common bounded region for the actual
normalized selected-angle vertices. No per-output translation is made. -/
theorem normalized_vertex_bound {R : ℝ} (hδ1 : δ ≤ 1) (hbounded : F.Bounded R)
    (q : Index P) : ‖(normalizedAngle P q).vertex‖ ≤ PrunedGraphLift.regionRadius width R := by
  have ha := (TransverseAngles.mem_angles F H kappa (P.chosen_angle q).val).mp
    (P.chosen_angle q).property
  have hv : (P.chosen_angle q).val.1 ∈ F.unionCells :=
    mem_biUnion.mpr ⟨(P.chosen_angle q).val.2.1,mem_univ _,ha.2.1⟩
  have hb := PrunedGraphLift.union_bounded F hδ1 hwidth hadm hbounded _ hv
  rw [dist_zero_right] at hb
  have hR : 0 < 1+2*width := by linarith
  have hinv : (1+2*width)⁻¹ ≤ 1 := (inv_le_one₀ hR).mpr (by linarith)
  change ‖(1+2*width)⁻¹ • cellCenter δ (P.chosen_angle q).val.1‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hR.le)]
  simpa only [one_mul] using mul_le_mul hinv hb (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)

/-- The actual selected reference slope has norm at most one. -/
theorem reference_slope_bound (q : Index P) :
    ‖(reference P q).endpoints.coefficient • (normalizedAngle P q).second‖ ≤ 1 := by
  apply SlabNormalization.reference_slope_bound
  exact div_pos hkappa (by linarith)

/-- The actual original output labels determine the selected graph slope with
fixed error 2width+(k+1)/2 at the normalized mesh. -/
theorem reference_pivot_residual (hδ : 0 < δ) (q : Index P) :
    ‖(reference P q).endpoints.coefficient • (normalizedAngle P q).second-
      (cellCenter (δ/(1+2*width)) (P.chosen_output q).1-
        cellCenter (δ/(1+2*width)) (P.chosen_output q).2)‖ ≤
      (2*width+((k+1 : ℕ) : ℝ)/2)*(δ/(1+2*width)) :=
  SlabNormalization.reference_pivot_residual (reference P q) _ _
    (div_pos hδ (by linarith)) (reference_pivot P q) (intermediate_close P q)

/-- The normalized density has a fixed upper bound derived from the actual
original pair-fiber geometry, for each selected original output. -/
theorem common_density_upper (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hkappa1 : kappa ≤ 1)
    (q : Index P) :
    (δ/(1+2*width))*(commonK P : ℝ) ≤
      1+PivotOutputCount.fiberConstant (k+1) (2*width)/
        (10*multiplicityConstant (k+1) (2*width)) := by
  have hR : 0 < 1+2*width := by linarith
  have hh := SelectedFiberSlab.common_density_upper (reference P q) (raw P q)
    (div_pos hδ hR) ((div_le_one hR).mpr (by linarith))
    (div_pos hkappa hR) ((div_le_one hR).mpr (by linarith))
    (fun s hs => (raw_pivot P q s hs).trans (reference_pivot P q).symm)
  simpa only [raw_card,commonK] using hh

end
end KakeyaFormal.SelectedOutputSlabs
