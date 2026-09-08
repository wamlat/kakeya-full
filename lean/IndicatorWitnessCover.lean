import KakeyaOperator
import CapCover

/-! An actual finite separated family of strict indicator-level witnesses.
The direction net is constructed inside the level set, even when that set has
not yet been proved measurable. Compactness supplies an ordinary finite cover;
a maximal projectively separated subset then covers the entire level set. -/
namespace KakeyaFormal.IndicatorWitnessCover
open MeasureTheory Set Metric KakeyaOperator ProjectiveGeometry
noncomputable section

/-- Every subset of the unit direction sphere has an actual finite separated
projective cover with centers in that same subset. -/
theorem level_net {n : ℕ} (L : Set (Direction n)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ net : Finset (Direction n),
      (∀ v ∈ net, v ∈ L) ∧
      CapCover.SeparatedOn (fun v : Direction n => v.val) (δ/2) net ∧
      ∀ v ∈ L, ∃ w ∈ net, projectiveDistance v.val w.val < δ := by
  classical
  have hc : IsCompact (closure L) := isClosed_closure.isCompact
  obtain ⟨points,hsub,hfinite,hcover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hc (show 0 < δ/4 by positivity)
  obtain ⟨net,hnet,hsep,hproj⟩ := CapCover.finite_projective_net hfinite.toFinset
    (fun v : Direction n => v.val) (show 0 < δ/2 by positivity)
  refine ⟨net,fun v hv => hsub (hfinite.mem_toFinset.mp (hnet hv)),hsep,?_⟩
  intro v hv
  obtain ⟨w,hw,hvw⟩ := Set.mem_iUnion₂.mp (hcover hv)
  obtain ⟨z,hz,hwz⟩ := hproj w (hfinite.mem_toFinset.mpr hw)
  refine ⟨z,hz,?_⟩
  have hvw' : projectiveDistance v.val w.val < δ/4 := by
    apply (projective_le_chord _ _).trans_lt
    simpa only [Metric.mem_ball,Subtype.dist_eq,dist_eq_norm] using hvw
  have htri := projective_triangle v.val w.val z.val
  linarith

/-- The constructed family keeps the actual original positions of the strict
supremum witnesses. Finite grid shadings are unused; `shading` contains the
literal measurable intersections with the test set. -/
structure Witnesses (n : ℕ) (δ lam : ℝ) (E : Set (Space n)) where
  M : ℕ
  direction : Fin M → Direction n
  family : TubeFamily n M
  direction_eq : ∀ i, (family.tube i).direction = (direction i).val
  shading : Fin M → Set (Space n)
  shading_eq : ∀ i, shading i = E ∩ (family.tube i).carrier δ
  shading_measurable : ∀ i, MeasurableSet (shading i)
  shading_subset : ∀ i, shading i ⊆ (family.tube i).carrier δ
  union_subset : (⋃ i, shading i) ⊆ E
  strict_mass : ∀ i, lam*(volume : Measure (Space n)).real ((family.tube i).carrier δ) <
    (volume : Measure (Space n)).real (shading i)
  separated : family.Separated (δ/2)
  direction_level : ∀ i, direction i ∈ indicatorLevel δ E lam
  covers : ∀ v ∈ indicatorLevel δ E lam,
    ∃ i, projectiveDistance v.val (direction i).val < δ

/-- No finite net, tube position, or density witness is an input. -/
theorem construct {n : ℕ} {δ lam : ℝ} (hδ : 0 < δ)
    (E : Set (Space n)) (hE : MeasurableSet E) : Nonempty (Witnesses n δ lam E) := by
  classical
  obtain ⟨net,hlevel,hsep,hcover⟩ := level_net (indicatorLevel δ E lam) hδ
  let direction : Fin net.card → Direction n := fun i => (net.equivFin.symm i).val
  have hinj : Function.Injective direction := Subtype.val_injective.comp net.equivFin.symm.injective
  have hdir (i : Fin net.card) : direction i ∈ net := (net.equivFin.symm i).property
  have hdirlevel (i : Fin net.card) : direction i ∈ indicatorLevel δ E lam := hlevel _ (hdir i)
  have hex (i : Fin net.card) := (mem_indicatorLevel_iff hδ E (direction i) lam).mp (hdirlevel i)
  choose base hbase using hex
  let F : TubeFamily n net.card := { tube := fun i => tube (direction i) (base i), shade := fun _ => ∅ }
  let Y : Fin net.card → Set (Space n) := fun i => E ∩ (F.tube i).carrier δ
  refine ⟨{
    M := net.card, direction := direction, family := F,
    direction_eq := fun _ => rfl, shading := Y, shading_eq := fun _ => rfl,
    shading_measurable := fun i => hE.inter (TubeVolume.carrier_measurable _ _),
    shading_subset := fun _ => inter_subset_right,
    union_subset := ?_, strict_mass := hbase, separated := ?_,
    direction_level := hdirlevel, covers := ?_ }⟩
  · exact iUnion_subset (fun _ => inter_subset_left)
  · intro i j hij
    exact hsep _ (hdir i) _ (hdir j) (fun heq => hij (hinj heq))
  · intro v hv
    obtain ⟨w,hw,hvw⟩ := hcover v hv
    refine ⟨net.equivFin ⟨w,hw⟩,?_⟩
    simpa [direction] using hvw

end
end KakeyaFormal.IndicatorWitnessCover
