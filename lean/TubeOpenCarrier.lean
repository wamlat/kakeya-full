import TubeVolume

/-! Actual open and closed Euclidean capsules. Their difference is null, so
nonnegative tube integrals can use the open capsule without changing the
operator. The open carrier is open jointly in its base and direction. -/
namespace KakeyaFormal.TubeOpenCarrier
open Set Metric MeasureTheory
open scoped Pointwise Topology ENNReal
noncomputable section
open Classical

def axisSet {n : ℕ} (b v : Space n) : Set (Space n) :=
  (fun t : ℝ => b+t•v) '' Icc 0 1

def openCarrier {n : ℕ} (b v : Space n) (δ : ℝ) : Set (Space n) :=
  {x | ∃ t ∈ Icc (0:ℝ) 1, dist x (b+t•v) < δ}

theorem axisSet_eq_segment {n : ℕ} (b v : Space n) :
    axisSet b v = segment ℝ b (b+v) := by
  simp only [segment_eq_image',add_sub_cancel_left,axisSet]

theorem axisSet_compact {n : ℕ} (b v : Space n) : IsCompact (axisSet b v) :=
  isCompact_Icc.image (by fun_prop)

theorem axisSet_nonempty {n : ℕ} (b v : Space n) : (axisSet b v).Nonempty :=
  ⟨b,⟨0,by norm_num,by simp⟩⟩

theorem openCarrier_eq_add {n : ℕ} (b v : Space n) (δ : ℝ) :
    openCarrier b v δ = axisSet b v + ball 0 δ := by
  ext x
  constructor
  · rintro ⟨t,ht,hd⟩
    exact ⟨b+t•v,⟨t,ht,rfl⟩,x-(b+t•v),by simpa [dist_eq_norm] using hd,by abel_nf⟩
  · rintro ⟨a,⟨t,ht,rfl⟩,e,he,rfl⟩
    exact ⟨t,ht,by simpa [dist_eq_norm] using he⟩

theorem carrier_eq_add {n : ℕ} (T : UnitTube n) (δ : ℝ) :
    T.carrier δ = axisSet T.base T.direction + closedBall 0 δ := by
  ext x
  constructor
  · rintro ⟨t,ht,hd⟩
    exact ⟨T.axisPoint t,⟨t,ht,rfl⟩,x-T.axisPoint t,by simpa [dist_eq_norm] using hd,by abel_nf⟩
  · rintro ⟨a,⟨t,ht,rfl⟩,e,he,rfl⟩
    exact ⟨t,ht,by simpa [dist_eq_norm,UnitTube.axisPoint] using he⟩

theorem openCarrier_convex {n : ℕ} (b v : Space n) (δ : ℝ) :
    Convex ℝ (openCarrier b v δ) := by
  rw [openCarrier_eq_add,axisSet_eq_segment]
  exact (convex_segment _ _).add (convex_ball _ _)

theorem carrier_convex {n : ℕ} (T : UnitTube n) (δ : ℝ) :
    Convex ℝ (T.carrier δ) := by
  rw [carrier_eq_add,axisSet_eq_segment]
  exact (convex_segment _ _).add (convex_closedBall _ _)

theorem openCarrier_isOpen {n : ℕ} (b v : Space n) (δ : ℝ) :
    IsOpen (openCarrier b v δ) := by
  have heq : openCarrier b v δ = ⋃ t ∈ Icc (0:ℝ) 1, ball (b+t•v) δ := by
    ext x
    simp only [openCarrier,mem_ofPred_eq,mem_iUnion,mem_ball,exists_prop]
  rw [heq]
  exact isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => isOpen_ball))

theorem openCarrier_subset {n : ℕ} (T : UnitTube n) (δ : ℝ) :
    openCarrier T.base T.direction δ ⊆ T.carrier δ :=
  fun _ ⟨t,ht,hd⟩ => ⟨t,ht,hd.le⟩

/-- Every positive-radius closed capsule is the closure of its open capsule. -/
theorem closure_openCarrier {n : ℕ} (T : UnitTube n) {δ : ℝ} (hδ : 0 < δ) :
    closure (openCarrier T.base T.direction δ) = T.carrier δ := by
  apply Subset.antisymm
  · exact closure_minimal (openCarrier_subset T δ) (TubeVolume.carrier_compact T δ).isClosed
  · rintro x ⟨t,ht,hd⟩
    have hx : x ∈ closure (ball (T.axisPoint t) δ) := by
      rw [closure_ball _ hδ.ne']
      exact hd
    have hsub : ball (T.axisPoint t) δ ⊆ openCarrier T.base T.direction δ :=
      fun _y hy => ⟨t,ht,hy⟩
    exact closure_mono hsub hx

theorem openCarrier_frontier_null {n : ℕ} (b v : Space n) (δ : ℝ) :
    (volume : Measure (Space n)) (frontier (openCarrier b v δ)) = 0 :=
  (openCarrier_convex b v δ).addHaar_frontier volume

theorem carrier_frontier_null {n : ℕ} (T : UnitTube n) (δ : ℝ) :
    (volume : Measure (Space n)) (frontier (T.carrier δ)) = 0 :=
  (carrier_convex T δ).addHaar_frontier volume

/-- Exact a.e. equality, valid for arbitrary nonnegative measurable or
nonmeasurable integrands; no finite output integral is assumed. -/
theorem carrier_ae_eq_open {n : ℕ} (T : UnitTube n) {δ : ℝ} (hδ : 0 < δ) :
    T.carrier δ =ᵐ[volume] openCarrier T.base T.direction δ := by
  have hn : ∀ᵐ x ∂(volume : Measure (Space n)), x ∉ frontier (openCarrier T.base T.direction δ) :=
    ae_iff.mpr (by simpa using openCarrier_frontier_null T.base T.direction δ)
  filter_upwards [hn] with x hx
  apply propext
  constructor
  · intro hc
    by_contra ho
    apply hx
    rw [frontier,(openCarrier_isOpen T.base T.direction δ).interior_eq,closure_openCarrier T hδ]
    exact ⟨hc,ho⟩
  · exact fun ho => openCarrier_subset T δ ho

theorem carrier_lintegral_eq_open {n : ℕ} (T : UnitTube n) {δ : ℝ}
    (hδ : 0 < δ) (f : Space n → ℝ≥0∞) :
    (∫⁻ x in T.carrier δ, f x ∂volume) =
      ∫⁻ x in openCarrier T.base T.direction δ, f x ∂volume :=
  setLIntegral_congr (carrier_ae_eq_open T hδ)

theorem carrier_volume_eq_open {n : ℕ} (T : UnitTube n) {δ : ℝ} (hδ : 0 < δ) :
    (volume : Measure (Space n)) (T.carrier δ) =
      volume (openCarrier T.base T.direction δ) :=
  measure_congr (carrier_ae_eq_open T hδ)

/-- Membership in the open capsule is open jointly in its actual base and
direction; no continuity of the test integrand is involved. -/
theorem parameter_membership_isOpen {n : ℕ} (x : Space n) (δ : ℝ) :
    IsOpen {p : Space n × Space n | x ∈ openCarrier p.1 p.2 δ} := by
  have heq : {p : Space n × Space n | x ∈ openCarrier p.1 p.2 δ} =
      ⋃ t ∈ Icc (0:ℝ) 1, {p : Space n × Space n | dist x (p.1+t•p.2) < δ} := by
    ext p
    simp only [mem_ofPred_eq,openCarrier,mem_iUnion,exists_prop]
  rw [heq]
  apply isOpen_iUnion
  intro t
  apply isOpen_iUnion
  intro _ht
  exact isOpen_lt (by fun_prop) continuous_const

end
end KakeyaFormal.TubeOpenCarrier
