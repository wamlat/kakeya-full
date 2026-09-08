import SlabNormalization

/-! Actual centered selected lift cells are attached to their original legal
endpoint samples. Original energy positions are recovered from common group
translations, with the slab index determined by the original cell center. -/
namespace KakeyaFormal.SelectedLiftWitness
open Finset PivotWitnesses PivotSupport PivotOutputCount SelectedFiberLift SlabNormalization
open EuclideanSplit
open scoped BigOperators
noncomputable section
open Classical

/-- The full centered grid label, with the vertical coordinate first in the
Euclidean space, represented in the horizontal/vertical convention of energy. -/
def splitCell {k : ℕ} (z : Cell (k+1)) : LiftCell k := (fun i => z i.succ,z 0)

theorem splitCell_injective {k : ℕ} : Function.Injective (@splitCell k) := by
  intro x y h
  ext i
  cases i using Fin.cases with
  | zero => exact congrArg Prod.snd h
  | succ i => exact congrFun (congrArg Prod.fst h) i

def errorConstant (k : ℕ) (width : ℝ) : ℝ := width+((k : ℝ)+1)/2

theorem errorConstant_nonneg (k : ℕ) {width : ℝ} (hw : 0 ≤ width) :
    0 ≤ errorConstant k width := by dsimp [errorConstant]; positivity

/-- The horizontal and vertical errors of the actual centered lifted cell
are derived from full Euclidean grid rounding, not assumed independently. -/
theorem split_lift_rounding {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (reference s : LabeledPair a δ width fc sc) (hδ : 0 < δ) :
    ‖cellCenter δ (splitCell (liftedCell reference s)).1-s.endpoints.secondPoint‖ ≤ ((k : ℝ)+1)*δ/2 ∧
      |δ*((splitCell (liftedCell reference s)).2 : ℝ)-
        s.endpoints.secondCoord/reference.endpoints.coefficient| ≤ ((k : ℝ)+1)*δ/2 := by
  have hr := GridCells.cell_center_distance (GridCells.gridCell_covers hδ (liftedPoint reference s))
  change dist (liftedPoint reference s) (cellCenter δ (liftedCell reference s)) ≤ _ at hr
  have hr' : ‖cellCenter δ (liftedCell reference s)-liftedPoint reference s‖ ≤ ((k : ℝ)+1)*δ/2 := by
    simpa only [dist_eq_norm,norm_sub_rev,Nat.cast_add,Nat.cast_one] using hr
  constructor
  · have ht := tail_norm_le (cellCenter δ (liftedCell reference s)-liftedPoint reference s)
    rw [tail_sub] at ht
    simp only [liftedPoint,tail_cons] at ht
    change ‖cellCenter δ (splitCell (liftedCell reference s)).1-s.endpoints.secondPoint‖ ≤ _ at ht
    exact ht.trans hr'
  · have hh := GridGeometry.coordinate_dist_le (cellCenter δ (liftedCell reference s)) (liftedPoint reference s) 0
    exact hh.trans hr'

/-- Build the exact closing-energy witness from one selected original pair
and its actual centered lifted cell. The common pivot equality is the only
fiber condition; endpoint and lift label closeness are all derived. -/
def attach {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (reference s : LabeledPair a δ width fc sc)
    (intermediate : Cell k) (hδ : 0 < δ) (hw : 0 ≤ width)
    (hpivot : s.pivotLabel=reference.pivotLabel)
    (hintermediate : dist (cellCenter δ intermediate) (a.vertex+a.intermediate • a.first) ≤ width*δ) :
    AttachedSample k δ kap (errorConstant k width) := by
  have hwC : width*δ ≤ errorConstant k width*δ := by
    have hdim : 0 ≤ ((k : ℝ)+1)/2 := by positivity
    dsimp [errorConstant]
    nlinarith
  have hkC : (k : ℝ)*δ/2 ≤ errorConstant k width*δ := by
    dsimp [errorConstant]
    nlinarith
  have hk1C : ((k : ℝ)+1)*δ/2 ≤ errorConstant k width*δ := by
    dsimp [errorConstant]
    nlinarith
  have href : ‖cellCenter δ reference.pivotLabel-reference.endpoints.pivot‖ ≤ errorConstant k width*δ := by
    simpa only [dist_eq_norm,norm_sub_rev] using (reference.pivot_rounding hδ).trans hkC
  have hs : ‖cellCenter δ reference.pivotLabel-s.endpoints.pivot‖ ≤ errorConstant k width*δ := by
    have hh := (s.pivot_rounding hδ).trans hkC
    rw [hpivot] at hh
    simpa only [dist_eq_norm,norm_sub_rev] using hh
  exact {
    fiber := {
      angle := a
      reference := reference.endpoints
      pivotLabel := reference.pivotLabel
      intermediateLabel := intermediate
      reference_close := href
      intermediate_close := hintermediate.trans hwC
    }
    endpoints := s.endpoints
    firstLabel := s.firstLabel
    secondLabel := s.secondLabel
    liftLabel := splitCell (liftedCell reference s)
    first_close := s.first_close.trans hwC
    second_close := s.second_close.trans hwC
    pivot_close := hs
    horizontal_close := (split_lift_rounding reference s hδ).1.trans hk1C
    vertical_close := (split_lift_rounding reference s hδ).2.trans hk1C
  }

/-- Actual original triple and original lifted cell; the construction neither
rounds again nor replaces the selected sample by one from another fiber. -/
theorem attach_label {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (reference s : LabeledPair a δ width fc sc)
    (intermediate : Cell k) (hδ : 0 < δ) (hw : 0 ≤ width)
    (hpivot : s.pivotLabel=reference.pivotLabel)
    (hintermediate : dist (cellCenter δ intermediate) (a.vertex+a.intermediate • a.first) ≤ width*δ) :
    (attach reference s intermediate hδ hw hpivot hintermediate).label =
      ((s.firstLabel,s.secondLabel,reference.pivotLabel),splitCell (liftedCell reference s)) := rfl

/-- Undo the actual groupwise integral vertical label shift. -/
def unshiftCell {k : ℕ} (δ : ℝ) (j : ℕ) (z : Cell (k+1)) : Cell (k+1) :=
  fun i => z i+((Fin.cons (shiftIndex δ j) (fun _ : Fin k => (0:ℤ))) : Cell (k+1)) i

theorem unshift_shift {k : ℕ} (δ : ℝ) (j : ℕ) (z : Cell (k+1)) :
    unshiftCell δ j (shiftCell δ j z)=z := by
  ext i
  simp only [unshiftCell,shiftCell,Rescaling.shiftLabel,sub_add_cancel]

theorem shift_unshift {k : ℕ} (δ : ℝ) (j : ℕ) (z : Cell (k+1)) :
    shiftCell δ j (unshiftCell δ j z)=z := by
  ext i
  simp only [unshiftCell,shiftCell,Rescaling.shiftLabel,add_sub_cancel_right]

abbrev GroupPosition (k : ℕ) := (Cell k × ℕ) × Cell (k+1)

def originalCell {k : ℕ} (δ : ℝ) (p : GroupPosition k) : Cell (k+1) :=
  unshiftCell δ p.1.2 p.2

def originalPosition {k : ℕ} (δ : ℝ) (p : GroupPosition k) : Cell k × LiftCell k :=
  (p.1.1,splitCell (originalCell δ p))

def LegalPosition {k : ℕ} (δ : ℝ) (p : GroupPosition k) : Prop :=
  (p.1.2 : ℝ) ≤ δ*((originalCell δ p) 0 : ℝ) ∧
    δ*((originalCell δ p) 0 : ℝ) < (p.1.2 : ℝ)+1

theorem shifted_position_legal {k : ℕ} {δ : ℝ} (group : Cell k × ℕ) (z : Cell (k+1))
    (hz : (group.2 : ℝ) ≤ δ*(z 0 : ℝ) ∧ δ*(z 0 : ℝ) < (group.2 : ℝ)+1) :
    LegalPosition δ (group,shiftCell δ group.2 z) := by
  simpa only [LegalPosition,originalCell,unshift_shift] using hz

theorem shifted_original_position {k : ℕ} (δ : ℝ) (group : Cell k × ℕ) (z : Cell (k+1)) :
    originalPosition δ (group,shiftCell δ group.2 z)=(group.1,splitCell z) := by
  simp only [originalPosition,originalCell,unshift_shift]

/-- Recovering the slab index uses its actual center interval. Thus no extra
slab multiplicity occurs among the original closing-energy positions. -/
theorem originalPosition_injective {k : ℕ} {δ : ℝ} :
    Set.InjOn (originalPosition (k := k) δ) {p | LegalPosition δ p} := by
  intro p hp q hq he
  have hpivot : p.1.1=q.1.1 := congrArg (fun x : Cell k × LiftCell k => x.1) he
  have hcell : originalCell δ p=originalCell δ q := splitCell_injective (congrArg Prod.snd he)
  change (p.1.2 : ℝ) ≤ δ*((originalCell δ p) 0 : ℝ) ∧
    δ*((originalCell δ p) 0 : ℝ) < (p.1.2 : ℝ)+1 at hp
  change (q.1.2 : ℝ) ≤ δ*((originalCell δ q) 0 : ℝ) ∧
    δ*((originalCell δ q) 0 : ℝ) < (q.1.2 : ℝ)+1 at hq
  rw [hcell] at hp
  have hj : p.1.2=q.1.2 := by
    have hle (a b : ℕ) (hab : (a : ℝ)<(b : ℝ)+1) : a ≤ b := by
      have hh : a < b+1 := by exact_mod_cast hab
      omega
    exact Nat.le_antisymm (hle _ _ (by linarith)) (hle _ _ (by linarith))
  have hshift : p.2=q.2 := by
    have hh := congrArg (shiftCell δ p.1.2) hcell
    simpa only [originalCell,← hj,shift_unshift] using hh
  exact Prod.ext (Prod.ext hpivot hj) hshift


/-- Relabeling actual finite energy positions injectively leaves every fiber
multiplicity and the whole sum of squared multiplicities unchanged. -/
theorem relabel_energy {A B D : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq D] (S : Finset A) (f : A → B) (g : B → D)
    (hinj : Set.InjOn g (S.image f : Set B)) :
    (∑ q ∈ S.image (fun x => g (f x)), ((S.filter (fun x => g (f x)=q)).card : ℝ)^2) =
      ∑ p ∈ S.image f, ((S.filter (fun x => f x=p)).card : ℝ)^2 := by
  have himage : S.image (fun x => g (f x))=(S.image f).image g := (image_image).symm
  rw [himage,sum_image]
  · apply sum_congr rfl
    intro p hp
    have hf : S.filter (fun x => g (f x)=g p)=S.filter (fun x => f x=p) := by
      ext x
      simp only [mem_filter]
      constructor
      · rintro ⟨hx,he⟩
        exact ⟨hx,hinj (mem_image.mpr ⟨x,hx,rfl⟩) hp he⟩
      · rintro ⟨hx,he⟩
        exact ⟨hx,congrArg g he⟩
    rw [hf]
  · exact hinj

/-- The actual grouped normalized-cell energy is exactly the original
pivot/lifted-cell energy. The slab index costs no independent multiplicity. -/
theorem grouped_energy_equals_original {I : Type*} {k : ℕ} {δ : ℝ}
    (S : Finset I) (position : I → GroupPosition k)
    (hlegal : ∀ i ∈ S, LegalPosition δ (position i)) :
    (∑ q ∈ S.image (fun i => originalPosition δ (position i)),
      ((S.filter (fun i => originalPosition δ (position i)=q)).card : ℝ)^2) =
      ∑ p ∈ S.image position, ((S.filter (fun i => position i=p)).card : ℝ)^2 := by
  apply relabel_energy S position (originalPosition δ)
  intro p hp q hq he
  have hmem (p) (hp : p ∈ S.image position) : LegalPosition δ p := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact hlegal i hi
  exact originalPosition_injective (hmem p hp) (hmem q hq) he

/-- An actual retained normalized cell has an original sample in the same
reference fiber. Undoing the group shift recovers its literal old lifted label. -/
theorem retained_cell_sample {k : ℕ} {kap δ width : ℝ} {a : Angle k kap}
    {fc sc : Cell k → ℝ} (reference : LabeledPair a δ width fc sc)
    (raw : Finset (LabeledPair a δ width fc sc)) (selected : Finset (Cell (k+1)))
    (hselected : selected ⊆ liftedCells reference raw) (j : ℕ)
    (z : Cell (k+1)) (hz : z ∈ selected.image (shiftCell δ j)) :
    ∃ s ∈ raw, liftedCell reference s=unshiftCell δ j z := by
  obtain ⟨q,hq,rfl⟩ := mem_image.mp hz
  obtain ⟨s,hs,hcell⟩ := mem_image.mp (hselected hq)
  exact ⟨s,hs,by simpa only [unshift_shift] using hcell⟩


/-- Summing actual support-label multiplicities over one energy position is
exactly the degree of that position in the original incidence set. -/
theorem fiber_weight_sum {A B D : Type*} [DecidableEq A] [DecidableEq B] [DecidableEq D] (S : Finset A) (f : A → B) (g : B → D) (p : D) :
    (∑ b ∈ (S.image f).filter (fun b => g b=p), ((S.filter (fun x => f x=b)).card : ℝ)) =
      ((S.filter (fun x => g (f x)=p)).card : ℝ) := by
  let T := S.filter (fun x => g (f x)=p)
  let U := (S.image f).filter (fun b => g b=p)
  have hmap : ∀ x ∈ T, f x ∈ U := by
    intro x hx
    obtain ⟨hxS,hxp⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_image.mpr ⟨x,hxS,rfl⟩,hxp⟩
  have hsum : (∑ b ∈ U, ((T.filter (fun x => f x=b)).card : ℝ))=(T.card : ℝ) := by
    simpa only [sum_const,nsmul_eq_mul,mul_one] using
      (sum_fiberwise_of_maps_to (s := T) (t := U) (g := f) hmap (fun _ => (1:ℝ)))
  have hf (b) (hb : b ∈ U) : T.filter (fun x => f x=b)=S.filter (fun x => f x=b) := by
    ext x
    simp only [T,mem_filter]
    constructor
    · rintro ⟨⟨hx,_⟩,he⟩
      exact ⟨hx,he⟩
    · rintro ⟨hx,he⟩
      exact ⟨⟨hx,by rw [he]; exact (mem_filter.mp hb).2⟩,he⟩
  change (∑ b ∈ U, ((S.filter (fun x => f x=b)).card : ℝ))=(T.card : ℝ)
  calc
    _ = ∑ b ∈ U, ((T.filter (fun x => f x=b)).card : ℝ) := by
      apply sum_congr rfl
      intro b hb
      rw [hf b hb]
    _ = _ := hsum

/-- The existing actual geometric support theorem in the precise degree-energy
form used by grouped high-cell pruning. No energy-comparison hypothesis remains. -/
theorem attached_sample_degree_energy {I : Type*} {k : ℕ} {δ kap C : ℝ}
    (S : Finset I) (sample : I → AttachedSample k δ kap C) (occupied : Finset (Cell k))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hscale : 2*C*δ ≤ kap^5/4)
    (hend : ∀ i ∈ S, (sample i).firstLabel ∈ occupied ∧ (sample i).secondLabel ∈ occupied) :
    (S.card : ℝ)^2 ≤
      ((occupied.card : ℝ)^2*(pivotCount k δ (4*C) (2+2*C) : ℝ)*
        (liftCount k δ (2*C*δ) (4*(2*C*δ)/kap^2) (kap^3) (2/kap) : ℝ))*
      ∑ p ∈ S.image (fun i => energyPosition (sample i).label),
        ((S.filter (fun i => energyPosition (sample i).label=p)).card : ℝ)^2 := by
  have hh := finite_sample_energy S sample occupied hδ hδ1 hC hk hk1 hscale hend
  have hid : (∑ pos ∈ (S.image (fun i => (sample i).label)).image energyPosition,
      (∑ p ∈ S.image (fun i => (sample i).label) with energyPosition p=pos,
        incidenceWeight S sample p)^2) =
      ∑ p ∈ S.image (fun i => energyPosition (sample i).label),
        ((S.filter (fun i => energyPosition (sample i).label=p)).card : ℝ)^2 := by
    rw [image_image]
    apply sum_congr rfl
    intro p hp
    congr 1
    exact fiber_weight_sum S (fun i => (sample i).label) energyPosition p
  rwa [hid] at hh


/-- Only the actually occupied incidence values matter when comparing two
position maps. Equality is not required away from the retained set. -/
theorem energy_congr {I P : Type*} [DecidableEq I] [DecidableEq P]
    (S : Finset I) (f g : I → P) (hfg : ∀ i ∈ S, f i=g i) :
    (∑ p ∈ S.image f, ((S.filter (fun i => f i=p)).card : ℝ)^2) =
      ∑ p ∈ S.image g, ((S.filter (fun i => g i=p)).card : ℝ)^2 := by
  have himage : S.image f=S.image g := image_congr hfg
  rw [himage]
  apply sum_congr rfl
  intro p hp
  have hf : S.filter (fun i => f i=p)=S.filter (fun i => g i=p) := by
    apply filter_congr
    intro i hi
    rw [hfg i hi]
  rw [hf]

/-- Closing lower energy in the exact original group/normalized-cell positions
used by high-cell pruning. Actual legal attached samples supply every geometric
witness; undoing the common grid shift and the center-defined slab identity pay
no energy factor. -/
theorem grouped_attached_sample_energy {I : Type*} {k : ℕ} {δ kap C : ℝ}
    (S : Finset I) (sample : I → AttachedSample k δ kap C)
    (position : I → GroupPosition k) (occupied : Finset (Cell k))
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hC : 0 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1)
    (hscale : 2*C*δ ≤ kap^5/4)
    (hend : ∀ i ∈ S, (sample i).firstLabel ∈ occupied ∧ (sample i).secondLabel ∈ occupied)
    (hlegal : ∀ i ∈ S, LegalPosition δ (position i))
    (hposition : ∀ i ∈ S, energyPosition (sample i).label=originalPosition δ (position i)) :
    (S.card : ℝ)^2 ≤
      ((occupied.card : ℝ)^2*(pivotCount k δ (4*C) (2+2*C) : ℝ)*
        (liftCount k δ (2*C*δ) (4*(2*C*δ)/kap^2) (kap^3) (2/kap) : ℝ))*
      ∑ p ∈ S.image position, ((S.filter (fun i => position i=p)).card : ℝ)^2 := by
  have hh := attached_sample_degree_energy S sample occupied hδ hδ1 hC hk hk1 hscale hend
  rw [energy_congr S (fun i => energyPosition (sample i).label)
    (fun i => originalPosition δ (position i)) hposition,
    grouped_energy_equals_original S position hlegal] at hh
  exact hh

end
end KakeyaFormal.SelectedLiftWitness

#print axioms KakeyaFormal.SelectedLiftWitness.attach
#print axioms KakeyaFormal.SelectedLiftWitness.attach_label
#print axioms KakeyaFormal.SelectedLiftWitness.originalPosition_injective

#print axioms KakeyaFormal.SelectedLiftWitness.grouped_energy_equals_original
#print axioms KakeyaFormal.SelectedLiftWitness.retained_cell_sample

#print axioms KakeyaFormal.SelectedLiftWitness.attached_sample_degree_energy

#print axioms KakeyaFormal.SelectedLiftWitness.grouped_attached_sample_energy
