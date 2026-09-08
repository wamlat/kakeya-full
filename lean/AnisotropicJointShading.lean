import AnisotropicTransport

/-! Joint full/marked unit-segment selection. The actual maximizing segment is
chosen using the marked shading; both shadings are restricted to that one
carrier. No independent full-shading maximizer is used. -/
namespace KakeyaFormal.AnisotropicJointShading
open SpatialAngular AnisotropicRescaling AnisotropicVolume AnisotropicShading MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
open Classical

/-- The full output on exactly the segment maximizing marked mass. -/
def full {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    (Full G : Set (Space (k+1))) : Set (Space (k+1)) :=
  segmentSet u htau q T width δ Full (bestSegment u htau q T angular width δ G)

/-- The marks and full shading use the same deterministic choice. -/
def marks {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    (G : Set (Space (k+1))) : Set (Space (k+1)) :=
  selectedSet u htau q T angular width δ G

/-- The original tube index is retained once, with the common marked choice. -/
def family {k M : ℕ} (F : TubeFamily (k+1) M) (u : Space (k+1)) {tau : ℝ}
    (htau : tau ≠ 0) (q : Cell k) (angular width δ : ℝ) (G : Fin M → Set (Space (k+1))) :
    TubeFamily (k+1) M :=
  AnisotropicCap.family F u htau q
    (fun i => bestSegment u htau q (F.tube i) angular width δ (G i)) (fun _ => ∅)

theorem nested {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    {Full G : Set (Space (k+1))} (hsub : G ⊆ Full) :
    marks u htau q T angular width δ G ⊆ full u htau q T angular width δ Full G :=
  Set.inter_subset_inter_left _ (Set.image_mono hsub)

theorem full_subset {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    (Full G : Set (Space (k+1))) :
    full u htau q T angular width δ Full G ⊆ normalizeBox u tau q '' Full ∧
    full u htau q T angular width δ Full G ⊆
      (transformedTube u htau q T (bestSegment u htau q T angular width δ G)).carrier (width*(δ/tau)) :=
  ⟨Set.inter_subset_left,Set.inter_subset_right⟩

theorem marks_subset {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ) (G : Set (Space (k+1))) :
    marks u htau q T angular width δ G ⊆ normalizeBox u tau q '' G :=
  Set.inter_subset_left

theorem full_measurable {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    {Full : Set (Space (k+1))} (G : Set (Space (k+1))) (hFull : MeasurableSet Full) :
    MeasurableSet (full u htau q T angular width δ Full G) :=
  segmentSet_measurable u htau q T width δ hFull _

theorem marks_measurable {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    {G : Set (Space (k+1))} (hG : MeasurableSet G) :
    MeasurableSet (marks u htau q T angular width δ G) :=
  selected_measurable u htau q T angular width δ hG

theorem full_finite {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    (Full G : Set (Space (k+1))) : volume (full u htau q T angular width δ Full G) ≠ ∞ :=
  segmentSet_finite u htau q T width δ Full _

theorem marks_finite {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : tau ≠ 0)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    (G : Set (Space (k+1))) : volume (marks u htau q T angular width δ G) ≠ ∞ :=
  selected_finite u htau q T angular width δ G

/-- Each tube retains at least 1/N of its original marked mass after the exact
Jacobian factor. No lower marked density on that tube is assumed. -/
theorem marks_mass_lower {k : ℕ} (u : Space (k+1)) {tau angular width δ : ℝ}
    (hu : ‖u‖=1) (htau : 0 < tau) (htau1 : tau ≤ 1) (q : Cell k)
    (T : UnitTube (k+1)) (Full G : Set (Space (k+1)))
    (hcap : projectiveDistance T.direction u ≤ angular*tau)
    (hFull : Full ⊆ T.carrier (width*δ)) (hsub : G ⊆ Full) :
    (volume : Measure (Space (k+1))).real G/(tau^k*(segmentCount angular:ℝ)) ≤
      (volume : Measure (Space (k+1))).real (marks u htau.ne' q T angular width δ G) :=
  selected_mass_lower u hu htau htau1 q T G hcap (hsub.trans hFull)

/-- The full upper mass is inherited from the exact original full set. -/
theorem full_mass_upper {k : ℕ} (u : Space (k+1)) {tau : ℝ} (htau : 0 < tau)
    (q : Cell k) (T : UnitTube (k+1)) (angular width δ : ℝ)
    (Full G : Set (Space (k+1))) (hFull : volume Full ≠ ∞) :
    (volume : Measure (Space (k+1))).real (full u htau.ne' q T angular width δ Full G) ≤
      (volume : Measure (Space (k+1))).real Full/tau^k := by
  have hh := measureReal_mono (full_subset u htau.ne' q T angular width δ Full G).1
    (normalizeBox_volume_finite u htau q hFull)
  rwa [normalizeBox_realVolume u htau] at hh

/-- Crucial restricted-union boundary: full outputs are subsets of the common
image of the actual input Full union, even when Full was itself a restricted
angular reference shading. -/
theorem full_union_subset {k : ℕ} {I : Type*} (u : Space (k+1)) {tau : ℝ}
    (htau : tau ≠ 0) (q : Cell k) (T : I → UnitTube (k+1)) (angular width δ : ℝ)
    (Full G : I → Set (Space (k+1))) :
    (⋃ i, full u htau q (T i) angular width δ (Full i) (G i)) ⊆
      normalizeBox u tau q '' (⋃ i, Full i) := by
  intro x hx
  obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y,hy,rfl⟩ := (full_subset u htau q (T i) angular width δ (Full i) (G i)).1 hi
  exact ⟨y,Set.mem_iUnion.mpr ⟨i,hy⟩,rfl⟩

theorem full_union_volume {k : ℕ} {I : Type*} [Fintype I] (u : Space (k+1)) {tau : ℝ}
    (htau : 0 < tau) (q : Cell k) (T : I → UnitTube (k+1)) (angular width δ : ℝ)
    (Full G : I → Set (Space (k+1))) (hFull : ∀ i, volume (Full i) ≠ ∞) :
    (volume : Measure (Space (k+1))).real (⋃ i, full u htau.ne' q (T i) angular width δ (Full i) (G i)) ≤
      (volume : Measure (Space (k+1))).real (⋃ i, Full i)/tau^k := by
  have hU : volume (⋃ i, Full i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ:=volume)
      (s:=Set.univ) (f:=Full) (Set.toFinite _) (fun i _ => hFull i)
  have hh := measureReal_mono (full_union_subset u htau.ne' q T angular width δ Full G)
    (normalizeBox_volume_finite u htau q hU)
  rwa [normalizeBox_realVolume u htau] at hh

/-- Summed marked mass survives by a fixed segment-count factor; sparse or
empty individual marks require no exception. -/
theorem total_marks_lower {k M : ℕ} (u : Space (k+1)) {tau angular width δ : ℝ}
    (hu : ‖u‖=1) (htau : 0 < tau) (htau1 : tau ≤ 1) (q : Cell k)
    (T : Fin M → UnitTube (k+1)) (Full G : Fin M → Set (Space (k+1)))
    (hcap : ∀ i, projectiveDistance (T i).direction u ≤ angular*tau)
    (hFull : ∀ i, Full i ⊆ (T i).carrier (width*δ)) (hsub : ∀ i, G i ⊆ Full i) :
    (∑ i, (volume : Measure (Space (k+1))).real (G i))/(tau^k*(segmentCount angular:ℝ)) ≤
      ∑ i, (volume : Measure (Space (k+1))).real (marks u htau.ne' q (T i) angular width δ (G i)) := by
  rw [Finset.sum_div]
  exact Finset.sum_le_sum (fun i _ => marks_mass_lower u hu htau htau1 q (T i) (Full i) (G i)
    (hcap i) (hFull i) (hsub i))

/-- An actual source total marked budget supplies the recovery budget after
joint selection, with eta/N and lambda/tau^k. -/
theorem total_marks_budget {k M : ℕ} (u : Space (k+1)) {tau angular width δ eta lam : ℝ}
    (hu : ‖u‖=1) (htau : 0 < tau) (htau1 : tau ≤ 1) (q : Cell k)
    (T : Fin M → UnitTube (k+1)) (Full G : Fin M → Set (Space (k+1)))
    (hcap : ∀ i, projectiveDistance (T i).direction u ≤ angular*tau)
    (hFull : ∀ i, Full i ⊆ (T i).carrier (width*δ)) (hsub : ∀ i, G i ⊆ Full i)
    (hmass : eta*lam*(M:ℝ) ≤ ∑ i, (volume : Measure (Space (k+1))).real (G i)) :
    (eta/(segmentCount angular:ℝ))*(lam/tau^k)*(M:ℝ) ≤
      ∑ i, (volume : Measure (Space (k+1))).real (marks u htau.ne' q (T i) angular width δ (G i)) := by
  have hn : (0:ℝ) < segmentCount angular := Nat.cast_pos.mpr (segmentCount_pos angular)
  have hh := div_le_div_of_nonneg_right hmass (mul_pos (pow_pos htau k) hn).le
  have hh' : (eta/(segmentCount angular:ℝ))*(lam/tau^k)*(M:ℝ) ≤
      (∑ i, (volume : Measure (Space (k+1))).real (G i))/(tau^k*(segmentCount angular:ℝ)) := by
    convert hh using 1 <;> first | rfl | ring
  exact hh'.trans (total_marks_lower u hu htau htau1 q T Full G hcap hFull hsub)

end
end KakeyaFormal.AnisotropicJointShading
