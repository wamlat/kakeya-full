import SpatialSplitting

/-! Actual simultaneous spatial partition and proportional whole-cell restoration
of the previously constructed angular shadings. -/
namespace KakeyaFormal.SpatialAssignment
open KakeyaFormal.SpatialAngular KakeyaFormal.SpatialSplitting
open KakeyaFormal.AngularDecomposition KakeyaFormal.AngularAssignment
noncomputable section

/-- Actual original index incidence of a finite shading at a full grid cell. -/
def cellDirections {k M : ℕ} (shading : Fin M → Finset (Cell k)) (z : Cell k) : Finset (Fin M) := by
  classical
  exact Finset.univ.filter (fun i => z ∈ shading i)

/-- Actual spatially split finite shading; restoration acts on whole original cells. -/
def splitShading {k M : ℕ} {γ : Type*} [DecidableEq γ]
    (shading : Fin M → Finset (Cell k)) (label : Fin M → γ) (B : ℝ) (q : γ)
    (i : Fin M) : Finset (Cell k) := by
  classical
  exact (shading i).filter (fun z => i ∈ restore (cellDirections shading z) label B q)

theorem splitShading_subset {k M : ℕ} {γ : Type*} [DecidableEq γ]
    (shading : Fin M → Finset (Cell k)) (label : Fin M → γ) (B : ℝ) (q : γ) (i : Fin M) :
    splitShading shading label B q i ⊆ shading i := Finset.filter_subset _ _

/-- The spatially split shading's full-cell incidence is exactly the restored label fiber. -/
theorem splitShading_incidence {k M : ℕ} {γ : Type*} [DecidableEq γ]
    (shading : Fin M → Finset (Cell k)) (label : Fin M → γ) (B : ℝ) (q : γ) (z : Cell k) :
    cellDirections (splitShading shading label B q) z = restore (cellDirections shading z) label B q := by
  classical
  ext i
  constructor
  · intro hi
    have hz := (Finset.mem_filter.mp hi).2
    exact (Finset.mem_filter.mp hz).2
  · intro hi
    have hp := restore_subset_parent (cellDirections shading z) label B q hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).2,hi⟩⟩

/-- One spatial label is assigned to an entire original tube. -/
theorem splitShading_label {k M : ℕ} {γ : Type*} [DecidableEq γ]
    (shading : Fin M → Finset (Cell k)) (label : Fin M → γ) (B : ℝ) (q : γ)
    (i : Fin M) (hne : (splitShading shading label B q i).Nonempty) : label i = q := by
  obtain ⟨z,hz⟩ := hne
  exact restore_label (cellDirections shading z) label B q (Finset.mem_filter.mp hz).2

/-- Exact incidence double counting for arbitrary actual finite shadings. -/
theorem shading_double_count {k M : ℕ} (cells : Finset (Cell k))
    (shading : Fin M → Finset (Cell k)) (hsub : ∀ i, shading i ⊆ cells) :
    (∑ i : Fin M, ((shading i).card : ℝ)) = ∑ z ∈ cells, ((cellDirections shading z).card : ℝ) := by
  classical
  have hrow (i : Fin M) : cells.filter (fun z => i ∈ cellDirections shading z) = shading i := by
    ext z
    simp only [cellDirections,Finset.mem_filter,Finset.mem_univ,true_and]
    exact and_iff_right_of_imp (fun hz => hsub i hz)
  have h := sum_row_cards cells (cellDirections shading)
  simp_rw [hrow] at h
  exact_mod_cast h.symm

/-- The spatial overlap constant depends only on dimension and original fixed width. -/
def spatialOverlap (k : ℕ) (width : ℝ) : ℕ :=
  (2*Nat.ceil (((k:ℝ)+width+3)/2)+3)^k

theorem spatialOverlap_pos (k : ℕ) (width : ℝ) : 0 < spatialOverlap k width := by
  unfold spatialOverlap
  positivity

/-- The actual occupied spatial labels at each angular-parent cell satisfy the
required fixed overlap bound, using original admissibility and original tube geometry. -/
theorem cell_spatial_label_count {k M : ℕ} (F : TubeFamily (k+1) M)
    (shading : Fin M → Finset (Cell (k+1))) (u : Space (k+1)) (hu : ‖u‖ = 1)
    {δ tau width : ℝ} (htau : 0 < tau) (hdr : δ ≤ tau) (hw : 0 ≤ width)
    (hadmissible : F.Admissible width δ)
    (hsub : ∀ i, shading i ⊆ F.shade i)
    (hcap : ∀ i, (shading i).Nonempty → projectiveDistance (F.tube i).direction u ≤ 3*tau)
    (z : Cell (k+1)) :
    ((cellDirections shading z).image (fun i => spatialLabel u tau (F.tube i))).card ≤ spatialOverlap k width := by
  classical
  apply occupied_spatial_labels u hu F.tube (cellDirections shading z) (cellCenter δ z) htau hdr hw (by norm_num)
  · intro i hi
    exact hcap i ⟨z,(Finset.mem_filter.mp hi).2⟩
  · intro i hi
    exact hadmissible i z (hsub i (Finset.mem_filter.mp hi).2)

/-- Actual parallel spatial assignment and proportional restoration of arbitrary
already-broad angular shadings. Spatial labels and covering geometry are constructed
from the original tube bases, not supplied as an overlap hypothesis. -/
theorem spatial_shading_assignment {k M : ℕ} (F : TubeFamily (k+1) M)
    (cells : Finset (Cell (k+1))) (net : Finset (Fin M))
    (shading : Fin M → Fin M → Finset (Cell (k+1)))
    {δ tau width R beta K H : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (htau : 0 < tau) (hdr : δ ≤ tau) (hw : 0 ≤ width) (hK : 0 ≤ K)
    (hadmissible : F.Admissible width δ) (hbounded : F.Bounded R)
    (hsub : ∀ g ∈ net, ∀ i, shading g i ⊆ F.shade i ∧ shading g i ⊆ cells)
    (hcap : ∀ g ∈ net, ∀ i, (shading g i).Nonempty →
      projectiveDistance (F.tube i).direction (F.tube g).direction ≤ 3*tau)
    (hbroad : ∀ z : Cell (k+1), ∀ g ∈ net, Broad F (cellDirections (shading g) z) δ beta tau K)
    (hover : ∀ z : Cell (k+1), ((net.filter (fun g => (cellDirections (shading g) z).Nonempty)).card : ℝ) ≤ H) :
    let B : ℝ := spatialOverlap k width
    ∃ labels : Fin M → Finset (Cell k),
      ∃ output : Fin M → Cell k → Fin M → Finset (Cell (k+1)),
      (∀ g ∈ net, ∀ q i, output g q i ⊆ shading g i ∧ output g q i ⊆ cells) ∧
      (∀ g q i, (output g q i).Nonempty → spatialLabel (F.tube g).direction tau (F.tube i) = q) ∧
      (∀ g ∈ net, ∀ q i, (output g q i).Nonempty →
        (F.tube i).carrier (width*δ) ⊆ parallelBox (F.tube g).direction tau q
          (R+1+width) ((k:ℝ)+width+3)) ∧
      (3/4:ℝ)*(∑ g ∈ net, ∑ i : Fin M, ((shading g i).card : ℝ)) ≤
        ∑ g ∈ net, ∑ q ∈ labels g, ∑ i : Fin M, ((output g q i).card : ℝ) ∧
      (∀ z : Cell (k+1), ∀ g ∈ net, ∀ q ∈ labels g,
        Broad F (cellDirections (output g q) z) δ beta tau (K*(4*B))) ∧
      ∀ z : Cell (k+1),
        (∑ g ∈ net, (({q ∈ labels g | (cellDirections (output g q) z).Nonempty}).card : ℝ)) ≤ B*H := by
  classical
  let B : ℝ := spatialOverlap k width
  have hB : 0 < B := by
    dsimp [B]
    exact_mod_cast spatialOverlap_pos k width
  let label := fun g i => spatialLabel (F.tube g).direction tau (F.tube i)
  let labels := fun g => (Finset.univ : Finset (Fin M)).image (label g)
  let parent := fun g z => cellDirections (shading g) z
  let output := fun g q => splitShading (shading g) (label g) B q
  have houtput (g : Fin M) (q : Cell k) (z : Cell (k+1)) :
      cellDirections (output g q) z = restore (parent g z) (label g) B q :=
    splitShading_incidence (shading g) (label g) B q z
  have hlabels (g : Fin M) (z : Cell (k+1)) : (parent g z).image (label g) ⊆ labels g :=
    Finset.image_subset_image (Finset.subset_univ _)
  have hcount (g : Fin M) (hg : g ∈ net) (z : Cell (k+1)) :
      (((parent g z).image (label g)).card : ℝ) ≤ B := by
    dsimp [parent,label,B]
    exact_mod_cast cell_spatial_label_count F (shading g) (F.tube g).direction (F.tube g).unit_direction
      htau hdr hw hadmissible (fun i => (hsub g hg i).1) (hcap g hg) z
  have hpointMass (g : Fin M) (hg : g ∈ net) (z : Cell (k+1)) :
      (3/4:ℝ)*((parent g z).card : ℝ) ≤
        ∑ q ∈ labels g, ((cellDirections (output g q) z).card : ℝ) := by
    simp_rw [houtput]
    exact pointwise_restoration_mass_on (parent g z) (label g) (labels g) (hlabels g z) hB (hcount g hg z)
  have hnewTotal : (∑ g ∈ net, ∑ q ∈ labels g, ∑ i : Fin M, ((output g q i).card : ℝ)) =
      ∑ z ∈ cells, ∑ g ∈ net, ∑ q ∈ labels g, ((cellDirections (output g q) z).card : ℝ) := by
    rw [Finset.sum_comm (s := cells)]
    apply Finset.sum_congr rfl
    intro g hg
    rw [Finset.sum_comm (s := cells)]
    apply Finset.sum_congr rfl
    intro q _
    exact shading_double_count cells (output g q)
      (fun i => (splitShading_subset (shading g) (label g) B q i).trans (hsub g hg i).2)
  have holdTotal : (∑ g ∈ net, ∑ i : Fin M, ((shading g i).card : ℝ)) =
      ∑ z ∈ cells, ∑ g ∈ net, ((parent g z).card : ℝ) := by
    rw [Finset.sum_comm (s := cells)]
    apply Finset.sum_congr rfl
    intro g hg
    exact shading_double_count cells (shading g) (fun i => (hsub g hg i).2)
  refine ⟨labels,output,?_,?_,?_,?_,?_,?_⟩
  · intro g hg q i
    exact ⟨splitShading_subset (shading g) (label g) B q i,
      (splitShading_subset (shading g) (label g) B q i).trans (hsub g hg i).2⟩
  · intro g q i hi
    exact splitShading_label (shading g) (label g) B q i hi
  · intro g hg q i hi
    have hlabel := splitShading_label (shading g) (label g) B q i hi
    have hiold : (shading g i).Nonempty := hi.mono (splitShading_subset (shading g) (label g) B q i)
    have hbox := bounded_tube_spatial_box (F.tube g).direction (F.tube g).unit_direction (F.tube i)
      htau hdr hδ1 hw (by norm_num : (0:ℝ) ≤ 3) (hbounded i) (hcap g hg i hiold)
    simpa only [← hlabel] using hbox
  · rw [hnewTotal,holdTotal,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z _
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun g hg => hpointMass g hg z)
  · intro z g hg q _
    rw [houtput]
    exact restore_broad F (parent g z) (label g) B q hδ.le htau hK (hbroad z g hg)
  · intro z
    let active := net.filter (fun g => (parent g z).Nonempty)
    let count := fun g => (({q ∈ labels g | (cellDirections (output g q) z).Nonempty}).card : ℝ)
    have hzero (g : Fin M) (hg : g ∈ net) (hgn : g ∉ active) : count g = 0 := by
      have hp : parent g z = ∅ := Finset.not_nonempty_iff_eq_empty.mp
        (fun hp => hgn (Finset.mem_filter.mpr ⟨hg,hp⟩))
      simp only [count]
      simp_rw [houtput,hp]
      simp [restore,fiber]
    have hsum : ∑ g ∈ net, count g = ∑ g ∈ active, count g :=
      (Finset.sum_subset (Finset.filter_subset _ _) hzero).symm
    have hcountOut (g : Fin M) (hg : g ∈ net) : count g ≤ B := by
      have h := occupied_restored_count (parent g z) (label g) B (labels g)
      have hr : count g ≤ (((parent g z).image (label g)).card : ℝ) := by
        dsimp [count]
        simp_rw [houtput]
        exact_mod_cast h
      exact hr.trans (hcount g hg z)
    change (∑ g ∈ net, count g) ≤ B*H
    rw [hsum]
    calc
      _ ≤ ∑ _g ∈ active, B := Finset.sum_le_sum (fun g hg => hcountOut g (Finset.mem_filter.mp hg).1)
      _ = (active.card : ℝ)*B := by simp
      _ ≤ H*B := mul_le_mul_of_nonneg_right (hover z) hB.le
      _ = _ := mul_comm _ _

/-- Complete actual finite-cell angular and spatial decomposition for bounded
admissible tube shadings. Every nonempty output tube has exactly one angular
assignment and one spatial lattice label. No cap-cover, spatial-cover, selection,
assignment, broadness, or mass-retention conclusion is assumed as an input. -/
theorem discrete_angular_spatial_decomposition {k M : ℕ} (F : TubeFamily (k+1) M)
    (hM : 0 < M) (cells : Finset (Cell (k+1))) (hcells : cells ⊆ F.unionCells)
    {δ width R beta : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hw : 0 ≤ width) (hb : 0 ≤ beta)
    (hadmissible : F.Admissible width δ) (hbounded : F.Bounded R) :
    let C := ProjectiveGeometry.packingConstant k*(3:ℝ)^k
    let B : ℝ := spatialOverlap k width
    ∃ J : ℕ, ∃ j : Fin (J+1), ∃ net : Finset (Fin M), ∃ assign : Fin M → Fin M,
      ∃ labels : Fin M → Finset (Cell k),
      ∃ output : Fin M → Cell k → Fin M → Finset (Cell (k+1)),
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      δ ≤ Localization.radius J j ∧ Localization.radius J j ≤ 1 ∧
      (∀ i, assign i ∈ net) ∧
      (∀ g ∈ net, ∀ q i, output g q i ⊆ F.shade i ∧ output g q i ⊆ cells) ∧
      (∀ g ∈ net, ∀ q i, (output g q i).Nonempty → assign i = g ∧
        spatialLabel (F.tube g).direction (Localization.radius J j) (F.tube i) = q) ∧
      (∀ g ∈ net, ∀ q i, (output g q i).Nonempty →
        projectiveDistance (F.tube i).direction (F.tube g).direction ≤ 3*Localization.radius J j) ∧
      (∀ g ∈ net, ∀ q i, (output g q i).Nonempty →
        (F.tube i).carrier (width*δ) ⊆ parallelBox (F.tube g).direction (Localization.radius J j) q
          (R+1+width) ((k:ℝ)+width+3)) ∧
      (3/4:ℝ)*(3/(4*C))*(AngularIncidence.incidenceMass F cells/(2*((J:ℝ)+1))) ≤
        ∑ g ∈ net, ∑ q ∈ labels g, ∑ i : Fin M, ((output g q i).card : ℝ) ∧
      (∀ z : Cell (k+1), ∀ g ∈ net, ∀ q ∈ labels g,
        Broad F (cellDirections (output g q) z) δ beta (Localization.radius J j)
          ((((4:ℝ)^beta)*(4*C))*(4*B))) ∧
      ∀ z : Cell (k+1),
        (∑ g ∈ net, (({q ∈ labels g | (cellDirections (output g q) z).Nonempty}).card : ℝ)) ≤
          B*(2*(Localization.radius J j)^(-beta)) := by
  classical
  let C := ProjectiveGeometry.packingConstant k*(3:ℝ)^k
  have hC : 0 < C := by
    have hp := ProjectiveGeometry.packingConstant_ge_one k
    dsimp [C]
    positivity
  obtain ⟨J,j,net,assign,angular,hdepth,hdτ,hτ1,hassign,hsub,hunique,hcap,hmass,hbroad,hover⟩ :=
    actual_angular_shading_assignment F hM cells hcells hδ hδ1 hb
  have hK : 0 ≤ ((4:ℝ)^beta)*(4*C) := by positivity
  have hBroad : ∀ z : Cell (k+1), ∀ g ∈ net,
      Broad F (cellDirections (angular g) z) δ beta (Localization.radius J j) (((4:ℝ)^beta)*(4*C)) := hbroad
  have hOverlap : ∀ z : Cell (k+1),
      ((net.filter (fun g => (cellDirections (angular g) z).Nonempty)).card : ℝ) ≤
        2*(Localization.radius J j)^(-beta) := by
    intro z
    simpa only [cellDirections,Finset.filter_nonempty_iff,Finset.mem_univ,true_and] using hover z
  obtain ⟨labels,output,hosub,holabel,hbox,hretain,hoBroad,hoOverlap⟩ := spatial_shading_assignment
    F cells net angular hδ hδ1 (Localization.radius_pos J j) hdτ hw hK hadmissible hbounded
    (fun g _ i => hsub g i) hcap hBroad hOverlap
  refine ⟨J,j,net,assign,labels,output,hdepth,hdτ,hτ1,hassign,?_,?_,?_,hbox,?_,hoBroad,hoOverlap⟩
  · intro g hg q i
    exact ⟨(hosub g hg q i).1.trans (hsub g i).1,(hosub g hg q i).2⟩
  · intro g hg q i hi
    exact ⟨hunique g i (hi.mono (hosub g hg q i).1),holabel g q i hi⟩
  · intro g hg q i hi
    exact hcap g hg i (hi.mono (hosub g hg q i).1)
  · have h := mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ) ≤ 3/4)
    calc
      _ ≤ (3/4:ℝ)*(∑ g ∈ net, ∑ i : Fin M, ((angular g i).card : ℝ)) :=
        by simpa only [mul_assoc] using h
      _ ≤ _ := hretain

end
end KakeyaFormal.SpatialAssignment
