import LocalizedCellPartition
import LocalizedSeedNormalization
import TwoEndsDiscreteEstimate

/-! Actual common-origin normalization after old-cell spatial partitioning.
The dilation is chosen from proved local tube counts, so normalized density
is legal. Complete selected old shadings undergo an injective lattice shift.
Direction thinning costs only rho^m/A and produces an absolute cap bound. -/
namespace KakeyaFormal.LocalizedGroupedNormalization
open Finset LocalizedCellPartition LocalizedSeedNormalization
open LocalizedGridTubes LocalizedDirectionThinning Rescaling GridTwoEnds
noncomputable section
open Classical

def baseRadius (n : ℕ) (width : ℝ) : ℝ :=
  (6*localWidth width+(1+(n:ℝ)))/dilationConstant n width

theorem baseRadius_pos (n : ℕ) (width : ℝ) : 0 < baseRadius n width := by
  have hW := localWidth_pos width
  have hD := dilationConstant_pos n width
  unfold baseRadius
  positivity

def geometry (n : ℕ) (width : ℝ) : Normalization :=
  ⟨localWidth width,1,baseRadius n width,localWidth_pos width,by norm_num,baseRadius_pos n width⟩

/-- The local axes can be extended to the fixed dilation interval without
changing their starting points, which are quantitatively near their centers. -/
theorem bounded_axis_intervals {n M : ℕ} (F : TubeFamily n M) {δ rho width : ℝ}
    (hδ : 0 < δ) (hδrho : δ ≤ rho) (centers : Fin M → Space n)
    (hne : ∀ i, (F.shade i).Nonempty) (hadm : F.Admissible width δ)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho) :
    ∃ a : Fin M → ℝ,
      (∀ i, dist ((F.tube i).axisPoint (a i)) (centers i) ≤ 6*localWidth width*rho) ∧
      ∀ i z, z ∈ F.shade i →
        ∃ t ∈ Set.Icc (a i) (a i+dilationConstant n width*rho),
          dist (cellCenter δ z) ((F.tube i).axisPoint t) ≤ localWidth width*δ := by
  have hrho := hδ.trans_le hδrho
  choose a ha hlocal using fun i => localized_grid_interval (F.tube i) (F.shade i)
    hδ hδrho (centers i) (hne i) (hadm i) (hball i)
  refine ⟨a,ha,?_⟩
  intro i z hz
  obtain ⟨t,ht,hd⟩ := hlocal i z hz
  refine ⟨t,⟨ht.1,ht.2.trans ?_⟩,hd⟩
  have hh := mul_le_mul_of_nonneg_right
    (le_max_left (8*localWidth width) (countConstant n width)) hrho.le
  simpa only [dilationConstant,add_comm] using add_le_add_left hh (a i)

/-- A genuine normalized configuration, with exact original index and cell
correspondence. Every field follows from the construction below. -/
structure Output {k M : ℕ} (F : TubeFamily (k+1) M)
    (δ rho s width B alpha m A : ℝ) (origin : Cell (k+1)) where
  configuration : ShadedConfiguration (k+1) (geometry (k+1) width) m
  population_pos : 0 < configuration.M
  index : Fin configuration.M → Fin M
  index_injective : Function.Injective index
  scale_eq : configuration.δ=δ/(dilationConstant (k+1) width*rho)
  density_eq : configuration.lam=s/(dilationConstant (k+1) width*rho)
  cap_eq : configuration.A=capConstant k m
  count_lower : ((M:ℝ)*rho^m)/(retentionConstant k m*A) ≤ (configuration.M:ℝ)
  shade_eq : ∀ i, configuration.family.shade i=
    (F.shade (index i)).image (shiftLabel origin)
  direction_eq : ∀ i, (configuration.family.tube i).direction=(F.tube (index i)).direction
  union_subset : configuration.family.unionCells ⊆ F.unionCells.image (shiftLabel origin)
  two_ends : ∀ i x r, configuration.δ ≤ r →
    (((configuration.family.shade i).filter
      (fun z => dist (cellCenter configuration.δ z) x ≤ r)).card:ℝ) ≤
      (B*(dilationConstant (k+1) width)^alpha)*r^alpha*
        ((configuration.family.shade i).card:ℝ)

/-- Actual thinning and common-origin rescaling. This is a geometric
construction with no estimate, desired cap family, or output-density premise. -/
theorem construct {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ rho s width B alpha m A : ℝ} (hM : 0 < M)
    (hδ : 0 < δ) (hδrho : δ ≤ rho) (hrho1 : rho ≤ 1) (hs : 0 < s)
    (hB : 1 ≤ B) (halpha : 0 ≤ alpha) (hm : 0 ≤ m) (hA : 1 ≤ A)
    (centers : Fin M → Space (k+1)) (origin : Cell (k+1))
    (hadm : F.Admissible width δ) (hcomp : F.Comparable δ s) (hcap : F.CapBound δ m A)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho)
    (hcenter : ∀ i, dist (centers i) (cellCenter δ origin) ≤ (1+((k+1:ℕ):ℝ))*rho)
    (hends : ∀ i x r, δ ≤ r → r ≤ rho →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*(r/rho)^alpha*((F.shade i).card:ℝ)) :
    Nonempty (Output F δ rho s width B alpha m A origin) := by
  let L := dilationConstant (k+1) width*rho
  have hrho := hδ.trans_le hδrho
  have hL : 0 < L := mul_pos (dilationConstant_pos _ _) hrho
  have hrhoL : rho ≤ L := le_mul_of_one_le_left hrho.le (dilationConstant_ge_one _ _)
  have hδL := hδrho.trans hrhoL
  have hne (i : Fin M) : (F.shade i).Nonempty := by
    exact card_pos.mp (by exact_mod_cast ((div_pos hs hδ).trans_le (hcomp i).1))
  obtain ⟨a,ha,hinterval⟩ := bounded_axis_intervals F hδ hδrho centers hne hadm hball
  obtain ⟨N,e,he,H,hN,htubes,hshades,hsep,hcaps,hU⟩ :=
    thin_at_localized_scale F hδ (hδrho.trans hrho1) hrho hrho1 hrhoL hδL hm hA hcap
  have hNpos : 0 < N := by
    have hpos : 0 < ((M:ℝ)*rho^m)/(retentionConstant k m*A) := by
      have hM' : (0:ℝ) < M := by exact_mod_cast hM
      have hC := retentionConstant_pos k m
      positivity
    exact_mod_cast hpos.trans_le hN
  let G := Rescaling.family H L δ origin (fun i => a (e i))
  have hHcomp : H.Comparable δ s := by
    intro i
    rw [hshades i]
    exact hcomp (e i)
  have hGadm : G.Admissible (localWidth width) (δ/L) := by
    apply rescaled_admissible H hL
    intro i z hz
    rw [htubes i]
    exact hinterval (e i) z (by simpa only [hshades i] using hz)
  have hGbounded : G.Bounded (baseRadius (k+1) width) := by
    apply rescaled_bounded H hL
    intro i
    rw [htubes i]
    have ht := dist_triangle ((F.tube (e i)).axisPoint (a (e i))) (centers (e i)) (cellCenter δ origin)
    have hid : L*baseRadius (k+1) width =
        (6*localWidth width+(1+((k+1:ℕ):ℝ)))*rho := by
      dsimp [L,baseRadius]
      field_simp [(dilationConstant_pos (k+1) width).ne']
    rw [hid]
    nlinarith [ha (e i),hcenter (e i)]
  let V : ShadedConfiguration (k+1) (geometry (k+1) width) m := {
    M := N, δ := δ/L, lam := s/L, A := capConstant k m, family := G,
    scale_pos := div_pos hδ hL, scale_le_one := (div_le_one hL).mpr hδL,
    density_pos := div_pos hs hL,
    density_le_one := normalized_density_le_one F hM hδ hδrho centers hadm hcomp hball,
    cap_ge_one := capConstant_ge_one k m,
    admissible := hGadm, separated := by
      change G.Separated (1*(δ/L))
      rw [one_mul]
      exact hsep,
    bounded := hGbounded, cap_bound := hcaps,
    comparable := rescaled_comparable H hL.ne' _ _ hHcomp }
  refine ⟨⟨V,hNpos,e,he,rfl,rfl,rfl,hN,?_,?_,?_,?_⟩⟩
  · intro i
    exact congrArg (fun S : Finset (Cell (k+1)) => S.image (shiftLabel origin)) (hshades i)
  · intro i
    change (H.tube i).direction=(F.tube (e i)).direction
    exact congrArg UnitTube.direction (htubes i)
  · change G.unionCells ⊆ F.unionCells.image (shiftLabel origin)
    rw [rescaled_union]
    exact image_subset_image hU
  · have hHends : ∀ i x r, δ ≤ r → r ≤ rho →
        (((H.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
          B*(r/rho)^alpha*((H.shade i).card:ℝ) := by
      intro i x r hr hr1
      simpa only [hshades i] using hends (e i) x r hr hr1
    have hh := rescaled_two_ends H hL hδ hrho hB halpha origin (fun i => a (e i)) hHends
    have hid : L/rho=dilationConstant (k+1) width := by dsimp [L]; field_simp
    simpa only [hid] using hh


theorem Output.shade_card {k M : ℕ} {F : TubeFamily (k+1) M}
    {δ rho s width B alpha m A : ℝ} {origin : Cell (k+1)}
    (O : Output F δ rho s width B alpha m A origin) (i : Fin O.configuration.M) :
    (O.configuration.family.shade i).card=(F.shade (O.index i)).card := by
  rw [O.shade_eq]
  exact card_image_of_injective _ (shiftLabel_injective origin)

theorem Output.union_card_le {k M : ℕ} {F : TubeFamily (k+1) M}
    {δ rho s width B alpha m A : ℝ} {origin : Cell (k+1)}
    (O : Output F δ rho s width B alpha m A origin) :
    O.configuration.family.unionCells.card ≤ F.unionCells.card := by
  have hh := card_le_card O.union_subset
  rwa [card_image_of_injective _ (shiftLabel_injective origin)] at hh

theorem Output.full_two_ends {k M : ℕ} {F : TubeFamily (k+1) M}
    {δ rho s width B alpha m A : ℝ} {origin : Cell (k+1)}
    (O : Output F δ rho s width B alpha m A origin) :
    O.configuration.family.FullTwoEnds O.configuration.δ
      (B*(dilationConstant (k+1) width)^alpha) alpha :=
  fun i x r hr _ => O.two_ends i x r hr

/-- Each nonempty actual old spatial group produces a legal configuration.
The bin construction supplies the center bound and every retained ball test. -/
theorem partition_construct {k M : ℕ} {F : TubeFamily (k+1) M} {δ rho s width B alpha m A : ℝ}
    (P : Partition F δ rho s) (hδ : 0 < δ) (hδrho : δ ≤ rho) (hrho1 : rho ≤ 1)
    (hB : 1 ≤ B) (halpha : 0 ≤ alpha) (hm : 0 ≤ m) (hA : 1 ≤ A)
    (centers : Fin M → Space (k+1))
    (hadm : F.Admissible width δ) (hcap : F.CapBound δ m A)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho)
    (hends : ∀ i x r, δ ≤ r → r ≤ rho →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*(r/rho)^alpha*((F.shade i).card:ℝ))
    (q : ↥P.bins) :
    Nonempty (Output (P.groupFamily q.val) δ rho P.density width
      (2*(binCount (k+1):ℝ)*B) alpha m A (fineOrigin δ rho q.val)) := by
  have hK : (1:ℝ) ≤ binCount (k+1) := by exact_mod_cast binCount_pos (k+1)
  have hBB : 1 ≤ 2*(binCount (k+1):ℝ)*B := by nlinarith
  have hM : 0 < (groupIndices P.assignment q.val).card := by
    obtain ⟨i,_,hi⟩ := mem_image.mp q.property
    exact card_pos.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩⟩
  have hs' : 0 < P.density := mul_pos hδ (Nat.cast_pos.mpr P.commonCard_pos)
  apply construct (P.groupFamily q.val) hM hδ hδrho hrho1 hs' hBB halpha hm hA
    (fun i => centers (P.index q.val i)) (fineOrigin δ rho q.val)
    (P.group_admissible hadm q.val) (P.group_comparable hδ q.val) (P.group_cap_bound hcap q.val)
  · intro i z hz
    exact hball _ z (P.subset _ hz)
  · intro i
    have hh := P.origin_bound hδ hδrho centers hball (P.index q.val i)
    rw [P.index_assignment q.val i] at hh
    exact hh
  · intro i x r hr hr1
    exact P.two_ends hδ (hδ.trans_le hδrho) (zero_le_one.trans hB) hends (P.index q.val i) x r hr hr1

/-- The literal fixed coefficient supplied to a uniform two-ends estimate is
at least one. It has no dependence on rho, delta, density, or population. -/
theorem normalized_ends_ge_one {n : ℕ} {width B alpha : ℝ} (hB : 1 ≤ B) (ha : 0 ≤ alpha) :
    1 ≤ (2*(binCount n:ℝ)*B)*(dilationConstant n width)^alpha := by
  have hK : (1:ℝ) ≤ binCount n := by exact_mod_cast binCount_pos n
  have hBB : 1 ≤ 2*(binCount n:ℝ)*B := by nlinarith
  have hp := Real.one_le_rpow (dilationConstant_ge_one n width) ha
  nlinarith


/-- Spatial normalization and thinning retain a rho^m/A fraction of the
original localized population after summing all actual spatial groups. -/
theorem partition_population_lower {k M : ℕ} {F : TubeFamily (k+1) M}
    {δ rho s width B alpha m A : ℝ} (P : Partition F δ rho s)
    (O : (q : ↥P.bins) → Output (P.groupFamily q.val) δ rho P.density width
      (2*(binCount (k+1):ℝ)*B) alpha m A (fineOrigin δ rho q.val)) :
    ((M:ℝ)*rho^m)/(retentionConstant k m*A) ≤
      ∑ q : ↥P.bins, ((O q).configuration.M:ℝ) := by
  have hpop : (∑ q : ↥P.bins, ((groupIndices P.assignment q.val).card:ℝ))=(M:ℝ) := by
    rw [sum_coe_sort P.bins (fun q => ((groupIndices P.assignment q).card:ℝ))]
    exact_mod_cast P.population_sum
  have hh := sum_le_sum (s:=univ) (fun q _ => (O q).count_lower)
  simpa only [← sum_div,← sum_mul,hpop] using hh

/-- Although each spatial group uses its own common origin, injective label
shifts preserve its cardinality. Summation refers to disjoint OLD unions. -/
theorem partition_union_sum {k M : ℕ} {F : TubeFamily (k+1) M}
    {δ rho s width B alpha m A : ℝ} (P : Partition F δ rho s)
    (O : (q : ↥P.bins) → Output (P.groupFamily q.val) δ rho P.density width
      (2*(binCount (k+1):ℝ)*B) alpha m A (fineOrigin δ rho q.val)) :
    (∑ q : ↥P.bins, (O q).configuration.family.unionCells.card) ≤ F.unionCells.card := by
  calc
    _ ≤ ∑ q : ↥P.bins, (P.groupFamily q.val).unionCells.card :=
      sum_le_sum (fun q _ => (O q).union_card_le)
    _ = ∑ q ∈ P.bins, (P.groupFamily q).unionCells.card := sum_coe_sort P.bins (fun q => (P.groupFamily q).unionCells.card)
    _ ≤ _ := P.union_sum

/-- Simultaneously construct actual legal configurations for all old spatial
bins, with the population and union summations already discharged. -/
theorem construct_partition {k M : ℕ} {F : TubeFamily (k+1) M} {δ rho s width B alpha m A : ℝ}
    (P : Partition F δ rho s) (hδ : 0 < δ) (hδrho : δ ≤ rho) (hrho1 : rho ≤ 1)
    (hB : 1 ≤ B) (halpha : 0 ≤ alpha) (hm : 0 ≤ m) (hA : 1 ≤ A)
    (centers : Fin M → Space (k+1))
    (hadm : F.Admissible width δ) (hcap : F.CapBound δ m A)
    (hball : ∀ i z, z ∈ F.shade i → dist (cellCenter δ z) (centers i) ≤ rho)
    (hends : ∀ i x r, δ ≤ r → r ≤ rho →
      (((F.shade i).filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤
        B*(r/rho)^alpha*((F.shade i).card:ℝ)) :
    ∃ O : (q : ↥P.bins) → Output (P.groupFamily q.val) δ rho P.density width
      (2*(binCount (k+1):ℝ)*B) alpha m A (fineOrigin δ rho q.val),
      ((M:ℝ)*rho^m)/(retentionConstant k m*A) ≤
        (∑ q : ↥P.bins, ((O q).configuration.M:ℝ)) ∧
      (∑ q : ↥P.bins, (O q).configuration.family.unionCells.card) ≤ F.unionCells.card := by
  let O := fun q : ↥P.bins => Classical.choice
    (partition_construct P hδ hδrho hrho1 hB halpha hm hA centers hadm hcap hball hends q)
  exact ⟨O,partition_population_lower P O,partition_union_sum P O⟩

end
end KakeyaFormal.LocalizedGroupedNormalization
