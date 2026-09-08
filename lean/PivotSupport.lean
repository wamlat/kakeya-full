import TubeGeometry
import GridGeometry
import Finite

/-!
# Actual integer-grid support of endpoint-pivot triples

This module derives finite support counts from geometric witnesses on the actual
scaled integer grid. A lifted grid label is its horizontal integer cell together
with its final integer coordinate. No support-cardinality conclusion is assumed.
The construction of these witnesses from every selected finite pivot fiber is a
separate interface, as are the probabilistic and analytic Kakeya inputs.
-/

namespace KakeyaFormal.PivotSupport

open KakeyaFormal KakeyaFormal.GridGeometry

noncomputable section

abbrev LiftCell (k : ℕ) := Cell k × ℤ

/-- Explicit one-dimensional integer-grid count with arbitrary real center. -/
theorem integer_interval_count (labels : Finset ℤ) (anchor R : ℝ)
    (h : ∀ n ∈ labels, |(n:ℝ)-anchor| ≤ R) :
    labels.card ≤ 2*Nat.ceil R+3 := by
  let b : ℤ := ⌊anchor⌋
  let r : ℕ := Nat.ceil R+1
  have hsub : labels ⊆ Finset.Icc (b-(r:ℤ)) (b+(r:ℤ)) := by
    intro n hn
    have hdist := abs_le.mp (h n hn)
    have hlo := Int.floor_le anchor
    have hhi := Int.lt_floor_add_one anchor
    have hceil := Nat.le_ceil R
    apply Finset.mem_Icc.mpr
    constructor
    · have hh : (⌊anchor⌋:ℝ)-((Nat.ceil R:ℝ)+1) ≤ (n:ℝ) := by linarith
      dsimp [b,r]
      exact_mod_cast hh
    · have hh : (n:ℝ) ≤ (⌊anchor⌋:ℝ)+((Nat.ceil R:ℝ)+1) := by linarith
      dsimp [b,r]
      exact_mod_cast hh
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hid : b+(r:ℤ)+1-(b-(r:ℤ)) = (2*Nat.ceil R+3:ℕ) := by
    dsimp [r]
    omega
  rw [hid, Int.toNat_natCast] at hcard
  exact hcard

/-- Horizontal Euclidean-ball localization and vertical interval localization
count actual product-grid labels. The vertical factor is linear in the radius. -/
theorem lift_grid_box_count {k : ℕ} {δ H V : ℝ} (hδ : 0 < δ)
    (x : Space k) (anchor : ℝ) (cells : Finset (LiftCell k))
    (hh : ∀ z ∈ cells, dist (cellCenter δ z.1) x ≤ H*δ)
    (hv : ∀ z ∈ cells, |(z.2:ℝ)-anchor| ≤ V) :
    cells.card ≤ (2*Nat.ceil H+3)^k * (2*Nat.ceil V+3) := by
  classical
  have hhcount : (cells.image Prod.fst).card ≤ (2*Nat.ceil H+3)^k := by
    apply ball_grid_count hδ x
    intro z hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    exact hh p hp
  have hvcount : (cells.image Prod.snd).card ≤ 2*Nat.ceil V+3 := by
    apply integer_interval_count _ anchor V
    intro n hn
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact hv p hp
  have hsub : cells ⊆ (cells.image Prod.fst) ×ˢ (cells.image Prod.snd) := by
    intro z hz
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩, Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  calc
    cells.card ≤ ((cells.image Prod.fst) ×ˢ (cells.image Prod.snd)).card :=
      Finset.card_le_card hsub
    _ = (cells.image Prod.fst).card * (cells.image Prod.snd).card := Finset.card_product ..
    _ ≤ _ := Nat.mul_le_mul hhcount hvcount

/-- Geometric data carried by one actual lifted incidence. Exact representatives
can differ between incidences even when all three original grid labels coincide.
The residual is the one proved quantitatively in `TubeGeometry`; it is not a
support-counting or parameter-interval assumption. -/
structure RoundedLiftWitness (k : ℕ) (δ err residual separation timeBound : ℝ)
    (e1 e2 pivot : Cell k) (lift : LiftCell k) where
  y1 : Space k
  y2 : Space k
  z : Space k
  time : ℝ
  pivot_between : z ∈ segment ℝ y1 y2
  first_close : ‖cellCenter δ e1-y1‖ ≤ err
  second_close : ‖cellCenter δ e2-y2‖ ≤ err
  pivot_close : ‖cellCenter δ pivot-z‖ ≤ err
  separated : separation ≤ ‖z-y1‖
  time_bound : |time| ≤ timeBound
  residual_bound : ‖time • z-y2-(time-1) • y1‖ ≤ residual
  horizontal_close : ‖cellCenter δ lift.1-y2‖ ≤ err
  vertical_close : |δ*(lift.2:ℝ)-time| ≤ err

/-- Derived radius of the final integer coordinate of a lift fiber. -/
def verticalRadius (δ err residual separation timeBound : ℝ) : ℝ :=
  (err+4*(residual+(2*timeBound+2)*err)/separation)/δ

/-- A fixed endpoint/pivot triple has only boundedly many lifted grid positions.
Every counting premise is a metric property of its actual exact representatives;
the cardinality bound is a conclusion. The inverse-separation factor is explicit. -/
theorem fixed_triple_lift_count {k : ℕ} {δ err residual separation timeBound : ℝ}
    (hδ : 0 < δ) (hsep : 0 < separation) (herr : err ≤ separation/4)
    (e1 e2 pivot : Cell k) (lifts : Finset (LiftCell k))
    (w : ∀ l ∈ lifts,
      RoundedLiftWitness k δ err residual separation timeBound e1 e2 pivot l) :
    lifts.card ≤ (2*Nat.ceil (2*err/δ)+3)^k *
      (2*Nat.ceil (verticalRadius δ err residual separation timeBound)+3) := by
  classical
  by_cases hn : lifts.Nonempty
  · obtain ⟨base,hbase⟩ := hn
    let wb := w base hbase
    apply lift_grid_box_count hδ (cellCenter δ e2) (wb.time/δ) lifts
    · intro l hl
      let wl := w l hl
      have hnorm : ‖cellCenter δ l.1-cellCenter δ e2‖ ≤ 2*err := by
        have hid : cellCenter δ l.1-cellCenter δ e2 =
            (cellCenter δ l.1-wl.y2)+(wl.y2-cellCenter δ e2) := by abel
        rw [hid]
        have hrev : ‖wl.y2-cellCenter δ e2‖ ≤ err := by
          simpa only [norm_sub_rev] using wl.second_close
        exact (norm_add_le _ _).trans (by linarith [wl.horizontal_close])
      rw [dist_eq_norm]
      have hid : (2*err/δ)*δ = 2*err := by field_simp
      rw [hid]
      exact hnorm
    · intro l hl
      let wl := w l hl
      have ht := KakeyaAudit.TubeGeometry.rounded_triple_parameter_bound
        wb.y1 wb.y2 wb.z wl.y1 wl.y2 wl.z
        (cellCenter δ e1) (cellCenter δ e2) (cellCenter δ pivot)
        hsep herr wb.separated wb.first_close wb.second_close wb.pivot_close
        wl.first_close wl.second_close wl.pivot_close
        wb.time_bound wl.time_bound wb.residual_bound wl.residual_bound
      have htri : |δ*(l.2:ℝ)-wb.time| ≤
          err+4*(residual+(2*timeBound+2)*err)/separation := by
        have hid : δ*(l.2:ℝ)-wb.time = (δ*(l.2:ℝ)-wl.time)+(wl.time-wb.time) := by ring
        rw [hid]
        exact (abs_add_le _ _).trans (add_le_add wl.vertical_close ht)
      have hid : (l.2:ℝ)-wb.time/δ = (δ*(l.2:ℝ)-wb.time)/δ := by field_simp
      rw [hid, abs_div, abs_of_pos hδ]
      exact div_le_div_of_nonneg_right htri hδ.le
  · simp [Finset.not_nonempty_iff_eq_empty.mp hn]

/-- Rounding both endpoints of an actual segment and its pivot preserves
segment proximity with error at most twice the coordinate-rounding error. -/
theorem rounded_segment_proximity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (y1 y2 z e1 e2 z0 : E) {err : ℝ}
    (hbetween : z ∈ segment ℝ y1 y2)
    (h1 : ‖e1-y1‖ ≤ err) (h2 : ‖e2-y2‖ ≤ err) (hz : ‖z0-z‖ ≤ err) :
    ∃ p ∈ segment ℝ e1 e2, dist z0 p ≤ 2*err := by
  obtain ⟨a,b,ha,hb,hab,habz⟩ := hbetween
  let p := a • e1+b • e2
  have hp : p ∈ segment ℝ e1 e2 := ⟨a,b,ha,hb,hab,rfl⟩
  refine ⟨p,hp,?_⟩
  have hid : z-p = a • (y1-e1)+b • (y2-e2) := by
    rw [← habz]
    dsimp [p]
    module
  have hnorm : ‖z-p‖ ≤ err := by
    rw [hid]
    calc
      ‖a • (y1-e1)+b • (y2-e2)‖ ≤ ‖a • (y1-e1)‖+‖b • (y2-e2)‖ := norm_add_le _ _
      _ = a*‖y1-e1‖+b*‖y2-e2‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a*err+b*err := add_le_add
        (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using h1) ha)
        (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using h2) hb)
      _ = err := by rw [← add_mul,hab,one_mul]
  rw [dist_eq_norm]
  have hid2 : z0-p = (z0-z)+(z-p) := by abel
  rw [hid2]
  exact (norm_add_le _ _).trans (by linarith)

abbrev Triple (k : ℕ) := Cell k × Cell k × Cell k
abbrev SupportLabel (k : ℕ) := Triple k × LiftCell k

def pivotCount (k : ℕ) (δ width D : ℝ) : ℕ :=
  (Nat.ceil (D/δ)+1)*(2*Nat.ceil (width+1)+3)^k

def liftCount (k : ℕ) (δ err residual separation timeBound : ℝ) : ℕ :=
  (2*Nat.ceil (2*err/δ)+3)^k *
    (2*Nat.ceil (verticalRadius δ err residual separation timeBound)+3)

/-- Actual endpoint/pivot triples are counted by the segment-grid theorem.
The two endpoint labels belong to the original occupied set; the pivot label
is only required to lie near their segment. Degenerate segments are permitted. -/
theorem endpoint_triple_count {k : ℕ} {δ width D : ℝ} (hδ : 0 < δ)
    (occupied : Finset (Cell k)) (triples : Finset (Triple k))
    (hend : ∀ tr ∈ triples, tr.1 ∈ occupied ∧ tr.2.1 ∈ occupied)
    (hlen : ∀ tr ∈ triples, dist (cellCenter δ tr.1) (cellCenter δ tr.2.1) ≤ D)
    (hseg : ∀ tr ∈ triples, ∃ p ∈ segment ℝ (cellCenter δ tr.1) (cellCenter δ tr.2.1),
      dist (cellCenter δ tr.2.2) p ≤ width*δ) :
    triples.card ≤ occupied.card^2 * pivotCount k δ width D := by
  classical
  let endpoints : Triple k → Cell k × Cell k := fun tr => (tr.1,tr.2.1)
  have hmap : ∀ tr ∈ triples, endpoints tr ∈ occupied ×ˢ occupied := by
    intro tr ht
    exact Finset.mem_product.mpr (hend tr ht)
  have hfiber : ∀ pair ∈ occupied ×ˢ occupied,
      (triples.filter fun tr => endpoints tr = pair).card ≤ pivotCount k δ width D := by
    intro pair hp
    let fiber := triples.filter fun tr => endpoints tr = pair
    let pivots := fiber.image (fun tr => tr.2.2)
    have hinj : Set.InjOn (fun tr : Triple k => tr.2.2) (↑fiber : Set (Triple k)) := by
      intro a ha b hb hab
      have hea := (Finset.mem_filter.mp ha).2
      have heb := (Finset.mem_filter.mp hb).2
      have he : endpoints a = endpoints b := hea.trans heb.symm
      change (a.1,a.2.1) = (b.1,b.2.1) at he
      have hh : a.1 = b.1 ∧ a.2.1 = b.2.1 :=
        ⟨congrArg (fun p : Cell k × Cell k => p.1) he,
          congrArg (fun p : Cell k × Cell k => p.2) he⟩
      exact Prod.ext hh.1 (Prod.ext hh.2 hab)
    have hcard : pivots.card = fiber.card := Finset.card_image_of_injOn hinj
    by_cases hnon : fiber.Nonempty
    · obtain ⟨tr,htr⟩ := hnon
      have ht := (Finset.mem_filter.mp htr).1
      have heq := (Finset.mem_filter.mp htr).2
      have he : tr.1 = pair.1 ∧ tr.2.1 = pair.2 :=
        ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      have hD : dist (cellCenter δ pair.1) (cellCenter δ pair.2) ≤ D := by
        simpa only [he.1,he.2] using hlen tr ht
      have hbound := segment_grid_count_of_length_le (cellCenter δ pair.1)
        (cellCenter δ pair.2) hδ hD pivots (by
          intro z hz
          obtain ⟨tr,htr,rfl⟩ := Finset.mem_image.mp hz
          have ht := (Finset.mem_filter.mp htr).1
          have heq := (Finset.mem_filter.mp htr).2
          have he : tr.1 = pair.1 ∧ tr.2.1 = pair.2 :=
            ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
          simpa only [he.1,he.2] using hseg tr ht)
      rw [hcard] at hbound
      exact hbound
    · change fiber.card ≤ _
      rw [Finset.not_nonempty_iff_eq_empty.mp hnon]
      exact Nat.zero_le _
  have h := KakeyaFinite.support_card_by_fibers triples (occupied ×ˢ occupied) endpoints hmap hfiber
  simpa [Finset.card_product, pow_two] using h

/-- Count the occupied `(triple,lift-cell)` support by geometric lift witnesses.
No multiplicity of angles over an output is introduced: labels are actual pairs. -/
theorem support_count_by_triples {k : ℕ} {δ err residual separation timeBound : ℝ}
    (hδ : 0 < δ) (hsep : 0 < separation) (herr : err ≤ separation/4)
    (triples : Finset (Triple k)) (labels : Finset (SupportLabel k))
    (hmap : ∀ p ∈ labels, p.1 ∈ triples)
    (w : ∀ p ∈ labels, RoundedLiftWitness k δ err residual separation timeBound
      p.1.1 p.1.2.1 p.1.2.2 p.2) :
    labels.card ≤ triples.card * liftCount k δ err residual separation timeBound := by
  classical
  apply KakeyaFinite.support_card_by_fibers labels triples Prod.fst hmap
  intro tr htr
  let fiber := labels.filter fun p => p.1 = tr
  let lifts := fiber.image Prod.snd
  have hinj : Set.InjOn Prod.snd (↑fiber : Set (SupportLabel k)) := by
    intro a ha b hb hab
    have hea := (Finset.mem_filter.mp ha).2
    have heb := (Finset.mem_filter.mp hb).2
    exact Prod.ext (hea.trans heb.symm) hab
  have hcard : lifts.card = fiber.card := Finset.card_image_of_injOn hinj
  have hbound := fixed_triple_lift_count (residual := residual) (timeBound := timeBound)
    hδ hsep herr tr.1 tr.2.1 tr.2.2 lifts (by
      intro l hl
      have hm : ∃ p ∈ fiber, p.2 = l := Finset.mem_image.mp hl
      let p := Classical.choose hm
      have hp : p ∈ fiber ∧ p.2 = l := Classical.choose_spec hm
      have hptr := (Finset.mem_filter.mp hp.1).2
      have hpin := (Finset.mem_filter.mp hp.1).1
      have heq : p = (tr,l) := Prod.ext hptr hp.2
      have hw := w p hpin
      rw [heq] at hw
      exact hw)
  rw [hcard] at hbound
  exact hbound

/-- The complete geometric support-cardinality bound entering (5.32).
Its inputs are endpoint membership, bounded length, segment proximity, and the
actual rounded lift witnesses. It does not assume a support cardinality bound. -/
theorem endpoint_lift_support_count {k : ℕ}
    {δ width D err residual separation timeBound : ℝ}
    (hδ : 0 < δ) (hsep : 0 < separation) (herr : err ≤ separation/4)
    (occupied : Finset (Cell k)) (triples : Finset (Triple k))
    (labels : Finset (SupportLabel k))
    (hend : ∀ tr ∈ triples, tr.1 ∈ occupied ∧ tr.2.1 ∈ occupied)
    (hlen : ∀ tr ∈ triples, dist (cellCenter δ tr.1) (cellCenter δ tr.2.1) ≤ D)
    (hseg : ∀ tr ∈ triples, ∃ p ∈ segment ℝ (cellCenter δ tr.1) (cellCenter δ tr.2.1),
      dist (cellCenter δ tr.2.2) p ≤ width*δ)
    (hmap : ∀ p ∈ labels, p.1 ∈ triples)
    (w : ∀ p ∈ labels, RoundedLiftWitness k δ err residual separation timeBound
      p.1.1 p.1.2.1 p.1.2.2 p.2) :
    labels.card ≤ occupied.card^2 * pivotCount k δ width D *
      liftCount k δ err residual separation timeBound := by
  have htr := endpoint_triple_count hδ occupied triples hend hlen hseg
  have hlift := support_count_by_triples hδ hsep herr triples labels hmap w
  exact hlift.trans (Nat.mul_le_mul_right _ htr)

/-- Finite-image version of the support-sensitive energy lemma, allowing the
ambient grid of possible energy positions to be infinite. It sums only over
actual occupied positions, so no `Fintype` instance for the integer grid is used. -/
theorem finite_image_support_energy {α β : Type*} [DecidableEq β]
    (labels : Finset α) (position : α → β) (weight : α → ℝ) {B : ℝ}
    (hw : ∀ i ∈ labels, 0 ≤ weight i) (hB : (labels.card:ℝ) ≤ B) :
    (∑ i ∈ labels, weight i)^2 ≤
      B * ∑ p ∈ labels.image position,
        (∑ i ∈ labels with position i = p, weight i)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq labels (fun _ => (1:ℝ)) weight
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hmap : ∀ i ∈ labels, position i ∈ labels.image position := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i,hi,rfl⟩
  have hsplit := Finset.sum_fiberwise_of_maps_to hmap (fun i => weight i^2)
  have hagg : (∑ i ∈ labels, weight i^2) ≤
      ∑ p ∈ labels.image position, (∑ i ∈ labels with position i = p, weight i)^2 := by
    rw [← hsplit]
    apply Finset.sum_le_sum
    intro p hp
    apply Finset.sum_sq_le_sq_sum_of_nonneg
    intro i hi
    exact hw i (Finset.mem_filter.mp hi).1
  have henergy : 0 ≤ ∑ p ∈ labels.image position,
      (∑ i ∈ labels with position i = p, weight i)^2 := by positivity
  exact hcs.trans ((mul_le_mul_of_nonneg_left hagg (Nat.cast_nonneg _)).trans
    (mul_le_mul_of_nonneg_right hB henergy))

/-- The actual grouped energy position: the pivot label and the lifted grid
cell. The integer slab is determined by the final grid coordinate, so it does
not create an additional independently varying index. -/
def energyPosition {k : ℕ} (p : SupportLabel k) : Cell k × LiftCell k :=
  (p.1.2.2,p.2)

/-- End-to-end finite geometric lower-energy bound. The support cardinality is
proved internally from the metric/segment witnesses, rather than assumed. -/
theorem geometric_energy_bound {k : ℕ}
    {δ width D err residual separation timeBound : ℝ}
    (hδ : 0 < δ) (hsep : 0 < separation) (herr : err ≤ separation/4)
    (occupied : Finset (Cell k)) (triples : Finset (Triple k))
    (labels : Finset (SupportLabel k)) (weight : SupportLabel k → ℝ)
    (hw : ∀ p ∈ labels, 0 ≤ weight p)
    (hend : ∀ tr ∈ triples, tr.1 ∈ occupied ∧ tr.2.1 ∈ occupied)
    (hlen : ∀ tr ∈ triples, dist (cellCenter δ tr.1) (cellCenter δ tr.2.1) ≤ D)
    (hseg : ∀ tr ∈ triples, ∃ p ∈ segment ℝ (cellCenter δ tr.1) (cellCenter δ tr.2.1),
      dist (cellCenter δ tr.2.2) p ≤ width*δ)
    (hmap : ∀ p ∈ labels, p.1 ∈ triples)
    (w : ∀ p ∈ labels, RoundedLiftWitness k δ err residual separation timeBound
      p.1.1 p.1.2.1 p.1.2.2 p.2) :
    (∑ p ∈ labels, weight p)^2 ≤
      ((occupied.card:ℝ)^2 * (pivotCount k δ width D:ℝ) *
        (liftCount k δ err residual separation timeBound:ℝ)) *
      ∑ pos ∈ labels.image energyPosition,
        (∑ p ∈ labels with energyPosition p = pos, weight p)^2 := by
  have hcount := endpoint_lift_support_count hδ hsep herr occupied triples labels
    hend hlen hseg hmap w
  have hB : (labels.card:ℝ) ≤ (occupied.card:ℝ)^2 * (pivotCount k δ width D:ℝ) *
      (liftCount k δ err residual separation timeBound:ℝ) := by exact_mod_cast hcount
  exact finite_image_support_energy labels energyPosition weight hw hB

/-- Strong form with only actual lifted incidences and their original occupied
endpoint labels. Rounded segment proximity and the set of triples are derived
inside the proof, so neither is an independent assumed counting interface. -/
theorem support_count_from_legal_witnesses {k : ℕ}
    {δ D err residual separation timeBound : ℝ}
    (hδ : 0 < δ) (hsep : 0 < separation) (herr : err ≤ separation/4)
    (occupied : Finset (Cell k)) (labels : Finset (SupportLabel k))
    (hend : ∀ p ∈ labels, p.1.1 ∈ occupied ∧ p.1.2.1 ∈ occupied)
    (hlen : ∀ p ∈ labels, dist (cellCenter δ p.1.1) (cellCenter δ p.1.2.1) ≤ D)
    (w : ∀ p ∈ labels, RoundedLiftWitness k δ err residual separation timeBound
      p.1.1 p.1.2.1 p.1.2.2 p.2) :
    labels.card ≤ occupied.card^2 * pivotCount k δ (2*err/δ) D *
      liftCount k δ err residual separation timeBound := by
  classical
  let triples := labels.image Prod.fst
  have hend' : ∀ tr ∈ triples, tr.1 ∈ occupied ∧ tr.2.1 ∈ occupied := by
    intro tr htr
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp htr
    exact hend p hp
  have hlen' : ∀ tr ∈ triples, dist (cellCenter δ tr.1) (cellCenter δ tr.2.1) ≤ D := by
    intro tr htr
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp htr
    exact hlen p hp
  have hseg' : ∀ tr ∈ triples, ∃ q ∈ segment ℝ (cellCenter δ tr.1) (cellCenter δ tr.2.1),
      dist (cellCenter δ tr.2.2) q ≤ (2*err/δ)*δ := by
    intro tr htr
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp htr
    let wp := w p hp
    have h := rounded_segment_proximity wp.y1 wp.y2 wp.z
      (cellCenter δ p.1.1) (cellCenter δ p.1.2.1) (cellCenter δ p.1.2.2)
      wp.pivot_between wp.first_close wp.second_close wp.pivot_close
    have hid : (2*err/δ)*δ = 2*err := by field_simp
    rwa [hid]
  exact endpoint_lift_support_count hδ hsep herr occupied triples labels hend' hlen' hseg'
    (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩) w

/-- Actual grouped lower-energy estimate using legal pivot witnesses only;
all support cardinalities are derived from the Euclidean/integer-grid geometry. -/
theorem energy_bound_from_legal_witnesses {k : ℕ}
    {δ D err residual separation timeBound : ℝ}
    (hδ : 0 < δ) (hsep : 0 < separation) (herr : err ≤ separation/4)
    (occupied : Finset (Cell k)) (labels : Finset (SupportLabel k))
    (weight : SupportLabel k → ℝ) (hw : ∀ p ∈ labels, 0 ≤ weight p)
    (hend : ∀ p ∈ labels, p.1.1 ∈ occupied ∧ p.1.2.1 ∈ occupied)
    (hlen : ∀ p ∈ labels, dist (cellCenter δ p.1.1) (cellCenter δ p.1.2.1) ≤ D)
    (w : ∀ p ∈ labels, RoundedLiftWitness k δ err residual separation timeBound
      p.1.1 p.1.2.1 p.1.2.2 p.2) :
    (∑ p ∈ labels, weight p)^2 ≤
      ((occupied.card:ℝ)^2 * (pivotCount k δ (2*err/δ) D:ℝ) *
        (liftCount k δ err residual separation timeBound:ℝ)) *
      ∑ pos ∈ labels.image energyPosition,
        (∑ p ∈ labels with energyPosition p = pos, weight p)^2 := by
  have hcount := support_count_from_legal_witnesses hδ hsep herr occupied labels hend hlen w
  have hB : (labels.card:ℝ) ≤ (occupied.card:ℝ)^2 * (pivotCount k δ (2*err/δ) D:ℝ) *
      (liftCount k δ err residual separation timeBound:ℝ) := by exact_mod_cast hcount
  exact finite_image_support_energy labels energyPosition weight hw hB

/-- Substituting the geometric pivot scales gives the expected fifth inverse
power, independent of the ambient dimension. This is a derived radius bound. -/
theorem normalized_vertical_radius_bound {δ C kap : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1) :
    verticalRadius δ (C*δ) (4*C*δ/kap^2) (kap^3) (2/kap) ≤ 41*C/kap^5 := by
  have hid : verticalRadius δ (C*δ) (4*C*δ/kap^2) (kap^3) (2/kap) * kap^5 =
      C*(kap^5+16+16*kap+8*kap^2) := by
    dsimp [verticalRadius]
    field_simp
    ring
  apply (le_div_iff₀ (pow_pos hk 5)).mpr
  rw [hid]
  have hp2 : kap^2 ≤ 1 := pow_le_one₀ hk.le hk1
  have hp5 : kap^5 ≤ 1 := pow_le_one₀ hk.le hk1
  have hpoly : kap^5+16+16*kap+8*kap^2 ≤ 41 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hpoly hC]

/-- Actual lifted-cell count has only `kap^(-5)` dependence, with the horizontal
grid constant depending on the fixed rounding constant and ambient dimension. -/
theorem normalized_liftCount_bound (k : ℕ) {δ C kap : ℝ}
    (hδ : 0 < δ) (hC : 1 ≤ C) (hk : 0 < kap) (hk1 : kap ≤ 1) :
    (liftCount k δ (C*δ) (4*C*δ/kap^2) (kap^3) (2/kap):ℝ) ≤
      87*C*((2*Nat.ceil (2*C)+3:ℕ):ℝ)^k/kap^5 := by
  let V := verticalRadius δ (C*δ) (4*C*δ/kap^2) (kap^3) (2/kap)
  have hC0 : 0 ≤ C := by linarith
  have hV0 : 0 ≤ V := by dsimp [V,verticalRadius]; positivity
  have hV := normalized_vertical_radius_bound hδ hC0 hk hk1
  have hp5 : kap^5 ≤ 1 := pow_le_one₀ hk.le hk1
  have hceil := Nat.ceil_lt_add_one hV0
  have hceilbound : ((2*Nat.ceil V+3:ℕ):ℝ) ≤ 2*V+5 := by push_cast; linarith
  have hvert : ((2*Nat.ceil V+3:ℕ):ℝ) ≤ 87*C/kap^5 := by
    apply (le_div_iff₀ (pow_pos hk 5)).mpr
    have hmul := (le_div_iff₀ (pow_pos hk 5)).mp hV
    change V*kap^5 ≤ 41*C at hmul
    have hscaled := mul_le_mul_of_nonneg_right hceilbound (pow_pos hk 5).le
    nlinarith
  have hh : 2*(C*δ)/δ = 2*C := by field_simp
  calc
    (liftCount k δ (C*δ) (4*C*δ/kap^2) (kap^3) (2/kap):ℝ) =
        ((2*Nat.ceil (2*C)+3:ℕ):ℝ)^k * ((2*Nat.ceil V+3:ℕ):ℝ) := by
      simp only [liftCount,hh,Nat.cast_mul,Nat.cast_pow]
      rfl
    _ ≤ ((2*Nat.ceil (2*C)+3:ℕ):ℝ)^k * (87*C/kap^5) :=
      mul_le_mul_of_nonneg_left hvert (by positivity)
    _ = 87*C*((2*Nat.ceil (2*C)+3:ℕ):ℝ)^k/kap^5 := by ring

/-- The pivot-label bound has exactly one inverse power of the mesh size,
uniformly over bounded endpoint length. -/
theorem pivotCount_scale_bound (k : ℕ) {δ width D : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hD : 0 ≤ D) :
    (pivotCount k δ width D:ℝ) ≤
      ((D+2)/δ)*((2*Nat.ceil (width+1)+3:ℕ):ℝ)^k := by
  have hceil := Nat.ceil_lt_add_one (div_nonneg hD hδ.le)
  have hbase : ((Nat.ceil (D/δ)+1:ℕ):ℝ) ≤ (D+2)/δ := by
    calc
      ((Nat.ceil (D/δ)+1:ℕ):ℝ) ≤ D/δ+2 := by push_cast; linarith
      _ ≤ (D+2)/δ := by
        apply (le_div_iff₀ hδ).mpr
        have hid : (D/δ)*δ = D := by field_simp
        nlinarith
  simpa only [pivotCount,Nat.cast_mul,Nat.cast_pow] using
    mul_le_mul_of_nonneg_right hbase
      (show 0 ≤ ((2*Nat.ceil (width+1)+3:ℕ):ℝ)^k by positivity)

end
end KakeyaFormal.PivotSupport

#print axioms KakeyaFormal.PivotSupport.fixed_triple_lift_count
#print axioms KakeyaFormal.PivotSupport.support_count_from_legal_witnesses
#print axioms KakeyaFormal.PivotSupport.energy_bound_from_legal_witnesses

#print axioms KakeyaFormal.PivotSupport.normalized_liftCount_bound

#print axioms KakeyaFormal.PivotSupport.pivotCount_scale_bound
