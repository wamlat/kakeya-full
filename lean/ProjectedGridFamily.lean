import ProjectedGrid

/-! Actual projected tube axes and image shadings, retaining the common label
map and the original incidence/fiber geometry. Lengths are the actual norms
of the projected original unit directions. -/
namespace KakeyaFormal.ProjectedGridFamily
open ProjectedGrid SamplingGeometry
noncomputable section
open Classical

/-- The projected direction is normalized; its physical axis length is kept
separately as the actual projected original direction norm. -/
def tube {n d : ℕ} (P : Space n →L[ℝ] Space d) (T : UnitTube n)
    (hdir : ‖P T.direction‖ ≠ 0) : UnitTube d where
  base := P T.base
  direction := ‖P T.direction‖⁻¹ • P T.direction
  unit_direction := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hdir]

def lengths {n d M : ℕ} (P : Space n →L[ℝ] Space d) (F : TubeFamily n M) (i : Fin M) : ℝ :=
  ‖P (F.tube i).direction‖

def family {n d M : ℕ} (P : Space n →L[ℝ] Space d) (F : TubeFamily n M) (δ : ℝ)
    (hdir : ∀ i, ‖P (F.tube i).direction‖ ≠ 0) : TubeFamily d M where
  tube i := tube P (F.tube i) (hdir i)
  shade i := (F.shade i).image (labelMap P δ)

theorem axis_image {n d : ℕ} (P : Space n →L[ℝ] Space d) (T : UnitTube n)
    (hdir : ‖P T.direction‖ ≠ 0) (t : ℝ) :
    (tube P T hdir).axisPoint (t*‖P T.direction‖)=P (T.axisPoint t) := by
  simp [tube,UnitTube.axisPoint,map_add,map_smul,smul_smul,hdir]

/-- The actual projected physical lengths obey the desired fixed bounds. -/
theorem length_bounds {n d M : ℕ} (P : Space n →L[ℝ] Space d) (F : TubeFamily n M)
    {c K : ℝ} (hK : ‖P‖ ≤ K) (hgood : ∀ i, c ≤ ‖P (F.tube i).direction‖) :
    ∀ i, c ≤ lengths P F i ∧ lengths P F i ≤ K := by
  intro i
  refine ⟨hgood i,?_⟩
  have hh := P.le_opNorm (F.tube i).direction
  rw [(F.tube i).unit_direction,mul_one] at hh
  exact hh.trans hK

/-- Rounding the actual projected center adds only target-dimension/2 to
width. The axis is the genuine projected original finite segment. -/
theorem projected_carrier {n d : ℕ} (P : Space n →L[ℝ] Space d) (T : UnitTube n)
    (hdir : ‖P T.direction‖ ≠ 0) {δ K width : ℝ} (hδ : 0 < δ) (hK : ‖P‖ ≤ K)
    {z : Cell n} (hz : ∃ t ∈ Set.Icc (0:ℝ) 1,
      dist (cellCenter δ z) (T.axisPoint t) ≤ width*δ) :
    cellCenter δ (labelMap P δ z) ∈
      lengthCarrier (tube P T hdir) ‖P T.direction‖ ((K*width+(d:ℝ)/2)*δ) := by
  obtain ⟨t,ht,hd⟩ := hz
  refine ⟨t*‖P T.direction‖,⟨mul_nonneg ht.1 (norm_nonneg _),?_⟩,?_⟩
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right ht.2 (norm_nonneg (P T.direction))
  · rw [axis_image]
    have hK0 := (norm_nonneg P).trans hK
    have himage : dist (P (cellCenter δ z)) (P (T.axisPoint t)) ≤ K*(width*δ) := by
      rw [dist_eq_norm,← map_sub]
      have hh := P.le_opNorm (cellCenter δ z-T.axisPoint t)
      have hm := mul_le_mul hK (show ‖cellCenter δ z-T.axisPoint t‖ ≤ width*δ from hd)
        (norm_nonneg _) hK0
      exact hh.trans hm
    have hround := rounding_distance P hδ z
    have htri := dist_triangle (cellCenter δ (labelMap P δ z)) (P (cellCenter δ z))
      (P (T.axisPoint t))
    have hround' : dist (cellCenter δ (labelMap P δ z)) (P (cellCenter δ z)) ≤ (d:ℝ)*δ/2 := by
      simpa only [dist_comm] using hround
    linarith

/-- Every actual image shading label has the proved projected carrier
incidence, with no supplied output admissibility premise. -/
theorem family_carrier {n d M : ℕ} (P : Space n →L[ℝ] Space d) (F : TubeFamily n M)
    (hdir : ∀ i, ‖P (F.tube i).direction‖ ≠ 0) {δ K width : ℝ}
    (hδ : 0 < δ) (hK : ‖P‖ ≤ K) (hadm : F.Admissible width δ) :
    ∀ i q, q ∈ (family P F δ hdir).shade i →
      cellCenter δ q ∈ lengthCarrier ((family P F δ hdir).tube i) (lengths P F i)
        ((K*width+(d:ℝ)/2)*δ) := by
  intro i q hq
  obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hq
  exact projected_carrier P (F.tube i) (hdir i) hδ hK (hadm i z hz)

/-- One common map commutes with the actual full shading union. -/
theorem union_image {n d M : ℕ} (P : Space n →L[ℝ] Space d) (F : TubeFamily n M)
    (δ : ℝ) (hdir : ∀ i, ‖P (F.tube i).direction‖ ≠ 0) :
    (family P F δ hdir).unionCells=F.unionCells.image (labelMap P δ) := by
  ext q
  simp only [TubeFamily.unionCells,family,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · rintro ⟨i,z,hz,heq⟩
    exact ⟨z,⟨i,hz⟩,heq⟩
  · rintro ⟨z,⟨i,hz⟩,heq⟩
    exact ⟨i,z,hz,heq⟩

theorem union_card_le {n d M : ℕ} (P : Space n →L[ℝ] Space d) (F : TubeFamily n M)
    (δ : ℝ) (hdir : ∀ i, ‖P (F.tube i).direction‖ ≠ 0) :
    (family P F δ hdir).unionCells.card ≤ F.unionCells.card := by
  rw [union_image]
  exact Finset.card_image_le

/-- Both row bounds concern the actual image of the original same-index row. -/
theorem row_card_bounds {n d M : ℕ} (P : Space n →L[ℝ] Space d) (F : TubeFamily n M)
    (hdir : ∀ i, ‖P (F.tube i).direction‖ ≠ 0) {δ c K width : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hK : ‖P‖ ≤ K)
    (hgood : ∀ i, c ≤ ‖P (F.tube i).direction‖) (hadm : F.Admissible width δ) :
    ∀ i, ((F.shade i).card:ℝ)/(fiberConstant n d c K width:ℝ) ≤
        (((family P F δ hdir).shade i).card:ℝ) ∧
      (((family P F δ hdir).shade i).card:ℝ) ≤ (F.shade i).card := by
  intro i
  exact ⟨image_card_lower P (F.tube i) hδ hc hK (hgood i) (F.shade i) (hadm i),
    by exact_mod_cast Finset.card_image_le (s:=F.shade i) (f:=labelMap P δ)⟩

/-- Original comparable density yields fixed comparable projected density;
the image need not be padded or retaken to achieve its lower bound. -/
theorem density_bounds {n d M : ℕ} (P : Space n →L[ℝ] Space d) (F : TubeFamily n M)
    (hdir : ∀ i, ‖P (F.tube i).direction‖ ≠ 0) {δ c K width lam : ℝ}
    (hδ : 0 < δ) (hc : 0 < c) (hK : ‖P‖ ≤ K)
    (hgood : ∀ i, c ≤ ‖P (F.tube i).direction‖) (hadm : F.Admissible width δ)
    (hcomp : F.Comparable δ lam) :
    ∀ i, lam/((fiberConstant n d c K width:ℝ)*δ) ≤
        (((family P F δ hdir).shade i).card:ℝ) ∧
      (((family P F δ hdir).shade i).card:ℝ) ≤ 2*lam/δ := by
  intro i
  obtain ⟨hl,hu⟩ := row_card_bounds P F hdir hδ hc hK hgood hadm i
  have hC : 0 ≤ (fiberConstant n d c K width:ℝ) := Nat.cast_nonneg _
  refine ⟨?_,hu.trans (hcomp i).2⟩
  have hh := div_le_div_of_nonneg_right (hcomp i).1 hC
  have hh' : lam/((fiberConstant n d c K width:ℝ)*δ) ≤ (F.shade i).card/(fiberConstant n d c K width:ℝ) := by
    simpa only [div_div,mul_comm] using hh
  exact hh'.trans hl

/-- A bounded original family stays bounded under the actual projected bases. -/
theorem bounded {n d M : ℕ} (P : Space n →L[ℝ] Space d) (F : TubeFamily n M)
    (δ : ℝ) (hdir : ∀ i, ‖P (F.tube i).direction‖ ≠ 0) {K R : ℝ}
    (hK : ‖P‖ ≤ K) (hF : F.Bounded R) :
    (family P F δ hdir).Bounded (K*R) := by
  intro i
  exact (P.le_opNorm (F.tube i).base).trans
    (mul_le_mul hK (hF i) (norm_nonneg _) ((norm_nonneg P).trans hK))

/-- A complete actual projected family from the original geometric data.
Every asserted carrier, image, union and cardinality conclusion is derived;
there is no fiber-count or output-geometry assumption. The normalized
projected directions are explicitly identified for later collision extraction. -/
theorem construct {n d M : ℕ} (P : Space n →L[ℝ] Space d) (F : TubeFamily n M)
    {δ c K width : ℝ} (hδ : 0 < δ) (hc : 0 < c) (hK : ‖P‖ ≤ K)
    (hgood : ∀ i, c ≤ ‖P (F.tube i).direction‖) (hadm : F.Admissible width δ) :
    ∃ H : TubeFamily d M,
      (∀ i, H.shade i=(F.shade i).image (labelMap P δ)) ∧
      (∀ i, (H.tube i).base=P (F.tube i).base ∧
        (H.tube i).direction=‖P (F.tube i).direction‖⁻¹ • P (F.tube i).direction) ∧
      (∀ i, c ≤ lengths P F i ∧ lengths P F i ≤ K) ∧
      (∀ i q, q∈H.shade i → cellCenter δ q ∈
        lengthCarrier (H.tube i) (lengths P F i) ((K*width+(d:ℝ)/2)*δ)) ∧
      H.unionCells=F.unionCells.image (labelMap P δ) ∧
      H.unionCells.card ≤ F.unionCells.card ∧
      (∀ i, ((F.shade i).card:ℝ)/(fiberConstant n d c K width:ℝ) ≤ ((H.shade i).card:ℝ) ∧
        ((H.shade i).card:ℝ) ≤ (F.shade i).card) := by
  let hd : ∀ i, ‖P (F.tube i).direction‖ ≠ 0 := fun i => (hc.trans_le (hgood i)).ne'
  refine ⟨family P F δ hd,fun _ => rfl,fun _ => ⟨rfl,rfl⟩,
    length_bounds P F hK hgood,family_carrier P F hd hδ hK hadm,
    union_image P F δ hd,union_card_le P F δ hd,?_⟩
  exact row_card_bounds P F hd hδ hc hK hgood hadm

end
end KakeyaFormal.ProjectedGridFamily
