import MeasurableUnitPartition
import MaximalShading

/-! Remove the bounded-position convention in the literal measurable maximal
formula. Every tube survives in one actual unit spatial bin, with a fixed
fraction of its shading. Shared translations preserve exact tube volumes. -/
namespace KakeyaFormal.MaximalPositionReduction
open Finset MeasureTheory MeasurableUnitPartition SpatialMarkedPartition
open Rescaling MeasurableRescaling
open scoped ENNReal
noncomputable section
open Classical

/-- Pure translation takes the actual full tube carrier to the translated
unit tube carrier, with no width, length, or volume approximation. -/
theorem translated_carrier {n : ℕ} (T : UnitTube n) (origin : Space n) (δ : ℝ) :
    rescale 1 origin '' T.carrier δ = (Rescaling.tube T 1 origin 0).carrier δ := by
  have haxis (t : ℝ) : rescale 1 origin (T.axisPoint t) =
      (Rescaling.tube T 1 origin 0).axisPoint t := by
    simpa only [zero_add,one_mul] using rescale_axisPoint T (by norm_num : (1:ℝ)≠0) origin 0 t
  ext x
  constructor
  · rintro ⟨y,⟨t,ht,hd⟩,rfl⟩
    refine ⟨t,ht,?_⟩
    rw [← haxis,rescale_distance (by norm_num),div_one]
    exact hd
  · rintro ⟨t,ht,hd⟩
    refine ⟨inverse 1 origin x,⟨t,ht,?_⟩,rescale_inverse (by norm_num) origin x⟩
    have hh := rescale_distance (by norm_num : (0:ℝ)<1) origin
      (inverse 1 origin x) (T.axisPoint t)
    rw [rescale_inverse (by norm_num),haxis,div_one] at hh
    exact hh ▸ hd

theorem translated_tube_volume {n : ℕ} (T : UnitTube n) (origin : Space n) (δ : ℝ) :
    (volume : Measure (Space n)).real ((Rescaling.tube T 1 origin 0).carrier δ) =
      (volume : Measure (Space n)).real (T.carrier δ) := by
  rw [← translated_carrier]
  simpa only [one_pow,div_one] using image_volume (by norm_num : (0:ℝ)<1) origin (T.carrier δ)

def translatedFamily {n M : ℕ} (F : TubeFamily n M) (assign : Fin M → Cell n) (q : Cell n) :
    TubeFamily n (indices assign q).card where
  tube i := Rescaling.tube (F.tube (MeasurableMarkedSelection.index (indices assign q) i))
    1 (cellCenter 1 q) 0
  shade _ := ∅

def translatedShading {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) (q : Cell n) (i : Fin (indices P.assignment q).card) : Set (Space n) :=
  rescale 1 (cellCenter 1 q) '' Full P.selected P.assignment q i

theorem translated_bounded {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) (q : Cell n) :
    (translatedFamily F P.assignment q).Bounded (radius n) := by
  intro i
  have hb := P.bounded (MeasurableMarkedSelection.index (indices P.assignment q) i)
  rw [index_label P.assignment q i] at hb
  simpa only [translatedFamily,Rescaling.tube,rescale,UnitTube.axisPoint,zero_smul,
    add_zero,inv_one,one_smul,dist_eq_norm] using hb

theorem translated_separated {n M : ℕ} (F : TubeFamily n M) (assign : Fin M → Cell n)
    {r : ℝ} (hsep : F.Separated r) (q : Cell n) :
    (translatedFamily F assign q).Separated r := by
  intro i j hij
  exact hsep _ _ (fun he => hij (MeasurableMarkedSelection.index_injective (indices assign q) he))

theorem translated_measurable {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) (hY : ∀ i, MeasurableSet (Y i)) (q : Cell n)
    (i : Fin (indices P.assignment q).card) : MeasurableSet (translatedShading P q i) :=
  image_measurable (by norm_num) _ ((hY _).inter (GridCells.measurable_gridCell 1 _))

theorem translated_subset {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) {δ : ℝ} (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (q : Cell n) (i : Fin (indices P.assignment q).card) :
    translatedShading P q i ⊆ ((translatedFamily F P.assignment q).tube i).carrier δ := by
  change rescale 1 (cellCenter 1 q) '' _ ⊆
    (Rescaling.tube (F.tube (MeasurableMarkedSelection.index (indices P.assignment q) i))
      1 (cellCenter 1 q) 0).carrier δ
  rw [← translated_carrier]
  exact Set.image_mono (Set.inter_subset_left.trans (hsub _))

theorem translated_density {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) {δ lam : ℝ}
    (hmass : ∀ i, lam*(volume : Measure (Space n)).real ((F.tube i).carrier δ) ≤
      (volume : Measure (Space n)).real (Y i))
    (q : Cell n) (i : Fin (indices P.assignment q).card) :
    (lam/(binsPerTube n:ℝ))*(volume : Measure (Space n)).real
      (((translatedFamily F P.assignment q).tube i).carrier δ) ≤
        (volume : Measure (Space n)).real (translatedShading P q i) := by
  have hK : (0:ℝ)<binsPerTube n := Nat.cast_pos.mpr (binsPerTube_pos n)
  change (lam/(binsPerTube n:ℝ))*(volume : Measure (Space n)).real
    ((Rescaling.tube _ 1 _ 0).carrier δ) ≤ (volume : Measure (Space n)).real (rescale 1 _ '' _)
  rw [translated_tube_volume,image_volume (by norm_num),one_pow,div_one]
  have hh := (hmass (MeasurableMarkedSelection.index (indices P.assignment q) i)).trans
    (P.retention (MeasurableMarkedSelection.index (indices P.assignment q) i))
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hK).mpr
  simpa only [Full,MeasurableMarkedSelection.reindex,Partition.selected,mul_comm] using hh

theorem translated_union_volume {n M : ℕ} {F : TubeFamily n M} {Y : Fin M → Set (Space n)}
    (P : Partition F Y) (q : Cell n) :
    (volume : Measure (Space n)).real (⋃ i, translatedShading P q i) =
      (volume : Measure (Space n)).real (P.group q) := by
  simp only [translatedShading,← Set.image_iUnion]
  simpa only [Partition.group,one_pow,div_one] using
    image_volume (by norm_num : (0:ℝ)<1) (cellCenter 1 q) (P.group q)

/-- The weight is the sum of actual tube volumes, retained once per original
tube. This avoids introducing a tube-volume comparability constant. -/
theorem translated_volume_sum {n M : ℕ} (F : TubeFamily n M) (assign : Fin M → Cell n) (δ : ℝ) :
    (∑ q ∈ labels assign, ∑ i, (volume : Measure (Space n)).real
      (((translatedFamily F assign q).tube i).carrier δ)) =
      ∑ i, (volume : Measure (Space n)).real ((F.tube i).carrier δ) := by
  change (∑ q ∈ labels assign, ∑ i, (volume : Measure (Space n)).real
    ((Rescaling.tube _ 1 _ 0).carrier δ)) = _
  simp_rw [translated_tube_volume]
  exact full_mass_partition (volume : Measure (Space n)) (fun i => (F.tube i).carrier δ) assign

/-- The bounded-position convention implies the literal unrestricted-position
maximal estimate. All groups and translations are constructed from the actual
shadings; the only loss is the fixed fraction in each tube's selected cell. -/
theorem bounded_to_unbounded {n : ℕ} {d : ℝ} (h : MaximalShading.BoundedEstimate n d) :
    MaximalShading.Estimate n d := by
  intro separation hsep0 eps heps
  have hradius : 0 < radius n := by dsimp [radius]; positivity
  let geom : MeasurableNormalization := ⟨separation,radius n,hsep0,hradius⟩
  obtain ⟨c,hc,hbound⟩ := h geom eps heps
  let K : ℝ := binsPerTube n
  have hK : 0 < K := Nat.cast_pos.mpr (binsPerTube_pos n)
  have hK1 : 1 ≤ K := by
    have hn : 1 ≤ binsPerTube n := Nat.succ_le_iff.mpr (binsPerTube_pos n)
    change (1:ℝ) ≤ (binsPerTube n:ℝ)
    exact_mod_cast hn
  refine ⟨c/K^d,by positivity,?_⟩
  intro M F δ lam Y hδ hδ1 hlam hlam1 hY hsub hmass hsep
  have hpositive (i : Fin M) : 0 < (volume : Measure (Space n)).real (Y i) := by
    have hv := TubeVolume.carrier_volume_lower (F.tube i) hδ
    have hp := TubeVolume.unitBallVolume_pos n
    have ht : 0 < (volume : Measure (Space n)).real ((F.tube i).carrier δ) :=
      (by positivity : 0 < (TubeVolume.unitBallVolume n/((2:ℝ)^(n+1)))*δ^n/δ).trans_le hv
    exact (mul_pos hlam ht).trans_le (hmass i)
  obtain ⟨P⟩ := MeasurableUnitPartition.construct F Y hδ1 hY hsub hpositive
  have hfinite : (volume : Measure (Space n)) (⋃ i, Y i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ:=(volume : Measure (Space n)))
      (s:=Set.univ) (f:=Y) (Set.toFinite _)
      (fun i _ => measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite (F.tube i) δ))
  have hlocal (q : Cell n) :
      c*δ^((n:ℝ)-d+eps)*(lam/K)^d*
        (∑ i, (volume : Measure (Space n)).real (((translatedFamily F P.assignment q).tube i).carrier δ)) ≤
          (volume : Measure (Space n)).real (P.group q) := by
    have hnew : lam/K ≤ 1 := (div_le_one hK).mpr (hlam1.trans hK1)
    have hh := hbound (translatedFamily F P.assignment q) (translatedShading P q)
      hδ hδ1 (div_pos hlam hK) hnew (translated_measurable P hY q)
      (translated_subset P hsub q) (translated_density P hmass q)
      (translated_separated F P.assignment hsep q) (translated_bounded P q)
    rwa [translated_union_volume] at hh
  have hsum := sum_le_sum (s:=labels P.assignment) (fun q _ => hlocal q)
  have hpop := translated_volume_sum F P.assignment δ
  have hbound' : c*δ^((n:ℝ)-d+eps)*(lam/K)^d*
      (∑ i, (volume : Measure (Space n)).real ((F.tube i).carrier δ)) ≤
        (volume : Measure (Space n)).real (⋃ i, Y i) := by
    rw [← hpop,mul_sum]
    exact hsum.trans (P.union_sum hY hfinite)
  have hid : (c/K^d)*δ^((n:ℝ)-d+eps)*lam^d = c*δ^((n:ℝ)-d+eps)*(lam/K)^d := by
    rw [Real.div_rpow hlam.le hK.le]
    ring
  rw [hid]
  exact hbound'

end
end KakeyaFormal.MaximalPositionReduction
