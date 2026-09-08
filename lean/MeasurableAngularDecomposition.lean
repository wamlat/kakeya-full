import MeasurableAngularSpatial

/-! The actual measurable angular-spatial decomposition of Lemma 3.2.
The output is constructed from the original shadings; there is no supplied
angular decomposition, spatial cover, retention bound or broadness premise.
The exact depth loss is stronger than the stated cubic logarithmic loss. -/
namespace KakeyaFormal.MeasurableAngularDecomposition
open MeasureTheory Set AngularDecomposition MeasurableAngularSpatial
open scoped ENNReal
noncomputable section
open Classical

def retentionConstant (k : ℕ) : ℝ :=
  9*(Real.log (2:ℝ))^3/(32*AngularSeedPieces.angularConstant k)

theorem retentionConstant_pos (k : ℕ) : 0 < retentionConstant k := by
  unfold retentionConstant
  positivity [Real.log_pos (by norm_num : (1:ℝ)<2),AngularSeedPieces.angularConstant_pos k]

/-- The actual dyadic depth costs at most the source's L^(-3), uniformly even
when log(2/delta) is below one. -/
theorem cubic_log_rate (k J : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hdepth : (J:ℝ) ≤ Real.log (1/δ)/Real.log 2) :
    retentionConstant k*(Real.log (2/δ))^(-(3:ℝ)) ≤
      (3/4:ℝ)*AngularSeedPieces.retentionRate k J := by
  let L := Real.log (2/δ)
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hLmin : Real.log (2:ℝ) ≤ L := Real.log_le_log (by norm_num)
    ((le_div_iff₀ hδ).mpr (by linarith))
  have hL : 0 < L := hlog.trans_le hLmin
  have hJ : 0 < (J:ℝ)+1 := by positivity
  have hident : Real.log (1/δ)/Real.log 2+1 = L/Real.log 2 := by
    dsimp only [L]
    rw [Real.log_div one_ne_zero hδ.ne',Real.log_one,
      Real.log_div (by norm_num : (2:ℝ)≠0) hδ.ne']
    field_simp
    ring
  have hJL : ((J:ℝ)+1)*Real.log 2 ≤ L :=
    (le_div_iff₀ hlog).mp (by rw [← hident]; linarith)
  have hpow : (Real.log (2:ℝ))^3*((J:ℝ)+1) ≤ L^3 := by
    have hsq : (Real.log (2:ℝ))^2 ≤ L^2 := pow_le_pow_left₀ hlog.le hLmin 2
    calc
      _ = (Real.log (2:ℝ))^2*(((J:ℝ)+1)*Real.log 2) := by ring
      _ ≤ L^2*L := mul_le_mul hsq hJL (by positivity) (by positivity)
      _ = _ := by ring
  have hC := AngularSeedPieces.angularConstant_pos k
  have hpower : (Real.log (2/δ))^(-(3:ℝ)) = 1/L^3 := by
    rw [Real.rpow_neg hL.le]
    simp only [Real.rpow_ofNat,one_div]
  rw [hpower]
  have hdiv : (Real.log (2:ℝ))^3/L^3 ≤ 1/((J:ℝ)+1) :=
    (div_le_div_iff₀ (pow_pos hL 3) hJ).mpr (by simpa only [one_mul] using hpow)
  have hh := mul_le_mul_of_nonneg_left hdiv
    (show 0 ≤ 9/(32*AngularSeedPieces.angularConstant k) by positivity)
  calc
    _ = (9/(32*AngularSeedPieces.angularConstant k))*((Real.log (2:ℝ))^3/L^3) := by
      unfold retentionConstant
      ring
    _ ≤ (9/(32*AngularSeedPieces.angularConstant k))*(1/((J:ℝ)+1)) := hh
    _ = _ := by
      unfold AngularSeedPieces.retentionRate
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring

/-- Empty original families are included, without introducing a fictitious
direction or a nonempty angular cap. -/
theorem exists_angular_pieces {k M : ℕ} (F : TubeFamily (k+1) M)
    (Y : Fin M → Set (Space (k+1))) {δ beta : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta)
    (hY : ∀ i, MeasurableSet (Y i)) (hfin : ∀ i, volume (Y i) ≠ ∞) :
    Nonempty (MeasurableAngularPieces.Pieces F Y δ beta) := by
  by_cases hM : 0 < M
  · exact MeasurableAngularPieces.exists_pieces F hM Y hY hfin hδ hδ1 hb
  · have hz : M=0 := by omega
    subst M
    have hdepth : (0:ℝ) ≤ Real.log (1/δ)/Real.log 2 :=
      div_nonneg (Real.log_nonneg ((one_le_div hδ).mpr hδ1))
        (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    refine ⟨{
      J := 0, tau := δ, groups := ∅, assign := id, shading := fun _ _ => ∅,
      depth := by simpa using hdepth, lower_scale := le_rfl, upper_scale := hδ1,
      assign_mem := fun i => Fin.elim0 i,
      measurable := fun g => Fin.elim0 g,
      finite := fun g => Fin.elim0 g,
      subset := fun g => Fin.elim0 g,
      unique := fun g => Fin.elim0 g,
      local_cap := fun g => Fin.elim0 g,
      retained := by simp,
      broad := fun _ g => Fin.elim0 g,
      overlap := by intro x; simp; positivity }⟩

/-- A constructed angular piece object with all spatial and measured
conclusions at one common scale. The families and sets are the concrete
definitions in MeasurableAngularSpatial, indexed by finite angular labels
and their actual occupied finite spatial-label sets. -/
structure Decomposition {k M : ℕ} (F : TubeFamily (k+1) M)
    (Y : Fin M → Set (Space (k+1))) (δ beta width : ℝ) where
  angular : MeasurableAngularPieces.Pieces F Y δ beta
  retained : retentionConstant k*(Real.log (2/δ))^(-(3:ℝ))*(∑ i,volume.real (Y i)) ≤
    ∑ g ∈ angular.groups, ∑ q ∈ labels angular g, ∑ i,volume.real (shading angular width g q i)
  overlap : ∀ x, (∑ g ∈ angular.groups, ((occupied angular width g x).card:ℝ)) ≤
    (2*(spatialConstant k width:ℝ))*angular.tau^(-beta)
  broad : ∀ g ∈ angular.groups, ∀ q, ∀ x,
    Broad (family angular g q) (Finset.univ.filter (fun i => x ∈ shading angular width g q i))
      δ beta angular.tau (64*AngularSeedPieces.angularConstant k*spatialConstant k width)
  containing_box : ∀ g ∈ angular.groups, ∀ q i,
    ((family angular g q).tube i).carrier (width*δ) ⊆
      SpatialTubeCover.parallelBox (F.tube g).direction angular.tau q
        (2+width) ((k:ℝ)+width+3)
  containing_tube : ∀ g ∈ angular.groups, ∀ q i,
    ((family angular g q).tube i).carrier (width*δ) ⊆
      SamplingGeometry.lengthCarrier
        (SpatialTubeCover.containingTube (F.tube g).direction (F.tube g).unit_direction
          angular.tau q (2+width)) (2*(2+width)) (((k:ℝ)+width+3)*angular.tau)

/-- Literal measurable Lemma 3.2 at every physical mesh in (0,1], with fixed
width. The positive retention coefficient and broadness/overlap constants
depend only on dimension and fixed width, including uniformly 0<beta<=1.
Direction separation is inherited when present; construction does not need it. -/
theorem construct {k M : ℕ} (F : TubeFamily (k+1) M)
    (Y : Fin M → Set (Space (k+1))) {δ beta width : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hb : 0 ≤ beta) (hb1 : beta ≤ 1) (hw : 0 ≤ width)
    (hY : ∀ i, MeasurableSet (Y i))
    (hcarrier : ∀ i, Y i ⊆ (F.tube i).carrier (width*δ)) :
    Nonempty (Decomposition F Y δ beta width) := by
  have hf (i) : volume (Y i) ≠ ∞ :=
    measure_ne_top_of_subset (hcarrier i) (TubeVolume.carrier_finite _ _)
  obtain ⟨P⟩ := exists_angular_pieces F Y hδ hδ1 hb hY hf
  refine ⟨⟨P,?_,total_overlap P hδ hδ1 hw hcarrier,?_,
    fun g hg q i => containing_box P g hg q i hδ hδ1 hw,
    fun g hg q i => containing_tube P g hg q i hδ hδ1 hw⟩⟩
  · exact (mul_le_mul_of_nonneg_right (cubic_log_rate k P.J hδ hδ1 P.depth)
      (Finset.sum_nonneg (fun _ _ => measureReal_nonneg))).trans
      (retained_mass P hδ hδ1 hw hcarrier)
  · intro g hg q x center r hr
    have hh := MeasurableAngularSpatial.broad P (width:=width) hδ g hg q x center r hr
    have hp : (4:ℝ)^beta ≤ 4 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤4) hb1
    have hcoeff : (4:ℝ)^beta*(4*AngularSeedPieces.angularConstant k)*(4*spatialConstant k width) ≤
        64*AngularSeedPieces.angularConstant k*spatialConstant k width := by
      nlinarith [AngularSeedPieces.angularConstant_pos k,
        mul_le_mul_of_nonneg_right hp (show 0 ≤ 16*AngularSeedPieces.angularConstant k*spatialConstant k width by positivity [AngularSeedPieces.angularConstant_pos k])]
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg (div_nonneg (hδ.le.trans hr) (hδ.trans_le P.lower_scale).le) beta))
      (Nat.cast_nonneg _))

end
end KakeyaFormal.MeasurableAngularDecomposition
