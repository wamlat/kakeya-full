import MeasurableAngularPieces
import AngularSeedBound

/-! All-angle hairbrush summation for actual measurable shadings. Angular
pieces, their nonempty families, and the low-mass deletion are all constructed.
This file retains the exact finite-depth constant, including square-root cap
dependence, before any uniform logarithmic simplification. -/
namespace KakeyaFormal.MeasurableAngularHairbrush
open MeasureTheory Set AngularDecomposition MeasurableAngularGroups
open MeasurableAngularPruning MeasurableAngularPieces AngularSeedPieces
open AngularBoxAlgebra HairbrushScales
open scoped ENNReal
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily (k+1) M} {Y : Fin M → Set (Space (k+1))} {δ beta : ℝ}

def keptGroups (P : MeasurableAngularPieces.Pieces F Y δ beta) (lam : ℝ) : Finset (Fin M) :=
  kept volume P.groups P.shading ((retentionRate k P.J/4)*lam)

def groupUnion (P : MeasurableAngularPieces.Pieces F Y δ beta) (g : Fin M) : Set (Space (k+1)) :=
  ⋃ i, P.shading g i

/-- The union-overlap cost is the actual pointwise angular overlap, independent
of the number of atoms, group centers, or tube positions. -/
theorem group_volume_sum (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (G : Finset (Fin M)) (hG : G ⊆ P.groups) (hδ : 0 < δ) (hfin : ∀ i, volume (Y i) ≠ ∞) :
    (∑ g ∈ G, volume.real (groupUnion P g)) ≤
      (2*P.tau^(-beta))*volume.real (⋃ i, Y i) := by
  let Z := fun g : ↥G => groupUnion P g.val
  have hm (g : ↥G) : MeasurableSet (Z g) := MeasurableSet.iUnion (P.measurable g.val)
  have hf (g : ↥G) : volume (Z g) ≠ ∞ := by
    change volume (⋃ i, P.shading g.val i) ≠ ∞
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ:=volume)
      (s:=Set.univ) (f:=P.shading g.val) (Set.toFinite _) (fun i _ => P.finite _ i)
  have hover (x) : (MeasurableEnergy.overlapCount Z x:ℝ) ≤ 2*P.tau^(-beta) := by
    have hc : (Finset.univ.filter (fun g : ↥G => x ∈ Z g)).card ≤
        (P.groups.filter (fun g => ∃ i, x ∈ P.shading g i)).card := by
      apply Finset.card_le_card_of_injOn Subtype.val
      · intro g hg
        exact Finset.mem_filter.mpr ⟨hG g.property,mem_iUnion.mp (Finset.mem_filter.mp hg).2⟩
      · exact fun _ _ _ _ hh => Subtype.val_injective hh
    exact (Nat.cast_le.mpr hc).trans (P.overlap x)
  have hh := MeasurableEnergy.finite_union_overlap Z hm hf hover
  have hs : (⋃ g : ↥G, Z g) ⊆ ⋃ i, Y i := by
    intro x hx
    obtain ⟨g,hg⟩ := mem_iUnion.mp hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hg
    exact mem_iUnion.mpr ⟨i,P.subset _ i hi⟩
  have hyf : volume (⋃ i, Y i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ:=volume)
      (s:=Set.univ) (f:=Y) (Set.toFinite _) (fun i _ => hfin i)
  have hmeasure := measureReal_mono hs hyf
  have hsum : (∑ g : ↥G, volume.real (Z g)) = ∑ g ∈ G, volume.real (groupUnion P g) := by
    exact (Finset.sum_subtype G (fun _ => Iff.rfl) (fun g => volume.real (groupUnion P g))).symm
  rw [hsum] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hmeasure (mul_nonneg (by norm_num)
    (Real.rpow_nonneg (hδ.trans_le P.lower_scale).le _)))

/-- The actual positive single-group constant for directly measurable input. -/
def seedConstant (k J : ℕ) (alpha beta B m A : ℝ) : ℝ :=
  densityConstant k 3 (retentionRate (k+1) J/4) alpha beta B
    (AngularSeedHairbrush.broadConstant (k+1) beta) m A

theorem seedConstant_pos (k J : ℕ) {alpha beta B m A : ℝ}
    (hbeta : 0 ≤ beta) (hB : 1 ≤ B) (hA : 1 ≤ A) :
    0 < seedConstant k J alpha beta B m A :=
  densityConstant_pos k (by norm_num) (div_pos (retentionRate_pos _ _) (by norm_num))
    (zero_lt_one.trans_le hB)
    (zero_lt_one.trans_le (AngularSeedHairbrush.broadConstant_ge_one (k+1) hbeta))
    (zero_lt_one.trans_le hA)

/-- Each actual retained group meets the measurable angular hairbrush premises;
its full sets are the unchanged original full shadings on the same indices. -/
theorem kept_group_hairbrush {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) {δ beta lam alpha B m A : ℝ}
    (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (hδ : 0 < δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hB : 1 ≤ B) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hupper : ∀ i, volume.real (Y i) ≤ 2*lam*δ^(k+1))
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
      B*r^alpha*volume.real (Y i))
    {g : Fin M} (hg : g ∈ keptGroups P (lam*δ^(k+1))) :
    seedConstant k P.J alpha beta B m A*lam^2*((active (P.shading g)).card:ℝ)*
      δ^(k+1)*(δ/P.tau)^((m-1)/2)/(hairbrushLog k (δ/P.tau))^((5:ℝ)/2) ≤
      volume.real (groupUnion P g) := by
  have hgg : g ∈ P.groups := kept_subset volume P.groups P.shading _ hg
  have hgs := kept_spec volume P.groups P.shading _ hg
  have heta1 : retentionRate (k+1) P.J/4 ≤ 1 := by
    have hh := retentionRate_le_one (k+1) P.J
    linarith
  have hmass : (retentionRate (k+1) P.J/4)*lam*δ^(k+1)*((active (P.shading g)).card:ℝ) ≤
      ∑ i, volume.real (compressed (P.shading g) (P.shading g) i) := by
    rw [mass_eq]
    exact (by ring : (retentionRate (k+1) P.J/4)*lam*δ^(k+1)*((active (P.shading g)).card:ℝ) =
      (retentionRate (k+1) P.J/4)*(lam*δ^(k+1))*((active (P.shading g)).card:ℝ)).trans_le hgs.2
  have hh := single_box_quadratic_density (family F (P.shading g))
    (compressed Y (P.shading g)) (compressed (P.shading g) (P.shading g))
    (F.tube g).direction (0:Cell (k+1)) hgs.1 (F.tube g).unit_direction hδ
    P.lower_scale P.upper_scale (by norm_num : (0:ℝ) ≤ 3)
    (div_pos (retentionRate_pos _ _) (by norm_num)) heta1 hlam hlam1 hB halpha
    (AngularSeedHairbrush.broadConstant_ge_one (k+1) hbeta.le) hbeta hm hA
    (compressed_measurable Y _ hY) (compressed_measurable _ _ (P.measurable g))
    (compressed_subset Y _ (P.subset g)) (fun i => hsub (index (P.shading g) i))
    (family_local_cap F _ _ (P.local_cap g hgg)) (family_separated F _ hsep)
    (family_cap_bound F _ hcap) (fun i => hupper (index (P.shading g) i)) hmass
    (family_broad F _ (fun x => P.broad x g hgg))
    (fun i x r hr hr1 => hends (index (P.shading g) i) x r hr hr1)
  simpa only [union_eq,groupUnion,seedConstant] using hh

/-- Summation across the genuinely retained measurable groups. -/
theorem summed_hairbrush {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) {δ beta lam alpha B m A : ℝ}
    (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (hδ : 0 < δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hB : 1 ≤ B) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hlower : ∀ i, lam*δ^(k+1) ≤ volume.real (Y i))
    (hupper : ∀ i, volume.real (Y i) ≤ 2*lam*δ^(k+1))
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
      B*r^alpha*volume.real (Y i)) :
    seedConstant k P.J alpha beta B m A*lam^2*((3*retentionRate (k+1) P.J/8)*(M:ℝ))*
      δ^(k+1)*(δ/P.tau)^((m-1)/2)/(hairbrushLog k (δ/P.tau))^((5:ℝ)/2) ≤
      (2*P.tau^(-beta))*volume.real (⋃ i, Y i) := by
  have hfin (i) : volume (Y i) ≠ ∞ := measure_ne_top_of_subset (hsub i) (TubeVolume.carrier_finite _ _)
  have hprune := P.pruning (mul_pos hlam (pow_pos hδ _)) hfin hlower (by simpa only [mul_assoc] using hupper)
  have hcount := hprune.2.2.2.1
  let G := keptGroups P (lam*δ^(k+1))
  let factor := seedConstant k P.J alpha beta B m A*lam^2*δ^(k+1)*
    (δ/P.tau)^((m-1)/2)/(hairbrushLog k (δ/P.tau))^((5:ℝ)/2)
  have htau := hδ.trans_le P.lower_scale
  have hlog := hairbrushLog_pos (k:=k) (div_pos hδ htau) ((div_le_one htau).mpr P.lower_scale)
  have hfactor : 0 ≤ factor := by dsimp [factor]; positivity [seedConstant_pos k P.J (alpha:=alpha) (m:=m) hbeta.le hB hA]
  have hg (g) (hg : g ∈ G) : factor*((active (P.shading g)).card:ℝ) ≤ volume.real (groupUnion P g) := by
    have hh := kept_group_hairbrush F Y P hδ hlam hlam1 halpha hbeta hB hm hA hY hsub hupper hsep hcap hends hg
    convert hh using 1; dsimp [factor]; ring
  calc
    _ = factor*((3*retentionRate (k+1) P.J/8)*(M:ℝ)) := by dsimp [factor]; ring
    _ ≤ factor*∑ g ∈ G, ((active (P.shading g)).card:ℝ) := mul_le_mul_of_nonneg_left hcount hfactor
    _ = ∑ g ∈ G, factor*((active (P.shading g)).card:ℝ) := Finset.mul_sum _ _ _
    _ ≤ ∑ g ∈ G, volume.real (groupUnion P g) := Finset.sum_le_sum hg
    _ ≤ _ := group_volume_sum P G hprune.1 hδ hfin

/-- Exact measurable seed at its constructed depth, before logarithmic losses.
The right-hand side is the original measurable union, with no grid enlargement. -/
theorem measurable_seed_at_depth {k M : ℕ} (F : TubeFamily (k+2) M)
    (Y : Fin M → Set (Space (k+2))) {δ beta lam alpha B m A : ℝ}
    (P : MeasurableAngularPieces.Pieces F Y δ beta)
    (hδ : 0 < δ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hbetaS : beta ≤ (m-1)/2)
    (hB : 1 ≤ B) (hm : 1 ≤ m) (hA : 1 ≤ A)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (F.tube i).carrier δ)
    (hlower : ∀ i, lam*δ^(k+1) ≤ volume.real (Y i))
    (hupper : ∀ i, volume.real (Y i) ≤ 2*lam*δ^(k+1))
    (hsep : F.Separated δ) (hcap : F.CapBound δ m A)
    (hends : ∀ i x r, δ ≤ r → r ≤ 1 → volume.real (Y i ∩ Metric.closedBall x r) ≤
      B*r^alpha*volume.real (Y i)) :
    (seedConstant k P.J alpha beta B m A*(3*retentionRate (k+1) P.J/16))*lam^2*(M:ℝ)*
      δ^((m-3)/2)/(hairbrushLog k (δ/P.tau))^((5:ℝ)/2) ≤ volume.real (⋃ i, Y i)/δ^(k+2) := by
  have htau := hδ.trans_le P.lower_scale
  have hlog := hairbrushLog_pos (k:=k) (div_pos hδ htau) ((div_le_one htau).mpr P.lower_scale)
  have hsum := summed_hairbrush F Y P hδ hlam hlam1 halpha hbeta hB hm hA
    hY hsub hlower hupper hsep hcap hends
  have hh := AngularSeedBound.cancel_overlap_and_width (W:=1)
    (seedConstant_pos k P.J (alpha:=alpha) (m:=m) hbeta.le hB hA).le (retentionRate_pos (k+1) P.J).le
    (Nat.cast_nonneg M) (pow_pos hδ (k+1)).le hδ htau P.upper_scale (by norm_num)
    (Real.rpow_pos_of_pos hlog ((5:ℝ)/2)) hbetaS
    (by simpa only [div_one] using hsum)
  simp only [div_one] at hh
  have hpow : δ^(k+2)*δ^((m-3)/2) = δ^(k+1)*δ^((m-1)/2) := by
    rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_add hδ,← Real.rpow_add hδ]
    congr 1
    push_cast
    ring
  apply (le_div_iff₀ (pow_pos hδ (k+2))).mpr
  calc
    _ = (seedConstant k P.J alpha beta B m A*(3*retentionRate (k+1) P.J/16))*lam^2*(M:ℝ)*
        (δ^(k+2)*δ^((m-3)/2))/(hairbrushLog k (δ/P.tau))^((5:ℝ)/2) := by ring
    _ = _ := by rw [hpow]; ring
    _ ≤ _ := hh

end
end KakeyaFormal.MeasurableAngularHairbrush
