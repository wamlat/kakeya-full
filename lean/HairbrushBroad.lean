import HairbrushSelection

/-!
# Broad marked mass yields a real geometric hairbrush

The stem and bristles are selected from actual measurable shadings. Original
bristle shadings are retained in full; this removes the manuscript's additional
retention step without changing the global union or two-ends assumptions.
-/
namespace KakeyaFormal.HairbrushBroad
open MeasureTheory
open scoped ENNReal
open KakeyaFormal.MeasurableEnergy KakeyaFormal.HairbrushSelection
open KakeyaFormal.HairbrushStem KakeyaFormal.TubeVolume
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {ι : Type*} [Fintype ι]

/-- The actual number of original shading directions within the indicated
projective angle of the chosen tube direction at a physical point. -/
def nearCount {k : ℕ} (T : ι → UnitTube k) (Y : ι → Set (Space k))
    (stem : ι) (theta : ℝ) (x : Space k) : ℕ := by
  classical
  exact ((Finset.univ.filter fun i => x ∈ Y i).filter
    fun i => projectiveDistance (T stem).direction (T i).direction < theta).card

/-- The actual finite transverse bristles meeting a specified stem portion. -/
def bristles {k : ℕ} (T : ι → UnitTube k) (Y : ι → Set (Space k))
    (stem : ι) (theta : ℝ) (S : Set (Space k)) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => theta ≤ projectiveDistance (T stem).direction (T i).direction ∧
    (S ∩ Y i).Nonempty

omit [Fintype ι] in
/-- Restricting to actual finite original indices gives exactly the corresponding
filtered incidence count. -/
theorem overlap_restrict {X : Type*} (Y : ι → Set X) (H : Finset ι) (x : X) :
    overlapCount (fun i : {i // i ∈ H} => Y i.1) x = (H.filter fun i => x ∈ Y i).card := by
  classical
  unfold overlapCount
  apply Finset.card_bij (fun i _ => i.1)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨i.2,(Finset.mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact Subtype.ext hij
  · intro i hi
    exact ⟨⟨i,(Finset.mem_filter.mp hi).1⟩,by simpa using (Finset.mem_filter.mp hi).2,rfl⟩

/-- Actual transverse bristles account for every incident direction outside the
small stem cap. No transverse incidence lower bound is postulated. -/
theorem bristle_multiplicity {k : ℕ} (T : ι → UnitTube k) (Y : ι → Set (Space k))
    (stem : ι) (theta : ℝ) (S : Set (Space k)) {x : Space k} (hx : x ∈ S) :
    (nearCount T Y stem theta x:ℝ)+
      (overlapCount (fun i : {i // i ∈ bristles T Y stem theta S} => Y i.1) x:ℝ) =
        MeasurableEnergy.multiplicity Y x := by
  classical
  have hid : ((Finset.univ.filter fun i => x ∈ Y i).filter
      fun i => ¬projectiveDistance (T stem).direction (T i).direction < theta) =
        (bristles T Y stem theta S).filter (fun i => x ∈ Y i) := by
    ext i
    simp only [bristles,Finset.mem_filter,Finset.mem_univ,true_and,not_lt]
    constructor
    · intro hi
      exact ⟨⟨hi.2,⟨x,hx,hi.1⟩⟩,hi.1⟩
    · intro hi
      exact ⟨hi.2,hi.1.1⟩
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun i => x ∈ Y i)
    (fun i => projectiveDistance (T stem).direction (T i).direction < theta)
  rw [hid] at h
  rw [overlap_restrict,multiplicity_eq_card]
  exact_mod_cast h

/-- Half-cap broadness gives an actual positive fraction of transverse bristle
incidence at every selected stem point. -/
theorem bristle_multiplicity_lower {k : ℕ} (T : ι → UnitTube k) (Y : ι → Set (Space k))
    (stem : ι) (theta : ℝ) (S : Set (Space k)) {x : Space k} {mu : ℝ} (hx : x ∈ S)
    (hmass : 2*mu ≤ MeasurableEnergy.multiplicity Y x)
    (hbroad : (nearCount T Y stem theta x:ℝ) ≤ MeasurableEnergy.multiplicity Y x/2) :
    mu ≤ (overlapCount (fun i : {i // i ∈ bristles T Y stem theta S} => Y i.1) x:ℝ) := by
  have h := bristle_multiplicity T Y stem theta S hx
  linarith

/-- Constant for the squared broad hairbrush bound. -/
def broadConstant (k : ℕ) : ℝ := 32*stemConstant k

theorem broadConstant_pos (k : ℕ) : 0 < broadConstant k := by
  exact mul_pos (by norm_num) (stemConstant_pos k)

/-- The complete fine-scale broad hairbrush estimate, in squared form. The
actual multiplicity level, actual stem, actual transverse bristles, crossing
points and plane bins are all constructed. The angular premise is a literal
cap count at each marked physical point, not a geometric incidence conclusion. -/
theorem broad_hairbrush_squared [Nonempty ι] {k : ℕ}
    (T : ι → UnitTube (k+2)) (Y : ι → Set (Space (k+2))) (G : Set (Space (k+2)))
    {δ theta r lam L B alpha : ℝ} (J : ℕ)
    (hδ : 0 < δ) (htheta : 0 < theta) (htheta1 : theta ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1) (hscale : 88*δ ≤ r*theta)
    (hlam : 0 ≤ lam) (hL : 0 < L) (hJL : (J:ℝ)+1 ≤ L)
    (hlogL : Real.logb 2 (2/δ)+2 ≤ L) (htop : (Fintype.card ι:ℝ) ≤ (2:ℝ)^J)
    (hdir : ∀ i j, i ≠ j → δ ≤ projectiveDistance (T i).direction (T j).direction)
    (hY : ∀ i, MeasurableSet (Y i)) (hsub : ∀ i, Y i ⊆ (T i).carrier δ)
    (hG : MeasurableSet G)
    (hgood : (∑ i, (volume : Measure (Space (k+2))).real (Y i))/2 ≤ markedMass (ν := volume) Y G)
    (hbroad : ∀ x ∈ G, ∀ i, x ∈ Y i →
      (nearCount T Y i theta x:ℝ) ≤ MeasurableEnergy.multiplicity Y x/2)
    (hmass : ∀ i, lam*δ^(k+1) ≤ (volume : Measure (Space (k+2))).real (Y i))
    (hends : ∀ i p t, δ ≤ t → t ≤ 1 →
      (volume : Measure (Space (k+2))).real (Y i ∩ Metric.closedBall p t) ≤
        B*t^alpha*(volume : Measure (Space (k+2))).real (Y i))
    (hsmall : B*r^alpha ≤ 1/2) :
    markedMass (ν := volume) Y G*lam^3*δ^k*(r*theta)^(k+1)/(broadConstant k*L^5) ≤
      ((volume : Measure (Space (k+2))).real (⋃ i, Y i))^2 := by
  have hfin (i : ι) : (volume : Measure (Space (k+2))) (Y i) ≠ ∞ :=
    measure_ne_top_of_subset (hsub i) (carrier_finite (T i) δ)
  obtain ⟨j,_,hj⟩ := exists_mass_shell Y G hfin J htop
  obtain ⟨stem,hstem⟩ := exists_stem_in_shell Y G hgood hj
  let S := Y stem ∩ multiplicityShell Y G j
  let H := bristles T Y stem theta S
  let mu : ℝ := (2:ℝ)^j/4
  have hmu : 0 < mu := by dsimp [mu]; positivity
  have hL1 : 1 ≤ L := by linarith [show (0:ℝ) ≤ J from Nat.cast_nonneg J]
  have hSmass : (lam/2)*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real S := by
    have h₁ := div_le_div_of_nonneg_left (by positivity : 0 ≤ lam*δ^(k+1))
      (by positivity : 0 < 2*((J:ℝ)+1)) (by linarith : 2*((J:ℝ)+1) ≤ 2*L)
    have h₂ := div_le_div_of_nonneg_right (hmass stem) (by positivity : 0 ≤ 2*((J:ℝ)+1))
    have hid : (lam/2)*δ^(k+1)/L = lam*δ^(k+1)/(2*L) := by field_simp
    rw [hid]
    exact h₁.trans (h₂.trans hstem)
  have hmass' (i : ι) : (lam/2)*δ^(k+1)/L ≤ (volume : Measure (Space (k+2))).real (Y i) := by
    have hid : (lam/2)*δ^(k+1)/L = lam*δ^(k+1)/(2*L) := by field_simp
    rw [hid]
    exact (div_le_self (by positivity : 0 ≤ lam*δ^(k+1)) (by linarith : 1 ≤ 2*L)).trans (hmass i)
  have hH (i : {i : ι // i ∈ H}) :
      theta ≤ projectiveDistance (T stem).direction (T i.1).direction ∧ (S ∩ Y i.1).Nonempty :=
    (Finset.mem_filter.mp i.2).2
  have hpoint (x : Space (k+2)) (hx : x ∈ S) :
      mu ≤ (overlapCount (fun i : {i : ι // i ∈ H} => Y i.1) x:ℝ) := by
    apply bristle_multiplicity_lower T Y stem theta S hx
    · have hlow := (shell_bounds Y G hx.2 (Set.mem_iUnion.mpr ⟨stem,hx.1⟩)).1
      dsimp [mu]
      linarith
    · exact hbroad x hx.2.1 stem hx.1
  have hhair := stem_hairbrush_union_lower (T stem) (fun i : {i : ι // i ∈ H} => T i.1)
    (fun i => Y i.1) S hδ htheta htheta1 hr hr1 hscale hmu.le (by positivity : 0 ≤ lam/2)
    hL hlogL (fun i => (hH i).1)
    (fun i l hil => hdir i.1 l.1 (fun he => hil (Subtype.ext he)))
    (fun i => hY i.1) (fun i => hsub i.1) ((hY stem).inter (shell_measurable Y G hY hG j))
    (fun _ hx => hsub stem hx.1) hSmass (fun i => (hH i).2) hpoint (fun i => hmass' i.1)
    (fun i => hends i.1) hsmall
  have hUf : (volume : Measure (Space (k+2))) (⋃ i, Y i) ≠ ∞ := by
    simpa only [Set.biUnion_univ] using measure_biUnion_ne_top (μ := (volume : Measure (Space (k+2))))
      (s := Set.univ) (f := Y) (Set.toFinite _) (fun i _ => hfin i)
  have hE := hhair.trans (measureReal_mono
    (by intro x hx; obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx; exact Set.mem_iUnion.mpr ⟨i.1,hi⟩) hUf)
  have hW0 : 0 ≤ markedMass (ν := volume) Y G := Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  have hW := (div_le_div_of_nonneg_left hW0 (by positivity : 0 < (J:ℝ)+1) hJL).trans hj
  have hlevel := hW.trans (shell_mass_union_upper Y G hY hG hfin j)
  have hbranch : markedMass (ν := volume) Y G/(L*((2:ℝ)^j)) ≤
      (volume : Measure (Space (k+2))).real (⋃ i, Y i) := by
    apply (div_le_iff₀ (by positivity : 0 < L*((2:ℝ)^j))).mpr
    have hh := (div_le_iff₀ hL).mp hlevel
    nlinarith
  have hprod := mul_le_mul hbranch hE
    (by have hc := stemConstant_pos k; positivity : 0 ≤ mu*(lam/2)^3*theta*δ^k*(r*theta)^k/(stemConstant k*L^4))
    (measureReal_nonneg : 0 ≤ (volume : Measure (Space (k+2))).real (⋃ i, Y i))
  have hid : (markedMass (ν := volume) Y G/(L*((2:ℝ)^j))) *
      (mu*(lam/2)^3*theta*δ^k*(r*theta)^k/(stemConstant k*L^4)) =
      markedMass (ν := volume) Y G*lam^3*δ^k*((r*theta)^k*theta)/(broadConstant k*L^5) := by
    dsimp [mu,broadConstant]
    field_simp
    ring
  rw [hid,← pow_two] at hprod
  have hrt : r*theta ≤ theta := by nlinarith
  have hpow : (r*theta)^(k+1) ≤ (r*theta)^k*theta := by
    rw [pow_succ]
    exact mul_le_mul_of_nonneg_left hrt (by positivity)
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ markedMass (ν := volume) Y G*lam^3*δ^k))
    (by have hc := broadConstant_pos k; positivity : 0 ≤ broadConstant k*L^5)
  exact hm.trans hprod

end
end KakeyaFormal.HairbrushBroad

#print axioms KakeyaFormal.HairbrushBroad.broad_hairbrush_squared
