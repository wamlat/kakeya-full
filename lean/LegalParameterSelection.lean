import TubeGeometry
import GridGeometry

/-! Actual early/late finite parameter selection from interval nonconcentration.
This supplies the finite one-dimensional abundance step for legal pivot samples. -/
namespace KakeyaFormal.LegalParameterSelection
open Finset
noncomputable section
open Classical

/-- A genuine quantile at one of the finitely many occupied parameters. -/
theorem finite_quantile {I : Type*} (S : Finset I) (f : I → ℝ) {t : ℝ}
    (ht : 0 < t) (htotal : t ≤ (S.card:ℝ)) :
    ∃ a ∈ S, ((S.filter (fun i => f i < f a)).card:ℝ) < t ∧
      t ≤ ((S.filter (fun i => f i ≤ f a)).card:ℝ) := by
  have hSne : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast ht.trans_le htotal)
  let C := S.filter (fun a => t ≤ ((S.filter (fun i => f i ≤ f a)).card:ℝ))
  have hC : C.Nonempty := by
    obtain ⟨a,ha,hmax⟩ := S.exists_max_image f hSne
    refine ⟨a,mem_filter.mpr ⟨ha,?_⟩⟩
    have heq : S.filter (fun i => f i ≤ f a) = S := filter_eq_self.mpr hmax
    rwa [heq]
  obtain ⟨a,ha,hmin⟩ := C.exists_min_image f hC
  refine ⟨a,(mem_filter.mp ha).1,?_,(mem_filter.mp ha).2⟩
  by_contra hn
  let P := S.filter (fun i => f i < f a)
  have hPmass : t ≤ (P.card:ℝ) := le_of_not_gt hn
  have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast ht.trans_le hPmass)
  obtain ⟨b,hb,hmax⟩ := P.exists_max_image f hP
  have hba : f b < f a := (mem_filter.mp hb).2
  have heq : S.filter (fun i => f i ≤ f b) = P := by
    ext i
    constructor
    · intro hi
      exact mem_filter.mpr ⟨(mem_filter.mp hi).1,lt_of_le_of_lt (mem_filter.mp hi).2 hba⟩
    · intro hi
      exact mem_filter.mpr ⟨(mem_filter.mp hi).1,hmax i hi⟩
  have hbC : b ∈ C := mem_filter.mpr ⟨(mem_filter.mp hb).1,by rwa [heq]⟩
  have hh := hmin b hbC
  linarith

/-- A substantial positive branch contains two substantial parameter sets
separated from the vertex and from each other by at least kappa. -/
theorem early_late_on_positive_branch {I : Type*} (S P : Finset I) (f : I → ℝ)
    {kappa : ℝ} (hS : 0 < (S.card:ℝ)) (hkappa : 0 < kappa) (hPS : P ⊆ S)
    (hPmass : (S.card:ℝ)/3 ≤ (P.card:ℝ))
    (hPpos : ∀ i ∈ P, kappa ≤ f i)
    (hwindow : ∀ t : ℝ, ((S.filter (fun i => |f i-t| ≤ kappa)).card:ℝ) ≤ (S.card:ℝ)/16) :
    ∃ early late : Finset I, early ⊆ S ∧ late ⊆ S ∧
      (S.card:ℝ)/8 ≤ (early.card:ℝ) ∧ (S.card:ℝ)/8 ≤ (late.card:ℝ) ∧
      ∀ i ∈ early, ∀ j ∈ late, kappa ≤ f i ∧ kappa ≤ f j-f i := by
  obtain ⟨a,ha,hlow,hhigh⟩ := finite_quantile P f (by positivity : 0 < (S.card:ℝ)/8) (by linarith : (S.card:ℝ)/8 ≤ P.card)
  let early := P.filter (fun i => f i ≤ f a)
  let late := P.filter (fun i => f a+kappa < f i)
  let low := P.filter (fun i => f i < f a)
  let middle := S.filter (fun i => |f i-f a| ≤ kappa)
  let initial := P.filter (fun i => f i ≤ f a+kappa)
  have hcover : initial ⊆ low ∪ middle := by
    intro i hi
    obtain ⟨hiP,hit⟩ := mem_filter.mp hi
    by_cases hlo : f i < f a
    · exact mem_union_left _ (mem_filter.mpr ⟨hiP,hlo⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hPS hiP,abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  have hcount : (initial.card:ℝ) ≤ (low.card:ℝ)+(middle.card:ℝ) := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
  have hwindow' := hwindow (f a)
  have hpartition : (initial.card:ℝ)+(late.card:ℝ) = (P.card:ℝ) := by
    have hh := card_filter_add_card_filter_not (s := P) (fun i => f i ≤ f a+kappa)
    simpa only [not_le,Nat.cast_add] using (congrArg (fun n : ℕ => (n:ℝ)) hh)
  refine ⟨early,late,(filter_subset _ _).trans hPS,(filter_subset _ _).trans hPS,hhigh,?_,?_⟩
  · change (low.card:ℝ) < (S.card:ℝ)/8 at hlow
    change (middle.card:ℝ) ≤ (S.card:ℝ)/16 at hwindow'
    linarith
  · intro i hi j hj
    refine ⟨hPpos i (mem_filter.mp hi).1,?_⟩
    have hei := (mem_filter.mp hi).2
    have hlj := (mem_filter.mp hj).2
    change f i ≤ f a at hei
    change f a+kappa < f j at hlj
    linarith

/-- At least one orientation has a substantial branch outside the vertex's
nonconcentrated interval; no symmetry of the finite shading is assumed. -/
theorem positive_or_negative_branch {I : Type*} (S : Finset I) (f : I → ℝ)
    {kappa : ℝ} (hS : 0 < (S.card:ℝ))
    (hnear : ((S.filter (fun i => |f i| ≤ kappa)).card:ℝ) ≤ (S.card:ℝ)/16) :
    (S.card:ℝ)/3 ≤ ((S.filter (fun i => kappa ≤ f i)).card:ℝ) ∨
      (S.card:ℝ)/3 ≤ ((S.filter (fun i => f i ≤ -kappa)).card:ℝ) := by
  let P := S.filter (fun i => kappa ≤ f i)
  let N := S.filter (fun i => f i ≤ -kappa)
  let Z := S.filter (fun i => |f i| ≤ kappa)
  have hcover : S ⊆ (P ∪ N) ∪ Z := by
    intro i hi
    by_cases hp : kappa ≤ f i
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hi,hp⟩))
    by_cases hn : f i ≤ -kappa
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hi,hn⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hi,abs_le.mpr ⟨by linarith,by linarith⟩⟩)
  have hcount : (S.card:ℝ) ≤ (P.card:ℝ)+(N.card:ℝ)+(Z.card:ℝ) := by
    have hh := (card_le_card hcover).trans (card_union_le _ _)
    have hu := card_union_le P N
    exact_mod_cast hh.trans (Nat.add_le_add_right hu _)
  change (Z.card:ℝ) ≤ (S.card:ℝ)/16 at hnear
  by_contra hn
  push Not at hn
  change (P.card:ℝ) < (S.card:ℝ)/3 ∧ (N.card:ℝ) < (S.card:ℝ)/3 at hn
  linarith [hn.1,hn.2]

/-- One orientation and two actual occupied-label subsets give the early/late
coordinates used in a legal pivot. Their sizes are fixed fractions of the input. -/
theorem oriented_early_late {I : Type*} (S : Finset I) (f : I → ℝ)
    {kappa : ℝ} (hS : 0 < (S.card:ℝ)) (hkappa : 0 < kappa)
    (hwindow : ∀ t : ℝ, ((S.filter (fun i => |f i-t| ≤ kappa)).card:ℝ) ≤ (S.card:ℝ)/16) :
    ∃ sign : ℝ, ∃ early late : Finset I, (sign=1 ∨ sign= -1) ∧
      early ⊆ S ∧ late ⊆ S ∧ (S.card:ℝ)/8 ≤ (early.card:ℝ) ∧ (S.card:ℝ)/8 ≤ (late.card:ℝ) ∧
      ∀ i ∈ early, ∀ j ∈ late, kappa ≤ sign*f i ∧ kappa ≤ sign*f j-sign*f i := by
  have hnear : ((S.filter (fun i => |f i| ≤ kappa)).card:ℝ) ≤ (S.card:ℝ)/16 := by
    simpa only [sub_zero] using hwindow 0
  rcases positive_or_negative_branch S f hS hnear with hp | hn
  · obtain ⟨early,late,he,hl,hce,hcl,hsep⟩ := early_late_on_positive_branch S
      (S.filter (fun i => kappa ≤ f i)) f hS hkappa (filter_subset _ _) hp
      (fun i hi => (mem_filter.mp hi).2) hwindow
    exact ⟨1,early,late,Or.inl rfl,he,hl,hce,hcl,by simpa only [one_mul] using hsep⟩
  · have hw : ∀ t : ℝ, ((S.filter (fun i => |-f i-t| ≤ kappa)).card:ℝ) ≤ (S.card:ℝ)/16 := by
      intro t
      have hid (i : I) : |-f i-t| = |f i-(-t)| := by
        rw [show -f i-t = -(f i-(-t)) by ring,abs_neg]
      simpa only [hid] using hwindow (-t)
    obtain ⟨early,late,he,hl,hce,hcl,hsep⟩ := early_late_on_positive_branch S
      (S.filter (fun i => f i ≤ -kappa)) (fun i => -f i) hS hkappa (filter_subset _ _) hn
      (fun i hi => by have hh := (mem_filter.mp hi).2; linarith) hw
    exact ⟨-1,early,late,Or.inr rfl,he,hl,hce,hcl,by simpa only [neg_one_mul] using hsep⟩

/-- A fixed proportion of the second shade lies outside the vertex interval. -/
theorem remote_count {I : Type*} (S : Finset I) (f : I → ℝ) {kappa : ℝ}
    (hnear : ((S.filter (fun i => |f i| ≤ kappa)).card:ℝ) ≤ (S.card:ℝ)/16) :
    (S.card:ℝ)/2 ≤ ((S.filter (fun i => kappa ≤ |f i|)).card:ℝ) := by
  have hcover : S ⊆ (S.filter (fun i => kappa ≤ |f i|)) ∪ (S.filter (fun i => |f i| ≤ kappa)) := by
    intro i hi
    by_cases hh : kappa ≤ |f i|
    · exact mem_union_left _ (mem_filter.mpr ⟨hi,hh⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hi,(lt_of_not_ge hh).le⟩)
  have hc : (S.card:ℝ) ≤ ((S.filter (fun i => kappa ≤ |f i|)).card:ℝ)+
      ((S.filter (fun i => |f i| ≤ kappa)).card:ℝ) := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le _ _)
  have hS : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  linarith

/-- An interval of projected coordinates is contained in an actual physical
ball about the shifted axis. Original two ends therefore supplies the needed
one-dimensional nonconcentration; no interval-count hypothesis is assumed. -/
theorem projected_interval_nonconcentration {k : ℕ} (S : Finset (Cell k))
    (vertex u : Space k) (coord : Cell k → ℝ) {δ kappa width B alpha : ℝ}
    (hδ : 0 < δ) (hδkappa : δ ≤ kappa) (hwidth : 0 ≤ width) (hu : ‖u‖ = 1)
    (hclose : ∀ z ∈ S, dist (cellCenter δ z) (vertex+coord z • u) ≤ width*δ)
    (hends : ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((S.filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤ B*r^alpha*(S.card:ℝ))
    (hradius : (width+1)*kappa ≤ 1)
    (hsmall : B*((width+1)*kappa)^alpha ≤ 1/16) :
    ∀ t : ℝ, ((S.filter (fun z => |coord z-t| ≤ kappa)).card:ℝ) ≤ (S.card:ℝ)/16 := by
  intro t
  have hkappa := hδ.trans_le hδkappa
  have hlo : δ ≤ (width+1)*kappa := by nlinarith
  have hsub : S.filter (fun z => |coord z-t| ≤ kappa) ⊆
      S.filter (fun z => dist (cellCenter δ z) (vertex+t • u) ≤ (width+1)*kappa) := by
    intro z hz
    obtain ⟨hzS,hzt⟩ := mem_filter.mp hz
    refine mem_filter.mpr ⟨hzS,?_⟩
    have haxis : dist (vertex+coord z • u) (vertex+t • u) = |coord z-t| := by
      have hid : (vertex+coord z • u)-(vertex+t • u) = (coord z-t) • u := by module
      rw [dist_eq_norm,hid,norm_smul,hu,mul_one,Real.norm_eq_abs]
    have hh := dist_triangle (cellCenter δ z) (vertex+coord z • u) (vertex+t • u)
    rw [haxis] at hh
    nlinarith [hclose z hzS]
  have hc : ((S.filter (fun z => |coord z-t| ≤ kappa)).card:ℝ) ≤
      ((S.filter (fun z => dist (cellCenter δ z) (vertex+t • u) ≤ (width+1)*kappa)).card:ℝ) := by
    exact_mod_cast card_le_card hsub
  have hh := hc.trans (hends (vertex+t • u) ((width+1)*kappa) hlo hradius)
  have hf := mul_le_mul_of_nonneg_right hsmall (show (0:ℝ) ≤ S.card by positivity)
  exact hh.trans (by simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm] using hf)

/-- Three independent, actual occupied-label choices supply the cubic sample
mass in (5.11). The first axis is oriented once for the whole set. -/
theorem legal_triples {I J : Type*} (S : Finset I) (T : Finset J)
    (f : I → ℝ) (g : J → ℝ) {kappa density : ℝ}
    (hkappa : 0 < kappa) (hdensity : 0 < density)
    (hS : density ≤ (S.card:ℝ)) (hT : density ≤ (T.card:ℝ))
    (hwindow : ∀ t : ℝ, ((S.filter (fun i => |f i-t| ≤ kappa)).card:ℝ) ≤ (S.card:ℝ)/16)
    (hremote : ((T.filter (fun j => |g j| ≤ kappa)).card:ℝ) ≤ (T.card:ℝ)/16) :
    ∃ sign : ℝ, ∃ samples : Finset (I × (I × J)),
      (sign=1 ∨ sign= -1) ∧ density^3/128 ≤ (samples.card:ℝ) ∧
      ∀ p ∈ samples, p.1 ∈ S ∧ p.2.1 ∈ S ∧ p.2.2 ∈ T ∧
        kappa ≤ sign*f p.1 ∧ kappa ≤ sign*f p.2.1-sign*f p.1 ∧
        kappa ≤ |g p.2.2| := by
  obtain ⟨sign,early,late,hsign,he,hl,hce,hcl,hsep⟩ :=
    oriented_early_late S f (hdensity.trans_le hS) hkappa hwindow
  let remote := T.filter (fun j => kappa ≤ |g j|)
  have hcr := remote_count T g hremote
  let samples := early.product (late.product remote)
  refine ⟨sign,samples,hsign,?_,?_⟩
  · have he' : density/8 ≤ (early.card:ℝ) := (div_le_div_of_nonneg_right hS (by norm_num)).trans hce
    have hl' : density/8 ≤ (late.card:ℝ) := (div_le_div_of_nonneg_right hS (by norm_num)).trans hcl
    have hr' : density/2 ≤ (remote.card:ℝ) := (div_le_div_of_nonneg_right hT (by norm_num)).trans hcr
    have hprod := mul_le_mul he' (mul_le_mul hl' hr' (by positivity) (by positivity))
      (by positivity) (by positivity)
    calc
      density^3/128 = (density/8)*((density/8)*(density/2)) := by ring
      _ ≤ (early.card:ℝ)*((late.card:ℝ)*(remote.card:ℝ)) := hprod
      _ = (samples.card:ℝ) := by simp only [samples,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
  · intro p hp
    obtain ⟨hi,hj,hk⟩ := by simpa only [samples,Finset.product_eq_sprod,Finset.mem_product] using hp
    have hijk := hsep p.1 hi p.2.1 hj
    exact ⟨he hi,hl hj,(mem_filter.mp hk).1,hijk.1,hijk.2,(mem_filter.mp hk).2⟩

end
end KakeyaFormal.LegalParameterSelection
