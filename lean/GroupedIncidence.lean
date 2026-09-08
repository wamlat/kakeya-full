import Finite

/-! Actual finite high-cell deletion and colored-support counting. The cutoff
sets and all multiplicities are constructed from the original incidence records. -/
namespace KakeyaFormal.GroupedIncidence
open Finset
open scoped BigOperators
noncomputable section
open Classical

variable {A B C : Type*}

def degree (S : Finset A) (f : A → B) (b : B) : ℕ := (S.filter (fun a => f a = b)).card

def high (S : Finset A) (f : A → B) (H : ℝ) : Finset A :=
  S.filter (fun a => H < (degree S f (f a):ℝ))

def retained (S : Finset A) (f : A → B) (H : ℝ) : Finset A :=
  S.filter (fun a => (degree S f (f a):ℝ) ≤ H)

lemma degree_mono {S T : Finset A} (hST : S ⊆ T) (f : A → B) (b : B) :
    degree S f b ≤ degree T f b :=
  card_le_card (filter_subset_filter _ hST)

lemma sum_degree (S : Finset A) (f : A → B) :
    ∑ b ∈ S.image f, degree S f b = S.card := by
  simpa only [degree,card_eq_sum_ones] using
    sum_fiberwise_of_maps_to (fun a ha => mem_image.mpr ⟨a,ha,rfl⟩) (fun _ => (1:ℕ))

lemma mass_partition (S : Finset A) (f : A → B) (H : ℝ) :
    (high S f H).card+(retained S f H).card = S.card := by
  simpa only [high,retained,not_lt] using
    card_filter_add_card_filter_not (s := S) (p := fun a => H < (degree S f (f a):ℝ))

lemma high_degree (S : Finset A) (f : A → B) (H : ℝ) {b : B}
    (hb : b ∈ (high S f H).image f) : degree (high S f H) f b = degree S f b := by
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
  have hh := (mem_filter.mp ha).2
  unfold degree
  congr 1
  ext z
  simp only [high,mem_filter]
  constructor
  · rintro ⟨⟨hz,_⟩,heq⟩
    exact ⟨hz,heq⟩
  · rintro ⟨hz,heq⟩
    exact ⟨⟨hz,by simpa only [heq] using hh⟩,heq⟩

lemma high_support_bound (S : Finset A) (f : A → B) (H : ℝ) :
    H * (((high S f H).image f).card:ℝ) ≤ ((high S f H).card:ℝ) := by
  have hsum : ∑ b ∈ (high S f H).image f, (degree (high S f H) f b:ℝ) =
      ((high S f H).card:ℝ) := by exact_mod_cast sum_degree (high S f H) f
  rw [← hsum]
  calc
    _ = ∑ _b ∈ (high S f H).image f, H := by simp [mul_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro b hb
      rw [high_degree S f H hb]
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
      exact (mem_filter.mp ha).2.le

/-- A refined support with one finite color coordinate has at most the number
of colors times its actual coarse support. No geometric overlap is assumed. -/
theorem colored_support_bound [Fintype C] (S : Finset A) (f : A → B) (color : A → C) :
    (S.image (fun a => (f a,color a))).card ≤ Fintype.card C * (S.image f).card := by
  let labels := S.image (fun a => (f a,color a))
  have hb : labels.card ≤ (S.image f).card * Fintype.card C := by
    apply KakeyaFinite.support_card_by_fibers labels (S.image f) Prod.fst
    · intro l hl
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hl
      exact mem_image.mpr ⟨a,ha,rfl⟩
    · intro b _
      have hinj : Set.InjOn Prod.snd ((labels.filter (fun l => l.1 = b)):Set (B×C)) := by
        intro x hx y hy heq
        exact Prod.ext ((mem_filter.mp hx).2.trans (mem_filter.mp hy).2.symm) heq
      have hh := card_image_of_injOn hinj
      have hc : ((labels.filter (fun l => l.1 = b)).image Prod.snd).card ≤ Fintype.card C :=
        card_le_univ _
      rwa [hh] at hc
  simpa only [Nat.mul_comm] using hb

/-- This is the actual high-cell colored-union upper bound in (5.28). -/
theorem high_colored_support_bound [Fintype C] (S : Finset A) (f : A → B)
    (color : A → C) {H : ℝ} (hH : 0 ≤ H) :
    H * (((high S f H).image (fun a => (f a,color a))).card:ℝ) ≤
      (Fintype.card C:ℝ) * (S.card:ℝ) := by
  have hc : (((high S f H).image (fun a => (f a,color a))).card:ℝ) ≤
      (Fintype.card C:ℝ)*(((high S f H).image f).card:ℝ) := by
    exact_mod_cast colored_support_bound (high S f H) f color
  have hh := high_support_bound S f H
  have hsub : ((high S f H).card:ℝ) ≤ (S.card:ℝ) := by
    exact_mod_cast card_le_card (filter_subset _ _ : high S f H ⊆ S)
  have hm := mul_le_mul_of_nonneg_left hc hH
  have hn := mul_le_mul_of_nonneg_left (hh.trans hsub) (Nat.cast_nonneg (Fintype.card C))
  nlinarith

lemma retained_degree_bound (S : Finset A) (f : A → B) {H : ℝ} (hH : 0 ≤ H) (b : B) :
    (degree (retained S f H) f b:ℝ) ≤ H := by
  by_cases hb : b ∈ (retained S f H).image f
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
    have hh := (mem_filter.mp ha).2
    have hm : (degree (retained S f H) f (f a):ℝ) ≤ (degree S f (f a):ℝ) := by
      exact_mod_cast degree_mono (filter_subset _ _ : retained S f H ⊆ S) f (f a)
    exact hm.trans hh
  · have hempty : (retained S f H).filter (fun a => f a = b) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hb (mem_image.mpr ⟨a,(mem_filter.mp ha).1,(mem_filter.mp ha).2⟩)
    simpa only [degree,hempty,card_empty,Nat.cast_zero] using hH

/-- Actual retained incidences have bounded group-cell energy and their exact
mass is the sum of the retained multiplicities. -/
theorem retained_energy_bound (S : Finset A) (f : A → B) {H : ℝ} (hH : 0 ≤ H) :
    (∑ b ∈ (retained S f H).image f, (degree (retained S f H) f b:ℝ)^2) ≤
      H*((retained S f H).card:ℝ) := by
  have hh := KakeyaFinite.bounded_multiplicity_energy ((retained S f H).image f)
    (fun b => (degree (retained S f H) f b:ℝ))
    (fun _ _ => Nat.cast_nonneg _) (fun b _ => retained_degree_bound S f hH b)
  have hsum : (∑ b ∈ (retained S f H).image f, (degree (retained S f H) f b:ℝ)) =
      ((retained S f H).card:ℝ) := by exact_mod_cast sum_degree (retained S f H) f
  rwa [hsum] at hh

/-- Once the analytic cutoff argument forces fewer than half the original
incidences into high cells, the constructed retained family keeps half. -/
theorem retained_mass_of_high_lt_half (S : Finset A) (f : A → B) (H : ℝ)
    (hhigh : ((high S f H).card:ℝ) < (S.card:ℝ)/2) :
    (S.card:ℝ)/2 < ((retained S f H).card:ℝ) := by
  have hp : ((high S f H).card:ℝ)+((retained S f H).card:ℝ) = (S.card:ℝ) := by
    exact_mod_cast mass_partition S f H
  linarith


/-- The finite cutoff is now calibrated and applied to the constructed sets.
The sole substantive input is a cumulative analytic lower bound for every actual
restricted colored support. Its grouped derivation belongs to the analytic input. -/
theorem calibrated_pruning [Fintype C] [Nonempty C]
    (S : Finset A) (f : A → B) (color : A → C)
    {N Q rho r a : ℝ} (hN : 0 < N) (hQ : 0 < Q) (hrho : 0 < rho)
    (hr : 1 ≤ r) (ha : 0 < a) (hmass : (S.card:ℝ) = rho*N*Q)
    (hanalytic : ∀ T ⊆ S,
      a*(Q*((T.card:ℝ)/(N*Q))^r) ≤ ((T.image (fun x => (f x,color x))).card:ℝ)) :
    let H := (2:ℝ)^(r+1)*(Fintype.card C:ℝ)*N/(a*rho^(r-1))
    ∃ T ⊆ S, (S.card:ℝ)/2 < (T.card:ℝ) ∧
      (∑ b ∈ T.image f, (degree T f b:ℝ)^2) ≤ H*(T.card:ℝ) := by
  intro H
  have hJ : (0:ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hH : 0 < H := by dsimp [H]; positivity
  have hhigh : ((high S f H).card:ℝ) < (S.card:ℝ)/2 := by
    by_contra hn
    have hlarge : (S.card:ℝ)/2 ≤ ((high S f H).card:ℝ) := le_of_not_gt hn
    have hdensity : rho/2 ≤ ((high S f H).card:ℝ)/(N*Q) := by
      apply (le_div_iff₀ (mul_pos hN hQ)).mpr
      rw [hmass] at hlarge
      nlinarith
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ rho/2) hdensity (by linarith : 0 ≤ r)
    have hlower := (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hp hQ.le) ha.le).trans
      (hanalytic (high S f H) (filter_subset _ _))
    have hupper := high_colored_support_bound S f color hH.le
    rw [hmass] at hupper
    have hmul := mul_le_mul_of_nonneg_left hlower hH.le
    have hid : H*(a*(Q*(rho/2)^r)) = 2*(Fintype.card C:ℝ)*(rho*N*Q) :=
      KakeyaFinite.cutoff_calibration_identity hrho ha.ne'
    rw [hid] at hmul
    have hpositive : 0 < (Fintype.card C:ℝ)*(rho*N*Q) := by positivity
    linarith
  exact ⟨retained S f H,filter_subset _ _,retained_mass_of_high_lt_half S f H hhigh,
    retained_energy_bound S f hH.le⟩

end
end KakeyaFormal.GroupedIncidence
