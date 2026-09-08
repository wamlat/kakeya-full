import OccupancySelection
import GroupedIncidence

/-! Actual angle-specific fibers, integer dyadic selection, whole-edge label
selection, collision counting, and one-angle exact-cardinality representatives. -/
namespace KakeyaFormal.AngleFiberSelection
open Finset
open scoped BigOperators
noncomputable section
open Classical

variable {Angle Sample Output Label : Type*}

def fiber (P : Angle → Finset Sample) (out : Angle → Sample → Output)
    (a : Angle) (f : Output) : Finset Sample := (P a).filter (fun x => out a x = f)

def outputs (P : Angle → Finset Sample) (out : Angle → Sample → Output)
    (a : Angle) : Finset Output := (P a).image (out a)

def edges (A : Finset Angle) (P : Angle → Finset Sample) (out : Angle → Sample → Output) :
    Finset (Angle × Output) := A.biUnion (fun a => (outputs P out a).image (fun f => (a,f)))

def size (P : Angle → Finset Sample) (out : Angle → Sample → Output) (e : Angle × Output) : ℕ :=
  (fiber P out e.1 e.2).card

def goodEdges (A : Finset Angle) (P : Angle → Finset Sample) (out : Angle → Sample → Output)
    (t : ℝ) : Finset (Angle × Output) := (edges A P out).filter (fun e => t ≤ (size P out e : ℝ))

lemma mem_edges {A : Finset Angle} {P : Angle → Finset Sample} {out : Angle → Sample → Output}
    {e : Angle × Output} : e ∈ edges A P out ↔ e.1 ∈ A ∧ e.2 ∈ outputs P out e.1 := by
  rcases e with ⟨a,f⟩
  simp [edges]

lemma fiber_pos {P : Angle → Finset Sample} {out : Angle → Sample → Output}
    {a : Angle} {f : Output} (hf : f ∈ outputs P out a) : 0 < (fiber P out a f).card := by
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hf
  exact card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,rfl⟩⟩

lemma sum_fibers (P : Angle → Finset Sample) (out : Angle → Sample → Output) (a : Angle) :
    ∑ f ∈ outputs P out a, (fiber P out a f).card = (P a).card := by
  exact GroupedIncidence.sum_degree (P a) (out a)

lemma sum_edges (A : Finset Angle) (P : Angle → Finset Sample) (out : Angle → Sample → Output)
    (w : Angle × Output → ℝ) :
    ∑ e ∈ edges A P out, w e = ∑ a ∈ A, ∑ f ∈ outputs P out a, w (a,f) := by
  unfold edges
  rw [sum_biUnion]
  · apply sum_congr rfl
    intro a ha
    rw [sum_image]
    intro f _ g _ hfg
    exact (Prod.mk.inj hfg).2
  · intro a ha b hb hab
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨f,_,he⟩ := mem_image.mp he
    obtain ⟨g,_,hf⟩ := mem_image.mp hf
    exact hab (congrArg Prod.fst (he.trans hf.symm))

lemma mass_edges (A : Finset Angle) (P : Angle → Finset Sample) (out : Angle → Sample → Output) :
    ∑ e ∈ edges A P out, (size P out e : ℝ) = ∑ a ∈ A, ((P a).card : ℝ) := by
  rw [sum_edges]
  apply sum_congr rfl
  intro a ha
  exact_mod_cast sum_fibers P out a

/-- Low fibers are actually deleted, at a loss at most threshold times the
actual number of outputs. The surviving total sample mass is at least half. -/
theorem low_fiber_deletion (A : Finset Angle) (P : Angle → Finset Sample)
    (out : Angle → Sample → Output) {mu U t : ℝ}
    (ht : 0 ≤ t) (hsamples : ∀ a ∈ A, mu ≤ ((P a).card : ℝ))
    (houtputs : ∀ a ∈ A, ((outputs P out a).card : ℝ) ≤ U) (hcut : t*U ≤ mu/2) :
    mu*(A.card : ℝ)/2 ≤ ∑ e ∈ goodEdges A P out t, (size P out e : ℝ) := by
  have hbad : (∑ e ∈ edges A P out with ¬t ≤ (size P out e : ℝ), (size P out e : ℝ)) ≤
      t*U*(A.card : ℝ) := by
    rw [sum_filter,sum_edges]
    calc
      _ ≤ ∑ a ∈ A, ∑ _f ∈ outputs P out a, t := by
        apply sum_le_sum
        intro a ha
        apply sum_le_sum
        intro f hf
        split_ifs with h
        · exact ht
        · exact (lt_of_not_ge h).le
      _ ≤ ∑ _a ∈ A, t*U := by
        apply sum_le_sum
        intro a ha
        simpa only [sum_const,nsmul_eq_mul,mul_comm] using mul_le_mul_of_nonneg_left (houtputs a ha) ht
      _ = _ := by simp [mul_comm]
  have htotal : mu*(A.card : ℝ) ≤ ∑ e ∈ edges A P out, (size P out e : ℝ) := by
    rw [mass_edges]
    simpa only [sum_const,nsmul_eq_mul,mul_comm] using sum_le_sum hsamples
  have hsplit := sum_filter_add_sum_filter_not (edges A P out)
    (fun e => t ≤ (size P out e : ℝ)) (fun e => (size P out e : ℝ))
  change mu*(A.card : ℝ)/2 ≤ ∑ e ∈ (edges A P out).filter _, (size P out e : ℝ)
  nlinarith [mul_le_mul_of_nonneg_right hcut (Nat.cast_nonneg A.card)]

/-- One global integer dyadic bin of actual whole angle-output edges. The
number of bins depends only on the maximum integer fiber size. -/
theorem dyadic_edge_selection (A : Finset Angle) (P : Angle → Finset Sample)
    (out : Angle → Sample → Output) (hA : A.Nonempty) {mu U t : ℝ} {B : ℕ}
    (hmu : 0 < mu) (ht : 0 ≤ t) (hsamples : ∀ a ∈ A, mu ≤ ((P a).card : ℝ))
    (houtputs : ∀ a ∈ A, ((outputs P out a).card : ℝ) ≤ U) (hcut : t*U ≤ mu/2)
    (hfiber : ∀ e ∈ edges A P out, size P out e ≤ B) :
    ∃ j ≤ Nat.log 2 B, ∃ Ω : Finset (Angle × Output),
      Ω = (goodEdges A P out t).filter (fun e => 2^j ≤ size P out e ∧ size P out e < 2*(2^j)) ∧
      Ω.Nonempty ∧
      t/2 < (2^j : ℕ) ∧ (2^j : ℕ) ≤ B ∧
      mu*(A.card : ℝ)/(2*(Nat.log 2 B+1 : ℕ)) ≤ ∑ e ∈ Ω, (size P out e : ℝ) ∧
      mu*(A.card : ℝ)/(4*(2^j : ℕ)*(Nat.log 2 B+1 : ℕ)) ≤ (Ω.card : ℝ) := by
  let E := goodEdges A P out t
  let J := Nat.log 2 B+1
  have hJ : 0 < J := Nat.succ_pos _
  have hmass := low_fiber_deletion A P out ht hsamples houtputs hcut
  have hpos (e) (he : e ∈ E) : 0 < size P out e :=
    fiber_pos (mem_edges.mp (mem_filter.mp he).1).2
  have hbin (e) (he : e ∈ E) := KakeyaFinite.dyadic_bin_membership (hpos e he) (hfiber e (mem_filter.mp he).1)
  let bin : Angle × Output → Fin J := fun e => if he : e ∈ E then
    ⟨Nat.log 2 (size P out e), mem_range.mp (hbin e he).2.2⟩ else ⟨0,hJ⟩
  obtain ⟨j,hj⟩ := OccupancySelection.weighted_class_selection E (fun e => (size P out e : ℝ)) hJ bin
  let Ω := E.filter (fun e => 2^j.val ≤ size P out e ∧ size P out e < 2*(2^j.val))
  have hsub : (E.filter (fun e => bin e = j)) ⊆ Ω := by
    intro e he
    obtain ⟨he,hlabel⟩ := mem_filter.mp he
    have heq : Nat.log 2 (size P out e) = j.val := by
      simpa only [bin,dif_pos he] using congrArg Fin.val hlabel
    have hb := hbin e he
    exact mem_filter.mpr ⟨he,by simpa only [heq,pow_succ,Nat.mul_comm] using hb.1,by
      simpa only [heq,pow_succ,Nat.mul_comm] using hb.2.1⟩
  have hsel : mu*(A.card : ℝ)/(2*(J : ℝ)) ≤ ∑ e ∈ Ω, (size P out e : ℝ) := by
    have hh := (div_le_div_of_nonneg_right hmass (show (0:ℝ) ≤ J by positivity)).trans hj
    have hm := sum_le_sum_of_subset_of_nonneg (f := fun e => (size P out e : ℝ)) hsub (fun _ _ _ => Nat.cast_nonneg _)
    convert hh.trans hm using 1 <;> first | rfl | ring
  have hleft : 0 < mu*(A.card : ℝ)/(2*(J : ℝ)) := by
    have hc : 0 < (A.card : ℝ) := by exact_mod_cast card_pos.mpr hA
    positivity
  have hΩ : Ω.Nonempty := by
    by_contra hh
    have he : Ω = ∅ := not_nonempty_iff_eq_empty.mp hh
    rw [he,sum_empty] at hsel
    linarith
  have hΩcopy := hΩ
  obtain ⟨e,he⟩ := hΩcopy
  obtain ⟨heE,helo,hehi⟩ := mem_filter.mp he
  have htlo : t/2 < (2^j.val : ℕ) := by
    have hh : (size P out e : ℝ) < 2*(2^j.val : ℕ) := by exact_mod_cast hehi
    linarith [(mem_filter.mp heE).2]
  have hupper : 2^j.val ≤ B := helo.trans (hfiber e (mem_filter.mp heE).1)
  have hsum : (∑ e ∈ Ω, (size P out e : ℝ)) ≤ 2*(2^j.val : ℕ)*(Ω.card : ℝ) := by
    calc
      _ ≤ ∑ _e ∈ Ω, (2*(2^j.val : ℕ) : ℝ) := sum_le_sum fun e he => by
        exact_mod_cast (mem_filter.mp he).2.2.le
      _ = _ := by simp [mul_comm]
  refine ⟨j.val,by have := j.isLt; dsimp [J] at this; omega,Ω,rfl,hΩ,htlo,hupper,?_,?_⟩
  · simpa only [J,Nat.cast_mul,Nat.cast_ofNat] using hsel
  · change mu*(A.card : ℝ)/(4*(2^j.val : ℕ)*(J : ℝ)) ≤ (Ω.card : ℝ)
    apply (div_le_iff₀ (show (0:ℝ) < 4*(2^j.val : ℕ)*(J : ℝ) by positivity)).mpr
    have h := (div_le_iff₀ (show (0:ℝ) < 2*(J : ℝ) by positivity)).mp (hsel.trans hsum)
    nlinarith


/-- A true most-frequent label class, including the empty input case. Every
member of the chosen label class is retained. -/
theorem frequent_class {EType : Type*} (E : Finset EType) (label : EType → Label)
    {K : ℕ} (hK : (E.image label).card ≤ K) :
    ∃ R : Finset EType, R ⊆ E ∧ E.card ≤ K*R.card ∧
      (E.Nonempty → R.Nonempty) ∧
      (∀ e ∈ R, ∀ e' ∈ R, label e = label e') ∧
      (∀ e ∈ R, ∀ e' ∈ E, label e' = label e → e' ∈ R) ∧
      (∀ e ∈ R, ∀ l, (E.filter (fun e' => label e' = l)).card ≤ R.card) := by
  by_cases hE : E.Nonempty
  · obtain ⟨l,hl,hmax⟩ := exists_max_image (E.image label)
      (fun l => (E.filter (fun e => label e = l)).card) (hE.image label)
    let R := E.filter (fun e => label e = l)
    have hcard : E.card ≤ K*R.card := by
      calc
        E.card = ∑ l ∈ E.image label, (E.filter (fun e => label e = l)).card :=
          (GroupedIncidence.sum_degree E label).symm
        _ ≤ ∑ _l ∈ E.image label, R.card := sum_le_sum hmax
        _ = (E.image label).card*R.card := by simp
        _ ≤ K*R.card := Nat.mul_le_mul_right _ hK
    have hR : R.Nonempty := by
      obtain ⟨e,he,rfl⟩ := mem_image.mp hl
      exact ⟨e,mem_filter.mpr ⟨he,rfl⟩⟩
    refine ⟨R,filter_subset _ _,hcard,fun _ => hR,?_,?_,?_⟩
    · intro e he e' he'
      exact (mem_filter.mp he).2.trans (mem_filter.mp he').2.symm
    · intro e he e' he' heq
      exact mem_filter.mpr ⟨he',heq.trans (mem_filter.mp he).2⟩
    · intro e he l'
      by_cases hl' : l' ∈ E.image label
      · exact hmax l' hl'
      · have hz : E.filter (fun e' => label e' = l') = ∅ := by
          apply eq_empty_iff_forall_notMem.mpr
          intro e' he'
          exact hl' (mem_image.mpr ⟨e',(mem_filter.mp he').1,(mem_filter.mp he').2⟩)
        simp [hz]
  · have hz : E = ∅ := not_nonempty_iff_eq_empty.mp hE
    subst E
    exact ⟨∅,by simp,by simp,by simp,by simp,by simp,by simp⟩

def outputEdges (Ω : Finset (Angle × Output)) (f : Output) : Finset (Angle × Output) :=
  Ω.filter (fun e => e.2 = f)

def outputSupport (Ω : Finset (Angle × Output)) : Finset Output := Ω.image Prod.snd

/-- For each actual output, independently keep one most-frequent second-tube
label. Whole edges are retained; all originally represented outputs remain. -/
theorem frequent_output_labels (Ω : Finset (Angle × Output)) (label : Angle → Label)
    {K : ℕ} (hK : ∀ f, ((outputEdges Ω f).image (fun e => label e.1)).card ≤ K) :
    ∃ Ωstar : Finset (Angle × Output), Ωstar ⊆ Ω ∧
      outputSupport Ωstar = outputSupport Ω ∧ Ω.card ≤ K*Ωstar.card ∧
      (∀ e ∈ Ωstar, ∀ e' ∈ Ωstar, e.2 = e'.2 → label e.1 = label e'.1) ∧
      (∀ e ∈ Ωstar, ∀ e' ∈ Ω, e'.2 = e.2 → label e'.1 = label e.1 → e' ∈ Ωstar) ∧
      (∀ f, ∀ l, ((outputEdges Ω f).filter (fun e => label e.1 = l)).card ≤
        (outputEdges Ωstar f).card) := by
  have hlocal (f : Output) := frequent_class (outputEdges Ω f) (fun e => label e.1) (hK f)
  choose R hRsub hRcard hRnonempty hRconstant hRwhole hRmax using hlocal
  let Ωstar := (outputSupport Ω).biUnion R
  have hRf (f : Output) {e} (he : e ∈ R f) : e.2 = f := (mem_filter.mp (hRsub f he)).2
  have hsub : Ωstar ⊆ Ω := by
    intro e he
    obtain ⟨f,hf,he⟩ := mem_biUnion.mp he
    exact (mem_filter.mp (hRsub f he)).1
  have hdisj : (outputSupport Ω : Set Output).Pairwise (fun f g => Disjoint (R f) (R g)) := by
    intro f hf g hg hfg
    apply disjoint_left.mpr
    intro e he he'
    exact hfg ((hRf f he).symm.trans (hRf g he'))
  have hΩcard : Ωstar.card = ∑ f ∈ outputSupport Ω, (R f).card := card_biUnion hdisj
  have hsupport : outputSupport Ωstar = outputSupport Ω := by
    apply Subset.antisymm (image_subset_image hsub)
    intro f hf
    obtain ⟨e,he,heq⟩ := mem_image.mp hf
    have hE : (outputEdges Ω f).Nonempty := ⟨e,mem_filter.mpr ⟨he,heq⟩⟩
    obtain ⟨e',he'⟩ := hRnonempty f hE
    exact mem_image.mpr ⟨e',mem_biUnion.mpr ⟨f,mem_image.mpr ⟨e,he,heq⟩,he'⟩,hRf f he'⟩
  have hfiber (f : Output) : outputEdges Ωstar f = R f := by
    ext e
    constructor
    · intro he
      obtain ⟨he,heq⟩ := mem_filter.mp he
      obtain ⟨g,hg,he⟩ := mem_biUnion.mp he
      have hg' : g = f := (hRf g he).symm.trans heq
      rwa [hg'] at he
    · intro he
      have hf : f ∈ outputSupport Ω := mem_image.mpr ⟨e,(mem_filter.mp (hRsub f he)).1,hRf f he⟩
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨f,hf,he⟩,hRf f he⟩
  refine ⟨Ωstar,hsub,hsupport,?_,?_,?_,?_⟩
  · calc
      Ω.card = ∑ f ∈ outputSupport Ω, (outputEdges Ω f).card :=
        (GroupedIncidence.sum_degree Ω Prod.snd).symm
      _ ≤ ∑ f ∈ outputSupport Ω, K*(R f).card := sum_le_sum fun f _ => hRcard f
      _ = K*Ωstar.card := by rw [hΩcard,mul_sum]
  · intro e he e' he' heq
    have h1 : e ∈ R e.2 := by rw [← hfiber]; exact mem_filter.mpr ⟨he,rfl⟩
    have h2 : e' ∈ R e.2 := by rw [← hfiber]; exact mem_filter.mpr ⟨he',heq.symm⟩
    exact hRconstant e.2 e h1 e' h2
  · intro e he e' he' heq hlabel
    have h1 : e ∈ R e.2 := by rw [← hfiber]; exact mem_filter.mpr ⟨he,rfl⟩
    have h2 := hRwhole e.2 e h1 e' (mem_filter.mpr ⟨he',heq⟩) hlabel
    rw [← hfiber] at h2
    exact (mem_filter.mp h2).1
  · intro f l
    rw [hfiber]
    by_cases hE : (outputEdges Ω f).Nonempty
    · obtain ⟨e,he⟩ := hRnonempty f hE
      exact hRmax f e he l
    · have hh : outputEdges Ω f = ∅ := not_nonempty_iff_eq_empty.mp hE
      simp [hh]


/-- Collision energy of actual retained angle-output edges. -/
def collisionEnergy (Ω : Finset (Angle × Output)) : ℝ :=
  ∑ f ∈ outputSupport Ω, ((outputEdges Ω f).card : ℝ)^2

/-- Ordered pairs of actual edges colliding at the same output. -/
def collisionPairs (Ω : Finset (Angle × Output)) : Finset ((Angle × Output) × (Angle × Output)) :=
  (Ω.product Ω).filter (fun e => e.1.2 = e.2.2)

/-- The defined collision energy is exactly the number of actual ordered
collisions, including diagonal pairs. -/
theorem collision_energy_count (Ω : Finset (Angle × Output)) :
    collisionEnergy Ω = ((collisionPairs Ω).card : ℝ) := by
  have hfirst : (collisionPairs Ω).card = ∑ e ∈ Ω, (outputEdges Ω e.2).card := by
    simp only [collisionPairs,outputEdges,card_eq_sum_ones,sum_filter]
    rw [Finset.sum_finset_product (Ω.product Ω) Ω (fun _ => Ω) (fun _ => mem_product)
      (f := fun e => if e.1.2 = e.2.2 then (1:ℕ) else 0)]
    apply sum_congr rfl
    intro e he
    apply sum_congr rfl
    intro e' he'
    simp only [eq_comm]
  have hgroup : (∑ e ∈ Ω, (outputEdges Ω e.2).card) =
      ∑ f ∈ outputSupport Ω, (outputEdges Ω f).card^2 := by
    rw [← sum_fiberwise_of_maps_to (s := Ω) (t := outputSupport Ω) (g := Prod.snd)
      (fun e he => mem_image.mpr ⟨e,he,rfl⟩) (fun e => (outputEdges Ω e.2).card)]
    apply sum_congr rfl
    intro f hf
    calc
      _ = ∑ _e ∈ outputEdges Ω f, (outputEdges Ω f).card := by
        apply sum_congr rfl
        intro e he
        rw [(mem_filter.mp he).2]
      _ = _ := by simp [pow_two]
  unfold collisionEnergy
  exact_mod_cast (hfirst.trans hgroup).symm

/-- Cauchy--Schwarz on actual output multiplicities, with the exact edge count. -/
theorem collision_cauchy (Ω : Finset (Angle × Output)) :
    (Ω.card : ℝ)^2 ≤ (outputSupport Ω).card*collisionEnergy Ω := by
  have hsum : (∑ f ∈ outputSupport Ω, ((outputEdges Ω f).card : ℝ)) = Ω.card := by
    exact_mod_cast GroupedIncidence.sum_degree Ω Prod.snd
  have hh := sum_mul_sq_le_sq_mul_sq (outputSupport Ω) (fun _ => (1:ℝ))
    (fun f => ((outputEdges Ω f).card : ℝ))
  simpa only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,hsum,collisionEnergy] using hh

/-- A supplied geometric collision upper bound is applied only to the actual
energy just defined. No output-support lower bound is assumed. -/
theorem collision_support_bound (Ω : Finset (Angle × Output)) {lower E : ℝ}
    (hlower : 0 ≤ lower) (hmass : lower ≤ (Ω.card : ℝ))
    (hE : 0 < E) (henergy : collisionEnergy Ω ≤ E) :
    lower^2/E ≤ ((outputSupport Ω).card : ℝ) := by
  have hcs := (collision_cauchy Ω).trans
    (mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg _))
  apply (div_le_iff₀ hE).mpr
  have hs : lower^2 ≤ (Ω.card : ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) Ω.card]
  exact hs.trans hcs

/-- Distinct outputs are injectively indexed, each chooses one incident angle,
and exactly h samples are selected from that angle's original fiber. No union
over incident angles appears in the chosen sample set. -/
theorem exact_fiber_representatives (A : Finset Angle) (P : Angle → Finset Sample)
    (out : Angle → Sample → Output) (Ω : Finset (Angle × Output)) {h : ℕ}
    (hsub : Ω ⊆ edges A P out) (hsize : ∀ e ∈ Ω, h ≤ size P out e) :
    ∃ f : Fin (outputSupport Ω).card → Output,
    ∃ a : Fin (outputSupport Ω).card → Angle,
    ∃ R : Fin (outputSupport Ω).card → Finset Sample,
      Function.Injective f ∧ univ.image f = outputSupport Ω ∧
      (∀ i, a i ∈ A ∧ (a i,f i) ∈ Ω ∧ R i ⊆ fiber P out (a i) (f i) ∧ (R i).card = h) ∧
      (∑ i, (R i).card) = h*(outputSupport Ω).card := by
  let f : Fin (outputSupport Ω).card → Output := fun i => ((outputSupport Ω).equivFin.symm i).val
  have hfinj : Function.Injective f := Subtype.val_injective.comp (outputSupport Ω).equivFin.symm.injective
  have hfmem (i) : f i ∈ outputSupport Ω := ((outputSupport Ω).equivFin.symm i).property
  have himage : univ.image f = outputSupport Ω := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨i,_,rfl⟩ := mem_image.mp hz
      exact hfmem i
    · intro z hz
      refine mem_image.mpr ⟨(outputSupport Ω).equivFin ⟨z,hz⟩,mem_univ _,?_⟩
      simp [f]
  have hex (i) : ∃ a : Angle, (a,f i) ∈ Ω := by
    obtain ⟨e,he,heq⟩ := mem_image.mp (hfmem i)
    exact ⟨e.1,by simpa only [← heq] using he⟩
  choose a ha using hex
  have hR (i) : ∃ R ⊆ fiber P out (a i) (f i), R.card = h :=
    exists_subset_card_eq (hsize _ (ha i))
  choose R hRsub hRcard using hR
  refine ⟨f,a,R,hfinj,himage,?_,?_⟩
  · intro i
    exact ⟨(mem_edges.mp (hsub (ha i))).1,ha i,hRsub i,hRcard i⟩
  · simp [hRcard,Nat.mul_comm]

/-- The complete finite selection from legal samples to one exact h-sample
fiber per distinct output. The lower sample/output/fiber and local label-count
hypotheses are explicit geometric inputs; every subsequent set is constructed. -/
theorem select_angle_fibers (A : Finset Angle) (P : Angle → Finset Sample)
    (out : Angle → Sample → Output) (label : Angle → Label) (hA : A.Nonempty)
    {mu U t : ℝ} {B K : ℕ}
    (hmu : 0 < mu) (ht : 0 ≤ t) (hK : 0 < K)
    (hsamples : ∀ a ∈ A, mu ≤ ((P a).card : ℝ))
    (houtputs : ∀ a ∈ A, ((outputs P out a).card : ℝ) ≤ U)
    (hcut : t*U ≤ mu/2) (hfiber : ∀ e ∈ edges A P out, size P out e ≤ B)
    (hlabels : ∀ f, ((outputEdges (edges A P out) f).image (fun e => label e.1)).card ≤ K) :
    ∃ j ≤ Nat.log 2 B, ∃ Ω Ωstar : Finset (Angle × Output),
      Ω = (goodEdges A P out t).filter (fun e => 2^j ≤ size P out e ∧ size P out e < 2*(2^j)) ∧
      Ω.Nonempty ∧ Ωstar.Nonempty ∧ Ωstar ⊆ Ω ∧ outputSupport Ωstar = outputSupport Ω ∧
      1 ≤ (2^j : ℕ) ∧ t/2 < (2^j : ℕ) ∧ (2^j : ℕ) ≤ B ∧
      mu*(A.card : ℝ)/(2*(Nat.log 2 B+1 : ℕ)) ≤ ∑ e ∈ Ω, (size P out e : ℝ) ∧
      mu*(A.card : ℝ)/(4*(2^j : ℕ)*(Nat.log 2 B+1 : ℕ)) ≤ (Ω.card : ℝ) ∧
      Ω.card ≤ K*Ωstar.card ∧
      mu*(A.card : ℝ)/(4*(2^j : ℕ)*(Nat.log 2 B+1 : ℕ)*K) ≤ (Ωstar.card : ℝ) ∧
      (∀ e ∈ Ωstar, ∀ e' ∈ Ωstar, e.2 = e'.2 → label e.1 = label e'.1) ∧
      (∀ e ∈ Ωstar, ∀ e' ∈ Ω, e'.2 = e.2 → label e'.1 = label e.1 → e' ∈ Ωstar) ∧
      (∀ f, ∀ l, ((outputEdges Ω f).filter (fun e => label e.1 = l)).card ≤
        (outputEdges Ωstar f).card) ∧
      (∀ E : ℝ, 0 < E → collisionEnergy Ωstar ≤ E →
        (mu*(A.card : ℝ)/(4*(2^j : ℕ)*(Nat.log 2 B+1 : ℕ)*K))^2/E ≤
          ((outputSupport Ωstar).card : ℝ)) ∧
      ∃ f : Fin (outputSupport Ωstar).card → Output,
      ∃ a : Fin (outputSupport Ωstar).card → Angle,
      ∃ R : Fin (outputSupport Ωstar).card → Finset Sample,
        Function.Injective f ∧ univ.image f = outputSupport Ωstar ∧
        (∀ i, a i ∈ A ∧ (a i,f i) ∈ Ωstar ∧ R i ⊆ fiber P out (a i) (f i) ∧ (R i).card = 2^j) ∧
        (∑ i, (R i).card) = (2^j)*(outputSupport Ωstar).card := by
  obtain ⟨j,hj,Ω,hΩ,hΩne,hlo,hhi,hmass,hedges⟩ :=
    dyadic_edge_selection A P out hA hmu ht hsamples houtputs hcut hfiber
  have hΩsub : Ω ⊆ edges A P out := by
    rw [hΩ]
    exact (filter_subset _ _).trans (filter_subset _ _)
  have hlabelsΩ (f) : ((outputEdges Ω f).image (fun e => label e.1)).card ≤ K :=
    (card_le_card (image_subset_image (filter_subset_filter _ hΩsub))).trans (hlabels f)
  obtain ⟨Ωstar,hstarsub,hsupport,hstarcard,hconstant,hwhole,hmax⟩ := frequent_output_labels Ω label hlabelsΩ
  have hstarne : Ωstar.Nonempty := by
    have hh : (outputSupport Ω).Nonempty := hΩne.image Prod.snd
    rw [← hsupport] at hh
    exact image_nonempty.mp hh
  have hstarreal : (Ω.card : ℝ) ≤ (K : ℝ)*(Ωstar.card : ℝ) := by exact_mod_cast hstarcard
  have hretained : mu*(A.card : ℝ)/(4*(2^j : ℕ)*(Nat.log 2 B+1 : ℕ)*K) ≤ (Ωstar.card : ℝ) := by
    have hh : (mu*(A.card : ℝ)/(4*(2^j : ℕ)*(Nat.log 2 B+1 : ℕ)))/(K : ℝ) ≤ (Ωstar.card : ℝ) :=
      (div_le_iff₀ (show (0:ℝ) < K by positivity)).mpr (by simpa only [mul_comm] using hedges.trans hstarreal)
    convert hh using 1
    ring
  refine ⟨j,hj,Ω,Ωstar,hΩ,hΩne,hstarne,hstarsub,hsupport,one_le_pow₀ (by norm_num),hlo,hhi,hmass,hedges,
    hstarcard,hretained,hconstant,hwhole,hmax,?_,?_⟩
  · intro E hE henergy
    exact collision_support_bound Ωstar (by positivity) hretained hE henergy
  · apply exact_fiber_representatives A P out Ωstar (hstarsub.trans hΩsub)
    intro e he
    have hh := hstarsub he
    rw [hΩ] at hh
    exact (mem_filter.mp hh).2.1

end
end KakeyaFormal.AngleFiberSelection

#print axioms KakeyaFormal.AngleFiberSelection.low_fiber_deletion
#print axioms KakeyaFormal.AngleFiberSelection.dyadic_edge_selection
#print axioms KakeyaFormal.AngleFiberSelection.frequent_output_labels
#print axioms KakeyaFormal.AngleFiberSelection.collision_energy_count
#print axioms KakeyaFormal.AngleFiberSelection.collision_support_bound
#print axioms KakeyaFormal.AngleFiberSelection.exact_fiber_representatives
#print axioms KakeyaFormal.AngleFiberSelection.select_angle_fibers
