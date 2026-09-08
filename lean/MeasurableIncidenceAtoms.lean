import Mathlib

/-! Exact finite measurable incidence-pattern atoms. Atom volumes give the
weights needed to run finite incidence constructions on arbitrary measurable
shadings, without replacing those shadings by whole grid cells. -/
namespace KakeyaFormal.MeasurableIncidenceAtoms
open MeasureTheory Set
open scoped ENNReal
noncomputable section
open Classical

def pattern {X : Type*} {M : ℕ} (Y : Fin M → Set X) (x : X) : Finset (Fin M) :=
  Finset.univ.filter (fun i => x ∈ Y i)

def atom {X : Type*} {M : ℕ} (Y : Fin M → Set X) (s : Finset (Fin M)) : Set X :=
  {x | ∀ i, x ∈ Y i ↔ i ∈ s}

def patterns (M : ℕ) : Finset (Finset (Fin M)) :=
  Finset.univ.filter Finset.Nonempty

@[simp] theorem mem_pattern {X : Type*} {M : ℕ} (Y : Fin M → Set X) (x : X) (i : Fin M) :
    i ∈ pattern Y x ↔ x ∈ Y i := by simp [pattern]

theorem mem_atom {X : Type*} {M : ℕ} (Y : Fin M → Set X) (s : Finset (Fin M)) (x : X) :
    x ∈ atom Y s ↔ pattern Y x = s := by
  simp only [atom,mem_ofPred_eq,Finset.ext_iff,mem_pattern]

@[simp] theorem mem_patterns {M : ℕ} (s : Finset (Fin M)) : s ∈ patterns M ↔ s.Nonempty := by
  simp [patterns]

theorem atom_measurable {X : Type*} [MeasurableSpace X] {M : ℕ}
    (Y : Fin M → Set X) (hY : ∀ i, MeasurableSet (Y i)) (s : Finset (Fin M)) :
    MeasurableSet (atom Y s) := by
  have heq : atom Y s = ⋂ i : Fin M, (if i ∈ s then Y i else (Y i)ᶜ) := by
    ext x
    simp only [atom,mem_ofPred_eq,mem_iInter]
    apply forall_congr'
    intro i
    by_cases hi : i ∈ s <;> simp [hi]
  rw [heq]
  exact MeasurableSet.iInter (fun i => by
    split_ifs
    · exact hY i
    · exact (hY i).compl)

theorem atom_disjoint {X : Type*} {M : ℕ} (Y : Fin M → Set X) :
    Pairwise (fun s t : Finset (Fin M) => Disjoint (atom Y s) (atom Y t)) := by
  intro s t hst
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact hst (((mem_atom Y s x).mp hx).symm.trans ((mem_atom Y t x).mp hy))

theorem atom_subset_shading {X : Type*} {M : ℕ} (Y : Fin M → Set X)
    {s : Finset (Fin M)} {i : Fin M} (hi : i ∈ s) : atom Y s ⊆ Y i :=
  fun _ hx => (hx i).mpr hi

theorem atom_subset_union {X : Type*} {M : ℕ} (Y : Fin M → Set X)
    {s : Finset (Fin M)} (hs : s ∈ patterns M) : atom Y s ⊆ ⋃ i, Y i := by
  obtain ⟨i,hi⟩ := (mem_patterns _).mp hs
  exact fun _ hx => mem_iUnion.mpr ⟨i,atom_subset_shading Y hi hx⟩

theorem atom_finite {X : Type*} [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (Y : Fin M → Set X) (hfin : ∀ i, μ (Y i) ≠ ∞)
    {s : Finset (Fin M)} (hs : s ∈ patterns M) : μ (atom Y s) ≠ ∞ := by
  obtain ⟨i,hi⟩ := (mem_patterns _).mp hs
  exact measure_ne_top_of_subset (atom_subset_shading Y hi) (hfin i)

theorem union_atoms {X : Type*} {M : ℕ} (Y : Fin M → Set X) :
    (⋃ s ∈ patterns M, atom Y s) = ⋃ i, Y i := by
  apply Subset.antisymm
  · exact iUnion₂_subset (fun s hs => atom_subset_union Y hs)
  · intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    refine mem_iUnion₂.mpr ⟨pattern Y x,(mem_patterns _).mpr ⟨i,(mem_pattern Y x i).mpr hi⟩,?_⟩
    exact (mem_atom Y _ _).mpr rfl

theorem shading_atoms {X : Type*} {M : ℕ} (Y : Fin M → Set X) (i : Fin M) :
    (⋃ s ∈ (patterns M).filter (fun s => i ∈ s), atom Y s) = Y i := by
  apply Subset.antisymm
  · exact iUnion₂_subset (fun s hs => atom_subset_shading Y (Finset.mem_filter.mp hs).2)
  · intro x hx
    have hi := (mem_pattern Y x i).mpr hx
    refine mem_iUnion₂.mpr ⟨pattern Y x,Finset.mem_filter.mpr ⟨(mem_patterns _).mpr ⟨i,hi⟩,hi⟩,?_⟩
    exact (mem_atom Y _ _).mpr rfl

theorem union_mass {X : Type*} [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (Y : Fin M → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) :
    (∑ s ∈ patterns M, μ.real (atom Y s)) = μ.real (⋃ i, Y i) := by
  rw [← union_atoms Y]
  exact (measureReal_biUnion_finset (fun s _ t _ hst => atom_disjoint Y hst)
    (fun s _ => atom_measurable Y hY s) (fun s hs => atom_finite μ Y hfin hs)).symm

theorem shading_mass {X : Type*} [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (Y : Fin M → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) (i : Fin M) :
    (∑ s ∈ patterns M, if i ∈ s then μ.real (atom Y s) else 0) = μ.real (Y i) := by
  rw [← Finset.sum_filter,← shading_atoms Y i]
  exact (measureReal_biUnion_finset (fun s _ t _ hst => atom_disjoint Y hst)
    (fun s _ => atom_measurable Y hY s)
    (fun s hs => atom_finite μ Y hfin (Finset.mem_filter.mp hs).1)).symm

/-- Literal incidence-volume double counting. The possibly exponentially many
atoms cause no loss: their volumes enter only through exact weighted sums. -/
theorem incidence_mass {X : Type*} [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (Y : Fin M → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) :
    (∑ s ∈ patterns M, μ.real (atom Y s)*(s.card:ℝ)) = ∑ i, μ.real (Y i) := by
  have hc (s : Finset (Fin M)) : (s.card:ℝ) = ∑ i : Fin M, if i ∈ s then (1:ℝ) else 0 := by simp
  simp_rw [hc,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => shading_mass μ Y hY hfin i)

/-- Any finite list of retained directions per atom gives actual measurable
shadings with exactly that direction incidence at every point in the old union. -/
def realize {X : Type*} {M : ℕ} (Y : Fin M → Set X)
    (row : Finset (Fin M) → Finset (Fin M)) (i : Fin M) : Set X :=
  ⋃ s ∈ (patterns M).filter (fun s => i ∈ row s), atom Y s

theorem realize_measurable {X : Type*} [MeasurableSpace X] {M : ℕ}
    (Y : Fin M → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (row : Finset (Fin M) → Finset (Fin M)) (i : Fin M) : MeasurableSet (realize Y row i) :=
  MeasurableSet.iUnion (fun s => MeasurableSet.iUnion (fun _ => atom_measurable Y hY s))

theorem realize_subset {X : Type*} {M : ℕ} (Y : Fin M → Set X)
    (row : Finset (Fin M) → Finset (Fin M)) (hrow : ∀ s ∈ patterns M, row s ⊆ s)
    (i : Fin M) : realize Y row i ⊆ Y i := by
  intro x hx
  obtain ⟨s,hs,hx⟩ := mem_iUnion₂.mp hx
  exact atom_subset_shading Y (hrow s (Finset.mem_filter.mp hs).1 (Finset.mem_filter.mp hs).2) hx

theorem realize_pattern {X : Type*} {M : ℕ} (Y : Fin M → Set X)
    (row : Finset (Fin M) → Finset (Fin M)) {x : X} (hx : x ∈ ⋃ i, Y i) :
    pattern (realize Y row) x = row (pattern Y x) := by
  have hp : pattern Y x ∈ patterns M := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact (mem_patterns _).mpr ⟨i,(mem_pattern Y x i).mpr hi⟩
  ext i
  rw [mem_pattern]
  constructor
  · intro hi
    obtain ⟨s,hs,hxs⟩ := mem_iUnion₂.mp hi
    have heq := (mem_atom Y s x).mp hxs
    simpa only [heq] using (Finset.mem_filter.mp hs).2
  · intro hi
    exact mem_iUnion₂.mpr ⟨pattern Y x,Finset.mem_filter.mpr ⟨hp,hi⟩,(mem_atom Y _ _).mpr rfl⟩

theorem realize_mass {X : Type*} [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (Y : Fin M → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) (row : Finset (Fin M) → Finset (Fin M)) (i : Fin M) :
    μ.real (realize Y row i) = ∑ s ∈ patterns M, if i ∈ row s then μ.real (atom Y s) else 0 := by
  rw [realize,measureReal_biUnion_finset (fun s _ t _ hst => atom_disjoint Y hst)
    (fun s _ => atom_measurable Y hY s)
    (fun s hs => atom_finite μ Y hfin (Finset.mem_filter.mp hs).1),Finset.sum_filter]

theorem realize_incidence_mass {X : Type*} [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (Y : Fin M → Set X) (hY : ∀ i, MeasurableSet (Y i))
    (hfin : ∀ i, μ (Y i) ≠ ∞) (row : Finset (Fin M) → Finset (Fin M)) :
    (∑ i, μ.real (realize Y row i)) = ∑ s ∈ patterns M, μ.real (atom Y s)*((row s).card:ℝ) := by
  simp_rw [realize_mass μ Y hY hfin row]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp [mul_comm]

/-- Every realized shading remains in the old union, even before imposing the
stronger incidence-preserving row-subset condition. -/
theorem realize_union_subset {X : Type*} {M : ℕ} (Y : Fin M → Set X)
    (row : Finset (Fin M) → Finset (Fin M)) :
    (⋃ i, realize Y row i) ⊆ ⋃ i, Y i := by
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨s,hs,hxs⟩ := mem_iUnion₂.mp hi
  exact atom_subset_union Y (Finset.mem_filter.mp hs).1 hxs

theorem realize_finite {X : Type*} [MeasurableSpace X] {M : ℕ}
    (μ : Measure X) (Y : Fin M → Set X) (hfin : ∀ i, μ (Y i) ≠ ∞)
    (row : Finset (Fin M) → Finset (Fin M)) (i : Fin M) :
    μ (realize Y row i) ≠ ∞ := by
  apply measure_ne_top_of_subset (fun x hx => realize_union_subset Y row (mem_iUnion.mpr ⟨i,hx⟩))
  simpa using measure_biUnion_ne_top (μ := μ) (f := Y) (Set.finite_univ : (Set.univ : Set (Fin M)).Finite) (fun i _ => hfin i)

/-- The omitted empty pattern has no retained incidence anywhere outside the
old union, regardless of what the abstract row map does at the empty pattern. -/
theorem realize_pattern_outside {X : Type*} {M : ℕ} (Y : Fin M → Set X)
    (row : Finset (Fin M) → Finset (Fin M)) {x : X} (hx : x ∉ ⋃ i, Y i) :
    pattern (realize Y row) x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact hx (realize_union_subset Y row (mem_iUnion.mpr ⟨i,(mem_pattern _ x i).mp hi⟩))

/-- The full pointwise description, including points of zero original
multiplicity. No assertion is made merely almost everywhere. -/
theorem realize_pattern_eq {X : Type*} {M : ℕ} (Y : Fin M → Set X)
    (row : Finset (Fin M) → Finset (Fin M)) (x : X) :
    pattern (realize Y row) x = if x ∈ ⋃ i, Y i then row (pattern Y x) else ∅ := by
  split_ifs with hx
  · exact realize_pattern Y row hx
  · exact realize_pattern_outside Y row hx

end
end KakeyaFormal.MeasurableIncidenceAtoms
