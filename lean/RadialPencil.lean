import LiftGraph
import CumulativeEstimate

/-! An explicit full-dimensional radial pencil. Directions are normalized
graphs of a literal finite k-dimensional rational grid. Every tube starts at
the origin and is shaded by the same original grid cell. -/
namespace KakeyaFormal.RadialPencil
open Finset ProjectiveGeometry LiftGraph
noncomputable section
open Classical

abbrev Index (k N : ℕ) := Fin k → Fin N

def population (k N : ℕ) : ℕ := Fintype.card (Index k N)

theorem population_eq (k N : ℕ) : population k N = N^k := by
  simp [population,Index]

def label {k N : ℕ} (i : Index k N) : Cell k := fun j => ((i j).val:ℤ)

theorem label_injective {k N : ℕ} : Function.Injective (label (k:=k) (N:=N)) := by
  intro i j h
  funext l
  apply Fin.ext
  have hh := congrFun h l
  dsimp [label] at hh
  exact_mod_cast hh

def slope {k N : ℕ} (i : Index k N) : Space k := cellCenter (1/(N:ℝ)) (label i)

def chartConstant (k : ℕ) : ℝ := 2*(1+(k:ℝ))^2

def scale (k N : ℕ) : ℝ := 1/(chartConstant k*(N:ℝ))

theorem chartConstant_ge_two (k : ℕ) : 2 ≤ chartConstant k := by
  dsimp [chartConstant]
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [sq_nonneg (k:ℝ)]

theorem scale_pos (k : ℕ) {N : ℕ} (hN : 0 < N) : 0 < scale k N := by
  have hC := chartConstant_ge_two k
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  unfold scale
  positivity

theorem scale_le_one (k : ℕ) {N : ℕ} (hN : 0 < N) : scale k N ≤ 1 := by
  have hC := chartConstant_ge_two k
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  unfold scale
  apply (div_le_one (by positivity)).mpr
  nlinarith

theorem slope_norm {k N : ℕ} (hN : 0 < N) (i : Index k N) : ‖slope i‖ ≤ (k:ℝ) := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hcoord (j : Fin k) : |WithLp.ofLp (slope i) j| ≤ 1 := by
    change |(1/(N:ℝ))*(((i j).val:ℤ):ℝ)| ≤ 1
    rw [Int.cast_natCast,abs_of_nonneg (by positivity)]
    have hj : ((i j).val:ℝ) ≤ N := by exact_mod_cast (i j).isLt.le
    have hh := mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ 1/(N:ℝ))
    simpa only [one_div,inv_mul_cancel₀ hNR.ne'] using hh
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hcoord j)
  exact (norm_le_coordinate_sum (slope i)).trans (by simpa using hh)

theorem slope_separation {k N : ℕ} (hN : 0 < N) {i j : Index k N} (hij : i ≠ j) :
    1/(N:ℝ) ≤ ‖slope i-slope j‖ := by
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hh := modular_grid_separation (Q:=1) label label_injective
    (show 0 < 1/(N:ℝ) by positivity) hij (by funext l; exact Subsingleton.elim _ _)
  simpa only [Nat.cast_one,mul_one,dist_eq_norm,slope] using hh

theorem direction_separation {k N : ℕ} (hN : 0 < N) {i j : Index k N} (hij : i ≠ j) :
    scale k N ≤ projectiveDistance (graphDirection (slope i)) (graphDirection (slope j)) := by
  have hh := (slope_separation hN hij).trans
    (graphDirection_inverse (slope i) (slope j) (Nat.cast_nonneg k) (slope_norm hN i) (slope_norm hN j))
  have hC : 0 < chartConstant k := lt_of_lt_of_le (by norm_num) (chartConstant_ge_two k)
  have hh' : 1/(N:ℝ) ≤
      projectiveDistance (graphDirection (slope i)) (graphDirection (slope j))*chartConstant k := by
    simpa only [chartConstant,mul_comm] using hh
  have hdiv := (div_le_iff₀ hC).mpr hh'
  simpa only [scale,div_div,mul_comm] using hdiv

def index (k N : ℕ) : Fin (population k N) → Index k N := (Fintype.equivFin (Index k N)).symm

theorem index_injective (k N : ℕ) : Function.Injective (index k N) :=
  (Fintype.equivFin (Index k N)).symm.injective

def family (k N : ℕ) : TubeFamily (k+1) (population k N) where
  tube i := { base := 0, direction := graphDirection (slope (index k N i)), unit_direction := graphDirection_unit _ }
  shade _ := {0}

theorem family_separated (k : ℕ) {N : ℕ} (hN : 0 < N) :
    (family k N).Separated (scale k N) := by
  intro i j hij
  exact direction_separation hN (fun heq => hij (index_injective k N heq))

theorem family_base (k N : ℕ) (i : Fin (population k N)) : ((family k N).tube i).base = 0 := rfl

theorem family_shade (k N : ℕ) (i : Fin (population k N)) : (family k N).shade i = {0} := rfl

theorem family_admissible (k : ℕ) {N : ℕ} (hN : 0 < N) :
    (family k N).Admissible 1 (scale k N) := by
  intro i z hz
  have hz0 : z = 0 := Finset.mem_singleton.mp hz
  subst z
  refine ⟨0,by norm_num,?_⟩
  have hc : cellCenter (scale k N) (0:Cell (k+1)) = 0 := by ext j; simp [cellCenter]
  simp only [hc,UnitTube.axisPoint,family,zero_smul,zero_add,dist_self,one_mul]
  exact (scale_pos k hN).le

theorem family_bounded (k N : ℕ) : (family k N).Bounded 1 := by
  intro i
  simp only [family,norm_zero]
  norm_num

theorem family_comparable (k : ℕ) {N : ℕ} (hN : 0 < N) :
    (family k N).Comparable (scale k N) (scale k N) := by
  intro i
  have hd := (scale_pos k hN).ne'
  simp only [family,Finset.card_singleton,Nat.cast_one,div_self hd]
  constructor
  · exact le_rfl
  · rw [mul_div_cancel_right₀ _ hd]
    norm_num

theorem population_pos (k : ℕ) {N : ℕ} (hN : 0 < N) : 0 < population k N := by
  rw [population_eq]
  exact pow_pos hN k

theorem family_union (k : ℕ) {N : ℕ} (hN : 0 < N) : (family k N).unionCells = {0} := by
  ext z
  simp only [TubeFamily.unionCells,Finset.mem_biUnion,Finset.mem_univ,true_and,
    family,Finset.mem_singleton]
  constructor
  · rintro ⟨i,hi⟩
    exact hi
  · intro hz
    exact ⟨⟨0,population_pos k hN⟩,hz⟩

theorem family_union_card (k : ℕ) {N : ℕ} (hN : 0 < N) :
    ((family k N).unionCells.card:ℝ) = 1 := by rw [family_union k hN]; simp

theorem family_total_incidence (k N : ℕ) :
    ∑ i, (((family k N).shade i).card:ℝ) = (population k N:ℝ) := by simp [family]

/-- Exact full-dimensional population at the actual separated mesh. -/
theorem population_scale_identity (k : ℕ) {N : ℕ} (hN : 0 < N) :
    (scale k N)^k*(population k N:ℝ) = (1/chartConstant k)^k := by
  rw [population_eq,Nat.cast_pow,← mul_pow]
  congr 1
  have hNR : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  dsimp [scale]
  field_simp

/-- The explicit pencils occur at arbitrarily small positive meshes. -/
theorem arbitrarily_small_scale (k : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ N : ℕ, 0 < N ∧ scale k N < eps := by
  have hC : 0 < chartConstant k := lt_of_lt_of_le (by norm_num) (chartConstant_ge_two k)
  obtain ⟨N,hN⟩ := exists_nat_gt (1/(chartConstant k*eps))
  have hNR : (0:ℝ) < N := (by positivity : 0 < 1/(chartConstant k*eps)).trans hN
  refine ⟨N,Nat.cast_pos.mp hNR,?_⟩
  have hh := (div_lt_iff₀ (mul_pos hC heps)).mp hN
  apply (div_lt_iff₀ (mul_pos hC hNR)).mpr
  convert hh using 1
  ring

/-- A full-dimensional separated family has the claimed fractional cap
coefficient. The upper radius cutoff r≤1 supplies the missing fractional power. -/
theorem fractional_cap_from_full {k M : ℕ} (F : TubeFamily (k+1) M)
    {δ m C : ℝ} (hδ : 0 < δ) (hm : m ≤ (k:ℝ)) (hC : 0 ≤ C)
    (hfull : F.CapBound δ (k:ℝ) C) :
    F.CapBound δ m (C*δ^(m-(k:ℝ))) := by
  intro v hv r hr hr1
  have hrpos : 0 < r := hδ.trans_le hr
  have hratio : 0 < r/δ := div_pos hrpos hδ
  have htail := Real.rpow_le_rpow hratio.le
    (div_le_div_of_nonneg_right hr1 hδ.le) (sub_nonneg.mpr hm)
  have hid : (r/δ)^(k:ℝ) = (r/δ)^m*(r/δ)^((k:ℝ)-m) := by
    rw [← Real.rpow_add hratio]
    congr 1
    ring
  have hinv : (1/δ)^((k:ℝ)-m) = δ^(m-(k:ℝ)) := by
    rw [one_div,Real.inv_rpow hδ.le,← Real.rpow_neg hδ.le]
    congr 1
    ring
  calc
    _ ≤ C*(r/δ)^(k:ℝ) := hfull v hv r hr hr1
    _ = C*((r/δ)^m*(r/δ)^((k:ℝ)-m)) := by rw [hid]
    _ ≤ C*((r/δ)^m*(1/δ)^((k:ℝ)-m)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htail (Real.rpow_nonneg hratio.le _)) hC
    _ = (C*δ^(m-(k:ℝ)))*(r/δ)^m := by rw [hinv]; ring

def capCoefficient (k N : ℕ) (m : ℝ) : ℝ :=
  fullDirectionCoefficient k 1 * (scale k N)^(m-(k:ℝ))

theorem capCoefficient_ge_one (k : ℕ) {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : m ≤ (k:ℝ)) :
    1 ≤ capCoefficient k N m := by
  have hC := fullDirectionCoefficient_ge_one k (show (0:ℝ)<1 by norm_num)
  have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos
    (scale_pos k hN) (scale_le_one k hN) (sub_nonpos.mpr hm)
  exact one_le_mul_of_one_le_of_one_le hC hp

theorem family_cap_bound (k : ℕ) {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : m ≤ (k:ℝ)) :
    (family k N).CapBound (scale k N) m (capCoefficient k N m) := by
  have hsep : (family k N).Separated (1*scale k N) := by
    simpa only [one_mul] using family_separated k hN
  have hfull := separated_tube_family_cap_bound (family k N) (scale_pos k hN)
    (show (0:ℝ)<1 by norm_num) hsep
  exact fractional_cap_from_full (family k N) (scale_pos k hN) hm
    (zero_le_one.trans (fullDirectionCoefficient_ge_one k (by norm_num))) hfull

/-- Fixed geometry before every pencil size and real cap exponent. -/
def geometry : Normalization where
  width := 1
  separation := 1
  radius := 1
  width_pos := by norm_num
  separation_pos := by norm_num
  radius_pos := by norm_num

/-- A literal normalized shaded configuration, with density exactly its mesh
and all individual shadings equal to the common original singleton cell. -/
def configuration (k : ℕ) {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : m ≤ (k:ℝ)) :
    ShadedConfiguration (k+1) geometry m where
  M := population k N
  δ := scale k N
  lam := scale k N
  A := capCoefficient k N m
  family := family k N
  scale_pos := scale_pos k hN
  scale_le_one := scale_le_one k hN
  density_pos := scale_pos k hN
  density_le_one := scale_le_one k hN
  cap_ge_one := capCoefficient_ge_one k hN hm
  admissible := family_admissible k hN
  separated := by simpa only [geometry,one_mul] using family_separated k hN
  bounded := family_bounded k N
  cap_bound := family_cap_bound k hN hm
  comparable := family_comparable k hN

/-- The same actual pencil is a cumulative configuration with total incidence
exactly delta times population at density s=delta. -/
def cumulativeConfiguration (k : ℕ) {N : ℕ} (hN : 0 < N) {m : ℝ} (hm : m ≤ (k:ℝ)) :
    CumulativeConfiguration (k+1) geometry m where
  M := population k N
  δ := scale k N
  s := scale k N
  A := capCoefficient k N m
  family := family k N
  scale_pos := scale_pos k hN
  scale_le_one := scale_le_one k hN
  density_nonneg := (scale_pos k hN).le
  cap_ge_one := capCoefficient_ge_one k hN hm
  admissible := family_admissible k hN
  separated := by simpa only [geometry,one_mul] using family_separated k hN
  bounded := family_bounded k N
  cap_bound := family_cap_bound k hN hm
  cumulative := by rw [family_total_incidence]

end
end KakeyaFormal.RadialPencil
