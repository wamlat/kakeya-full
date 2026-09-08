import GridCells
import ScaleChoice
import PrunedGraphLift

/-! Actual finite spatial tests for sampling. Test centers are occupied grid
centers and test radii are doubled dyadic radii. Every relevant arbitrary ball
is covered with factor four, and Euclidean geometry bounds the number of tests. -/
namespace KakeyaFormal.SamplingBallTests
open Finset KakeyaFormal.Localization GridCells GridGeometry
open scoped BigOperators
noncomputable section
open Classical

abbrev Test {n : ℕ} (E : Finset (Cell n)) (J : ℕ) := ↥E × Fin (J+1)

def testRadius {n : ℕ} {E : Finset (Cell n)} {J : ℕ} (t : Test E J) : ℝ :=
  2*radius J t.2.val

def testCells {n : ℕ} (E : Finset (Cell n)) (δ : ℝ) {J : ℕ} (t : Test E J) : Finset (Cell n) :=
  E.filter (fun z => dist (cellCenter δ z) (cellCenter δ t.1.val) ≤ testRadius t)

/-- A finite actual Boolean mask, directly usable by SamplingApplication. -/
def mask {n : ℕ} {E : Finset (Cell n)} (δ : ℝ) {J : ℕ} (t : Test E J) (z : ↥E) : Bool :=
  decide (dist (cellCenter δ z.val) (cellCenter δ t.1.val) ≤ testRadius t)

theorem test_card {n : ℕ} (E : Finset (Cell n)) (J : ℕ) :
    Fintype.card (Test E J) = E.card*(J+1) := by simp [Test]

theorem radius_bounds {n : ℕ} {E : Finset (Cell n)} {δ : ℝ} {J : ℕ}
    (hbottom : δ ≤ radius J 0) (t : Test E J) :
    2*δ ≤ testRadius t ∧ testRadius t ≤ 2 := by
  have hlo := radius_mono J (Nat.zero_le t.2.val)
  have hhi := radius_mono J (show t.2.val ≤ J by omega)
  rw [radius_top] at hhi
  dsimp [testRadius]
  constructor <;> linarith

/-- The chosen dyadic scale also covers radii below the coarser bottom scale. -/
theorem round_from_mesh {δ r : ℝ} {J : ℕ}
    (hbottom : radius J 0 ≤ 2*δ) (hr : δ ≤ r) (hr1 : r ≤ 1) :
    ∃ j ≤ J, r ≤ radius J j ∧ radius J j ≤ 2*r := by
  by_cases hlo : radius J 0 ≤ r
  · exact dyadic_round hlo hr1
  · exact ⟨0,Nat.zero_le _,le_of_not_ge hlo,by linarith⟩

/-- A nonempty intersection with an arbitrary ball chooses one ACTUAL occupied
center. All its other occupied cells lie in the corresponding doubled test. -/
theorem covers_ball {n : ℕ} (E : Finset (Cell n)) {δ : ℝ} {J : ℕ}
    (hbottom : radius J 0 ≤ 2*δ) (x : Space n) {r : ℝ}
    (hr : δ ≤ r) (hr1 : r ≤ 1)
    (hne : (E.filter (fun z => dist (cellCenter δ z) x ≤ r)).Nonempty) :
    ∃ t : Test E J, r ≤ testRadius t ∧ testRadius t ≤ 4*r ∧
      E.filter (fun z => dist (cellCenter δ z) x ≤ r) ⊆ testCells E δ t := by
  obtain ⟨z,hz⟩ := hne
  obtain ⟨j,hj,hrj,hj2⟩ := round_from_mesh hbottom hr hr1
  let t : Test E J := (⟨z,(mem_filter.mp hz).1⟩,⟨j,by omega⟩)
  have hpos := radius_pos J j
  refine ⟨t,?_,?_,?_⟩
  · dsimp [t,testRadius]; linarith
  · dsimp [t,testRadius]; linarith
  · intro y hy
    have htri := dist_triangle (cellCenter δ y) x (cellCenter δ z)
    rw [dist_comm x] at htri
    exact mem_filter.mpr ⟨(mem_filter.mp hy).1,by
      change dist (cellCenter δ y) (cellCenter δ z) ≤ 2*radius J j
      linarith [(mem_filter.mp hy).2,(mem_filter.mp hz).2]⟩

/-- A finite bounded support has its geometric grid count derived explicitly. -/
theorem support_card {n : ℕ} (E : Finset (Cell n)) {δ R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R)
    (hbounded : ∀ z ∈ E, ‖cellCenter δ z‖ ≤ R) :
    (E.card : ℝ) ≤ (5:ℝ)^n*(1+R)^n*(1/δ)^n := by
  have hgrid := ball_grid_count_real hδ (div_nonneg hR hδ.le) (0 : Space n) E
    (fun z hz => by simpa only [dist_zero_right,div_mul_cancel₀ _ hδ.ne'] using hbounded z hz)
  have hbase : 1+R/δ ≤ (1+R)*(1/δ) := by
    have hN : 1 ≤ 1/δ := (le_div_iff₀ hδ).mpr (by simpa using hδ1)
    rw [show (1+R)*(1/δ) = 1/δ+R/δ by ring]
    linarith
  calc
    (E.card : ℝ) ≤ (5:ℝ)^n*(1+R/δ)^n := hgrid
    _ ≤ (5:ℝ)^n*((1+R)*(1/δ))^n := by gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Actual cardinality of the spatial testing family, bounded only by fixed
Euclidean support geometry and the scale logarithm. -/
theorem test_card_bound {n : ℕ} (E : Finset (Cell n)) {δ R : ℝ} {J : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R)
    (hbounded : ∀ z ∈ E, ‖cellCenter δ z‖ ≤ R)
    (hdepth : (J:ℝ) ≤ Real.log (1/δ)/Real.log 2) :
    (Fintype.card (Test E J) : ℝ) ≤
      (5:ℝ)^n*(1+R)^n*(1/δ)^n*(Real.log (1/δ)/Real.log 2+1) := by
  rw [test_card,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  exact mul_le_mul (support_card E hδ hδ1 hR hbounded) (by linarith)
    (by positivity) (by positivity)

/-- Construct the finite family without any covering or count premise. Empty
support intersections are handled separately and require no artificial test. -/
theorem construct {n : ℕ} (E : Finset (Cell n)) {δ R : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 ≤ R)
    (hbounded : ∀ z ∈ E, ‖cellCenter δ z‖ ≤ R) :
    ∃ J : ℕ, δ ≤ radius J 0 ∧ radius J 0 < 2*δ ∧
      (J:ℝ) ≤ Real.log (1/δ)/Real.log 2 ∧
      (∀ t : Test E J, 2*δ ≤ testRadius t ∧ testRadius t ≤ 2) ∧
      (Fintype.card (Test E J) : ℝ) ≤
        (5:ℝ)^n*(1+R)^n*(1/δ)^n*(Real.log (1/δ)/Real.log 2+1) ∧
      ∀ x : Space n, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
        (E.filter (fun z => dist (cellCenter δ z) x ≤ r))=∅ ∨
        ∃ t : Test E J, r ≤ testRadius t ∧ testRadius t ≤ 4*r ∧
          E.filter (fun z => dist (cellCenter δ z) x ≤ r) ⊆ testCells E δ t := by
  obtain ⟨J,hbottom,hbottom2,hdepth⟩ := ScaleChoice.dyadic_depth hδ hδ1
  refine ⟨J,hbottom,hbottom2,hdepth,radius_bounds hbottom,test_card_bound E hδ hδ1 hR hbounded hdepth,?_⟩
  intro x r hr hr1
  by_cases hne : (E.filter (fun z => dist (cellCenter δ z) x ≤ r)).Nonempty
  · exact Or.inr (covers_ball E hbottom2.le x hr hr1 hne)
  · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)

/-- Bounds on the finitely many actual tests imply the required all-ball
bound for every sampled shading contained in the available support. -/
theorem all_ball_from_tests {n : ℕ} (E Y : Finset (Cell n)) {δ D alpha : ℝ} {J : ℕ}
    (hsub : Y ⊆ E) (hδ : 0 < δ) (hbottom : radius J 0 ≤ 2*δ)
    (hD : 0 ≤ D) (ha : 0 ≤ alpha)
    (htest : ∀ t : Test E J,
      ((Y.filter (fun z => dist (cellCenter δ z) (cellCenter δ t.1.val) ≤ testRadius t)).card : ℝ) ≤
        D*(testRadius t)^alpha) :
    ∀ x : Space n, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((Y.filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
        (4:ℝ)^alpha*D*r^alpha := by
  intro x r hr hr1
  have hEsub : Y.filter (fun z => dist (cellCenter δ z) x ≤ r) ⊆
      E.filter (fun z => dist (cellCenter δ z) x ≤ r) := filter_subset_filter _ hsub
  by_cases hne : (E.filter (fun z => dist (cellCenter δ z) x ≤ r)).Nonempty
  · obtain ⟨t,_,htr,hcover⟩ := covers_ball E hbottom x hr hr1 hne
    have hcovered : Y.filter (fun z => dist (cellCenter δ z) x ≤ r) ⊆
        Y.filter (fun z => dist (cellCenter δ z) (cellCenter δ t.1.val) ≤ testRadius t) := by
      intro z hz
      exact mem_filter.mpr ⟨(mem_filter.mp hz).1,(mem_filter.mp (hcover (hEsub hz))).2⟩
    have hcard : ((Y.filter (fun z => dist (cellCenter δ z) x ≤ r)).card : ℝ) ≤
        (Y.filter (fun z => dist (cellCenter δ z) (cellCenter δ t.1.val) ≤ testRadius t)).card := by
      exact_mod_cast card_le_card hcovered
    have hrad : 0 ≤ testRadius t :=
      mul_nonneg (by norm_num) (radius_pos J t.2.val).le
    calc
      _ ≤ D*(testRadius t)^alpha := hcard.trans (htest t)
      _ ≤ D*(4*r)^alpha := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hrad htr ha) hD
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (hδ.trans_le hr).le]; ring
  · have hempty : Y.filter (fun z => dist (cellCenter δ z) x ≤ r) = ∅ :=
      subset_empty.mp ((not_nonempty_iff_eq_empty.mp hne) ▸ hEsub)
    rw [hempty,card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hD)
      (Real.rpow_nonneg (hδ.trans_le hr).le _)

end
end KakeyaFormal.SamplingBallTests

#print axioms KakeyaFormal.SamplingBallTests.construct
#print axioms KakeyaFormal.SamplingBallTests.all_ball_from_tests
