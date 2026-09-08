import LegalParameterSelection
import PivotWitnesses

/-! Legal pivot samples constructed from actual tube shadings and two ends. -/
namespace KakeyaFormal.LegalTubeSamples
open KakeyaAudit.TubeGeometry
open Finset
noncomputable section
open Classical

def coordinate {k : ℕ} (u vertex x : Space k) : ℝ := inner ℝ u (x-vertex)

/-- Orthogonal projection onto the shifted axis is at least as close as any
other point on that axis. -/
theorem projection_distance_le {k : ℕ} (u vertex x : Space k) (s : ℝ)
    (hu : ‖u‖ = 1) :
    dist x (vertex+coordinate u vertex x • u) ≤ dist x (vertex+s • u) := by
  have hid : transverse u (x-(vertex+s • u)) = x-(vertex+coordinate u vertex x • u) := by
    simp only [transverse,coordinate,inner_sub_right,inner_add_right,inner_smul_right,
      real_inner_self_eq_norm_sq,hu,one_pow,mul_one]
    module
  simpa only [dist_eq_norm,hid] using transverse_norm_le u (x-(vertex+s • u)) hu

/-- Actual projection changes the longitudinal coordinate by at most the
physical distance to any given axis point. -/
theorem coordinate_difference_le {k : ℕ} (u vertex x : Space k) (s : ℝ)
    (hu : ‖u‖ = 1) : |coordinate u vertex x-s| ≤ dist x (vertex+s • u) := by
  have hid : coordinate u vertex x-s = inner ℝ u (x-(vertex+s • u)) := by
    simp only [coordinate,inner_sub_right,inner_add_right,inner_smul_right,
      real_inner_self_eq_norm_sq,hu,one_pow,mul_one]
    ring
  calc
    |coordinate u vertex x-s| = |inner ℝ u (x-(vertex+s • u))| := congrArg abs hid
    _ ≤ ‖u‖*‖x-(vertex+s • u)‖ := abs_real_inner_le_norm _ _
    _ = dist x (vertex+s • u) := by rw [hu,one_mul,dist_eq_norm]

/-- Both occupied points lie in the original tube. Shifting its axis through
the actual common vertex costs at most twice the tube radius, and all projected
coordinates stay within a fixed extension of a unit segment. -/
theorem shifted_tube_projection {k : ℕ} (T : UnitTube k) (vertex x : Space k)
    {radius : ℝ} (hv : vertex ∈ T.carrier radius) (hx : x ∈ T.carrier radius) :
    dist x (vertex+coordinate T.direction vertex x • T.direction) ≤ 2*radius ∧
    |coordinate T.direction vertex x| ≤ 1+2*radius := by
  obtain ⟨s,hs,hxs⟩ := hx
  obtain ⟨t,ht,hvt⟩ := hv
  have hid : x-(vertex+(s-t) • T.direction) =
      (x-T.axisPoint s)-(vertex-T.axisPoint t) := by
    dsimp [UnitTube.axisPoint]
    module
  have hclose : dist x (vertex+(s-t) • T.direction) ≤ 2*radius := by
    rw [dist_eq_norm,hid]
    have hh := norm_sub_le (x-T.axisPoint s) (vertex-T.axisPoint t)
    rw [dist_eq_norm] at hxs hvt
    linarith
  refine ⟨(projection_distance_le T.direction vertex x (s-t) T.unit_direction).trans hclose,?_⟩
  have hc := (coordinate_difference_le T.direction vertex x (s-t) T.unit_direction).trans hclose
  have hst : |s-t| ≤ 1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
  have hh := abs_add_le (coordinate T.direction vertex x-(s-t)) (s-t)
  rw [sub_add_cancel] at hh
  linarith

/-- The geometric abundance assertion of (5.11), with actual occupied cell
labels and deterministic orthogonal projections. Its interval nonconcentration
is proved from physical two ends, and the common vertex belongs to both tubes. -/
theorem legal_triples_from_tubes {k : ℕ} (T1 T2 : UnitTube k)
    (S1 S2 : Finset (Cell k)) (vertex : Space k)
    {δ lam kappa width B alpha : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hlam : 0 < lam) (hwidth : 0 ≤ width)
    (hδkappa : δ ≤ kappa)
    (hv1 : vertex ∈ T1.carrier (width*δ)) (hv2 : vertex ∈ T2.carrier (width*δ))
    (hS1 : ∀ z ∈ S1, cellCenter δ z ∈ T1.carrier (width*δ))
    (hS2 : ∀ z ∈ S2, cellCenter δ z ∈ T2.carrier (width*δ))
    (hmass1 : lam/δ ≤ (S1.card:ℝ)) (hmass2 : lam/δ ≤ (S2.card:ℝ))
    (hends1 : ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((S1.filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤ B*r^alpha*(S1.card:ℝ))
    (hends2 : ∀ x : Space k, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ((S2.filter (fun z => dist (cellCenter δ z) x ≤ r)).card:ℝ) ≤ B*r^alpha*(S2.card:ℝ))
    (hradius : (2*width+1)*kappa ≤ 1)
    (hsmall : B*((2*width+1)*kappa)^alpha ≤ 1/16) :
    let f := fun z => coordinate T1.direction vertex (cellCenter δ z)
    let g := fun z => coordinate T2.direction vertex (cellCenter δ z)
    ∃ sign : ℝ, ∃ samples : Finset (Cell k × (Cell k × Cell k)),
      (sign=1 ∨ sign= -1) ∧ (lam/δ)^3/128 ≤ (samples.card:ℝ) ∧
      ∀ p ∈ samples, p.1 ∈ S1 ∧ p.2.1 ∈ S1 ∧ p.2.2 ∈ S2 ∧
        kappa ≤ sign*f p.1 ∧ kappa ≤ sign*f p.2.1-sign*f p.1 ∧
        kappa ≤ |g p.2.2| ∧ sign*f p.2.1 ≤ 1+2*width ∧ |g p.2.2| ≤ 1+2*width := by
  dsimp only
  let f := fun z => coordinate T1.direction vertex (cellCenter δ z)
  let g := fun z => coordinate T2.direction vertex (cellCenter δ z)
  have hclose1 : ∀ z ∈ S1, dist (cellCenter δ z) (vertex+f z • T1.direction) ≤ (2*width)*δ := by
    intro z hz
    convert (shifted_tube_projection T1 vertex (cellCenter δ z) hv1 (hS1 z hz)).1 using 1; ring
  have hclose2 : ∀ z ∈ S2, dist (cellCenter δ z) (vertex+g z • T2.direction) ≤ (2*width)*δ := by
    intro z hz
    convert (shifted_tube_projection T2 vertex (cellCenter δ z) hv2 (hS2 z hz)).1 using 1; ring
  have hw1 := LegalParameterSelection.projected_interval_nonconcentration S1 vertex T1.direction f
    hδ hδkappa (by positivity : 0 ≤ 2*width) T1.unit_direction hclose1 hends1 hradius hsmall
  have hw2 := LegalParameterSelection.projected_interval_nonconcentration S2 vertex T2.direction g
    hδ hδkappa (by positivity : 0 ≤ 2*width) T2.unit_direction hclose2 hends2 hradius hsmall
  obtain ⟨sign,samples,hsign,hcard,hlegal⟩ := LegalParameterSelection.legal_triples S1 S2 f g
    (hδ.trans_le hδkappa) (div_pos hlam hδ) hmass1 hmass2 hw1
    (by simpa only [sub_zero] using hw2 0)
  refine ⟨sign,samples,hsign,hcard,?_⟩
  intro p hp
  obtain ⟨hi,hj,hc,ha,hgap,hremote⟩ := hlegal p hp
  have hfirst := (shifted_tube_projection T1 vertex (cellCenter δ p.2.1) hv1 (hS1 _ hj)).2
  have hsecond := (shifted_tube_projection T2 vertex (cellCenter δ p.2.2) hv2 (hS2 _ hc)).2
  have hfirst' : |f p.2.1| ≤ 1+2*width := hfirst.trans (by nlinarith)
  have hsecond' : |g p.2.2| ≤ 1+2*width := hsecond.trans (by nlinarith)
  refine ⟨hi,hj,hc,ha,hgap,hremote,?_,hsecond'⟩
  rcases hsign with rfl | rfl
  · simpa only [one_mul] using (le_abs_self _).trans hfirst'
  · simpa only [neg_one_mul] using (neg_le_abs _).trans hfirst'

end
end KakeyaFormal.LegalTubeSamples
