import LegalAngleSamples

/-! Actual intermediate and endpoint label fibers, with the common normalized
angle and endpoint geometry for each original marked angle. -/
namespace KakeyaFormal.LegalAngleNormalization
open Finset LegalAngleSamples TransverseAngles PivotWitnesses
noncomputable section
open Classical

variable {k M : ℕ} {F : TubeFamily k M} {H : Finset (Cell k)} {δ lam kappa width : ℝ}

def intermediates (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) : Finset (Cell k) := (S.samples a).image Prod.fst

def endpointLabels (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (i : Cell k) : Finset (Cell k × Cell k) :=
  ((S.samples a).filter (fun p => p.1=i)).image Prod.snd

theorem mem_endpointLabels (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (i : Cell k) (e : Cell k × Cell k) :
    e ∈ endpointLabels S a i ↔ (i,e) ∈ S.samples a := by
  constructor
  · intro he
    obtain ⟨p,hp,heq⟩ := mem_image.mp he
    obtain ⟨hp,hi⟩ := mem_filter.mp hp
    have hpEq : p=(i,e) := Prod.ext hi heq
    rwa [← hpEq]
  · intro hp
    exact mem_image.mpr ⟨(i,e),mem_filter.mpr ⟨hp,rfl⟩,rfl⟩

theorem intermediate_lower (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (i : ↥(intermediates S a)) :
    kappa ≤ S.sign a*firstCoordinate F δ a.val i.val := by
  obtain ⟨p,hp,hi⟩ := mem_image.mp i.property
  have hh := S.legal a p hp
  simpa only [hi] using hh.2.2.2.1

theorem angle_transverse (a : ↥(angles F H kappa)) (hkappa : 0 ≤ kappa) :
    kappa ≤ ‖KakeyaAudit.TubeGeometry.transverse (F.tube a.val.2.1).direction
      (F.tube a.val.2.2).direction‖ := by
  exact TransverseAngles.transverse_lower _ _ (F.tube _).unit_direction (F.tube _).unit_direction
    hkappa ((mem_angles F H kappa a.val).mp a.property).2.2.2

/-- The normalized angle depends only on its actual marked angle and its
intermediate label. It is common to all endpoint pairs in that fiber. -/
def angle (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (i : ↥(intermediates S a))
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) : Angle k (kappa/(1+2*width)) :=
  LegalSampleNormalization.normalizeAngle (cellCenter δ a.val.1)
    (F.tube a.val.2.1).direction (F.tube a.val.2.2).direction
    (firstCoordinate F δ a.val i.val) (S.sign a) kappa (1+2*width)
    (S.sign_valid a) (F.tube _).unit_direction (F.tube _).unit_direction hkappa
    (by linarith) (angle_transverse a hkappa.le) (intermediate_lower S a i)

/-- Original endpoint-label pairs instantiate the existing normalized
Endpoint record for precisely that common intermediate angle. -/
def endpoints (S : SampleSystem F H δ lam kappa width)
    (a : ↥(angles F H kappa)) (i : ↥(intermediates S a))
    (e : ↥(endpointLabels S a i.val))
    (hkappa : 0 < kappa) (hwidth : 0 ≤ width) : Endpoints (angle S a i hkappa hwidth) := by
  have hp := (mem_endpointLabels S a i.val e.val).mp e.property
  have hlegal := S.legal a (i.val,e.val) hp
  exact LegalSampleNormalization.normalizeEndpoints (cellCenter δ a.val.1)
    (F.tube a.val.2.1).direction (F.tube a.val.2.2).direction
    (firstCoordinate F δ a.val i.val) (firstCoordinate F δ a.val e.val.1)
    (secondCoordinate F δ a.val e.val.2) (S.sign a) kappa (1+2*width)
    (S.sign_valid a) (F.tube _).unit_direction (F.tube _).unit_direction hkappa
    (by linarith) (angle_transverse a hkappa.le) (intermediate_lower S a i)
    hlegal.2.2.2.2.1 hlegal.2.2.2.2.2.2.1 hlegal.2.2.2.2.2.1 hlegal.2.2.2.2.2.2.2

end
end KakeyaFormal.LegalAngleNormalization
