import Lean
namespace Fixture
structure Certificate : Type where
  proof : True
axiom published : True
def proofCertificate : Certificate := ⟨published⟩
theorem unrelated : True := True.intro
end Fixture
