import Lean
namespace Fixture
set_option linter.deprecated false
structure Certificate : Type where
  proof : True
opaque proofCertificate : Certificate := ⟨Lean.trustCompiler⟩
theorem unrelated : True := True.intro
end Fixture
