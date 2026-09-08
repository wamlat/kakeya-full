import Lean
namespace Fixture
set_option linter.deprecated false
theorem usesCompilerAxiom : True := Lean.trustCompiler
end Fixture
