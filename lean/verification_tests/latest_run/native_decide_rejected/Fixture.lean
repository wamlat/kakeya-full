import Lean
namespace Fixture
theorem nativeChecked : (1 : Nat) = 1 := by native_decide
end Fixture
