import Lean
namespace Fixture
axiom rogue : True
theorem usesRogue : True := rogue
end Fixture
