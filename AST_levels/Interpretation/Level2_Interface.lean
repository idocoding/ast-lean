import AST_levels.Foundation.Level0
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# AST.Level2

Level 2 is where a physical interpretation must be specified and verified.

This file is based on the role played by `AST_files/AST_Level2_Programme.lean`
and `AST_files/AST_Level2_Framework.lean`: it is an interface layer, not a
place for silent physical assumptions.
-/

namespace AST
namespace Level2

universe u

/-- A Level-2 theory chooses a physical primitive and proves that its
distinguishability model matches the structural requirements. -/
class Theory (Primitive : Type u) [DecidableEq Primitive] where
  Dist : Finset Primitive -> ℝ
  charge : Primitive -> Bool
  charge_binary : forall p : Primitive, charge p = true \/ charge p = false
  dist_bounded : exists Kmax : ℝ, forall c : Finset Primitive, Real.log (Dist c) <= Kmax
  dist_pos : forall c : Finset Primitive, c.Nonempty -> 0 < Dist c
  dist_multiplicative :
    forall c1 c2 : Finset Primitive, Disjoint c1 c2 -> Dist (c1 ∪ c2) = Dist c1 * Dist c2
  corrections_terminate : True

namespace OpenQuestions

/-- Level 2 still requires a concrete primitive, a concrete `Dist`, and
verification that the primitive really satisfies the structural interface. -/
def programmeStatement : String :=
  "Choose Primitive, define Dist, derive charge from Dist, and verify the structural interface."

end OpenQuestions

end Level2
end AST
