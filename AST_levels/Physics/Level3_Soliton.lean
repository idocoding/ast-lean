import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# AST.Level3.Soliton

Canonical Level 3 vocabulary for soliton-scale physics quantities.

This module promotes the stable loop-radius kinematics used later in the string
and particle discussions, without yet importing the stronger model-specific
claims from those files.
-/

open Real

namespace AST
namespace Level3
namespace Soliton

/-- The minimal interior support size for a stable loop/soliton sector. -/
abbrev SigmaMin := ℕ

/-- The loop radius associated to a soliton support threshold `σ_min`. -/
noncomputable def loopRadius (σ_min : SigmaMin) : ℝ :=
  (σ_min : ℝ) ^ ((1 : ℝ) / 3)

theorem loopRadius_pos (σ_min : SigmaMin) (hσ : 0 < σ_min) :
    0 < loopRadius σ_min := by
  unfold loopRadius
  apply Real.rpow_pos_of_pos
  exact_mod_cast hσ

/-- A purely kinematic worldsheet-area proxy for a loop tracked over `T` steps. -/
noncomputable def worldsheetArea (σ_min : SigmaMin) (T : ℝ) : ℝ :=
  2 * loopRadius σ_min * T

theorem worldsheetArea_pos (σ_min : SigmaMin) (hσ : 0 < σ_min)
    (T : ℝ) (hT : 0 < T) :
    0 < worldsheetArea σ_min T := by
  unfold worldsheetArea
  apply mul_pos
  · apply mul_pos
    · norm_num
    · exact loopRadius_pos σ_min hσ
  · exact hT

end Soliton
end Level3
end AST
