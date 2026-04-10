import AST_levels.Foundation.Level1

/-!
# AST.Level1.CorrectionDynamics

Canonical Level 1 support for the correction-dynamics side of Paper 0.

This file keeps only what is genuinely derivable from the current canonical
Level 0 semantics: a step exists, and by definition it does not increase `K`.
Anything stronger about continuum geometry belongs in Level 2 or higher.
-/

namespace AST
namespace Level1
namespace CorrectionDynamics

open Level0

universe u

variable {X : Type u} [DecidableEq X] [Fintype X]
variable [Level0.SigmaStructure X] [Level0.StepStructure X]

/-- Configurations in the canonical correction-dynamics layer. -/
abbrev Config (X : Type u) := Finset X

/-- The one-step correction pressure is the capacity decrease across a single step. -/
noncomputable def correctionPressure (region : Config X) : ℝ :=
  Level0.K region - Level0.K (Level0.StepStructure.step region)

/-- Structural equilibrium means one correction step leaves the configuration unchanged. -/
def IsEquilibrium (region : Config X) : Prop :=
  Level0.StepStructure.step region = region

theorem correctionPressure_nonneg (region : Config X) :
    0 ≤ correctionPressure region := by
  dsimp [correctionPressure]
  linarith [Level1.correction_monotone region]

theorem correctionPressure_eq_capacity_drop (region : Config X) :
    correctionPressure region =
      Level0.K region - Level0.K (Level0.StepStructure.step region) := rfl

theorem equilibrium_preserves_capacity (region : Config X)
    (hEq : IsEquilibrium region) :
    Level0.K (Level0.StepStructure.step region) = Level0.K region := by
  simp [IsEquilibrium] at hEq
  simp [hEq]

theorem equilibrium_has_zero_pressure (region : Config X)
    (hEq : IsEquilibrium region) :
    correctionPressure region = 0 := by
  simp [correctionPressure, IsEquilibrium] at hEq ⊢
  rw [hEq]
  ring

theorem step_of_equilibrium_eq_self (region : Config X)
    (hEq : IsEquilibrium region) :
    Level0.StepStructure.step (Level0.StepStructure.step region) =
      Level0.StepStructure.step region := by
  simpa [IsEquilibrium] using congrArg Level0.StepStructure.step hEq

theorem two_step_capacity_nonincrease (region : Config X) :
    Level0.K (Level0.StepStructure.step (Level0.StepStructure.step region)) ≤
      Level0.K region := by
  exact le_trans (Level1.correction_monotone (Level0.StepStructure.step region))
    (Level1.correction_monotone region)

theorem iterate_capacity_nonincrease (n : ℕ) (region : Config X) :
    Level0.K ((Level0.StepStructure.step^[n]) region) ≤ Level0.K region := by
  induction n generalizing region with
  | zero =>
      simp
  | succ n ihn =>
      rw [Function.iterate_succ_apply']
      exact le_trans (Level1.correction_monotone ((Level0.StepStructure.step^[n]) region))
        (ihn region)

theorem iterate_of_equilibrium (n : ℕ) (region : Config X)
    (hEq : IsEquilibrium region) :
    (Level0.StepStructure.step^[n]) region = region := by
  induction n with
  | zero =>
      simp
  | succ n ihn =>
      rw [Function.iterate_succ_apply', ihn]
      exact hEq

/-- The step clock is normalized so one correction step counts as one unit. -/
def normalizedStepRate : ℝ := 1

theorem normalizedStepRate_eq_one : normalizedStepRate = 1 := rfl

end CorrectionDynamics
end Level1
end AST
