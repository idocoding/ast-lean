import AST_levels.Foundation.Level0

/-!
# AST.Level1

Level 1 is reserved for derivations from the structural core.

This file is deliberately small at first: it imports the canonical Level 0
definitions and establishes a namespaced place for future migration from
`AST_files/AST_Level1_*`.
-/

namespace AST
namespace Level1

open Level0

universe u

variable {X : Type u} [DecidableEq X] [Fintype X]
variable [Level0.SigmaStructure X] [Level0.StepStructure X]

/-- Level 1 canonical principle: structural corrections do not increase the boundary capacity. -/
theorem correction_monotone (region : Finset X) :
    Level0.K (Level0.StepStructure.step region) <= Level0.K region :=
  Level0.K_nonincreasing_under_step region

/-- Upper bound on correction-chain length suggested by the sigma-pair count. -/
noncomputable def N_max : ℕ := Fintype.card X / 2

omit [DecidableEq X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem N_max_le_card :
    N_max (X := X) ≤ Fintype.card X := by
  unfold N_max
  exact Nat.div_le_self _ _

/-- Conservative Level-1 bound currently available from the public tree. -/
theorem correction_iterate_nonincrease (n : ℕ) (region : Finset X) :
    Level0.K ((Level0.StepStructure.step^[n]) region) ≤ Level0.K region := by
  induction n generalizing region with
  | zero =>
      simp
  | succ n ih =>
      simpa [Function.iterate_succ_apply] using
        le_trans (ih (Level0.StepStructure.step region)) (correction_monotone region)

/-- Migration note for the still-open finite-descent termination proof. -/
def correctionTerminationStatus : String :=
  "N_max is now a canonical Level-1 quantity, and iterate nonincrease is proved. The full finite-descent theorem that every chain terminates within N_max steps still requires a sharper strict-drop argument than the current public StepStructure provides."

/-- Migration note for exact flow results that belong at Level 1 rather than in compat files. -/
def exactBetaFlowMigrationTarget : String :=
  "Migrate the remaining exact beta-flow and correction-bound theorems from the historical files into canonical Level 1 as direct proofs rather than placeholders."

end Level1
end AST
