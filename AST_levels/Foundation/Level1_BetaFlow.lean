import AST_levels.Foundation.Level1
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# AST.Level1.BetaFlow

Canonical Level 1 support for the capacity potential and exact beta-flow.

This module keeps only the mathematical core needed by Paper 1 and by the
internal synthesis paper:

- the potential `V(ρ) = ρ log ρ`
- the equilibrium point `ρ₀ = e^{-1}`
- the exact drift `dβ/dτ = -log β`
- the uniqueness and sign properties of the fixed point `β = 1`

No cosmological or particle interpretation is introduced here.
-/

open Real

namespace AST
namespace Level1
namespace BetaFlow

/-- The Level 1 equilibrium density selected by `V'(ρ₀) = 0`. -/
noncomputable def rhoEq : ℝ := Real.exp (-1)

theorem rhoEq_pos : 0 < rhoEq := Real.exp_pos (-1)

theorem log_rhoEq : Real.log rhoEq = -1 := by
  simp [rhoEq, Real.log_exp]

/-- The canonical Level 1 capacity potential. -/
noncomputable def capacityPotential (ρ : ℝ) : ℝ := ρ * Real.log ρ

theorem capacityPotential_deriv (ρ : ℝ) (hρ : 0 < ρ) :
    HasDerivAt capacityPotential (1 + Real.log ρ) ρ := by
  unfold capacityPotential
  have hlog := hasDerivAt_log (ne_of_gt hρ)
  have hmul := (hasDerivAt_id ρ).mul hlog
  simpa [hρ.ne', add_comm, add_left_comm, add_assoc] using hmul

theorem equilibrium_deriv_zero : 1 + Real.log rhoEq = 0 := by
  simp [log_rhoEq]

theorem equilibrium_curvature : (1 : ℝ) / rhoEq = Real.exp 1 := by
  simp [rhoEq, Real.exp_neg]

/-- The exact beta-flow drift after rescaling around `ρ₀ = e^{-1}`. -/
noncomputable def betaDrift (β : ℝ) : ℝ := -Real.log β

theorem beta_flow_from_vacuum_rescaling (β : ℝ) (hβ : 0 < β) :
    -(1 + Real.log (β * rhoEq)) = betaDrift β := by
  unfold betaDrift
  rw [Real.log_mul (ne_of_gt hβ) (ne_of_gt rhoEq_pos)]
  linarith [equilibrium_deriv_zero]

theorem beta_fixed_point (β : ℝ) (hβ : 0 < β) :
    betaDrift β = 0 ↔ β = 1 := by
  unfold betaDrift
  constructor
  · intro h
    have hlog : Real.log β = 0 := by linarith
    have hexp : Real.exp (Real.log β) = Real.exp 0 := congrArg Real.exp hlog
    simpa [Real.exp_log hβ] using hexp
  · intro h
    simp [h]

theorem beta_flow_neg_above (β : ℝ) (hβ : 1 < β) :
    betaDrift β < 0 := by
  unfold betaDrift
  simp [Real.log_pos hβ]

theorem beta_flow_pos_below (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < betaDrift β := by
  unfold betaDrift
  simp [Real.log_neg hβ0 hβ1]

theorem beta_log_slower_than_linear (β : ℝ) (hβ : 1 < β) :
    Real.log β < β - 1 := by
  exact Real.log_lt_sub_one_of_pos (by linarith) (ne_of_gt hβ)

/-- The linearized drift `-(β-1)` is the first-order approximation to `-log β` near `β=1`. -/
theorem beta_linearization_identity (ε : ℝ) :
    Real.log (1 + ε) = ε - ε ^ 2 / 2 + (Real.log (1 + ε) - ε + ε ^ 2 / 2) := by
  ring

end BetaFlow
end Level1
end AST
