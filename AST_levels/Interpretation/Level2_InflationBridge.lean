import AST_levels.Foundation.Level1_BetaFlow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# AST.Level2.InflationBridge

Canonical Level 2 bridge from the exact beta-flow to cosmological interpretation
formulas. This file stops short of empirical calibration: it records the
interpretive formulas and positivity facts, but leaves numerical pivot choices
and observational comparisons to Level 4.
-/

namespace AST
namespace Level2
namespace InflationSemantics

open Level1.BetaFlow

/-- Explicit Level 2 bridge from the Level 1 beta-flow to inflationary observables. -/
structure InflationBridge where
  scalarSpectralIndex : ℝ → ℝ
  scalarRunning : ℝ → ℝ
  tauAsEFolds : Prop
  hubbleSqTracksDensity : Prop
  horizonCrossingClock : Prop
  scalarTiltFromBetaFlow :
    ∀ {N_e : ℝ}, 0 < N_e → scalarSpectralIndex N_e = 1 - 2 / N_e
  scalarRunningFromBetaFlow :
    ∀ {N_e : ℝ}, 0 < N_e → scalarRunning N_e = -(2 : ℝ) / N_e ^ 2

/-- Canonical Level 2 Hubble-squared scaling used in the AST inflation bridge. -/
noncomputable def hubbleSq (β : ℝ) : ℝ := rhoEq * β / 3

/-- Canonical Level 2 Hubble scale used in the e-fold integral. -/
noncomputable def hubble (β : ℝ) : ℝ := Real.sqrt (hubbleSq β)

/-- Canonical Level 2 e-fold integrand from `H(β)` and the exact beta-flow. -/
noncomputable def eFoldIntegrand (β : ℝ) : ℝ := hubble β / Real.log β

/-- Canonical Level 2 regularized e-fold count from `β_end > 1` to a pivot `β_*`.

The integrand `H(β) / log β` is singular at `β = 1`, so the canonical
mathematical object must keep the end-of-inflation cutoff explicit.
-/
noncomputable def eFoldCountFrom (β_end β_star : ℝ) : ℝ :=
  ∫ x in β_end..β_star, eFoldIntegrand x

/-- Canonical Level 2 slow-roll expression used in the AST inflation bridge. -/
noncomputable def slowRollEpsilonFormula (β : ℝ) : ℝ :=
  Real.sqrt 3 * Real.log β / (2 * Real.sqrt rhoEq * β * Real.sqrt β)

/-- The Hubble scaling is positive throughout the inflationary phase `β > 1`. -/
theorem hubbleSq_pos (β : ℝ) (hβ : 1 < β) :
    0 < hubbleSq β := by
  unfold hubbleSq
  have hβ0 : 0 < β := by linarith
  have hmul : 0 < rhoEq * β := mul_pos rhoEq_pos hβ0
  nlinarith

theorem hubble_pos (β : ℝ) (hβ : 1 < β) :
    0 < hubble β := by
  unfold hubble
  exact Real.sqrt_pos.mpr (hubbleSq_pos β hβ)

/-- The e-fold integrand is positive throughout the inflationary phase `β > 1`. -/
theorem eFoldIntegrand_pos (β : ℝ) (hβ : 1 < β) :
    0 < eFoldIntegrand β := by
  unfold eFoldIntegrand
  have hh : 0 < hubble β := hubble_pos β hβ
  have hlog : 0 < Real.log β := Real.log_pos hβ
  exact div_pos hh hlog

/-- The regularized e-fold count is nonnegative on any interval above `β = 1`. -/
theorem eFoldCountFrom_nonneg {β_end β_star : ℝ}
    (hend : β_end ≤ β_star) (hphase : 1 < β_end) :
    0 ≤ eFoldCountFrom β_end β_star := by
  unfold eFoldCountFrom
  refine intervalIntegral.integral_nonneg hend ?_
  intro u hu
  exact le_of_lt <| eFoldIntegrand_pos u (lt_of_lt_of_le hphase hu.1)

/-- The canonical slow-roll expression is positive throughout the inflationary phase `β > 1`. -/
theorem slowRollEpsilonFormula_pos (β : ℝ) (hβ : 1 < β) :
    0 < slowRollEpsilonFormula β := by
  unfold slowRollEpsilonFormula
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hlog : 0 < Real.log β := Real.log_pos hβ
  have hrho : 0 < Real.sqrt rhoEq := Real.sqrt_pos.mpr rhoEq_pos
  have hβ0 : 0 < β := by linarith
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ0
  positivity

end InflationSemantics
end Level2
end AST
