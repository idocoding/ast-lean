import AST_levels.Physics.Level3_Interface
import Mathlib

/-!
# AST.Level3.TensorModes

Canonical Level 3 support for the mode-counting statements used by the
inflation phenomenology layer.

This is the right home for the "named physical sector" decomposition:

- one scalar mode
- four gauge-boson modes
- two physical gravitational-wave modes
- three remaining modes

The observational use of these counts belongs in Level 4, but the counting
itself is already a physics-identification statement and therefore belongs here.
-/

namespace AST
namespace Level3
namespace TensorModes

/-- Scalar-sector contribution in the orientation-tensor counting. -/
def scalarModeCount : ℕ := 1

/-- Gauge-sector contribution in the orientation-tensor counting. -/
def gaugeModeCount : ℕ := 4

/-- Physical gravitational-wave contribution in the orientation-tensor counting. -/
def gravitationalWaveModeCount : ℕ := 2

/-- Residual non-scalar, non-gauge, non-gravitational modes in the counting. -/
def residualModeCount : ℕ := 3

/-- Total number of counted orientation-tensor modes used in Paper 1. -/
def totalModeCount : ℕ :=
  scalarModeCount + gaugeModeCount + gravitationalWaveModeCount + residualModeCount

theorem totalModeCount_eq_ten : totalModeCount = 10 := by
  native_decide

/-- The physical tensor fraction used in the Paper-1 tensor-to-scalar estimate. -/
noncomputable def physicalGravitationalWaveFraction : ℝ :=
  (gravitationalWaveModeCount : ℝ) / (totalModeCount : ℝ)

theorem physicalGravitationalWaveFraction_eq :
    physicalGravitationalWaveFraction = (1 : ℝ) / 5 := by
  norm_num [physicalGravitationalWaveFraction, totalModeCount,
    scalarModeCount, gaugeModeCount, gravitationalWaveModeCount, residualModeCount]

theorem physicalGravitationalWaveFraction_pos :
    0 < physicalGravitationalWaveFraction := by
  rw [physicalGravitationalWaveFraction_eq]
  norm_num

end TensorModes
end Level3
end AST
