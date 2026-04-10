import AST_levels.Applications.Level4_Interface
import AST_levels.Interpretation.Level2_InflationBridge
import AST_levels.Physics.Level3_TensorModes

/-!
# AST.Level4.Inflation

Canonical Paper-1 support for the inflationary prediction layer of AST.

The mathematical core remains in `AST.Level1.BetaFlow`, and the interpretive
bridge formulas now live in `AST.Level2.InflationSemantics`. This module keeps the
Level 4 numerical calibration and prediction statements that depend on those
bridges.
-/

namespace AST
namespace Level4
namespace Inflation

open Level1.BetaFlow
open Level2.InflationSemantics
open Level3.TensorModes

abbrev InflationBridge := Level2.InflationSemantics.InflationBridge
noncomputable def hubbleSq := Level2.InflationSemantics.hubbleSq
noncomputable def hubble := Level2.InflationSemantics.hubble
noncomputable def eFoldIntegrand := Level2.InflationSemantics.eFoldIntegrand
noncomputable def eFoldCountFrom := Level2.InflationSemantics.eFoldCountFrom
noncomputable def slowRollEpsilonFormula := Level2.InflationSemantics.slowRollEpsilonFormula

/-- Explicit Level 4 bridge for the pivot-scale e-fold matching used in Paper 1. -/
structure PivotScaleBridge where
  endBeta : ℝ
  pivotBeta : ℝ
  pivotEFolds : ℝ
  endBeta_gt_one : 1 < endBeta
  endBeta_lt_pivot : endBeta < pivotBeta
  pivotEFolds_eq_sixty : pivotEFolds = 60
  pivotFromEFoldIntegral : eFoldCountFrom endBeta pivotBeta = pivotEFolds
  pivotBeta_window : 93 < pivotBeta ∧ pivotBeta < 95

/-- Explicit Level 4 bridge for the tensor-to-scalar ratio used in Paper 1. -/
structure TensorRatioBridge where
  slowRollEpsilon : ℝ → ℝ
  tensorToScalarRatio : ℝ → ℝ
  epsilon_at_pivot : ℝ
  epsilonAtPivot_eq : epsilon_at_pivot = 71 / 10000
  epsilonFromFormula :
    ∀ {β : ℝ}, 1 < β → slowRollEpsilon β = slowRollEpsilonFormula β
  ratioFromEpsilon :
    ∀ {β : ℝ},
      tensorToScalarRatio β = 16 * slowRollEpsilon β * physicalGravitationalWaveFraction
  slowRollAtPivot :
    ∀ {pivot : ℝ}, 93 < pivot → pivot < 95 → slowRollEpsilon pivot = epsilon_at_pivot

/-- The inflationary phase corresponds to beta values above the Level 1 fixed point. -/
theorem inflationary_phase_rolls_toward_equilibrium (β : ℝ) (hβ : 1 < β) :
    betaDrift β < 0 :=
  beta_flow_neg_above β hβ

/-- The Level 1 fixed point `β = 1` is the unique candidate endpoint of the flow. -/
theorem inflation_ends_at_beta_one (β : ℝ) (hβ : 0 < β) :
    betaDrift β = 0 ↔ β = 1 :=
  beta_fixed_point β hβ

/-- Under the explicit inflation bridge, the scalar tilt follows the AST formula. -/
theorem spectralIndex_formula (bridge : InflationBridge) {N_e : ℝ} (hN : 0 < N_e) :
    bridge.scalarSpectralIndex N_e = 1 - 2 / N_e :=
  bridge.scalarTiltFromBetaFlow hN

/-- Under the explicit inflation bridge, the running follows the AST formula. -/
theorem spectralRunning_formula (bridge : InflationBridge) {N_e : ℝ} (hN : 0 < N_e) :
    bridge.scalarRunning N_e = -(2 : ℝ) / N_e ^ 2 :=
  bridge.scalarRunningFromBetaFlow hN

/-- The paper's pivot value at `N_e = 60` is exactly `29/30`. -/
theorem spectralIndex_at_sixty (bridge : InflationBridge) :
    bridge.scalarSpectralIndex 60 = (29 : ℝ) / 30 := by
  calc
    bridge.scalarSpectralIndex 60 = 1 - 2 / (60 : ℝ) :=
      spectralIndex_formula bridge (by norm_num)
    _ = (29 : ℝ) / 30 := by norm_num

/-- The AST spectral index at `N_e = 60` lies in the standard quoted Planck-era window. -/
theorem spectralIndex_window_at_sixty (bridge : InflationBridge) :
    let n_s := bridge.scalarSpectralIndex 60
    0.960 < n_s ∧ n_s < 0.970 := by
  dsimp
  have hns : bridge.scalarSpectralIndex 60 = (29 : ℝ) / 30 :=
    spectralIndex_at_sixty bridge
  constructor <;> nlinarith [hns]

/-- The AST prediction sits comfortably within a one-sigma Planck-2018-style band. -/
theorem spectralIndex_within_one_sigma_planck2018 (bridge : InflationBridge) :
    |bridge.scalarSpectralIndex 60 - 0.9649| / 0.0042 < 1 := by
  have hns : bridge.scalarSpectralIndex 60 = (29 : ℝ) / 30 :=
    spectralIndex_at_sixty bridge
  norm_num [hns]

/-- The AST running at `N_e = 60` is exactly `-1/1800`. -/
theorem spectralRunning_at_sixty (bridge : InflationBridge) :
    bridge.scalarRunning 60 = -(1 : ℝ) / 1800 := by
  calc
    bridge.scalarRunning 60 = -(2 : ℝ) / (60 : ℝ) ^ 2 :=
      spectralRunning_formula bridge (by norm_num)
    _ = -(1 : ℝ) / 1800 := by norm_num

/-- The running prediction is numerically close to `-5.6 × 10^{-4}`. -/
theorem spectralRunning_window_at_sixty (bridge : InflationBridge) :
    let αs := bridge.scalarRunning 60
    (-0.00056 < αs) ∧ (αs < -0.00055) := by
  dsimp
  have hα : bridge.scalarRunning 60 = -(1 : ℝ) / 1800 :=
    spectralRunning_at_sixty bridge
  norm_num [hα]

/-- The canonical Paper-1 pivot lies near `β_* = 94`. -/
theorem pivotBeta_near_ninety_four (pivot : PivotScaleBridge) :
    93 < pivot.pivotBeta ∧ pivot.pivotBeta < 95 :=
  pivot.pivotBeta_window

/-- The canonical e-fold relation used to pick the Paper-1 pivot is explicit. -/
theorem pivot_from_efold_integral (pivot : PivotScaleBridge) :
    eFoldCountFrom pivot.endBeta pivot.pivotBeta = pivot.pivotEFolds :=
  pivot.pivotFromEFoldIntegral

/-- The canonical Paper-1 pivot uses `N_e = 60` e-folds. -/
theorem pivotEFolds_eq_sixty (pivot : PivotScaleBridge) :
    pivot.pivotEFolds = 60 :=
  pivot.pivotEFolds_eq_sixty

/-- The regularized e-fold integral uses an explicit end-of-inflation cutoff above `β = 1`. -/
theorem endBeta_gt_one (pivot : PivotScaleBridge) :
    1 < pivot.endBeta :=
  pivot.endBeta_gt_one

theorem endBeta_lt_pivot (pivot : PivotScaleBridge) :
    pivot.endBeta < pivot.pivotBeta :=
  pivot.endBeta_lt_pivot

/-- The pivot scale lies above the equilibrium endpoint because the cutoff does. -/
theorem pivotBeta_gt_one (pivot : PivotScaleBridge) :
    1 < pivot.pivotBeta := by
  linarith [pivot.endBeta_gt_one, pivot.endBeta_lt_pivot]

/-- The regularized canonical e-fold integral is nonnegative at the Paper-1 pivot. -/
theorem pivot_eFoldCountFrom_nonneg (pivot : PivotScaleBridge) :
    0 ≤ eFoldCountFrom pivot.endBeta pivot.pivotBeta :=
  eFoldCountFrom_nonneg (le_of_lt (endBeta_lt_pivot pivot)) (endBeta_gt_one pivot)

/-- The canonical pivot e-fold count is strictly positive. -/
theorem pivotEFolds_pos (pivot : PivotScaleBridge) :
    0 < pivot.pivotEFolds := by
  rw [pivotEFolds_eq_sixty pivot]
  norm_num

/-- The regularized e-fold count at the canonical pivot is strictly positive. -/
theorem pivot_eFoldCountFrom_pos (pivot : PivotScaleBridge) :
    0 < eFoldCountFrom pivot.endBeta pivot.pivotBeta := by
  have hnonneg : 0 ≤ eFoldCountFrom pivot.endBeta pivot.pivotBeta :=
    pivot_eFoldCountFrom_nonneg pivot
  have hEq : eFoldCountFrom pivot.endBeta pivot.pivotBeta = pivot.pivotEFolds :=
    pivot_from_efold_integral pivot
  have hPos : 0 < pivot.pivotEFolds := pivotEFolds_pos pivot
  linarith [hnonneg, hEq, hPos]

/-- Under the explicit slow-roll bridge, the canonical epsilon formula is used above `β = 1`. -/
theorem epsilon_from_formula (tensor : TensorRatioBridge) {β : ℝ} (hβ : 1 < β) :
    tensor.slowRollEpsilon β = slowRollEpsilonFormula β :=
  tensor.epsilonFromFormula hβ

/-- The tensor fraction used in the Paper-1 estimate is the explicit `2/10` bridge. -/
theorem tensorFraction_eq_two_tenths :
    physicalGravitationalWaveFraction = (1 : ℝ) / 5 := by
  exact physicalGravitationalWaveFraction_eq

/-- The slow-roll parameter used in the Paper-1 estimate is the explicit `0.0071` bridge. -/
theorem epsilon_at_pivot_eq (tensor : TensorRatioBridge) :
    tensor.epsilon_at_pivot = 0.0071 := by
  norm_num [tensor.epsilonAtPivot_eq]

/-- Under the explicit tensor bridge, the Paper-1 tensor ratio is `0.02272`. -/
theorem tensorRatio_at_pivot
    (pivot : PivotScaleBridge) (tensor : TensorRatioBridge) :
    tensor.tensorToScalarRatio pivot.pivotBeta = 0.02272 := by
  obtain ⟨hpivot_lo, hpivot_hi⟩ := pivot.pivotBeta_window
  rw [tensor.ratioFromEpsilon, tensor.slowRollAtPivot hpivot_lo hpivot_hi, physicalGravitationalWaveFraction_eq,
    tensor.epsilonAtPivot_eq]
  norm_num

/-- The canonical Paper-1 tensor ratio lies in a narrow window around `0.023`. -/
theorem tensorRatio_window_at_pivot
    (pivot : PivotScaleBridge) (tensor : TensorRatioBridge) :
    let r := tensor.tensorToScalarRatio pivot.pivotBeta
    0.022 < r ∧ r < 0.023 := by
  dsimp
  have hr : tensor.tensorToScalarRatio pivot.pivotBeta = 0.02272 :=
    tensorRatio_at_pivot pivot tensor
  constructor <;> nlinarith [hr]

/-- The canonical Paper-1 tensor ratio is within `3 × 10^{-4}` of `0.023`. -/
theorem tensorRatio_near_point_zero_two_three
    (pivot : PivotScaleBridge) (tensor : TensorRatioBridge) :
    |tensor.tensorToScalarRatio pivot.pivotBeta - 0.023| < 0.0003 := by
  have hr : tensor.tensorToScalarRatio pivot.pivotBeta = 0.02272 :=
    tensorRatio_at_pivot pivot tensor
  norm_num [hr]

end Inflation
end Level4
end AST
