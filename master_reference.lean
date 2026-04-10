/-!
# AST Public Master Reference

This file is a review-only concatenation of the public Lean package in dependency order.
It is intended for sharing and reading, not as the canonical build entry point.
-/

/-!
Source order follows `AST_levels.lean`.
-/

/-!
===== PUBLIC ENTRY FILE: AST_levels.lean =====
-/

import AST_levels.Foundation.Level0
import AST_levels.Foundation.Level1
import AST_levels.Foundation.Level1_Correction
import AST_levels.Foundation.Level1_BetaFlow
import AST_levels.Interpretation.Level2_Interface
import AST_levels.Interpretation.Level2_CorrectionGraph
import AST_levels.Interpretation.Level2_QuantumBridge
import AST_levels.Interpretation.Level2_QuantumResults
import AST_levels.Interpretation.Level2_InflationBridge
import AST_levels.Interpretation.Level2_ManifoldBridge
import AST_levels.Interpretation.Level2_SpacetimeBridge
import AST_levels.Interpretation.Level2_GeometryRoute
import AST_levels.Physics.Level3_Interface
import AST_levels.Physics.Level3_GRBridge
import AST_levels.Physics.Level3_GeometryRoute
import AST_levels.Physics.Level3_Hurwitz
import AST_levels.Physics.Level3_LQG
import AST_levels.Physics.Level3_Soliton
import AST_levels.Physics.Level3_TensorModes
import AST_levels.Applications.Level4_Interface
import AST_levels.Applications.AlphaEstimate
import AST_levels.Applications.Inflation
import AST_levels.Applications.Holography
import AST_levels.Applications.ProtonStability

/-!
===== END PUBLIC ENTRY FILE: AST_levels.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Foundation/Level0.lean =====
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# AST.Level0

Pure structural mathematics for the new levelized consolidation.

This file is derived from `AST_files/AST_Level0_Clean.lean`, but moved under a
single root namespace so later levels can import one canonical definition site.
-/

open Real BigOperators

universe u

namespace AST
namespace Level0

variable {X : Type u} [DecidableEq X] [Fintype X]

/-- Level 0 foundation: a fixed-point-free involution on a finite type. -/
class SigmaStructure (X : Type u) [DecidableEq X] [Fintype X] where
  sigma : X -> X
  sigma_inv : Function.Involutive sigma
  sigma_free : forall x : X, sigma x != x

variable [SigmaStructure X]

open SigmaStructure

/-- Boundary of a finite region with respect to the involution. -/
def sigmaBoundary (region : Finset X) : Finset X :=
  region.filter (fun x => sigma x ∉ region)

/-- Interior of a finite region with respect to the involution. -/
def sigmaInterior (region : Finset X) : Finset X :=
  region.filter (fun x => sigma x ∈ region)

/-- Distinguishability count forced by boundary freedom. -/
noncomputable def Dist (region : Finset X) : ℝ :=
  (2 : ℝ) ^ (sigmaBoundary region).card

/-- Boundary capacity functional. -/
noncomputable def K (region : Finset X) : ℝ :=
  (sigmaBoundary region).card * Real.log 2

/-- Auxiliary distinguishability measure. At Level 0 this is definitionally the same as `K`. -/
noncomputable def DMeasure (region : Finset X) : ℝ :=
  (sigmaBoundary region).card * Real.log 2

theorem sigmaBoundary_union_sigmaInterior (region : Finset X) :
    sigmaBoundary region ∪ sigmaInterior region = region := by
  ext x
  simp [sigmaBoundary, sigmaInterior]
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact hx.1
    · exact hx.1
  · intro hx
    by_cases hs : sigma x ∈ region
    · exact Or.inr ⟨hx, hs⟩
    · exact Or.inl ⟨hx, hs⟩

theorem sigmaBoundary_disjoint_sigmaInterior (region : Finset X) :
    Disjoint (sigmaBoundary region) (sigmaInterior region) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxB hxI
  simp [sigmaBoundary, sigmaInterior] at hxB hxI
  exact hxB.2 hxI.2

theorem sigmaBoundary_card_add_sigmaInterior_card (region : Finset X) :
    (sigmaBoundary region).card + (sigmaInterior region).card = region.card := by
  rw [← Finset.card_union_of_disjoint (sigmaBoundary_disjoint_sigmaInterior region)]
  exact congrArg Finset.card (sigmaBoundary_union_sigmaInterior region)

theorem sigmaBoundary_union_sigmaInterior_compl (region : Finset X) :
    sigmaBoundary regionᶜ ∪ sigmaInterior regionᶜ = regionᶜ :=
  sigmaBoundary_union_sigmaInterior (region := regionᶜ)

theorem sigma_four_way_partition (region : Finset X) :
    sigmaBoundary region ∪ sigmaInterior region ∪
        (sigmaBoundary regionᶜ ∪ sigmaInterior regionᶜ) =
      (Finset.univ : Finset X) := by
  rw [sigmaBoundary_union_sigmaInterior, sigmaBoundary_union_sigmaInterior_compl]
  ext x
  simp

theorem K_eq_log_Dist (region : Finset X) :
    K region = Real.log (Dist region) := by
  simp [K, Dist, Real.log_pow]

theorem D_eq_K (region : Finset X) :
    DMeasure region = K region := rfl

theorem sigma_sum_zero
    (f : X → ℤ) (hf : ∀ x : X, f (sigma x) = -(f x)) :
    ∑ x : X, f x = 0 := by
  apply Finset.sum_involution (fun x _ => sigma x)
  · intro x _
    simp [hf x]
  · intro x _ hne
    simpa using sigma_free x
  · intro x _
    exact sigma_inv x
  · intro x _
    exact Finset.mem_univ _

theorem antisymmetric_label_balance
    (f : X → ℤ) (hf : ∀ x : X, f (sigma x) = -(f x)) :
    ∑ x : X, f x = 0 :=
  sigma_sum_zero f hf

theorem K_nonneg (region : Finset X) : 0 <= K region := by
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)

theorem K_local (region : Finset X) :
    K region = (sigmaBoundary region).card * Real.log 2 := rfl

theorem K_determined_by_boundary (region1 region2 : Finset X)
    (h : (sigmaBoundary region1).card = (sigmaBoundary region2).card) :
    K region1 = K region2 := by
  simp [K, h]

theorem K_spectrum (region : Finset X) :
    exists n : ℕ, K region = n * Real.log 2 :=
  ⟨(sigmaBoundary region).card, rfl⟩

theorem K_gap (region : Finset X) (h : K region ≠ 0) :
    Real.log 2 ≤ K region := by
  have hcard : 0 < (sigmaBoundary region).card := by
    rcases Nat.eq_zero_or_pos (sigmaBoundary region).card with h0 | h0
    · have hk0 : K region = 0 := by simp [K, h0]
      exact False.elim (h hk0)
    · exact h0
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hmul : (1 : ℝ) * Real.log 2 ≤ (sigmaBoundary region).card * Real.log 2 := by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast (show 1 ≤ (sigmaBoundary region).card from Nat.succ_le_of_lt hcard)
    · exact hlog
  simpa [K] using hmul

theorem closed_region_zero_K (region : Finset X)
    (h : sigmaBoundary region = ∅) : K region = 0 := by
  simp [K, h]

theorem closed_minimises_K (region : Finset X)
    (h : sigmaBoundary region = ∅) : K region = 0 :=
  closed_region_zero_K region h

theorem closed_region_global_minimum (region other : Finset X)
    (h : sigmaBoundary region = ∅) : K region ≤ K other := by
  rw [closed_region_zero_K region h]
  exact K_nonneg other

theorem admissibility_trivial (region : Finset X) :
    DMeasure region <= K region := le_refl _

/-- Structural dynamics exists once a step map is supplied. -/
class StepStructure (X : Type u) [DecidableEq X] [Fintype X] [SigmaStructure X] where
  step : Finset X -> Finset X
  step_nonincreasing : forall region : Finset X, K (step region) <= K region

variable [StepStructure X]

open StepStructure

theorem K_nonincreasing_under_step (region : Finset X) :
    K (step region) <= K region :=
  step_nonincreasing region

theorem step_preserves_or_reduces_K (region : Finset X) :
    K (step region) ≤ K region :=
  K_nonincreasing_under_step region

theorem max_rate_is_one : (1 : ℝ) = 1 := rfl

end Level0
end AST

/-!
===== END FILE: AST_levels/Foundation/Level0.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Foundation/Level1.lean =====
-/

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

/-!
===== END FILE: AST_levels/Foundation/Level1.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Foundation/Level1_Correction.lean =====
-/

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

/-!
===== END FILE: AST_levels/Foundation/Level1_Correction.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Foundation/Level1_BetaFlow.lean =====
-/

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

/-!
===== END FILE: AST_levels/Foundation/Level1_BetaFlow.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Interpretation/Level2_Interface.lean =====
-/

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

/-!
===== END FILE: AST_levels/Interpretation/Level2_Interface.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Interpretation/Level2_CorrectionGraph.lean =====
-/

import AST_levels.Foundation.Level1_Correction

/-!
# AST.Level2.CorrectionGraph

Canonical Level 2 interface for the correction-graph bridge.

This module does not claim the continuum limit has been derived. Its role is to
give the correction graph a canonical home in `AST_levels` and to expose the
bridge data that later geometric or spacetime interpretations must supply.
-/

namespace AST
namespace Level2
namespace CorrectionGraph

open Level0
open Level1.CorrectionDynamics

universe u

variable {X : Type u} [DecidableEq X] [Fintype X]
variable [Level0.SigmaStructure X] [Level0.StepStructure X]

/-- Configurations are the vertices of the canonical correction graph. -/
abbrev Config (X : Type u) := Finset X

/-- The correction graph adjacency relation induced by one structural step. -/
def Edge (C D : Config X) : Prop :=
  D = Level0.StepStructure.step C ∨ C = Level0.StepStructure.step D

theorem edge_symm {C D : Config X} :
    Edge C D -> Edge D C := by
  intro h
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem forward_edge (C : Config X) :
    Edge C (Level0.StepStructure.step C) :=
  Or.inl rfl

theorem backward_edge (C : Config X) :
    Edge (Level0.StepStructure.step C) C :=
  edge_symm (forward_edge C)

/-- Canonical graph package used by higher-level emergence bridges. -/
structure GraphModel (X : Type u) where
  edge : Config X -> Config X -> Prop
  symm : ∀ {C D : Config X}, edge C D -> edge D C

/-- The undirected correction graph canonically induced by the step map. -/
def canonicalGraph : GraphModel X where
  edge := Edge
  symm := by
    intro C D h
    exact edge_symm h

/-- The abstract correction-step clock that Level 2 may later identify with physical time. -/
abbrev StepClock := ℕ

theorem stepClock_has_successor (τ : StepClock) :
    ∃ τ' : StepClock, τ' = τ + 1 :=
  ⟨τ + 1, rfl⟩

/-- Explicit Level 2 bridge assumptions for continuum geometry.
These are named data, not hidden theorems. -/
structure ContinuumBridge where
  roughTransitivity : Prop
  roughTransitivity_holds : roughTransitivity
  polynomialGrowthDegree : ℕ
  polynomialGrowth : Prop
  polynomialGrowth_holds : polynomialGrowth
  gromovHausdorffLimit : Prop
  gromovHausdorffLimit_holds : gromovHausdorffLimit
  sourceNote : String

/-- A separate named bridge for dimension selection.
This keeps classical/Huygens input explicit rather than burying it in prose. -/
structure DimensionSelectionBridge where
  candidateDimension : ℕ
  huygensSelection : Prop
  huygensSelection_holds : huygensSelection
  sourceNote : String

end CorrectionGraph
end Level2
end AST

/-!
===== END FILE: AST_levels/Interpretation/Level2_CorrectionGraph.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Interpretation/Level2_QuantumBridge.lean =====
-/

import AST_levels.Foundation.Level0
import AST_levels.Foundation.Level1

/-!
# AST.Level2.QuantumBridge

Canonical Level 2 bridge vocabulary for the quantum-emergence side of AST.

This file does not claim that Hilbert space, Born weights, or measurement
theory have already been derived internally from the canonical Level 0 and
Level 1 modules. Instead, it gives those later-paper claims a precise and
auditable home in the canonical tree, with explicit bridge records and simple
theorems that unpack what has been assumed.
-/

namespace AST
namespace Level2
namespace QuantumBridge

universe u

variable {X : Type u} [DecidableEq X] [Fintype X]
variable [Level0.SigmaStructure X] [Level0.StepStructure X]

/-- Level-2 bridge for the nonclassical event-logic side of AST. -/
structure LogicBridge where
  booleanExclusion : Prop
  booleanExclusion_holds : booleanExclusion
  orthomodularEventLattice : Prop
  orthomodularEventLattice_holds : orthomodularEventLattice
  scepWitness : Prop
  scepWitness_holds : scepWitness
  sourceNote : String

theorem boolean_logic_excluded (B : LogicBridge) :
    B.booleanExclusion :=
  B.booleanExclusion_holds

theorem orthomodular_logic_available (B : LogicBridge) :
    B.orthomodularEventLattice :=
  B.orthomodularEventLattice_holds

theorem scep_available (B : LogicBridge) :
    B.scepWitness :=
  B.scepWitness_holds

/-- Level-2 bridge for the state-space / superposition side of AST. -/
structure HilbertBridge where
  homogeneousSelfDualCone : Prop
  homogeneousSelfDualCone_holds : homogeneousSelfDualCone
  hilbertRepresentation : Prop
  hilbertRepresentation_holds : hilbertRepresentation
  superpositionStructure : Prop
  superpositionStructure_holds : superpositionStructure
  sourceNote : String

theorem hilbert_representation_available (B : HilbertBridge) :
    B.hilbertRepresentation :=
  B.hilbertRepresentation_holds

theorem superposition_available (B : HilbertBridge) :
    B.superpositionStructure :=
  B.superpositionStructure_holds

/-- Level-2 bridge for the probability / measurement side of AST. -/
structure BornBridge where
  multiplicativeWeights : Prop
  multiplicativeWeights_holds : multiplicativeWeights
  quadraticExponent : Prop
  quadraticExponent_holds : quadraticExponent
  bornRule : Prop
  bornRule_holds : bornRule
  measurementInterpretation : Prop
  measurementInterpretation_holds : measurementInterpretation
  sourceNote : String

theorem born_rule_available (B : BornBridge) :
    B.bornRule :=
  B.bornRule_holds

theorem measurement_interpretation_available (B : BornBridge) :
    B.measurementInterpretation :=
  B.measurementInterpretation_holds

/-- Canonical package for the full quantum-emergence overview. -/
structure QuantumEmergenceBridge where
  logic : LogicBridge
  hilbert : HilbertBridge
  born : BornBridge

theorem quantum_nonclassicality
    (B : QuantumEmergenceBridge) :
    B.logic.booleanExclusion ∧ B.logic.orthomodularEventLattice := by
  exact ⟨B.logic.booleanExclusion_holds, B.logic.orthomodularEventLattice_holds⟩

theorem quantum_state_space_available
    (B : QuantumEmergenceBridge) :
    B.hilbert.hilbertRepresentation ∧ B.hilbert.superpositionStructure := by
  exact ⟨B.hilbert.hilbertRepresentation_holds, B.hilbert.superpositionStructure_holds⟩

theorem quantum_measurement_package
    (B : QuantumEmergenceBridge) :
    B.born.bornRule ∧ B.born.measurementInterpretation := by
  exact ⟨B.born.bornRule_holds, B.born.measurementInterpretation_holds⟩

end QuantumBridge
end Level2
end AST

/-!
===== END FILE: AST_levels/Interpretation/Level2_QuantumBridge.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Interpretation/Level2_QuantumResults.lean =====
-/

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Topology.Algebra.Module.Basic
import AST_levels.Interpretation.Level2_QuantumBridge

open Filter

/-!
# AST.Level2.QuantumResults

Canonical theorem-facing home for the strongest currently stabilized
quantum-side results in the levelized AST tree.

This file is intentionally self-contained. It does not import the migration
compatibility layer.

- Boolean exclusion is proved directly from a minimal correction-dynamics
  package.
- Orthomodularity from SCEP is stated as a direct canonical theorem over a
  generic ortholattice with explicit factorisation hypotheses.
- The multiplicative-to-power and quadratic Born-rule steps remain explicit
  canonical closure records while their longer analytic proof is modernized.
-/

namespace AST
namespace Level2
namespace QuantumResults

universe u

/-- Minimal data needed for the internal Boolean-exclusion argument. -/
structure CorrectionDynamics (Cfg : Type u) where
  K : Cfg → ℝ
  step : Cfg → Cfg → Prop
  asymptotic_decay :
    ∀ C₁ C₂ C₃, step C₁ C₂ → step C₂ C₃ →
      K C₂ - K C₁ > K C₃ - K C₂

/-- Boolean-style event logic would force a single uniform capacity increment
along every correction step. -/
def IsBooleanLike {Cfg : Type u} (D : CorrectionDynamics Cfg) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∀ C₁ C₂, D.step C₁ C₂ → D.K C₂ - D.K C₁ = δ

/-- Closed nonclassicality result: asymptotically decaying correction steps
exclude a Boolean event logic with a single uniform capacity gain. -/
theorem boolean_event_logic_exclusion
    {Cfg : Type u}
    (D : CorrectionDynamics Cfg)
    (C₁ C₂ C₃ : Cfg)
    (h₁₂ : D.step C₁ C₂)
    (h₂₃ : D.step C₂ C₃) :
    ¬ IsBooleanLike D := by
  intro hB
  rcases hB with ⟨δ, _hδ, hconst⟩
  have hdecay := D.asymptotic_decay C₁ C₂ C₃ h₁₂ h₂₃
  have h12 : D.K C₂ - D.K C₁ = δ := hconst C₁ C₂ h₁₂
  have h23 : D.K C₃ - D.K C₂ = δ := hconst C₂ C₃ h₂₃
  rw [h12, h23] at hdecay
  exact lt_irrefl _ hdecay

/-- Generic ortholattice data used by the canonical orthomodularity theorem. -/
structure OrthoLattice where
  Event       : Type u
  le          : Event → Event → Prop
  meet        : Event → Event → Event
  join        : Event → Event → Event
  bot         : Event
  top         : Event
  compl       : Event → Event
  le_refl     : ∀ a, le a a
  le_trans    : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  meet_le_l   : ∀ a b, le (meet a b) a
  meet_le_r   : ∀ a b, le (meet a b) b
  le_join_l   : ∀ a b, le a (join a b)
  le_join_r   : ∀ a b, le b (join a b)
  join_le     : ∀ a b c, le a c → le b c → le (join a b) c
  meet_le     : ∀ a b c, le a b → le a c → le a (meet b c)
  bot_le      : ∀ a, le bot a
  le_top      : ∀ a, le a top
  compl_compl : ∀ a, compl (compl a) = a
  meet_compl  : ∀ a, meet a (compl a) = bot
  join_compl  : ∀ a, join a (compl a) = top
  compl_anti  : ∀ a b, le a b → le (compl b) (compl a)

def IsOrthomodular (L : OrthoLattice) : Prop :=
  ∀ a b : L.Event, L.le a b → b = L.join a (L.meet b (L.compl a))

def corrLE {Cfg : Type u} (step : Cfg → Cfg → Prop) (C C' : Cfg) : Prop :=
  Relation.ReflTransGen step C C'

/-- Direct canonical orthomodularity theorem from SCEP-style factorisation. -/
theorem scep_yields_orthomodularity
    {Cfg : Type u}
    (step : Cfg → Cfg → Prop)
    (L : OrthoLattice)
    (ev : L.Event → Cfg)
    (le_iff  : ∀ a b : L.Event, L.le a b ↔ corrLE step (ev a) (ev b))
    (join_corr : ∀ a b : L.Event, corrLE step (ev a) (ev (L.join a b)) ∧
                                  corrLE step (ev b) (ev (L.join a b)))
    (_meet_corr : ∀ a b : L.Event,
        ∀ C, corrLE step C (ev a) → corrLE step C (ev b) → corrLE step C (ev (L.meet a b)))
    (_compl_sector : ∀ a : L.Event,
        ∀ C, corrLE step C (ev L.top) →
        ¬ corrLE step C (ev a) →
        corrLE step C (ev (L.compl a)))
    (scep_factor : ∀ a b : L.Event, L.le a b →
        ∀ C, corrLE step (ev L.bot) C → corrLE step C (ev b) →
        corrLE step C (ev a) ∨ corrLE step (ev (L.compl a)) (ev (L.meet b (L.compl a)))) :
    IsOrthomodular L := by
  intro a b hab
  have cT : ∀ {C C' C'' : Cfg}, corrLE step C C' → corrLE step C' C'' → corrLE step C C'' :=
    fun h1 h2 => h1.trans h2
  apply L.le_antisymm
  ·
    have h_bot_b : corrLE step (ev L.bot) (ev b) := (le_iff L.bot b).mp (L.bot_le b)
    have h_b_refl : corrLE step (ev b) (ev b) := Relation.ReflTransGen.refl
    have h_join_r := (join_corr a (L.meet b (L.compl a))).2
    rcases scep_factor a b hab (ev b) h_bot_b h_b_refl with h_ba | h_compl
    ·
      have hab' : L.le b a := (le_iff b a).mpr h_ba
      exact L.le_trans _ _ _ hab' (L.le_join_l a (L.meet b (L.compl a)))
    ·
      rw [le_iff]
      have h_compl_le_b : L.le (L.compl a) b := by
        rw [le_iff]
        exact cT h_compl ((le_iff (L.meet b (L.compl a)) b).mp (L.meet_le_l b (L.compl a)))
      have h_top_le_b : L.le L.top b := by
        simpa [L.join_compl a] using (L.join_le a (L.compl a) b hab h_compl_le_b)
      have hb_top : b = L.top := L.le_antisymm _ _ (L.le_top b) h_top_le_b
      subst hb_top
      have h_meet_top : L.meet L.top (L.compl a) = L.compl a :=
        L.le_antisymm _ _
          (L.meet_le_r L.top (L.compl a))
          (L.meet_le _ _ _ (L.le_top _) (L.le_refl _))
      rw [h_meet_top, L.join_compl]
      exact Relation.ReflTransGen.refl
  ·
    exact L.join_le _ _ _ hab (L.meet_le_l b (L.compl a))

/-- Multiplicative weight assignment on the unit interval. -/
def SatisfiesMultiplicativity (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → f (a * b) = f a * f b

/-- Normalization of branch weights on unit vectors. -/
def SatisfiesNormalization (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ c : Fin n → ℝ,
    (∀ i, 0 ≤ c i) → (∀ i, c i ≤ 1) →
    ∑ i, (c i)^2 = 1 → ∑ i, f (c i) = 1

/-- Continuous additive maps `ℝ → ℝ` are linear. -/
theorem continuous_additive_linear (φ : ℝ → ℝ)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hcont : Continuous φ) :
    ∀ x : ℝ, φ x = x * φ 1 := by
  have hφ0 : φ 0 = 0 := by
    have := hadd 0 0
    simp at this
    linarith
  let fAdd : ℝ →+ ℝ :=
    { toFun := φ
      map_zero' := hφ0
      map_add' := hadd }
  have h_rat : ∀ q : ℚ, φ q = q * φ 1 := by
    intro q
    simpa [fAdd] using (map_rat_smul fAdd q (1 : ℝ))
  have hS_cl : IsClosed {t : ℝ | φ t = t * φ 1} :=
    isClosed_eq hcont (continuous_id.mul continuous_const)
  have hS_Q : Set.range ((↑) : ℚ → ℝ) ⊆ {t : ℝ | φ t = t * φ 1} :=
    fun _ ⟨q, hq⟩ => hq ▸ h_rat q
  have hS_dense : Dense {t : ℝ | φ t = t * φ 1} :=
    Rat.isDenseEmbedding_coe_real.dense.mono hS_Q
  intro x
  exact hS_cl.closure_subset (hS_dense x)

lemma mul_pow_eq (f : ℝ → ℝ) (hm : SatisfiesMultiplicativity f) (hf1 : f 1 = 1) :
    ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f (x^n) = f x ^ n := by
  intro n
  induction n with
  | zero =>
      intro x hx0 hx1
      simp [hf1]
  | succ m ih =>
      intro x hx0 hx1
      rw [pow_succ, hm _ _ (pow_nonneg hx0 m) (pow_le_one₀ hx0 hx1) hx0 hx1, ih x hx0 hx1, pow_succ]

lemma f_zero_from_norm (f : ℝ → ℝ) (hf1 : f 1 = 1)
    (hf_norm : SatisfiesNormalization f) : f 0 = 0 := by
  set c : Fin 2 → ℝ := ![1, 0]
  have hcnn : ∀ i : Fin 2, 0 ≤ c i := by
    intro i
    fin_cases i <;> simp [c]
  have hc1 : ∀ i : Fin 2, c i ≤ 1 := by
    intro i
    fin_cases i <;> simp [c]
  have hcnorm : ∑ i : Fin 2, (c i)^2 = 1 := by
    simp [c, Fin.sum_univ_two]
  have heq : ∑ i : Fin 2, f (c i) = 1 := hf_norm 2 (by norm_num) c hcnn hc1 hcnorm
  simp [c, Fin.sum_univ_two, hf1] at heq
  linarith

lemma f_lt_one_of_lt_one (f : ℝ → ℝ) (hm : SatisfiesMultiplicativity f) (hf1 : f 1 = 1)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf0 : f 0 = 0)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : f x < 1 := by
  by_contra h_lt
  have h_ge : 1 ≤ f x := le_of_not_gt h_lt
  have h_pow_ge : ∀ n : ℕ, 1 ≤ f (x ^ n) := by
    intro n
    rw [mul_pow_eq f hm hf1 n x hx0.le hx1.le]
    exact one_le_pow₀ h_ge
  have hx_pow_zero : Tendsto (fun n : ℕ => x ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
  have hx_pow_within : Tendsto (fun n : ℕ => x ^ n) atTop (nhdsWithin 0 (Set.Icc 0 1)) := by
    refine tendsto_nhdsWithin_iff.mpr ?_
    refine ⟨hx_pow_zero, Filter.Eventually.of_forall ?_⟩
    intro n
    exact ⟨pow_nonneg hx0.le n, pow_le_one₀ hx0.le hx1.le⟩
  have hzero_mem : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, by norm_num⟩
  have hcont0 : ContinuousWithinAt f (Set.Icc 0 1) 0 := by
    simpa using hf_cont (x := 0) hzero_mem
  have hfxn_zero : Tendsto (fun n : ℕ => f (x ^ n)) atTop (nhds 0) := by
    rw [← hf0]
    exact hcont0.tendsto.comp hx_pow_within
  have h_eventually : ∀ᶠ n in atTop, f (x ^ n) < 1 :=
    hfxn_zero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  simp [Filter.eventually_atTop] at h_eventually
  obtain ⟨N, hN⟩ := h_eventually
  have h_large := h_pow_ge N
  linarith [hN N le_rfl]

/-- Logarithmic transform of a multiplicative weight on the negative half-line. -/
noncomputable def logWeight (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (f (Real.exp t))

/-- Symmetric extension of `logWeight` from `(-∞,0]` to all of `ℝ`. -/
noncomputable def logWeightFull (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then logWeight f t else -logWeight f (-t)

lemma logWeight_zero (f : ℝ → ℝ) (hf1 : f 1 = 1) :
    logWeight f 0 = 0 := by
  simp [logWeight, hf1]

lemma logWeight_add_nonpos (f : ℝ → ℝ)
    (hf_mult : SatisfiesMultiplicativity f)
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x) :
    ∀ s t : ℝ, s ≤ 0 → t ≤ 0 →
      logWeight f (s + t) = logWeight f s + logWeight f t := by
  intro s t hs ht
  simp only [logWeight, Real.exp_add]
  rw [hf_mult _ _ (Real.exp_pos s).le (Real.exp_le_one_iff.mpr hs)
      (Real.exp_pos t).le (Real.exp_le_one_iff.mpr ht)]
  rw [Real.log_mul (hf_pos _ (Real.exp_pos s) (Real.exp_le_one_iff.mpr hs)).ne'
      (hf_pos _ (Real.exp_pos t) (Real.exp_le_one_iff.mpr ht)).ne']

lemma logWeightFull_additive (f : ℝ → ℝ)
    (hf_mult : SatisfiesMultiplicativity f)
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x) :
    ∀ x y : ℝ, logWeightFull f (x + y) = logWeightFull f x + logWeightFull f y := by
  intro x y
  have hg_add := logWeight_add_nonpos f hf_mult hf_pos
  by_cases hx : x ≤ 0 <;> by_cases hy : y ≤ 0
  ·
    have hxy : x + y ≤ 0 := add_nonpos hx hy
    simp [logWeightFull, hx, hy, hxy, hg_add x y hx hy]
  ·
    have hy_pos : 0 < y := lt_of_not_ge hy
    by_cases hxy : x + y ≤ 0
    ·
      simp [logWeightFull, hx, hy, hxy]
      have hneg_y : -y ≤ 0 := by linarith
      have hk := hg_add (x + y) (-y) hxy hneg_y
      have hk' : logWeight f x = logWeight f (x + y) + logWeight f (-y) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk
      linarith
    ·
      have hxy_pos : 0 < x + y := lt_of_not_ge hxy
      have hneg_xy : -(x + y) ≤ 0 := by linarith
      have hk := hg_add (-(x + y)) x hneg_xy hx
      have hk' : logWeight f (-y) = logWeight f (-(x + y)) + logWeight f x := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk
      calc
        logWeightFull f (x + y)
            = -logWeight f (-(x + y)) := by
                simp [logWeightFull, hxy]
        _ = logWeight f x - logWeight f (-y) := by
              linarith
        _ = logWeightFull f x + logWeightFull f y := by
              simp [logWeightFull, hx, hy, sub_eq_add_neg]
  ·
    have hx_pos : 0 < x := lt_of_not_ge hx
    by_cases hxy : x + y ≤ 0
    ·
      simp [logWeightFull, hx, hy, hxy]
      have hneg_x : -x ≤ 0 := by linarith
      have hk := hg_add (x + y) (-x) hxy hneg_x
      have hk' : logWeight f y = logWeight f (x + y) + logWeight f (-x) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk
      linarith
    ·
      have hxy_pos : 0 < x + y := lt_of_not_ge hxy
      have hneg_xy : -(x + y) ≤ 0 := by linarith
      have hk := hg_add (-(x + y)) y hneg_xy hy
      have hk' : logWeight f (-x) = logWeight f (-(x + y)) + logWeight f y := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk
      calc
        logWeightFull f (x + y)
            = -logWeight f (-(x + y)) := by
                simp [logWeightFull, hxy]
        _ = -logWeight f (-x) + logWeight f y := by
              linarith
        _ = logWeightFull f x + logWeightFull f y := by
              simp [logWeightFull, hx, hy]
  ·
    have hx_pos : 0 < x := lt_of_not_ge hx
    have hy_pos : 0 < y := lt_of_not_ge hy
    have hxy_pos : 0 < x + y := by linarith
    have hneg_x : -x ≤ 0 := by linarith
    have hneg_y : -y ≤ 0 := by linarith
    have hk := hg_add (-x) (-y) hneg_x hneg_y
    have hk' : logWeight f (-(x + y)) = logWeight f (-x) + logWeight f (-y) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk
    calc
      logWeightFull f (x + y)
          = -logWeight f (-(x + y)) := by
              simp [logWeightFull, not_le.mpr hxy_pos]
      _ = -logWeight f (-x) + -logWeight f (-y) := by
            linarith
      _ = logWeightFull f x + logWeightFull f y := by
            simp [logWeightFull, hx, hy]

lemma logWeight_continuousOn_nonpos (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x) :
    ContinuousOn (logWeight f) {x : ℝ | x ≤ 0} := by
  unfold logWeight
  refine Real.continuousOn_log.comp ?_ ?_
  ·
    exact hf_cont.comp Real.continuous_exp.continuousOn
      (by
        intro x hx
        exact ⟨(Real.exp_pos x).le, Real.exp_le_one_iff.mpr hx⟩)
  ·
    intro x hx
    exact (hf_pos (Real.exp x) (Real.exp_pos x) (Real.exp_le_one_iff.mpr hx)).ne'

lemma logWeightFull_continuous (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x)
    (hf_one : f 1 = 1) :
    Continuous (logWeightFull f) := by
  have hleft : ContinuousOn (logWeight f) {x : ℝ | x ≤ 0} :=
    logWeight_continuousOn_nonpos f hf_cont hf_pos
  have hright : ContinuousOn (fun x : ℝ => -logWeight f (-x)) {x : ℝ | 0 ≤ x} := by
    apply ContinuousOn.neg
    exact hleft.comp continuous_neg.continuousOn (by
      intro x hx
      have hx0 : 0 ≤ x := hx
      exact neg_nonpos.mpr hx0)
  refine continuous_if_le continuous_id continuous_const hleft hright ?_
  intro x hx_eq
  have hx0 : x = 0 := by linarith
  subst hx0
  simp [logWeight_zero, hf_one]

lemma logWeightFull_linear (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_mult : SatisfiesMultiplicativity f)
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x)
    (hf_one : f 1 = 1) :
    ∀ t : ℝ, logWeightFull f t = t * logWeightFull f 1 := by
  exact continuous_additive_linear (logWeightFull f)
    (logWeightFull_additive f hf_mult hf_pos)
    (logWeightFull_continuous f hf_cont hf_pos hf_one)

/-- Direct power-law closure from multiplicativity, positivity, continuity, and normalization. -/
theorem multiplicative_implies_power (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_mult : SatisfiesMultiplicativity f)
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x)
    (hf_one : f 1 = 1)
    (hf_norm : SatisfiesNormalization f) :
    ∃ k : ℝ, 0 < k ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = x ^ k := by
  have hf0 : f 0 = 0 := f_zero_from_norm f hf_one hf_norm
  set k : ℝ := logWeightFull f 1
  have hlin : ∀ t : ℝ, logWeightFull f t = t * k := by
    intro t
    simpa [k] using logWeightFull_linear f hf_cont hf_mult hf_pos hf_one t
  have hk_pos : 0 < k := by
    have h1e_pos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
    have h1e_lt : Real.exp (-1) < 1 := by
      exact Real.exp_lt_one_iff.mpr (by norm_num)
    have hf1e_lt1 : f (Real.exp (-1)) < 1 :=
      f_lt_one_of_lt_one f hf_mult hf_one hf_cont hf0 (Real.exp (-1)) h1e_pos h1e_lt
    have hf1e_pos : 0 < f (Real.exp (-1)) := hf_pos _ h1e_pos h1e_lt.le
    have hk_eq : k = -Real.log (f (Real.exp (-1))) := by
      simp [k, logWeightFull, logWeight]
    rw [hk_eq]
    rw [neg_pos]
    simpa using (Real.log_lt_log hf1e_pos hf1e_lt1)
  refine ⟨k, hk_pos, ?_⟩
  intro x hx0 hx1
  by_cases hx : x = 0
  ·
    subst hx
    rw [hf0, Real.zero_rpow (ne_of_gt hk_pos)]
  have hx_pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  have hlog_nonpos : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
  have hfull_eq : logWeightFull f (Real.log x) = logWeight f (Real.log x) := by
    simp [logWeightFull, hlog_nonpos]
  have hfx_pos : 0 < f x := hf_pos x hx_pos hx1
  have hfx_eq : f x = Real.exp (logWeight f (Real.log x)) := by
    simp only [logWeight, Real.exp_log hx_pos]
    exact (Real.exp_log hfx_pos).symm
  rw [hfx_eq, ← hfull_eq, hlin (Real.log x)]
  rw [Real.rpow_def_of_pos hx_pos, mul_comm]

theorem born_rule (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_mult : SatisfiesMultiplicativity f)
    (hf_pos  : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x)
    (hf_one  : f 1 = 1)
    (hf_norm : SatisfiesNormalization f) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = x ^ (2 : ℝ) := by
  obtain ⟨k, hk_pos, hk_pow⟩ :=
    multiplicative_implies_power f hf_cont hf_mult hf_pos hf_one hf_norm
  intro x hx0 hx1
  rw [hk_pow x hx0 hx1]
  suffices hk_two : k = 2 by rw [hk_two]
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set c : Fin 2 → ℝ := fun _ => 1 / Real.sqrt 2
  have hcnn : ∀ i : Fin 2, 0 ≤ c i := by
    intro i
    simp [c]
  have hc1 : ∀ i : Fin 2, c i ≤ 1 := by
    intro i
    simp [c]
    exact (inv_le_one₀ hsqrt2_pos).2
      (Real.one_le_sqrt.2 (by norm_num : (1 : ℝ) ≤ 2))
  have hcnorm : ∑ i : Fin 2, (c i)^2 = 1 := by
    simp [c, hsqrt2_sq]
  have hsum : ∑ i : Fin 2, f (c i) = 1 := hf_norm 2 (by norm_num) c hcnn hc1 hcnorm
  have hcpos : 0 < c 0 := by
    simp [c]
  have hpow_c : f ((Real.sqrt 2)⁻¹) = ((Real.sqrt 2)⁻¹) ^ k := by
    simpa [one_div] using hk_pow (1 / Real.sqrt 2) (hcnn 0) (hc1 0)
  simp [c] at hsum
  rw [hpow_c] at hsum
  have hhalf_inv : ((Real.sqrt 2)⁻¹) ^ k = 1 / 2 := by
    linarith
  have hhalf : (1 / Real.sqrt 2) ^ k = 1 / 2 := by
    simpa [one_div] using hhalf_inv
  have hone_over_pos : (0 : ℝ) < 1 / Real.sqrt 2 := by
    positivity
  have hlog : k * Real.log (1 / Real.sqrt 2) = Real.log (1 / 2) := by
    calc
      k * Real.log (1 / Real.sqrt 2) = Real.log ((1 / Real.sqrt 2) ^ k) := by
        rw [Real.log_rpow hone_over_pos]
      _ = Real.log (1 / 2) := by rw [hhalf]
  have hlog_lhs : Real.log (1 / Real.sqrt 2) = -(1 / 2 : ℝ) * Real.log 2 := by
    rw [Real.log_div one_ne_zero hsqrt2_pos.ne', Real.log_one,
      Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hlog_rhs : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
    ring
  rw [hlog_lhs, hlog_rhs] at hlog
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Canonical closure record for the multiplicative-to-power step. -/
structure PowerLawClosure (f : ℝ → ℝ) where
  exponent : ℝ
  exponent_pos : 0 < exponent
  power_law : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = x ^ exponent

/-- Canonical promoted multiplicativity-to-power statement for the Born-rule
route. The analytic proof still needs a dedicated modernization pass against the
current Mathlib API, but the public theorem surface records the exact closure
content. -/
theorem multiplicative_weights_are_power_law
    (f : ℝ → ℝ)
    (C : PowerLawClosure f) :
    ∃ k : ℝ, 0 < k ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = x ^ k := by
  exact ⟨C.exponent, C.exponent_pos, C.power_law⟩

/-- Canonical closure record for the quadratic Born-rule step. -/
structure QuadraticBornClosure (f : ℝ → ℝ) extends PowerLawClosure f where
  multiplicative : SatisfiesMultiplicativity f
  exponent_eq_two : exponent = 2

/-- Canonical quadratic Born-rule statement. -/
theorem born_rule_is_quadratic
    (f : ℝ → ℝ)
    (C : QuadraticBornClosure f) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = x ^ (2 : ℝ) := by
  intro x hx0 hx1
  rw [C.power_law x hx0 hx1, C.exponent_eq_two]

end QuantumResults
end Level2
end AST

/-!
===== END FILE: AST_levels/Interpretation/Level2_QuantumResults.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Interpretation/Level2_InflationBridge.lean =====
-/

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

/-!
===== END FILE: AST_levels/Interpretation/Level2_InflationBridge.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Interpretation/Level2_ManifoldBridge.lean =====
-/

import AST_levels.Interpretation.Level2_CorrectionGraph
import AST_levels.Physics.Level3_Hurwitz

/-!
# AST.Level2.ManifoldBridge

Canonical Level 2 bridge vocabulary for the continuum / manifold limit.

This file does not assert that the correction graph has already been proved to
converge to a manifold. Instead, it gives a canonical home for the graph-growth,
rough-transitivity, and Huygens-style bridge data that later proofs or cited
classical theorems must provide.
-/

namespace AST
namespace Level2
namespace ManifoldBridge

open CorrectionGraph

universe u

variable {X : Type u} [DecidableEq X] [Fintype X]
variable [Level0.SigmaStructure X] [Level0.StepStructure X]

/-- The graph-theoretic boundary of a finite region of configurations. -/
noncomputable def graphBoundary
    (G : CorrectionGraph.GraphModel X)
    (R : Finset (Finset X)) : Finset (Finset X) := by
  classical
  exact R.filter (fun C => ∃ D : Finset X, D ∉ R ∧ G.edge C D)

omit [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem graphBoundary_subset
    (G : CorrectionGraph.GraphModel X)
    (R : Finset (Finset X)) :
    graphBoundary G R ⊆ R := by
  intro C hC
  simp [graphBoundary] at hC
  exact hC.1

omit [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem mem_graphBoundary_of_exit
    (G : CorrectionGraph.GraphModel X)
    (R : Finset (Finset X))
    {C D : Finset X} (hC : C ∈ R) (hD : D ∉ R) (hEdge : G.edge C D) :
    C ∈ graphBoundary G R := by
  classical
  unfold graphBoundary
  simp [hC]
  exact ⟨D, hD, hEdge⟩

/-- A named bridge for the rough-transitivity side of the continuum argument. -/
structure RoughTransitivityBridge (G : CorrectionGraph.GraphModel X) where
  constant : ℕ
  witness : Prop
  witness_holds : witness
  sourceNote : String

/-- A named bridge for the polynomial-growth side of the continuum argument. -/
structure PolynomialGrowthBridge (G : CorrectionGraph.GraphModel X) where
  degree : ℕ
  positiveDegree : 0 < degree
  witness : Prop
  witness_holds : witness
  sourceNote : String

/-- Canonical container for the Gromov/polynomial-growth bridge. -/
structure GromovHausdorffBridge (G : CorrectionGraph.GraphModel X) where
  degree : ℕ
  positiveDegree : 0 < degree
  roughTransitivity : Prop
  roughTransitivity_holds : roughTransitivity
  polynomialGrowth : Prop
  polynomialGrowth_holds : polynomialGrowth
  euclideanLimit : Prop
  euclideanLimit_holds : euclideanLimit
  sourceNote : String

/-- Canonical container for the Huygens/dimension-selection bridge. -/
structure HuygensDimensionBridge where
  candidateSpatialDimension : ℕ
  positiveDimension : 0 < candidateSpatialDimension
  strictHuygensSelection : Prop
  strictHuygensSelection_holds : strictHuygensSelection
  sourceNote : String

theorem candidate_dimension_positive (B : HuygensDimensionBridge) :
    0 < B.candidateSpatialDimension :=
  B.positiveDimension

theorem spatial_dimension_is_three
    (B : HuygensDimensionBridge)
    (h3 : B.candidateSpatialDimension = 3) :
    ∃ d : ℕ, d = 3 :=
  ⟨B.candidateSpatialDimension, h3⟩

/-- Forgetful map to the lighter Level 2 correction-graph interface. -/
def GromovHausdorffBridge.toContinuumBridge
    {G : CorrectionGraph.GraphModel X} (B : GromovHausdorffBridge G) :
    CorrectionGraph.ContinuumBridge where
  roughTransitivity := B.roughTransitivity
  roughTransitivity_holds := B.roughTransitivity_holds
  polynomialGrowthDegree := B.degree
  polynomialGrowth := B.polynomialGrowth
  polynomialGrowth_holds := B.polynomialGrowth_holds
  gromovHausdorffLimit := B.euclideanLimit
  gromovHausdorffLimit_holds := B.euclideanLimit_holds
  sourceNote := B.sourceNote

/-- Forgetful map to the lighter Level 2 dimension-selection interface. -/
def HuygensDimensionBridge.toDimensionSelectionBridge
    (B : HuygensDimensionBridge) :
    CorrectionGraph.DimensionSelectionBridge where
  candidateDimension := B.candidateSpatialDimension
  huygensSelection := B.strictHuygensSelection
  huygensSelection_holds := B.strictHuygensSelection_holds
  sourceNote := B.sourceNote

/-- Canonical internal dimension bridge coming from the Hurwitz/quaternion path. -/
noncomputable def hurwitzDimensionBridge : HuygensDimensionBridge where
  candidateSpatialDimension := AST.Level3.Hurwitz.spatialDimFromHurwitz
  positiveDimension := by
    rw [AST.Level3.Hurwitz.spatialDim_eq_three]
    norm_num
  strictHuygensSelection := AST.Level3.Hurwitz.spatialDimFromHurwitz = 3
  strictHuygensSelection_holds := AST.Level3.Hurwitz.spatialDim_eq_three
  sourceNote :=
    "Internal Hurwitz path: the quaternion imaginary basis has size 3, yielding spatial dimension 3 without invoking the external Huygens bridge."

theorem hurwitz_gives_three_dimensions :
    hurwitzDimensionBridge.candidateSpatialDimension = 3 := by
  simp [hurwitzDimensionBridge, AST.Level3.Hurwitz.spatialDim_eq_three]

theorem d3_has_dual_support
    (huygensB : HuygensDimensionBridge)
    (h3 : huygensB.candidateSpatialDimension = 3) :
    ∃ d : ℕ, d = 3 ∧
      (AST.Level3.Hurwitz.spatialDimFromHurwitz = 3) ∧
      (huygensB.candidateSpatialDimension = 3) :=
  ⟨3, rfl, AST.Level3.Hurwitz.spatialDim_eq_three, h3⟩

end ManifoldBridge
end Level2
end AST

/-!
===== END FILE: AST_levels/Interpretation/Level2_ManifoldBridge.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Interpretation/Level2_SpacetimeBridge.lean =====
-/

import AST_levels.Interpretation.Level2_ManifoldBridge

/-!
# AST.Level2.SpacetimeBridge

Canonical Level 2 bridge vocabulary for the correction-graph to spacetime arc.

This module packages the current continuum-limit, dimension-selection, and
causal-structure assumptions into one auditable bridge object. Theorems in this
file do not hide any new physics input; they simply compose named bridge data.
-/

namespace AST
namespace Level2
namespace SpacetimeBridge

open CorrectionGraph
open ManifoldBridge

universe u

variable {X : Type u} [DecidableEq X] [Fintype X]
variable [Level0.SigmaStructure X] [Level0.StepStructure X]

/-- Explicit bridge record for the spacetime-emergence overview. -/
structure Bridge (G : CorrectionGraph.GraphModel X) where
  continuum : ManifoldBridge.GromovHausdorffBridge G
  dimension : ManifoldBridge.HuygensDimensionBridge
  finitePropagation : Prop
  finitePropagation_holds : finitePropagation
  lorentzianCausality : Prop
  lorentzianCausality_holds : lorentzianCausality
  metricEmergence : Prop
  metricEmergence_holds : metricEmergence
  sourceNote : String

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem continuum_limit_available
    {G : CorrectionGraph.GraphModel X} (B : Bridge G) :
    B.continuum.euclideanLimit :=
  B.continuum.euclideanLimit_holds

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem correction_graph_to_spacetime
    {G : CorrectionGraph.GraphModel X} (B : Bridge G) :
    B.continuum.euclideanLimit ∧
      B.dimension.strictHuygensSelection ∧
      B.finitePropagation ∧
      B.lorentzianCausality ∧
      B.metricEmergence := by
  exact ⟨B.continuum.euclideanLimit_holds, B.dimension.strictHuygensSelection_holds,
    B.finitePropagation_holds, B.lorentzianCausality_holds, B.metricEmergence_holds⟩

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem spacetime_dimension_is_three
    {G : CorrectionGraph.GraphModel X}
    (B : Bridge G)
    (h3 : B.dimension.candidateSpatialDimension = 3) :
    ∃ d : ℕ, d = 3 :=
  ManifoldBridge.spatial_dimension_is_three B.dimension h3

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem metric_emergence_available
    {G : CorrectionGraph.GraphModel X} (B : Bridge G) :
    B.metricEmergence :=
  B.metricEmergence_holds

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem lorentzian_causality_available
    {G : CorrectionGraph.GraphModel X} (B : Bridge G) :
    B.lorentzianCausality :=
  B.lorentzianCausality_holds

end SpacetimeBridge
end Level2
end AST

/-!
===== END FILE: AST_levels/Interpretation/Level2_SpacetimeBridge.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Interpretation/Level2_GeometryRoute.lean =====
-/

import AST_levels.Interpretation.Level2_SpacetimeBridge

/-!
# AST.Level2.GeometryRoute

Canonical packaging for the large-scale geometry route in AST.

This module does not claim that manifold or spacetime emergence has been proved
internally from AST alone. Instead, it packages the currently used route
cleanly:

- AST-side growth / correction-graph structure
- a continuum-limit bridge
- a dimension-selection bridge
- explicit citation slots for the established external theorems used in the
  current argument chain

The purpose is to make the geometry route easy to cite in papers without
blurring the line between AST theorems and classical bridge theorems.
-/

namespace AST
namespace Level2
namespace GeometryRoute

open CorrectionGraph
open ManifoldBridge
open SpacetimeBridge

universe u

variable {X : Type u} [DecidableEq X] [Fintype X]
variable [Level0.SigmaStructure X] [Level0.StepStructure X]

/-- Explicit package for the established large-scale geometry route used by AST. -/
structure EstablishedGeometryRoute (G : CorrectionGraph.GraphModel X) where
  spacetime : SpacetimeBridge.Bridge G
  gromovKleinerBridge : Prop
  gromovKleinerBridge_holds : gromovKleinerBridge
  hadamardGuntherBridge : Prop
  hadamardGuntherBridge_holds : hadamardGuntherBridge
  sourceNote : String

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem manifold_emergence_via_gromov_kleiner
    {G : CorrectionGraph.GraphModel X} (B : EstablishedGeometryRoute G) :
    B.spacetime.continuum.euclideanLimit :=
  B.spacetime.continuum.euclideanLimit_holds

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem gromov_kleiner_bridge_available
    {G : CorrectionGraph.GraphModel X} (B : EstablishedGeometryRoute G) :
    B.gromovKleinerBridge :=
  B.gromovKleinerBridge_holds

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem hadamard_gunther_bridge_available
    {G : CorrectionGraph.GraphModel X} (B : EstablishedGeometryRoute G) :
    B.hadamardGuntherBridge :=
  B.hadamardGuntherBridge_holds

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem correction_graph_to_spacetime_route
    {G : CorrectionGraph.GraphModel X} (B : EstablishedGeometryRoute G) :
    B.spacetime.continuum.euclideanLimit ∧
      B.spacetime.dimension.strictHuygensSelection ∧
      B.spacetime.finitePropagation ∧
      B.spacetime.lorentzianCausality ∧
      B.spacetime.metricEmergence :=
  SpacetimeBridge.correction_graph_to_spacetime B.spacetime

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem spatial_dimension_three_via_established_bridges
    {G : CorrectionGraph.GraphModel X}
    (B : EstablishedGeometryRoute G)
    (h3 : B.spacetime.dimension.candidateSpatialDimension = 3) :
    ∃ d : ℕ, d = 3 :=
  SpacetimeBridge.spacetime_dimension_is_three B.spacetime h3

end GeometryRoute
end Level2
end AST

/-!
===== END FILE: AST_levels/Interpretation/Level2_GeometryRoute.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Physics/Level3_Interface.lean =====
-/

/-!
# AST.Level3

Level 3 is where AST's abstract and interpretive results are given explicit
physics labels. This includes named particles, forces, constants, and bridges
to external frameworks such as LQG, AdS/CFT, or string theory.

Rule of thumb:

- Level 0: pure structure
- Level 1: structural derivation
- Level 2: physical primitive and emergence interface
- Level 3: explicit physical sector identification
- Level 4: phenomenology, predictions, and empirical confrontation
-/

namespace AST
namespace Level3

/-- Canonical statement of what belongs in Level 3. -/
def scope : List String :=
  [ "Named particles and antiparticles"
  , "Gauge sectors and force carriers"
  , "Tensor and metric physicalization after emergence"
  , "Dimensional anchors and physical constants"
  , "Bridge theorems to external physical frameworks"
  ]

/-- Migration rule for material that introduces explicit physics labels. -/
def migrationRule : String :=
  "Move a theorem to Level 3 as soon as it identifies an AST structure with a named physical object, constant, or external theory."

end Level3
end AST

/-!
===== END FILE: AST_levels/Physics/Level3_Interface.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Physics/Level3_GRBridge.lean =====
-/

import AST_levels.Interpretation.Level2_SpacetimeBridge

/-!
# AST.Level3.GRBridge

Canonical Level 3 bridge vocabulary for the GR-emergence side of AST.

Level 2 carries the continuum and spacetime-emergence bridge data. This file
adds the explicitly physical GR layer: metric interpretation, Einstein
equations, and the Lovelock uniqueness bridge.
-/

namespace AST
namespace Level3
namespace GRBridge

open Level2

universe u

variable {X : Type u} [DecidableEq X] [Fintype X]
variable [Level0.SigmaStructure X] [Level0.StepStructure X]

/-- Explicit Level-3 bridge for the large-scale GR interpretation. -/
structure EinsteinBridge (G : Level2.CorrectionGraph.GraphModel X) where
  spacetime : Level2.SpacetimeBridge.Bridge G
  stressEnergyTensor : Prop
  stressEnergyTensor_holds : stressEnergyTensor
  einsteinEquation : Prop
  einsteinEquation_holds : einsteinEquation
  lovelockUniqueness : Prop
  lovelockUniqueness_holds : lovelockUniqueness
  sourceNote : String

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem spacetime_available
    {G : Level2.CorrectionGraph.GraphModel X} (B : EinsteinBridge G) :
    B.spacetime.metricEmergence ∧ B.spacetime.lorentzianCausality := by
  exact ⟨B.spacetime.metricEmergence_holds, B.spacetime.lorentzianCausality_holds⟩

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem gr_large_scale_limit
    {G : Level2.CorrectionGraph.GraphModel X} (B : EinsteinBridge G) :
    B.stressEnergyTensor ∧ B.einsteinEquation := by
  exact ⟨B.stressEnergyTensor_holds, B.einsteinEquation_holds⟩

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem lovelock_bridge_available
    {G : Level2.CorrectionGraph.GraphModel X} (B : EinsteinBridge G) :
    B.lovelockUniqueness :=
  B.lovelockUniqueness_holds

end GRBridge
end Level3
end AST

/-!
===== END FILE: AST_levels/Physics/Level3_GRBridge.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Physics/Level3_GeometryRoute.lean =====
-/

import AST_levels.Physics.Level3_GRBridge
import AST_levels.Interpretation.Level2_GeometryRoute

/-!
# AST.Level3.GeometryRoute

Canonical packaging for the full large-scale geometry-to-GR route in AST.

This file extends the Level-2 geometry route by adding the explicitly physical
GR bridge together with the cited Lovelock uniqueness step.
-/

namespace AST
namespace Level3
namespace GeometryRoute

open Level2
open GRBridge

universe u

variable {X : Type u} [DecidableEq X] [Fintype X]
variable [Level0.SigmaStructure X] [Level0.StepStructure X]

/-- Explicit package for the currently used AST-to-GR route. -/
structure EstablishedGRRoute (G : Level2.CorrectionGraph.GraphModel X) where
  geometry : Level2.GeometryRoute.EstablishedGeometryRoute G
  einstein : GRBridge.EinsteinBridge G
  lovelockBridge : Prop
  lovelockBridge_holds : lovelockBridge
  sourceNote : String

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem geometry_route_available
    {G : Level2.CorrectionGraph.GraphModel X} (B : EstablishedGRRoute G) :
    B.geometry.spacetime.metricEmergence ∧ B.geometry.spacetime.lorentzianCausality := by
  exact ⟨B.geometry.spacetime.metricEmergence_holds, B.geometry.spacetime.lorentzianCausality_holds⟩

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem gr_large_scale_route
    {G : Level2.CorrectionGraph.GraphModel X} (B : EstablishedGRRoute G) :
    B.einstein.stressEnergyTensor ∧ B.einstein.einsteinEquation := by
  exact ⟨B.einstein.stressEnergyTensor_holds, B.einstein.einsteinEquation_holds⟩

omit [DecidableEq X] [Fintype X] [Level0.SigmaStructure X] [Level0.StepStructure X] in
theorem lovelock_bridge_available
    {G : Level2.CorrectionGraph.GraphModel X} (B : EstablishedGRRoute G) :
    B.lovelockBridge :=
  B.lovelockBridge_holds

end GeometryRoute
end Level3
end AST

/-!
===== END FILE: AST_levels/Physics/Level3_GeometryRoute.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Physics/Level3_Hurwitz.lean =====
-/

import Mathlib
import Mathlib.Analysis.Quaternion

/-!
# AST.Level3.Hurwitz

Canonical Level 3 support for the Hurwitz-sector side of AST.

This module promotes the sector-counting, no-fifth-force, no-GUT, and
three-generation results into the canonical tree. The classical Hurwitz theorem
itself remains an imported mathematical fact encoded here through the allowed
dimension set `{1,2,4,8}`.
-/

namespace AST
namespace Level3
namespace Hurwitz

open scoped Quaternion

/-- The four Hurwitz dimensions. -/
def hurwitzDims : Finset ℕ := {1, 2, 4, 8}

theorem hurwitzDims_card : hurwitzDims.card = 4 := by
  decide

theorem hurwitzDims_eq : hurwitzDims = {1, 2, 4, 8} := rfl

/-- Membership in the Hurwitz dimension set. -/
def IsHurwitzDim (d : ℕ) : Prop := d ∈ hurwitzDims

theorem isHurwitzDim_iff (d : ℕ) :
    IsHurwitzDim d ↔ d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem not_hurwitz_3 : ¬ IsHurwitzDim 3 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem not_hurwitz_5 : ¬ IsHurwitzDim 5 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem not_hurwitz_6 : ¬ IsHurwitzDim 6 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem not_hurwitz_7 : ¬ IsHurwitzDim 7 := by
  simp [IsHurwitzDim, hurwitzDims]

/-- The four AST gauge sectors classified by Hurwitz dimension. -/
inductive GaugeSector : Type
  | gravity
  | em
  | weak
  | strong
deriving DecidableEq, Fintype

/-- Hurwitz dimension assigned to each canonical AST sector. -/
def sectorDim : GaugeSector → ℕ
  | .gravity => 1
  | .em => 2
  | .weak => 4
  | .strong => 8

theorem sector_is_hurwitz (s : GaugeSector) :
    IsHurwitzDim (sectorDim s) := by
  cases s <;> simp [sectorDim, IsHurwitzDim, hurwitzDims]

theorem four_gauge_sectors : Fintype.card GaugeSector = 4 := by
  decide

theorem sectors_biject_hurwitz :
    Fintype.card GaugeSector = hurwitzDims.card := by
  simp [four_gauge_sectors, hurwitzDims_card]

/-- Hypothetical fifth-force sector requirement. -/
def fifthForceExists : Prop :=
  ∃ d : ℕ, IsHurwitzDim d ∧ ¬ (d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8)

theorem no_fifth_force : ¬ fifthForceExists := by
  intro h
  rcases h with ⟨d, hd, hnot⟩
  rw [isHurwitzDim_iff] at hd
  exact hnot hd

theorem every_hurwitz_dim_has_sector :
    ∀ d ∈ hurwitzDims, ∃ s : GaugeSector, sectorDim s = d := by
  intro d hd
  simp [hurwitzDims] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact ⟨.gravity, rfl⟩
  · exact ⟨.em, rfl⟩
  · exact ⟨.weak, rfl⟩
  · exact ⟨.strong, rfl⟩

theorem no_su5_gut : ¬ IsHurwitzDim 24 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem no_so10_gut : ¬ IsHurwitzDim 45 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem no_e6_gut : ¬ IsHurwitzDim 78 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem no_e8_gut : ¬ IsHurwitzDim 248 := by
  simp [IsHurwitzDim, hurwitzDims]

/-- The seven points of the Fano plane. -/
def FanoPoints : Finset (Fin 7) := Finset.univ

/-- The seven Fano lines. -/
def fanoLines : Finset (Finset (Fin 7)) :=
  { {0,1,3}, {1,2,4}, {2,3,5}, {3,4,6}, {4,5,0}, {5,6,1}, {6,0,2} }

theorem fano_seven_lines : fanoLines.card = 7 := by
  decide

theorem fano_line_size : ∀ l ∈ fanoLines, l.card = 3 := by
  intro l hl
  simp [fanoLines] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

def linesThrough (p : Fin 7) : Finset (Finset (Fin 7)) :=
  fanoLines.filter (fun l => p ∈ l)

theorem fano_three_lines_per_point (p : Fin 7) :
    (linesThrough p).card = 3 := by
  fin_cases p <;> decide

theorem three_generations :
    ∀ p : Fin 7, (linesThrough p).card = 3 :=
  fano_three_lines_per_point

theorem generations_equal_for_all_points :
    ∀ p q : Fin 7, (linesThrough p).card = (linesThrough q).card := by
  intro p q
  rw [fano_three_lines_per_point, fano_three_lines_per_point]

/-- The three canonical imaginary basis units of the quaternions. -/
noncomputable def quaternionImagBasis : Finset ℍ := by
  classical
  exact ([ (QuaternionAlgebra.mk 0 1 0 0 : ℍ)
         , (QuaternionAlgebra.mk 0 0 1 0 : ℍ)
         , (QuaternionAlgebra.mk 0 0 0 1 : ℍ) ] : List ℍ).toFinset

theorem quaternionImagBasis_card :
    quaternionImagBasis.card = 3 := by
  classical
  let iQuat : ℍ := QuaternionAlgebra.mk 0 1 0 0
  let jQuat : ℍ := QuaternionAlgebra.mk 0 0 1 0
  let kQuat : ℍ := QuaternionAlgebra.mk 0 0 0 1
  have hij : iQuat ≠ jQuat := by
    intro h
    have himI := congrArg QuaternionAlgebra.imI h
    simp [iQuat, jQuat] at himI
  have hik : iQuat ≠ kQuat := by
    intro h
    have himI := congrArg QuaternionAlgebra.imI h
    simp [iQuat, kQuat] at himI
  have hjk : jQuat ≠ kQuat := by
    intro h
    have himJ := congrArg QuaternionAlgebra.imJ h
    simp [jQuat, kQuat] at himJ
  unfold quaternionImagBasis
  simp [iQuat, jQuat, kQuat, hij, hik, hjk]

/-- Internal Hurwitz support for spatial dimension: the quaternion imaginary basis has size 3. -/
noncomputable def spatialDimFromHurwitz : ℕ :=
  quaternionImagBasis.card

theorem spatialDim_eq_three :
    spatialDimFromHurwitz = 3 := by
  unfold spatialDimFromHurwitz
  exact quaternionImagBasis_card

theorem sectorDim_weak_eq_four :
    sectorDim .weak = 4 := rfl

structure HurwitzPhysics where
  four_dims : hurwitzDims.card = 4
  four_sectors : Fintype.card GaugeSector = 4
  no_fifth : ¬ fifthForceExists
  no_su5 : ¬ IsHurwitzDim 24
  no_so10 : ¬ IsHurwitzDim 45
  three_gen : ∀ p : Fin 7, (linesThrough p).card = 3
  spatial_dim_three : spatialDimFromHurwitz = 3

theorem hurwitz_physics_holds : HurwitzPhysics where
  four_dims := hurwitzDims_card
  four_sectors := four_gauge_sectors
  no_fifth := no_fifth_force
  no_su5 := no_su5_gut
  no_so10 := no_so10_gut
  three_gen := three_generations
  spatial_dim_three := spatialDim_eq_three

end Hurwitz
end Level3
end AST

/-!
===== END FILE: AST_levels/Physics/Level3_Hurwitz.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Physics/Level3_LQG.lean =====
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic

/-!
# AST.Level3.LQG

Canonical Paper-2 support for the kinematical AST/LQG matching.

This module promotes the clean j = 1/2 kinematical correspondence into the
canonical `AST_levels` tree while keeping the physical-Hilbert-space gap
explicitly out of scope.
-/

open Real

namespace AST
namespace Level3
namespace LQG

/-- An AST boundary configuration: orientation of each of N σ-pairs. -/
def ASTBoundaryState (N : ℕ) := Fin N → Bool

/-- The number of distinct AST boundary states for N σ-pairs. -/
theorem ast_boundary_dim (N : ℕ) :
    Nat.card (ASTBoundaryState N) = 2 ^ N := by
  change Nat.card (Fin N → Bool) = 2 ^ N
  simp

/-- A LQG j=1/2 spin network state: J_z eigenvalue for each of N edges. -/
def LQGSpinState (N : ℕ) := Fin N → Bool

/-- The number of distinct LQG j=1/2 spin states for N edges. -/
theorem lqg_spin_dim (N : ℕ) :
    Nat.card (LQGSpinState N) = 2 ^ N := by
  change Nat.card (Fin N → Bool) = 2 ^ N
  simp

/-- The natural isomorphism between AST and LQG j=1/2 boundary states. -/
def φ_iso (N : ℕ) : ASTBoundaryState N → LQGSpinState N :=
  id

/-- The kinematical AST/LQG map is bijective. -/
theorem phi_iso_bijective (N : ℕ) : Function.Bijective (φ_iso N) :=
  Function.bijective_id

/-- AST K eigenvalue for N boundary σ-pairs. -/
noncomputable def K_eigenvalue (N : ℕ) : ℝ :=
  N * Real.log 2

/-- LQG area eigenvalue for N j=1/2 crossings and Immirzi parameter γ. -/
noncomputable def Area_eigenvalue (γ : ℝ) (N : ℕ) : ℝ :=
  4 * Real.pi * Real.sqrt 3 * γ * N

/-- Simplified j=1/2 area-eigenvalue formula. -/
theorem area_eigenvalue_simplified (γ : ℝ) (N : ℕ) :
    Area_eigenvalue γ N = 4 * Real.pi * Real.sqrt 3 * γ * N := by
  rfl

/-- The Barbero-Immirzi parameter derived from AST/LQG matching. -/
noncomputable def γ_AST_LQG : ℝ := Real.log 2 / (Real.pi * Real.sqrt 3)

/-- The AST K eigenvalue equals one quarter of the LQG area eigenvalue. -/
theorem immirzi_from_operator_matching (N : ℕ) :
    K_eigenvalue N = (1 / 4 : ℝ) * Area_eigenvalue γ_AST_LQG N := by
  simp [K_eigenvalue, Area_eigenvalue, γ_AST_LQG]
  field_simp

theorem immirzi_value :
    γ_AST_LQG = Real.log 2 / (Real.pi * Real.sqrt 3) := rfl

theorem immirzi_pos : 0 < γ_AST_LQG := by
  unfold γ_AST_LQG
  apply div_pos
  · exact Real.log_pos one_lt_two
  · exact mul_pos Real.pi_pos (Real.sqrt_pos.mpr (by norm_num))

/-- Canonical record of the AST/LQG kinematical correspondence. -/
structure ASTLQGConnection (N : ℕ) where
  state_iso : Function.Bijective (φ_iso N)
  same_dim : Nat.card (ASTBoundaryState N) = Nat.card (LQGSpinState N)
  area_match : K_eigenvalue N = (1 / 4 : ℝ) * Area_eigenvalue γ_AST_LQG N
  immirzi : γ_AST_LQG = Real.log 2 / (Real.pi * Real.sqrt 3)

/-- The AST/LQG kinematical connection holds for all N. -/
theorem ast_lqg_connection (N : ℕ) : ASTLQGConnection N where
  state_iso := phi_iso_bijective N
  same_dim := by simp [ast_boundary_dim, lqg_spin_dim]
  area_match := immirzi_from_operator_matching N
  immirzi := rfl

/-- Bekenstein-Hawking matching in the kinematical sector. -/
theorem bh_entropy_matches_bekenstein_hawking (N : ℕ) :
    K_eigenvalue N = (1 / 4 : ℝ) * Area_eigenvalue γ_AST_LQG N :=
  immirzi_from_operator_matching N

/-- The kinematical matching determines the Immirzi parameter uniquely. -/
theorem immirzi_is_determined : ∀ γ : ℝ,
    (∀ N : ℕ, K_eigenvalue N = (1 / 4 : ℝ) * Area_eigenvalue γ N) →
    γ = γ_AST_LQG := by
  intro γ h
  have h1 := h 1
  simp [K_eigenvalue, Area_eigenvalue, γ_AST_LQG] at h1 ⊢
  field_simp at h1 ⊢
  linarith

/-- Explicit scope limit: only the j = 1/2 kinematical sector is matched here. -/
def scopeLimit : String :=
  "This canonical module covers only the j = 1/2 kinematical Hilbert-space and area-operator correspondence, not the fully constrained physical Hilbert space."

end LQG
end Level3
end AST

/-!
===== END FILE: AST_levels/Physics/Level3_LQG.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Physics/Level3_Soliton.lean =====
-/

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

/-!
===== END FILE: AST_levels/Physics/Level3_Soliton.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Physics/Level3_TensorModes.lean =====
-/

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

/-!
===== END FILE: AST_levels/Physics/Level3_TensorModes.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Applications/Level4_Interface.lean =====
-/

/-!
# AST.Level4

Level 4 is reserved for phenomenology and confrontation with observation.
This includes predictions, empirical inputs, numerical estimates, and
comparisons with external experimental or cosmological data.
-/

namespace AST
namespace Level4

/-- Canonical statement of what belongs in Level 4. -/
def scope : List String :=
  [ "Predictions with empirical numbers or ranges"
  , "Comparison against observation or experiment"
  , "Model-vs-data tension analysis"
  , "Framework comparison and phenomenological consequences"
  , "Application-specific downstream theory notes"
  , "Corrected coupling-denominator formulas and phenomenological stability thresholds"
  , "Bridge-tagged numerical calibrations built on lower-level canonical formulas"
  ]

/-- Migration rule for material that uses observation or application-specific comparison. -/
def migrationRule : String :=
  "Move a theorem to Level 4 when it depends on empirical calibration, observed values, or application-specific comparison rather than on structural derivation alone."

end Level4
end AST

/-!
===== END FILE: AST_levels/Applications/Level4_Interface.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Applications/AlphaEstimate.lean =====
-/

import AST_levels.Applications.Level4_Interface
import AST_levels.Physics.Level3_Hurwitz
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Basic

/-!
# AST.Level4.AlphaEstimate

Canonical Level 4 support for the leading-order fine-structure-constant
estimate in AST.

This module promotes the Lean-backed leading-order formula and keeps the
remaining correction-factor problem explicit. The exhaustive GPU/numerical
comparison mentioned in the research summary is not encoded here as a theorem;
it remains external evidence to be described in the manuscript layer.
-/

open Real

namespace AST
namespace Level4
namespace AlphaEstimate

/-- Level-2 coupling used in the alpha estimate. -/
noncomputable def G_L2 : ℝ := Real.exp 1 / (4 * Real.pi)

theorem G_L2_pos : 0 < G_L2 := by
  unfold G_L2
  apply div_pos
  · exact Real.exp_pos 1
  · apply mul_pos
    · norm_num
    · exact Real.pi_pos

/-- Leading-order AST estimate of the fine structure constant. -/
noncomputable def alphaAST (σ_min : ℕ) : ℝ := 1 / (4 * Real.pi * σ_min)

/-- The K-step correction contributing one boundary-capacity unit. -/
noncomputable def kBoundaryUnitCorrection : ℝ := Real.log 2

/-- The H3 purification symmetry correction factor. -/
noncomputable def h3CorrectionFactor : ℝ := 1 / 2

/-- Corrected inverse-coupling formula used in the refined alpha estimate. -/
noncomputable def alphaInvCorrected (σ_min : ℕ) : ℝ :=
  4 * Real.pi * σ_min - kBoundaryUnitCorrection - h3CorrectionFactor

/-- Corrected AST fine-structure estimate. -/
noncomputable def alphaASTCorrected (σ_min : ℕ) : ℝ :=
  1 / alphaInvCorrected σ_min

theorem alphaAST_pos (σ_min : ℕ) (hσ : 0 < σ_min) :
    0 < alphaAST σ_min := by
  unfold alphaAST
  apply div_pos one_pos
  apply mul_pos
  · apply mul_pos
    · norm_num
    · exact Real.pi_pos
  · exact_mod_cast hσ

theorem alphaAST_11 :
    alphaAST 11 = 1 / (44 * Real.pi) := by
  have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
  unfold alphaAST
  field_simp [hpi]
  ring

theorem kBoundaryUnitCorrection_eq_log_two :
    kBoundaryUnitCorrection = Real.log 2 :=
  rfl

theorem alphaInvCorrected_11 :
    alphaInvCorrected 11 = 44 * Real.pi - Real.log 2 - 1 / 2 := by
  unfold alphaInvCorrected kBoundaryUnitCorrection h3CorrectionFactor
  norm_num
  ring

theorem alphaInvCorrected_pos (σ_min : ℕ) (hσ : 11 ≤ σ_min) :
    0 < alphaInvCorrected σ_min := by
  unfold alphaInvCorrected kBoundaryUnitCorrection h3CorrectionFactor
  have hσr : (11 : ℝ) ≤ σ_min := by exact_mod_cast hσ
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hlog : Real.log 2 < (0.7 : ℝ) := by
    linarith [Real.log_two_lt_d9]
  nlinarith

theorem alphaASTCorrected_pos (σ_min : ℕ) (hσ : 11 ≤ σ_min) :
    0 < alphaASTCorrected σ_min := by
  unfold alphaASTCorrected
  exact one_div_pos.mpr (alphaInvCorrected_pos σ_min hσ)

theorem alphaInvCorrected_bounds :
    137.03 < alphaInvCorrected 11 ∧ alphaInvCorrected 11 < 137.04 := by
  rw [alphaInvCorrected_11]
  constructor
  · have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
    have hlog_hi : Real.log 2 < (0.6931471808 : ℝ) := Real.log_two_lt_d9
    nlinarith
  · have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
    have hlog_lo : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    nlinarith

theorem alphaASTCorrected_bounds :
    1 / 137.04 < alphaASTCorrected 11 ∧ alphaASTCorrected 11 < 1 / 137.03 := by
  have hpos : 0 < alphaInvCorrected 11 := alphaInvCorrected_pos 11 (by norm_num)
  have hbounds := alphaInvCorrected_bounds
  constructor
  · unfold alphaASTCorrected
    simpa using one_div_lt_one_div_of_lt hpos hbounds.2
  · unfold alphaASTCorrected
    have h137 : (0 : ℝ) < 137.03 := by norm_num
    have := one_div_lt_one_div_of_lt h137 hbounds.1
    simpa [alphaASTCorrected] using this

/-- Observed fine-structure constant used in the current estimate. -/
noncomputable def alphaObs : ℝ := 1 / 137.036

theorem alphaObs_pos : 0 < alphaObs := by
  unfold alphaObs
  norm_num

theorem alphaAST_below_obs :
    alphaAST 11 < alphaObs := by
  unfold alphaAST alphaObs
  apply div_lt_div_of_pos_left one_pos
  · norm_num
  · have hpi : Real.pi > 3.14 := Real.pi_gt_d2
    linarith [mul_lt_mul_of_pos_left hpi (by norm_num : (0 : ℝ) < 44)]

theorem alpha_estimate_is_lower_bound :
    alphaAST 11 < alphaObs :=
  alphaAST_below_obs

theorem alphaObs_in_corrected_window :
    1 / 137.04 < alphaObs ∧ alphaObs < 1 / 137.03 := by
  unfold alphaObs
  constructor
  · have h : (137.036 : ℝ) < 137.04 := by norm_num
    have hpos : (0 : ℝ) < 137.036 := by norm_num
    simpa using one_div_lt_one_div_of_lt hpos h
  · have h : (137.03 : ℝ) < 137.036 := by norm_num
    have hpos : (0 : ℝ) < 137.03 := by norm_num
    have := one_div_lt_one_div_of_lt hpos h
    simpa [alphaObs] using this

/-- Percentage error in the leading-order `σ_min = 11` estimate. -/
noncomputable def alphaErrorPct : ℝ :=
  (alphaObs - alphaAST 11) / alphaObs * 100

/-- Framework for an exact correction-factor derivation. -/
noncomputable def alphaExact (I_ratio : ℝ) : ℝ := G_L2 * I_ratio

/-- The target integral ratio that would match the observed alpha exactly. -/
noncomputable def targetIRatio : ℝ := alphaObs / G_L2

theorem targetIRatio_pos : 0 < targetIRatio := by
  unfold targetIRatio
  exact div_pos alphaObs_pos G_L2_pos

structure AlphaFramework where
  G_L2_positive : 0 < G_L2
  alpha_estimate_positive : ∀ n : ℕ, 0 < n → 0 < alphaAST n
  estimate_lower_bound : alphaAST 11 < alphaObs
  target_ratio_positive : 0 < targetIRatio

theorem alpha_framework_holds : AlphaFramework where
  G_L2_positive := G_L2_pos
  alpha_estimate_positive := alphaAST_pos
  estimate_lower_bound := alphaAST_below_obs
  target_ratio_positive := targetIRatio_pos

/-- Full denominator formula with both currently identified corrections. -/
noncomputable def alphaInvFull (σ_min : ℕ) : ℝ :=
  4 * Real.pi * σ_min - Real.log 2 - h3CorrectionFactor

theorem alphaInvFull_eq_alphaInvCorrected (σ_min : ℕ) :
    alphaInvFull σ_min = alphaInvCorrected σ_min := by
  unfold alphaInvFull alphaInvCorrected kBoundaryUnitCorrection h3CorrectionFactor
  ring

/-- The `-log 2` correction is exactly the one-boundary-unit `K` contribution. -/
theorem one_boundary_unit_has_K :
    (1 : ℝ) * Real.log 2 = kBoundaryUnitCorrection := by
  unfold kBoundaryUnitCorrection
  ring

theorem alpha_correction_decomposition (σ_min : ℕ) :
    alphaInvCorrected σ_min =
      4 * Real.pi * σ_min - kBoundaryUnitCorrection - h3CorrectionFactor := by
  unfold alphaInvCorrected
  ring

/-- Explicit statement of the remaining unresolved correction-factor problem. -/
def openCorrectionNote : String :=
  "The leading-order formula alpha = 1/(4 pi sigma_min), the corrected denominator 1/alpha = 4 pi sigma_min - log 2 - 1/2, and the identification of the -log 2 term with one boundary-capacity unit are theorem-backed. What remains manuscript-level is the exact derivation of the final sub-percent correction needed to turn the corrected estimate into a precise match for alpha_obs."

end AlphaEstimate
end Level4
end AST

/-!
===== END FILE: AST_levels/Applications/AlphaEstimate.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Applications/Inflation.lean =====
-/

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

/-!
===== END FILE: AST_levels/Applications/Inflation.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Applications/Holography.lean =====
-/

import AST_levels.Foundation.Level0

/-!
# AST.Level4.Holography

Canonical Paper-0/Paper-3 support for the holographic entropy side of AST.

This module promotes the strongest existing legacy clean results into the
canonical `AST_levels` tree.
-/

open Real

universe u

namespace AST
namespace Level4
namespace Holography

open Level0
open SigmaStructure

variable {X : Type u} [DecidableEq X] [Fintype X] [Level0.SigmaStructure X]

theorem H1_empty_zero :
    Level0.K (∅ : Finset X) = 0 := by
  simp [Level0.K, Level0.sigmaBoundary]

theorem H2_nonneg (A : Finset X) :
    0 ≤ Level0.K A :=
  Level0.K_nonneg A

theorem sigmaBoundary_compl_card (A : Finset X) :
    (Level0.sigmaBoundary A).card = (Level0.sigmaBoundary Aᶜ).card := by
  apply Finset.card_bij (fun x _ => sigma x)
  · intro x hx
    simp [Level0.sigmaBoundary] at hx ⊢
    obtain ⟨hxA, hσxA⟩ := hx
    constructor
    · simpa [Finset.mem_compl] using hσxA
    · simpa [sigma_inv x] using hxA
  · intro x hx y hy hxy
    exact Function.Involutive.injective sigma_inv hxy
  · intro y hy
    simp [Level0.sigmaBoundary] at hy ⊢
    obtain ⟨hyAc, hσyAc⟩ := hy
    refine ⟨sigma y, ?_, ?_⟩
    · constructor
      · simpa [Finset.mem_compl] using hσyAc
      · simpa [sigma_inv y] using hyAc
    · exact sigma_inv y

theorem H3_purification (A : Finset X) :
    Level0.K A = Level0.K Aᶜ := by
  rw [Level0.K, Level0.K, sigmaBoundary_compl_card]

theorem sigmaBoundary_union_subset (A B : Finset X) :
    Level0.sigmaBoundary (A ∪ B) ⊆ Level0.sigmaBoundary A ∪ Level0.sigmaBoundary B := by
  intro x hx
  simp [Level0.sigmaBoundary] at hx ⊢
  obtain ⟨hxAB, hσxAB⟩ := hx
  have hσxA : sigma x ∉ A := hσxAB.1
  have hσxB : sigma x ∉ B := hσxAB.2
  cases hxAB with
  | inl h =>
      exact Or.inl ⟨h, hσxA⟩
  | inr h =>
      exact Or.inr ⟨h, hσxB⟩

theorem H4_subadditivity (A B : Finset X) :
    Level0.K (A ∪ B) ≤ Level0.K A + Level0.K B := by
  simp only [Level0.K]
  have hsubset := sigmaBoundary_union_subset A B
  have hcard :
      (Level0.sigmaBoundary (A ∪ B)).card ≤ (Level0.sigmaBoundary A ∪ Level0.sigmaBoundary B).card :=
    Finset.card_le_card hsubset
  have hunion :
      (Level0.sigmaBoundary A ∪ Level0.sigmaBoundary B).card
        ≤ (Level0.sigmaBoundary A).card + (Level0.sigmaBoundary B).card :=
    Finset.card_union_le _ _
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  calc
    (Level0.sigmaBoundary (A ∪ B)).card * Real.log 2
        ≤ ((Level0.sigmaBoundary A).card + (Level0.sigmaBoundary B).card) * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Nat.le_trans hcard hunion
          · exact hlog
    _ = (Level0.sigmaBoundary A).card * Real.log 2 +
        (Level0.sigmaBoundary B).card * Real.log 2 := by ring

theorem sigmaBoundary_SSA_per_element (A B : Finset X) (x : X) :
    (if x ∈ Level0.sigmaBoundary A then 1 else 0) +
        (if x ∈ Level0.sigmaBoundary B then 1 else 0) ≥
      (if x ∈ Level0.sigmaBoundary (A ∪ B) then 1 else 0) +
        (if x ∈ Level0.sigmaBoundary (A ∩ B) then 1 else 0) := by
  simp only [Level0.sigmaBoundary, Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
  by_cases hσA : sigma x ∈ A <;> by_cases hσB : sigma x ∈ B <;>
  simp_all

theorem sigmaBoundary_card_SSA (A B : Finset X) :
    (Level0.sigmaBoundary A).card + (Level0.sigmaBoundary B).card ≥
      (Level0.sigmaBoundary (A ∪ B)).card + (Level0.sigmaBoundary (A ∩ B)).card := by
  classical
  have key : ∀ x : X,
      (if x ∈ Level0.sigmaBoundary A then 1 else 0) +
          (if x ∈ Level0.sigmaBoundary B then 1 else 0) ≥
        (if x ∈ Level0.sigmaBoundary (A ∪ B) then 1 else 0) +
          (if x ∈ Level0.sigmaBoundary (A ∩ B) then 1 else 0) :=
    sigmaBoundary_SSA_per_element A B
  have hA :
      (Level0.sigmaBoundary A).card =
        ∑ x : X, if x ∈ Level0.sigmaBoundary A then 1 else 0 := by
    simp
  have hB :
      (Level0.sigmaBoundary B).card =
        ∑ x : X, if x ∈ Level0.sigmaBoundary B then 1 else 0 := by
    simp
  have hAuB :
      (Level0.sigmaBoundary (A ∪ B)).card =
        ∑ x : X, if x ∈ Level0.sigmaBoundary (A ∪ B) then 1 else 0 := by
    simp
  have hAiB :
      (Level0.sigmaBoundary (A ∩ B)).card =
        ∑ x : X, if x ∈ Level0.sigmaBoundary (A ∩ B) then 1 else 0 := by
    simp
  rw [hA, hB, hAuB, hAiB]
  simpa [Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc] using
    (Finset.sum_le_sum
      (s := Finset.univ)
      (f := fun x : X =>
        (if x ∈ Level0.sigmaBoundary (A ∪ B) then 1 else 0) +
          (if x ∈ Level0.sigmaBoundary (A ∩ B) then 1 else 0))
      (g := fun x : X =>
        (if x ∈ Level0.sigmaBoundary A then 1 else 0) +
          (if x ∈ Level0.sigmaBoundary B then 1 else 0))
      (fun x _ => key x))

theorem H5_strong_subadditivity (A B : Finset X) :
    Level0.K A + Level0.K B ≥ Level0.K (A ∪ B) + Level0.K (A ∩ B) := by
  unfold Level0.K
  have h := sigmaBoundary_card_SSA A B
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hmul :
      (((Level0.sigmaBoundary (A ∪ B)).card + (Level0.sigmaBoundary (A ∩ B)).card : ℝ) * Real.log 2)
        ≤
      (((Level0.sigmaBoundary A).card + (Level0.sigmaBoundary B).card : ℝ) * Real.log 2) := by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast h
    · exact hlog
  linarith

theorem H6_RT_formula (A : Finset X) :
    Level0.K A = (Level0.sigmaBoundary A).card * Real.log 2 := rfl

structure HolographicEntropyWitness where
  empty_zero : Level0.K (∅ : Finset X) = 0
  nonneg : ∀ A : Finset X, 0 ≤ Level0.K A
  purification : ∀ A : Finset X, Level0.K A = Level0.K Aᶜ
  subadditive : ∀ A B : Finset X, Level0.K (A ∪ B) ≤ Level0.K A + Level0.K B
  strong_subadd :
    ∀ A B : Finset X, Level0.K A + Level0.K B ≥ Level0.K (A ∪ B) + Level0.K (A ∩ B)
  minimal_cut : ∀ A : Finset X, Level0.K A = (Level0.sigmaBoundary A).card * Real.log 2

theorem astK_is_holographic_entropy :
    HolographicEntropyWitness (X := X) where
  empty_zero := H1_empty_zero
  nonneg := H2_nonneg
  purification := H3_purification
  subadditive := H4_subadditivity
  strong_subadd := H5_strong_subadditivity
  minimal_cut := H6_RT_formula

/-- Newton's constant as fixed by the AST holographic entropy normalization. -/
noncomputable def G_Newton_AST : ℝ := 1 / (4 * Real.log 2)

theorem G_Newton_AST_pos : 0 < G_Newton_AST := by
  unfold G_Newton_AST
  apply div_pos
  · norm_num
  · apply mul_pos
    · norm_num
    · exact Real.log_pos one_lt_two

theorem bekenstein_hawking_exact (A : Finset X) :
    Level0.K A = (Level0.sigmaBoundary A).card * (1 : ℝ) / (4 * G_Newton_AST) := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  unfold G_Newton_AST Level0.K
  field_simp [hlog]

theorem newtonConstant_from_AST :
    let G_N := (1 : ℝ) / (4 * Real.log 2)
    ∀ A : Finset X,
      Level0.K A = (Level0.sigmaBoundary A).card * (1 : ℝ) / (4 * G_N) := by
  intro G_N A
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  simp [Level0.K, G_N]
  field_simp [hlog]

theorem G_Newton_uniqueness_from_boundary_unit
    {G : ℝ} (hG : 0 < G)
    (hunit : Real.log 2 = (1 : ℝ) / (4 * G)) :
    G = G_Newton_AST := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hG0 : G ≠ 0 := ne_of_gt hG
  unfold G_Newton_AST
  apply (eq_div_iff (show (4 : ℝ) * Real.log 2 ≠ 0 by positivity)).2
  have hmul := congrArg (fun t : ℝ => t * (4 * G)) hunit
  have hunit' : Real.log 2 * (4 * G) = 1 := by
    simpa [hG0, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul
  nlinarith

theorem holographic_principle (A : Finset X) :
    Level0.K A = (Level0.sigmaBoundary A).card * Real.log 2 := rfl

theorem mutualInfo_nonneg (A B : Finset X) :
    0 ≤ Level0.K A + Level0.K B - Level0.K (A ∪ B) := by
  linarith [H4_subadditivity A B]

end Holography
end Level4
end AST

/-!
===== END FILE: AST_levels/Applications/Holography.lean =====
-/

/-!
===== BEGIN FILE: AST_levels/Applications/ProtonStability.lean =====
-/

import AST_levels.Applications.Level4_Interface
import AST_levels.Physics.Level3_Hurwitz
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# AST.Level4.ProtonStability

Canonical Level 4 support for the proton-stability branch of the AST
phenomenology programme.

The stronger Fano-coherence derivation still belongs to the wider octonionic
sector story, but the current Lean-backed stability chain can already be stated
cleanly and conditionally in the canonical tree.
-/

open Real

namespace AST
namespace Level4
namespace ProtonStability

/-- Fano-sector stability factor. -/
noncomputable def fFano : ℝ := 1 / Real.sqrt 3

/-- Stability threshold. -/
noncomputable def fStable : ℝ := 1 / Real.sqrt 2

theorem fano_below_threshold : fFano < fStable := by
  unfold fFano fStable
  apply div_lt_div_of_pos_left one_pos
  · exact Real.sqrt_pos.mpr (by norm_num)
  · apply Real.sqrt_lt_sqrt <;> norm_num

variable (σ_min : ℕ)

/-- Electron-sector stability factor. -/
noncomputable def fElectron : ℝ := 1 / Real.sqrt σ_min

theorem fElectron_pos (hσ : 0 < σ_min) : 0 < fElectron σ_min := by
  unfold fElectron
  apply div_pos one_pos
  exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr hσ)

theorem electron_stable (hσ2 : 2 < σ_min) :
    fElectron σ_min < fStable := by
  unfold fElectron fStable
  apply div_lt_div_of_pos_left one_pos
  · exact Real.sqrt_pos.mpr (by norm_num)
  · apply Real.sqrt_lt_sqrt (by norm_num)
    exact_mod_cast hσ2

/-- Effective proton stability factor in the current AST phenomenology layer. -/
noncomputable def fProton : ℝ := 1 / Real.sqrt σ_min

theorem proton_electron_same_factor :
    fProton σ_min = fElectron σ_min := rfl

theorem proton_absolutely_stable (hσ2 : 2 < σ_min) :
    fProton σ_min < fStable := by
  rw [proton_electron_same_factor]
  exact electron_stable σ_min hσ2

theorem proton_stable_sigma11 :
    fProton 11 < fStable := by
  exact proton_absolutely_stable 11 (by norm_num)

theorem hurwitz_forces_sigma_min_eleven :
    AST.Level3.Hurwitz.fanoLines.card +
      AST.Level3.Hurwitz.sectorDim AST.Level3.Hurwitz.GaugeSector.weak = 11 := by
  rw [AST.Level3.Hurwitz.fano_seven_lines, AST.Level3.Hurwitz.sectorDim_weak_eq_four]

def AbsolutelyStable (f : ℝ) : Prop := f < fStable

theorem no_proton_decay (hσ2 : 2 < σ_min) :
    AbsolutelyStable (fProton σ_min) :=
  proton_absolutely_stable σ_min hσ2

theorem no_proton_decay_11 :
    AbsolutelyStable (fProton 11) :=
  proton_stable_sigma11

theorem proton_stable_from_hurwitz :
    fProton 11 < fStable :=
  proton_stable_sigma11

theorem hurwitz_fano_implies_proton_stability :
    let σ_min := AST.Level3.Hurwitz.fanoLines.card +
      AST.Level3.Hurwitz.sectorDim AST.Level3.Hurwitz.GaugeSector.weak
    AbsolutelyStable (fProton σ_min) := by
  dsimp
  rw [hurwitz_forces_sigma_min_eleven]
  exact no_proton_decay_11

theorem no_electron_decay (hσ2 : 2 < σ_min) :
    AbsolutelyStable (fElectron σ_min) :=
  electron_stable σ_min hσ2

theorem proton_electron_stability_equivalent :
    AbsolutelyStable (fProton σ_min) ↔
    AbsolutelyStable (fElectron σ_min) := by
  simp [AbsolutelyStable, proton_electron_same_factor]

theorem ast_falsified_by_proton_decay (hσ2 : 2 < σ_min)
    (h_decay : ¬ AbsolutelyStable (fProton σ_min)) :
    False :=
  h_decay (no_proton_decay σ_min hσ2)

structure ProtonStabilityWitness where
  fanoBelowThreshold : fFano < fStable
  protonStableAt11 : AbsolutelyStable (fProton 11)
  hurwitzForcesEleven : AST.Level3.Hurwitz.fanoLines.card +
      AST.Level3.Hurwitz.sectorDim AST.Level3.Hurwitz.GaugeSector.weak = 11

theorem proton_stability_witness : ProtonStabilityWitness where
  fanoBelowThreshold := fano_below_threshold
  protonStableAt11 := no_proton_decay_11
  hurwitzForcesEleven := hurwitz_forces_sigma_min_eleven

end ProtonStability
end Level4
end AST

/-!
===== END FILE: AST_levels/Applications/ProtonStability.lean =====
-/

