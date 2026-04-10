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
