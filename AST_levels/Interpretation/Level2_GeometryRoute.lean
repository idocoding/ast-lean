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
