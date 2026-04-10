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
