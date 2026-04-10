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
