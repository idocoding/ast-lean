# Geometry Chain Status

This note isolates the large-scale geometric route used in the AST papers.

## Status labels

- `Theorem`: proved directly in the public canonical modules.
- `Bridge`: represented canonically, but depends on an explicit external
  mathematical theorem or interpretation bridge.
- `Open`: not yet closed even at the bridge level.

## Chain

| Stage | Result | Status | Canonical location | Remaining dependency |
|---|---|---|---|---|
| 1 | `β = 1` rate control / polynomial-growth input | `Theorem` | [AST_levels/Foundation/Level1_BetaFlow.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Foundation/Level1_BetaFlow.lean) together with the promoted geometry chain | AST-side growth control is available. |
| 2 | correction graph has the right large-scale growth profile | `Theorem + Bridge` | [AST_levels/Interpretation/Level2_ManifoldBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_ManifoldBridge.lean) | The AST prerequisites are present; the continuum/manifold step still uses the classical Gromov/Kleiner bridge. |
| 3 | manifold emergence | `Bridge` | [AST_levels/Interpretation/Level2_GeometryRoute.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_GeometryRoute.lean) | External classical theorem: polynomial growth to manifold/Gromov-Hausdorff limit. |
| 4 | strict Huygens selects odd `d >= 3` | `Bridge` | [AST_levels/Interpretation/Level2_GeometryRoute.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_GeometryRoute.lean) and [AST_levels/Interpretation/Level2_SpacetimeBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_SpacetimeBridge.lean) | External classical theorem: Hadamard-Gunther. |
| 5 | minimal admissible spatial dimension is `d = 3` | `Bridge` | [AST_levels/Interpretation/Level2_GeometryRoute.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_GeometryRoute.lean) | Depends on the Huygens bridge plus the minimality argument. |
| 5a | internal Hurwitz/quaternion support for `d = 3` | `Theorem` | [AST_levels/Physics/Level3_Hurwitz.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_Hurwitz.lean) and [AST_levels/Interpretation/Level2_ManifoldBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_ManifoldBridge.lean) | Internal AST-side support from the three-element quaternion imaginary basis, packaged canonically as `hurwitzDimensionBridge`. |
| 6 | GR uniqueness in `3+1` dimensions | `Bridge` | [AST_levels/Physics/Level3_GeometryRoute.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_GeometryRoute.lean) and [AST_levels/Physics/Level3_GRBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_GRBridge.lean) | External classical theorem: Lovelock. |

## Interpretation

The AST-side content is strongest at the `β = 1` and large-scale growth stage.
The remaining large-scale geometry steps are currently explicit bridges to
established mathematical theorems:

- Gromov/Kleiner for the manifold-emergence step
- Hadamard-Gunther for the strict-Huygens / `d = 3` step
- Lovelock for the GR uniqueness step

In parallel with that classical route, the public tree now also records an
internal Hurwitz/quaternion support path for `d = 3`, so the spatial-dimension
claim has both internal and external support in the canonical package.

This means the current public package already captures the AST contribution and
its exact mathematical dependencies honestly, with the route now bundled
explicitly in `Level2_GeometryRoute` and `Level3_GeometryRoute`.
