# Theorem Status Map

This file is a concise guide to what the public AST Lean subset currently
establishes and what it still records as explicit bridge or assumption
structure.

## Status labels

- `Theorem`: proved directly in the canonical public modules.
- `Bridge`: represented canonically, but still depends on an explicit
  interpretation or external mathematical bridge.
- `Open`: planned but not yet closed in the public canonical tree.

## Foundation

- `Theorem`: finite involution substrate and boundary/interior partition in
  [Level0.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Foundation/Level0.lean)
- `Theorem`: `Dist(C) = 2^{|σBdry(C)|}` / `K = log Dist` structural package in
  [Level0.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Foundation/Level0.lean)
- `Theorem`: discrete `K` spectrum, `log 2` gap, and closed-region minimum in
  [Level0.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Foundation/Level0.lean)
- `Theorem`: correction-step monotonicity and iterate nonincrease in
  [Level1_Correction.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Foundation/Level1_Correction.lean)
- `Theorem`: beta-flow fixed-point structure in
  [Level1_BetaFlow.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Foundation/Level1_BetaFlow.lean)

## Interpretation

- `Theorem`: Boolean event-logic exclusion in
  [Level2_QuantumResults.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_QuantumResults.lean)
- `Theorem`: orthomodularity from SCEP in
  [Level2_QuantumResults.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_QuantumResults.lean)
- `Theorem`: multiplicative-to-power closure and direct quadratic Born rule in
  [Level2_QuantumResults.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_QuantumResults.lean)
- `Bridge`: Hilbert-space and Born-rule emergence packages are represented in
  [Level2_QuantumBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_QuantumBridge.lean)
- `Bridge`: manifold/spacetime emergence is represented canonically in
  [Level2_ManifoldBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_ManifoldBridge.lean)
  and
  [Level2_SpacetimeBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_SpacetimeBridge.lean),
  with the established classical route bundled in
  [Level2_GeometryRoute.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_GeometryRoute.lean)
  and an internal Hurwitz-based `d = 3` support path packaged in
  [Level2_ManifoldBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_ManifoldBridge.lean)
- `Bridge`: inflation interpretation formulas are represented in
  [Level2_InflationBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_InflationBridge.lean)

## Physics

- `Bridge`: GR large-scale limit and Lovelock route in
  [Level3_GRBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_GRBridge.lean)
  and
  [Level3_GeometryRoute.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_GeometryRoute.lean)
- `Theorem`: LQG kinematical comparison package in
  [Level3_LQG.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_LQG.lean)
- `Theorem`: tensor-mode counting used by the inflation paper in
  [Level3_TensorModes.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_TensorModes.lean)
- `Theorem`: soliton/worldsheet kinematics in
  [Level3_Soliton.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_Soliton.lean)
- `Theorem`: Hurwitz / no-fifth-force package in
  [Level3_Hurwitz.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_Hurwitz.lean)
  including the internal quaternion-imaginary-basis `3`-support

## Applications

- `Theorem`: holographic entropy package H1-H6 and Newton-constant matching in
  [Holography.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Applications/Holography.lean)
- `Theorem`: corrected fine-structure denominator
  `1/α = 4πσ_min - log 2 - 1/2`, corrected positivity, and tight corrected window in
  [AlphaEstimate.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Applications/AlphaEstimate.lean)
- `Bridge`: inflation observables package in
  [Inflation.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Applications/Inflation.lean)
- `Theorem`: proton-stability package in
  [ProtonStability.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Applications/ProtonStability.lean),
  now explicitly linked to the Hurwitz/Fano `σ_min = 11` count

## Main open items

- `Open`: internal manifold/spacetime emergence without explicit bridge records
- `Open`: full `d = 3` and GR closure without the current geometric bridges
- `Open`: inflation pivot derivation and complete tensor-ratio closure
- `Open`: 4D central-charge closure for the string paper
- `Open`: subleading correction that closes the remaining fine-structure gap

## Geometry chain

The large-scale geometry route is best read as a staged chain, not as a single
all-or-nothing theorem.

| Step | Current status | Lean home | Notes |
|---|---|---|---|
| `β = 1` shell/growth control | `Theorem` | [Level1_BetaFlow.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Foundation/Level1_BetaFlow.lean) and the promoted geometry bridge layer | This is the AST-side rate/growth input. |
| polynomial-growth to manifold emergence | `Bridge` | [Level2_ManifoldBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_ManifoldBridge.lean) | This currently depends on the classical Gromov/Kleiner polynomial-growth bridge. |
| strict Huygens to `d = 3` | `Bridge` | [Level2_SpacetimeBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_SpacetimeBridge.lean) | This currently depends on the classical Hadamard-Gunther theorem together with the AST-to-Huygens bridge. |
| internal Hurwitz support for `d = 3` | `Theorem` | [Level3_Hurwitz.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_Hurwitz.lean) and [Level2_ManifoldBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Interpretation/Level2_ManifoldBridge.lean) | This gives an internal quaternion-based `3`-support path alongside the classical bridge route. |
| GR uniqueness in `3+1` dimensions | `Bridge` | [Level3_GRBridge.lean](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/AST_levels/Physics/Level3_GRBridge.lean) | This currently depends on Lovelock as a cited classical theorem after the manifold and dimension bridges are in place. |

The bridge steps above are not placeholders for unknown AST mathematics. They
are explicit interfaces to established external mathematical theorems.
