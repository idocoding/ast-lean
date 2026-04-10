# AST Lean

This repository is the public Lean package for the levelized Admissible
Structure Theory (AST) codebase.

## Package layout

- `AST_levels/Foundation/`
  Structural mathematics, substrate definitions, correction dynamics, and
  beta-flow.
- `AST_levels/Interpretation/`
  Emergence interfaces and theorem-facing interpretation results.
- `AST_levels/Physics/`
  Physical identifications and theory-specific bridge modules.
- `AST_levels/Applications/`
  Holography, inflation, proton stability, and fine-structure application
  modules.

## Entry point

- `AST_levels.lean`
  Imports the canonical public theorem surface.

## Build

```bash
lake build AST_levels
```

## Repository Metadata

- License: see [LICENSE](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/LICENSE)
- Citation metadata: see [CITATION.cff](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/CITATION.cff)
- Theorem/status overview: see [THEOREM_STATUS.md](/Users/harishkumar/KagazKala/VSCode/ast-lean/ast-public/THEOREM_STATUS.md)

## Scope

This package is the code reference target for the AST paper series. The public
modules are organized by semantic level so that structural results, emergence
results, physics identifications, and application-level consequences can be
cited independently.
