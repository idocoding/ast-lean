# AST Levels

This is the canonical levelized AST module tree.

## Layout

- `Foundation/`
  Structural mathematics and correction dynamics.
- `Interpretation/`
  Emergence interfaces and theorem-facing interpretation results.
- `Physics/`
  Physical identifications and theory-specific bridge modules.
- `Applications/`
  Phenomenology, comparisons, and higher-level consequences.

## Public entry point

The public package root is:

- `AST_levels.lean`

It imports the canonical modules only.

## Naming policy

- Root namespace: `AST`
- Level namespaces: `AST.Level0`, `AST.Level1`, `AST.Level2`, `AST.Level3`, `AST.Level4`
- Physics interpretation names do not belong in Level 0.
- Level 2 carries interpretation and bridge structure.
- Level 3 carries named physical identifications.
- Level 4 carries application and phenomenology layers.
