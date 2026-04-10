import Lake
open Lake DSL

package «ast_levels» where
  -- Keep the package rooted at the repository top level so the new
  -- `AST_levels/...` tree can coexist with legacy files during migration.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ s!"v{Lean.versionString}"

lean_lib AST_levels where
  -- The default source directory `.` matches the current folder layout.
