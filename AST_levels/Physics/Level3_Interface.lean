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
