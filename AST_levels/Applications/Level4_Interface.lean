/-!
# AST.Level4

Level 4 is reserved for phenomenology and confrontation with observation.
This includes predictions, empirical inputs, numerical estimates, and
comparisons with external experimental or cosmological data.
-/

namespace AST
namespace Level4

/-- Canonical statement of what belongs in Level 4. -/
def scope : List String :=
  [ "Predictions with empirical numbers or ranges"
  , "Comparison against observation or experiment"
  , "Model-vs-data tension analysis"
  , "Framework comparison and phenomenological consequences"
  , "Application-specific downstream theory notes"
  , "Corrected coupling-denominator formulas and phenomenological stability thresholds"
  , "Bridge-tagged numerical calibrations built on lower-level canonical formulas"
  ]

/-- Migration rule for material that uses observation or application-specific comparison. -/
def migrationRule : String :=
  "Move a theorem to Level 4 when it depends on empirical calibration, observed values, or application-specific comparison rather than on structural derivation alone."

end Level4
end AST
