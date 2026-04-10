import AST_levels.Applications.Level4_Interface
import AST_levels.Physics.Level3_Hurwitz
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

/-!
# AST.Level4.ProtonStability

Canonical Level 4 support for the proton-stability branch of the AST
phenomenology programme.

The stronger Fano-coherence derivation still belongs to the wider octonionic
sector story, but the current Lean-backed stability chain can already be stated
cleanly and conditionally in the canonical tree.
-/

open Real

namespace AST
namespace Level4
namespace ProtonStability

/-- Fano-sector stability factor. -/
noncomputable def fFano : ℝ := 1 / Real.sqrt 3

/-- Stability threshold. -/
noncomputable def fStable : ℝ := 1 / Real.sqrt 2

theorem fano_below_threshold : fFano < fStable := by
  unfold fFano fStable
  apply div_lt_div_of_pos_left one_pos
  · exact Real.sqrt_pos.mpr (by norm_num)
  · apply Real.sqrt_lt_sqrt <;> norm_num

variable (σ_min : ℕ)

/-- Electron-sector stability factor. -/
noncomputable def fElectron : ℝ := 1 / Real.sqrt σ_min

theorem fElectron_pos (hσ : 0 < σ_min) : 0 < fElectron σ_min := by
  unfold fElectron
  apply div_pos one_pos
  exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr hσ)

theorem electron_stable (hσ2 : 2 < σ_min) :
    fElectron σ_min < fStable := by
  unfold fElectron fStable
  apply div_lt_div_of_pos_left one_pos
  · exact Real.sqrt_pos.mpr (by norm_num)
  · apply Real.sqrt_lt_sqrt (by norm_num)
    exact_mod_cast hσ2

/-- Effective proton stability factor in the current AST phenomenology layer. -/
noncomputable def fProton : ℝ := 1 / Real.sqrt σ_min

theorem proton_electron_same_factor :
    fProton σ_min = fElectron σ_min := rfl

theorem proton_absolutely_stable (hσ2 : 2 < σ_min) :
    fProton σ_min < fStable := by
  rw [proton_electron_same_factor]
  exact electron_stable σ_min hσ2

theorem proton_stable_sigma11 :
    fProton 11 < fStable := by
  exact proton_absolutely_stable 11 (by norm_num)

theorem hurwitz_forces_sigma_min_eleven :
    AST.Level3.Hurwitz.fanoLines.card +
      AST.Level3.Hurwitz.sectorDim AST.Level3.Hurwitz.GaugeSector.weak = 11 := by
  rw [AST.Level3.Hurwitz.fano_seven_lines, AST.Level3.Hurwitz.sectorDim_weak_eq_four]

def AbsolutelyStable (f : ℝ) : Prop := f < fStable

theorem no_proton_decay (hσ2 : 2 < σ_min) :
    AbsolutelyStable (fProton σ_min) :=
  proton_absolutely_stable σ_min hσ2

theorem no_proton_decay_11 :
    AbsolutelyStable (fProton 11) :=
  proton_stable_sigma11

theorem proton_stable_from_hurwitz :
    fProton 11 < fStable :=
  proton_stable_sigma11

theorem hurwitz_fano_implies_proton_stability :
    let σ_min := AST.Level3.Hurwitz.fanoLines.card +
      AST.Level3.Hurwitz.sectorDim AST.Level3.Hurwitz.GaugeSector.weak
    AbsolutelyStable (fProton σ_min) := by
  dsimp
  rw [hurwitz_forces_sigma_min_eleven]
  exact no_proton_decay_11

theorem no_electron_decay (hσ2 : 2 < σ_min) :
    AbsolutelyStable (fElectron σ_min) :=
  electron_stable σ_min hσ2

theorem proton_electron_stability_equivalent :
    AbsolutelyStable (fProton σ_min) ↔
    AbsolutelyStable (fElectron σ_min) := by
  simp [AbsolutelyStable, proton_electron_same_factor]

theorem ast_falsified_by_proton_decay (hσ2 : 2 < σ_min)
    (h_decay : ¬ AbsolutelyStable (fProton σ_min)) :
    False :=
  h_decay (no_proton_decay σ_min hσ2)

structure ProtonStabilityWitness where
  fanoBelowThreshold : fFano < fStable
  protonStableAt11 : AbsolutelyStable (fProton 11)
  hurwitzForcesEleven : AST.Level3.Hurwitz.fanoLines.card +
      AST.Level3.Hurwitz.sectorDim AST.Level3.Hurwitz.GaugeSector.weak = 11

theorem proton_stability_witness : ProtonStabilityWitness where
  fanoBelowThreshold := fano_below_threshold
  protonStableAt11 := no_proton_decay_11
  hurwitzForcesEleven := hurwitz_forces_sigma_min_eleven

end ProtonStability
end Level4
end AST
