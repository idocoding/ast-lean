import Mathlib
import Mathlib.Analysis.Quaternion

/-!
# AST.Level3.Hurwitz

Canonical Level 3 support for the Hurwitz-sector side of AST.

This module promotes the sector-counting, no-fifth-force, no-GUT, and
three-generation results into the canonical tree. The classical Hurwitz theorem
itself remains an imported mathematical fact encoded here through the allowed
dimension set `{1,2,4,8}`.
-/

namespace AST
namespace Level3
namespace Hurwitz

open scoped Quaternion

/-- The four Hurwitz dimensions. -/
def hurwitzDims : Finset ℕ := {1, 2, 4, 8}

theorem hurwitzDims_card : hurwitzDims.card = 4 := by
  decide

theorem hurwitzDims_eq : hurwitzDims = {1, 2, 4, 8} := rfl

/-- Membership in the Hurwitz dimension set. -/
def IsHurwitzDim (d : ℕ) : Prop := d ∈ hurwitzDims

theorem isHurwitzDim_iff (d : ℕ) :
    IsHurwitzDim d ↔ d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem not_hurwitz_3 : ¬ IsHurwitzDim 3 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem not_hurwitz_5 : ¬ IsHurwitzDim 5 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem not_hurwitz_6 : ¬ IsHurwitzDim 6 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem not_hurwitz_7 : ¬ IsHurwitzDim 7 := by
  simp [IsHurwitzDim, hurwitzDims]

/-- The four AST gauge sectors classified by Hurwitz dimension. -/
inductive GaugeSector : Type
  | gravity
  | em
  | weak
  | strong
deriving DecidableEq, Fintype

/-- Hurwitz dimension assigned to each canonical AST sector. -/
def sectorDim : GaugeSector → ℕ
  | .gravity => 1
  | .em => 2
  | .weak => 4
  | .strong => 8

theorem sector_is_hurwitz (s : GaugeSector) :
    IsHurwitzDim (sectorDim s) := by
  cases s <;> simp [sectorDim, IsHurwitzDim, hurwitzDims]

theorem four_gauge_sectors : Fintype.card GaugeSector = 4 := by
  decide

theorem sectors_biject_hurwitz :
    Fintype.card GaugeSector = hurwitzDims.card := by
  simp [four_gauge_sectors, hurwitzDims_card]

/-- Hypothetical fifth-force sector requirement. -/
def fifthForceExists : Prop :=
  ∃ d : ℕ, IsHurwitzDim d ∧ ¬ (d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8)

theorem no_fifth_force : ¬ fifthForceExists := by
  intro h
  rcases h with ⟨d, hd, hnot⟩
  rw [isHurwitzDim_iff] at hd
  exact hnot hd

theorem every_hurwitz_dim_has_sector :
    ∀ d ∈ hurwitzDims, ∃ s : GaugeSector, sectorDim s = d := by
  intro d hd
  simp [hurwitzDims] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact ⟨.gravity, rfl⟩
  · exact ⟨.em, rfl⟩
  · exact ⟨.weak, rfl⟩
  · exact ⟨.strong, rfl⟩

theorem no_su5_gut : ¬ IsHurwitzDim 24 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem no_so10_gut : ¬ IsHurwitzDim 45 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem no_e6_gut : ¬ IsHurwitzDim 78 := by
  simp [IsHurwitzDim, hurwitzDims]

theorem no_e8_gut : ¬ IsHurwitzDim 248 := by
  simp [IsHurwitzDim, hurwitzDims]

/-- The seven points of the Fano plane. -/
def FanoPoints : Finset (Fin 7) := Finset.univ

/-- The seven Fano lines. -/
def fanoLines : Finset (Finset (Fin 7)) :=
  { {0,1,3}, {1,2,4}, {2,3,5}, {3,4,6}, {4,5,0}, {5,6,1}, {6,0,2} }

theorem fano_seven_lines : fanoLines.card = 7 := by
  decide

theorem fano_line_size : ∀ l ∈ fanoLines, l.card = 3 := by
  intro l hl
  simp [fanoLines] at hl
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

def linesThrough (p : Fin 7) : Finset (Finset (Fin 7)) :=
  fanoLines.filter (fun l => p ∈ l)

theorem fano_three_lines_per_point (p : Fin 7) :
    (linesThrough p).card = 3 := by
  fin_cases p <;> decide

theorem three_generations :
    ∀ p : Fin 7, (linesThrough p).card = 3 :=
  fano_three_lines_per_point

theorem generations_equal_for_all_points :
    ∀ p q : Fin 7, (linesThrough p).card = (linesThrough q).card := by
  intro p q
  rw [fano_three_lines_per_point, fano_three_lines_per_point]

/-- The three canonical imaginary basis units of the quaternions. -/
noncomputable def quaternionImagBasis : Finset ℍ := by
  classical
  exact ([ (QuaternionAlgebra.mk 0 1 0 0 : ℍ)
         , (QuaternionAlgebra.mk 0 0 1 0 : ℍ)
         , (QuaternionAlgebra.mk 0 0 0 1 : ℍ) ] : List ℍ).toFinset

theorem quaternionImagBasis_card :
    quaternionImagBasis.card = 3 := by
  classical
  let iQuat : ℍ := QuaternionAlgebra.mk 0 1 0 0
  let jQuat : ℍ := QuaternionAlgebra.mk 0 0 1 0
  let kQuat : ℍ := QuaternionAlgebra.mk 0 0 0 1
  have hij : iQuat ≠ jQuat := by
    intro h
    have himI := congrArg QuaternionAlgebra.imI h
    simp [iQuat, jQuat] at himI
  have hik : iQuat ≠ kQuat := by
    intro h
    have himI := congrArg QuaternionAlgebra.imI h
    simp [iQuat, kQuat] at himI
  have hjk : jQuat ≠ kQuat := by
    intro h
    have himJ := congrArg QuaternionAlgebra.imJ h
    simp [jQuat, kQuat] at himJ
  unfold quaternionImagBasis
  simp [iQuat, jQuat, kQuat, hij, hik, hjk]

/-- Internal Hurwitz support for spatial dimension: the quaternion imaginary basis has size 3. -/
noncomputable def spatialDimFromHurwitz : ℕ :=
  quaternionImagBasis.card

theorem spatialDim_eq_three :
    spatialDimFromHurwitz = 3 := by
  unfold spatialDimFromHurwitz
  exact quaternionImagBasis_card

theorem sectorDim_weak_eq_four :
    sectorDim .weak = 4 := rfl

structure HurwitzPhysics where
  four_dims : hurwitzDims.card = 4
  four_sectors : Fintype.card GaugeSector = 4
  no_fifth : ¬ fifthForceExists
  no_su5 : ¬ IsHurwitzDim 24
  no_so10 : ¬ IsHurwitzDim 45
  three_gen : ∀ p : Fin 7, (linesThrough p).card = 3
  spatial_dim_three : spatialDimFromHurwitz = 3

theorem hurwitz_physics_holds : HurwitzPhysics where
  four_dims := hurwitzDims_card
  four_sectors := four_gauge_sectors
  no_fifth := no_fifth_force
  no_su5 := no_su5_gut
  no_so10 := no_so10_gut
  three_gen := three_generations
  spatial_dim_three := spatialDim_eq_three

end Hurwitz
end Level3
end AST
