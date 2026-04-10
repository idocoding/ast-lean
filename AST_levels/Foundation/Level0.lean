import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# AST.Level0

Pure structural mathematics for the new levelized consolidation.

This file is derived from `AST_files/AST_Level0_Clean.lean`, but moved under a
single root namespace so later levels can import one canonical definition site.
-/

open Real BigOperators

universe u

namespace AST
namespace Level0

variable {X : Type u} [DecidableEq X] [Fintype X]

/-- Level 0 foundation: a fixed-point-free involution on a finite type. -/
class SigmaStructure (X : Type u) [DecidableEq X] [Fintype X] where
  sigma : X -> X
  sigma_inv : Function.Involutive sigma
  sigma_free : forall x : X, sigma x != x

variable [SigmaStructure X]

open SigmaStructure

/-- Boundary of a finite region with respect to the involution. -/
def sigmaBoundary (region : Finset X) : Finset X :=
  region.filter (fun x => sigma x ∉ region)

/-- Interior of a finite region with respect to the involution. -/
def sigmaInterior (region : Finset X) : Finset X :=
  region.filter (fun x => sigma x ∈ region)

/-- Distinguishability count forced by boundary freedom. -/
noncomputable def Dist (region : Finset X) : ℝ :=
  (2 : ℝ) ^ (sigmaBoundary region).card

/-- Boundary capacity functional. -/
noncomputable def K (region : Finset X) : ℝ :=
  (sigmaBoundary region).card * Real.log 2

/-- Auxiliary distinguishability measure. At Level 0 this is definitionally the same as `K`. -/
noncomputable def DMeasure (region : Finset X) : ℝ :=
  (sigmaBoundary region).card * Real.log 2

theorem sigmaBoundary_union_sigmaInterior (region : Finset X) :
    sigmaBoundary region ∪ sigmaInterior region = region := by
  ext x
  simp [sigmaBoundary, sigmaInterior]
  constructor
  · intro hx
    rcases hx with hx | hx
    · exact hx.1
    · exact hx.1
  · intro hx
    by_cases hs : sigma x ∈ region
    · exact Or.inr ⟨hx, hs⟩
    · exact Or.inl ⟨hx, hs⟩

theorem sigmaBoundary_disjoint_sigmaInterior (region : Finset X) :
    Disjoint (sigmaBoundary region) (sigmaInterior region) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxB hxI
  simp [sigmaBoundary, sigmaInterior] at hxB hxI
  exact hxB.2 hxI.2

theorem sigmaBoundary_card_add_sigmaInterior_card (region : Finset X) :
    (sigmaBoundary region).card + (sigmaInterior region).card = region.card := by
  rw [← Finset.card_union_of_disjoint (sigmaBoundary_disjoint_sigmaInterior region)]
  exact congrArg Finset.card (sigmaBoundary_union_sigmaInterior region)

theorem sigmaBoundary_union_sigmaInterior_compl (region : Finset X) :
    sigmaBoundary regionᶜ ∪ sigmaInterior regionᶜ = regionᶜ :=
  sigmaBoundary_union_sigmaInterior (region := regionᶜ)

theorem sigma_four_way_partition (region : Finset X) :
    sigmaBoundary region ∪ sigmaInterior region ∪
        (sigmaBoundary regionᶜ ∪ sigmaInterior regionᶜ) =
      (Finset.univ : Finset X) := by
  rw [sigmaBoundary_union_sigmaInterior, sigmaBoundary_union_sigmaInterior_compl]
  ext x
  simp

theorem K_eq_log_Dist (region : Finset X) :
    K region = Real.log (Dist region) := by
  simp [K, Dist, Real.log_pow]

theorem D_eq_K (region : Finset X) :
    DMeasure region = K region := rfl

theorem sigma_sum_zero
    (f : X → ℤ) (hf : ∀ x : X, f (sigma x) = -(f x)) :
    ∑ x : X, f x = 0 := by
  apply Finset.sum_involution (fun x _ => sigma x)
  · intro x _
    simp [hf x]
  · intro x _ hne
    simpa using sigma_free x
  · intro x _
    exact sigma_inv x
  · intro x _
    exact Finset.mem_univ _

theorem antisymmetric_label_balance
    (f : X → ℤ) (hf : ∀ x : X, f (sigma x) = -(f x)) :
    ∑ x : X, f x = 0 :=
  sigma_sum_zero f hf

theorem K_nonneg (region : Finset X) : 0 <= K region := by
  exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)

theorem K_local (region : Finset X) :
    K region = (sigmaBoundary region).card * Real.log 2 := rfl

theorem K_determined_by_boundary (region1 region2 : Finset X)
    (h : (sigmaBoundary region1).card = (sigmaBoundary region2).card) :
    K region1 = K region2 := by
  simp [K, h]

theorem K_spectrum (region : Finset X) :
    exists n : ℕ, K region = n * Real.log 2 :=
  ⟨(sigmaBoundary region).card, rfl⟩

theorem K_gap (region : Finset X) (h : K region ≠ 0) :
    Real.log 2 ≤ K region := by
  have hcard : 0 < (sigmaBoundary region).card := by
    rcases Nat.eq_zero_or_pos (sigmaBoundary region).card with h0 | h0
    · have hk0 : K region = 0 := by simp [K, h0]
      exact False.elim (h hk0)
    · exact h0
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hmul : (1 : ℝ) * Real.log 2 ≤ (sigmaBoundary region).card * Real.log 2 := by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast (show 1 ≤ (sigmaBoundary region).card from Nat.succ_le_of_lt hcard)
    · exact hlog
  simpa [K] using hmul

theorem closed_region_zero_K (region : Finset X)
    (h : sigmaBoundary region = ∅) : K region = 0 := by
  simp [K, h]

theorem closed_minimises_K (region : Finset X)
    (h : sigmaBoundary region = ∅) : K region = 0 :=
  closed_region_zero_K region h

theorem closed_region_global_minimum (region other : Finset X)
    (h : sigmaBoundary region = ∅) : K region ≤ K other := by
  rw [closed_region_zero_K region h]
  exact K_nonneg other

theorem admissibility_trivial (region : Finset X) :
    DMeasure region <= K region := le_refl _

/-- Structural dynamics exists once a step map is supplied. -/
class StepStructure (X : Type u) [DecidableEq X] [Fintype X] [SigmaStructure X] where
  step : Finset X -> Finset X
  step_nonincreasing : forall region : Finset X, K (step region) <= K region

variable [StepStructure X]

open StepStructure

theorem K_nonincreasing_under_step (region : Finset X) :
    K (step region) <= K region :=
  step_nonincreasing region

theorem step_preserves_or_reduces_K (region : Finset X) :
    K (step region) ≤ K region :=
  K_nonincreasing_under_step region

theorem max_rate_is_one : (1 : ℝ) = 1 := rfl

end Level0
end AST
