import AST_levels.Foundation.Level0

/-!
# AST.Level4.Holography

Canonical Paper-0/Paper-3 support for the holographic entropy side of AST.

This module promotes the strongest existing legacy clean results into the
canonical `AST_levels` tree.
-/

open Real

universe u

namespace AST
namespace Level4
namespace Holography

open Level0
open SigmaStructure

variable {X : Type u} [DecidableEq X] [Fintype X] [Level0.SigmaStructure X]

theorem H1_empty_zero :
    Level0.K (∅ : Finset X) = 0 := by
  simp [Level0.K, Level0.sigmaBoundary]

theorem H2_nonneg (A : Finset X) :
    0 ≤ Level0.K A :=
  Level0.K_nonneg A

theorem sigmaBoundary_compl_card (A : Finset X) :
    (Level0.sigmaBoundary A).card = (Level0.sigmaBoundary Aᶜ).card := by
  apply Finset.card_bij (fun x _ => sigma x)
  · intro x hx
    simp [Level0.sigmaBoundary] at hx ⊢
    obtain ⟨hxA, hσxA⟩ := hx
    constructor
    · simpa [Finset.mem_compl] using hσxA
    · simpa [sigma_inv x] using hxA
  · intro x hx y hy hxy
    exact Function.Involutive.injective sigma_inv hxy
  · intro y hy
    simp [Level0.sigmaBoundary] at hy ⊢
    obtain ⟨hyAc, hσyAc⟩ := hy
    refine ⟨sigma y, ?_, ?_⟩
    · constructor
      · simpa [Finset.mem_compl] using hσyAc
      · simpa [sigma_inv y] using hyAc
    · exact sigma_inv y

theorem H3_purification (A : Finset X) :
    Level0.K A = Level0.K Aᶜ := by
  rw [Level0.K, Level0.K, sigmaBoundary_compl_card]

theorem sigmaBoundary_union_subset (A B : Finset X) :
    Level0.sigmaBoundary (A ∪ B) ⊆ Level0.sigmaBoundary A ∪ Level0.sigmaBoundary B := by
  intro x hx
  simp [Level0.sigmaBoundary] at hx ⊢
  obtain ⟨hxAB, hσxAB⟩ := hx
  have hσxA : sigma x ∉ A := hσxAB.1
  have hσxB : sigma x ∉ B := hσxAB.2
  cases hxAB with
  | inl h =>
      exact Or.inl ⟨h, hσxA⟩
  | inr h =>
      exact Or.inr ⟨h, hσxB⟩

theorem H4_subadditivity (A B : Finset X) :
    Level0.K (A ∪ B) ≤ Level0.K A + Level0.K B := by
  simp only [Level0.K]
  have hsubset := sigmaBoundary_union_subset A B
  have hcard :
      (Level0.sigmaBoundary (A ∪ B)).card ≤ (Level0.sigmaBoundary A ∪ Level0.sigmaBoundary B).card :=
    Finset.card_le_card hsubset
  have hunion :
      (Level0.sigmaBoundary A ∪ Level0.sigmaBoundary B).card
        ≤ (Level0.sigmaBoundary A).card + (Level0.sigmaBoundary B).card :=
    Finset.card_union_le _ _
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  calc
    (Level0.sigmaBoundary (A ∪ B)).card * Real.log 2
        ≤ ((Level0.sigmaBoundary A).card + (Level0.sigmaBoundary B).card) * Real.log 2 := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Nat.le_trans hcard hunion
          · exact hlog
    _ = (Level0.sigmaBoundary A).card * Real.log 2 +
        (Level0.sigmaBoundary B).card * Real.log 2 := by ring

theorem sigmaBoundary_SSA_per_element (A B : Finset X) (x : X) :
    (if x ∈ Level0.sigmaBoundary A then 1 else 0) +
        (if x ∈ Level0.sigmaBoundary B then 1 else 0) ≥
      (if x ∈ Level0.sigmaBoundary (A ∪ B) then 1 else 0) +
        (if x ∈ Level0.sigmaBoundary (A ∩ B) then 1 else 0) := by
  simp only [Level0.sigmaBoundary, Finset.mem_filter, Finset.mem_union, Finset.mem_inter]
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
  by_cases hσA : sigma x ∈ A <;> by_cases hσB : sigma x ∈ B <;>
  simp_all

theorem sigmaBoundary_card_SSA (A B : Finset X) :
    (Level0.sigmaBoundary A).card + (Level0.sigmaBoundary B).card ≥
      (Level0.sigmaBoundary (A ∪ B)).card + (Level0.sigmaBoundary (A ∩ B)).card := by
  classical
  have key : ∀ x : X,
      (if x ∈ Level0.sigmaBoundary A then 1 else 0) +
          (if x ∈ Level0.sigmaBoundary B then 1 else 0) ≥
        (if x ∈ Level0.sigmaBoundary (A ∪ B) then 1 else 0) +
          (if x ∈ Level0.sigmaBoundary (A ∩ B) then 1 else 0) :=
    sigmaBoundary_SSA_per_element A B
  have hA :
      (Level0.sigmaBoundary A).card =
        ∑ x : X, if x ∈ Level0.sigmaBoundary A then 1 else 0 := by
    simp
  have hB :
      (Level0.sigmaBoundary B).card =
        ∑ x : X, if x ∈ Level0.sigmaBoundary B then 1 else 0 := by
    simp
  have hAuB :
      (Level0.sigmaBoundary (A ∪ B)).card =
        ∑ x : X, if x ∈ Level0.sigmaBoundary (A ∪ B) then 1 else 0 := by
    simp
  have hAiB :
      (Level0.sigmaBoundary (A ∩ B)).card =
        ∑ x : X, if x ∈ Level0.sigmaBoundary (A ∩ B) then 1 else 0 := by
    simp
  rw [hA, hB, hAuB, hAiB]
  simpa [Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc] using
    (Finset.sum_le_sum
      (s := Finset.univ)
      (f := fun x : X =>
        (if x ∈ Level0.sigmaBoundary (A ∪ B) then 1 else 0) +
          (if x ∈ Level0.sigmaBoundary (A ∩ B) then 1 else 0))
      (g := fun x : X =>
        (if x ∈ Level0.sigmaBoundary A then 1 else 0) +
          (if x ∈ Level0.sigmaBoundary B then 1 else 0))
      (fun x _ => key x))

theorem H5_strong_subadditivity (A B : Finset X) :
    Level0.K A + Level0.K B ≥ Level0.K (A ∪ B) + Level0.K (A ∩ B) := by
  unfold Level0.K
  have h := sigmaBoundary_card_SSA A B
  have hlog : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
  have hmul :
      (((Level0.sigmaBoundary (A ∪ B)).card + (Level0.sigmaBoundary (A ∩ B)).card : ℝ) * Real.log 2)
        ≤
      (((Level0.sigmaBoundary A).card + (Level0.sigmaBoundary B).card : ℝ) * Real.log 2) := by
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast h
    · exact hlog
  linarith

theorem H6_RT_formula (A : Finset X) :
    Level0.K A = (Level0.sigmaBoundary A).card * Real.log 2 := rfl

structure HolographicEntropyWitness where
  empty_zero : Level0.K (∅ : Finset X) = 0
  nonneg : ∀ A : Finset X, 0 ≤ Level0.K A
  purification : ∀ A : Finset X, Level0.K A = Level0.K Aᶜ
  subadditive : ∀ A B : Finset X, Level0.K (A ∪ B) ≤ Level0.K A + Level0.K B
  strong_subadd :
    ∀ A B : Finset X, Level0.K A + Level0.K B ≥ Level0.K (A ∪ B) + Level0.K (A ∩ B)
  minimal_cut : ∀ A : Finset X, Level0.K A = (Level0.sigmaBoundary A).card * Real.log 2

theorem astK_is_holographic_entropy :
    HolographicEntropyWitness (X := X) where
  empty_zero := H1_empty_zero
  nonneg := H2_nonneg
  purification := H3_purification
  subadditive := H4_subadditivity
  strong_subadd := H5_strong_subadditivity
  minimal_cut := H6_RT_formula

/-- Newton's constant as fixed by the AST holographic entropy normalization. -/
noncomputable def G_Newton_AST : ℝ := 1 / (4 * Real.log 2)

theorem G_Newton_AST_pos : 0 < G_Newton_AST := by
  unfold G_Newton_AST
  apply div_pos
  · norm_num
  · apply mul_pos
    · norm_num
    · exact Real.log_pos one_lt_two

theorem bekenstein_hawking_exact (A : Finset X) :
    Level0.K A = (Level0.sigmaBoundary A).card * (1 : ℝ) / (4 * G_Newton_AST) := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  unfold G_Newton_AST Level0.K
  field_simp [hlog]

theorem newtonConstant_from_AST :
    let G_N := (1 : ℝ) / (4 * Real.log 2)
    ∀ A : Finset X,
      Level0.K A = (Level0.sigmaBoundary A).card * (1 : ℝ) / (4 * G_N) := by
  intro G_N A
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  simp [Level0.K, G_N]
  field_simp [hlog]

theorem G_Newton_uniqueness_from_boundary_unit
    {G : ℝ} (hG : 0 < G)
    (hunit : Real.log 2 = (1 : ℝ) / (4 * G)) :
    G = G_Newton_AST := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos one_lt_two)
  have hG0 : G ≠ 0 := ne_of_gt hG
  unfold G_Newton_AST
  apply (eq_div_iff (show (4 : ℝ) * Real.log 2 ≠ 0 by positivity)).2
  have hmul := congrArg (fun t : ℝ => t * (4 * G)) hunit
  have hunit' : Real.log 2 * (4 * G) = 1 := by
    simpa [hG0, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul
  nlinarith

theorem holographic_principle (A : Finset X) :
    Level0.K A = (Level0.sigmaBoundary A).card * Real.log 2 := rfl

theorem mutualInfo_nonneg (A B : Finset X) :
    0 ≤ Level0.K A + Level0.K B - Level0.K (A ∪ B) := by
  linarith [H4_subadditivity A B]

end Holography
end Level4
end AST
