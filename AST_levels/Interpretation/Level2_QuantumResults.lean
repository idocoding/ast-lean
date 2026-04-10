import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Topology.Algebra.Module.Basic
import AST_levels.Interpretation.Level2_QuantumBridge

open Filter

/-!
# AST.Level2.QuantumResults

Canonical theorem-facing home for the strongest currently stabilized
quantum-side results in the levelized AST tree.

This file is intentionally self-contained. It does not import the migration
compatibility layer.

- Boolean exclusion is proved directly from a minimal correction-dynamics
  package.
- Orthomodularity from SCEP is stated as a direct canonical theorem over a
  generic ortholattice with explicit factorisation hypotheses.
- The multiplicative-to-power and quadratic Born-rule steps remain explicit
  canonical closure records while their longer analytic proof is modernized.
-/

namespace AST
namespace Level2
namespace QuantumResults

universe u

/-- Minimal data needed for the internal Boolean-exclusion argument. -/
structure CorrectionDynamics (Cfg : Type u) where
  K : Cfg → ℝ
  step : Cfg → Cfg → Prop
  asymptotic_decay :
    ∀ C₁ C₂ C₃, step C₁ C₂ → step C₂ C₃ →
      K C₂ - K C₁ > K C₃ - K C₂

/-- Boolean-style event logic would force a single uniform capacity increment
along every correction step. -/
def IsBooleanLike {Cfg : Type u} (D : CorrectionDynamics Cfg) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∀ C₁ C₂, D.step C₁ C₂ → D.K C₂ - D.K C₁ = δ

/-- Closed nonclassicality result: asymptotically decaying correction steps
exclude a Boolean event logic with a single uniform capacity gain. -/
theorem boolean_event_logic_exclusion
    {Cfg : Type u}
    (D : CorrectionDynamics Cfg)
    (C₁ C₂ C₃ : Cfg)
    (h₁₂ : D.step C₁ C₂)
    (h₂₃ : D.step C₂ C₃) :
    ¬ IsBooleanLike D := by
  intro hB
  rcases hB with ⟨δ, _hδ, hconst⟩
  have hdecay := D.asymptotic_decay C₁ C₂ C₃ h₁₂ h₂₃
  have h12 : D.K C₂ - D.K C₁ = δ := hconst C₁ C₂ h₁₂
  have h23 : D.K C₃ - D.K C₂ = δ := hconst C₂ C₃ h₂₃
  rw [h12, h23] at hdecay
  exact lt_irrefl _ hdecay

/-- Generic ortholattice data used by the canonical orthomodularity theorem. -/
structure OrthoLattice where
  Event       : Type u
  le          : Event → Event → Prop
  meet        : Event → Event → Event
  join        : Event → Event → Event
  bot         : Event
  top         : Event
  compl       : Event → Event
  le_refl     : ∀ a, le a a
  le_trans    : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  meet_le_l   : ∀ a b, le (meet a b) a
  meet_le_r   : ∀ a b, le (meet a b) b
  le_join_l   : ∀ a b, le a (join a b)
  le_join_r   : ∀ a b, le b (join a b)
  join_le     : ∀ a b c, le a c → le b c → le (join a b) c
  meet_le     : ∀ a b c, le a b → le a c → le a (meet b c)
  bot_le      : ∀ a, le bot a
  le_top      : ∀ a, le a top
  compl_compl : ∀ a, compl (compl a) = a
  meet_compl  : ∀ a, meet a (compl a) = bot
  join_compl  : ∀ a, join a (compl a) = top
  compl_anti  : ∀ a b, le a b → le (compl b) (compl a)

def IsOrthomodular (L : OrthoLattice) : Prop :=
  ∀ a b : L.Event, L.le a b → b = L.join a (L.meet b (L.compl a))

def corrLE {Cfg : Type u} (step : Cfg → Cfg → Prop) (C C' : Cfg) : Prop :=
  Relation.ReflTransGen step C C'

/-- Direct canonical orthomodularity theorem from SCEP-style factorisation. -/
theorem scep_yields_orthomodularity
    {Cfg : Type u}
    (step : Cfg → Cfg → Prop)
    (L : OrthoLattice)
    (ev : L.Event → Cfg)
    (le_iff  : ∀ a b : L.Event, L.le a b ↔ corrLE step (ev a) (ev b))
    (join_corr : ∀ a b : L.Event, corrLE step (ev a) (ev (L.join a b)) ∧
                                  corrLE step (ev b) (ev (L.join a b)))
    (_meet_corr : ∀ a b : L.Event,
        ∀ C, corrLE step C (ev a) → corrLE step C (ev b) → corrLE step C (ev (L.meet a b)))
    (_compl_sector : ∀ a : L.Event,
        ∀ C, corrLE step C (ev L.top) →
        ¬ corrLE step C (ev a) →
        corrLE step C (ev (L.compl a)))
    (scep_factor : ∀ a b : L.Event, L.le a b →
        ∀ C, corrLE step (ev L.bot) C → corrLE step C (ev b) →
        corrLE step C (ev a) ∨ corrLE step (ev (L.compl a)) (ev (L.meet b (L.compl a)))) :
    IsOrthomodular L := by
  intro a b hab
  have cT : ∀ {C C' C'' : Cfg}, corrLE step C C' → corrLE step C' C'' → corrLE step C C'' :=
    fun h1 h2 => h1.trans h2
  apply L.le_antisymm
  ·
    have h_bot_b : corrLE step (ev L.bot) (ev b) := (le_iff L.bot b).mp (L.bot_le b)
    have h_b_refl : corrLE step (ev b) (ev b) := Relation.ReflTransGen.refl
    have h_join_r := (join_corr a (L.meet b (L.compl a))).2
    rcases scep_factor a b hab (ev b) h_bot_b h_b_refl with h_ba | h_compl
    ·
      have hab' : L.le b a := (le_iff b a).mpr h_ba
      exact L.le_trans _ _ _ hab' (L.le_join_l a (L.meet b (L.compl a)))
    ·
      rw [le_iff]
      have h_compl_le_b : L.le (L.compl a) b := by
        rw [le_iff]
        exact cT h_compl ((le_iff (L.meet b (L.compl a)) b).mp (L.meet_le_l b (L.compl a)))
      have h_top_le_b : L.le L.top b := by
        simpa [L.join_compl a] using (L.join_le a (L.compl a) b hab h_compl_le_b)
      have hb_top : b = L.top := L.le_antisymm _ _ (L.le_top b) h_top_le_b
      subst hb_top
      have h_meet_top : L.meet L.top (L.compl a) = L.compl a :=
        L.le_antisymm _ _
          (L.meet_le_r L.top (L.compl a))
          (L.meet_le _ _ _ (L.le_top _) (L.le_refl _))
      rw [h_meet_top, L.join_compl]
      exact Relation.ReflTransGen.refl
  ·
    exact L.join_le _ _ _ hab (L.meet_le_l b (L.compl a))

/-- Multiplicative weight assignment on the unit interval. -/
def SatisfiesMultiplicativity (f : ℝ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → f (a * b) = f a * f b

/-- Normalization of branch weights on unit vectors. -/
def SatisfiesNormalization (f : ℝ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → ∀ c : Fin n → ℝ,
    (∀ i, 0 ≤ c i) → (∀ i, c i ≤ 1) →
    ∑ i, (c i)^2 = 1 → ∑ i, f (c i) = 1

/-- Continuous additive maps `ℝ → ℝ` are linear. -/
theorem continuous_additive_linear (φ : ℝ → ℝ)
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hcont : Continuous φ) :
    ∀ x : ℝ, φ x = x * φ 1 := by
  have hφ0 : φ 0 = 0 := by
    have := hadd 0 0
    simp at this
    linarith
  let fAdd : ℝ →+ ℝ :=
    { toFun := φ
      map_zero' := hφ0
      map_add' := hadd }
  have h_rat : ∀ q : ℚ, φ q = q * φ 1 := by
    intro q
    simpa [fAdd] using (map_rat_smul fAdd q (1 : ℝ))
  have hS_cl : IsClosed {t : ℝ | φ t = t * φ 1} :=
    isClosed_eq hcont (continuous_id.mul continuous_const)
  have hS_Q : Set.range ((↑) : ℚ → ℝ) ⊆ {t : ℝ | φ t = t * φ 1} :=
    fun _ ⟨q, hq⟩ => hq ▸ h_rat q
  have hS_dense : Dense {t : ℝ | φ t = t * φ 1} :=
    Rat.isDenseEmbedding_coe_real.dense.mono hS_Q
  intro x
  exact hS_cl.closure_subset (hS_dense x)

lemma mul_pow_eq (f : ℝ → ℝ) (hm : SatisfiesMultiplicativity f) (hf1 : f 1 = 1) :
    ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f (x^n) = f x ^ n := by
  intro n
  induction n with
  | zero =>
      intro x hx0 hx1
      simp [hf1]
  | succ m ih =>
      intro x hx0 hx1
      rw [pow_succ, hm _ _ (pow_nonneg hx0 m) (pow_le_one₀ hx0 hx1) hx0 hx1, ih x hx0 hx1, pow_succ]

lemma f_zero_from_norm (f : ℝ → ℝ) (hf1 : f 1 = 1)
    (hf_norm : SatisfiesNormalization f) : f 0 = 0 := by
  set c : Fin 2 → ℝ := ![1, 0]
  have hcnn : ∀ i : Fin 2, 0 ≤ c i := by
    intro i
    fin_cases i <;> simp [c]
  have hc1 : ∀ i : Fin 2, c i ≤ 1 := by
    intro i
    fin_cases i <;> simp [c]
  have hcnorm : ∑ i : Fin 2, (c i)^2 = 1 := by
    simp [c, Fin.sum_univ_two]
  have heq : ∑ i : Fin 2, f (c i) = 1 := hf_norm 2 (by norm_num) c hcnn hc1 hcnorm
  simp [c, Fin.sum_univ_two, hf1] at heq
  linarith

lemma f_lt_one_of_lt_one (f : ℝ → ℝ) (hm : SatisfiesMultiplicativity f) (hf1 : f 1 = 1)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf0 : f 0 = 0)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) : f x < 1 := by
  by_contra h_lt
  have h_ge : 1 ≤ f x := le_of_not_gt h_lt
  have h_pow_ge : ∀ n : ℕ, 1 ≤ f (x ^ n) := by
    intro n
    rw [mul_pow_eq f hm hf1 n x hx0.le hx1.le]
    exact one_le_pow₀ h_ge
  have hx_pow_zero : Tendsto (fun n : ℕ => x ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hx0.le hx1
  have hx_pow_within : Tendsto (fun n : ℕ => x ^ n) atTop (nhdsWithin 0 (Set.Icc 0 1)) := by
    refine tendsto_nhdsWithin_iff.mpr ?_
    refine ⟨hx_pow_zero, Filter.Eventually.of_forall ?_⟩
    intro n
    exact ⟨pow_nonneg hx0.le n, pow_le_one₀ hx0.le hx1.le⟩
  have hzero_mem : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, by norm_num⟩
  have hcont0 : ContinuousWithinAt f (Set.Icc 0 1) 0 := by
    simpa using hf_cont (x := 0) hzero_mem
  have hfxn_zero : Tendsto (fun n : ℕ => f (x ^ n)) atTop (nhds 0) := by
    rw [← hf0]
    exact hcont0.tendsto.comp hx_pow_within
  have h_eventually : ∀ᶠ n in atTop, f (x ^ n) < 1 :=
    hfxn_zero.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  simp [Filter.eventually_atTop] at h_eventually
  obtain ⟨N, hN⟩ := h_eventually
  have h_large := h_pow_ge N
  linarith [hN N le_rfl]

/-- Logarithmic transform of a multiplicative weight on the negative half-line. -/
noncomputable def logWeight (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.log (f (Real.exp t))

/-- Symmetric extension of `logWeight` from `(-∞,0]` to all of `ℝ`. -/
noncomputable def logWeightFull (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t ≤ 0 then logWeight f t else -logWeight f (-t)

lemma logWeight_zero (f : ℝ → ℝ) (hf1 : f 1 = 1) :
    logWeight f 0 = 0 := by
  simp [logWeight, hf1]

lemma logWeight_add_nonpos (f : ℝ → ℝ)
    (hf_mult : SatisfiesMultiplicativity f)
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x) :
    ∀ s t : ℝ, s ≤ 0 → t ≤ 0 →
      logWeight f (s + t) = logWeight f s + logWeight f t := by
  intro s t hs ht
  simp only [logWeight, Real.exp_add]
  rw [hf_mult _ _ (Real.exp_pos s).le (Real.exp_le_one_iff.mpr hs)
      (Real.exp_pos t).le (Real.exp_le_one_iff.mpr ht)]
  rw [Real.log_mul (hf_pos _ (Real.exp_pos s) (Real.exp_le_one_iff.mpr hs)).ne'
      (hf_pos _ (Real.exp_pos t) (Real.exp_le_one_iff.mpr ht)).ne']

lemma logWeightFull_additive (f : ℝ → ℝ)
    (hf_mult : SatisfiesMultiplicativity f)
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x) :
    ∀ x y : ℝ, logWeightFull f (x + y) = logWeightFull f x + logWeightFull f y := by
  intro x y
  have hg_add := logWeight_add_nonpos f hf_mult hf_pos
  by_cases hx : x ≤ 0 <;> by_cases hy : y ≤ 0
  ·
    have hxy : x + y ≤ 0 := add_nonpos hx hy
    simp [logWeightFull, hx, hy, hxy, hg_add x y hx hy]
  ·
    have hy_pos : 0 < y := lt_of_not_ge hy
    by_cases hxy : x + y ≤ 0
    ·
      simp [logWeightFull, hx, hy, hxy]
      have hneg_y : -y ≤ 0 := by linarith
      have hk := hg_add (x + y) (-y) hxy hneg_y
      have hk' : logWeight f x = logWeight f (x + y) + logWeight f (-y) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk
      linarith
    ·
      have hxy_pos : 0 < x + y := lt_of_not_ge hxy
      have hneg_xy : -(x + y) ≤ 0 := by linarith
      have hk := hg_add (-(x + y)) x hneg_xy hx
      have hk' : logWeight f (-y) = logWeight f (-(x + y)) + logWeight f x := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk
      calc
        logWeightFull f (x + y)
            = -logWeight f (-(x + y)) := by
                simp [logWeightFull, hxy]
        _ = logWeight f x - logWeight f (-y) := by
              linarith
        _ = logWeightFull f x + logWeightFull f y := by
              simp [logWeightFull, hx, hy, sub_eq_add_neg]
  ·
    have hx_pos : 0 < x := lt_of_not_ge hx
    by_cases hxy : x + y ≤ 0
    ·
      simp [logWeightFull, hx, hy, hxy]
      have hneg_x : -x ≤ 0 := by linarith
      have hk := hg_add (x + y) (-x) hxy hneg_x
      have hk' : logWeight f y = logWeight f (x + y) + logWeight f (-x) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk
      linarith
    ·
      have hxy_pos : 0 < x + y := lt_of_not_ge hxy
      have hneg_xy : -(x + y) ≤ 0 := by linarith
      have hk := hg_add (-(x + y)) y hneg_xy hy
      have hk' : logWeight f (-x) = logWeight f (-(x + y)) + logWeight f y := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk
      calc
        logWeightFull f (x + y)
            = -logWeight f (-(x + y)) := by
                simp [logWeightFull, hxy]
        _ = -logWeight f (-x) + logWeight f y := by
              linarith
        _ = logWeightFull f x + logWeightFull f y := by
              simp [logWeightFull, hx, hy]
  ·
    have hx_pos : 0 < x := lt_of_not_ge hx
    have hy_pos : 0 < y := lt_of_not_ge hy
    have hxy_pos : 0 < x + y := by linarith
    have hneg_x : -x ≤ 0 := by linarith
    have hneg_y : -y ≤ 0 := by linarith
    have hk := hg_add (-x) (-y) hneg_x hneg_y
    have hk' : logWeight f (-(x + y)) = logWeight f (-x) + logWeight f (-y) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hk
    calc
      logWeightFull f (x + y)
          = -logWeight f (-(x + y)) := by
              simp [logWeightFull, not_le.mpr hxy_pos]
      _ = -logWeight f (-x) + -logWeight f (-y) := by
            linarith
      _ = logWeightFull f x + logWeightFull f y := by
            simp [logWeightFull, hx, hy]

lemma logWeight_continuousOn_nonpos (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x) :
    ContinuousOn (logWeight f) {x : ℝ | x ≤ 0} := by
  unfold logWeight
  refine Real.continuousOn_log.comp ?_ ?_
  ·
    exact hf_cont.comp Real.continuous_exp.continuousOn
      (by
        intro x hx
        exact ⟨(Real.exp_pos x).le, Real.exp_le_one_iff.mpr hx⟩)
  ·
    intro x hx
    exact (hf_pos (Real.exp x) (Real.exp_pos x) (Real.exp_le_one_iff.mpr hx)).ne'

lemma logWeightFull_continuous (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x)
    (hf_one : f 1 = 1) :
    Continuous (logWeightFull f) := by
  have hleft : ContinuousOn (logWeight f) {x : ℝ | x ≤ 0} :=
    logWeight_continuousOn_nonpos f hf_cont hf_pos
  have hright : ContinuousOn (fun x : ℝ => -logWeight f (-x)) {x : ℝ | 0 ≤ x} := by
    apply ContinuousOn.neg
    exact hleft.comp continuous_neg.continuousOn (by
      intro x hx
      have hx0 : 0 ≤ x := hx
      exact neg_nonpos.mpr hx0)
  refine continuous_if_le continuous_id continuous_const hleft hright ?_
  intro x hx_eq
  have hx0 : x = 0 := by linarith
  subst hx0
  simp [logWeight_zero, hf_one]

lemma logWeightFull_linear (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_mult : SatisfiesMultiplicativity f)
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x)
    (hf_one : f 1 = 1) :
    ∀ t : ℝ, logWeightFull f t = t * logWeightFull f 1 := by
  exact continuous_additive_linear (logWeightFull f)
    (logWeightFull_additive f hf_mult hf_pos)
    (logWeightFull_continuous f hf_cont hf_pos hf_one)

/-- Direct power-law closure from multiplicativity, positivity, continuity, and normalization. -/
theorem multiplicative_implies_power (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_mult : SatisfiesMultiplicativity f)
    (hf_pos : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x)
    (hf_one : f 1 = 1)
    (hf_norm : SatisfiesNormalization f) :
    ∃ k : ℝ, 0 < k ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = x ^ k := by
  have hf0 : f 0 = 0 := f_zero_from_norm f hf_one hf_norm
  set k : ℝ := logWeightFull f 1
  have hlin : ∀ t : ℝ, logWeightFull f t = t * k := by
    intro t
    simpa [k] using logWeightFull_linear f hf_cont hf_mult hf_pos hf_one t
  have hk_pos : 0 < k := by
    have h1e_pos : (0 : ℝ) < Real.exp (-1) := Real.exp_pos _
    have h1e_lt : Real.exp (-1) < 1 := by
      exact Real.exp_lt_one_iff.mpr (by norm_num)
    have hf1e_lt1 : f (Real.exp (-1)) < 1 :=
      f_lt_one_of_lt_one f hf_mult hf_one hf_cont hf0 (Real.exp (-1)) h1e_pos h1e_lt
    have hf1e_pos : 0 < f (Real.exp (-1)) := hf_pos _ h1e_pos h1e_lt.le
    have hk_eq : k = -Real.log (f (Real.exp (-1))) := by
      simp [k, logWeightFull, logWeight]
    rw [hk_eq]
    rw [neg_pos]
    simpa using (Real.log_lt_log hf1e_pos hf1e_lt1)
  refine ⟨k, hk_pos, ?_⟩
  intro x hx0 hx1
  by_cases hx : x = 0
  ·
    subst hx
    rw [hf0, Real.zero_rpow (ne_of_gt hk_pos)]
  have hx_pos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  have hlog_nonpos : Real.log x ≤ 0 := Real.log_nonpos hx0 hx1
  have hfull_eq : logWeightFull f (Real.log x) = logWeight f (Real.log x) := by
    simp [logWeightFull, hlog_nonpos]
  have hfx_pos : 0 < f x := hf_pos x hx_pos hx1
  have hfx_eq : f x = Real.exp (logWeight f (Real.log x)) := by
    simp only [logWeight, Real.exp_log hx_pos]
    exact (Real.exp_log hfx_pos).symm
  rw [hfx_eq, ← hfull_eq, hlin (Real.log x)]
  rw [Real.rpow_def_of_pos hx_pos, mul_comm]

theorem born_rule (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Set.Icc 0 1))
    (hf_mult : SatisfiesMultiplicativity f)
    (hf_pos  : ∀ x : ℝ, 0 < x → x ≤ 1 → 0 < f x)
    (hf_one  : f 1 = 1)
    (hf_norm : SatisfiesNormalization f) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = x ^ (2 : ℝ) := by
  obtain ⟨k, hk_pos, hk_pow⟩ :=
    multiplicative_implies_power f hf_cont hf_mult hf_pos hf_one hf_norm
  intro x hx0 hx1
  rw [hk_pow x hx0 hx1]
  suffices hk_two : k = 2 by rw [hk_two]
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set c : Fin 2 → ℝ := fun _ => 1 / Real.sqrt 2
  have hcnn : ∀ i : Fin 2, 0 ≤ c i := by
    intro i
    simp [c]
  have hc1 : ∀ i : Fin 2, c i ≤ 1 := by
    intro i
    simp [c]
    exact (inv_le_one₀ hsqrt2_pos).2
      (Real.one_le_sqrt.2 (by norm_num : (1 : ℝ) ≤ 2))
  have hcnorm : ∑ i : Fin 2, (c i)^2 = 1 := by
    simp [c, hsqrt2_sq]
  have hsum : ∑ i : Fin 2, f (c i) = 1 := hf_norm 2 (by norm_num) c hcnn hc1 hcnorm
  have hcpos : 0 < c 0 := by
    simp [c]
  have hpow_c : f ((Real.sqrt 2)⁻¹) = ((Real.sqrt 2)⁻¹) ^ k := by
    simpa [one_div] using hk_pow (1 / Real.sqrt 2) (hcnn 0) (hc1 0)
  simp [c] at hsum
  rw [hpow_c] at hsum
  have hhalf_inv : ((Real.sqrt 2)⁻¹) ^ k = 1 / 2 := by
    linarith
  have hhalf : (1 / Real.sqrt 2) ^ k = 1 / 2 := by
    simpa [one_div] using hhalf_inv
  have hone_over_pos : (0 : ℝ) < 1 / Real.sqrt 2 := by
    positivity
  have hlog : k * Real.log (1 / Real.sqrt 2) = Real.log (1 / 2) := by
    calc
      k * Real.log (1 / Real.sqrt 2) = Real.log ((1 / Real.sqrt 2) ^ k) := by
        rw [Real.log_rpow hone_over_pos]
      _ = Real.log (1 / 2) := by rw [hhalf]
  have hlog_lhs : Real.log (1 / Real.sqrt 2) = -(1 / 2 : ℝ) * Real.log 2 := by
    rw [Real.log_div one_ne_zero hsqrt2_pos.ne', Real.log_one,
      Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hlog_rhs : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div one_ne_zero (by norm_num : (2 : ℝ) ≠ 0), Real.log_one]
    ring
  rw [hlog_lhs, hlog_rhs] at hlog
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Canonical closure record for the multiplicative-to-power step. -/
structure PowerLawClosure (f : ℝ → ℝ) where
  exponent : ℝ
  exponent_pos : 0 < exponent
  power_law : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = x ^ exponent

/-- Canonical promoted multiplicativity-to-power statement for the Born-rule
route. The analytic proof still needs a dedicated modernization pass against the
current Mathlib API, but the public theorem surface records the exact closure
content. -/
theorem multiplicative_weights_are_power_law
    (f : ℝ → ℝ)
    (C : PowerLawClosure f) :
    ∃ k : ℝ, 0 < k ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = x ^ k := by
  exact ⟨C.exponent, C.exponent_pos, C.power_law⟩

/-- Canonical closure record for the quadratic Born-rule step. -/
structure QuadraticBornClosure (f : ℝ → ℝ) extends PowerLawClosure f where
  multiplicative : SatisfiesMultiplicativity f
  exponent_eq_two : exponent = 2

/-- Canonical quadratic Born-rule statement. -/
theorem born_rule_is_quadratic
    (f : ℝ → ℝ)
    (C : QuadraticBornClosure f) :
    ∀ x : ℝ, 0 ≤ x → x ≤ 1 → f x = x ^ (2 : ℝ) := by
  intro x hx0 hx1
  rw [C.power_law x hx0 hx1, C.exponent_eq_two]

end QuantumResults
end Level2
end AST
