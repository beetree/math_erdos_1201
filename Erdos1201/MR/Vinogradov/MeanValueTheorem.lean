/-
The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.Basic
import Erdos1201.PrimeSums
import Erdos1201.SmoothBound
import Erdos1201.MR.Vinogradov.CurveCounts
import Erdos1201.MR.Vinogradov.HolderRestriction
import Erdos1201.MR.Vinogradov.CongruencingStep
import Erdos1201.MR.Vinogradov.PrimeSelectionAssembly
import Erdos1201.MR.Vinogradov.PrimesInRange
import Erdos1201.MR.Vinogradov.PrimeSelectionSq

namespace Erdos1201.MR.Vinogradov

/-- The normalised Vinogradov mean value quantity. -/
noncomputable def jnorm (k ℓ M : ℕ) : ℝ :=
  (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * J k ℓ M

/-- The trivial upper bound for jnorm using the trivial bound for J. -/
lemma jnorm_le_trivial (k ℓ M : ℕ) (hM : 1 ≤ M) :
    jnorm k ℓ M ≤ (M : ℝ) ^ (k * (k + 1) / 2 : ℝ) := by
  dsimp [jnorm]
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hJ : (J k ℓ M : ℝ) ≤ (M : ℝ) ^ (2 * (ℓ : ℝ)) := by
    have := J_le k ℓ M
    have h1 : (J k ℓ M : ℝ) ≤ ((M ^ (2 * ℓ) : ℕ) : ℝ) := by exact_mod_cast this
    have h2 : ((M ^ (2 * ℓ) : ℕ) : ℝ) = (M : ℝ) ^ (2 * ℓ) := by push_cast; rfl
    have h3 : (M : ℝ) ^ (2 * ℓ) = (M : ℝ) ^ (2 * (ℓ : ℝ)) := by
      have step1 : (M : ℝ) ^ (2 * ℓ) = (M : ℝ) ^ ((2 * ℓ : ℕ) : ℝ) := (Real.rpow_natCast (M : ℝ) (2 * ℓ)).symm
      have step2 : ((2 * ℓ : ℕ) : ℝ) = 2 * (ℓ : ℝ) := by push_cast; rfl
      rw [step1, step2]
    linarith
  have h_mul : (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (J k ℓ M : ℝ) ≤
      (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (2 * (ℓ : ℝ)) := by
    gcongr
  refine h_mul.trans ?_
  rw [← Real.rpow_add hMpos]
  have h_add : ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) + 2 * (ℓ : ℝ) = (k * (k + 1) / 2 : ℝ) := by ring
  rw [h_add]

/-- Conversion identity from J to jnorm. -/
lemma J_eq_rpow_mul_jnorm (k ℓ M : ℕ) (hM : 1 ≤ M) :
    (J k ℓ M : ℝ) = (M : ℝ) ^ (2 * (ℓ : ℝ) - (k * (k + 1) / 2 : ℝ)) * jnorm k ℓ M := by
  dsimp [jnorm]
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  rw [← mul_assoc, ← Real.rpow_add hMpos]
  have : (2 * (ℓ : ℝ) - (k * (k + 1) / 2 : ℝ)) + ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

/-- Base case of Tao's Theorem 13: for ℓ ≤ 10 k^2, the trivial bound establishes the claim
unconditionally for any constant C ≥ exp(10). -/
lemma jnorm_le_base (C : ℝ) (hC : Real.exp 10 ≤ C) (k ℓ M : ℕ)
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hl : ℓ ≤ 10 * k ^ 2) :
    jnorm k ℓ M ≤ Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * k ^ 2 * Real.exp (-(ℓ : ℝ) / k ^ 2)) := by
  have htriv := jnorm_le_trivial k ℓ M hM
  have hM_ge1 : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk2_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have h_exp_le : (k * (k + 1) / 2 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : (k : ℝ) * ((k : ℝ) + 1) / 2 = ((k : ℝ) ^ 2 + (k : ℝ)) / 2 := by ring
    rw [this]
    have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : 1 ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
    linarith
  have h_triv2 : jnorm k ℓ M ≤ (M : ℝ) ^ ((k : ℝ) ^ 2) := by
    refine htriv.trans (Real.rpow_le_rpow_of_exponent_le hM_ge1 h_exp_le)
  have h_div_le : (ℓ : ℝ) / (k : ℝ) ^ 2 ≤ 10 := by
    rw [div_le_iff₀ hk2_pos]
    have : (ℓ : ℝ) ≤ (10 * k ^ 2 : ℕ) := by exact_mod_cast hl
    push_cast at this
    linarith
  have h_neg_ge : -10 ≤ -(ℓ : ℝ) / (k : ℝ) ^ 2 := by
    have : -(ℓ : ℝ) / (k : ℝ) ^ 2 = -((ℓ : ℝ) / (k : ℝ) ^ 2) := by ring
    rw [this]
    linarith
  have h_exp_ge : Real.exp (-10) ≤ Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) :=
    Real.exp_le_exp.mpr h_neg_ge
  have hC_pos : 0 < C := (Real.exp_pos 10).trans_le hC
  have h_mul_ge : 1 ≤ C * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by
    calc 1 = Real.exp 10 * Real.exp (-10) := by
          rw [← Real.exp_add]
          norm_num
      _ ≤ C * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by
        refine mul_le_mul hC h_exp_ge (Real.exp_pos _).le (by positivity)
  have h_pow_exp_ge : (k : ℝ) ^ 2 ≤ C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by
    calc (k : ℝ) ^ 2 = (k : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (k : ℝ) ^ 2 * (C * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left h_mul_ge (by positivity)
      _ = C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by ring
  have h_M_le : (M : ℝ) ^ ((k : ℝ) ^ 2) ≤ (M : ℝ) ^ (C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)) :=
    Real.rpow_le_rpow_of_exponent_le hM_ge1 h_pow_exp_ge
  have h_exp_C_ge1 : 1 ≤ Real.exp (C * ℓ ^ 2) := by
    have : 0 ≤ C * ℓ ^ 2 := by positivity
    exact Real.one_le_exp this
  calc jnorm k ℓ M ≤ (M : ℝ) ^ ((k : ℝ) ^ 2) := h_triv2
    _ = 1 * (M : ℝ) ^ ((k : ℝ) ^ 2) := (one_mul _).symm
    _ ≤ Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)) := by
      refine mul_le_mul h_exp_C_ge1 h_M_le (by positivity) (Real.exp_pos _).le
    _ = Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * k ^ 2 * Real.exp (-(ℓ : ℝ) / k ^ 2)) := rfl

/-- Tao's Theorem 13 for the range ℓ ≤ 10 k^2. -/
lemma jnorm_le_base_case : ∃ C : ℝ, 0 < C ∧ ∀ (k ℓ M : ℕ),
    1 ≤ k → k ^ 2 ≤ ℓ → ℓ ≤ 10 * k ^ 2 → 1 ≤ M →
      jnorm k ℓ M ≤ Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * k ^ 2 * Real.exp (-(ℓ : ℝ) / k ^ 2)) :=
  ⟨Real.exp 10, Real.exp_pos 10, fun k ℓ M hk _ hl hM => jnorm_le_base (Real.exp 10) le_rfl k ℓ M hk hM hl⟩

/-- Assembly of Tao's Lemma 14 (Vinogradov prime selection), Lemma 19 (Hölder restriction bound),
and Lemma 21 (Linnik congruencing step bound) into a single-step reduction for J. -/
lemma J_le_combined (k ℓ M : ℕ) (hk : 1 ≤ k) (hkl : k < ℓ) (hM : Real.exp (100 * (k : ℝ) ^ 3) ≤ M) :
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < p ∧ (p : ℝ) ≤ 4 * k * (M : ℝ) ^ (1 / (k : ℝ)) ∧
      (J k ℓ M : ℝ) ≤
        ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) *
          ((p : ℝ) ^ (2 * (ℓ - k) - 1) *
            ((p : ℝ) * (M : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k) *
              J k (ℓ - k) (M / p + 1))) +
        2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k * (M : ℝ) ^ (ℓ + k - 1) := by
  obtain ⟨p, hp_prime, hp_lo, hp_hi, hJ⟩ := exists_prime_J_le k ℓ M hk hkl.le hM
  refine ⟨p, hp_prime, hp_lo, hp_hi, ?_⟩
  have hp_pos : 0 < p := hp_prime.pos
  have hJp := Jp_le_Jtilde k ℓ M p hkl.le hp_pos
  have h1M_lt : 1 < M := one_lt_M_of_hM hk hM
  have h1M : 1 ≤ M := h1M_lt.le
  have hpM : (M : ℝ) ^ (1 / (k : ℝ)) < p := by
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    have hk_ge1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    have : (M : ℝ) ^ (1 / (k : ℝ)) ≤ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by
      calc (M : ℝ) ^ (1 / (k : ℝ)) = 1 * (M : ℝ) ^ (1 / (k : ℝ)) := (one_mul _).symm
        _ ≤ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hk_ge1 ?_
          positivity
    linarith
  have hpk : k < p := by
    have hM_gt1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast h1M_lt
    have hM_pow_gt1 : 1 < (M : ℝ) ^ (1 / (k : ℝ)) := by
      have : 0 < 1 / (k : ℝ) := by positivity
      exact Real.one_lt_rpow hM_gt1 this
    have : (k : ℝ) < (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by
      calc (k : ℝ) = (k : ℝ) * 1 := (mul_one _).symm
        _ < (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by
          refine mul_lt_mul_of_pos_left hM_pow_gt1 (by positivity)
    have : (k : ℝ) < (p : ℝ) := this.trans hp_lo
    exact_mod_cast this
  have hJtilde := Jtilde_le k ℓ M p hk hkl hp_prime hpk hpM h1M
  have hJp_bound : (Jp k ℓ M p hkl.le : ℝ) ≤
      (p : ℝ) ^ (2 * (ℓ - k) - 1) *
        ((p : ℝ) * (M : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k) *
          J k (ℓ - k) (M / p + 1)) := by
    refine hJp.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hJtilde
  have h1 : ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * (Jp k ℓ M p hkl.le : ℝ) ≤
      ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) *
        ((p : ℝ) ^ (2 * (ℓ - k) - 1) *
          ((p : ℝ) * (M : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k) *
            J k (ℓ - k) (M / p + 1))) := by
    refine mul_le_mul_of_nonneg_left hJp_bound ?_
    positivity
  linarith

/-- Assembly of Tao's Lemma 14, 19, 21 with relaxed hypothesis exp(100 k^2) ≤ M. -/
lemma J_le_combined_sq (k ℓ M : ℕ) (hk : 1 ≤ k) (hkl : k < ℓ) (hM : Real.exp (100 * (k : ℝ) ^ 2) ≤ M) :
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < p ∧ (p : ℝ) ≤ 4 * k * (M : ℝ) ^ (1 / (k : ℝ)) ∧
      (J k ℓ M : ℝ) ≤
        ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) *
          ((p : ℝ) ^ (2 * (ℓ - k) - 1) *
            ((p : ℝ) * (M : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k) *
              J k (ℓ - k) (M / p + 1))) +
        2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k * (M : ℝ) ^ (ℓ + k - 1) := by
  obtain ⟨p, hp_prime, hp_lo, hp_hi, hJ⟩ := exists_prime_J_le_sq k ℓ M hk hkl.le hM
  refine ⟨p, hp_prime, hp_lo, hp_hi, ?_⟩
  have hp_pos : 0 < p := hp_prime.pos
  have hJp := Jp_le_Jtilde k ℓ M p hkl.le hp_pos
  have h1M_lt : 1 < M := one_lt_M_of_hM_sq hk hM
  have h1M : 1 ≤ M := h1M_lt.le
  have hpM : (M : ℝ) ^ (1 / (k : ℝ)) < p := by
    have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
    have hk_ge1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    have : (M : ℝ) ^ (1 / (k : ℝ)) ≤ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by
      calc (M : ℝ) ^ (1 / (k : ℝ)) = 1 * (M : ℝ) ^ (1 / (k : ℝ)) := (one_mul _).symm
        _ ≤ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by
          refine mul_le_mul_of_nonneg_right hk_ge1 ?_
          positivity
    linarith
  have hpk : k < p := by
    have hM_gt1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast h1M_lt
    have hM_pow_gt1 : 1 < (M : ℝ) ^ (1 / (k : ℝ)) := by
      have : 0 < 1 / (k : ℝ) := by positivity
      exact Real.one_lt_rpow hM_gt1 this
    have : (k : ℝ) < (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by
      calc (k : ℝ) = (k : ℝ) * 1 := (mul_one _).symm
        _ < (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by
          refine mul_lt_mul_of_pos_left hM_pow_gt1 (by positivity)
    have : (k : ℝ) < (p : ℝ) := this.trans hp_lo
    exact_mod_cast this
  have hJtilde := Jtilde_le k ℓ M p hk hkl hp_prime hpk hpM h1M
  have hJp_bound : (Jp k ℓ M p hkl.le : ℝ) ≤
      (p : ℝ) ^ (2 * (ℓ - k) - 1) *
        ((p : ℝ) * (M : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k) *
          J k (ℓ - k) (M / p + 1)) := by
    refine hJp.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hJtilde
  have h1 : ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * (Jp k ℓ M p hkl.le : ℝ) ≤
      ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) *
        ((p : ℝ) ^ (2 * (ℓ - k) - 1) *
          ((p : ℝ) * (M : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k) *
            J k (ℓ - k) (M / p + 1))) := by
    refine mul_le_mul_of_nonneg_left hJp_bound ?_
    positivity
  linarith

lemma jnorm_le_base_11 (C : ℝ) (hC : Real.exp 11 ≤ C) (k ℓ M : ℕ)
    (hk : 1 ≤ k) (hM : 1 ≤ M) (hl : ℓ ≤ 11 * k ^ 2) :
    jnorm k ℓ M ≤ Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * k ^ 2 * Real.exp (-(ℓ : ℝ) / k ^ 2)) := by
  have htriv := jnorm_le_trivial k ℓ M hM
  have hM_ge1 : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk2_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have h_exp_le : (k * (k + 1) / 2 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : (k : ℝ) * ((k : ℝ) + 1) / 2 = ((k : ℝ) ^ 2 + (k : ℝ)) / 2 := by ring
    rw [this]
    have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : 1 ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
    linarith
  have h_triv2 : jnorm k ℓ M ≤ (M : ℝ) ^ ((k : ℝ) ^ 2) := by
    refine htriv.trans (Real.rpow_le_rpow_of_exponent_le hM_ge1 h_exp_le)
  have h_div_le : (ℓ : ℝ) / (k : ℝ) ^ 2 ≤ 11 := by
    rw [div_le_iff₀ hk2_pos]
    have : (ℓ : ℝ) ≤ (11 * k ^ 2 : ℕ) := by exact_mod_cast hl
    push_cast at this
    linarith
  have h_neg_ge : -11 ≤ -(ℓ : ℝ) / (k : ℝ) ^ 2 := by
    have : -(ℓ : ℝ) / (k : ℝ) ^ 2 = -((ℓ : ℝ) / (k : ℝ) ^ 2) := by ring
    rw [this]
    linarith
  have h_exp_ge : Real.exp (-11) ≤ Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) :=
    Real.exp_le_exp.mpr h_neg_ge
  have hC_pos : 0 < C := (Real.exp_pos 11).trans_le hC
  have h_mul_ge : 1 ≤ C * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by
    calc 1 = Real.exp 11 * Real.exp (-11) := by
          rw [← Real.exp_add]
          norm_num
      _ ≤ C * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by
        refine mul_le_mul hC h_exp_ge (Real.exp_pos _).le (by positivity)
  have h_pow_exp_ge : (k : ℝ) ^ 2 ≤ C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by
    calc (k : ℝ) ^ 2 = (k : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (k : ℝ) ^ 2 * (C * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)) := by
        refine mul_le_mul_of_nonneg_left h_mul_ge (by positivity)
      _ = C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by ring
  have h_M_le : (M : ℝ) ^ ((k : ℝ) ^ 2) ≤ (M : ℝ) ^ (C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)) :=
    Real.rpow_le_rpow_of_exponent_le hM_ge1 h_pow_exp_ge
  have h_exp_C_ge1 : 1 ≤ Real.exp (C * ℓ ^ 2) := by
    have : 0 ≤ C * ℓ ^ 2 := by positivity
    exact Real.one_le_exp this
  calc jnorm k ℓ M ≤ (M : ℝ) ^ ((k : ℝ) ^ 2) := h_triv2
    _ = 1 * (M : ℝ) ^ ((k : ℝ) ^ 2) := (one_mul _).symm
    _ ≤ Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)) := by
      refine mul_le_mul h_exp_C_ge1 h_M_le (by positivity) (Real.exp_pos _).le
    _ = Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * k ^ 2 * Real.exp (-(ℓ : ℝ) / k ^ 2)) := rfl

lemma jnorm_le_small_M (C : ℝ) (hC : 100 ≤ C) (k ℓ M : ℕ)
    (hk : 1 ≤ k) (hl : k ^ 2 ≤ ℓ) (hM : 1 ≤ M) (hM_lt : (M : ℝ) < Real.exp (100 * (k : ℝ) ^ 2)) :
    jnorm k ℓ M ≤ Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * k ^ 2 * Real.exp (-(ℓ : ℝ) / k ^ 2)) := by
  have htriv := jnorm_le_trivial k ℓ M hM
  have hM_ge1 : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hM_pos : 0 < (M : ℝ) := by positivity
  have h_exp_le : (k * (k + 1) / 2 : ℝ) ≤ (k : ℝ) ^ 2 := by
    have : (k : ℝ) * ((k : ℝ) + 1) / 2 = ((k : ℝ) ^ 2 + (k : ℝ)) / 2 := by ring
    rw [this]
    have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : 1 ≤ (k : ℝ) := by exact_mod_cast hk
      nlinarith
    linarith
  have h_triv2 : jnorm k ℓ M ≤ (M : ℝ) ^ ((k : ℝ) ^ 2) :=
    htriv.trans (Real.rpow_le_rpow_of_exponent_le hM_ge1 h_exp_le)
  have h_log_lt : Real.log (M : ℝ) < 100 * (k : ℝ) ^ 2 := by
    rw [← Real.log_exp (100 * (k : ℝ) ^ 2)]
    exact Real.log_lt_log hM_pos hM_lt
  have h_pow_eq : (M : ℝ) ^ ((k : ℝ) ^ 2) = Real.exp ((k : ℝ) ^ 2 * Real.log (M : ℝ)) := by
    rw [Real.rpow_def_of_pos hM_pos, mul_comm]
  have h_exp_bound : (k : ℝ) ^ 2 * Real.log (M : ℝ) ≤ 100 * (ℓ : ℝ) ^ 2 := by
    have hk2_pos : 0 ≤ (k : ℝ) ^ 2 := by positivity
    have h1 : (k : ℝ) ^ 2 * Real.log (M : ℝ) ≤ (k : ℝ) ^ 2 * (100 * (k : ℝ) ^ 2) := by
      nlinarith
    have h2 : (k : ℝ) ^ 2 * (100 * (k : ℝ) ^ 2) = 100 * ((k : ℝ) ^ 2) ^ 2 := by ring
    have h3 : ((k : ℝ) ^ 2) ^ 2 ≤ (ℓ : ℝ) ^ 2 := by
      have : (k : ℝ) ^ 2 ≤ (ℓ : ℝ) := by exact_mod_cast hl
      nlinarith
    linarith
  have h_M_bound : (M : ℝ) ^ ((k : ℝ) ^ 2) ≤ Real.exp (100 * (ℓ : ℝ) ^ 2) := by
    rw [h_pow_eq]
    exact Real.exp_le_exp.mpr h_exp_bound
  have h100_C : 100 * (ℓ : ℝ) ^ 2 ≤ C * (ℓ : ℝ) ^ 2 := by
    have : 0 ≤ (ℓ : ℝ) ^ 2 := by positivity
    nlinarith
  have h_exp_C : Real.exp (100 * (ℓ : ℝ) ^ 2) ≤ Real.exp (C * (ℓ : ℝ) ^ 2) :=
    Real.exp_le_exp.mpr h100_C
  have h_M_pow_ge1 : 1 ≤ (M : ℝ) ^ (C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)) := by
    have : 0 ≤ C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by
      have : 0 ≤ C := by linarith
      positivity
    exact Real.one_le_rpow hM_ge1 this
  calc jnorm k ℓ M ≤ (M : ℝ) ^ ((k : ℝ) ^ 2) := h_triv2
    _ ≤ Real.exp (100 * (ℓ : ℝ) ^ 2) := h_M_bound
    _ ≤ Real.exp (C * (ℓ : ℝ) ^ 2) := h_exp_C
    _ = Real.exp (C * ℓ ^ 2) * 1 := (mul_one _).symm
    _ ≤ Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * k ^ 2 * Real.exp (-(ℓ : ℝ) / k ^ 2)) := by
      refine mul_le_mul_of_nonneg_left h_M_pow_ge1 (Real.exp_pos _).le

lemma one_sub_mul_exp_le_one (x : ℝ) : (1 - x) * Real.exp x ≤ 1 := by
  have h := Real.add_one_le_exp (-x)
  have h1 : 1 - x ≤ Real.exp (-x) := by linarith
  have hpos : 0 < Real.exp x := Real.exp_pos x
  calc (1 - x) * Real.exp x ≤ Real.exp (-x) * Real.exp x := mul_le_mul_of_nonneg_right h1 hpos.le
  _ = Real.exp (-x + x) := by rw [← Real.exp_add]
  _ = Real.exp 0 := by ring_nf
  _ = 1 := Real.exp_zero

lemma exp_contract (k ℓ : ℝ) (hk : 0 < k) :
    (1 - 1 / k) * Real.exp (-(ℓ - k) / k ^ 2) ≤ Real.exp (-ℓ / k ^ 2) := by
  have h_split : -(ℓ - k) / k ^ 2 = -ℓ / k ^ 2 + 1 / k := by
    calc -(ℓ - k) / k ^ 2 = (-ℓ + k) / k ^ 2 := by ring
    _ = -ℓ / k ^ 2 + k / k ^ 2 := by rw [add_div]
    _ = -ℓ / k ^ 2 + 1 / k := by
      congr 1
      rw [show k ^ 2 = k * k by ring, mul_comm k k, ← div_div, div_self hk.ne', one_div]
  rw [h_split, Real.exp_add]
  have h_assoc : (1 - 1 / k) * (Real.exp (-ℓ / k ^ 2) * Real.exp (1 / k)) =
      Real.exp (-ℓ / k ^ 2) * ((1 - 1 / k) * Real.exp (1 / k)) := by ring
  rw [h_assoc]
  have h_le := one_sub_mul_exp_le_one (1 / k)
  have h_pos : 0 ≤ Real.exp (-ℓ / k ^ 2) := (Real.exp_pos _).le
  calc Real.exp (-ℓ / k ^ 2) * ((1 - 1 / k) * Real.exp (1 / k))
    ≤ Real.exp (-ℓ / k ^ 2) * 1 := mul_le_mul_of_nonneg_left h_le h_pos
  _ = Real.exp (-ℓ / k ^ 2) := mul_one _

lemma q_pow_le (C : ℝ) (hC : 0 ≤ C) (k ℓ : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ)
    (M q : ℕ) (hM : 1 ≤ M) (hq : 1 ≤ q) (hq_le : (q : ℝ) ≤ 4 * (M : ℝ) ^ (1 - 1 / (k : ℝ))) :
    let α := C * (k : ℝ) ^ 2 * Real.exp (-((ℓ - k : ℕ) : ℝ) / (k : ℝ) ^ 2)
    (q : ℝ) ^ α ≤ Real.exp (2 * C * (k : ℝ) ^ 2) * (M : ℝ) ^ (C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)) := by
  intro α
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hM_pos : 0 < (M : ℝ) := by positivity
  have hM_ge1 : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hq_pos : 0 ≤ (q : ℝ) := by positivity
  have h4_pos : 0 ≤ (4 : ℝ) := by positivity
  have hMr_pos : 0 ≤ (M : ℝ) ^ (1 - 1 / (k : ℝ)) := by positivity
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  have h_cast : ((ℓ - k : ℕ) : ℝ) = (ℓ : ℝ) - (k : ℝ) := Nat.cast_sub hkl
  have h_q_rpow : (q : ℝ) ^ α ≤ (4 * (M : ℝ) ^ (1 - 1 / (k : ℝ))) ^ α :=
    Real.rpow_le_rpow hq_pos hq_le hα_nonneg
  have h_mul_rpow : (4 * (M : ℝ) ^ (1 - 1 / (k : ℝ))) ^ α =
      (4 : ℝ) ^ α * ((M : ℝ) ^ (1 - 1 / (k : ℝ))) ^ α :=
    Real.mul_rpow h4_pos hMr_pos
  rw [h_mul_rpow] at h_q_rpow
  have h_exp_le1 : Real.exp (-((ℓ - k : ℕ) : ℝ) / (k : ℝ) ^ 2) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    rw [h_cast]
    have : 0 ≤ (ℓ : ℝ) - (k : ℝ) := by
      have : (k : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hkl
      linarith
    have h_div : 0 ≤ ((ℓ : ℝ) - (k : ℝ)) / (k : ℝ) ^ 2 := by positivity
    have : -((ℓ : ℝ) - (k : ℝ)) / (k : ℝ) ^ 2 = - (((ℓ : ℝ) - (k : ℝ)) / (k : ℝ) ^ 2) := by ring
    rw [this]
    linarith
  have hα_le : α ≤ C * (k : ℝ) ^ 2 := by
    dsimp [α]
    calc C * (k : ℝ) ^ 2 * Real.exp (-((ℓ - k : ℕ) : ℝ) / (k : ℝ) ^ 2)
      ≤ C * (k : ℝ) ^ 2 * 1 := mul_le_mul_of_nonneg_left h_exp_le1 (by positivity)
      _ = C * (k : ℝ) ^ 2 := mul_one _
  have h4_le : (4 : ℝ) ^ α ≤ Real.exp (2 * C * (k : ℝ) ^ 2) := by
    have h4_eq : (4 : ℝ) ^ α = Real.exp (α * Real.log 4) := by
      have h4_gt0 : (0 : ℝ) < 4 := by norm_num
      rw [Real.rpow_def_of_pos h4_gt0 α, mul_comm]
    have hlog4_le : Real.log 4 ≤ 2 := by
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      have : (4 : ℝ) ≤ Real.exp 2 := by
        have hsq : (2 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := by nlinarith
        have h_ring : (Real.exp 1) ^ 2 = Real.exp 2 := by
          rw [sq, ← Real.exp_add]
          norm_num
        have : (2 : ℝ) ^ 2 = 4 := by norm_num
        linarith
      rw [← Real.log_exp 2]
      exact Real.log_le_log (by norm_num) this
    have h_prod : α * Real.log 4 ≤ 2 * C * (k : ℝ) ^ 2 := by
      calc α * Real.log 4 ≤ (C * (k : ℝ) ^ 2) * 2 := by
            refine mul_le_mul hα_le hlog4_le (Real.log_nonneg (by norm_num)) ?_
            positivity
      _ = 2 * C * (k : ℝ) ^ 2 := by ring
    rw [h4_eq]
    exact Real.exp_le_exp.mpr h_prod
  have h_rpow_rpow : ((M : ℝ) ^ (1 - 1 / (k : ℝ))) ^ α = (M : ℝ) ^ ((1 - 1 / (k : ℝ)) * α) :=
    (Real.rpow_mul hM_pos.le (1 - 1 / (k : ℝ)) α).symm
  have h_exp_contract : (1 - 1 / (k : ℝ)) * α ≤ C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by
    dsimp [α]
    rw [h_cast]
    calc (1 - 1 / (k : ℝ)) * (C * (k : ℝ) ^ 2 * Real.exp (-((ℓ : ℝ) - (k : ℝ)) / (k : ℝ) ^ 2))
      = (C * (k : ℝ) ^ 2) * ((1 - 1 / (k : ℝ)) * Real.exp (-((ℓ : ℝ) - (k : ℝ)) / (k : ℝ) ^ 2)) := by ring
    _ ≤ (C * (k : ℝ) ^ 2) * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by
      refine mul_le_mul_of_nonneg_left ?_ ?_
      · exact exp_contract (k : ℝ) (ℓ : ℝ) hk_pos
      · positivity
    _ = C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) := by ring
  have hM_le : ((M : ℝ) ^ (1 - 1 / (k : ℝ))) ^ α ≤ (M : ℝ) ^ (C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)) := by
    rw [h_rpow_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hM_ge1 h_exp_contract
  calc (q : ℝ) ^ α ≤ (4 : ℝ) ^ α * ((M : ℝ) ^ (1 - 1 / (k : ℝ))) ^ α := h_q_rpow
  _ ≤ Real.exp (2 * C * (k : ℝ) ^ 2) * (M : ℝ) ^ (C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)) :=
    mul_le_mul h4_le hM_le (by positivity) (Real.exp_pos _).le

lemma exp_diff_le (C A : ℝ) (hA : 0 ≤ A) (hC : 11 * A + 11 ≤ C)
    (k ℓ : ℕ) (hk : 1 ≤ k) (hl : 11 * k ^ 2 ≤ ℓ) :
    let diff := C * (ℓ : ℝ) ^ 2 - (C * ((ℓ : ℝ) - (k : ℝ)) ^ 2 + 2 * C * (k : ℝ) ^ 2 + A * (ℓ : ℝ) * (k : ℝ))
    1 ≤ diff ∧ A * (ℓ : ℝ) * (k : ℝ) + 1 ≤ C * (ℓ : ℝ) ^ 2 := by
  intro diff
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : 0 < (k : ℝ) := by positivity
  have h_k2_pos : 0 < (k : ℝ) ^ 2 := by positivity
  have hl_ge : 11 * (k : ℝ) ^ 2 ≤ (ℓ : ℝ) := by exact_mod_cast hl
  have hl_ge1 : (1 : ℝ) ≤ (ℓ : ℝ) := by
    have : 1 ≤ ℓ := by
      calc 1 ≤ 11 * 1 ^ 2 := by norm_num
      _ ≤ 11 * k ^ 2 := by nlinarith
      _ ≤ ℓ := hl
    exact_mod_cast this
  have h_diff_eq : diff = 2 * C * (ℓ : ℝ) * (k : ℝ) - 3 * C * (k : ℝ) ^ 2 - A * (ℓ : ℝ) * (k : ℝ) := by
    dsimp [diff]
    ring
  have h_3k2 : 3 * (k : ℝ) ^ 2 ≤ (3 / 11 : ℝ) * (ℓ : ℝ) * (k : ℝ) := by
    calc 3 * (k : ℝ) ^ 2 = (3 / 11 : ℝ) * (11 * (k : ℝ) ^ 2) := by ring
    _ ≤ (3 / 11 : ℝ) * ((ℓ : ℝ) * (k : ℝ)) := by
      have : 11 * (k : ℝ) ^ 2 ≤ (ℓ : ℝ) * (k : ℝ) := by
        calc 11 * (k : ℝ) ^ 2 = (11 * (k : ℝ) ^ 2) * 1 := (mul_one _).symm
        _ ≤ (ℓ : ℝ) * (k : ℝ) := by
          calc (11 * (k : ℝ) ^ 2) * 1 ≤ (ℓ : ℝ) * 1 := by nlinarith
          _ ≤ (ℓ : ℝ) * (k : ℝ) := by nlinarith
      nlinarith
    _ = (3 / 11 : ℝ) * (ℓ : ℝ) * (k : ℝ) := by ring
  have hC_pos : 0 ≤ C := by linarith
  have h_3C : 3 * C * (k : ℝ) ^ 2 ≤ (3 / 11 : ℝ) * C * (ℓ : ℝ) * (k : ℝ) := by
    calc 3 * C * (k : ℝ) ^ 2 = C * (3 * (k : ℝ) ^ 2) := by ring
    _ ≤ C * ((3 / 11 : ℝ) * (ℓ : ℝ) * (k : ℝ)) := mul_le_mul_of_nonneg_left h_3k2 hC_pos
    _ = (3 / 11 : ℝ) * C * (ℓ : ℝ) * (k : ℝ) := by ring
  have h_diff_ge : (19 / 11 : ℝ) * C * (ℓ : ℝ) * (k : ℝ) - A * (ℓ : ℝ) * (k : ℝ) ≤ diff := by
    rw [h_diff_eq]
    linarith
  have h_fact : (19 / 11 : ℝ) * C * (ℓ : ℝ) * (k : ℝ) - A * (ℓ : ℝ) * (k : ℝ)
      = ((19 / 11 : ℝ) * C - A) * ((ℓ : ℝ) * (k : ℝ)) := by ring
  have h_coeff : 1 ≤ (19 / 11 : ℝ) * C - A := by
    have : (19 / 11 : ℝ) * (11 * A + 11) = 19 * A + 19 := by ring
    have : (19 / 11 : ℝ) * (11 * A + 11) ≤ (19 / 11 : ℝ) * C := by nlinarith
    linarith
  have h_lk : 1 ≤ (ℓ : ℝ) * (k : ℝ) := by nlinarith
  have h_diff_1 : 1 ≤ diff := by
    calc 1 = 1 * 1 := (mul_one 1).symm
    _ ≤ ((19 / 11 : ℝ) * C - A) * ((ℓ : ℝ) * (k : ℝ)) := mul_le_mul h_coeff h_lk (by norm_num) (by linarith)
    _ = (19 / 11 : ℝ) * C * (ℓ : ℝ) * (k : ℝ) - A * (ℓ : ℝ) * (k : ℝ) := h_fact.symm
    _ ≤ diff := h_diff_ge
  have h_Ak_le : A * (ℓ : ℝ) * (k : ℝ) + 1 ≤ C * (ℓ : ℝ) ^ 2 := by
    have h_l2 : (ℓ : ℝ) * (k : ℝ) ≤ (ℓ : ℝ) ^ 2 := by
      have : (k : ℝ) ≤ (ℓ : ℝ) := by
        calc (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
        _ ≤ 11 * (k : ℝ) ^ 2 := by nlinarith
        _ ≤ (ℓ : ℝ) := hl_ge
      nlinarith
    have : A * (ℓ : ℝ) * (k : ℝ) ≤ A * (ℓ : ℝ) ^ 2 := by nlinarith
    have hC_A : A + 1 ≤ C := by linarith
    have : 1 ≤ (ℓ : ℝ) ^ 2 := by nlinarith
    nlinarith
  exact ⟨h_diff_1, h_Ak_le⟩

lemma exp_sum_le_exp (C A : ℝ) (hA : 0 ≤ A) (hC : 11 * A + 11 ≤ C)
    (k ℓ : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ) (hl : 11 * k ^ 2 ≤ ℓ) (M : ℕ) (hM : 1 ≤ M) :
    let β := C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2)
    Real.exp (A * (ℓ : ℝ) * (k : ℝ)) * (Real.exp (C * ((ℓ - k : ℕ) : ℝ) ^ 2) *
      (Real.exp (2 * C * (k : ℝ) ^ 2) * (M : ℝ) ^ β)) +
    Real.exp (A * (ℓ : ℝ) * (k : ℝ)) ≤ Real.exp (C * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ β := by
  intro β
  have h_cast : ((ℓ - k : ℕ) : ℝ) = (ℓ : ℝ) - (k : ℝ) := Nat.cast_sub hkl
  obtain ⟨h_diff, h_Ak⟩ := exp_diff_le C A hA hC k ℓ hk hl
  have hM_pos : 0 < (M : ℝ) := by positivity
  have hM_ge1 : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    have : 0 ≤ C := by linarith
    positivity
  have hM_pow_ge1 : 1 ≤ (M : ℝ) ^ β := Real.one_le_rpow hM_ge1 hβ_nonneg
  have h_exp_2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h_prod_eq : Real.exp (A * (ℓ : ℝ) * (k : ℝ)) * (Real.exp (C * ((ℓ - k : ℕ) : ℝ) ^ 2) *
      (Real.exp (2 * C * (k : ℝ) ^ 2) * (M : ℝ) ^ β)) =
      Real.exp (C * ((ℓ : ℝ) - (k : ℝ)) ^ 2 + 2 * C * (k : ℝ) ^ 2 + A * (ℓ : ℝ) * (k : ℝ)) * (M : ℝ) ^ β := by
    rw [h_cast]
    calc Real.exp (A * (ℓ : ℝ) * (k : ℝ)) * (Real.exp (C * ((ℓ : ℝ) - (k : ℝ)) ^ 2) *
          (Real.exp (2 * C * (k : ℝ) ^ 2) * (M : ℝ) ^ β))
      = (Real.exp (A * (ℓ : ℝ) * (k : ℝ)) * Real.exp (C * ((ℓ : ℝ) - (k : ℝ)) ^ 2) *
          Real.exp (2 * C * (k : ℝ) ^ 2)) * (M : ℝ) ^ β := by ring
    _ = Real.exp (A * (ℓ : ℝ) * (k : ℝ) + C * ((ℓ : ℝ) - (k : ℝ)) ^ 2 + 2 * C * (k : ℝ) ^ 2) * (M : ℝ) ^ β := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ = Real.exp (C * ((ℓ : ℝ) - (k : ℝ)) ^ 2 + 2 * C * (k : ℝ) ^ 2 + A * (ℓ : ℝ) * (k : ℝ)) * (M : ℝ) ^ β := by
      congr 2
      ring
  rw [h_prod_eq]
  have h_exp_le : Real.exp (C * ((ℓ : ℝ) - (k : ℝ)) ^ 2 + 2 * C * (k : ℝ) ^ 2 + A * (ℓ : ℝ) * (k : ℝ))
      ≤ (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) := by
    have h_sub : C * ((ℓ : ℝ) - (k : ℝ)) ^ 2 + 2 * C * (k : ℝ) ^ 2 + A * (ℓ : ℝ) * (k : ℝ)
        ≤ C * (ℓ : ℝ) ^ 2 - 1 := by linarith
    have h_exp := Real.exp_le_exp.mpr h_sub
    rw [Real.exp_sub] at h_exp
    calc Real.exp (C * ((ℓ : ℝ) - (k : ℝ)) ^ 2 + 2 * C * (k : ℝ) ^ 2 + A * (ℓ : ℝ) * (k : ℝ))
      ≤ Real.exp (C * (ℓ : ℝ) ^ 2) / Real.exp 1 := h_exp
    _ ≤ Real.exp (C * (ℓ : ℝ) ^ 2) / 2 := by
      refine div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h_exp_2
    _ = (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) := by ring
  have h_exp_A_le : Real.exp (A * (ℓ : ℝ) * (k : ℝ)) ≤ (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) := by
    have h_sub : A * (ℓ : ℝ) * (k : ℝ) ≤ C * (ℓ : ℝ) ^ 2 - 1 := by linarith
    have h_exp := Real.exp_le_exp.mpr h_sub
    rw [Real.exp_sub] at h_exp
    calc Real.exp (A * (ℓ : ℝ) * (k : ℝ))
      ≤ Real.exp (C * (ℓ : ℝ) ^ 2) / Real.exp 1 := h_exp
    _ ≤ Real.exp (C * (ℓ : ℝ) ^ 2) / 2 :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le (by norm_num) h_exp_2
    _ = (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) := by ring
  have h_term1 : Real.exp (C * ((ℓ : ℝ) - (k : ℝ)) ^ 2 + 2 * C * (k : ℝ) ^ 2 + A * (ℓ : ℝ) * (k : ℝ)) * (M : ℝ) ^ β
      ≤ (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ β :=
    mul_le_mul_of_nonneg_right h_exp_le (by positivity)
  have h_term2 : Real.exp (A * (ℓ : ℝ) * (k : ℝ)) ≤ (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ β := by
    calc Real.exp (A * (ℓ : ℝ) * (k : ℝ)) ≤ (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) := h_exp_A_le
    _ = (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) * 1 := (mul_one _).symm
    _ ≤ (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ β := by
      refine mul_le_mul_of_nonneg_left hM_pow_ge1 ?_
      positivity
  calc Real.exp (C * ((ℓ : ℝ) - (k : ℝ)) ^ 2 + 2 * C * (k : ℝ) ^ 2 + A * (ℓ : ℝ) * (k : ℝ)) * (M : ℝ) ^ β +
    Real.exp (A * (ℓ : ℝ) * (k : ℝ))
    ≤ (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ β +
      (1 / 2 : ℝ) * Real.exp (C * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ β := add_le_add h_term1 h_term2
  _ = Real.exp (C * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ β := by ring

lemma log_le_self (x : ℝ) (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.add_one_le_exp (Real.log x)
  rw [Real.exp_log hx] at this
  linarith

lemma term2_le_exp (k ℓ M : ℕ) (hk : 1 ≤ k) (hl : 11 * k ^ 2 ≤ ℓ) (hM : 1 ≤ M) :
    (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k * (M : ℝ) ^ (ℓ + k - 1))
      ≤ Real.exp (3 * (ℓ : ℝ) * (k : ℝ)) := by
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hk_ge1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hM_pos : 0 < (M : ℝ) := by positivity
  have hM_ge1 : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hl_ge1 : 1 ≤ (ℓ : ℝ) := by
    have : 1 ≤ ℓ := by
      calc 1 ≤ 11 * 1 ^ 2 := by norm_num
      _ ≤ 11 * k ^ 2 := by nlinarith
      _ ≤ ℓ := hl
    exact_mod_cast this
  have hl_pos : 0 < (ℓ : ℝ) := by linarith
  have h_exp_M : ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) + ((ℓ + k - 1 : ℕ) : ℝ) ≤ 0 := by
    have h1 : (k * (k + 1) / 2 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (k : ℝ) * ((k : ℝ) + 1) / 2 = ((k : ℝ) ^ 2 + (k : ℝ)) / 2 := by ring
      rw [this]
      have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      linarith
    have h2 : ((ℓ + k - 1 : ℕ) : ℝ) ≤ (ℓ : ℝ) + (k : ℝ) := by
      have : ℓ + k - 1 ≤ ℓ + k := Nat.sub_le _ _
      have hcast : ((ℓ + k - 1 : ℕ) : ℝ) ≤ ((ℓ + k : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hcast
      exact hcast
    have h3 : 11 * (k : ℝ) ^ 2 ≤ (ℓ : ℝ) := by exact_mod_cast hl
    linarith
  have h_rpow_M : (M : ℝ) ^ (((k * (k + 1) / 2 : ℝ) - 2 * ℓ) + ((ℓ + k - 1 : ℕ) : ℝ)) ≤ 1 := by
    calc (M : ℝ) ^ (((k * (k + 1) / 2 : ℝ) - 2 * ℓ) + ((ℓ + k - 1 : ℕ) : ℝ))
      ≤ (M : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM_ge1 h_exp_M
      _ = 1 := Real.rpow_zero _
  have hM_nat : (M : ℝ) ^ (ℓ + k - 1) = (M : ℝ) ^ ((ℓ + k - 1 : ℕ) : ℝ) := (Real.rpow_natCast (M : ℝ) _).symm
  have h_assoc : (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k * (M : ℝ) ^ (ℓ + k - 1))
      = (2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k) * ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ ((ℓ + k - 1 : ℕ) : ℝ)) := by
    rw [hM_nat]
    ring
  rw [h_assoc, ← Real.rpow_add hM_pos]
  have h_prod_le : (2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k) * ((M : ℝ) ^ (((k * (k + 1) / 2 : ℝ) - 2 * ℓ) + ((ℓ + k - 1 : ℕ) : ℝ)))
      ≤ 2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k * 1 := by
    refine mul_le_mul_of_nonneg_left h_rpow_M (by positivity)
  rw [mul_one] at h_prod_le
  refine h_prod_le.trans ?_
  have h2 : (2 : ℝ) ≤ Real.exp ((ℓ : ℝ) * (k : ℝ)) := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h2' : (1 : ℝ) ≤ (ℓ : ℝ) * (k : ℝ) := by nlinarith
    exact h1.trans (Real.exp_le_exp.mpr h2')
  have hk_pow : (k : ℝ) ^ ℓ ≤ Real.exp ((ℓ : ℝ) * (k : ℝ)) := by
    rw [show (k : ℝ) ^ ℓ = (k : ℝ) ^ (ℓ : ℝ) by exact (Real.rpow_natCast (k : ℝ) ℓ).symm]
    have : (k : ℝ) ^ (ℓ : ℝ) = Real.exp ((ℓ : ℝ) * Real.log (k : ℝ)) := by
      rw [Real.rpow_def_of_pos hk_pos (ℓ : ℝ), mul_comm]
    rw [this]
    apply Real.exp_le_exp.mpr
    have : Real.log (k : ℝ) ≤ (k : ℝ) := log_le_self (k : ℝ) hk_pos
    nlinarith
  have hl_pow : (ℓ : ℝ) ^ k ≤ Real.exp ((ℓ : ℝ) * (k : ℝ)) := by
    rw [show (ℓ : ℝ) ^ k = (ℓ : ℝ) ^ (k : ℝ) by exact (Real.rpow_natCast (ℓ : ℝ) k).symm]
    have : (ℓ : ℝ) ^ (k : ℝ) = Real.exp ((k : ℝ) * Real.log (ℓ : ℝ)) := by
      rw [Real.rpow_def_of_pos hl_pos (k : ℝ), mul_comm]
    rw [this]
    apply Real.exp_le_exp.mpr
    have : Real.log (ℓ : ℝ) ≤ (ℓ : ℝ) := log_le_self (ℓ : ℝ) hl_pos
    calc (k : ℝ) * Real.log (ℓ : ℝ) ≤ (k : ℝ) * (ℓ : ℝ) := by nlinarith
    _ = (ℓ : ℝ) * (k : ℝ) := mul_comm _ _
  have h_prod1 : 2 * (k : ℝ) ^ ℓ ≤ Real.exp ((ℓ : ℝ) * (k : ℝ)) * Real.exp ((ℓ : ℝ) * (k : ℝ)) :=
    mul_le_mul h2 hk_pow (by positivity) (by positivity)
  have h_prod2 : 2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k ≤
      Real.exp ((ℓ : ℝ) * (k : ℝ)) * Real.exp ((ℓ : ℝ) * (k : ℝ)) * Real.exp ((ℓ : ℝ) * (k : ℝ)) :=
    mul_le_mul h_prod1 hl_pow (by positivity) (by positivity)
  refine h_prod2.trans ?_
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  ring_nf
  rfl

lemma div_add_two_pow_le_three_pow (k M p : ℕ) (hk : 1 ≤ k) (hM : 1 ≤ M)
    (hp_lo : (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < (p : ℝ)) :
    ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k ≤ (3 : ℝ) ^ k := by
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hM_pos : 0 < (M : ℝ) := by positivity
  have hp_pos : 0 < (p : ℝ) := by
    have : 0 < (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by positivity
    linarith
  have h_p_ge : (M : ℝ) ^ (1 / (k : ℝ)) < (p : ℝ) := by
    calc (M : ℝ) ^ (1 / (k : ℝ)) = 1 * (M : ℝ) ^ (1 / (k : ℝ)) := (one_mul _).symm
    _ ≤ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast hk
    _ < (p : ℝ) := hp_lo
  have h_pk_gt : (M : ℝ) < (p : ℝ) ^ k := by
    rw [show (p : ℝ) ^ k = (p : ℝ) ^ (k : ℝ) by exact (Real.rpow_natCast (p : ℝ) k).symm]
    have h1 : ((M : ℝ) ^ (1 / (k : ℝ))) ^ (k : ℝ) < (p : ℝ) ^ (k : ℝ) :=
      Real.rpow_lt_rpow (by positivity) h_p_ge hk_pos
    rw [← Real.rpow_mul hM_pos.le, one_div_mul_cancel hk_pos.ne', Real.rpow_one] at h1
    exact h1
  have h_div_lt1 : (M : ℝ) / (p : ℝ) ^ k < 1 := by
    rw [div_lt_one (by positivity)]
    exact h_pk_gt
  have h_base_le : (M : ℝ) / (p : ℝ) ^ k + 2 ≤ 3 := by linarith
  have h_base_nonneg : 0 ≤ (M : ℝ) / (p : ℝ) ^ k + 2 := by positivity
  gcongr

lemma p_pow_step (p : ℝ) (ℓ k : ℕ) (hlk : 1 ≤ ℓ - k) :
    p ^ (2 * (ℓ - k) - 1) * p = p ^ (2 * (ℓ - k)) := by
  have : 1 ≤ 2 * (ℓ - k) := by omega
  rw [← pow_succ, Nat.sub_add_cancel this]

lemma exponent_identity (k ℓ : ℝ) (hk : k ≠ 0) :
    let E := 2 * (ℓ - k) - k * (k + 1) / 2
    let exp_p := 2 * (ℓ - k) + k * (k - 1) / 2
    (k * (k + 1) / 2 - 2 * ℓ + k) + (1 - 1 / k) * E + (1 / k) * exp_p = 0 := by
  intro E exp_p
  dsimp [E, exp_p]
  rw [add_assoc]
  have : (1 - 1 / k) * (2 * (ℓ - k) - k * (k + 1) / 2) + (1 / k) * (2 * (ℓ - k) + k * (k - 1) / 2)
    = (2 * (ℓ - k) - k * (k + 1) / 2) + (1 / k) * (k * (k - 1) / 2 + k * (k + 1) / 2) := by ring
  rw [this]
  have : k * (k - 1) / 2 + k * (k + 1) / 2 = k ^ 2 := by ring
  rw [this]
  have : (1 / k) * k ^ 2 = k := by
    rw [show k ^ 2 = k * k by ring, ← mul_assoc, one_div_mul_cancel hk, one_mul]
  rw [this]
  ring

lemma prefactors_bound (k ℓ : ℕ) (hk : 1 ≤ k) (hl : 11 * k ^ 2 ≤ ℓ) :
    let E := 2 * ((ℓ : ℝ) - (k : ℝ)) - (k * (k + 1) / 2 : ℝ)
    let exp_p := 2 * ((ℓ : ℝ) - (k : ℝ)) + (k * (k - 1) / 2 : ℝ)
    ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ k *
      (4 * (k : ℝ)) ^ exp_p * (4 : ℝ) ^ E ≤ Real.exp (30 * (ℓ : ℝ) * (k : ℝ)) := by
  intro E exp_p
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hk_ge1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hl_ge : 11 * (k : ℝ) ^ 2 ≤ (ℓ : ℝ) := by exact_mod_cast hl
  have hl_pos : 0 < (ℓ : ℝ) := by
    have : 1 ≤ (ℓ : ℝ) := by
      calc 1 ≤ 11 * (k : ℝ) ^ 2 := by nlinarith
      _ ≤ (ℓ : ℝ) := hl_ge
    linarith
  have hkl : (k : ℝ) ≤ (ℓ : ℝ) := by
    calc (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    _ ≤ 11 * (k : ℝ) ^ 2 := by nlinarith
    _ ≤ (ℓ : ℝ) := hl_ge
  have hlk : 1 ≤ (ℓ : ℝ) * (k : ℝ) := by nlinarith
  have hE_le : E ≤ 2 * (ℓ : ℝ) := by
    dsimp [E]
    have : 0 ≤ (k * (k + 1) / 2 : ℝ) := by positivity
    linarith
  have hexp_p_le : exp_p ≤ 3 * (ℓ : ℝ) := by
    dsimp [exp_p]
    have h2 : (k * (k - 1) / 2 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have h3 : (k : ℝ) ^ 2 ≤ (ℓ : ℝ) := by
      calc (k : ℝ) ^ 2 ≤ 11 * (k : ℝ) ^ 2 := by nlinarith
      _ ≤ (ℓ : ℝ) := hl_ge
    linarith
  have h_k3 : (k : ℝ) ^ 3 + 1 ≤ Real.exp (2 * (ℓ : ℝ) * (k : ℝ)) := by
    have h1 : (k : ℝ) ^ 3 + 1 ≤ 2 * (k : ℝ) ^ 3 := by
      have : 1 ≤ (k : ℝ) ^ 3 := by nlinarith
      linarith
    have h2 : 2 * (k : ℝ) ^ 3 ≤ Real.exp (2 * (ℓ : ℝ) * (k : ℝ)) := by
      have : (k : ℝ) ^ 3 ≤ (ℓ : ℝ) * (k : ℝ) := by
        calc (k : ℝ) ^ 3 = (k : ℝ) ^ 2 * (k : ℝ) := by ring
        _ ≤ (ℓ : ℝ) * (k : ℝ) := by nlinarith
      have he : 2 * (k : ℝ) ^ 3 ≤ Real.exp (2 * ((k : ℝ) ^ 3)) := by
        have := Real.add_one_le_exp (2 * (k : ℝ) ^ 3)
        linarith
      refine he.trans (Real.exp_le_exp.mpr (by nlinarith))
    exact h1.trans h2
  have h_l2k : (ℓ : ℝ) ^ (2 * k) ≤ Real.exp (2 * (ℓ : ℝ) * (k : ℝ)) := by
    rw [show (ℓ : ℝ) ^ (2 * k) = (ℓ : ℝ) ^ ((2 * k : ℕ) : ℝ) by exact (Real.rpow_natCast _ _).symm]
    push_cast
    have : (ℓ : ℝ) ^ (2 * (k : ℝ)) = Real.exp (2 * (k : ℝ) * Real.log (ℓ : ℝ)) := by
      rw [Real.rpow_def_of_pos hl_pos, mul_comm]
    rw [this]
    apply Real.exp_le_exp.mpr
    have : Real.log (ℓ : ℝ) ≤ (ℓ : ℝ) := log_le_self (ℓ : ℝ) hl_pos
    nlinarith
  have h_fact : (k.factorial : ℝ) ≤ Real.exp ((ℓ : ℝ) * (k : ℝ)) := by
    have : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
      have : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
      have hcast : (k.factorial : ℝ) ≤ ((k ^ k : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hcast
      exact hcast
    refine this.trans ?_
    rw [show (k : ℝ) ^ k = (k : ℝ) ^ (k : ℝ) by exact (Real.rpow_natCast _ _).symm]
    have : (k : ℝ) ^ (k : ℝ) = Real.exp ((k : ℝ) * Real.log (k : ℝ)) := by
      rw [Real.rpow_def_of_pos hk_pos, mul_comm]
    rw [this]
    apply Real.exp_le_exp.mpr
    have : Real.log (k : ℝ) ≤ (k : ℝ) := log_le_self (k : ℝ) hk_pos
    calc (k : ℝ) * Real.log (k : ℝ) ≤ (k : ℝ) * (k : ℝ) := by nlinarith
    _ ≤ (ℓ : ℝ) * (k : ℝ) := by nlinarith
  have h_3k : (3 : ℝ) ^ k ≤ Real.exp (2 * (ℓ : ℝ) * (k : ℝ)) := by
    rw [show (3 : ℝ) ^ k = (3 : ℝ) ^ (k : ℝ) by exact (Real.rpow_natCast _ _).symm]
    have : (3 : ℝ) ^ (k : ℝ) = Real.exp ((k : ℝ) * Real.log 3) := by
      rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    rw [this]
    apply Real.exp_le_exp.mpr
    have hlog3 : Real.log 3 ≤ 2 := by
      have : (3 : ℝ) ≤ Real.exp 2 := by
        have : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
        have : (4 : ℝ) ≤ Real.exp 2 := by
          have hsq : (2 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := by nlinarith
          have h_ring : (Real.exp 1) ^ 2 = Real.exp 2 := by
            rw [sq, ← Real.exp_add]
            norm_num
          linarith
        linarith
      rw [← Real.log_exp 2]
      exact Real.log_le_log (by norm_num) this
    nlinarith
  have h_4k_exp : (4 * (k : ℝ)) ^ exp_p ≤ Real.exp (12 * (ℓ : ℝ) * (k : ℝ)) := by
    have h4k_pos : 0 < 4 * (k : ℝ) := by positivity
    have : (4 * (k : ℝ)) ^ exp_p = Real.exp (exp_p * Real.log (4 * (k : ℝ))) := by
      rw [Real.rpow_def_of_pos h4k_pos, mul_comm]
    rw [this]
    apply Real.exp_le_exp.mpr
    have hlog4k : Real.log (4 * (k : ℝ)) ≤ 4 * (k : ℝ) := log_le_self _ h4k_pos
    have h_step : exp_p * Real.log (4 * (k : ℝ)) ≤ (3 * (ℓ : ℝ)) * (4 * (k : ℝ)) :=
      mul_le_mul hexp_p_le hlog4k (Real.log_nonneg (by linarith)) (by positivity)
    calc exp_p * Real.log (4 * (k : ℝ)) ≤ (3 * (ℓ : ℝ)) * (4 * (k : ℝ)) := h_step
    _ = 12 * (ℓ : ℝ) * (k : ℝ) := by ring
  have h_4E : (4 : ℝ) ^ E ≤ Real.exp (4 * (ℓ : ℝ) * (k : ℝ)) := by
    have : (4 : ℝ) ^ E = Real.exp (E * Real.log 4) := by
      rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    rw [this]
    apply Real.exp_le_exp.mpr
    have : Real.log 4 ≤ 2 := by
      have : (4 : ℝ) ≤ Real.exp 2 := by
        have : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.add_one_le_exp (1 : ℝ)
          linarith
        have : (4 : ℝ) ≤ Real.exp 2 := by
          have hsq : (2 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := by nlinarith
          have h_ring : (Real.exp 1) ^ 2 = Real.exp 2 := by
            rw [sq, ← Real.exp_add]
            norm_num
          linarith
        linarith
      rw [← Real.log_exp 2]
      exact Real.log_le_log (by norm_num) this
    have h_step : E * Real.log 4 ≤ (2 * (ℓ : ℝ)) * 2 :=
      mul_le_mul hE_le this (Real.log_nonneg (by norm_num)) (by positivity)
    calc E * Real.log 4 ≤ (2 * (ℓ : ℝ)) * 2 := h_step
    _ = 4 * (ℓ : ℝ) := by ring
    _ ≤ 4 * (ℓ : ℝ) * (k : ℝ) := by
      calc 4 * (ℓ : ℝ) = 4 * (ℓ : ℝ) * 1 := (mul_one _).symm
      _ ≤ 4 * (ℓ : ℝ) * (k : ℝ) := by nlinarith
  have h_prod1 : ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) ≤ Real.exp (4 * (ℓ : ℝ) * (k : ℝ)) := by
    have := mul_le_mul h_k3 h_l2k (by positivity) (by positivity)
    rw [← Real.exp_add] at this
    have h_ring : 2 * (ℓ : ℝ) * (k : ℝ) + 2 * (ℓ : ℝ) * (k : ℝ) = 4 * (ℓ : ℝ) * (k : ℝ) := by ring
    rwa [h_ring] at this
  have h_prod2 : ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * (k.factorial : ℝ) ≤ Real.exp (5 * (ℓ : ℝ) * (k : ℝ)) := by
    have := mul_le_mul h_prod1 h_fact (by positivity) (by positivity)
    rw [← Real.exp_add] at this
    have h_ring : 4 * (ℓ : ℝ) * (k : ℝ) + (ℓ : ℝ) * (k : ℝ) = 5 * (ℓ : ℝ) * (k : ℝ) := by ring
    rwa [h_ring] at this
  have h_prod3 : ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ k
      ≤ Real.exp (7 * (ℓ : ℝ) * (k : ℝ)) := by
    have := mul_le_mul h_prod2 h_3k (by positivity) (by positivity)
    rw [← Real.exp_add] at this
    have h_ring : 5 * (ℓ : ℝ) * (k : ℝ) + 2 * (ℓ : ℝ) * (k : ℝ) = 7 * (ℓ : ℝ) * (k : ℝ) := by ring
    rwa [h_ring] at this
  have h_prod4 : ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ k *
      (4 * (k : ℝ)) ^ exp_p ≤ Real.exp (19 * (ℓ : ℝ) * (k : ℝ)) := by
    have := mul_le_mul h_prod3 h_4k_exp (by positivity) (by positivity)
    rw [← Real.exp_add] at this
    have h_ring : 7 * (ℓ : ℝ) * (k : ℝ) + 12 * (ℓ : ℝ) * (k : ℝ) = 19 * (ℓ : ℝ) * (k : ℝ) := by ring
    rwa [h_ring] at this
  have h_prod5 : ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ k *
      (4 * (k : ℝ)) ^ exp_p * (4 : ℝ) ^ E ≤ Real.exp (23 * (ℓ : ℝ) * (k : ℝ)) := by
    have := mul_le_mul h_prod4 h_4E (by positivity) (by positivity)
    rw [← Real.exp_add] at this
    have h_ring : 19 * (ℓ : ℝ) * (k : ℝ) + 4 * (ℓ : ℝ) * (k : ℝ) = 23 * (ℓ : ℝ) * (k : ℝ) := by ring
    rwa [h_ring] at this
  refine h_prod5.trans ?_
  apply Real.exp_le_exp.mpr
  nlinarith

lemma q_le_four_mul_rpow (k M p : ℕ) (hk : 1 ≤ k) (hM : 1 ≤ M)
    (hp_lo : (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < (p : ℝ)) :
    let q := M / p + 1
    (q : ℝ) ≤ 4 * (M : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  intro q
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hM_ge1 : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hM_pos : 0 < (M : ℝ) := by positivity
  have hp_pos : 0 < (p : ℝ) := by
    have : 0 < (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by positivity
    linarith
  have h_exp_ge0 : 0 ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 := by
      rw [div_le_iff₀ hk_pos]
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    linarith
  have hM_pow_ge1 : 1 ≤ (M : ℝ) ^ (1 - 1 / (k : ℝ)) := Real.one_le_rpow hM_ge1 h_exp_ge0
  by_cases hpM : M < p
  · have hdiv : M / p = 0 := Nat.div_eq_of_lt hpM
    have hq_eq : q = 1 := by
      dsimp [q]
      rw [hdiv, zero_add]
    have : (q : ℝ) = 1 := by exact_mod_cast hq_eq
    rw [this]
    calc (1 : ℝ) ≤ 4 := by norm_num
    _ = 4 * 1 := (mul_one _).symm
    _ ≤ 4 * (M : ℝ) ^ (1 - 1 / (k : ℝ)) := by
      refine mul_le_mul_of_nonneg_left hM_pow_ge1 (by norm_num)
  · have hp_le_M : (p : ℝ) ≤ (M : ℝ) := by
      have : p ≤ M := le_of_not_gt hpM
      exact_mod_cast this
    have hdiv_le : ((M / p : ℕ) : ℝ) ≤ (M : ℝ) / (p : ℝ) := by
      have hmul : (M / p) * p ≤ M := Nat.div_mul_le_self M p
      have hcast : (((M / p) * p : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmul
      push_cast at hcast
      rwa [← le_div_iff₀ hp_pos] at hcast
    have h_p_ge : (M : ℝ) ^ (1 / (k : ℝ)) ≤ (p : ℝ) := by
      calc (M : ℝ) ^ (1 / (k : ℝ)) = 1 * (M : ℝ) ^ (1 / (k : ℝ)) := (one_mul _).symm
      _ ≤ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hk
      _ ≤ (p : ℝ) := hp_lo.le
    have h_div_bound : (M : ℝ) / (p : ℝ) ≤ (M : ℝ) ^ (1 - 1 / (k : ℝ)) := by
      calc (M : ℝ) / (p : ℝ) ≤ (M : ℝ) / (M : ℝ) ^ (1 / (k : ℝ)) :=
            div_le_div_of_nonneg_left hM_pos.le (by positivity) h_p_ge
      _ = (M : ℝ) * ((M : ℝ) ^ (1 / (k : ℝ)))⁻¹ := div_eq_mul_inv _ _
      _ = (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (- (1 / (k : ℝ))) := by
        rw [Real.rpow_one, Real.rpow_neg hM_pos.le]
      _ = (M : ℝ) ^ (1 + (- (1 / (k : ℝ)))) := by rw [← Real.rpow_add hM_pos]
      _ = (M : ℝ) ^ (1 - 1 / (k : ℝ)) := by congr 1
    have h1_le_div : 1 ≤ (M : ℝ) / (p : ℝ) := by
      rw [one_le_div hp_pos]
      exact hp_le_M
    have hq_le : (q : ℝ) ≤ (M : ℝ) / (p : ℝ) + 1 := by
      dsimp [q]
      push_cast
      linarith
    calc (q : ℝ) ≤ (M : ℝ) / (p : ℝ) + 1 := hq_le
    _ ≤ (M : ℝ) / (p : ℝ) + (M : ℝ) / (p : ℝ) := by linarith
    _ = 2 * ((M : ℝ) / (p : ℝ)) := by ring
    _ ≤ 2 * (M : ℝ) ^ (1 - 1 / (k : ℝ)) := by
      refine mul_le_mul_of_nonneg_left h_div_bound (by norm_num)
    _ ≤ 4 * (M : ℝ) ^ (1 - 1 / (k : ℝ)) := by
      refine mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

lemma term1_normalized_le (k ℓ M p : ℕ) (hk : 1 ≤ k) (hl : 11 * k ^ 2 ≤ ℓ)
    (hM_exp : Real.exp (100 * (k : ℝ) ^ 2) ≤ (M : ℝ))
    (hp_lo : (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < (p : ℝ))
    (hp_hi : (p : ℝ) ≤ 4 * (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ))) :
    let q := M / p + 1
    let Term₁ := ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) *
      ((p : ℝ) ^ (2 * (ℓ - k) - 1) *
        ((p : ℝ) * (M : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k) *
          (J k (ℓ - k) q : ℝ)))
    (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * Term₁ ≤
      Real.exp (30 * (ℓ : ℝ) * (k : ℝ)) * jnorm k (ℓ - k) q := by
  intro q Term₁
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hk_ge1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hM_pos : 0 < (M : ℝ) := (Real.exp_pos _).trans_le hM_exp
  have hM_ge1 : 1 ≤ (M : ℝ) := by
    have : (1 : ℝ) ≤ Real.exp 0 := by rw [Real.exp_zero]
    have : Real.exp 0 ≤ Real.exp (100 * (k : ℝ) ^ 2) := Real.exp_le_exp.mpr (by positivity)
    linarith
  have hM_nat : 1 ≤ M := by exact_mod_cast hM_ge1
  have hp_pos : 0 < (p : ℝ) := by
    have : 0 < (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := by positivity
    linarith
  have hq_ge1 : 1 ≤ q := by
    dsimp [q]
    exact Nat.le_add_left 1 _
  have hkl_sub : (k : ℝ) ≤ (ℓ : ℝ) := by
    have hl_ge : 11 * (k : ℝ) ^ 2 ≤ (ℓ : ℝ) := by exact_mod_cast hl
    calc (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    _ ≤ 11 * (k : ℝ) ^ 2 := by nlinarith
    _ ≤ (ℓ : ℝ) := hl_ge
  have hkl_nat : k ≤ ℓ := by exact_mod_cast hkl_sub
  have h_cast_sub : ((ℓ - k : ℕ) : ℝ) = (ℓ : ℝ) - (k : ℝ) := Nat.cast_sub hkl_nat
  set E := 2 * ((ℓ : ℝ) - (k : ℝ)) - (k * (k + 1) / 2 : ℝ) with hE_def
  set exp_p := 2 * ((ℓ : ℝ) - (k : ℝ)) + (k * (k - 1) / 2 : ℝ) with hexp_p_def
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    have h1 : (k : ℝ) ^ 2 ≤ 11 * (k : ℝ) ^ 2 := by nlinarith
    have h2 : 11 * (k : ℝ) ^ 2 ≤ (ℓ : ℝ) := by exact_mod_cast hl
    have h3 : (k * (k + 1) / 2 : ℝ) ≤ (k : ℝ) ^ 2 := by
      have : (k : ℝ) * ((k : ℝ) + 1) / 2 = ((k : ℝ) ^ 2 + (k : ℝ)) / 2 := by ring
      rw [this]
      have : (k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
      linarith
    linarith
  have h_J_eq : (J k (ℓ - k) q : ℝ) = (q : ℝ) ^ E * jnorm k (ℓ - k) q := by
    have hj := J_eq_rpow_mul_jnorm k (ℓ - k) q hq_ge1
    rw [h_cast_sub] at hj
    exact hj
  have h_c2 : ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k ≤ (3 : ℝ) ^ k :=
    div_add_two_pow_le_three_pow k M p hk hM_nat hp_lo
  have h_p_step : (p : ℝ) ^ (2 * (ℓ - k) - 1) * (p : ℝ) = (p : ℝ) ^ (2 * (ℓ - k)) := by
    have hk_lt_l : k < ℓ := by
      have : (k : ℝ) < 11 * (k : ℝ) ^ 2 := by nlinarith
      have : (k : ℝ) < (ℓ : ℝ) := this.trans_le (by exact_mod_cast hl)
      exact_mod_cast this
    have : 1 ≤ ℓ - k := by omega
    exact p_pow_step (p : ℝ) ℓ k this
  set exp_p_nat := 2 * (ℓ - k) + k * (k - 1) / 2 with hexp_p_nat_def
  have h_p_combine : (p : ℝ) ^ (2 * (ℓ - k) - 1) * ((p : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2))
      = (p : ℝ) ^ exp_p_nat := by
    calc (p : ℝ) ^ (2 * (ℓ - k) - 1) * ((p : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2))
      = ((p : ℝ) ^ (2 * (ℓ - k) - 1) * (p : ℝ)) * (p : ℝ) ^ (k * (k - 1) / 2) := by ring
    _ = (p : ℝ) ^ (2 * (ℓ - k)) * (p : ℝ) ^ (k * (k - 1) / 2) := by rw [h_p_step]
    _ = (p : ℝ) ^ (2 * (ℓ - k) + k * (k - 1) / 2) := by rw [← pow_add]
  have hexp_p_cast : ((exp_p_nat : ℕ) : ℝ) = exp_p := by
    dsimp [exp_p_nat, exp_p]
    push_cast
    rw [h_cast_sub]
    congr 1
    have h2dvd : 2 ∣ k * (k - 1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self k)
    rw [Nat.cast_div_charZero (K := ℝ) h2dvd]
    push_cast
    rw [Nat.cast_sub hk]
    push_cast
    rfl
  have h_p_rpow : (p : ℝ) ^ exp_p_nat = (p : ℝ) ^ exp_p := by
    rw [show (p : ℝ) ^ exp_p_nat = (p : ℝ) ^ ((exp_p_nat : ℕ) : ℝ) by exact (Real.rpow_natCast _ _).symm]
    rw [hexp_p_cast]
  have h_p_bound : (p : ℝ) ^ exp_p ≤ (4 * (k : ℝ)) ^ exp_p * (M : ℝ) ^ (exp_p / (k : ℝ)) := by
    have h_base : (p : ℝ) ≤ 4 * (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) := hp_hi
    have hexp_p_nonneg : 0 ≤ exp_p := by positivity
    have h1 := Real.rpow_le_rpow hp_pos.le h_base hexp_p_nonneg
    have h2 : (4 * (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ))) ^ exp_p
        = (4 * (k : ℝ)) ^ exp_p * ((M : ℝ) ^ (1 / (k : ℝ))) ^ exp_p := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    have h3 : ((M : ℝ) ^ (1 / (k : ℝ))) ^ exp_p = (M : ℝ) ^ (exp_p / (k : ℝ)) := by
      rw [← Real.rpow_mul hM_pos.le]
      congr 1
      ring
    rw [h2, h3] at h1
    exact h1
  have hq_bound : (q : ℝ) ^ E ≤ (4 : ℝ) ^ E * (M : ℝ) ^ ((1 - 1 / (k : ℝ)) * E) := by
    have hq_le := q_le_four_mul_rpow k M p hk hM_nat hp_lo
    have h1 := Real.rpow_le_rpow (by positivity) hq_le hE_nonneg
    have h2 : (4 * (M : ℝ) ^ (1 - 1 / (k : ℝ))) ^ E = (4 : ℝ) ^ E * ((M : ℝ) ^ (1 - 1 / (k : ℝ))) ^ E := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    have h3 : ((M : ℝ) ^ (1 - 1 / (k : ℝ))) ^ E = (M : ℝ) ^ ((1 - 1 / (k : ℝ)) * E) := by
      rw [← Real.rpow_mul hM_pos.le]
    rw [h2, h3] at h1
    exact h1
  have hM_pow_nat : (M : ℝ) ^ k = (M : ℝ) ^ (k : ℝ) := (Real.rpow_natCast (M : ℝ) k).symm
  have hM_all_cancel : (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ) *
      (M : ℝ) ^ (exp_p / (k : ℝ)) * (M : ℝ) ^ ((1 - 1 / (k : ℝ)) * E) = 1 := by
    rw [← Real.rpow_add hM_pos, ← Real.rpow_add hM_pos, ← Real.rpow_add hM_pos]
    have h_sum : ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) + (k : ℝ) + exp_p / (k : ℝ) + (1 - 1 / (k : ℝ)) * E = 0 := by
      have : ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) + (k : ℝ) = (k * (k + 1) / 2 : ℝ) - 2 * ℓ + k := by ring
      rw [this]
      have h_comm : (k * (k + 1) / 2 : ℝ) - 2 * ℓ + k + exp_p / (k : ℝ) + (1 - 1 / (k : ℝ)) * E
          = ((k * (k + 1) / 2 : ℝ) - 2 * ℓ + k) + (1 - 1 / (k : ℝ)) * E + (1 / (k : ℝ)) * exp_p := by ring
      rw [h_comm]
      exact exponent_identity (k : ℝ) (ℓ : ℝ) hk_pos.ne'
    rw [h_sum, Real.rpow_zero]
  set c₁ := ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * (k.factorial : ℝ) with hc₁_def
  set c₂ := ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k with hc₂_def
  have h_Term₁_eq : Term₁ = c₁ * c₂ * ((p : ℝ) ^ exp_p_nat * (M : ℝ) ^ (k : ℝ) * (q : ℝ) ^ E) * jnorm k (ℓ - k) q := by
    dsimp [Term₁, c₁, c₂]
    rw [h_J_eq, hM_pow_nat]
    have h_p_ring : (p : ℝ) ^ (2 * (ℓ - k) - 1) *
        ((p : ℝ) * (M : ℝ) ^ (k : ℝ) * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k) *
          ((q : ℝ) ^ E * jnorm k (ℓ - k) q))
        = (k.factorial : ℝ) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k *
          ((p : ℝ) ^ (2 * (ℓ - k) - 1) * ((p : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2)) * (M : ℝ) ^ (k : ℝ) * (q : ℝ) ^ E) *
          jnorm k (ℓ - k) q := by ring
    rw [h_p_ring, h_p_combine]
    ring
  rw [h_Term₁_eq]
  have h_assoc_M : (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) *
      (c₁ * c₂ * ((p : ℝ) ^ exp_p_nat * (M : ℝ) ^ (k : ℝ) * (q : ℝ) ^ E) * jnorm k (ℓ - k) q)
      = (c₁ * c₂) * (((p : ℝ) ^ exp_p_nat * (q : ℝ) ^ E) *
          ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ))) * jnorm k (ℓ - k) q := by ring
  rw [h_assoc_M]
  have h_middle_le : ((p : ℝ) ^ exp_p_nat * (q : ℝ) ^ E) *
      ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ))
      ≤ (4 * (k : ℝ)) ^ exp_p * (4 : ℝ) ^ E := by
    rw [h_p_rpow]
    have h_comb : ((p : ℝ) ^ exp_p * (q : ℝ) ^ E) *
        ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ))
        = ((p : ℝ) ^ exp_p) * ((q : ℝ) ^ E) *
          ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ)) := by ring
    rw [h_comb]
    have h_prod_le1 : (p : ℝ) ^ exp_p * (q : ℝ) ^ E ≤
        ((4 * (k : ℝ)) ^ exp_p * (M : ℝ) ^ (exp_p / (k : ℝ))) *
        ((4 : ℝ) ^ E * (M : ℝ) ^ ((1 - 1 / (k : ℝ)) * E)) :=
      mul_le_mul h_p_bound hq_bound (by positivity) (by positivity)
    have h_prod_le2 : (p : ℝ) ^ exp_p * (q : ℝ) ^ E * ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ)) ≤
        ((4 * (k : ℝ)) ^ exp_p * (M : ℝ) ^ (exp_p / (k : ℝ))) *
        ((4 : ℝ) ^ E * (M : ℝ) ^ ((1 - 1 / (k : ℝ)) * E)) *
        ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ)) :=
      mul_le_mul_of_nonneg_right h_prod_le1 (by positivity)
    have h_calc : ((4 * (k : ℝ)) ^ exp_p * (M : ℝ) ^ (exp_p / (k : ℝ))) *
          ((4 : ℝ) ^ E * (M : ℝ) ^ ((1 - 1 / (k : ℝ)) * E)) *
          ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ))
        = (4 * (k : ℝ)) ^ exp_p * (4 : ℝ) ^ E := by
      calc ((4 * (k : ℝ)) ^ exp_p * (M : ℝ) ^ (exp_p / (k : ℝ))) *
            ((4 : ℝ) ^ E * (M : ℝ) ^ ((1 - 1 / (k : ℝ)) * E)) *
            ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ))
        = ((4 * (k : ℝ)) ^ exp_p * (4 : ℝ) ^ E) *
          ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ) *
            (M : ℝ) ^ (exp_p / (k : ℝ)) * (M : ℝ) ^ ((1 - 1 / (k : ℝ)) * E)) := by ring
      _ = ((4 * (k : ℝ)) ^ exp_p * (4 : ℝ) ^ E) * 1 := by rw [hM_all_cancel]
      _ = (4 * (k : ℝ)) ^ exp_p * (4 : ℝ) ^ E := mul_one _
    exact h_prod_le2.trans (le_of_eq h_calc)
  have h_c_prod_le : c₁ * c₂ * (((p : ℝ) ^ exp_p_nat * (q : ℝ) ^ E) *
      ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ)))
      ≤ Real.exp (30 * (ℓ : ℝ) * (k : ℝ)) := by
    have h_c_prod1 : c₁ * c₂ ≤ c₁ * (3 : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left h_c2 (by positivity)
    have h_c_prod2 : c₁ * c₂ * (((p : ℝ) ^ exp_p_nat * (q : ℝ) ^ E) *
          ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ)))
        ≤ (c₁ * (3 : ℝ) ^ k) * ((4 * (k : ℝ)) ^ exp_p * (4 : ℝ) ^ E) :=
      mul_le_mul h_c_prod1 h_middle_le (by positivity) (by positivity)
    refine h_c_prod2.trans ?_
    have h_ring_c : (c₁ * (3 : ℝ) ^ k) * ((4 * (k : ℝ)) ^ exp_p * (4 : ℝ) ^ E)
        = ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * (k.factorial : ℝ) * (3 : ℝ) ^ k *
          (4 * (k : ℝ)) ^ exp_p * (4 : ℝ) ^ E := by
      dsimp [c₁]
      ring
    rw [h_ring_c]
    exact prefactors_bound k ℓ hk hl
  have hj_nonneg : 0 ≤ jnorm k (ℓ - k) q := by
    dsimp [jnorm]
    positivity
  calc (c₁ * c₂) * (((p : ℝ) ^ exp_p_nat * (q : ℝ) ^ E) *
        ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ))) * jnorm k (ℓ - k) q
    = (c₁ * c₂ * (((p : ℝ) ^ exp_p_nat * (q : ℝ) ^ E) *
        ((M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (M : ℝ) ^ (k : ℝ)))) * jnorm k (ℓ - k) q := by ring
  _ ≤ Real.exp (30 * (ℓ : ℝ) * (k : ℝ)) * jnorm k (ℓ - k) q :=
    mul_le_mul_of_nonneg_right h_c_prod_le hj_nonneg

lemma jnorm_le_of_C (C : ℝ) (hC11 : Real.exp 11 ≤ C) (hC_exp : 11 * 30 + 11 ≤ C) (hC100 : 100 ≤ C)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ (ℓ : ℕ), k ^ 2 ≤ ℓ → ∀ (M : ℕ), 1 ≤ M →
      jnorm k ℓ M ≤ Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * k ^ 2 * Real.exp (-(ℓ : ℝ) / k ^ 2)) := by
  have hC_nonneg : 0 ≤ C := by linarith
  have hk_pos : 0 < (k : ℝ) := by positivity
  intro ℓ
  induction' ℓ using Nat.strong_induction_on with ℓ ih
  intro hl M hM
  have hM_pos : 0 < (M : ℝ) := by positivity
  by_cases hl11 : ℓ ≤ 11 * k ^ 2
  · exact jnorm_le_base_11 C hC11 k ℓ M hk hM hl11
  · have hl_gt : 11 * k ^ 2 ≤ ℓ := by omega
    by_cases hM_lt : (M : ℝ) < Real.exp (100 * (k : ℝ) ^ 2)
    · exact jnorm_le_small_M C hC100 k ℓ M hk hl hM hM_lt
    · have hM_ge : Real.exp (100 * (k : ℝ) ^ 2) ≤ (M : ℝ) := le_of_not_gt hM_lt
      have hkl_lt : k < ℓ := by
        have : k < 11 * k ^ 2 := by nlinarith
        exact this.trans_le hl_gt
      obtain ⟨p, hp_prime, hp_lo, hp_hi, hJ⟩ := J_le_combined_sq k ℓ M hk hkl_lt hM_ge
      set q := M / p + 1 with hq_def
      have hq_ge1 : 1 ≤ q := Nat.le_add_left 1 _
      have h_lt : ℓ - k < ℓ := by omega
      have h_k2_le : k ^ 2 ≤ ℓ - k := by
        have hk_le_k2 : k ≤ k ^ 2 := by
          calc k = 1 * k := (one_mul k).symm
          _ ≤ k * k := Nat.mul_le_mul_right k hk
          _ = k ^ 2 := (sq k).symm
        omega
      have h_ih := ih (ℓ - k) h_lt h_k2_le q hq_ge1
      set Term₁ := ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) *
        ((p : ℝ) ^ (2 * (ℓ - k) - 1) *
          ((p : ℝ) * (M : ℝ) ^ k * ((k.factorial : ℝ) * (p : ℝ) ^ (k * (k - 1) / 2) * ((M : ℝ) / (p : ℝ) ^ k + 2) ^ k) *
            J k (ℓ - k) q)) with hTerm₁_def
      set Term₂ := 2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k * (M : ℝ) ^ (ℓ + k - 1) with hTerm₂_def
      have hJ_sum : (J k ℓ M : ℝ) ≤ Term₁ + Term₂ := hJ
      have h_norm_def : jnorm k ℓ M = (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * J k ℓ M := rfl
      have hM_weight_nonneg : 0 ≤ (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) := by positivity
      have hjnorm_split : jnorm k ℓ M ≤
          (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * Term₁ +
          (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * Term₂ := by
        rw [h_norm_def]
        calc (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * J k ℓ M
          ≤ (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * (Term₁ + Term₂) :=
            mul_le_mul_of_nonneg_left hJ_sum hM_weight_nonneg
        _ = (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * Term₁ +
            (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * Term₂ := mul_add _ _ _
      have h_term1_bound := term1_normalized_le k ℓ M p hk hl_gt hM_ge hp_lo hp_hi
      have h_term2_bound := term2_le_exp k ℓ M hk hl_gt hM
      have h_term2_30 : (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * Term₂ ≤ Real.exp (30 * (ℓ : ℝ) * (k : ℝ)) := by
        refine h_term2_bound.trans ?_
        apply Real.exp_le_exp.mpr
        have : 0 ≤ (ℓ : ℝ) * (k : ℝ) := by positivity
        nlinarith
      set α := C * (k : ℝ) ^ 2 * Real.exp (-((ℓ - k : ℕ) : ℝ) / (k : ℝ) ^ 2) with hα_def
      set β := C * (k : ℝ) ^ 2 * Real.exp (-(ℓ : ℝ) / (k : ℝ) ^ 2) with hβ_def
      have h_ih_cast : jnorm k (ℓ - k) q ≤ Real.exp (C * ((ℓ - k : ℕ) : ℝ) ^ 2) * (q : ℝ) ^ α := by
        have := h_ih
        rw [show (ℓ - k : ℕ) ^ 2 = ((ℓ - k : ℕ) : ℝ) ^ 2 by rfl] at this
        exact this
      have hq_bound := q_le_four_mul_rpow k M p hk hM hp_lo
      have h_q_pow := q_pow_le C hC_nonneg k ℓ hk hkl_lt.le M q hM hq_ge1 hq_bound
      have hj_q_bound : jnorm k (ℓ - k) q ≤ Real.exp (C * ((ℓ - k : ℕ) : ℝ) ^ 2) *
          (Real.exp (2 * C * (k : ℝ) ^ 2) * (M : ℝ) ^ β) := by
        calc jnorm k (ℓ - k) q ≤ Real.exp (C * ((ℓ - k : ℕ) : ℝ) ^ 2) * (q : ℝ) ^ α := h_ih_cast
        _ ≤ Real.exp (C * ((ℓ - k : ℕ) : ℝ) ^ 2) *
            (Real.exp (2 * C * (k : ℝ) ^ 2) * (M : ℝ) ^ β) :=
          mul_le_mul_of_nonneg_left h_q_pow (by positivity)
      have h_term1_full : (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * Term₁ ≤
          Real.exp (30 * (ℓ : ℝ) * (k : ℝ)) *
            (Real.exp (C * ((ℓ - k : ℕ) : ℝ) ^ 2) * (Real.exp (2 * C * (k : ℝ) ^ 2) * (M : ℝ) ^ β)) := by
        refine h_term1_bound.trans ?_
        exact mul_le_mul_of_nonneg_left hj_q_bound (by positivity)
      have h_sum_le : (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * Term₁ +
          (M : ℝ) ^ ((k * (k + 1) / 2 : ℝ) - 2 * ℓ) * Term₂ ≤
          Real.exp (30 * (ℓ : ℝ) * (k : ℝ)) *
            (Real.exp (C * ((ℓ - k : ℕ) : ℝ) ^ 2) * (Real.exp (2 * C * (k : ℝ) ^ 2) * (M : ℝ) ^ β)) +
          Real.exp (30 * (ℓ : ℝ) * (k : ℝ)) :=
        add_le_add h_term1_full h_term2_30
      refine hjnorm_split.trans (h_sum_le.trans ?_)
      have h_exp_sum := exp_sum_le_exp C 30 (by norm_num) hC_exp k ℓ hk hkl_lt.le hl_gt M hM
      exact h_exp_sum

theorem jnorm_le : ∃ C : ℝ, 0 < C ∧ ∀ (k ℓ M : ℕ), 1 ≤ k → k ^ 2 ≤ ℓ → 1 ≤ M →
    jnorm k ℓ M ≤ Real.exp (C * ℓ ^ 2) * (M : ℝ) ^ (C * k ^ 2 * Real.exp (-(ℓ : ℝ) / k ^ 2)) := by
  set C := Real.exp 12 + 441 with hC_def
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, ?_⟩
  intro k ℓ M hk hl hM
  have hC11 : Real.exp 11 ≤ C := by
    have : Real.exp 11 ≤ Real.exp 12 := Real.exp_le_exp.mpr (by norm_num)
    linarith [show 0 ≤ (441 : ℝ) by norm_num]
  have hC_exp : 11 * 30 + 11 ≤ C := by
    have : 0 ≤ Real.exp 12 := (Real.exp_pos 12).le
    linarith
  have hC100 : 100 ≤ C := by
    have : 0 ≤ Real.exp 12 := (Real.exp_pos 12).le
    linarith
  exact jnorm_le_of_C C hC11 hC_exp hC100 k hk ℓ hl M hM

end Erdos1201.MR.Vinogradov

