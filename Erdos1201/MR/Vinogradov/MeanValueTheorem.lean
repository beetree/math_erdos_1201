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

end Erdos1201.MR.Vinogradov
