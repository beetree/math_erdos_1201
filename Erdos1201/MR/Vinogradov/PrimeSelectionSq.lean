/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

Attribution: the original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
-/
import Mathlib
import Erdos1201.MR.Vinogradov.PrimesInRange
import Erdos1201.MR.Vinogradov.PrimeSelectionAssembly
import Erdos1201.MR.Vinogradov.PrimeSelectionFinal3

/-!
# Vinogradov Prime Selection with relaxed lower bound $M \ge \exp(100 k^2)$

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

This module proves that the prime selection theorems of `PrimesInRange` and
`PrimeSelectionAssembly` hold under the relaxed hypothesis $M \ge \exp(100 k^2)$ instead
of $M \ge \exp(100 k^3)$.
-/

open Real Finset

namespace Erdos1201.MR.Vinogradov

/-- `exp(100 k) ≤ M^(1/k)` when `exp(100 k^2) ≤ M` and `1 ≤ k`. -/
lemma exp_hundred_k_le_rpow (k M : ℕ) (hk : 1 ≤ k) (hM : Real.exp (100 * (k : ℝ) ^ 2) ≤ M) :
    Real.exp (100 * (k : ℝ)) ≤ (M : ℝ) ^ (1 / (k : ℝ)) := by
  have hk_pos : 0 < (k : ℝ) := by positivity
  have h_exp_nonneg : 0 ≤ Real.exp (100 * (k : ℝ) ^ 2) := (Real.exp_pos _).le
  have h_exp_le_M : Real.exp (100 * (k : ℝ) ^ 2) ≤ (M : ℝ) := hM
  have h_pow := Real.rpow_le_rpow h_exp_nonneg h_exp_le_M (one_div_pos.mpr hk_pos).le
  have h_exp_pow : (Real.exp (100 * (k : ℝ) ^ 2)) ^ (1 / (k : ℝ)) =
      Real.exp (100 * (k : ℝ)) := by
    rw [← Real.exp_mul]
    congr 1
    calc 100 * (k : ℝ) ^ 2 * (1 / (k : ℝ)) = 100 * ((k : ℝ) ^ 2 * (1 / (k : ℝ))) := by ring
    _ = 100 * (k : ℝ) := by
      congr 1
      rw [show (k : ℝ) ^ 2 = (k : ℝ) * (k : ℝ) by ring]
      rw [mul_assoc, mul_one_div_cancel hk_pos.ne', mul_one]
  rwa [h_exp_pow] at h_pow

/-- `k^3 * log(4y) < y` for `y = k Y` with `Y ≥ exp(100 k)` and `k ≥ 1`. -/
lemma k_pow_three_mul_log_lt_y_sq (k : ℕ) (hk : 1 ≤ k) (Y : ℝ) (hY : Real.exp (100 * (k : ℝ)) ≤ Y) :
    let y := (k : ℝ) * Y
    (k : ℝ) ^ 3 * Real.log (4 * y) < y := by
  intro y
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hY_pos : 0 < Y := by
    have : 0 < Real.exp (100 * (k : ℝ)) := Real.exp_pos _
    linarith
  have h_exp_ge : 100 * (k : ℝ) ≤ Real.exp (100 * (k : ℝ)) := by
    have := Real.add_one_le_exp (100 * (k : ℝ))
    linarith
  have h_4k_le_Y : 4 * (k : ℝ) ≤ Y := by
    have h1 : 4 * (k : ℝ) ≤ 100 * (k : ℝ) := by
      nlinarith
    linarith
  have h_4kY_le_YY : 4 * (k : ℝ) * Y ≤ Y * Y := by
    nlinarith
  have h_log_4kY : Real.log (4 * y) ≤ 2 * Real.log Y := by
    dsimp [y]
    have h_assoc : 4 * ((k : ℝ) * Y) = 4 * (k : ℝ) * Y := by ring
    rw [h_assoc]
    have hlog_le := Real.log_le_log (by positivity) h_4kY_le_YY
    have hlog_mul : Real.log (Y * Y) = 2 * Real.log Y := by
      rw [Real.log_mul hY_pos.ne' hY_pos.ne']
      ring
    linarith
  have h_exp_taylor := Real.pow_div_factorial_le_exp (100 * (k : ℝ)) (by positivity) 5
  have h5 : Nat.factorial 5 = 120 := rfl
  have h_16k4_lt_Y : 16 * (k : ℝ) ^ 4 < Y := by
    have h_poly : 16 * (k : ℝ) ^ 4 < (100 * (k : ℝ)) ^ 5 / Nat.factorial 5 := by
      rw [h5]
      have : (100 * (k : ℝ)) ^ 5 = 10000000000 * (k : ℝ) ^ 5 := by ring
      rw [this]
      have hk_pow_pos : 0 < (k : ℝ) ^ 4 := by positivity
      have hk_ge : 1 ≤ (k : ℝ) := hk1
      have hk5 : (k : ℝ) ^ 4 ≤ (k : ℝ) ^ 5 := by
        calc (k : ℝ) ^ 4 = (k : ℝ) ^ 4 * 1 := by ring
        _ ≤ (k : ℝ) ^ 4 * (k : ℝ) := by nlinarith
        _ = (k : ℝ) ^ 5 := by ring
      have h_const : (16 : ℝ) < 10000000000 / 120 := by norm_num
      calc 16 * (k : ℝ) ^ 4 ≤ 16 * (k : ℝ) ^ 5 := by nlinarith
      _ < (10000000000 / 120 : ℝ) * (k : ℝ) ^ 5 := by nlinarith
      _ = 10000000000 * (k : ℝ) ^ 5 / 120 := by ring
    linarith
  have h_4k2_lt_sqrtY : 4 * (k : ℝ) ^ 2 < Real.sqrt Y := by
    by_contra! hle
    have hsq : Y ≤ (4 * (k : ℝ) ^ 2) ^ 2 := by
      calc Y = (Real.sqrt Y) ^ 2 := (Real.sq_sqrt hY_pos.le).symm
      _ ≤ (4 * (k : ℝ) ^ 2) ^ 2 := by nlinarith [Real.sqrt_nonneg Y]
    have h_ring : (4 * (k : ℝ) ^ 2) ^ 2 = 16 * (k : ℝ) ^ 4 := by ring
    rw [h_ring] at hsq
    linarith
  have h_4k2_mul_sqrt_lt_Y : 4 * (k : ℝ) ^ 2 * Real.sqrt Y < Y := by
    calc 4 * (k : ℝ) ^ 2 * Real.sqrt Y < Real.sqrt Y * Real.sqrt Y := by
          nlinarith [Real.sqrt_pos.mpr hY_pos]
    _ = Y := Real.mul_self_sqrt hY_pos.le
  have h_logY_le : Real.log Y ≤ 2 * Real.sqrt Y := log_le_two_mul_sqrt hY_pos
  have h_k2_log_lt_Y : (k : ℝ) ^ 2 * Real.log (4 * y) < Y := by
    calc (k : ℝ) ^ 2 * Real.log (4 * y) ≤ (k : ℝ) ^ 2 * (2 * Real.log Y) := by
          have : 0 ≤ (k : ℝ) ^ 2 := by positivity
          nlinarith
    _ = 2 * (k : ℝ) ^ 2 * Real.log Y := by ring
    _ ≤ 2 * (k : ℝ) ^ 2 * (2 * Real.sqrt Y) := by
          have : 0 ≤ 2 * (k : ℝ) ^ 2 := by positivity
          nlinarith
    _ = 4 * (k : ℝ) ^ 2 * Real.sqrt Y := by ring
    _ < Y := h_4k2_mul_sqrt_lt_Y
  dsimp [y]
  calc (k : ℝ) ^ 3 * Real.log (4 * ((k : ℝ) * Y))
      = (k : ℝ) * ((k : ℝ) ^ 2 * Real.log (4 * ((k : ℝ) * Y))) := by ring
  _ < (k : ℝ) * Y := by
      have : (k : ℝ) ^ 2 * Real.log (4 * ((k : ℝ) * Y)) < Y := h_k2_log_lt_Y
      nlinarith

/-- There are more than `k^3` primes in `(k M^(1/k), 4 k M^(1/k)]` once `M ≥ exp(100 k^2)`. -/
theorem exists_primes_finset_in_range_sq (k M : ℕ) (hk : 1 ≤ k) (hM : Real.exp (100 * (k : ℝ) ^ 2) ≤ M) :
    ∃ P : Finset ℕ, (k : ℝ) ^ 3 < P.card ∧ ∀ p ∈ P, p.Prime ∧ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < p ∧ (p : ℝ) ≤ 4 * k * (M : ℝ) ^ (1 / (k : ℝ)) := by
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  set Y := (M : ℝ) ^ (1 / (k : ℝ)) with hY_def
  set y := (k : ℝ) * Y with hy_def
  have hY_ge : Real.exp (100 * (k : ℝ)) ≤ Y := exp_hundred_k_le_rpow k M hk hM
  have h_exp100_le : Real.exp 100 ≤ Real.exp (100 * (k : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hY_pos : 0 < Y := by
    have : 0 < Real.exp 100 := Real.exp_pos 100
    linarith
  have hy_ge1 : 1 ≤ y := by
    have : Real.exp 100 ≤ y := by
      calc Real.exp 100 ≤ Y := by linarith
      _ ≤ (k : ℝ) * Y := by nlinarith
    have : 1 ≤ Real.exp 100 := (Real.one_le_exp_iff).mpr (by norm_num)
    linarith
  have h4y_ge_sq : (40000 : ℝ) ^ 2 ≤ 4 * y := by
    calc (40000 : ℝ) ^ 2 ≤ 4 * Real.exp 100 := sq_forty_thousand_le_four_mul_exp_hundred
    _ ≤ 4 * Y := by nlinarith
    _ ≤ 4 * y := by
      dsimp [y]
      have : Y ≤ (k : ℝ) * Y := by nlinarith
      linarith
  set P := (Finset.Ioc ⌊y⌋₊ ⌊4 * y⌋₊).filter Nat.Prime with hP_def
  refine ⟨P, ?_, ?_⟩
  · -- Prove (k : ℝ) ^ 3 < P.card
    have h_theta_diff : y ≤ Chebyshev.theta (4 * y) - Chebyshev.theta y :=
      y_le_theta_four_mul_sub_theta y h4y_ge_sq
    have h_sum_eq : Chebyshev.theta (4 * y) - Chebyshev.theta y = ∑ p ∈ P, Real.log (p : ℝ) :=
      theta_sub_theta_eq_sum_primes y (by positivity)
    have h_sum_le : ∑ p ∈ P, Real.log (p : ℝ) ≤ (P.card : ℝ) * Real.log (4 * y) :=
      sum_primes_le_card_mul_log y hy_ge1
    have hy_le_card_mul : y ≤ (P.card : ℝ) * Real.log (4 * y) := by
      linarith
    have h_k3_log_lt_y : (k : ℝ) ^ 3 * Real.log (4 * y) < y :=
      k_pow_three_mul_log_lt_y_sq k hk Y hY_ge
    have h_lt : (k : ℝ) ^ 3 * Real.log (4 * y) < (P.card : ℝ) * Real.log (4 * y) :=
      lt_of_lt_of_le h_k3_log_lt_y hy_le_card_mul
    have h4y_gt1 : 1 < 4 * y := by
      have : (1 : ℝ) < (40000 : ℝ) ^ 2 := by norm_num
      linarith
    have hlog_pos : 0 < Real.log (4 * y) := Real.log_pos h4y_gt1
    nlinarith
  · -- Prove range conditions
    intro p hp
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp_ioc : p ∈ Finset.Ioc ⌊y⌋₊ ⌊4 * y⌋₊ := (Finset.mem_filter.mp hp).1
    refine ⟨hp_prime, ?_, ?_⟩
    · have hp_gt := (Finset.mem_Ioc.mp hp_ioc).1
      have : 0 ≤ y := by positivity
      rwa [Nat.floor_lt this] at hp_gt
    · have hp_le := (Finset.mem_Ioc.mp hp_ioc).2
      have hp_le_real : (p : ℝ) ≤ 4 * y :=
        le_trans (Nat.cast_le.mpr hp_le) (Nat.floor_le (by positivity))
      have h_assoc : 4 * y = 4 * k * (M : ℝ) ^ (1 / (k : ℝ)) := by
        dsimp [y, Y]
        ring
      rwa [h_assoc] at hp_le_real

/-- M exceeds 1 when log M ≥ 100 * k^2. -/
lemma one_lt_M_of_hM_sq {k M : ℕ} (hk : 1 ≤ k) (hM : Real.exp (100 * (k : ℝ) ^ 2) ≤ M) : 1 < M := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have h100 : (100 : ℝ) ≤ 100 * (k : ℝ) ^ 2 := by nlinarith
  have h_exp : Real.exp 100 ≤ (M : ℝ) := (Real.exp_le_exp.mpr h100).trans hM
  have : (2 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have : (2 : ℝ) ≤ (M : ℝ) := this.trans h_exp
  exact_mod_cast (by linarith : 1 < (M : ℝ))

/-- Tao's Lemma 14 (Vinogradov prime selection): for `M ≥ exp(100 k^2)` and `k ≤ ℓ`,
there exists a prime `p` in `(k M^(1/k), 4 k M^(1/k)]` such that
`J k ℓ M ≤ (k^3 + 1) ℓ^(2k) J^{(p)} + 2 k^ℓ ℓ^k M^(ℓ+k-1)`. -/
theorem exists_prime_J_le_sq (k ℓ M : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ) (hM : Real.exp (100 * (k : ℝ) ^ 2) ≤ M) :
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < p ∧ (p : ℝ) ≤ 4 * k * (M : ℝ) ^ (1 / (k : ℝ)) ∧
      (J k ℓ M : ℝ) ≤ ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * Jp k ℓ M p hkl + 2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k * M ^ (ℓ + k - 1) := by
  obtain ⟨P, hP_card, hP_all⟩ := exists_primes_finset_in_range_sq k M hk hM
  have hk3_lt : k ^ 3 < P.card := by exact_mod_cast hP_card
  have hk3_le : k ^ 3 + 1 ≤ P.card := Nat.succ_le_of_lt hk3_lt
  obtain ⟨P₀, hP₀_sub, hP₀_card⟩ := Finset.exists_subset_card_eq hk3_le
  have hP₀_card_real : (k : ℝ) ^ 3 < (P₀.card : ℝ) := by
    rw [hP₀_card]
    push_cast
    linarith
  have hP₀_prime : ∀ p ∈ P₀, Nat.Prime p := fun p hp => (hP_all p (hP₀_sub hp)).1
  have hP₀_range : ∀ p ∈ P₀, (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < p ∧
      (p : ℝ) ≤ 4 * k * (M : ℝ) ^ (1 / (k : ℝ)) := fun p hp => (hP_all p (hP₀_sub hp)).2
  have h1M : 1 < M := one_lt_M_of_hM_sq hk hM
  obtain ⟨p, hpP₀, hJ_le⟩ := exists_prime_J_le_of_primes k ℓ M hk hkl h1M P₀ hP₀_card_real hP₀_prime hP₀_range
  have hpP := hP₀_sub hpP₀
  refine ⟨p, (hP_all p hpP).1, (hP_all p hpP).2.1, (hP_all p hpP).2.2, ?_⟩
  rw [hP₀_card] at hJ_le
  push_cast at hJ_le
  exact hJ_le

end Erdos1201.MR.Vinogradov
