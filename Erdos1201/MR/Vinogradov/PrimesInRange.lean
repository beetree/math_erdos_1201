/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

Attribution: the original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
-/
import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Existence of primes in short geometric intervals

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

This module proves that for any `k ≥ 1` and `M ≥ exp(100 k^3)`, there exists a finset `P` of
primes in `(k M^(1/k), 4 k M^(1/k)]` with cardinality `|P| > k^3`.
-/

open Real Finset

namespace Erdos1201.MR.Vinogradov

/-- The logarithm of `√x` is bounded by `√x`. -/
lemma log_sqrt_le {x : ℝ} (hx : 0 < x) : Real.log (Real.sqrt x) ≤ Real.sqrt x := by
  have hpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos hpos
  linarith

/-- The logarithm of `x` is bounded by `2 √x`. -/
lemma log_le_two_mul_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt (le_of_lt hx)]
    ring
  rw [h]
  have := log_sqrt_le hx
  linarith

/-- If `B^2 ≤ x` with `0 < B`, then `√x ≤ x / B`. -/
lemma sqrt_le_div_of_sq_le {x B : ℝ} (hB : 0 < B) (h : B ^ 2 ≤ x) : Real.sqrt x ≤ x / B := by
  have hx : 0 ≤ x := (sq_nonneg B).trans h
  have hB_le : B ≤ Real.sqrt x := by
    rw [← Real.sqrt_sq (le_of_lt hB)]
    exact Real.sqrt_le_sqrt h
  have hmul : B * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := by
    nlinarith [Real.sqrt_nonneg x]
  rw [Real.mul_self_sqrt hx] at hmul
  exact (le_div_iff₀ hB).mpr (by linarith)

/-- Logarithm upper bound `log x ≤ x / C + C` for any `x > 0` and `C > 0`. -/
lemma log_le_div_add (x C : ℝ) (hx : 0 < x) (hC : 0 < C) : Real.log x ≤ x / C + C := by
  have hpos : 0 < x / C := div_pos hx hC
  have h := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div hx.ne' hC.ne'] at h
  have hlogC : Real.log C ≤ C := Real.log_le_self hC.le
  linarith

/-- Bounding the lower-order terms in Chebyshev's lower bound for `x ≥ 40000^2`. -/
lemma lower_order_terms_le (x : ℝ) (hx_le : (40000 : ℝ) ^ 2 ≤ x) :
    Real.log 2 + Real.log (x + 2) + 2 * Real.sqrt x * Real.log x ≤ (7 / 100 : ℝ) * x := by
  have hx_pos : 0 < x := by
    have : (0 : ℝ) < (40000 : ℝ) ^ 2 := by norm_num
    linarith
  have hx0 : 0 ≤ x := le_of_lt hx_pos
  have h_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have hlog_sqrt : Real.log (Real.sqrt x) ≤ Real.sqrt x / 100 + 100 :=
    log_le_div_add (Real.sqrt x) 100 h_sqrt_pos (by norm_num)
  have hlogx_eq : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0]
    ring
  have hlogx : Real.log x ≤ Real.sqrt x / 50 + 200 := by
    calc Real.log x = 2 * Real.log (Real.sqrt x) := hlogx_eq
    _ ≤ 2 * (Real.sqrt x / 100 + 100) := by linarith
    _ = Real.sqrt x / 50 + 200 := by ring
  have h_two_sqrt_mul : 2 * Real.sqrt x * Real.log x ≤ (5 / 100 : ℝ) * x := by
    have h1 : 2 * Real.sqrt x * Real.log x ≤ 2 * Real.sqrt x * (Real.sqrt x / 50 + 200) := by
      nlinarith [Real.sqrt_nonneg x]
    have h2 : 2 * Real.sqrt x * (Real.sqrt x / 50 + 200) = x / 25 + 400 * Real.sqrt x := by
      calc 2 * Real.sqrt x * (Real.sqrt x / 50 + 200)
        = (Real.sqrt x * Real.sqrt x) / 25 + 400 * Real.sqrt x := by ring
        _ = x / 25 + 400 * Real.sqrt x := by rw [Real.mul_self_sqrt hx0]
    have h3 : 400 * Real.sqrt x ≤ x / 100 := by
      have h_sqrt_div : Real.sqrt x ≤ x / 40000 := sqrt_le_div_of_sq_le (by norm_num) hx_le
      calc 400 * Real.sqrt x ≤ 400 * (x / 40000) := by linarith
      _ = x / 100 := by ring
    linarith
  have hlog_x2 : Real.log (x + 2) ≤ x / 100 + 101 := by
    have h := log_le_div_add (x + 2) 100 (by linarith) (by norm_num : (0 : ℝ) < 100)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9
    linarith
  have h102 : (102 : ℝ) ≤ x / 100 := by
    calc (102 : ℝ) ≤ (40000 : ℝ) ^ 2 / 100 := by norm_num
    _ ≤ x / 100 := by linarith
  linarith

/-- The Chebyshev difference `θ(4y) - θ(y)` is at least `y` when `40000^2 ≤ 4y`. -/
lemma y_le_theta_four_mul_sub_theta (y : ℝ) (hy_le : (40000 : ℝ) ^ 2 ≤ 4 * y) :
    y ≤ Chebyshev.theta (4 * y) - Chebyshev.theta y := by
  have hy_pos : 0 < y := by
    have : (0 : ℝ) < (40000 : ℝ) ^ 2 := by norm_num
    linarith
  have h4y_ge1 : 1 ≤ 4 * y := by
    have : (1 : ℝ) ≤ (40000 : ℝ) ^ 2 := by norm_num
    linarith
  have h_theta_ge := Chebyshev.theta_ge' h4y_ge1
  have h_theta_le := Chebyshev.theta_le_log4_mul_x hy_pos.le
  rw [Real.log_four_eq] at h_theta_le
  have h_low := lower_order_terms_le (4 * y) hy_le
  have h_log2_gt : (0.69 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  calc y ≤ (2 * Real.log 2 - 28 / 100) * y := by
        have : (1 : ℝ) ≤ 2 * Real.log 2 - 28 / 100 := by linarith
        nlinarith
    _ = 4 * y * Real.log 2 - (28 / 100) * y - 2 * y * Real.log 2 := by ring
    _ ≤ 4 * y * Real.log 2 - (Real.log 2 + Real.log (4 * y + 2) + 2 * Real.sqrt (4 * y) * Real.log (4 * y)) -
        2 * y * Real.log 2 := by
        have : (28 / 100 : ℝ) * y = (7 / 100 : ℝ) * (4 * y) := by ring
        linarith
    _ = ((4 * y - 1) * Real.log 2 - Real.log (4 * y + 2) - 2 * Real.sqrt (4 * y) * Real.log (4 * y)) -
        (2 * Real.log 2 * y) := by ring
    _ ≤ Chebyshev.theta (4 * y) - Chebyshev.theta y := by linarith

/-- The Chebyshev difference `θ(4y) - θ(y)` equals the sum of `log p` over primes in `(y, 4y]`. -/
lemma theta_sub_theta_eq_sum_primes (y : ℝ) (hy : 0 ≤ y) :
    let P := (Finset.Ioc ⌊y⌋₊ ⌊4 * y⌋₊).filter Nat.Prime
    Chebyshev.theta (4 * y) - Chebyshev.theta y = ∑ p ∈ P, Real.log (p : ℝ) := by
  intro P
  have hle : ⌊y⌋₊ ≤ ⌊4 * y⌋₊ := Nat.floor_le_floor (by linarith)
  have hdisj : Disjoint (Finset.Ioc 0 ⌊y⌋₊) (Finset.Ioc ⌊y⌋₊ ⌊4 * y⌋₊) :=
    Finset.Ioc_disjoint_Ioc_of_le le_rfl
  have hunion : Finset.Ioc 0 ⌊y⌋₊ ∪ Finset.Ioc ⌊y⌋₊ ⌊4 * y⌋₊ = Finset.Ioc 0 ⌊4 * y⌋₊ :=
    Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hle
  have hfilter : (Finset.Ioc 0 ⌊4 * y⌋₊).filter Nat.Prime =
      (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime ∪ P := by
    dsimp [P]
    rw [← hunion, Finset.filter_union]
  have hdisj' : Disjoint ((Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime) P :=
    hdisj.mono (filter_subset _ _) (filter_subset _ _)
  have hsum : ∑ p ∈ (Finset.Ioc 0 ⌊4 * y⌋₊).filter Nat.Prime, Real.log (p : ℝ) =
      (∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime, Real.log (p : ℝ)) + ∑ p ∈ P, Real.log (p : ℝ) := by
    rw [hfilter, Finset.sum_union hdisj']
  have hP1 : (Finset.Ioc 0 ⌊y⌋₊).filter Nat.Prime = Nat.primesLE ⌊y⌋₊ :=
    (Nat.primesLE_eq_filter_Ioc_zero _).symm
  have hP2 : (Finset.Ioc 0 ⌊4 * y⌋₊).filter Nat.Prime = Nat.primesLE ⌊4 * y⌋₊ :=
    (Nat.primesLE_eq_filter_Ioc_zero _).symm
  rw [hP1, hP2] at hsum
  have ht1 : Chebyshev.theta y = ∑ p ∈ Nat.primesLE ⌊y⌋₊, Real.log (p : ℝ) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, Chebyshev.theta_eq_sum_primesLE_log]
  have ht2 : Chebyshev.theta (4 * y) = ∑ p ∈ Nat.primesLE ⌊4 * y⌋₊, Real.log (p : ℝ) := by
    rw [Chebyshev.theta_eq_theta_coe_floor, Chebyshev.theta_eq_sum_primesLE_log]
  linarith

/-- The sum of `log p` over primes in `(y, 4y]` is at most `|P| * log(4y)`. -/
lemma sum_primes_le_card_mul_log (y : ℝ) (hy : 1 ≤ y) :
    let P := (Finset.Ioc ⌊y⌋₊ ⌊4 * y⌋₊).filter Nat.Prime
    ∑ p ∈ P, Real.log (p : ℝ) ≤ (P.card : ℝ) * Real.log (4 * y) := by
  intro P
  have hle : ∀ p ∈ P, Real.log (p : ℝ) ≤ Real.log (4 * y) := by
    intro p hp
    have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
    have hp_ioc : p ∈ Finset.Ioc ⌊y⌋₊ ⌊4 * y⌋₊ := (Finset.mem_filter.mp hp).1
    have hp_le : p ≤ ⌊4 * y⌋₊ := (Finset.mem_Ioc.mp hp_ioc).2
    have hp_le_real : (p : ℝ) ≤ 4 * y := le_trans (Nat.cast_le.mpr hp_le) (Nat.floor_le (by linarith))
    have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos
    exact Real.log_le_log hp_pos hp_le_real
  calc ∑ p ∈ P, Real.log (p : ℝ) ≤ ∑ _p ∈ P, Real.log (4 * y) := Finset.sum_le_sum hle
  _ = (P.card : ℝ) * Real.log (4 * y) := by rw [Finset.sum_const, nsmul_eq_mul]

/-- `exp(100 k^2) ≤ M^(1/k)` when `exp(100 k^3) ≤ M` and `1 ≤ k`. -/
lemma exp_hundred_k_sq_le_rpow (k M : ℕ) (hk : 1 ≤ k) (hM : Real.exp (100 * (k : ℝ) ^ 3) ≤ M) :
    Real.exp (100 * (k : ℝ) ^ 2) ≤ (M : ℝ) ^ (1 / (k : ℝ)) := by
  have hk_pos : 0 < (k : ℝ) := by positivity
  have h_exp_nonneg : 0 ≤ Real.exp (100 * (k : ℝ) ^ 3) := (Real.exp_pos _).le
  have h_exp_le_M : Real.exp (100 * (k : ℝ) ^ 3) ≤ (M : ℝ) := hM
  have h_pow := Real.rpow_le_rpow h_exp_nonneg h_exp_le_M (one_div_pos.mpr hk_pos).le
  have h_exp_pow : (Real.exp (100 * (k : ℝ) ^ 3)) ^ (1 / (k : ℝ)) =
      Real.exp (100 * (k : ℝ) ^ 2) := by
    rw [← Real.exp_mul]
    congr 1
    calc 100 * (k : ℝ) ^ 3 * (1 / (k : ℝ)) = 100 * ((k : ℝ) ^ 3 * (1 / (k : ℝ))) := by ring
    _ = 100 * (k : ℝ) ^ 2 := by
      congr 1
      rw [show (k : ℝ) ^ 3 = (k : ℝ) ^ 2 * (k : ℝ) by ring]
      rw [mul_assoc, mul_one_div_cancel hk_pos.ne', mul_one]
  rwa [h_exp_pow] at h_pow

/-- Explicit numerical lower bound `40000^2 ≤ 4 exp(100)`. -/
lemma sq_forty_thousand_le_four_mul_exp_hundred :
    (40000 : ℝ) ^ 2 ≤ 4 * Real.exp 100 := by
  have h := Real.pow_div_factorial_le_exp 100 (by norm_num : (0 : ℝ) ≤ 100) 7
  have h7 : Nat.factorial 7 = 5040 := rfl
  have h_bound : (40000 : ℝ) ^ 2 ≤ 4 * ((100 : ℝ) ^ 7 / Nat.factorial 7) := by
    rw [h7]
    norm_num
  linarith

/-- `k^3 * log(4y) < y` for `y = k Y` with `Y ≥ exp(100 k^2)` and `k ≥ 1`. -/
lemma k_pow_three_mul_log_lt_y (k : ℕ) (hk : 1 ≤ k) (Y : ℝ) (hY : Real.exp (100 * (k : ℝ) ^ 2) ≤ Y) :
    let y := (k : ℝ) * Y
    (k : ℝ) ^ 3 * Real.log (4 * y) < y := by
  intro y
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hY_pos : 0 < Y := by
    have : 0 < Real.exp (100 * (k : ℝ) ^ 2) := Real.exp_pos _
    linarith
  have h_exp_ge : 100 * (k : ℝ) ^ 2 ≤ Real.exp (100 * (k : ℝ) ^ 2) := by
    have := Real.add_one_le_exp (100 * (k : ℝ) ^ 2)
    linarith
  have h_4k_le_Y : 4 * (k : ℝ) ≤ Y := by
    have h1 : 4 * (k : ℝ) ≤ 100 * (k : ℝ) ^ 2 := by
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
  have h_exp_taylor := Real.pow_div_factorial_le_exp (100 * (k : ℝ) ^ 2) (by positivity) 3
  have h3 : Nat.factorial 3 = 6 := rfl
  have h_16k4_lt_Y : 16 * (k : ℝ) ^ 4 < Y := by
    have h_poly : 16 * (k : ℝ) ^ 4 < (100 * (k : ℝ) ^ 2) ^ 3 / Nat.factorial 3 := by
      rw [h3]
      have : (100 * (k : ℝ) ^ 2) ^ 3 = 1000000 * (k : ℝ) ^ 6 := by ring
      rw [this]
      have hk_pow_pos : 0 < (k : ℝ) ^ 4 := by positivity
      have hk2_ge : 1 ≤ (k : ℝ) ^ 2 := by nlinarith
      have hk6 : (k : ℝ) ^ 4 ≤ (k : ℝ) ^ 6 := by
        calc (k : ℝ) ^ 4 = (k : ℝ) ^ 4 * 1 := by ring
        _ ≤ (k : ℝ) ^ 4 * (k : ℝ) ^ 2 := by nlinarith
        _ = (k : ℝ) ^ 6 := by ring
      have h_const : (160000 : ℝ) ≤ 1000000 / 6 := by norm_num
      calc 16 * (k : ℝ) ^ 4 < 160000 * (k : ℝ) ^ 4 := by nlinarith
      _ ≤ 160000 * (k : ℝ) ^ 6 := by nlinarith
      _ ≤ 1000000 * (k : ℝ) ^ 6 / 6 := by nlinarith [show 0 ≤ (k : ℝ) ^ 6 by positivity]
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

/-- There are more than `k^3` primes in `(k M^(1/k), 4 k M^(1/k)]` once `M ≥ exp(100 k^3)`. -/
theorem exists_primes_finset_in_range (k M : ℕ) (hk : 1 ≤ k) (hM : Real.exp (100 * (k : ℝ) ^ 3) ≤ M) :
    ∃ P : Finset ℕ, (k : ℝ) ^ 3 < P.card ∧ ∀ p ∈ P, p.Prime ∧ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < p ∧ (p : ℝ) ≤ 4 * k * (M : ℝ) ^ (1 / (k : ℝ)) := by
  have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  set Y := (M : ℝ) ^ (1 / (k : ℝ)) with hY_def
  set y := (k : ℝ) * Y with hy_def
  have hY_ge : Real.exp (100 * (k : ℝ) ^ 2) ≤ Y := exp_hundred_k_sq_le_rpow k M hk hM
  have h_exp100_le : Real.exp 100 ≤ Real.exp (100 * (k : ℝ) ^ 2) := by
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
      k_pow_three_mul_log_lt_y k hk Y hY_ge
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

end Erdos1201.MR.Vinogradov
