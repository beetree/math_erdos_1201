/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Chebyshev
import Erdos1201.Vendor.NumberTheory.SelbergSieve.BrunTitchmarsh

/-!
# Short-range prime mass via the Brun–Titchmarsh inequality

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module bounds the prime reciprocal mass and reciprocal square mass in short multiplicative
ranges `(⌊P⌋₊, ⌊P e^{1/H}⌋₊]` using the Selberg sieve / Brun–Titchmarsh inequality, achieving
the saving factor `1 / H`.
-/

open Finset BrunTitchmarsh

namespace Erdos1201.MR

/-- The exponential function satisfies `exp u - 1 ≤ 3 * u` for `0 ≤ u ≤ 1`. -/
lemma exp_sub_one_le_three_mul {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u - 1 ≤ 3 * u := by
  have h_deriv : ∀ x ∈ Set.Icc 0 u, HasDerivWithinAt Real.exp (Real.exp x) (Set.Icc 0 u) x := by
    intro x _
    exact (Real.hasDerivAt_exp x).hasDerivWithinAt
  have h_bound : ∀ x ∈ Set.Ico 0 u, ‖Real.exp x‖ ≤ 3 := by
    intro x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)]
    have hx_le_1 : x ≤ 1 := hx.2.le.trans hu1
    have hexp : Real.exp x ≤ Real.exp 1 := Real.exp_le_exp.mpr hx_le_1
    exact hexp.trans Real.exp_one_lt_three.le
  have h_mvt := norm_image_sub_le_of_norm_deriv_le_segment' h_deriv h_bound u (Set.right_mem_Icc.mpr hu0)
  rw [Real.exp_zero, Real.norm_eq_abs, sub_zero] at h_mvt
  exact (le_abs_self _).trans h_mvt

/-- The number of primes in `(⌊P⌋₊, ⌊Q⌋₊]` is at most `primesBetween P Q`. -/
lemma card_Ioc_filter_prime_le_primesBetween (P Q : ℝ) :
    ((Finset.Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime).card ≤ primesBetween P Q := by
  have h_sub : (Finset.Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime ⊆ (Finset.Icc ⌈P⌉₊ ⌊Q⌋₊).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_Ioc, mem_Icc] at hp ⊢
    refine ⟨⟨?_, hp.1.2⟩, hp.2⟩
    have hp_gt : ⌊P⌋₊ < p := hp.1.1
    have hp_ge : ⌊P⌋₊ + 1 ≤ p := hp_gt
    have hP_lt : P < ⌊P⌋₊ + 1 := Nat.lt_floor_add_one P
    have hP_lt_p : P < (p : ℝ) := hP_lt.trans_le (by exact_mod_cast hp_ge)
    exact Nat.ceil_le.mpr hP_lt_p.le
  exact card_le_card h_sub

/-- The prime reciprocal sum over `(⌊P⌋₊, ⌊Q⌋₊]` is at most the prime count divided by `P`. -/
lemma sum_one_div_primes_le_card_div {P Q : ℝ} (hP : 0 < P) :
    (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
      ((Finset.Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime).card / P := by
  have h_term : ∀ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime, (1 : ℝ) / p ≤ 1 / P := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    have hp_gt : ⌊P⌋₊ < p := hp.1.1
    have hp_ge : ⌊P⌋₊ + 1 ≤ p := hp_gt
    have hP_lt : P < ⌊P⌋₊ + 1 := Nat.lt_floor_add_one P
    have hP_lt_p : P < (p : ℝ) := hP_lt.trans_le (by exact_mod_cast hp_ge)
    exact one_div_le_one_div_of_le hP hP_lt_p.le
  have h_sum := sum_le_sum h_term
  have h_const : (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime, (1 : ℝ) / P) =
      ((Finset.Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime).card * (1 / P) := by
    rw [sum_const, nsmul_eq_mul]
  rw [h_const] at h_sum
  have : ((Finset.Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime).card * (1 / P) =
      ((Finset.Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime).card / P := by ring
  rwa [this] at h_sum

/-- For `P > 0`, `√P / P = 1 / √P`. -/
lemma sqrt_div_self {P : ℝ} (hP : 0 < P) :
    Real.sqrt P / P = 1 / Real.sqrt P := by
  have h_sqrt_pos : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP
  have h_sq : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt hP.le
  calc Real.sqrt P / P = Real.sqrt P / (Real.sqrt P * Real.sqrt P) := by rw [h_sq]
  _ = 1 / Real.sqrt P := by
    rw [mul_comm, ← div_div, div_self h_sqrt_pos.ne', one_div]

/-- For `1 ≤ P`, `log √P ≤ log P`. -/
lemma log_sqrt_le_log {P : ℝ} (hP : 1 ≤ P) :
    Real.log (Real.sqrt P) ≤ Real.log P := by
  rw [Real.log_sqrt (by linarith)]
  have : 0 ≤ Real.log P := Real.log_nonneg hP
  linarith

/-- Upper bound for the prime reciprocal sum in the short range `(⌊P⌋₊, ⌊P e^{1/H}⌋₊]` via Brun–Titchmarsh. -/
theorem sum_inv_primes_short_range_le_bt :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 2 ≤ P → 1 ≤ H → H ≤ Real.sqrt P →
      (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
        C * (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) := by
  use 12
  refine ⟨by norm_num, fun P H hP hH _hH_le ↦ ?_⟩
  have hP_pos : 0 < P := by linarith
  have hH_pos : 0 < H := by linarith
  have h1H_nonneg : 0 ≤ 1 / H := by positivity
  have h1H_le_one : 1 / H ≤ 1 := by
    rw [div_le_iff₀ hH_pos]
    linarith
  have hexp_sub_one : Real.exp (1 / H) - 1 ≤ 3 / H := by
    have h_le := exp_sub_one_le_three_mul h1H_nonneg h1H_le_one
    have : 3 * (1 / H) = 3 / H := by ring
    linarith
  set y := P * (Real.exp (1 / H) - 1) with _hy_def
  have hy_pos : 0 < y := by
    have hexp_gt_one : 1 < Real.exp (1 / H) := by
      calc 1 = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp (1 / H) := Real.exp_lt_exp.mpr (by positivity)
    exact mul_pos hP_pos (by linarith)
  have hz : 1 < Real.sqrt P := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  have h_bt := BrunTitchmarsh.primesBetween_le P y (Real.sqrt P) hP_pos hy_pos hz
  have hy_add : P + y = P * Real.exp (1 / H) := by
    dsimp [y]
    ring
  rw [hy_add] at h_bt
  have h_card_le : ((Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime).card ≤
      primesBetween P (P * Real.exp (1 / H)) :=
    card_Ioc_filter_prime_le_primesBetween P (P * Real.exp (1 / H))
  have h_card_cast : (↑((Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime).card : ℝ) ≤
      ↑(primesBetween P (P * Real.exp (1 / H))) := by
    exact_mod_cast h_card_le
  have h_sum_le_card := sum_one_div_primes_le_card_div hP_pos (Q := P * Real.exp (1 / H))
  have h_div_P : (↑((Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime).card : ℝ) / P ≤
      (2 * y / Real.log (Real.sqrt P) + 6 * Real.sqrt P * (1 + Real.log (Real.sqrt P)) ^ 3) / P := by
    have h_le := h_card_cast.trans h_bt
    exact div_le_div_of_nonneg_right h_le hP_pos.le
  have h_main_le : (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
      (2 * y / Real.log (Real.sqrt P) + 6 * Real.sqrt P * (1 + Real.log (Real.sqrt P)) ^ 3) / P :=
    h_sum_le_card.trans h_div_P
  refine h_main_le.trans ?_
  have hlogP_pos : 0 < Real.log P := Real.log_pos (by linarith)
  have h_split : (2 * y / Real.log (Real.sqrt P) + 6 * Real.sqrt P * (1 + Real.log (Real.sqrt P)) ^ 3) / P =
      (2 * y / Real.log (Real.sqrt P)) / P + (6 * Real.sqrt P * (1 + Real.log (Real.sqrt P)) ^ 3) / P :=
    add_div _ _ _
  rw [h_split]
  have h_term1_eq : (2 * y / Real.log (Real.sqrt P)) / P = (4 / Real.log P) * (Real.exp (1 / H) - 1) := by
    rw [Real.log_sqrt hP_pos.le]
    dsimp [y]
    field_simp [hP_pos.ne', hlogP_pos.ne']
    ring
  have h_term1_le : (2 * y / Real.log (Real.sqrt P)) / P ≤ 12 / (H * Real.log P) := by
    rw [h_term1_eq]
    have : (4 / Real.log P) * (Real.exp (1 / H) - 1) ≤ (4 / Real.log P) * (3 / H) :=
      mul_le_mul_of_nonneg_left hexp_sub_one (by positivity)
    refine this.trans_eq ?_
    ring
  have h_term2_le : (6 * Real.sqrt P * (1 + Real.log (Real.sqrt P)) ^ 3) / P ≤
      6 * (1 + Real.log P) ^ 3 / Real.sqrt P := by
    have h_eq : (6 * Real.sqrt P * (1 + Real.log (Real.sqrt P)) ^ 3) / P =
        6 * (Real.sqrt P / P) * (1 + Real.log (Real.sqrt P)) ^ 3 := by ring
    rw [h_eq, sqrt_div_self hP_pos]
    have h_pow_le : (1 + Real.log (Real.sqrt P)) ^ 3 ≤ (1 + Real.log P) ^ 3 := by
      have _hlog_nonneg : 0 ≤ Real.log (Real.sqrt P) := Real.log_nonneg (by
        rw [Real.one_le_sqrt]
        linarith)
      have _h_le : 1 + Real.log (Real.sqrt P) ≤ 1 + Real.log P := by
        linarith [log_sqrt_le_log (by linarith : 1 ≤ P)]
      gcongr
    have h_mul : 6 * (1 / Real.sqrt P) * (1 + Real.log (Real.sqrt P)) ^ 3 ≤
        6 * (1 / Real.sqrt P) * (1 + Real.log P) ^ 3 :=
      mul_le_mul_of_nonneg_left h_pow_le (by positivity)
    refine h_mul.trans_eq ?_
    ring
  have h_comb : (2 * y / Real.log (Real.sqrt P)) / P + (6 * Real.sqrt P * (1 + Real.log (Real.sqrt P)) ^ 3) / P ≤
      12 / (H * Real.log P) + 6 * (1 + Real.log P) ^ 3 / Real.sqrt P :=
    add_le_add h_term1_le h_term2_le
  refine h_comb.trans ?_
  calc 12 / (H * Real.log P) + 6 * (1 + Real.log P) ^ 3 / Real.sqrt P
    _ = 12 * (1 / (H * Real.log P)) + 6 * ((1 + Real.log P) ^ 3 / Real.sqrt P) := by ring
    _ ≤ 12 * (1 / (H * Real.log P)) + 12 * ((1 + Real.log P) ^ 3 / Real.sqrt P) := by
      gcongr
      norm_num
    _ = 12 * (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) := by ring

/-- Upper bound for the prime reciprocal square sum in the short range `(⌊P⌋₊, ⌊P e^{1/H}⌋₊]` via Brun–Titchmarsh. -/
theorem sum_inv_sq_primes_short_range_le_bt :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 2 ≤ P → 1 ≤ H → H ≤ Real.sqrt P →
      (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) ≤
        C * (1 / (H * P * Real.log P) + (1 + Real.log P) ^ 3 / (P * Real.sqrt P)) := by
  obtain ⟨C, hC_pos, hC⟩ := sum_inv_primes_short_range_le_bt
  refine ⟨C, hC_pos, fun P H hP hH hH_le ↦ ?_⟩
  have hP_pos : 0 < P := by linarith
  have h_term_le : ∀ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime,
      (1 : ℝ) / (p : ℝ) ^ 2 ≤ (1 / P) * ((1 : ℝ) / (p : ℝ)) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp_gt_floor : ⌊P⌋₊ < p := hp.1.1
    have hp_ge_floor_succ : ⌊P⌋₊ + 1 ≤ p := hp_gt_floor
    have hP_lt_succ : P < ⌊P⌋₊ + 1 := Nat.lt_floor_add_one P
    have hP_le_p : P ≤ (p : ℝ) := by
      have : P < (p : ℝ) := hP_lt_succ.trans_le (by exact_mod_cast hp_ge_floor_succ)
      linarith
    have hp_pos : 0 < (p : ℝ) := by linarith
    have hp_prod_pos : 0 < P * (p : ℝ) := mul_pos hP_pos hp_pos
    have h_prod_le : P * (p : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have h_inv_le : 1 / (p : ℝ) ^ 2 ≤ 1 / (P * (p : ℝ)) :=
      one_div_le_one_div_of_le hp_prod_pos h_prod_le
    have h_split : (1 : ℝ) / (P * (p : ℝ)) = (1 / P) * ((1 : ℝ) / (p : ℝ)) := by ring
    rwa [h_split] at h_inv_le
  have h_sum_le := Finset.sum_le_sum h_term_le
  rw [← Finset.mul_sum] at h_sum_le
  have h_primes_le := hC P H hP hH hH_le
  have h_bound : (1 / P) * (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
      (1 / P) * (C * (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P)) := by
    exact mul_le_mul_of_nonneg_left h_primes_le (by positivity)
  have h_trans := h_sum_le.trans h_bound
  refine h_trans.trans_eq ?_
  ring

end Erdos1201.MR
