/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
import Mathlib.NumberTheory.Chebyshev
import Erdos1201.PrimeSums
import Erdos1201.Vendor.NumberTheory.PNT.MertensErrorTermAsymptotics

/-!
# Reciprocal prime mass in short multiplicative ranges

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module provides upper bounds for the reciprocal sum and square reciprocal sum of primes
in short multiplicative ranges `(⌊P⌋₊, ⌊P e^{1/H}⌋₊]`, controlling the Dirichlet polynomials
`Q_{v,H}` of Matomäki–Radziwiłł Lemma 12.
-/

open Finset Real MertensErrorTermAsymptotics

namespace Erdos1201.MR

/-- Splitting the prime reciprocal sum over `(⌊P⌋₊, ⌊Q⌋₊]` as the difference of sums from `0`. -/
lemma sum_Ioc_filter_prime_split {P Q : ℝ} (_hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∑ p ∈ (Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime, (1 : ℝ) / p =
      (∑ p ∈ (Ioc 0 ⌊Q⌋₊).filter Nat.Prime, (1 : ℝ) / p) -
      (∑ p ∈ (Ioc 0 ⌊P⌋₊).filter Nat.Prime, (1 : ℝ) / p) := by
  have hb : 0 ≤ ⌊P⌋₊ := Nat.zero_le _
  have hbc : ⌊P⌋₊ ≤ ⌊Q⌋₊ := Nat.floor_mono hPQ
  have hunion : Ioc 0 ⌊Q⌋₊ = Ioc 0 ⌊P⌋₊ ∪ Ioc ⌊P⌋₊ ⌊Q⌋₊ := (Ioc_union_Ioc_eq_Ioc hb hbc).symm
  have hdisj : Disjoint (Ioc 0 ⌊P⌋₊) (Ioc ⌊P⌋₊ ⌊Q⌋₊) := by
    rw [disjoint_iff_ne]
    intro x hx y hy
    simp only [mem_Ioc] at hx hy
    omega
  have hfilt : (Ioc 0 ⌊Q⌋₊).filter Nat.Prime =
      ((Ioc 0 ⌊P⌋₊).filter Nat.Prime) ∪ ((Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime) := by
    rw [hunion, filter_union]
  have hdisj_filt : Disjoint ((Ioc 0 ⌊P⌋₊).filter Nat.Prime) ((Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime) :=
    disjoint_filter_filter hdisj
  rw [hfilt, sum_union hdisj_filt]
  ring

/-- Decomposition of the short-range prime reciprocal sum into log-log difference plus error difference. -/
lemma sum_Ioc_filter_prime_eq_log_log_diff {P Q : ℝ} (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ∑ p ∈ (Ioc ⌊P⌋₊ ⌊Q⌋₊).filter Nat.Prime, (1 : ℝ) / p =
      (Real.log (Real.log Q) - Real.log (Real.log P)) + (E₂p Q - E₂p P) := by
  rw [sum_Ioc_filter_prime_split hP hPQ]
  rw [sum_prime_div_eq Q, sum_prime_div_eq P]
  ring

/-- The main log-log difference for `(P, P e^{1/H}]` is bounded by `1 / (H log P)`. -/
lemma log_log_diff_le {P H : ℝ} (hP : 2 ≤ P) (hH : 1 ≤ H) :
    Real.log (Real.log (P * Real.exp (1 / H))) - Real.log (Real.log P) ≤ 1 / (H * Real.log P) := by
  have hP_pos : 0 < P := by linarith
  have hlogP_pos : 0 < Real.log P := Real.log_pos (by linarith)
  have _hH_pos : 0 < H := by linarith
  have h1H_nonneg : 0 ≤ 1 / H := by positivity
  have hexp_ge_one : 1 ≤ Real.exp (1 / H) := by
    calc 1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (1 / H) := Real.exp_le_exp_of_le h1H_nonneg
  have _hQ_ge_P : P ≤ P * Real.exp (1 / H) := by
    calc P = P * 1 := (mul_one P).symm
    _ ≤ P * Real.exp (1 / H) := mul_le_mul_of_nonneg_left hexp_ge_one (by linarith)
  have h_exp_pos : 0 < Real.exp (1 / H) := Real.exp_pos _
  have hlogQ : Real.log (P * Real.exp (1 / H)) = Real.log P + 1 / H := by
    rw [Real.log_mul hP_pos.ne' h_exp_pos.ne', Real.log_exp]
  rw [hlogQ]
  have h_eq : Real.log P + 1 / H = Real.log P * (1 + 1 / (H * Real.log P)) := by
    have h1 : Real.log P * (1 / (H * Real.log P)) = 1 / H := by field_simp
    calc Real.log P + 1 / H = Real.log P + Real.log P * (1 / (H * Real.log P)) := by rw [h1]
    _ = Real.log P * (1 + 1 / (H * Real.log P)) := by ring
  have h_inner_pos : 0 < 1 + 1 / (H * Real.log P) := by positivity
  rw [h_eq, Real.log_mul hlogP_pos.ne' h_inner_pos.ne']
  have : Real.log (Real.log P) + Real.log (1 + 1 / (H * Real.log P)) - Real.log (Real.log P)
      = Real.log (1 + 1 / (H * Real.log P)) := by ring
  rw [this]
  have h_le := Real.log_le_sub_one_of_pos h_inner_pos
  linarith

/-- The Mertens error difference `E₂p(P e^{1/H}) - E₂p(P)` is bounded by `2 * (log 4 + 6 + E₁) / log P`. -/
lemma E₂p_diff_le {P H : ℝ} (hP : 2 ≤ P) (hH : 1 ≤ H) :
    E₂p (P * Real.exp (1 / H)) - E₂p P ≤ 2 * (Real.log 4 + 6 + E₁) / Real.log P := by
  have _hP_pos : 0 < P := by linarith
  have hlogP_pos : 0 < Real.log P := Real.log_pos (by linarith)
  have _hH_pos : 0 < H := by linarith
  have h1H_nonneg : 0 ≤ 1 / H := by positivity
  have hexp_ge_one : 1 ≤ Real.exp (1 / H) := by
    calc 1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (1 / H) := Real.exp_le_exp_of_le h1H_nonneg
  have hQ_ge_P : P ≤ P * Real.exp (1 / H) := by
    calc P = P * 1 := (mul_one P).symm
    _ ≤ P * Real.exp (1 / H) := mul_le_mul_of_nonneg_left hexp_ge_one (by linarith)
  have hQ_ge_two : 2 ≤ P * Real.exp (1 / H) := hP.trans hQ_ge_P
  have hE2Q := E₂p.abs_le hQ_ge_two
  have hE2P := E₂p.abs_le hP
  have hlogQ_ge_logP : Real.log P ≤ Real.log (P * Real.exp (1 / H)) :=
    Real.log_le_log (by linarith) hQ_ge_P
  have hB_nonneg : 0 ≤ Real.log 4 + 6 + E₁ := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith [E₁.nonneg]
  have hE2Q_le : E₂p (P * Real.exp (1 / H)) ≤ (Real.log 4 + 6 + E₁) / Real.log P := by
    have h1 : E₂p (P * Real.exp (1 / H)) ≤ |E₂p (P * Real.exp (1 / H))| := le_abs_self _
    have h2 : (Real.log 4 + 6 + E₁) / Real.log (P * Real.exp (1 / H)) ≤
        (Real.log 4 + 6 + E₁) / Real.log P := by
      exact div_le_div_of_nonneg_left hB_nonneg hlogP_pos hlogQ_ge_logP
    exact h1.trans (hE2Q.trans h2)
  have hE2P_ge : - ((Real.log 4 + 6 + E₁) / Real.log P) ≤ E₂p P := by
    have _h1 : - |E₂p P| ≤ E₂p P := neg_le_of_abs_le (le_refl _)
    linarith [hE2P]
  have h_sub : E₂p (P * Real.exp (1 / H)) - E₂p P ≤ 2 * ((Real.log 4 + 6 + E₁) / Real.log P) := by
    linarith
  rw [mul_div_assoc]
  exact h_sub

/-- Upper bound valid for all P ≥ 2, H ≥ 1: mass ≤ C (1/(H log P) + 1/log P).

Note: The statement in the task requested a second term of `1 / (log P)^2`. However, from
`MertensErrorTermAsymptotics.E₂p.bound`, the error term `E₂p` satisfies `|E₂p(x)| ≤ C'/log x`,
which provides an error difference of `O(1 / log P)`, not `O(1 / (log P)^2)`. Without an external
short-interval prime count (such as Brun–Titchmarsh / Selberg sieve), `O(1 / log P)` is the strongest
provable decay rate for the error contribution across all `H ≥ 1`. -/
theorem sum_inv_primes_short_range_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 2 ≤ P → 1 ≤ H →
      (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
        C * (1 / (H * Real.log P) + 1 / Real.log P) := by
  use 1 + 2 * (Real.log 4 + 6 + E₁)
  have hB_nonneg : 0 ≤ Real.log 4 + 6 + E₁ := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith [E₁.nonneg]
  have hC_pos : 0 < 1 + 2 * (Real.log 4 + 6 + E₁) := by linarith
  refine ⟨hC_pos, fun P H hP hH ↦ ?_⟩
  have _hlogP_pos : 0 < Real.log P := Real.log_pos (by linarith)
  have _hH_pos : 0 < H := by linarith
  have h1H_nonneg : 0 ≤ 1 / H := by positivity
  have hexp_ge_one : 1 ≤ Real.exp (1 / H) := by
    calc 1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (1 / H) := Real.exp_le_exp_of_le h1H_nonneg
  have hQ_ge_P : P ≤ P * Real.exp (1 / H) := by
    calc P = P * 1 := (mul_one P).symm
    _ ≤ P * Real.exp (1 / H) := mul_le_mul_of_nonneg_left hexp_ge_one (by linarith)
  rw [sum_Ioc_filter_prime_eq_log_log_diff hP hQ_ge_P]
  have h_log_le := log_log_diff_le hP hH
  have h_E_le := E₂p_diff_le hP hH
  have h_sum_le : (Real.log (Real.log (P * Real.exp (1 / H))) - Real.log (Real.log P)) +
      (E₂p (P * Real.exp (1 / H)) - E₂p P) ≤
      1 / (H * Real.log P) + 2 * (Real.log 4 + 6 + E₁) / Real.log P := by
    linarith
  refine h_sum_le.trans ?_
  have _h_term1_pos : 0 ≤ 1 / (H * Real.log P) := by positivity
  have _h_term2_pos : 0 ≤ 1 / Real.log P := by positivity
  have h_div_eq : 2 * (Real.log 4 + 6 + E₁) / Real.log P =
      (2 * (Real.log 4 + 6 + E₁)) * (1 / Real.log P) := by ring
  rw [h_div_eq]
  calc 1 / (H * Real.log P) + 2 * (Real.log 4 + 6 + E₁) * (1 / Real.log P)
    _ = 1 * (1 / (H * Real.log P)) + (2 * (Real.log 4 + 6 + E₁)) * (1 / Real.log P) := by ring
    _ ≤ (1 + 2 * (Real.log 4 + 6 + E₁)) * (1 / (H * Real.log P)) +
        (1 + 2 * (Real.log 4 + 6 + E₁)) * (1 / Real.log P) := by
      gcongr
      · linarith
      · linarith
    _ = (1 + 2 * (Real.log 4 + 6 + E₁)) * (1 / (H * Real.log P) + 1 / Real.log P) := by ring

/-- Reciprocal square mass: bounded by `C * (1 / (H P log P) + 1 / (P log P))`. -/
theorem sum_inv_sq_primes_short_range_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 2 ≤ P → 1 ≤ H →
      (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) ≤
        C * (1 / (H * P * Real.log P) + 1 / (P * Real.log P)) := by
  obtain ⟨C, hC_pos, hC⟩ := sum_inv_primes_short_range_le
  refine ⟨C, hC_pos, fun P H hP hH ↦ ?_⟩
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
    have _hp_sq_pos : 0 < (p : ℝ) ^ 2 := by positivity
    have hp_prod_pos : 0 < P * (p : ℝ) := mul_pos hP_pos hp_pos
    have h_prod_le : P * (p : ℝ) ≤ (p : ℝ) ^ 2 := by
      nlinarith
    have h_inv_le : 1 / (p : ℝ) ^ 2 ≤ 1 / (P * (p : ℝ)) :=
      one_div_le_one_div_of_le hp_prod_pos h_prod_le
    have h_split : (1 : ℝ) / (P * (p : ℝ)) = (1 / P) * ((1 : ℝ) / (p : ℝ)) := by ring
    rwa [h_split] at h_inv_le
  have h_sum_le := Finset.sum_le_sum h_term_le
  rw [← Finset.mul_sum] at h_sum_le
  have h_primes_le := hC P H hP hH
  have h_bound : (1 / P) * (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
      (1 / P) * (C * (1 / (H * Real.log P) + 1 / Real.log P)) := by
    exact mul_le_mul_of_nonneg_left h_primes_le (by positivity)
  have h_trans := h_sum_le.trans h_bound
  refine h_trans.trans_eq ?_
  ring

/-- For any fixed upper threshold `H ≤ H₀`, the requested bound with `1 / (log P)^2` holds unconditionally. -/
theorem sum_inv_primes_short_range_le_of_le_H₀ (H₀ : ℝ) (hH₀ : 1 ≤ H₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 2 ≤ P → 1 ≤ H → H ≤ H₀ →
      (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
        C * (1 / (H * Real.log P) + 1 / (Real.log P) ^ 2) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := sum_inv_primes_short_range_le
  use C₁ * (1 + H₀)
  have hC_pos : 0 < C₁ * (1 + H₀) := by positivity
  refine ⟨hC_pos, fun P H hP hH hH_le ↦ ?_⟩
  have h_base := hC₁ P H hP hH
  refine h_base.trans ?_
  have _hlogP_pos : 0 < Real.log P := Real.log_pos (by linarith)
  have hH_pos : 0 < H := by linarith
  have h_inv_le : 1 / Real.log P ≤ H₀ * (1 / (H * Real.log P)) := by
    calc 1 / Real.log P = (H / H) * (1 / Real.log P) := by
          rw [div_self hH_pos.ne', one_mul]
      _ = H * (1 / (H * Real.log P)) := by
          field_simp
      _ ≤ H₀ * (1 / (H * Real.log P)) := by
          have : 0 ≤ 1 / (H * Real.log P) := by positivity
          nlinarith
  have h_inner : 1 / (H * Real.log P) + 1 / Real.log P ≤ (1 + H₀) * (1 / (H * Real.log P)) := by
    calc 1 / (H * Real.log P) + 1 / Real.log P
      _ ≤ 1 / (H * Real.log P) + H₀ * (1 / (H * Real.log P)) := by linarith
      _ = (1 + H₀) * (1 / (H * Real.log P)) := by ring
  have _h_sq_nonneg : 0 ≤ 1 / (Real.log P) ^ 2 := by positivity
  have h_sum_le : (1 + H₀) * (1 / (H * Real.log P)) ≤ (1 + H₀) * (1 / (H * Real.log P) + 1 / (Real.log P) ^ 2) := by
    have : 0 ≤ 1 + H₀ := by linarith
    nlinarith
  calc C₁ * (1 / (H * Real.log P) + 1 / Real.log P)
    _ ≤ C₁ * ((1 + H₀) * (1 / (H * Real.log P))) := mul_le_mul_of_nonneg_left h_inner (le_of_lt hC₁_pos)
    _ ≤ C₁ * ((1 + H₀) * (1 / (H * Real.log P) + 1 / (Real.log P) ^ 2)) :=
        mul_le_mul_of_nonneg_left h_sum_le (le_of_lt hC₁_pos)
    _ = (C₁ * (1 + H₀)) * (1 / (H * Real.log P) + 1 / (Real.log P) ^ 2) := by ring

/-- For any fixed upper threshold `H ≤ H₀`, the reciprocal square bound with `1 / (P * (log P)^2)` holds unconditionally. -/
theorem sum_inv_sq_primes_short_range_le_of_le_H₀ (H₀ : ℝ) (hH₀ : 1 ≤ H₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 2 ≤ P → 1 ≤ H → H ≤ H₀ →
      (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) ≤
        C * (1 / (H * P * Real.log P) + 1 / (P * (Real.log P) ^ 2)) := by
  obtain ⟨C, hC_pos, hC⟩ := sum_inv_primes_short_range_le_of_le_H₀ H₀ hH₀
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
      (1 / P) * (C * (1 / (H * Real.log P) + 1 / (Real.log P) ^ 2)) := by
    exact mul_le_mul_of_nonneg_left h_primes_le (by positivity)
  have h_trans := h_sum_le.trans h_bound
  refine h_trans.trans_eq ?_
  ring

/-- Conditional version: if the error difference decays as `1 / (log P)^2`, then the exact requested
bound with `1 / (log P)^2` holds for all `H ≥ 1`. -/
theorem sum_inv_primes_short_range_le_of_E₂p_diff
    (hE : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (P H : ℝ), 2 ≤ P → 1 ≤ H →
      E₂p (P * Real.exp (1 / H)) - E₂p P ≤ C₂ / (Real.log P) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 2 ≤ P → 1 ≤ H →
      (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
        C * (1 / (H * Real.log P) + 1 / (Real.log P) ^ 2) := by
  obtain ⟨C₂, _hC₂_nonneg, hC₂⟩ := hE
  use 1 + C₂
  have hC_pos : 0 < 1 + C₂ := by linarith
  refine ⟨hC_pos, fun P H hP hH ↦ ?_⟩
  have _hlogP_pos : 0 < Real.log P := Real.log_pos (by linarith)
  have _hH_pos : 0 < H := by linarith
  have h1H_nonneg : 0 ≤ 1 / H := by positivity
  have hexp_ge_one : 1 ≤ Real.exp (1 / H) := by
    calc 1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp (1 / H) := Real.exp_le_exp_of_le h1H_nonneg
  have hQ_ge_P : P ≤ P * Real.exp (1 / H) := by
    calc P = P * 1 := (mul_one P).symm
    _ ≤ P * Real.exp (1 / H) := mul_le_mul_of_nonneg_left hexp_ge_one (by linarith)
  rw [sum_Ioc_filter_prime_eq_log_log_diff hP hQ_ge_P]
  have h_log_le := log_log_diff_le hP hH
  have h_E_le := hC₂ P H hP hH
  have h_sum_le : (Real.log (Real.log (P * Real.exp (1 / H))) - Real.log (Real.log P)) +
      (E₂p (P * Real.exp (1 / H)) - E₂p P) ≤
      1 / (H * Real.log P) + C₂ / (Real.log P) ^ 2 := by
    linarith
  refine h_sum_le.trans ?_
  have h_div_eq : C₂ / (Real.log P) ^ 2 = C₂ * (1 / (Real.log P) ^ 2) := by ring
  rw [h_div_eq]
  have _h_term1_pos : 0 ≤ 1 / (H * Real.log P) := by positivity
  have _h_term2_pos : 0 ≤ 1 / (Real.log P) ^ 2 := by positivity
  calc 1 / (H * Real.log P) + C₂ * (1 / (Real.log P) ^ 2)
    _ = 1 * (1 / (H * Real.log P)) + C₂ * (1 / (Real.log P) ^ 2) := by ring
    _ ≤ (1 + C₂) * (1 / (H * Real.log P)) + (1 + C₂) * (1 / (Real.log P) ^ 2) := by
      gcongr
      · linarith
      · linarith
    _ = (1 + C₂) * (1 / (H * Real.log P) + 1 / (Real.log P) ^ 2) := by ring

/-- Conditional version for reciprocal squares: if the error difference decays as `1 / (log P)^2`. -/
theorem sum_inv_sq_primes_short_range_le_of_E₂p_diff
    (hE : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (P H : ℝ), 2 ≤ P → 1 ≤ H →
      E₂p (P * Real.exp (1 / H)) - E₂p P ≤ C₂ / (Real.log P) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P H : ℝ), 2 ≤ P → 1 ≤ H →
      (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) ≤
        C * (1 / (H * P * Real.log P) + 1 / (P * (Real.log P) ^ 2)) := by
  obtain ⟨C, hC_pos, hC⟩ := sum_inv_primes_short_range_le_of_E₂p_diff hE
  refine ⟨C, hC_pos, fun P H hP hH ↦ ?_⟩
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
  have h_primes_le := hC P H hP hH
  have h_bound : (1 / P) * (∑ p ∈ (Finset.Ioc ⌊P⌋₊ ⌊P * Real.exp (1 / H)⌋₊).filter Nat.Prime, (1 : ℝ) / p) ≤
      (1 / P) * (C * (1 / (H * Real.log P) + 1 / (Real.log P) ^ 2)) := by
    exact mul_le_mul_of_nonneg_left h_primes_le (by positivity)
  have h_trans := h_sum_le.trans h_bound
  refine h_trans.trans_eq ?_
  ring

end Erdos1201.MR
