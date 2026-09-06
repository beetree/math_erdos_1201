/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

Attribution: the original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Chebyshev
import Erdos1201.Basic
import Erdos1201.SmoothBound

/-!
# Medium interval average replacement for Matomäki–Radziwiłł Lemma 4

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This file formalizes the elementary replacement of Matomäki–Radziwiłł Lemma 4
for the smooth indicator $f_X = \text{smoothIndicator}(X^\beta)$ with $3/4 \le \beta < 1$.
For intervals $(x, x+y]$ with $X \le x \le 2X$ and $y \ge X/(\log X)^{1/5}$,
the interval average agrees with the block mean up to $O((\log X)^{-4/5})$.
-/

open scoped BigOperators Real
open Finset Erdos1201

namespace Erdos1201.MR

/-- Elementary bound $\log x \le 2 \sqrt{x}$ for $x > 0$. -/
lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h_sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h := Real.log_le_sub_one_of_pos h_sqrt_pos
  rw [Real.log_sqrt (le_of_lt hx)] at h
  linarith

/-- Explicit Chebyshev upper bound on $\pi(3X)$ for $X \ge 16$. -/
lemma primeCounting_three_mul_le {X : ℕ} (hX : 16 ≤ X) :
    (Nat.primeCounting (3 * X) : ℝ) ≤ (6 * Real.log 4 + 4) * (X : ℝ) / Real.log (X : ℝ) := by
  have hX_pos : (0 : ℝ) < (X : ℝ) := by
    have : 16 ≤ (X : ℝ) := by exact_mod_cast hX
    linarith
  have hX_ge16 : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have h3X_pos : (0 : ℝ) < 3 * (X : ℝ) := by linarith
  have h3X_gt1 : (1 : ℝ) < 3 * (X : ℝ) := by linarith
  have h_floor : ⌊3 * (X : ℝ)⌋₊ = 3 * X := by
    have : 3 * (X : ℝ) = ((3 * X : ℕ) : ℝ) := by push_cast; ring
    rw [this, Nat.floor_natCast]
  have h_cheb := Chebyshev.pi_le_log4_mul_div h3X_gt1
  rw [h_floor] at h_cheb
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlog3X : Real.log (Real.sqrt (3 * (X : ℝ))) = Real.log (3 * (X : ℝ)) / 2 :=
    Real.log_sqrt (le_of_lt h3X_pos)
  have hlog3X_ge : Real.log (X : ℝ) ≤ Real.log (3 * (X : ℝ)) := by
    apply Real.log_le_log hX_pos
    linarith
  have h_term1 : Real.log 4 * (3 * (X : ℝ)) / Real.log (Real.sqrt (3 * (X : ℝ))) ≤
      6 * Real.log 4 * (X : ℝ) / Real.log (X : ℝ) := by
    rw [hlog3X]
    have : Real.log 4 * (3 * (X : ℝ)) / (Real.log (3 * (X : ℝ)) / 2) =
        6 * Real.log 4 * (X : ℝ) / Real.log (3 * (X : ℝ)) := by ring
    rw [this]
    apply div_le_div_of_nonneg_left
    · positivity
    · exact hlogX_pos
    · exact hlog3X_ge
  have h_sqrt_log : Real.sqrt (3 * (X : ℝ)) * Real.log (X : ℝ) ≤ 4 * (X : ℝ) := by
    have h_sqrt_mul : Real.sqrt (3 * (X : ℝ)) = Real.sqrt 3 * Real.sqrt (X : ℝ) :=
      Real.sqrt_mul (by norm_num) (X : ℝ)
    rw [h_sqrt_mul]
    have h_log_le := log_le_two_sqrt hX_pos
    have h_sqrt3_le : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_iff]
      norm_num
    have : Real.sqrt 3 * Real.sqrt (X : ℝ) * Real.log (X : ℝ) ≤
        Real.sqrt 3 * Real.sqrt (X : ℝ) * (2 * Real.sqrt (X : ℝ)) := by
      apply mul_le_mul_of_nonneg_left h_log_le
      positivity
    refine this.trans ?_
    have : Real.sqrt 3 * Real.sqrt (X : ℝ) * (2 * Real.sqrt (X : ℝ)) =
        2 * Real.sqrt 3 * (Real.sqrt (X : ℝ) * Real.sqrt (X : ℝ)) := by ring
    rw [this, Real.mul_self_sqrt (le_of_lt hX_pos)]
    nlinarith
  have h_term2 : Real.sqrt (3 * (X : ℝ)) ≤ 4 * (X : ℝ) / Real.log (X : ℝ) := by
    rw [le_div_iff₀ hlogX_pos]
    linarith
  have h_sum : Real.log 4 * (3 * (X : ℝ)) / Real.log (Real.sqrt (3 * (X : ℝ))) + Real.sqrt (3 * (X : ℝ)) ≤
      6 * Real.log 4 * (X : ℝ) / Real.log (X : ℝ) + 4 * (X : ℝ) / Real.log (X : ℝ) :=
    add_le_add h_term1 h_term2
  have h_comb : 6 * Real.log 4 * (X : ℝ) / Real.log (X : ℝ) + 4 * (X : ℝ) / Real.log (X : ℝ) =
      (6 * Real.log 4 + 4) * (X : ℝ) / Real.log (X : ℝ) := by ring
  rw [h_comb] at h_sum
  exact h_cheb.trans h_sum

/-- Primes in the window $(X^\beta, 3X]$. -/
noncomputable def primeRange3 (β : ℝ) (X : ℕ) : Finset ℕ :=
  (Ioc ⌊(X : ℝ) ^ β⌋₊ (3 * X)).filter Nat.Prime

/-- The primes in `primeRange3 β X` are primes up to $3X$. -/
lemma primeRange3_subset_primesLE (β : ℝ) (X : ℕ) :
    primeRange3 β X ⊆ Nat.primesLE (3 * X) := by
  intro p hp
  simp only [primeRange3, mem_filter, mem_Ioc] at hp
  rw [Nat.mem_primesLE]
  exact ⟨hp.1.2, hp.2⟩

/-- The size of `primeRange3 β X` is bounded by $\pi(3X)$. -/
lemma card_primeRange3_le_primeCounting (β : ℝ) (X : ℕ) :
    (primeRange3 β X).card ≤ Nat.primeCounting (3 * X) := by
  have h := card_le_card (primeRange3_subset_primesLE β X)
  rw [Nat.primesLE_card_eq_primeCounting] at h
  exact h

/-- For $X \ge 16$ and $\beta \ge 3/4$, the product of any two primes in `primeRange3 β X` exceeds $3X$. -/
lemma three_mul_lt_prime_mul {X : ℕ} (hX : 16 ≤ X) {β : ℝ} (hβ : 3/4 ≤ β)
    {p q : ℕ} (hp : p ∈ primeRange3 β X) (hq : q ∈ primeRange3 β X) :
    3 * (X : ℝ) < (p * q : ℝ) := by
  have hX_ge16 : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX_pos : 0 < (X : ℝ) := by linarith
  have hX_ge1 : 1 ≤ (X : ℝ) := by linarith
  have hp_ioc := (mem_filter.mp hp).1
  have hq_ioc := (mem_filter.mp hq).1
  have hp_gt_floor := (mem_Ioc.mp hp_ioc).1
  have hq_gt_floor := (mem_Ioc.mp hq_ioc).1
  have h_rpow_pos : 0 ≤ (X : ℝ) ^ β := Real.rpow_nonneg (by linarith) β
  have hp_gt : (X : ℝ) ^ β < (p : ℝ) := (Nat.floor_lt h_rpow_pos).mp hp_gt_floor
  have hq_gt : (X : ℝ) ^ β < (q : ℝ) := (Nat.floor_lt h_rpow_pos).mp hq_gt_floor
  have hpq_gt : (X : ℝ) ^ β * (X : ℝ) ^ β < (p : ℝ) * (q : ℝ) := by nlinarith
  have h_add : (X : ℝ) ^ β * (X : ℝ) ^ β = (X : ℝ) ^ (β + β) := by
    rw [← Real.rpow_add hX_pos]
  have h_two_beta : 3/2 ≤ β + β := by linarith
  have h_rpow_ge : (X : ℝ) ^ (3/2 : ℝ) ≤ (X : ℝ) ^ (β + β) :=
    Real.rpow_le_rpow_of_exponent_le hX_ge1 h_two_beta
  have h_split : (X : ℝ) ^ (3/2 : ℝ) = (X : ℝ) * (X : ℝ) ^ (1/2 : ℝ) := by
    have : (3/2 : ℝ) = 1 + 1/2 := by norm_num
    rw [this, Real.rpow_add hX_pos, Real.rpow_one]
  have h_sqrt : (4 : ℝ) ≤ (X : ℝ) ^ (1/2 : ℝ) := by
    have h16 : (16 : ℝ) ^ (1/2 : ℝ) ≤ (X : ℝ) ^ (1/2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hX_ge16 (by norm_num)
    have h16_val : (16 : ℝ) ^ (1/2 : ℝ) = 4 := by
      rw [← Real.sqrt_eq_rpow]
      norm_num
    linarith
  have h_4X_le : 4 * (X : ℝ) ≤ (X : ℝ) ^ (3/2 : ℝ) := by
    rw [h_split]
    nlinarith
  linarith

/-- At most one prime in `primeRange3 β X` divides any integer $n \le 3X$. -/
lemma card_filter_primeRange3_dvd_le_one {X : ℕ} (hX : 16 ≤ X) {β : ℝ} (hβ : 3/4 ≤ β)
    {n : ℕ} (hn_pos : 0 < n) (hn_le : n ≤ 3 * X) :
    ((primeRange3 β X).filter (fun p => p ∣ n)).card ≤ 1 := by
  by_contra! h
  rcases one_lt_card_iff.mp h with ⟨p, q, hp, hq, hpq⟩
  simp only [mem_filter] at hp hq
  have hp_prime : p.Prime := (mem_filter.mp hp.1).2
  have hq_prime : q.Prime := (mem_filter.mp hq.1).2
  have hcoprime : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr hpq
  have hmul_dvd : p * q ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcoprime hp.2 hq.2
  have hpq_le_n : p * q ≤ n := Nat.le_of_dvd hn_pos hmul_dvd
  have h_prod_le : (p * q : ℝ) ≤ 3 * (X : ℝ) := by
    have : (p * q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpq_le_n
    have : (n : ℝ) ≤ 3 * (X : ℝ) := by exact_mod_cast hn_le
    linarith
  have h_prod_gt := three_mul_lt_prime_mul hX hβ hp.1 hq.1
  linarith

/-- Pointwise formula: for $n \le 3X$, the smooth indicator is $1 - \sum_{p \in P} \mathbf{1}_{p \mid n}$. -/
lemma smoothIndicator_eq_one_sub_sum_primeRange3 {X : ℕ} (hX : 16 ≤ X) {β : ℝ} (hβ : 3/4 ≤ β)
    {n : ℕ} (hn_pos : 0 < n) (hn_le : n ≤ 3 * X) :
    smoothIndicator ((X : ℝ) ^ β) n = 1 - ∑ p ∈ primeRange3 β X, (if p ∣ n then (1 : ℝ) else 0) := by
  have hX_nonneg : (0 : ℝ) ≤ (X : ℝ) := by positivity
  rw [sum_indicator_dvd_eq_card]
  by_cases hs : Smooth ((X : ℝ) ^ β) n
  · have : (primeRange3 β X).filter (fun p => p ∣ n) = ∅ := by
      rw [filter_eq_empty_iff]
      intro p hp hp_dvd
      have hp_prime : p.Prime := (mem_filter.mp hp).2
      have hp_ioc := (mem_filter.mp hp).1
      have hp_gt_floor := (mem_Ioc.mp hp_ioc).1
      have h_rpow_pos : 0 ≤ (X : ℝ) ^ β := Real.rpow_nonneg hX_nonneg β
      have hp_gt : (X : ℝ) ^ β < (p : ℝ) := (Nat.floor_lt h_rpow_pos).mp hp_gt_floor
      have hp_le : (p : ℝ) ≤ (X : ℝ) ^ β := hs.2 p hp_prime hp_dvd
      linarith
    rw [this, card_empty, Nat.cast_zero, sub_zero]
    simp [smoothIndicator, hs]
  · simp only [smoothIndicator, hs, ↓reduceIte]
    have hn_ne : n ≠ 0 := ne_of_gt hn_pos
    have h_not : ¬ (∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ (X : ℝ) ^ β) := by
      intro h_all
      exact hs ⟨hn_ne, h_all⟩
    push Not at h_not
    rcases h_not with ⟨p, hp_prime, hp_dvd, hp_gt⟩
    have hp_le_n : p ≤ n := Nat.le_of_dvd hn_pos hp_dvd
    have hp_le_3X : p ≤ 3 * X := hp_le_n.trans hn_le
    have h_rpow_pos : 0 ≤ (X : ℝ) ^ β := Real.rpow_nonneg hX_nonneg β
    have hp_gt_floor : ⌊(X : ℝ) ^ β⌋₊ < p := (Nat.floor_lt h_rpow_pos).mpr hp_gt
    have hp_mem : p ∈ primeRange3 β X := by
      simp only [primeRange3, mem_filter, mem_Ioc]
      exact ⟨⟨hp_gt_floor, hp_le_3X⟩, hp_prime⟩
    have hp_in_filter : p ∈ (primeRange3 β X).filter (fun q => q ∣ n) := by
      simp only [mem_filter]
      exact ⟨hp_mem, hp_dvd⟩
    have h_card_pos : 0 < ((primeRange3 β X).filter (fun q => q ∣ n)).card :=
      card_pos.mpr ⟨p, hp_in_filter⟩
    have h_card_le := card_filter_primeRange3_dvd_le_one hX hβ hn_pos hn_le
    have h_card_eq : ((primeRange3 β X).filter (fun q => q ∣ n)).card = 1 := by omega
    rw [h_card_eq]
    norm_num

/-- Summing the smooth indicator over any sub-finset of $[1, 3X]$. -/
lemma sum_smoothIndicator_eq {X : ℕ} (hX : 16 ≤ X) {β : ℝ} (hβ : 3/4 ≤ β) (s : Finset ℕ)
    (hs : ∀ n ∈ s, 0 < n ∧ n ≤ 3 * X) :
    ∑ n ∈ s, smoothIndicator ((X : ℝ) ^ β) n =
      (s.card : ℝ) - ∑ p ∈ primeRange3 β X, (((s.filter (fun n => p ∣ n)).card : ℝ)) := by
  have h_eq : ∀ n ∈ s, smoothIndicator ((X : ℝ) ^ β) n =
      1 - ∑ p ∈ primeRange3 β X, (if p ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    have := hs n hn
    exact smoothIndicator_eq_one_sub_sum_primeRange3 hX hβ this.1 this.2
  rw [sum_congr rfl h_eq, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one, sum_comm]
  congr 1
  apply sum_congr rfl
  intro p _
  rw [← sum_filter]
  simp

/-- Cardinality of multiples of $p$ in an interval $(a, b]$ is $b/p - a/p$. -/
lemma card_Ioc_filter_dvd_general {a b p : ℕ} (hab : a ≤ b) :
    ((Ioc a b).filter (fun n => p ∣ n)).card = b / p - a / p := by
  have h_union : Ioc 0 b = Ioc 0 a ∪ Ioc a b := by
    rw [Ioc_union_Ioc_eq_Ioc (by omega) hab]
  have h_disj : Disjoint ((Ioc 0 a).filter (fun x => p ∣ x)) ((Ioc a b).filter (fun x => p ∣ x)) := by
    rw [disjoint_left]
    intro x h1 h2
    simp only [mem_filter, mem_Ioc] at h1 h2
    omega
  have h_filt : (Ioc 0 b).filter (fun x => p ∣ x) =
      ((Ioc 0 a).filter (fun x => p ∣ x)) ∪ ((Ioc a b).filter (fun x => p ∣ x)) := by
    rw [h_union, filter_union]
  have h_card := card_union_of_disjoint h_disj
  rw [← h_filt, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at h_card
  omega

/-- Difference between integer division step and real ratio is at most 1. -/
lemma abs_div_sub_div_sub_div_le (x y : ℕ) {p : ℕ} (hp : 0 < p) :
    |(((x + y) / p - x / p : ℕ) : ℝ) - (y : ℝ) / (p : ℝ)| ≤ 1 := by
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have h1 : (x + y) < ((x + y) / p + 1) * p := by
    have h := Nat.div_add_mod (x + y) p
    have hmod := Nat.mod_lt (x + y) hp
    rw [add_mul, one_mul, mul_comm ((x + y) / p) p]
    omega
  have h2 : (x / p) * p ≤ x := Nat.div_mul_le_self x p
  have h3 : ((x + y) / p) * p ≤ x + y := Nat.div_mul_le_self (x + y) p
  have h4 : x < (x / p + 1) * p := by
    have h := Nat.div_add_mod x p
    have hmod := Nat.mod_lt x hp
    rw [add_mul, one_mul, mul_comm (x / p) p]
    omega
  have h1_real : (x + y : ℝ) < (((x + y) / p : ℕ) : ℝ) * (p : ℝ) + (p : ℝ) := by
    have : (x + y : ℝ) < (((x + y) / p + 1 : ℕ) : ℝ) * (p : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  have h2_real : ((x / p : ℕ) : ℝ) * (p : ℝ) ≤ (x : ℝ) := by exact_mod_cast h2
  have h3_real : (((x + y) / p : ℕ) : ℝ) * (p : ℝ) ≤ (x + y : ℝ) := by exact_mod_cast h3
  have h4_real : (x : ℝ) < (((x / p : ℕ) : ℝ) + 1) * (p : ℝ) := by
    have : (x : ℝ) < (((x / p + 1 : ℕ) : ℝ)) * (p : ℝ) := by exact_mod_cast h4
    push_cast at this
    exact this
  have h_le_div : x / p ≤ (x + y) / p := Nat.div_le_div_right (by omega)
  have h_cast_sub : (((x + y) / p - x / p : ℕ) : ℝ) = (((x + y) / p : ℕ) : ℝ) - ((x / p : ℕ) : ℝ) :=
    Nat.cast_sub h_le_div
  rw [abs_le]
  constructor
  · have : (y : ℝ) < ((((x + y) / p : ℕ) : ℝ) - ((x / p : ℕ) : ℝ) + 1) * (p : ℝ) := by
      calc (y : ℝ) = (x + y : ℝ) - (x : ℝ) := by ring
      _ < (((x + y) / p : ℕ) : ℝ) * (p : ℝ) + (p : ℝ) - ((x / p : ℕ) : ℝ) * (p : ℝ) := by linarith
      _ = ((((x + y) / p : ℕ) : ℝ) - ((x / p : ℕ) : ℝ) + 1) * (p : ℝ) := by ring
    have h_div : (y : ℝ) / (p : ℝ) < (((x + y) / p : ℕ) : ℝ) - ((x / p : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hp_pos]
      linarith
    rw [h_cast_sub]
    linarith
  · have : ((((x + y) / p : ℕ) : ℝ) - ((x / p : ℕ) : ℝ) - 1) * (p : ℝ) < (y : ℝ) := by
      calc ((((x + y) / p : ℕ) : ℝ) - ((x / p : ℕ) : ℝ) - 1) * (p : ℝ) =
        (((x + y) / p : ℕ) : ℝ) * (p : ℝ) - (((x / p : ℕ) : ℝ) + 1) * (p : ℝ) := by ring
      _ < (x + y : ℝ) - (x : ℝ) := by linarith
      _ = (y : ℝ) := by ring
    have h_div : (((x + y) / p : ℕ) : ℝ) - ((x / p : ℕ) : ℝ) - 1 < (y : ℝ) / (p : ℝ) := by
      rw [lt_div_iff₀ hp_pos]
      linarith
    rw [h_cast_sub]
    linarith

/-- Multiples density error in $(x, x+y]$ is at most $1/y$. -/
lemma abs_Ioc_filter_dvd_card_div_sub_inv_le (x : ℕ) {y p : ℕ} (hy : 0 < y) (hp : 0 < p) :
    |(((Ioc x (x + y)).filter (fun n => p ∣ n)).card : ℝ) / (y : ℝ) - 1 / (p : ℝ)| ≤ 1 / (y : ℝ) := by
  rw [card_Ioc_filter_dvd_general (by omega)]
  have hy_pos : 0 < (y : ℝ) := Nat.cast_pos.mpr hy
  have h := abs_div_sub_div_sub_div_le x y hp
  have h_rw : ((((x + y) / p - x / p : ℕ) : ℝ) / (y : ℝ) - 1 / (p : ℝ)) =
      ((((x + y) / p - x / p : ℕ) : ℝ) - (y : ℝ) / (p : ℝ)) / (y : ℝ) := by
    have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
    field_simp
  rw [h_rw, abs_div, abs_of_pos hy_pos]
  exact div_le_div_of_nonneg_right h (le_of_lt hy_pos)

/-- Count of multiples in $[X, 2X)$ is at most one more than in $(X, 2X]$. -/
lemma card_Ico_filter_dvd_le (X : ℕ) (p : ℕ) :
    ((Ico X (2 * X)).filter (fun x => p ∣ x)).card ≤
      ((Ioc X (2 * X)).filter (fun x => p ∣ x)).card + 1 := by
  have hsub : (Ico X (2 * X)).filter (fun x => p ∣ x) ⊆
      insert X ((Ioc X (2 * X)).filter (fun x => p ∣ x)) := by
    intro x hx
    simp only [mem_filter, mem_Ico, mem_insert, mem_Ioc] at hx ⊢
    rcases hx with ⟨⟨hX, h2X⟩, hp⟩
    by_cases h : x = X
    · left; exact h
    · right; exact ⟨⟨lt_of_le_of_ne hX (Ne.symm h), le_of_lt h2X⟩, hp⟩
  have hcard := card_le_card hsub
  have hcard2 := card_insert_le X ((Ioc X (2 * X)).filter (fun x => p ∣ x))
  omega

/-- Upper bound for multiples count in $[X, 2X)$. -/
lemma card_Ico_filter_dvd_upper_bound (X : ℕ) {p : ℕ} (hp : 0 < p) :
    (((Ico X (2 * X)).filter (fun x => p ∣ x)).card : ℝ) ≤ (X : ℝ) / p + 2 := by
  have h1 := card_Ico_filter_dvd_le X p
  have h2 : ((Ioc X (2 * X)).filter (fun x => p ∣ x)).card = 2 * X / p - X / p :=
    card_Ioc_filter_dvd_general (by omega)
  have h3 := abs_div_sub_div_sub_div_le X X hp
  have h_two_X : X + X = 2 * X := by omega
  rw [h_two_X] at h3
  have h4 : (((2 * X / p - X / p : ℕ) : ℝ) - (X : ℝ) / (p : ℝ)) ≤ 1 := (abs_le.mp h3).2
  have h_card_real : (((Ico X (2 * X)).filter (fun x => p ∣ x)).card : ℝ) ≤
      (((Ioc X (2 * X)).filter (fun x => p ∣ x)).card : ℝ) + 1 := by
    exact_mod_cast h1
  rw [h2] at h_card_real
  linarith

/-- Multiples density error in $[X, 2X)$ is at most $2/X$. -/
lemma abs_Ico_filter_dvd_card_div_sub_inv_le (X : ℕ) {p : ℕ} (hX : 0 < X) (hp : 0 < p) :
    |(((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) / (X : ℝ) - 1 / (p : ℝ)| ≤ 2 / (X : ℝ) := by
  have hX_pos : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  by_cases hp_gt : 2 * X < p
  · have h_empty : (Ico X (2 * X)).filter (fun n => p ∣ n) = ∅ := by
      rw [filter_eq_empty_iff]
      intro n hn hdvd
      have hn_pos : 0 < n := by
        have := (mem_Ico.mp hn).1
        omega
      have hp_le_n : p ≤ n := Nat.le_of_dvd hn_pos hdvd
      have hn_lt : n < 2 * X := (mem_Ico.mp hn).2
      omega
    rw [h_empty, card_empty, Nat.cast_zero, zero_div, zero_sub, abs_neg]
    rw [abs_of_pos (by positivity)]
    have hp_real : 2 * (X : ℝ) < (p : ℝ) := by exact_mod_cast hp_gt
    have h_inv : 1 / (p : ℝ) < 1 / (2 * (X : ℝ)) := by
      exact one_div_lt_one_div_of_lt (by positivity) hp_real
    have : 1 / (2 * (X : ℝ)) ≤ 2 / (X : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hX_pos]
      linarith
    linarith
  · push Not at hp_gt
    have h_low := Erdos1201.card_Ico_filter_dvd_lower_bound X hp
    have h_high := card_Ico_filter_dvd_upper_bound X hp
    rw [abs_le]
    constructor
    · have h_sub_le : -2 ≤ (((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) - (X : ℝ) / (p : ℝ) := by linarith
      have h_div_le := div_le_div_of_nonneg_right h_sub_le (le_of_lt hX_pos)
      have h_rw : ((((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) - (X : ℝ) / (p : ℝ)) / (X : ℝ) =
          (((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) / (X : ℝ) - 1 / (p : ℝ) := by
        field_simp
      rw [h_rw] at h_div_le
      have h_neg : -(2 / (X : ℝ)) = -2 / (X : ℝ) := by ring
      rw [h_neg]
      exact h_div_le
    · have h_sub_le : (((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) - (X : ℝ) / (p : ℝ) ≤ 2 := by linarith
      have h_div_le := div_le_div_of_nonneg_right h_sub_le (le_of_lt hX_pos)
      have h_rw : ((((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) - (X : ℝ) / (p : ℝ)) / (X : ℝ) =
          (((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) / (X : ℝ) - 1 / (p : ℝ) := by
        field_simp
      rw [h_rw] at h_div_le
      exact h_div_le

/-- Simplification $L^{1/5} / L = 1 / L^{4/5}$ for $L > 0$. -/
lemma rpow_one_fifth_div_self {L : ℝ} (hL : 0 < L) :
    L ^ (1 / 5 : ℝ) / L = 1 / L ^ (4 / 5 : ℝ) := by
  have : L = L ^ (1 : ℝ) := (Real.rpow_one L).symm
  nth_rw 2 [this]
  rw [← Real.rpow_sub hL]
  have h_exp : (1 / 5 : ℝ) - 1 = - (4 / 5 : ℝ) := by norm_num
  rw [h_exp, Real.rpow_neg (le_of_lt hL), one_div]

/-- Elementary replacement of Matomäki–Radziwiłł Lemma 4 for the smooth indicator:
averages over any interval $(x, x+y]$ with $X \le x \le 2X$ and $y \ge X/(\log X)^{1/5}$
agree with the block mean up to $O((\log X)^{-4/5})$. -/
theorem abs_intervalMean_sub_blockMean_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (X x y : ℕ), 3 / 4 ≤ β → β < 1 → 16 ≤ X → X ≤ x → x ≤ 2 * X → (X : ℝ) / (Real.log X) ^ (1 / 5 : ℝ) ≤ y → y ≤ X →
      |(∑ n ∈ Finset.Ioc x (x + y), smoothIndicator ((X : ℝ) ^ β) n) / (y : ℝ) - blockMean (smoothIndicator ((X : ℝ) ^ β)) X| ≤
        C / (Real.log X) ^ (4 / 5 : ℝ) := by
  refine ⟨3 * (6 * Real.log 4 + 4), by positivity, ?_⟩
  intro β X x y hβ34 hβ1 hX16 hXx hx2X hy_lower hy_leX
  have hX_pos : 0 < (X : ℝ) := by
    have : 16 ≤ (X : ℝ) := by exact_mod_cast hX16
    linarith
  have hX_gt1 : (1 : ℝ) < (X : ℝ) := by
    have : 16 ≤ (X : ℝ) := by exact_mod_cast hX16
    linarith
  have hX_nat_pos : 0 < X := by omega
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos hX_gt1
  have hlogX_pow_pos : 0 < (Real.log (X : ℝ)) ^ (1 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hlogX_pos _
  have hy_lower_pos : 0 < (X : ℝ) / (Real.log (X : ℝ)) ^ (1 / 5 : ℝ) :=
    div_pos hX_pos hlogX_pow_pos
  have hy_pos : 0 < (y : ℝ) := lt_of_lt_of_le hy_lower_pos hy_lower
  have hy_nat_pos : 0 < y := by exact_mod_cast hy_pos
  have hs_ioc : ∀ n ∈ Ioc x (x + y), 0 < n ∧ n ≤ 3 * X := by
    intro n hn
    simp only [mem_Ioc] at hn
    constructor
    · omega
    · omega
  have h_sum_ioc := sum_smoothIndicator_eq hX16 hβ34 (Ioc x (x + y)) hs_ioc
  have h_ioc_card : (Ioc x (x + y)).card = y := by
    rw [Nat.card_Ioc]
    omega
  set N_ioc : ℕ → ℝ := fun p => (((Ioc x (x + y)).filter (fun n => p ∣ n)).card : ℝ)
  set N_ico : ℕ → ℝ := fun p => (((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ)
  have h_ioc_div : (∑ n ∈ Ioc x (x + y), smoothIndicator ((X : ℝ) ^ β) n) / (y : ℝ) =
      1 - (∑ p ∈ primeRange3 β X, (N_ioc p / (y : ℝ))) := by
    rw [h_sum_ioc, h_ioc_card]
    have : ((y : ℝ) - ∑ p ∈ primeRange3 β X, N_ioc p) / (y : ℝ) =
        (y : ℝ) / (y : ℝ) - (∑ p ∈ primeRange3 β X, N_ioc p) / (y : ℝ) :=
      sub_div (y : ℝ) _ (y : ℝ)
    rw [this, div_self (ne_of_gt hy_pos), sum_div]
  have hs_ico : ∀ n ∈ Ico X (2 * X), 0 < n ∧ n ≤ 3 * X := by
    intro n hn
    simp only [mem_Ico] at hn
    constructor
    · omega
    · omega
  have h_sum_ico := sum_smoothIndicator_eq hX16 hβ34 (Ico X (2 * X)) hs_ico
  have h_ico_card : (Ico X (2 * X)).card = X := by
    rw [Nat.card_Ico]
    omega
  have h_ico_div : blockMean (smoothIndicator ((X : ℝ) ^ β)) X =
      1 - (∑ p ∈ primeRange3 β X, (N_ico p / (X : ℝ))) := by
    rw [blockMean, h_sum_ico, h_ico_card]
    have : ((X : ℝ) - ∑ p ∈ primeRange3 β X, N_ico p) / (X : ℝ) =
        (X : ℝ) / (X : ℝ) - (∑ p ∈ primeRange3 β X, N_ico p) / (X : ℝ) :=
      sub_div (X : ℝ) _ (X : ℝ)
    rw [this, div_self (ne_of_gt hX_pos), sum_div]
  have h_diff : (∑ n ∈ Ioc x (x + y), smoothIndicator ((X : ℝ) ^ β) n) / (y : ℝ) -
      blockMean (smoothIndicator ((X : ℝ) ^ β)) X =
      ∑ p ∈ primeRange3 β X, (N_ico p / (X : ℝ) - N_ioc p / (y : ℝ)) := by
    rw [h_ioc_div, h_ico_div]
    have : (1 - ∑ p ∈ primeRange3 β X, N_ioc p / (y : ℝ)) -
           (1 - ∑ p ∈ primeRange3 β X, N_ico p / (X : ℝ)) =
           (∑ p ∈ primeRange3 β X, N_ico p / (X : ℝ)) -
           (∑ p ∈ primeRange3 β X, N_ioc p / (y : ℝ)) := by ring
    rw [this, ← sum_sub_distrib]
  have h_abs_le : |(∑ n ∈ Ioc x (x + y), smoothIndicator ((X : ℝ) ^ β) n) / (y : ℝ) -
      blockMean (smoothIndicator ((X : ℝ) ^ β)) X| ≤
      ∑ p ∈ primeRange3 β X, |N_ico p / (X : ℝ) - N_ioc p / (y : ℝ)| := by
    rw [h_diff]
    exact abs_sum_le_sum_abs _ _
  have h_term_le : ∀ p ∈ primeRange3 β X,
      |N_ico p / (X : ℝ) - N_ioc p / (y : ℝ)| ≤ 3 / (y : ℝ) := by
    intro p hp
    have hp_prime : p.Prime := (mem_filter.mp hp).2
    have hp_pos : 0 < p := hp_prime.pos
    have h1 : |N_ico p / (X : ℝ) - 1 / (p : ℝ)| ≤ 2 / (X : ℝ) :=
      abs_Ico_filter_dvd_card_div_sub_inv_le X hX_nat_pos hp_pos
    have h2 : |N_ioc p / (y : ℝ) - 1 / (p : ℝ)| ≤ 1 / (y : ℝ) :=
      abs_Ioc_filter_dvd_card_div_sub_inv_le x hy_nat_pos hp_pos
    have h_tri : |N_ico p / (X : ℝ) - N_ioc p / (y : ℝ)| ≤
        |N_ico p / (X : ℝ) - 1 / (p : ℝ)| + |1 / (p : ℝ) - N_ioc p / (y : ℝ)| := by
      have : (N_ico p / (X : ℝ) - N_ioc p / (y : ℝ)) =
          (N_ico p / (X : ℝ) - 1 / (p : ℝ)) + (1 / (p : ℝ) - N_ioc p / (y : ℝ)) := by ring
      rw [this]
      exact abs_add_le _ _
    rw [abs_sub_comm (1 / (p : ℝ))] at h_tri
    have h_X_le_y : 2 / (X : ℝ) ≤ 2 / (y : ℝ) := by
      apply div_le_div_of_nonneg_left (by norm_num) hy_pos
      exact_mod_cast hy_leX
    have h_add : 2 / (X : ℝ) + 1 / (y : ℝ) ≤ 3 / (y : ℝ) := by
      calc 2 / (X : ℝ) + 1 / (y : ℝ) ≤ 2 / (y : ℝ) + 1 / (y : ℝ) := by linarith
      _ = (2 + 1) / (y : ℝ) := by rw [add_div]
      _ = 3 / (y : ℝ) := by norm_num
    linarith [h_tri, h1, h2, h_add]
  have h_sum_le : (∑ p ∈ primeRange3 β X, |N_ico p / (X : ℝ) - N_ioc p / (y : ℝ)|) ≤
      (primeRange3 β X).card * (3 / (y : ℝ)) := by
    have := sum_le_sum h_term_le
    rw [sum_const, nsmul_eq_mul] at this
    exact this
  have h_card_le : ((primeRange3 β X).card : ℝ) ≤ (Nat.primeCounting (3 * X) : ℝ) := by
    exact_mod_cast card_primeRange3_le_primeCounting β X
  have h_bound1 : ((primeRange3 β X).card : ℝ) * (3 / (y : ℝ)) ≤
      (Nat.primeCounting (3 * X) : ℝ) * (3 / (y : ℝ)) := by
    apply mul_le_mul_of_nonneg_right h_card_le (by positivity)
  have h_cheb := primeCounting_three_mul_le hX16
  have h_bound2 : (Nat.primeCounting (3 * X) : ℝ) * (3 / (y : ℝ)) ≤
      ((6 * Real.log 4 + 4) * (X : ℝ) / Real.log (X : ℝ)) * (3 / (y : ℝ)) := by
    apply mul_le_mul_of_nonneg_right h_cheb (by positivity)
  have h_alg1 : ((6 * Real.log 4 + 4) * (X : ℝ) / Real.log (X : ℝ)) * (3 / (y : ℝ)) =
      3 * (6 * Real.log 4 + 4) * ((X : ℝ) / (y : ℝ)) / Real.log (X : ℝ) := by ring
  have h_X_div_y : (X : ℝ) / (y : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 / 5 : ℝ) := by
    rw [div_le_iff₀ hy_pos]
    have := (div_le_iff₀ hlogX_pow_pos).mp hy_lower
    linarith
  have h_bound3 : 3 * (6 * Real.log 4 + 4) * ((X : ℝ) / (y : ℝ)) / Real.log (X : ℝ) ≤
      3 * (6 * Real.log 4 + 4) * (Real.log (X : ℝ)) ^ (1 / 5 : ℝ) / Real.log (X : ℝ) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hlogX_pos)
    apply mul_le_mul_of_nonneg_left h_X_div_y (by positivity)
  have h_pow := rpow_one_fifth_div_self hlogX_pos
  have h_alg2 : 3 * (6 * Real.log 4 + 4) * (Real.log (X : ℝ)) ^ (1 / 5 : ℝ) / Real.log (X : ℝ) =
      (3 * (6 * Real.log 4 + 4)) * ((Real.log (X : ℝ)) ^ (1 / 5 : ℝ) / Real.log (X : ℝ)) := by ring
  rw [h_alg2, h_pow] at h_bound3
  have h_final_bound : (3 * (6 * Real.log 4 + 4)) * (1 / (Real.log (X : ℝ)) ^ (4 / 5 : ℝ)) =
      (3 * (6 * Real.log 4 + 4)) / (Real.log (X : ℝ)) ^ (4 / 5 : ℝ) := by ring
  rw [h_final_bound] at h_bound3
  calc |(∑ n ∈ Ioc x (x + y), smoothIndicator ((X : ℝ) ^ β) n) / (y : ℝ) -
          blockMean (smoothIndicator ((X : ℝ) ^ β)) X|
    _ ≤ ∑ p ∈ primeRange3 β X, |N_ico p / (X : ℝ) - N_ioc p / (y : ℝ)| := h_abs_le
    _ ≤ (primeRange3 β X).card * (3 / (y : ℝ)) := h_sum_le
    _ ≤ (Nat.primeCounting (3 * X) : ℝ) * (3 / (y : ℝ)) := h_bound1
    _ ≤ ((6 * Real.log 4 + 4) * (X : ℝ) / Real.log (X : ℝ)) * (3 / (y : ℝ)) := h_bound2
    _ = 3 * (6 * Real.log 4 + 4) * ((X : ℝ) / (y : ℝ)) / Real.log (X : ℝ) := h_alg1
    _ ≤ (3 * (6 * Real.log 4 + 4)) / (Real.log (X : ℝ)) ^ (4 / 5 : ℝ) := h_bound3

end Erdos1201.MR
