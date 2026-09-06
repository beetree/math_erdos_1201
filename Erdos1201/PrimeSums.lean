/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

Attribution: the original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Lower bounds for prime reciprocal sums

Attribution: the original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.

This module provides an elementary lower bound for the sum of reciprocals of primes in `(X^γ, X]`.
Using Chebyshev's bounds for `θ(x)`, we establish that `θ(4y) - θ(y) ≥ y * log 2` for large `y`,
giving a lower bound for each block `(4^k, 4^(k+1)]`, and summing across the base-4 blocks gives a
Mertens-type lower bound of order `(1 - γ) / 16`.
-/

open Filter Real Topology Asymptotics Finset
open scoped Chebyshev

namespace Erdos1201

/-! ### Section 1: Asymptotics of error terms for Chebyshev θ difference -/

/-- A function that is `o(y)` is eventually at most `y * log 2`. -/
lemma eventually_le_mul_log_two_of_isLittleO (f : ℝ → ℝ) (hf : f =o[atTop] id) :
    ∀ᶠ y in atTop, f y ≤ y * log 2 := by
  have hpos : (0 : ℝ) < log 2 := by positivity
  have hb := hf.bound hpos
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with y hy hy0
  have : f y ≤ ‖f y‖ := le_norm_self _
  refine this.trans ?_
  simp only [id] at hy
  rw [norm_of_nonneg hy0] at hy
  linarith

/-- `√y = o(y)` as `y → ∞`. -/
lemma isLittleO_sqrt_id : (fun y : ℝ => Real.sqrt y) =o[atTop] id := by
  rw [isLittleO_iff_tendsto']
  · refine Tendsto.congr' ?_ (tendsto_rpow_neg_atTop (show 0 < (1/2 : ℝ) by norm_num))
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [id]
    rw [Real.sqrt_eq_rpow]
    nth_rw 3 [← rpow_one y]
    rw [← rpow_sub hy]
    norm_num
  · filter_upwards [eventually_gt_atTop 0] with y hy hzero
    exact False.elim (hy.ne' hzero)

/-- `√y * log y = o(y)` as `y → ∞`. -/
lemma isLittleO_sqrt_mul_log_id : (fun y : ℝ => Real.sqrt y * log y) =o[atTop] id := by
  have h1 : (fun y : ℝ => log y) =o[atTop] (fun y => y ^ (1/2 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num)
  have hsqrt : (fun y : ℝ => Real.sqrt y) =O[atTop] (fun y => y ^ (1/2 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 0] with y hy
    rw [norm_of_nonneg (sqrt_nonneg y), norm_of_nonneg (rpow_nonneg hy _), Real.sqrt_eq_rpow]
    simp
  have h2 := hsqrt.mul_isLittleO h1
  have h3 : (fun y : ℝ => y ^ (1/2 : ℝ) * y ^ (1/2 : ℝ)) =ᶠ[atTop] id := by
    filter_upwards [eventually_gt_atTop 0] with y hy
    simp only [id]
    rw [← rpow_add hy]
    norm_num
  exact h2.congr' .rfl h3

/-- `log (4 * y + 2) = o(y)` as `y → ∞`. -/
lemma isLittleO_log_four_y_add_two : (fun y : ℝ => log (4 * y + 2)) =o[atTop] id := by
  have h_le : (fun y : ℝ => log (4 * y + 2)) =O[atTop] (fun y => log 6 + log y) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    have hpos : 0 < 4 * y + 2 := by linarith
    have h6y : 4 * y + 2 ≤ 6 * y := by linarith
    have hlog_le : log (4 * y + 2) ≤ log (6 * y) := log_le_log hpos h6y
    rw [log_mul (by norm_num) (by linarith)] at hlog_le
    have hlog_nonneg : 0 ≤ log (4 * y + 2) := log_nonneg (by linarith)
    rw [norm_of_nonneg hlog_nonneg]
    have hsum_nonneg : 0 ≤ log 6 + log y := by
      have : 0 ≤ log 6 := log_nonneg (by norm_num)
      have : 0 ≤ log y := log_nonneg hy
      positivity
    rw [norm_of_nonneg hsum_nonneg]
    linarith
  have h_o : (fun y : ℝ => log 6 + log y) =o[atTop] id := by
    have hc : (fun _ : ℝ => log 6) =o[atTop] id := isLittleO_const_id_atTop (log 6)
    exact hc.add isLittleO_log_id_atTop
  exact h_le.trans_isLittleO h_o

/-- `4 * √y * log (4 * y) = o(y)` as `y → ∞`. -/
lemma isLittleO_four_sqrt_mul_log : (fun y : ℝ => 4 * Real.sqrt y * log (4 * y)) =o[atTop] id := by
  have h1 : (fun y : ℝ => Real.sqrt y * log (4 * y)) =ᶠ[atTop]
      (fun y => log 4 * Real.sqrt y + Real.sqrt y * log y) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [log_mul (by norm_num) hy.ne']
    ring
  have ho1 : (fun y : ℝ => log 4 * Real.sqrt y) =o[atTop] id :=
    isLittleO_sqrt_id.const_mul_left (log 4)
  have ho2 : (fun y : ℝ => Real.sqrt y * log (4 * y)) =o[atTop] id :=
    (ho1.add isLittleO_sqrt_mul_log_id).congr' h1.symm .rfl
  have ho3 : (fun y : ℝ => 4 * (Real.sqrt y * log (4 * y))) =o[atTop] id :=
    ho2.const_mul_left 4
  refine ho3.congr' ?_ .rfl
  filter_upwards with y
  ring

/-- `log 4 = 2 * log 2`. -/
lemma log_four_eq_two_mul_log_two : log 4 = 2 * log 2 := by
  have : (4 : ℝ) = 2 * 2 := by norm_num
  rw [this, log_mul two_ne_zero two_ne_zero]
  ring

/-- `√4 = 2`. -/
lemma sqrt_four : Real.sqrt 4 = 2 := by
  have : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [this, Real.sqrt_sq zero_le_two]

/-- The Chebyshev block difference `θ(4y) - θ(y)` is eventually at least `y * log 2`. -/
lemma eventually_theta_four_mul_sub_theta_ge :
    ∀ᶠ y : ℕ in atTop, (y : ℝ) * log 2 ≤ θ ((4 * y : ℕ) : ℝ) - θ (y : ℝ) := by
  have ho : (fun y : ℝ => log 2 + log (4 * y + 2) + 4 * Real.sqrt y * log (4 * y)) =o[atTop] id := by
    have h1 : (fun _ : ℝ => log 2) =o[atTop] id := isLittleO_const_id_atTop (log 2)
    exact (h1.add isLittleO_log_four_y_add_two).add isLittleO_four_sqrt_mul_log
  have hb : ∀ᶠ y : ℝ in atTop, log 2 + log (4 * y + 2) + 4 * Real.sqrt y * log (4 * y) ≤ y * log 2 :=
    eventually_le_mul_log_two_of_isLittleO _ ho
  have h_nat := tendsto_natCast_atTop_atTop.eventually hb
  filter_upwards [h_nat, eventually_ge_atTop (1 : ℕ)] with y hy hy1
  have hy1_real : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  have h4y1_real : (1 : ℝ) ≤ (4 * (y : ℝ)) := by linarith
  have hcast4y : ((4 * y : ℕ) : ℝ) = 4 * (y : ℝ) := by push_cast; rfl
  rw [hcast4y]
  have h_theta_ge := Chebyshev.theta_ge' h4y1_real
  have h_theta_le := Chebyshev.theta_le_log4_mul_x (show 0 ≤ (y : ℝ) by linarith)
  have hsqrt4y : Real.sqrt (4 * (y : ℝ)) = 2 * Real.sqrt (y : ℝ) := by
    rw [Real.sqrt_mul (by norm_num), sqrt_four]
  rw [hsqrt4y] at h_theta_ge
  rw [log_four_eq_two_mul_log_two] at h_theta_le
  linarith

/-! ### Section 2: Chebyshev block bound for prime reciprocals -/

/-- `θ n` as a sum of `log p` over primes in `(0, n]`. -/
lemma theta_nat (n : ℕ) : θ (n : ℝ) = ∑ p ∈ (Ioc 0 n).filter Nat.Prime, log p := by
  unfold Chebyshev.theta
  rw [Nat.floor_natCast]

/-- The difference `θ b - θ a` equals the sum of `log p` over primes in `(a, b]`. -/
lemma theta_sub_theta {a b : ℕ} (h : a ≤ b) :
    θ (b : ℝ) - θ (a : ℝ) = ∑ p ∈ (Ioc a b).filter Nat.Prime, log p := by
  rw [theta_nat b, theta_nat a]
  have hunion : Ioc 0 b = Ioc 0 a ∪ Ioc a b := (Ioc_union_Ioc_eq_Ioc (Nat.zero_le a) h).symm
  have hdisj : Disjoint (Ioc 0 a) (Ioc a b) := Ioc_disjoint_Ioc_of_le (le_refl a)
  have hf_union : (Ioc 0 b).filter Nat.Prime =
      ((Ioc 0 a).filter Nat.Prime) ∪ ((Ioc a b).filter Nat.Prime) := by
    rw [hunion, filter_union]
  have hf_disj : Disjoint ((Ioc 0 a).filter Nat.Prime) ((Ioc a b).filter Nat.Prime) :=
    hdisj.mono (filter_subset _ _) (filter_subset _ _)
  rw [hf_union, sum_union hf_disj, add_sub_cancel_left]

/-- Lower bound for reciprocal sum of primes in a dyadic block `(y, 4y]`. -/
lemma sum_inv_primes_block_ge {y : ℕ} (hy1 : 1 ≤ y)
    (h_theta : (y : ℝ) * log 2 ≤ θ ((4 * y : ℕ) : ℝ) - θ (y : ℝ)) :
    log 2 / (4 * log (4 * (y : ℝ))) ≤ ∑ p ∈ (Ioc y (4 * y)).filter Nat.Prime, (1 : ℝ) / p := by
  have htheta_eq : θ ((4 * y : ℕ) : ℝ) - θ (y : ℝ) = ∑ p ∈ (Ioc y (4 * y)).filter Nat.Prime, log p :=
    theta_sub_theta (by omega)
  rw [htheta_eq] at h_theta
  have hy1_real : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy1
  have hy_pos : 0 < (y : ℝ) := by positivity
  have h4y_gt1 : 1 < (4 * (y : ℝ)) := by linarith
  have hlog4y_pos : 0 < log (4 * (y : ℝ)) := log_pos h4y_gt1
  have hcoeff_pos : 0 < 4 * (y : ℝ) * log (4 * (y : ℝ)) := by positivity
  have h_le : ∑ p ∈ (Ioc y (4 * y)).filter Nat.Prime, log p ≤
      (4 * (y : ℝ) * log (4 * (y : ℝ))) * ∑ p ∈ (Ioc y (4 * y)).filter Nat.Prime, (1 : ℝ) / p := by
    rw [mul_sum]
    refine sum_le_sum fun p hp ↦ ?_
    simp only [mem_filter, mem_Ioc] at hp
    have hp_le : (p : ℝ) ≤ 4 * (y : ℝ) := by
      have : p ≤ 4 * y := hp.1.2
      exact_mod_cast this
    have hp_pos : 0 < (p : ℝ) := by
      have : 0 < p := by omega
      positivity
    have hlog_le : log (p : ℝ) ≤ log (4 * (y : ℝ)) := log_le_log hp_pos hp_le
    have hp_inv_ge : (1 : ℝ) / (4 * (y : ℝ)) ≤ (1 : ℝ) / (p : ℝ) :=
      one_div_le_one_div_of_le hp_pos hp_le
    calc log (p : ℝ)
      _ ≤ log (4 * (y : ℝ)) := hlog_le
      _ = (4 * (y : ℝ) * (1 / (4 * (y : ℝ)))) * log (4 * (y : ℝ)) := by
        have : 4 * (y : ℝ) ≠ 0 := by positivity
        rw [mul_one_div_cancel this, one_mul]
      _ = (4 * (y : ℝ) * log (4 * (y : ℝ))) * (1 / (4 * (y : ℝ))) := by ring
      _ ≤ (4 * (y : ℝ) * log (4 * (y : ℝ))) * (1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_left hp_inv_ge (by positivity)
  have h_comb : (y : ℝ) * log 2 ≤
      (4 * (y : ℝ) * log (4 * (y : ℝ))) * ∑ p ∈ (Ioc y (4 * y)).filter Nat.Prime, (1 : ℝ) / p :=
    h_theta.trans h_le
  rw [mul_comm (4 * (y : ℝ) * log (4 * (y : ℝ)))] at h_comb
  have h_div : (y : ℝ) * log 2 / (4 * (y : ℝ) * log (4 * (y : ℝ))) ≤
      ∑ p ∈ (Ioc y (4 * y)).filter Nat.Prime, (1 : ℝ) / p :=
    (div_le_iff₀ hcoeff_pos).mpr h_comb
  have h_cancel : (y : ℝ) * log 2 / (4 * (y : ℝ) * log (4 * (y : ℝ))) =
      log 2 / (4 * log (4 * (y : ℝ))) := by
    have hy_ne : (y : ℝ) ≠ 0 := by positivity
    have : 4 * (y : ℝ) * log (4 * (y : ℝ)) = (y : ℝ) * (4 * log (4 * (y : ℝ))) := by ring
    rw [this, mul_div_mul_left _ _ hy_ne]
  rw [h_cancel] at h_div
  exact h_div

/-- `log(4 * 4^k) = (k + 1) * 2 * log 2`. -/
lemma log_four_pow (k : ℕ) : log (4 * ((4 ^ k : ℕ) : ℝ)) = (k + 1 : ℝ) * (2 * log 2) := by
  have hmul : 4 * ((4 ^ k : ℕ) : ℝ) = ((4 ^ (k + 1) : ℕ) : ℝ) := by
    push_cast; rw [pow_succ']
  rw [hmul]
  have hpow : ((4 ^ (k + 1) : ℕ) : ℝ) = (4 : ℝ) ^ (k + 1) := by push_cast; rfl
  rw [hpow, log_pow]
  have h4_eq : (4 : ℝ) = 2 * 2 := by norm_num
  rw [h4_eq, log_mul two_ne_zero two_ne_zero]
  push_cast
  ring

/-- Exact evaluation of `log 2 / (4 * log (4 * 4^k)) = 1 / (8 * (k + 1))`. -/
lemma block_bound_val (k : ℕ) :
    log 2 / (4 * log (4 * ((4 ^ k : ℕ) : ℝ))) = 1 / (8 * (k + 1 : ℝ)) := by
  rw [log_four_pow k]
  have hlog2 : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-! ### Section 3: Union and sum of blocks -/

/-- Consecutive interval union for prime reciprocal sums. -/
lemma sum_filter_Ioc_consecutive (f : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ p ∈ (Ioc a b).filter Nat.Prime, f p) + (∑ p ∈ (Ioc b c).filter Nat.Prime, f p) =
      ∑ p ∈ (Ioc a c).filter Nat.Prime, f p := by
  have hunion : Ioc a c = Ioc a b ∪ Ioc b c := (Ioc_union_Ioc_eq_Ioc hab hbc).symm
  have hdisj : Disjoint (Ioc a b) (Ioc b c) := Ioc_disjoint_Ioc_of_le (le_refl b)
  have hf_union : (Ioc a c).filter Nat.Prime =
      ((Ioc a b).filter Nat.Prime) ∪ ((Ioc b c).filter Nat.Prime) := by
    rw [hunion, filter_union]
  have hf_disj : Disjoint ((Ioc a b).filter Nat.Prime) ((Ioc b c).filter Nat.Prime) :=
    hdisj.mono (filter_subset _ _) (filter_subset _ _)
  rw [hf_union, sum_union hf_disj]

/-- Sum of blocks decomposes into a single interval sum. -/
lemma sum_blocks_eq (f : ℕ → ℝ) (k₀ : ℕ) :
    ∀ n : ℕ, ∑ k ∈ Ico k₀ (k₀ + n), ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, f p =
      ∑ p ∈ (Ioc (4 ^ k₀) (4 ^ (k₀ + n))).filter Nat.Prime, f p
  | 0 => by simp
  | n + 1 => by
    rw [← Nat.add_assoc, sum_Ico_succ_top (by omega)]
    rw [sum_blocks_eq f k₀ n]
    rw [sum_filter_Ioc_consecutive f]
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- General form of `sum_blocks_eq` for `k₀ ≤ k₁`. -/
lemma sum_blocks_eq' (f : ℕ → ℝ) {k₀ k₁ : ℕ} (h : k₀ ≤ k₁) :
    ∑ k ∈ Ico k₀ k₁, ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, f p =
      ∑ p ∈ (Ioc (4 ^ k₀) (4 ^ k₁)).filter Nat.Prime, f p := by
  have : k₁ = k₀ + (k₁ - k₀) := (Nat.add_sub_of_le h).symm
  nth_rw 1 [this]
  nth_rw 2 [this]
  exact sum_blocks_eq f k₀ (k₁ - k₀)

/-- Sum of blocks is bounded above by sum over `(⌊X^γ⌋₊, X]`. -/
lemma sum_blocks_le_sum_Ioc (k₀ k₁ : ℕ) (X : ℕ) (γ : ℝ)
    (h_low : ⌊(X : ℝ) ^ γ⌋₊ ≤ 4 ^ k₀) (h_high : 4 ^ k₁ ≤ X) :
    ∑ p ∈ (Ioc (4 ^ k₀) (4 ^ k₁)).filter Nat.Prime, (1 : ℝ) / p ≤
      ∑ p ∈ (Ioc ⌊(X : ℝ) ^ γ⌋₊ X).filter Nat.Prime, (1 : ℝ) / p := by
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ by positivity)
  refine filter_subset_filter _ ?_
  refine Ioc_subset_Ioc h_low h_high

/-- Lower bounding the sum of blocks by `(k₁ - k₀) / (8 k₁)`. -/
lemma sum_blocks_lower_bound (k₀ k₁ : ℕ) (hk : k₀ ≤ k₁)
    (h_block : ∀ k ∈ Ico k₀ k₁, 1 / (8 * (k + 1 : ℝ)) ≤
      ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p) :
    ((k₁ : ℝ) - (k₀ : ℝ)) / (8 * (k₁ : ℝ)) ≤
      ∑ k ∈ Ico k₀ k₁, ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p := by
  have h_term : ∀ k ∈ Ico k₀ k₁, 1 / (8 * (k₁ : ℝ)) ≤
      ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p := by
    intro k hk_mem
    have hk_lt : k < k₁ := (mem_Ico.mp hk_mem).2
    have hk_le : (k + 1 : ℝ) ≤ (k₁ : ℝ) := by
      have : k + 1 ≤ k₁ := hk_lt
      exact_mod_cast this
    have h1 : 1 / (8 * (k₁ : ℝ)) ≤ 1 / (8 * (k + 1 : ℝ)) := by
      refine one_div_le_one_div_of_le ?_ ?_
      · positivity
      · linarith
    exact h1.trans (h_block k hk_mem)
  have h_sum := sum_le_sum h_term
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at h_sum
  have h_cast : ((k₁ - k₀ : ℕ) : ℝ) = (k₁ : ℝ) - (k₀ : ℝ) := Nat.cast_sub hk
  rw [h_cast] at h_sum
  have : ((k₁ : ℝ) - (k₀ : ℝ)) * (1 / (8 * (k₁ : ℝ))) =
      ((k₁ : ℝ) - (k₀ : ℝ)) / (8 * (k₁ : ℝ)) := by ring
  rwa [this] at h_sum

/-! ### Section 4: Rpow and floor estimates -/

/-- `4 ^ (log X / log 4) = X`. -/
lemma four_rpow_div_log_four {X : ℝ} (hX : 0 < X) :
    (4 : ℝ) ^ (log X / log 4) = X := by
  have h4_pos : (0 : ℝ) < 4 := by norm_num
  have hlog4_ne : log 4 ≠ 0 := (log_pos (by norm_num)).ne'
  rw [Real.rpow_def_of_pos h4_pos]
  rw [mul_div_cancel₀ _ hlog4_ne]
  exact Real.exp_log hX

/-- `4 ^ (γ * (log X / log 4)) = X ^ γ`. -/
lemma four_rpow_mul_div_log_four {X : ℝ} (hX : 0 < X) (γ : ℝ) :
    (4 : ℝ) ^ (γ * (log X / log 4)) = X ^ γ := by
  have h4_pos : (0 : ℝ) < 4 := by norm_num
  have hlog4_ne : log 4 ≠ 0 := (log_pos (by norm_num)).ne'
  rw [Real.rpow_def_of_pos h4_pos]
  have : log 4 * (γ * (log X / log 4)) = γ * (log 4 * (log X / log 4)) := by ring
  rw [this, mul_div_cancel₀ _ hlog4_ne]
  rw [mul_comm]
  exact (Real.rpow_def_of_pos hX γ).symm

/-- `⌊X^γ⌋₊ ≤ 4 ^ (⌊γ * (log X / log 4)⌋₊ + 1)`. -/
lemma floor_rpow_le_four_pow (X : ℕ) (hX : 1 ≤ X) (γ : ℝ) :
    ⌊(X : ℝ) ^ γ⌋₊ ≤ 4 ^ (⌊γ * (log (X : ℝ) / log 4)⌋₊ + 1) := by
  have hX_real : 0 < (X : ℝ) := by positivity
  have h_floor_le : (⌊(X : ℝ) ^ γ⌋₊ : ℝ) ≤ (X : ℝ) ^ γ := Nat.floor_le (by positivity)
  have h_lt : γ * (log (X : ℝ) / log 4) < ((⌊γ * (log (X : ℝ) / log 4)⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  have h_pow_le : (X : ℝ) ^ γ ≤ (4 : ℝ) ^ (((⌊γ * (log (X : ℝ) / log 4)⌋₊ + 1 : ℕ) : ℝ)) := by
    rw [← four_rpow_mul_div_log_four hX_real γ]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h_lt.le
  rw [Real.rpow_natCast] at h_pow_le
  exact_mod_cast h_floor_le.trans h_pow_le

/-- `4 ^ ⌊log X / log 4⌋₊ ≤ X`. -/
lemma four_pow_floor_le (X : ℕ) (hX : 1 ≤ X) :
    4 ^ ⌊log (X : ℝ) / log 4⌋₊ ≤ X := by
  have hX_real : 0 < (X : ℝ) := by positivity
  have hdiv_nonneg : 0 ≤ log (X : ℝ) / log 4 := by positivity
  have h_floor_le : (⌊log (X : ℝ) / log 4⌋₊ : ℝ) ≤ log (X : ℝ) / log 4 :=
    Nat.floor_le hdiv_nonneg
  have h_pow_le : (4 : ℝ) ^ (⌊log (X : ℝ) / log 4⌋₊ : ℝ) ≤ (4 : ℝ) ^ (log (X : ℝ) / log 4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h_floor_le
  rw [four_rpow_div_log_four hX_real] at h_pow_le
  rw [Real.rpow_natCast] at h_pow_le
  exact_mod_cast h_pow_le

/-! ### Section 5: Real algebra for the block ratio -/

/-- Algebraic lower bound: `(k₁ - k₀) / (8 k₁) ≥ (1 - γ) / 16`. -/
lemma lower_bound_algebra {γ L : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hL : 4 / (1 - γ) ≤ L)
    (k₀ k₁ : ℕ) (hk₀ : (k₀ : ℝ) ≤ γ * L + 1) (hk₁_low : L - 1 ≤ (k₁ : ℝ)) (hk₁_high : (k₁ : ℝ) ≤ L) :
    (1 - γ) / 16 ≤ ((k₁ : ℝ) - (k₀ : ℝ)) / (8 * (k₁ : ℝ)) := by
  have h_one_sub_pos : 0 < 1 - γ := by linarith
  have h4 : 4 ≤ (1 - γ) * L := by
    rw [← div_le_iff₀' h_one_sub_pos]
    exact hL
  have hL_pos : 0 < L := by
    have : 0 < 4 / (1 - γ) := div_pos (by norm_num) h_one_sub_pos
    linarith
  have hk₁_pos : 0 < (k₁ : ℝ) := by
    have : 1 < 4 / (1 - γ) := by
      rw [lt_div_iff₀ h_one_sub_pos, one_mul]
      linarith
    linarith
  have hnum : (1 - γ) * L - 2 ≤ (k₁ : ℝ) - (k₀ : ℝ) := by linarith
  have h_frac1 : ((1 - γ) * L - 2) / (8 * L) ≤ ((k₁ : ℝ) - (k₀ : ℝ)) / (8 * (k₁ : ℝ)) := by
    have hnum_pos : 0 < (1 - γ) * L - 2 := by linarith
    have hden_pos : 0 < 8 * (k₁ : ℝ) := by linarith
    have hden_le : 8 * (k₁ : ℝ) ≤ 8 * L := by linarith
    have h1 : ((1 - γ) * L - 2) / (8 * L) ≤ ((1 - γ) * L - 2) / (8 * (k₁ : ℝ)) :=
      div_le_div_of_nonneg_left hnum_pos.le hden_pos hden_le
    have h2 : ((1 - γ) * L - 2) / (8 * (k₁ : ℝ)) ≤ ((k₁ : ℝ) - (k₀ : ℝ)) / (8 * (k₁ : ℝ)) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    exact h1.trans h2
  have h_frac2 : (1 - γ) / 16 ≤ ((1 - γ) * L - 2) / (8 * L) := by
    have h_sub : 2 / (8 * L) ≤ (1 - γ) / 16 := by
      have h1 : (1 - γ) / 16 = ((1 - γ) * L) / (16 * L) := by
        have : L ≠ 0 := hL_pos.ne'
        field_simp
      have h2 : 2 / (8 * L) = 4 / (16 * L) := by
        have : L ≠ 0 := hL_pos.ne'
        field_simp
        ring
      rw [h1, h2]
      have hden : 0 < 16 * L := by linarith
      exact div_le_div_of_nonneg_right (by linarith) hden.le
    have h_split : ((1 - γ) * L - 2) / (8 * L) = (1 - γ) * L / (8 * L) - 2 / (8 * L) := by
      exact sub_div ((1 - γ) * L) 2 (8 * L)
    have h_first : (1 - γ) / 8 = (1 - γ) * L / (8 * L) := by
      have : L ≠ 0 := hL_pos.ne'
      field_simp
    rw [h_split, ← h_first]
    linarith
  exact h_frac2.trans h_frac1

/-! ### Section 6: The main theorem -/

/-- `log X / log 4` tends to infinity with `X`. -/
lemma eventually_div_log_four_ge (M : ℝ) :
    ∀ᶠ X : ℕ in atTop, M ≤ log (X : ℝ) / log 4 := by
  have hlog4 : (0 : ℝ) < log 4 := log_pos (by norm_num)
  have ht : Tendsto (fun X : ℕ => log (X : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht_div : Tendsto (fun X : ℕ => log (X : ℝ) / log 4) atTop atTop :=
    Tendsto.atTop_div_const hlog4 ht
  exact ht_div.eventually_ge_atTop M

/--
Mertens-type lower bound for prime reciprocal sum in `(X^γ, X]`.

Attribution: the original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
-/
theorem exists_sum_inv_primes_lower {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop,
      c ≤ ∑ p ∈ (Finset.Ioc ⌊(X : ℝ) ^ γ⌋₊ X).filter Nat.Prime, (1 : ℝ) / p := by
  use (1 - γ) / 16
  refine ⟨by linarith, ?_⟩
  rcases eventually_atTop.mp eventually_theta_four_mul_sub_theta_ge with ⟨y₀, hy₀⟩
  let k_min : ℕ := max 1 y₀
  have h_block_k : ∀ k ≥ k_min, 1 / (8 * (k + 1 : ℝ)) ≤
      ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p := by
    intro k hk
    have hk_ge1 : 1 ≤ 4 ^ k := by
      have : 4 ^ 0 ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      exact this
    have h4k_ge_y0 : y₀ ≤ 4 ^ k := by
      have h1 : y₀ ≤ k_min := le_max_right 1 y₀
      have h2 : k ≤ 4 ^ k := (Nat.lt_pow_self (by norm_num : 1 < 4)).le
      exact h1.trans (hk.trans h2)
    have h_theta_k := hy₀ (4 ^ k) h4k_ge_y0
    have h_block_ge := sum_inv_primes_block_ge hk_ge1 h_theta_k
    have h_succ : 4 * 4 ^ k = 4 ^ (k + 1) := by rw [pow_succ']
    rw [h_succ] at h_block_ge
    have h_val := block_bound_val k
    rwa [h_val] at h_block_ge
  let M : ℝ := max (4 / (1 - γ)) ((k_min : ℝ) / γ + 2)
  have hM := eventually_div_log_four_ge M
  filter_upwards [hM, eventually_ge_atTop (1 : ℕ)] with X hX_L hX1
  let L : ℝ := log (X : ℝ) / log 4
  let k₀ : ℕ := ⌊γ * L⌋₊ + 1
  let k₁ : ℕ := ⌊L⌋₊
  have hL_ge_M : M ≤ L := hX_L
  have hL_ge_frac : 4 / (1 - γ) ≤ L := (le_max_left _ _).trans hL_ge_M
  have hL_ge_kmin : (k_min : ℝ) / γ + 2 ≤ L := (le_max_right _ _).trans hL_ge_M
  have hk₁_high : (k₁ : ℝ) ≤ L := Nat.floor_le (by positivity)
  have hk₁_low : L - 1 ≤ (k₁ : ℝ) := by
    have : L < (k₁ : ℝ) + 1 := Nat.lt_floor_add_one L
    linarith
  have hk₀_high : (k₀ : ℝ) ≤ γ * L + 1 := by
    have : (⌊γ * L⌋₊ : ℝ) ≤ γ * L := Nat.floor_le (by positivity)
    dsimp [k₀]
    push_cast
    linarith
  have hk₀_ge_kmin : k_min ≤ k₀ := by
    have hmul : ((k_min : ℝ) / γ + 2) * γ ≤ L * γ :=
      mul_le_mul_of_nonneg_right hL_ge_kmin hγ0.le
    have hdiv : ((k_min : ℝ) / γ + 2) * γ = (k_min : ℝ) + 2 * γ := by
      rw [add_mul, div_mul_cancel₀ _ hγ0.ne']
    rw [hdiv] at hmul
    have h_le : (k_min : ℝ) ≤ γ * L := by linarith
    have h_nonneg : 0 ≤ γ * L := by linarith
    have h_floor : k_min ≤ ⌊γ * L⌋₊ := (Nat.le_floor_iff h_nonneg).mpr h_le
    dsimp [k₀]
    omega
  have hk_le : k₀ ≤ k₁ := by
    have : 4 ≤ (1 - γ) * L := by
      rw [← div_le_iff₀' (by linarith)]
      exact hL_ge_frac
    have : (k₀ : ℝ) ≤ (k₁ : ℝ) := by linarith
    exact_mod_cast this
  have h_blocks_hold : ∀ k ∈ Ico k₀ k₁, 1 / (8 * (k + 1 : ℝ)) ≤
      ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p := by
    intro k hk_mem
    have : k₀ ≤ k := (mem_Ico.mp hk_mem).1
    exact h_block_k k (hk₀_ge_kmin.trans this)
  have h_alg := lower_bound_algebra hγ0 hγ1 hL_ge_frac k₀ k₁ hk₀_high hk₁_low hk₁_high
  have h_sum_block := sum_blocks_lower_bound k₀ k₁ hk_le h_blocks_hold
  have h_decomp := sum_blocks_eq' (fun p => (1 : ℝ) / p) hk_le
  have h_sub_sum := sum_blocks_le_sum_Ioc k₀ k₁ X γ (floor_rpow_le_four_pow X hX1 γ) (four_pow_floor_le X hX1)
  calc (1 - γ) / 16
    _ ≤ ((k₁ : ℝ) - (k₀ : ℝ)) / (8 * (k₁ : ℝ)) := h_alg
    _ ≤ ∑ k ∈ Ico k₀ k₁, ∑ p ∈ (Ioc (4 ^ k) (4 ^ (k + 1))).filter Nat.Prime, (1 : ℝ) / p := h_sum_block
    _ = ∑ p ∈ (Ioc (4 ^ k₀) (4 ^ k₁)).filter Nat.Prime, (1 : ℝ) / p := h_decomp
    _ ≤ ∑ p ∈ (Ioc ⌊(X : ℝ) ^ γ⌋₊ X).filter Nat.Prime, (1 : ℝ) / p := h_sub_sum

end Erdos1201
