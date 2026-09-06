import Mathlib.NumberTheory.Chebyshev
import Erdos1201.PrimeSums

/-!
# Chebyshev-type bounds for primes in dyadic and short multiplicative ranges

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module provides upper bounds for the count and reciprocal sums of primes in intervals `(P, Q]`,
specifically:
- `card_primes_Ioc_le`: `π(Q) - π(P) ≤ log 4 * Q / log P`
- `sum_inv_primes_Ioc_le`: `∑_{P < p ≤ Q} 1/p ≤ log 4 * Q / (P * log P)`
- `sum_inv_sq_primes_Ioc_le`: `∑_{P < p ≤ Q} 1/p^2 ≤ log 4 * Q / (P^2 * log P)`
- `sum_inv_primes_Ioc_two_mul_le`: `∑_{P < p ≤ 2P} 1/p ≤ 4 / log P`
-/

open Finset Real
open scoped Chebyshev

namespace Erdos1201.MR

/-- The sum of `log p` over primes in `(P, Q]` is bounded by Chebyshev's `θ(Q)`. -/
lemma sum_primes_Ioc_log_le_theta (P Q : ℕ) :
    ∑ p ∈ (Ioc P Q).filter Nat.Prime, log (p : ℝ) ≤ θ (Q : ℝ) := by
  rw [theta_nat Q]
  refine sum_le_sum_of_subset_of_nonneg ?_ ?_
  · refine filter_subset_filter _ (Ioc_subset_Ioc (Nat.zero_le P) le_rfl)
  · intro p hp _
    have hp_prime : Nat.Prime p := (mem_filter.mp hp).2
    have hp_two_le : 2 ≤ p := hp_prime.two_le
    have hp_ge_one : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
    exact log_nonneg hp_ge_one

/-- The sum of `log p` over primes in `(P, Q]` is at most `log 4 * Q`. -/
lemma sum_primes_Ioc_log_le (P Q : ℕ) :
    ∑ p ∈ (Ioc P Q).filter Nat.Prime, log (p : ℝ) ≤ log 4 * (Q : ℝ) := by
  have hQ_nonneg : 0 ≤ (Q : ℝ) := Nat.cast_nonneg Q
  exact (sum_primes_Ioc_log_le_theta P Q).trans (Chebyshev.theta_le_log4_mul_x hQ_nonneg)

/-- The number of primes in `(P, Q]` is at most `log 4 * Q / log P`. -/
theorem card_primes_Ioc_le (P Q : ℕ) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    (((Finset.Ioc P Q).filter Nat.Prime).card : ℝ) ≤ Real.log 4 * Q / Real.log P := by
  have _ := hPQ
  have hP_pos : 0 < (P : ℝ) := by positivity
  have hP_gt_one : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hlogP_pos : 0 < log (P : ℝ) := log_pos hP_gt_one
  have h_sum_le : (((Ioc P Q).filter Nat.Prime).card : ℝ) * log (P : ℝ) ≤
      ∑ p ∈ (Ioc P Q).filter Nat.Prime, log (p : ℝ) := by
    have h_const : ∑ p ∈ (Ioc P Q).filter Nat.Prime, log (P : ℝ) =
        (((Ioc P Q).filter Nat.Prime).card : ℝ) * log (P : ℝ) := by
      rw [sum_const, nsmul_eq_mul]
    rw [← h_const]
    refine sum_le_sum fun p hp ↦ ?_
    simp only [mem_filter, mem_Ioc] at hp
    have hp_le : P ≤ p := hp.1.1.le
    have hp_real : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_le
    exact log_le_log hP_pos hp_real
  have h_trans : (((Ioc P Q).filter Nat.Prime).card : ℝ) * log (P : ℝ) ≤ log 4 * (Q : ℝ) :=
    h_sum_le.trans (sum_primes_Ioc_log_le P Q)
  exact (le_div_iff₀ hlogP_pos).mpr h_trans

/-- The sum of reciprocals of primes in `(P, Q]` is at most `log 4 * Q / (P * log P)`. -/
theorem sum_inv_primes_Ioc_le (P Q : ℕ) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    (∑ p ∈ (Finset.Ioc P Q).filter Nat.Prime, (1 : ℝ) / p) ≤ Real.log 4 * Q / (P * Real.log P) := by
  have hP_pos : 0 < (P : ℝ) := by positivity
  have h_term_le : ∀ p ∈ (Ioc P Q).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ≤ 1 / (P : ℝ) := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    have hp_le : P ≤ p := hp.1.1.le
    have hp_real : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_le
    exact one_div_le_one_div_of_le hP_pos hp_real
  have h_sum_le : (∑ p ∈ (Ioc P Q).filter Nat.Prime, (1 : ℝ) / p) ≤
      (((Ioc P Q).filter Nat.Prime).card : ℝ) * (1 / (P : ℝ)) := by
    have h_const : ∑ p ∈ (Ioc P Q).filter Nat.Prime, (1 : ℝ) / (P : ℝ) =
        (((Ioc P Q).filter Nat.Prime).card : ℝ) * (1 / (P : ℝ)) := by
      rw [sum_const, nsmul_eq_mul]
    rw [← h_const]
    exact sum_le_sum h_term_le
  have h_card := card_primes_Ioc_le P Q hP hPQ
  have h_card_div : (((Ioc P Q).filter Nat.Prime).card : ℝ) * (1 / (P : ℝ)) ≤
      (Real.log 4 * Q / Real.log P) * (1 / (P : ℝ)) := by
    refine mul_le_mul_of_nonneg_right h_card (by positivity)
  have h_eq : (Real.log 4 * (Q : ℝ) / Real.log (P : ℝ)) * (1 / (P : ℝ)) =
      Real.log 4 * (Q : ℝ) / ((P : ℝ) * Real.log (P : ℝ)) := by
    have hP_ne : (P : ℝ) ≠ 0 := hP_pos.ne'
    have hlog_ne : Real.log (P : ℝ) ≠ 0 := (log_pos (show 1 < (P : ℝ) by exact_mod_cast (by omega : 1 < P))).ne'
    field_simp
  exact h_sum_le.trans (h_card_div.trans_eq h_eq)

/-- The sum of squared reciprocals of primes in `(P, Q]` is at most `log 4 * Q / (P^2 * log P)`. -/
theorem sum_inv_sq_primes_Ioc_le (P Q : ℕ) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    (∑ p ∈ (Finset.Ioc P Q).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) ≤ Real.log 4 * Q / ((P : ℝ) ^ 2 * Real.log P) := by
  have hP_pos : 0 < (P : ℝ) := by positivity
  have h_term_le : ∀ p ∈ (Ioc P Q).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / (P : ℝ) ^ 2 := by
    intro p hp
    simp only [mem_filter, mem_Ioc] at hp
    have hp_le : P ≤ p := hp.1.1.le
    have hp_real : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_le
    have hp_sq_le : (P : ℝ) ^ 2 ≤ (p : ℝ) ^ 2 := by
      nlinarith
    exact one_div_le_one_div_of_le (by positivity) hp_sq_le
  have h_sum_le : (∑ p ∈ (Ioc P Q).filter Nat.Prime, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      (((Ioc P Q).filter Nat.Prime).card : ℝ) * (1 / (P : ℝ) ^ 2) := by
    have h_const : ∑ p ∈ (Ioc P Q).filter Nat.Prime, (1 : ℝ) / (P : ℝ) ^ 2 =
        (((Ioc P Q).filter Nat.Prime).card : ℝ) * (1 / (P : ℝ) ^ 2) := by
      rw [sum_const, nsmul_eq_mul]
    rw [← h_const]
    exact sum_le_sum h_term_le
  have h_card := card_primes_Ioc_le P Q hP hPQ
  have h_card_div : (((Ioc P Q).filter Nat.Prime).card : ℝ) * (1 / (P : ℝ) ^ 2) ≤
      (Real.log 4 * Q / Real.log P) * (1 / (P : ℝ) ^ 2) := by
    refine mul_le_mul_of_nonneg_right h_card (by positivity)
  have h_eq : (Real.log 4 * (Q : ℝ) / Real.log (P : ℝ)) * (1 / (P : ℝ) ^ 2) =
      Real.log 4 * (Q : ℝ) / ((P : ℝ) ^ 2 * Real.log (P : ℝ)) := by
    have hP_ne : (P : ℝ) ≠ 0 := hP_pos.ne'
    have hlog_ne : Real.log (P : ℝ) ≠ 0 := (log_pos (show 1 < (P : ℝ) by exact_mod_cast (by omega : 1 < P))).ne'
    field_simp
  exact h_sum_le.trans (h_card_div.trans_eq h_eq)

/-- `log 4 ≤ 2`, derived from `log x ≤ x - 1`. -/
lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h4 : (4 : ℝ) = 2 * 2 := by norm_num
  rw [h4, Real.log_mul two_ne_zero two_ne_zero]
  have h2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos zero_lt_two
  linarith

/-- In a dyadic range the reciprocal sum is at most 4/log P. -/
theorem sum_inv_primes_Ioc_two_mul_le (P : ℕ) (hP : 2 ≤ P) :
    (∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, (1 : ℝ) / p) ≤ 4 / Real.log P := by
  have hPQ : P ≤ 2 * P := by omega
  have h_bound := sum_inv_primes_Ioc_le P (2 * P) hP hPQ
  have hP_pos : 0 < (P : ℝ) := by positivity
  have hlogP_pos : 0 < log (P : ℝ) := log_pos (show 1 < (P : ℝ) by exact_mod_cast (by omega : 1 < P))
  have hcast : ((2 * P : ℕ) : ℝ) = 2 * (P : ℝ) := by push_cast; rfl
  rw [hcast] at h_bound
  have h_cancel : Real.log 4 * (2 * (P : ℝ)) / ((P : ℝ) * Real.log (P : ℝ)) =
      (2 * Real.log 4) / Real.log (P : ℝ) := by
    have hP_ne : (P : ℝ) ≠ 0 := hP_pos.ne'
    have hlog_ne : Real.log (P : ℝ) ≠ 0 := hlogP_pos.ne'
    field_simp
  rw [h_cancel] at h_bound
  refine h_bound.trans ?_
  have h_num : 2 * Real.log 4 ≤ 4 := by
    have := log_four_le_two
    linarith
  exact div_le_div_of_nonneg_right h_num hlogP_pos.le

end Erdos1201.MR
