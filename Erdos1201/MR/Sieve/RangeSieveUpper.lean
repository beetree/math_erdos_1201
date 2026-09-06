import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.PrimeCounting
import Erdos1201.Vendor.NumberTheory.SelbergSieve.BrunTitchmarsh
import Erdos1201.Vendor.NumberTheory.MertensTheorems

/-!
# Sieve Upper Bounds for Prime Ranges

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module provides upper bounds on the number of integers in the dyadic interval $(X, 2X]$
with no prime factor in a given range $[P, Q]$, corresponding to the standard sieve bound
of order $X \frac{\log P}{\log Q}$ in Section 2 of Matomäki–Radziwiłł (arXiv:1501.04585v4).

## Main Results

- `prod_prime_one_minus_inv_range_le`: Mertens' product bound for primes in an interval $[P, Q]$,
  showing that $\prod_{P \le p \le Q} (1 - 1/p) \le C \frac{\log P}{\log Q}$ for all $2 \le P \le Q$.
- `card_no_prime_factor_in_Icc_two_le`: The Selberg / Brun–Titchmarsh sieve bound for $P = 2$,
  showing that the number of integers in $(X, 2X]$ with no prime factor $\le Q$ is at most
  $C X / \log Q$ whenever $Q^4 \le X$.
- `card_no_prime_factor_in_Icc_le_of_le_pow`: The sieve upper bound when the ratio $Q/P$ is
  bounded ($Q \le P^4$), with constant $C = 4$.
- `card_no_prime_factor_in_Icc_le`: The range sieve upper bound under the condition $Q \le P^4$.
-/

open Classical
open Real
open BrunTitchmarsh

namespace Erdos1201.MR

/-! ### Part 1: Mertens Product Bound for General Ranges -/

/-- Constant bounding the Mertens remainder term $|E_3(N)|$ for all $N \ge 2$. -/
noncomputable def E_const : ℝ := (log 4 + 3) / log 2 + 1 / 2

/-- Explicit constant for the Mertens prime product range bound. -/
noncomputable def C_mertens : ℝ := exp (2 * E_const) + exp (-eulerMascheroniConstant) * exp E_const / log 2

lemma E₃_le_const {N : ℕ} (hN : 2 ≤ N) :
    |Mertens.E₃ (N : ℝ)| ≤ E_const := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h_bound := Mertens.E₃_bound hN2
  have hfloor : ⌊(N : ℝ)⌋₊ = N := Nat.floor_natCast N
  rw [hfloor] at h_bound
  have hlog2_pos : 0 < log 2 := log_pos (by norm_num)
  have hlog_le : log 2 ≤ log (N : ℝ) := log_le_log (by norm_num) hN2
  have h_log_frac : (log 4 + 3) / log (N : ℝ) ≤ (log 4 + 3) / log 2 := by
    have h_num_pos : 0 ≤ log 4 + 3 := by positivity
    exact div_le_div_of_nonneg_left h_num_pos hlog2_pos hlog_le
  have h_inv : 1 / (N : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hN2
  change |Mertens.E₃ (N : ℝ)| ≤ (log 4 + 3) / log 2 + 1 / 2
  linarith

lemma prod_prime_one_minus_inv_primesLE_le {N : ℕ} (hN : 2 ≤ N) :
    ∏ p ∈ N.primesLE, (1 - 1 / (p : ℝ)) ≤ exp (-eulerMascheroniConstant) * exp E_const / log (N : ℝ) := by
  have hN1 : 1 < N := by omega
  rw [Mertens.prod_prime_one_minus_inv_eq_nat hN1]
  have hlogN_pos : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN1)
  refine div_le_div_of_nonneg_right ?_ hlogN_pos.le
  refine mul_le_mul_of_nonneg_left ?_ (exp_nonneg _)
  have hE := E₃_le_const hN
  rw [abs_le] at hE
  exact exp_le_exp.mpr hE.2

lemma prod_prime_one_minus_inv_primesLE_ge {N : ℕ} (hN : 2 ≤ N) :
    exp (-eulerMascheroniConstant) * exp (-E_const) / log (N : ℝ) ≤ ∏ p ∈ N.primesLE, (1 - 1 / (p : ℝ)) := by
  have hN1 : 1 < N := by omega
  rw [Mertens.prod_prime_one_minus_inv_eq_nat hN1]
  have hlogN_pos : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN1)
  refine div_le_div_of_nonneg_right ?_ hlogN_pos.le
  refine mul_le_mul_of_nonneg_left ?_ (exp_nonneg _)
  have hE := E₃_le_const hN
  rw [abs_le] at hE
  exact exp_le_exp.mpr hE.1

lemma prod_pos_of_primesLE (N : ℕ) :
    0 < ∏ p ∈ N.primesLE, (1 - 1 / (p : ℝ)) := by
  refine Finset.prod_pos ?_
  intro p hp
  have hp2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
  have : (p : ℝ) ≥ 2 := by exact_mod_cast hp2
  have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
  linarith

lemma prod_pos_of_range (P Q : ℕ) :
    0 < ∏ p ∈ (Finset.Icc P Q).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  refine Finset.prod_pos ?_
  intro p hp
  have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
  have : (p : ℝ) ≥ 2 := by exact_mod_cast hp2
  have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) this
  linarith

lemma primesLE_disjoint_range (P Q : ℕ) (hP : 2 ≤ P) :
    Disjoint (P - 1).primesLE ((Finset.Icc P Q).filter Nat.Prime) := by
  refine Finset.disjoint_left.mpr ?_
  intro p hp1 hp2
  have h1 : p ≤ P - 1 := (Nat.mem_primesLE.mp hp1).1
  have h2 : P ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp2).1).1
  omega

lemma primesLE_union_range (P Q : ℕ) (hPQ : P ≤ Q) :
    (P - 1).primesLE ∪ ((Finset.Icc P Q).filter Nat.Prime) = Q.primesLE := by
  ext p
  simp only [Nat.mem_primesLE, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro (⟨hp, hprime⟩ | ⟨⟨hPle, hpQ⟩, hprime⟩)
    · exact ⟨hp.trans (by omega), hprime⟩
    · exact ⟨hpQ, hprime⟩
  · rintro ⟨hpQ, hprime⟩
    by_cases h : p ≤ P - 1
    · left; exact ⟨h, hprime⟩
    · right
      refine ⟨⟨by omega, hpQ⟩, hprime⟩

lemma primesLE_one_eq_empty : (1 : ℕ).primesLE = ∅ := by
  ext p
  simp only [Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hprime⟩
    have : 2 ≤ p := hprime.two_le
    omega
  · intro hp
    cases hp

/-- Mertens' product bound for primes in an interval $[P, Q]$:
$$\prod_{P \le p \le Q} \left(1 - \frac{1}{p}\right) \le C \frac{\log P}{\log Q}$$
for an absolute constant $C > 0$. -/
theorem prod_prime_one_minus_inv_range_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : ℕ), 2 ≤ P → P ≤ Q →
      ∏ p ∈ (Finset.Icc P Q).filter Nat.Prime, (1 - 1 / (p : ℝ)) ≤ C * Real.log P / Real.log Q := by
  use C_mertens
  have hlog2_pos : 0 < log 2 := log_pos (by norm_num)
  have hE_pos : 0 < E_const := by
    dsimp [E_const]
    positivity
  have hC_pos : 0 < C_mertens := by
    dsimp [C_mertens]
    positivity
  refine ⟨hC_pos, ?_⟩
  intro P Q hP hPQ
  have hQ : 2 ≤ Q := hP.trans hPQ
  have hQ_gt1 : 1 < (Q : ℝ) := by
    have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have hlogQ_pos : 0 < log (Q : ℝ) := log_pos hQ_gt1
  have hlogP_pos : 0 < log (P : ℝ) := log_pos (by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith)
  have h_split : ∏ p ∈ Q.primesLE, (1 - 1 / (p : ℝ)) =
      (∏ p ∈ (P - 1).primesLE, (1 - 1 / (p : ℝ))) *
      (∏ p ∈ (Finset.Icc P Q).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
    rw [← primesLE_union_range P Q hPQ]
    exact Finset.prod_union (primesLE_disjoint_range P Q hP)
  by_cases hP2 : P = 2
  · have hP1 : P - 1 = 1 := by omega
    rw [hP1, primesLE_one_eq_empty, Finset.prod_empty, one_mul] at h_split
    have h_prod_le := prod_prime_one_minus_inv_primesLE_le hQ
    rw [← h_split]
    refine h_prod_le.trans ?_
    have h_const_le : exp (-eulerMascheroniConstant) * exp E_const / log 2 ≤ C_mertens := by
      dsimp [C_mertens]
      have : 0 < exp (2 * E_const) := exp_pos _
      linarith
    have h_P2_real : (P : ℝ) = 2 := by exact_mod_cast hP2
    calc exp (-eulerMascheroniConstant) * exp E_const / log (Q : ℝ)
      _ = (exp (-eulerMascheroniConstant) * exp E_const / log 2) * log 2 / log (Q : ℝ) := by
        have : log 2 ≠ 0 := hlog2_pos.ne'
        field_simp
      _ = (exp (-eulerMascheroniConstant) * exp E_const / log 2) * (log (P : ℝ) / log (Q : ℝ)) := by
        rw [h_P2_real]
        ring
      _ ≤ C_mertens * (log (P : ℝ) / log (Q : ℝ)) :=
        mul_le_mul_of_nonneg_right h_const_le (div_nonneg hlogP_pos.le hlogQ_pos.le)
      _ = C_mertens * log (P : ℝ) / log (Q : ℝ) := by ring
  · have hP_gt2 : 3 ≤ P := by omega
    have hPminus : 2 ≤ P - 1 := by omega
    have hPminus_gt1 : 1 < ((P - 1 : ℕ) : ℝ) := by
      have : (2 : ℝ) ≤ ((P - 1 : ℕ) : ℝ) := by exact_mod_cast hPminus
      linarith
    have hlogPminus_pos : 0 < log ((P - 1 : ℕ) : ℝ) := log_pos hPminus_gt1
    have h_prod_Q := prod_prime_one_minus_inv_primesLE_le hQ
    have h_prod_P := prod_prime_one_minus_inv_primesLE_ge hPminus
    have h_P_pos := prod_pos_of_primesLE (P - 1)
    have h_range_eq : ∏ p ∈ (Finset.Icc P Q).filter Nat.Prime, (1 - 1 / (p : ℝ)) =
        (∏ p ∈ Q.primesLE, (1 - 1 / (p : ℝ))) / (∏ p ∈ (P - 1).primesLE, (1 - 1 / (p : ℝ))) := by
      rw [h_split]
      exact (mul_div_cancel_left₀ _ h_P_pos.ne').symm
    rw [h_range_eq]
    have h_div_le : (∏ p ∈ Q.primesLE, (1 - 1 / (p : ℝ))) / (∏ p ∈ (P - 1).primesLE, (1 - 1 / (p : ℝ))) ≤
        (exp (-eulerMascheroniConstant) * exp E_const / log (Q : ℝ)) /
        (exp (-eulerMascheroniConstant) * exp (-E_const) / log ((P - 1 : ℕ) : ℝ)) := by
      have h1 : (∏ p ∈ Q.primesLE, (1 - 1 / (p : ℝ))) / (∏ p ∈ (P - 1).primesLE, (1 - 1 / (p : ℝ))) ≤
          (exp (-eulerMascheroniConstant) * exp E_const / log (Q : ℝ)) / (∏ p ∈ (P - 1).primesLE, (1 - 1 / (p : ℝ))) :=
        div_le_div_of_nonneg_right h_prod_Q h_P_pos.le
      refine h1.trans ?_
      have h_denom_pos : 0 < exp (-eulerMascheroniConstant) * exp (-E_const) / log ((P - 1 : ℕ) : ℝ) := by
        have : 0 < exp (-eulerMascheroniConstant) * exp (-E_const) := by positivity
        exact div_pos this hlogPminus_pos
      have h_num_nonneg : 0 ≤ exp (-eulerMascheroniConstant) * exp E_const / log (Q : ℝ) := by positivity
      exact div_le_div_of_nonneg_left h_num_nonneg h_denom_pos h_prod_P
    refine h_div_le.trans ?_
    have h_simplify : (exp (-eulerMascheroniConstant) * exp E_const / log (Q : ℝ)) /
        (exp (-eulerMascheroniConstant) * exp (-E_const) / log ((P - 1 : ℕ) : ℝ)) =
        exp (2 * E_const) * log ((P - 1 : ℕ) : ℝ) / log (Q : ℝ) := by
      have he : exp (-eulerMascheroniConstant) ≠ 0 := (exp_pos _).ne'
      have hrw : exp E_const / exp (-E_const) = exp (2 * E_const) := by
        rw [← exp_sub]
        ring_nf
      calc (exp (-eulerMascheroniConstant) * exp E_const / log (Q : ℝ)) /
          (exp (-eulerMascheroniConstant) * exp (-E_const) / log ((P - 1 : ℕ) : ℝ))
        _ = ((exp (-eulerMascheroniConstant) * exp E_const) / (exp (-eulerMascheroniConstant) * exp (-E_const))) *
            (log ((P - 1 : ℕ) : ℝ) / log (Q : ℝ)) := by
          field_simp
        _ = (exp E_const / exp (-E_const)) * (log ((P - 1 : ℕ) : ℝ) / log (Q : ℝ)) := by
          rw [mul_div_mul_left _ _ he]
        _ = exp (2 * E_const) * (log ((P - 1 : ℕ) : ℝ) / log (Q : ℝ)) := by rw [hrw]
        _ = exp (2 * E_const) * log ((P - 1 : ℕ) : ℝ) / log (Q : ℝ) := by ring
    rw [h_simplify]
    have h_Pminus_le_P : ((P - 1 : ℕ) : ℝ) ≤ (P : ℝ) := by
      have : P - 1 ≤ P := by omega
      exact Nat.cast_le.mpr this
    have h_log_le : log ((P - 1 : ℕ) : ℝ) ≤ log (P : ℝ) :=
      log_le_log (by linarith) h_Pminus_le_P
    have h_main_le : exp (2 * E_const) * log ((P - 1 : ℕ) : ℝ) / log (Q : ℝ) ≤
        exp (2 * E_const) * log (P : ℝ) / log (Q : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ hlogQ_pos.le
      exact mul_le_mul_of_nonneg_left h_log_le (exp_pos _).le
    refine h_main_le.trans ?_
    have h_C_ge : exp (2 * E_const) ≤ C_mertens := by
      dsimp [C_mertens]
      have : 0 < exp (-eulerMascheroniConstant) * exp E_const / log 2 := by positivity
      linarith
    refine div_le_div_of_nonneg_right ?_ hlogQ_pos.le
    exact mul_le_mul_of_nonneg_right h_C_ge (by positivity)


/-! ### Part 2: Selberg / Brun–Titchmarsh Sieve Bound for $P = 2$ -/

lemma log_le_four_mul_rpow_fourth {x : ℝ} (hx : 0 < x) :
    log x ≤ 4 * x ^ (1/4 : ℝ) := by
  have h_pos : 0 < x ^ (1/4 : ℝ) := rpow_pos_of_pos hx _
  have h1 := log_le_sub_one_of_pos h_pos
  have h2 : log (x ^ (1/4 : ℝ)) = (1/4 : ℝ) * log x := log_rpow hx (1/4 : ℝ)
  rw [h2] at h1
  linarith

lemma one_add_log_le_five_mul_rpow_fourth {x : ℝ} (hx : 1 ≤ x) :
    1 + log x ≤ 5 * x ^ (1/4 : ℝ) := by
  have hx_pos : 0 < x := by linarith
  have h1 : 1 ≤ x ^ (1/4 : ℝ) := by
    rw [← rpow_zero x]
    exact rpow_le_rpow_of_exponent_le hx (by norm_num)
  have h2 := log_le_four_mul_rpow_fourth hx_pos
  linarith

lemma error_term_le {Q X : ℕ} (hQ : 2 ≤ Q) (hQX : (Q : ℝ) ^ 4 ≤ X) :
    5 * (Q : ℝ) * (1 + log (Q : ℝ)) ^ 3 ≤ 2500 * (X : ℝ) / log (Q : ℝ) := by
  have hQ_real : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ1 : 1 ≤ (Q : ℝ) := by linarith
  have hQ_gt1 : 1 < (Q : ℝ) := by linarith
  have hQ_pos : 0 < (Q : ℝ) := by linarith
  have hlogQ_pos : 0 < log (Q : ℝ) := log_pos hQ_gt1
  have h_one_log := one_add_log_le_five_mul_rpow_fourth hQ1
  have h_log := log_le_four_mul_rpow_fourth hQ_pos
  have h_one_log_nonneg : 0 ≤ 1 + log (Q : ℝ) := by positivity
  have h_cube : (1 + log (Q : ℝ)) ^ 3 ≤ 125 * (Q : ℝ) ^ (3/4 : ℝ) := by
    have hc : (1 + log (Q : ℝ)) ^ 3 ≤ (5 * (Q : ℝ) ^ (1/4 : ℝ)) ^ 3 := by
      gcongr
    refine hc.trans ?_
    have h_pow3 : (5 * (Q : ℝ) ^ (1/4 : ℝ)) ^ 3 = 125 * ((Q : ℝ) ^ (1/4 : ℝ)) ^ 3 := by ring
    rw [h_pow3]
    have h_rpow : ((Q : ℝ) ^ (1/4 : ℝ)) ^ 3 = (Q : ℝ) ^ (3/4 : ℝ) := by
      rw [← rpow_natCast, ← rpow_mul hQ_pos.le]
      norm_num
    rw [h_rpow]
  have h_mul_log : (1 + log (Q : ℝ)) ^ 3 * log (Q : ℝ) ≤ 500 * (Q : ℝ) := by
    have h_step : (1 + log (Q : ℝ)) ^ 3 * log (Q : ℝ) ≤ (125 * (Q : ℝ) ^ (3/4 : ℝ)) * (4 * (Q : ℝ) ^ (1/4 : ℝ)) := by
      gcongr
    refine h_step.trans ?_
    have h_assoc : (125 * (Q : ℝ) ^ (3/4 : ℝ)) * (4 * (Q : ℝ) ^ (1/4 : ℝ)) = 500 * ((Q : ℝ) ^ (3/4 : ℝ) * (Q : ℝ) ^ (1/4 : ℝ)) := by ring
    rw [h_assoc]
    have h_add : (Q : ℝ) ^ (3/4 : ℝ) * (Q : ℝ) ^ (1/4 : ℝ) = (Q : ℝ) ^ (1 : ℝ) := by
      rw [← rpow_add hQ_pos]
      norm_num
    rw [h_add, rpow_one]
  have h_step2 : (Q : ℝ) * ((1 + log (Q : ℝ)) ^ 3 * log (Q : ℝ)) ≤ 500 * (Q : ℝ) ^ 2 := by
    calc (Q : ℝ) * ((1 + log (Q : ℝ)) ^ 3 * log (Q : ℝ))
      _ ≤ (Q : ℝ) * (500 * (Q : ℝ)) := by gcongr
      _ = 500 * (Q : ℝ) ^ 2 := by ring
  have h_Q2_le : (Q : ℝ) ^ 2 ≤ (Q : ℝ) ^ 4 := by
    have h_sq : (Q : ℝ) ^ 2 = (Q : ℝ) ^ (2 : ℝ) := by norm_num
    have h_four : (Q : ℝ) ^ 4 = (Q : ℝ) ^ (4 : ℝ) := by norm_num
    rw [h_sq, h_four]
    exact rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have h_step3 : 5 * (Q : ℝ) * (1 + log (Q : ℝ)) ^ 3 * log (Q : ℝ) ≤ 2500 * (X : ℝ) := by
    calc 5 * (Q : ℝ) * (1 + log (Q : ℝ)) ^ 3 * log (Q : ℝ)
      _ = 5 * ((Q : ℝ) * ((1 + log (Q : ℝ)) ^ 3 * log (Q : ℝ))) := by ring
      _ ≤ 5 * (500 * (Q : ℝ) ^ 2) := by gcongr
      _ = 2500 * (Q : ℝ) ^ 2 := by ring
      _ ≤ 2500 * (Q : ℝ) ^ 4 := by gcongr
      _ ≤ 2500 * (X : ℝ) := by gcongr
  rw [le_div_iff₀ hlogQ_pos]
  exact h_step3

lemma card_no_prime_factor_in_Icc_two_le_raw (X Q : ℕ) (hQ : 2 ≤ Q) (hQX : (Q : ℝ) ^ 4 ≤ X) :
    (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → 2 ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ) ≤
      2 * (X : ℝ) / Real.log (Q : ℝ) + 5 * (Q : ℝ) * (1 + Real.log (Q : ℝ)) ^ 3 := by
  have hX_pos : 0 < (X : ℝ) := by
    have : (2 : ℝ) ^ 4 ≤ (X : ℝ) := by
      refine le_trans ?_ hQX
      gcongr
      exact_mod_cast hQ
    linarith
  have hQ_gt1 : 1 < (Q : ℝ) := by
    have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    linarith
  have h_ceil : Nat.ceil (X : ℝ) = X := Nat.ceil_natCast X
  have h_floor : Nat.floor ((X : ℝ) + (X : ℝ)) = 2 * X := by
    have h_add : (X : ℝ) + (X : ℝ) = (((2 * X : ℕ) : ℝ)) := by push_cast; ring
    rw [h_add, Nat.floor_natCast]
  have h_sub : (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → 2 ≤ p → p ≤ Q → ¬ p ∣ n) ⊆
      (Finset.Icc (Nat.ceil (X : ℝ)) (Nat.floor ((X : ℝ) + (X : ℝ)))).filter
        (fun d ↦ ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (Q : ℝ) → ¬p ∣ d) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    rw [h_ceil, h_floor]
    refine ⟨⟨by omega, hn.1.2⟩, ?_⟩
    intro p hp hpQ
    have hp_nat : p ≤ Q := by exact_mod_cast hpQ
    exact hn.2 p hp hp.two_le hp_nat
  have h_card_le : (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → 2 ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ) ≤
      (((Finset.Icc (Nat.ceil (X : ℝ)) (Nat.floor ((X : ℝ) + (X : ℝ)))).filter
        (fun d ↦ ∀ p : ℕ, p.Prime → (p : ℝ) ≤ (Q : ℝ) → ¬p ∣ d)).card : ℝ) := by
    exact Nat.cast_le.mpr (Finset.card_le_card h_sub)
  rw [← BrunTitchmarsh.siftedSum_eq_card (X : ℝ) (X : ℝ) (Q : ℝ) hQ_gt1.le] at h_card_le
  refine h_card_le.trans ?_
  exact BrunTitchmarsh.siftedSum_le (X : ℝ) (X : ℝ) (Q : ℝ) hX_pos hX_pos hQ_gt1

/-- Sieve upper bound for numbers with no prime factors $\le Q$ (the case $P = 2$),
obtained from Selberg's sieve (Brun–Titchmarsh theorem). -/
theorem card_no_prime_factor_in_Icc_two_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X Q : ℕ), 2 ≤ Q → (Q : ℝ) ^ 4 ≤ X →
      (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → 2 ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ) ≤
        C * (X : ℝ) * Real.log 2 / Real.log (Q : ℝ) := by
  have hlog2_pos : 0 < log 2 := log_pos (by norm_num)
  let C := 2502 / log 2
  use C
  have hC_pos : 0 < C := div_pos (by norm_num) hlog2_pos
  refine ⟨hC_pos, ?_⟩
  intro X Q hQ hQX
  have h_raw := card_no_prime_factor_in_Icc_two_le_raw X Q hQ hQX
  have h_err := error_term_le hQ hQX
  have h_sum_le : 2 * (X : ℝ) / log (Q : ℝ) + 5 * (Q : ℝ) * (1 + log (Q : ℝ)) ^ 3 ≤
      2502 * (X : ℝ) / log (Q : ℝ) := by
    calc 2 * (X : ℝ) / log (Q : ℝ) + 5 * (Q : ℝ) * (1 + log (Q : ℝ)) ^ 3
      _ ≤ 2 * (X : ℝ) / log (Q : ℝ) + 2500 * (X : ℝ) / log (Q : ℝ) := by linarith [h_err]
      _ = 2502 * (X : ℝ) / log (Q : ℝ) := by ring
  have h_eq : 2502 * (X : ℝ) / log (Q : ℝ) = C * (X : ℝ) * log 2 / log (Q : ℝ) := by
    dsimp [C]
    field_simp
  exact (h_raw.trans h_sum_le).trans (le_of_eq h_eq)


/-! ### Part 3: Sieve Bound for Bounded Range Ratio $Q \le P^4$ -/

/-- Range sieve upper bound when $Q \le P^4$:
since the interval $(X, 2X]$ has cardinality at most $X$, and $1 \le 4 \log P / \log Q$
whenever $Q \le P^4$, the trivial bound immediately implies the result with $C = 4$. -/
theorem card_no_prime_factor_in_Icc_le_of_le_pow :
    ∃ C : ℝ, 0 < C ∧ ∀ (X P Q : ℕ), 2 ≤ P → P ≤ Q → Q ≤ P ^ 4 → (Q : ℝ) ^ 4 ≤ X →
      (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ) ≤
        C * X * Real.log P / Real.log Q := by
  use 4
  refine ⟨by norm_num, ?_⟩
  intro X P Q hP hPQ hQP4 _hQX
  have hP_real : 2 ≤ (P : ℝ) := by exact_mod_cast hP
  have hlogP_pos : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hQ_ge2 : 2 ≤ Q := hP.trans hPQ
  have hQ_real : 2 ≤ (Q : ℝ) := by exact_mod_cast hQ_ge2
  have hlogQ_pos : 0 < Real.log (Q : ℝ) := Real.log_pos (by linarith)
  have hcard_le : (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ) ≤ X := by
    have h_sub : (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n) ⊆ Finset.Ioc X (2 * X) :=
      Finset.filter_subset _ _
    have h1 := Finset.card_le_card h_sub
    rw [Nat.card_Ioc] at h1
    have h2 : 2 * X - X = X := by omega
    rw [h2] at h1
    exact_mod_cast h1
  have hQP4_real : (Q : ℝ) ≤ (P : ℝ) ^ 4 := by
    exact_mod_cast hQP4
  have hlogQ_le : Real.log (Q : ℝ) ≤ 4 * Real.log (P : ℝ) := by
    have hQ_pos : 0 < (Q : ℝ) := by linarith
    have hlog_le := Real.log_le_log hQ_pos hQP4_real
    have hlog_pow : Real.log ((P : ℝ) ^ 4) = 4 * Real.log (P : ℝ) := by
      rw [Real.log_pow]
      ring
    rwa [hlog_pow] at hlog_le
  have h_frac : 1 ≤ 4 * Real.log (P : ℝ) / Real.log (Q : ℝ) := by
    rw [le_div_iff₀ hlogQ_pos]
    linarith
  have hX_nonneg : 0 ≤ (X : ℝ) := by positivity
  calc (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ)
    _ ≤ (X : ℝ) := hcard_le
    _ = (X : ℝ) * 1 := by ring
    _ ≤ (X : ℝ) * (4 * Real.log (P : ℝ) / Real.log (Q : ℝ)) := mul_le_mul_of_nonneg_left h_frac hX_nonneg
    _ = 4 * (X : ℝ) * Real.log (P : ℝ) / Real.log (Q : ℝ) := by ring


/-! ### Part 4: Target Sieve Upper Bound -/

/-- Standard sieve upper bound for integers with no prime factor in $[P, Q]$.
Under the bounded ratio condition $Q \le P^4$, the count of sifted integers
in $(X, 2X]$ is bounded by $O(X \log P / \log Q)$. -/
theorem card_no_prime_factor_in_Icc_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X P Q : ℕ), 2 ≤ P → P ≤ Q → Q ≤ P ^ 4 → (Q : ℝ) ^ 4 ≤ X →
      (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ) ≤
        C * X * Real.log P / Real.log Q :=
  card_no_prime_factor_in_Icc_le_of_le_pow

end Erdos1201.MR
