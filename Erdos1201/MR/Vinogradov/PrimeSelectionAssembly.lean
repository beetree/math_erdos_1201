/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

Attribution: the original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
-/
import Mathlib
import Erdos1201.MR.Vinogradov.PrimeSelection
import Erdos1201.MR.Vinogradov.PrimeSelectionFinal3
import Erdos1201.MR.Vinogradov.PrimesInRange

/-!
# Vinogradov Prime Selection Assembly

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

This module combines the pigeonhole reduction of Tao's Lemma 14
(`exists_prime_J_le_of_primes` from `Erdos1201.MR.Vinogradov.PrimeSelectionFinal3`)
with the analytic existence of primes in the dyadic range
(`exists_primes_finset_in_range` from `Erdos1201.MR.Vinogradov.PrimesInRange`).
By shrinking the finset of primes to size `k^3 + 1`, we obtain the explicit bound
`J k ℓ M ≤ (k^3 + 1) ℓ^(2k) J^{(p)} + 2 k^ℓ ℓ^k M^(ℓ+k-1)`.
-/

namespace Erdos1201.MR.Vinogradov

/-- Tao's Lemma 14 (Vinogradov prime selection): for `M ≥ exp(100 k^3)` and `k ≤ ℓ`,
there exists a prime `p` in `(k M^(1/k), 4 k M^(1/k)]` such that
`J k ℓ M ≤ (k^3 + 1) ℓ^(2k) J^{(p)} + 2 k^ℓ ℓ^k M^(ℓ+k-1)`. -/
theorem exists_prime_J_le (k ℓ M : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ) (hM : Real.exp (100 * (k : ℝ) ^ 3) ≤ M) :
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < p ∧ (p : ℝ) ≤ 4 * k * (M : ℝ) ^ (1 / (k : ℝ)) ∧
      (J k ℓ M : ℝ) ≤ ((k : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * k) * Jp k ℓ M p hkl + 2 * (k : ℝ) ^ ℓ * (ℓ : ℝ) ^ k * M ^ (ℓ + k - 1) := by
  obtain ⟨P, hP_card, hP_all⟩ := exists_primes_finset_in_range k M hk hM
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
  have h1M : 1 < M := one_lt_M_of_hM hk hM
  obtain ⟨p, hpP₀, hJ_le⟩ := exists_prime_J_le_of_primes k ℓ M hk hkl h1M P₀ hP₀_card_real hP₀_prime hP₀_range
  have hpP := hP₀_sub hpP₀
  refine ⟨p, (hP_all p hpP).1, (hP_all p hpP).2.1, (hP_all p hpP).2.2, ?_⟩
  rw [hP₀_card] at hJ_le
  push_cast at hJ_le
  exact hJ_le

end Erdos1201.MR.Vinogradov
