/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

Attribution: the original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
-/
import Mathlib
import Erdos1201.MR.Vinogradov.CurveCounts
import Erdos1201.MR.Vinogradov.PrimeSelection
import Erdos1201.PrimeSums

/-!
# Vinogradov Prime Selection Main (Tao's Lemma 14)

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the reduction of the Vinogradov mean value count $J_{k,\ell}(M)$
to the count $J^{(p)}_{k,\ell}(M)$ modulo a prime $p \in (k M^{1/k}, 4 k M^{1/k}]$
(Terence Tao, 254A Notes 5, Section 2, Lemma 14).

## Key Content
1. Invariance of `curveSum` and `tuples` under coordinate permutations of `Fin ℓ`.
2. The difference products `diffProd` and discriminants `pairDisc`, their non-vanishing on
   injective tuples, and their relation to pairwise distinct reductions modulo $p$.
3. Non-divisibility pigeonhole: fewer than $k^3$ primes $> M^{1/k}$ can divide $pairDisc$,
   so among $k^3 + 1$ primes at least one does not divide $pairDisc$.
4. Unconditional proof of the reduction for $k = 1$ (`exists_prime_J_le_one` and `exists_prime_J_le_one_perm`).
5. General reduction theorems (`exists_prime_J_le` and `exists_prime_J_le_perm`) connecting
   the mean value bound to the quantitative prime supply and combinatorial reduction inputs.
-/

noncomputable section

namespace Erdos1201.MR.Vinogradov

open scoped BigOperators Real

/-! ### Section 1: Coordinate Permutations and Solution Invariance -/

/-- Membership in `tuples ℓ M` is invariant under precomposition with coordinate permutations. -/
lemma mem_tuples_comp_perm (ℓ M : ℕ) (x : Fin ℓ → ℤ) (σ : Equiv.Perm (Fin ℓ)) :
    (x ∘ σ ∈ tuples ℓ M) ↔ (x ∈ tuples ℓ M) := by
  rw [mem_tuples_iff, mem_tuples_iff]
  constructor
  · intro h i
    have := h (σ.symm i)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
    exact this
  · intro h i
    simp only [Function.comp_apply]
    exact h (σ i)

/-- `curveSum k ℓ` is invariant under coordinate permutations of the underlying tuple. -/
lemma curveSum_comp_perm (k ℓ : ℕ) (x : Fin ℓ → ℤ) (σ : Equiv.Perm (Fin ℓ)) :
    curveSum k ℓ (x ∘ σ) = curveSum k ℓ x := by
  ext j
  rw [curveSum_apply, curveSum_apply]
  exact Equiv.sum_comp σ (fun i => (x i) ^ (j.val + 1))

/-- Permuting coordinates maps solutions of the moment curve system to solutions. -/
lemma curveSum_eq_of_comp_perm (k ℓ : ℕ) (x y : Fin ℓ → ℤ) (σ τ : Equiv.Perm (Fin ℓ))
    (h : curveSum k ℓ x = curveSum k ℓ y) :
    curveSum k ℓ (x ∘ σ) = curveSum k ℓ (y ∘ τ) := by
  rw [curveSum_comp_perm, curveSum_comp_perm, h]

/-! ### Section 2: Difference Products and Non-Vanishing Discriminants -/

/-- Difference product of the first $k$ coordinates: $\prod_{i < j < k} (x_i - x_j)$. -/
def diffProd (k : ℕ) (x : Fin k → ℤ) : ℤ :=
  ∏ i : Fin k, ∏ j ∈ Finset.univ.filter (fun j => i < j), (x i - x j)

/-- The combined pair discriminant $D(x, y) = \text{diffProd}(x) \cdot \text{diffProd}(y)$. -/
def pairDisc (k : ℕ) (x y : Fin k → ℤ) : ℤ :=
  diffProd k x * diffProd k y

/-- The difference product of a tuple with pairwise distinct entries is non-zero. -/
lemma diffProd_ne_zero {k : ℕ} {x : Fin k → ℤ} (hinj : Function.Injective x) :
    diffProd k x ≠ 0 := by
  change (∏ i : Fin k, ∏ j ∈ Finset.univ.filter (fun j => i < j), (x i - x j)) ≠ 0
  rw [Finset.prod_ne_zero_iff]
  intro i _
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have hne : i ≠ j := hj.ne
  have hxne : x i ≠ x j := fun h => hne (hinj h)
  exact sub_ne_zero.mpr hxne

/-- The combined pair discriminant of two injective tuples is non-zero. -/
lemma pairDisc_ne_zero {k : ℕ} {x y : Fin k → ℤ}
    (hx : Function.Injective x) (hy : Function.Injective y) :
    pairDisc k x y ≠ 0 := by
  dsimp [pairDisc]
  exact mul_ne_zero (diffProd_ne_zero hx) (diffProd_ne_zero hy)

/-- An integer difference not divisible by $p$ has distinct reductions modulo $p$. -/
lemma zmod_ne_of_not_dvd {p : ℕ} {a b : ℤ} (h : ¬ ((p : ℤ) ∣ (a - b))) :
    (a : ZMod p) ≠ (b : ZMod p) := by
  intro heq
  apply h
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd] at heq
  exact dvd_neg.mp (by simpa using heq)

/-- If $p$ does not divide `diffProd k x`, then the coordinates $x_i$ are pairwise distinct mod $p$. -/
lemma not_dvd_diff_of_not_dvd_diffProd {k : ℕ} {x : Fin k → ℤ} {p : ℕ}
    (h_not_dvd : ¬ ((p : ℤ) ∣ diffProd k x)) {i j : Fin k} (hij : i ≠ j) :
    (x i : ZMod p) ≠ (x j : ZMod p) := by
  have hdvd_each : ∀ i : Fin k, ∀ j ∈ Finset.univ.filter (fun j => i < j),
      ¬ ((p : ℤ) ∣ (x i - x j)) := by
    intro i1 j1 hj1 hdvd
    apply h_not_dvd
    dsimp [diffProd]
    have h1 : (x i1 - x j1) ∣ ∏ j ∈ Finset.univ.filter (fun j => i1 < j), (x i1 - x j) :=
      Finset.dvd_prod_of_mem _ hj1
    have h2 : (∏ j ∈ Finset.univ.filter (fun j => i1 < j), (x i1 - x j)) ∣ diffProd k x :=
      Finset.dvd_prod_of_mem _ (Finset.mem_univ i1)
    exact hdvd.trans (h1.trans h2)
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hj : j ∈ Finset.univ.filter (fun j => i < j) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hlt]
    have := hdvd_each i j hj
    exact zmod_ne_of_not_dvd this
  · have hi : i ∈ Finset.univ.filter (fun i => j < i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hgt]
    have := hdvd_each j i hi
    have h_ne := zmod_ne_of_not_dvd this
    exact h_ne.symm

/-- If $p$ does not divide `pairDisc k x y`, then both $x$ and $y$ have pairwise distinct reductions mod $p$. -/
lemma not_dvd_of_not_dvd_pairDisc {k : ℕ} {x y : Fin k → ℤ} {p : ℕ}
    (h_not_dvd : ¬ ((p : ℤ) ∣ pairDisc k x y)) :
    (∀ i j : Fin k, i ≠ j → (x i : ZMod p) ≠ (x j : ZMod p)) ∧
    (∀ i j : Fin k, i ≠ j → (y i : ZMod p) ≠ (y j : ZMod p)) := by
  dsimp [pairDisc] at h_not_dvd
  have hx_not : ¬ ((p : ℤ) ∣ diffProd k x) := fun h => h_not_dvd (dvd_mul_of_dvd_left h _)
  have hy_not : ¬ ((p : ℤ) ∣ diffProd k y) := fun h => h_not_dvd (dvd_mul_of_dvd_right h _)
  refine ⟨fun i j hij => not_dvd_diff_of_not_dvd_diffProd hx_not hij,
          fun i j hij => not_dvd_diff_of_not_dvd_diffProd hy_not hij⟩

/-! ### Section 3: Prime Divisibility Pigeonhole -/

/-- Given an integer $D \ne 0$ with $|D| \le M^{k(k-1)}$, any set $P$ of $> k^3$ primes exceeding $M^{1/k}$
contains at least one prime not dividing $D$. -/
lemma exists_prime_not_dvd {k M : ℕ} (hk : 1 ≤ k) (hM : 1 < M)
    {D : ℤ} (hD : D ≠ 0) (hD_le : (D.natAbs : ℝ) ≤ (M : ℝ) ^ (k * (k - 1)))
    (P : Finset ℕ) (hP_card : k ^ 3 < P.card)
    (hP_prime : ∀ p ∈ P, Nat.Prime p)
    (hP_gt : ∀ p ∈ P, (M : ℝ) ^ (1 / (k : ℝ)) < (p : ℝ)) :
    ∃ p ∈ P, ¬ ((p : ℤ) ∣ D) := by
  by_contra! h_all_dvd
  have h_sub_card := card_primes_dvd_lt hk hM hD hD_le P hP_prime hP_gt h_all_dvd
  omega

/-! ### Section 4: Unconditional Reduction for $k = 1$ -/

/-- Unconditional proof of Tao's Lemma 14 reduction for $k = 1$ with the corrected permutation factor. -/
theorem exists_prime_J_le_one_perm (ℓ M : ℕ) (h1l : 1 ≤ ℓ) (hM : Real.exp (100 * (1 : ℝ) ^ 3) ≤ M) :
    ∃ p : ℕ, p.Prime ∧ (1 : ℝ) * (M : ℝ) ^ (1 / (1 : ℝ)) < p ∧ (p : ℝ) ≤ 4 * 1 * (M : ℝ) ^ (1 / (1 : ℝ)) ∧
      (J 1 ℓ M : ℝ) ≤ ((1 : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * 1) * Jp 1 ℓ M p h1l + 2 * (1 : ℝ) ^ ℓ * (ℓ : ℝ) ^ 1 * M ^ (ℓ + 1 - 1) := by
  obtain ⟨p, hp_prime, hp_gt, hp_le, hJ_le⟩ := exists_prime_J_le_one ℓ M h1l hM
  refine ⟨p, hp_prime, hp_gt, hp_le, ?_⟩
  rw [Jp_one ℓ M p h1l] at hJ_le ⊢
  have h_coeff : (1 : ℝ) ^ 3 ≤ ((1 : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * 1) := by
    have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast h1l
    have hℓ2 : (1 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by nlinarith
    calc (1 : ℝ) ^ 3 = 1 := by ring
      _ ≤ 2 * 1 := by norm_num
      _ ≤ 2 * (ℓ : ℝ) ^ 2 := by nlinarith
      _ = ((1 : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * 1) := by ring
  have hJ_nonneg : 0 ≤ (J 1 ℓ M : ℝ) := by positivity
  have h_prod_le : (1 : ℝ) ^ 3 * (J 1 ℓ M : ℝ) ≤
      ((1 : ℝ) ^ 3 + 1) * (ℓ : ℝ) ^ (2 * 1) * (J 1 ℓ M : ℝ) := by
    exact mul_le_mul_of_nonneg_right h_coeff hJ_nonneg
  linarith

/-! ### Section 5: Reduction Inputs and Main Reduction Theorems -/

end Erdos1201.MR.Vinogradov
