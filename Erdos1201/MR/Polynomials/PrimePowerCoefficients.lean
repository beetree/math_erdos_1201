import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.List.Permutation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Coefficients of Prime Dirichlet Polynomial Powers

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

These lemmas establish coefficient bounds for powers of prime Dirichlet polynomials
(the coefficient bound behind Matomäki–Radziwiłł Lemma 8).
-/

open scoped BigOperators
open Classical

namespace Erdos1201.MR

/-- Number of k-tuples of elements of `P` (a finset of naturals) with product `n`. -/
def tupleCount (P : Finset ℕ) (k n : ℕ) : ℕ :=
  ((Fintype.piFinset fun _ : Fin k => P).filter (fun v => ∏ i, v i = n)).card

/-- Products of k elements of P. -/
def tupleProducts (P : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (Fintype.piFinset fun _ : Fin k => P).image (fun v => ∏ i, v i)

/-- Product of natural casts under complex power. -/
theorem prod_natCast_cpow {α : Type*} (s : Finset α) (f : α → ℕ) (z : ℂ) :
    ∏ i ∈ s, ((f i : ℂ) ^ z) = ((∏ i ∈ s, f i : ℕ) : ℂ) ^ z := by
  induction' s using Finset.induction with a s has ih
  · simp
  · rw [Finset.prod_insert has, Finset.prod_insert has, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, ih]

/-- Expansion of the k-th power of a sum into a sum over functions from `Fin k`. -/
theorem sum_pow_piFinset {R : Type*} [CommSemiring R] (s : Finset ℕ) (f : ℕ → R) (k : ℕ) :
    (∑ p ∈ s, f p) ^ k = ∑ v ∈ Fintype.piFinset (fun _ : Fin k => s), ∏ i : Fin k, f (v i) := by
  rw [← Finset.prod_univ_sum]
  simp

/-- The k-th power of the prime polynomial is the Dirichlet polynomial with coefficients `tupleCount`. -/
theorem prime_poly_pow_eq (P : Finset ℕ) (k : ℕ) (s : ℂ) (hP : ∀ p ∈ P, 0 < p) :
    (∑ p ∈ P, (p : ℂ) ^ (-s)) ^ k = ∑ n ∈ tupleProducts P k, (tupleCount P k n : ℂ) * (n : ℂ) ^ (-s) := by
  have _ := hP
  rw [sum_pow_piFinset]
  have hprod (v : Fin k → ℕ) : ∏ i : Fin k, ((v i : ℂ) ^ (-s)) = ((∏ i : Fin k, v i : ℕ) : ℂ) ^ (-s) :=
    prod_natCast_cpow Finset.univ v (-s)
  simp_rw [hprod]
  rw [Finset.sum_comp (fun n : ℕ => ((n : ℂ) ^ (-s))) (fun (v : Fin k → ℕ) => ∏ i : Fin k, v i)]
  simp only [tupleProducts, tupleCount, nsmul_eq_mul]

/-- The sum of `tupleCount n / n` equals the k-th power of the reciprocal sum. -/
theorem sum_tupleCount_div (P : Finset ℕ) (k : ℕ) :
    ∑ n ∈ tupleProducts P k, ((tupleCount P k n : ℝ) / n) = (∑ p ∈ P, (1 : ℝ) / p) ^ k := by
  rw [sum_pow_piFinset]
  have hprod (v : Fin k → ℕ) : (∏ i : Fin k, ((1 : ℝ) / (v i : ℝ))) = (1 : ℝ) / ((∏ i : Fin k, v i : ℕ) : ℝ) := by
    simp only [one_div]
    rw [Finset.prod_inv_distrib, ← Nat.cast_prod]
  simp_rw [hprod]
  rw [Finset.sum_comp (fun n : ℕ => (1 : ℝ) / (n : ℝ)) (fun (v : Fin k → ℕ) => ∏ i : Fin k, v i)]
  simp only [tupleProducts, tupleCount, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- By unique prime factorization, any tuple of prime elements with product `n` is a permutation
of the prime factors list of `n`, so there are at most `k!` such tuples. -/
theorem tupleCount_le_factorial (P : Finset ℕ) (k n : ℕ) (hprime : ∀ p ∈ P, Nat.Prime p) :
    tupleCount P k n ≤ k.factorial := by
  let S := (Fintype.piFinset fun _ : Fin k => P).filter (fun v => ∏ i, v i = n)
  change S.card ≤ k.factorial
  by_cases hS : S.Nonempty
  · obtain ⟨v₀, hv₀⟩ := hS
    have hv₀_mem : v₀ ∈ Fintype.piFinset (fun _ : Fin k => P) := (Finset.mem_filter.mp hv₀).1
    have hv₀_prod : ∏ i, v₀ i = n := (Finset.mem_filter.mp hv₀).2
    have hv₀_primes : ∀ p ∈ List.ofFn v₀, Nat.Prime p := by
      intro p hp
      rw [List.mem_ofFn] at hp
      obtain ⟨i, rfl⟩ := hp
      have hvi : v₀ i ∈ P := Fintype.mem_piFinset.mp hv₀_mem i
      exact hprime (v₀ i) hvi
    have h_prod₀ : (List.ofFn v₀).prod = n := by rw [List.prod_ofFn, hv₀_prod]
    have h_perm₀ := Nat.primeFactorsList_unique h_prod₀ hv₀_primes
    have h_len : n.primeFactorsList.length = k := by
      rw [← h_perm₀.length_eq, List.length_ofFn]
    have h_inj : Function.Injective (List.ofFn : (Fin k → ℕ) → List ℕ) := List.ofFn_injective
    have h_card : S.card = (S.image List.ofFn).card := (Finset.card_image_of_injective S h_inj).symm
    rw [h_card]
    have h_sub : S.image List.ofFn ⊆ (n.primeFactorsList.permutations).toFinset := by
      intro l hl
      rw [Finset.mem_image] at hl
      obtain ⟨w, hw, rfl⟩ := hl
      have hw_mem : w ∈ Fintype.piFinset (fun _ : Fin k => P) := (Finset.mem_filter.mp hw).1
      have hw_prod : ∏ i, w i = n := (Finset.mem_filter.mp hw).2
      have hw_primes : ∀ p ∈ List.ofFn w, Nat.Prime p := by
        intro p hp
        rw [List.mem_ofFn] at hp
        obtain ⟨i, rfl⟩ := hp
        have hwi : w i ∈ P := Fintype.mem_piFinset.mp hw_mem i
        exact hprime (w i) hwi
      have h_prod_w : (List.ofFn w).prod = n := by rw [List.prod_ofFn, hw_prod]
      have h_perm_w := Nat.primeFactorsList_unique h_prod_w hw_primes
      rw [List.mem_toFinset, List.mem_permutations]
      exact h_perm_w
    have h_le := Finset.card_le_card h_sub
    have h_le2 := List.toFinset_card_le (n.primeFactorsList.permutations)
    have h_len_perm : (n.primeFactorsList.permutations).length = (n.primeFactorsList.length).factorial :=
      List.length_permutations n.primeFactorsList
    rw [h_len_perm, h_len] at h_le2
    exact h_le.trans h_le2
  · rw [Finset.nonempty_iff_ne_empty, not_not] at hS
    rw [hS, Finset.card_empty]
    exact Nat.zero_le _

/-- Any product of `k` elements of `P` with lower bound `P₀` is at least `P₀ ^ k`. -/
theorem le_prod_of_mem_tupleProducts (P : Finset ℕ) (k : ℕ) (P₀ : ℝ) (hP₀ : 0 ≤ P₀)
    (hlow : ∀ p ∈ P, P₀ ≤ p) (n : ℕ) (hn : n ∈ tupleProducts P k) :
    P₀ ^ k ≤ (n : ℝ) := by
  rw [tupleProducts, Finset.mem_image] at hn
  obtain ⟨v, hv, rfl⟩ := hn
  have h_prod : (∏ i : Fin k, (v i : ℝ)) = ((∏ i : Fin k, v i : ℕ) : ℝ) := by
    exact (Nat.cast_prod v (Finset.univ : Finset (Fin k))).symm
  rw [← h_prod]
  have h_le : ∏ i : Fin k, P₀ ≤ ∏ i : Fin k, (v i : ℝ) := by
    refine Finset.prod_le_prod (fun _ _ => hP₀) (fun i _ => ?_)
    have hvi : v i ∈ P := Fintype.mem_piFinset.mp hv i
    exact hlow (v i) hvi
  have h_const : (∏ _i : Fin k, P₀) = P₀ ^ k := by simp
  rwa [← h_const]

/-- Single-term inequality bounding `(C / n)^2` by `(B / D) * (C / n)`. -/
lemma sq_div_le_div_mul_div (C n B D : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hCn_le : C ≤ B) (hD_pos : 0 < D) (hn_le : D ≤ n) :
    (C / n) ^ 2 ≤ B / D * (C / n) := by
  have hn_pos : 0 < n := hD_pos.trans_le hn_le
  rw [sq]
  have h_div_le : C / n ≤ B / D := div_le_div₀ hB hCn_le hD_pos hn_le
  have h_cn_nonneg : 0 ≤ C / n := div_nonneg hC hn_pos.le
  exact mul_le_mul_of_nonneg_right h_div_le h_cn_nonneg

/-- Mean-square coefficient bound: if all elements of `P` exceed `P₀` and are prime, then
∑ (tupleCount n / n)² ≤ k! · (∑ 1/p)^k / P₀^k. -/
theorem sum_sq_tupleCount_div_le (P : Finset ℕ) (k : ℕ) (P₀ : ℝ) (hP₀ : 0 < P₀)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hlow : ∀ p ∈ P, P₀ ≤ p) :
    ∑ n ∈ tupleProducts P k, ((tupleCount P k n : ℝ) / n) ^ 2 ≤
      (k.factorial : ℝ) / P₀ ^ k * (∑ p ∈ P, (1 : ℝ) / p) ^ k := by
  have hP0_pow_pos : 0 < P₀ ^ k := pow_pos hP₀ k
  have h_term (n : ℕ) (hn : n ∈ tupleProducts P k) :
      ((tupleCount P k n : ℝ) / n) ^ 2 ≤ (k.factorial : ℝ) / P₀ ^ k * ((tupleCount P k n : ℝ) / n) := by
    apply sq_div_le_div_mul_div
    · exact Nat.cast_nonneg _
    · exact Nat.cast_nonneg _
    · exact Nat.cast_le.mpr (tupleCount_le_factorial P k n hprime)
    · exact hP0_pow_pos
    · exact le_prod_of_mem_tupleProducts P k P₀ hP₀.le hlow n hn
  have h_sum := Finset.sum_le_sum h_term
  refine h_sum.trans ?_
  rw [← Finset.mul_sum]
  rw [sum_tupleCount_div]

end Erdos1201.MR
