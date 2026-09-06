import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite Inclusion–Exclusion over Prime Ranges

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes Lemma 5 of Matomäki–Radziwiłł: finite inclusion–exclusion
expressing the property that an integer $n$ has a factor in each of $J$ finite ranges $R j$
in terms of sums of indicators avoiding prime factors in subsets of ranges.
-/

open Classical

namespace Erdos1201.MR

/-- `n` has a prime factor in every one of the ranges `R j` (each `R j : Finset ℕ`). -/
def HasFactorInEach (J : ℕ) (R : Fin J → Finset ℕ) (n : ℕ) : Prop := ∀ j, ∃ p ∈ R j, p ∣ n

/-- Indicator (as a real) that `n` has no factor in ∪_{j ∈ T} R j. -/
def avoidsIndicator (J : ℕ) (R : Fin J → Finset ℕ) (T : Finset (Fin J)) (n : ℕ) : ℝ :=
  if ∀ j ∈ T, ∀ p ∈ R j, ¬ p ∣ n then 1 else 0

/-- Product of 0-1 indicators over a finite set is the indicator of the conjunction. -/
theorem prod_ite_one_zero {α R : Type*} [CommSemiring R] (s : Finset α) (P : α → Prop) :
    ∏ i ∈ s, (if P i then (1 : R) else 0) = if ∀ i ∈ s, P i then (1 : R) else 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, ih]
    by_cases hxP : P x
    · simp [hxP]
    · simp [hxP]

/-- Complement of the single-range avoidance indicator is the factor-existence indicator. -/
lemma one_sub_avoids_single (R : Finset ℕ) (n : ℕ) :
    1 - (if ∀ p ∈ R, ¬ p ∣ n then (1 : ℝ) else 0) =
      if ∃ p ∈ R, p ∣ n then (1 : ℝ) else 0 := by
  split_ifs with h1 h2 h2
  · exfalso
    rcases h2 with ⟨p, hp, hpn⟩
    exact h1 p hp hpn
  · ring
  · ring
  · exfalso
    apply h1
    intro p hp hpn
    exact h2 ⟨p, hp, hpn⟩

/-- Product $\prod_{j < J} (1 - 1_{\text{avoids } R_j}(n))$ equals the indicator that $n$
has a factor in each $R j$. -/
theorem prod_one_sub_avoids_eq_indicator (J : ℕ) (R : Fin J → Finset ℕ) (n : ℕ) :
    (∏ j : Fin J, (1 - (if ∀ p ∈ R j, ¬ p ∣ n then (1 : ℝ) else 0))) =
      if HasFactorInEach J R n then (1 : ℝ) else 0 := by
  have h1 : (∏ j : Fin J, (1 - (if ∀ p ∈ R j, ¬ p ∣ n then (1 : ℝ) else 0))) =
      ∏ j : Fin J, (if ∃ p ∈ R j, p ∣ n then (1 : ℝ) else 0) := by
    refine Finset.prod_congr rfl (fun j _ => ?_)
    exact one_sub_avoids_single (R j) n
  rw [h1]
  have h_eq : HasFactorInEach J R n = (∀ i ∈ (Finset.univ : Finset (Fin J)), ∃ p ∈ R i, p ∣ n) := by
    apply propext
    unfold HasFactorInEach
    simp
  rw [h_eq]
  have h2 := prod_ite_one_zero (R := ℝ) (Finset.univ : Finset (Fin J)) (fun j => ∃ p ∈ R j, p ∣ n)
  convert h2

/-- Product of avoidance indicators over $j \in T$ equals the avoidance indicator for $T$. -/
lemma prod_avoids_eq (J : ℕ) (R : Fin J → Finset ℕ) (T : Finset (Fin J)) (n : ℕ) :
    ∏ j ∈ T, (if ∀ p ∈ R j, ¬ p ∣ n then (1 : ℝ) else 0) = avoidsIndicator J R T n := by
  have h := prod_ite_one_zero (R := ℝ) T (fun j => ∀ p ∈ R j, ¬ p ∣ n)
  dsimp [avoidsIndicator]
  convert h

/-- Inclusion–exclusion algebraic expansion of the product
$\prod_{j < J} (1 - 1_{\text{avoids } R_j}(n))$. -/
theorem prod_one_sub_expansion (J : ℕ) (R : Fin J → Finset ℕ) (n : ℕ) :
    (∏ j : Fin J, (1 - (if ∀ p ∈ R j, ¬ p ∣ n then (1 : ℝ) else 0))) =
      ∑ T : Finset (Fin J), (-1 : ℝ) ^ T.card * avoidsIndicator J R T n := by
  have h := Finset.prod_sub (R := ℝ) (fun _ => 1) (fun j => if ∀ p ∈ R j, ¬ p ∣ n then (1 : ℝ) else 0) (Finset.univ : Finset (Fin J))
  simp only [Finset.prod_const_one, mul_one] at h
  rw [h]
  rw [← Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro T _
  rw [prod_avoids_eq]

/-- Pointwise inclusion–exclusion identity for the indicator of having a factor in each range. -/
theorem indicator_hasFactorInEach_eq (J : ℕ) (R : Fin J → Finset ℕ) (n : ℕ) :
    (if HasFactorInEach J R n then (1 : ℝ) else 0) =
      ∑ T : Finset (Fin J), (-1 : ℝ) ^ T.card * avoidsIndicator J R T n := by
  rw [← prod_one_sub_avoids_eq_indicator, prod_one_sub_expansion]

/-- Matomäki–Radziwiłł Lemma 5: finite inclusion–exclusion over prime ranges.
Sum of weights $a(n)$ over integers $n \in A$ having a factor in every range $R j$
equals the alternating sum over subsets $T \subseteq \{0, \dots, J-1\}$ of weights
of integers in $A$ avoiding all prime factors in $\bigcup_{j \in T} R j$. -/
theorem sum_indicator_hasFactorInEach_eq (J : ℕ) (R : Fin J → Finset ℕ) (A : Finset ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ A.filter (HasFactorInEach J R), a n) =
      ∑ T : Finset (Fin J), (-1 : ℝ) ^ T.card * ∑ n ∈ A, avoidsIndicator J R T n * a n := by
  rw [Finset.sum_filter]
  have h_step1 : (∑ n ∈ A, if HasFactorInEach J R n then a n else 0) =
      ∑ n ∈ A, (if HasFactorInEach J R n then (1 : ℝ) else 0) * a n := by
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring
  rw [h_step1]
  have h_step2 : (∑ n ∈ A, (if HasFactorInEach J R n then (1 : ℝ) else 0) * a n) =
      ∑ n ∈ A, (∑ T : Finset (Fin J), (-1 : ℝ) ^ T.card * avoidsIndicator J R T n) * a n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [indicator_hasFactorInEach_eq]
  rw [h_step2]
  have h_step3 : (∑ n ∈ A, (∑ T : Finset (Fin J), (-1 : ℝ) ^ T.card * avoidsIndicator J R T n) * a n) =
      ∑ n ∈ A, ∑ T : Finset (Fin J), (-1 : ℝ) ^ T.card * (avoidsIndicator J R T n * a n) := by
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro T _
    ring
  rw [h_step3]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  rw [← Finset.mul_sum]

end Erdos1201.MR
