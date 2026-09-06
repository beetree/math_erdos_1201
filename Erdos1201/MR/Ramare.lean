import Erdos1201.MR.Arithmetic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Corrected exact finite Ramaré decomposition

The original paper and proof for Erdős Problem #1201 are by Przemek Chojecki together
with ChatGPT 5.5 (`erdos1201.pdf`).

These Matomäki–Radziwiłł auxiliary lemmas formalize finite reductions
based on Section 5, equation 16 of arXiv:1501.04585v4.
These lemmas DO NOT prove `QuantitativeShortIntervalInput`.

This file implements the algebraic identity at the beginning of the corrected
proof of Lemma 12, including the prime-square correction. It does NOT prove the
mean-square estimate in Lemma 12.

The finite coefficient identities work over any characteristic-zero field.
-/

namespace Erdos1201.MR

section Field

variable {K : Type*} [Field K]

section CharZero

variable [CharZero K]

/-- Divide a coefficient equally among the selected prime divisors. If there
are no such divisors, keep it in the residual term. -/
theorem ramare_pointwise_uniform (S : Finset ℕ) (n : ℕ) (z : K) :
    z = (∑ _p ∈ divisorsIn S n, z / (omegaIn S n : K)) +
      if omegaIn S n = 0 then z else 0 := by
  classical
  by_cases hz : omegaIn S n = 0
  · have hempty : divisorsIn S n = ∅ := Finset.card_eq_zero.mp hz
    simp [hempty, hz]
  · have hcast : (omegaIn S n : K) ≠ 0 := Nat.cast_ne_zero.mpr hz
    simp only [hz, ↓reduceIte, add_zero]
    calc
      z = (omegaIn S n : K) * (z / (omegaIn S n : K)) := by
        field_simp [hcast]
      _ = ∑ _p ∈ divisorsIn S n, z / (omegaIn S n : K) := by
        simp [omegaIn, nsmul_eq_mul]

/-- Pointwise form of the corrected quotient denominator. -/
theorem ramare_pointwise (S : Finset ℕ) (n : ℕ) (z : K)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    z = (∑ p ∈ divisorsIn S n, z / (correctedCount S p (n / p) : K)) +
      if omegaIn S n = 0 then z else 0 := by
  calc
    z = (∑ _p ∈ divisorsIn S n, z / (omegaIn S n : K)) +
        if omegaIn S n = 0 then z else 0 :=
      ramare_pointwise_uniform S n z
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      rw [correctedCount_div hS (mem_divisorsIn.mp hp).1
        (mem_divisorsIn.mp hp).2]

/-- The exact partition of unity on integers having a selected prime factor. -/
theorem ramare_weights_sum (S : Finset ℕ) (n : ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p) (hn : omegaIn S n ≠ 0) :
    (∑ p ∈ divisorsIn S n, (1 : K) / (correctedCount S p (n / p) : K)) = 1 := by
  simpa [hn] using (ramare_pointwise S n (1 : K) hS).symm

/-- Sum the pointwise identity and interchange the two finite sums. -/
theorem ramare_finite_uniform (T S : Finset ℕ) (a : ℕ → K) :
    (∑ n ∈ T, a n) =
      (∑ p ∈ S, ∑ n ∈ T.filter (fun n => p ∣ n),
        a n / (omegaIn S n : K)) +
      ∑ n ∈ T.filter (fun n => omegaIn S n = 0), a n := by
  classical
  calc
    (∑ n ∈ T, a n) =
        ∑ n ∈ T, ((∑ _p ∈ divisorsIn S n, a n / (omegaIn S n : K)) +
          if omegaIn S n = 0 then a n else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact ramare_pointwise_uniform S n (a n)
    _ = (∑ n ∈ T, ∑ _p ∈ divisorsIn S n, a n / (omegaIn S n : K)) +
        ∑ n ∈ T, if omegaIn S n = 0 then a n else 0 := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      congr 1
      · simp only [divisorsIn, Finset.sum_filter]
        exact Finset.sum_comm
      · rw [Finset.sum_filter]

/-- Equation (16) before changing variables from `n` to `p*m`. -/
theorem ramare_finite (T S : Finset ℕ) (a : ℕ → K)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    (∑ n ∈ T, a n) =
      (∑ p ∈ S, ∑ n ∈ T.filter (fun n => p ∣ n),
        a n / (correctedCount S p (n / p) : K)) +
      ∑ n ∈ T.filter (fun n => omegaIn S n = 0), a n := by
  rw [ramare_finite_uniform T S a]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro n hn
  rw [correctedCount_div hS hp (Finset.mem_filter.mp hn).2]

end CharZero

end Field

/-- Cofactors associated with multiples of `p` in an arbitrary finite set `T`. -/
def cofactors (T : Finset ℕ) (p : ℕ) : Finset ℕ :=
  (T.filter (fun n => p ∣ n)).image (fun n => n / p)

/-- Division by `p` is injective on the multiples of `p`, including at zero. -/
theorem quotient_injOn_multiples (T : Finset ℕ) (p : ℕ) :
    Set.InjOn (fun n : ℕ => n / p) (T.filter (fun n => p ∣ n)) := by
  intro a ha b hb hab
  dsimp at hab
  calc
    a = p * (a / p) := (Nat.mul_div_cancel' (Finset.mem_filter.mp ha).2).symm
    _ = p * (b / p) := by rw [hab]
    _ = b := Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2

/-- Exact finite reindexing `n = p*m`; no flooring convention is needed. -/
theorem sum_cofactors {K : Type*} [AddCommMonoid K]
    (T : Finset ℕ) (p : ℕ) (F : ℕ → K) :
    (∑ m ∈ cofactors T p, F (p * m)) =
      ∑ n ∈ T.filter (fun n => p ∣ n), F n := by
  unfold cofactors
  rw [Finset.sum_image (quotient_injOn_multiples T p)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

section Field

variable {K : Type*} [Field K]

section RamareCofactors

variable [CharZero K]

/-- Corrected finite Ramaré identity in prime/cofactor coordinates. -/
theorem ramare_cofactors (T S : Finset ℕ) (a : ℕ → K)
    (hS : ∀ p ∈ S, Nat.Prime p) :
    (∑ n ∈ T, a n) =
      (∑ p ∈ S, ∑ m ∈ cofactors T p,
        a (p * m) / (correctedCount S p m : K)) +
      ∑ n ∈ T.filter (fun n => omegaIn S n = 0), a n := by
  rw [ramare_finite_uniform T S a]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  calc
    (∑ n ∈ T.filter (fun n => p ∣ n), a n / (omegaIn S n : K)) =
        ∑ m ∈ cofactors T p, a (p * m) / (omegaIn S (p * m) : K) :=
      (sum_cofactors T p (fun n => a n / (omegaIn S n : K))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [omegaIn_prime_mul hS hp]

end RamareCofactors

/-- The correction when changing both the coefficient and denominator to the
factorized main term. The two denominators genuinely differ when `p ∣ m`. -/
noncomputable def squareCorrection (S : Finset ℕ)
    (a b c w : ℕ → K) (p m : ℕ) : K :=
  if p ∣ m then
    a (p * m) * w (p * m) / (omegaIn S m : K) -
      (b m * c p) * w (p * m) / ((omegaIn S m : K) + 1)
  else 0

/-- Exact correction, with multiplicativity required only off the square terms.
No boundedness assumptions are needed for this algebraic identity. -/
theorem ramare_summand_split (S : Finset ℕ) (a b c w : ℕ → K) (p m : ℕ)
    (hfactor : ¬p ∣ m → a (p * m) = b m * c p) :
    a (p * m) * w (p * m) / (correctedCount S p m : K) =
      (b m * c p) * w (p * m) / ((omegaIn S m : K) + 1) +
      squareCorrection S a b c w p m := by
  by_cases hpm : p ∣ m
  · simp [correctedCount, squareCorrection, hpm]
  · simp [correctedCount, squareCorrection, hpm, hfactor hpm]

@[simp] theorem squareCorrection_of_not_dvd (S : Finset ℕ)
    (a b c w : ℕ → K) {p m : ℕ} (hpm : ¬p ∣ m) :
    squareCorrection S a b c w p m = 0 := by
  simp [squareCorrection, hpm]

/-- The error is supported on integers divisible by a square of a selected prime. -/
theorem squareCorrection_of_not_square_dvd (S : Finset ℕ)
    (a b c w : ℕ → K) {p m : ℕ} (hsq : ¬p ^ 2 ∣ p * m) :
    squareCorrection S a b c w p m = 0 := by
  have hpm : ¬p ∣ m := by
    intro hdiv
    obtain ⟨k, hk⟩ := hdiv
    apply hsq
    refine ⟨k, ?_⟩
    rw [hk]
    ring
  exact squareCorrection_of_not_dvd S a b c w hpm

section MainSplit

variable [CharZero K]

/-- Exact decomposition preceding the binning and mean-square estimates of
Lemma 12: factorized main sum + prime-square correction + unsifted remainder. -/
theorem ramare_with_square_correction (T S : Finset ℕ) (a b c w : ℕ → K)
    (hS : ∀ p ∈ S, Nat.Prime p)
    (hfactor : ∀ p ∈ S, ∀ m, ¬p ∣ m → a (p * m) = b m * c p) :
    (∑ n ∈ T, a n * w n) =
      (∑ p ∈ S, ∑ m ∈ cofactors T p,
        (b m * c p) * w (p * m) / ((omegaIn S m : K) + 1)) +
      (∑ p ∈ S, ∑ m ∈ cofactors T p, squareCorrection S a b c w p m) +
      ∑ n ∈ T.filter (fun n => omegaIn S n = 0), a n * w n := by
  rw [ramare_cofactors T S (fun n => a n * w n) hS]
  have hinner :
      (∑ p ∈ S, ∑ m ∈ cofactors T p,
        a (p * m) * w (p * m) / (correctedCount S p m : K)) =
      (∑ p ∈ S, ∑ m ∈ cofactors T p,
        (b m * c p) * w (p * m) / ((omegaIn S m : K) + 1)) +
      ∑ p ∈ S, ∑ m ∈ cofactors T p, squareCorrection S a b c w p m := by
    calc
      _ = ∑ p ∈ S, ∑ m ∈ cofactors T p,
          ((b m * c p) * w (p * m) / ((omegaIn S m : K) + 1) +
            squareCorrection S a b c w p m) := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro m hm
        exact ramare_summand_split S a b c w p m (hfactor p hp m)
      _ = _ := by simp only [Finset.sum_add_distrib]
  rw [hinner]

end MainSplit

/-- Concrete regression tests distinguish the corrected and published denominators. -/
example : (1 : ℚ) / (correctedCount {2} 2 2 : ℚ) = 1 := by
  have : correctedCount {2} 2 2 = 1 := by decide
  rw [this]
  norm_num

example : (1 : ℚ) / ((omegaIn {2} 2 : ℚ) + 1) = 1 / 2 := by
  have : omegaIn {2} 2 = 1 := by decide
  rw [this]
  norm_num

end Field

end Erdos1201.MR
