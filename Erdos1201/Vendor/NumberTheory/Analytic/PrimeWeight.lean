module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Factors
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Star
public import Mathlib.Data.SetLike.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Finset.SuccPred
public import Mathlib.Order.Lattice
public import Mathlib.Order.Max
public import Mathlib.Order.Nat
public import Mathlib.Order.RelClasses
public import Mathlib.Order.SuccPred.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Erdos1201.Vendor.NumberTheory.Analytic.MeanValue

@[expose] public section
namespace Analytic

open Finset Real

/-- The completely multiplicative weight obtained by assigning a real
weight to every prime factor, counted with multiplicity. -/
noncomputable def factorWeight (w : ℕ → ℝ) :
    ArithmeticFunction ℝ where
  toFun n :=
    if n = 0 then 0 else (n.primeFactorsList.map w).prod
  map_zero' := by simp

@[simp] theorem factorWeight_zero (w : ℕ → ℝ) :
    factorWeight w 0 = 0 := by
  simp [factorWeight]

/-- For `n ≠ 0`, `factorWeight w n` unfolds to the product of `w` over the prime factors of `n`, counted with multiplicity. -/
theorem factorWeight_apply {w : ℕ → ℝ} {n : ℕ} (hn : n ≠ 0) :
    factorWeight w n = (n.primeFactorsList.map w).prod := by
  simp [factorWeight, hn]

@[simp] theorem factorWeight_one (w : ℕ → ℝ) :
    factorWeight w 1 = 1 := by
  simp [factorWeight]

/-- `factorWeight w` is multiplicative: `factorWeight w (a * b) = factorWeight w a * factorWeight w b`, for every `a, b` (including `0`). -/
theorem factorWeight_mul {w : ℕ → ℝ} (a b : ℕ) :
    factorWeight w (a * b) =
      factorWeight w a * factorWeight w b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  rw [factorWeight_apply (Nat.mul_ne_zero ha hb),
    factorWeight_apply ha, factorWeight_apply hb]
  simpa [List.map_append, List.prod_append] using
    ((Nat.perm_primeFactorsList_mul ha hb).map w).prod_eq

/-- `factorWeight w` is a multiplicative arithmetic function. -/
theorem factorWeight_isMultiplicative (w : ℕ → ℝ) :
    (factorWeight w).IsMultiplicative :=
  ⟨factorWeight_one w, fun _ ↦ factorWeight_mul _ _⟩

/-- `factorWeight w n` is nonnegative, given `w` is nonnegative on primes. -/
theorem factorWeight_nonneg {w : ℕ → ℝ}
    (hw : ∀ p, 0 ≤ w p) (n : ℕ) :
    0 ≤ factorWeight w n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [factorWeight_apply hn]
  apply List.prod_nonneg
  intro x hx
  rcases List.mem_map.mp hx with ⟨p, _hp, rfl⟩
  exact hw p

/-- Prime-factor products are monotone in their nonnegative local
weights. -/
theorem factorWeight_mono
    {w v : ℕ → ℝ} (hw0 : ∀ p, 0 ≤ w p)
    (hwv : ∀ p, w p ≤ v p) (n : ℕ) :
    factorWeight w n ≤ factorWeight v n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [factorWeight_apply hn, factorWeight_apply hn]
  exact List.prod_map_le_prod_map₀ w v (fun p _ ↦ hw0 p) (fun p _ ↦ hwv p)

/-- `factorWeight w n` is at most `1`, given `w` takes values in `[0, 1]` on primes. -/
theorem factorWeight_le_one {w : ℕ → ℝ}
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p ≤ 1)
    (n : ℕ) :
    factorWeight w n ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  simpa [factorWeight_apply hn] using factorWeight_mono (v := fun _ ↦ 1) hw0 hw1 n

/-- `factorWeight w (a * b) ≤ factorWeight w a * factorWeight w b`, the inequality form of `factorWeight_mul`. -/
theorem factorWeight_submultiplicative {w : ℕ → ℝ} (a b : ℕ) :
    factorWeight w (a * b) ≤
      factorWeight w a * factorWeight w b :=
  (factorWeight_mul a b).le

/-- `factorWeight w (p ^ k) = w p ^ k`, given `p` is prime. -/
theorem factorWeight_primePow {w : ℕ → ℝ}
    {p k : ℕ} (hp : p.Prime) :
    factorWeight w (p ^ k) = (w p) ^ k := by
  rw [factorWeight_apply (pow_ne_zero k hp.ne_zero),
    hp.primeFactorsList_pow, List.map_replicate, List.prod_replicate]

/-- `factorWeight w p = w p`, given `p` is prime. -/
theorem factorWeight_prime {w : ℕ → ℝ}
    {p : ℕ} (hp : p.Prime) :
    factorWeight w p = w p := by
  simpa using factorWeight_primePow (w := w) hp (k := 1)

/-- `harmonicArithmetic (factorWeight w) (p ^ k) = (w p / p) ^ k`, given `p` is prime. -/
theorem harmonicArithmetic_factorWeight_primePow
    {w : ℕ → ℝ} {p k : ℕ} (hp : p.Prime) :
    harmonicArithmetic (factorWeight w) (p ^ k) =
      ((w p) / p) ^ k := by
  rw [harmonicArithmetic_apply, factorWeight_primePow hp]
  push_cast
  rw [div_pow]

/-- The Euler-product form of the harmonic moment of `factorWeight w` over `Y!` equals the same product with each local factor rewritten as `(w p / p) ^ k`. -/
theorem factorWeight_eulerProduct_eq (w : ℕ → ℝ) (Y : ℕ) :
    Y.factorial.factorization.prod (fun p e ↦
      ∑ k ∈ range (e + 1),
        harmonicArithmetic (factorWeight w) (p ^ k)) =
    Y.factorial.factorization.prod (fun p e ↦
      ∑ k ∈ range (e + 1), ((w p) / p) ^ k) :=
  Finsupp.prod_congr fun p hp ↦ sum_congr rfl fun _ _ ↦
    harmonicArithmetic_factorWeight_primePow
      (Nat.prime_of_mem_primeFactors
        (by simpa [Nat.support_factorization] using hp))

/-- If every local prime weight lies in `[0,1]`, the von Mangoldt moment
has a uniform linear bound supplied by Chebyshev's theorem. -/
theorem factorWeight_vonMangoldt_le
    {w : ℕ → ℝ}
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p ≤ 1)
    (X : ℕ) :
    (∑ d ∈ Icc 1 X,
      factorWeight w d * ArithmeticFunction.vonMangoldt d)
      ≤ (log 4 + 4) * X := by
  calc
    (∑ d ∈ Icc 1 X,
        factorWeight w d * ArithmeticFunction.vonMangoldt d)
        ≤ ∑ d ∈ Icc 1 X,
            ArithmeticFunction.vonMangoldt d := by
          apply sum_le_sum
          intro d _
          simpa using mul_le_of_le_one_left
            ArithmeticFunction.vonMangoldt_nonneg
            (factorWeight_le_one hw0 hw1 d)
    _ = Chebyshev.psi X := by
      simp [Chebyshev.psi, ← Icc_succ_left_eq_Ioc]
    _ ≤ (log 4 + 4) * X :=
      Chebyshev.psi_le_const_mul_self (by positivity)

/-- A fully proved finite-Euler-product mean-value bound for any
completely multiplicative prime-factor weight with local values in
`[0,1]`.  This directly covers both residual sums in the paper. -/
theorem factorWeight_partialSum_le_eulerProduct
    {w : ℕ → ℝ}
    (hw0 : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p ≤ 1)
    {Y : ℕ} (hY : 2 ≤ Y) :
    partialSum (factorWeight w) Y ≤
      ((log 4 + 5) * Y / log Y) *
        Y.factorial.factorization.prod (fun p e ↦
          ∑ k ∈ range (e + 1), ((w p) / p) ^ k) := by
  have h := partialSum_le_eulerProduct
    (g := factorWeight w) (C := log 4 + 4)
    (factorWeight_nonneg hw0)
    (factorWeight_one w)
    (factorWeight_isMultiplicative w).2
    factorWeight_submultiplicative
    (factorWeight_vonMangoldt_le hw0 hw1)
    hY
  rw [factorWeight_eulerProduct_eq] at h
  have hc : (log 4 + 4) + 1 = log 4 + 5 := by ring
  simpa only [hc] using h

end Analytic
