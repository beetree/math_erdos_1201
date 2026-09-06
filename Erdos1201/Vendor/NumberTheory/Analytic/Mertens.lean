module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Real.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Erdos1201.Vendor.NumberTheory.MertensTheorems

@[expose] public section
namespace Analytic

open Filter Real Asymptotics
open scoped Nat



/-- The explicit error estimate behind Mertens' third theorem. -/
theorem primeProduct_error_bound {N : ℕ} (hN : 2 ≤ N) :
    |Mertens.E₃ N| ≤
      (log 4 + 3) / log N + 1 / N :=
  by
    simpa using Mertens.E₃_bound (x := (N : ℝ)) (mod_cast hN)

/-- A fixed explicit error reserve for the lower form of Mertens' third
theorem. -/
noncomputable def mertensLowerError : ℝ :=
  (log 4 + 3) / log 2 + 1 / 2

/-- A fixed positive constant in the lower Mertens product estimate. -/
noncomputable def mertensLowerConstant : ℝ :=
  exp (-eulerMascheroniConstant) * exp (-mertensLowerError)

/-- `mertensLowerConstant` is positive. -/
theorem mertensLowerConstant_pos :
    0 < mertensLowerConstant := by
  unfold mertensLowerConstant
  positivity

/-- Explicit lower bound `c / log N` for the prime product. -/
theorem mertensLowerConstant_div_log_le_primeProduct
    {N : ℕ} (hN : 2 ≤ N) :
    mertensLowerConstant / log N ≤
      ∏ p ∈ Nat.primesLE N, (1 - (1 : ℝ) / p) := by
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlogN : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hN))
  have hlogMono : log (2 : ℝ) ≤ log (N : ℝ) := by
    exact log_le_log (by norm_num) (by exact_mod_cast hN)
  have hinvLog :
      1 / log (N : ℝ) ≤ 1 / log (2 : ℝ) := by
    exact one_div_le_one_div_of_le hlog2 hlogMono
  have hinvN : 1 / (N : ℝ) ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hN)
  have herror :
      (log 4 + 3) / log (N : ℝ) + 1 / (N : ℝ) ≤
        mertensLowerError := by
    unfold mertensLowerError
    have hcoef : 0 ≤ log 4 + 3 := by positivity
    have hterm :
        (log 4 + 3) / log (N : ℝ) ≤
          (log 4 + 3) / log (2 : ℝ) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinvLog hcoef
    exact add_le_add hterm hinvN
  have hEbound := primeProduct_error_bound hN
  have hE : -mertensLowerError ≤ Mertens.E₃ N := by
    rw [abs_le] at hEbound
    linarith
  rw [Mertens.prod_prime_one_minus_inv_eq_nat (lt_of_lt_of_le (by omega : 1 < 2) hN)]
  unfold mertensLowerConstant
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (exp_le_exp.mpr hE) (exp_nonneg _))
    hlogN.le

end Analytic
