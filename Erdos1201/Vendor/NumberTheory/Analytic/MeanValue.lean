module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.Prod.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Defs
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Erdos1201.Vendor.NumberTheory.Analytic.Mertens

@[expose] public section
namespace Analytic

open Finset Real

/-- The partial sum of a nonnegative arithmetic weight.  We use `Icc 1 Y`
so that all logarithms and reciprocals below are taken at positive
integers. -/
noncomputable def partialSum (g : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 Y, g n

/-- The harmonic partial sum associated to an arithmetic weight. -/
noncomputable def harmonicSum (g : ℕ → ℝ) (Y : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 Y, g n / n

/-- The arithmetic function `n ↦ g(n) / n`, with the conventional value
zero at `n = 0`. -/
noncomputable def harmonicArithmetic (g : ℕ → ℝ) :
    ArithmeticFunction ℝ where
  toFun n := if n = 0 then 0 else g n / n
  map_zero' := by simp

/-- `harmonicArithmetic g n` unfolds to `g n / n` for every `n`, including
`n = 0` (where both sides vanish, since division by zero is zero in `ℝ`). -/
@[simp] theorem harmonicArithmetic_apply (g : ℕ → ℝ) (n : ℕ) :
    harmonicArithmetic g n = g n / n := by
  rcases eq_or_ne n 0 with hn | hn <;> simp [harmonicArithmetic, hn]

/-- `harmonicArithmetic g` is a multiplicative arithmetic function, given `g 1 = 1` and `g` multiplicative on coprime arguments. -/
theorem harmonicArithmetic_isMultiplicative
    {g : ℕ → ℝ} (hg1 : g 1 = 1)
    (hgMul : ∀ {a b : ℕ}, Nat.Coprime a b →
      g (a * b) = g a * g b) :
    (harmonicArithmetic g).IsMultiplicative := by
  refine ⟨by simp [hg1], fun {a b} hab ↦ ?_⟩
  simp only [harmonicArithmetic_apply]
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  rw [hgMul hab]
  push_cast
  field_simp

/-- Regroup a sum over positive integers and their divisor pairs by the
larger cofactor `m`, nesting the divisor `d ≤ Y / m` inside `m ≤ Y`. -/
theorem sum_divisorPairs_eq_nested
    (f : ℕ → ℕ → ℝ) (Y : ℕ) :
    (∑ n ∈ Icc 1 Y, ∑ x ∈ n.divisorsAntidiagonal, f x.1 x.2) =
      ∑ m ∈ Icc 1 Y, ∑ d ∈ Icc 1 (Y / m), f d m := by
  rw [sum_sigma', sum_sigma']
  apply Finset.sum_nbij' (fun x ↦ (⟨x.2.2, x.2.1⟩ : Σ _ : ℕ, ℕ))
    (fun y ↦ (⟨y.2 * y.1, (y.2, y.1)⟩ : Σ _ : ℕ, ℕ × ℕ))
  · intro x hx
    rw [mem_sigma] at hx ⊢
    obtain ⟨hn, hx2⟩ := hx
    have hpair := Nat.mem_divisorsAntidiagonal.mp hx2
    have hd0 : x.2.1 ≠ 0 := fun h ↦ hpair.2 (by rw [← hpair.1, h, zero_mul])
    have hm0 : x.2.2 ≠ 0 := fun h ↦ hpair.2 (by rw [← hpair.1, h, mul_zero])
    refine ⟨mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm0,
        le_trans (Nat.le_mul_of_pos_left _ (Nat.one_le_iff_ne_zero.mpr hd0))
          (hpair.1 ▸ (mem_Icc.mp hn).2)⟩,
      mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hd0,
        (Nat.le_div_iff_mul_le (Nat.one_le_iff_ne_zero.mpr hm0)).mpr
          (hpair.1 ▸ (mem_Icc.mp hn).2)⟩⟩
  · intro y hy
    rw [mem_sigma] at hy ⊢
    obtain ⟨hm, hd⟩ := hy
    have hm' := mem_Icc.mp hm
    have hd' := mem_Icc.mp hd
    have hmulne := Nat.mul_ne_zero
      (Nat.one_le_iff_ne_zero.mp hd'.1) (Nat.one_le_iff_ne_zero.mp hm'.1)
    exact ⟨mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hmulne,
        (Nat.le_div_iff_mul_le hm'.1).mp hd'.2⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hmulne⟩⟩
  · intro x hx
    rw [mem_sigma] at hx
    exact Sigma.ext (Nat.mem_divisorsAntidiagonal.mp hx.2).1 (by simp)
  · intro y _
    rfl
  · intro x _
    rfl

/-- Every positive `n ≤ Y` divides `Y!`, so its harmonic weight occurs
in the full divisor sum of `Y!`. -/
theorem harmonicSum_le_factorialDivisorSum
    {g : ℕ → ℝ} (hg : ∀ n, 0 ≤ g n) (Y : ℕ) :
    harmonicSum g Y ≤
      ∑ d ∈ Y.factorial.divisors, harmonicArithmetic g d := by
  simp only [harmonicSum, harmonicArithmetic_apply]
  exact sum_le_sum_of_subset_of_nonneg
    (fun n hn ↦ Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (mem_Icc.mp hn).1 (mem_Icc.mp hn).2,
      Nat.factorial_ne_zero Y⟩)
    (fun n _ _ ↦ div_nonneg (hg n) n.cast_nonneg)

/-- The divisor sum of a multiplicative arithmetic function over `Y!`
is a finite Euler product. -/
theorem factorialDivisorSum_eq_eulerProduct
    {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative)
    (Y : ℕ) :
    (∑ d ∈ Y.factorial.divisors, f d) =
      Y.factorial.factorization.prod fun p e ↦
        ∑ k ∈ range (e + 1), f (p ^ k) := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply,
    (hf.mul ArithmeticFunction.isMultiplicative_zeta.natCast).multiplicative_factorization
      (f * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
      (Nat.factorial_ne_zero Y)]
  apply Finsupp.prod_congr
  intro p hp
  rw [ArithmeticFunction.coe_mul_zeta_apply,
    Nat.sum_divisors_prime_pow
      (Nat.prime_of_mem_primeFactors
        (by simpa [Nat.support_factorization] using hp))]

/-- The convolution step of the completely submultiplicative
Halberstam--Richert estimate. -/
theorem logMoment_le_harmonic
    {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ n, 0 ≤ g n)
    (hgMul : ∀ a b, g (a * b) ≤ g a * g b)
    (hMangoldt :
      ∀ X : ℕ,
        (∑ d ∈ Icc 1 X,
          g d * ArithmeticFunction.vonMangoldt d) ≤ C * X)
    (Y : ℕ) :
    (∑ n ∈ Icc 1 Y, g n * log n)
      ≤ C * Y * harmonicSum g Y := by
  have hC : 0 ≤ C := by
    simpa [ArithmeticFunction.vonMangoldt_apply_one] using hMangoldt 1
  calc
    (∑ n ∈ Icc 1 Y, g n * log n)
        ≤ ∑ n ∈ Icc 1 Y,
            ∑ x ∈ n.divisorsAntidiagonal,
              g x.1 * g x.2 *
                ArithmeticFunction.vonMangoldt x.1 := by
          apply sum_le_sum
          intro n _
          rw [← ArithmeticFunction.vonMangoldt_sum, mul_sum,
            Nat.sum_divisorsAntidiagonal
              (fun d m ↦ g d * g m * ArithmeticFunction.vonMangoldt d)]
          apply sum_le_sum
          intro d hd
          gcongr
          simpa [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)] using hgMul d (n / d)
    _ = ∑ m ∈ Icc 1 Y,
          ∑ d ∈ Icc 1 (Y / m),
            g d * g m * ArithmeticFunction.vonMangoldt d :=
      sum_divisorPairs_eq_nested
        (fun d m ↦ g d * g m * ArithmeticFunction.vonMangoldt d) Y
    _ = ∑ m ∈ Icc 1 Y,
          g m * (∑ d ∈ Icc 1 (Y / m),
            g d * ArithmeticFunction.vonMangoldt d) :=
      sum_congr rfl fun m _ ↦ by
        rw [mul_sum]; exact sum_congr rfl fun d _ ↦ by ring
    _ ≤ ∑ m ∈ Icc 1 Y, C * Y * (g m / m) := by
      apply sum_le_sum
      intro m _
      calc
        g m * (∑ d ∈ Icc 1 (Y / m), g d * ArithmeticFunction.vonMangoldt d)
            ≤ g m * (C * (Y / m : ℕ)) := by
              gcongr
              · exact hg m
              · exact hMangoldt (Y / m)
        _ ≤ g m * (C * ((Y : ℝ) / m)) := by
              gcongr
              exacts [hg m, Nat.cast_div_le]
        _ = C * Y * (g m / m) := by ring
    _ = C * Y * harmonicSum g Y := by
      unfold harmonicSum
      rw [mul_sum]

/-- The elementary final step in the Halberstam--Richert argument.

Once the logarithmically weighted moment is at most
`C * Y * harmonicSum g Y`, the unweighted moment loses only one further
copy of `Y * harmonicSum g Y`.  No multiplicativity is used in this step.
-/
theorem partialSum_le_of_logMoment
    {g : ℕ → ℝ} {C : ℝ} (hg : ∀ n, 0 ≤ g n)
    {Y : ℕ} (hY : 2 ≤ Y)
    (hlog :
      (∑ n ∈ Icc 1 Y, g n * log n)
        ≤ C * Y * harmonicSum g Y) :
    partialSum g Y
      ≤ ((C + 1) * Y / log Y) * harmonicSum g Y := by
  have hlogY : 0 < log (Y : ℝ) := log_pos (by norm_num; omega)
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hY)
  have hpoint : ∀ n ∈ Icc 1 Y, g n * log Y ≤ g n * log n + g n * ((Y : ℝ) / n) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hratio : 0 < (Y : ℝ) / n := div_pos hYpos hnpos
    have hlogle : log (Y : ℝ) - log n ≤ (Y : ℝ) / n := by
      rw [← log_div hYpos.ne' hnpos.ne']
      exact (log_le_sub_one_of_pos hratio).trans (sub_le_self _ zero_le_one)
    nlinarith [mul_le_mul_of_nonneg_left hlogle (hg n)]
  have hmoment :
      partialSum g Y * log Y
        ≤ (C + 1) * (Y : ℝ) * harmonicSum g Y := by
    unfold partialSum harmonicSum
    unfold harmonicSum at hlog
    calc
      (∑ n ∈ Icc 1 Y, g n) * log Y
          = ∑ n ∈ Icc 1 Y, g n * log Y := by rw [sum_mul]
      _ ≤ ∑ n ∈ Icc 1 Y, (g n * log n + g n * ((Y : ℝ) / n)) := sum_le_sum hpoint
      _ = (∑ n ∈ Icc 1 Y, g n * log n) + Y * ∑ n ∈ Icc 1 Y, g n / n := by
          rw [sum_add_distrib, mul_sum]
          congr 1
          exact sum_congr rfl fun n _ ↦ by ring
      _ ≤ C * Y * (∑ n ∈ Icc 1 Y, g n / n) + Y * ∑ n ∈ Icc 1 Y, g n / n :=
          add_le_add hlog le_rfl
      _ = (C + 1) * Y * ∑ n ∈ Icc 1 Y, g n / n := by ring
  calc
    partialSum g Y
        ≤ ((C + 1) * Y * harmonicSum g Y) / log Y :=
      (le_div_iff₀ hlogY).2 hmoment
    _ = ((C + 1) * Y / log Y) * harmonicSum g Y := by ring

/-- Finite-Euler-product form of the completely submultiplicative
Halberstam--Richert estimate. -/
theorem partialSum_le_eulerProduct
    {g : ℕ → ℝ} {C : ℝ}
    (hg : ∀ n, 0 ≤ g n)
    (hg1 : g 1 = 1)
    (hgCoprime : ∀ {a b : ℕ}, Nat.Coprime a b →
      g (a * b) = g a * g b)
    (hgMul : ∀ a b, g (a * b) ≤ g a * g b)
    (hMangoldt :
      ∀ X : ℕ,
        (∑ d ∈ Icc 1 X,
          g d * ArithmeticFunction.vonMangoldt d) ≤ C * X)
    {Y : ℕ} (hY : 2 ≤ Y) :
    partialSum g Y ≤
      ((C + 1) * Y / log Y) *
        Y.factorial.factorization.prod (fun p e ↦
          ∑ k ∈ range (e + 1), harmonicArithmetic g (p ^ k)) := by
  have hC : 0 ≤ C := by
    simpa [ArithmeticFunction.vonMangoldt_apply_one] using hMangoldt 1
  calc
    partialSum g Y
        ≤ ((C + 1) * Y / log Y) * harmonicSum g Y :=
      partialSum_le_of_logMoment hg hY
        (logMoment_le_harmonic hg hgMul hMangoldt Y)
    _ ≤ _ := by
      gcongr
      calc
        harmonicSum g Y
            ≤ ∑ d ∈ Y.factorial.divisors, harmonicArithmetic g d :=
          harmonicSum_le_factorialDivisorSum hg Y
        _ = _ := factorialDivisorSum_eq_eulerProduct
          (harmonicArithmetic_isMultiplicative hg1 hgCoprime) Y

end Analytic
