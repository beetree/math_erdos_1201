module

public import Erdos1201.Vendor.NumberTheory.FriableIntegers.DickmanBasic
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.PrimeSums
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.StructuredCells
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.Scale
public import Erdos1201.Vendor.NumberTheory.PNT.MediumPNT
public import Mathlib.NumberTheory.Harmonic.Bounds


@[expose] public section

/-!
# Friable counts on the main friable-integer estimate scale — part 1

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's concrete finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.

Quantitative prime-number input, Dickman kernel regularity, the Dickman test weight in the prime recurrence, and explicit oscillation / Riemann error.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace FriableIntegers.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale PrimeSums

/-! ## Quantitative prime-number input

The finite de Bruijn induction below needs a power-saving prime Stieltjes
estimate.  We derive it here from the audited medium-strength PNT, rather than
postulating a prime-distribution contract.  The exponential PNT remainder is
stronger than every fixed power of `1 / log x`.
-/

/-- The medium PNT error for `ψ` is `O(x / log(x)^A)` for every fixed real
power `A`. -/
theorem psi_error_isBigO_log_power (A : ℝ) :
    (Chebyshev.psi - id) =O[atTop]
      (fun x : ℝ => x / (Real.log x) ^ A) := by
  obtain ⟨c, hc, hPNT⟩ := MediumPNT
  apply hPNT.trans
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10))
      atTop atTop := by
    exact tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10) |>.comp
      Real.tendsto_log_atTop
  have hdecay :=
    (isLittleO_exp_neg_mul_rpow_atTop hc (-10 * A)).comp_tendsto hpow
  have hdecay' :
      (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
        =O[atTop] (fun x : ℝ => (Real.log x) ^ (-A)) := by
    apply hdecay.isBigO.congr' (Eventually.of_forall fun x => rfl)
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (0 : ℝ))]
      with x hx
    simp only [Function.comp_apply]
    rw [← Real.rpow_mul hx]
    congr 2
    ring
  have hmul := (isBigO_refl (fun x : ℝ => x) atTop).mul hdecay'
  apply hmul.congr' (Eventually.of_forall fun x => rfl)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))]
    with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv]

/-- The prime-power correction `√x log x` is smaller than the same arbitrary
fixed logarithmic PNT scale. -/
theorem sqrt_mul_log_isBigO_log_power (A : ℝ) :
    (fun x : ℝ => Real.sqrt x * Real.log x) =O[atTop]
      (fun x : ℝ => x / (Real.log x) ^ A) := by
  have hlog :=
    (isLittleO_log_rpow_rpow_atTop (A + 1) (by norm_num : (0 : ℝ) < 1 / 2)).isBigO
  let common : ℝ → ℝ := fun x => x ^ ((1 : ℝ) / 2) / (Real.log x) ^ A
  have hmul := hlog.mul (isBigO_refl common atTop)
  apply hmul.congr'
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with x hlogx hx
    dsimp [common]
    rw [Real.sqrt_eq_rpow, Real.rpow_add hlogx]
    field_simp
    simp [Real.rpow_one]
  · filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
      eventually_gt_atTop (0 : ℝ)] with x hlogx hx
    dsimp [common]
    calc
      x ^ ((1 : ℝ) / 2) * (x ^ ((1 : ℝ) / 2) / Real.log x ^ A) =
          (x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) / Real.log x ^ A := by ring
      _ = x ^ ((1 : ℝ) / 2 + (1 : ℝ) / 2) / Real.log x ^ A := by
        rw [Real.rpow_add hx]
      _ = x / Real.log x ^ A := by norm_num [Real.rpow_one]

/-- Quantitative PNT for Chebyshev's `θ`, at every fixed logarithmic power.
This is the form used by partial summation over primes. -/
theorem theta_error_isBigO_log_power (A : ℝ) :
    (Chebyshev.theta - id) =O[atTop]
      (fun x : ℝ => x / (Real.log x) ^ A) := by
  have hraw := theta_sub_psi_isBigO_sqrt_mul_log
  have hdiff := hraw.trans (sqrt_mul_log_isBigO_log_power A)
  have hadd := hdiff.add (psi_error_isBigO_log_power A)
  apply hadd.congr' (Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => rfl)
  simp only [Pi.sub_apply, id_eq]
  ring

/-- The concrete finite Chebyshev prime sum, written with the same
`Nat.primesBelow` finset used by the friable recurrence. -/
noncomputable def primeLogSumUpTo (X : ℕ) : ℝ :=
  ∑ p ∈ (X + 1).primesBelow, Real.log (p : ℝ)

theorem primeLogSumUpTo_eq_theta (X : ℕ) :
    primeLogSumUpTo X = Chebyshev.theta (X : ℝ) := by
  have hfin : (X + 1).primesBelow = (Finset.Ioc 0 X).filter Nat.Prime := by
    ext p
    simp only [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨hpX, hp⟩
      exact ⟨⟨hp.pos, by omega⟩, hp⟩
    · rintro ⟨⟨_, hpX⟩, hp⟩
      exact ⟨by omega, hp⟩
  rw [primeLogSumUpTo, hfin, Chebyshev.theta]
  simp only [Nat.floor_natCast]

/-- Quantitative PNT for the precise natural-number prime finset used below.
-/
theorem primeLogSumUpTo_error_isBigO_log_power (A : ℝ) :
    (fun X : ℕ => primeLogSumUpTo X - (X : ℝ)) =O[atTop]
      (fun X : ℕ => (X : ℝ) / (Real.log (X : ℝ)) ^ A) := by
  have h := (theta_error_isBigO_log_power A).comp_tendsto
    tendsto_natCast_atTop_atTop
  apply h.congr' (Eventually.of_forall fun X => ?_)
    (Eventually.of_forall fun X => rfl)
  simp only [Function.comp_apply, Pi.sub_apply, id_eq, primeLogSumUpTo_eq_theta]

/-- An explicit eventual inequality extracted from the quantitative PNT.  In
particular, later uses may choose the constant and threshold before starting
the finite de Bruijn induction. -/
theorem exists_primeLogSumUpTo_error_bound (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / (Real.log (X : ℝ)) ^ A) := by
  obtain ⟨C, hC, hbound⟩ :=
    (primeLogSumUpTo_error_isBigO_log_power A).exists_pos
  rw [IsBigOWith, eventually_atTop] at hbound
  obtain ⟨X₀, hX₀⟩ := hbound
  refine ⟨C, hC, max X₀ 2, fun X hX => ?_⟩
  have hXX₀ : X₀ ≤ X := (le_max_left X₀ 2).trans hX
  have hX2 : 2 ≤ X := (le_max_right X₀ 2).trans hX
  have htarget : 0 ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ A := by
    positivity
  simpa only [Real.norm_eq_abs, Real.norm_of_nonneg htarget] using
    hX₀ X hXX₀

/-- The logarithmically weighted prime sum on the half-open natural interval
`z < p ≤ y`. -/
noncomputable def primeLogSumInterval (z y : ℕ) : ℝ :=
  ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
    Real.log (p : ℝ)

theorem primeLogSumInterval_eq_sub {z y : ℕ} (hzy : z ≤ y) :
    primeLogSumInterval z y = primeLogSumUpTo y - primeLogSumUpTo z := by
  have hsubset : (z + 1).primesBelow ⊆ (y + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum := Finset.sum_sdiff
    (f := fun p : ℕ => Real.log (p : ℝ)) hsubset
  simp only [primeLogSumInterval, primeLogSumUpTo] at hsum ⊢
  linarith

/-- Uniform two-endpoint form of the quantitative PNT.  This is the exact
finite interval estimate used on each cell of a prime Stieltjes partition. -/
theorem primeLogSumInterval_error_bound {A C : ℝ} {X₀ z y : ℕ}
    (hbound : ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / (Real.log (X : ℝ)) ^ A))
    (hz : X₀ ≤ z) (hy : X₀ ≤ y) (hzy : z ≤ y) :
    |primeLogSumInterval z y - ((y : ℝ) - (z : ℝ))| ≤
      C * ((y : ℝ) / (Real.log (y : ℝ)) ^ A +
        (z : ℝ) / (Real.log (z : ℝ)) ^ A) := by
  rw [primeLogSumInterval_eq_sub hzy]
  calc
    |(primeLogSumUpTo y - primeLogSumUpTo z) - ((y : ℝ) - (z : ℝ))| =
        |(primeLogSumUpTo y - (y : ℝ)) -
          (primeLogSumUpTo z - (z : ℝ))| := by ring_nf
    _ ≤ |primeLogSumUpTo y - (y : ℝ)| +
        |primeLogSumUpTo z - (z : ℝ)| := abs_sub _ _
    _ ≤ C * ((y : ℝ) / (Real.log (y : ℝ)) ^ A) +
        C * ((z : ℝ) / (Real.log (z : ℝ)) ^ A) :=
      add_le_add (hbound y hy) (hbound z hz)
    _ = _ := by ring

/-- The point mass of the Chebyshev `θ` measure at an integer. -/
noncomputable def primeLogIncrement (m : ℕ) : ℝ :=
  primeLogCoeff m

theorem sum_range_primeLogIncrement (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), primeLogIncrement m =
      primeLogSumUpTo n := by
  rw [primeLogSumUpTo]
  simp only [primeLogIncrement, primeLogCoeff]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_primesBelow]
  · intro p hp
    rfl

/-- A prime Stieltjes sum, still written as a finite sum. -/
noncomputable def primeThetaWeightedInterval (f : ℕ → ℝ) (z y : ℕ) : ℝ :=
  ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
    f p * Real.log (p : ℝ)

theorem primeThetaWeightedInterval_eq_Ioc (f : ℕ → ℝ) {z y : ℕ} :
    primeThetaWeightedInterval f z y =
      ∑ m ∈ Finset.Ioc z y, f m * primeLogIncrement m := by
  rw [primeThetaWeightedInterval]
  simp only [primeLogIncrement, primeLogCoeff, mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesBelow,
      Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨hpy, hp⟩, hpz⟩
      refine ⟨⟨?_, by omega⟩, hp⟩
      by_contra hnot
      apply hpz
      exact ⟨by omega, hp⟩
    · rintro ⟨⟨hzp, hpy⟩, hp⟩
      exact ⟨⟨by omega, hp⟩, by omega⟩
  · intro p hp
    rfl

/-- Exact Abel summation for a prime Stieltjes sum.  No asymptotic statement
is hidden here: the cumulative mass is the concrete finite `primeLogSumUpTo`.
This is the arithmetic identity to which the quantitative PNT error is
applied. -/
theorem primeThetaWeightedInterval_by_parts (f : ℕ → ℝ) {z y : ℕ}
    (hzy : z < y) :
    primeThetaWeightedInterval f z y =
      f y * primeLogSumUpTo y - f (z + 1) * primeLogSumUpTo z -
        ∑ m ∈ Finset.Ioc z (y - 1),
          (f (m + 1) - f m) * primeLogSumUpTo m := by
  rw [primeThetaWeightedInterval_eq_Ioc f]
  have hparts := Finset.sum_Ioc_by_parts f primeLogIncrement hzy
  simpa only [smul_eq_mul, sum_range_primeLogIncrement,
    Nat.add_sub_cancel] using hparts

/-- Abel's main term after replacing the cumulative prime mass `θ(m)` by its
PNT main term `m`.  This is deliberately kept discrete; the subsequent
comparison with a Dickman integral is a separate Riemann-sum step. -/
noncomputable def integerAbelMain (f : ℕ → ℝ) (z y : ℕ) : ℝ :=
  f y * (y : ℝ) - f (z + 1) * (z : ℝ) -
    ∑ m ∈ Finset.Ioc z (y - 1),
      (f (m + 1) - f m) * (m : ℝ)

/-- Unit mass on the positive integers.  Its cumulative mass through `n` is
exactly `n`, matching the main term of `θ(n)`. -/
def positiveIncrement (m : ℕ) : ℝ := if m = 0 then 0 else 1

theorem sum_range_positiveIncrement (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), positiveIncrement m = (n : ℝ) := by
  induction n with
  | zero => simp [positiveIncrement]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp [positiveIncrement]

/-- Consequently the discrete Abel main term is just the ordinary integer
Riemann sum of the test weight. -/
theorem integerAbelMain_eq_sum_Ioc (f : ℕ → ℝ) {z y : ℕ}
    (hzy : z < y) :
    integerAbelMain f z y = ∑ m ∈ Finset.Ioc z y, f m := by
  have hparts := Finset.sum_Ioc_by_parts f positiveIncrement hzy
  have hlhs : (∑ m ∈ Finset.Ioc z y, f m * positiveIncrement m) =
      ∑ m ∈ Finset.Ioc z y, f m := by
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 : m ≠ 0 := by
      rw [Finset.mem_Ioc] at hm
      omega
    simp [positiveIncrement, hm0]
  simp only [smul_eq_mul] at hparts
  rw [hlhs] at hparts
  simpa only [sum_range_positiveIncrement,
    Nat.add_sub_cancel, integerAbelMain, mul_one] using hparts.symm

/-- Shift a sum over `z < m ≤ y` to the adjacent unit cells
`z ≤ k < y`. -/
theorem sum_Ioc_shift (f : ℕ → ℝ) {z y : ℕ} :
    ∑ m ∈ Finset.Ioc z y, f m =
      ∑ k ∈ Finset.Ico z y, f (k + 1) := by
  have hfin : (Finset.Ico z y).image (fun k => k + 1) =
      Finset.Ioc z y := by
    ext m
    simp only [Finset.mem_image, Finset.mem_Ico, Finset.mem_Ioc]
    constructor
    · rintro ⟨k, ⟨hzk, hky⟩, rfl⟩
      omega
    · rintro ⟨hzm, hmy⟩
      refine ⟨m - 1, ?_, by omega⟩
      omega
  have hinj : Set.InjOn (fun k : ℕ => k + 1)
      (Finset.Ico z y : Set ℕ) := by
    intro a ha b hb hab
    exact Nat.add_right_cancel hab
  rw [← hfin, Finset.sum_image hinj]

/-- Exact decomposition of an integer Riemann-sum error into its unit-cell
errors. -/
theorem sum_sub_integral_identity (f : ℝ → ℝ) {z y : ℕ}
    (hzy : z ≤ y)
    (hint : ∀ k ∈ Set.Ico z y,
      IntervalIntegrable f MeasureTheory.volume (k : ℝ) (k + 1 : ℕ)) :
    (∑ m ∈ Finset.Ioc z y, f m) -
        ∫ t in (z : ℝ)..(y : ℝ), f t =
      ∑ k ∈ Finset.Ico z y,
        (f (k + 1) - ∫ t in (k : ℝ)..(k + 1 : ℕ), f t) := by
  rw [sum_Ioc_shift (fun m => f m)]
  have hintsum := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (f := f) (μ := MeasureTheory.volume)
    (a := fun k : ℕ => (k : ℝ)) hzy hint
  simp only [Nat.cast_add, Nat.cast_one] at hintsum
  simp only [Nat.cast_add, Nat.cast_one]
  rw [← hintsum, Finset.sum_sub_distrib]

/-- A quantitative Riemann-sum estimate from a supplied oscillation on each
unit cell.  Later the one-Lipschitz Dickman bound supplies `hosc` for the
specific de Bruijn kernel. -/
theorem sum_integral_error_bound (f : ℝ → ℝ) (e : ℕ → ℝ)
    {z y : ℕ} (hzy : z ≤ y)
    (hint : ∀ k ∈ Set.Ico z y,
      IntervalIntegrable f MeasureTheory.volume (k : ℝ) (k + 1 : ℕ))
    (hosc : ∀ k ∈ Finset.Ico z y,
      ∀ t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ),
        |f (k + 1) - f t| ≤ e k) :
    |(∑ m ∈ Finset.Ioc z y, f m) -
        ∫ t in (z : ℝ)..(y : ℝ), f t| ≤
      ∑ k ∈ Finset.Ico z y, e k := by
  rw [sum_sub_integral_identity f hzy hint]
  calc
    |∑ k ∈ Finset.Ico z y,
        (f (k + 1) - ∫ t in (k : ℝ)..(k + 1 : ℕ), f t)| ≤
        ∑ k ∈ Finset.Ico z y,
          |f (k + 1) - ∫ t in (k : ℝ)..(k + 1 : ℕ), f t| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico z y, e k := by
      apply Finset.sum_le_sum
      intro k hk
      have hconst :
          (∫ _t in (k : ℝ)..(k + 1 : ℕ), f (k + 1)) =
            f (k + 1) := by
        simp
      rw [← hconst, ← intervalIntegral.integral_sub
        (continuous_const.intervalIntegrable _ _)
        (hint k (by simpa using hk))]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t => f (k + 1) - f t) (C := e k)
        (a := (k : ℝ)) (b := (k + 1 : ℕ)) (fun t ht => ?_)
      · simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one,
          add_sub_cancel_left, abs_one, mul_one] using hnorm
      · apply hosc k hk t
        have ht' := Set.uIoc_subset_uIcc ht
        rw [Set.uIcc_of_le
          (by norm_num : (k : ℝ) ≤ (k + 1 : ℕ))] at ht'
        exact ht'

/-- Exact decomposition of the prime Stieltjes error into endpoint errors and
the discrete variation of the test weight. -/
theorem primeThetaWeightedInterval_error_identity (f : ℕ → ℝ) {z y : ℕ}
    (hzy : z < y) :
    primeThetaWeightedInterval f z y - integerAbelMain f z y =
      f y * (primeLogSumUpTo y - (y : ℝ)) -
      f (z + 1) * (primeLogSumUpTo z - (z : ℝ)) -
      ∑ m ∈ Finset.Ioc z (y - 1),
        (f (m + 1) - f m) *
          (primeLogSumUpTo m - (m : ℝ)) := by
  rw [primeThetaWeightedInterval_by_parts f hzy]
  simp only [integerAbelMain]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- Total-variation estimate for the prime Stieltjes error.  Together with
`exists_primeLogSumUpTo_error_bound`, this is a quantitative and completey finite
partial-summation interface; no prime asymptotic is assumed by callers. -/
theorem primeThetaWeightedInterval_error_bound (f : ℕ → ℝ) {z y : ℕ}
    (hzy : z < y) :
    |primeThetaWeightedInterval f z y - integerAbelMain f z y| ≤
      |f y| * |primeLogSumUpTo y - (y : ℝ)| +
      |f (z + 1)| * |primeLogSumUpTo z - (z : ℝ)| +
      ∑ m ∈ Finset.Ioc z (y - 1),
        |f (m + 1) - f m| *
          |primeLogSumUpTo m - (m : ℝ)| := by
  rw [primeThetaWeightedInterval_error_identity f hzy]
  calc
    |f y * (primeLogSumUpTo y - (y : ℝ)) -
        f (z + 1) * (primeLogSumUpTo z - (z : ℝ)) -
        ∑ m ∈ Finset.Ioc z (y - 1),
          (f (m + 1) - f m) *
            (primeLogSumUpTo m - (m : ℝ))| ≤
      |f y * (primeLogSumUpTo y - (y : ℝ)) -
        f (z + 1) * (primeLogSumUpTo z - (z : ℝ))| +
        |∑ m ∈ Finset.Ioc z (y - 1),
          (f (m + 1) - f m) *
            (primeLogSumUpTo m - (m : ℝ))| := abs_sub _ _
    _ ≤ (|f y * (primeLogSumUpTo y - (y : ℝ))| +
        |f (z + 1) * (primeLogSumUpTo z - (z : ℝ))|) +
        ∑ m ∈ Finset.Ioc z (y - 1),
          |(f (m + 1) - f m) *
            (primeLogSumUpTo m - (m : ℝ))| := by
      apply add_le_add
      · exact abs_sub _ _
      · exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul]

/-- The preceding variation estimate with the quantitative PNT substituted at
every endpoint.  The single threshold `X₀` is uniform over the whole finite
prime interval. -/
theorem primeThetaWeightedInterval_pnt_bound (f : ℕ → ℝ)
    {A C : ℝ} {X₀ z y : ℕ}
    (hbound : ∀ X, X₀ ≤ X →
      |primeLogSumUpTo X - (X : ℝ)| ≤
        C * ((X : ℝ) / (Real.log (X : ℝ)) ^ A))
    (hz : X₀ ≤ z) (hzy : z < y) :
    |primeThetaWeightedInterval f z y - integerAbelMain f z y| ≤
      |f y| * (C * ((y : ℝ) / (Real.log (y : ℝ)) ^ A)) +
      |f (z + 1)| * (C * ((z : ℝ) / (Real.log (z : ℝ)) ^ A)) +
      ∑ m ∈ Finset.Ioc z (y - 1),
        |f (m + 1) - f m| *
          (C * ((m : ℝ) / (Real.log (m : ℝ)) ^ A)) := by
  calc
    |primeThetaWeightedInterval f z y - integerAbelMain f z y| ≤
        |f y| * |primeLogSumUpTo y - (y : ℝ)| +
        |f (z + 1)| * |primeLogSumUpTo z - (z : ℝ)| +
        ∑ m ∈ Finset.Ioc z (y - 1),
          |f (m + 1) - f m| *
            |primeLogSumUpTo m - (m : ℝ)| :=
      primeThetaWeightedInterval_error_bound f hzy
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (hbound y (hz.trans hzy.le)) (abs_nonneg (f y))
        · exact mul_le_mul_of_nonneg_left
            (hbound z hz) (abs_nonneg (f (z + 1)))
      · apply Finset.sum_le_sum
        intro m hm
        apply mul_le_mul_of_nonneg_left
        · apply hbound m
          exact hz.trans (Nat.le_of_lt (Finset.mem_Ioc.mp hm).1)
        · exact abs_nonneg (f (m + 1) - f m)

/-! ## Explicit regularity of the finite Dickman kernel -/

/-- The method-of-steps Dickman solution is at most one on the complete compact
range used by the friable induction. -/
theorem rho_le_one_of_le_five {x : ℝ} (hx5 : x ≤ 5) :
    rho x ≤ 1 := by
  by_cases hx1 : x ≤ 1
  · rw [rho_eq_one_of_le_one hx1]
  · have hxmem : x ∈ Set.Icc (1 : ℝ) 5 :=
      ⟨le_of_not_ge hx1, hx5⟩
    have hone : (1 : ℝ) ∈ Set.Icc (1 : ℝ) 5 := by norm_num
    simpa [rho_one] using
      antitoneOn_rho_one_five hone hxmem hxmem.1

/-- On `[1,5]` the delay-equation integrand lies in `[0,1]`. -/
theorem rho_delay_integrand_bounds {t : ℝ} (ht1 : 1 ≤ t) (ht5 : t ≤ 5) :
    0 ≤ rho (t - 1) / t ∧ rho (t - 1) / t ≤ 1 := by
  have hrpos : 0 < rho (t - 1) :=
    rho_pos_on_zero_five (by linarith) (by linarith)
  have hrle : rho (t - 1) ≤ 1 :=
    rho_le_one_of_le_five (by linarith)
  constructor
  · exact div_nonneg hrpos.le (by linarith)
  · apply (div_le_one (by linarith : 0 < t)).mpr
    exact hrle.trans ht1

/-- Explicit one-Lipschitz estimate for `rho` to the right of its initial
corner.  The proof integrates the concrete delay equation, so no smoothness at
the corner `1` is assumed. -/
theorem rho_lipschitz_one_five {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 5) :
    |rho b - rho a| ≤ b - a := by
  let g : ℝ → ℝ := fun t => rho (t - 1) / t
  have hgcont : ContinuousOn g (Set.Icc a b) := by
    apply ContinuousOn.div
    · exact (continuous_rho.comp
        (continuous_id.sub continuous_const)).continuousOn
    · exact continuous_id.continuousOn
    · intro t ht
      exact ne_of_gt (by linarith [ha, ht.1])
  have hgint_ab : IntervalIntegrable g MeasureTheory.volume a b :=
    by
      rw [← Set.uIcc_of_le hab] at hgcont
      exact hgcont.intervalIntegrable
  have hgint_1a : IntervalIntegrable g MeasureTheory.volume 1 a := by
    have hgcont_1a : ContinuousOn g (Set.Icc (1 : ℝ) a) := by
      apply ContinuousOn.div
      · exact (continuous_rho.comp
          (continuous_id.sub continuous_const)).continuousOn
      · exact continuous_id.continuousOn
      · intro t ht
        exact ne_of_gt (by linarith [ht.1])
    rw [← Set.uIcc_of_le ha] at hgcont_1a
    exact hgcont_1a.intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hgint_1a hgint_ab
  have hrhoa := rho_integral_eq ha (hab.trans hb)
  have hrhob := rho_integral_eq (ha.trans hab) hb
  have hdiff : rho b - rho a = -(∫ t in a..b, g t) := by
    dsimp [g] at hadd ⊢
    linarith
  rw [hdiff, abs_neg]
  have hnonneg : 0 ≤ ∫ t in a..b, g t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact (rho_delay_integrand_bounds
      (ha.trans ht.1) (ht.2.trans hb)).1
  rw [abs_of_nonneg hnonneg]
  have hmono := intervalIntegral.integral_mono_on hab hgint_ab
    (continuous_const.intervalIntegrable a b)
    (fun t ht => (rho_delay_integrand_bounds
      (ha.trans ht.1) (ht.2.trans hb)).2)
  simpa using hmono

/-- Global ordered one-Lipschitz estimate on `[0,5]`, including intervals
that cross the corner at `1`. -/
theorem rho_lipschitz_of_le_five {a b : ℝ}
    (hab : a ≤ b) (hb : b ≤ 5) :
    |rho b - rho a| ≤ b - a := by
  by_cases hb1 : b ≤ 1
  · rw [rho_eq_one_of_le_one hb1,
      rho_eq_one_of_le_one (hab.trans hb1)]
    simp only [sub_self, abs_zero]
    linarith
  by_cases ha1 : 1 ≤ a
  · exact rho_lipschitz_one_five ha1 hab hb
  · have hcross := rho_lipschitz_one_five
      (a := (1 : ℝ)) (b := b) le_rfl (le_of_not_ge hb1) hb
    rw [rho_eq_one_of_le_one (le_of_not_ge ha1)]
    simpa only [rho_one] using hcross.trans (by linarith)

/-! ## The Dickman test weight in the prime recurrence -/

/-- The real main term contributed by a prime `p` in the largest-prime
recurrence. -/
noncomputable def dickmanPrimeSummand (X m : ℕ) : ℝ :=
  (X : ℝ) / (m : ℝ) *
    rho (Real.log (X : ℝ) / Real.log (m : ℝ) - 1)

/-- The corresponding test function against Chebyshev's `θ` measure. -/
noncomputable def dickmanThetaWeight (X m : ℕ) : ℝ :=
  dickmanPrimeSummand X m / Real.log (m : ℝ)

/-- Continuous extension of the Dickman test weight used for the ordinary
Riemann integral. -/
noncomputable def dickmanContinuousWeight (X t : ℝ) : ℝ :=
  (X / t * rho (Real.log X / Real.log t - 1)) / Real.log t

/-- An antiderivative of the Dickman test weight on every compact region
where the Dickman delay equation applies. -/
noncomputable def dickmanAntiderivative (X t : ℝ) : ℝ :=
  X * rho (Real.log X / Real.log t)

theorem dickmanContinuousWeight_nat (X m : ℕ) :
    dickmanContinuousWeight (X : ℝ) (m : ℝ) =
      dickmanThetaWeight X m := by
  simp only [dickmanContinuousWeight, dickmanThetaWeight,
    dickmanPrimeSummand]

/-- The continuous Dickman test weight is continuous away from the two
irrelevant singular points `0` and `1`. -/
theorem continuousOn_dickmanContinuousWeight (X : ℝ) :
    ContinuousOn (dickmanContinuousWeight X) (Set.Ioi (1 : ℝ)) := by
  intro t ht
  rw [Set.mem_Ioi] at ht
  have ht0 : t ≠ 0 := by linarith [ht]
  have ht1 : t ≠ 1 := by linarith [ht]
  have hlog_ne : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht]) ht1
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0
  have hq : ContinuousAt
      (fun u : ℝ => Real.log X / Real.log u - 1) t :=
    (continuousAt_const.div hlog hlog_ne).sub continuousAt_const
  have hrho : ContinuousAt
      (fun u : ℝ => rho (Real.log X / Real.log u - 1)) t :=
    continuous_rho.continuousAt.comp hq
  have hmain : ContinuousAt
      (fun u : ℝ => X / u * rho (Real.log X / Real.log u - 1)) t :=
    (continuousAt_const.div continuousAt_id ht0).mul hrho
  exact (hmain.div hlog hlog_ne).continuousWithinAt

/-- Pointwise derivative identity behind the de Bruijn integral. -/
theorem hasDerivAt_dickmanAntiderivative (X t : ℝ) (ht : 1 < t)
    (hq1 : 1 < Real.log X / Real.log t)
    (hq6 : Real.log X / Real.log t ≤ 6) :
    HasDerivAt (dickmanAntiderivative X)
      (dickmanContinuousWeight X t) t := by
  have ht0 : t ≠ 0 := by linarith
  have htlog : Real.log t ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
  let q : ℝ → ℝ := fun s => Real.log X / Real.log s
  have hq : HasDerivAt q
      (-(Real.log X) / (t * (Real.log t) ^ 2)) t := by
    have hraw := (hasDerivAt_const t (Real.log X)).div
      (Real.hasDerivAt_log ht0) htlog
    convert hraw using 1 <;> try rfl
    all_goals field_simp [q, htlog]
    all_goals ring
  have hrho := (hasDerivAt_rho hq1 hq6).comp t hq
  have hmul := (hasDerivAt_const t X).mul hrho
  unfold dickmanAntiderivative dickmanContinuousWeight
  change HasDerivAt (fun s : ℝ => X * rho (q s))
    ((X / t * rho (q t - 1)) / Real.log t) t
  have hq0 : Real.log X / Real.log t ≠ 0 := by linarith
  have hlogX : Real.log X ≠ 0 := by
    intro hzero
    apply hq0
    rw [hzero, zero_div]
  have hqshift : (Real.log X - Real.log t) / Real.log t =
      Real.log X / Real.log t - 1 := by
    field_simp [htlog]
  convert hmul using 1 <;> try rfl
  all_goals field_simp [q, hlogX, htlog, ht0]
  all_goals simp only [mul_zero, zero_mul]
  all_goals dsimp [q]
  all_goals rw [hqshift]
  all_goals ring

/-- Exact evaluation of the continuous de Bruijn integral by the Dickman
delay equation.  The compact coordinate condition is stated explicitly and
is elementary to verify in each method-of-steps strip. -/
theorem integral_dickmanContinuousWeight (X z y : ℝ)
    (hz : 1 < z) (hzy : z ≤ y)
    (hq : ∀ t ∈ Set.Icc z y,
      1 < Real.log X / Real.log t ∧
        Real.log X / Real.log t ≤ 6) :
    (∫ t in z..y, dickmanContinuousWeight X t) =
      dickmanAntiderivative X y - dickmanAntiderivative X z := by
  have hcontW : ContinuousOn
      (dickmanContinuousWeight X) (Set.Icc z y) :=
    (continuousOn_dickmanContinuousWeight X).mono (fun t ht => by
      rw [Set.mem_Ioi]
      exact hz.trans_le ht.1)
  have hint : IntervalIntegrable (dickmanContinuousWeight X)
      MeasureTheory.volume z y := by
    rw [← Set.uIcc_of_le hzy] at hcontW
    exact hcontW.intervalIntegrable
  have hcontA : ContinuousOn
      (dickmanAntiderivative X) (Set.Icc z y) := by
    intro t ht
    exact (hasDerivAt_dickmanAntiderivative X t
      (hz.trans_le ht.1) (hq t ht).1 (hq t ht).2).continuousAt.continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hzy hcontA
  · intro t ht
    exact hasDerivAt_dickmanAntiderivative X t (hz.trans ht.1)
      (hq t ⟨ht.1.le, ht.2.le⟩).1
      (hq t ⟨ht.1.le, ht.2.le⟩).2
  · exact hint

/-- Against a prime point mass, the factor `log p` in `θ` cancels exactly.
Thus the weighted Stieltjes sum is literally the desired Dickman prime sum,
not merely an approximation. -/
theorem primeThetaWeightedInterval_dickman (X : ℕ) {z y : ℕ} :
    primeThetaWeightedInterval (dickmanThetaWeight X) z y =
      ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        dickmanPrimeSummand X p := by
  rw [primeThetaWeightedInterval]
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime := by
    exact Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast hpprime.pos) (by exact_mod_cast hpprime.ne_one)
  rw [dickmanThetaWeight]
  exact div_mul_cancel₀ _ hlog

/-- The genuine finite friable counting function `Ψ(X,y)`. -/
def friableCount (X y : ℕ) : ℕ :=
  (Nat.smoothNumbersUpTo X (y + 1)).card

/-- The Dickman coordinate attached to integral endpoints.  It is total at
the irrelevant boundary `y = 0,1`; analytic statements impose `1 < y`. -/
noncomputable def dickmanU (X y : ℕ) : ℝ :=
  Real.log (X : ℝ) / Real.log (y : ℝ)

@[simp] theorem friableCount_zero (y : ℕ) : friableCount 0 y = 0 := by
  rw [friableCount]
  have hempty : Nat.smoothNumbersUpTo 0 (y + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    rw [Nat.mem_smoothNumbersUpTo] at hm
    have hm0 : m = 0 := by omega
    exact Nat.ne_zero_of_mem_smoothNumbers hm.2 hm0
  rw [hempty]
  simp

theorem friableCount_mono_left {X₁ X₂ y : ℕ} (hX : X₁ ≤ X₂) :
    friableCount X₁ y ≤ friableCount X₂ y := by
  apply Finset.card_le_card
  intro m hm
  rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans hX, hm.2⟩


/-- Below the smoothness threshold every positive integer is smooth.  This is
the exact (not asymptotic) initial condition for the de Bruijn induction. -/
theorem friableCount_eq_self {X y : ℕ} (hXy : X ≤ y) :
    friableCount X y = X := by
  have hrough : Nat.roughNumbersUpTo X (y + 1) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro m hm
    rw [Nat.roughNumbersUpTo, Finset.mem_filter, Finset.mem_range] at hm
    exact hm.2.2 (Nat.mem_smoothNumbers_of_lt
      (Nat.pos_of_ne_zero hm.2.1) (by omega))
  have hcard := Nat.smoothNumbersUpTo_card_add_roughNumbersUpTo_card X (y + 1)
  rw [hrough] at hcard
  simpa [friableCount] using hcard

theorem dickmanU_le_one {X y : ℕ} (hX : 0 < X) (hy : 1 < y)
    (hXy : X ≤ y) : dickmanU X y ≤ 1 := by
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy)
  have hlogxy : Real.log (X : ℝ) ≤ Real.log (y : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast hX
    · exact_mod_cast hXy
  rw [dickmanU, div_le_one hlogy]
  exact hlogxy

/-- Exact Dickman formula on the initial face `u ≤ 1`.  The only discrepancy
between the real endpoint and the count is therefore the explicit floor used
to create `X`; no analytic error occurs here. -/
theorem friableCount_eq_dickman_initial {X y : ℕ} (hX : 0 < X)
    (hy : 1 < y) (hXy : X ≤ y) :
    (friableCount X y : ℝ) = (X : ℝ) * rho (dickmanU X y) := by
  rw [friableCount_eq_self hXy, rho_eq_one_of_le_one
    (dickmanU_le_one hX hy hXy)]
  ring

/-- The part of the `p`-smooth count divisible by the newly admitted prime
`p`. -/
def primeMultipleCell (X p : ℕ) : Finset ℕ :=
  (Nat.smoothNumbersUpTo X (p + 1)).filter (p ∣ ·)

theorem mem_smooth_succ_not_smooth_iff_dvd {p m : ℕ}
    (hp : p.Prime) (hm : m ∈ Nat.smoothNumbers (p + 1)) :
    m ∉ Nat.smoothNumbers p ↔ p ∣ m := by
  rw [Nat.mem_smoothNumbers'] at hm
  constructor
  · intro hnot
    by_contra hpdvd
    apply hnot
    rw [Nat.mem_smoothNumbers']
    intro q hq hqdiv
    have hqsucc : q < p + 1 := hm q hq hqdiv
    have hqne : q ≠ p := by
      intro hqp
      exact hpdvd (hqp ▸ hqdiv)
    omega
  · intro hpdiv hsmooth
    rw [Nat.mem_smoothNumbers'] at hsmooth
    exact (Nat.lt_irrefl p) (hsmooth p hp hpdiv)

theorem primeMultipleCell_card (X : ℕ) {p : ℕ} (hp : p.Prime) :
    (primeMultipleCell X p).card = friableCount (X / p) p := by
  classical
  apply Finset.card_bij (fun m _ => m / p)
  · intro m hm
    rw [primeMultipleCell, Finset.mem_filter,
      Nat.mem_smoothNumbersUpTo] at hm
    rw [Nat.mem_smoothNumbersUpTo]
    refine ⟨?_, Nat.mem_smoothNumbers_of_dvd hm.1.2 (Nat.div_dvd_of_dvd hm.2)⟩
    apply (Nat.le_div_iff_mul_le hp.pos).mpr
    simpa [Nat.div_mul_cancel hm.2] using hm.1.1
  · intro m₁ hm₁ m₂ hm₂ heq
    rw [primeMultipleCell, Finset.mem_filter] at hm₁ hm₂
    calc
      m₁ = m₁ / p * p := (Nat.div_mul_cancel hm₁.2).symm
      _ = m₂ / p * p := by rw [heq]
      _ = m₂ := Nat.div_mul_cancel hm₂.2
  · intro k hk
    rw [Nat.mem_smoothNumbersUpTo] at hk
    refine ⟨k * p, ?_, ?_⟩
    · rw [primeMultipleCell, Finset.mem_filter,
        Nat.mem_smoothNumbersUpTo]
      refine ⟨⟨?_, Nat.mul_mem_smoothNumbers hk.2 ?_⟩, by simp⟩
      · exact (Nat.le_div_iff_mul_le hp.pos).mp hk.1
      · exact Nat.mem_smoothNumbers_of_lt hp.pos (by omega)
    · exact Nat.mul_div_left k hp.pos

/-- Exact one-prime Buchstab recursion.  The first term excludes `p`; the
second term divides the newly admitted multiples of `p` by `p`.  Repeatedly
applying this identity is the discrete arithmetic induction underlying the
finite-range de Bruijn argument. -/
theorem friableCount_prime_step (X : ℕ) {p : ℕ} (hp : p.Prime) :
    friableCount X p =
      friableCount X (p - 1) + friableCount (X / p) p := by
  classical
  let A := Nat.smoothNumbersUpTo X (p + 1)
  let P : ℕ → Prop := fun m => m ∈ Nat.smoothNumbers p
  have hpartition := Finset.card_filter_add_card_filter_not (s := A) P
  have hbelow : A.filter P = Nat.smoothNumbersUpTo X p := by
    ext m
    simp only [A, P, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨hmX, hm⟩, hmp⟩
      exact ⟨hmX, hmp⟩
    · rintro ⟨hmX, hmp⟩
      exact ⟨⟨hmX, Nat.smoothNumbers_mono (by omega) hmp⟩, hmp⟩
  have hnew : A.filter (fun m => ¬P m) = primeMultipleCell X p := by
    ext m
    simp only [A, P, primeMultipleCell, Finset.mem_filter,
      Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨⟨hmX, hm⟩, hn⟩
      exact ⟨⟨hmX, hm⟩, (mem_smooth_succ_not_smooth_iff_dvd hp hm).mp hn⟩
    · rintro ⟨⟨hmX, hm⟩, hpdiv⟩
      exact ⟨⟨hmX, hm⟩, (mem_smooth_succ_not_smooth_iff_dvd hp hm).mpr hpdiv⟩
  rw [hbelow, hnew, primeMultipleCell_card X hp] at hpartition
  have hpone : 1 ≤ p := hp.one_le
  simpa [friableCount, Nat.sub_add_cancel hpone, A] using hpartition.symm

/-- At a composite cutoff no new smooth numbers appear. -/
theorem friableCount_composite_step (X : ℕ) {k : ℕ} (hk : ¬k.Prime) :
    friableCount X k = friableCount X (k - 1) := by
  by_cases hk0 : k = 0
  · subst k
    simp [friableCount]
  have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
  rw [friableCount, friableCount, Nat.sub_add_cancel hkone]
  unfold Nat.smoothNumbersUpTo
  congr 1
  ext m
  simp only [Finset.mem_filter, Nat.smoothNumbers_succ hk]

theorem friableCount_cutoff_zero {X : ℕ} (hX : 0 < X) :
    friableCount X 0 = 1 := by
  have hset : Nat.smoothNumbersUpTo X 1 = {1} := by
    ext m
    rw [Nat.mem_smoothNumbersUpTo, Nat.smoothNumbers_one]
    simp only [Set.mem_singleton_iff, Finset.mem_singleton]
    constructor
    · rintro ⟨hmX, rfl⟩
      rfl
    · rintro rfl
      exact ⟨hX, rfl⟩
  rw [friableCount, hset]
  simp

/-- Exact largest-prime-factor recursion

`\Psi(X,y) = 1 + \sum_{p \le y} \Psi(\lfloor X/p\rfloor,p)`.

The identity follows here from the one-prime step and therefore does not need
an independently postulated greatest-prime-factor decomposition.  This is the
finite recurrence to which prime Stieltjes summation is applied in the
de Bruijn induction. -/
theorem friableCount_largest_prime (X y : ℕ) (hX : 0 < X) :
    friableCount X y =
      1 + ∑ p ∈ (y + 1).primesBelow, friableCount (X / p) p := by
  induction y with
  | zero =>
      rw [friableCount_cutoff_zero hX]
      simp [Nat.primesBelow]
  | succ y ih =>
      by_cases hp : (y + 1).Prime
      · rw [friableCount_prime_step X hp]
        have hsub : y + 1 - 1 = y := by omega
        have hprimes : (y + 1 + 1).primesBelow =
            insert (y + 1) (y + 1).primesBelow := by
          rw [Nat.primesBelow_succ, ite_eq_left hp]
        rw [hsub, ih, hprimes,
          Finset.sum_insert (Nat.notMem_primesBelow (y + 1))]
        omega
      · rw [friableCount_composite_step X hp]
        have hsub : y + 1 - 1 = y := by omega
        have hprimes : (y + 1 + 1).primesBelow = (y + 1).primesBelow := by
          rw [Nat.primesBelow_succ, ite_eq_right hp]
        rw [hsub, ih, hprimes]

/-- Truncated largest-prime recursion.  This is the induction-friendly form:
choosing `z` so that `log X / log z` is an integer puts the first term on the
previous Dickman step, while every quotient in the prime interval has a
strictly smaller Dickman coordinate. -/
theorem friableCount_prime_interval (X : ℕ) {z y : ℕ} (hX : 0 < X)
    (hzy : z ≤ y) :
    friableCount X y = friableCount X z +
      ∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        friableCount (X / p) p := by
  have hsubset : (z + 1).primesBelow ⊆ (y + 1).primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum :
      (∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          friableCount (X / p) p) +
        ∑ p ∈ (z + 1).primesBelow, friableCount (X / p) p =
          ∑ p ∈ (y + 1).primesBelow, friableCount (X / p) p := by
    simpa only using
      (Finset.sum_sdiff (f := fun p => friableCount (X / p) p) hsubset)
  rw [friableCount_largest_prime X y hX,
    friableCount_largest_prime X z hX]
  omega


end FriableIntegers.FriableAsymptotic
