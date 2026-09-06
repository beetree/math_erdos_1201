module


public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Group.Unbundled.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Algebra.Order.SuccPred
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Star
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.SetLike.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.AtTopBot.Field
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.Max
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Order.Nat
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Erdos1201.Vendor.NumberTheory.MertensTheorems




@[expose] public section

/-!
# Quantitative lower bounds for sums of prime reciprocals
-/

open Nat Finset Filter Asymptotics
open scoped Nat.Prime Topology

namespace Research

/-- Sum of reciprocals of primes at most `N`. -/
noncomputable def primeReciprocalSum (N : ℕ) : ℝ :=
  ∑ p ∈ N.primesLE, (1 / p : ℝ)

/-- Reciprocal-prime mass in the half-open numerical block `(a,b]`. -/
noncomputable def primeReciprocalBlock (a b : ℕ) : ℝ :=
  ∑ p ∈ b.primesLE \ a.primesLE, (1 / p : ℝ)

/-- A reciprocal-prime block is the difference of its two prefix sums. -/
theorem primeReciprocalBlock_eq_sub {a b : ℕ} (hab : a ≤ b) :
    primeReciprocalBlock a b =
      primeReciprocalSum b - primeReciprocalSum a := by
  have hsub : a.primesLE ⊆ b.primesLE := Nat.primesLE_mono hab
  have hs := Finset.sum_sdiff hsub (f := fun p : ℕ ↦ (1 / p : ℝ))
  unfold primeReciprocalBlock primeReciprocalSum
  linarith

/-- The raw `primesLE` spelling of `primeReciprocalBlock_eq_sub`. -/
theorem sum_primesLE_sdiff_one_div {a b : ℕ} (hab : a ≤ b) :
    (∑ p ∈ b.primesLE \ a.primesLE, (1 / p : ℝ)) =
      primeReciprocalSum b - primeReciprocalSum a :=
  primeReciprocalBlock_eq_sub hab

/-- The reciprocal mass in `(a,b]` dominates the number of primes in that
interval divided by `b`. -/
theorem primeCounting_sub_div_le_primeReciprocalSum_sub
    {a b : ℕ} (hab : a ≤ b) (_ : 0 < b) :
    ((b.primeCounting - a.primeCounting : ℕ) : ℝ) / b ≤
      primeReciprocalSum b - primeReciprocalSum a := by
  let block := b.primesLE \ a.primesLE
  have hsub : a.primesLE ⊆ b.primesLE := Nat.primesLE_mono hab
  have hcard : block.card = b.primeCounting - a.primeCounting := by
    dsimp [block]
    rw [Finset.card_sdiff_of_subset hsub,
      Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting]
  have hterm : ∀ p ∈ block, (1 / (b : ℝ)) ≤ (1 / (p : ℝ)) := by
    intro p hp
    have hp' := Finset.mem_sdiff.mp hp |>.1
    have hple : p ≤ b := (Nat.mem_primesLE.mp hp').1
    have hppos : 0 < (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primesBelow
        (show p ∈ (b + 1).primesBelow by simpa [Nat.primesLE] using hp')).pos
    exact one_div_le_one_div_of_le hppos (by exact_mod_cast hple)
  have hsum : (block.card : ℝ) / b ≤ ∑ p ∈ block, (1 / p : ℝ) := by
    calc
      (block.card : ℝ) / b = ∑ _p ∈ block, (1 / (b : ℝ)) := by simp [div_eq_mul_inv]
      _ ≤ ∑ p ∈ block, (1 / p : ℝ) := Finset.sum_le_sum hterm
  have hdiff : (∑ p ∈ block, (1 / p : ℝ)) =
      primeReciprocalSum b - primeReciprocalSum a :=
    sum_primesLE_sdiff_one_div hab
  rw [← hcard]
  exact hsum.trans_eq hdiff

/-- A convenient eventual lower Chebyshev bound for the prime-counting
function. -/
theorem eventually_log_two_half_mul_div_log_le_primeCounting :
    ∀ᶠ x : ℝ in atTop,
      (Real.log 2 / 2) * x / Real.log x ≤ (⌊x⌋₊.primeCounting : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < Real.log 2 / 8 := div_pos hlog2 (by norm_num)
  have hsmall := Real.isLittleO_log_id_atTop.bound hc
  filter_upwards [eventually_ge_atTop (16 : ℝ), hsmall] with x hx hlog
  have hxpos : 0 < x := by linarith
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith)
  simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg hxpos.le,
    abs_of_nonneg hlogxpos.le] at hlog
  have hx2pos : 0 < x + 2 := by linarith
  have h2xpos : 0 < 2 * x := mul_pos (by norm_num) hxpos
  have hlogadd : Real.log (x + 2) ≤ Real.log (2 * x) :=
    Real.strictMonoOn_log.monotoneOn hx2pos h2xpos (by linarith)
  have hlogmul : Real.log (2 * x) = Real.log 2 + Real.log x := by
    rw [Real.log_mul (by norm_num) hxpos.ne']
  have hconst : 2 * Real.log 2 ≤ (Real.log 2 / 8) * x := by
    nlinarith
  have hnum : (Real.log 2 / 2) * x ≤
      (x - 1) * Real.log 2 - Real.log (x + 2) := by
    nlinarith
  calc
    (Real.log 2 / 2) * x / Real.log x ≤
        ((x - 1) * Real.log 2 - Real.log (x + 2)) / Real.log x :=
      (div_le_div_iff_of_pos_right hlogxpos).2 hnum
    _ ≤ (⌊x⌋₊.primeCounting : ℝ) := Chebyshev.pi_ge' (by linarith)

/-- One geometric prime block contributes a reciprocal mass comparable to
`1/log n`, assuming the standard Chebyshev upper and lower estimates at its
endpoints. -/
theorem log_two_div_sixteen_log_le_primeReciprocal_block
    {n : ℕ} (hn : 16 ≤ n)
    (hlower : (Real.log 2 / 2) * (16 * n : ℝ) / Real.log (16 * n) ≤
      ((16 * n).primeCounting : ℝ))
    (hupper : (n.primeCounting : ℝ) ≤
      (Real.log 4 + Real.log 2) * n / Real.log n) :
    Real.log 2 / (16 * Real.log n) ≤
      primeReciprocalSum (16 * n) - primeReciprocalSum n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog16n : Real.log (16 * n : ℝ) = Real.log 16 + Real.log n := by
    rw [Real.log_mul (by norm_num) (by positivity : (n : ℝ) ≠ 0)]
  have hlog16_le : Real.log (16 : ℝ) ≤ Real.log n := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num)
      (show (0 : ℝ) < n by positivity) (by exact_mod_cast hn)
  have hden : Real.log (16 * n : ℝ) ≤ 2 * Real.log n := by
    rw [hlog16n]
    linarith
  have h16n : (1 : ℝ) < 16 * n := by
    exact_mod_cast (show 1 < 16 * n by omega)
  have hendpoint : 4 * Real.log 2 * n / Real.log n ≤
      (Real.log 2 / 2) * (16 * n : ℝ) / Real.log (16 * n) := by
    rw [div_le_div_iff₀ hlogn (Real.log_pos h16n)]
    nlinarith [mul_nonneg (show 0 ≤ 4 * Real.log 2 * (n : ℝ) by positivity)
      (sub_nonneg.mpr hden)]
  have hbig := hendpoint.trans hlower
  let A : ℝ := Real.log 2 * n / Real.log n
  have hbig' : 4 * A ≤ ((16 * n).primeCounting : ℝ) := by
    calc
      4 * A = 4 * Real.log 2 * n / Real.log n := by dsimp [A]; ring
      _ ≤ ((16 * n).primeCounting : ℝ) := hbig
  have hupper' : (n.primeCounting : ℝ) ≤ 3 * A := by
    rw [hlog4] at hupper
    calc
      (n.primeCounting : ℝ) ≤
          (2 * Real.log 2 + Real.log 2) * n / Real.log n := hupper
      _ = 3 * A := by dsimp [A]; ring
  have hcountR : Real.log 2 * n / Real.log n ≤
      ((16 * n).primeCounting : ℝ) - (n.primeCounting : ℝ) := by
    change A ≤ _
    linarith
  have hpimon : n.primeCounting ≤ (16 * n).primeCounting :=
    Nat.monotone_primeCounting (by omega)
  have hcount : Real.log 2 * n / Real.log n ≤
      (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpimon]
    exact hcountR
  have hdiv := div_le_div_of_nonneg_right hcount
    (show 0 ≤ (16 * n : ℝ) by positivity)
  have hblock : (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) /
      (16 * n : ℝ) ≤ primeReciprocalSum (16 * n) - primeReciprocalSum n := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      primeCounting_sub_div_le_primeReciprocalSum_sub
        (show n ≤ 16 * n by omega) (show 0 < 16 * n by positivity)
  calc
    Real.log 2 / (16 * Real.log n) =
        (Real.log 2 * n / Real.log n) / (16 * n : ℝ) := by field_simp
    _ ≤ (((16 * n).primeCounting - n.primeCounting : ℕ) : ℝ) /
        (16 * n : ℝ) := hdiv
    _ ≤ primeReciprocalSum (16 * n) - primeReciprocalSum n := hblock

/-- Eventually every multiplicative block `(n,16n]` contributes at least
`log 2 /(16 log n)` to the prime reciprocal sum. -/
theorem eventually_primeReciprocal_block_lower :
    ∀ᶠ n : ℕ in atTop, Real.log 2 / (16 * Real.log n) ≤
      primeReciprocalSum (16 * n) - primeReciprocalSum n := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlower :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 16)).eventually
      eventually_log_two_half_mul_div_log_le_primeCounting
  have hupper := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (Chebyshev.eventually_primeCounting_le hlog2)
  filter_upwards [eventually_ge_atTop 16, hlower, hupper] with n hn hl hu
  apply log_two_div_sixteen_log_le_primeReciprocal_block hn
  · have hf : ⌊(16 : ℝ) * (n : ℝ)⌋₊ = 16 * n := by
      calc
        ⌊(16 : ℝ) * (n : ℝ)⌋₊ = ⌊((16 * n : ℕ) : ℝ)⌋₊ := by norm_num
        _ = 16 * n := Nat.floor_natCast _
    simpa only [Nat.cast_mul, Nat.cast_ofNat, hf] using hl
  · simpa only [Nat.floor_natCast] using hu

/-- Mertens' second theorem read at the geometric endpoints `16 ^ J`: for
`J ≥ 4096` the prime reciprocal sum up to `16 ^ J` equals
`log J + log (log 16) + M` to within `1/1000`. -/
theorem abs_primeReciprocalSum_pow_sixteen_sub_le {J : ℕ} (hJ : 4096 ≤ J) :
    |primeReciprocalSum (16 ^ J) -
        (Real.log J + Real.log (Real.log 16)) - Mertens.Weight.prime.M|
      ≤ 1 / 1000 := by
  have hJpos : 0 < J := by omega
  have hJR : (4096 : ℝ) ≤ (J : ℝ) := by exact_mod_cast hJ
  have hJne : ((J : ℝ)) ≠ 0 := by positivity
  have h2 : 2 ≤ 16 ^ J := by
    calc (2 : ℕ) ≤ 16 ^ 1 := by norm_num
      _ ≤ 16 ^ J := Nat.pow_le_pow_right (by norm_num) hJpos
  have hb := Mertens.sum_prime_inv_sub_sub_bound_nat h2
  have hlog16 : (0 : ℝ) < Real.log 16 := Real.log_pos (by norm_num)
  have hcast : (((16 ^ J : ℕ)) : ℝ) = (16 : ℝ) ^ J := by push_cast; ring
  have hlogpow : Real.log (((16 ^ J : ℕ)) : ℝ) = (J : ℝ) * Real.log 16 := by
    rw [hcast, Real.log_pow]
  have hloglog : Real.log (Real.log (((16 ^ J : ℕ)) : ℝ))
      = Real.log J + Real.log (Real.log 16) := by
    rw [hlogpow, Real.log_mul hJne (ne_of_gt hlog16)]
  rw [hloglog, hlogpow] at hb
  have h4 : Real.log 4 < 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    nlinarith [Real.log_two_lt_d9]
  have h16 : (2.7725 : ℝ) < Real.log 16 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    nlinarith [Real.log_two_gt_d9]
  have herr : (Real.log 4 + 3) / ((J : ℝ) * Real.log 16) ≤ 1 / 1000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hJR, h4, h16, hlog16]
  calc |primeReciprocalSum (16 ^ J) -
          (Real.log J + Real.log (Real.log 16)) - Mertens.Weight.prime.M|
      ≤ (Real.log 4 + 3) / ((J : ℝ) * Real.log 16) := hb
    _ ≤ 1 / 1000 := herr

-- Instantiating `16 ^ J` at the concrete cutoff `J = 4096` requires this threshold
-- (`push_cast at *` would otherwise try to evaluate that power).
set_option exponentiation.threshold 4096 in
theorem exists_geometric_primeReciprocal_log_upper :
    ∃ J₀ : ℕ, 0 < J₀ ∧ ∀ J : ℕ, J₀ ≤ J →
      primeReciprocalSum (16 ^ J) - primeReciprocalSum (16 ^ J₀) ≤
        12 * (1 + Real.log J) := by
  refine ⟨4096, by norm_num, ?_⟩
  intro J hJ
  have hJ1 : 1 < J := by omega
  have hupper := (abs_le.mp (abs_primeReciprocalSum_pow_sixteen_sub_le hJ)).2
  have hlower := (abs_le.mp
    (abs_primeReciprocalSum_pow_sixteen_sub_le (le_refl 4096))).1
  have hlogJ : 0 ≤ Real.log J := Real.log_nonneg (by exact_mod_cast hJ1.le)
  have hlog0 : (0 : ℝ) ≤ Real.log ((4096 : ℕ) : ℝ) :=
    Real.log_nonneg (by norm_num)
  push_cast at *
  linarith

theorem exists_geometric_interval_primeReciprocal_bounds :
    ∃ Jmin : ℕ, 2 ≤ Jmin ∧ ∀ Jz Jy : ℕ, Jmin ≤ Jz → Jz ≤ Jy →
      (Real.log Jy - (1 + Real.log Jz)) / 64 ≤
          primeReciprocalSum (16 ^ Jy) - primeReciprocalSum (16 ^ Jz) ∧
      primeReciprocalSum (16 ^ Jy) - primeReciprocalSum (16 ^ Jz) ≤
          12 * (1 + Real.log Jy) := by
  refine ⟨4096, by norm_num, ?_⟩
  intro Jz Jy hmin hzy
  have hz := abs_primeReciprocalSum_pow_sixteen_sub_le hmin
  have hy := abs_primeReciprocalSum_pow_sixteen_sub_le (le_trans hmin hzy)
  have hz1 := (abs_le.mp hz).1
  have hz2 := (abs_le.mp hz).2
  have hy1 := (abs_le.mp hy).1
  have hy2 := (abs_le.mp hy).2
  have hZR : (1 : ℝ) ≤ (Jz : ℝ) := by exact_mod_cast (by omega : 1 ≤ Jz)
  have hYR : ((Jz : ℝ)) ≤ (Jy : ℝ) := by exact_mod_cast hzy
  have hlogz : 0 ≤ Real.log Jz := Real.log_nonneg hZR
  have hmono : Real.log Jz ≤ Real.log Jy :=
    Real.log_le_log (by linarith) hYR
  constructor
  · linarith
  · linarith

end Research
