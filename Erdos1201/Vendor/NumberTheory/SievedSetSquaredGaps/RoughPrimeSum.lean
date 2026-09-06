module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.IsBotOne
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.SDiff
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Star
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Data.SetLike.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FieldSimp.Lemmas
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
public import Erdos1201.Vendor.NumberTheory.SievedSetSquaredGaps.RoughCoprimePairs

@[expose] public section


open scoped BigOperators

/-- The elementary telescoping bound `1/(m+1)^2 ≤ 1/m - 1/(m+1)`. -/
theorem one_div_succ_sq_le_telescope (m : ℕ) (hm : 0 < m) :
    (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2 ≤
      1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  have hid : (1 : ℝ) / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) =
      1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
    field_simp
    norm_num only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hid]
  apply one_div_le_one_div_of_le
  · positivity
  · have hle : (m : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ m
    have hmul := mul_le_mul_of_nonneg_right hle hsR.le
    simpa [pow_two] using hmul

/-- A finite initial segment of the reciprocal-square tail above `Y` is at
most `1/Y`. -/
theorem sum_range_one_div_add_sq_le (Y N : ℕ) (hY : 0 < Y) :
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((Y + i + 1 : ℕ) : ℝ) ^ 2) ≤
      1 / (Y : ℝ) := by
  let f : ℕ → ℝ := fun i => 1 / ((Y + i : ℕ) : ℝ)
  calc
    (∑ i ∈ Finset.range N, (1 : ℝ) / ((Y + i + 1 : ℕ) : ℝ) ^ 2) ≤
        ∑ i ∈ Finset.range N, (f i - f (i + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      simpa [f, Nat.add_assoc] using one_div_succ_sq_le_telescope (Y + i) (by omega)
    _ = f 0 - f N := Finset.sum_range_sub' f N
    _ ≤ 1 / (Y : ℝ) := by
      dsimp [f]
      have hnonneg : (0 : ℝ) ≤ 1 / ((Y + N : ℕ) : ℝ) := by positivity
      linarith

/-- The reciprocal-square sum over any finite set of distinct integers in
`(Y,G]` is at most `1/Y`. -/
theorem finset_sum_one_div_sq_le
    (S : Finset ℕ) (Y G : ℕ) (hY : 0 < Y)
    (hlow : ∀ d ∈ S, Y < d) (hupp : ∀ d ∈ S, d ≤ G) :
    (∑ d ∈ S, (1 : ℝ) / (d : ℝ) ^ 2) ≤ 1 / (Y : ℝ) := by
  let shift : ℕ → ℕ := fun d => d - Y - 1
  let g : ℕ → ℝ := fun k => 1 / ((Y + k + 1 : ℕ) : ℝ) ^ 2
  have hinj : Set.InjOn shift (S : Set ℕ) := by
    intro d hd e he hde
    dsimp [shift] at hde
    have hdY := hlow d hd
    have heY := hlow e he
    omega
  have himage : S.image shift ⊆ Finset.range G := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨d, hd, rfl⟩
    apply Finset.mem_range.mpr
    dsimp [shift]
    have hdG := hupp d hd
    have hdY := hlow d hd
    omega
  calc
    (∑ d ∈ S, (1 : ℝ) / (d : ℝ) ^ 2) = ∑ d ∈ S, g (shift d) := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdY := hlow d hd
      simp only [g, shift]
      congr 3
      omega
    _ = ∑ k ∈ S.image shift, g k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Finset.range G, g k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro k hk hkn
      positivity
    _ ≤ 1 / (Y : ℝ) := by
      exact sum_range_one_div_add_sq_le Y G hY


