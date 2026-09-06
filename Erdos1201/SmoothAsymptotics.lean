import Erdos1201.AnalyticInputs

/-!
# Smooth number asymptotics and deduction of mean input

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This file is part of a Lean reproduction of that work; see `erdos1201.pdf`.

This module defines the smooth counting function `smoothCount Y N`, representing
Ψ(N, Y) = |{m ≤ N : P+(m) ≤ Y}| for positive integers m, and the explicit
analytic input `SmoothCountingInput` capturing the Dickman–de Bruijn asymptotic
estimates for Ψ(X, X^β) and Ψ(2X, X^β).

It then proves `SmoothCountingInput.to_smoothMeanInput`, showing that
`SmoothCountingInput` implies `SmoothMeanInput` by exact endpoint correction and
a squeeze-theorem argument for the boundary difference.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1201

/-- The counting function of Y-smooth positive integers up to N.
Since `smoothIndicator Y 0 = 0`, summing over `range (N + 1)` exactly counts
positive integers `m ≤ N` with `Smooth Y m`. -/
noncomputable def smoothCount (Y : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), smoothIndicator Y n

@[simp] theorem smoothIndicator_zero (Y : ℝ) : smoothIndicator Y 0 = 0 := by
  simp [smoothIndicator, Smooth]

/-- Exact endpoint decomposition of `blockMean f X` via prefix sums over `range`.
For any arithmetic function `f`, the block mean over `[X, 2X)` satisfies:
`blockMean f X = (∑_{n ≤ 2X} f(n) - ∑_{n ≤ X} f(n) + f(X) - f(2X)) / X`. -/
theorem blockMean_eq_range_sum (f : ℕ → ℝ) (X : ℕ) :
    blockMean f X =
      ((∑ n ∈ range (2 * X + 1), f n) - (∑ n ∈ range (X + 1), f n) + f X - f (2 * X)) / (X : ℝ) := by
  unfold blockMean
  rw [sum_range_succ, sum_range_succ]
  have hle : X ≤ 2 * X := by omega
  have h := (sum_range_add_sum_Ico f hle).symm
  rw [h]
  ring

/-- Exact endpoint correction expressing `blockMean (smoothIndicator Y) X` in terms of
smooth counts `smoothCount Y (2 * X)` and `smoothCount Y X`. -/
theorem blockMean_smoothIndicator_eq (Y : ℝ) (X : ℕ) :
    blockMean (smoothIndicator Y) X =
      (smoothCount Y (2 * X) - smoothCount Y X +
        smoothIndicator Y X - smoothIndicator Y (2 * X)) / (X : ℝ) :=
  blockMean_eq_range_sum (smoothIndicator Y) X

/-- The normalized reciprocal `1 / X` tends to 0 as natural `X → ∞`. -/
theorem tendsto_one_div_atTop :
    Tendsto (fun X : ℕ => (1 : ℝ) / (X : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The normalized reciprocal `-1 / X` tends to 0 as natural `X → ∞`. -/
theorem tendsto_neg_one_div_atTop :
    Tendsto (fun X : ℕ => (-1 : ℝ) / (X : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))

/-- The difference of two values of `smoothIndicator` is bounded in absolute value by 1,
since each indicator value is either 0 or 1. -/
theorem abs_smoothIndicator_sub_le (Y : ℝ) (m n : ℕ) :
    |smoothIndicator Y m - smoothIndicator Y n| ≤ 1 := by
  simp only [smoothIndicator]
  split_ifs <;> norm_num

/-- Upper bound of 1 on the difference of two indicator values. -/
theorem smoothIndicator_sub_le_one (Y : ℝ) (m n : ℕ) :
    smoothIndicator Y m - smoothIndicator Y n ≤ 1 :=
  (abs_le.mp (abs_smoothIndicator_sub_le Y m n)).2

/-- Lower bound of -1 on the difference of two indicator values. -/
theorem neg_one_le_smoothIndicator_sub (Y : ℝ) (m n : ℕ) :
    -1 ≤ smoothIndicator Y m - smoothIndicator Y n :=
  (abs_le.mp (abs_smoothIndicator_sub_le Y m n)).1

/-- Upper squeeze bound: `(f(X) - f(2X)) / X ≤ 1 / X`. -/
theorem endpoint_div_le (Y : ℝ) (X : ℕ) :
    (smoothIndicator Y X - smoothIndicator Y (2 * X)) / (X : ℝ) ≤ 1 / (X : ℝ) := by
  by_cases hX : (X : ℝ) = 0
  · simp [hX]
  · have hXpos : 0 < (X : ℝ) := by
      have : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
      exact lt_of_le_of_ne this (Ne.symm hX)
    exact div_le_div_of_nonneg_right (smoothIndicator_sub_le_one Y X (2 * X)) hXpos.le

/-- Lower squeeze bound: `-1 / X ≤ (f(X) - f(2X)) / X`. -/
theorem neg_one_div_le_endpoint (Y : ℝ) (X : ℕ) :
    (-1 : ℝ) / (X : ℝ) ≤ (smoothIndicator Y X - smoothIndicator Y (2 * X)) / (X : ℝ) := by
  by_cases hX : (X : ℝ) = 0
  · simp [hX]
  · have hXpos : 0 < (X : ℝ) := by
      have : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
      exact lt_of_le_of_ne this (Ne.symm hX)
    exact div_le_div_of_nonneg_right (neg_one_le_smoothIndicator_sub Y X (2 * X)) hXpos.le

/-- Squeeze theorem: the normalized endpoint difference `(f(X) - f(2X)) / X` tends to 0. -/
theorem tendsto_endpoint_zero (β : ℝ) :
    Tendsto (fun X : ℕ => (smoothIndicator ((X : ℝ) ^ β) X -
      smoothIndicator ((X : ℝ) ^ β) (2 * X)) / (X : ℝ)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_neg_one_div_atTop tendsto_one_div_atTop
  · intro X
    exact neg_one_div_le_endpoint _ X
  · intro X
    exact endpoint_div_le _ X

/-- Explicit analytic input from the Dickman–de Bruijn asymptotic estimate:
for every `0 < β < 1`, there exists `r < 1` such that
`Ψ(X, X^β) / X → r` and `Ψ(2X, X^β) / X → 2 * r` as natural `X → ∞`.
This is an explicit unproved hypothesis, not an axiom. -/
def SmoothCountingInput : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 → ∃ r : ℝ, r < 1 ∧
    Tendsto (fun X : ℕ => smoothCount ((X : ℝ) ^ β) X / (X : ℝ)) atTop (𝓝 r) ∧
    Tendsto (fun X : ℕ => smoothCount ((X : ℝ) ^ β) (2 * X) / (X : ℝ)) atTop (𝓝 (2 * r))

/-- Deduction of `SmoothMeanInput` from `SmoothCountingInput`:
the limiting block mean of the smooth indicator equals `(2 * r) - r + 0 = r < 1`. -/
theorem SmoothCountingInput.to_smoothMeanInput (H : SmoothCountingInput) : SmoothMeanInput := by
  intro β hβ0 hβ1
  obtain ⟨r, hr, hX, h2X⟩ := H β hβ0 hβ1
  refine ⟨r, hr, ?_⟩
  have hsub : Tendsto (fun X : ℕ =>
      (smoothCount ((X : ℝ) ^ β) (2 * X) / (X : ℝ)) -
      (smoothCount ((X : ℝ) ^ β) X / (X : ℝ))) atTop (𝓝 (2 * r - r)) :=
    h2X.sub hX
  have hend := tendsto_endpoint_zero β
  have hsum : Tendsto (fun X : ℕ =>
      ((smoothCount ((X : ℝ) ^ β) (2 * X) / (X : ℝ)) -
       (smoothCount ((X : ℝ) ^ β) X / (X : ℝ))) +
      ((smoothIndicator ((X : ℝ) ^ β) X -
        smoothIndicator ((X : ℝ) ^ β) (2 * X)) / (X : ℝ))) atTop (𝓝 (2 * r - r + 0)) :=
    hsub.add hend
  rw [show 2 * r - r + 0 = r by ring] at hsum
  refine hsum.congr (fun X => ?_)
  rw [blockMean_smoothIndicator_eq]
  ring

end Erdos1201
