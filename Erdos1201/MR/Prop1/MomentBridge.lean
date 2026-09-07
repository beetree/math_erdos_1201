import Mathlib
import Erdos1201.MR.Setup
import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.MR.Polynomials.MomentComputation

open scoped BigOperators
open intervalIntegral

/-!
# Bridge from Lemma 13 to Short Prime and Cofactor Ranges

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module provides the bridge from Lemma 13 (dyadic moment computation,
`integral_norm_sq_prime_poly_pow_mul_le_general`) to the short prime range
`shortPrimeRange Pi Qi Hi r` and the real cofactor range `cofactorRange X H v`
used in Proposition 1 of Matomäki–Radziwiłł.
-/

namespace Erdos1201.MR

/-! ### Part 1: Continuity and Integrability of Dirichlet Polynomials -/

/-- Continuity of a single Dirichlet power summand `t ↦ n^{-(1 + it)}`. -/
lemma continuous_cpow_term_mb (n : ℕ) (hn : 0 < n) :
    Continuous (fun t : ℝ => (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) := by
  have h_eq : (fun t : ℝ => (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) =
      (fun t : ℝ => (1 / (n : ℂ)) * Complex.exp (-Complex.I * (t : ℂ) * ((Real.log n : ℝ) : ℂ))) := by
    ext t
    exact natCast_cpow_neg_one_add_mul_I_eq_exp n hn t
  rw [h_eq]
  fun_prop

/-- Continuity of a finite Dirichlet polynomial on the line `Re s = 1`. -/
lemma continuous_dirichletPoly_mb (a : ℕ → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    Continuous (fun t : ℝ => dirichletPoly a S ((1 : ℂ) + (t : ℝ) * Complex.I)) := by
  unfold dirichletPoly
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.mul (continuous_cpow_term_mb n (hS n hn))

/-- Continuity of the squared norm of a product of Dirichlet polynomial powers. -/
lemma continuous_norm_sq_dirichletPoly_pow_mul (c a : ℕ → ℂ) (P A : Finset ℕ) (ℓ : ℕ)
    (hP : ∀ p ∈ P, 0 < p) (hA : ∀ m ∈ A, 0 < m) :
    Continuous (fun t : ℝ => ‖(dirichletPoly c P ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
      dirichletPoly a A ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
  have h1 : Continuous (fun t : ℝ => dirichletPoly c P ((1 : ℂ) + (t : ℝ) * Complex.I)) :=
    continuous_dirichletPoly_mb c P hP
  have h2 : Continuous (fun t : ℝ => dirichletPoly a A ((1 : ℂ) + (t : ℝ) * Complex.I)) :=
    continuous_dirichletPoly_mb a A hA
  exact (h1.pow ℓ |>.mul h2).norm.pow 2

/-! ### Part 2: Norm Inequalities and Algebra -/

/-- Identity relating powers of 2 and 4. -/
lemma two_pow_two_mul (ℓ : ℕ) : (2 : ℝ) ^ (2 * ℓ) = (4 : ℝ) ^ ℓ := by
  calc (2 : ℝ) ^ (2 * ℓ) = ((2 : ℝ) ^ 2) ^ ℓ := by rw [pow_mul]
  _ = (4 : ℝ) ^ ℓ := by norm_num

/-- Elementary inequality `‖u + v‖² ≤ 2 (‖u‖² + ‖v‖²)`. -/
lemma norm_sq_add_le (u v : ℂ) : ‖u + v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have h1 : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
  have h2 : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    nlinarith [norm_nonneg (u + v), norm_nonneg u, norm_nonneg v]
  have h3 : (‖u‖ + ‖v‖) ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have : 0 ≤ (‖u‖ - ‖v‖) ^ 2 := sq_nonneg _
    linarith
  linarith

/-- Bound `‖u + v‖^(2ℓ) ≤ 4^ℓ (‖u‖^(2ℓ) + ‖v‖^(2ℓ))`. -/
lemma norm_pow_add_le (u v : ℂ) (ℓ : ℕ) :
    ‖u + v‖ ^ (2 * ℓ) ≤ (4 : ℝ) ^ ℓ * (‖u‖ ^ (2 * ℓ) + ‖v‖ ^ (2 * ℓ)) := by
  have h1 : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
  have h2 : ‖u‖ + ‖v‖ ≤ 2 * max ‖u‖ ‖v‖ := by
    have : ‖u‖ ≤ max ‖u‖ ‖v‖ := le_max_left _ _
    have : ‖v‖ ≤ max ‖u‖ ‖v‖ := le_max_right _ _
    linarith
  have h_nonneg : 0 ≤ ‖u + v‖ := norm_nonneg _
  have h_max_nonneg : 0 ≤ max ‖u‖ ‖v‖ := le_trans (norm_nonneg u) (le_max_left _ _)
  have h3 : ‖u + v‖ ≤ 2 * max ‖u‖ ‖v‖ := le_trans h1 h2
  have h4 : ‖u + v‖ ^ (2 * ℓ) ≤ (2 * max ‖u‖ ‖v‖) ^ (2 * ℓ) := by
    exact pow_le_pow_left₀ h_nonneg h3 _
  rw [mul_pow, two_pow_two_mul] at h4
  have h5 : (max ‖u‖ ‖v‖) ^ (2 * ℓ) ≤ ‖u‖ ^ (2 * ℓ) + ‖v‖ ^ (2 * ℓ) := by
    rcases le_total ‖u‖ ‖v‖ with h | h
    · rw [max_eq_right h]
      have : 0 ≤ ‖u‖ ^ (2 * ℓ) := by positivity
      linarith
    · rw [max_eq_left h]
      have : 0 ≤ ‖v‖ ^ (2 * ℓ) := by positivity
      linarith
  calc ‖u + v‖ ^ (2 * ℓ) ≤ (4 : ℝ) ^ ℓ * (max ‖u‖ ‖v‖) ^ (2 * ℓ) := h4
  _ ≤ (4 : ℝ) ^ ℓ * (‖u‖ ^ (2 * ℓ) + ‖v‖ ^ (2 * ℓ)) := by
    have : 0 ≤ (4 : ℝ) ^ ℓ := by positivity
    exact mul_le_mul_of_nonneg_left h5 this

/-- Pointwise norm bound for a 4-term decomposition of `(q₁ + q₂)^ℓ (a₁ + a₂)`. -/
lemma norm_pow_mul_norm_sq_le (q1 q2 a1 a2 : ℂ) (ℓ : ℕ) :
    ‖(q1 + q2) ^ ℓ * (a1 + a2)‖ ^ 2 ≤
      2 * (4 : ℝ) ^ ℓ * (‖q1 ^ ℓ * a1‖ ^ 2 + ‖q1 ^ ℓ * a2‖ ^ 2 +
                        ‖q2 ^ ℓ * a1‖ ^ 2 + ‖q2 ^ ℓ * a2‖ ^ 2) := by
  rw [norm_mul, mul_pow, norm_pow, show (‖q1 + q2‖ ^ ℓ) ^ 2 = ‖q1 + q2‖ ^ (2 * ℓ) by rw [← pow_mul, mul_comm]]
  have hq := norm_pow_add_le q1 q2 ℓ
  have ha := norm_sq_add_le a1 a2
  have h_prod : ‖q1 + q2‖ ^ (2 * ℓ) * ‖a1 + a2‖ ^ 2 ≤
      ((4 : ℝ) ^ ℓ * (‖q1‖ ^ (2 * ℓ) + ‖q2‖ ^ (2 * ℓ))) * (2 * (‖a1‖ ^ 2 + ‖a2‖ ^ 2)) := by
    have : 0 ≤ ‖q1 + q2‖ ^ (2 * ℓ) := by positivity
    have : 0 ≤ ‖a1 + a2‖ ^ 2 := by positivity
    nlinarith
  have h_id1 (q : ℂ) : ‖q‖ ^ (2 * ℓ) = ‖q ^ ℓ‖ ^ 2 := by
    rw [norm_pow, ← pow_mul, mul_comm]
  rw [h_id1 q1, h_id1 q2] at h_prod
  have h_id2 (q a : ℂ) : ‖q ^ ℓ‖ ^ 2 * ‖a‖ ^ 2 = ‖q ^ ℓ * a‖ ^ 2 := by
    rw [← mul_pow, ← norm_mul]
  calc ‖q1 + q2‖ ^ (2 * ℓ) * ‖a1 + a2‖ ^ 2
    _ ≤ ((4 : ℝ) ^ ℓ * (‖q1 ^ ℓ‖ ^ 2 + ‖q2 ^ ℓ‖ ^ 2)) * (2 * (‖a1‖ ^ 2 + ‖a2‖ ^ 2)) := h_prod
    _ = 2 * (4 : ℝ) ^ ℓ * (‖q1 ^ ℓ‖ ^ 2 * ‖a1‖ ^ 2 + ‖q1 ^ ℓ‖ ^ 2 * ‖a2‖ ^ 2 +
                          ‖q2 ^ ℓ‖ ^ 2 * ‖a1‖ ^ 2 + ‖q2 ^ ℓ‖ ^ 2 * ‖a2‖ ^ 2) := by ring
    _ = 2 * (4 : ℝ) ^ ℓ * (‖q1 ^ ℓ * a1‖ ^ 2 + ‖q1 ^ ℓ * a2‖ ^ 2 +
                          ‖q2 ^ ℓ * a1‖ ^ 2 + ‖q2 ^ ℓ * a2‖ ^ 2) := by
      rw [h_id2 q1 a1, h_id2 q1 a2, h_id2 q2 a1, h_id2 q2 a2]

/-! ### Part 3: Splitting Dirichlet Polynomials -/

/-- Splitting a Dirichlet polynomial into two ranges based on a threshold `K`. -/
lemma dirichletPoly_split_two {S P1 P2 : Finset ℕ} (K : ℕ)
    (hS1 : ∀ n ∈ S, n ≤ K → n ∈ P1)
    (hS2 : ∀ n ∈ S, K < n → n ∈ P2)
    (c : ℕ → ℂ) (s : ℂ) :
    let c1 := fun n => if n ∈ S ∧ n ≤ K then c n else 0
    let c2 := fun n => if n ∈ S ∧ K < n then c n else 0
    dirichletPoly c S s = dirichletPoly c1 P1 s + dirichletPoly c2 P2 s := by
  intro c1 c2
  have h_part : S = (S.filter (· ≤ K)) ∪ (S.filter (K < ·)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      by_cases h : x ≤ K
      · exact Or.inl ⟨hx, h⟩
      · have : K < x := by omega
        exact Or.inr ⟨hx, this⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have h_disj : Disjoint (S.filter (· ≤ K)) (S.filter (K < ·)) := by
    rw [Finset.disjoint_filter]
    intro x _hx _hle _hlt
    omega
  unfold dirichletPoly
  rw [h_part, Finset.sum_union h_disj]
  have h1 : ∑ n ∈ P1, c1 n * (n : ℂ) ^ (-s) = ∑ n ∈ S.filter (· ≤ K), c n * (n : ℂ) ^ (-s) := by
    have h_sub : S.filter (· ≤ K) ⊆ P1 := by
      intro x hx
      rw [Finset.mem_filter] at hx
      exact hS1 x hx.1 hx.2
    rw [← Finset.sum_subset h_sub]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_filter] at hx
      dsimp [c1]
      simp [hx.1, hx.2]
    · intro x _hx hnx
      dsimp [c1]
      have : ¬(x ∈ S ∧ x ≤ K) := by
        intro h
        apply hnx
        rw [Finset.mem_filter]
        exact h
      simp [this]
  have h2 : ∑ n ∈ P2, c2 n * (n : ℂ) ^ (-s) = ∑ n ∈ S.filter (K < ·), c n * (n : ℂ) ^ (-s) := by
    have h_sub : S.filter (K < ·) ⊆ P2 := by
      intro x hx
      rw [Finset.mem_filter] at hx
      exact hS2 x hx.1 hx.2
    rw [← Finset.sum_subset h_sub]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mem_filter] at hx
      dsimp [c2]
      simp [hx.1, hx.2]
    · intro x _hx hnx
      dsimp [c2]
      have : ¬(x ∈ S ∧ K < x) := by
        intro h
        apply hnx
        rw [Finset.mem_filter]
        exact h
      simp [this]
  rw [h1, h2]

/-- Coefficients extended by zero on a subcondition remain bounded by 1. -/
lemma norm_split_le_one {S : Finset ℕ} (P : ℕ → Prop) [DecidablePred P]
    (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (n : ℕ) :
    ‖if n ∈ S ∧ P n then c n else 0‖ ≤ 1 := by
  split_ifs
  · exact hc n
  · simp

/-! ### Part 4: Arithmetic and Floor/Ceil Estimates -/

/-- For real `y ≥ 1`, the ceiling is bounded by twice the floor. -/
lemma Nat_ceil_le_two_mul_floor {y : ℝ} (hy : 1 ≤ y) : ⌈y⌉₊ ≤ 2 * ⌊y⌋₊ := by
  have hy0 : 0 ≤ y := by linarith
  have _h1 : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by simpa using hy)
  have hceil : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy0
  have hfloor : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have h_lt : (⌈y⌉₊ : ℝ) < (⌊y⌋₊ : ℝ) + 2 := by linarith
  have _h_le : ⌈y⌉₊ < ⌊y⌋₊ + 2 := by exact_mod_cast h_lt
  omega

/-- Divisor monotonicity for natural division when `Y₁ ≤ 2 Y₂`. -/
lemma div_le_two_mul_div {X Y1 Y2 : ℕ} (hY1 : 0 < Y1) (hY : Y1 ≤ 2 * Y2) :
    X / Y2 ≤ 2 * X / Y1 := by
  have h1 : 2 * X / (2 * Y2) ≤ 2 * X / Y1 := Nat.div_le_div_left hY hY1
  have h2 : 2 * X / (2 * Y2) = X / Y2 := Nat.mul_div_mul_left X Y2 (by omega)
  omega

/-- Real lower bound implies natural division lower bound. -/
lemma nat_div_le_of_real_lt {X Y m : ℕ} {y : ℝ} (hy : 0 < y) (hyY : y ≤ (Y : ℝ))
    (hm : (X : ℝ) / y < (m : ℝ)) : X / Y ≤ m := by
  have h1 : ((X / Y : ℕ) : ℝ) ≤ (X : ℝ) / (Y : ℝ) := Nat.cast_div_le
  have h2 : (X : ℝ) / (Y : ℝ) ≤ (X : ℝ) / y := by
    have _hY_pos : 0 < (Y : ℝ) := by linarith
    exact div_le_div_of_nonneg_left (by positivity) hy hyY
  have h_lt : ((X / Y : ℕ) : ℝ) < (m : ℝ) := by linarith
  exact_mod_cast h_lt.le

/-- Real upper bound implies natural division upper bound. -/
lemma le_two_mul_div_of_real_le {X Y m : ℕ} {y : ℝ} (hY_pos : 0 < Y)
    (hYy : (Y : ℝ) ≤ y) (hm : (m : ℝ) ≤ 2 * (X : ℝ) / y) : m ≤ 2 * X / Y := by
  have _hy_pos : 0 < y := by
    have : 0 < (Y : ℝ) := by exact_mod_cast hY_pos
    linarith
  have h_le : (m : ℝ) ≤ 2 * (X : ℝ) / (Y : ℝ) := by
    calc (m : ℝ) ≤ 2 * (X : ℝ) / y := hm
    _ ≤ 2 * (X : ℝ) / (Y : ℝ) := div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hY_pos) hYy
  have h_mul : (m : ℝ) * (Y : ℝ) ≤ 2 * (X : ℝ) := by
    rwa [le_div_iff₀ (by exact_mod_cast hY_pos)] at h_le
  have h_nat : m * Y ≤ 2 * X := by exact_mod_cast h_mul
  exact Nat.le_div_iff_mul_le hY_pos |>.mpr h_nat

/-- Upper bound `exp(1 / Hi) ≤ 2` for `Hi ≥ 2`. -/
lemma exp_one_div_Hi_le_two {Hi : ℝ} (hHi : 2 ≤ Hi) :
    Real.exp (1 / Hi) ≤ 2 := by
  have h1 : 1 / Hi ≤ (1 / 2 : ℝ) := by
    have : 0 < Hi := by linarith
    rw [div_le_div_iff₀ this (by norm_num)]
    linarith
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h3 : 1 / Hi ≤ Real.log 2 := h1.trans h2
  have h4 : Real.exp (1 / Hi) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h3
  rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h4
  exact h4

/-- The upper prime boundary `exp((r+1)/Hi)` is at most `4 Y₁`. -/
lemma exp_r_add_one_div_Hi_le_four_Y1 {r : ℕ} {Hi : ℝ} (hHi : 2 ≤ Hi) (hrHi : 1 ≤ (r : ℝ) / Hi) :
    Real.exp (((r : ℝ) + 1) / Hi) ≤ 4 * (⌊Real.exp ((r : ℝ) / Hi)⌋₊ : ℝ) := by
  have h_exp_add : Real.exp (((r : ℝ) + 1) / Hi) =
      Real.exp ((r : ℝ) / Hi) * Real.exp (1 / Hi) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_exp_add]
  have _h_le2 : Real.exp (1 / Hi) ≤ 2 := exp_one_div_Hi_le_two hHi
  have _h_u_lt : Real.exp ((r : ℝ) / Hi) < (⌊Real.exp ((r : ℝ) / Hi)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have h_Y1_ge : 2 ≤ (⌊Real.exp ((r : ℝ) / Hi)⌋₊ : ℝ) := by
    have := Nat.le_floor (show (2 : ℝ) ≤ Real.exp ((r : ℝ) / Hi) from by
      calc (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      _ ≤ Real.exp ((r : ℝ) / Hi) := Real.exp_le_exp.mpr hrHi)
    exact_mod_cast this
  have _h_mul : Real.exp ((r : ℝ) / Hi) * Real.exp (1 / Hi) ≤
      ((⌊Real.exp ((r : ℝ) / Hi)⌋₊ : ℝ) + 1) * 2 := by
    have _hu_pos : 0 ≤ Real.exp ((r : ℝ) / Hi) := (Real.exp_pos _).le
    have _hu1_pos : 0 ≤ (⌊Real.exp ((r : ℝ) / Hi)⌋₊ : ℝ) + 1 := by linarith
    nlinarith
  have _h_arith : ((⌊Real.exp ((r : ℝ) / Hi)⌋₊ : ℝ) + 1) * 2 ≤ 4 * (⌊Real.exp ((r : ℝ) / Hi)⌋₊ : ℝ) := by
    linarith
  linarith

/-- Lower bound `exp(ℓ r / Hi) / 2^ℓ ≤ Y₁^ℓ`. -/
lemma Y1_pow_ge_exp_div_two_pow (r ℓ : ℕ) (Hi : ℝ) (hrHi : 1 ≤ (r : ℝ) / Hi) :
    Real.exp (ℓ * ((r : ℝ) / Hi)) / (2 : ℝ) ^ ℓ ≤ ((⌊Real.exp ((r : ℝ) / Hi)⌋₊ : ℝ)) ^ ℓ := by
  have _hu_two : (2 : ℝ) ≤ Real.exp ((r : ℝ) / Hi) := by
    calc (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    _ ≤ Real.exp ((r : ℝ) / Hi) := Real.exp_le_exp.mpr hrHi
  have _h_floor : Real.exp ((r : ℝ) / Hi) - 1 < (⌊Real.exp ((r : ℝ) / Hi)⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor _
  have h_half : Real.exp ((r : ℝ) / Hi) / 2 ≤ (⌊Real.exp ((r : ℝ) / Hi)⌋₊ : ℝ) := by linarith
  have h_nonneg : 0 ≤ Real.exp ((r : ℝ) / Hi) / 2 := by positivity
  have h_pow := pow_le_pow_left₀ h_nonneg h_half ℓ
  rw [div_pow, ← Real.exp_nat_mul] at h_pow
  exact h_pow

/-- Bound `T Y₂ / (X Y₁'^ℓ) ≤ 2^{ℓ+1} (T / X)`. -/
lemma T_mul_Y2_div_le (T : ℝ) (hT : 0 ≤ T) (X : ℕ) (_hX : 1 ≤ X) (Y2 : ℕ) (y : ℝ) (hy : 0 < y)
    (hY2 : (Y2 : ℝ) ≤ 2 * y) (Y1' ℓ : ℕ) (hY1' : y / (2 : ℝ) ^ ℓ ≤ (Y1' : ℝ) ^ ℓ) :
    T * (Y2 : ℝ) / ((X : ℝ) * (Y1' : ℝ) ^ ℓ) ≤ (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ)) := by
  have _hX_pos : 0 < (X : ℝ) := by positivity
  have hdenom_pos : 0 < (Y1' : ℝ) ^ ℓ := by
    have : 0 < y / (2 : ℝ) ^ ℓ := by positivity
    linarith
  have h_frac1 : (Y2 : ℝ) / (Y1' : ℝ) ^ ℓ ≤ (2 * y) / (Y1' : ℝ) ^ ℓ := by
    exact div_le_div_of_nonneg_right hY2 (le_of_lt hdenom_pos)
  have h_frac2 : (2 * y) / (Y1' : ℝ) ^ ℓ ≤ (2 * y) / (y / (2 : ℝ) ^ ℓ) := by
    have : 0 ≤ 2 * y := by positivity
    exact div_le_div_of_nonneg_left this (by positivity) hY1'
  have h_frac : (Y2 : ℝ) / (Y1' : ℝ) ^ ℓ ≤ (2 * y) / (y / (2 : ℝ) ^ ℓ) := h_frac1.trans h_frac2
  have h_cancel : (2 * y) / (y / (2 : ℝ) ^ ℓ) = (2 : ℝ) ^ (ℓ + 1) := by
    rw [pow_add, pow_one]
    field_simp
  rw [h_cancel] at h_frac
  calc T * (Y2 : ℝ) / ((X : ℝ) * (Y1' : ℝ) ^ ℓ)
    _ = (T / (X : ℝ)) * ((Y2 : ℝ) / (Y1' : ℝ) ^ ℓ) := by ring
    _ ≤ (T / (X : ℝ)) * (2 : ℝ) ^ (ℓ + 1) := by
      have : 0 ≤ T / (X : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left h_frac this
    _ = (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ)) := by ring

/-- Linear combination of four bounded integrals. -/
lemma integral_four_terms_le {f1 f2 f3 f4 : ℝ → ℝ} {T : ℝ} (_hT : 0 ≤ T)
    (h1 : IntervalIntegrable f1 MeasureTheory.volume (-T) T)
    (h2 : IntervalIntegrable f2 MeasureTheory.volume (-T) T)
    (h3 : IntervalIntegrable f3 MeasureTheory.volume (-T) T)
    (h4 : IntervalIntegrable f4 MeasureTheory.volume (-T) T)
    {B : ℝ} (hB1 : ∫ t in (-T)..T, f1 t ≤ B) (hB2 : ∫ t in (-T)..T, f2 t ≤ B)
    (hB3 : ∫ t in (-T)..T, f3 t ≤ B) (hB4 : ∫ t in (-T)..T, f4 t ≤ B) (ℓ : ℕ) :
    (∫ t in (-T)..T, 2 * (4 : ℝ) ^ ℓ * (f1 t + f2 t + f3 t + f4 t)) ≤
      8 * (4 : ℝ) ^ ℓ * B := by
  have hint12 : IntervalIntegrable (fun t => f1 t + f2 t) MeasureTheory.volume (-T) T := h1.add h2
  have hint123 : IntervalIntegrable (fun t => f1 t + f2 t + f3 t) MeasureTheory.volume (-T) T := hint12.add h3
  have hint1234 : IntervalIntegrable (fun t => f1 t + f2 t + f3 t + f4 t) MeasureTheory.volume (-T) T := hint123.add h4
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_add hint123 h4]
  rw [intervalIntegral.integral_add hint12 h3]
  rw [intervalIntegral.integral_add h1 h2]
  have h_sum : (∫ t in (-T)..T, f1 t) + (∫ t in (-T)..T, f2 t) +
      (∫ t in (-T)..T, f3 t) + (∫ t in (-T)..T, f4 t) ≤ 4 * B := by linarith
  have h_nonneg : 0 ≤ 2 * (4 : ℝ) ^ ℓ := by positivity
  calc 2 * (4 : ℝ) ^ ℓ * ((∫ t in (-T)..T, f1 t) + (∫ t in (-T)..T, f2 t) +
          (∫ t in (-T)..T, f3 t) + (∫ t in (-T)..T, f4 t))
    _ ≤ 2 * (4 : ℝ) ^ ℓ * (4 * B) := mul_le_mul_of_nonneg_left h_sum h_nonneg
    _ = 8 * (4 : ℝ) ^ ℓ * B := by ring

/-- Bounds on elements of `cofactorRange`. -/
lemma mem_cofactor_bounds {X : ℕ} {H : ℝ} {v m : ℕ} (hm : m ∈ cofactorRange X H v) :
    0 < m ∧ (m : ℝ) ≤ 2 * (X : ℝ) / Real.exp ((v : ℝ) / H) ∧
    (X : ℝ) / Real.exp ((v : ℝ) / H) < (m : ℝ) := by
  unfold cofactorRange at hm
  rw [Finset.mem_filter, Finset.mem_Ioc] at hm
  rcases hm with ⟨⟨hm_pos, hm_floor⟩, hm_lt⟩
  have h_exp_neg : Real.exp (-(v / H)) = 1 / Real.exp ((v : ℝ) / H) := by
    rw [Real.exp_neg, one_div]
  have h_floor_le : (⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊ : ℝ) ≤
      2 * (X : ℝ) * Real.exp (-(v / H)) := Nat.floor_le (by positivity)
  have hm_le_real : (m : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(v / H)) := by
    exact (show (m : ℝ) ≤ (⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊ : ℝ) by exact_mod_cast hm_floor).trans h_floor_le
  have h1 : 2 * (X : ℝ) * Real.exp (-(v / H)) = 2 * (X : ℝ) / Real.exp ((v : ℝ) / H) := by
    rw [h_exp_neg]
    ring
  have h2 : (X : ℝ) * Real.exp (-(v / H)) = (X : ℝ) / Real.exp ((v : ℝ) / H) := by
    rw [h_exp_neg]
    ring
  refine ⟨hm_pos, ?_, ?_⟩
  · rwa [← h1]
  · rwa [← h2]

/-- The elements of `cofactorRange` are covered by two dyadic-type ranges. -/
lemma cofactor_split_cases (X : ℕ) (H : ℝ) (v : ℕ) (_hH : 1 ≤ H)
    (m : ℕ) (hm : m ∈ cofactorRange X H v) :
    let y := Real.exp ((v : ℝ) / H)
    let Y21 := ⌈y⌉₊
    let Y22 := ⌊y⌋₊
    (m ≤ 2 * X / Y21 → m ∈ (Finset.Ioc 0 (2 * X / Y21)).filter (fun k => X / Y21 ≤ k)) ∧
    (2 * X / Y21 < m → m ∈ (Finset.Ioc 0 (2 * X / Y22)).filter (fun k => X / Y22 ≤ k)) := by
  intro y Y21 Y22
  have hy1 : 1 ≤ y := by
    have : 0 ≤ (v : ℝ) / H := by positivity
    calc 1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp ((v : ℝ) / H) := Real.exp_le_exp.mpr this
  have hY22_pos : 0 < Y22 := by
    have : 1 ≤ Y22 := Nat.le_floor (by simpa using hy1)
    omega
  have hY21_pos : 0 < Y21 := by
    have : Y22 ≤ Y21 := Nat.floor_le_ceil y
    omega
  have hm_bounds := mem_cofactor_bounds hm
  constructor
  · intro hle
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨hm_bounds.1, hle⟩, ?_⟩
    exact nat_div_le_of_real_lt (by positivity) (Nat.le_ceil y) hm_bounds.2.2
  · intro hlt
    rw [Finset.mem_filter, Finset.mem_Ioc]
    have h_le_div := le_two_mul_div_of_real_le hY22_pos (Nat.floor_le (by positivity)) hm_bounds.2.1
    refine ⟨⟨hm_bounds.1, h_le_div⟩, ?_⟩
    have h_ceil_floor := Nat_ceil_le_two_mul_floor hy1
    have h_div_div := div_le_two_mul_div hY21_pos h_ceil_floor (X := X)
    dsimp [Y21, Y22] at *
    omega

/-- The elements of `shortPrimeRange` are covered by two dyadic prime ranges. -/
lemma prime_split_cases (Pi Qi : ℕ) (Hi : ℝ) (r : ℕ) (hHi : 2 ≤ Hi) (hrHi : 1 ≤ (r : ℝ) / Hi)
    (p : ℕ) (hp : p ∈ shortPrimeRange Pi Qi Hi r) :
    let u := Real.exp ((r : ℝ) / Hi)
    let Y1 := ⌊u⌋₊
    (p ≤ 2 * Y1 → p ∈ (Finset.Icc Y1 (2 * Y1)).filter Nat.Prime) ∧
    (2 * Y1 < p → p ∈ (Finset.Icc (2 * Y1) (2 * (2 * Y1))).filter Nat.Prime) := by
  intro u Y1
  rw [mem_shortPrimeRange] at hp
  rcases hp with ⟨⟨hp_prime, _⟩, hp_u, hp_lt⟩
  have hY1_le_p : Y1 ≤ p := Nat.floor_le_of_le hp_u
  have h_four_Y1 : (p : ℝ) < 4 * (Y1 : ℝ) := by
    have h_le := exp_r_add_one_div_Hi_le_four_Y1 hHi hrHi
    exact hp_lt.trans_le h_le
  have hp_le_four_Y1 : p ≤ 2 * (2 * Y1) := by
    have h_lt : (p : ℝ) < ((4 * Y1 : ℕ) : ℝ) := by
      push_cast
      exact h_four_Y1
    have : p < 4 * Y1 := by exact_mod_cast h_lt
    omega
  constructor
  · intro hle
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hY1_le_p, hle⟩, hp_prime⟩
  · intro hlt
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hlt.le, hp_le_four_Y1⟩, hp_prime⟩

/-- Monotonicity helper for bracket multiplication by non-negative factorials. -/
lemma mul_bracket_fact_le {C13 bracket bound fact : ℝ}
    (hC : 0 ≤ C13) (h_br : bracket ≤ bound) (h_fact : 0 ≤ fact) :
    C13 * bracket * fact ≤ C13 * bound * fact := by
  have : C13 * bracket ≤ C13 * bound := mul_le_mul_of_nonneg_left h_br hC
  exact mul_le_mul_of_nonneg_right this h_fact

/-! ### Part 5: Main Theorem: Lemma 13 Bridge -/

/-- Bridge from Lemma 13 (dyadic moment computation) to short prime and cofactor ranges. -/
theorem integral_norm_sq_shortPrimePoly_pow_mul_cofactor_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X _P _Q Pi Qi : ℕ) (H Hi : ℝ) (v r ℓ : ℕ) (c a : ℕ → ℂ) (T : ℝ),
      1 ≤ X → 1 ≤ H → 2 ≤ Hi → 1 ≤ ℓ → 0 ≤ T → 1 ≤ (r : ℝ) / Hi → (v : ℝ) / H ≤ ℓ * ((r : ℝ) / Hi) →
      Real.exp ((v : ℝ) / H) + 1 ≤ X → (∀ p, ‖c p‖ ≤ 1) → (∀ m, ‖a m‖ ≤ 1) →
      ∫ t in (-T)..T, ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
          dirichletPoly a (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (T / X + Real.exp ((r : ℝ) / Hi)) * (8 : ℝ) ^ ℓ * (((ℓ + 1).factorial : ℝ)) ^ 2 := by
  obtain ⟨C13, hC13_pos, hC13⟩ := integral_norm_sq_prime_poly_pow_mul_le_general
  refine ⟨16 * C13, by positivity, ?_⟩
  intro X _P _Q Pi Qi H Hi v r ℓ c a T hX hH hHi hℓ hT hrHi hvH hexp hc ha
  let u := Real.exp ((r : ℝ) / Hi)
  let y := Real.exp ((v : ℝ) / H)
  let Y1 := ⌊u⌋₊
  let Y21 := ⌈y⌉₊
  let Y22 := ⌊y⌋₊

  have hu_two : (2 : ℝ) ≤ u := by
    calc (2 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    _ ≤ Real.exp ((r : ℝ) / Hi) := Real.exp_le_exp.mpr hrHi

  have hY1_ge2 : 2 ≤ Y1 := Nat.le_floor hu_two
  have h2Y1_ge2 : 2 ≤ 2 * Y1 := by linarith [hY1_ge2]

  have hy1 : 1 ≤ y := by
    have : 0 ≤ (v : ℝ) / H := by positivity
    calc 1 = Real.exp 0 := Real.exp_zero.symm
    _ ≤ Real.exp ((v : ℝ) / H) := Real.exp_le_exp.mpr this

  have hY22_ge1 : 1 ≤ Y22 := Nat.le_floor (by simpa using hy1)
  have hY21_ge1 : 1 ≤ Y21 := hY22_ge1.trans (Nat.floor_le_ceil y)

  have hY21_le_X : Y21 ≤ X := by
    have : y ≤ (X : ℝ) := by linarith
    exact Nat.ceil_le.mpr this

  have hY22_le_X : Y22 ≤ X := by
    have : Y22 ≤ Y21 := Nat.floor_le_ceil y
    exact this.trans hY21_le_X

  let SP := shortPrimeRange Pi Qi Hi r
  let SA := cofactorRange X H v

  let P1 := (Finset.Icc Y1 (2 * Y1)).filter Nat.Prime
  let P2 := (Finset.Icc (2 * Y1) (2 * (2 * Y1))).filter Nat.Prime

  let A1 := (Finset.Ioc 0 (2 * X / Y21)).filter (fun m => X / Y21 ≤ m)
  let A2 := (Finset.Ioc 0 (2 * X / Y22)).filter (fun m => X / Y22 ≤ m)

  let c1 := fun p => if p ∈ SP ∧ p ≤ 2 * Y1 then c p else 0
  let c2 := fun p => if p ∈ SP ∧ 2 * Y1 < p then c p else 0

  let a1 := fun m => if m ∈ SA ∧ m ≤ 2 * X / Y21 then a m else 0
  let a2 := fun m => if m ∈ SA ∧ 2 * X / Y21 < m then a m else 0

  have hP1_pos : ∀ p ∈ P1, 0 < p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    omega
  have hP2_pos : ∀ p ∈ P2, 0 < p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    omega
  have hA1_pos : ∀ m ∈ A1, 0 < m := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    exact hm.1.1
  have hA2_pos : ∀ m ∈ A2, 0 < m := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    exact hm.1.1
  have hSP_pos : ∀ p ∈ SP, 0 < p := by
    intro p hp
    rw [mem_shortPrimeRange] at hp
    exact hp.1.1.pos
  have hSA_pos : ∀ m ∈ SA, 0 < m := by
    intro m hm
    exact (mem_cofactor_bounds hm).1

  have hP_cases := prime_split_cases Pi Qi Hi r hHi hrHi
  have hA_cases := cofactor_split_cases X H v hH

  have hQ_split (t : ℝ) :
      dirichletPoly c SP ((1 : ℂ) + (t : ℝ) * Complex.I) =
      dirichletPoly c1 P1 ((1 : ℂ) + (t : ℝ) * Complex.I) +
      dirichletPoly c2 P2 ((1 : ℂ) + (t : ℝ) * Complex.I) := by
    exact dirichletPoly_split_two (2 * Y1) (fun p hp hle => (hP_cases p hp).1 hle)
      (fun p hp hlt => (hP_cases p hp).2 hlt) c ((1 : ℂ) + (t : ℝ) * Complex.I)

  have hA_split (t : ℝ) :
      dirichletPoly a SA ((1 : ℂ) + (t : ℝ) * Complex.I) =
      dirichletPoly a1 A1 ((1 : ℂ) + (t : ℝ) * Complex.I) +
      dirichletPoly a2 A2 ((1 : ℂ) + (t : ℝ) * Complex.I) := by
    exact dirichletPoly_split_two (2 * X / Y21) (fun m hm hle => (hA_cases m hm).1 hle)
      (fun m hm hlt => (hA_cases m hm).2 hlt) a ((1 : ℂ) + (t : ℝ) * Complex.I)

  have h_pointwise (t : ℝ) :
      ‖(dirichletPoly c SP ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
          dirichletPoly a SA ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
        2 * (4 : ℝ) ^ ℓ *
          (‖(dirichletPoly c1 P1 ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
              dirichletPoly a1 A1 ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 +
           ‖(dirichletPoly c1 P1 ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
              dirichletPoly a2 A2 ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 +
           ‖(dirichletPoly c2 P2 ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
              dirichletPoly a1 A1 ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 +
           ‖(dirichletPoly c2 P2 ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
              dirichletPoly a2 A2 ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) := by
    rw [hQ_split t, hA_split t]
    exact norm_pow_mul_norm_sq_le _ _ _ _ ℓ

  let f := fun t : ℝ => ‖(dirichletPoly c SP ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
      dirichletPoly a SA ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
  let f1 := fun t : ℝ => ‖(dirichletPoly c1 P1 ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
      dirichletPoly a1 A1 ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
  let f2 := fun t : ℝ => ‖(dirichletPoly c1 P1 ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
      dirichletPoly a2 A2 ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
  let f3 := fun t : ℝ => ‖(dirichletPoly c2 P2 ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
      dirichletPoly a1 A1 ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
  let f4 := fun t : ℝ => ‖(dirichletPoly c2 P2 ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
      dirichletPoly a2 A2 ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2

  have hf_cont : Continuous f := continuous_norm_sq_dirichletPoly_pow_mul c a SP SA ℓ hSP_pos hSA_pos
  have hf1_cont : Continuous f1 := continuous_norm_sq_dirichletPoly_pow_mul c1 a1 P1 A1 ℓ hP1_pos hA1_pos
  have hf2_cont : Continuous f2 := continuous_norm_sq_dirichletPoly_pow_mul c1 a2 P1 A2 ℓ hP1_pos hA2_pos
  have hf3_cont : Continuous f3 := continuous_norm_sq_dirichletPoly_pow_mul c2 a1 P2 A1 ℓ hP2_pos hA1_pos
  have hf4_cont : Continuous f4 := continuous_norm_sq_dirichletPoly_pow_mul c2 a2 P2 A2 ℓ hP2_pos hA2_pos

  have hf_int : IntervalIntegrable f MeasureTheory.volume (-T) T := hf_cont.intervalIntegrable (-T) T
  have hf1_int : IntervalIntegrable f1 MeasureTheory.volume (-T) T := hf1_cont.intervalIntegrable (-T) T
  have hf2_int : IntervalIntegrable f2 MeasureTheory.volume (-T) T := hf2_cont.intervalIntegrable (-T) T
  have hf3_int : IntervalIntegrable f3 MeasureTheory.volume (-T) T := hf3_cont.intervalIntegrable (-T) T
  have hf4_int : IntervalIntegrable f4 MeasureTheory.volume (-T) T := hf4_cont.intervalIntegrable (-T) T

  have hg_int : IntervalIntegrable (fun t => 2 * (4 : ℝ) ^ ℓ * (f1 t + f2 t + f3 t + f4 t))
      MeasureTheory.volume (-T) T := by
    have h12 : IntervalIntegrable (fun t => f1 t + f2 t) MeasureTheory.volume (-T) T := hf1_int.add hf2_int
    have h123 : IntervalIntegrable (fun t => f1 t + f2 t + f3 t) MeasureTheory.volume (-T) T := h12.add hf3_int
    have h1234 : IntervalIntegrable (fun t => f1 t + f2 t + f3 t + f4 t) MeasureTheory.volume (-T) T := h123.add hf4_int
    exact h1234.const_mul (2 * (4 : ℝ) ^ ℓ)

  have h_mono : (∫ t in (-T)..T, f t) ≤ ∫ t in (-T)..T, 2 * (4 : ℝ) ^ ℓ * (f1 t + f2 t + f3 t + f4 t) := by
    have hle : -T ≤ T := by linarith
    apply intervalIntegral.integral_mono_on hle hf_int hg_int
    intro t _ht
    exact h_pointwise t

  have hc1 : ∀ p, ‖c1 p‖ ≤ 1 := norm_split_le_one _ c hc
  have hc2 : ∀ p, ‖c2 p‖ ≤ 1 := norm_split_le_one _ c hc
  have ha1 : ∀ m, ‖a1 m‖ ≤ 1 := norm_split_le_one _ a ha
  have ha2 : ∀ m, ‖a2 m‖ ≤ 1 := norm_split_le_one _ a ha

  have hy_pos : 0 < y := by positivity
  have _htwo_pow_pos : 0 < (2 : ℝ) ^ ℓ := by positivity

  have hy_div_two_pow_le_Y1 : y / (2 : ℝ) ^ ℓ ≤ (Y1 : ℝ) ^ ℓ := by
    have h_pow := Y1_pow_ge_exp_div_two_pow r ℓ Hi hrHi
    have h_y_le : y ≤ Real.exp (ℓ * ((r : ℝ) / Hi)) := by
      dsimp [y]
      exact Real.exp_le_exp.mpr hvH
    have : y / (2 : ℝ) ^ ℓ ≤ Real.exp (ℓ * ((r : ℝ) / Hi)) / (2 : ℝ) ^ ℓ := by
      exact div_le_div_of_nonneg_right h_y_le (by positivity)
    exact this.trans h_pow

  have hy_div_two_pow_le_2Y1 : y / (2 : ℝ) ^ ℓ ≤ ((2 * Y1 : ℕ) : ℝ) ^ ℓ := by
    have : (Y1 : ℝ) ≤ ((2 * Y1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h_le := pow_le_pow_left₀ (by positivity) this ℓ
    exact hy_div_two_pow_le_Y1.trans h_le

  have hY21_le_2y : (Y21 : ℝ) ≤ 2 * y := by
    have : (Y21 : ℝ) < y + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith

  have hY22_le_2y : (Y22 : ℝ) ≤ 2 * y := by
    have : (Y22 : ℝ) ≤ y := Nat.floor_le (by positivity)
    linarith

  have _hY1_le_u : (Y1 : ℝ) ≤ u := Nat.floor_le (by positivity)
  have _h2Y1_le_2u : ((2 * Y1 : ℕ) : ℝ) ≤ 2 * u := by
    push_cast
    linarith

  have h_bound_Y1_Y21 : T * (Y21 : ℝ) / ((X : ℝ) * (Y1 : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y1 : ℝ) ≤
      (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ) + u) := by
    have h1 := T_mul_Y2_div_le T hT X hX Y21 y hy_pos hY21_le_2y Y1 ℓ hy_div_two_pow_le_Y1
    have _h2 : (2 : ℝ) ^ ℓ * (Y1 : ℝ) ≤ (2 : ℝ) ^ (ℓ + 1) * u := by
      have : (2 : ℝ) ^ (ℓ + 1) = 2 * (2 : ℝ) ^ ℓ := by rw [pow_add, pow_one]; ring
      rw [this]
      nlinarith
    calc T * (Y21 : ℝ) / ((X : ℝ) * (Y1 : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y1 : ℝ)
      _ ≤ (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ)) + (2 : ℝ) ^ (ℓ + 1) * u := by linarith
      _ = (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ) + u) := by ring

  have h_bound_Y1_Y22 : T * (Y22 : ℝ) / ((X : ℝ) * (Y1 : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y1 : ℝ) ≤
      (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ) + u) := by
    have h1 := T_mul_Y2_div_le T hT X hX Y22 y hy_pos hY22_le_2y Y1 ℓ hy_div_two_pow_le_Y1
    have _h2 : (2 : ℝ) ^ ℓ * (Y1 : ℝ) ≤ (2 : ℝ) ^ (ℓ + 1) * u := by
      have : (2 : ℝ) ^ (ℓ + 1) = 2 * (2 : ℝ) ^ ℓ := by rw [pow_add, pow_one]; ring
      rw [this]
      nlinarith
    calc T * (Y22 : ℝ) / ((X : ℝ) * (Y1 : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y1 : ℝ)
      _ ≤ (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ)) + (2 : ℝ) ^ (ℓ + 1) * u := by linarith
      _ = (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ) + u) := by ring

  have h_bound_2Y1_Y21 : T * (Y21 : ℝ) / ((X : ℝ) * ((2 * Y1 : ℕ) : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * ((2 * Y1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ) + u) := by
    have h1 := T_mul_Y2_div_le T hT X hX Y21 y hy_pos hY21_le_2y (2 * Y1) ℓ hy_div_two_pow_le_2Y1
    have _h2 : (2 : ℝ) ^ ℓ * ((2 * Y1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ℓ + 1) * u := by
      have : (2 : ℝ) ^ (ℓ + 1) = (2 : ℝ) ^ ℓ * 2 := by rw [pow_add, pow_one]
      rw [this]
      have : 0 ≤ (2 : ℝ) ^ ℓ := by positivity
      nlinarith
    calc T * (Y21 : ℝ) / ((X : ℝ) * ((2 * Y1 : ℕ) : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * ((2 * Y1 : ℕ) : ℝ)
      _ ≤ (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ)) + (2 : ℝ) ^ (ℓ + 1) * u := by linarith
      _ = (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ) + u) := by ring

  have h_bound_2Y1_Y22 : T * (Y22 : ℝ) / ((X : ℝ) * ((2 * Y1 : ℕ) : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * ((2 * Y1 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ) + u) := by
    have h1 := T_mul_Y2_div_le T hT X hX Y22 y hy_pos hY22_le_2y (2 * Y1) ℓ hy_div_two_pow_le_2Y1
    have _h2 : (2 : ℝ) ^ ℓ * ((2 * Y1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ℓ + 1) * u := by
      have : (2 : ℝ) ^ (ℓ + 1) = (2 : ℝ) ^ ℓ * 2 := by rw [pow_add, pow_one]
      rw [this]
      have : 0 ≤ (2 : ℝ) ^ ℓ := by positivity
      nlinarith
    calc T * (Y22 : ℝ) / ((X : ℝ) * ((2 * Y1 : ℕ) : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * ((2 * Y1 : ℕ) : ℝ)
      _ ≤ (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ)) + (2 : ℝ) ^ (ℓ + 1) * u := by linarith
      _ = (2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ) + u) := by ring

  let B := C13 * ((2 : ℝ) ^ (ℓ + 1) * (T / (X : ℝ) + u)) * (((ℓ + 1).factorial : ℝ) ^ 2)

  have h_l13_1 := hC13 Y1 Y21 X c1 a1 T ℓ hY1_ge2 hY21_ge1 hY21_le_X hT hℓ hc1 ha1
  have hB1 : ∫ t in (-T)..T, f1 t ≤ B := by
    refine h_l13_1.trans ?_
    exact mul_bracket_fact_le hC13_pos.le h_bound_Y1_Y21 (by positivity)

  have h_l13_2 := hC13 Y1 Y22 X c1 a2 T ℓ hY1_ge2 hY22_ge1 hY22_le_X hT hℓ hc1 ha2
  have hB2 : ∫ t in (-T)..T, f2 t ≤ B := by
    refine h_l13_2.trans ?_
    exact mul_bracket_fact_le hC13_pos.le h_bound_Y1_Y22 (by positivity)

  have h_l13_3 := hC13 (2 * Y1) Y21 X c2 a1 T ℓ h2Y1_ge2 hY21_ge1 hY21_le_X hT hℓ hc2 ha1
  have hB3 : ∫ t in (-T)..T, f3 t ≤ B := by
    refine h_l13_3.trans ?_
    exact mul_bracket_fact_le hC13_pos.le h_bound_2Y1_Y21 (by positivity)

  have h_l13_4 := hC13 (2 * Y1) Y22 X c2 a2 T ℓ h2Y1_ge2 hY22_ge1 hY22_le_X hT hℓ hc2 ha2
  have hB4 : ∫ t in (-T)..T, f4 t ≤ B := by
    refine h_l13_4.trans ?_
    exact mul_bracket_fact_le hC13_pos.le h_bound_2Y1_Y22 (by positivity)

  have h_four := integral_four_terms_le hT hf1_int hf2_int hf3_int hf4_int hB1 hB2 hB3 hB4 ℓ

  have h_final_bound : 8 * (4 : ℝ) ^ ℓ * B =
      (16 * C13) * (T / (X : ℝ) + u) * (8 : ℝ) ^ ℓ * (((ℓ + 1).factorial : ℝ) ^ 2) := by
    dsimp [B]
    have h_pow_eight : (4 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ = (8 : ℝ) ^ ℓ := by
      rw [← mul_pow]
      norm_num
    have h_two_pow_succ : (2 : ℝ) ^ (ℓ + 1) = (2 : ℝ) ^ ℓ * 2 := by
      rw [pow_add, pow_one]
    rw [h_two_pow_succ]
    calc 8 * (4 : ℝ) ^ ℓ * (C13 * ((2 : ℝ) ^ ℓ * 2 * (T / (X : ℝ) + u)) * (((ℓ + 1).factorial : ℝ) ^ 2))
      _ = (16 * C13) * (T / (X : ℝ) + u) * ((4 : ℝ) ^ ℓ * (2 : ℝ) ^ ℓ) * (((ℓ + 1).factorial : ℝ) ^ 2) := by ring
      _ = (16 * C13) * (T / (X : ℝ) + u) * (8 : ℝ) ^ ℓ * (((ℓ + 1).factorial : ℝ) ^ 2) := by rw [h_pow_eight]

  rw [h_final_bound] at h_four
  exact h_mono.trans h_four

end Erdos1201.MR
