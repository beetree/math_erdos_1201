import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Discrete Kusmin–Landau Lemma

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the discrete Kusmin–Landau lemma (Graham–Kolesnik, Theorem 2.1,
discrete form; Montgomery, Ten Lectures, Lemma 3.1) bounding exponential sums with monotone
first differences:
`‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ))‖ ≤ 1 / δ + 1`.
When `a < b`, the condition `δ ≤ |g (a+1) - g a| ≤ 1/2` forces `δ ≤ 1/2`, yielding the
classical bound `3 / δ`.
-/

open Real Complex Finset

namespace Erdos1201.MR

/-- Jordan's inequality: `4 * y ≤ 2 * sin (π * y)` for `0 ≤ y ≤ 1 / 2`. -/
lemma four_mul_le_two_mul_sin_pi_mul {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    4 * y ≤ 2 * Real.sin (Real.pi * y) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : 0 ≤ Real.pi * y := mul_nonneg hpi.le hy0
  have h2 : Real.pi * y ≤ Real.pi / 2 := by nlinarith [hpi]
  have hsin := Real.mul_le_sin h1 h2
  have hcancel : 2 / Real.pi * (Real.pi * y) = 2 * y := by
    calc 2 / Real.pi * (Real.pi * y) = (2 / Real.pi * Real.pi) * y := by ring
    _ = 2 * y := by rw [div_mul_cancel₀ 2 hpi.ne']
  linarith

/-- Double-angle formula: `cos (2 * π * x) = 1 - 2 * sin (π * x)^2`. -/
lemma cos_two_pi_mul (x : ℝ) :
    Real.cos (2 * Real.pi * x) = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
  have harg : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
  rw [harg]
  have hcos := Real.cos_two_mul (Real.pi * x)
  have hsin := Real.sin_sq (Real.pi * x)
  linarith

/-- Complex exponential `exp(2 * π * I * x)` decomposed into real and imaginary parts. -/
lemma exp_two_pi_I_eq (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) =
      ((Real.cos (2 * Real.pi * x) : ℝ) : ℂ) + Complex.I * ((Real.sin (2 * Real.pi * x) : ℝ) : ℂ) := by
  have : 2 * Real.pi * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I]
  ring

/-- Real part of `exp(2 * π * I * x)`. -/
lemma exp_two_pi_I_mul_re (x : ℝ) :
    (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))).re = Real.cos (2 * Real.pi * x) := by
  have : 2 * Real.pi * Complex.I * (x : ℂ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]

/-- The complex exponential on the real axis has unit norm. -/
lemma norm_exp_two_pi_I_mul (x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))‖ = 1 := by
  have : 2 * Real.pi * Complex.I * (x : ℂ) = Complex.I * ((2 * Real.pi * x : ℝ) : ℂ) := by
    push_cast; ring
  rw [this]
  exact Complex.norm_exp_I_mul_ofReal (2 * Real.pi * x)

/-- Squared norm of `exp(2 * π * I * x) - 1`. -/
lemma normSq_exp_two_pi_I_sub_one_eq (x : ℝ) :
    Complex.normSq (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1) =
      (2 * |Real.sin (Real.pi * x)|) ^ 2 := by
  let z := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))
  have hz_norm : ‖z‖ = 1 := norm_exp_two_pi_I_mul x
  have hz_normSq : Complex.normSq z = 1 := by
    have := Complex.normSq_eq_norm_sq z
    rw [hz_norm] at this
    linarith
  have hsub := Complex.normSq_sub z 1
  simp only [map_one, mul_one] at hsub
  rw [hz_normSq, exp_two_pi_I_mul_re, cos_two_pi_mul] at hsub
  have habs : (2 * |Real.sin (Real.pi * x)|) ^ 2 = 4 * Real.sin (Real.pi * x) ^ 2 := by
    calc (2 * |Real.sin (Real.pi * x)|) ^ 2 = 4 * |Real.sin (Real.pi * x)| ^ 2 := by ring
    _ = 4 * Real.sin (Real.pi * x) ^ 2 := by rw [sq_abs]
  linarith

/-- The norm `‖exp(2 * π * I * x) - 1‖` equals `2 * |sin(π * x)|`. -/
lemma norm_exp_two_pi_I_sub_one (x : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1‖ = 2 * |Real.sin (Real.pi * x)| := by
  have hsq : ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1‖ ^ 2 =
      (2 * |Real.sin (Real.pi * x)|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_exp_two_pi_I_sub_one_eq]
  have h1 : 0 ≤ ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1‖ := norm_nonneg _
  have h2 : 0 ≤ 2 * |Real.sin (Real.pi * x)| := by positivity
  nlinarith

/-- Reciprocal difference bound: `‖1 / (exp(2 * π * I * d) - 1)‖ ≤ 1 / (4 * δ)`. -/
lemma norm_one_div_exp_two_pi_I_sub_one_le {d δ : ℝ} (hδ : 0 < δ)
    (hd_neg : d < 0) (hlow : δ ≤ |d|) (hhalf : |d| ≤ 1 / 2) :
    ‖1 / (Complex.exp (2 * Real.pi * Complex.I * (d : ℂ)) - 1)‖ ≤ 1 / (4 * δ) := by
  have hyd0 : 0 ≤ |d| := by positivity
  have hsin_ge := four_mul_le_two_mul_sin_pi_mul hyd0 hhalf
  have hsin_abs : |Real.sin (Real.pi * d)| = Real.sin (Real.pi * |d|) := by
    have hd_eq : |d| = -d := abs_of_neg hd_neg
    have hd_ge : - (1 / 2 : ℝ) ≤ d := by
      have : -|d| = d := by linarith
      linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : -Real.pi < Real.pi * d := by nlinarith [hpi]
    have h2 : Real.pi * d < 0 := by nlinarith [hpi]
    have hsin_neg := Real.sin_neg_of_neg_of_neg_pi_lt h2 h1
    rw [abs_of_neg hsin_neg]
    have : Real.pi * |d| = -(Real.pi * d) := by rw [hd_eq]; ring
    rw [this, Real.sin_neg]
  have hnorm_sub : ‖Complex.exp (2 * Real.pi * Complex.I * (d : ℂ)) - 1‖ =
      2 * Real.sin (Real.pi * |d|) := by
    rw [norm_exp_two_pi_I_sub_one, hsin_abs]
  have hdenom_ge : 4 * δ ≤ ‖Complex.exp (2 * Real.pi * Complex.I * (d : ℂ)) - 1‖ := by
    rw [hnorm_sub]
    have : 4 * δ ≤ 4 * |d| := by linarith
    linarith
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le (by linarith) hdenom_ge

/-- Auxiliary algebraic identity for reciprocal of complex exponential increment. -/
lemma one_div_exp_two_pi_I_sub_one_aux (s c : ℝ) (hs : s ≠ 0) (hpyth : c ^ 2 + s ^ 2 = 1) :
    (-2 * (s : ℂ) ^ 2 + Complex.I * (2 * (s : ℂ) * (c : ℂ))) *
      (-1 / 2 - Complex.I * ((c : ℂ) / (2 * (s : ℂ)))) = 1 := by
  have hs_c : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hs2 : 2 * (s : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hs_c
  have h1 : (-1 / 2 - Complex.I * ((c : ℂ) / (2 * (s : ℂ)))) =
      (-(s : ℂ) - Complex.I * (c : ℂ)) / (2 * (s : ℂ)) := by
    field_simp
  rw [h1]
  have h2 : (-2 * (s : ℂ) ^ 2 + Complex.I * (2 * (s : ℂ) * (c : ℂ))) =
      (-(s : ℂ) + Complex.I * (c : ℂ)) * (2 * (s : ℂ)) := by ring
  rw [h2, mul_assoc, mul_div_cancel₀ _ hs2]
  calc (-(s : ℂ) + Complex.I * (c : ℂ)) * (-(s : ℂ) - Complex.I * (c : ℂ))
    _ = (s : ℂ) ^ 2 - Complex.I ^ 2 * (c : ℂ) ^ 2 := by ring
    _ = (s : ℂ) ^ 2 - (-1) * (c : ℂ) ^ 2 := by rw [hI]
    _ = (c : ℂ) ^ 2 + (s : ℂ) ^ 2 := by ring
    _ = ((c ^ 2 + s ^ 2 : ℝ) : ℂ) := by push_cast; rfl
    _ = 1 := by rw [hpyth]; exact Complex.ofReal_one

/-- Explicit formula for `1 / (exp(2 * π * I * x) - 1)` with constant real part `-1/2`. -/
lemma one_div_exp_two_pi_I_sub_one (x : ℝ) (hsin : Real.sin (Real.pi * x) ≠ 0) :
    1 / (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1) =
      (-1 / 2 : ℂ) - Complex.I * (((Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ)) := by
  have hcos2 : Real.cos (2 * Real.pi * x) = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
    have harg : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
    rw [harg]
    have hcos := Real.cos_two_mul (Real.pi * x)
    have hsin_sq := Real.sin_sq (Real.pi * x)
    linarith
  have hsin2 : Real.sin (2 * Real.pi * x) = 2 * Real.sin (Real.pi * x) * Real.cos (Real.pi * x) := by
    have harg : 2 * Real.pi * x = 2 * (Real.pi * x) := by ring
    rw [harg, Real.sin_two_mul]
  set s := Real.sin (Real.pi * x)
  set c := Real.cos (Real.pi * x)
  have hpyth : c ^ 2 + s ^ 2 = 1 := Real.cos_sq_add_sin_sq (Real.pi * x)
  have hprod := one_div_exp_two_pi_I_sub_one_aux s c hsin hpyth
  have hA : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1 =
      -2 * (s : ℂ) ^ 2 + Complex.I * (2 * (s : ℂ) * (c : ℂ)) := by
    rw [exp_two_pi_I_eq, hcos2, hsin2]
    push_cast
    ring
  have hB : (-1 / 2 : ℂ) - Complex.I * (((Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x)) : ℝ) : ℂ)) =
      -1 / 2 - Complex.I * ((c : ℂ) / (2 * (s : ℂ))) := by
    have : (((c / (2 * s) : ℝ) : ℂ)) = (c : ℂ) / (2 * (s : ℂ)) := by push_cast; rfl
    rw [this]
  rw [hA, hB]
  exact (eq_one_div_of_mul_eq_one_right hprod).symm

/-- Norm of a purely imaginary number `I * y`. -/
lemma norm_I_mul_ofReal (y : ℝ) :
    ‖Complex.I * (y : ℂ)‖ = |y| := by
  rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The difference of weights has zero real part and purely imaginary increment. -/
lemma sub_w_eq (x y : ℝ) (hx : Real.sin (Real.pi * x) ≠ 0) (hy : Real.sin (Real.pi * y) ≠ 0) :
    1 / (Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) - 1) -
      1 / (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1) =
    Complex.I * ((((Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x)) -
      Real.cos (Real.pi * y) / (2 * Real.sin (Real.pi * y))) : ℝ) : ℂ)) := by
  have hw_x := one_div_exp_two_pi_I_sub_one x hx
  have hw_y := one_div_exp_two_pi_I_sub_one y hy
  rw [hw_x, hw_y]
  push_cast
  ring

/-- Cotangent difference identity via sine subtraction. -/
lemma cot_sub_cot (α β : ℝ) (hα : Real.sin α ≠ 0) (hβ : Real.sin β ≠ 0) :
    Real.cos α / Real.sin α - Real.cos β / Real.sin β =
      Real.sin (β - α) / (Real.sin α * Real.sin β) := by
  have hsin := Real.sin_sub β α
  have : Real.sin β * Real.cos α - Real.cos β * Real.sin α =
    Real.cos α * Real.sin β - Real.sin α * Real.cos β := by ring
  rw [this] at hsin
  have h_denom : Real.sin α * Real.sin β ≠ 0 := mul_ne_zero hα hβ
  field_simp
  linarith

/-- Monotonicity of cotangent on `[-π/2, 0)`. -/
lemma cot_le_cot_of_le {α β : ℝ}
    (hα_low : -Real.pi / 2 ≤ α) (hαβ : α ≤ β) (hβ_high : β < 0) :
    Real.cos β / Real.sin β ≤ Real.cos α / Real.sin α := by
  have hα_neg : α < 0 := lt_of_le_of_lt hαβ hβ_high
  have hα_gt_neg_pi : -Real.pi < α := by linarith
  have hβ_gt_neg_pi : -Real.pi < β := by linarith
  have hsin_α_neg : Real.sin α < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hα_neg hα_gt_neg_pi
  have hsin_β_neg : Real.sin β < 0 := Real.sin_neg_of_neg_of_neg_pi_lt hβ_high hβ_gt_neg_pi
  have hdiff_nonneg : 0 ≤ β - α := by linarith
  have hdiff_le_pi : β - α ≤ Real.pi := by linarith
  have hsin_diff_nonneg : 0 ≤ Real.sin (β - α) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hdiff_nonneg hdiff_le_pi
  have hdenom_pos : 0 < Real.sin α * Real.sin β :=
    mul_pos_of_neg_of_neg hsin_α_neg hsin_β_neg
  have hdiv_nonneg : 0 ≤ Real.sin (β - α) / (Real.sin α * Real.sin β) :=
    div_nonneg hsin_diff_nonneg hdenom_pos.le
  have heq := cot_sub_cot α β hsin_α_neg.ne hsin_β_neg.ne
  linarith

/-- Telescoping sum for adjacent differences. -/
lemma sum_Ico_sub' {M : Type*} [AddCommGroup M] (f : ℕ → M) {m n : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ Ico m n, (f i - f (i + 1)) = f m - f n := by
  have : ∑ i ∈ Ico m n, (f i - f (i + 1)) = - ∑ i ∈ Ico m n, (f (i + 1) - f i) := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl (fun x _ => (neg_sub (f (x + 1)) (f x)).symm)
  rw [this, sum_Ico_sub f hmn, neg_sub]

/-- Summation by parts identity on `Ico a b`. -/
lemma sum_Ico_sub_mul {R : Type*} [CommRing R] (u w : ℕ → R) (a b : ℕ) (hab : a < b) :
    ∑ n ∈ Ico a b, (u (n + 1) - u n) * w n =
      u b * w (b - 1) - u a * w a - ∑ n ∈ Ico a (b - 1), u (n + 1) * (w (n + 1) - w n) := by
  have hb : b = (b - 1) + 1 := (Nat.sub_add_cancel (by omega)).symm
  have htop : ∑ n ∈ Ico a b, u (n + 1) * w n =
      (∑ n ∈ Ico a (b - 1), u (n + 1) * w n) + u b * w (b - 1) := by
    conv_lhs => rw [hb]
    rw [sum_Ico_succ_top (by omega)]
    have : b - 1 + 1 = b := by omega
    rw [this]
  have hbot : ∑ n ∈ Ico a b, u n * w n =
      u a * w a + ∑ n ∈ Ico a (b - 1), u (n + 1) * w (n + 1) := by
    rw [sum_eq_sum_Ico_succ_bot hab]
    congr 1
    have hshift := (sum_Ico_add' (fun x => u x * w x) a (b - 1) 1)
    have h_b : (b - 1) + 1 = b := by omega
    rw [h_b] at hshift
    exact hshift.symm
  have h_sub : ∑ n ∈ Ico a b, (u (n + 1) - u n) * w n =
      (∑ n ∈ Ico a b, u (n + 1) * w n) - (∑ n ∈ Ico a b, u n * w n) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl (fun x _ => by ring)
  rw [h_sub, htop, hbot]
  have h_rearr : (∑ n ∈ Ico a (b - 1), u (n + 1) * w n) -
      (∑ n ∈ Ico a (b - 1), u (n + 1) * w (n + 1)) =
      - ∑ n ∈ Ico a (b - 1), u (n + 1) * (w (n + 1) - w n) := by
    rw [← sum_sub_distrib, ← sum_neg_distrib]
    refine sum_congr rfl (fun x _ => by ring)
  linear_combination h_rearr

/-- Decomposing `Icc a b` into `Ico a b` and the right endpoint `b`. -/
lemma sum_Icc_eq_sum_Ico_add_top {M : Type*} [AddCommMonoid M] (f : ℕ → M) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Icc a b, f n = (∑ n ∈ Ico a b, f n) + f b := by
  have : b ∉ Ico a b := by simp
  rw [← Ico_insert_right hab, sum_insert this, add_comm]

/-- Step factorization for exponential difference. -/
lemma exp_diff_step (g : ℕ → ℝ) (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (g (n + 1) : ℂ)) -
      Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ)) *
      (Complex.exp (2 * Real.pi * Complex.I * ((g (n + 1) - g n : ℝ) : ℂ)) - 1) := by
  have h_add : 2 * Real.pi * Complex.I * (g (n + 1) : ℂ) =
      2 * Real.pi * Complex.I * (g n : ℂ) +
        2 * Real.pi * Complex.I * ((g (n + 1) - g n : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h_add, Complex.exp_add]
  ring

/-- Expressing `E n` in terms of difference `E (n+1) - E n` and weight `w n`. -/
lemma exp_step_mul_w (g : ℕ → ℝ) (n : ℕ)
    (hne : Complex.exp (2 * Real.pi * Complex.I * ((g (n + 1) - g n : ℝ) : ℂ)) - 1 ≠ 0) :
    (Complex.exp (2 * Real.pi * Complex.I * (g (n + 1) : ℂ)) -
      Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ))) *
    (1 / (Complex.exp (2 * Real.pi * Complex.I * ((g (n + 1) - g n : ℝ) : ℂ)) - 1)) =
    Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ)) := by
  rw [exp_diff_step, mul_assoc, mul_one_div_cancel hne, mul_one]

/-- Imaginary component is bounded by the full norm of the weight. -/
lemma abs_le_norm_one_div_exp_two_pi_I_sub_one (x : ℝ) (hsin : Real.sin (Real.pi * x) ≠ 0) :
    |Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x))| ≤
      ‖1 / (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1)‖ := by
  have hw := one_div_exp_two_pi_I_sub_one x hsin
  rw [hw]
  set f := Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x))
  have hsq : ‖(-1 / 2 : ℂ) - Complex.I * (f : ℂ)‖ ^ 2 =
      Complex.normSq ((-1 / 2 : ℂ) - Complex.I * (f : ℂ)) := by
    rw [Complex.normSq_eq_norm_sq]
  have hnormsq : Complex.normSq ((-1 / 2 : ℂ) - Complex.I * (f : ℂ)) = (1 / 4 : ℝ) + f ^ 2 := by
    have : (-1 / 2 : ℂ) - Complex.I * (f : ℂ) = ((-1 / 2 : ℝ) : ℂ) + ((-f : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.normSq_add_mul_I]
    ring
  have hf_sq : f ^ 2 ≤ ‖(-1 / 2 : ℂ) - Complex.I * (f : ℂ)‖ ^ 2 := by
    rw [hsq, hnormsq]
    linarith
  have h_abs : |f| ^ 2 = f ^ 2 := sq_abs f
  rw [← h_abs] at hf_sq
  have h1 : 0 ≤ |f| := abs_nonneg f
  have h2 : 0 ≤ ‖(-1 / 2 : ℂ) - Complex.I * (f : ℂ)‖ := norm_nonneg _
  nlinarith

/-- Non-vanishing of `exp(2 * π * I * x) - 1` when `sin(π * x) ≠ 0`. -/
lemma exp_sub_one_ne_zero_of_sin_ne_zero (x : ℝ) (hsin : Real.sin (Real.pi * x) ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1 ≠ 0 := by
  intro heq
  have hnorm : ‖Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) - 1‖ = 0 := by rw [heq, norm_zero]
  rw [norm_exp_two_pi_I_sub_one] at hnorm
  have : |Real.sin (Real.pi * x)| = 0 := by linarith
  have : Real.sin (Real.pi * x) = 0 := abs_eq_zero.mp this
  exact hsin this

/-- Sign of sine on `[-1/2, 0)`. -/
lemma sin_pi_mul_neg_of_neg {d : ℝ} (hd_neg : d < 0) (hd_half : - (1 / 2 : ℝ) ≤ d) :
    Real.sin (Real.pi * d) < 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : Real.pi * d < 0 := by nlinarith [hpi]
  have h2 : -Real.pi < Real.pi * d := by nlinarith [hpi]
  exact Real.sin_neg_of_neg_of_neg_pi_lt h1 h2

/-- Kusmin–Landau: if the consecutive differences d n := g (n+1) - g n are negative, increasing (i.e. monotone), and satisfy δ ≤ |d n| ≤ 1/2 on [a, b), then the exponential sum over [a, b] is at most 1/δ + 1. -/
theorem norm_sum_exp_le_of_monotone_diff (g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) (δ : ℝ) (hδ : 0 < δ)
    (hneg : ∀ n, a ≤ n → n < b → g (n + 1) - g n < 0)
    (hmono : ∀ n, a ≤ n → n + 1 < b → g (n + 1) - g n ≤ g (n + 2) - g (n + 1))
    (hlow : ∀ n, a ≤ n → n < b → δ ≤ |g (n + 1) - g n|)
    (hhalf : ∀ n, a ≤ n → n < b → |g (n + 1) - g n| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ))‖ ≤ 1 / δ + 1 := by
  by_cases hab_eq : a = b
  · subst hab_eq
    rw [Finset.Icc_self, Finset.sum_singleton, norm_exp_two_pi_I_mul]
    have : 0 < 1 / δ := one_div_pos.mpr hδ
    linarith
  · have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
    set E : ℕ → ℂ := fun n => Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ))
    set d : ℕ → ℝ := fun n => g (n + 1) - g n
    set w : ℕ → ℂ := fun n => 1 / (Complex.exp (2 * Real.pi * Complex.I * (d n : ℂ)) - 1)
    set f : ℝ → ℝ := fun t => Real.cos (Real.pi * t) / (2 * Real.sin (Real.pi * t))
    have hd_neg : ∀ n, a ≤ n → n < b → d n < 0 := hneg
    have hd_low : ∀ n, a ≤ n → n < b → δ ≤ |d n| := hlow
    have hd_half : ∀ n, a ≤ n → n < b → |d n| ≤ 1 / 2 := hhalf
    have hd_ge_half : ∀ n, a ≤ n → n < b → - (1 / 2 : ℝ) ≤ d n := by
      intro n hn hnb
      have : |d n| = -d n := abs_of_neg (hd_neg n hn hnb)
      have := hd_half n hn hnb
      linarith
    have hsin_neg : ∀ n, a ≤ n → n < b → Real.sin (Real.pi * d n) < 0 := by
      intro n hn hnb
      exact sin_pi_mul_neg_of_neg (hd_neg n hn hnb) (hd_ge_half n hn hnb)
    have hsin_ne : ∀ n, a ≤ n → n < b → Real.sin (Real.pi * d n) ≠ 0 := by
      intro n hn hnb
      exact (hsin_neg n hn hnb).ne
    have hne : ∀ n, a ≤ n → n < b → Complex.exp (2 * Real.pi * Complex.I * (d n : ℂ)) - 1 ≠ 0 := by
      intro n hn hnb
      exact exp_sub_one_ne_zero_of_sin_ne_zero (d n) (hsin_ne n hn hnb)
    have hw_bound : ∀ n, a ≤ n → n < b → ‖w n‖ ≤ 1 / (4 * δ) := by
      intro n hn hnb
      exact norm_one_div_exp_two_pi_I_sub_one_le hδ (hd_neg n hn hnb) (hd_low n hn hnb) (hd_half n hn hnb)
    have h_step : ∀ n ∈ Ico a b, E n = (E (n + 1) - E n) * w n := by
      intro n hn
      have hna := (mem_Ico.mp hn).1
      have hnb := (mem_Ico.mp hn).2
      exact (exp_step_mul_w g n (hne n hna hnb)).symm
    have h_Icc_split := sum_Icc_eq_sum_Ico_add_top E hab
    have h_sum_Ico : ∑ n ∈ Ico a b, E n = ∑ n ∈ Ico a b, (E (n + 1) - E n) * w n :=
      sum_congr rfl (fun n hn => h_step n hn)
    have h_parts := sum_Ico_sub_mul E w a b hab_lt
    have h_decomp : ∑ n ∈ Finset.Icc a b, E n =
        (E b * w (b - 1) - E a * w a - ∑ n ∈ Ico a (b - 1), E (n + 1) * (w (n + 1) - w n)) + E b := by
      rw [h_Icc_split, h_sum_Ico, h_parts]
    have h_norm_Eb : ‖E b‖ = 1 := norm_exp_two_pi_I_mul (g b)
    have h_norm_Ea : ‖E a‖ = 1 := norm_exp_two_pi_I_mul (g a)
    have h_norm_term1 : ‖E b * w (b - 1)‖ ≤ 1 / (4 * δ) := by
      rw [norm_mul, h_norm_Eb, one_mul]
      exact hw_bound (b - 1) (by omega) (by omega)
    have h_norm_term2 : ‖E a * w a‖ ≤ 1 / (4 * δ) := by
      rw [norm_mul, h_norm_Ea, one_mul]
      exact hw_bound a le_rfl hab_lt
    have h_step_diff : ∀ n ∈ Ico a (b - 1), ‖w (n + 1) - w n‖ = f (d n) - f (d (n + 1)) := by
      intro n hn
      have hna := (mem_Ico.mp hn).1
      have hnb_pred := (mem_Ico.mp hn).2
      have hnb : n < b := by omega
      have hn1b : n + 1 < b := by omega
      have hsin_n := hsin_ne n hna hnb
      have hsin_n1 := hsin_ne (n + 1) (by omega) hn1b
      have hdiff := sub_w_eq (d n) (d (n + 1)) hsin_n hsin_n1
      have hmono_n := hmono n hna hn1b
      have hd_n_half := hd_ge_half n hna hnb
      have hd_n1_neg := hd_neg (n + 1) (by omega) hn1b
      have hpi : 0 < Real.pi := Real.pi_pos
      have hcot_le := cot_le_cot_of_le (α := Real.pi * d n) (β := Real.pi * d (n + 1))
        (by nlinarith [hpi, hd_n_half])
        (by nlinarith [hpi, hmono_n])
        (by nlinarith [hpi, hd_n1_neg])
      have hf_le : f (d (n + 1)) ≤ f (d n) := by
        change Real.cos (Real.pi * d (n + 1)) / (2 * Real.sin (Real.pi * d (n + 1))) ≤
          Real.cos (Real.pi * d n) / (2 * Real.sin (Real.pi * d n))
        have : Real.cos (Real.pi * d (n + 1)) / (2 * Real.sin (Real.pi * d (n + 1))) =
            (1 / 2 : ℝ) * (Real.cos (Real.pi * d (n + 1)) / Real.sin (Real.pi * d (n + 1))) := by ring
        have : Real.cos (Real.pi * d n) / (2 * Real.sin (Real.pi * d n)) =
            (1 / 2 : ℝ) * (Real.cos (Real.pi * d n) / Real.sin (Real.pi * d n)) := by ring
        nlinarith
      rw [hdiff, norm_I_mul_ofReal, abs_of_nonneg (by linarith)]
    have h_sum_diff : ∑ n ∈ Ico a (b - 1), ‖w (n + 1) - w n‖ = f (d a) - f (d (b - 1)) := by
      have h_eq : ∑ n ∈ Ico a (b - 1), ‖w (n + 1) - w n‖ =
          ∑ n ∈ Ico a (b - 1), (f (d n) - f (d (n + 1))) :=
        sum_congr rfl (fun n hn => h_step_diff n hn)
      rw [h_eq, sum_Ico_sub' (fun n => f (d n)) (by omega)]
    have h_norm_fa : |f (d a)| ≤ 1 / (4 * δ) := by
      have h1 := abs_le_norm_one_div_exp_two_pi_I_sub_one (d a) (hsin_ne a le_rfl hab_lt)
      have h2 := hw_bound a le_rfl hab_lt
      linarith
    have h_norm_fb1 : |f (d (b - 1))| ≤ 1 / (4 * δ) := by
      have h1 := abs_le_norm_one_div_exp_two_pi_I_sub_one (d (b - 1))
        (hsin_ne (b - 1) (by omega) (by omega))
      have h2 := hw_bound (b - 1) (by omega) (by omega)
      linarith
    have h_sum_diff_bound : ∑ n ∈ Ico a (b - 1), ‖w (n + 1) - w n‖ ≤ 1 / (2 * δ) := by
      rw [h_sum_diff]
      have : f (d a) - f (d (b - 1)) ≤ |f (d a)| + |f (d (b - 1))| := by
        have : f (d a) ≤ |f (d a)| := le_abs_self _
        have : -f (d (b - 1)) ≤ |f (d (b - 1))| := by
          have := neg_le_abs (f (d (b - 1)))
          linarith
        linarith
      have h_add_half : 1 / (4 * δ) + 1 / (4 * δ) = 1 / (2 * δ) := by
        have h4 : 4 * δ ≠ 0 := by linarith
        have h2 : 2 * δ ≠ 0 := by linarith
        field_simp
        ring
      linarith
    have h_sum_prod_bound : ‖∑ n ∈ Ico a (b - 1), E (n + 1) * (w (n + 1) - w n)‖ ≤ 1 / (2 * δ) := by
      refine (norm_sum_le _ _).trans ?_
      have : ∑ n ∈ Ico a (b - 1), ‖E (n + 1) * (w (n + 1) - w n)‖ =
          ∑ n ∈ Ico a (b - 1), ‖w (n + 1) - w n‖ := by
        refine sum_congr rfl (fun n _ => ?_)
        rw [norm_mul, norm_exp_two_pi_I_mul, one_mul]
      rw [this]
      exact h_sum_diff_bound
    have h_tri1 := norm_add_le (E b * w (b - 1) - E a * w a - ∑ n ∈ Ico a (b - 1), E (n + 1) * (w (n + 1) - w n)) (E b)
    have h_tri2 := norm_sub_le (E b * w (b - 1) - E a * w a) (∑ n ∈ Ico a (b - 1), E (n + 1) * (w (n + 1) - w n))
    have h_tri3 := norm_sub_le (E b * w (b - 1)) (E a * w a)
    have h_total : ‖∑ n ∈ Finset.Icc a b, E n‖ ≤
        ‖E b * w (b - 1)‖ + ‖E a * w a‖ + ‖∑ n ∈ Ico a (b - 1), E (n + 1) * (w (n + 1) - w n)‖ + ‖E b‖ := by
      rw [h_decomp]
      linarith [h_tri1, h_tri2, h_tri3]
    have h_add_all : 1 / (4 * δ) + 1 / (4 * δ) + 1 / (2 * δ) = 1 / δ := by
      have hd : δ ≠ 0 := by linarith
      have h2 : 2 * δ ≠ 0 := by linarith
      have h4 : 4 * δ ≠ 0 := by linarith
      field_simp
      ring
    linarith [h_norm_term1, h_norm_term2, h_sum_prod_bound, h_norm_Eb, h_total, h_add_all]

/-- Kusmin–Landau inequality with bound `3 / δ + 1`. -/
theorem norm_sum_exp_le_of_monotone_diff_three_div_add_one (g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) (δ : ℝ) (hδ : 0 < δ)
    (hneg : ∀ n, a ≤ n → n < b → g (n + 1) - g n < 0)
    (hmono : ∀ n, a ≤ n → n + 1 < b → g (n + 1) - g n ≤ g (n + 2) - g (n + 1))
    (hlow : ∀ n, a ≤ n → n < b → δ ≤ |g (n + 1) - g n|)
    (hhalf : ∀ n, a ≤ n → n < b → |g (n + 1) - g n| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ))‖ ≤ 3 / δ + 1 := by
  have h := norm_sum_exp_le_of_monotone_diff g a b hab δ hδ hneg hmono hlow hhalf
  have : 1 / δ ≤ 3 / δ := by
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  linarith

/-- Kusmin–Landau inequality on non-empty intervals `a < b`, where `δ ≤ 1 / 2` holds automatically,
giving the classical bound `3 / δ`. -/
theorem norm_sum_exp_le_of_monotone_diff_of_lt (g : ℕ → ℝ) (a b : ℕ) (hab : a < b) (δ : ℝ) (hδ : 0 < δ)
    (hneg : ∀ n, a ≤ n → n < b → g (n + 1) - g n < 0)
    (hmono : ∀ n, a ≤ n → n + 1 < b → g (n + 1) - g n ≤ g (n + 2) - g (n + 1))
    (hlow : ∀ n, a ≤ n → n < b → δ ≤ |g (n + 1) - g n|)
    (hhalf : ∀ n, a ≤ n → n < b → |g (n + 1) - g n| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ))‖ ≤ 3 / δ := by
  have h := norm_sum_exp_le_of_monotone_diff g a b hab.le δ hδ hneg hmono hlow hhalf
  have hδ_le_half : δ ≤ 1 / 2 := by
    have h1 := hlow a le_rfl hab
    have h2 := hhalf a le_rfl hab
    linarith
  have h_one_le : 1 ≤ 1 / (2 * δ) := by
    have h2δ_pos : 0 < 2 * δ := by linarith
    rw [le_div_iff₀ h2δ_pos]
    linarith
  have h_one_div_add : 1 / δ + 1 / (2 * δ) = 3 / (2 * δ) := by
    have hd : δ ≠ 0 := by linarith
    have h2 : 2 * δ ≠ 0 := by linarith
    field_simp
    ring
  have h_three_half : 3 / (2 * δ) ≤ 3 / δ := by
    have : (3 : ℝ) / (2 * δ) = (3 / 2) / δ := by ring
    rw [this]
    exact div_le_div_of_nonneg_right (by norm_num) hδ.le
  linarith

/-- Kusmin–Landau inequality for `a ≤ b` under the standard hypothesis `δ ≤ 1 / 2`. -/
theorem norm_sum_exp_le_of_monotone_diff_of_le_half (g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) (δ : ℝ) (hδ : 0 < δ)
    (hδhalf : δ ≤ 1 / 2)
    (hneg : ∀ n, a ≤ n → n < b → g (n + 1) - g n < 0)
    (hmono : ∀ n, a ≤ n → n + 1 < b → g (n + 1) - g n ≤ g (n + 2) - g (n + 1))
    (hlow : ∀ n, a ≤ n → n < b → δ ≤ |g (n + 1) - g n|)
    (hhalf : ∀ n, a ≤ n → n < b → |g (n + 1) - g n| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ))‖ ≤ 3 / δ := by
  by_cases hab_eq : a = b
  · subst hab_eq
    rw [Finset.Icc_self, Finset.sum_singleton, norm_exp_two_pi_I_mul]
    have : 1 ≤ 3 / δ := by
      rw [le_div_iff₀ hδ]
      linarith
    linarith
  · exact norm_sum_exp_le_of_monotone_diff_of_lt g a b (lt_of_le_of_ne hab hab_eq) δ hδ hneg hmono hlow hhalf

/-- Kusmin–Landau inequality for `a ≤ b` under the hypothesis `δ ≤ 3`. -/
theorem norm_sum_exp_le_of_monotone_diff_of_le_three (g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) (δ : ℝ) (hδ : 0 < δ)
    (hδ3 : δ ≤ 3)
    (hneg : ∀ n, a ≤ n → n < b → g (n + 1) - g n < 0)
    (hmono : ∀ n, a ≤ n → n + 1 < b → g (n + 1) - g n ≤ g (n + 2) - g (n + 1))
    (hlow : ∀ n, a ≤ n → n < b → δ ≤ |g (n + 1) - g n|)
    (hhalf : ∀ n, a ≤ n → n < b → |g (n + 1) - g n| ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ))‖ ≤ 3 / δ := by
  by_cases hab_eq : a = b
  · subst hab_eq
    rw [Finset.Icc_self, Finset.sum_singleton, norm_exp_two_pi_I_mul]
    have : 1 ≤ 3 / δ := by
      rw [le_div_iff₀ hδ]
      linarith
    linarith
  · exact norm_sum_exp_le_of_monotone_diff_of_lt g a b (lt_of_le_of_ne hab hab_eq) δ hδ hneg hmono hlow hhalf

end Erdos1201.MR
