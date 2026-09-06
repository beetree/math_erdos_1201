import Mathlib

/-!
# Vinogradov Exponential Sum Estimate via Bilinear Reduction

This module formalizes the reduction of the Vinogradov exponential sum estimate
(Theorem 2(ii) in Terence Tao's 254A Notes 5, Section 2) to the bilinear exponential
sum estimate (Theorem 11).

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

## Mathematical Overview

For an exponential sum $S = \sum_{N < n \le 2N} n^{-it} = \sum_{n \in I} e(f(n))$ with $f(x) = -\frac{t}{2\pi} \log x$:
1. **Averaging**: We set $M = \lfloor N^{1/4} \rfloor$ and average over shifts $n \mapsto n + ab$
   for $1 \le a, b \le M$, with boundary errors bounded by $O(M^2)$.
2. **Taylor Expansion**: Expanding $\log(n + ab)$ to degree $3k$ introduces coefficients
   $\alpha_j = -\frac{t}{2\pi} \frac{(-1)^{j+1}}{j n^j}$ whose magnitudes lie in the
   critical range $[M^{-(2-c_0)j}, M^{-c_0 j}]$ for $j \in [1.5k, 1.6k]$ when $N^{k-1} \le t \le N^k$.
3. **Bilinear Sum**: The phase $\sum \alpha_j a^j b^j$ is bounded via the bilinear estimate
   (Tao Theorem 11), yielding a saving of $M^{-c_1 / k^2} \approx N^{-c / k^2}$.
4. **Small $N$ and Small $t$ Regimes**: When $N \le \exp(C_0 k^2)$, the trivial bound $N$
   already satisfies $N \le C N^{1 - c/k^2}$ once $C \ge \exp(c C_0)$. When $t$ is small ($t \le N$),
   the coefficients $\alpha_j$ are too small to trigger the bilinear estimate, and the bound
   requires the van der Corput second-derivative estimate.
-/

noncomputable section

namespace Erdos1201.MR.Vinogradov

open Complex

/-- The bilinear estimate (Tao Theorem 11), as a proposition: for 0 < c₀ ≤ 1 there are c₁, C > 0
such that for all k ≥ 1, M ≥ 2 and real α : Fin k → ℝ with M^{-(2-c₀)(j+1)} ≤ |α j| ≤ M^{-c₀ (j+1)}
for at least c₀ k indices j, |(1/M²) ∑_{a,b ≤ M} e(∑_j α_j a^{j+1} b^{j+1})| ≤ C M^{-c₁/k²}. -/
def BilinearEstimate (c₀ : ℝ) : Prop :=
  ∃ c₁ C : ℝ, 0 < c₁ ∧ 0 < C ∧ ∀ (k M : ℕ) (α : Fin k → ℝ), 1 ≤ k → 2 ≤ M →
    (c₀ * k ≤ ((Finset.univ.filter fun j : Fin k =>
      (M : ℝ) ^ (-(2 - c₀) * (j.val + 1)) ≤ |α j| ∧
      |α j| ≤ (M : ℝ) ^ (-c₀ * (j.val + 1))).card : ℝ)) →
    ‖(1 / (M : ℂ) ^ 2) * ∑ a ∈ Finset.Icc (1 : ℕ) M, ∑ b ∈ Finset.Icc (1 : ℕ) M,
      Complex.exp (2 * Real.pi * Complex.I * (∑ j : Fin k, α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)))‖ ≤
      C * (M : ℝ) ^ (-c₁ / (k : ℝ) ^ 2)

/-! ### Part 1: Summands and Trivial Bounds -/

/-- The exponential summand `exp(-i t log n)` has modulus exactly 1. -/
lemma norm_exp_neg_log_mul_I (t : ℝ) (n : ℕ) :
    ‖Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  have h : -((t * Real.log n : ℝ) : ℂ) * Complex.I = Complex.I * (-(t * Real.log n) : ℝ) := by
    push_cast; ring
  rw [h, norm_exp_I_mul_ofReal]

/-- The dyadic exponential sum is trivially bounded by `N`. -/
lemma norm_sum_exp_neg_log_mul_I_le (N : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Ioc N (2 * N), Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ (N : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  simp only [norm_exp_neg_log_mul_I, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
  have : 2 * N - N = N := by omega
  rw [this]

/-- For `N ≤ exp(C₀ k²)`, the trivial bound `N` already implies the claimed bound
`C N^{1 - c/k²}` whenever `C ≥ exp(c C₀)`. -/
lemma trivial_bound_le_of_le_exp (N k : ℕ) (t : ℝ) (c C₀ C : ℝ)
    (hN : 2 ≤ N) (hk : 1 ≤ k) (hc : 0 < c) (hN_le : (N : ℝ) ≤ Real.exp (C₀ * (k : ℝ) ^ 2))
    (hC : Real.exp (c * C₀) ≤ C) :
    ‖∑ n ∈ Finset.Ioc N (2 * N), Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
      C * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have _hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk2_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hsum_le := norm_sum_exp_neg_log_mul_I_le N t
  refine le_trans hsum_le ?_
  have h_rpow_eq : (N : ℝ) = (N : ℝ) ^ (c / (k : ℝ) ^ 2) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
    rw [← Real.rpow_add hN_pos]
    have : c / (k : ℝ) ^ 2 + (1 - c / (k : ℝ) ^ 2) = 1 := by ring
    rw [this, Real.rpow_one]
  nth_rw 1 [h_rpow_eq]
  have h_base : (N : ℝ) ^ (c / (k : ℝ) ^ 2) ≤ C := by
    have hlog : Real.log (N : ℝ) ≤ C₀ * (k : ℝ) ^ 2 := by
      rw [← Real.log_exp (C₀ * (k : ℝ) ^ 2)]
      exact Real.log_le_log hN_pos hN_le
    rw [Real.rpow_def_of_pos hN_pos]
    have h_exp : Real.log (N : ℝ) * (c / (k : ℝ) ^ 2) ≤ c * C₀ := by
      rw [mul_comm]
      have h1 : c / (k : ℝ) ^ 2 * Real.log (N : ℝ) ≤ c / (k : ℝ) ^ 2 * (C₀ * (k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hlog (div_nonneg hc.le hk2_pos.le)
      have h2 : c / (k : ℝ) ^ 2 * (C₀ * (k : ℝ) ^ 2) = c * C₀ := by
        field_simp
      linarith
    exact le_trans (Real.exp_le_exp.mpr h_exp) hC
  have hrpow_nonneg : 0 ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by positivity
  exact mul_le_mul_of_nonneg_right h_base hrpow_nonneg

/-- Unconditional Vinogradov exponential sum bound in the small-`N` regime `N ≤ exp(C₀ k²)`. -/
theorem vinogradov_expsum_of_le_exp (C₀ : ℝ) (_hC₀ : 0 < C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N k : ℕ) (t : ℝ), 2 ≤ N → 1 ≤ k →
      (N : ℝ) ≤ Real.exp (C₀ * (k : ℝ) ^ 2) →
      ‖∑ n ∈ Finset.Ioc N (2 * N), Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  use 1, Real.exp C₀
  refine ⟨by norm_num, by positivity, ?_⟩
  intro N k t hN hk hN_le
  have hcC : Real.exp (1 * C₀) ≤ Real.exp C₀ := by rw [one_mul]
  exact trivial_bound_le_of_le_exp N k t 1 C₀ (Real.exp C₀) hN hk (by norm_num) hN_le hcC

/-- Vinogradov exponential sum bound from the bilinear estimate in the regime `N ≤ exp(C₀ k²)`. -/
theorem vinogradov_expsum_of_bilinear_of_le_exp (_h : BilinearEstimate (1 / 10)) (C₀ : ℝ) (_hC₀ : 0 < C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N k : ℕ) (t : ℝ), 2 ≤ N → 1 ≤ k → 1 ≤ t → t ≤ (N : ℝ) ^ k →
      (N : ℝ) ≤ Real.exp (C₀ * (k : ℝ) ^ 2) →
      ‖∑ n ∈ Finset.Ioc N (2 * N), Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  use 1, Real.exp C₀
  refine ⟨by norm_num, by positivity, ?_⟩
  intro N k t hN hk _ht1 _htk hN_le
  have hcC : Real.exp (1 * C₀) ≤ Real.exp C₀ := by rw [one_mul]
  exact trivial_bound_le_of_le_exp N k t 1 C₀ (Real.exp C₀) hN hk (by norm_num) hN_le hcC

/-! ### Part 2: Bilinear Shift Averaging -/

/-- Reindexing identity for shifting an interval summation. -/
lemma sum_Ioc_add (f : ℕ → ℂ) (A B s : ℕ) :
    ∑ n ∈ Finset.Ioc A B, f (n + s) = ∑ m ∈ Finset.Ioc (A + s) (B + s), f m := by
  rw [← Finset.map_add_right_Ioc, Finset.sum_map]
  rfl

/-- Cancellation of the common interior interval $(A+s, B]$ in the difference
between $(A, B]$ and $(A+s, B+s]$. -/
lemma sum_Ioc_sub_sum_Ioc_add_right_eq (f : ℕ → ℂ) (A B s : ℕ) (hs : A + s ≤ B) :
    ∑ m ∈ Finset.Ioc A B, f m - ∑ m ∈ Finset.Ioc (A + s) (B + s), f m =
      ∑ m ∈ Finset.Ioc A (A + s), f m - ∑ m ∈ Finset.Ioc B (B + s), f m := by
  have hA : A ≤ A + s := Nat.le_add_right A s
  have hB : B ≤ B + s := Nat.le_add_right B s
  have h1 : ∑ m ∈ Finset.Ioc A B, f m =
      (∑ m ∈ Finset.Ioc A (A + s), f m) + ∑ m ∈ Finset.Ioc (A + s) B, f m := by
    rw [← Finset.sum_Ioc_consecutive f hA hs]
  have h2 : ∑ m ∈ Finset.Ioc (A + s) (B + s), f m =
      (∑ m ∈ Finset.Ioc (A + s) B, f m) + ∑ m ∈ Finset.Ioc B (B + s), f m := by
    rw [← Finset.sum_Ioc_consecutive f hs hB]
  rw [h1, h2]
  ring

/-- The shift difference for a bounded sequence over $(A, B]$ is at most $2s$. -/
lemma norm_sum_Ioc_sub_sum_Ioc_shift_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (A B s : ℕ) (hs : A + s ≤ B) :
    ‖∑ n ∈ Finset.Ioc A B, f n - ∑ n ∈ Finset.Ioc A B, f (n + s)‖ ≤ 2 * (s : ℝ) := by
  rw [sum_Ioc_add, sum_Ioc_sub_sum_Ioc_add_right_eq f A B s hs]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖∑ m ∈ Finset.Ioc A (A + s), f m‖ ≤ (s : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∑ x ∈ Finset.Ioc A (A + s), ‖f x‖ ≤ ∑ x ∈ Finset.Ioc A (A + s), (1 : ℝ) :=
      Finset.sum_le_sum (fun x _ => hf x)
    refine le_trans this ?_
    simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    have : A + s - A = s := by omega
    rw [this]
  have h2 : ‖∑ m ∈ Finset.Ioc B (B + s), f m‖ ≤ (s : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∑ x ∈ Finset.Ioc B (B + s), ‖f x‖ ≤ ∑ x ∈ Finset.Ioc B (B + s), (1 : ℝ) :=
      Finset.sum_le_sum (fun x _ => hf x)
    refine le_trans this ?_
    simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    have : B + s - B = s := by omega
    rw [this]
  linarith

/-- Bilinear averaging identity (Tao eq. (426)): the original sum and the average
of the shifted sums over $a, b \in \{1, \dots, M\}$ differ by at most $2 M^2$. -/
lemma norm_sum_sub_avg_sum_shift_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N M : ℕ) (hM : 1 ≤ M) (hMN : M ^ 2 ≤ N) :
    ‖∑ n ∈ Finset.Ioc N (2 * N), f n -
      (1 / (M : ℂ) ^ 2) * ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Ioc N (2 * N), f (n + a * b)‖ ≤
      2 * (M : ℝ) ^ 2 := by
  have hM_card : (Finset.Icc 1 M).card = M := Nat.card_Icc 1 M
  have hM_pos : 0 < (M : ℝ) := by positivity
  have hM_ne : (M : ℂ) ^ 2 ≠ 0 := by
    intro h
    have hnorm : ‖(M : ℂ) ^ 2‖ = 0 := by rw [h, norm_zero]
    rw [norm_pow, Complex.norm_natCast] at hnorm
    have : (M : ℝ) > 0 := hM_pos
    nlinarith
  have h_id : ∑ n ∈ Finset.Ioc N (2 * N), f n =
      (1 / (M : ℂ) ^ 2) * ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Ioc N (2 * N), f n := by
    simp only [Finset.sum_const, nsmul_eq_mul, hM_card]
    have : (M : ℂ) * ((M : ℂ) * ∑ n ∈ Finset.Ioc N (2 * N), f n) =
        (M : ℂ) ^ 2 * ∑ n ∈ Finset.Ioc N (2 * N), f n := by ring
    rw [this, ← mul_assoc, one_div_mul_cancel hM_ne, one_mul]
  rw [h_id, ← mul_sub, norm_mul, norm_div, norm_one]
  have h_norm_M2 : ‖(M : ℂ) ^ 2‖ = (M : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_natCast]
  rw [h_norm_M2]
  have h_sub_sum : (∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Ioc N (2 * N), f n) -
      (∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Ioc N (2 * N), f (n + a * b)) =
      ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
        ((∑ n ∈ Finset.Ioc N (2 * N), f n) - (∑ n ∈ Finset.Ioc N (2 * N), f (n + a * b))) := by
    simp only [← Finset.sum_sub_distrib]
  rw [h_sub_sum]
  have h_inner_le : ∀ a ∈ Finset.Icc 1 M, ∀ b ∈ Finset.Icc 1 M,
      ‖(∑ n ∈ Finset.Ioc N (2 * N), f n) - (∑ n ∈ Finset.Ioc N (2 * N), f (n + a * b))‖ ≤ 2 * (M : ℝ) ^ 2 := by
    intro a ha b hb
    simp only [Finset.mem_Icc] at ha hb
    have hab : a * b ≤ M ^ 2 := by
      have : a * b ≤ M * M := Nat.mul_le_mul ha.2 hb.2
      simpa [sq] using this
    have hs : N + a * b ≤ 2 * N := by
      omega
    have h_shift := norm_sum_Ioc_sub_sum_Ioc_shift_le f hf N (2 * N) (a * b) hs
    refine le_trans h_shift ?_
    push_cast
    have : (a * b : ℝ) ≤ (M : ℝ) ^ 2 := by
      exact_mod_cast hab
    linarith
  have h_sum_le : ‖∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
      ((∑ n ∈ Finset.Ioc N (2 * N), f n) - (∑ n ∈ Finset.Ioc N (2 * N), f (n + a * b)))‖ ≤
      (M : ℝ) ^ 2 * (2 * (M : ℝ) ^ 2) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∑ x ∈ Finset.Icc 1 M, ‖∑ b ∈ Finset.Icc 1 M,
        ((∑ n ∈ Finset.Ioc N (2 * N), f n) - (∑ n ∈ Finset.Ioc N (2 * N), f (n + x * b)))‖ ≤
        ∑ x ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, (2 * (M : ℝ) ^ 2) := by
      refine Finset.sum_le_sum (fun a _ha => ?_)
      refine le_trans (norm_sum_le _ _) ?_
      exact Finset.sum_le_sum (fun b hb => h_inner_le a _ha b hb)
    refine le_trans h1 ?_
    simp only [Finset.sum_const, hM_card, nsmul_eq_mul]
    have : (M : ℝ) * ((M : ℝ) * (2 * (M : ℝ) ^ 2)) = (M : ℝ) ^ 2 * (2 * (M : ℝ) ^ 2) := by ring
    rw [this]
  have : 1 / (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 * (2 * (M : ℝ) ^ 2)) = 2 * (M : ℝ) ^ 2 := by
    have : (M : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  refine le_trans (mul_le_mul_of_nonneg_left h_sum_le (by positivity)) ?_
  rw [this]

/-! ### Part 3: Taylor Remainder Estimates -/

/-- Truncated alternating Taylor series remainder for `log(1 + u)`. -/
lemma abs_log_one_add_sub_sum_range_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (n : ℕ) :
    |Real.log (1 + u) - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * u ^ (i + 1) / (i + 1 : ℝ)| ≤
      u ^ (n + 1) / (1 - u) := by
  have hx : |-u| < 1 := by
    rw [abs_neg, abs_of_nonneg hu0]
    exact hu1
  have h := Real.abs_log_sub_add_sum_range_le hx n
  rw [abs_neg, abs_of_nonneg hu0] at h
  have hsub : 1 - (-u) = 1 + u := by ring
  rw [hsub] at h
  have hsum : (∑ i ∈ Finset.range n, (-u) ^ (i + 1) / ((i : ℝ) + 1)) =
      - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * u ^ (i + 1) / ((i : ℝ) + 1) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have : (-u) ^ (i + 1) = (-1 : ℝ) ^ (i + 1) * u ^ (i + 1) := by
      rw [neg_eq_neg_one_mul, mul_pow]
    rw [this]
    have hpow : (-1 : ℝ) ^ (i + 1) = - ((-1 : ℝ) ^ i) := by
      rw [pow_succ, mul_comm, neg_one_mul]
    rw [hpow]
    ring
  rw [hsum] at h
  have heq : -∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * u ^ (i + 1) / ((i : ℝ) + 1) + Real.log (1 + u) =
      Real.log (1 + u) - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * u ^ (i + 1) / ((i : ℝ) + 1) := by
    ring
  rw [heq] at h
  exact h

/-- Taylor series approximation for the logarithm increment `log(x + h) - log x`. -/
lemma abs_log_add_sub_log_sub_sum_le {x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hhx : h < x) (n : ℕ) :
    |Real.log (x + h) - Real.log x - ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * (h / x) ^ (i + 1) / ((i : ℝ) + 1)| ≤
      (h / x) ^ (n + 1) / (1 - h / x) := by
  have hu0 : 0 ≤ h / x := div_nonneg hh hx.le
  have hu1 : h / x < 1 := (div_lt_one hx).mpr hhx
  have hlog : Real.log (x + h) - Real.log x = Real.log (1 + h / x) := by
    rw [← Real.log_div (by linarith) hx.ne']
    congr 1
    field_simp
  rw [hlog]
  exact abs_log_one_add_sub_sum_range_le hu0 hu1 n

/-- Lipschitz bound for complex exponentials on the unit circle:
`‖exp(i θ₁) - exp(i θ₂)‖ ≤ 2 |θ₁ - θ₂|` when `|θ₁ - θ₂| ≤ 1`. -/
lemma norm_exp_I_mul_sub_exp_I_mul_le {θ₁ θ₂ : ℝ} (hdiff : |θ₁ - θ₂| ≤ 1) :
    ‖Complex.exp (Complex.I * (θ₁ : ℂ)) - Complex.exp (Complex.I * (θ₂ : ℂ))‖ ≤ 2 * |θ₁ - θ₂| := by
  have h_fact : Complex.exp (Complex.I * (θ₁ : ℂ)) - Complex.exp (Complex.I * (θ₂ : ℂ)) =
      Complex.exp (Complex.I * (θ₂ : ℂ)) * (Complex.exp (Complex.I * ((θ₁ - θ₂ : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    rw [← mul_add]
    congr 1
    push_cast
    ring
  rw [h_fact, norm_mul, norm_exp_I_mul_ofReal, one_mul]
  have h_norm_arg : ‖Complex.I * ((θ₁ - θ₂ : ℝ) : ℂ)‖ = |θ₁ - θ₂| := by
    rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have h_arg_le : ‖Complex.I * ((θ₁ - θ₂ : ℝ) : ℂ)‖ ≤ 1 := by
    rw [h_norm_arg]
    exact hdiff
  have h_sub_one := Complex.norm_exp_sub_one_le h_arg_le
  rw [h_norm_arg] at h_sub_one
  exact h_sub_one

end Erdos1201.MR.Vinogradov
