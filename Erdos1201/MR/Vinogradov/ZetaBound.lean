import Mathlib
import Erdos1201.MR.Vinogradov.TaylorReduction
import Erdos1201.MR.Vinogradov.TaylorReductionMain
import Erdos1201.MR.Vinogradov.ZetaFromExpSums
import Erdos1201.MR.Analysis.VanDerCorputKth
import Erdos1201.MR.Analysis.VanDerCorputSubblock

/-!
# Vinogradov-Korobov Zeta Bound

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

open Real Complex Finset

namespace Erdos1201.MR.Vinogradov

/-- A generalized shift lemma for sub-blocks, eliminating the `A + s ≤ B` requirement. -/
lemma norm_sum_Ioc_sub_sum_Ioc_shift_le_subblock (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (A B s : ℕ) :
    ‖∑ n ∈ Finset.Ioc A B, f n - ∑ n ∈ Finset.Ioc A B, f (n + s)‖ ≤ 2 * (s : ℝ) := by
  by_cases hAB : A ≤ B
  · by_cases hs : A + s ≤ B
    · rw [sum_Ioc_add, sum_Ioc_sub_sum_Ioc_add_right_eq f A B s hs]
      refine le_trans (norm_sub_le _ _) ?_
      have h1 : ‖∑ n ∈ Finset.Ioc A (A + s), f n‖ ≤ s := by
        refine le_trans (norm_sum_le _ _) ?_
        have : ∑ n ∈ Finset.Ioc A (A + s), ‖f n‖ ≤ ∑ n ∈ Finset.Ioc A (A + s), (1 : ℝ) :=
          Finset.sum_le_sum (fun n _ => hf n)
        refine le_trans this ?_
        simp only [sum_const, Nat.card_Ioc, add_tsub_cancel_left, nsmul_eq_mul, mul_one]
        rfl
      have h2 : ‖∑ n ∈ Finset.Ioc B (B + s), f n‖ ≤ s := by
        refine le_trans (norm_sum_le _ _) ?_
        have : ∑ n ∈ Finset.Ioc B (B + s), ‖f n‖ ≤ ∑ n ∈ Finset.Ioc B (B + s), (1 : ℝ) :=
          Finset.sum_le_sum (fun n _ => hf n)
        refine le_trans this ?_
        simp only [sum_const, Nat.card_Ioc, add_tsub_cancel_left, nsmul_eq_mul, mul_one]
        rfl
      linarith
    · have hs_lt : B < A + s := not_le.mp hs
      have hB_le : B ≤ A + s := hs_lt.le
      have h_sum1 : ‖∑ n ∈ Finset.Ioc A B, f n‖ ≤ (B - A : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have : ∑ n ∈ Finset.Ioc A B, ‖f n‖ ≤ ∑ n ∈ Finset.Ioc A B, (1 : ℝ) :=
          Finset.sum_le_sum (fun n _ => hf n)
        refine le_trans this ?_
        simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
        have h_cast : ((B - A : ℕ) : ℝ) = (B : ℝ) - (A : ℝ) := Nat.cast_sub hAB
        exact le_of_eq h_cast
      have h_sum2 : ‖∑ n ∈ Finset.Ioc A B, f (n + s)‖ ≤ (B - A : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have : ∑ n ∈ Finset.Ioc A B, ‖f (n + s)‖ ≤ ∑ n ∈ Finset.Ioc A B, (1 : ℝ) :=
          Finset.sum_le_sum (fun n _ => hf (n + s))
        refine le_trans this ?_
        simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
        have h_cast : ((B - A : ℕ) : ℝ) = (B : ℝ) - (A : ℝ) := Nat.cast_sub hAB
        exact le_of_eq h_cast
      refine le_trans (norm_sub_le _ _) ?_
      have : (B : ℝ) - (A : ℝ) ≤ (s : ℝ) := by
        have : B - A ≤ s := by omega
        have h_cast : ((B - A : ℕ) : ℝ) = (B : ℝ) - (A : ℝ) := Nat.cast_sub hAB
        rw [← h_cast]
        exact_mod_cast this
      linarith
  · have hAB_lt : B < A := not_le.mp hAB
    have h_emp : Finset.Ioc A B = ∅ := by
      rw [Finset.Ioc_eq_empty_iff]
      exact not_lt.mpr hAB_lt.le
    rw [h_emp, Finset.sum_empty, Finset.sum_empty, sub_self, norm_zero]
    positivity


/-- Swapping summation order between sub-block interval and shift parameters. -/
lemma sum_avg_swap_subblock (f : ℕ → ℂ) (N M_shift M : ℕ) :
    (1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, ∑ n ∈ Ioc N M, f (n + a * b) =
    ∑ n ∈ Ioc N M, (1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, f (n + a * b) := by
  have h_comm : (∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, ∑ n ∈ Ioc N M, f (n + a * b)) =
      ∑ n ∈ Ioc N M, ∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, f (n + a * b) := by
    simp_rw [sum_comm (s := Icc 1 M_shift) (t := Ioc N M)]
  rw [h_comm, mul_sum]

/-- Bilinear averaging identity for sub-blocks: the sum over `(N, M]` and the average
of shifted sums differ by at most `2 M_shift^2`. -/
lemma norm_sum_sub_avg_sum_shift_le_subblock (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N M M_shift : ℕ)
    (hM_shift : 1 ≤ M_shift) :
    ‖∑ n ∈ Finset.Ioc N M, f n -
      (1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Finset.Icc 1 M_shift, ∑ b ∈ Finset.Icc 1 M_shift, ∑ n ∈ Finset.Ioc N M, f (n + a * b)‖ ≤
      2 * (M_shift : ℝ) ^ 2 := by
  have hM_card : (Finset.Icc 1 M_shift).card = M_shift := Nat.card_Icc 1 M_shift
  have hM_pos : 0 < (M_shift : ℝ) := by positivity
  have hM_ne : (M_shift : ℂ) ^ 2 ≠ 0 := by
    intro h
    have hnorm : ‖(M_shift : ℂ) ^ 2‖ = 0 := by rw [h, norm_zero]
    rw [norm_pow, Complex.norm_natCast] at hnorm
    have : (M_shift : ℝ) > 0 := hM_pos
    nlinarith
  have h_id : ∑ n ∈ Finset.Ioc N M, f n =
      (1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Finset.Icc 1 M_shift, ∑ b ∈ Finset.Icc 1 M_shift, ∑ n ∈ Finset.Ioc N M, f n := by
    simp only [Finset.sum_const, nsmul_eq_mul, hM_card]
    have : (M_shift : ℂ) * ((M_shift : ℂ) * ∑ n ∈ Finset.Ioc N M, f n) =
        (M_shift : ℂ) ^ 2 * ∑ n ∈ Finset.Ioc N M, f n := by ring
    rw [this, ← mul_assoc, one_div_mul_cancel hM_ne, one_mul]
  rw [h_id, ← mul_sub, norm_mul, norm_div, norm_one]
  have h_norm_M2 : ‖(M_shift : ℂ) ^ 2‖ = (M_shift : ℝ) ^ 2 := by
    rw [norm_pow, Complex.norm_natCast]
  rw [h_norm_M2]
  have h_sub_sum : (∑ a ∈ Finset.Icc 1 M_shift, ∑ b ∈ Finset.Icc 1 M_shift, ∑ n ∈ Finset.Ioc N M, f n) -
      (∑ a ∈ Finset.Icc 1 M_shift, ∑ b ∈ Finset.Icc 1 M_shift, ∑ n ∈ Finset.Ioc N M, f (n + a * b)) =
      ∑ a ∈ Finset.Icc 1 M_shift, ∑ b ∈ Finset.Icc 1 M_shift,
        ((∑ n ∈ Finset.Ioc N M, f n) - (∑ n ∈ Finset.Ioc N M, f (n + a * b))) := by
    simp only [← Finset.sum_sub_distrib]
  rw [h_sub_sum]
  have h_inner_le : ∀ a ∈ Finset.Icc 1 M_shift, ∀ b ∈ Finset.Icc 1 M_shift,
      ‖(∑ n ∈ Finset.Ioc N M, f n) - (∑ n ∈ Finset.Ioc N M, f (n + a * b))‖ ≤ 2 * (M_shift : ℝ) ^ 2 := by
    intro a ha b hb
    simp only [Finset.mem_Icc] at ha hb
    have hab : a * b ≤ M_shift ^ 2 := by
      have : a * b ≤ M_shift * M_shift := Nat.mul_le_mul ha.2 hb.2
      simpa [sq] using this
    have h_shift := norm_sum_Ioc_sub_sum_Ioc_shift_le_subblock f hf N M (a * b)
    refine le_trans h_shift ?_
    push_cast
    have : (a * b : ℝ) ≤ (M_shift : ℝ) ^ 2 := by
      exact_mod_cast hab
    linarith
  have h_sum_le : ‖∑ a ∈ Finset.Icc 1 M_shift, ∑ b ∈ Finset.Icc 1 M_shift,
      ((∑ n ∈ Finset.Ioc N M, f n) - (∑ n ∈ Finset.Ioc N M, f (n + a * b)))‖ ≤
      (M_shift : ℝ) ^ 2 * (2 * (M_shift : ℝ) ^ 2) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∑ x ∈ Finset.Icc 1 M_shift, ‖∑ b ∈ Finset.Icc 1 M_shift,
        ((∑ n ∈ Finset.Ioc N M, f n) - (∑ n ∈ Finset.Ioc N M, f (n + x * b)))‖ ≤
        ∑ x ∈ Finset.Icc 1 M_shift, ∑ b ∈ Finset.Icc 1 M_shift, (2 * (M_shift : ℝ) ^ 2) := by
      refine Finset.sum_le_sum (fun a _ha => ?_)
      refine le_trans (norm_sum_le _ _) ?_
      exact Finset.sum_le_sum (fun b hb => h_inner_le a _ha b hb)
    refine le_trans h1 ?_
    simp only [Finset.sum_const, hM_card, nsmul_eq_mul]
    have : (M_shift : ℝ) * ((M_shift : ℝ) * (2 * (M_shift : ℝ) ^ 2)) = (M_shift : ℝ) ^ 2 * (2 * (M_shift : ℝ) ^ 2) := by ring
    rw [this]
  refine le_trans (mul_le_mul_of_nonneg_left h_sum_le (by positivity)) ?_
  rw [← mul_assoc, one_div_mul_cancel (by positivity), one_mul]

/-- Reduction of sub-block exponential sum to point-wise bilinear average bounds. -/
lemma norm_sum_le_of_avg_bound_subblock (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N M M_shift : ℕ)
    (hNM : N < M) (hM : M ≤ 2 * N)
    (hM_shift : 1 ≤ M_shift) (B : ℝ)
    (hB : ∀ n ∈ Ioc N M, ‖(1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, f (n + a * b)‖ ≤ B) :
    ‖∑ n ∈ Ioc N M, f n‖ ≤ (N : ℝ) * B + 2 * (M_shift : ℝ) ^ 2 := by
  let A := (1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, ∑ n ∈ Ioc N M, f (n + a * b)
  have h_diff := norm_sum_sub_avg_sum_shift_le_subblock f hf N M M_shift hM_shift
  have h_tri : ‖∑ n ∈ Ioc N M, f n‖ ≤ ‖A‖ + 2 * (M_shift : ℝ) ^ 2 := by
    have := norm_le_norm_sub_add (∑ n ∈ Ioc N M, f n) A
    linarith
  have hA_swap : A = ∑ n ∈ Ioc N M, (1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, f (n + a * b) :=
    sum_avg_swap_subblock f N M_shift M
  have hA_norm : ‖A‖ ≤ (N : ℝ) * B := by
    rw [hA_swap]
    refine le_trans (norm_sum_le _ _) ?_
    have h_card : ∑ x ∈ Ioc N M, B = ((Finset.Ioc N M).card : ℝ) * B := by
      simp only [sum_const, nsmul_eq_mul]
    have hcard_le : ((Finset.Ioc N M).card : ℝ) ≤ (N : ℝ) := by
      rw [Nat.card_Ioc]
      have : M - N ≤ N := by omega
      exact_mod_cast this
    have hB_nonneg : 0 ≤ B := by
      obtain ⟨n, hn⟩ : (Finset.Ioc N M).Nonempty := Finset.nonempty_Ioc.mpr hNM
      exact le_trans (norm_nonneg _) (hB n hn)
    refine le_trans (Finset.sum_le_sum hB) ?_
    rw [h_card]
    exact mul_le_mul_of_nonneg_right hcard_le hB_nonneg
  linarith

/-- Trivial bound for sub-blocks when `N ≤ exp(C₀ k²)`. -/
lemma trivial_bound_le_of_le_exp_subblock (N M k : ℕ) (t : ℝ) (c C₀ C : ℝ)
    (hN : 2 ≤ N) (hNM : N < M) (hM : M ≤ 2 * N) (hk : 1 ≤ k) (hc : 0 < c)
    (hN_le : (N : ℝ) ≤ Real.exp (C₀ * (k : ℝ) ^ 2))
    (hC : Real.exp (c * C₀) ≤ C) :
    ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
      C * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have _hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk2_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hsum_le : ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ (N : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h_card : (Finset.Ioc N M).card ≤ N := by
      rw [Nat.card_Ioc]
      omega
    have h_terms : ∑ x ∈ Finset.Ioc N M, ‖Complex.exp (-((t * Real.log (x : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
        ∑ x ∈ Finset.Ioc N M, (1 : ℝ) := by
      refine Finset.sum_le_sum fun x _ => (norm_exp_neg_log_mul_I t x).le
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h_terms
    exact h_terms.trans (by exact_mod_cast h_card)
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
    have h_exp_le : Real.exp (Real.log (N : ℝ) * (c / (k : ℝ) ^ 2)) ≤ Real.exp (c * C₀) :=
      Real.exp_le_exp.mpr h_exp
    exact le_trans h_exp_le hC
  have h_pow_pos : 0 ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by positivity
  exact mul_le_mul_of_nonneg_right h_base h_pow_pos

/-- Deduction of the Vinogradov exponential sum estimate for sub-blocks from the bilinear estimate. -/
theorem vinogradov_expsum_regime_subblock (h : BilinearEstimate (1 / 30)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N M k : ℕ) (t : ℝ), 2 ≤ N → N < M → M ≤ 2 * N → 10 ≤ k → (N : ℝ) ^ (k - 1) ≤ t → t ≤ (N : ℝ) ^ k →
      ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ C * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  rcases h with ⟨c₁, C₁, hc₁, hC₁, h_bilin⟩
  let c := min (c₁ / 36) (1 / 4 : ℝ)
  have hc : 0 < c := lt_min (by linarith) (by norm_num)
  let C₀ : ℝ := 100
  have _hC₀ : 0 < C₀ := by norm_num
  let C₂ : ℝ := C₁ * (2 : ℝ) ^ c₁ + 6
  have _hC₂ : 0 < C₂ := by
    have : 0 < (2 : ℝ) ^ c₁ := rpow_pos_of_pos (by norm_num) c₁
    positivity
  let C := max (Real.exp (c * C₀)) C₂
  have hC : 0 < C := lt_max_of_lt_left (Real.exp_pos _)
  use c, C, hc, hC
  intro N M k t hN hNM hM hk ht1 ht2
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have ht_pos : (0 : ℝ) < t := by
    have : 0 < (N : ℝ) ^ (k - 1) := by positivity
    linarith
  by_cases h_regime : (N : ℝ) ≤ Real.exp (C₀ * (k : ℝ) ^ 2)
  · have hcC : Real.exp (c * C₀) ≤ C := le_max_left _ _
    exact trivial_bound_le_of_le_exp_subblock N M k t c C₀ C hN hNM hM (by omega) hc h_regime hcC
  · have h_regime' : Real.exp (C₀ * (k : ℝ) ^ 2) < (N : ℝ) := not_le.mp h_regime
    have hlogN : C₀ * (k : ℝ) ^ 2 ≤ Real.log (N : ℝ) := by
      rw [← Real.log_exp (C₀ * (k : ℝ) ^ 2)]
      exact (Real.log_lt_log (Real.exp_pos _) h_regime').le
    have _hk_10 : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have _hk2_100 : (100 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have h16_N : 16 ≤ N := by
      have : Real.exp (C₀ * 100) ≤ (N : ℝ) := by
        refine le_trans ?_ h_regime'.le
        exact Real.exp_le_exp.mpr (by nlinarith)
      have : (16 : ℝ) ≤ Real.exp (C₀ * 100) := by
        have : (16 : ℝ) ≤ Real.exp 4 := by
          have : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have h27 : (16 : ℝ) ≤ (2.7 : ℝ) ^ 4 := by norm_num
          have hexp4 : (Real.exp 1) ^ 4 = Real.exp 4 := by
            rw [← Real.exp_nat_mul]
            norm_num
          rw [← hexp4]
          exact le_trans h27 (pow_le_pow_left₀ (by norm_num) this 4)
        refine le_trans this ?_
        exact Real.exp_le_exp.mpr (by norm_num)
      exact_mod_cast (by linarith : (16 : ℝ) ≤ (N : ℝ))
    let M_shift := Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ))
    have hM_two : 2 ≤ M_shift := floor_rpow_quarter_ge_two (by exact_mod_cast h16_N)
    have hM_one : 1 ≤ M_shift := by omega
    have hMN : M_shift ^ 2 ≤ N := floor_rpow_quarter_sq_le (by omega)
    have hM_le : (M_shift : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := floor_rpow_quarter_le
    have hM_ge : (N : ℝ) ^ (1 / 4 : ℝ) / 2 ≤ (M_shift : ℝ) := floor_rpow_quarter_ge_half (by exact_mod_cast h16_N)
    let f := fun m : ℕ => Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)
    have hf : ∀ n, ‖f n‖ ≤ 1 := fun n => by
      simp only [f]
      exact (norm_exp_neg_log_mul_I t n).le
    have h_inner_bound : ∀ n ∈ Ioc N M,
        ‖(1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, f (n + a * b)‖ ≤
          (C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by
      intro n hn
      rw [mem_Ioc] at hn
      have hn_2N : N < n ∧ n ≤ 2 * N := ⟨hn.1, le_trans hn.2 hM⟩
      let g := fun a b : ℕ => Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi *
        (∑ j : Fin (3 * k), taylor_coeff t n k j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) : ℝ) : ℂ))
      have h_term1_le := bilinear_inner_bound t n k N M_shift c₁ C₁ hc₁ hC₁ h_bilin h16_N hn_2N ht1 ht2 ht_pos hk hlogN hM_two hM_le hM_ge c (min_le_left _ _)
      have h_diff_avg := bilinear_avg_diff_le t n k N M_shift h16_N hn.1.le hM_two hM_le ht_pos ht2 hk c hc (min_le_right _ _)
      have h_decomp : (1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, f (n + a * b) =
          ((1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, g a b) +
          (1 / (M_shift : ℂ) ^ 2) * ∑ a ∈ Icc 1 M_shift, ∑ b ∈ Icc 1 M_shift, (f (n + a * b) - g a b) := by
        rw [← mul_add, ← sum_add_distrib]
        refine congr_arg _ (sum_congr rfl fun a _ => ?_)
        rw [← sum_add_distrib]
        refine sum_congr rfl fun b _ => ?_
        ring
      rw [h_decomp]
      refine le_trans (norm_add_le _ _) ?_
      have : (C₁ * (2 : ℝ) ^ c₁) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) + 4 * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) =
          (C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by ring
      rw [← this]
      exact add_le_add h_term1_le h_diff_avg
    have h_avg_bound := norm_sum_le_of_avg_bound_subblock f hf N M M_shift hNM hM hM_one
        ((C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) h_inner_bound
    refine h_avg_bound.trans ?_
    have h_term1_N : (N : ℝ) * ((C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) =
        (C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      have : (N : ℝ) * ((C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) =
          (C₁ * (2 : ℝ) ^ c₁ + 4) * ((N : ℝ) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) := by ring
      rw [this]
      congr 1
      have hN1 : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
      nth_rw 1 [hN1]
      rw [← rpow_add hN_pos]
      ring_nf
    rw [h_term1_N]
    have h_term2_N : 2 * (M_shift : ℝ) ^ 2 ≤ 2 * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      have hM2 : (M_shift : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
        have : (M_shift : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℝ) := by
          have : (M_shift : ℝ) ^ 2 = (M_shift : ℝ) ^ (2 : ℝ) := (rpow_two _).symm
          rw [this]
          exact rpow_le_rpow (by positivity) hM_le (by norm_num)
        refine this.trans ?_
        rw [← rpow_mul (by positivity)]
        norm_num
      have hN12 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
        refine rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) ?_
        have : c ≤ 1 / 4 := min_le_right _ _
        have : c / (k : ℝ) ^ 2 ≤ 1 / 4 := by
          have : 0 < (k : ℝ) ^ 2 := by positivity
          have : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
          have : c / (k : ℝ) ^ 2 ≤ c / 1 := div_le_div₀ hc.le (by linarith) (by norm_num) (by nlinarith)
          linarith
        linarith
      nlinarith
    have h_sum_terms : (C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) + 2 * (M_shift : ℝ) ^ 2 ≤
        C₂ * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      have : (C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) + 2 * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) =
          C₂ * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
        dsimp [C₂]
        ring
      linarith
    refine h_sum_terms.trans ?_
    have hC_ge : C₂ ≤ C := le_max_right _ _
    exact mul_le_mul_of_nonneg_right hC_ge (by positivity)

/-- Invariance of exponential sum norm under sign flip of `t`. -/
lemma norm_sum_exp_neg_log_eq_abs (N M : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ =
    ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((|t| * Real.log n : ℝ) : ℂ) * Complex.I)‖ := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
  · rw [abs_of_nonpos ht]
    have h_conj : (starRingEnd ℂ) (∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)) =
        ∑ n ∈ Finset.Ioc N M, Complex.exp (-((-t * Real.log n : ℝ) : ℂ) * Complex.I) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_neg, conj_ofReal, conj_I]
      push_cast
      ring
    have h_norm := Complex.norm_conj (∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I))
    rw [h_conj] at h_norm
    exact h_norm.symm


lemma exp_one_lt_three' : Real.exp 1 < 3 := by
  have : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  linarith

lemma one_lt_log_three' : 1 < Real.log 3 := by
  have h := exp_one_lt_three'
  rw [← Real.log_exp 1]
  exact Real.log_lt_log (Real.exp_pos 1) h

lemma log_log_three_pos' : 0 < Real.log (Real.log 3) := by
  rw [← Real.log_one]
  exact Real.log_lt_log (by norm_num) one_lt_log_three'

lemma log_le_self_of_pos' {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos hx
  linarith

lemma log_pow_two_thirds_div_le_one {x : ℝ} (hx : 3 ≤ x) :
    (Real.log (Real.log x)) ^ (2 / 3 : ℝ) / (Real.log x) ^ (2 / 3 : ℝ) ≤ 1 := by
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hlog_ge : Real.log 3 ≤ Real.log x := Real.log_le_log h3 hx
  have hlog_gt1 : 1 < Real.log x := lt_of_lt_of_le one_lt_log_three' hlog_ge
  have hlog_pos : 0 < Real.log x := by linarith
  have hlog_log_pos : 0 < Real.log (Real.log x) := by
    rw [← Real.log_one]
    exact Real.log_lt_log (by norm_num) hlog_gt1
  have hlog_log_le : Real.log (Real.log x) ≤ Real.log x := log_le_self_of_pos' hlog_pos
  rw [← Real.div_rpow hlog_log_pos.le hlog_pos.le]
  have hdiv_pos : 0 ≤ Real.log (Real.log x) / Real.log x := div_nonneg hlog_log_pos.le hlog_pos.le
  have hdiv_le : Real.log (Real.log x) / Real.log x ≤ 1 := (div_le_one₀ hlog_pos).mpr hlog_log_le
  have h_rpow := Real.rpow_le_rpow hdiv_pos hdiv_le (by norm_num : 0 ≤ (2 / 3 : ℝ))
  rw [Real.one_rpow] at h_rpow
  exact h_rpow

lemma cubic_opt_identity (b L L₀ : ℝ) :
    (2 / 3 : ℝ) * (3 * b * L₀ ^ 2) * L₀ - (3 * b * L₀ ^ 2) * L + b * L ^ 3 =
    b * (L - L₀) ^ 2 * (L + 2 * L₀) := by
  ring

lemma cubic_opt_bound {b L L₀ : ℝ} (hb : 0 ≤ b) (hL : 0 ≤ L) (hL₀ : 0 ≤ L₀) :
    (3 * b * L₀ ^ 2) * L - b * L ^ 3 ≤ (2 / 3 : ℝ) * (3 * b * L₀ ^ 2) * L₀ := by
  have hid := cubic_opt_identity b L L₀
  have hpos : 0 ≤ b * (L - L₀) ^ 2 * (L + 2 * L₀) := by
    have : 0 ≤ (L - L₀) ^ 2 := sq_nonneg _
    have : 0 ≤ L + 2 * L₀ := by linarith
    positivity
  linarith

lemma cubic_opt_bound_a {a b L : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hL : 0 ≤ L) :
    a * L - b * L ^ 3 ≤ (2 / 3 : ℝ) * a * Real.sqrt (a / (3 * b)) := by
  have hb3 : 0 < 3 * b := by linarith
  have hdiv_nonneg : 0 ≤ a / (3 * b) := div_nonneg ha hb3.le
  set L₀ := Real.sqrt (a / (3 * b))
  have hL₀_nonneg : 0 ≤ L₀ := Real.sqrt_nonneg _
  have hL₀_sq : L₀ ^ 2 = a / (3 * b) := Real.sq_sqrt hdiv_nonneg
  have ha_eq : 3 * b * L₀ ^ 2 = a := by
    rw [hL₀_sq]
    exact mul_div_cancel₀ a (by linarith : 3 * b ≠ 0)
  have h_bound := cubic_opt_bound hb.le hL hL₀_nonneg
  rw [ha_eq] at h_bound
  exact h_bound

lemma sqrt_div_mul_eq (a cvk ℓ : ℝ) (_ha : 0 ≤ a) (hcvk : 0 < cvk) (hℓ : 0 < ℓ) :
    Real.sqrt (a / (3 * (cvk / (4 * ℓ ^ 2)))) = (2 * ℓ / Real.sqrt (3 * cvk)) * Real.sqrt a := by
  have hb3_pos : 0 < 3 * (cvk / (4 * ℓ ^ 2)) := by positivity
  have h_rew : a / (3 * (cvk / (4 * ℓ ^ 2))) = (4 * ℓ ^ 2 / (3 * cvk)) * a := by
    have : 3 * (cvk / (4 * ℓ ^ 2)) ≠ 0 := by positivity
    have : 4 * ℓ ^ 2 ≠ 0 := by positivity
    have : 3 * cvk ≠ 0 := by positivity
    field_simp
  rw [h_rew, Real.sqrt_mul (by positivity)]
  have h_sq : Real.sqrt (4 * ℓ ^ 2 / (3 * cvk)) = 2 * ℓ / Real.sqrt (3 * cvk) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt 4 = 2 by norm_num]
    rw [Real.sqrt_sq hℓ.le]
  rw [h_sq]

lemma a_sqrt_a_sq (a : ℝ) (ha : 0 ≤ a) : (a * Real.sqrt a) ^ 2 = a ^ 3 := by
  have : (a * Real.sqrt a) ^ 2 = a ^ 2 * (Real.sqrt a) ^ 2 := mul_pow a (Real.sqrt a) 2
  rw [this, Real.sq_sqrt ha]
  ring

lemma rpow_two_thirds_cube (x : ℝ) (hx : 0 ≤ x) : (x ^ (2 / 3 : ℝ)) ^ 3 = x ^ 2 := by
  have h1 : (x ^ (2 / 3 : ℝ)) ^ 3 = (x ^ (2 / 3 : ℝ)) ^ (3 : ℝ) := by norm_cast
  rw [h1, ← Real.rpow_mul hx]
  have : (2 / 3 : ℝ) * 3 = 2 := by norm_num
  rw [this, Real.rpow_two]

lemma a_sqrt_a_le (a c ℓ : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hℓ : 0 < ℓ)
    (hlogℓ : 0 ≤ Real.log ℓ)
    (ha_le : a ≤ c * (Real.log ℓ) ^ (2 / 3 : ℝ) / ℓ ^ (2 / 3 : ℝ)) :
    a * Real.sqrt a ≤ (c * Real.sqrt c) * Real.log ℓ / ℓ := by
  have h_cube : a ^ 3 ≤ (c * (Real.log ℓ) ^ (2 / 3 : ℝ) / ℓ ^ (2 / 3 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ ha ha_le 3
  have h_rhs_cube : (c * (Real.log ℓ) ^ (2 / 3 : ℝ) / ℓ ^ (2 / 3 : ℝ)) ^ 3 =
      c ^ 3 * (Real.log ℓ) ^ 2 / ℓ ^ 2 := by
    have : (c * (Real.log ℓ) ^ (2 / 3 : ℝ) / ℓ ^ (2 / 3 : ℝ)) ^ 3 =
        c ^ 3 * ((Real.log ℓ) ^ (2 / 3 : ℝ)) ^ 3 / (ℓ ^ (2 / 3 : ℝ)) ^ 3 := by ring
    rw [this, rpow_two_thirds_cube (Real.log ℓ) hlogℓ, rpow_two_thirds_cube ℓ hℓ.le]
  rw [h_rhs_cube] at h_cube
  have h_sq1 : (a * Real.sqrt a) ^ 2 = a ^ 3 := a_sqrt_a_sq a ha
  have h_sq2 : ((c * Real.sqrt c) * Real.log ℓ / ℓ) ^ 2 = c ^ 3 * (Real.log ℓ) ^ 2 / ℓ ^ 2 := by
    have : ((c * Real.sqrt c) * Real.log ℓ / ℓ) ^ 2 =
        (c * Real.sqrt c) ^ 2 * (Real.log ℓ) ^ 2 / ℓ ^ 2 := by ring
    rw [this, a_sqrt_a_sq c hc]
  have h_sq_le : (a * Real.sqrt a) ^ 2 ≤ ((c * Real.sqrt c) * Real.log ℓ / ℓ) ^ 2 := by
    rw [h_sq1, h_sq2]
    exact h_cube
  have h1_pos : 0 ≤ a * Real.sqrt a := by positivity
  have h2_pos : 0 ≤ (c * Real.sqrt c) * Real.log ℓ / ℓ := by positivity
  have h_abs : |a * Real.sqrt a| ≤ |(c * Real.sqrt c) * Real.log ℓ / ℓ| := sq_le_sq.mp h_sq_le
  rwa [abs_of_nonneg h1_pos, abs_of_nonneg h2_pos] at h_abs

lemma regime_c_exp_le (a c cvk ℓ L : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hcvk : 0 < cvk)
    (hℓ : 0 < ℓ) (hlogℓ : 0 ≤ Real.log ℓ) (hL : 0 ≤ L)
    (ha_le : a ≤ c * (Real.log ℓ) ^ (2 / 3 : ℝ) / ℓ ^ (2 / 3 : ℝ)) :
    a * L - (cvk / (4 * ℓ ^ 2)) * L ^ 3 ≤
      ((4 * (c * Real.sqrt c)) / (3 * Real.sqrt (3 * cvk))) * Real.log ℓ := by
  have hb_pos : 0 < cvk / (4 * ℓ ^ 2) := by positivity
  have h_cubic := cubic_opt_bound_a ha hb_pos hL
  refine h_cubic.trans ?_
  rw [sqrt_div_mul_eq a cvk ℓ ha hcvk hℓ]
  have h_a_sqrt := a_sqrt_a_le a c ℓ ha hc hℓ hlogℓ ha_le
  have h_factor_nonneg : 0 ≤ 4 / (3 * Real.sqrt (3 * cvk)) := by positivity
  have h_alg : (2 / 3 : ℝ) * a * ((2 * ℓ / Real.sqrt (3 * cvk)) * Real.sqrt a) =
      (4 / (3 * Real.sqrt (3 * cvk))) * ((a * Real.sqrt a) * ℓ) := by ring
  rw [h_alg]
  have h_mul_ℓ : (a * Real.sqrt a) * ℓ ≤ (c * Real.sqrt c) * Real.log ℓ := by
    have := mul_le_mul_of_nonneg_right h_a_sqrt hℓ.le
    rw [div_mul_cancel₀ _ hℓ.ne'] at this
    exact this
  have h_final := mul_le_mul_of_nonneg_left h_mul_ℓ h_factor_nonneg
  have h_final_rew : (4 / (3 * Real.sqrt (3 * cvk))) * ((c * Real.sqrt c) * Real.log ℓ) =
      ((4 * (c * Real.sqrt c)) / (3 * Real.sqrt (3 * cvk))) * Real.log ℓ := by ring
  rwa [h_final_rew] at h_final

lemma regime_c_k_properties {L ℓ : ℝ} (hL : 0 < L) (hℓ9 : 9 * L < ℓ) :
    let k := Nat.ceil (ℓ / L)
    10 ≤ k ∧ (k - 1 : ℝ) * L ≤ ℓ ∧ ℓ ≤ (k : ℝ) * L ∧ (k : ℝ) ≤ 2 * ℓ / L := by
  intro k
  have hdiv_gt9 : 9 < ℓ / L := (lt_div_iff₀ hL).mpr hℓ9
  have hdiv_pos : 0 ≤ ℓ / L := by linarith
  have hk_ge10 : 10 ≤ k := by
    dsimp [k]
    have : 9 < Nat.ceil (ℓ / L) := Nat.lt_ceil.mpr hdiv_gt9
    omega
  have h_le_ceil : ℓ / L ≤ (k : ℝ) := Nat.le_ceil (ℓ / L)
  have h_ceil_lt : (k : ℝ) < ℓ / L + 1 := Nat.ceil_lt_add_one hdiv_pos
  have h_k_le : (k : ℝ) ≤ 2 * ℓ / L := by
    have h1 : 1 ≤ ℓ / L := by linarith
    have h2 : (k : ℝ) ≤ 2 * (ℓ / L) := by linarith
    have h_rew : 2 * (ℓ / L) = 2 * ℓ / L := by ring
    rwa [h_rew] at h2
  refine ⟨hk_ge10, ?_, ?_, h_k_le⟩
  · have h1 : (k : ℝ) - 1 ≤ ℓ / L := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hL.le
    rwa [div_mul_cancel₀ ℓ hL.ne'] at h2
  · have h2 := mul_le_mul_of_nonneg_right h_le_ceil hL.le
    rwa [div_mul_cancel₀ ℓ hL.ne'] at h2

lemma nat_pow_eq_exp_log {N : ℕ} (hN : 0 < N) (m : ℕ) :
    (N : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log (N : ℝ)) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  rw [← Real.rpow_natCast (N : ℝ) m]
  rw [Real.rpow_def_of_pos hN_pos]
  rw [mul_comm]

lemma regime_c_rpow_bounds {N : ℕ} {T : ℝ} (hN : 2 ≤ N) (hT : 0 < T) (k : ℕ) (hk : 1 ≤ k)
    (h1 : ((k : ℝ) - 1) * Real.log (N : ℝ) ≤ Real.log T)
    (h2 : Real.log T ≤ (k : ℝ) * Real.log (N : ℝ)) :
    (N : ℝ) ^ (k - 1) ≤ T ∧ T ≤ (N : ℝ) ^ k := by
  have hN_pos : 0 < N := by omega
  have h_rpow1 := nat_pow_eq_exp_log hN_pos (k - 1)
  have h_rpow2 := nat_pow_eq_exp_log hN_pos k
  constructor
  · rw [h_rpow1]
    have h_cast : (((k - 1 : ℕ) : ℝ)) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk, Nat.cast_one]
    rw [h_cast]
    have h_le : Real.exp (((k : ℝ) - 1) * Real.log (N : ℝ)) ≤ Real.exp (Real.log T) :=
      Real.exp_le_exp.mpr h1
    rwa [Real.exp_log hT] at h_le
  · rw [h_rpow2]
    have h_le : Real.exp (Real.log T) ≤ Real.exp ((k : ℝ) * Real.log (N : ℝ)) :=
      Real.exp_le_exp.mpr h2
    rwa [Real.exp_log hT] at h_le

lemma regime_c_bound_exponent (c L ℓ : ℝ) (k : ℕ) (_hk10 : 10 ≤ k)
    (hc : 0 < c) (hL : 0 < L) (_hℓ : 0 < ℓ) (hk_le : (k : ℝ) ≤ 2 * ℓ / L) :
    - (c / (k : ℝ) ^ 2) * L ≤ - (c / (4 * ℓ ^ 2)) * L ^ 3 := by
  have hkL : (k : ℝ) * L ≤ 2 * ℓ := by
    have := mul_le_mul_of_nonneg_right hk_le hL.le
    rwa [div_mul_cancel₀ (2 * ℓ) hL.ne'] at this
  have _hk_pos : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have _hkL_pos : 0 ≤ (k : ℝ) * L := by positivity
  have h_sq : ((k : ℝ) * L) ^ 2 ≤ (2 * ℓ) ^ 2 := by nlinarith
  have h_pos1 : 0 < (k : ℝ) ^ 2 := by positivity
  have h_pos2 : 0 < 4 * ℓ ^ 2 := by positivity
  have h_equiv : (c / (4 * ℓ ^ 2)) * L ^ 3 ≤ (c / (k : ℝ) ^ 2) * L := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    rw [div_le_div_iff₀ h_pos2 h_pos1]
    have hLHS : c * L ^ 3 * (k : ℝ) ^ 2 = (c * L) * ((k : ℝ) * L) ^ 2 := by ring
    have hRHS : c * L * (4 * ℓ ^ 2) = (c * L) * (2 * ℓ) ^ 2 := by ring
    rw [hLHS, hRHS]
    exact mul_le_mul_of_nonneg_left h_sq (by positivity)
  linarith

lemma rpow_product_eq_exp {N : ℕ} (_hN : 2 ≤ N) (σ c : ℝ) (k : ℕ) :
    (N : ℝ) ^ (-σ) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) =
    Real.exp (((1 - σ) - c / (k : ℝ) ^ 2) * Real.log (N : ℝ)) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  rw [← Real.rpow_add hN_pos]
  rw [Real.rpow_def_of_pos hN_pos]
  congr 1
  ring

lemma exp_mul_log_eq_rpow {ℓ A₁ : ℝ} (hℓ : 0 < ℓ) :
    Real.exp (A₁ * Real.log ℓ) = ℓ ^ A₁ := by
  rw [Real.rpow_def_of_pos hℓ, mul_comm]

lemma ge_two_of_rpow_ninth_le {N : ℕ} {T : ℝ} (hT : 3 ≤ T)
    (h : T ^ (1 / 9 : ℝ) ≤ (N : ℝ)) : 2 ≤ N := by
  by_contra! hN
  have : N ≤ 1 := by omega
  have hN_le : (N : ℝ) ≤ 1 := by exact_mod_cast this
  have hT1 : (1 : ℝ) < T ^ (1 / 9 : ℝ) := by
    nth_rw 1 [← Real.one_rpow (1 / 9 : ℝ)]
    exact Real.rpow_lt_rpow (by norm_num) (by linarith) (by norm_num)
  linarith

lemma le_rpow_nine_of_rpow_ninth_le {N : ℕ} {T : ℝ} (_hN : 2 ≤ N) (hT : 0 < T)
    (h : T ^ (1 / 9 : ℝ) ≤ (N : ℝ)) : T ≤ (N : ℝ) ^ 9 := by
  have h_pow := Real.rpow_le_rpow (by positivity) h (by norm_num : 0 ≤ (9 : ℝ))
  rw [← Real.rpow_mul hT.le] at h_pow
  have : (1 / 9 : ℝ) * 9 = 1 := by norm_num
  rw [this, Real.rpow_one] at h_pow
  have : (N : ℝ) ^ (9 : ℝ) = (N : ℝ) ^ 9 := Real.rpow_natCast (N : ℝ) 9
  rw [this] at h_pow
  exact h_pow

lemma regime_a_bound {N : ℕ} {T σ : ℝ} (hT : 3 ≤ T)
    (hσ1 : 3 / 4 ≤ σ) (hσ2 : σ ≤ 1)
    (hNT : T ≤ (N : ℝ)) (hNT2 : (N : ℝ) ≤ T ^ 2) :
    (N : ℝ) ^ (-σ) * (Real.sqrt T + (N : ℝ) / Real.sqrt T) ≤ 2 := by
  have hT_pos : 0 < T := by linarith
  have hT_ge1 : 1 ≤ T := by linarith
  have hN_pos : (0 : ℝ) < (N : ℝ) := by linarith
  have h_sqrtT : Real.sqrt T = T ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow T
  have h_div_sqrtT : (N : ℝ) / T ^ (1 / 2 : ℝ) = (N : ℝ) * T ^ (- (1 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hT_pos.le]
  have h_exp : (N : ℝ) ^ (-σ) * (Real.sqrt T + (N : ℝ) / Real.sqrt T) =
      (N : ℝ) ^ (-σ) * T ^ (1 / 2 : ℝ) + (N : ℝ) ^ (1 - σ) * T ^ (- (1 / 2 : ℝ)) := by
    rw [mul_add, h_sqrtT, h_div_sqrtT]
    congr 1
    have hN1 : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
    nth_rw 2 [hN1]
    rw [← mul_assoc, ← Real.rpow_add hN_pos]
    congr 2
    ring
  rw [h_exp]
  have h_term1 : (N : ℝ) ^ (-σ) * T ^ (1 / 2 : ℝ) ≤ 1 := by
    have h1 : (N : ℝ) ^ (-σ) ≤ T ^ (-σ) := by
      exact Real.rpow_le_rpow_of_nonpos hT_pos hNT (by linarith)
    have h2 : (N : ℝ) ^ (-σ) * T ^ (1 / 2 : ℝ) ≤ T ^ (-σ) * T ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    refine h2.trans ?_
    rw [← Real.rpow_add hT_pos]
    have : -σ + 1 / 2 ≤ 0 := by linarith
    have h3 : T ^ (-σ + 1 / 2) ≤ T ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT_ge1 this
    rw [Real.rpow_zero] at h3
    exact h3
  have h_term2 : (N : ℝ) ^ (1 - σ) * T ^ (- (1 / 2 : ℝ)) ≤ 1 := by
    have hNT2_rpow : (N : ℝ) ≤ T ^ (2 : ℝ) := by
      rw [Real.rpow_two]
      exact hNT2
    have h1 : (N : ℝ) ^ (1 - σ) ≤ (T ^ (2 : ℝ)) ^ (1 - σ) := by
      exact Real.rpow_le_rpow (by positivity) hNT2_rpow (by linarith)
    rw [← Real.rpow_mul hT_pos.le] at h1
    have h2 : (N : ℝ) ^ (1 - σ) * T ^ (- (1 / 2 : ℝ)) ≤ T ^ (2 * (1 - σ)) * T ^ (- (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    refine h2.trans ?_
    rw [← Real.rpow_add hT_pos]
    have : 2 * (1 - σ) + - (1 / 2 : ℝ) ≤ 0 := by linarith
    have h3 : T ^ (2 * (1 - σ) + - (1 / 2 : ℝ)) ≤ T ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT_ge1 this
    rw [Real.rpow_zero] at h3
    exact h3
  linarith

lemma step2_bound_gen {ℓ A₁ CE A C_zeta : ℝ} (hℓ3 : Real.log 3 ≤ ℓ)
    (hA₁ : 0 < A₁) (hCE : 1 ≤ CE) (hC_zeta : 0 < C_zeta)
    (hone_lt_log3 : 1 < Real.log 3)
    (hloglog3 : 0 < Real.log (Real.log 3))
    (hA : A₁ + 1 + Real.log (2 * C_zeta * CE + 1) / Real.log (Real.log 3) ≤ A) :
    C_zeta * (1 + ℓ * (CE * ℓ ^ A₁)) ≤ ℓ ^ A := by
  have hCE_pos : 0 < CE := by linarith
  have _h2C_pos : 0 < 2 * C_zeta * CE := by positivity
  have hCmult_pos : 0 < 2 * C_zeta * CE + 1 := by positivity
  have hCmult_gt1 : 1 < 2 * C_zeta * CE + 1 := by linarith
  have hlog_Cmult_pos : 0 < Real.log (2 * C_zeta * CE + 1) := Real.log_pos hCmult_gt1
  have hℓ_gt1 : 1 < ℓ := lt_of_lt_of_le hone_lt_log3 hℓ3
  have hℓ_pos : 0 < ℓ := by linarith
  have hlogℓ_pos : 0 < Real.log ℓ := Real.log_pos hℓ_gt1
  have hloglog3_le : Real.log (Real.log 3) ≤ Real.log ℓ :=
    Real.log_le_log (by linarith) hℓ3
  have h_rpow_pos : 1 ≤ ℓ ^ (A₁ + 1) := by
    nth_rw 1 [← Real.one_rpow (A₁ + 1)]
    refine Real.rpow_le_rpow (by norm_num) hℓ_gt1.le (by linarith)
  have h_prod : ℓ * (CE * ℓ ^ A₁) = CE * ℓ ^ (A₁ + 1) := by
    have h_rpow_add : ℓ ^ A₁ * ℓ = ℓ ^ (A₁ + 1) := by
      have : ℓ = ℓ ^ (1 : ℝ) := (Real.rpow_one ℓ).symm
      nth_rw 2 [this]
      rw [← Real.rpow_add hℓ_pos]
    calc ℓ * (CE * ℓ ^ A₁) = CE * (ℓ ^ A₁ * ℓ) := by ring
      _ = CE * ℓ ^ (A₁ + 1) := by rw [h_rpow_add]
  rw [h_prod]
  have h_term_le : C_zeta * (1 + CE * ℓ ^ (A₁ + 1)) ≤ 2 * C_zeta * CE * ℓ ^ (A₁ + 1) := by
    have h_le : 1 ≤ CE * ℓ ^ (A₁ + 1) := by
      calc (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ CE * ℓ ^ (A₁ + 1) := mul_le_mul hCE h_rpow_pos (by norm_num) hCE_pos.le
    calc C_zeta * (1 + CE * ℓ ^ (A₁ + 1))
      _ ≤ C_zeta * (CE * ℓ ^ (A₁ + 1) + CE * ℓ ^ (A₁ + 1)) := by
        refine mul_le_mul_of_nonneg_left ?_ hC_zeta.le
        linarith
      _ = 2 * C_zeta * CE * ℓ ^ (A₁ + 1) := by ring
  refine h_term_le.trans ?_
  set Δ := A - (A₁ + 1)
  have hΔ_ge : Real.log (2 * C_zeta * CE + 1) / Real.log (Real.log 3) ≤ Δ := by
    dsimp [Δ]; linarith
  have h_div_nonneg : 0 ≤ Real.log (2 * C_zeta * CE + 1) / Real.log (Real.log 3) :=
    div_nonneg hlog_Cmult_pos.le hloglog3.le
  have h_exp_le : 2 * C_zeta * CE ≤ ℓ ^ Δ := by
    have h_le_Cmult : 2 * C_zeta * CE ≤ 2 * C_zeta * CE + 1 := by linarith
    refine h_le_Cmult.trans ?_
    rw [Real.rpow_def_of_pos hℓ_pos]
    have h_log_le : Real.log (2 * C_zeta * CE + 1) ≤ Real.log ℓ * Δ := by
      have h1 : Real.log (2 * C_zeta * CE + 1) =
          Real.log (Real.log 3) * (Real.log (2 * C_zeta * CE + 1) / Real.log (Real.log 3)) := by
        exact (mul_div_cancel₀ (Real.log (2 * C_zeta * CE + 1)) hloglog3.ne').symm
      rw [h1]
      have : Real.log (Real.log 3) * (Real.log (2 * C_zeta * CE + 1) / Real.log (Real.log 3)) ≤ Real.log ℓ * Δ :=
        mul_le_mul hloglog3_le hΔ_ge h_div_nonneg hlogℓ_pos.le
      exact this
    have h_exp := Real.exp_le_exp.mpr h_log_le
    rw [Real.exp_log hCmult_pos] at h_exp
    exact h_exp
  have h_pow_comb : 2 * C_zeta * CE * ℓ ^ (A₁ + 1) ≤ ℓ ^ Δ * ℓ ^ (A₁ + 1) :=
    mul_le_mul_of_nonneg_right h_exp_le (by positivity)
  refine h_pow_comb.trans ?_
  rw [← Real.rpow_add hℓ_pos]
  have h_exp_eq : Δ + (A₁ + 1) = A := by
    dsimp [Δ]; ring
  rw [h_exp_eq]

/-- Vinogradov-Korobov bound for the Riemann zeta function near the 1-line, conditional
on the bilinear exponential sum estimate. -/
theorem norm_riemannZeta_le_of_bilinear (h : BilinearEstimate (1 / 30)) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ (σ t : ℝ), 3 ≤ |t| →
      1 - c * (Real.log (Real.log |t|)) ^ (2 / 3 : ℝ) / (Real.log |t|) ^ (2 / 3 : ℝ) ≤ σ → σ ≤ 1 →
      ‖riemannZeta (σ + t * Complex.I)‖ ≤ (Real.log |t|) ^ A := by
  rcases vinogradov_expsum_regime_subblock h with ⟨c_vk, C_vk, hc_vk, _hC_vk, h_vk⟩
  rcases Erdos1201.MR.norm_sum_exp_neg_log_mul_I_le_pow_iterated 9 (by norm_num) with ⟨c_vdc, C_vdc, hc_vdc, _hC_vdc, h_vdc⟩
  rcases Erdos1201.MR.norm_sum_exp_neg_log_mul_I_subblock_le with ⟨C_sub, _hC_sub, h_sub⟩
  let c : ℝ := min (1 / 8 : ℝ) c_vdc
  have hc_pos : 0 < c := lt_min (by norm_num) hc_vdc
  have hc_le_one_eighth : c ≤ 1 / 8 := min_le_left _ _
  have hc_le_vdc : c ≤ c_vdc := min_le_right _ _
  let A₁ : ℝ := (4 * (c * Real.sqrt c)) / (3 * Real.sqrt (3 * c_vk))
  have hA₁_pos : 0 < A₁ := by
    have : 0 < c * Real.sqrt c := mul_pos hc_pos (Real.sqrt_pos.mpr hc_pos)
    have : 0 < Real.sqrt (3 * c_vk) := Real.sqrt_pos.mpr (by linarith)
    positivity
  let C_E : ℝ := max 1 (max (2 * C_sub) (max C_vdc C_vk))
  have hC_E_ge1 : 1 ≤ C_E := le_max_left 1 _
  have hC_E_pos : 0 < C_E := by linarith
  have hC_E_sub : 2 * C_sub ≤ C_E := le_trans (le_max_left (2 * C_sub) _) (le_max_right 1 _)
  have hC_E_vdc : C_vdc ≤ C_E := le_trans (le_max_left C_vdc C_vk) (le_trans (le_max_right (2 * C_sub) _) (le_max_right 1 _))
  have hC_E_vk : C_vk ≤ C_E := le_trans (le_max_right C_vdc C_vk) (le_trans (le_max_right (2 * C_sub) _) (le_max_right 1 _))
  have hone_lt_log3 : 1 < Real.log 3 := one_lt_log_three'
  have hloglog3_pos : 0 < Real.log (Real.log 3) := log_log_three_pos'
  rcases norm_riemannZeta_le_dyadic_expsums with ⟨C_zeta, hC_zeta, h_zeta_bound⟩
  let A : ℝ := A₁ + 1 + max 0 (Real.log (2 * C_zeta * C_E + 1)) / Real.log (Real.log 3) + 1
  have hA_pos : 0 < A := by
    have : 0 ≤ max 0 (Real.log (2 * C_zeta * C_E + 1)) / Real.log (Real.log 3) := by
      exact div_nonneg (le_max_left 0 _) hloglog3_pos.le
    linarith
  use c, A, hc_pos, hA_pos
  intro σ t ht hσ1 hσ2
  set T := |t|
  have hT3 : 3 ≤ T := ht
  have hT_pos : 0 < T := by linarith
  have hℓ3 : Real.log 3 ≤ Real.log T := Real.log_le_log (by norm_num) hT3
  have hℓ_gt1 : 1 < Real.log T := lt_of_lt_of_le hone_lt_log3 hℓ3
  have hℓ_pos : 0 < Real.log T := by linarith
  have hloglogT_nonneg : 0 ≤ Real.log (Real.log T) := by
    rw [← Real.log_one]
    exact Real.log_le_log (by norm_num) hℓ_gt1.le
  have h_ratio_le1 := log_pow_two_thirds_div_le_one hT3
  have h_c_ratio_le : c * (Real.log (Real.log T)) ^ (2 / 3 : ℝ) / (Real.log T) ^ (2 / 3 : ℝ) ≤ c := by
    have : c * (Real.log (Real.log T)) ^ (2 / 3 : ℝ) / (Real.log T) ^ (2 / 3 : ℝ) =
        c * ((Real.log (Real.log T)) ^ (2 / 3 : ℝ) / (Real.log T) ^ (2 / 3 : ℝ)) := by ring
    rw [this]
    calc c * ((Real.log (Real.log T)) ^ (2 / 3 : ℝ) / (Real.log T) ^ (2 / 3 : ℝ))
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left h_ratio_le1 hc_pos.le
      _ = c := mul_one c
  have hσ_ge_34 : 3 / 4 ≤ σ := by
    have h1 : 1 - c ≤ σ := by linarith [hσ1, h_c_ratio_le]
    have h2 : 1 - (1 / 8 : ℝ) ≤ 1 - c := by linarith [hc_le_one_eighth]
    linarith
  have ht_ge2 : 2 ≤ |t| := by linarith
  have h_block_bound : ∀ (N : ℕ) (_ : 1 ≤ N ∧ (N : ℝ) ≤ t ^ 2) (M : ℕ) (_ : N < M ∧ M ≤ 2 * N),
      (N : ℝ) ^ (-σ) * ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
        C_E * (Real.log T) ^ A₁ := by
    intro N ⟨_hN1, hNt2⟩ M ⟨hNM, hM2N⟩
    rw [norm_sum_exp_neg_log_eq_abs]
    by_cases hN_eq1 : N = 1
    · subst hN_eq1
      have hM2 : M = 2 := by omega
      subst hM2
      have hIoc : Finset.Ioc 1 2 = {2} := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
      rw [hIoc, Finset.sum_singleton]
      rw [norm_exp_neg_log_mul_I]
      have h1_rpow : ((1 : ℕ) : ℝ) ^ (-σ) = 1 := by
        have : ((1 : ℕ) : ℝ) = 1 := by norm_num
        rw [this, Real.one_rpow]
      rw [h1_rpow, mul_one]
      have : 1 * 1 ≤ C_E * (Real.log T) ^ A₁ := by
        refine mul_le_mul hC_E_ge1 ?_ (by norm_num) hC_E_pos.le
        nth_rw 1 [← Real.one_rpow A₁]
        exact Real.rpow_le_rpow (by norm_num) hℓ_gt1.le hA₁_pos.le
      linarith
    · have hN2 : 2 ≤ N := by omega
      by_cases hNT : T < (N : ℝ)
      · have hNT2 : (N : ℝ) ≤ T ^ 2 := by
          have : t ^ 2 = T ^ 2 := (sq_abs t).symm
          linarith
        have h_regA := regime_a_bound hT3 hσ_ge_34 hσ2 hNT.le hNT2
        have h_sub_sum := h_sub N M T (by omega) hNM hM2N (by linarith)
        have h_prod : (N : ℝ) ^ (-σ) * ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((T * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
            (N : ℝ) ^ (-σ) * (C_sub * (Real.sqrt T + (N : ℝ) / Real.sqrt T)) :=
          mul_le_mul_of_nonneg_left h_sub_sum (by positivity)
        have h_alg : (N : ℝ) ^ (-σ) * (C_sub * (Real.sqrt T + (N : ℝ) / Real.sqrt T)) =
            C_sub * ((N : ℝ) ^ (-σ) * (Real.sqrt T + (N : ℝ) / Real.sqrt T)) := by ring
        rw [h_alg] at h_prod
        have h_prod2 : C_sub * ((N : ℝ) ^ (-σ) * (Real.sqrt T + (N : ℝ) / Real.sqrt T)) ≤ C_sub * 2 :=
          mul_le_mul_of_nonneg_left h_regA (by positivity)
        refine (h_prod.trans h_prod2).trans ?_
        have h_2Csub : C_sub * 2 ≤ C_E := by
          have : C_sub * 2 = 2 * C_sub := by ring
          rw [this]
          exact hC_E_sub
        have h_rpow_ge1 : 1 ≤ (Real.log T) ^ A₁ := by
          nth_rw 1 [← Real.one_rpow A₁]
          exact Real.rpow_le_rpow (by norm_num) hℓ_gt1.le hA₁_pos.le
        calc C_sub * 2 ≤ C_E := h_2Csub
          _ = C_E * 1 := (mul_one C_E).symm
          _ ≤ C_E * (Real.log T) ^ A₁ := mul_le_mul_of_nonneg_left h_rpow_ge1 hC_E_pos.le
      · have hN_le_T : (N : ℝ) ≤ T := not_lt.mp hNT
        by_cases hT9 : T ^ (1 / 9 : ℝ) ≤ (N : ℝ)
        · have hT_le_N9 := le_rpow_nine_of_rpow_ninth_le hN2 hT_pos hT9
          have h_vdc_sum := h_vdc N M T hN2 hNM hM2N hN_le_T hT_le_N9
          have h_prod : (N : ℝ) ^ (-σ) * ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((T * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
              (N : ℝ) ^ (-σ) * (C_vdc * (N : ℝ) ^ (1 - c_vdc)) :=
            mul_le_mul_of_nonneg_left h_vdc_sum (by positivity)
          have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
          have h_rew : (N : ℝ) ^ (-σ) * (C_vdc * (N : ℝ) ^ (1 - c_vdc)) =
              C_vdc * ((N : ℝ) ^ (-σ) * (N : ℝ) ^ (1 - c_vdc)) := by ring
          rw [h_rew, ← Real.rpow_add hN_pos] at h_prod
          have h_exp_add : -σ + (1 - c_vdc) = 1 - σ - c_vdc := by ring
          rw [h_exp_add] at h_prod
          have h_exp_nonpos : 1 - σ - c_vdc ≤ 0 := by
            have : 1 - c ≤ σ := by linarith [hσ1, h_c_ratio_le]
            linarith [hc_le_vdc]
          have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
          have h_pow_le1 : (N : ℝ) ^ (1 - σ - c_vdc) ≤ 1 := by
            have h_rpow0 := Real.rpow_le_rpow_of_exponent_le hN_ge1 h_exp_nonpos
            rw [Real.rpow_zero] at h_rpow0
            exact h_rpow0
          have h_prod2 : C_vdc * (N : ℝ) ^ (1 - σ - c_vdc) ≤ C_vdc * 1 :=
            mul_le_mul_of_nonneg_left h_pow_le1 (by positivity)
          rw [mul_one] at h_prod2
          refine (h_prod.trans h_prod2).trans ?_
          have h_rpow_ge1 : 1 ≤ (Real.log T) ^ A₁ := by
            nth_rw 1 [← Real.one_rpow A₁]
            exact Real.rpow_le_rpow (by norm_num) hℓ_gt1.le hA₁_pos.le
          calc C_vdc ≤ C_E := hC_E_vdc
            _ = C_E * 1 := (mul_one C_E).symm
            _ ≤ C_E * (Real.log T) ^ A₁ := mul_le_mul_of_nonneg_left h_rpow_ge1 hC_E_pos.le
        · have hN_lt_T9 : (N : ℝ) < T ^ (1 / 9 : ℝ) := not_le.mp hT9
          have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
          have hlogN_pos : 0 < Real.log (N : ℝ) := by
            have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
            exact Real.log_pos this
          have h_9logN_lt : 9 * Real.log (N : ℝ) < Real.log T := by
            have h_pow : (N : ℝ) ^ (9 : ℝ) < (T ^ (1 / 9 : ℝ)) ^ (9 : ℝ) :=
              Real.rpow_lt_rpow (by positivity) hN_lt_T9 (by norm_num)
            rw [← Real.rpow_mul hT_pos.le] at h_pow
            have : (1 / 9 : ℝ) * 9 = 1 := by norm_num
            rw [this, Real.rpow_one] at h_pow
            have h_log_lt : Real.log ((N : ℝ) ^ (9 : ℝ)) < Real.log T :=
              Real.log_lt_log (by positivity) h_pow
            rw [Real.log_rpow hN_pos] at h_log_lt
            linarith
          let k := Nat.ceil (Real.log T / Real.log (N : ℝ))
          have hk_props := regime_c_k_properties hlogN_pos h_9logN_lt
          rcases hk_props with ⟨hk10, hk_lower, hk_upper, hk_le⟩
          have hk1 : 1 ≤ k := by omega
          have h_rpow_bd := regime_c_rpow_bounds hN2 hT_pos k hk1 hk_lower hk_upper
          rcases h_rpow_bd with ⟨ht_ge, ht_le⟩
          have h_vk_sum := h_vk N M k T hN2 hNM hM2N hk10 ht_ge ht_le
          have h_prod : (N : ℝ) ^ (-σ) * ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((T * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
              (N : ℝ) ^ (-σ) * (C_vk * (N : ℝ) ^ (1 - c_vk / (k : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left h_vk_sum (by positivity)
          have h_rew : (N : ℝ) ^ (-σ) * (C_vk * (N : ℝ) ^ (1 - c_vk / (k : ℝ) ^ 2)) =
              C_vk * ((N : ℝ) ^ (-σ) * (N : ℝ) ^ (1 - c_vk / (k : ℝ) ^ 2)) := by ring
          rw [h_rew] at h_prod
          rw [rpow_product_eq_exp hN2 σ c_vk k] at h_prod
          have h_exp_bound := regime_c_bound_exponent c_vk (Real.log (N : ℝ)) (Real.log T) k hk10
              hc_vk hlogN_pos hℓ_pos hk_le
          have h_alg_exp : ((1 - σ) - c_vk / (k : ℝ) ^ 2) * Real.log (N : ℝ) =
              (1 - σ) * Real.log (N : ℝ) - (c_vk / (k : ℝ) ^ 2) * Real.log (N : ℝ) := by ring
          rw [h_alg_exp] at h_prod
          have h_exp_le1 : (1 - σ) * Real.log (N : ℝ) - (c_vk / (k : ℝ) ^ 2) * Real.log (N : ℝ) ≤
              (1 - σ) * Real.log (N : ℝ) - (c_vk / (4 * (Real.log T) ^ 2)) * (Real.log (N : ℝ)) ^ 3 := by
            linarith [h_exp_bound]
          have h_1subσ_nonneg : 0 ≤ 1 - σ := by linarith
          have h_1subσ_le : 1 - σ ≤ c * (Real.log (Real.log T)) ^ (2 / 3 : ℝ) / (Real.log T) ^ (2 / 3 : ℝ) := by linarith
          have h_opt := regime_c_exp_le (1 - σ) c c_vk (Real.log T) (Real.log (N : ℝ))
              h_1subσ_nonneg hc_pos.le hc_vk hℓ_pos hloglogT_nonneg hlogN_pos.le h_1subσ_le
          have h_total_exp : (1 - σ) * Real.log (N : ℝ) - (c_vk / (k : ℝ) ^ 2) * Real.log (N : ℝ) ≤
              A₁ * Real.log (Real.log T) := by
            refine le_trans h_exp_le1 ?_
            dsimp [A₁]
            exact h_opt
          have h_exp_total := Real.exp_le_exp.mpr h_total_exp
          rw [exp_mul_log_eq_rpow hℓ_pos] at h_exp_total
          have h_prod2 : C_vk * Real.exp ((1 - σ) * Real.log (N : ℝ) - c_vk / (k : ℝ) ^ 2 * Real.log (N : ℝ)) ≤
              C_vk * (Real.log T) ^ A₁ :=
            mul_le_mul_of_nonneg_left h_exp_total (by positivity)
          refine (h_prod.trans h_prod2).trans ?_
          exact mul_le_mul_of_nonneg_right hC_E_vk (by positivity)
  have h_zeta := h_zeta_bound σ t hσ_ge_34 hσ2 ht_ge2 (C_E * (Real.log T) ^ A₁) h_block_bound
  refine h_zeta.trans ?_
  have hA_le : A₁ + 1 + Real.log (2 * C_zeta * C_E + 1) / Real.log (Real.log 3) ≤ A := by
    dsimp [A]
    have : Real.log (2 * C_zeta * C_E + 1) ≤ max 0 (Real.log (2 * C_zeta * C_E + 1)) := le_max_right 0 _
    have : Real.log (2 * C_zeta * C_E + 1) / Real.log (Real.log 3) ≤
        max 0 (Real.log (2 * C_zeta * C_E + 1)) / Real.log (Real.log 3) :=
      div_le_div_of_nonneg_right this hloglog3_pos.le
    linarith
  exact step2_bound_gen hℓ3 hA₁_pos hC_E_ge1 hC_zeta hone_lt_log3 hloglog3_pos hA_le

end Erdos1201.MR.Vinogradov

