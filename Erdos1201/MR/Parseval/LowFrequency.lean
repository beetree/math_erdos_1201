import Mathlib
import Erdos1201.MR.Parseval.HighFrequency
import Erdos1201.MR.Parseval.WindowKernel
import Erdos1201.MR.Analysis.DirichletPolyBasics

/-!
The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

namespace Erdos1201.MR

open Complex

lemma cont_wk (u : ℝ) (hu : 0 < u) : Continuous (fun t : ℝ => windowKernel u t) := by
  unfold windowKernel
  apply Continuous.div
  · apply Continuous.sub
    · apply Continuous.cpow
      · exact continuous_const
      · exact continuous_const.add (continuous_ofReal.mul continuous_const)
      · intro t
        rw [Complex.mem_slitPlane_iff]
        left
        simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
        linarith
    · exact continuous_const
  · exact continuous_const.add (continuous_ofReal.mul continuous_const)
  · intro x h
    have h_re : ((1 : ℂ) + (x : ℂ) * I).re = (0 : ℂ).re := by rw [h]
    simp at h_re

lemma cont_dp (a : ℕ → ℂ) (N : Finset ℕ) (hN : ∀ n ∈ N, 0 < n) : Continuous (fun t : ℝ => dirichletPoly a N (1 + ↑t * I)) := by
  unfold dirichletPoly
  apply continuous_finsetSum
  intro n hn
  apply Continuous.mul
  · exact continuous_const
  · apply Continuous.cpow
    · exact continuous_const
    · exact (continuous_const.add (continuous_ofReal.mul continuous_const)).neg
    · intro t
      rw [Complex.mem_slitPlane_iff]
      left
      have h1 := hN n hn
      have h2 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr h1
      simp only [Complex.natCast_re]
      exact h2

lemma cont_exp (y : ℝ) : Continuous (fun t : ℝ => exp (↑t * ↑y * I)) := by
  apply continuous_exp.comp
  exact (continuous_ofReal.mul continuous_const).mul continuous_const

lemma int_sub_lemma (f g : ℝ → ℂ) (a b : ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ t in a..b, f t) - (∫ t in a..b, g t) = ∫ t in a..b, (f t - g t) :=
  (intervalIntegral.integral_sub (hf.intervalIntegrable a b) (hg.intervalIntegrable a b)).symm

lemma norm_exp_sub_exp_le (t y y' : ℝ) : ‖exp (↑t * ↑y * I) - exp (↑t * ↑y' * I)‖ ≤ |t| * |y - y'| := by
  have h_eq : exp (↑t * ↑y * I) - exp (↑t * ↑y' * I) =
      exp (↑(t * y') * I) * (exp (I * ↑(t * (y - y'))) - 1) := by
    rw [mul_sub, mul_one, ← exp_add]
    have h1 : (↑t : ℂ) * ↑y * I = ↑(t * y') * I + I * ↑(t * (y - y')) := by push_cast; ring
    have h2 : (↑t : ℂ) * ↑y' * I = ↑(t * y') * I := by push_cast; ring
    rw [h1, h2]
  rw [h_eq, norm_mul, norm_exp_ofReal_mul_I, one_mul, norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  calc
    2 * |Real.sin (t * (y - y') / 2)| ≤ 2 * |t * (y - y') / 2| := mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = |t * (y - y')| := by
      rw [abs_div, abs_two]
      ring_nf
    _ = |t| * |y - y'| := abs_mul t (y - y')

theorem norm_lowPart_le (a : ℕ → ℂ) (N : Finset ℕ) (u T₀ y : ℝ) (hu : 0 < u) (hu' : u ≤ 1 / 2) (hT₀ : 0 < T₀) (hN : ∀ n ∈ N, 0 < n) :
    ‖lowPart a N u T₀ y‖ ≤ (2 * T₀ / Real.pi) * u * ∑ n ∈ N, ‖a n‖ / n := by
  unfold lowPart
  rw [norm_mul, norm_div, norm_one, norm_mul, Complex.norm_real]
  have h1_n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h2_n : ‖Real.pi‖ = Real.pi := abs_of_pos Real.pi_pos
  rw [h1_n, h2_n]
  have h_int : ‖∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y * I)‖ ≤ (2 * u * ∑ n ∈ N, ‖a n‖ / n) * |T₀ - -T₀| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have hy : ↑t * ↑y * I = ↑(t * y) * I := by push_cast; ring
    rw [norm_mul, norm_mul, hy, norm_exp_ofReal_mul_I, mul_one]
    have h1 : ‖dirichletPoly a N (1 + ↑t * I)‖ ≤ ∑ n ∈ N, ‖a n‖ / n := norm_dirichletPoly_le a N hN t
    have h2 : ‖windowKernel u t‖ ≤ 2 * u := norm_windowKernel_le_mul u t hu (by linarith)
    nlinarith [norm_nonneg (dirichletPoly a N (1 + ↑t * I))]
  have hz : 0 ≤ ∑ n ∈ N, ‖a n‖ / (n : ℝ) := Finset.sum_nonneg (fun i _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have hT0_abs : |T₀ - -T₀| = 2 * T₀ := by
    have h_eq_t : T₀ - -T₀ = 2 * T₀ := by ring
    rw [h_eq_t, abs_of_pos (by linarith)]
  rw [hT0_abs] at h_int
  calc
    1 / (2 * Real.pi) * ‖∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y * I)‖
      ≤ 1 / (2 * Real.pi) * ((2 * u * ∑ n ∈ N, ‖a n‖ / n) * (2 * T₀)) := by gcongr
    _ = (2 * T₀ / Real.pi) * u * ∑ n ∈ N, ‖a n‖ / n := by ring

theorem norm_lowPart_div_sub_le (a : ℕ → ℂ) (N : Finset ℕ) (u₁ u₂ T₀ y : ℝ) (h1 : 0 < u₁) (h1' : u₁ ≤ 1 / 2) (h2 : 0 < u₂) (h2' : u₂ ≤ 1 / 2) (hT₀ : 0 < T₀) (hN : ∀ n ∈ N, 0 < n) :
    ‖lowPart a N u₁ T₀ y / u₁ - lowPart a N u₂ T₀ y / u₂‖ ≤ (8 * T₀ * (1 + T₀) / Real.pi) * (u₁ + u₂) * ∑ n ∈ N, ‖a n‖ / n := by
  have hz : 0 ≤ ∑ n ∈ N, ‖a n‖ / (n : ℝ) := Finset.sum_nonneg (fun i _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have h_eq : lowPart a N u₁ T₀ y / u₁ - lowPart a N u₂ T₀ y / u₂ =
      (1 / (2 * ↑Real.pi) : ℂ) * ∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * (windowKernel u₁ t / u₁ - windowKernel u₂ t / u₂) * exp (↑t * ↑y * I) := by
    unfold lowPart
    have h_div1 : (∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u₁ t * exp (↑t * ↑y * I)) / (u₁ : ℂ) =
      ∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u₁ t * exp (↑t * ↑y * I) / (u₁ : ℂ) := (intervalIntegral.integral_div (u₁ : ℂ) _).symm
    have h_div2 : (∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u₂ t * exp (↑t * ↑y * I)) / (u₂ : ℂ) =
      ∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u₂ t * exp (↑t * ↑y * I) / (u₂ : ℂ) := (intervalIntegral.integral_div (u₂ : ℂ) _).symm
    calc
      ((1 / (2 * ↑Real.pi) : ℂ) * ∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u₁ t * exp (↑t * ↑y * I)) / u₁ -
      ((1 / (2 * ↑Real.pi) : ℂ) * ∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u₂ t * exp (↑t * ↑y * I)) / u₂
      _ = (1 / (2 * ↑Real.pi) : ℂ) * ((∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u₁ t * exp (↑t * ↑y * I)) / u₁ -
                                   (∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u₂ t * exp (↑t * ↑y * I)) / u₂) := by ring
      _ = (1 / (2 * ↑Real.pi) : ℂ) * ((∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u₁ t * exp (↑t * ↑y * I) / u₁) -
                                   (∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u₂ t * exp (↑t * ↑y * I) / u₂)) := by
        congr 1
        rw [h_div1, h_div2]
      _ = (1 / (2 * ↑Real.pi) : ℂ) * ∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * (windowKernel u₁ t / u₁ - windowKernel u₂ t / u₂) * exp (↑t * ↑y * I) := by
        congr 1
        rw [int_sub_lemma]
        · congr 1
          ext t
          ring
        · apply Continuous.div
          · exact ((cont_dp a N hN).mul (cont_wk u₁ h1)).mul (cont_exp y)
          · exact continuous_const
          · intro _x; exact_mod_cast ne_of_gt h1
        · apply Continuous.div
          · exact ((cont_dp a N hN).mul (cont_wk u₂ h2)).mul (cont_exp y)
          · exact continuous_const
          · intro _x; exact_mod_cast ne_of_gt h2
  rw [h_eq, norm_mul, norm_div, norm_one, norm_mul, Complex.norm_real]
  have h1_n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h2_n : ‖Real.pi‖ = Real.pi := abs_of_pos Real.pi_pos
  rw [h1_n, h2_n]
  have h_int : ‖∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * (windowKernel u₁ t / u₁ - windowKernel u₂ t / u₂) * exp (↑t * ↑y * I)‖ ≤ (8 * (1 + T₀) * (u₁ + u₂) * ∑ n ∈ N, ‖a n‖ / n) * |T₀ - -T₀| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have ht_abs : |t| ≤ T₀ := by
      rw [Set.mem_Ioc] at ht
      exact abs_le.mpr ⟨le_of_lt ht.1, ht.2⟩
    have hy : ↑t * ↑y * I = ↑(t * y) * I := by push_cast; ring
    rw [norm_mul, norm_mul, hy, norm_exp_ofReal_mul_I, mul_one]
    have h1_b : ‖dirichletPoly a N (1 + ↑t * I)‖ ≤ ∑ n ∈ N, ‖a n‖ / n := norm_dirichletPoly_le a N hN t
    have h2_b : ‖windowKernel u₁ t / u₁ - windowKernel u₂ t / u₂‖ ≤ 8 * (1 + |t|) * (u₁ + u₂) := norm_windowKernel_div_sub_le u₁ u₂ t h1 h1' h2 h2'
    have h2_b_le : ‖windowKernel u₁ t / u₁ - windowKernel u₂ t / u₂‖ ≤ 8 * (1 + T₀) * (u₁ + u₂) := by
      calc
        ‖windowKernel u₁ t / u₁ - windowKernel u₂ t / u₂‖ ≤ 8 * (1 + |t|) * (u₁ + u₂) := h2_b
        _ ≤ 8 * (1 + T₀) * (u₁ + u₂) := by
          gcongr
    calc
      ‖dirichletPoly a N (1 + ↑t * I)‖ * ‖windowKernel u₁ t / u₁ - windowKernel u₂ t / u₂‖
        ≤ (∑ n ∈ N, ‖a n‖ / n) * (8 * (1 + T₀) * (u₁ + u₂)) := mul_le_mul h1_b h2_b_le (norm_nonneg _) hz
      _ = 8 * (1 + T₀) * (u₁ + u₂) * ∑ n ∈ N, ‖a n‖ / n := by ring
  have hT0_abs : |T₀ - -T₀| = 2 * T₀ := by
    have h_eq_t : T₀ - -T₀ = 2 * T₀ := by ring
    rw [h_eq_t, abs_of_pos (by linarith)]
  rw [hT0_abs] at h_int
  calc
    1 / (2 * Real.pi) * ‖∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * (windowKernel u₁ t / u₁ - windowKernel u₂ t / u₂) * exp (↑t * ↑y * I)‖
      ≤ 1 / (2 * Real.pi) * ((8 * (1 + T₀) * (u₁ + u₂) * ∑ n ∈ N, ‖a n‖ / n) * (2 * T₀)) := by gcongr
    _ = (8 * T₀ * (1 + T₀) / Real.pi) * (u₁ + u₂) * ∑ n ∈ N, ‖a n‖ / n := by ring

theorem norm_lowPart_div_sub_shift_le (a : ℕ → ℂ) (N : Finset ℕ) (u T₀ y y' : ℝ) (hu : 0 < u) (hu' : u ≤ 1 / 2) (hT₀ : 0 < T₀) (hN : ∀ n ∈ N, 0 < n) :
    ‖lowPart a N u T₀ y / u - lowPart a N u T₀ y' / u‖ ≤ (2 * T₀ ^ 2 / Real.pi) * |y - y'| * ∑ n ∈ N, ‖a n‖ / n := by
  have hz : 0 ≤ ∑ n ∈ N, ‖a n‖ / (n : ℝ) := Finset.sum_nonneg (fun i _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have h_eq : lowPart a N u T₀ y / u - lowPart a N u T₀ y' / u =
      (1 / (2 * ↑Real.pi) : ℂ) * ∫ (t : ℝ) in -T₀..T₀, (dirichletPoly a N (1 + ↑t * I) * (windowKernel u t / u)) * (exp (↑t * ↑y * I) - exp (↑t * ↑y' * I)) := by
    unfold lowPart
    have h_div1 : (∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y * I)) / (u : ℂ) =
      ∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y * I) / (u : ℂ) := (intervalIntegral.integral_div (u : ℂ) _).symm
    have h_div2 : (∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y' * I)) / (u : ℂ) =
      ∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y' * I) / (u : ℂ) := (intervalIntegral.integral_div (u : ℂ) _).symm
    calc
      ((1 / (2 * ↑Real.pi) : ℂ) * ∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y * I)) / u -
      ((1 / (2 * ↑Real.pi) : ℂ) * ∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y' * I)) / u
      _ = (1 / (2 * ↑Real.pi) : ℂ) * ((∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y * I)) / u -
                                   (∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y' * I)) / u) := by ring
      _ = (1 / (2 * ↑Real.pi) : ℂ) * ((∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y * I) / u) -
                                   (∫ (t : ℝ) in -T₀..T₀, dirichletPoly a N (1 + ↑t * I) * windowKernel u t * exp (↑t * ↑y' * I) / u)) := by
        congr 1
        rw [h_div1, h_div2]
      _ = (1 / (2 * ↑Real.pi) : ℂ) * ∫ (t : ℝ) in -T₀..T₀, (dirichletPoly a N (1 + ↑t * I) * (windowKernel u t / u)) * (exp (↑t * ↑y * I) - exp (↑t * ↑y' * I)) := by
        congr 1
        rw [int_sub_lemma]
        · congr 1
          ext t
          ring
        · apply Continuous.div
          · exact ((cont_dp a N hN).mul (cont_wk u hu)).mul (cont_exp y)
          · exact continuous_const
          · intro _x; exact_mod_cast ne_of_gt hu
        · apply Continuous.div
          · exact ((cont_dp a N hN).mul (cont_wk u hu)).mul (cont_exp y')
          · exact continuous_const
          · intro _x; exact_mod_cast ne_of_gt hu
  rw [h_eq, norm_mul, norm_div, norm_one, norm_mul, Complex.norm_real]
  have h1_n : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h2_n : ‖Real.pi‖ = Real.pi := abs_of_pos Real.pi_pos
  rw [h1_n, h2_n]
  have h_int : ‖∫ (t : ℝ) in -T₀..T₀, (dirichletPoly a N (1 + ↑t * I) * (windowKernel u t / u)) * (exp (↑t * ↑y * I) - exp (↑t * ↑y' * I))‖ ≤ (T₀ * |y - y'| * 2 * ∑ n ∈ N, ‖a n‖ / n) * |T₀ - -T₀| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have ht_abs : |t| ≤ T₀ := by
      rw [Set.mem_Ioc] at ht
      exact abs_le.mpr ⟨le_of_lt ht.1, ht.2⟩
    rw [norm_mul, norm_mul]
    have h1_b : ‖dirichletPoly a N (1 + ↑t * I)‖ ≤ ∑ n ∈ N, ‖a n‖ / n := norm_dirichletPoly_le a N hN t
    have h2_b : ‖windowKernel u t‖ ≤ 2 * u := norm_windowKernel_le_mul u t hu (by linarith)
    have h2_b_div : ‖windowKernel u t / u‖ ≤ 2 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
      exact (div_le_iff₀ hu).mpr h2_b
    have h3_b : ‖exp (↑t * ↑y * I) - exp (↑t * ↑y' * I)‖ ≤ |t| * |y - y'| := norm_exp_sub_exp_le t y y'
    have h3_b_le : ‖exp (↑t * ↑y * I) - exp (↑t * ↑y' * I)‖ ≤ T₀ * |y - y'| := by
      calc
        ‖exp (↑t * ↑y * I) - exp (↑t * ↑y' * I)‖ ≤ |t| * |y - y'| := h3_b
        _ ≤ T₀ * |y - y'| := by
          gcongr
    calc
      ‖dirichletPoly a N (1 + ↑t * I)‖ * ‖windowKernel u t / u‖ * ‖exp (↑t * ↑y * I) - exp (↑t * ↑y' * I)‖
        ≤ (∑ n ∈ N, ‖a n‖ / n) * 2 * (T₀ * |y - y'|) := by
          refine mul_le_mul ?_ h3_b_le (norm_nonneg _) ?_
          · exact mul_le_mul h1_b h2_b_div (norm_nonneg _) hz
          · exact mul_nonneg hz (by positivity)
      _ = T₀ * |y - y'| * 2 * ∑ n ∈ N, ‖a n‖ / n := by ring
  have hT0_abs : |T₀ - -T₀| = 2 * T₀ := by
    have h_eq_t : T₀ - -T₀ = 2 * T₀ := by ring
    rw [h_eq_t, abs_of_pos (by linarith)]
  rw [hT0_abs] at h_int
  calc
    1 / (2 * Real.pi) * ‖∫ (t : ℝ) in -T₀..T₀, (dirichletPoly a N (1 + ↑t * I) * (windowKernel u t / u)) * (exp (↑t * ↑y * I) - exp (↑t * ↑y' * I))‖
      ≤ 1 / (2 * Real.pi) * ((T₀ * |y - y'| * 2 * ∑ n ∈ N, ‖a n‖ / n) * (2 * T₀)) := by gcongr
    _ = (2 * T₀ ^ 2 / Real.pi) * |y - y'| * ∑ n ∈ N, ‖a n‖ / n := by ring

end Erdos1201.MR
