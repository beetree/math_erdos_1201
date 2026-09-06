import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Pi.Bounds
import Erdos1201.MR.Analysis.KusminLandau

/-!
# Van der Corput Second Derivative Bound

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the van der Corput second-derivative bound for dyadic exponential sums
of the form `∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I)`.
-/

open Real Complex Finset

namespace Erdos1201.MR

/-- The phase function `g(m) = - (t / (2π)) * log m`. -/
noncomputable def vdc_g (t : ℝ) (m : ℕ) : ℝ :=
  - (t / (2 * Real.pi)) * Real.log (m : ℝ)

/-- The first difference `d(m) = g(m+1) - g(m)`. -/
noncomputable def vdc_d (t : ℝ) (m : ℕ) : ℝ :=
  vdc_g t (m + 1) - vdc_g t m

lemma two_pi_mul_vdc_g (t : ℝ) (m : ℕ) :
    2 * Real.pi * vdc_g t m = - (t * Real.log (m : ℝ)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2pi : 2 * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hpi
  simp only [vdc_g]
  calc 2 * Real.pi * (- (t / (2 * Real.pi)) * Real.log (m : ℝ))
    _ = - (2 * Real.pi * (t / (2 * Real.pi))) * Real.log (m : ℝ) := by ring
    _ = - t * Real.log (m : ℝ) := by rw [mul_div_cancel₀ _ h2pi]
    _ = - (t * Real.log (m : ℝ)) := by ring

lemma exp_phase_eq (t : ℝ) (m : ℕ) :
    Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * ((vdc_g t m : ℝ) : ℂ)) := by
  congr 1
  have h := two_pi_mul_vdc_g t m
  have : (2 * Real.pi * Complex.I * ((vdc_g t m : ℝ) : ℂ)) =
      (((2 * Real.pi * vdc_g t m : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [this, h]
  push_cast
  ring

lemma norm_exp_phase (t : ℝ) (m : ℕ) :
    ‖Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  rw [exp_phase_eq]
  exact norm_exp_two_pi_I_mul (vdc_g t m)

lemma card_Ioc_M_two_M (M : ℕ) :
    (Finset.Ioc M (2 * M)).card = M := by
  rw [Nat.card_Ioc, Nat.two_mul, Nat.add_sub_cancel_left]

lemma norm_sum_exp_phase_le_card (M : ℕ) (t : ℝ) :
    ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ (M : ℝ) := by
  have h1 := norm_sum_le (Finset.Ioc M (2 * M)) (fun m => Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I))
  have h2 : ∑ m ∈ Finset.Ioc M (2 * M), ‖Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ = (M : ℝ) := by
    have : ∀ m ∈ Finset.Ioc M (2 * M), ‖Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ = 1 :=
      fun m _ => norm_exp_phase t m
    rw [sum_congr rfl this, sum_const, card_Ioc_M_two_M, nsmul_eq_mul, mul_one]
  linarith

lemma norm_sum_exp_phase_of_large_t (M : ℕ) (t : ℝ) (hM : 1 ≤ M) (ht : (M : ℝ) ^ 2 ≤ t) :
    ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      1 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  have ht_pos : 0 < t := by
    have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
    have : 0 < (M : ℝ) ^ 2 := by positivity
    linarith
  have hM_le_sqrt : (M : ℝ) ≤ Real.sqrt t := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg M)]
    exact Real.sqrt_le_sqrt ht
  have hcard := norm_sum_exp_phase_le_card M t
  have h_sqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hdiv_nonneg : 0 ≤ (M : ℝ) / Real.sqrt t := div_nonneg (Nat.cast_nonneg M) h_sqrt_pos.le
  calc ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖
    _ ≤ (M : ℝ) := hcard
    _ ≤ Real.sqrt t := hM_le_sqrt
    _ ≤ Real.sqrt t + (M : ℝ) / Real.sqrt t := le_add_of_nonneg_right hdiv_nonneg
    _ = 1 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by ring

lemma log_one_add_inv_ge (m : ℕ) (hm : 1 ≤ m) :
    1 / (2 * (m : ℝ)) ≤ Real.log (1 + 1 / (m : ℝ)) := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1_pos : 0 < (m : ℝ) + 1 := by linarith
  have hdiv_pos : 0 < (m : ℝ) / ((m : ℝ) + 1) := div_pos hm_pos hm1_pos
  have hle := Real.log_le_sub_one_of_pos hdiv_pos
  have hid : (m : ℝ) / ((m : ℝ) + 1) - 1 = - (1 / ((m : ℝ) + 1)) := by
    have : (m : ℝ) / ((m : ℝ) + 1) - 1 = ((m : ℝ) - ((m : ℝ) + 1)) / ((m : ℝ) + 1) := by
      rw [div_sub_one hm1_pos.ne']
    rw [this]
    ring
  rw [hid] at hle
  have hneg : 1 / ((m : ℝ) + 1) ≤ - Real.log ((m : ℝ) / ((m : ℝ) + 1)) := by linarith
  have hlog_inv : - Real.log ((m : ℝ) / ((m : ℝ) + 1)) = Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    rw [← Real.log_inv, inv_div]
  have hsplit : ((m : ℝ) + 1) / (m : ℝ) = 1 + 1 / (m : ℝ) := by
    rw [add_div, div_self hm_pos.ne']
  rw [hlog_inv, hsplit] at hneg
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2m : 1 / (2 * (m : ℝ)) ≤ 1 / ((m : ℝ) + 1) := by
    apply one_div_le_one_div_of_le hm1_pos
    linarith [hm_real]
  exact h2m.trans hneg

lemma log_one_add_inv_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (1 + 1 / (m : ℝ)) ≤ 1 / (m : ℝ) := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hpos : 0 < 1 + 1 / (m : ℝ) := by positivity
  have hle := Real.log_le_sub_one_of_pos hpos
  linarith

lemma vdc_d_eq (t : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    vdc_d t m = - (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ)) := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1_pos : 0 < (m + 1 : ℝ) := by positivity
  simp only [vdc_d, vdc_g]
  push_cast
  have hlog : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) = Real.log (1 + 1 / (m : ℝ)) := by
    rw [← Real.log_div (by linarith) hm_pos.ne']
    congr 1
    rw [add_div, div_self hm_pos.ne']
  calc - (t / (2 * Real.pi)) * Real.log ((m : ℝ) + 1) - - (t / (2 * Real.pi)) * Real.log (m : ℝ)
    _ = - (t / (2 * Real.pi)) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by ring
    _ = - (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ)) := by rw [hlog]

lemma vdc_d_neg (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : 1 ≤ m) :
    vdc_d t m < 0 := by
  rw [vdc_d_eq t m hm]
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2pi : 0 < 2 * Real.pi := by linarith
  have ht2pi : 0 < t / (2 * Real.pi) := div_pos ht h2pi
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hlog_pos : 0 < Real.log (1 + 1 / (m : ℝ)) := by
    rw [Real.log_pos_iff (by positivity)]
    have : 0 < 1 / (m : ℝ) := one_div_pos.mpr hm_pos
    linarith
  have : 0 < (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ)) := mul_pos ht2pi hlog_pos
  linarith

lemma vdc_d_mono (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : 1 ≤ m) :
    vdc_d t m ≤ vdc_d t (m + 1) := by
  have hm1 : 1 ≤ m + 1 := by omega
  rw [vdc_d_eq t m hm, vdc_d_eq t (m + 1) hm1]
  push_cast
  have hpi : 0 < Real.pi := Real.pi_pos
  have ht2pi : 0 < t / (2 * Real.pi) := by positivity
  have hlog_le : Real.log (1 + 1 / ((m : ℝ) + 1)) ≤ Real.log (1 + 1 / (m : ℝ)) := by
    apply Real.log_le_log (by positivity)
    have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have : 1 / ((m : ℝ) + 1) ≤ 1 / (m : ℝ) := one_div_le_one_div_of_le hm_pos (by linarith)
    linarith
  nlinarith

lemma abs_vdc_d_eq (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : 1 ≤ m) :
    |vdc_d t m| = (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ)) := by
  have hneg := vdc_d_neg t ht m hm
  rw [abs_of_neg hneg, vdc_d_eq t m hm]
  ring

lemma norm_sum_exp_phase_of_small_t (M : ℕ) (t : ℝ) (hM : 1 ≤ M) (ht1 : 1 ≤ t) (ht_small : t ≤ Real.pi * (M : ℝ)) :
    ‖∑ m ∈ Finset.Icc (M + 1) (2 * M), Complex.exp (2 * Real.pi * Complex.I * ((vdc_g t m : ℝ) : ℂ))‖ ≤
      (8 * Real.pi + 1) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  have ht_pos : 0 < t := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hab : M + 1 ≤ 2 * M := by omega
  set δ := t / (8 * Real.pi * (M : ℝ))
  have hδ_pos : 0 < δ := by positivity
  have hneg : ∀ n, M + 1 ≤ n → n < 2 * M → vdc_g t (n + 1) - vdc_g t n < 0 := by
    intro n hn _
    exact vdc_d_neg t ht_pos n (by omega)
  have hmono : ∀ n, M + 1 ≤ n → n + 1 < 2 * M →
      vdc_g t (n + 1) - vdc_g t n ≤ vdc_g t (n + 2) - vdc_g t (n + 1) := by
    intro n hn _
    exact vdc_d_mono t ht_pos n (by omega)
  have hlow : ∀ n, M + 1 ≤ n → n < 2 * M → δ ≤ |vdc_g t (n + 1) - vdc_g t n| := by
    intro n hn _
    have hn1 : 1 ≤ n := by omega
    change δ ≤ |vdc_d t n|
    rw [abs_vdc_d_eq t ht_pos n hn1]
    have hlog := log_one_add_inv_ge n hn1
    have hn_le : (n : ℝ) ≤ 2 * (M : ℝ) := by
      have : n ≤ 2 * M := by omega
      exact_mod_cast this
    have h1 : 1 / (4 * (M : ℝ)) ≤ 1 / (2 * (n : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    have hlog_ge : 1 / (4 * (M : ℝ)) ≤ Real.log (1 + 1 / (n : ℝ)) := h1.trans hlog
    have ht2pi_nonneg : 0 ≤ t / (2 * Real.pi) := by positivity
    calc δ = (t / (2 * Real.pi)) * (1 / (4 * (M : ℝ))) := by
           simp only [δ]; ring
      _ ≤ (t / (2 * Real.pi)) * Real.log (1 + 1 / (n : ℝ)) :=
           mul_le_mul_of_nonneg_left hlog_ge ht2pi_nonneg
  have hhalf : ∀ n, M + 1 ≤ n → n < 2 * M → |vdc_g t (n + 1) - vdc_g t n| ≤ 1 / 2 := by
    intro n hn _
    have hn1 : 1 ≤ n := by omega
    change |vdc_d t n| ≤ 1 / 2
    rw [abs_vdc_d_eq t ht_pos n hn1]
    have hlog := log_one_add_inv_le n hn1
    have hM_le_n : (M : ℝ) ≤ (n : ℝ) := by
      have : M ≤ n := by omega
      exact_mod_cast this
    have h1 : 1 / (n : ℝ) ≤ 1 / (M : ℝ) := one_div_le_one_div_of_le hM_pos hM_le_n
    have hlog_le : Real.log (1 + 1 / (n : ℝ)) ≤ 1 / (M : ℝ) := hlog.trans h1
    have ht2pi_nonneg : 0 ≤ t / (2 * Real.pi) := by positivity
    have hmul : (t / (2 * Real.pi)) * Real.log (1 + 1 / (n : ℝ)) ≤ (t / (2 * Real.pi)) * (1 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_le ht2pi_nonneg
    have h_cancel : (t / (2 * Real.pi)) * (1 / (M : ℝ)) = t / (2 * Real.pi * (M : ℝ)) := by ring
    rw [h_cancel] at hmul
    have ht_div : t / (2 * Real.pi * (M : ℝ)) ≤ 1 / 2 := by
      have h2piM_pos : 0 < 2 * Real.pi * (M : ℝ) := by positivity
      rw [div_le_iff₀ h2piM_pos]
      linarith
    linarith
  have hKL := norm_sum_exp_le_of_monotone_diff (vdc_g t) (M + 1) (2 * M) hab δ hδ_pos hneg hmono hlow hhalf
  have h_one_div_δ : 1 / δ = 8 * Real.pi * (M : ℝ) / t := by
    simp only [δ]
    field_simp
  have h_sqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have ht_ge_sqrt : Real.sqrt t ≤ t := by
    have : 1 ≤ Real.sqrt t := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt ht1
    calc Real.sqrt t ≤ Real.sqrt t * Real.sqrt t := by nlinarith
      _ = t := Real.mul_self_sqrt (by linarith)
  have h_div_le : 8 * Real.pi * (M : ℝ) / t ≤ 8 * Real.pi * ((M : ℝ) / Real.sqrt t) := by
    have h1 : 1 / t ≤ 1 / Real.sqrt t := one_div_le_one_div_of_le h_sqrt_pos ht_ge_sqrt
    have h2 : 0 ≤ 8 * Real.pi * (M : ℝ) := by positivity
    calc 8 * Real.pi * (M : ℝ) / t = (8 * Real.pi * (M : ℝ)) * (1 / t) := by ring
      _ ≤ (8 * Real.pi * (M : ℝ)) * (1 / Real.sqrt t) := mul_le_mul_of_nonneg_left h1 h2
      _ = 8 * Real.pi * ((M : ℝ) / Real.sqrt t) := by ring
  have h_one_le_sqrt : 1 ≤ Real.sqrt t := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ht1
  have hM_div_nonneg : 0 ≤ (M : ℝ) / Real.sqrt t := div_nonneg (by positivity) (by positivity)
  have hsqrt_nonneg : 0 ≤ Real.sqrt t := by positivity
  calc ‖∑ m ∈ Finset.Icc (M + 1) (2 * M), Complex.exp (2 * Real.pi * Complex.I * ((vdc_g t m : ℝ) : ℂ))‖
    _ ≤ 1 / δ + 1 := hKL
    _ = 8 * Real.pi * (M : ℝ) / t + 1 := by rw [h_one_div_δ]
    _ ≤ 8 * Real.pi * ((M : ℝ) / Real.sqrt t) + Real.sqrt t := by linarith [h_div_le, h_one_le_sqrt]
    _ ≤ (8 * Real.pi + 1) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
         nlinarith [hpi, hM_div_nonneg, hsqrt_nonneg]

lemma Ioc_eq_Icc_succ (M : ℕ) :
    Finset.Ioc M (2 * M) = Finset.Icc (M + 1) (2 * M) := by
  ext x
  simp only [mem_Ioc, mem_Icc]
  omega

lemma norm_sum_exp_phase_of_small_t' (M : ℕ) (t : ℝ) (hM : 1 ≤ M) (ht1 : 1 ≤ t) (ht_small : t ≤ Real.pi * (M : ℝ)) :
    ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (8 * Real.pi + 1) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  have heq : ∀ m ∈ Finset.Ioc M (2 * M),
      Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * ((vdc_g t m : ℝ) : ℂ)) :=
    fun m _ => exp_phase_eq t m
  rw [sum_congr rfl heq, Ioc_eq_Icc_succ]
  exact norm_sum_exp_phase_of_small_t M t hM ht1 ht_small


lemma vdc_d_diff_ge (t : ℝ) (ht : 0 < t) (M : ℕ) (hM : 1 ≤ M) (m : ℕ) (hm1 : M ≤ m) (hm2 : m < 2 * M) :
    t / (32 * Real.pi * (M : ℝ) ^ 2) ≤ vdc_d t (m + 1) - vdc_d t m := by
  have hm_pos : 1 ≤ m := le_trans hM hm1
  have hm1_pos : 1 ≤ m + 1 := by omega
  rw [vdc_d_eq t m hm_pos, vdc_d_eq t (m + 1) hm1_pos]
  push_cast
  have hlog_sub : Real.log (1 + 1 / (m : ℝ)) - Real.log (1 + 1 / ((m : ℝ) + 1)) =
      Real.log (1 + 1 / ((m : ℝ) * ((m : ℝ) + 2))) := by
    have h1 : 0 < 1 + 1 / (m : ℝ) := by positivity
    have h2 : 0 < 1 + 1 / ((m : ℝ) + 1) := by positivity
    rw [← Real.log_div h1.ne' h2.ne']
    congr 1
    have hm_gt0 : 0 < (m : ℝ) := by positivity
    have hm1_gt0 : 0 < (m : ℝ) + 1 := by positivity
    have hm2_gt0 : 0 < (m : ℝ) + 2 := by positivity
    field_simp
    ring
  have h_diff_eq : - (t / (2 * Real.pi)) * Real.log (1 + 1 / ((m : ℝ) + 1)) -
      - (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ)) =
      (t / (2 * Real.pi)) * Real.log (1 + 1 / ((m : ℝ) * ((m : ℝ) + 2))) := by
    calc - (t / (2 * Real.pi)) * Real.log (1 + 1 / ((m : ℝ) + 1)) -
      - (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ))
      _ = (t / (2 * Real.pi)) * (Real.log (1 + 1 / (m : ℝ)) - Real.log (1 + 1 / ((m : ℝ) + 1))) := by ring
      _ = (t / (2 * Real.pi)) * Real.log (1 + 1 / ((m : ℝ) * ((m : ℝ) + 2))) := by rw [hlog_sub]
  rw [h_diff_eq]
  have hprod_nat : 1 ≤ m * (m + 2) := by
    have : 1 ≤ m := hm_pos
    have : 1 ≤ m + 2 := by omega
    nlinarith
  have hlog_ge := log_one_add_inv_ge (m * (m + 2)) hprod_nat
  push_cast at hlog_ge
  have hm_le_2M : (m : ℝ) ≤ 2 * (M : ℝ) := by
    have : m ≤ 2 * M := by omega
    exact_mod_cast this
  have hm2_le_4M : (m : ℝ) + 2 ≤ 4 * (M : ℝ) := by
    have hM_real : 1 ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  have hprod_le : (m : ℝ) * ((m : ℝ) + 2) ≤ 8 * (M : ℝ) ^ 2 := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
    nlinarith
  have hdenom_le : 2 * ((m : ℝ) * ((m : ℝ) + 2)) ≤ 16 * (M : ℝ) ^ 2 := by linarith
  have hdenom_pos : 0 < 2 * ((m : ℝ) * ((m : ℝ) + 2)) := by positivity
  have h16_pos : 0 < 16 * (M : ℝ) ^ 2 := by positivity
  have hinv_le : 1 / (16 * (M : ℝ) ^ 2) ≤ 1 / (2 * ((m : ℝ) * ((m : ℝ) + 2))) :=
    one_div_le_one_div_of_le hdenom_pos hdenom_le
  have hlog_lower : 1 / (16 * (M : ℝ) ^ 2) ≤ Real.log (1 + 1 / ((m : ℝ) * ((m : ℝ) + 2))) :=
    hinv_le.trans hlog_ge
  have ht2pi_pos : 0 < t / (2 * Real.pi) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog_lower ht2pi_pos.le
  calc t / (32 * Real.pi * (M : ℝ) ^ 2)
    _ = (t / (2 * Real.pi)) * (1 / (16 * (M : ℝ) ^ 2)) := by ring
    _ ≤ (t / (2 * Real.pi)) * Real.log (1 + 1 / ((m : ℝ) * ((m : ℝ) + 2))) := hmul

lemma sum_Ico_d_diff (t : ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ m ∈ Finset.Ico a b, (vdc_d t (m + 1) - vdc_d t m) = vdc_d t b - vdc_d t a :=
  sum_Ico_sub (fun m => vdc_d t m) hab

lemma d_sub_ge_mul_diff (t : ℝ) (_ht : 0 < t) (M : ℕ) (_hM : 1 ≤ M)
    (a b : ℕ) (ha : M ≤ a) (hb : b ≤ 2 * M) (hab : a ≤ b)
    (hstep : ∀ m, M ≤ m → m < 2 * M → t / (32 * Real.pi * (M : ℝ) ^ 2) ≤ vdc_d t (m + 1) - vdc_d t m) :
    ((b - a : ℕ) : ℝ) * (t / (32 * Real.pi * (M : ℝ) ^ 2)) ≤ vdc_d t b - vdc_d t a := by
  have h_sum := (sum_Ico_d_diff t a b hab).symm
  rw [h_sum]
  have hcard : (Finset.Ico a b).card = b - a := Nat.card_Ico a b
  have h_const : ∑ m ∈ Finset.Ico a b, (t / (32 * Real.pi * (M : ℝ) ^ 2)) =
      ((b - a : ℕ) : ℝ) * (t / (32 * Real.pi * (M : ℝ) ^ 2)) := by
    rw [sum_const, hcard, nsmul_eq_mul]
  rw [← h_const]
  apply sum_le_sum
  intro m hm
  have hma := (mem_Ico.mp hm).1
  have hmb := (mem_Ico.mp hm).2
  exact hstep m (le_trans ha hma) (lt_of_lt_of_le hmb hb)

lemma card_Icc_le_of_d_sub_le (t : ℝ) (ht : 0 < t) (M : ℕ) (hM : 1 ≤ M)
    (a b : ℕ) (ha : M ≤ a) (hb : b ≤ 2 * M) (hab : a ≤ b)
    (hstep : ∀ m, M ≤ m → m < 2 * M → t / (32 * Real.pi * (M : ℝ) ^ 2) ≤ vdc_d t (m + 1) - vdc_d t m)
    (δ : ℝ) (_hδ : 0 < δ) (hsub : vdc_d t b - vdc_d t a ≤ 2 * δ) :
    ((Finset.Icc a b).card : ℝ) ≤ 64 * Real.pi * δ * (M : ℝ) ^ 2 / t + 1 := by
  have hge := d_sub_ge_mul_diff t ht M hM a b ha hb hab hstep
  have hstep_pos : 0 < t / (32 * Real.pi * (M : ℝ) ^ 2) := by positivity
  have hba : ((b - a : ℕ) : ℝ) * (t / (32 * Real.pi * (M : ℝ) ^ 2)) ≤ 2 * δ := hge.trans hsub
  have hba_le : ((b - a : ℕ) : ℝ) ≤ 2 * δ / (t / (32 * Real.pi * (M : ℝ) ^ 2)) := by
    rwa [le_div_iff₀ hstep_pos]
  have h_simp : 2 * δ / (t / (32 * Real.pi * (M : ℝ) ^ 2)) = 64 * Real.pi * δ * (M : ℝ) ^ 2 / t := by
    field_simp; ring
  rw [h_simp] at hba_le
  have hcard_eq : (Finset.Icc a b).card = (b - a) + 1 := by
    rw [Nat.card_Icc]
    have : b + 1 - a = b - a + 1 := by omega
    exact this
  rw [hcard_eq]
  push_cast
  linarith

lemma filter_Ioc_eq_Icc_of_mono (f : ℕ → ℝ) (hmono : ∀ x y, x ≤ y → f x ≤ f y)
    (M N : ℕ) (α β : ℝ) :
    let s := (Finset.Ioc M N).filter (fun m => α ≤ f m ∧ f m ≤ β)
    s.Nonempty → ∃ a b : ℕ, M < a ∧ a ≤ b ∧ b ≤ N ∧ s = Finset.Icc a b := by
  intro s hs
  let a := s.min' hs
  let b := s.max' hs
  have ha_mem : a ∈ s := Finset.min'_mem s hs
  have hb_mem : b ∈ s := Finset.max'_mem s hs
  have ha_Ioc : a ∈ Finset.Ioc M N := (Finset.mem_filter.mp ha_mem).1
  have hb_Ioc : b ∈ Finset.Ioc M N := (Finset.mem_filter.mp hb_mem).1
  have ha_prop : α ≤ f a ∧ f a ≤ β := (Finset.mem_filter.mp ha_mem).2
  have hb_prop : α ≤ f b ∧ f b ≤ β := (Finset.mem_filter.mp hb_mem).2
  have hab : a ≤ b := Finset.min'_le s b hb_mem
  refine ⟨a, b, (Finset.mem_Ioc.mp ha_Ioc).1, hab, (Finset.mem_Ioc.mp hb_Ioc).2, ?_⟩
  ext x
  constructor
  · intro hx
    have hx_ge : a ≤ x := Finset.min'_le s x hx
    have hx_le : x ≤ b := Finset.le_max' s x hx
    exact Finset.mem_Icc.mpr ⟨hx_ge, hx_le⟩
  · intro hx
    have hx_ge : a ≤ x := (Finset.mem_Icc.mp hx).1
    have hx_le : x ≤ b := (Finset.mem_Icc.mp hx).2
    have hx_Ioc : x ∈ Finset.Ioc M N := by
      rw [Finset.mem_Ioc]
      exact ⟨lt_of_lt_of_le (Finset.mem_Ioc.mp ha_Ioc).1 hx_ge,
             le_trans hx_le (Finset.mem_Ioc.mp hb_Ioc).2⟩
    have hfx_ge : α ≤ f x := le_trans ha_prop.1 (hmono a x hx_ge)
    have hfx_le : f x ≤ β := le_trans (hmono x b hx_le) hb_prop.2
    exact Finset.mem_filter.mpr ⟨hx_Ioc, ⟨hfx_ge, hfx_le⟩⟩


lemma exp_phase_shift (x : ℝ) (k : ℤ) (m : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((x + (k : ℝ) * (m : ℝ) : ℝ) : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  have h_add : (2 * Real.pi * Complex.I * ((x + (k : ℝ) * (m : ℝ) : ℝ) : ℂ)) =
      (2 * Real.pi * Complex.I * (x : ℂ)) + ((k * (m : ℤ) : ℤ) * (2 * Real.pi * Complex.I)) := by
    push_cast; ring
  rw [h_add, Complex.exp_add]
  have h_int := Complex.exp_int_mul_two_pi_mul_I (k * (m : ℤ))
  rw [h_int, mul_one]

lemma sum_Icc_rev (f : ℕ → ℂ) (a b : ℕ) (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc a b, f (a + b - j) = ∑ j ∈ Finset.Icc a b, f j := by
  have hext : Finset.Icc a b = Finset.Ico a (b + 1) := by
    ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [hext]
  have h := Finset.sum_Ico_reflect f a (m := b + 1) (n := a + b) (by omega)
  have h1 : a + b + 1 - (b + 1) = a := by omega
  have h2 : a + b + 1 - a = b + 1 := by omega
  rw [h1, h2] at h
  rw [← h]

theorem norm_sum_exp_le_of_monotone_diff_pos (h : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) (δ : ℝ) (hδ : 0 < δ)
    (hpos : ∀ n, a ≤ n → n < b → 0 < h (n + 1) - h n)
    (hmono : ∀ n, a ≤ n → n + 1 < b → h (n + 1) - h n ≤ h (n + 2) - h (n + 1))
    (hlow : ∀ n, a ≤ n → n < b → δ ≤ h (n + 1) - h n)
    (hhalf : ∀ n, a ≤ n → n < b → h (n + 1) - h n ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (h n : ℂ))‖ ≤ 1 / δ + 1 := by
  let H : ℕ → ℝ := fun j => h (a + b - j)
  have h_sum_rev : ∑ n ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (h n : ℂ)) =
      ∑ j ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * (H j : ℂ)) := by
    rw [← sum_Icc_rev (fun n => Complex.exp (2 * Real.pi * Complex.I * (h n : ℂ))) a b hab]
  rw [h_sum_rev]
  apply norm_sum_exp_le_of_monotone_diff H a b hab δ hδ
  · intro j hja hjb
    change h (a + b - (j + 1)) - h (a + b - j) < 0
    have h1 : a + b - (j + 1) = a + b - j - 1 := by omega
    have hidx : a ≤ a + b - j - 1 := by omega
    have hidx2 : a + b - j - 1 < b := by omega
    have hpos_val := hpos (a + b - j - 1) hidx hidx2
    have e1 : a + b - j - 1 + 1 = a + b - j := by omega
    rw [e1] at hpos_val
    rw [h1]
    linarith
  · intro j hja hjb
    have h1 : a + b - (j + 1) = a + b - j - 1 := by omega
    have h2 : a + b - (j + 2) = a + b - j - 2 := by omega
    have hidx : a ≤ a + b - j - 2 := by omega
    have hidx2 : a + b - j - 2 + 1 < b := by omega
    have hmono_val := hmono (a + b - j - 2) hidx hidx2
    have e1 : a + b - j - 2 + 1 = a + b - j - 1 := by omega
    have e2 : a + b - j - 2 + 2 = a + b - j := by omega
    rw [e1, e2] at hmono_val
    change h (a + b - (j + 1)) - h (a + b - j) ≤ h (a + b - (j + 2)) - h (a + b - (j + 1))
    rw [h1, h2]
    linarith
  · intro j hja hjb
    have h1 : a + b - (j + 1) = a + b - j - 1 := by omega
    have hidx : a ≤ a + b - j - 1 := by omega
    have hidx2 : a + b - j - 1 < b := by omega
    have hlow_val := hlow (a + b - j - 1) hidx hidx2
    have hpos_val := hpos (a + b - j - 1) hidx hidx2
    have e1 : a + b - j - 1 + 1 = a + b - j := by omega
    rw [e1] at hlow_val hpos_val
    change δ ≤ |h (a + b - (j + 1)) - h (a + b - j)|
    rw [h1]
    have : h (a + b - j - 1) - h (a + b - j) = - (h (a + b - j) - h (a + b - j - 1)) := by ring
    rw [this, abs_neg, abs_of_pos hpos_val]
    linarith
  · intro j hja hjb
    have h1 : a + b - (j + 1) = a + b - j - 1 := by omega
    have hidx : a ≤ a + b - j - 1 := by omega
    have hidx2 : a + b - j - 1 < b := by omega
    have hhalf_val := hhalf (a + b - j - 1) hidx hidx2
    have hpos_val := hpos (a + b - j - 1) hidx hidx2
    have e1 : a + b - j - 1 + 1 = a + b - j := by omega
    rw [e1] at hhalf_val hpos_val
    change |h (a + b - (j + 1)) - h (a + b - j)| ≤ 1 / 2
    rw [h1]
    have : h (a + b - j - 1) - h (a + b - j) = - (h (a + b - j) - h (a + b - j - 1)) := by ring
    rw [this, abs_neg, abs_of_pos hpos_val]
    linarith

noncomputable def vdc_k (d : ℝ) : ℤ := ⌊-d + 1 / 2⌋

noncomputable def vdc_tag (d : ℝ) (δ : ℝ) : Fin 3 :=
  let r := d + (vdc_k d : ℝ)
  if |r| ≤ δ then 0
  else if r < -δ then 1
  else 2

noncomputable def vdc_class (d : ℝ) (δ : ℝ) : ℤ × Fin 3 :=
  (vdc_k d, vdc_tag d δ)

lemma vdc_tag_zero_of_le (d δ : ℝ) (h : |d + (vdc_k d : ℝ)| ≤ δ) :
    vdc_tag d δ = 0 := by
  dsimp [vdc_tag]
  simp [h]

lemma vdc_tag_one_of_lt (d δ : ℝ) (h1 : ¬ |d + (vdc_k d : ℝ)| ≤ δ) (h2 : d + (vdc_k d : ℝ) < -δ) :
    vdc_tag d δ = 1 := by
  dsimp [vdc_tag]
  simp [h1, h2]

lemma vdc_tag_two_of_ge (d δ : ℝ) (h1 : ¬ |d + (vdc_k d : ℝ)| ≤ δ) (h2 : ¬ d + (vdc_k d : ℝ) < -δ) :
    vdc_tag d δ = 2 := by
  dsimp [vdc_tag]
  simp [h1, h2]

lemma vdc_class_zero_iff (d δ : ℝ) (hδ_half : δ < 1 / 2) (k : ℤ) :
    vdc_class d δ = (k, 0) ↔ - (k : ℝ) - δ ≤ d ∧ d ≤ - (k : ℝ) + δ := by
  constructor
  · intro h
    simp only [vdc_class, Prod.mk.injEq] at h
    have hk : vdc_k d = k := h.1
    have htag : vdc_tag d δ = 0 := h.2
    simp only [vdc_tag, hk] at htag
    split_ifs at htag with h1 h2
    · rw [abs_le] at h1
      constructor <;> linarith
    · contradiction
    · contradiction
  · intro h
    have h_r : |d + (k : ℝ)| ≤ δ := by
      rw [abs_le]
      constructor <;> linarith
    have hk : vdc_k d = k := by
      simp only [vdc_k]
      exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    have h_tag : vdc_tag d δ = 0 := by
      have : |d + (vdc_k d : ℝ)| ≤ δ := by rwa [hk]
      exact vdc_tag_zero_of_le d δ this
    exact Prod.ext hk h_tag

lemma vdc_class_one_iff (d δ : ℝ) (hδ : 0 < δ) (k : ℤ) :
    vdc_class d δ = (k, 1) ↔ - (k : ℝ) - 1 / 2 < d ∧ d < - (k : ℝ) - δ := by
  constructor
  · intro h
    simp only [vdc_class, Prod.mk.injEq] at h
    have hk : ⌊-d + 1 / 2⌋ = k := h.1
    have hk_cast : ((⌊-d + 1 / 2⌋ : ℤ) : ℝ) = (k : ℝ) := by exact_mod_cast hk
    have htag : vdc_tag d δ = 1 := h.2
    simp only [vdc_tag, h.1] at htag
    split_ifs at htag with h1 h2
    · contradiction
    · have h_ceil := Int.lt_floor_add_one (-d + 1 / 2)
      constructor
      · linarith [h_ceil, hk_cast]
      · linarith
    · contradiction
  · intro h
    have hk : vdc_k d = k := by
      simp only [vdc_k]
      exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    have h_not_le : ¬ |d + (vdc_k d : ℝ)| ≤ δ := by
      rw [hk, abs_le]
      intro ⟨_, h2⟩
      linarith
    have h_lt : d + (vdc_k d : ℝ) < -δ := by
      rw [hk]
      linarith
    have htag : vdc_tag d δ = 1 := vdc_tag_one_of_lt d δ h_not_le h_lt
    exact Prod.ext hk htag

lemma vdc_class_two_iff (d δ : ℝ) (hδ : 0 < δ) (k : ℤ) :
    vdc_class d δ = (k, 2) ↔ - (k : ℝ) + δ < d ∧ d ≤ - (k : ℝ) + 1 / 2 := by
  constructor
  · intro h
    simp only [vdc_class, Prod.mk.injEq] at h
    have hk : ⌊-d + 1 / 2⌋ = k := h.1
    have hk_cast : ((⌊-d + 1 / 2⌋ : ℤ) : ℝ) = (k : ℝ) := by exact_mod_cast hk
    have htag : vdc_tag d δ = 2 := h.2
    simp only [vdc_tag, h.1] at htag
    split_ifs at htag with h1 h2
    · contradiction
    · contradiction
    · have h_floor := Int.floor_le (-d + 1 / 2)
      rw [abs_le, not_and_or] at h1
      constructor
      · cases h1 with
        | inl h1 => linarith
        | inr h1 => linarith
      · linarith [h_floor, hk_cast]
  · intro h
    have hk : vdc_k d = k := by
      simp only [vdc_k]
      exact Int.floor_eq_iff.mpr ⟨by linarith, by linarith⟩
    have h_not_le : ¬ |d + (vdc_k d : ℝ)| ≤ δ := by
      rw [hk, abs_le]
      intro ⟨h1, _⟩
      linarith
    have h_not_lt : ¬ d + (vdc_k d : ℝ) < -δ := by
      rw [hk]
      linarith
    have htag : vdc_tag d δ = 2 := vdc_tag_two_of_ge d δ h_not_le h_not_lt
    exact Prod.ext hk htag

lemma vdc_class_convex (k : ℤ) (tag : Fin 3) (δ : ℝ) (hδ : 0 < δ) (hδ_half : δ < 1 / 2) :
    ∀ x y z : ℝ, x ≤ y → y ≤ z → vdc_class x δ = (k, tag) → vdc_class z δ = (k, tag) →
      vdc_class y δ = (k, tag) := by
  intro x y z hxy hyz hx hz
  fin_cases tag
  · have hx' : vdc_class x δ = (k, 0) := hx
    have hz' : vdc_class z δ = (k, 0) := hz
    rw [vdc_class_zero_iff x δ hδ_half k] at hx'
    rw [vdc_class_zero_iff z δ hδ_half k] at hz'
    have hy' : vdc_class y δ = (k, 0) := by
      rw [vdc_class_zero_iff y δ hδ_half k]
      constructor <;> linarith
    exact hy'
  · have hx' : vdc_class x δ = (k, 1) := hx
    have hz' : vdc_class z δ = (k, 1) := hz
    rw [vdc_class_one_iff x δ hδ k] at hx'
    rw [vdc_class_one_iff z δ hδ k] at hz'
    have hy' : vdc_class y δ = (k, 1) := by
      rw [vdc_class_one_iff y δ hδ k]
      constructor <;> linarith
    exact hy'
  · have hx' : vdc_class x δ = (k, 2) := hx
    have hz' : vdc_class z δ = (k, 2) := hz
    rw [vdc_class_two_iff x δ hδ k] at hx'
    rw [vdc_class_two_iff z δ hδ k] at hz'
    have hy' : vdc_class y δ = (k, 2) := by
      rw [vdc_class_two_iff y δ hδ k]
      constructor <;> linarith
    exact hy'

lemma filter_Ioc_eq_Icc_of_convex_mono (f : ℕ → ℝ) (hmono : ∀ x y, x ≤ y → f x ≤ f y)
    (M N : ℕ) (P : ℝ → Prop) [DecidablePred (fun m => P (f m))]
    (hP : ∀ x y z, x ≤ y → y ≤ z → P x → P z → P y) :
    let s := (Finset.Ioc M N).filter (fun m => P (f m))
    s.Nonempty → ∃ a b : ℕ, M < a ∧ a ≤ b ∧ b ≤ N ∧ s = Finset.Icc a b := by
  intro s hs
  let a := s.min' hs
  let b := s.max' hs
  have ha_mem : a ∈ s := Finset.min'_mem s hs
  have hb_mem : b ∈ s := Finset.max'_mem s hs
  have ha_Ioc : a ∈ Finset.Ioc M N := (Finset.mem_filter.mp ha_mem).1
  have hb_Ioc : b ∈ Finset.Ioc M N := (Finset.mem_filter.mp hb_mem).1
  have ha_prop : P (f a) := (Finset.mem_filter.mp ha_mem).2
  have hb_prop : P (f b) := (Finset.mem_filter.mp hb_mem).2
  have hab : a ≤ b := Finset.min'_le s b hb_mem
  refine ⟨a, b, (Finset.mem_Ioc.mp ha_Ioc).1, hab, (Finset.mem_Ioc.mp hb_Ioc).2, ?_⟩
  ext x
  constructor
  · intro hx
    have hx_ge : a ≤ x := Finset.min'_le s x hx
    have hx_le : x ≤ b := Finset.le_max' s x hx
    exact Finset.mem_Icc.mpr ⟨hx_ge, hx_le⟩
  · intro hx
    have hx_ge : a ≤ x := (Finset.mem_Icc.mp hx).1
    have hx_le : x ≤ b := (Finset.mem_Icc.mp hx).2
    have hx_Ioc : x ∈ Finset.Ioc M N := by
      rw [Finset.mem_Ioc]
      exact ⟨lt_of_lt_of_le (Finset.mem_Ioc.mp ha_Ioc).1 hx_ge,
             le_trans hx_le (Finset.mem_Ioc.mp hb_Ioc).2⟩
    have hfx : P (f x) := hP (f a) (f x) (f b) (hmono a x hx_ge) (hmono x b hx_le) ha_prop hb_prop
    exact Finset.mem_filter.mpr ⟨hx_Ioc, hfx⟩


lemma vdc_d_ge_neg (t : ℝ) (ht : 0 < t) (M : ℕ) (hM : 1 ≤ M) (m : ℕ) (hm : M < m) :
    - (t / (2 * Real.pi * (M : ℝ))) ≤ vdc_d t m := by
  have hm1 : 1 ≤ m := by omega
  rw [vdc_d_eq t m hm1]
  have hlog := log_one_add_inv_le m hm1
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hm_pos : 0 < (m : ℝ) := by positivity
  have hinv : 1 / (m : ℝ) ≤ 1 / (M : ℝ) := one_div_le_one_div_of_le hM_pos (by exact_mod_cast hm.le)
  have ht2pi : 0 ≤ t / (2 * Real.pi) := by positivity
  have hmul : (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ)) ≤ (t / (2 * Real.pi)) * (1 / (M : ℝ)) :=
    mul_le_mul_of_nonneg_left (hlog.trans hinv) ht2pi
  have : (t / (2 * Real.pi)) * (1 / (M : ℝ)) = t / (2 * Real.pi * (M : ℝ)) := by ring
  linarith

lemma vdc_k_mem_Icc (t : ℝ) (ht : 0 < t) (M : ℕ) (hM : 1 ≤ M) (m : ℕ) (hm : m ∈ Finset.Ioc M (2 * M)) :
    vdc_k (vdc_d t m) ∈ Finset.Icc 0 ⌊t / (2 * Real.pi * (M : ℝ)) + 1⌋ := by
  rw [Finset.mem_Ioc] at hm
  simp only [vdc_k, Finset.mem_Icc]
  have hneg := vdc_d_neg t ht m (by omega)
  have hge := vdc_d_ge_neg t ht M hM m hm.1
  constructor
  · have : (0 : ℝ) ≤ - vdc_d t m + 1 / 2 := by linarith
    exact Int.floor_nonneg.mpr this
  · apply Int.floor_le_floor
    linarith


lemma vdc_d_mono_on (t : ℝ) (ht : 0 < t) (M : ℕ) (_hM : 1 ≤ M) {x y : ℕ} (hx : M ≤ x) (hxy : x ≤ y) :
    vdc_d t x ≤ vdc_d t y := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hxy
  clear hxy
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : 1 ≤ x + k := by omega
    have hstep := vdc_d_mono t ht (x + k) h1
    have : x + (k + 1) = (x + k) + 1 := by omega
    rw [this]
    exact le_trans ih hstep

lemma filter_Ioc_eq_Icc_of_convex_mono_on (f : ℕ → ℝ)
    (M N : ℕ) (hmono : ∀ x y, M ≤ x → x ≤ y → y ≤ N → f x ≤ f y)
    (P : ℝ → Prop) [DecidablePred (fun m => P (f m))]
    (hP : ∀ x y z, x ≤ y → y ≤ z → P x → P z → P y) :
    let s := (Finset.Ioc M N).filter (fun m => P (f m))
    s.Nonempty → ∃ a b : ℕ, M < a ∧ a ≤ b ∧ b ≤ N ∧ s = Finset.Icc a b := by
  intro s hs
  let a := s.min' hs
  let b := s.max' hs
  have ha_mem : a ∈ s := Finset.min'_mem s hs
  have hb_mem : b ∈ s := Finset.max'_mem s hs
  have ha_Ioc : a ∈ Finset.Ioc M N := (Finset.mem_filter.mp ha_mem).1
  have hb_Ioc : b ∈ Finset.Ioc M N := (Finset.mem_filter.mp hb_mem).1
  have ha_prop : P (f a) := (Finset.mem_filter.mp ha_mem).2
  have hb_prop : P (f b) := (Finset.mem_filter.mp hb_mem).2
  have hab : a ≤ b := Finset.min'_le s b hb_mem
  have ha_ge : M ≤ a := (Finset.mem_Ioc.mp ha_Ioc).1.le
  have hb_le : b ≤ N := (Finset.mem_Ioc.mp hb_Ioc).2
  refine ⟨a, b, (Finset.mem_Ioc.mp ha_Ioc).1, hab, hb_le, ?_⟩
  ext x
  constructor
  · intro hx
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le s x hx, Finset.le_max' s x hx⟩
  · intro hx
    have hx_ge : a ≤ x := (Finset.mem_Icc.mp hx).1
    have hx_le : x ≤ b := (Finset.mem_Icc.mp hx).2
    have hx_Ioc : x ∈ Finset.Ioc M N := by
      rw [Finset.mem_Ioc]
      exact ⟨lt_of_lt_of_le (Finset.mem_Ioc.mp ha_Ioc).1 hx_ge, le_trans hx_le hb_le⟩
    have h1 := hmono a x ha_ge hx_ge (le_trans hx_le hb_le)
    have h2 := hmono x b (le_trans ha_ge hx_ge) hx_le hb_le
    have hfx : P (f x) := hP (f a) (f x) (f b) h1 h2 ha_prop hb_prop
    exact Finset.mem_filter.mpr ⟨hx_Ioc, hfx⟩


lemma delta_eval_simp (t M : ℝ) (ht : 0 < t) (hM : 0 < M) :
    64 * Real.pi * (Real.sqrt t / (8 * Real.pi * M)) * M ^ 2 / t = 8 * M / Real.sqrt t := by
  have ht_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have ht_eq : t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt ht.le).symm
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hM_ne : M ≠ 0 := hM.ne'
  have hS_ne : Real.sqrt t ≠ 0 := ht_pos.ne'
  nth_rw 2 [ht_eq]
  field_simp
  ring

lemma norm_sum_exp_fiber_le (M : ℕ) (t : ℝ) (hM : 1 ≤ M) (ht1 : 1 ≤ t)
    (_ht_med1 : Real.pi * (M : ℝ) < t) (ht_med2 : t < (M : ℝ) ^ 2)
    (δ : ℝ) (hδ : δ = Real.sqrt t / (8 * Real.pi * (M : ℝ)))
    (k : ℤ) (tag : Fin 3) :
    let s := (Finset.Ioc M (2 * M)).filter (fun m => vdc_class (vdc_d t m) δ = (k, tag))
    ‖∑ m ∈ s, Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1 := by
  intro s
  have ht_pos : 0 < t := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have h_sqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hδ_pos : 0 < δ := by rw [hδ]; positivity
  have h_sqrt_lt_M : Real.sqrt t < (M : ℝ) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg M)]
    exact Real.sqrt_lt_sqrt (by positivity) ht_med2
  have hδ_half : δ < 1 / 2 := by
    rw [hδ]
    have h1 : Real.sqrt t / (8 * Real.pi * (M : ℝ)) < (M : ℝ) / (8 * Real.pi * (M : ℝ)) :=
      div_lt_div_of_pos_right h_sqrt_lt_M (by positivity)
    have h2 : (M : ℝ) / (8 * Real.pi * (M : ℝ)) = 1 / (8 * Real.pi) := by
      field_simp
    have h3 : (1 : ℝ) / (8 * Real.pi) < 1 / 2 := by
      have : (2 : ℝ) < 8 * Real.pi := by nlinarith [pi_gt_three]
      exact one_div_lt_one_div_of_lt (by norm_num) this
    linarith
  have h_one_div_δ : 1 / δ = 8 * Real.pi * (M : ℝ) / Real.sqrt t := by
    rw [hδ]; field_simp
  have h_exp_eq : ∀ m ∈ s,
      Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * (((vdc_g t m + (k : ℝ) * (m : ℝ)) : ℝ) : ℂ)) := by
    intro m hm
    have hm_Ioc := (Finset.mem_filter.mp hm).1
    rw [exp_phase_eq t m, exp_phase_shift (vdc_g t m) k m]
  rw [sum_congr rfl h_exp_eq]
  have h_dist : (8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t =
      8 * Real.pi * (M : ℝ) / Real.sqrt t + 8 * (M : ℝ) / Real.sqrt t := by ring
  by_cases hs : s.Nonempty
  · have hconv := vdc_class_convex k tag δ hδ_pos hδ_half
    have hmono : ∀ x y, M ≤ x → x ≤ y → y ≤ 2 * M → vdc_d t x ≤ vdc_d t y :=
      fun x y hx hxy _ => vdc_d_mono_on t ht_pos M hM hx hxy
    have ⟨a, b, ha, hab, hb, heq⟩ := filter_Ioc_eq_Icc_of_convex_mono_on (vdc_d t) M (2 * M) hmono
      (fun d => vdc_class d δ = (k, tag)) hconv hs
    have hs_eq : s = Finset.Icc a b := heq
    rw [hs_eq]
    set h := fun m => vdc_g t m + (k : ℝ) * (m : ℝ)
    have h_diff_eq : ∀ n, h (n + 1) - h n = vdc_d t n + (k : ℝ) := by
      intro n
      simp only [h, vdc_d]
      push_cast
      ring
    have h_diff_mono : ∀ n, a ≤ n → n + 1 < b →
        h (n + 1) - h n ≤ h (n + 2) - h (n + 1) := by
      intro n hn hnb
      rw [h_diff_eq n, h_diff_eq (n + 1)]
      have : 1 ≤ n := by omega
      have hstep := vdc_d_mono t ht_pos n this
      linarith
    fin_cases tag
    · have h_norm_le : ‖∑ m ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * ((h m : ℝ) : ℂ))‖ ≤
          ((Finset.Icc a b).card : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have : ∀ m ∈ Finset.Icc a b, ‖Complex.exp (2 * Real.pi * Complex.I * ((h m : ℝ) : ℂ))‖ = 1 :=
          fun m _ => norm_exp_two_pi_I_mul (h m)
        rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]
      have ha_in : a ∈ s := by rw [hs_eq]; exact mem_Icc.mpr ⟨le_rfl, hab⟩
      have hb_in : b ∈ s := by rw [hs_eq]; exact mem_Icc.mpr ⟨hab, le_rfl⟩
      have ha_class := (Finset.mem_filter.mp ha_in).2
      have hb_class := (Finset.mem_filter.mp hb_in).2
      have ha_0 := (vdc_class_zero_iff (vdc_d t a) δ hδ_half k).mp ha_class
      have hb_0 := (vdc_class_zero_iff (vdc_d t b) δ hδ_half k).mp hb_class
      have hsub : vdc_d t b - vdc_d t a ≤ 2 * δ := by linarith [ha_0.1, hb_0.2]
      have hstep : ∀ m, M ≤ m → m < 2 * M → t / (32 * Real.pi * (M : ℝ) ^ 2) ≤ vdc_d t (m + 1) - vdc_d t m :=
        fun m hm1 hm2 => vdc_d_diff_ge t ht_pos M hM m hm1 hm2
      have hcard := card_Icc_le_of_d_sub_le t ht_pos M hM a b ha.le hb hab hstep δ hδ_pos hsub
      have h_δ_eval : 64 * Real.pi * δ * (M : ℝ) ^ 2 / t = 8 * (M : ℝ) / Real.sqrt t := by
        rw [hδ]
        exact delta_eval_simp t (M : ℝ) ht_pos hM_pos
      rw [h_δ_eval] at hcard
      have h8pi_pos : 0 ≤ 8 * Real.pi * (M : ℝ) / Real.sqrt t := by positivity
      have h8_pos : 0 ≤ 8 * (M : ℝ) / Real.sqrt t := by positivity
      rw [h_dist]
      linarith [h_norm_le, hcard]
    · have hKL := norm_sum_exp_le_of_monotone_diff h a b hab δ hδ_pos
      have hneg : ∀ n, a ≤ n → n < b → h (n + 1) - h n < 0 := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_1 := (vdc_class_one_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        linarith [hn_1.2]
      have hlow : ∀ n, a ≤ n → n < b → δ ≤ |h (n + 1) - h n| := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_1 := (vdc_class_one_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        have : vdc_d t n + (k : ℝ) < 0 := by linarith [hn_1.2]
        rw [abs_of_neg this]
        linarith [hn_1.2]
      have hhalf : ∀ n, a ≤ n → n < b → |h (n + 1) - h n| ≤ 1 / 2 := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_1 := (vdc_class_one_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        have : vdc_d t n + (k : ℝ) < 0 := by linarith [hn_1.2]
        rw [abs_of_neg this]
        linarith [hn_1.1]
      have hKL_bound := hKL hneg h_diff_mono hlow hhalf
      rw [h_one_div_δ] at hKL_bound
      have h8pi_pos : 0 ≤ 8 * Real.pi * (M : ℝ) / Real.sqrt t := by positivity
      have h8_pos : 0 ≤ 8 * (M : ℝ) / Real.sqrt t := by positivity
      rw [h_dist]
      linarith
    · have hKL_pos := norm_sum_exp_le_of_monotone_diff_pos h a b hab δ hδ_pos
      have hpos : ∀ n, a ≤ n → n < b → 0 < h (n + 1) - h n := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_2 := (vdc_class_two_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        linarith [hn_2.1]
      have hlow : ∀ n, a ≤ n → n < b → δ ≤ h (n + 1) - h n := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_2 := (vdc_class_two_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        linarith [hn_2.1]
      have hhalf : ∀ n, a ≤ n → n < b → h (n + 1) - h n ≤ 1 / 2 := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_2 := (vdc_class_two_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        linarith [hn_2.2]
      have hKL_bound := hKL_pos hpos h_diff_mono hlow hhalf
      rw [h_one_div_δ] at hKL_bound
      have h8pi_pos : 0 ≤ 8 * Real.pi * (M : ℝ) / Real.sqrt t := by positivity
      have h8_pos : 0 ≤ 8 * (M : ℝ) / Real.sqrt t := by positivity
      rw [h_dist]
      linarith
  · have : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    rw [this, sum_empty, norm_zero]
    have : 0 ≤ (8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1 := by positivity
    linarith

lemma card_T_le (M : ℕ) (t : ℝ) (hM : 1 ≤ M) (ht1 : 1 ≤ t) :
    let K := Nat.floor (t / (2 * Real.pi * (M : ℝ)) + 1)
    let T : Finset (ℕ × Fin 3) := (Finset.range (K + 1)) ×ˢ (Finset.univ : Finset (Fin 3))
    (T.card : ℝ) ≤ 3 * (t / (2 * Real.pi * (M : ℝ)) + 2) := by
  intro K T
  have h_card_univ : (Finset.univ : Finset (Fin 3)).card = 3 := by decide
  have h_card_T : T.card = (K + 1) * 3 := by
    simp only [T, card_product, card_range, h_card_univ]
  rw [h_card_T]
  push_cast
  have h_floor_le : (K : ℝ) ≤ t / (2 * Real.pi * (M : ℝ)) + 1 := by
    apply Nat.floor_le
    positivity
  linarith

lemma medium_algebra_bound (M : ℕ) (t : ℝ) (hM : 1 ≤ M) (ht1 : 1 ≤ t)
    (ht_med2 : t < (M : ℝ) ^ 2) :
    3 * (t / (2 * Real.pi * (M : ℝ)) + 2) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) ≤
      250 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  have ht_pos : 0 < t := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi3 := pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have h_sqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have h_sqrt_lt_M : Real.sqrt t < (M : ℝ) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg M)]
    exact Real.sqrt_lt_sqrt (by positivity) ht_med2
  have ht_eq : t = Real.sqrt t * Real.sqrt t := (Real.mul_self_sqrt ht_pos.le).symm
  have h_term1 : t / (2 * Real.pi * (M : ℝ)) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t) =
      (4 + 4 / Real.pi) * Real.sqrt t := by
    have hpi_ne : Real.pi ≠ 0 := hpi.ne'
    have hM_ne : (M : ℝ) ≠ 0 := hM_pos.ne'
    have hS_ne : Real.sqrt t ≠ 0 := h_sqrt_pos.ne'
    nth_rw 1 [ht_eq]
    field_simp
    ring
  have h_term2 : t / (2 * Real.pi * (M : ℝ)) ≤ (1 / (2 * Real.pi)) * Real.sqrt t := by
    have ht_div : t / (M : ℝ) ≤ Real.sqrt t := by
      have : t ≤ Real.sqrt t * (M : ℝ) := by
        calc t = Real.sqrt t * Real.sqrt t := ht_eq
          _ ≤ Real.sqrt t * (M : ℝ) := mul_le_mul_of_nonneg_left h_sqrt_lt_M.le h_sqrt_pos.le
      rwa [div_le_iff₀ hM_pos]
    calc t / (2 * Real.pi * (M : ℝ)) = (1 / (2 * Real.pi)) * (t / (M : ℝ)) := by ring
      _ ≤ (1 / (2 * Real.pi)) * Real.sqrt t := by
        have : 0 ≤ 1 / (2 * Real.pi) := by positivity
        exact mul_le_mul_of_nonneg_left ht_div this
  have h_term3 : 2 * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t) =
      (16 * Real.pi + 16) * ((M : ℝ) / Real.sqrt t) := by ring
  have h_term4 : (2 : ℝ) ≤ 2 * ((M : ℝ) / Real.sqrt t) := by
    have : 1 ≤ (M : ℝ) / Real.sqrt t := by
      rw [one_le_div h_sqrt_pos]
      linarith [h_sqrt_lt_M]
    linarith
  have h_prod : 3 * (t / (2 * Real.pi * (M : ℝ)) + 2) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) =
      3 * (t / (2 * Real.pi * (M : ℝ)) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t) +
           t / (2 * Real.pi * (M : ℝ)) +
           2 * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t) +
           2) := by ring
  rw [h_prod, h_term1, h_term3]
  have h_sqrt_nonneg : 0 ≤ Real.sqrt t := h_sqrt_pos.le
  have h_M_div_nonneg : 0 ≤ (M : ℝ) / Real.sqrt t := div_nonneg hM_pos.le h_sqrt_pos.le
  have : (4 + 4 / Real.pi) ≤ 6 := by
    have : 4 / Real.pi ≤ 4 / 3 := by
      have : 3 ≤ Real.pi := hpi3.le
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
    linarith
  have : 1 / (2 * Real.pi) ≤ 1 := by
    have : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [hpi3]
    exact div_le_one_of_le₀ this (by positivity)
  have : 16 * Real.pi + 16 ≤ 80 := by nlinarith [hpi4]
  nlinarith

lemma norm_sum_exp_phase_of_medium_t (M : ℕ) (t : ℝ) (hM : 1 ≤ M) (ht1 : 1 ≤ t)
    (ht_med1 : Real.pi * (M : ℝ) < t) (ht_med2 : t < (M : ℝ) ^ 2) :
    ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      250 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  have ht_pos : 0 < t := by linarith
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  set δ := Real.sqrt t / (8 * Real.pi * (M : ℝ))
  set K := Nat.floor (t / (2 * Real.pi * (M : ℝ)) + 1)
  set T : Finset (ℕ × Fin 3) := (Finset.range (K + 1)) ×ˢ (Finset.univ : Finset (Fin 3))
  have h_maps : ∀ m ∈ Finset.Ioc M (2 * M), ((vdc_k (vdc_d t m)).toNat, vdc_tag (vdc_d t m) δ) ∈ T := by
    intro m hm
    simp only [T, mem_product, mem_univ, and_true, mem_range]
    have hk_mem := vdc_k_mem_Icc t ht_pos M hM m hm
    simp only [mem_Icc] at hk_mem
    have h_toNat_le : (vdc_k (vdc_d t m)).toNat ≤ K := by
      change (vdc_k (vdc_d t m)).toNat ≤ (⌊t / (2 * Real.pi * (M : ℝ)) + 1⌋).toNat
      exact Int.toNat_le_toNat hk_mem.2
    omega
  set g_class : ℕ → ℕ × Fin 3 := fun m => ((vdc_k (vdc_d t m)).toNat, vdc_tag (vdc_d t m) δ)
  have h_fiber := Finset.sum_fiberwise_of_maps_to h_maps
    (fun m => Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I))
  have h_tri : ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      ∑ j ∈ T, ‖∑ m ∈ Finset.Ioc M (2 * M) with g_class m = j,
        Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ := by
    rw [← h_fiber]
    exact norm_sum_le T _
  have h_term_bound : ∀ j ∈ T, ‖∑ m ∈ Finset.Ioc M (2 * M) with g_class m = j,
      Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1 := by
    intro j _
    rcases j with ⟨k_nat, tag⟩
    set k : ℤ := (k_nat : ℤ)
    have heq_fiber : ∀ m ∈ Finset.Ioc M (2 * M),
        (g_class m = (k_nat, tag)) ↔ (vdc_class (vdc_d t m) δ = (k, tag)) := by
      intro m hm
      have hk_mem := vdc_k_mem_Icc t ht_pos M hM m hm
      simp only [mem_Icc] at hk_mem
      have h_toNat : (vdc_k (vdc_d t m)).toNat = k_nat ↔ vdc_k (vdc_d t m) = k := by
        constructor
        · intro h
          have : ((vdc_k (vdc_d t m)).toNat : ℤ) = (k_nat : ℤ) := by exact_mod_cast h
          rwa [Int.toNat_of_nonneg hk_mem.1] at this
        · intro h; rw [h]; rfl
      simp only [g_class, vdc_class, Prod.mk.injEq, h_toNat]
    have h_filter_eq : (Finset.Ioc M (2 * M)).filter (fun m => g_class m = (k_nat, tag)) =
        (Finset.Ioc M (2 * M)).filter (fun m => vdc_class (vdc_d t m) δ = (k, tag)) := by
      ext m
      simp only [mem_filter]
      constructor
      · intro ⟨hm1, hm2⟩; exact ⟨hm1, (heq_fiber m hm1).mp hm2⟩
      · intro ⟨hm1, hm2⟩; exact ⟨hm1, (heq_fiber m hm1).mpr hm2⟩
    rw [h_filter_eq]
    exact norm_sum_exp_fiber_le M t hM ht1 ht_med1 ht_med2 δ rfl k tag
  have h_sum_le : ∑ j ∈ T, ‖∑ m ∈ Finset.Ioc M (2 * M) with g_class m = j,
      Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (T.card : ℝ) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) := by
    have h_const : ∑ j ∈ T, ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) =
        (T.card : ℝ) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) := by
      simp only [sum_const, nsmul_eq_mul]
    rw [← h_const]
    exact sum_le_sum h_term_bound
  have h_card_le := card_T_le M t hM ht1
  have h_B_nonneg : 0 ≤ (8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1 := by positivity
  have h_mult_le : (T.card : ℝ) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) ≤
      3 * (t / (2 * Real.pi * (M : ℝ)) + 2) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) :=
    mul_le_mul_of_nonneg_right h_card_le h_B_nonneg
  have h_alg := medium_algebra_bound M t hM ht1 ht_med2
  linarith [h_tri, h_sum_le, h_mult_le, h_alg]

/-- Van der Corput second derivative bound for dyadic exponential sums of n^{-it}. -/
theorem norm_sum_exp_neg_log_mul_I_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) (t : ℝ), 1 ≤ M → 1 ≤ t →
      ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  refine ⟨250, by norm_num, ?_⟩
  intro M t hM ht
  have h_sum_nonneg : 0 ≤ Real.sqrt t + (M : ℝ) / Real.sqrt t := by positivity
  by_cases ht_large : (M : ℝ) ^ 2 ≤ t
  · have h := norm_sum_exp_phase_of_large_t M t hM ht_large
    calc ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I)‖
      _ ≤ 1 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := h
      _ ≤ 250 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by nlinarith
  · have ht_large' : t < (M : ℝ) ^ 2 := lt_of_not_ge ht_large
    by_cases ht_small : t ≤ Real.pi * (M : ℝ)
    · have h := norm_sum_exp_phase_of_small_t' M t hM ht ht_small
      have hpi4 := Real.pi_lt_four
      have : 8 * Real.pi + 1 ≤ 250 := by nlinarith [hpi4]
      calc ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I)‖
        _ ≤ (8 * Real.pi + 1) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := h
        _ ≤ 250 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by nlinarith
    · have ht_small' : Real.pi * (M : ℝ) < t := lt_of_not_ge ht_small
      exact norm_sum_exp_phase_of_medium_t M t hM ht ht_small' ht_large'

end Erdos1201.MR
