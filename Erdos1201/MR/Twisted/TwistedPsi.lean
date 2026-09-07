/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gemini

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.MR.Twisted.TwistedPrimeSums
import Erdos1201.MR.Twisted.TwistedBounds
import Erdos1201.MR.Twisted.TwistedChebyshev
import Erdos1201.Vendor.NumberTheory.PNT.MellinCalculus
import Erdos1201.Vendor.Analysis.SmoothExistence

/-!
# Twisted Chebyshev Error Bound: Main Theorem

This module formalizes the main estimate for the twisted von Mangoldt sum
`twistedPsi_sub_main_le`, establishing an exponential decay bound for the difference
between the twisted sum $\sum_{n \le X} \Lambda(n) n^{-iu}$ and the main term
$X^{1 - iu} / (1 - iu)$.
-/

namespace Erdos1201.MR

open Complex Real MeasureTheory Set Filter Function

lemma norm_cpow_sub_one_le {x : ℝ} (hx_ge : 1 / 2 ≤ x) (hx_le : x ≤ 2) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(x : ℂ) ^ w - 1‖ ≤ 2 * ‖w‖ := by
  have hx_pos : 0 < x := by linarith
  rw [cpow_def_of_ne_zero (by exact_mod_cast ne_of_gt hx_pos)]
  rw [← ofReal_log hx_pos.le]
  rw [mul_comm]
  have hlog_ge : - Real.log 2 ≤ Real.log x := by
    rw [← Real.log_inv]
    have : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rw [this]
    exact Real.log_le_log (by norm_num) hx_ge
  have hlog_le : Real.log x ≤ Real.log 2 := Real.log_le_log hx_pos hx_le
  have hlog_abs : |Real.log x| ≤ Real.log 2 := abs_le.mpr ⟨by linarith, hlog_le⟩
  have hlog2_lt1 : Real.log 2 < 1 := by
    linarith [Real.log_two_lt_d9]
  have h_arg_norm : ‖w * (Real.log x : ℂ)‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖w‖ * |Real.log x| ≤ 1 * Real.log 2 := mul_le_mul hw hlog_abs (abs_nonneg _) (by norm_num)
    _ ≤ 1 := by linarith
  have h_exp := Complex.norm_exp_sub_one_le h_arg_norm
  refine le_trans h_exp ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have : 2 * (‖w‖ * |Real.log x|) ≤ 2 * ‖w‖ * 1 := by
    have : |Real.log x| ≤ 1 := le_trans hlog_abs (by linarith)
    nlinarith [norm_nonneg w]
  linarith

lemma mellin_psi_sub_one_le {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1)
    {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖mellin (fun x => (ν x : ℂ)) w - 1‖ ≤ 2 * ‖w‖ := by
  have h_sub : Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ioi 0 := by
    intro x hx; simp only [mem_Icc, mem_Ioi] at hx ⊢; linarith
  have h_supp_m : Function.support (fun t : ℝ => (t : ℂ) ^ (w - 1) • (ν t : ℂ)) ⊆ Set.Icc (1 / 2) 2 := by
    intro t ht
    simp only [Function.mem_support, smul_eq_mul, ne_eq] at ht ⊢
    by_contra h_not
    have hν0 : ν t = 0 := by
      by_contra h_ne
      exact h_not (suppν (Function.mem_support.mpr h_ne))
    have : (t : ℂ) ^ (w - 1) * (ν t : ℂ) = 0 := by rw [hν0, ofReal_zero, mul_zero]
    exact ht this
  have hm : mellin (fun x => (ν x : ℂ)) w = ∫ t in Set.Icc (1 / 2 : ℝ) 2, (t : ℂ) ^ (w - 1) * (ν t : ℂ) := by
    dsimp [mellin]
    have h := @SetIntegral.integral_eq_integral_inter_of_support_subset_Icc (1 / 2) 2 volume ℂ _ _ (Ioi 0)
      (fun t : ℝ => (t : ℂ) ^ (w - 1) • (ν t : ℂ)) h_supp_m h_sub
    simp_rw [smul_eq_mul] at h ⊢
    exact h
  have h_supp_r : Function.support (fun t : ℝ => ν t / t) ⊆ Set.Icc (1 / 2) 2 := by
    intro t ht
    simp only [Function.mem_support, ne_eq] at ht ⊢
    by_contra h_not
    have hν0 : ν t = 0 := by
      by_contra h_ne
      exact h_not (suppν (Function.mem_support.mpr h_ne))
    have : ν t / t = 0 := by rw [hν0, zero_div]
    exact ht this
  have h1_real : ∫ t in Set.Icc (1 / 2 : ℝ) 2, ν t / t = 1 := by
    have h := @SetIntegral.integral_eq_integral_inter_of_support_subset_Icc (1 / 2) 2 volume ℝ _ _ (Ioi 0)
      (fun t : ℝ => ν t / t) h_supp_r h_sub
    rw [← h, mass_one]
  have h1 : (1 : ℂ) = ∫ t in Set.Icc (1 / 2 : ℝ) 2, ((ν t / t : ℝ) : ℂ) := by
    have h_int_real : (∫ t in Set.Icc (1 / 2 : ℝ) 2, ((ν t / t : ℝ) : ℂ)) =
        ((∫ t in Set.Icc (1 / 2 : ℝ) 2, ν t / t : ℝ) : ℂ) := integral_ofReal
    rw [h_int_real, h1_real, ofReal_one]

  have h_cont_m : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * (ν t : ℂ)) (Icc (1 / 2) 2) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.cpow_const
      · exact continuous_ofReal.continuousOn
      · intro x hx
        simp only [mem_Icc] at hx
        left; simpa using (by linarith : 0 < x)
    · exact (continuous_ofReal.comp diffν.continuous).continuousOn

  have h_cont_1 : ContinuousOn (fun t : ℝ => ((ν t / t : ℝ) : ℂ)) (Icc (1 / 2) 2) := by
    apply ContinuousOn.comp continuous_ofReal.continuousOn
    · apply ContinuousOn.div diffν.continuous.continuousOn continuousOn_id
      intro x hx; dsimp; linarith [hx.1]
    · intro x _; exact mem_univ _

  have h_int_m : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) * (ν t : ℂ)) (Icc (1 / 2) 2) :=
    h_cont_m.integrableOn_compact isCompact_Icc
  have h_int_1 : IntegrableOn (fun t : ℝ => ((ν t / t : ℝ) : ℂ)) (Icc (1 / 2) 2) :=
    h_cont_1.integrableOn_compact isCompact_Icc

  have h_diff_eq : mellin (fun x => (ν x : ℂ)) w - 1 =
      ∫ t in Set.Icc (1 / 2 : ℝ) 2, ((t : ℂ) ^ (w - 1) * (ν t : ℂ) - ((ν t / t : ℝ) : ℂ)) := by
    calc mellin (fun x => (ν x : ℂ)) w - 1
        = (∫ t in Set.Icc (1 / 2 : ℝ) 2, (t : ℂ) ^ (w - 1) * (ν t : ℂ)) -
            ∫ t in Set.Icc (1 / 2 : ℝ) 2, ((ν t / t : ℝ) : ℂ) := by rw [hm, h1]
      _ = ∫ t in Set.Icc (1 / 2 : ℝ) 2, ((t : ℂ) ^ (w - 1) * (ν t : ℂ) - ((ν t / t : ℝ) : ℂ)) :=
          (integral_sub h_int_m h_int_1).symm

  rw [h_diff_eq]
  have h_norm_le : ‖∫ t in Set.Icc (1 / 2 : ℝ) 2, ((t : ℂ) ^ (w - 1) * (ν t : ℂ) - ((ν t / t : ℝ) : ℂ))‖ ≤
      ∫ t in Set.Icc (1 / 2 : ℝ) 2, ‖(t : ℂ) ^ (w - 1) * (ν t : ℂ) - ((ν t / t : ℝ) : ℂ)‖ :=
    norm_integral_le_integral_norm _
  refine le_trans h_norm_le ?_

  have h_le_pt : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2,
      ‖(t : ℂ) ^ (w - 1) * (ν t : ℂ) - ((ν t / t : ℝ) : ℂ)‖ ≤ 2 * ‖w‖ * (ν t / t) := by
    intro t ht
    have ht_pos : 0 < t := by
      simp only [mem_Icc] at ht; linarith
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht_pos)
    have h_alg : (t : ℂ) ^ (w - 1) * (ν t : ℂ) - ((ν t / t : ℝ) : ℂ) = ((ν t / t : ℝ) : ℂ) * ((t : ℂ) ^ w - 1) := by
      have : (t : ℂ) ^ (w - 1) = (t : ℂ) ^ w * (t : ℂ)⁻¹ := by
        rw [sub_eq_add_neg, cpow_add _ _ ht_ne, cpow_neg_one]
      rw [this]; push_cast; ring
    rw [h_alg, norm_mul, Complex.norm_real, Real.norm_of_nonneg]
    · have h_cpow := norm_cpow_sub_one_le ht.1 ht.2 hw
      calc (ν t / t) * ‖(t : ℂ) ^ w - 1‖
          ≤ (ν t / t) * (2 * ‖w‖) := mul_le_mul_of_nonneg_left h_cpow (div_nonneg (νnonneg t ht_pos) ht_pos.le)
        _ = 2 * ‖w‖ * (ν t / t) := by ring
    · exact div_nonneg (νnonneg t ht_pos) ht_pos.le

  have h_cont_norm : ContinuousOn (fun t : ℝ => ‖(t : ℂ) ^ (w - 1) * (ν t : ℂ) - ((ν t / t : ℝ) : ℂ)‖) (Icc (1 / 2) 2) :=
    (h_cont_m.sub h_cont_1).norm
  have h_cont_bd : ContinuousOn (fun t : ℝ => 2 * ‖w‖ * (ν t / t)) (Icc (1 / 2) 2) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div diffν.continuous.continuousOn continuousOn_id
    intro x hx; dsimp; linarith [hx.1]

  have h1_int : IntegrableOn (fun t : ℝ => ‖(t : ℂ) ^ (w - 1) * (ν t : ℂ) - ((ν t / t : ℝ) : ℂ)‖) (Icc (1 / 2) 2) volume :=
    h_cont_norm.integrableOn_compact isCompact_Icc
  have h2_int : IntegrableOn (fun t : ℝ => 2 * ‖w‖ * (ν t / t)) (Icc (1 / 2) 2) volume :=
    h_cont_bd.integrableOn_compact isCompact_Icc

  have h_int_mono := setIntegral_mono_on h1_int h2_int measurableSet_Icc h_le_pt
  refine le_trans h_int_mono ?_
  rw [integral_const_mul, h1_real, mul_one]

lemma mellin_smooth1_sub_main_le {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1)
    {ε X u : ℝ} (hε : 0 < ε) (hX : 0 < X)
    (h_eps_s : ‖(ε : ℂ) * ((1 : ℂ) - (u : ℂ) * I)‖ ≤ 1) :
    ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) (1 - u * I) * (X : ℂ) ^ ((1 : ℂ) - u * I) -
        (X : ℂ) ^ ((1 : ℂ) - u * I) / ((1 : ℂ) - u * I)‖ ≤ 2 * ε * X := by
  let s : ℂ := 1 - (u : ℂ) * I
  have hs_re : 0 < s.re := by
    dsimp [s]
    simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, sub_zero, zero_lt_one]
  have hs_ne : s ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp only [zero_re] at this; linarith [hs_re]
  have h_mellin := MellinOfSmooth1a diffν suppν hε hs_re
  have h_norm_Xs : ‖(X : ℂ) ^ s‖ = X := by
    rw [norm_cpow_eq_rpow_re_of_pos hX]
    have : s.re = 1 := by
      dsimp [s]
      simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, sub_zero]
    rw [this, Real.rpow_one]
  have h_diff : mellin (fun x => (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s - (X : ℂ) ^ s / s =
      s⁻¹ * (X : ℂ) ^ s * (mellin (fun x => (ν x : ℂ)) ((ε : ℂ) * s) - 1) := by
    rw [h_mellin, div_eq_inv_mul]; ring
  rw [h_diff, norm_mul, norm_mul, norm_inv, h_norm_Xs]
  have h_psi := mellin_psi_sub_one_le diffν suppν νnonneg mass_one h_eps_s
  have h_norm_eps_s : ‖(ε : ℂ) * s‖ = ε * ‖s‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
  rw [h_norm_eps_s] at h_psi
  have hs_norm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs_ne
  calc ‖s‖⁻¹ * X * ‖mellin (fun x => (ν x : ℂ)) (↑ε * s) - 1‖
      ≤ ‖s‖⁻¹ * X * (2 * (ε * ‖s‖)) := mul_le_mul_of_nonneg_left h_psi (by positivity)
    _ = 2 * ε * X * (‖s‖⁻¹ * ‖s‖) := by ring
    _ = 2 * ε * X := by rw [inv_mul_cancel₀ (ne_of_gt hs_norm_pos), mul_one]

lemma mellin_smooth1_sub_main_unified {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1) :
    ∃ C_main > 0, ∀ {ε X u : ℝ} (_hε : 0 < ε) (_hε1 : ε < 1) (_hX : 0 < X),
      ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) (1 - u * I) * (X : ℂ) ^ ((1 : ℂ) - u * I) -
          (X : ℂ) ^ ((1 : ℂ) - u * I) / ((1 : ℂ) - u * I)‖ ≤ C_main * ε * X := by
  obtain ⟨C_M, hCM_pos, hCM⟩ := MellinOfSmooth1b diffν suppν
  let C_main := max 2 (C_M + 1)
  have hCmain_pos : 0 < C_main := by
    have : 0 < (2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this (le_max_left _ _)
  refine ⟨C_main, hCmain_pos, ?_⟩
  intro ε X u hε hε1 hX
  let s : ℂ := 1 - (u : ℂ) * I
  have hs_re : s.re = 1 := by
    dsimp [s]
    simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, sub_zero]
  have hs_ne : s ≠ 0 := by
    intro h; have := congr_arg Complex.re h; simp [hs_re] at this
  have hs_norm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs_ne
  have h_norm_Xs : ‖(X : ℂ) ^ s‖ = X := by
    rw [norm_cpow_eq_rpow_re_of_pos hX, hs_re, Real.rpow_one]
  by_cases h_case : ‖(ε : ℂ) * s‖ ≤ 1
  · have h_le := mellin_smooth1_sub_main_le diffν suppν νnonneg mass_one hε hX h_case
    refine le_trans h_le ?_
    have h_c2 : (2 : ℝ) ≤ C_main := le_max_left _ _
    calc 2 * ε * X = 2 * (ε * X) := by ring
      _ ≤ C_main * (ε * X) := mul_le_mul_of_nonneg_right h_c2 (by positivity)
      _ = C_main * ε * X := by ring
  · have h_not_le : 1 < ‖(ε : ℂ) * s‖ := lt_of_not_ge h_case
    have h_norm_eps_s : ‖(ε : ℂ) * s‖ = ε * ‖s‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε.le]
    rw [h_norm_eps_s] at h_not_le
    have h_inv_s_le_eps : ‖s‖⁻¹ ≤ ε := by
      have h1 : ‖s‖⁻¹ * 1 ≤ ‖s‖⁻¹ * (ε * ‖s‖) :=
        mul_le_mul_of_nonneg_left h_not_le.le (inv_nonneg.mpr hs_norm_pos.le)
      rw [mul_one] at h1
      have h2 : ‖s‖⁻¹ * (ε * ‖s‖) = ε * (‖s‖⁻¹ * ‖s‖) := by ring
      rw [inv_mul_cancel₀ (ne_of_gt hs_norm_pos), mul_one] at h2
      linarith
    have h_bound_M1 : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s‖ ≤ C_M * ε * X := by
      rw [norm_mul, h_norm_Xs]
      have hs1 : (1 / 2 : ℝ) ≤ s.re := by linarith [hs_re]
      have hs2 : s.re ≤ 2 := by linarith [hs_re]
      have hMb := hCM (1 / 2) (by norm_num) s hs1 hs2 ε hε hε1
      have h_calc : C_M * (ε * ‖s‖ ^ 2)⁻¹ ≤ C_M * ε := by
        have h_sq : ‖s‖⁻¹ * ‖s‖⁻¹ ≤ ε * ε := mul_le_mul h_inv_s_le_eps h_inv_s_le_eps (by positivity) hε.le
        have : (ε * ‖s‖ ^ 2)⁻¹ = ε⁻¹ * (‖s‖⁻¹ * ‖s‖⁻¹) := by
          rw [mul_inv, ← inv_pow, sq]
        rw [this]
        have h_inv_eps : ε⁻¹ * (‖s‖⁻¹ * ‖s‖⁻¹) ≤ ε⁻¹ * (ε * ε) :=
          mul_le_mul_of_nonneg_left h_sq (inv_nonneg.mpr hε.le)
        have h_cancel : ε⁻¹ * (ε * ε) = ε := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hε), one_mul]
        rw [h_cancel] at h_inv_eps
        exact mul_le_mul_of_nonneg_left h_inv_eps hCM_pos.le
      calc ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) s‖ * X
          ≤ (C_M * (ε * ‖s‖ ^ 2)⁻¹) * X := mul_le_mul_of_nonneg_right hMb (by positivity)
        _ ≤ (C_M * ε) * X := mul_le_mul_of_nonneg_right h_calc (by positivity)
        _ = C_M * ε * X := by ring
    have h_bound_M : ‖(X : ℂ) ^ s / s‖ ≤ ε * X := by
      rw [norm_div, h_norm_Xs, div_eq_mul_inv]
      calc X * ‖s‖⁻¹ ≤ X * ε := mul_le_mul_of_nonneg_left h_inv_s_le_eps hX.le
        _ = ε * X := by ring
    have h_tri := norm_sub_le (mellin (fun x => (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s) ((X : ℂ) ^ s / s)
    refine le_trans h_tri ?_
    have h_c_right : C_M + 1 ≤ C_main := le_max_right _ _
    calc ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) s * (X : ℂ) ^ s‖ + ‖(X : ℂ) ^ s / s‖
        ≤ C_M * ε * X + ε * X := add_le_add h_bound_M1 h_bound_M
      _ = (C_M + 1) * (ε * X) := by ring
      _ ≤ C_main * (ε * X) := mul_le_mul_of_nonneg_right h_c_right (by positivity)
      _ = C_main * ε * X := by ring

lemma mul_exp_neg_mul_le {η y : ℝ} (hη : 0 < η) (_hy : 0 ≤ y) :
    y * Real.exp (- (η * y)) ≤ 1 / η := by
  have h := Real.log_le_rpow_div (x := Real.exp y) (by positivity) hη
  rw [Real.log_exp, ← Real.exp_mul] at h
  have h2 := mul_le_mul_of_nonneg_right h (Real.exp_pos (- (η * y))).le
  rw [div_mul_eq_mul_div, ← Real.exp_add] at h2
  have : y * η + - (η * y) = 0 := by ring
  rw [this, Real.exp_zero] at h2
  exact h2

lemma pow_mul_exp_neg_mul_le {η y : ℝ} (hη : 0 < η) (hy : 0 ≤ y) (k : ℕ) (hk : 0 < k) :
    y ^ k * Real.exp (- (η * y)) ≤ (k / η) ^ k := by
  have h_k_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have h_eta_div_k : 0 < η / k := div_pos hη h_k_pos
  have h1 := mul_exp_neg_mul_le h_eta_div_k hy
  have h1_nonneg : 0 ≤ y * Real.exp (- (η / k * y)) := by positivity
  have h_pow := pow_le_pow_left₀ h1_nonneg h1 k
  rw [mul_pow, ← Real.exp_nat_mul] at h_pow
  have h_arg : (k : ℝ) * - (η / k * y) = - (η * y) := by
    calc (k : ℝ) * - (η / k * y) = - ((k : ℝ) * (η / k * y)) := by ring
      _ = - ((k : ℝ) * (η / k) * y) := by ring
      _ = - (η * y) := by rw [mul_div_cancel₀ _ (ne_of_gt h_k_pos)]
  rw [h_arg] at h_pow
  have h_inv : (1 / (η / k)) ^ k = (k / η) ^ k := by rw [one_div_div]
  rw [h_inv] at h_pow
  exact h_pow

lemma sum_vonMangoldt_cpow_le (X u : ℝ) (hX : 1 ≤ X) :
    ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I)‖ ≤ X * Real.log X := by
  have h_tri := norm_sum_le (Finset.Icc 1 ⌊X⌋₊) (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I))
  refine le_trans h_tri ?_
  have h_term : ∀ n ∈ Finset.Icc 1 ⌊X⌋₊, ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I)‖ ≤ Real.log X := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn_pos : 0 < n := hn.1
    have hn_pos_real : (0 : ℝ) < n := Nat.cast_pos.mpr hn_pos
    rw [norm_mul]
    have h_cast : (n : ℂ) = ((n : ℝ) : ℂ) := by simp
    rw [h_cast, norm_cpow_neg_mul_I hn_pos_real, mul_one, Complex.norm_real, Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h1 := ArithmeticFunction.vonMangoldt_le_log (n := n)
    have h2 : Real.log (n : ℝ) ≤ Real.log X := by
      apply Real.log_le_log hn_pos_real
      calc (n : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hn.2
        _ ≤ X := Nat.floor_le (by linarith)
    exact le_trans h1 h2
  have h_sum := Finset.sum_le_card_nsmul (Finset.Icc 1 ⌊X⌋₊) (fun n => ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I)‖) (Real.log X) h_term
  refine le_trans h_sum ?_
  rw [Nat.card_Icc]
  have h_card : ⌊X⌋₊ + 1 - 1 = ⌊X⌋₊ := Nat.add_sub_cancel _ _
  rw [h_card, nsmul_eq_mul]
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have h_floor_le : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
  exact mul_le_mul_of_nonneg_right h_floor_le hlogX

lemma log_le_four_mul_rpow_quarter {T : ℝ} (hT : 0 ≤ T) :
    Real.log T ≤ 4 * T ^ (1 / 4 : ℝ) := by
  have h := Real.log_le_rpow_div hT (by norm_num : (0 : ℝ) < 1 / 4)
  have : T ^ (1 / 4 : ℝ) / (1 / 4 : ℝ) = 4 * T ^ (1 / 4 : ℝ) := by ring
  rwa [this] at h

lemma K_mul_log_sq_le_of_ge {K T : ℝ} (hK : 1 ≤ K) (hT : (16 * K) ^ 4 ≤ T) :
    K * (Real.log T) ^ 2 ≤ T := by
  have hK_pos : 0 < K := by linarith
  have h16K_ge : (16 : ℝ) ≤ 16 * K := by linarith
  have h16K_pos : 0 < 16 * K := by positivity
  have h_base : (16 : ℝ) ^ 4 ≤ (16 * K) ^ 4 := by gcongr
  have hT_ge_16 : (16 : ℝ) ^ 4 ≤ T := le_trans h_base hT
  have hT_pos : 0 < T := by
    have : (0 : ℝ) < (16 : ℝ) ^ 4 := by norm_num
    linarith
  have h_log := log_le_four_mul_rpow_quarter hT_pos.le
  have h_log_nonneg : 0 ≤ Real.log T := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (16 : ℝ) ^ 4 := by norm_num
    linarith
  have h_sq : (Real.log T) ^ 2 ≤ 16 * (T ^ (1 / 4 : ℝ)) ^ 2 := by
    have h_sq' : (Real.log T) ^ 2 ≤ (4 * T ^ (1 / 4 : ℝ)) ^ 2 := by nlinarith
    have : (4 * T ^ (1 / 4 : ℝ)) ^ 2 = 16 * (T ^ (1 / 4 : ℝ)) ^ 2 := by ring
    linarith
  have h_rpow_sq : (T ^ (1 / 4 : ℝ)) ^ 2 = T ^ (1 / 2 : ℝ) := by
    have : (T ^ (1 / 4 : ℝ)) ^ 2 = (T ^ (1 / 4 : ℝ)) ^ (2 : ℝ) := by
      exact (Real.rpow_two _).symm
    rw [this, ← Real.rpow_mul hT_pos.le]
    norm_num
  rw [h_rpow_sq] at h_sq
  have h_K_log : K * (Real.log T) ^ 2 ≤ 16 * K * T ^ (1 / 2 : ℝ) := by
    calc K * (Real.log T) ^ 2 ≤ K * (16 * T ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left h_sq hK_pos.le
      _ = 16 * K * T ^ (1 / 2 : ℝ) := by ring
  refine le_trans h_K_log ?_
  have h_16K : 16 * K ≤ T ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity) hT (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h_pow : ((16 * K) ^ 4) ^ (1 / 4 : ℝ) = 16 * K := by
      have : ((16 * K) ^ (4 : ℝ)) ^ (1 / 4 : ℝ) = (16 * K) ^ ((4 : ℝ) * (1 / 4 : ℝ)) := by
        rw [← Real.rpow_mul h16K_pos.le]
      have h4 : ((16 * K) ^ 4 : ℝ) = (16 * K) ^ (4 : ℝ) := by
        have := (Real.rpow_natCast (16 * K) 4).symm
        push_cast at this; exact this
      rw [h4, this]
      norm_num
    rwa [h_pow] at h
  have h_16K_T12 : 16 * K * T ^ (1 / 2 : ℝ) ≤ T ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right h_16K (by positivity)
  refine le_trans h_16K_T12 ?_
  have h_prod : T ^ (1 / 4 : ℝ) * T ^ (1 / 2 : ℝ) = T ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hT_pos]
    norm_num
  rw [h_prod]
  have h_34_le_1 : T ^ (3 / 4 : ℝ) ≤ T ^ (1 : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le ?_ (by norm_num)
    have : (1 : ℝ) ≤ (16 : ℝ) ^ 4 := by norm_num
    linarith
  rw [Real.rpow_one] at h_34_le_1
  exact h_34_le_1

lemma rpow_le_rpow_of_exponent_le_one {y : ℝ} (hy : 1 ≤ y) :
    y ^ (1 / 16 : ℝ) ≤ y := by
  have : y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
  nth_rw 2 [this]
  exact Real.rpow_le_rpow_of_exponent_le hy (by norm_num)

lemma test_A_bound {A : ℕ} (hA : 3 ≤ A) : (2 : ℝ) < (A : ℝ) ^ (15 / 16 : ℝ) := by
  have hA_real : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have h_mono : (3 : ℝ) ^ (15 / 16 : ℝ) ≤ (A : ℝ) ^ (15 / 16 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hA_real (by norm_num)
  refine lt_of_lt_of_le ?_ h_mono
  have : (2 : ℝ) < (3 : ℝ) ^ (15 / 16 : ℝ) := by
    rw [← Real.rpow_lt_rpow_iff (by norm_num) (by positivity) (by norm_num : (0 : ℝ) < 16)]
    have h1 : ((3 : ℝ) ^ (15 / 16 : ℝ)) ^ (16 : ℝ) = (3 : ℝ) ^ ((15 / 16 : ℝ) * 16) := by
      rw [← Real.rpow_mul (by norm_num)]
    have h15 : (15 / 16 : ℝ) * 16 = 15 := by ring
    rw [h15] at h1
    rw [h1]
    have h2 : (2 : ℝ) ^ (16 : ℝ) = (65536 : ℝ) := by norm_num
    have h3 : (3 : ℝ) ^ (15 : ℝ) = (14348907 : ℝ) := by norm_num
    rw [h2, h3]
    norm_num
  exact this

lemma two_lt_X_mul_eps {c₁ : ℝ} {A : ℕ} {X : ℝ} (hA : 3 ≤ A) (hAX : (A : ℝ) ≤ X)
    (hc₁_pos : 0 < c₁) (hc₁_le : c₁ ≤ 1 / 4) :
    let ε := Real.exp (- (c₁ / 4) * (Real.log A) ^ (1 / 16 : ℝ))
    2 < X * ε := by
  intro ε
  have hA_ge3 : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hlog3_gt1 : (1 : ℝ) < Real.log 3 := by
    have : (Real.exp 1 : ℝ) < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_exp] at this
  have hlogA_ge : Real.log 3 ≤ Real.log (A : ℝ) := Real.log_le_log (by norm_num) hA_ge3
  have hlogA_gt1 : 1 < Real.log (A : ℝ) := lt_of_lt_of_le hlog3_gt1 hlogA_ge
  have h_le_log : (Real.log A) ^ (1 / 16 : ℝ) ≤ Real.log A :=
    rpow_le_rpow_of_exponent_le_one hlogA_gt1.le
  have h_c_le : c₁ / 4 ≤ 1 / 16 := by linarith
  have h_mul_le : (c₁ / 4) * (Real.log A) ^ (1 / 16 : ℝ) ≤ (1 / 16 : ℝ) * Real.log A := by
    calc (c₁ / 4) * (Real.log A) ^ (1 / 16 : ℝ)
        ≤ (1 / 16 : ℝ) * (Real.log A) ^ (1 / 16 : ℝ) := mul_le_mul_of_nonneg_right h_c_le (by positivity)
      _ ≤ (1 / 16 : ℝ) * Real.log A := mul_le_mul_of_nonneg_left h_le_log (by norm_num)
  have h_neg_le : -(1 / 16 : ℝ) * Real.log A ≤ - (c₁ / 4) * (Real.log A) ^ (1 / 16 : ℝ) := by
    linarith
  have h_exp_le : Real.exp (-(1 / 16 : ℝ) * Real.log A) ≤ ε := by
    dsimp [ε]
    exact Real.exp_le_exp.mpr h_neg_le
  have h_exp_eq : Real.exp (-(1 / 16 : ℝ) * Real.log A) = (A : ℝ) ^ (- (1 / 16 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    congr 1
    ring
  rw [h_exp_eq] at h_exp_le
  have hA_pos : (0 : ℝ) < (A : ℝ) := by linarith
  have h_mul_A : (A : ℝ) * (A : ℝ) ^ (- (1 / 16 : ℝ)) = (A : ℝ) ^ (15 / 16 : ℝ) := by
    have : (A : ℝ) = (A : ℝ) ^ (1 : ℝ) := (Real.rpow_one (A : ℝ)).symm
    nth_rw 1 [this]
    rw [← Real.rpow_add hA_pos]
    norm_num
  calc (2 : ℝ) < (A : ℝ) ^ (15 / 16 : ℝ) := test_A_bound hA
    _ = (A : ℝ) * (A : ℝ) ^ (- (1 / 16 : ℝ)) := h_mul_A.symm
    _ ≤ (A : ℝ) * ε := mul_le_mul_of_nonneg_left h_exp_le hA_pos.le
    _ ≤ X * ε := mul_le_mul_of_nonneg_right hAX (by positivity)

lemma log_T_le_BK {K : ℝ} {A : ℕ} {u : ℝ} (hK : 1 ≤ K) (hA : 3 ≤ A)
    (hu : 1 ≤ |u|) (hlogu : Real.log |u| ≤ (Real.log A) ^ (5 / 4 : ℝ)) :
    let B_K := 4 * Real.log (16 * K) + 15
    let T := (16 * K) ^ 4 * (A : ℝ) ^ 10 * (2 * |u| + 3)
    Real.log T ≤ B_K * (Real.log A) ^ (5 / 4 : ℝ) := by
  intro B_K T
  have hA_ge3 : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hlog3_gt1 : (1 : ℝ) < Real.log 3 := by
    have : (Real.exp 1 : ℝ) < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_exp] at this
  have hlogA_ge : Real.log 3 ≤ Real.log (A : ℝ) := Real.log_le_log (by norm_num) hA_ge3
  have hlogA_gt1 : 1 < Real.log (A : ℝ) := lt_of_lt_of_le hlog3_gt1 hlogA_ge
  have hlogA_pos : 0 < Real.log (A : ℝ) := by linarith
  have h16K_ge16 : (16 : ℝ) ≤ 16 * K := by linarith
  have h16K_pos : 0 < 16 * K := by positivity
  have hlog16K_nonneg : 0 ≤ Real.log (16 * K) := by
    apply Real.log_nonneg
    linarith
  have h16K4_pos : 0 < (16 * K) ^ 4 := by positivity
  have hA10_pos : 0 < (A : ℝ) ^ 10 := by positivity
  have hu_pos : 0 < 2 * |u| + 3 := by linarith [abs_nonneg u]
  have hT_eq : Real.log T = Real.log ((16 * K) ^ 4) + Real.log ((A : ℝ) ^ 10) + Real.log (2 * |u| + 3) := by
    dsimp [T]
    rw [Real.log_mul (by positivity) hu_pos.ne', Real.log_mul h16K4_pos.ne' hA10_pos.ne']
  rw [hT_eq]
  have h1 : Real.log ((16 * K) ^ 4) = 4 * Real.log (16 * K) := by
    rw [Real.log_pow (16 * K) 4]; ring
  have h2 : Real.log ((A : ℝ) ^ 10) = 10 * Real.log (A : ℝ) := by
    rw [Real.log_pow (A : ℝ) 10]; ring
  have h3 : Real.log (2 * |u| + 3) ≤ 4 + (Real.log A) ^ (5 / 4 : ℝ) := by
    have h_le5u : 2 * |u| + 3 ≤ 5 * |u| := by linarith
    have h_log_le : Real.log (2 * |u| + 3) ≤ Real.log (5 * |u|) :=
      Real.log_le_log hu_pos h_le5u
    refine le_trans h_log_le ?_
    rw [Real.log_mul (by norm_num) (by linarith)]
    have hlog5_le4 : Real.log 5 ≤ 4 := by
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 5)]
    linarith
  rw [h1, h2]
  have h_exp_ge1 : 1 ≤ (Real.log A) ^ (5 / 4 : ℝ) := by
    have : (1 : ℝ) = (1 : ℝ) ^ (5 / 4 : ℝ) := by norm_num
    rw [this]
    exact Real.rpow_le_rpow (by norm_num) hlogA_gt1.le (by norm_num)
  have h_exp_ge_log : Real.log (A : ℝ) ≤ (Real.log A) ^ (5 / 4 : ℝ) := by
    have : Real.log (A : ℝ) = (Real.log A) ^ (1 : ℝ) := (Real.rpow_one (Real.log A)).symm
    nth_rw 1 [this]
    exact Real.rpow_le_rpow_of_exponent_le hlogA_gt1.le (by norm_num : (1 : ℝ) ≤ 5 / 4)
  dsimp [B_K]
  calc 4 * Real.log (16 * K) + 10 * Real.log ↑A + Real.log (2 * |u| + 3)
      ≤ 4 * Real.log (16 * K) + 10 * Real.log ↑A + (4 + (Real.log A) ^ (5 / 4 : ℝ)) := by linarith [h3]
    _ ≤ 4 * Real.log (16 * K) * (Real.log A) ^ (5 / 4 : ℝ) + 10 * (Real.log A) ^ (5 / 4 : ℝ) +
          (4 * (Real.log A) ^ (5 / 4 : ℝ) + (Real.log A) ^ (5 / 4 : ℝ)) := by
        have h_a : 4 * Real.log (16 * K) ≤ 4 * Real.log (16 * K) * (Real.log A) ^ (5 / 4 : ℝ) := by
          calc 4 * Real.log (16 * K) = 4 * Real.log (16 * K) * 1 := by ring
            _ ≤ 4 * Real.log (16 * K) * (Real.log A) ^ (5 / 4 : ℝ) :=
              mul_le_mul_of_nonneg_left h_exp_ge1 (by positivity)
        have h_b : 10 * Real.log ↑A ≤ 10 * (Real.log A) ^ (5 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left h_exp_ge_log (by norm_num)
        have h_c : (4 : ℝ) ≤ 4 * (Real.log A) ^ (5 / 4 : ℝ) := by
          calc (4 : ℝ) = 4 * 1 := by ring
            _ ≤ 4 * (Real.log A) ^ (5 / 4 : ℝ) := mul_le_mul_of_nonneg_left h_exp_ge1 (by norm_num)
        linarith
    _ = (4 * Real.log (16 * K) + 15) * (Real.log A) ^ (5 / 4 : ℝ) := by ring

lemma theta_T_ge {K c₀' : ℝ} {A : ℕ} {u : ℝ} (hc₀' : 0 < c₀') (hK : 1 ≤ K) (hA : 3 ≤ A)
    (hu : 1 ≤ |u|) (hlogu : Real.log |u| ≤ (Real.log A) ^ (5 / 4 : ℝ)) :
    let B_K := 4 * Real.log (16 * K) + 15
    let T := (16 * K) ^ 4 * (A : ℝ) ^ 10 * (2 * |u| + 3)
    (c₀' / B_K ^ (3 / 4 : ℝ)) * (Real.log A) ^ (1 / 16 : ℝ) ≤ (c₀' / (Real.log T) ^ (3 / 4 : ℝ)) * Real.log A := by
  intro B_K T
  have hlog_le := log_T_le_BK hK hA hu hlogu
  have hA_ge3 : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hlog3_gt1 : (1 : ℝ) < Real.log 3 := by
    have : (Real.exp 1 : ℝ) < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_exp] at this
  have hlogA_ge : Real.log 3 ≤ Real.log (A : ℝ) := Real.log_le_log (by norm_num) hA_ge3
  have hlogA_gt1 : 1 < Real.log (A : ℝ) := lt_of_lt_of_le hlog3_gt1 hlogA_ge
  have hlogA_pos : 0 < Real.log (A : ℝ) := by linarith
  have hBK_pos : 0 < B_K := by
    dsimp [B_K]
    have : 0 ≤ Real.log (16 * K) := by
      apply Real.log_nonneg
      linarith
    linarith
  have hT_pos : 1 < T := by
    dsimp [T]
    have h1 : (1 : ℝ) ≤ (16 * K) ^ 4 := one_le_pow₀ (by linarith)
    have h2 : (1 : ℝ) ≤ (A : ℝ) ^ 10 := one_le_pow₀ (by linarith)
    have h3 : (1 : ℝ) < 2 * |u| + 3 := by linarith [abs_nonneg u]
    have h12 : (1 : ℝ) ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 := by
      calc (1 : ℝ) = 1 * 1 := by norm_num
        _ ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 := mul_le_mul h1 h2 (by norm_num) (by positivity)
    calc (1 : ℝ) < 1 * (2 * |u| + 3) := by linarith
      _ ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 * (2 * |u| + 3) :=
        mul_le_mul_of_nonneg_right h12 (by positivity)
  have hlogT_pos : 0 < Real.log T := Real.log_pos hT_pos
  have h_pow_le : (Real.log T) ^ (3 / 4 : ℝ) ≤ (B_K * (Real.log A) ^ (5 / 4 : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hlogT_pos.le hlog_le (by norm_num)
  have h_split : (B_K * (Real.log A) ^ (5 / 4 : ℝ)) ^ (3 / 4 : ℝ) =
      B_K ^ (3 / 4 : ℝ) * ((Real.log A) ^ (5 / 4 : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.mul_rpow hBK_pos.le (by positivity)
  have h_mult : ((Real.log A) ^ (5 / 4 : ℝ)) ^ (3 / 4 : ℝ) = (Real.log A) ^ (15 / 16 : ℝ) := by
    rw [← Real.rpow_mul hlogA_pos.le]
    norm_num
  rw [h_split, h_mult] at h_pow_le
  have h_inv : (B_K ^ (3 / 4 : ℝ) * (Real.log A) ^ (15 / 16 : ℝ))⁻¹ ≤ ((Real.log T) ^ (3 / 4 : ℝ))⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr h_pow_le
  have h_c_inv : c₀' / (B_K ^ (3 / 4 : ℝ) * (Real.log A) ^ (15 / 16 : ℝ)) ≤ c₀' / (Real.log T) ^ (3 / 4 : ℝ) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left h_inv hc₀'.le
  have h_div_split : c₀' / (B_K ^ (3 / 4 : ℝ) * (Real.log A) ^ (15 / 16 : ℝ)) =
      (c₀' / B_K ^ (3 / 4 : ℝ)) * ((Real.log A) ^ (15 / 16 : ℝ))⁻¹ := by
    ring
  rw [h_div_split] at h_c_inv
  have h_step := mul_le_mul_of_nonneg_right h_c_inv hlogA_pos.le
  have h_id : ((Real.log A) ^ (15 / 16 : ℝ))⁻¹ * Real.log A = (Real.log A) ^ (1 / 16 : ℝ) := by
    rw [← Real.rpow_neg hlogA_pos.le]
    have : Real.log A = (Real.log A) ^ (1 : ℝ) := (Real.rpow_one (Real.log A)).symm
    nth_rw 2 [this]
    rw [← Real.rpow_add hlogA_pos]
    norm_num
  calc (c₀' / B_K ^ (3 / 4 : ℝ)) * (Real.log A) ^ (1 / 16 : ℝ)
      = (c₀' / B_K ^ (3 / 4 : ℝ)) * (((Real.log A) ^ (15 / 16 : ℝ))⁻¹ * Real.log A) := by rw [h_id]
    _ = (c₀' / B_K ^ (3 / 4 : ℝ)) * ((Real.log A) ^ (15 / 16 : ℝ))⁻¹ * Real.log A := by ring
    _ ≤ c₀' / (Real.log T) ^ (3 / 4 : ℝ) * Real.log A := h_step

lemma log_X_le_two_log_A {A : ℕ} (hA : 3 ≤ A) {X : ℝ} (_hAX : (A : ℝ) ≤ X) (hX2A : X ≤ 2 * (A : ℝ)) :
    Real.log X ≤ 2 * Real.log (A : ℝ) := by
  have hA_pos : 0 < (A : ℝ) := by positivity
  have hX_pos : 0 < X := by
    have : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    linarith
  have hlogX : Real.log X ≤ Real.log (2 * (A : ℝ)) := Real.log_le_log hX_pos hX2A
  refine le_trans hlogX ?_
  rw [Real.log_mul (by norm_num) hA_pos.ne']
  have hlog2_le : Real.log 2 ≤ Real.log (A : ℝ) := by
    apply Real.log_le_log (by norm_num)
    have : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    linarith
  linarith

lemma log_A_eq_pow_16 {A : ℕ} (hA : 3 ≤ A) :
    Real.log (A : ℝ) = ((Real.log (A : ℝ)) ^ (1 / 16 : ℝ)) ^ 16 := by
  have hlogA_pos : 0 < Real.log (A : ℝ) := by
    apply Real.log_pos
    have : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    linarith
  have h_rpow : ((Real.log (A : ℝ)) ^ (1 / 16 : ℝ)) ^ 16 =
      ((Real.log (A : ℝ)) ^ (1 / 16 : ℝ)) ^ (16 : ℝ) := by
    have := (Real.rpow_natCast ((Real.log (A : ℝ)) ^ (1 / 16 : ℝ)) 16).symm
    push_cast at this; exact this
  rw [h_rpow, ← Real.rpow_mul hlogA_pos.le]
  norm_num

lemma log_A_52_eq_pow_40 {A : ℕ} (hA : 3 ≤ A) :
    (Real.log (A : ℝ)) ^ (5 / 2 : ℝ) = ((Real.log (A : ℝ)) ^ (1 / 16 : ℝ)) ^ 40 := by
  have hlogA_pos : 0 < Real.log (A : ℝ) := by
    apply Real.log_pos
    have : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    linarith
  have h_rpow : ((Real.log (A : ℝ)) ^ (1 / 16 : ℝ)) ^ 40 =
      ((Real.log (A : ℝ)) ^ (1 / 16 : ℝ)) ^ (40 : ℝ) := by
    have := (Real.rpow_natCast ((Real.log (A : ℝ)) ^ (1 / 16 : ℝ)) 40).symm
    push_cast at this; exact this
  rw [h_rpow, ← Real.rpow_mul hlogA_pos.le]
  congr 1
  norm_num

lemma term1_bound {c : ℝ} (hc : 0 < c) {A : ℕ} (hA : 3 ≤ A) {X : ℝ} (hAX : (A : ℝ) ≤ X) (hX2A : X ≤ 2 * (A : ℝ)) :
    let ε := Real.exp (- 2 * c * (Real.log A) ^ (1 / 16 : ℝ))
    ε * X * Real.log X ≤ (2 * (16 / c) ^ 16) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  intro ε
  have hlogX := log_X_le_two_log_A hA hAX hX2A
  have hX_nonneg : 0 ≤ X := by
    have : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    linarith
  have hε_nonneg : 0 ≤ ε := Real.exp_nonneg _
  have h_prod : ε * X * Real.log X ≤ ε * X * (2 * Real.log A) :=
    mul_le_mul_of_nonneg_left hlogX (by positivity)
  refine le_trans h_prod ?_
  have h_comm : ε * X * (2 * Real.log A) = 2 * X * (Real.log A * ε) := by ring
  rw [h_comm]
  have hlogA_eq := log_A_eq_pow_16 hA
  let y := (Real.log A) ^ (1 / 16 : ℝ)
  have hy_nonneg : 0 ≤ y := by positivity
  have h_eps_eq : ε = Real.exp (- (c * y)) * Real.exp (- (c * y)) := by
    dsimp [ε, y]
    rw [← Real.exp_add]
    congr 1
    linarith
  nth_rw 1 [hlogA_eq]
  rw [h_eps_eq]
  have h_assoc : y ^ 16 * (Real.exp (- (c * y)) * Real.exp (- (c * y))) =
      (y ^ 16 * Real.exp (- (c * y))) * Real.exp (- (c * y)) := by ring
  rw [h_assoc]
  have h_pow := pow_mul_exp_neg_mul_le hc hy_nonneg 16 (by norm_num)
  have h_term_le : (y ^ 16 * Real.exp (- (c * y))) * Real.exp (- (c * y)) ≤
      (16 / c) ^ 16 * Real.exp (- (c * y)) :=
    mul_le_mul_of_nonneg_right h_pow (Real.exp_pos _).le
  calc 2 * X * ((y ^ 16 * Real.exp (- (c * y))) * Real.exp (- (c * y)))
      ≤ 2 * X * ((16 / c) ^ 16 * Real.exp (- (c * y))) :=
        mul_le_mul_of_nonneg_left h_term_le (by positivity)
    _ = (2 * (16 / c) ^ 16) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
        have : -(c * y) = -c * (Real.log A) ^ (1 / 16 : ℝ) := by dsimp [y]; ring
        rw [this]
        ring

lemma term2_bound {c : ℝ} (hc : 0 < c) {A : ℕ} (_hA : 3 ≤ A) {X : ℝ} (hX : 0 ≤ X) :
    let ε := Real.exp (- 2 * c * (Real.log A) ^ (1 / 16 : ℝ))
    ε * X ≤ X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  intro ε
  let y := (Real.log A) ^ (1 / 16 : ℝ)
  have hy_nonneg : 0 ≤ y := by positivity
  have h_eps_eq : ε = Real.exp (- (c * y)) * Real.exp (- (c * y)) := by
    dsimp [ε, y]
    rw [← Real.exp_add]
    congr 1
    linarith
  rw [h_eps_eq]
  have h_le1 : Real.exp (- (c * y)) ≤ 1 := by
    have : - (c * y) ≤ 0 := by nlinarith
    exact Real.exp_le_one_iff.mpr this
  have h_prod_le : Real.exp (- (c * y)) * Real.exp (- (c * y)) ≤ 1 * Real.exp (- (c * y)) :=
    mul_le_mul_of_nonneg_right h_le1 (Real.exp_pos _).le
  rw [one_mul] at h_prod_le
  have h_le : (Real.exp (- (c * y)) * Real.exp (- (c * y))) * X ≤ Real.exp (- (c * y)) * X :=
    mul_le_mul_of_nonneg_right h_prod_le hX
  refine le_trans h_le ?_
  have : -(c * y) = -c * (Real.log A) ^ (1 / 16 : ℝ) := by dsimp [y]; ring
  rw [this, mul_comm]

lemma term5_bound {c σ₂ : ℝ} (hc : 0 < c) (hc_le : 8 * c ≤ 1 - σ₂)
    {A : ℕ} (hA : 3 ≤ A) {X : ℝ} (hAX : (A : ℝ) ≤ X) :
    let ε := Real.exp (- 2 * c * (Real.log A) ^ (1 / 16 : ℝ))
    X ^ σ₂ / ε ≤ X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  intro ε
  have hA_ge3 : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hA_pos : 0 < (A : ℝ) := by linarith
  have hX_pos : 0 < X := by linarith
  have hlog3_gt1 : (1 : ℝ) < Real.log 3 := by
    have : (Real.exp 1 : ℝ) < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_exp] at this
  have hlogA_ge : Real.log 3 ≤ Real.log (A : ℝ) := Real.log_le_log (by norm_num) hA_ge3
  have hlogA_gt1 : 1 < Real.log (A : ℝ) := lt_of_lt_of_le hlog3_gt1 hlogA_ge
  have h_le_log : (Real.log A) ^ (1 / 16 : ℝ) ≤ Real.log A :=
    rpow_le_rpow_of_exponent_le_one hlogA_gt1.le
  have h_sigma_le : σ₂ - 1 ≤ - (8 * c) := by linarith
  have h_sigma_nonpos : σ₂ - 1 ≤ 0 := by linarith
  have h_rpow_le : X ^ (σ₂ - 1) ≤ (A : ℝ) ^ (σ₂ - 1) :=
    Real.rpow_le_rpow_of_nonpos hA_pos hAX h_sigma_nonpos
  have hA_exp : (A : ℝ) ^ (σ₂ - 1) = Real.exp (Real.log A * (σ₂ - 1)) :=
    Real.rpow_def_of_pos hA_pos (σ₂ - 1)
  have hA_exp' : (A : ℝ) ^ (σ₂ - 1) = Real.exp ((σ₂ - 1) * Real.log A) := by
    rw [hA_exp, mul_comm]
  rw [hA_exp'] at h_rpow_le
  have hlogA_pos : 0 < Real.log (A : ℝ) := lt_trans (by norm_num) hlogA_gt1
  have h_exp_arg : (σ₂ - 1) * Real.log A ≤ - (8 * c) * (Real.log A) ^ (1 / 16 : ℝ) := by
    calc (σ₂ - 1) * Real.log A ≤ - (8 * c) * Real.log A :=
          mul_le_mul_of_nonneg_right h_sigma_le hlogA_pos.le
      _ = - ((8 * c) * Real.log A) := by ring
      _ ≤ - ((8 * c) * (Real.log A) ^ (1 / 16 : ℝ)) := by
          have : (8 * c) * (Real.log A) ^ (1 / 16 : ℝ) ≤ (8 * c) * Real.log A :=
            mul_le_mul_of_nonneg_left h_le_log (by positivity)
          linarith
      _ = - (8 * c) * (Real.log A) ^ (1 / 16 : ℝ) := by ring
  have h_rpow_exp_le : X ^ (σ₂ - 1) ≤ Real.exp (- (8 * c) * (Real.log A) ^ (1 / 16 : ℝ)) :=
    le_trans h_rpow_le (Real.exp_le_exp.mpr h_exp_arg)
  have h_split_X : X ^ σ₂ = X * X ^ (σ₂ - 1) := by
    calc X ^ σ₂ = X ^ (1 + (σ₂ - 1)) := by congr 1; ring
      _ = X ^ (1 : ℝ) * X ^ (σ₂ - 1) := Real.rpow_add hX_pos 1 (σ₂ - 1)
      _ = X * X ^ (σ₂ - 1) := by rw [Real.rpow_one]
  rw [h_split_X]
  have h_div : (X * X ^ (σ₂ - 1)) / ε = X * (X ^ (σ₂ - 1) / ε) := by ring
  rw [h_div]
  refine mul_le_mul_of_nonneg_left ?_ hX_pos.le
  have h_eps_inv : ε⁻¹ = Real.exp (2 * c * (Real.log A) ^ (1 / 16 : ℝ)) := by
    dsimp [ε]
    rw [← Real.exp_neg]
    congr 1
    ring
  have h_quot : X ^ (σ₂ - 1) / ε = X ^ (σ₂ - 1) * ε⁻¹ := div_eq_mul_inv _ _
  rw [h_quot, h_eps_inv]
  have h_mul_exp : X ^ (σ₂ - 1) * Real.exp (2 * c * (Real.log A) ^ (1 / 16 : ℝ)) ≤
      Real.exp (- (8 * c) * (Real.log A) ^ (1 / 16 : ℝ)) * Real.exp (2 * c * (Real.log A) ^ (1 / 16 : ℝ)) :=
    mul_le_mul_of_nonneg_right h_rpow_exp_le (Real.exp_pos _).le
  refine le_trans h_mul_exp ?_
  rw [← Real.exp_add]
  have h_add : - (8 * c) * (Real.log A) ^ (1 / 16 : ℝ) + 2 * c * (Real.log A) ^ (1 / 16 : ℝ) =
      - (6 * c) * (Real.log A) ^ (1 / 16 : ℝ) := by ring
  rw [h_add]
  have h_le_neg_c : - (6 * c) * (Real.log A) ^ (1 / 16 : ℝ) ≤ - c * (Real.log A) ^ (1 / 16 : ℝ) := by
    have : 0 ≤ (Real.log A) ^ (1 / 16 : ℝ) := by positivity
    nlinarith
  exact Real.exp_le_exp.mpr h_le_neg_c

lemma term4_bound {c K B_K : ℝ} (hc : 0 < c) (_hK : 0 ≤ K) (_hBK : 0 ≤ B_K)
    {A : ℕ} (hA : 3 ≤ A) {X : ℝ} (hAX : (A : ℝ) ≤ X)
    {θ_T φ_T : ℝ} (h_theta_logA : 8 * c * (Real.log A) ^ (1 / 16 : ℝ) ≤ θ_T * Real.log A)
    (h_phi_nonneg : 0 ≤ φ_T)
    (h_phi_le : φ_T ≤ K * B_K ^ 2 * (Real.log A) ^ (5 / 2 : ℝ)) :
    let ε := Real.exp (- 2 * c * (Real.log A) ^ (1 / 16 : ℝ))
    X ^ (1 - θ_T) * φ_T / ε ≤ (K * B_K ^ 2 * (8 / c) ^ 40) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  intro ε
  have hA_ge3 : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hA_pos : 0 < (A : ℝ) := by linarith
  have hX_pos : 0 < X := by linarith
  have hlog3_gt1 : (1 : ℝ) < Real.log 3 := by
    have : (Real.exp 1 : ℝ) < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_exp] at this
  have hlogA_ge : Real.log 3 ≤ Real.log (A : ℝ) := Real.log_le_log (by norm_num) hA_ge3
  have hlogA_gt1 : 1 < Real.log (A : ℝ) := lt_of_lt_of_le hlog3_gt1 hlogA_ge
  have hlogA_pos : 0 < Real.log (A : ℝ) := lt_trans (by norm_num) hlogA_gt1
  let y := (Real.log A) ^ (1 / 16 : ℝ)
  have hy_nonneg : 0 ≤ y := by positivity
  have h_theta_nonneg : 0 ≤ θ_T := by
    have h_prod_pos : 0 ≤ 8 * c * y := by positivity
    have h_le := le_trans h_prod_pos h_theta_logA
    exact nonneg_of_mul_nonneg_left h_le hlogA_pos
  have h_neg_theta_nonpos : -θ_T ≤ 0 := by linarith
  have h_rpow_le : X ^ (-θ_T) ≤ (A : ℝ) ^ (-θ_T) :=
    Real.rpow_le_rpow_of_nonpos hA_pos hAX h_neg_theta_nonpos
  have hA_exp : (A : ℝ) ^ (-θ_T) = Real.exp (Real.log A * (-θ_T)) :=
    Real.rpow_def_of_pos hA_pos (-θ_T)
  have hA_exp' : (A : ℝ) ^ (-θ_T) = Real.exp (- (θ_T * Real.log A)) := by
    rw [hA_exp]
    congr 1
    ring
  rw [hA_exp'] at h_rpow_le
  have h_neg_theta_logA : - (θ_T * Real.log A) ≤ - (8 * c * y) := by linarith [h_theta_logA]
  have h_rpow_exp_le : X ^ (-θ_T) ≤ Real.exp (- (8 * c * y)) :=
    le_trans h_rpow_le (Real.exp_le_exp.mpr h_neg_theta_logA)
  have h_split_X : X ^ (1 - θ_T) = X * X ^ (-θ_T) := by
    calc X ^ (1 - θ_T) = X ^ (1 : ℝ) * X ^ (-θ_T) := Real.rpow_add hX_pos 1 (-θ_T)
      _ = X * X ^ (-θ_T) := by rw [Real.rpow_one]
  rw [h_split_X]
  have h_phi_y : φ_T ≤ K * B_K ^ 2 * y ^ 40 := by
    have h40 := log_A_52_eq_pow_40 hA
    calc φ_T ≤ K * B_K ^ 2 * (Real.log A) ^ (5 / 2 : ℝ) := h_phi_le
      _ = K * B_K ^ 2 * y ^ 40 := by rw [h40]
  have h_eps_inv : ε⁻¹ = Real.exp (2 * c * y) := by
    dsimp [ε, y]
    rw [← Real.exp_neg]
    congr 1
    ring
  have h_KBK_nonneg : 0 ≤ K * B_K ^ 2 := by positivity
  have h_prod1 : X ^ (-θ_T) * φ_T ≤ Real.exp (- (8 * c * y)) * (K * B_K ^ 2 * y ^ 40) :=
    mul_le_mul h_rpow_exp_le h_phi_y h_phi_nonneg (Real.exp_nonneg _)
  have h_prod2 : X ^ (-θ_T) * φ_T * ε⁻¹ ≤
      (Real.exp (- (8 * c * y)) * (K * B_K ^ 2 * y ^ 40)) * Real.exp (2 * c * y) := by
    rw [h_eps_inv]
    exact mul_le_mul_of_nonneg_right h_prod1 (Real.exp_pos _).le
  have h_rearr : (Real.exp (- (8 * c * y)) * (K * B_K ^ 2 * y ^ 40)) * Real.exp (2 * c * y) =
      (K * B_K ^ 2) * (y ^ 40 * Real.exp (- (5 * c * y))) * Real.exp (- (c * y)) := by
    have h_exp_comb : Real.exp (- (8 * c * y)) * Real.exp (2 * c * y) =
        Real.exp (- (5 * c * y)) * Real.exp (- (c * y)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc (Real.exp (- (8 * c * y)) * (K * B_K ^ 2 * y ^ 40)) * Real.exp (2 * c * y)
        = (K * B_K ^ 2 * y ^ 40) * (Real.exp (- (8 * c * y)) * Real.exp (2 * c * y)) := by ring
      _ = (K * B_K ^ 2 * y ^ 40) * (Real.exp (- (5 * c * y)) * Real.exp (- (c * y))) := by rw [h_exp_comb]
      _ = (K * B_K ^ 2) * (y ^ 40 * Real.exp (- (5 * c * y))) * Real.exp (- (c * y)) := by ring
  have h5c_pos : 0 < 5 * c := by linarith
  have h_pow := pow_mul_exp_neg_mul_le h5c_pos hy_nonneg 40 (by norm_num)
  push_cast at h_pow
  have h_frac : (40 : ℝ) / (5 * c) = 8 / c := by ring
  rw [h_frac] at h_pow
  have h_main_le : (K * B_K ^ 2) * (y ^ 40 * Real.exp (- (5 * c * y))) * Real.exp (- (c * y)) ≤
      (K * B_K ^ 2 * (8 / c) ^ 40) * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
    have h1 : (K * B_K ^ 2) * (y ^ 40 * Real.exp (- (5 * c * y))) ≤
        (K * B_K ^ 2 * (8 / c) ^ 40) := by
      calc (K * B_K ^ 2) * (y ^ 40 * Real.exp (- (5 * c * y)))
          ≤ (K * B_K ^ 2) * (8 / c) ^ 40 := mul_le_mul_of_nonneg_left h_pow h_KBK_nonneg
        _ = (K * B_K ^ 2 * (8 / c) ^ 40) := by ring
    have h2 : Real.exp (- (c * y)) = Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
      congr 1; dsimp [y]; ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h_inner_le : X ^ (-θ_T) * φ_T * ε⁻¹ ≤
      (K * B_K ^ 2 * (8 / c) ^ 40) * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) :=
    le_trans h_prod2 (le_trans (le_of_eq h_rearr) h_main_le)
  calc (X * X ^ (-θ_T)) * φ_T / ε = X * (X ^ (-θ_T) * φ_T * ε⁻¹) := by ring
    _ ≤ X * ((K * B_K ^ 2 * (8 / c) ^ 40) * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))) :=
      mul_le_mul_of_nonneg_left h_inner_le hX_pos.le
    _ = (K * B_K ^ 2 * (8 / c) ^ 40) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by ring

lemma term3_bound {c K : ℝ} (hc : 0 < c) (hc_le : c ≤ 1 / 32) (hK : 1 ≤ K)
    {A : ℕ} (hA : 3 ≤ A) {X u : ℝ} (hAX : (A : ℝ) ≤ X) (hX2A : X ≤ 2 * (A : ℝ))
    (hu : 1 ≤ |u|) :
    let ε := Real.exp (- 2 * c * (Real.log A) ^ (1 / 16 : ℝ))
    let T := (16 * K) ^ 4 * (A : ℝ) ^ 10 * (2 * |u| + 3)
    X * Real.log X / (ε * T) ≤ X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  intro ε T
  have hA_ge3 : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hA_pos : 0 < (A : ℝ) := by linarith
  have hX_pos : 0 < X := by linarith
  have hlog3_gt1 : (1 : ℝ) < Real.log 3 := by
    have : (Real.exp 1 : ℝ) < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_exp] at this
  have hlogA_ge : Real.log 3 ≤ Real.log (A : ℝ) := Real.log_le_log (by norm_num) hA_ge3
  have hlogA_gt1 : 1 < Real.log (A : ℝ) := lt_of_lt_of_le hlog3_gt1 hlogA_ge
  have hlogA_pos : 0 < Real.log (A : ℝ) := lt_trans (by norm_num) hlogA_gt1
  let y := (Real.log A) ^ (1 / 16 : ℝ)
  have hy_le_log : y ≤ Real.log A := rpow_le_rpow_of_exponent_le_one hlogA_gt1.le
  have hy_nonneg : 0 ≤ y := by positivity
  have hT_ge_A10 : (A : ℝ) ^ 10 ≤ T := by
    dsimp [T]
    have h1 : (1 : ℝ) ≤ (16 * K) ^ 4 := by
      have : (1 : ℝ) ≤ 16 * K := by linarith
      exact one_le_pow₀ this
    have h3 : (1 : ℝ) ≤ 2 * |u| + 3 := by linarith
    have h1A : (A : ℝ) ^ 10 ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 := by
      calc (A : ℝ) ^ 10 = 1 * (A : ℝ) ^ 10 := by ring
        _ ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 := mul_le_mul_of_nonneg_right h1 (by positivity)
    calc (A : ℝ) ^ 10 ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 * 1 := by rw [mul_one]; exact h1A
      _ ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 * (2 * |u| + 3) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
  have hA10_pos : 0 < (A : ℝ) ^ 10 := by positivity
  have hT_pos : 0 < T := lt_of_lt_of_le hA10_pos hT_ge_A10
  have hT_inv_le : T⁻¹ ≤ ((A : ℝ) ^ 10)⁻¹ := (inv_le_inv₀ hT_pos hA10_pos).mpr hT_ge_A10
  have hA10_eq : (A : ℝ) ^ 10 = Real.exp (10 * Real.log A) := by
    have h1 : (A : ℝ) ^ 10 = (A : ℝ) ^ (10 : ℝ) := by
      have := (Real.rpow_natCast (A : ℝ) 10).symm; push_cast at this; exact this
    rw [h1, Real.rpow_def_of_pos hA_pos, mul_comm]
  have hA10_inv_eq : ((A : ℝ) ^ 10)⁻¹ = Real.exp (- (10 * Real.log A)) := by
    rw [hA10_eq, ← Real.exp_neg]
  rw [hA10_inv_eq] at hT_inv_le
  have h_eps_inv : ε⁻¹ = Real.exp (2 * c * y) := by
    dsimp [ε, y]
    rw [← Real.exp_neg]
    congr 1; ring
  have hlogX_le : Real.log X ≤ 2 * Real.log A := log_X_le_two_log_A hA hAX hX2A
  have hlogX_nonneg : 0 ≤ Real.log X := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (3 : ℝ) := by norm_num
    linarith
  have h_inner : Real.log X * ε⁻¹ * T⁻¹ ≤
      (2 * Real.log A) * Real.exp (2 * c * y) * Real.exp (- (10 * Real.log A)) := by
    have h1 := mul_le_mul hlogX_le (le_of_eq h_eps_inv) (by positivity) (by linarith)
    have h2 := mul_le_mul h1 hT_inv_le (by positivity) (by positivity)
    exact h2
  have h_div_eq : X * Real.log X / (ε * T) = X * (Real.log X * ε⁻¹ * T⁻¹) := by
    rw [div_eq_mul_inv, mul_inv]; ring
  rw [h_div_eq]
  have h_exp_comb : Real.exp (2 * c * y) * Real.exp (- (10 * Real.log A)) =
      Real.exp (- (8 * Real.log A)) * Real.exp (2 * c * y - 2 * Real.log A) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1; ring
  have h_log_bound := mul_exp_neg_mul_le (y := Real.log A) (by norm_num : (0 : ℝ) < 8) hlogA_pos.le
  have h_exp_le : Real.exp (2 * c * y - 2 * Real.log A) ≤ Real.exp (- (c * y)) := by
    refine Real.exp_le_exp.mpr ?_
    have : 3 * c * y ≤ 2 * Real.log A := by
      have h1 : 3 * c ≤ 3 * (1 / 32 : ℝ) := mul_le_mul_of_nonneg_left hc_le (by norm_num)
      have h2 : 3 * c * y ≤ (3 / 32 : ℝ) * Real.log A := by nlinarith [h1, hy_le_log]
      linarith [h2, hlogA_pos]
    linarith
  have h_prod_exp : (Real.log A * Real.exp (- (8 * Real.log A))) * Real.exp (2 * c * y - 2 * Real.log A) ≤
      (1 / 8 : ℝ) * Real.exp (- (c * y)) := by
    have h1 : 0 ≤ Real.log A * Real.exp (- (8 * Real.log A)) := by positivity
    have h2 : 0 ≤ Real.exp (2 * c * y - 2 * Real.log A) := by positivity
    nlinarith [h_log_bound, h_exp_le]
  have h_bracket : (2 * Real.log A) * Real.exp (2 * c * y) * Real.exp (- (10 * Real.log A)) ≤
      Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
    have h_assoc : (2 * Real.log A) * Real.exp (2 * c * y) * Real.exp (- (10 * Real.log A)) =
        2 * ((Real.log A * Real.exp (- (8 * Real.log A))) * Real.exp (2 * c * y - 2 * Real.log A)) := by
      calc (2 * Real.log A) * Real.exp (2 * c * y) * Real.exp (- (10 * Real.log A))
          = (2 * Real.log A) * (Real.exp (2 * c * y) * Real.exp (- (10 * Real.log A))) := by ring
        _ = (2 * Real.log A) * (Real.exp (- (8 * Real.log A)) * Real.exp (2 * c * y - 2 * Real.log A)) := by rw [h_exp_comb]
        _ = 2 * ((Real.log A * Real.exp (- (8 * Real.log A))) * Real.exp (2 * c * y - 2 * Real.log A)) := by ring
    rw [h_assoc]
    calc 2 * ((Real.log A * Real.exp (- (8 * Real.log A))) * Real.exp (2 * c * y - 2 * Real.log A))
        ≤ 2 * ((1 / 8 : ℝ) * Real.exp (- (c * y))) := mul_le_mul_of_nonneg_left h_prod_exp (by norm_num)
      _ = (1 / 4 : ℝ) * Real.exp (- (c * y)) := by ring
      _ ≤ 1 * Real.exp (- (c * y)) := mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
      _ = Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
          have : -(c * y) = -c * (Real.log A) ^ (1 / 16 : ℝ) := by dsimp [y]; ring
          rw [one_mul, this]
  calc X * (Real.log X * ε⁻¹ * T⁻¹)
      ≤ X * ((2 * Real.log A) * Real.exp (2 * c * y) * Real.exp (- (10 * Real.log A))) :=
        mul_le_mul_of_nonneg_left h_inner hX_pos.le
    _ ≤ X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) :=
        mul_le_mul_of_nonneg_left h_bracket hX_pos.le

lemma base_case_bound {c : ℝ} (hc : 0 < c) (hc_le : c ≤ 1 / 32) {A : ℕ} (hA3 : A = 3) {X u : ℝ} (hX3 : X = 3)
    (_hu : 1 ≤ |u|) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I)) -
        (X : ℂ) ^ ((1 : ℂ) - u * I) / ((1 : ℂ) - u * I)‖ ≤
      10 * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  have h_tri := norm_sub_le
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I))
    ((X : ℂ) ^ ((1 : ℂ) - u * I) / ((1 : ℂ) - u * I))
  refine le_trans h_tri ?_
  have hS_le : ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I)‖ ≤ 3 * Real.log 3 := by
    rw [hX3]
    exact sum_vonMangoldt_cpow_le 3 u (by norm_num)
  have hlog3_le2 : Real.log 3 ≤ 2 := by
    have : (3 : ℝ) ≤ Real.exp 2 := by
      have h1 : (2.7 : ℝ) ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9; linarith
      have h2 : (2.7 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 := by nlinarith
      rw [← Real.exp_nat_mul 1 2] at h2
      have : (3 : ℝ) ≤ (2.7 : ℝ) ^ 2 := by norm_num
      linarith
    have := Real.log_le_log (by norm_num) this
    rwa [Real.log_exp] at this
  have hS_le6 : ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I)‖ ≤ 6 := by
    calc ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I)‖
        ≤ 3 * Real.log 3 := hS_le
      _ ≤ 3 * 2 := mul_le_mul_of_nonneg_left hlog3_le2 (by norm_num)
      _ = 6 := by norm_num
  have hM_le3 : ‖(X : ℂ) ^ ((1 : ℂ) - u * I) / ((1 : ℂ) - u * I)‖ ≤ 3 := by
    rw [norm_div]
    have h_num : ‖(X : ℂ) ^ ((1 : ℂ) - u * I)‖ = 3 := by
      rw [hX3, norm_cpow_eq_rpow_re_of_pos (by norm_num)]
      have : ((1 : ℂ) - u * I).re = 1 := by
        simp only [sub_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, sub_zero]
      rw [this, Real.rpow_one]
    rw [h_num]
    have h_denom : 1 ≤ ‖(1 : ℂ) - u * I‖ := by
      have : ((1 : ℂ) - u * I).re ≤ ‖(1 : ℂ) - u * I‖ := Complex.re_le_norm _
      have h_re : ((1 : ℂ) - u * I).re = 1 := by
        simp only [sub_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, sub_zero]
      rwa [h_re] at this
    have h_div : (3 : ℝ) / ‖(1 : ℂ) - u * I‖ ≤ 3 / 1 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h_denom
    rw [div_one] at h_div
    exact h_div
  have hSM_le9 : ‖∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I)‖ +
      ‖(X : ℂ) ^ ((1 : ℂ) - u * I) / ((1 : ℂ) - u * I)‖ ≤ 9 := by linarith
  refine le_trans hSM_le9 ?_
  have hlog3_gt1 : 1 < Real.log 3 := by
    have : (Real.exp 1 : ℝ) < 3 := by
      have := Real.exp_one_lt_d9; linarith
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_exp] at this
  have h_rpow_le : (Real.log 3) ^ (1 / 16 : ℝ) ≤ Real.log 3 :=
    rpow_le_rpow_of_exponent_le_one hlog3_gt1.le
  have h_exp_arg : - Real.log 3 ≤ -c * (Real.log 3) ^ (1 / 16 : ℝ) := by
    have : c * (Real.log 3) ^ (1 / 16 : ℝ) ≤ Real.log 3 := by
      calc c * (Real.log 3) ^ (1 / 16 : ℝ) ≤ (1 / 32 : ℝ) * (Real.log 3) ^ (1 / 16 : ℝ) :=
            mul_le_mul_of_nonneg_right hc_le (by positivity)
        _ ≤ (1 / 32 : ℝ) * Real.log 3 := mul_le_mul_of_nonneg_left h_rpow_le (by norm_num)
        _ ≤ 1 * Real.log 3 := mul_le_mul_of_nonneg_right (by norm_num) (by linarith)
        _ = Real.log 3 := by ring
    linarith
  have h_exp_ge : (1 / 3 : ℝ) ≤ Real.exp (-c * (Real.log 3) ^ (1 / 16 : ℝ)) := by
    have h1 : Real.exp (- Real.log 3) ≤ Real.exp (-c * (Real.log 3) ^ (1 / 16 : ℝ)) :=
      Real.exp_le_exp.mpr h_exp_arg
    have h2 : Real.exp (- Real.log 3) = 1 / 3 := by
      rw [← Real.log_inv, Real.exp_log (by norm_num)]
      norm_num
    rwa [h2] at h1
  rw [hX3, hA3]
  calc (9 : ℝ) ≤ 10 * 3 * (1 / 3 : ℝ) := by norm_num
    _ ≤ 10 * 3 * Real.exp (-c * (Real.log 3) ^ (1 / 16 : ℝ)) :=
      mul_le_mul_of_nonneg_left h_exp_ge (by norm_num)

lemma hzeta_mono_twistedpsi {c₀ c₀' K : ℝ} (hle : c₀' ≤ c₀)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2) :
    ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀' / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2 := by
  intro σ t ht hσ hσ2
  refine hζ σ t ht ?_ hσ2
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hpow : 0 < (Real.log |t|) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hdiv : c₀' / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) :=
    div_le_div_of_nonneg_right hle hpow.le
  linarith

lemma hholo_mono_twistedpsi {c₀ c₀' : ℝ} (hle : c₀' ≤ c₀)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      ((Set.Icc (1 - c₀' / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1}) := by
  intro T hT
  have hH := hholo T hT
  refine hH.mono ?_
  intro z hz
  simp only [Set.mem_sdiff, Complex.mem_reProdIm, Set.mem_Icc, Set.mem_singleton_iff] at hz ⊢
  refine ⟨⟨?_, hz.1.2⟩, hz.2⟩
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hpow : 0 < (Real.log T) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hdiv : c₀' / (Real.log T) ^ (3 / 4 : ℝ) ≤ c₀ / (Real.log T) ^ (3 / 4 : ℝ) :=
    div_le_div_of_nonneg_right hle hpow.le
  refine ⟨by linarith [hz.1.1.1], hz.1.1.2⟩

lemma phi_ge_one'_twistedpsi {K : ℝ} (hK : 1 ≤ K) :
    ∀ t, 3 ≤ t → 1 ≤ K * (Real.log t) ^ 2 := by
  intro t ht
  have hlog3 : 1 < Real.log 3 := logt_gt_one (le_refl 3)
  have hlogt : 1 < Real.log t := lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) ht)
  have hsq : 1 ≤ (Real.log t) ^ 2 := by nlinarith
  nlinarith

lemma phi_mono'_twistedpsi {K : ℝ} (hK : 0 ≤ K) :
    MonotoneOn (fun t => K * (Real.log t) ^ 2) (Set.Ici 3) := by
  intro x hx y hy hxy
  have h3x : 3 ≤ x := hx
  have hx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  have hsq_le : (Real.log x) ^ 2 ≤ (Real.log y) ^ 2 := by
    nlinarith [hx_pos, hlog_le]
  exact mul_le_mul_of_nonneg_left hsq_le hK

set_option maxHeartbeats 800000 in
theorem twistedPsi_sub_main_le (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (A : ℕ) (X u : ℝ), 3 ≤ A → (A : ℝ) ≤ X → X ≤ 2 * A → 1 ≤ |u| → Real.log |u| ≤ (Real.log A) ^ (5 / 4 : ℝ) →
      ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)) -
          (X : ℂ) ^ ((1 : ℂ) - u * Complex.I) / ((1 : ℂ) - u * Complex.I)‖ ≤
        C * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  obtain ⟨ν, diffν, νnonneg_all, suppν, mass_one_ici⟩ := SmoothExistence
  have diffν1 : ContDiff ℝ 1 ν := diffν.of_le (by simp)
  have νnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ => νnonneg_all x
  have mass_one : ∫ x in Set.Ioi 0, ν x / x = 1 := by rwa [← MeasureTheory.integral_Ici_eq_integral_Ioi]
  obtain ⟨C_main, hCmain_pos, h_main⟩ := mellin_smooth1_sub_main_unified diffν1 suppν νnonneg mass_one
  obtain ⟨C_close, hCclose_pos, h_close⟩ := twistedSum_close ν diffν1 suppν νnonneg mass_one
  obtain ⟨σ₂, σ₂_pos, σ₂_lt_one, h_holo_zeta⟩ := holo_zeta_of_smallT
  let θ₀ := (1 - σ₂) / 2
  have hθ₀_pos : 0 < θ₀ := by dsimp [θ₀]; linarith
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3_34_pos : 0 < (Real.log 3) ^ (3 / 4 : ℝ) := rpow_pos_of_pos hlog3_pos _
  let c₀' := min c₀ (min ((1 / 2 : ℝ) * (Real.log 3) ^ (3 / 4 : ℝ)) (θ₀ * (Real.log 3) ^ (3 / 4 : ℝ)))
  have hc₀'_pos : 0 < c₀' := by
    dsimp [c₀']
    have : 0 < (1 / 2 : ℝ) * (Real.log 3) ^ (3 / 4 : ℝ) := mul_pos (by norm_num) hlog3_34_pos
    have : 0 < θ₀ * (Real.log 3) ^ (3 / 4 : ℝ) := mul_pos hθ₀_pos hlog3_34_pos
    positivity
  have hc₀'_le_c₀ : c₀' ≤ c₀ := min_le_left _ _
  have hc₀'_le_half : c₀' ≤ (1 / 2 : ℝ) * (Real.log 3) ^ (3 / 4 : ℝ) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hc₀'_le_theta0 : c₀' ≤ θ₀ * (Real.log 3) ^ (3 / 4 : ℝ) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hζ' := hzeta_mono_twistedpsi hc₀'_le_c₀ hζ
  have hholo' := hholo_mono_twistedpsi hc₀'_le_c₀ hholo
  let θ : ℝ → ℝ := fun t => c₀' / (Real.log t) ^ (3 / 4 : ℝ)
  let φ : ℝ → ℝ := fun t => K * (Real.log t) ^ 2
  have hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2 := by
    intro t ht
    have ht_pos : 0 < Real.log t := Real.log_pos (by linarith)
    have h1 : 0 < θ t := by dsimp [θ]; positivity
    have hlog3_le : (Real.log 3) ^ (3 / 4 : ℝ) ≤ (Real.log t) ^ (3 / 4 : ℝ) :=
      rpow_le_rpow (Real.log_pos (by norm_num)).le (Real.log_le_log (by norm_num) ht) (by norm_num)
    have h2 : θ t ≤ 1 / 2 := by
      dsimp [θ]
      calc c₀' / (Real.log t) ^ (3 / 4 : ℝ)
          ≤ ((1 / 2 : ℝ) * (Real.log 3) ^ (3 / 4 : ℝ)) / (Real.log t) ^ (3 / 4 : ℝ) :=
            div_le_div_of_nonneg_right hc₀'_le_half (by positivity)
        _ ≤ ((1 / 2 : ℝ) * (Real.log 3) ^ (3 / 4 : ℝ)) / (Real.log 3) ^ (3 / 4 : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hlog3_34_pos hlog3_le
        _ = 1 / 2 := by
            rw [mul_div_cancel_right₀ _ (ne_of_gt hlog3_34_pos)]
    exact ⟨h1, h2⟩
  have hθanti : AntitoneOn θ (Set.Ici 3) := theta_antitone hc₀'_pos.le
  have hφ : ∀ t, 3 ≤ t → 1 ≤ φ t := phi_ge_one'_twistedpsi hK
  have hφmono : MonotoneOn φ (Set.Ici 3) := phi_mono'_twistedpsi (by linarith)
  obtain ⟨C_tw, hCtw_pos, h_tw⟩ :=
    twistedSum_sub_main_le_of_holo ν diffν1 suppν νnonneg mass_one σ₂ σ₂_pos σ₂_lt_one h_holo_zeta
      θ φ hθ hθanti hφ hφmono hζ' hholo'
  let B_K := 4 * Real.log (16 * K) + 15
  have h16K : 1 ≤ 16 * K := by linarith
  have hlog16K : 0 ≤ Real.log (16 * K) := Real.log_nonneg h16K
  have hBK_pos : 0 < B_K := by dsimp [B_K]; linarith
  let c₁ := min (c₀' / B_K ^ (3 / 4 : ℝ)) (min (1 - σ₂) (1 / 4 : ℝ))
  have hc₁_pos : 0 < c₁ := by
    dsimp [c₁]
    have : 0 < c₀' / B_K ^ (3 / 4 : ℝ) := div_pos hc₀'_pos (rpow_pos_of_pos hBK_pos _)
    have : 0 < 1 - σ₂ := by linarith
    have : 0 < (1 / 4 : ℝ) := by norm_num
    positivity
  have hc₁_le_c₀' : c₁ ≤ c₀' / B_K ^ (3 / 4 : ℝ) := min_le_left _ _
  have hc₁_le_sigma2 : c₁ ≤ 1 - σ₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc₁_le_quarter : c₁ ≤ 1 / 4 := le_trans (min_le_right _ _) (min_le_right _ _)
  let c := c₁ / 8
  have hc_pos : 0 < c := by positivity
  have hc_le_32 : c ≤ 1 / 32 := by dsimp [c]; linarith [hc₁_le_quarter]
  have h8c_le_sigma2 : 8 * c ≤ 1 - σ₂ := by dsimp [c]; linarith
  have h8c_le_theta : 8 * c ≤ c₀' / B_K ^ (3 / 4 : ℝ) := by dsimp [c]; linarith
  let C := C_close * (2 * (16 / c) ^ 16) + C_main + C_tw * (2 + K * B_K ^ 2 * (8 / c) ^ 40) + 10
  have hC_pos : 0 < C := by positivity
  refine ⟨c, C, hc_pos, hC_pos, ?_⟩
  intro A X u hA hAX hX2A hu hlogu
  have hA_ge3 : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hA_pos : 0 < (A : ℝ) := by linarith
  have hX_pos : 0 < X := by linarith
  have hlogA_pos : 0 < Real.log (A : ℝ) := by
    apply Real.log_pos
    have : (1 : ℝ) < (3 : ℝ) := by norm_num
    linarith
  by_cases hX3 : 3 < X
  · let ε := Real.exp (- 2 * c * (Real.log A) ^ (1 / 16 : ℝ))
    let T := (16 * K) ^ 4 * (A : ℝ) ^ 10 * (2 * |u| + 3)
    have hε_pos : 0 < ε := Real.exp_pos _
    have hlogA_116_pos : 0 < (Real.log A) ^ (1 / 16 : ℝ) := rpow_pos_of_pos hlogA_pos _
    have hε_lt_one : ε < 1 := by
      dsimp [ε]
      have : - 2 * c * (Real.log A) ^ (1 / 16 : ℝ) < 0 := by nlinarith
      exact Real.exp_lt_one_iff.mpr this
    have h2_lt_Xeps : 2 < X * ε := by
      have h_eps_eq : ε = Real.exp (- (c₁ / 4) * (Real.log A) ^ (1 / 16 : ℝ)) := by
        dsimp [ε, c]; congr 1; ring
      have h2 := two_lt_X_mul_eps hA hAX hc₁_pos hc₁_le_quarter
      rwa [h_eps_eq]
    have h16K4_ge : (1 : ℝ) ≤ (16 * K) ^ 4 := one_le_pow₀ (by linarith)
    have hA10_ge : (1 : ℝ) ≤ (A : ℝ) ^ 10 := one_le_pow₀ (by linarith)
    have hu3_ge : (5 : ℝ) ≤ 2 * |u| + 3 := by linarith
    have hT_gt3 : 3 < T := by
      dsimp [T]
      have h1 : (65536 : ℝ) ≤ (16 * K) ^ 4 := by
        have : (16 : ℝ) ≤ 16 * K := by linarith
        have h_pow := pow_le_pow_left₀ (by norm_num) this 4
        have : (16 : ℝ) ^ 4 = 65536 := by norm_num
        linarith
      have h2 : (1 : ℝ) ≤ (A : ℝ) ^ 10 := hA10_ge
      have h3 : (5 : ℝ) ≤ 2 * |u| + 3 := hu3_ge
      have h12 : (65536 : ℝ) ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 := by
        calc (65536 : ℝ) = 65536 * 1 := by ring
          _ ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 := mul_le_mul h1 h2 (by norm_num) (by linarith)
      have h123 : (327680 : ℝ) ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 * (2 * |u| + 3) := by
        calc (327680 : ℝ) = 65536 * 5 := by norm_num
          _ ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 * (2 * |u| + 3) := mul_le_mul h12 h3 (by norm_num) (by linarith)
      linarith
    have hTu_le : 2 * |u| + 3 ≤ T := by
      dsimp [T]
      have h1 : 1 ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 := by
        calc (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 := mul_le_mul h16K4_ge hA10_ge (by norm_num) (by positivity)
      calc 2 * |u| + 3 = 1 * (2 * |u| + 3) := by ring
        _ ≤ (16 * K) ^ 4 * (A : ℝ) ^ 10 * (2 * |u| + 3) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
    have hT_ge_16K4 : (16 * K) ^ 4 ≤ T := by
      dsimp [T]
      have h_prod : (1 : ℝ) ≤ (A : ℝ) ^ 10 * (2 * |u| + 3) := by
        calc (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ (A : ℝ) ^ 10 * (2 * |u| + 3) := mul_le_mul hA10_ge (by linarith) (by norm_num) (by positivity)
      calc (16 * K) ^ 4 = (16 * K) ^ 4 * 1 := by ring
        _ ≤ (16 * K) ^ 4 * ((A : ℝ) ^ 10 * (2 * |u| + 3)) :=
          mul_le_mul_of_nonneg_left h_prod (by positivity)
        _ = (16 * K) ^ 4 * (A : ℝ) ^ 10 * (2 * |u| + 3) := by ring
    have hphiT_le : φ T ≤ T := K_mul_log_sq_le_of_ge hK hT_ge_16K4
    have hthetaT_le : θ T ≤ (1 - σ₂) / 2 := by
      dsimp [θ]
      have hT_ge3 : (3 : ℝ) ≤ T := hT_gt3.le
      have hlog3_le_logT : Real.log 3 ≤ Real.log T := Real.log_le_log (by norm_num) hT_ge3
      have h_pow_le : (Real.log 3) ^ (3 / 4 : ℝ) ≤ (Real.log T) ^ (3 / 4 : ℝ) :=
        rpow_le_rpow hlog3_pos.le hlog3_le_logT (by norm_num)
      calc c₀' / (Real.log T) ^ (3 / 4 : ℝ)
          ≤ c₀' / (Real.log 3) ^ (3 / 4 : ℝ) :=
            div_le_div_of_nonneg_left hc₀'_pos.le hlog3_34_pos h_pow_le
        _ ≤ (θ₀ * (Real.log 3) ^ (3 / 4 : ℝ)) / (Real.log 3) ^ (3 / 4 : ℝ) :=
            div_le_div_of_nonneg_right hc₀'_le_theta0 hlog3_34_pos.le
        _ = θ₀ := by rw [mul_div_cancel_right₀ _ (ne_of_gt hlog3_34_pos)]
    have h_bnd_tw := h_tw X hX3 ε hε_pos hε_lt_one u T hT_gt3 hTu_le hphiT_le hthetaT_le
    have h_bnd_close := h_close X hX3 ε hε_pos hε_lt_one h2_lt_Xeps u
    have h_bnd_main := h_main hε_pos hε_lt_one hX_pos (u := u)
    let S := ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I)
    let M := (X : ℂ) ^ ((1 : ℂ) - u * I) / ((1 : ℂ) - u * I)
    let T_sum := twistedSum ν ε X u
    let T_mel := mellin (fun x => (Smooth1 ν ε x : ℂ)) (1 - u * I) * (X : ℂ) ^ ((1 : ℂ) - u * I)
    have h_tri1 : ‖S - M‖ ≤ ‖S - T_sum‖ + ‖T_sum - M‖ := by
      have : S - M = (S - T_sum) + (T_sum - M) := by ring
      rw [this]
      exact norm_add_le _ _
    have h_tri2 : ‖T_sum - M‖ ≤ ‖T_sum - T_mel‖ + ‖T_mel - M‖ := by
      have : T_sum - M = (T_sum - T_mel) + (T_mel - M) := by ring
      rw [this]
      exact norm_add_le _ _
    have h_tri : ‖S - M‖ ≤ ‖T_sum - S‖ + ‖T_sum - T_mel‖ + ‖T_mel - M‖ := by
      rw [norm_sub_rev S T_sum] at h_tri1
      linarith
    refine le_trans h_tri ?_
    have h_t1 := term1_bound hc_pos hA hAX hX2A (c := c)
    have h_t2 := term2_bound hc_pos hA hX_pos.le (c := c)
    have h_t3 := term3_bound hc_pos hc_le_32 hK hA hAX hX2A hu (c := c)
    have h_theta_ge := theta_T_ge hc₀'_pos hK hA hu hlogu
    have h_theta_logA : 8 * c * (Real.log A) ^ (1 / 16 : ℝ) ≤ θ T * Real.log A := by
      calc 8 * c * (Real.log A) ^ (1 / 16 : ℝ)
          ≤ (c₀' / B_K ^ (3 / 4 : ℝ)) * (Real.log A) ^ (1 / 16 : ℝ) :=
            mul_le_mul_of_nonneg_right h8c_le_theta (by positivity)
        _ ≤ θ T * Real.log A := h_theta_ge
    have h_phi_le : φ T ≤ K * B_K ^ 2 * (Real.log A) ^ (5 / 2 : ℝ) := by
      dsimp [φ]
      have hlog_le := log_T_le_BK hK hA hu hlogu
      have h_sq : (Real.log T) ^ 2 ≤ (B_K * (Real.log A) ^ (5 / 4 : ℝ)) ^ 2 := by
        have : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        have : 0 ≤ B_K * (Real.log A) ^ (5 / 4 : ℝ) := by positivity
        nlinarith
      have h_mul_sq : (B_K * (Real.log A) ^ (5 / 4 : ℝ)) ^ 2 = B_K ^ 2 * ((Real.log A) ^ (5 / 4 : ℝ)) ^ 2 := mul_pow _ _ _
      have h_rpow_sq : ((Real.log A) ^ (5 / 4 : ℝ)) ^ 2 = (Real.log A) ^ (5 / 2 : ℝ) := by
        have : ((Real.log A) ^ (5 / 4 : ℝ)) ^ 2 = ((Real.log A) ^ (5 / 4 : ℝ)) ^ (2 : ℝ) := by
          have := (Real.rpow_natCast ((Real.log A) ^ (5 / 4 : ℝ)) 2).symm
          push_cast at this; exact this
        rw [this, ← Real.rpow_mul hlogA_pos.le]
        norm_num
      rw [h_mul_sq, h_rpow_sq] at h_sq
      calc K * (Real.log T) ^ 2 ≤ K * (B_K ^ 2 * (Real.log A) ^ (5 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left h_sq (by linarith)
        _ = K * B_K ^ 2 * (Real.log A) ^ (5 / 2 : ℝ) := by ring
    have h_phi_nonneg : 0 ≤ φ T := by dsimp [φ]; positivity
    have h_t4 := term4_bound hc_pos (by linarith) hBK_pos.le hA hAX h_theta_logA h_phi_nonneg h_phi_le (c := c)
    have h_t5 := term5_bound hc_pos h8c_le_sigma2 hA hAX (c := c)
    have h_all : C_close * (ε * X * Real.log X) +
        C_tw * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε) +
        C_main * ε * X ≤
        C * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
      have ht1_scaled : C_close * (ε * X * Real.log X) ≤
          (C_close * (2 * (16 / c) ^ 16)) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
        calc C_close * (ε * X * Real.log X)
            ≤ C_close * ((2 * (16 / c) ^ 16) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))) :=
              mul_le_mul_of_nonneg_left h_t1 hCclose_pos.le
          _ = (C_close * (2 * (16 / c) ^ 16)) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by ring
      have ht2_scaled : C_main * (ε * X) ≤ C_main * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
        calc C_main * (ε * X) ≤ C_main * (X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))) :=
          mul_le_mul_of_nonneg_left h_t2 hCmain_pos.le
          _ = C_main * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by ring
      have ht345_scaled : C_tw * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε) ≤
          (C_tw * (2 + K * B_K ^ 2 * (8 / c) ^ 40)) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
        have h_sum345 : X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε ≤
            (2 + K * B_K ^ 2 * (8 / c) ^ 40) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
          calc X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε
              ≤ X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) +
                (K * B_K ^ 2 * (8 / c) ^ 40) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) +
                X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by linarith [h_t3, h_t4, h_t5]
            _ = (2 + K * B_K ^ 2 * (8 / c) ^ 40) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by ring
        calc C_tw * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε)
            ≤ C_tw * ((2 + K * B_K ^ 2 * (8 / c) ^ 40) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))) :=
              mul_le_mul_of_nonneg_left h_sum345 hCtw_pos.le
          _ = (C_tw * (2 + K * B_K ^ 2 * (8 / c) ^ 40)) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by ring
      have h_sum_total : C_close * (ε * X * Real.log X) +
          C_tw * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε) +
          C_main * (ε * X) ≤
          (C_close * (2 * (16 / c) ^ 16) + C_main + C_tw * (2 + K * B_K ^ 2 * (8 / c) ^ 40)) *
            X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
        calc C_close * (ε * X * Real.log X) +
            C_tw * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε) +
            C_main * (ε * X)
            ≤ (C_close * (2 * (16 / c) ^ 16)) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) +
              (C_tw * (2 + K * B_K ^ 2 * (8 / c) ^ 40)) * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) +
              C_main * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by linarith [ht1_scaled, ht2_scaled, ht345_scaled]
          _ = (C_close * (2 * (16 / c) ^ 16) + C_main + C_tw * (2 + K * B_K ^ 2 * (8 / c) ^ 40)) *
                X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by ring
      have h_C_le : (C_close * (2 * (16 / c) ^ 16) + C_main + C_tw * (2 + K * B_K ^ 2 * (8 / c) ^ 40)) ≤ C := by
        dsimp [C]; linarith
      have h_pos_term : 0 ≤ X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by positivity
      calc C_close * (ε * X * Real.log X) +
          C_tw * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε) +
          C_main * ε * X
          = C_close * (ε * X * Real.log X) +
            C_tw * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε) +
            C_main * (ε * X) := by ring
        _ ≤ (C_close * (2 * (16 / c) ^ 16) + C_main + C_tw * (2 + K * B_K ^ 2 * (8 / c) ^ 40)) *
              X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := h_sum_total
        _ = (C_close * (2 * (16 / c) ^ 16) + C_main + C_tw * (2 + K * B_K ^ 2 * (8 / c) ^ 40)) *
              (X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))) := by ring
        _ ≤ C * (X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))) :=
          mul_le_mul_of_nonneg_right h_C_le h_pos_term
        _ = C * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by ring
    calc ‖T_sum - S‖ + ‖T_sum - T_mel‖ + ‖T_mel - M‖
        ≤ C_close * ε * X * Real.log X +
          C_tw * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε) +
          C_main * ε * X := by linarith [h_bnd_close, h_bnd_tw, h_bnd_main]
      _ = C_close * (ε * X * Real.log X) +
          C_tw * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε) +
          C_main * ε * X := by ring
      _ ≤ C * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := h_all
  · have hX_ge3 : (3 : ℝ) ≤ X := by
      have : (3 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
      linarith
    have hX_eq3 : X = 3 := by linarith [hX3, hX_ge3]
    have hA_eq3 : A = 3 := by
      have hA_real_le : (A : ℝ) ≤ 3 := by linarith [hAX, hX_eq3]
      have : A ≤ 3 := by exact_mod_cast hA_real_le
      omega
    have h_base := base_case_bound hc_pos hc_le_32 hA_eq3 hX_eq3 hu
    refine le_trans h_base ?_
    have h10_le_C : (10 : ℝ) ≤ C := by
      dsimp [C]
      have : 0 ≤ C_close * (2 * (16 / c) ^ 16) := by positivity
      have : 0 ≤ C_main := hCmain_pos.le
      have : 0 ≤ C_tw * (2 + K * B_K ^ 2 * (8 / c) ^ 40) := by positivity
      linarith
    have h_pos_term : 0 ≤ X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by positivity
    calc 10 * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))
        = 10 * (X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))) := by ring
      _ ≤ C * (X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))) :=
        mul_le_mul_of_nonneg_right h10_le_C h_pos_term
      _ = C * X * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by ring

end Erdos1201.MR
