/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
import Mathlib
import Erdos1201.MR.Vinogradov.ZetaBound
import Erdos1201.MR.Vinogradov.ZeroFreeGeneral
import Erdos1201.MR.Vinogradov.BilinearEstimate
import Erdos1201.Vendor.NumberTheory.PNT.ZetaBounds
import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.ZeroFreeRegionCapstone
import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.JensenZeroCountingDistanceBounds
import Erdos1201.Vendor.NumberTheory.ZetaFunctionEstimates.ZetaLogDerivativeBounds
import Erdos1201.Vendor.NumberTheory.BoundedPrimeGaps.BombieriVinogradov.Analytic.RiemannZetaZeroFree

/-!
# Vinogradov-Korobov Zero-Free Region and Logarithmic Derivative Bound

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

open Complex Metric ZetaFunctionEstimates AnalyticZeroCounting ZetaZeroFreeRegion Erdos1201.MR.Vinogradov

namespace Erdos1201.MR

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

lemma log_two_mul_le (t : ℝ) (ht : 3 ≤ t) : Real.log (2 * t) ≤ 2 * Real.log t := by
  have htpos : 0 < t := by linarith
  have h2pos : (0 : ℝ) < 2 := by norm_num
  rw [Real.log_mul (ne_of_gt h2pos) (ne_of_gt htpos)]
  have hlog2_le : Real.log 2 ≤ Real.log t := by
    apply Real.log_le_log (by norm_num)
    linarith
  linarith

lemma log_log_two_mul_le (t : ℝ) (ht : 3 ≤ t) :
    Real.log (Real.log (2 * t)) ≤ Real.log (Real.log t) + 1 := by
  have htpos : 0 < t := by linarith
  have h3pos : (0 : ℝ) < 3 := by norm_num
  have hlogt_pos : 0 < Real.log t := by
    have : (1 : ℝ) < Real.log 3 := one_lt_log_three'
    have : Real.log 3 ≤ Real.log t := Real.log_le_log h3pos ht
    linarith
  have h2t_gt1 : 1 < 2 * t := by linarith
  have hlog2t_pos : 0 < Real.log (2 * t) := Real.log_pos h2t_gt1
  have h_mul := log_two_mul_le t ht
  have h_le := Real.log_le_log hlog2t_pos h_mul
  have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
  rw [Real.log_mul h2_ne (ne_of_gt hlogt_pos)] at h_le
  have hlog2_lt1 : Real.log 2 ≤ 1 := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (by norm_num)
    linarith [Real.exp_one_gt_d9]
  linarith

lemma log_log_two_mul_add_one_le (t : ℝ) (ht : 3 ≤ t) :
    Real.log (Real.log (2 * t)) + 1 ≤ 2 * (Real.log (Real.log t) + 1) := by
  have h := log_log_two_mul_le t ht
  have hlogt_ge : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlog3_gt1 : 1 < Real.log 3 := one_lt_log_three'
  have hlogt_gt1 : 1 < Real.log t := lt_of_lt_of_le hlog3_gt1 hlogt_ge
  have hloglogt_pos : 0 < Real.log (Real.log t) := Real.log_pos hlogt_gt1
  linarith

lemma two_rpow_two_thirds_le_two : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
  have : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rwa [Real.rpow_one] at this

lemma two_rpow_three_quarters_le_two : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
  have : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  rwa [Real.rpow_one] at this

lemma theta_dyadic_le (c : ℝ) (hc : 0 < c) (t : ℝ) (ht : 3 ≤ t) :
    c / (Real.log t) ^ (2 / 3 : ℝ) ≤ 2 * (c / (Real.log (2 * t)) ^ (2 / 3 : ℝ)) := by
  have hlogt_ge : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlog3_gt1 : 1 < Real.log 3 := one_lt_log_three'
  have hlogt_gt1 : 1 < Real.log t := lt_of_lt_of_le hlog3_gt1 hlogt_ge
  have hlogt_pos : 0 < Real.log t := by linarith
  have h2t_gt1 : 1 < 2 * t := by linarith
  have hlog2t_pos : 0 < Real.log (2 * t) := Real.log_pos h2t_gt1
  have h_mul := log_two_mul_le t ht
  have h_rpow : (Real.log (2 * t)) ^ (2 / 3 : ℝ) ≤ (2 * Real.log t) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (le_of_lt hlog2t_pos) h_mul (by norm_num)
  have h2_rpow : (2 * Real.log t) ^ (2 / 3 : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) * (Real.log t) ^ (2 / 3 : ℝ) :=
    Real.mul_rpow (by norm_num) (le_of_lt hlogt_pos)
  rw [h2_rpow] at h_rpow
  have h_rpow_le : (Real.log (2 * t)) ^ (2 / 3 : ℝ) ≤ 2 * (Real.log t) ^ (2 / 3 : ℝ) := by
    have h_prod : (2 : ℝ) ^ (2 / 3 : ℝ) * (Real.log t) ^ (2 / 3 : ℝ) ≤ 2 * (Real.log t) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right two_rpow_two_thirds_le_two (by positivity)
    exact le_trans h_rpow h_prod
  have hden_pos1 : 0 < (Real.log t) ^ (2 / 3 : ℝ) := by positivity
  have hden_pos2 : 0 < (Real.log (2 * t)) ^ (2 / 3 : ℝ) := by positivity
  rw [div_le_iff₀ hden_pos1]
  have h_alg : 2 * (c / (Real.log (2 * t)) ^ (2 / 3 : ℝ)) * (Real.log t) ^ (2 / 3 : ℝ) =
      c * (2 * (Real.log t) ^ (2 / 3 : ℝ)) / (Real.log (2 * t)) ^ (2 / 3 : ℝ) := by ring
  rw [h_alg]
  rw [le_div_iff₀ hden_pos2]
  exact mul_le_mul_of_nonneg_left h_rpow_le (le_of_lt hc)

lemma theta_loc_le (c : ℝ) (hc : 0 < c) (t t' : ℝ) (ht : 3 ≤ t) (htt' : |t' - t| ≤ 1) :
    (c / (Real.log t) ^ (2 / 3 : ℝ)) / 2 ≤ c / (Real.log t') ^ (2 / 3 : ℝ) := by
  have ht_le : t' ≤ 2 * t := by
    have : t' - t ≤ 1 := (abs_le.mp htt').2
    linarith
  have ht'_gt1 : 1 < t' := by
    have : -1 ≤ t' - t := (abs_le.mp htt').1
    linarith
  have hlogt'_pos : 0 < Real.log t' := Real.log_pos ht'_gt1
  have hlogt_pos : 0 < Real.log t := Real.log_pos (by linarith)
  have ht'pos : 0 < t' := by linarith
  have htpos : 0 < t := by linarith
  have hlogt'_le : Real.log t' ≤ 2 * Real.log t := by
    have h1 : Real.log t' ≤ Real.log (2 * t) := Real.log_le_log ht'pos ht_le
    have h2 := log_two_mul_le t ht
    exact le_trans h1 h2
  have h_rpow : (Real.log t') ^ (2 / 3 : ℝ) ≤ 2 * (Real.log t) ^ (2 / 3 : ℝ) := by
    have h1 : (Real.log t') ^ (2 / 3 : ℝ) ≤ (2 * Real.log t) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt hlogt'_pos) hlogt'_le (by norm_num)
    have h2 : (2 * Real.log t) ^ (2 / 3 : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) * (Real.log t) ^ (2 / 3 : ℝ) :=
      Real.mul_rpow (by norm_num) (le_of_lt hlogt_pos)
    have h3 : (2 : ℝ) ^ (2 / 3 : ℝ) * (Real.log t) ^ (2 / 3 : ℝ) ≤ 2 * (Real.log t) ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right two_rpow_two_thirds_le_two (by positivity)
    exact le_trans h1 (by rw [h2]; exact h3)
  have hden_pos2 : 0 < (Real.log t') ^ (2 / 3 : ℝ) := by positivity
  have h_alg : (c / (Real.log t) ^ (2 / 3 : ℝ)) / 2 = c / (2 * (Real.log t) ^ (2 / 3 : ℝ)) := by
    ring
  rw [h_alg]
  exact div_le_div_of_nonneg_left (le_of_lt hc) hden_pos2 h_rpow

lemma phi_loc_le (K : ℝ) (hK : 0 ≤ K) (t t' : ℝ) (ht : 3 ≤ t) (htt' : |t' - t| ≤ 1) :
    K * (Real.log (Real.log t') + 1) ≤ 2 * (K * (Real.log (Real.log t) + 1)) := by
  have ht_le : t' ≤ 2 * t := by
    have : t' - t ≤ 1 := (abs_le.mp htt').2
    linarith
  have ht'_gt1 : 1 < t' := by
    have : -1 ≤ t' - t := (abs_le.mp htt').1
    linarith
  have hlogt'_pos : 0 < Real.log t' := Real.log_pos ht'_gt1
  have ht'pos : 0 < t' := by linarith
  have h1 : Real.log t' ≤ Real.log (2 * t) := Real.log_le_log ht'pos ht_le
  have h2 : Real.log (Real.log t') ≤ Real.log (Real.log (2 * t)) :=
    Real.log_le_log hlogt'_pos h1
  have h_two := log_log_two_mul_add_one_le t ht
  have h3 : Real.log (Real.log t') + 1 ≤ 2 * (Real.log (Real.log t) + 1) := by linarith [h2, h_two]
  have h_alg : 2 * (K * (Real.log (Real.log t) + 1)) = K * (2 * (Real.log (Real.log t) + 1)) := by ring
  rw [h_alg]
  exact mul_le_mul_of_nonneg_left h3 hK

lemma log_three_div_theta_le (c : ℝ) (hc : 0 < c) (K : ℝ) (hK : Real.log (3 / c) ≤ K) (hK1 : 1 ≤ K)
    (t : ℝ) (ht : 3 ≤ t) :
    Real.log (3 / (c / (Real.log t) ^ (2 / 3 : ℝ))) ≤ K * (Real.log (Real.log t) + 1) := by
  have hlogt_ge : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlog3_gt1 : 1 < Real.log 3 := one_lt_log_three'
  have hlogt_gt1 : 1 < Real.log t := lt_of_lt_of_le hlog3_gt1 hlogt_ge
  have hlogt_pos : 0 < Real.log t := by linarith
  have hloglogt_pos : 0 < Real.log (Real.log t) := Real.log_pos hlogt_gt1
  have hrpow_pos : 0 < (Real.log t) ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hlogt_pos _
  have h_alg : 3 / (c / (Real.log t) ^ (2 / 3 : ℝ)) = (3 / c) * (Real.log t) ^ (2 / 3 : ℝ) := by
    rw [div_div_eq_mul_div, mul_div_right_comm]
  rw [h_alg]
  have h3c_pos : 0 < 3 / c := div_pos (by norm_num) hc
  rw [Real.log_mul (ne_of_gt h3c_pos) (ne_of_gt hrpow_pos)]
  rw [Real.log_rpow hlogt_pos]
  have h_term2 : (2 / 3 : ℝ) * Real.log (Real.log t) ≤ K * Real.log (Real.log t) := by
    have : (2 / 3 : ℝ) ≤ K := by linarith
    exact mul_le_mul_of_nonneg_right this (le_of_lt hloglogt_pos)
  linarith

lemma log_le_mul_rpow (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ 12 * x ^ (1 / 12 : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hpowpos : 0 < x ^ (1 / 12 : ℝ) := Real.rpow_pos_of_pos hxpos _
  have hlog : Real.log (x ^ (1 / 12 : ℝ)) ≤ x ^ (1 / 12 : ℝ) := Real.log_le_self hpowpos.le
  rw [Real.log_rpow hxpos] at hlog
  linarith

lemma log_add_one_le_mul_rpow (x : ℝ) (hx : 1 ≤ x) : Real.log x + 1 ≤ 13 * x ^ (1 / 12 : ℝ) := by
  have h1 := log_le_mul_rpow x hx
  have h2 : 1 ≤ x ^ (1 / 12 : ℝ) := by
    nth_rw 1 [← Real.one_rpow (1 / 12 : ℝ)]
    exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  linarith

lemma rpow_add_eval (x : ℝ) (hx : 0 < x) :
    x ^ (2 / 3 : ℝ) * x ^ (1 / 12 : ℝ) = x ^ (3 / 4 : ℝ) := by
  rw [← Real.rpow_add hx]
  congr 1
  norm_num

lemma zeta_bound_one_to_two (A C : ℝ) (hA : 0 < A) (hC : 0 < C)
    (h_pnt : ∀ (σ t : ℝ), 3 < |t| → σ ∈ Set.Icc (1 - A / Real.log |t|) 2 → ‖riemannZeta (σ + t * I)‖ ≤ C * Real.log |t|)
    (σ t : ℝ) (ht : 3 ≤ |t|) (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) :
    ‖riemannZeta (σ + t * I)‖ ≤ max C 14 * Real.log |t| := by
  by_cases hgt : 3 < |t|
  · have h_mem : σ ∈ Set.Icc (1 - A / Real.log |t|) 2 := by
      constructor
      · have : 0 < Real.log |t| := Real.log_pos (by linarith)
        have : 0 < A / Real.log |t| := div_pos hA this
        linarith
      · exact hσ2
    have h := h_pnt σ t hgt h_mem
    have hC_le : C ≤ max C 14 := le_max_left _ _
    have hlog_nonneg : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
    exact le_trans h (mul_le_mul_of_nonneg_right hC_le hlog_nonneg)
  · push Not at hgt
    have ht_eq : |t| = 3 := by linarith
    set z : ℂ := σ + t * I
    have hz_re : z.re ∈ Set.Ico (1 / 2 : ℝ) 3 := by
      simp [z]
      constructor <;> linarith
    have hz_im : (1 : ℝ) ≤ |z.im| := by
      simp [z, ht_eq]
    have hupp := lem_zetaUppBd z hz_re hz_im
    have h14 : (8 : ℝ) + 2 * |z.im| = 14 := by
      simp [z, ht_eq]
      norm_num
    rw [h14] at hupp
    have h_log3 : 1 ≤ Real.log |t| := by
      rw [ht_eq]
      have : Real.exp 1 ≤ (3 : ℝ) := by
        have : Real.exp 1 < 3 := by
          have : (2.7182818286 : ℝ) < 3 := by norm_num
          exact lt_trans Real.exp_one_lt_d9 this
        linarith
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) this
    have h14_le : (14 : ℝ) ≤ max C 14 * Real.log |t| := by
      calc (14 : ℝ) = 14 * 1 := by ring
      _ ≤ max C 14 * 1 := mul_le_mul_of_nonneg_right (le_max_right C 14) (by norm_num)
      _ ≤ max C 14 * Real.log |t| := mul_le_mul_of_nonneg_left h_log3 (by positivity)
    exact le_trans (le_of_lt hupp) h14_le

lemma exists_vk_zero_free :
    ∃ c_vk : ℝ, 0 < c_vk ∧ ∀ (ρ : ℂ), riemannZeta ρ = 0 → 6 ≤ |ρ.im| →
      ρ.re ≤ 1 - c_vk / (Real.log |ρ.im|) ^ (3 / 4 : ℝ) := by
  have h_bilin : BilinearEstimate (1 / 30) := bilinearEstimate (1 / 30) (by norm_num) (by norm_num)
  obtain ⟨c_vk, A_vk, hc_vk, hA_vk, h_zeta_vk⟩ := norm_riemannZeta_le_of_bilinear h_bilin
  obtain ⟨A_pnt, hA_pnt, C_pnt, hC_pnt, h_zeta_pnt⟩ := ZetaUpperBnd
  have hlog3_gt1 : 1 < Real.log 3 := one_lt_log_three'
  have hlog3_pos : 0 < Real.log 3 := by linarith
  have hloglog3_pos : 0 < Real.log (Real.log 3) := Real.log_pos hlog3_gt1
  have hloglog3_rpow_pos : 0 < (Real.log (Real.log 3)) ^ (2 / 3 : ℝ) := by
    have : 0 < Real.log (Real.log 3) := hloglog3_pos
    positivity
  let c_theta : ℝ := min (c_vk * (Real.log (Real.log 3)) ^ (2 / 3 : ℝ) / 2) (1 / 4)
  have hc_theta_pos : 0 < c_theta := by
    apply lt_min
    · have : 0 < c_vk * (Real.log (Real.log 3)) ^ (2 / 3 : ℝ) :=
        mul_pos hc_vk hloglog3_rpow_pos
      linarith
    · norm_num
  have hc_theta_le_quarter : c_theta ≤ 1 / 4 := min_le_right _ _
  let θ : ℝ → ℝ := fun t => c_theta / (Real.log t) ^ (2 / 3 : ℝ)
  let M1 : ℝ := max C_pnt 14
  have hM1_pos : 0 < M1 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 14) (le_max_right C_pnt 14)
  let K0 : ℝ := max A_vk (max 1 (Real.log (3 / c_theta) + 1))
  let K_phi : ℝ := max K0 (|Real.log M1| / Real.log (Real.log 3) + 2)
  have hK_phi_ge1 : 1 ≤ K_phi := by
    have : 1 ≤ K0 := le_trans (le_max_left 1 _) (le_max_right A_vk _)
    exact le_trans this (le_max_left K0 _)
  have hK_phi_nonneg : 0 ≤ K_phi := by linarith
  have hK_phi_ge_log3ct : Real.log (3 / c_theta) ≤ K_phi := by
    have h1 : Real.log (3 / c_theta) ≤ Real.log (3 / c_theta) + 1 := by linarith
    have h2 : Real.log (3 / c_theta) + 1 ≤ max 1 (Real.log (3 / c_theta) + 1) := le_max_right _ _
    have h3 : max 1 (Real.log (3 / c_theta) + 1) ≤ K0 := le_max_right _ _
    have h4 : K0 ≤ K_phi := le_max_left _ _
    linarith
  have hK_phi_ge_Avk : A_vk ≤ K_phi := by
    have h1 : A_vk ≤ K0 := le_max_left _ _
    exact le_trans h1 (le_max_left _ _)
  let φ : ℝ → ℝ := fun t => K_phi * (Real.log (Real.log t) + 1)
  have hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2 := by
    intro t ht
    have hlogt_ge : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    have hlogt_gt1 : 1 < Real.log t := lt_of_lt_of_le hlog3_gt1 hlogt_ge
    have hlogt_pos : 0 < Real.log t := by linarith
    have hrpow_pos : 0 < (Real.log t) ^ (2 / 3 : ℝ) := by positivity
    constructor
    · exact div_pos hc_theta_pos hrpow_pos
    · have hrpow_ge1 : 1 ≤ (Real.log t) ^ (2 / 3 : ℝ) := by
        have : (1 : ℝ) ^ (2 / 3 : ℝ) ≤ (Real.log t) ^ (2 / 3 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) (le_of_lt hlogt_gt1) (by norm_num)
        simpa using this
      have : c_theta / (Real.log t) ^ (2 / 3 : ℝ) ≤ c_theta / 1 :=
        div_le_div_of_nonneg_left (le_of_lt hc_theta_pos) (by norm_num) hrpow_ge1
      simp only [div_one] at this
      linarith [hc_theta_le_quarter]
  have hθanti : AntitoneOn θ (Set.Ici 3) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    have hxpos : 0 < x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
    have hrpow_le : (Real.log x) ^ (2 / 3 : ℝ) ≤ (Real.log y) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (le_of_lt hlogx_pos) hlog_le (by norm_num)
    have hrpow_pos : 0 < (Real.log x) ^ (2 / 3 : ℝ) := by positivity
    exact div_le_div_of_nonneg_left (le_of_lt hc_theta_pos) hrpow_pos hrpow_le
  have hφ : ∀ t, 3 ≤ t → 1 ≤ φ t := by
    intro t ht
    have hlogt_ge : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    have hlogt_gt1 : 1 < Real.log t := lt_of_lt_of_le hlog3_gt1 hlogt_ge
    have hloglogt_pos : 0 < Real.log (Real.log t) := Real.log_pos hlogt_gt1
    have : 1 ≤ Real.log (Real.log t) + 1 := by linarith
    calc 1 = 1 * 1 := by ring
      _ ≤ K_phi * (Real.log (Real.log t) + 1) :=
        mul_le_mul hK_phi_ge1 this (by norm_num) hK_phi_nonneg
  have hφmono : MonotoneOn φ (Set.Ici 3) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    have hxpos : 0 < x := by linarith
    have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
    have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log hxpos hxy
    have hloglog_le : Real.log (Real.log x) ≤ Real.log (Real.log y) :=
      Real.log_le_log hlogx_pos hlog_le
    have : Real.log (Real.log x) + 1 ≤ Real.log (Real.log y) + 1 := by linarith
    exact mul_le_mul_of_nonneg_left this hK_phi_nonneg
  have hφθ : ∀ t, 3 ≤ t → φ (2 * t) ≤ 2 * φ t := by
    intro t ht
    have h := log_log_two_mul_add_one_le t ht
    dsimp [φ]
    calc K_phi * (Real.log (Real.log (2 * t)) + 1)
      ≤ K_phi * (2 * (Real.log (Real.log t) + 1)) :=
        mul_le_mul_of_nonneg_left h hK_phi_nonneg
      _ = 2 * (K_phi * (Real.log (Real.log t) + 1)) := by ring
  have hθdyadic : ∀ t, 3 ≤ t → θ t ≤ 2 * θ (2 * t) := by
    intro t ht
    exact theta_dyadic_le c_theta hc_theta_pos t ht
  have hθφ : ∀ t, 3 ≤ t → Real.log (3 / θ t) ≤ φ t := by
    intro t ht
    exact log_three_div_theta_le c_theta hc_theta_pos K_phi hK_phi_ge_log3ct hK_phi_ge1 t ht
  have hθloc : ∀ t t' : ℝ, 3 ≤ t → |t' - t| ≤ 1 → θ t / 2 ≤ θ t' := by
    intro t t' ht htt'
    exact theta_loc_le c_theta hc_theta_pos t t' ht htt'
  have hφloc : ∀ t t' : ℝ, 3 ≤ t → |t' - t| ≤ 1 → φ t' ≤ 2 * φ t := by
    intro t t' ht htt'
    exact phi_loc_le K_phi hK_phi_nonneg t t' ht htt'
  have hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 →
      ‖riemannZeta (σ + t * Complex.I)‖ ≤ Real.exp (φ |t|) := by
    intro σ t ht hσ_low hσ_high
    by_cases hσ1 : σ ≤ 1
    · have ht_pos : 0 < |t| := by linarith
      have hlogt_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
      have hlogt_rpow_pos : 0 < (Real.log |t|) ^ (2 / 3 : ℝ) := by positivity
      have h_theta_le : θ |t| ≤ c_vk * (Real.log (Real.log |t|)) ^ (2 / 3 : ℝ) / (Real.log |t|) ^ (2 / 3 : ℝ) := by
        dsimp [θ]
        have h_ct_le : c_theta ≤ c_vk * (Real.log (Real.log 3)) ^ (2 / 3 : ℝ) / 2 := min_le_left _ _
        have h_ct_le2 : c_theta ≤ c_vk * (Real.log (Real.log |t|)) ^ (2 / 3 : ℝ) := by
          have hloglog3_le : Real.log (Real.log 3) ≤ Real.log (Real.log |t|) := by
            apply Real.log_le_log hlog3_pos
            exact Real.log_le_log (by norm_num) ht
          have hrpow_le : (Real.log (Real.log 3)) ^ (2 / 3 : ℝ) ≤ (Real.log (Real.log |t|)) ^ (2 / 3 : ℝ) :=
            Real.rpow_le_rpow (le_of_lt hloglog3_pos) hloglog3_le (by norm_num)
          have h_half_le : c_vk * (Real.log (Real.log 3)) ^ (2 / 3 : ℝ) / 2 ≤ c_vk * (Real.log (Real.log 3)) ^ (2 / 3 : ℝ) := by
            have : 0 ≤ c_vk * (Real.log (Real.log 3)) ^ (2 / 3 : ℝ) := by positivity
            linarith
          have h_ct_le' : c_theta ≤ c_vk * (Real.log (Real.log 3)) ^ (2 / 3 : ℝ) := le_trans h_ct_le h_half_le
          have hmul_le : c_vk * (Real.log (Real.log 3)) ^ (2 / 3 : ℝ) ≤ c_vk * (Real.log (Real.log |t|)) ^ (2 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left hrpow_le (le_of_lt hc_vk)
          exact le_trans h_ct_le' hmul_le
        exact div_le_div_of_nonneg_right h_ct_le2 (le_of_lt hlogt_rpow_pos)
      have hσ_vk : 1 - c_vk * (Real.log (Real.log |t|)) ^ (2 / 3 : ℝ) / (Real.log |t|) ^ (2 / 3 : ℝ) ≤ σ := by
        linarith [hσ_low, h_theta_le]
      have h_bound := h_zeta_vk σ t ht hσ_vk hσ1
      have h_rpow_eq : (Real.log |t|) ^ A_vk = Real.exp (A_vk * Real.log (Real.log |t|)) := by
        rw [Real.rpow_def_of_pos hlogt_pos, mul_comm]
      rw [h_rpow_eq] at h_bound
      have h_exp_le : Real.exp (A_vk * Real.log (Real.log |t|)) ≤ Real.exp (φ |t|) := by
        apply Real.exp_le_exp.mpr
        dsimp [φ]
        have hloglogt_nonneg : 0 ≤ Real.log (Real.log |t|) := by
          have : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
          have : 1 ≤ Real.log |t| := le_trans (le_of_lt hlog3_gt1) this
          exact Real.log_nonneg this
        have h1 : A_vk * Real.log (Real.log |t|) ≤ K_phi * Real.log (Real.log |t|) :=
          mul_le_mul_of_nonneg_right hK_phi_ge_Avk hloglogt_nonneg
        have h2 : K_phi * Real.log (Real.log |t|) ≤ K_phi * (Real.log (Real.log |t|) + 1) := by
          have : Real.log (Real.log |t|) ≤ Real.log (Real.log |t|) + 1 := by linarith
          exact mul_le_mul_of_nonneg_left this hK_phi_nonneg
        exact le_trans h1 h2
      exact le_trans h_bound h_exp_le
    · push Not at hσ1
      have hσ_ge1 : 1 ≤ σ := le_of_lt hσ1
      have hA_pos : 0 < A_pnt := hA_pnt.1
      have h_zeta_pnt' : ‖riemannZeta (σ + t * Complex.I)‖ ≤ M1 * Real.log |t| :=
        zeta_bound_one_to_two A_pnt C_pnt hA_pos hC_pnt h_zeta_pnt σ t ht hσ_ge1 hσ_high
      have hlogt_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
      have h_prod_pos : 0 < M1 * Real.log |t| := mul_pos hM1_pos hlogt_pos
      have h_log_prod : Real.log (M1 * Real.log |t|) = Real.log M1 + Real.log (Real.log |t|) :=
        Real.log_mul (ne_of_gt hM1_pos) (ne_of_gt hlogt_pos)
      have h_prod_eq_exp : M1 * Real.log |t| = Real.exp (Real.log (M1 * Real.log |t|)) :=
        (Real.exp_log h_prod_pos).symm
      rw [h_prod_eq_exp] at h_zeta_pnt'
      rw [h_log_prod] at h_zeta_pnt'
      have h_le_phi : Real.log M1 + Real.log (Real.log |t|) ≤ φ |t| := by
        dsimp [φ]
        have hloglog3_le : Real.log (Real.log 3) ≤ Real.log (Real.log |t|) := by
          apply Real.log_le_log hlog3_pos
          exact Real.log_le_log (by norm_num) ht
        have hlogM1_le : Real.log M1 ≤ (|Real.log M1| / Real.log (Real.log 3)) * Real.log (Real.log |t|) := by
          have h1 : Real.log M1 ≤ |Real.log M1| := le_abs_self _
          have h2 : |Real.log M1| = (|Real.log M1| / Real.log (Real.log 3)) * Real.log (Real.log 3) := by
            rw [div_mul_cancel₀ _ (ne_of_gt hloglog3_pos)]
          have h3 : (|Real.log M1| / Real.log (Real.log 3)) * Real.log (Real.log 3) ≤
              (|Real.log M1| / Real.log (Real.log 3)) * Real.log (Real.log |t|) := by
            apply mul_le_mul_of_nonneg_left hloglog3_le
            exact div_nonneg (abs_nonneg _) (le_of_lt hloglog3_pos)
          linarith
        have hsum_le : Real.log M1 + Real.log (Real.log |t|) ≤
            (|Real.log M1| / Real.log (Real.log 3) + 1) * Real.log (Real.log |t|) := by
          calc Real.log M1 + Real.log (Real.log |t|)
            ≤ (|Real.log M1| / Real.log (Real.log 3)) * Real.log (Real.log |t|) + Real.log (Real.log |t|) := by linarith
            _ = (|Real.log M1| / Real.log (Real.log 3) + 1) * Real.log (Real.log |t|) := by ring
        have h_coeff_le : |Real.log M1| / Real.log (Real.log 3) + 1 ≤ K_phi := by
          have : |Real.log M1| / Real.log (Real.log 3) + 1 ≤ |Real.log M1| / Real.log (Real.log 3) + 2 := by linarith
          exact le_trans this (le_max_right K0 _)
        have hloglogt_nonneg : 0 ≤ Real.log (Real.log |t|) := by
          have : 0 < Real.log (Real.log 3) := hloglog3_pos
          linarith
        have hfinal_le : (|Real.log M1| / Real.log (Real.log 3) + 1) * Real.log (Real.log |t|) ≤
            K_phi * (Real.log (Real.log |t|) + 1) := by
          have h1 : (|Real.log M1| / Real.log (Real.log 3) + 1) * Real.log (Real.log |t|) ≤
              K_phi * Real.log (Real.log |t|) :=
            mul_le_mul_of_nonneg_right h_coeff_le hloglogt_nonneg
          have h2 : K_phi * Real.log (Real.log |t|) ≤ K_phi * (Real.log (Real.log |t|) + 1) := by
            have : Real.log (Real.log |t|) ≤ Real.log (Real.log |t|) + 1 := by linarith
            exact mul_le_mul_of_nonneg_left this hK_phi_nonneg
          exact le_trans h1 h2
        exact le_trans hsum_le hfinal_le
      exact le_trans h_zeta_pnt' (Real.exp_le_exp.mpr h_le_phi)
  obtain ⟨A_zfg, hA_zfg_pos, h_zf⟩ :=
    zero_free_of_zeta_bound' θ φ hθ hθanti hφ hφmono hφθ hθdyadic hθφ hθloc hφloc hζ
  let c_res : ℝ := A_zfg * c_theta / (13 * K_phi)
  have hc_res_pos : 0 < c_res := by
    dsimp [c_res]
    positivity
  refine ⟨c_res, hc_res_pos, ?_⟩
  intro ρ hzero hρim
  have hbound := h_zf ρ hzero hρim
  have hu_ge3 : 3 ≤ |ρ.im| := by linarith
  have hlogu_ge : Real.log 3 ≤ Real.log |ρ.im| := Real.log_le_log (by norm_num) hu_ge3
  have hlogu_ge1 : 1 ≤ Real.log |ρ.im| := le_trans (le_of_lt hlog3_gt1) hlogu_ge
  have hlogu_pos : 0 < Real.log |ρ.im| := by linarith
  have h13 := log_add_one_le_mul_rpow (Real.log |ρ.im|) hlogu_ge1
  have hrpow_add := rpow_add_eval (Real.log |ρ.im|) hlogu_pos
  have hden_le : (Real.log |ρ.im|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |ρ.im|) + 1) ≤
      13 * (Real.log |ρ.im|) ^ (3 / 4 : ℝ) := by
    have hrpow23_nonneg : 0 ≤ (Real.log |ρ.im|) ^ (2 / 3 : ℝ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left h13 hrpow23_nonneg
    calc (Real.log |ρ.im|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |ρ.im|) + 1)
      ≤ (Real.log |ρ.im|) ^ (2 / 3 : ℝ) * (13 * (Real.log |ρ.im|) ^ (1 / 12 : ℝ)) := h1
      _ = 13 * ((Real.log |ρ.im|) ^ (2 / 3 : ℝ) * (Real.log |ρ.im|) ^ (1 / 12 : ℝ)) := by ring
      _ = 13 * (Real.log |ρ.im|) ^ (3 / 4 : ℝ) := by rw [hrpow_add]
  have hden_pos : 0 < (Real.log |ρ.im|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |ρ.im|) + 1) := by
    have h1 : 0 < (Real.log |ρ.im|) ^ (2 / 3 : ℝ) := by positivity
    have h2 : 0 < Real.log (Real.log |ρ.im|) + 1 := by
      have : 0 < Real.log (Real.log 3) := hloglog3_pos
      have : Real.log (Real.log 3) ≤ Real.log (Real.log |ρ.im|) :=
        Real.log_le_log hlog3_pos hlogu_ge
      linarith
    exact mul_pos h1 h2
  have hden_pos2 : 0 < 13 * (Real.log |ρ.im|) ^ (3 / 4 : ℝ) := by positivity
  have hfrac_le : 1 / (13 * (Real.log |ρ.im|) ^ (3 / 4 : ℝ)) ≤
      1 / ((Real.log |ρ.im|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |ρ.im|) + 1)) :=
    one_div_le_one_div_of_le hden_pos hden_le
  have h_theta_div_phi : A_zfg * θ |ρ.im| / φ |ρ.im| =
      (A_zfg * c_theta / K_phi) * (1 / ((Real.log |ρ.im|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |ρ.im|) + 1))) := by
    dsimp [θ, φ]
    have hKne : K_phi ≠ 0 := ne_of_gt (by linarith)
    have hrpow_ne : (Real.log |ρ.im|) ^ (2 / 3 : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hloglog_ne : Real.log (Real.log |ρ.im|) + 1 ≠ 0 := by
      have : 0 < Real.log (Real.log 3) := hloglog3_pos
      have : Real.log (Real.log 3) ≤ Real.log (Real.log |ρ.im|) :=
        Real.log_le_log hlog3_pos hlogu_ge
      linarith
    field_simp
  rw [h_theta_div_phi] at hbound
  have h_lower : c_res / (Real.log |ρ.im|) ^ (3 / 4 : ℝ) ≤
      (A_zfg * c_theta / K_phi) * (1 / ((Real.log |ρ.im|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |ρ.im|) + 1))) := by
    have h_alg : c_res / (Real.log |ρ.im|) ^ (3 / 4 : ℝ) =
        (A_zfg * c_theta / K_phi) * (1 / (13 * (Real.log |ρ.im|) ^ (3 / 4 : ℝ))) := by
      dsimp [c_res]
      ring
    rw [h_alg]
    have h_coeff_nonneg : 0 ≤ A_zfg * c_theta / K_phi := by
      apply div_nonneg
      · exact mul_nonneg (le_of_lt hA_zfg_pos) (le_of_lt hc_theta_pos)
      · linarith
    exact mul_le_mul_of_nonneg_left hfrac_le h_coeff_nonneg
  linarith [hbound, h_lower]

lemma rpow_three_quarters_le_two_mul (t t' : ℝ) (ht : 3 ≤ t) (ht' : 6 ≤ t') (htt' : t' ≤ 2 * t) :
    (Real.log t') ^ (3 / 4 : ℝ) ≤ 2 * (Real.log t) ^ (3 / 4 : ℝ) := by
  have htpos : 0 < t := by linarith
  have ht'pos : 0 < t' := by linarith
  have hlogt_pos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogt'_pos : 0 < Real.log t' := Real.log_pos (by linarith)
  have hlogt'_le : Real.log t' ≤ 2 * Real.log t := by
    have h1 : Real.log t' ≤ Real.log (2 * t) := Real.log_le_log ht'pos htt'
    have h2 := log_two_mul_le t ht
    exact le_trans h1 h2
  have h_rpow : (Real.log t') ^ (3 / 4 : ℝ) ≤ (2 * Real.log t) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (le_of_lt hlogt'_pos) hlogt'_le (by norm_num)
  have h2_rpow : (2 * Real.log t) ^ (3 / 4 : ℝ) = (2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log t) ^ (3 / 4 : ℝ) :=
    Real.mul_rpow (by norm_num) (le_of_lt hlogt_pos)
  have h3 : (2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log t) ^ (3 / 4 : ℝ) ≤ 2 * (Real.log t) ^ (3 / 4 : ℝ) :=
    mul_le_mul_of_nonneg_right two_rpow_three_quarters_le_two (by positivity)
  calc (Real.log t') ^ (3 / 4 : ℝ)
    ≤ (2 * Real.log t) ^ (3 / 4 : ℝ) := h_rpow
    _ = (2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log t) ^ (3 / 4 : ℝ) := h2_rpow
    _ ≤ 2 * (Real.log t) ^ (3 / 4 : ℝ) := h3

lemma div_rpow_three_quarters_ge (c_vk c0 : ℝ) (hc_vk : 0 < c_vk) (hc0 : c0 ≤ c_vk / 4)
    (t t' : ℝ) (ht : 3 ≤ t) (ht' : 6 ≤ t') (htt' : t' ≤ 2 * t) :
    2 * c0 / (Real.log t) ^ (3 / 4 : ℝ) ≤ c_vk / (Real.log t') ^ (3 / 4 : ℝ) := by
  have hden_le := rpow_three_quarters_le_two_mul t t' ht ht' htt'
  have htpos : 0 < t := by linarith
  have ht'pos : 0 < t' := by linarith
  have hlogt_pos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogt'_pos : 0 < Real.log t' := Real.log_pos (by linarith)
  have hden_pos1 : 0 < (Real.log t') ^ (3 / 4 : ℝ) := by positivity
  have hden_pos2 : 0 < 2 * (Real.log t) ^ (3 / 4 : ℝ) := by positivity
  have h_recip : 1 / (2 * (Real.log t) ^ (3 / 4 : ℝ)) ≤ 1 / (Real.log t') ^ (3 / 4 : ℝ) :=
    one_div_le_one_div_of_le hden_pos1 hden_le
  have h1 : c_vk * (1 / (2 * (Real.log t) ^ (3 / 4 : ℝ))) ≤ c_vk * (1 / (Real.log t') ^ (3 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_left h_recip (le_of_lt hc_vk)
  have h_alg1 : c_vk * (1 / (Real.log t') ^ (3 / 4 : ℝ)) = c_vk / (Real.log t') ^ (3 / 4 : ℝ) := by ring
  have h_alg2 : (c_vk / 2) / (Real.log t) ^ (3 / 4 : ℝ) = c_vk * (1 / (2 * (Real.log t) ^ (3 / 4 : ℝ))) := by ring
  rw [h_alg1] at h1
  rw [← h_alg2] at h1
  have h2 : 2 * c0 ≤ c_vk / 2 := by linarith
  have hden_pos3 : 0 < (Real.log t) ^ (3 / 4 : ℝ) := by positivity
  have h3 : 2 * c0 / (Real.log t) ^ (3 / 4 : ℝ) ≤ (c_vk / 2) / (Real.log t) ^ (3 / 4 : ℝ) :=
    div_le_div_of_nonneg_right h2 (le_of_lt hden_pos3)
  exact le_trans h3 h1

lemma rho_re_lt_of_im_lt_six (M_bg : ℕ) (hM : 2 ≤ M_bg)
    (hMbound_bg : ∀ (rho : ℂ), riemannZeta rho = 0 → rho.re < 1 - 1 / ((M_bg : ℝ) ^ 2 * Real.log (|rho.im| + 2)))
    (ρ : ℂ) (hzero : riemannZeta ρ = 0) (h6 : |ρ.im| < 6) :
    ρ.re < 1 - 1 / ((M_bg : ℝ) ^ 2 * Real.log 8) := by
  have h_m := hMbound_bg ρ hzero
  have him2_pos : 0 < |ρ.im| + 2 := by positivity
  have him2_lt8 : |ρ.im| + 2 < 8 := by linarith
  have hlog_lt : Real.log (|ρ.im| + 2) ≤ Real.log 8 :=
    Real.log_le_log him2_pos (le_of_lt him2_lt8)
  have hM_pos : 0 < (M_bg : ℝ) := by positivity
  have hM2_pos : 0 < (M_bg : ℝ) ^ 2 := by positivity
  have hden_le : (M_bg : ℝ) ^ 2 * Real.log (|ρ.im| + 2) ≤ (M_bg : ℝ) ^ 2 * Real.log 8 :=
    mul_le_mul_of_nonneg_left hlog_lt (le_of_lt hM2_pos)
  have hden1_pos : 0 < (M_bg : ℝ) ^ 2 * Real.log (|ρ.im| + 2) := by
    have : 1 < |ρ.im| + 2 := by linarith [abs_nonneg ρ.im]
    have : 0 < Real.log (|ρ.im| + 2) := Real.log_pos this
    positivity
  have hfrac_le : 1 / ((M_bg : ℝ) ^ 2 * Real.log 8) ≤ 1 / ((M_bg : ℝ) ^ 2 * Real.log (|ρ.im| + 2)) :=
    one_div_le_one_div_of_le hden1_pos hden_le
  linarith

lemma div_rpow_three_quarters_le_delta_M (delta_M c0 : ℝ) (hdelta : 0 ≤ delta_M)
    (hc0 : c0 ≤ delta_M * (Real.log 3) ^ (3 / 4 : ℝ) / 2) (t : ℝ) (ht : 3 ≤ t) :
    2 * c0 / (Real.log t) ^ (3 / 4 : ℝ) ≤ delta_M := by
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3_le : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hrpow_le : (Real.log 3) ^ (3 / 4 : ℝ) ≤ (Real.log t) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (le_of_lt hlog3_pos) hlog3_le (by norm_num)
  have hrpow3_pos : 0 < (Real.log 3) ^ (3 / 4 : ℝ) := by positivity
  have hlogt_pos : 0 < Real.log t := Real.log_pos (by linarith)
  have hrpowt_pos : 0 < (Real.log t) ^ (3 / 4 : ℝ) := by positivity
  have h1 : 2 * c0 ≤ delta_M * (Real.log 3) ^ (3 / 4 : ℝ) := by linarith
  have h2 : 2 * c0 / (Real.log t) ^ (3 / 4 : ℝ) ≤ (delta_M * (Real.log 3) ^ (3 / 4 : ℝ)) / (Real.log t) ^ (3 / 4 : ℝ) :=
    div_le_div_of_nonneg_right h1 (le_of_lt hrpowt_pos)
  have h_frac : (delta_M * (Real.log 3) ^ (3 / 4 : ℝ)) / (Real.log t) ^ (3 / 4 : ℝ) =
      delta_M * ((Real.log 3) ^ (3 / 4 : ℝ) / (Real.log t) ^ (3 / 4 : ℝ)) := by ring
  rw [h_frac] at h2
  have h_ratio_le : (Real.log 3) ^ (3 / 4 : ℝ) / (Real.log t) ^ (3 / 4 : ℝ) ≤ 1 :=
    (div_le_one₀ hrpowt_pos).mpr hrpow_le
  have h_mul_le : delta_M * ((Real.log 3) ^ (3 / 4 : ℝ) / (Real.log t) ^ (3 / 4 : ℝ)) ≤ delta_M * 1 :=
    mul_le_mul_of_nonneg_left h_ratio_le hdelta
  rw [mul_one] at h_mul_le
  exact le_trans h2 h_mul_le

lemma log_rpow_seven_quarters_le_pow_two (t : ℝ) (ht : 3 ≤ |t|) :
    (Real.log |t|) ^ (7 / 4 : ℝ) ≤ (Real.log |t|) ^ 2 := by
  have hlogt_ge1 : 1 ≤ Real.log |t| := by
    have : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
    have : 1 < Real.log 3 := one_lt_log_three'
    linarith
  have h_rpow : (Real.log |t|) ^ (7 / 4 : ℝ) ≤ (Real.log |t|) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlogt_ge1 (by norm_num)
  have h_two : (Real.log |t|) ^ (2 : ℝ) = (Real.log |t|) ^ 2 :=
    Real.rpow_two (Real.log |t|)
  rwa [h_two] at h_rpow

lemma log_le_pow_two (t : ℝ) (ht : 3 ≤ |t|) :
    Real.log |t| ≤ (Real.log |t|) ^ 2 := by
  have hlogt_ge1 : 1 ≤ Real.log |t| := by
    have : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
    have : 1 < Real.log 3 := one_lt_log_three'
    linarith
  nlinarith

lemma norm_sum_m_div_le (s : Finset ℂ) (z : ℂ) :
    ‖∑ ρ ∈ s, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
    ∑ ρ ∈ s, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖ := by
  apply le_trans (norm_sum_le _ _)
  apply Finset.sum_le_sum
  intro ρ _
  rw [norm_div, Complex.norm_natCast]

lemma zerosetKfRc_finite (c : ℂ) (R : ℝ) : (zerosetKfRc R c riemannZeta).Finite := by
  have hK : IsCompact (Metric.closedBall c R) := ProperSpace.isCompact_closedBall c R
  simpa [zerosetKfRc] using (riemannZeta_zeros_finite_of_compact (Metric.closedBall c R) hK)

lemma sum_m_rho_zeta_ge3 :
    ∃ C_2 > 1, ∀ (t : ℝ) (ht : 3 ≤ |t|),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ C_2 * Real.log |t| := by
  classical
  obtain ⟨b, hb_gt1, hb_bound⟩ := zeta32upper
  obtain ⟨a, ha_pos, ha_bound⟩ := zeta_low_332
  let R1 : ℝ := 5 / 6
  let R : ℝ := 8 / 9
  let logRatio : ℝ := Real.log (R / R1)
  let u : ℝ := Real.log (b / a)
  let C2 : ℝ := max 2 ((1 + |u|) / logRatio)
  have hC2_gt_one : 1 < C2 := by
    have htwo_lt : (1 : ℝ) < 2 := by norm_num
    have hle : (2 : ℝ) ≤ C2 := le_max_left (2 : ℝ) ((1 + |u|) / logRatio)
    exact lt_of_lt_of_le htwo_lt hle
  refine ⟨C2, hC2_gt_one, ?_⟩
  intro t ht c hfin
  have hR1_pos : 0 < R1 := by dsimp [R1]; norm_num
  have hR1_lt_R : R1 < R := by dsimp [R1, R]; norm_num
  have hR_lt_1 : R < 1 := by dsimp [R]; norm_num
  have hR_le_one : R ≤ (1 : ℝ) := by dsimp [R]; norm_num
  have ht1 : |t| > 1 := by linarith
  have h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ riemannZeta z := by
    intro z hz
    have hz_ne_one : z ≠ (1 : ℂ) := (D1cinTt_pre t ht1) z (by simpa [c] using hz)
    have hz_mem : z ∈ ({1} : Set ℂ)ᶜ := by simpa using hz_ne_one
    exact analyticOn_riemannZeta z hz_mem
  have h_nonzero : riemannZeta c ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    norm_num [c, Complex.add_re, Complex.I_mul_re]
  have ht2 : |t| > 2 := by linarith
  have h_upper_on_ball1 : ∀ z ∈ Metric.closedBall c 1, ‖riemannZeta z‖ < b * |t| := by
    have h := hb_bound t ht2
    intro z hz; simpa [c] using h z (by simpa [c] using hz)
  have hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖riemannZeta z‖ ≤ b * |t| := by
    intro z hz
    have hz1 : z ∈ Metric.closedBall c 1 :=
      (Metric.closedBall_subset_closedBall hR_le_one) hz
    exact le_of_lt (h_upper_on_ball1 z hz1)
  have hb_pos : 0 < b := lt_trans (by norm_num) hb_gt1
  have htabove1 : (1 : ℝ) ≤ |t| := by linarith
  have hb_le_B : b ≤ b * |t| := by
    have := mul_le_mul_of_nonneg_left htabove1 (le_of_lt hb_pos)
    simpa [one_mul] using this
  have hBpos : 1 < b * |t| := lt_of_lt_of_le hb_gt1 hb_le_B
  have h_sum_bound :=
    lem_sum_m_rho_bound_c (B := b * |t|) (R := R) (R1 := R1)
      (hB := hBpos)
      (hR1_pos := hR1_pos)
      (hR1_lt_R := hR1_lt_R)
      (hR_lt_1 := hR_lt_1)
      (f := riemannZeta) (c := c)
      (h_f_analytic := h_f_analytic)
      (h_f_nonzero_at_zero := h_nonzero)
      (hf_le_B := hf_le_B)
      (hfin := hfin)
  have hlogRatio_pos : 0 < logRatio := by
    have : 1 < R / R1 := by dsimp [R, R1]; norm_num
    exact Real.log_pos this
  have h_zeta_ge_a : a ≤ ‖riemannZeta c‖ := by
    simpa [c, mul_comm] using ha_bound t
  have ht_abs_pos : 0 < |t| := by linarith
  have hζ_norm_pos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr h_nonzero
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have ht_abs_ne : (|t| : ℝ) ≠ 0 := ne_of_gt ht_abs_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hlog_split1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        = (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖ := by
    have : Real.log (b * |t|) = Real.log b + Real.log |t| :=
      Real.log_mul hb_ne ht_abs_ne
    have :
        Real.log ((b * |t|) / ‖riemannZeta c‖)
          = Real.log (b * |t|) - Real.log ‖riemannZeta c‖ :=
      Real.log_div (by exact mul_ne_zero hb_ne ht_abs_ne) (ne_of_gt hζ_norm_pos)
    simp [this, Real.log_mul hb_ne ht_abs_ne]
  have hlog_div_eq : Real.log (b / a) = Real.log b - Real.log a :=
    Real.log_div hb_ne ha_ne
  have hlog_a_le : Real.log a ≤ Real.log ‖riemannZeta c‖ :=
    Real.log_le_log (by exact ha_pos) (by exact h_zeta_ge_a)
  have hneg : -(Real.log ‖riemannZeta c‖) ≤ -Real.log a := by
    simpa using (neg_le_neg hlog_a_le)
  have hRHS_le_const :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        ≤ Real.log |t| + Real.log (b / a) := by
    have :
        (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖
          ≤ (Real.log b + Real.log |t|) - Real.log a := by
      linarith [hneg]
    simpa [hlog_split1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hlog_div_eq]
      using this
  have hRHS1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖) / logRatio
        ≤ (Real.log |t| + Real.log (b / a)) / logRatio := by
    exact div_le_div_of_nonneg_right hRHS_le_const (le_of_lt hlogRatio_pos)
  have hlogt_ge_one : (1 : ℝ) ≤ Real.log |t| := by
    have h3le : (3 : ℝ) ≤ |t| := ht
    have hlog3_le : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) h3le
    have h_exp_le : Real.exp (1 : ℝ) ≤ 3 := le_of_lt lem_three_gt_e
    have hlog3_ge_one : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : 0 < (3 : ℝ))).mpr h_exp_le
    exact le_trans hlog3_ge_one hlog3_le
  have hadd_le : Real.log |t| + Real.log (b / a) ≤ (1 + |u|) * Real.log |t| := by
    have haux1 : Real.log (b / a) ≤ |u| := by simpa [u] using le_abs_self (Real.log (b / a))
    have haux2 : |u| ≤ |u| * Real.log |t| := by
      have hnonneg : 0 ≤ |u| := abs_nonneg _
      have h1le : (1 : ℝ) ≤ Real.log |t| := hlogt_ge_one
      simpa [one_mul] using (mul_le_mul_of_nonneg_left h1le hnonneg)
    calc
      Real.log |t| + Real.log (b / a)
          ≤ Real.log |t| + |u| := by linarith [haux1]
      _ ≤ Real.log |t| + (|u| * Real.log |t|) := by linarith [haux2]
      _ = (1 + |u|) * Real.log |t| := by ring
  have hRHS2 :
      (Real.log |t| + Real.log (b / a)) / logRatio
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := div_le_div_of_nonneg_right hadd_le (le_of_lt hlogRatio_pos)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hfinal :
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ))
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := le_trans h_sum_bound hRHS1
    exact le_trans this hRHS2
  have hC2_ge : ((1 + |u|) / logRatio) ≤ C2 := by
    have := le_max_right (2 : ℝ) ((1 + |u|) / logRatio)
    simp [C2]
  have hlogt_nonneg : 0 ≤ Real.log |t| := le_trans (by norm_num) hlogt_ge_one
  have hscale := mul_le_mul_of_nonneg_right hC2_ge hlogt_nonneg
  exact le_trans hfinal hscale

lemma Zeta1_Zeta_Expansion_ge3
    (r1 r : ℝ)
    (hr1_pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < 5 / (6 : ℝ)) :
    ∃ C > 1,
    ∀ (t : ℝ) (ht : 3 ≤ |t|),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z ∈ closedBall c r1 \ zerosetKfRc (5 / (6 : ℝ)) c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
      C * (1 / (r - r1)^3 + 1) * Real.log |t| := by
  obtain ⟨A, hAgt1, b, hbgt1, hmain⟩ := Zeta1_Zeta_Expand
  let R1 : ℝ := 5 / 6
  let R  : ℝ := 8 / 9
  have hR1_pos : 0 < R1 := by norm_num [R1]
  have hR1_lt_R : R1 < R := by norm_num [R1, R]
  have hR_lt_1  : R < 1 := by norm_num [R]
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
  let d : ℝ := (r - r1) ^ 3
  have hd_pos : 0 < d := by
    have : 0 < r - r1 := sub_pos.mpr hr1_lt_r
    simpa [d] using pow_pos this 3
  let A0 : ℝ := 1 / ((R^2 / R1 - R1) * Real.log (R / R1))
  have hA0_pos : 0 < A0 := by
    have hx1 : 0 < R^2 / R1 - R1 := by
      norm_num [R, R1]
    have hx2 : 0 < Real.log (R / R1) := by
      have : (1 : ℝ) < R / R1 := by norm_num [R, R1]
      exact Real.log_pos this
    have hxden : 0 < (R^2 / R1 - R1) * Real.log (R / R1) := mul_pos hx1 hx2
    simpa [A0] using (one_div_pos.mpr hxden)
  let K : ℝ := 16 * r^2 / d + A0
  let S : ℝ := Real.log b + A
  have hS_pos : 0 < S := by
    have hbpos : 0 < Real.log b := Real.log_pos hbgt1
    have hApos : 0 < A := lt_trans (by norm_num) hAgt1
    exact add_pos hbpos hApos
  let Kcoeff : ℝ := max (16 * r^2) A0
  have hK_le : K ≤ Kcoeff * (1 / d + 1) := by
    have hx_nonneg : 0 ≤ 1 / d := by
      exact le_of_lt (one_div_pos.mpr hd_pos)
    have hα_le : 16 * r^2 / d ≤ Kcoeff * (1 / d) := by
        have hα : 16 * r^2 ≤ Kcoeff := le_max_left _ _
        have : (16 * r^2) * (1 / d) ≤ Kcoeff * (1 / d) :=
          mul_le_mul_of_nonneg_right hα hx_nonneg
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    have hβ_le : A0 ≤ Kcoeff * 1 := by
      have hβ : A0 ≤ Kcoeff := le_max_right _ _
      simpa using hβ
    have : 16 * r^2 / d + A0 ≤ Kcoeff * (1 / d) + Kcoeff * 1 :=
      add_le_add hα_le hβ_le
    simpa [K, mul_add, mul_one, add_comm, add_left_comm, add_assoc] using this
  let C : ℝ := max (Kcoeff * (1 + S / Real.log 3)) 2
  have hC_gt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hC_gt1, ?_⟩
  intro t ht
  simp only
  intro hfin z hz
  have ht2 : |t| > 2 := by linarith [ht]
  have hineq0 :=
    hmain t ht2 r1 r R1 R hr1_pos hr1_lt_r (lt_trans hr1_pos hr1_lt_r) hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1
  have hineq1 := hineq0 hfin z hz
  have hK_eq : (16 * r^2 / (r - r1)^3 + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) = K := by
    simp [K, A0, d, R1, R]
  have hLS_eq : Real.log |t| + Real.log b + A = Real.log |t| + S := by
    simp [S, add_comm, add_left_comm, add_assoc]
  have hineq2 : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
        ≤ K * (Real.log |t| + S) := by
    rw [← hK_eq, ← hLS_eq]
    exact hineq1
  have hlog3pos : 0 < Real.log (3 : ℝ) := by
    have : (1 : ℝ) < 3 := by norm_num
    exact Real.log_pos this
  have hpos_t : 0 < |t| := by linarith
  have hL_ge_log3' : Real.log 3 ≤ Real.log |t| := by
    exact Real.log_le_log (by norm_num) ht
  have hratio_nonneg : 0 ≤ S / Real.log 3 := le_of_lt (div_pos hS_pos hlog3pos)
  have hneq : Real.log 3 ≠ 0 := ne_of_gt hlog3pos
  have hS_le : S ≤ (S / Real.log 3) * Real.log |t| := by
    calc S
      = (S / Real.log 3) * Real.log 3 := by simp [hneq]
      _ ≤ (S / Real.log 3) * Real.log |t| := mul_le_mul_of_nonneg_left hL_ge_log3' hratio_nonneg
  have hsum_bound : Real.log |t| + S ≤ (1 + S / Real.log 3) * Real.log |t| := by
    have h_factor : Real.log |t| + (S / Real.log 3) * Real.log |t| = (1 + S / Real.log 3) * Real.log |t| := by ring
    linarith [hS_le, h_factor]
  have hineq3 : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
        ≤ K * ((1 + S / Real.log 3) * Real.log |t|) :=
    le_trans hineq2 (mul_le_mul_of_nonneg_left hsum_bound (by
      have hr2_nonneg : 0 ≤ r^2 := by
        have : 0 ≤ r * r := mul_nonneg (le_of_lt hr_pos) (le_of_lt hr_pos)
        simpa [pow_two] using this
      have hterm1 : 0 ≤ 16 * r^2 / d :=
        div_nonneg (mul_nonneg (by norm_num) hr2_nonneg) (le_of_lt hd_pos)
      have : 0 ≤ K := add_nonneg hterm1 (le_of_lt hA0_pos)
      exact this))
  have hKcoeff : K * ((1 + S / Real.log 3) * Real.log |t|)
      ≤ (Kcoeff * (1 / d + 1)) * ((1 + S / Real.log 3) * Real.log |t|) :=
    mul_le_mul_of_nonneg_right hK_le (by
      have hLpos : 0 < Real.log |t| :=
        Real.log_pos (by linarith)
      have hcoef_pos : 0 < 1 + S / Real.log 3 :=
        add_pos_of_pos_of_nonneg (by norm_num) (le_of_lt (div_pos hS_pos hlog3pos))
      have : 0 ≤ (1 + S / Real.log 3) * Real.log |t| :=
        le_of_lt (mul_pos hcoef_pos hLpos)
      simpa using this)
  have hfinal := le_trans hineq3 hKcoeff
  calc ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
    ≤ (Kcoeff * (1 / d + 1)) * ((1 + S / Real.log 3) * Real.log |t|) := hfinal
    _ = (Kcoeff * (1 + S / Real.log 3)) * (1 / d + 1) * Real.log |t| := by ring
    _ ≤ C * (1 / d + 1) * Real.log |t| := by
      have hC_ge : (Kcoeff * (1 + S / Real.log 3)) ≤ C := le_max_left _ _
      have hd_term_nonneg : 0 ≤ 1 / d + 1 := by
        have : 0 ≤ 1 / d := le_of_lt (one_div_pos.mpr hd_pos)
        linarith
      have hlogt_nonneg : 0 ≤ Real.log |t| := by
        have : (1 : ℝ) ≤ |t| := by linarith
        exact Real.log_nonneg this
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC_ge hd_term_nonneg) hlogt_nonneg
    _ = C * (1 / (r - r1)^3 + 1) * Real.log |t| := by simp [d]

lemma logDeriv_ge_32 (t σ : ℝ) (hσ : 3 / 2 ≤ σ) (C0 : ℝ)
    (hC0_bound : ∀ (δ : ℝ) (_ : 0 < δ), ‖-logDerivZeta ((1 : ℂ) + δ) - 1 / (δ : ℂ)‖ ≤ C0) :
    ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C0 + 2 := by
  have h_eq : (σ + t * I : ℂ) = Complex.mk σ t := by
    rw [Complex.mk_eq_add_mul_I]
  rw [h_eq]
  have h_center := lem_zetacenterbd t σ hσ
  set δ : ℝ := σ - 1
  have hδ_pos : 0 < δ := by linarith
  have hδ_ge_half : (1 / 2 : ℝ) ≤ δ := by linarith
  have hZ0 := hC0_bound δ hδ_pos
  have h_tri : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤
      ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ + ‖(1 / (δ : ℂ))‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (norm_add_le (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) (1 / (δ : ℂ)))
  have h_norm_div_le_two : ‖(1 / (δ : ℂ))‖ ≤ 2 := by
    have hnorm_div : ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by simp
    have hnorm_ofReal : ‖(δ : ℂ)‖ = |δ| := by simp
    have h_abs_ge : (1 / 2 : ℝ) ≤ |δ| := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [abs_of_nonneg hδ_nonneg] using hδ_ge_half
    have hhalfpos : (0 : ℝ) < 1 / 2 := by norm_num
    have hone_div_abs_le_two : 1 / |δ| ≤ 2 := by
      simpa using (one_div_le_one_div_of_le hhalfpos h_abs_ge)
    have : 1 / ‖(δ : ℂ)‖ ≤ 2 := by simpa [hnorm_ofReal] using hone_div_abs_le_two
    have hnorm_div' : ‖(1 / (δ : ℂ))‖ = 1 / ‖(δ : ℂ)‖ := by simp [norm_one]
    simpa [hnorm_div'] using this
  have h_real_axis_bound : ‖logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 := by
    have h1 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + ‖(1 / (δ : ℂ))‖ := by
      linarith [h_tri, hZ0]
    have h2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 := by
      linarith [h1, h_norm_div_le_two]
    simpa [norm_neg] using h2
  have hσ_real : (1 : ℝ) + δ = σ := by
    simp [δ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hσ_eq : (1 : ℂ) + δ = (σ : ℂ) := by
    have : ((1 + δ : ℝ) : ℂ) = (σ : ℂ) := by simpa using congrArg Complex.ofReal hσ_real
    simpa [Complex.ofReal_add] using this
  have hR_bound : ‖deriv riemannZeta σ / riemannZeta σ‖ ≤ C0 + 2 := by
    simpa [logDerivZeta, hσ_eq] using h_real_axis_bound
  exact le_trans h_center hR_bound

lemma rho_im_bound (t : ℝ) (ht : 3 ≤ |t|) (c : ℂ) (hc : c = (3 / 2 : ℂ) + I * t)
    (ρ : ℂ) (hρ : ρ ∈ Metric.closedBall c (5 / 6)) :
    |ρ.im| ≤ 2 * |t| := by
  have hnorm : ‖ρ - c‖ ≤ 5 / 6 := by simpa [dist_eq_norm] using Metric.mem_closedBall.mp hρ
  have him_le : |(ρ - c).im| ≤ ‖ρ - c‖ := Complex.abs_im_le_norm (ρ - c)
  have hc_im : c.im = t := by
    rw [hc]
    simp
  have hdiff_im : (ρ - c).im = ρ.im - t := by simp [hc_im]
  rw [hdiff_im] at him_le
  have h_sub_le : |ρ.im - t| ≤ 5 / 6 := le_trans him_le hnorm
  have h_tri : |ρ.im| - |t| ≤ |ρ.im - t| := abs_sub_abs_le_abs_sub ρ.im t
  have h_le : |ρ.im| ≤ |t| + 5 / 6 := by linarith [h_tri, h_sub_le]
  have h_one_le : (5 / 6 : ℝ) ≤ |t| := by linarith
  linarith

lemma z_mem_closedBall_two_thirds (t σ c0 : ℝ) (ht : 3 ≤ |t|) (hc0 : c0 ≤ 1 / 6) (hc0_pos : 0 < c0)
    (hσ_low : 1 - c0 / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ) (hσ_high : σ ≤ 3 / 2)
    (c : ℂ) (hc : c = (3 / 2 : ℂ) + Complex.I * t) (z : ℂ) (hz : z = σ + t * Complex.I) :
    z ∈ Metric.closedBall c (2 / 3) := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hz_sub_c : z - c = ((σ - 3 / 2 : ℝ) : ℂ) := by
    rw [hz, hc]
    push_cast
    ring
  rw [hz_sub_c]
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h_diff_nonpos : σ - 3 / 2 ≤ 0 := by linarith
  have h_abs_eq : |σ - 3 / 2| = 3 / 2 - σ := by
    rw [abs_of_nonpos h_diff_nonpos]
    ring
  rw [h_abs_eq]
  have hlogt_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hrpow_ge1 : 1 ≤ (Real.log |t|) ^ (3 / 4 : ℝ) := by
    have h1 : 1 ≤ Real.log |t| := by
      have : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
      have : 1 < Real.log 3 := one_lt_log_three'
      linarith
    nth_rw 1 [← Real.one_rpow (3 / 4 : ℝ)]
    exact Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  have hrpow_pos : 0 < (Real.log |t|) ^ (3 / 4 : ℝ) := by positivity
  have h_c0_div_le : c0 / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ c0 := by
    have : c0 / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ c0 / 1 :=
      div_le_div_of_nonneg_left (le_of_lt hc0_pos) (by norm_num) hrpow_ge1
    simpa using this
  have h_sigma_bound : 3 / 2 - σ ≤ 1 / 2 + c0 / (Real.log |t|) ^ (3 / 4 : ℝ) := by linarith
  linarith

theorem vk_logDeriv_region :
    ∃ c₀ K : ℝ, 0 < c₀ ∧ 1 ≤ K ∧
      (∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2) ∧
      (∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) := by
  obtain ⟨c_vk, hc_vk_pos, h_vk_zf⟩ := exists_vk_zero_free
  obtain ⟨M_bg, hM2_bg, hMbound_bg⟩ := BoundedGaps.Maynard.exists_nat_riemannZeta_zero_re_lt
  have hM_pos : 0 < (M_bg : ℝ) := by positivity
  have hlog8_pos : 0 < Real.log 8 := Real.log_pos (by norm_num)
  let delta_M : ℝ := 1 / ((M_bg : ℝ) ^ 2 * Real.log 8)
  have hdelta_M_pos : 0 < delta_M := by
    dsimp [delta_M]
    positivity
  have hdelta_M_nonneg : 0 ≤ delta_M := le_of_lt hdelta_M_pos
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hrpow3_pos : 0 < (Real.log 3) ^ (3 / 4 : ℝ) := by positivity
  let c0 : ℝ := min (c_vk / 4) (min (delta_M * (Real.log 3) ^ (3 / 4 : ℝ) / 2) (1 / 6))
  have hc0_pos : 0 < c0 := by
    dsimp [c0]
    apply lt_min
    · linarith
    · apply lt_min
      · have : 0 < delta_M * (Real.log 3) ^ (3 / 4 : ℝ) := mul_pos hdelta_M_pos hrpow3_pos
        linarith
      · norm_num
  have hc0_le_cvk4 : c0 ≤ c_vk / 4 := min_le_left _ _
  have hc0_le_deltaM : c0 ≤ delta_M * (Real.log 3) ^ (3 / 4 : ℝ) / 2 :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hc0_le_sixth : c0 ≤ 1 / 6 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hc0_lt_cvk : c0 < c_vk := by linarith [hc0_le_cvk4, hc_vk_pos]
  obtain ⟨C_2, hC_2_gt1, hC_2_bound⟩ := sum_m_rho_zeta_ge3
  have hr1_pos : (0 : ℝ) < 2 / 3 := by norm_num
  have hr1_lt_r : (2 / 3 : ℝ) < 3 / 4 := by norm_num
  have hr_lt_R1 : (3 / 4 : ℝ) < 5 / 6 := by norm_num
  obtain ⟨C_exp, hC_exp_gt1, hC_exp_bound⟩ :=
    Zeta1_Zeta_Expansion_ge3 (2 / 3) (3 / 4) hr1_pos hr1_lt_r hr_lt_R1
  let C_exp' : ℝ := C_exp * (1 / ((3 / 4 : ℝ) - (2 / 3 : ℝ)) ^ 3 + 1)
  have hC_exp'_nonneg : 0 ≤ C_exp' := by
    dsimp [C_exp']
    positivity
  obtain ⟨C0, hC0_gt1, hC0_bound⟩ := Z0bound_const
  let K : ℝ := max (C_exp' + C_2 / c0) (max (C0 + 2) 1)
  have hK_ge1 : 1 ≤ K := le_trans (le_max_right (C0 + 2) 1) (le_max_right _ _)
  refine ⟨c0, K, hc0_pos, hK_ge1, ?_, ?_⟩
  · intro σ t ht hσ_low hσ_high
    by_cases hσ_mid : σ ≤ 3 / 2
    · let c : ℂ := (3 / 2 : ℂ) + I * t
      let z : ℂ := σ + t * I
      have hc_eq : c = (3 / 2 : ℂ) + Complex.I * t := rfl
      have hz_eq : z = σ + t * Complex.I := rfl
      have hz_in_ball : z ∈ closedBall c (2 / 3) :=
        z_mem_closedBall_two_thirds t σ c0 ht hc0_le_sixth hc0_pos hσ_low hσ_mid c hc_eq z hz_eq
      have hfin := zerosetKfRc_finite c (5 / 6)
      have h_rho_re_le : ∀ ρ ∈ hfin.toFinset, ρ.re ≤ 1 - 2 * c0 / (Real.log |t|) ^ (3 / 4 : ℝ) := by
        intro ρ hρ_mem
        have hρ_in_K : ρ ∈ zerosetKfRc (5 / 6) c riemannZeta :=
          (Set.Finite.mem_toFinset (hs := hfin)).mp hρ_mem
        have hρ_zero : riemannZeta ρ = 0 := hρ_in_K.2
        have hρ_ball : ρ ∈ closedBall c (5 / 6) := hρ_in_K.1
        have him_le : |ρ.im| ≤ 2 * |t| := rho_im_bound t ht c hc_eq ρ hρ_ball
        by_cases h6 : 6 ≤ |ρ.im|
        · have h_vk := h_vk_zf ρ hρ_zero h6
          have h_ge := div_rpow_three_quarters_ge c_vk c0 hc_vk_pos hc0_le_cvk4 |t| |ρ.im| ht h6 him_le
          linarith [h_vk, h_ge]
        · push Not at h6
          have h_m := rho_re_lt_of_im_lt_six M_bg hM2_bg hMbound_bg ρ hρ_zero h6
          have h_le := div_rpow_three_quarters_le_delta_M delta_M c0 hdelta_M_nonneg hc0_le_deltaM |t| ht
          linarith [h_m, h_le]
      have hz_not_in_K : z ∉ zerosetKfRc (5 / 6) c riemannZeta := by
        intro hz_in
        have hz_fin : z ∈ hfin.toFinset := (Set.Finite.mem_toFinset (hs := hfin)).mpr hz_in
        have h_z_re_le := h_rho_re_le z hz_fin
        have hz_re : z.re = σ := by simp [z]
        rw [hz_re] at h_z_re_le
        have hrpow_pos : 0 < (Real.log |t|) ^ (3 / 4 : ℝ) := by
          have : 0 < Real.log |t| := Real.log_pos (by linarith)
          positivity
        have h_two_div : 2 * c0 / (Real.log |t|) ^ (3 / 4 : ℝ) = 2 * (c0 / (Real.log |t|) ^ (3 / 4 : ℝ)) := by ring
        rw [h_two_div] at h_z_re_le
        have : 0 < c0 / (Real.log |t|) ^ (3 / 4 : ℝ) := div_pos hc0_pos hrpow_pos
        linarith [hσ_low, h_z_re_le]
      have hz_diff : z ∈ closedBall c (2 / 3) \ zerosetKfRc (5 / 6) c riemannZeta :=
        ⟨hz_in_ball, hz_not_in_K⟩
      have h_expand := hC_exp_bound t ht hfin z hz_diff
      have h_sum_norm_le := norm_sum_m_div_le hfin.toFinset z
      have h_dist_ge : ∀ ρ ∈ hfin.toFinset, c0 / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ ‖z - ρ‖ := by
        intro ρ hρ_mem
        have h_rho_re := h_rho_re_le ρ hρ_mem
        have hz_re : z.re = σ := by simp [z]
        have h_two_div : 2 * c0 / (Real.log |t|) ^ (3 / 4 : ℝ) = 2 * (c0 / (Real.log |t|) ^ (3 / 4 : ℝ)) := by ring
        rw [h_two_div] at h_rho_re
        have h_diff : c0 / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ z.re - ρ.re := by
          rw [hz_re]
          linarith [hσ_low, h_rho_re]
        have h_re_norm : z.re - ρ.re ≤ ‖z - ρ‖ := by
          have : z.re - ρ.re = (z - ρ).re := by simp
          rw [this]
          exact Complex.re_le_norm (z - ρ)
        exact le_trans h_diff h_re_norm
      have h_recip_le : ∀ ρ ∈ hfin.toFinset, 1 / ‖z - ρ‖ ≤ (Real.log |t|) ^ (3 / 4 : ℝ) / c0 := by
        intro ρ hρ_mem
        have hpos : 0 < c0 / (Real.log |t|) ^ (3 / 4 : ℝ) := by
          have hrpow_pos : 0 < (Real.log |t|) ^ (3 / 4 : ℝ) := by
            have : 0 < Real.log |t| := Real.log_pos (by linarith)
            positivity
          exact div_pos hc0_pos hrpow_pos
        have hle := h_dist_ge ρ hρ_mem
        have hinv := one_div_le_one_div_of_le hpos hle
        have h_alg : 1 / (c0 / (Real.log |t|) ^ (3 / 4 : ℝ)) = (Real.log |t|) ^ (3 / 4 : ℝ) / c0 := by
          rw [one_div_div]
        rwa [h_alg] at hinv
      have h_sum_terms : (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
          ((Real.log |t|) ^ (3 / 4 : ℝ) / c0) * ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
        have h1 : (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) =
            ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * (1 / ‖z - ρ‖) := by
          congr 1; ext ρ; ring
        rw [h1]
        have h2 : ∀ ρ ∈ hfin.toFinset,
            ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * (1 / ‖z - ρ‖) ≤
            ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * ((Real.log |t|) ^ (3 / 4 : ℝ) / c0) := by
          intro ρ hρ_mem
          apply mul_le_mul_of_nonneg_left (h_recip_le ρ hρ_mem)
          positivity
        have h3 := Finset.sum_le_sum h2
        have h4 : (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * ((Real.log |t|) ^ (3 / 4 : ℝ) / c0)) =
            ((Real.log |t|) ^ (3 / 4 : ℝ) / c0) * ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
          rw [← Finset.sum_mul, mul_comm]
        rwa [h4] at h3
      have h_m_sum := hC_2_bound t ht hfin
      have h_sum_le_C2 : ((Real.log |t|) ^ (3 / 4 : ℝ) / c0) * ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤
          ((Real.log |t|) ^ (3 / 4 : ℝ) / c0) * (C_2 * Real.log |t|) := by
        apply mul_le_mul_of_nonneg_left h_m_sum
        have hrpow_pos : 0 < (Real.log |t|) ^ (3 / 4 : ℝ) := by
          have : 0 < Real.log |t| := Real.log_pos (by linarith)
          positivity
        exact div_nonneg (le_of_lt hrpow_pos) (le_of_lt hc0_pos)
      have h_alg_prod : ((Real.log |t|) ^ (3 / 4 : ℝ) / c0) * (C_2 * Real.log |t|) =
          (C_2 / c0) * ((Real.log |t|) ^ (3 / 4 : ℝ) * Real.log |t|) := by ring
      rw [h_alg_prod] at h_sum_le_C2
      have hlogt_pos : 0 < Real.log |t| := Real.log_pos (by linarith)
      have h_rpow_eval : (Real.log |t|) ^ (3 / 4 : ℝ) * Real.log |t| = (Real.log |t|) ^ (7 / 4 : ℝ) := by
        nth_rw 2 [← Real.rpow_one (Real.log |t|)]
        rw [← Real.rpow_add hlogt_pos]
        congr 1
        norm_num
      rw [h_rpow_eval] at h_sum_le_C2
      have h_pow2 := log_rpow_seven_quarters_le_pow_two t ht
      have h_sum_final : ((Real.log |t|) ^ (3 / 4 : ℝ) / c0) * ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤
          (C_2 / c0) * (Real.log |t|) ^ 2 := by
        have h_c2_c0_nonneg : 0 ≤ C_2 / c0 := div_nonneg (by linarith) (le_of_lt hc0_pos)
        have := mul_le_mul_of_nonneg_left h_pow2 h_c2_c0_nonneg
        exact le_trans h_sum_le_C2 this
      have h_sum_bound_total : (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
          (C_2 / c0) * (Real.log |t|) ^ 2 :=
        le_trans h_sum_terms h_sum_final
      have h_sum_norm_bound : ‖∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
          (C_2 / c0) * (Real.log |t|) ^ 2 :=
        le_trans h_sum_norm_le h_sum_bound_total
      have h_tri_logDeriv : ‖logDerivZeta z‖ ≤
          ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ +
          ‖∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ := by
        have : logDerivZeta z =
            (logDerivZeta z - ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)) +
            (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)) := by ring
        nth_rw 1 [this]
        exact norm_add_le _ _
      have h_expand_le : C_exp * (1 / ((3 / 4 : ℝ) - (2 / 3 : ℝ)) ^ 3 + 1) * Real.log |t| ≤
          C_exp' * (Real.log |t|) ^ 2 := by
        dsimp [C_exp']
        have h_log_le := log_le_pow_two t ht
        exact mul_le_mul_of_nonneg_left h_log_le hC_exp'_nonneg
      have h_logDeriv_le : ‖logDerivZeta z‖ ≤ (C_exp' + C_2 / c0) * (Real.log |t|) ^ 2 := by
        have h_sum_le := add_le_add h_expand h_sum_norm_bound
        have h_comb : ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ +
            ‖∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
            (C_exp' + C_2 / c0) * (Real.log |t|) ^ 2 := by
          calc ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ +
                ‖∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖
            ≤ C_exp * (1 / ((3 / 4 : ℝ) - (2 / 3 : ℝ)) ^ 3 + 1) * Real.log |t| + (C_2 / c0) * (Real.log |t|) ^ 2 := h_sum_le
            _ ≤ C_exp' * (Real.log |t|) ^ 2 + (C_2 / c0) * (Real.log |t|) ^ 2 := by linarith [h_expand_le]
            _ = (C_exp' + C_2 / c0) * (Real.log |t|) ^ 2 := by ring
        exact le_trans h_tri_logDeriv h_comb
      have hK_ge : C_exp' + C_2 / c0 ≤ K := le_max_left _ _
      have hpow2_nonneg : 0 ≤ (Real.log |t|) ^ 2 := by positivity
      have h_K_mul : (C_exp' + C_2 / c0) * (Real.log |t|) ^ 2 ≤ K * (Real.log |t|) ^ 2 :=
        mul_le_mul_of_nonneg_right hK_ge hpow2_nonneg
      have h_final_z : ‖logDerivZeta z‖ ≤ K * (Real.log |t|) ^ 2 := le_trans h_logDeriv_le h_K_mul
      have hz_def : logDerivZeta z = deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I) := rfl
      rwa [hz_def] at h_final_z
    · push Not at hσ_mid
      have hσ_ge : 3 / 2 ≤ σ := le_of_lt hσ_mid
      have h_bound := logDeriv_ge_32 t σ hσ_ge C0 hC0_bound
      have hlogt_ge1 : 1 ≤ Real.log |t| := by
        have : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
        have : 1 < Real.log 3 := one_lt_log_three'
        linarith
      have hpow2_ge1 : 1 ≤ (Real.log |t|) ^ 2 := by
        nlinarith
      have hC0_nonneg : 0 ≤ C0 + 2 := by linarith
      have h1 : C0 + 2 ≤ (C0 + 2) * (Real.log |t|) ^ 2 := by
        calc C0 + 2 = (C0 + 2) * 1 := by ring
          _ ≤ (C0 + 2) * (Real.log |t|) ^ 2 := mul_le_mul_of_nonneg_left hpow2_ge1 hC0_nonneg
      have h2 : C0 + 2 ≤ K := le_trans (le_max_left (C0 + 2) 1) (le_max_right _ _)
      have hpow2_nonneg : 0 ≤ (Real.log |t|) ^ 2 := by positivity
      have h3 : (C0 + 2) * (Real.log |t|) ^ 2 ≤ K * (Real.log |t|) ^ 2 :=
        mul_le_mul_of_nonneg_right h2 hpow2_nonneg
      exact le_trans h_bound (le_trans h1 h3)
  · intro T hT
    apply LogDerivZetaHoloOn (by intro h; exact h.2 rfl)
    intro s hs
    simp only [Set.mem_sdiff, Complex.mem_reProdIm, Set.mem_Icc, Set.mem_singleton_iff] at hs
    rcases hs with ⟨⟨⟨hs_re_low, hs_re_high⟩, hs_im_low, hs_im_high⟩, hs_ne1⟩
    intro hzero
    by_cases hs_re1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re hs_re1 hzero
    · push Not at hs_re1
      by_cases h6 : 6 ≤ |s.im|
      · have h_vk := h_vk_zf s hzero h6
        have him_le : |s.im| ≤ T := abs_le.mpr ⟨hs_im_low, hs_im_high⟩
        have hlog_im_le : Real.log |s.im| ≤ Real.log T := by
          apply Real.log_le_log (by linarith) him_le
        have hrpow_im_le : (Real.log |s.im|) ^ (3 / 4 : ℝ) ≤ (Real.log T) ^ (3 / 4 : ℝ) := by
          have : 0 < Real.log |s.im| := Real.log_pos (by linarith)
          exact Real.rpow_le_rpow (le_of_lt this) hlog_im_le (by norm_num)
        have hrpow_im_pos : 0 < (Real.log |s.im|) ^ (3 / 4 : ℝ) := by
          have : 0 < Real.log |s.im| := Real.log_pos (by linarith)
          positivity
        have h_frac_ge : c_vk / (Real.log T) ^ (3 / 4 : ℝ) ≤ c_vk / (Real.log |s.im|) ^ (3 / 4 : ℝ) :=
          div_le_div_of_nonneg_left (le_of_lt hc_vk_pos) hrpow_im_pos hrpow_im_le
        have h_c0_le : c0 / (Real.log T) ^ (3 / 4 : ℝ) < c_vk / (Real.log T) ^ (3 / 4 : ℝ) := by
          have hrpowT_pos : 0 < (Real.log T) ^ (3 / 4 : ℝ) := by
            have : 0 < Real.log T := Real.log_pos (by linarith)
            positivity
          exact div_lt_div_of_pos_right hc0_lt_cvk hrpowT_pos
        have : s.re < 1 - c0 / (Real.log T) ^ (3 / 4 : ℝ) := by
          linarith [h_vk, h_frac_ge, h_c0_le]
        linarith [hs_re_low]
      · push Not at h6
        have h_m := rho_re_lt_of_im_lt_six M_bg hM2_bg hMbound_bg s hzero h6
        have hlogT_ge : Real.log 3 ≤ Real.log T := Real.log_le_log (by norm_num) hT
        have hrpowT_ge : (Real.log 3) ^ (3 / 4 : ℝ) ≤ (Real.log T) ^ (3 / 4 : ℝ) := by
          have : 0 < Real.log 3 := Real.log_pos (by norm_num)
          exact Real.rpow_le_rpow (le_of_lt this) hlogT_ge (by norm_num)
        have h_c0_bound : c0 / (Real.log T) ^ (3 / 4 : ℝ) < delta_M := by
          have h1 : c0 / (Real.log T) ^ (3 / 4 : ℝ) ≤ c0 / (Real.log 3) ^ (3 / 4 : ℝ) := by
            have hrpow3_pos' : 0 < (Real.log 3) ^ (3 / 4 : ℝ) := hrpow3_pos
            exact div_le_div_of_nonneg_left (le_of_lt hc0_pos) hrpow3_pos' hrpowT_ge
          have h2 : c0 / (Real.log 3) ^ (3 / 4 : ℝ) ≤ delta_M / 2 := by
            have h_alg : delta_M * (Real.log 3) ^ (3 / 4 : ℝ) / 2 / (Real.log 3) ^ (3 / 4 : ℝ) = delta_M / 2 := by
              have : (Real.log 3) ^ (3 / 4 : ℝ) ≠ 0 := ne_of_gt hrpow3_pos
              field_simp
            have := div_le_div_of_nonneg_right hc0_le_deltaM (le_of_lt hrpow3_pos)
            rwa [h_alg] at this
          have h3 : delta_M / 2 < delta_M := by linarith [hdelta_M_pos]
          exact lt_of_le_of_lt (le_trans h1 h2) h3
        have : s.re < 1 - c0 / (Real.log T) ^ (3 / 4 : ℝ) := by linarith [h_m, h_c0_bound]
        linarith [hs_re_low]

end Erdos1201.MR
