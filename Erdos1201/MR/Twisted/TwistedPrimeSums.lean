/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gemini

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.MR.Twisted.TwistedBounds
import Erdos1201.MR.Twisted.TwistedChebyshev

/-!
# Twisted Prime Sums in Short Intervals

This module provides the calculus estimates and contour reduction lemmas for twisted
prime sums $\sum_{A < p \le B} p^{-(1 + iu)}$ over short intervals $[A, B]$ with $B \le 2A$.
-/

namespace Erdos1201.MR

open Complex Real MeasureTheory Set Filter Function

lemma norm_cpow_neg_mul_I {x u : ℝ} (hx : 0 < x) : ‖(x : ℂ) ^ (-(u : ℂ) * I)‖ = 1 := by
  rw [norm_cpow_eq_rpow_re_of_pos hx]
  have : (-(u : ℂ) * I).re = 0 := by
    simp only [neg_mul, neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, neg_zero]
  rw [this, rpow_zero]

lemma norm_neg_mul_I (u : ℝ) : ‖-(u : ℂ) * I‖ = |u| := by
  simp only [neg_mul, norm_neg, norm_mul, norm_real, norm_eq_abs, norm_I, mul_one]

lemma integral_inv_mul_sq_log_le {A B : ℝ} (hA : 3 ≤ A) (hAB : A ≤ B) :
    ∫ x in A..B, x⁻¹ / (Real.log x ^ 2) ≤ 1 / Real.log A := by
  have h_deriv : ∀ x ∈ uIcc A B, HasDerivAt (fun t => - (Real.log t)⁻¹) (x⁻¹ / (Real.log x ^ 2)) x := by
    intro x hx
    rw [uIcc_of_le hAB, mem_Icc] at hx
    have hx_gt : 1 < x := by linarith
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx_gt)
    have ht_pos : 0 < x := by linarith
    have h_log : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt ht_pos)
    have h1 : HasDerivAt (fun t => (Real.log t)⁻¹) (- x⁻¹ / (Real.log x ^ 2)) x := h_log.inv hlog
    have h2 := h1.neg
    have heq : - (- x⁻¹ / (Real.log x ^ 2)) = x⁻¹ / (Real.log x ^ 2) := by rw [neg_div, neg_neg]
    rw [heq] at h2
    exact h2
  have h_cont : ContinuousOn (fun x => x⁻¹ / (Real.log x ^ 2)) (uIcc A B) := by
    rw [uIcc_of_le hAB]
    apply ContinuousOn.div
    · exact continuousOn_inv₀.mono (fun x hx => by
        simp only [mem_Icc] at hx
        exact ne_of_gt (by linarith))
    · apply ContinuousOn.pow
      apply Real.continuousOn_log.mono (fun x hx => by
        simp only [mem_Icc] at hx
        exact mem_compl_singleton_iff.mpr (by linarith))
    · intro x hx
      simp only [mem_Icc] at hx
      have : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      exact pow_ne_zero 2 this
  have h_int : IntervalIntegrable (fun x => x⁻¹ / (Real.log x ^ 2)) volume A B := h_cont.intervalIntegrable
  have h_eval := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int
  rw [h_eval]
  have hlogA_pos : 0 < Real.log A := Real.log_pos (by linarith)
  have hlogB_pos : 0 < Real.log B := Real.log_pos (by linarith)
  have : - (Real.log B)⁻¹ - - (Real.log A)⁻¹ = (Real.log A)⁻¹ - (Real.log B)⁻¹ := by ring
  rw [this, one_div]
  have : 0 < (Real.log B)⁻¹ := by positivity
  linarith

lemma integral_norm_f'_mul_g_le (A B u : ℝ) (hA : 3 ≤ A) (hAB : A ≤ B) (hu : 1 ≤ |u|) :
    ∫ (x : ℝ) in A..B, ‖(- ((x : ℂ)⁻¹) / ((Real.log x : ℂ) ^ 2)) * ((x : ℂ) ^ (-(u : ℂ) * I) / (-(u : ℂ) * I))‖ ≤
      1 / (|u| * Real.log A) := by
  have hu_pos : 0 < |u| := by positivity
  have h_eq_on : Set.EqOn (fun (x : ℝ) => ‖(- ((x : ℂ)⁻¹) / ((Real.log x : ℂ) ^ 2)) * ((x : ℂ) ^ (-(u : ℂ) * I) / (-(u : ℂ) * I))‖)
      (fun (x : ℝ) => (1 / |u|) * (x⁻¹ / (Real.log x ^ 2))) (uIcc A B) := by
    intro x hx
    rw [uIcc_of_le hAB, mem_Icc] at hx
    have hx_pos : 0 < x := by linarith
    have hx_gt1 : 1 < x := by linarith
    have h_g : ‖(x : ℂ) ^ (-(u : ℂ) * I) / (-(u : ℂ) * I)‖ = 1 / |u| := by
      rw [norm_div, norm_cpow_neg_mul_I hx_pos, norm_neg_mul_I]
    have h_f' : ‖- ((x : ℂ)⁻¹) / ((Real.log x : ℂ) ^ 2)‖ = x⁻¹ / (Real.log x ^ 2) := by
      rw [norm_div, norm_neg, norm_inv, Complex.norm_real, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hx_pos.le, Real.norm_of_nonneg (Real.log_pos hx_gt1).le]
    dsimp
    rw [norm_mul, h_f', h_g]
    ring
  have h_int_eq : (∫ (x : ℝ) in A..B, ‖(- ((x : ℂ)⁻¹) / ((Real.log x : ℂ) ^ 2)) * ((x : ℂ) ^ (-(u : ℂ) * I) / (-(u : ℂ) * I))‖) =
      ∫ (x : ℝ) in A..B, (1 / |u|) * (x⁻¹ / (Real.log x ^ 2)) :=
    intervalIntegral.integral_congr (E := ℝ) (μ := volume) h_eq_on
  have h_int_const := @intervalIntegral.integral_const_mul ℝ A B volume _ _ (1 / |u|)
    (fun x => x⁻¹ / (Real.log x ^ 2))
  have h1 : (1 / |u|) * ∫ x in A..B, x⁻¹ / (Real.log x ^ 2) ≤ (1 / |u|) * (1 / Real.log A) := by
    have : 0 ≤ 1 / |u| := by positivity
    exact mul_le_mul_of_nonneg_left (integral_inv_mul_sq_log_le hA hAB) this
  have h2 : (1 / |u|) * (1 / Real.log A) = 1 / (|u| * Real.log A) := by ring
  calc
    (∫ (x : ℝ) in A..B, ‖(- ((x : ℂ)⁻¹) / ((Real.log x : ℂ) ^ 2)) * ((x : ℂ) ^ (-(u : ℂ) * I) / (-(u : ℂ) * I))‖)
      = ∫ (x : ℝ) in A..B, (1 / |u|) * (x⁻¹ / (Real.log x ^ 2)) := h_int_eq
    _ = (1 / |u|) * ∫ x in A..B, x⁻¹ / (Real.log x ^ 2) := h_int_const
    _ ≤ (1 / |u|) * (1 / Real.log A) := h1
    _ = 1 / (|u| * Real.log A) := h2

lemma hasDerivAt_cpow_div (u : ℝ) (hu : u ≠ 0) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-(u : ℂ) * I) / (-(u : ℂ) * I))
      ((x : ℂ) ^ (-((1 : ℂ) + u * Complex.I))) x := by
  have hs : (x : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    simpa using hx
  have h1 : HasDerivAt (fun z : ℂ => z ^ (-(u : ℂ) * I))
      ((-(u : ℂ) * I) * (x : ℂ) ^ (-(u : ℂ) * I - 1)) (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).cpow_const hs (c := -(u : ℂ) * I)
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (-(u : ℂ) * I))
      ((-(u : ℂ) * I) * (x : ℂ) ^ (-(u : ℂ) * I - 1)) x := h1.comp_ofReal
  have h_w_ne : -(u : ℂ) * I ≠ 0 := by simp [hu]
  have h3 := h2.div_const (-(u : ℂ) * I)
  have heq : (-(u : ℂ) * I) * (x : ℂ) ^ (-(u : ℂ) * I - 1) / (-(u : ℂ) * I) =
      (x : ℂ) ^ (-((1 : ℂ) + u * Complex.I)) := by
    rw [mul_div_cancel_left₀ _ h_w_ne]
    congr 1
    ring
  rw [heq] at h3
  exact h3

lemma hasDerivAt_inv_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => (Real.log t : ℂ)⁻¹) (- (x : ℂ)⁻¹ / ((Real.log x : ℂ) ^ 2)) x := by
  have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlog' : (Real.log x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hlog
  have h_log : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (by linarith)
  have h1 : HasDerivAt (fun t : ℝ => (Real.log t : ℂ)) (x : ℂ)⁻¹ x := by
    have := h_log.ofReal_comp
    push_cast at this ⊢
    exact this
  exact h1.inv hlog'

theorem norm_integral_cpow_div_log_le (A B u : ℝ) (hA : 3 ≤ A) (hAB : A ≤ B) (hu : 1 ≤ |u|) :
    ‖∫ x in A..B, (x : ℂ) ^ (-((1 : ℂ) + u * Complex.I)) / (Real.log x : ℂ)‖ ≤ 3 / (|u| * Real.log A) := by
  have hu_ne : u ≠ 0 := by
    intro h; subst h; simp only [abs_zero] at hu; linarith
  have hA_pos : (0 : ℝ) < A := by linarith
  have hA_gt1 : (1 : ℝ) < A := by linarith
  have hB_pos : (0 : ℝ) < B := by linarith
  have hB_gt1 : (1 : ℝ) < B := by linarith
  have hu_pos : 0 < |u| := by positivity
  have hlogA_pos : 0 < Real.log A := Real.log_pos hA_gt1
  have hlogB_pos : 0 < Real.log B := Real.log_pos hB_gt1
  have hlogA_le : Real.log A ≤ Real.log B := Real.log_le_log hA_pos hAB

  let f : ℝ → ℂ := fun t => (Real.log t : ℂ)⁻¹
  let f' : ℝ → ℂ := fun t => - (t : ℂ)⁻¹ / ((Real.log t : ℂ) ^ 2)
  let g : ℝ → ℂ := fun t => (t : ℂ) ^ (-(u : ℂ) * I) / (-(u : ℂ) * I)
  let g' : ℝ → ℂ := fun t => (t : ℂ) ^ (-((1 : ℂ) + u * Complex.I))

  have hf_deriv : ∀ x ∈ uIcc A B, HasDerivAt f (f' x) x := by
    intro x hx
    rw [uIcc_of_le hAB, mem_Icc] at hx
    exact hasDerivAt_inv_log (by linarith)

  have hg_deriv : ∀ x ∈ uIcc A B, HasDerivAt g (g' x) x := by
    intro x hx
    rw [uIcc_of_le hAB, mem_Icc] at hx
    exact hasDerivAt_cpow_div u hu_ne x (by linarith)

  have hf'_cont : ContinuousOn f' (uIcc A B) := by
    rw [uIcc_of_le hAB]
    apply ContinuousOn.div
    · apply ContinuousOn.neg
      apply ContinuousOn.inv₀
      · exact continuous_ofReal.continuousOn
      · intro x hx; simp only [mem_Icc] at hx; exact ofReal_ne_zero.mpr (by linarith)
    · apply ContinuousOn.pow
      apply ContinuousOn.comp continuous_ofReal.continuousOn
      · exact Real.continuousOn_log.mono (fun x hx => by
          simp only [mem_Icc] at hx
          exact mem_compl_singleton_iff.mpr (by linarith))
      · intro x hx; simp only [mem_Icc] at hx; exact mem_univ _
    · intro x hx
      simp only [mem_Icc] at hx
      have : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      exact pow_ne_zero 2 (ofReal_ne_zero.mpr this)

  have hg'_cont : ContinuousOn g' (uIcc A B) := by
    have h_sub : uIcc A B ⊆ Ioi 0 := by
      rw [uIcc_of_le hAB]
      intro x hx; simp only [mem_Icc, mem_Ioi] at hx ⊢; linarith
    refine ContinuousOn.mono ?_ h_sub
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hs : (x : ℂ) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left; simpa using hx
    exact ((hasDerivAt_id (x : ℂ)).cpow_const hs (c := -((1 : ℂ) + u * I))).comp_ofReal.continuousAt

  have hf'_int : IntervalIntegrable f' volume A B := hf'_cont.intervalIntegrable
  have hg'_int : IntervalIntegrable g' volume A B := hg'_cont.intervalIntegrable

  have h_ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf_deriv hg_deriv hf'_int hg'_int
  have h_integrand : (fun (x : ℝ) => (x : ℂ) ^ (-((1 : ℂ) + u * Complex.I)) / (Real.log x : ℂ)) =
      (fun x => f x * g' x) := by
    ext x
    dsimp [f, g']
    ring
  rw [h_integrand, h_ibp]

  have h_tri := norm_sub_le (f B * g B - f A * g A) (∫ x in A..B, f' x * g x)
  refine le_trans h_tri ?_
  have h_btri := norm_sub_le (f B * g B) (f A * g A)
  have h_bound1 : ‖f B * g B‖ ≤ 1 / (|u| * Real.log A) := by
    dsimp [f, g]
    rw [norm_mul, norm_inv, Complex.norm_real, norm_div, norm_cpow_neg_mul_I hB_pos,
      norm_neg_mul_I, Real.norm_of_nonneg hlogB_pos.le]
    have : (Real.log B)⁻¹ * (1 / |u|) = (|u| * Real.log B)⁻¹ := by
      rw [one_div, mul_comm, ← mul_inv]
    rw [this, one_div]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left hlogA_le hu_pos.le
  have h_bound2 : ‖f A * g A‖ = 1 / (|u| * Real.log A) := by
    dsimp [f, g]
    rw [norm_mul, norm_inv, Complex.norm_real, norm_div, norm_cpow_neg_mul_I hA_pos,
      norm_neg_mul_I, Real.norm_of_nonneg hlogA_pos.le]
    rw [one_div, mul_comm, ← mul_inv, one_div]
  have h_bterm : ‖f B * g B - f A * g A‖ ≤ 2 / (|u| * Real.log A) := by
    have := calc
      ‖f B * g B - f A * g A‖ ≤ ‖f B * g B‖ + ‖f A * g A‖ := h_btri
      _ ≤ 1 / (|u| * Real.log A) + 1 / (|u| * Real.log A) := by
        rw [h_bound2]
        linarith
      _ = 2 / (|u| * Real.log A) := by ring
    exact this

  have h_int_norm_le : ‖∫ x in A..B, f' x * g x‖ ≤ 1 / (|u| * Real.log A) := by
    have h_le_int := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun x => f' x * g x) hAB
    refine le_trans h_le_int ?_
    exact integral_norm_f'_mul_g_le A B u hA hAB hu

  calc
    ‖f B * g B - f A * g A‖ + ‖∫ x in A..B, f' x * g x‖
      ≤ 2 / (|u| * Real.log A) + 1 / (|u| * Real.log A) := add_le_add h_bterm h_int_norm_le
    _ = 3 / (|u| * Real.log A) := by ring

lemma zeta_bound_of_c0_le {c₀ c₀' K : ℝ} (hc : c₀' ≤ c₀)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2) :
    ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀' / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2 := by
  intro σ t ht hσ hσ2
  have ht_log : 0 < (Real.log |t|) ^ (3 / 4 : ℝ) := by
    have : 1 < Real.log 3 := logt_gt_one (le_refl 3)
    have : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
    have : 0 < Real.log |t| := by linarith
    positivity
  have h_div : c₀' / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) := by
    exact div_le_div_of_nonneg_right hc ht_log.le
  have h_σ : 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ := by linarith
  exact hζ σ t ht h_σ hσ2

lemma holo_zeta_of_c0_le {c₀ c₀' : ℝ} (hc : c₀' ≤ c₀)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      ((Set.Icc (1 - c₀' / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1}) := by
  intro T hT
  have hT_log : 0 < (Real.log T) ^ (3 / 4 : ℝ) := by
    have : 1 < Real.log 3 := logt_gt_one (le_refl 3)
    have : Real.log 3 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    have : 0 < Real.log T := by linarith
    positivity
  have h_div : c₀' / (Real.log T) ^ (3 / 4 : ℝ) ≤ c₀ / (Real.log T) ^ (3 / 4 : ℝ) :=
    div_le_div_of_nonneg_right hc hT_log.le
  have h_sub : (Set.Icc (1 - c₀' / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1} ⊆
      (Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1} := by
    intro s hs
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_singleton_iff] at hs ⊢
    refine ⟨⟨⟨by linarith, hs.1.1.2⟩, hs.1.2⟩, hs.2⟩
  exact (hholo T hT).mono h_sub

lemma theta_pos_and_le_half {c : ℝ} (hc_pos : 0 < c) (hc_le : c ≤ (1 / 2) * (Real.log 3) ^ (3 / 4 : ℝ)) :
    ∀ t, 3 ≤ t → 0 < c / (Real.log t) ^ (3 / 4 : ℝ) ∧ c / (Real.log t) ^ (3 / 4 : ℝ) ≤ 1 / 2 := by
  intro t ht
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlogt_ge : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hpow_pos : 0 < (Real.log t) ^ (3 / 4 : ℝ) := rpow_pos_of_pos (by linarith) _
  have h1 : 0 < c / (Real.log t) ^ (3 / 4 : ℝ) := div_pos hc_pos hpow_pos
  have hpow_mono : (Real.log 3) ^ (3 / 4 : ℝ) ≤ (Real.log t) ^ (3 / 4 : ℝ) :=
    rpow_le_rpow hlog3_pos.le hlogt_ge (by norm_num)
  have h2 : c / (Real.log t) ^ (3 / 4 : ℝ) ≤ 1 / 2 := by
    have h_le1 : c / (Real.log t) ^ (3 / 4 : ℝ) ≤ c / (Real.log 3) ^ (3 / 4 : ℝ) :=
      div_le_div_of_nonneg_left hc_pos.le (rpow_pos_of_pos hlog3_pos _) hpow_mono
    have h_le2 : c / (Real.log 3) ^ (3 / 4 : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ (rpow_pos_of_pos hlog3_pos _)]
      exact hc_le
    exact le_trans h_le1 h_le2
  exact ⟨h1, h2⟩

lemma theta_antitone {c : ℝ} (hc : 0 ≤ c) :
    AntitoneOn (fun t => c / (Real.log t) ^ (3 / 4 : ℝ)) (Set.Ici 3) := by
  intro x hx y hy hxy
  simp only [mem_Ici] at hx hy
  have hx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hy_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  have hpow_le : (Real.log x) ^ (3 / 4 : ℝ) ≤ (Real.log y) ^ (3 / 4 : ℝ) :=
    rpow_le_rpow hx_pos.le hlog_le (by norm_num)
  exact div_le_div_of_nonneg_left hc (rpow_pos_of_pos hx_pos _) hpow_le

lemma phi_ge_one {K : ℝ} (hK : 1 ≤ K) :
    ∀ t, 3 ≤ t → 1 ≤ K * (Real.log t) ^ (2 : ℝ) := by
  intro t ht
  have hlog3_gt1 : 1 < Real.log 3 := logt_gt_one (le_refl 3)
  have hlogt_ge : Real.log 3 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlogt_gt1 : 1 < Real.log t := lt_of_lt_of_le hlog3_gt1 hlogt_ge
  have hpow_ge : 1 ≤ (Real.log t) ^ (2 : ℝ) := by
    have : (1 : ℝ) = (1 : ℝ) ^ (2 : ℝ) := by norm_num
    rw [this]
    exact Real.rpow_le_rpow (by norm_num) hlogt_gt1.le (by norm_num)
  have : (1 : ℝ) * 1 ≤ K * (Real.log t) ^ (2 : ℝ) :=
    mul_le_mul hK hpow_ge (by norm_num) (by linarith)
  simpa using this

lemma phi_monotone {K : ℝ} (hK : 0 ≤ K) :
    MonotoneOn (fun t => K * (Real.log t) ^ (2 : ℝ)) (Set.Ici 3) := by
  intro x hx y hy hxy
  have hx_le : (3 : ℝ) ≤ x := hx
  have hy_le : (3 : ℝ) ≤ y := hy
  have hx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hy_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  have hpow_le : (Real.log x) ^ (2 : ℝ) ≤ (Real.log y) ^ (2 : ℝ) :=
    Real.rpow_le_rpow hx_pos.le hlog_le (by norm_num)
  exact mul_le_mul_of_nonneg_left hpow_le hK

theorem twistedSum_sub_main_le_of_holo (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1)
    (σ₂ : ℝ) (σ₂_pos : 0 < σ₂) (σ₂_lt_one : σ₂ < 1)
    (h_holo_zeta : DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1}))
    (θ φ : ℝ → ℝ) (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2) (hθanti : AntitoneOn θ (Set.Ici 3))
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t) (hφmono : MonotoneOn φ (Set.Ici 3))
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ φ |t|)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      ((Set.Icc (1 - θ T) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (u : ℝ) (T : ℝ)
        (_ : 3 < T) (_ : 2 * |u| + 3 ≤ T) (_ : φ T ≤ T) (_ : θ T ≤ (1 - σ₂) / 2),
      ‖twistedSum ν ε X u - mellin (fun x => (Smooth1 ν ε x : ℂ)) (1 - u * Complex.I) *
        (X : ℂ) ^ ((1 : ℂ) - u * Complex.I)‖ ≤
        C * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε) := by
  let θ₀ := (1 - σ₂) / 2
  have θ₀_pos : 0 < θ₀ := by dsimp [θ₀]; linarith
  obtain ⟨C₁, C₁_pos, hJ1⟩ := J1Bound ν diffν suppν νnonneg mass_one
  obtain ⟨C₂, C₂_pos, hJ2⟩ := J2Bound ν diffν suppν θ φ hθ hζ
  obtain ⟨C₃, C₃_pos, hJ3⟩ := J3Bound ν diffν suppν θ φ hθ hθanti hφ hφmono hζ
  obtain ⟨C₄, C₄_pos, hJ4⟩ := J4Bound ν diffν suppν σ₂_pos σ₂_lt_one h_holo_zeta
  obtain ⟨C₅, C₅_pos, hJ5⟩ := J5Bound ν diffν suppν σ₂_pos σ₂_lt_one h_holo_zeta
  obtain ⟨C₆, C₆_pos, hJ6⟩ := J6Bound ν diffν suppν σ₂_pos σ₂_lt_one h_holo_zeta
  obtain ⟨C₇, C₇_pos, hJ7⟩ := J7Bound ν diffν suppν θ φ hθ hθanti hφ hφmono hζ
  obtain ⟨C₈, C₈_pos, hJ8⟩ := J8Bound ν diffν suppν θ φ hθ hζ
  obtain ⟨C₉, C₉_pos, hJ9⟩ := J9Bound ν diffν suppν νnonneg mass_one
  let C := C₁ + C₂ + C₈ + C₉ + C₃ + C₄ + C₆ + C₇ + C₅
  have C_pos : 0 < C := by positivity
  refine ⟨C, C_pos, ?_⟩
  intro X X_gt ε ε_pos ε_lt_one u T T_gt hTu hphi htheta
  let σ₁ := 1 - θ T
  have hT_le : 3 ≤ T := T_gt.le
  have hθT := hθ T hT_le
  have σ₁_lt_one : σ₁ < 1 := by dsimp [σ₁]; linarith [hθT.1]
  have σ₁_pos : 0 < σ₁ := by dsimp [σ₁]; linarith [hθT.2]
  have σ₂_lt_σ₁ : σ₂ < σ₁ := by
    dsimp [σ₁, θ₀] at htheta ⊢
    linarith
  have h_holoT := hholo T hT_le
  have h_holo2 := holoOn2_of_LogDerivZeta ε_pos ε_lt_one X_gt u σ₂_pos suppν νnonneg mass_one diffν h_holo_zeta
  have h_sum := twistedChebyshev_eq_twistedSum ν diffν νnonneg suppν mass_one X_gt ε_pos ε_lt_one u
  have h_pull1 := twistedChebyshevPull1 ν ε_pos ε_lt_one X X_gt (by linarith) σ₁_pos σ₁_lt_one h_holoT suppν νnonneg mass_one diffν u
  have h_pull2 := twistedChebyshevPull2 ν ε_pos ε_lt_one X X_gt T_gt σ₂_pos σ₁_lt_one σ₂_lt_σ₁ h_holoT u h_holo2 suppν νnonneg mass_one diffν
  let main := mellin (fun x => (Smooth1 ν ε x : ℂ)) (1 - u * Complex.I) * (X : ℂ) ^ ((1 : ℂ) - u * Complex.I)
  have h_alg := contour_algebra_decomp ν ε X T σ₁ σ₂ u main h_sum h_pull1 h_pull2
  have h_norm := norm_nine_decomp h_alg
  let A := X * Real.log X / (ε * T)
  let B := X ^ (1 - θ T) * φ T / ε
  let K := X ^ σ₂ / ε
  have hA : 0 ≤ A := by
    dsimp [A]
    have : 0 ≤ Real.log X := (Real.log_pos (by linarith)).le
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    have : 0 ≤ φ T := (hφ T hT_le).trans' (by norm_num)
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]; positivity
  have h1 := hJ1 X X_gt ε ε_pos ε_lt_one u T T_gt hTu
  have h2 := hJ2 X X_gt ε ε_pos ε_lt_one u T T_gt hTu hphi
  have h3 := hJ3 X X_gt ε ε_pos ε_lt_one u T T_gt
  have h4 := hJ4 X X_gt ε ε_pos ε_lt_one u T T_gt θ hθT.1 hθT.2 σ₂_lt_σ₁ φ (hφ T hT_le)
  have h5 := hJ5 X X_gt ε ε_pos ε_lt_one u
  have h6 := hJ6 X X_gt ε ε_pos ε_lt_one u T T_gt θ hθT.1 hθT.2 σ₂_lt_σ₁ φ (hφ T hT_le)
  have h7 := hJ7 X X_gt ε ε_pos ε_lt_one u T T_gt
  have h8 := hJ8 X X_gt ε ε_pos ε_lt_one u T T_gt hTu hphi
  have h9 := hJ9 X X_gt ε ε_pos ε_lt_one u T T_gt hTu
  have h1' : ‖J₁ ν ε X T u‖ ≤ C₁ * A := by refine le_trans h1 (le_of_eq ?_); dsimp [A]; ring
  have h2' : ‖J₂ ν ε T X (1 - θ T) u‖ ≤ C₂ * A := by refine le_trans h2 (le_of_eq ?_); dsimp [A]; ring
  have h3' : ‖J₃ ν ε T X (1 - θ T) u‖ ≤ C₃ * B := by refine le_trans h3 (le_of_eq ?_); dsimp [B]; ring
  have h4' : ‖J₄ ν ε X (1 - θ T) σ₂ u‖ ≤ C₄ * B := by refine le_trans h4 (le_of_eq ?_); dsimp [B]; ring
  have h5' : ‖J₅ ν ε X σ₂ u‖ ≤ C₅ * K := by refine le_trans h5 (le_of_eq ?_); dsimp [K]; ring
  have h6' : ‖J₆ ν ε X (1 - θ T) σ₂ u‖ ≤ C₆ * B := by refine le_trans h6 (le_of_eq ?_); dsimp [B]; ring
  have h7' : ‖J₇ ν ε T X (1 - θ T) u‖ ≤ C₇ * B := by refine le_trans h7 (le_of_eq ?_); dsimp [B]; ring
  have h8' : ‖J₈ ν ε T X (1 - θ T) u‖ ≤ C₈ * A := by refine le_trans h8 (le_of_eq ?_); dsimp [A]; ring
  have h9' : ‖J₉ ν ε X T u‖ ≤ C₉ * A := by refine le_trans h9 (le_of_eq ?_); dsimp [A]; ring
  have h_comb := sum_nine_bounds_le (C₁ := C₁) (C₂ := C₂) (C₃ := C₃) (C₄ := C₄) (C₅ := C₅)
    (C₆ := C₆) (C₇ := C₇) (C₈ := C₈) (C₉ := C₉)
    hA hB hK (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    h1' h2' h3' h4' h5' h6' h7' h8' h9'
  exact le_trans h_norm h_comb

lemma sum_primes_bound_of_sub_integral (c C : ℝ) (_hc : 0 < c) (_hC : 0 < C)
    (h_main : ∀ (A B : ℕ) (u : ℝ), 3 ≤ A → A < B → B ≤ 2 * A → 1 ≤ |u| → Real.log |u| ≤ (Real.log A) ^ (5 / 4 : ℝ) →
      ‖(∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + u * Complex.I))) -
          ∫ x in (A : ℝ)..(B : ℝ), (x : ℂ) ^ (-((1 : ℂ) + u * Complex.I)) / (Real.log x : ℂ)‖ ≤
        C * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))) :
    ∀ (A B : ℕ) (u : ℝ), 3 ≤ A → A < B → B ≤ 2 * A → 1 ≤ |u| → Real.log |u| ≤ (Real.log A) ^ (5 / 4 : ℝ) →
      ‖∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + u * Complex.I))‖ ≤
        3 / (|u| * Real.log A) + C * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  intro A B u hA hAB hB2A hu hlogu
  have hA_real : 3 ≤ (A : ℝ) := by exact_mod_cast hA
  have hAB_real : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB.le
  have h_int_bound := norm_integral_cpow_div_log_le (A : ℝ) (B : ℝ) u hA_real hAB_real hu
  have h_diff_bound := h_main A B u hA hAB hB2A hu hlogu
  let S := ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + u * Complex.I))
  let I := ∫ x in (A : ℝ)..(B : ℝ), (x : ℂ) ^ (-((1 : ℂ) + u * Complex.I)) / (Real.log x : ℂ)
  have h_split : (∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + u * Complex.I))) =
      I + (S - I) := by
    change S = I + (S - I)
    ring
  rw [h_split]
  have h_tri := norm_add_le I (S - I)
  refine le_trans h_tri ?_
  exact add_le_add h_int_bound h_diff_bound

/-- Derivative of the weighting function `t ↦ 1 / (t * log t)` on `(1, ∞)`. -/
lemma hasDerivAt_inv_mul_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => ((t : ℂ) * (Real.log t : ℂ))⁻¹)
      (- ((Real.log x : ℂ) + 1) / ((x : ℂ) * (Real.log x : ℂ)) ^ 2) x := by
  have hx_pos : 0 < x := by linarith
  have hx_ne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx_pos)
  have hlog_ne : (Real.log x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos hx))
  have h_prod_ne : (x : ℂ) * (Real.log x : ℂ) ≠ 0 := mul_ne_zero hx_ne hlog_ne
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := hasDerivAt_id x |>.ofReal_comp
  have h_log : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (by linarith)
  have h2 : HasDerivAt (fun t : ℝ => (Real.log t : ℂ)) (x : ℂ)⁻¹ x := by
    have := h_log.ofReal_comp
    push_cast at this ⊢
    exact this
  have h_mul := h1.mul h2
  have h_eval : (1 : ℂ) * (Real.log x : ℂ) + (x : ℂ) * (x : ℂ)⁻¹ = (Real.log x : ℂ) + 1 := by
    rw [one_mul, mul_inv_cancel₀ hx_ne]
  rw [h_eval] at h_mul
  exact h_mul.inv h_prod_ne

/-- Differentiability and integrability of the Abel summation weight `f(t) = 1 / (t * log t)` on `[A, B]`. -/
lemma f_diff_and_int {A B : ℝ} (hA : 3 ≤ A) (_hAB : A ≤ B) :
    (∀ t ∈ Set.Icc A B, DifferentiableAt ℝ (fun t : ℝ => ((t : ℂ) * (Real.log t : ℂ))⁻¹) t) ∧
    MeasureTheory.IntegrableOn (deriv (fun t : ℝ => ((t : ℂ) * (Real.log t : ℂ))⁻¹)) (Set.Icc A B) MeasureTheory.volume := by
  have h_gt1 : ∀ t ∈ Set.Icc A B, 1 < t := by
    intro t ht; linarith [ht.1]
  have h_hasDeriv : ∀ t ∈ Set.Icc A B, HasDerivAt (fun t : ℝ => ((t : ℂ) * (Real.log t : ℂ))⁻¹)
      (- ((Real.log t : ℂ) + 1) / ((t : ℂ) * (Real.log t : ℂ)) ^ 2) t :=
    fun t ht => hasDerivAt_inv_mul_log (h_gt1 t ht)
  have h_diff : ∀ t ∈ Set.Icc A B, DifferentiableAt ℝ (fun t : ℝ => ((t : ℂ) * (Real.log t : ℂ))⁻¹) t :=
    fun t ht => (h_hasDeriv t ht).differentiableAt
  refine ⟨h_diff, ?_⟩
  have h_deriv_eq : ∀ t ∈ Set.Icc A B, deriv (fun t : ℝ => ((t : ℂ) * (Real.log t : ℂ))⁻¹) t =
      (- ((Real.log t : ℂ) + 1) / ((t : ℂ) * (Real.log t : ℂ)) ^ 2) :=
    fun t ht => (h_hasDeriv t ht).deriv
  have h_log_cont : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Set.Icc A B) := by
    apply ContinuousOn.comp continuous_ofReal.continuousOn
    · exact Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_Icc] at hx
        exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1]))
    · intro x _; exact Set.mem_univ _
  have h_cont : ContinuousOn (fun t : ℝ => - ((Real.log t : ℂ) + 1) / ((t : ℂ) * (Real.log t : ℂ)) ^ 2) (Set.Icc A B) := by
    apply ContinuousOn.div
    · exact (h_log_cont.add continuousOn_const).neg
    · apply ContinuousOn.pow
      exact continuous_ofReal.continuousOn.mul h_log_cont
    · intro t ht
      simp only [Set.mem_Icc] at ht
      have ht_pos : 0 < t := by linarith [ht.1]
      have ht_gt1 : 1 < t := by linarith [ht.1]
      have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht_pos)
      have hlog_ne : (Real.log t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos ht_gt1))
      have : (t : ℂ) * (Real.log t : ℂ) ≠ 0 := mul_ne_zero ht_ne hlog_ne
      exact pow_ne_zero 2 this
  have h_int : MeasureTheory.IntegrableOn (fun t : ℝ => - ((Real.log t : ℂ) + 1) / ((t : ℂ) * (Real.log t : ℂ)) ^ 2)
      (Set.Icc A B) MeasureTheory.volume :=
    h_cont.integrableOn_compact isCompact_Icc
  exact h_int.congr_fun (fun t ht => (h_deriv_eq t ht).symm) measurableSet_Icc

/-- Continuous Abel summation formula applied to the twisted von Mangoldt sequence. -/
lemma abel_sum_psi (u : ℝ) (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) :
    let c : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)
    let f : ℝ → ℂ := fun t => ((t : ℂ) * (Real.log t : ℂ))⁻¹
    ∑ k ∈ Finset.Ioc A B, f (k : ℝ) * c k =
      f (B : ℝ) * ∑ k ∈ Finset.Icc 0 B, c k - f (A : ℝ) * ∑ k ∈ Finset.Icc 0 A, c k -
        ∫ t in Set.Ioc (A : ℝ) (B : ℝ), deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k := by
  intro c f
  have hA_real : 0 ≤ (A : ℝ) := by positivity
  have hAB_real : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have h_diff_int := f_diff_and_int (by exact_mod_cast hA) hAB_real
  have h_abel := sum_mul_eq_sub_sub_integral_mul c (f := f) hA_real hAB_real h_diff_int.1 h_diff_int.2
  have h_floor_A : ⌊(A : ℝ)⌋₊ = A := Nat.floor_natCast A
  have h_floor_B : ⌊(B : ℝ)⌋₊ = B := Nat.floor_natCast B
  rw [h_floor_A, h_floor_B] at h_abel
  exact h_abel

/-- Derivative of the main term `M(t) = t^(1 - iu) / (1 - iu)` is `t^(-iu)`. -/
lemma hasDerivAt_main_term (u : ℝ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (t : ℂ) ^ ((1 : ℂ) - (u : ℂ) * I) / ((1 : ℂ) - (u : ℂ) * I))
      ((x : ℂ) ^ (-(u : ℂ) * I)) x := by
  have hs : (x : ℂ) ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    simpa using hx
  have h1 : HasDerivAt (fun z : ℂ => z ^ ((1 : ℂ) - (u : ℂ) * I))
      (((1 : ℂ) - (u : ℂ) * I) * (x : ℂ) ^ ((1 : ℂ) - (u : ℂ) * I - 1)) (x : ℂ) := by
    simpa using (hasDerivAt_id (x : ℂ)).cpow_const hs (c := (1 : ℂ) - (u : ℂ) * I)
  have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) ^ ((1 : ℂ) - (u : ℂ) * I))
      (((1 : ℂ) - (u : ℂ) * I) * (x : ℂ) ^ ((1 : ℂ) - (u : ℂ) * I - 1)) x := h1.comp_ofReal
  have h_w_ne : (1 : ℂ) - (u : ℂ) * I ≠ 0 := by
    intro h
    have := congr_arg Complex.re h
    simp only [sub_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, sub_zero, zero_re] at this
    linarith
  have h3 := h2.div_const ((1 : ℂ) - (u : ℂ) * I)
  have heq : ((1 : ℂ) - (u : ℂ) * I) * (x : ℂ) ^ ((1 : ℂ) - (u : ℂ) * I - 1) / ((1 : ℂ) - (u : ℂ) * I) =
      (x : ℂ) ^ (-(u : ℂ) * I) := by
    rw [mul_div_cancel_left₀ _ h_w_ne]
    congr 1
    ring
  rw [heq] at h3
  exact h3

/-- Integration by parts formula for the continuous main term. -/
lemma ibp_main_term (u : ℝ) (A B : ℝ) (hA : 3 ≤ A) (hAB : A ≤ B) :
    let M : ℝ → ℂ := fun t => (t : ℂ) ^ ((1 : ℂ) - (u : ℂ) * I) / ((1 : ℂ) - (u : ℂ) * I)
    let f : ℝ → ℂ := fun t => ((t : ℂ) * (Real.log t : ℂ))⁻¹
    let f' : ℝ → ℂ := fun t => - ((Real.log t : ℂ) + 1) / ((t : ℂ) * (Real.log t : ℂ)) ^ 2
    ∫ x in A..B, (x : ℂ) ^ (-((1 : ℂ) + u * Complex.I)) / (Real.log x : ℂ) =
      f B * M B - f A * M A - ∫ x in A..B, f' x * M x := by
  intro M f f'
  have hf_deriv : ∀ x ∈ uIcc A B, HasDerivAt f (f' x) x := by
    intro x hx
    rw [uIcc_of_le hAB, Set.mem_Icc] at hx
    exact hasDerivAt_inv_mul_log (by linarith [hx.1])
  have hM_deriv : ∀ x ∈ uIcc A B, HasDerivAt M ((x : ℂ) ^ (-(u : ℂ) * I)) x := by
    intro x hx
    rw [uIcc_of_le hAB, Set.mem_Icc] at hx
    exact hasDerivAt_main_term u x (by linarith [hx.1])
  have hf'_cont : ContinuousOn f' (uIcc A B) := by
    rw [uIcc_of_le hAB]
    have h_log_cont : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Set.Icc A B) := by
      apply ContinuousOn.comp continuous_ofReal.continuousOn
      · exact Real.continuousOn_log.mono (fun x hx => by
          simp only [Set.mem_Icc] at hx
          exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1]))
      · intro x _; exact Set.mem_univ _
    apply ContinuousOn.div
    · exact (h_log_cont.add continuousOn_const).neg
    · apply ContinuousOn.pow
      exact continuous_ofReal.continuousOn.mul h_log_cont
    · intro t ht
      simp only [Set.mem_Icc] at ht
      have ht_pos : 0 < t := by linarith [ht.1]
      have ht_gt1 : 1 < t := by linarith [ht.1]
      have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht_pos)
      have hlog_ne : (Real.log t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos ht_gt1))
      have : (t : ℂ) * (Real.log t : ℂ) ≠ 0 := mul_ne_zero ht_ne hlog_ne
      exact pow_ne_zero 2 this
  have hM'_cont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(u : ℂ) * I)) (uIcc A B) := by
    have h_sub : uIcc A B ⊆ Set.Ioi 0 := by
      rw [uIcc_of_le hAB]
      intro x hx; simp only [Set.mem_Icc, Set.mem_Ioi] at hx ⊢; linarith [hx.1]
    refine ContinuousOn.mono ?_ h_sub
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hs : (x : ℂ) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left; simpa using hx
    exact ((hasDerivAt_id (x : ℂ)).cpow_const hs (c := -(u : ℂ) * I)).comp_ofReal.continuousAt
  have hf'_int : IntervalIntegrable f' volume A B := hf'_cont.intervalIntegrable
  have hM'_int : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-(u : ℂ) * I)) volume A B := hM'_cont.intervalIntegrable
  have h_ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hf_deriv hM_deriv hf'_int hM'_int
  have h_integrand : (fun (x : ℝ) => (x : ℂ) ^ (-((1 : ℂ) + u * Complex.I)) / (Real.log x : ℂ)) =
      (fun x => f x * (x : ℂ) ^ (-(u : ℂ) * I)) := by
    ext x
    dsimp [f]
    by_cases hx : x = 0
    · simp [hx]
    · have hx_c_ne : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx
      have h_cpow : (x : ℂ) ^ (-((1 : ℂ) + u * I)) = (x : ℂ)⁻¹ * (x : ℂ) ^ (-(u : ℂ) * I) := by
        rw [show -((1 : ℂ) + u * I) = -1 + -(u : ℂ) * I by ring]
        rw [cpow_add _ _ hx_c_ne, cpow_neg_one]
      rw [h_cpow]
      ring
  rw [h_integrand]
  exact h_ibp

/-- Derivative of the iterated logarithm `t ↦ log (log t)`. -/
lemma hasDerivAt_log_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => Real.log (Real.log t)) (x * Real.log x)⁻¹ x := by
  have hx_pos : 0 < x := by linarith
  have hlog_pos : 0 < Real.log x := Real.log_pos hx
  have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx_pos)
  have h2 : HasDerivAt Real.log (Real.log x)⁻¹ (Real.log x) := Real.hasDerivAt_log (ne_of_gt hlog_pos)
  have h_comp := h2.comp x h1
  have heq : (Real.log x)⁻¹ * x⁻¹ = (x * Real.log x)⁻¹ := by
    rw [mul_inv, mul_comm]
  rw [heq] at h_comp
  exact h_comp

/-- Integral of `1 / (x * log x)` over `[A, B]` is at most `1` for `B ≤ 2A`. -/
lemma integral_inv_mul_log_le {A B : ℝ} (hA : 3 ≤ A) (hAB : A ≤ B) (hB2A : B ≤ 2 * A) :
    ∫ x in A..B, (x * Real.log x)⁻¹ ≤ 1 := by
  have h_gt1 : ∀ x ∈ uIcc A B, 1 < x := by
    intro x hx
    rw [uIcc_of_le hAB, Set.mem_Icc] at hx
    linarith [hx.1]
  have h_deriv : ∀ x ∈ uIcc A B, HasDerivAt (fun t => Real.log (Real.log t)) (x * Real.log x)⁻¹ x :=
    fun x hx => hasDerivAt_log_log (h_gt1 x hx)
  have h_cont : ContinuousOn (fun x => (x * Real.log x)⁻¹) (uIcc A B) := by
    rw [uIcc_of_le hAB]
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul (Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_Icc] at hx
        exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1])))
    · intro x hx
      simp only [Set.mem_Icc] at hx
      have hx_pos : 0 < x := by linarith [hx.1]
      have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
      exact mul_ne_zero (ne_of_gt hx_pos) (ne_of_gt hlog_pos)
  have h_int : IntervalIntegrable (fun x => (x * Real.log x)⁻¹) volume A B := h_cont.intervalIntegrable
  have h_eval := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int
  rw [h_eval]
  have hA_pos : 0 < A := by linarith
  have hB_pos : 0 < B := by linarith
  have hlogA_pos : 0 < Real.log A := Real.log_pos (by linarith)
  have hlogB_pos : 0 < Real.log B := Real.log_pos (by linarith)
  have h_diff_log : Real.log (Real.log B) - Real.log (Real.log A) = Real.log (Real.log B / Real.log A) := by
    rw [Real.log_div (ne_of_gt hlogB_pos) (ne_of_gt hlogA_pos)]
  rw [h_diff_log]
  have hlogB_le : Real.log B ≤ Real.log (2 * A) := Real.log_le_log hB_pos hB2A
  have hlog2A : Real.log (2 * A) = Real.log 2 + Real.log A := Real.log_mul (by norm_num) (ne_of_gt hA_pos)
  rw [hlog2A] at hlogB_le
  have h_quot_le : Real.log B / Real.log A ≤ (Real.log 2 + Real.log A) / Real.log A :=
    div_le_div_of_nonneg_right hlogB_le hlogA_pos.le
  have h_split : (Real.log 2 + Real.log A) / Real.log A = Real.log 2 / Real.log A + 1 := by
    rw [add_div, div_self (ne_of_gt hlogA_pos)]
  rw [h_split] at h_quot_le
  have h_log_le_sub : Real.log (Real.log B / Real.log A) ≤ Real.log B / Real.log A - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hlogB_pos hlogA_pos)
  refine le_trans h_log_le_sub ?_
  have h1 : Real.log B / Real.log A - 1 ≤ Real.log 2 / Real.log A := by linarith [h_quot_le]
  refine le_trans h1 ?_
  have hlog3_gt1 : 1 < Real.log 3 := by
    have : (Real.exp 1 : ℝ) < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_exp] at this
  have hlogA_ge : Real.log 3 ≤ Real.log A := Real.log_le_log (by norm_num) hA
  have hlogA_gt1 : 1 < Real.log A := lt_of_lt_of_le hlog3_gt1 hlogA_ge
  have hlog2_lt1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have : Real.log 2 / Real.log A ≤ 1 := by
    rw [div_le_one₀ hlogA_pos]
    linarith
  exact this

/-- Integral of `x * ‖f'(x)‖` is bounded by 2 for `3 ≤ A ≤ B ≤ 2A`. -/
lemma integral_x_mul_norm_f'_le {A B : ℝ} (hA : 3 ≤ A) (hAB : A ≤ B) (hB2A : B ≤ 2 * A) :
    ∫ x in A..B, x * ‖- ((Real.log x : ℂ) + 1) / ((x : ℂ) * (Real.log x : ℂ)) ^ 2‖ ≤ 2 := by
  have h_eq_on : Set.EqOn (fun x => x * ‖- ((Real.log x : ℂ) + 1) / ((x : ℂ) * (Real.log x : ℂ)) ^ 2‖)
      (fun x => (x * Real.log x)⁻¹ + x⁻¹ / (Real.log x ^ 2)) (uIcc A B) := by
    intro x hx
    rw [uIcc_of_le hAB, Set.mem_Icc] at hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have hx_gt1 : 1 < x := by linarith [hx.1]
    have hlog_pos : 0 < Real.log x := Real.log_pos hx_gt1
    have h_norm_top : ‖- ((Real.log x : ℂ) + 1)‖ = Real.log x + 1 := by
      rw [norm_neg]
      have : (Real.log x : ℂ) + 1 = ((Real.log x + 1 : ℝ) : ℂ) := by simp
      rw [this, Complex.norm_real, Real.norm_of_nonneg]
      linarith
    have h_norm_bot : ‖((x : ℂ) * (Real.log x : ℂ)) ^ 2‖ = (x * Real.log x) ^ 2 := by
      rw [norm_pow]
      have : (x : ℂ) * (Real.log x : ℂ) = ((x * Real.log x : ℝ) : ℂ) := by simp
      rw [this, Complex.norm_real, Real.norm_of_nonneg]
      positivity
    have h_norm_div : ‖- ((Real.log x : ℂ) + 1) / ((x : ℂ) * (Real.log x : ℂ)) ^ 2‖ =
        (Real.log x + 1) / (x * Real.log x) ^ 2 := by
      rw [norm_div, h_norm_top, h_norm_bot]
    dsimp
    rw [h_norm_div]
    have h_cancel : x * ((Real.log x + 1) / (x * Real.log x) ^ 2) = (Real.log x + 1) / (x * Real.log x ^ 2) := by
      have : (x * Real.log x) ^ 2 = x * (x * Real.log x ^ 2) := by ring
      rw [this, mul_div_assoc', mul_div_mul_left _ _ (ne_of_gt hx_pos)]
    rw [h_cancel]
    have h_split : (Real.log x + 1) / (x * Real.log x ^ 2) =
        Real.log x / (x * Real.log x ^ 2) + 1 / (x * Real.log x ^ 2) := by
      rw [add_div]
    rw [h_split]
    have h1 : Real.log x / (x * Real.log x ^ 2) = (x * Real.log x)⁻¹ := by
      have : x * Real.log x ^ 2 = (Real.log x) * (x * Real.log x) := by ring
      rw [this]
      nth_rw 1 [← mul_one (Real.log x)]
      rw [mul_div_mul_left _ _ (ne_of_gt hlog_pos), one_div]
    have h2 : 1 / (x * Real.log x ^ 2) = x⁻¹ / (Real.log x ^ 2) := by
      have : 1 / (x * Real.log x ^ 2) = (x * Real.log x ^ 2)⁻¹ := one_div _
      rw [this, mul_inv, div_eq_mul_inv, mul_comm]
    rw [h1, h2]
  have h_int_eq : (∫ x in A..B, x * ‖- ((Real.log x : ℂ) + 1) / ((x : ℂ) * (Real.log x : ℂ)) ^ 2‖) =
      ∫ x in A..B, ((x * Real.log x)⁻¹ + x⁻¹ / (Real.log x ^ 2)) :=
    intervalIntegral.integral_congr h_eq_on
  rw [h_int_eq]
  have h_cont1 : ContinuousOn (fun x => (x * Real.log x)⁻¹) (uIcc A B) := by
    rw [uIcc_of_le hAB]
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul (Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_Icc] at hx
        exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1])))
    · intro x hx
      simp only [Set.mem_Icc] at hx
      have hx_pos : 0 < x := by linarith [hx.1]
      have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
      exact mul_ne_zero (ne_of_gt hx_pos) (ne_of_gt hlog_pos)
  have h_cont2 : ContinuousOn (fun x => x⁻¹ / (Real.log x ^ 2)) (uIcc A B) := by
    rw [uIcc_of_le hAB]
    apply ContinuousOn.div
    · exact continuousOn_inv₀.mono (fun x hx => by
        simp only [Set.mem_Icc] at hx; exact ne_of_gt (by linarith [hx.1]))
    · apply ContinuousOn.pow
      exact Real.continuousOn_log.mono (fun x hx => by
        simp only [Set.mem_Icc] at hx; exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1]))
    · intro x hx
      simp only [Set.mem_Icc] at hx
      have : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith [hx.1]))
      exact pow_ne_zero 2 this
  have h_add := intervalIntegral.integral_add (μ := volume) h_cont1.intervalIntegrable h_cont2.intervalIntegrable
  rw [h_add]
  have h1 := integral_inv_mul_log_le hA hAB hB2A
  have h_deriv2 : ∀ x ∈ uIcc A B, HasDerivAt (fun t => - (Real.log t)⁻¹) (x⁻¹ / (Real.log x ^ 2)) x := by
    intro x hx
    rw [uIcc_of_le hAB, Set.mem_Icc] at hx
    have hx_gt : 1 < x := by linarith [hx.1]
    have hlog : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx_gt)
    have ht_pos : 0 < x := by linarith [hx.1]
    have h_log : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt ht_pos)
    have h1 : HasDerivAt (fun t => (Real.log t)⁻¹) (- x⁻¹ / (Real.log x ^ 2)) x := h_log.inv hlog
    have h2 := h1.neg
    have heq : - (- x⁻¹ / (Real.log x ^ 2)) = x⁻¹ / (Real.log x ^ 2) := by rw [neg_div, neg_neg]
    rw [heq] at h2
    exact h2
  have h_eval2 := intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv2 h_cont2.intervalIntegrable
  rw [h_eval2]
  have hlogA_pos : 0 < Real.log A := Real.log_pos (by linarith)
  have hlogB_pos : 0 < Real.log B := Real.log_pos (by linarith)
  have : - (Real.log B)⁻¹ - - (Real.log A)⁻¹ = (Real.log A)⁻¹ - (Real.log B)⁻¹ := by ring
  rw [this]
  have h_invB_pos : 0 < (Real.log B)⁻¹ := by positivity
  have h_logA_ge : 1 < Real.log A := by
    have hlog3_gt1 : 1 < Real.log 3 := by
      have : (Real.exp 1 : ℝ) < 3 := by linarith [Real.exp_one_lt_d9]
      have := Real.log_lt_log (by positivity) this
      rwa [Real.log_exp] at this
    have := Real.log_le_log (by norm_num) hA
    linarith
  have h_invA_le1 : (Real.log A)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hlogA_pos]
    linarith
  have h2 : (Real.log A)⁻¹ - (Real.log B)⁻¹ ≤ 1 := by linarith
  linarith

/-- Bound on the boundary terms and integral error factor in Abel summation: `‖f B‖ B + ‖f A‖ A + ∫ x ‖f' x‖ ≤ 4`. -/
lemma boundary_and_integral_error_le {A B : ℝ} (hA : 3 ≤ A) (hAB : A ≤ B) (hB2A : B ≤ 2 * A) :
    let f : ℝ → ℂ := fun t => ((t : ℂ) * (Real.log t : ℂ))⁻¹
    let f' : ℝ → ℂ := fun t => - ((Real.log t : ℂ) + 1) / ((t : ℂ) * (Real.log t : ℂ)) ^ 2
    ‖f B‖ * B + ‖f A‖ * A + ∫ x in A..B, x * ‖f' x‖ ≤ 4 := by
  intro f f'
  have hA_pos : 0 < A := by linarith
  have hB_pos : 0 < B := by linarith
  have hA_gt1 : 1 < A := by linarith
  have hB_gt1 : 1 < B := by linarith
  have hlogA_pos : 0 < Real.log A := Real.log_pos hA_gt1
  have hlogB_pos : 0 < Real.log B := Real.log_pos hB_gt1
  have hlog3_gt1 : 1 < Real.log 3 := by
    have : (Real.exp 1 : ℝ) < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_exp] at this
  have hlogA_gt1 : 1 < Real.log A := lt_of_lt_of_le hlog3_gt1 (Real.log_le_log (by norm_num) hA)
  have hlogB_ge : Real.log A ≤ Real.log B := Real.log_le_log hA_pos hAB
  have _hlogB_gt1 : 1 < Real.log B := lt_of_lt_of_le hlogA_gt1 hlogB_ge
  have h_norm_fB : ‖f B‖ * B = (Real.log B)⁻¹ := by
    dsimp [f]
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hB_pos.le,
      Complex.norm_real, Real.norm_of_nonneg hlogB_pos.le]
    have : (B * Real.log B)⁻¹ * B = (Real.log B)⁻¹ * (B⁻¹ * B) := by
      rw [mul_inv, mul_comm B⁻¹, mul_assoc]
    rw [this, inv_mul_cancel₀ (ne_of_gt hB_pos), mul_one]
  have h_norm_fA : ‖f A‖ * A = (Real.log A)⁻¹ := by
    dsimp [f]
    rw [norm_inv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA_pos.le,
      Complex.norm_real, Real.norm_of_nonneg hlogA_pos.le]
    have : (A * Real.log A)⁻¹ * A = (Real.log A)⁻¹ * (A⁻¹ * A) := by
      rw [mul_inv, mul_comm A⁻¹, mul_assoc]
    rw [this, inv_mul_cancel₀ (ne_of_gt hA_pos), mul_one]
  have h_fB_le1 : ‖f B‖ * B ≤ 1 := by
    rw [h_norm_fB, inv_le_one₀ hlogB_pos]
    linarith
  have h_fA_le1 : ‖f A‖ * A ≤ 1 := by
    rw [h_norm_fA, inv_le_one₀ hlogA_pos]
    linarith
  have h_int_le2 := integral_x_mul_norm_f'_le hA hAB hB2A
  linarith

end Erdos1201.MR

