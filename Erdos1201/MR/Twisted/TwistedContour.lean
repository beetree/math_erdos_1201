/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gemini

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Erdos1201.Vendor.NumberTheory.PNT.MediumPNT
import Erdos1201.MR.Twisted.TwistedChebyshev

namespace Erdos1201.MR

open Complex Real MeasureTheory Set Filter Function

/-!
# Twisted Contour Decompositions for Smoothed Chebyshev Functions

This module provides the twisted contour shift identities `twistedChebyshevPull1` and
`twistedChebyshevPull2`, adapting `SmoothedChebyshevPull1` and `SmoothedChebyshevPull2`
from `Erdos1201.Vendor.NumberTheory.PNT.MediumPNT` to the twisted setting with an additional
phase parameter `u : ℝ`.
-/

/-- The lower vertical tail contour integral in the twisted Chebyshev decomposition. -/
noncomputable def J₁ (ν : ℝ → ℝ) (ε X T u : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      twistedIntegrand ν ε X u ((1 + (Real.log X)⁻¹) + t * I)))

/-- The lower horizontal cross-segment contour integral from `σ₁` to `1 + 1/log X` at height `-T`. -/
noncomputable def J₂ (ν : ℝ → ℝ) (ε T X σ₁ u : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    twistedIntegrand ν ε X u (σ - T * I)))

/-- The vertical line segment contour integral along `Re s = σ₁` from `-T` to `T`. -/
noncomputable def J₃₇ (ν : ℝ → ℝ) (ε T X σ₁ u : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    twistedIntegrand ν ε X u (σ₁ + t * I)))

/-- The upper horizontal cross-segment contour integral from `σ₁` to `1 + 1/log X` at height `T`. -/
noncomputable def J₈ (ν : ℝ → ℝ) (ε T X σ₁ u : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    twistedIntegrand ν ε X u (σ + T * I)))

/-- The upper vertical tail contour integral in the twisted Chebyshev decomposition. -/
noncomputable def J₉ (ν : ℝ → ℝ) (ε X T u : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      twistedIntegrand ν ε X u ((1 + (Real.log X)⁻¹) + t * I)))

/-- The lower intermediate vertical contour integral along `Re s = σ₁` from `-T` to `-3`. -/
noncomputable def J₃ (ν : ℝ → ℝ) (ε T X σ₁ u : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    twistedIntegrand ν ε X u (σ₁ + t * I)))

/-- The upper intermediate vertical contour integral along `Re s = σ₁` from `3` to `T`. -/
noncomputable def J₇ (ν : ℝ → ℝ) (ε T X σ₁ u : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    twistedIntegrand ν ε X u (σ₁ + t * I)))

/-- The lower horizontal connecting contour integral from `σ₂` to `σ₁` at height `-3`. -/
noncomputable def J₄ (ν : ℝ → ℝ) (ε X σ₁ σ₂ u : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    twistedIntegrand ν ε X u (σ - 3 * I)))

/-- The upper horizontal connecting contour integral from `σ₂` to `σ₁` at height `3`. -/
noncomputable def J₆ (ν : ℝ → ℝ) (ε X σ₁ σ₂ u : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    twistedIntegrand ν ε X u (σ + 3 * I)))

/-- The central vertical contour integral along `Re s = σ₂` from `-3` to `3`. -/
noncomputable def J₅ (ν : ℝ → ℝ) (ε X σ₂ u : ℝ) : ℂ :=
  (1 / (2 * π * I)) *
    (I * (∫ t in (-3)..3, twistedIntegrand ν ε X u (σ₂ + t * I)))

/-- Real part of a complex number shifted by a purely imaginary shift is preserved. -/
lemma re_sub_u_I (s : ℂ) (u : ℝ) : (s - u * Complex.I).re = s.re := by
  simp only [sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, sub_zero]

/-- Shifted Mellin transform of a smooth function is differentiable in the open right half-plane. -/
lemma mellin_shift_diffAt (ν : ℝ → ℝ) {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) (diffν : ContDiff ℝ 1 ν) (u : ℝ)
    {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => mellin (fun x => (Smooth1 ν ε x : ℂ)) (z - u * Complex.I)) s := by
  have h1 : DifferentiableAt ℂ (mellin (fun x => (Smooth1 ν ε x : ℂ))) (s - u * Complex.I) := by
    apply Smooth1MellinDifferentiable diffν suppν ⟨ε_pos, ε_lt_one⟩ νnonneg mass_one
    rw [re_sub_u_I]
    exact hs
  have h2 : DifferentiableAt ℂ (fun z : ℂ => z - u * Complex.I) s := by fun_prop
  exact DifferentiableAt.comp (f := fun z => z - u * Complex.I) (g := mellin (fun x => (Smooth1 ν ε x : ℂ))) s h1 h2

/-- Shifted complex power of a positive real `X` is differentiable everywhere. -/
lemma cpow_shift_diffAt (X u : ℝ) (X_gt : 3 < X) (s : ℂ) :
    DifferentiableAt ℂ (fun z => (X : ℂ) ^ (z - u * Complex.I)) s := by
  apply DifferentiableAt.const_cpow (by fun_prop)
  left
  norm_cast
  linarith

/-- The shifted Mellin factor is continuous along vertical lines in the right half-plane. -/
lemma mellin_shift_contAt (ν : ℝ → ℝ) {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) (diffν : ContDiff ℝ 1 ν) (u : ℝ)
    {σ₁ : ℝ} (hσ₁ : 0 < σ₁) (t : ℝ) :
    ContinuousAt (fun y : ℝ => mellin (fun x => (Smooth1 ν ε x : ℂ)) (σ₁ + y * I - u * I)) t := by
  have hs : 0 < (σ₁ + t * I).re := by simp [hσ₁]
  have hd := mellin_shift_diffAt ν ε_pos ε_lt_one suppν νnonneg mass_one diffν u hs
  have hr := realDiff_of_complexDiff (σ₁ + t * I) hd
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at hr
  exact hr

/-- The shifted power factor is continuous along vertical lines. -/
lemma cpow_shift_contAt (X u : ℝ) (X_gt : 3 < X) {σ₁ : ℝ} (t : ℝ) :
    ContinuousAt (fun y : ℝ => (X : ℂ) ^ (σ₁ + y * I - u * I)) t := by
  have hd := cpow_shift_diffAt X u X_gt (σ₁ + t * I)
  have hr := realDiff_of_complexDiff (σ₁ + t * I) hd
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at hr
  exact hr

/-- Helper relating real differentiability along vertical lines to complex differentiability. -/
theorem realDiff_of_complexDiff' {f : ℂ → ℂ} (s : ℂ) (hf : DifferentiableAt ℂ f s) :
    ContinuousAt (fun (x : ℝ) ↦ f (s.re + x * I)) s.im := by
  apply ContinuousAt.comp _ (by fun_prop)
  convert hf.continuousAt
  simp

/-- Integrability of the twisted integrand along a vertical line `Re s = σ₀ > 1`. -/
theorem twistedChebyshevPull1_aux_integrable (ν : ℝ → ℝ) {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X)
    {σ₀ : ℝ} (σ₀_gt : 1 < σ₀) (σ₀_le_2 : σ₀ ≤ 2)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ (x : ℝ) in Set.Ioi 0, ν x / x = 1)
    (diffν : ContDiff ℝ 1 ν) (u : ℝ) :
    Integrable (fun (t : ℝ) ↦
      twistedIntegrand ν ε X u (σ₀ + (t : ℂ) * I)) volume := by
  obtain ⟨C, C_pos, hC⟩ := dlog_riemannZeta_bdd_on_vertical_lines σ₀_gt
  let c : ℝ := C * X ^ σ₀
  have h_bound : ∀ t, ‖(fun (t : ℝ) ↦ (- deriv riemannZeta (σ₀ + (t : ℂ) * I)) /
    riemannZeta (σ₀ + (t : ℂ) * I) *
    (X : ℂ) ^ (σ₀ + (t : ℂ) * I - u * I)) t‖ ≤ c := by
    intro t
    simp only [Complex.norm_mul, c]
    gcongr
    · convert! hC t using 1
      simp
    · rw [Complex.norm_cpow_eq_rpow_re_of_nonneg]
      · simp
      · linarith
      · simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, add_zero, sub_zero, ne_eq]
        linarith
  have h_shift : (fun t : ℝ => mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ₀ + (t - u : ℝ) * I)) =
      fun t : ℝ => (fun y : ℝ => mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ₀ + y * I)) (t - u) := rfl
  have h_base_int := SmoothedChebyshevDirichlet_aux_integrable diffν νnonneg suppν mass_one
    ε_pos ε_lt_one σ₀_gt σ₀_le_2
  have h_shifted_int : Integrable (fun t : ℝ => mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ₀ + (t - u : ℝ) * I)) := by
    rw [h_shift]
    exact h_base_int.comp_sub_right u
  have h_eq : (fun t : ℝ => twistedIntegrand ν ε X u (σ₀ + (t : ℂ) * I)) =
      fun t : ℝ => ((- deriv riemannZeta (σ₀ + (t : ℂ) * I)) / riemannZeta (σ₀ + (t : ℂ) * I) *
        (X : ℂ) ^ (σ₀ + (t : ℂ) * I - u * I)) *
        mellin (fun x ↦ (Smooth1 ν ε x : ℂ)) (σ₀ + (t - u : ℝ) * I) := by
    ext t
    unfold twistedIntegrand
    have : (σ₀ : ℂ) + (t : ℂ) * I - (u : ℂ) * I = (σ₀ : ℂ) + ((t - u : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this]
    ring
  rw [h_eq]
  refine h_shifted_int.bdd_mul (c := c) ?_ (ae_of_all _ h_bound)
  apply Continuous.aestronglyMeasurable
  rw [← continuousOn_univ]
  intro t _
  let s := σ₀ + (t : ℂ) * I
  have s_ne_one : s ≠ 1 := by
    intro h
    have : σ₀ = 1 := by
      have := congr_arg Complex.re h
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, one_re, s] at this
      exact this
    linarith [σ₀_gt]
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.mul
  · have diffζ := differentiableAt_riemannZeta s_ne_one
    apply ContinuousAt.div
    · apply ContinuousAt.neg
      have : DifferentiableAt ℂ (fun s ↦ deriv riemannZeta s) s :=
        differentiableAt_deriv_riemannZeta s_ne_one
      convert realDiff_of_complexDiff' (s := σ₀ + (t : ℂ) * I) this <;> simp
    · convert realDiff_of_complexDiff' (s := σ₀ + (t : ℂ) * I) diffζ <;> simp
    · apply riemannZeta_ne_zero_of_one_lt_re
      simp [σ₀_gt]
  · apply ContinuousAt.comp _ (by fun_prop)
    apply continuousAt_const_cpow
    norm_cast
    linarith

/-- First contour shift for the twisted smoothed Chebyshev function, pulling the contour from
the line `Re s = 1 + 1/log X` across the simple pole at `s = 1` to `Re s = σ₁`. -/
theorem twistedChebyshevPull1 (ν : ℝ → ℝ) {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1) (X : ℝ) (X_gt : 3 < X) {T : ℝ} (T_pos : 0 < T) {σ₁ : ℝ} (σ₁_pos : 0 < σ₁) (σ₁_lt_one : σ₁ < 1)
    (holoOn : DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc σ₁ 2) ×ℂ (Set.Icc (-T) T) \ {1}))
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) (diffν : ContDiff ℝ 1 ν) (u : ℝ) :
    twistedChebyshev ν ε X u = J₁ ν ε X T u - J₂ ν ε T X σ₁ u + J₃₇ ν ε T X σ₁ u + J₈ ν ε T X σ₁ u + J₉ ν ε X T u
      + mellin (fun x => (Smooth1 ν ε x : ℂ)) (1 - u * Complex.I) * (X : ℂ) ^ ((1 : ℂ) - u * Complex.I) := by
  unfold twistedChebyshev
  unfold VerticalIntegral'
  have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
    nth_rewrite 1 [← add_zero 1]
    bound
  have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
    rw [← one_add_one_eq_two]
    gcongr
    exact inv_lt_one_of_one_lt₀ <| logt_gt_one X_gt.le
  have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
  rw [verticalIntegral_split_three (a := -T) (b := T)]
  swap
  · exact twistedChebyshevPull1_aux_integrable ν ε_pos ε_lt_one X_gt X_eq_gt_one
      X_eq_le_two suppν νnonneg mass_one diffν u
  · have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by simp
    unfold J₁
    simp only [smul_eq_mul, mul_add, temp, sub_eq_add_neg, add_assoc, add_left_cancel_iff]
    unfold J₉
    nth_rewrite 6 [add_comm]
    simp only [← add_assoc]
    rw [add_right_cancel_iff,
        ← add_right_inj (1 / (2 * ↑π * I) *
          -VIntegral (twistedIntegrand ν ε X u) (1 + (Real.log X)⁻¹) (-T) T),
        ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
    unfold VIntegral J₂ J₃₇ J₈
    simp only [smul_eq_mul, temp, ← add_assoc, ← mul_neg, ← mul_add]
    let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
      twistedIntegrand ν ε X u ((x : ℝ) + (y : ℝ) * I)
    let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
    have : ∫ (y : ℝ) in -T..T,
        twistedIntegrand ν ε X u (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
        ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
        unfold fTempRR
        simp only [temp]
    rw [this]
    have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        twistedIntegrand ν ε X u (↑σ₀ - ↑T * I) =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
        unfold fTempRR
        simp only [ofReal_neg, neg_mul, sub_eq_add_neg]
    rw [this]
    have : ∫ (t : ℝ) in -T..T,
        twistedIntegrand ν ε X u (↑σ₁ + ↑t * I) =
        ∫ (y : ℝ) in -T..T, fTempRR σ₁ y := rfl
    rw [this]
    have : ∫ (σ₀ : ℝ) in σ₁..1 + (Real.log X)⁻¹,
        twistedIntegrand ν ε X u (↑σ₀ + ↑T * I) =
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T := rfl
    rw [this]
    have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
        -∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
        I * ∫ (y : ℝ) in -T..T, fTempRR σ₁ y) +
        ∫ (x : ℝ) in σ₁..1 + (Real.log X)⁻¹, fTempRR x T =
        -(2 * ↑π * I) * RectangleIntegral' fTempC (σ₁ - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
        unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral fTempC
        simp only [mul_neg, one_div, mul_inv_rev, inv_I, neg_mul, sub_im, ofReal_im, mul_im,
          ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_sub, ofReal_neg, add_re,
          neg_re, mul_re, sub_self, neg_zero, add_im, neg_im, zero_add, sub_re, sub_zero,
          ofReal_inv, one_re, inv_re, normSq_ofReal, div_self_mul_self', one_im, inv_im,
          zero_div, ofReal_add, ofReal_one, smul_eq_mul, neg_neg]
        ring_nf
        simp only [I_sq, neg_mul, one_mul, ne_eq, ofReal_eq_zero, pi_ne_zero, not_false_eq_true,
          mul_inv_cancel_right₀, sub_neg_eq_add, I_pow_three]
        ring_nf
    rw [this]
    field_simp
    rw [mul_comm, eq_comm, neg_add_eq_zero]

    have pInRectangleInterior :
        (Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
      refine rectangle_mem_nhds_iff.mpr ?_
      refine mem_reProdIm.mpr ?_
      simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        sub_zero, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero,
        sub_im, mul_im, zero_sub, add_im, one_im, inv_im, neg_zero, zero_div, zero_add]
      constructor
      · unfold uIoo
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        exact mem_Ioo.mpr ⟨σ₁_lt_one, (by linarith)⟩
      · unfold uIoo
        rw [min_eq_left (by linarith), max_eq_right (by linarith)]
        exact mem_Ioo.mpr ⟨(by linarith), (by linarith)⟩

    apply ResidueTheoremOnRectangleWithSimplePole'
    · simp; linarith
    · simp; linarith
    · simp only [one_div]
      exact pInRectangleInterior
    · apply DifferentiableOn.mul
      · apply DifferentiableOn.mul
        · simp only [re_add_im]
          have : (fun z ↦ -deriv riemannZeta z / riemannZeta z) = -(fun s => deriv riemannZeta s / riemannZeta s) := by ext; simp; ring
          rw [this]
          apply DifferentiableOn.neg
          apply holoOn.mono
          apply Set.sdiff_subset_sdiff_left
          apply reProdIm_subset_iff'.mpr
          left
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
            div_self_mul_self', add_zero, sub_im, mul_im, zero_sub, add_im, one_im, inv_im,
            neg_zero, zero_div, zero_add]
          constructor <;> apply uIcc_subset_Icc <;> constructor <;> linarith
        · intro s hs
          apply DifferentiableAt.differentiableWithinAt
          simp only [re_add_im]
          apply mellin_shift_diffAt ν ε_pos ε_lt_one suppν νnonneg mass_one diffν u
          have := mem_reProdIm.mp hs.1 |>.1
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
            div_self_mul_self', add_zero] at this
          rw [uIcc_of_le (by linarith)] at this
          linarith [this.1]
      · intro s hs
        apply DifferentiableAt.differentiableWithinAt
        simp only [re_add_im]
        exact cpow_shift_diffAt X u X_gt s
    · let U : Set ℂ := Rectangle (σ₁ - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
      let f : ℂ → ℂ := fun z ↦ -deriv riemannZeta z / riemannZeta z
      let g : ℂ → ℂ := fun z ↦ mellin (fun x ↦ ↑(Smooth1 ν ε x)) (z - u * I) * ↑X ^ (z - u * I)
      unfold fTempC fTempRR twistedIntegrand
      simp only [re_add_im]
      have g_holc : DifferentiableOn ℂ g U := by
        intro w wInU
        apply DifferentiableAt.differentiableWithinAt
        simp only [g]
        apply DifferentiableAt.mul
        · apply mellin_shift_diffAt ν ε_pos ε_lt_one suppν νnonneg mass_one diffν u
          simp only [ofReal_inv, U] at wInU
          unfold Rectangle at wInU
          rw [Complex.mem_reProdIm] at wInU
          have := wInU.1
          simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
            sub_zero, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero] at this
          rw [uIcc_of_le (by linarith)] at this
          linarith [this.1]
        · exact cpow_shift_diffAt X u X_gt w
      have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
        simp only [one_mul, f]
        exact riemannZetaLogDerivResidueBigO
      convert ResidueMult g_holc pInRectangleInterior f_near_p using 1
      ext
      simp [f, g]
      ring_nf

/-- Second contour shift for the central portion `J₃₇` of the twisted Chebyshev contour,
pulling the contour further left from `Re s = σ₁` to `Re s = σ₂` on `[-3, 3]`. -/
theorem twistedChebyshevPull2 (ν : ℝ → ℝ) {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1) (X : ℝ) (X_gt : 3 < X) {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ} (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1) (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc σ₁ 2) ×ℂ (Set.Icc (-T) T) \ {1}))
    (u : ℝ)
    (holoOn2 : DifferentiableOn ℂ (twistedIntegrand ν ε X u) (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1}))
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) (diffν : ContDiff ℝ 1 ν) :
    J₃₇ ν ε T X σ₁ u = J₃ ν ε T X σ₁ u - J₄ ν ε X σ₁ σ₂ u + J₅ ν ε X σ₂ u + J₆ ν ε X σ₁ σ₂ u + J₇ ν ε T X σ₁ u := by
  let z : ℂ := σ₂ - 3 * I
  let w : ℂ := σ₁ + 3 * I
  have σ₁_pos : 0 < σ₁ := by linarith
  have sub : z.Rectangle w ⊆ Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1} := by
    intro x hx
    constructor
    · simp only [Rectangle, uIcc] at hx
      rw [Complex.mem_reProdIm] at hx ⊢
      obtain ⟨hx_re, hx_im⟩ := hx
      have hzw_re : z.re < w.re := by
        simpa [z, w] using σ₂_lt_σ₁
      have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
        have hu : x.re ∈ Set.uIcc z.re w.re := by simpa only [Set.uIcc] using hx_re
        simpa only [Set.uIcc_of_le hzw_re.le, Set.mem_Icc] using hu
      have x_re_in_Icc : x.re ∈ Set.Icc σ₂ 2 := by
        have ⟨h_left, h_right⟩ := x_re_bounds
        have h_left' : σ₂ ≤ x.re := by
          simpa [z] using h_left
        have h_right' : x.re ≤ 2 := by
          apply le_trans h_right
          have : w.re ≤ 2 := by
            simp [w]
            linarith
          exact this
        exact ⟨h_left', h_right'⟩
      have hzw_im : z.im < w.im := by
        norm_num [z, w]
      have x_im_bounds : z.im ≤ x.im ∧ x.im ≤ w.im := by
        have hu : x.im ∈ Set.uIcc z.im w.im := by simpa only [Set.uIcc] using hx_im
        simpa only [Set.uIcc_of_le hzw_im.le, Set.mem_Icc] using hu
      have x_im_in_Icc : x.im ∈ Set.Icc (-3) 3 := by
        have ⟨h_left, h_right⟩ := x_im_bounds
        have h_left' : -3 ≤ x.im := by
          simpa [z] using h_left
        have h_right' : x.im ≤ 3 := by
          simpa [w] using h_right
        exact ⟨h_left', h_right'⟩
      exact ⟨x_re_in_Icc, x_im_in_Icc⟩
    · simp only [mem_singleton_iff]
      have x_re_upper: x.re ≤ σ₁ := by
        simp only [Rectangle, uIcc] at hx
        rw [Complex.mem_reProdIm] at hx
        obtain ⟨hx_re, _⟩ := hx
        have hzw_re : z.re < w.re := by
          simpa [z, w] using σ₂_lt_σ₁
        have x_re_bounds : z.re ≤ x.re ∧ x.re ≤ w.re := by
          have hu : x.re ∈ Set.uIcc z.re w.re := by simpa only [Set.uIcc] using hx_re
          simpa only [Set.uIcc_of_le hzw_re.le, Set.mem_Icc] using hu
        have x_re_upper' : x.re ≤ w.re := x_re_bounds.2
        have hw_re : w.re = σ₁ := by simp [w]
        linarith
      have h_x_ne_one : x ≠ 1 := by
        intro h_eq
        have h_re : x.re = 1 := by rw [h_eq, Complex.one_re]
        have h1 : 1 ≤ σ₁ := by
          rw [← h_re]
          exact x_re_upper
        linarith
      exact h_x_ne_one
  have zero_over_box : RectangleIntegral (twistedIntegrand ν ε X u) z w = 0 := by
    unfold RectangleIntegral VIntegral
    exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ _ _
      (holoOn2.mono (by simpa [Rectangle] using sub))
  have splitting : J₃₇ ν ε T X σ₁ u =
    J₃ ν ε T X σ₁ u + J₅ ν ε X σ₁ u + J₇ ν ε T X σ₁ u := by
    unfold J₃₇ J₃ J₅ J₇
    apply verticalIntegral_split_three_finite'
    · apply ContinuousOn.integrableOn_Icc
      unfold twistedIntegrand
      apply ContinuousOn.mul
      · apply ContinuousOn.mul
        · apply SmoothedChebyshevPull2_aux1 σ₁_lt_one holoOn
        · apply continuousOn_of_forall_continuousAt
          intro t _
          exact mellin_shift_contAt ν ε_pos ε_lt_one suppν νnonneg mass_one diffν u σ₁_pos t
      · apply continuousOn_of_forall_continuousAt
        intro t _
        exact cpow_shift_contAt X u X_gt t
    · refine ⟨by linarith, by linarith, by linarith⟩
  calc J₃₇ ν ε T X σ₁ u =
        J₃₇ ν ε T X σ₁ u - (1 / (2 * π * I)) * (0 : ℂ) := by simp
    _ = J₃₇ ν ε T X σ₁ u - (1 / (2 * π * I)) *
        (RectangleIntegral (twistedIntegrand ν ε X u) z w) := by rw [← zero_over_box]
    _ = J₃₇ ν ε T X σ₁ u - (1 / (2 * π * I)) *
        (HIntegral (twistedIntegrand ν ε X u) z.re w.re z.im
        - HIntegral (twistedIntegrand ν ε X u) z.re w.re w.im
        + VIntegral (twistedIntegrand ν ε X u) w.re z.im w.im
        - VIntegral (twistedIntegrand ν ε X u) z.re z.im w.im) := by
      simp [RectangleIntegral]
    _ = J₃₇ ν ε T X σ₁ u -
        ((1 / (2 * π * I)) * HIntegral (twistedIntegrand ν ε X u) z.re w.re z.im
        - (1 / (2 * π * I)) * HIntegral (twistedIntegrand ν ε X u) z.re w.re w.im
        + (1 / (2 * π * I)) * VIntegral (twistedIntegrand ν ε X u) w.re z.im w.im
        - (1 / (2 * π * I)) *
            VIntegral (twistedIntegrand ν ε X u) z.re z.im w.im) := by ring
    _ = J₃₇ ν ε T X σ₁ u - (J₄ ν ε X σ₁ σ₂ u
    - (1 / (2 * π * I)) * HIntegral (twistedIntegrand ν ε X u) z.re w.re w.im
    + (1 / (2 * π * I)) * VIntegral (twistedIntegrand ν ε X u) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (twistedIntegrand ν ε X u) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, sub_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_sub, ofReal_neg,
        ofReal_ofNat, sub_re, ofReal_re, mul_re, sub_self, sub_zero, add_re, add_im, zero_add,
        sub_neg_eq_add, J₄, sub_right_inj, add_left_inj, neg_inj, mul_eq_mul_left_iff, mul_eq_zero,
        I_ne_zero, inv_eq_zero, ofReal_eq_zero, OfNat.ofNat_ne_zero, or_false, false_or, z, w]
      left
      rfl
    _ = J₃₇ ν ε T X σ₁ u - (J₄ ν ε X σ₁ σ₂ u
    - J₆ ν ε X σ₁ σ₂ u
    + (1 / (2 * π * I)) * VIntegral (twistedIntegrand ν ε X u) w.re z.im w.im
    - (1 / (2 * π * I)) * VIntegral (twistedIntegrand ν ε X u) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, HIntegral, add_im, ofReal_im, mul_im,
        re_ofNat, I_im, mul_one, im_ofNat, I_re, mul_zero, add_zero, zero_add, ofReal_ofNat, sub_re,
        ofReal_re, mul_re, sub_self, sub_zero, add_re, sub_neg_eq_add, sub_im, zero_sub, J₆, w, z]
    _ = J₃₇ ν ε T X σ₁ u - (J₄ ν ε X σ₁ σ₂ u
    - J₆ ν ε X σ₁ σ₂ u
    + J₅ ν ε X σ₁ u
    - (1 / (2 * π * I)) * VIntegral (twistedIntegrand ν ε X u) z.re z.im w.im) := by
      simp only [one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, add_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, ofReal_im,
        mul_im, zero_sub, add_im, zero_add, smul_eq_mul, sub_re, sub_zero, sub_neg_eq_add, J₅,
        w, z]
    _ = J₃₇ ν ε T X σ₁ u - (J₄ ν ε X σ₁ σ₂ u
    - J₆ ν ε X σ₁ σ₂ u
    + J₅ ν ε X σ₁ u
    - J₅ ν ε X σ₂ u) := by
      simp only [J₅, one_div, mul_inv_rev, inv_I, neg_mul, VIntegral, sub_re, ofReal_re, mul_re,
        re_ofNat, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, sub_zero, sub_im, ofReal_im,
        mul_im, add_zero, zero_sub, add_im, zero_add, smul_eq_mul, sub_neg_eq_add, z, w]
    _ = J₃ ν ε T X σ₁ u
    + J₅ ν ε X σ₁ u
    + J₇ ν ε T X σ₁ u
    - (J₄ ν ε X σ₁ σ₂ u
    - J₆ ν ε X σ₁ σ₂ u
    + J₅ ν ε X σ₁ u
    - J₅ ν ε X σ₂ u) := by
      rw [splitting]
    _ = J₃ ν ε T X σ₁ u
    - J₄ ν ε X σ₁ σ₂ u
    + J₅ ν ε X σ₂ u
    + J₆ ν ε X σ₁ σ₂ u
    + J₇ ν ε T X σ₁ u := by
      ring

/-- Version of `twistedChebyshevPull2` with explicit equality connecting the implicit `u` in `holoOn2` to the explicit `u`. -/
theorem twistedChebyshevPull2_of_eq {u : ℝ} (ν : ℝ → ℝ) {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1) (X : ℝ) (X_gt : 3 < X) {T : ℝ} (T_pos : 3 < T) {σ₁ σ₂ : ℝ} (σ₂_pos : 0 < σ₂) (σ₁_lt_one : σ₁ < 1) (σ₂_lt_σ₁ : σ₂ < σ₁)
    (holoOn : DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc σ₁ 2) ×ℂ (Set.Icc (-T) T) \ {1}))
    (holoOn2 : DifferentiableOn ℂ (twistedIntegrand ν ε X u) (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1}))
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) (diffν : ContDiff ℝ 1 ν) (u' : ℝ)
    (h_u : u = u') :
    J₃₇ ν ε T X σ₁ u' = J₃ ν ε T X σ₁ u' - J₄ ν ε X σ₁ σ₂ u' + J₅ ν ε X σ₂ u' + J₆ ν ε X σ₁ σ₂ u' + J₇ ν ε T X σ₁ u' := by
  subst h_u
  exact twistedChebyshevPull2 ν ε_pos ε_lt_one X X_gt T_pos σ₂_pos σ₁_lt_one σ₂_lt_σ₁ holoOn u holoOn2 suppν νnonneg mass_one diffν

end Erdos1201.MR
