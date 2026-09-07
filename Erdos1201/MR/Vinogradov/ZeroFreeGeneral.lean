/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
import Mathlib
import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.ZeroFreeRegionExistence
import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.ZeroSetExplicitBounds
import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.VonMangoldtSeriesPositivityBounds
import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.ZeroOrderLogDerivSeries

/-!
# Titchmarsh Theorem 3.10: General Zero-Free Region from a Growth Bound

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the deduction of a zero-free region for the Riemann zeta
function from an upper bound on $\zeta(\sigma + it)$ in a strip $\sigma \ge 1 - \theta(t)$,
following E.C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, Theorem 3.10.

## Mathematical Architecture

The classical argument combines:
1. **Analytic Domain Isolation**: Disks of radius $\theta(t)/2 \le 1/4$ centered at
   $(1 + \theta(t)/2) + it$ lie entirely inside the region where $\zeta$ is analytic
   (avoiding the pole at $s = 1$) and satisfy the hypothesis $1 - \theta(t) \le \sigma \le 2$.
2. **The 3-4-1 Trigonometric Inequality**: Positivity of the Dirichlet series for
   $3 + 4\cos\theta + \cos 2\theta \ge 0$ gives
   $0 \le 3(-\zeta'/\zeta(1+\delta)) + 4\mathrm{Re}(-\zeta'/\zeta(1+\delta+it)) + \mathrm{Re}(-\zeta'/\zeta(1+\delta+2it))$.
3. **Logarithmic Derivative Bounds**: Carathéodory / Borel–Carathéodory bounds with
   parameter $L(t) = \varphi(t)/\theta(t)$ give the upper bound
   $3/\delta - 4/(1+\delta-\sigma) + CL(t)$ near a zero with real part $\sigma$.
4. **Algebraic Deduction (`zero_free_algebra`)**: Choosing $\delta = 1/(2CL)$ in the
   inequality $0 \le 3/\delta - 4/(1+\delta-\sigma) + CL$ forces
   $\sigma \le 1 - \frac{1}{14C \cdot L}$.
5. **Zero-Free Region Theorems**:
   - `zero_free_of_341_bound`: deduces the zero-free region from the 3-4-1 bound.
   - `zero_free_of_classical_subordinate`: deduces the zero-free region when $\theta/\varphi \le M/\log(t+2)$
     unconditionally from the vendored capstone `ZetaZeroFreeRegion.zerofree`.
   - `zero_free_of_zeta_bound`: the general zero-free region under growth bounds and 3-4-1 input.
   - `zero_free_of_zeta_bound'`: the general zero-free region under growth bounds, fully unconditional.
-/

open Complex Metric ZetaFunctionEstimates AnalyticZeroCounting ZetaZeroFreeRegion

namespace Erdos1201.MR.Vinogradov

/-- Algebraic deduction of the zero-free region width from the 3-4-1 trigonometric inequality.
Given $0 \le 3/\delta - 4/(1+\delta-\sigma) + C L$ with $\delta = 1/(2CL)$ and $\sigma < 1$,
we deduce $\sigma \le 1 - (1/(14C)) / L$. -/
lemma zero_free_algebra (C L σ δ : ℝ) (hC : 1 < C) (hL : 0 < L)
    (hδ : δ = 1 / (2 * C * L))
    (h_pos : 0 ≤ 3 / δ - 4 / (1 + δ - σ) + C * L)
    (hσ : σ < 1) :
    σ ≤ 1 - (1 / (14 * C)) / L := by
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have h2CL : 0 < 2 * C * L := by
    have : 0 < 2 * (C * L) := mul_pos (by norm_num) (mul_pos hCpos hL)
    simpa [mul_assoc] using this
  have hδpos : 0 < δ := by
    rw [hδ]
    exact one_div_pos.mpr h2CL
  have hineq1 : 4 / (1 + δ - σ) ≤ 3 / δ + C * L := by linarith [h_pos]
  have hineq2 : 4 / (1 - σ + δ) ≤ 3 / δ + C * L := by
    convert hineq1 using 2
    ring
  have hinv : 1 / δ = 2 * C * L := by
    rw [hδ]
    simp
  have hrhs_eval : 3 / δ + C * L = 7 * C * L := rhs_eval_of_inv C L δ hinv
  have hfinal : 4 / (1 - σ + δ) ≤ 7 * C * L := by
    rw [← hrhs_eval]
    exact hineq2
  set a := 1 - σ + δ
  set b := 7 * C * L
  have ha_pos : 0 < a := by
    have : 0 < 1 - σ := sub_pos.mpr hσ
    exact add_pos this hδpos
  have hb_pos : 0 < b := mul_pos (mul_pos (by norm_num) hCpos) hL
  have h_recip := reciprocal_div_inequality a b ha_pos hb_pos hfinal
  have h_diff_bound : 4 / (7 * C * L) ≤ (1 - σ) + 1 / (2 * C * L) := by
    have h_rw : a = (1 - σ) + 1 / (2 * C * L) := by
      dsimp [a]
      rw [hδ]
    rw [h_rw] at h_recip
    exact h_recip
  have h_bound := fraction_diff_lower_bound C L (1 - σ) h_diff_bound
  have h_rearr : 1 / (14 * C * L) = (1 / (14 * C)) / L := by
    ring
  rw [h_rearr] at h_bound
  linarith

/-- Positivity of the zero-free width constant $A = 1/(14C)$ for $C > 1$. -/
lemma zero_free_width_pos (C : ℝ) (hC : 1 < C) : 0 < 1 / (14 * C) := by
  have : 0 < 14 * C := mul_pos (by norm_num) (lt_trans zero_lt_one hC)
  exact one_div_pos.mpr this

/-- Positivity of the shift parameter $\delta = 1/(2CL)$ for positive $C$ and $L$. -/
lemma delta_pos_of_pos (C L : ℝ) (hC : 0 < C) (hL : 0 < L) : 0 < 1 / (2 * C * L) := by
  have : 0 < 2 * C * L := by
    have : 0 < 2 * (C * L) := mul_pos (by norm_num) (mul_pos hC hL)
    simpa [mul_assoc] using this
  exact one_div_pos.mpr this

/-- A closed ball of radius 1 centered at $c$ with $|\mathrm{Im}(c)| > 1$ is disjoint from $1$. -/
lemma closedBall_c_one_subset_ne_one (c : ℂ) (hc : 1 < |c.im|) :
    Metric.closedBall c 1 ⊆ {s : ℂ | s ≠ 1} := by
  intro s hs
  rw [Metric.mem_closedBall] at hs
  intro hs1
  subst hs1
  have h_im_dist : |(1 : ℂ).im - c.im| ≤ ‖(1 : ℂ) - c‖ :=
    Complex.abs_im_le_norm ((1 : ℂ) - c)
  simp only [Complex.one_im, zero_sub, abs_neg] at h_im_dist
  have h_norm_le : ‖(1 : ℂ) - c‖ ≤ 1 := by
    rwa [← dist_eq]
  linarith

/-- The Riemann zeta function is analytic in a neighborhood of the closed ball of radius
$\theta(t)/2 \le 1$ centered at $(1 + \theta(t)/2) + it$ when $|t| \ge 3$. -/
lemma zeta_analytic_on_closedBall (t : ℝ) (ht : 3 ≤ |t|) (θ : ℝ) (hθ : 0 < θ ∧ θ ≤ 1 / 2) :
    AnalyticOnNhd ℂ riemannZeta (Metric.closedBall ((1 + θ / 2 : ℝ) + t * Complex.I) (θ / 2)) := by
  have hθ2_le_1 : θ / 2 ≤ 1 := by linarith [hθ.2]
  have h_sub : Metric.closedBall ((1 + θ / 2 : ℝ) + t * Complex.I) (θ / 2) ⊆
      Metric.closedBall ((1 + θ / 2 : ℝ) + t * Complex.I) 1 :=
    Metric.closedBall_subset_closedBall hθ2_le_1
  have hc_im : 1 < |((1 + θ / 2 : ℝ) + t * Complex.I).im| := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re, zero_add]
    linarith
  have h_ne1 := closedBall_c_one_subset_ne_one ((1 + θ / 2 : ℝ) + t * Complex.I) hc_im
  have h_sub_ne1 := subset_trans h_sub h_ne1
  exact analyticOn_riemannZeta.mono h_sub_ne1

/-- Upper bound on the Riemann zeta function along the disk:
for any $z \in \bar{B}((1 + \theta(t)/2) + it, \theta(t)/2)$,
we have $1 - \theta(|t|) \le z.\mathrm{re} \le 2$, hence the growth hypothesis $h\zeta$ applies. -/
lemma zeta_bound_on_disk (θ φ : ℝ → ℝ)
    (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 → ‖riemannZeta (σ + t * Complex.I)‖ ≤ Real.exp (φ |t|))
    (t : ℝ) (ht : 3 ≤ t) (z : ℂ)
    (hz : z ∈ Metric.closedBall ((1 + θ t / 2 : ℝ) + t * Complex.I) (θ t / 2)) :
    ‖riemannZeta (z.re + t * Complex.I)‖ ≤ Real.exp (φ t) := by
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_abs : |t| = t := abs_of_nonneg ht_nonneg
  have ht_ge3 : 3 ≤ |t| := by rwa [ht_abs]
  have hθt := hθ t ht
  rw [Metric.mem_closedBall, dist_eq] at hz
  have h_re_dist : |z.re - (1 + θ t / 2)| ≤ ‖z - ((1 + θ t / 2 : ℝ) + t * Complex.I)‖ := by
    have h1 : z.re - (1 + θ t / 2) = (z - ((1 + θ t / 2 : ℝ) + t * Complex.I)).re := by simp
    rw [h1]
    exact Complex.abs_re_le_norm _
  have h_re_bound : |z.re - (1 + θ t / 2)| ≤ θ t / 2 := le_trans h_re_dist hz
  rw [abs_le] at h_re_bound
  have hσ_ge : 1 - θ |t| ≤ z.re := by
    rw [ht_abs]
    linarith [h_re_bound.1]
  have hσ_le : z.re ≤ 2 := by linarith [h_re_bound.2, hθt.2]
  have h_res := hζ z.re t ht_ge3 hσ_ge hσ_le
  rwa [ht_abs] at h_res

/-- General zero-free region for the Riemann zeta function (Titchmarsh, Theorem 3.10)
from the 3-4-1 trigonometric inequality input. -/
theorem zero_free_of_341_bound (θ φ : ℝ → ℝ)
    (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2)
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t)
    (C : ℝ) (hC : 1 < C)
    (h341 : ∀ (ρ : ℂ), riemannZeta ρ = 0 → 6 ≤ |ρ.im| → 0 < ρ.re → ρ.re < 1 →
      let L := φ |ρ.im| / θ |ρ.im|
      let δ := 1 / (2 * C * L)
      0 ≤ 3 / δ - 4 / (1 + δ - ρ.re) + C * L) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ρ : ℂ), riemannZeta ρ = 0 → 6 ≤ |ρ.im| → ρ.re ≤ 1 - A * θ |ρ.im| / φ |ρ.im| := by
  let A := 1 / (14 * C)
  have hApos : 0 < A := zero_free_width_pos C hC
  use A, hApos
  intro ρ hzero hρim
  have ht_ge3 : 3 ≤ |ρ.im| := by linarith
  have hθ_pos := (hθ |ρ.im| ht_ge3).1
  have hθ_le := (hθ |ρ.im| ht_ge3).2
  have hφ_ge := hφ |ρ.im| ht_ge3
  have hLpos : 0 < φ |ρ.im| / θ |ρ.im| := div_pos (by linarith) hθ_pos
  by_cases hρre_le_zero : ρ.re ≤ 0
  · have h_frac_le : θ |ρ.im| / φ |ρ.im| ≤ 1 / 2 := by
      have h1 : θ |ρ.im| / φ |ρ.im| ≤ θ |ρ.im| / 1 :=
        div_le_div_of_nonneg_left (le_of_lt hθ_pos) (by norm_num) hφ_ge
      have h2 : θ |ρ.im| / 1 = θ |ρ.im| := by ring
      linarith [hθ_le]
    have hA_le : A ≤ 1 := by
      have : 14 * C > 14 := by linarith
      have : A < 1 / 14 := by
        dsimp [A]
        exact one_div_lt_one_div_of_lt (by norm_num) this
      linarith
    have h_prod_le_half : A * (θ |ρ.im| / φ |ρ.im|) ≤ 1 / 2 := by
      have hA_nonneg : 0 ≤ A := le_of_lt hApos
      have hfrac_nonneg : 0 ≤ θ |ρ.im| / φ |ρ.im| := le_of_lt (div_pos hθ_pos (by linarith))
      nlinarith
    have h_rhs_ge_half : 1 / 2 ≤ 1 - A * θ |ρ.im| / φ |ρ.im| := by
      have : A * θ |ρ.im| / φ |ρ.im| = A * (θ |ρ.im| / φ |ρ.im|) := by ring
      rw [this]
      linarith
    linarith
  · push Not at hρre_le_zero
    have hnot_ge_one : ¬ (1 ≤ ρ.re) := fun h1 =>
      riemannZeta_ne_zero_of_one_le_re h1 hzero
    push Not at hnot_ge_one
    let L := φ |ρ.im| / θ |ρ.im|
    let δ := 1 / (2 * C * L)
    have h_pos := h341 ρ hzero hρim hρre_le_zero hnot_ge_one
    have h_bound := zero_free_algebra C L ρ.re δ hC hLpos rfl h_pos hnot_ge_one
    have h_div_rewrite : (1 / (14 * C)) / L = A * θ |ρ.im| / φ |ρ.im| := by
      dsimp [A, L]
      simp only [div_div_eq_mul_div]
    rwa [h_div_rewrite] at h_bound

/-- General zero-free region when the ratio $\theta(t)/\varphi(t)$ is subordinate to
the classical $O(1/\log(t+2))$ rate, deduced unconditionally from `ZetaZeroFreeRegion.zerofree`. -/
theorem zero_free_of_classical_subordinate (θ φ : ℝ → ℝ)
    (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2)
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t)
    (M : ℝ) (hM : 0 < M)
    (hsub : ∀ t, 6 ≤ t → θ t / φ t ≤ M / Real.log (t + 2)) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ρ : ℂ), riemannZeta ρ = 0 → 6 ≤ |ρ.im| → ρ.re ≤ 1 - A * θ |ρ.im| / φ |ρ.im| := by
  obtain ⟨c, hc_pos, hc_lt1, hzero_free⟩ := zerofree
  let A := min (c / M) (1 / 2)
  have hApos : 0 < A := lt_min (div_pos hc_pos hM) (by norm_num)
  use A, hApos
  intro ρ hzero hρim
  have ht_ge3 : 3 ≤ |ρ.im| := by linarith
  have hθ_pos := (hθ |ρ.im| ht_ge3).1
  have hθ_le := (hθ |ρ.im| ht_ge3).2
  have hφ_ge := hφ |ρ.im| ht_ge3
  by_cases hρre_le_zero : ρ.re ≤ 0
  · have h_frac_le : θ |ρ.im| / φ |ρ.im| ≤ 1 / 2 := by
      have h1 : θ |ρ.im| / φ |ρ.im| ≤ θ |ρ.im| / 1 :=
        div_le_div_of_nonneg_left (le_of_lt hθ_pos) (by norm_num) hφ_ge
      have h2 : θ |ρ.im| / 1 = θ |ρ.im| := by ring
      linarith [hθ_le]
    have hA_le : A ≤ 1 / 2 := min_le_right _ _
    have h_prod_le : A * (θ |ρ.im| / φ |ρ.im|) ≤ 1 / 4 := by
      have hA_nonneg : 0 ≤ A := le_of_lt hApos
      have hfrac_nonneg : 0 ≤ θ |ρ.im| / φ |ρ.im| := le_of_lt (div_pos hθ_pos (by linarith))
      nlinarith
    have h_rhs : 1 / 2 ≤ 1 - A * θ |ρ.im| / φ |ρ.im| := by
      have : A * θ |ρ.im| / φ |ρ.im| = A * (θ |ρ.im| / φ |ρ.im|) := by ring
      rw [this]
      linarith
    linarith
  · push Not at hρre_le_zero
    have hnot_ge_one : ¬ (1 ≤ ρ.re) := fun h1 =>
      riemannZeta_ne_zero_of_one_le_re h1 hzero
    push Not at hnot_ge_one
    have hmem : ρ ∈ zeroZ := hzero
    have h2lt : 2 < |ρ.im| := by linarith
    have h_zf := hzero_free ρ ⟨hmem, hρre_le_zero, hnot_ge_one⟩ h2lt
    have hsub_ρ := hsub |ρ.im| hρim
    have hA_le_cM : A ≤ c / M := min_le_left _ _
    have hfrac_nonneg : 0 ≤ θ |ρ.im| / φ |ρ.im| := le_of_lt (div_pos hθ_pos (by linarith))
    have hcM_nonneg : 0 ≤ c / M := le_of_lt (div_pos hc_pos hM)
    have h_step1 : A * (θ |ρ.im| / φ |ρ.im|) ≤ (c / M) * (θ |ρ.im| / φ |ρ.im|) :=
      mul_le_mul_of_nonneg_right hA_le_cM hfrac_nonneg
    have h_step2 : (c / M) * (θ |ρ.im| / φ |ρ.im|) ≤ (c / M) * (M / Real.log (|ρ.im| + 2)) :=
      mul_le_mul_of_nonneg_left hsub_ρ hcM_nonneg
    have h_step3 : (c / M) * (M / Real.log (|ρ.im| + 2)) = c / Real.log (|ρ.im| + 2) := by
      have hMne : M ≠ 0 := ne_of_gt hM
      field_simp
    have h_ineq : A * (θ |ρ.im| / φ |ρ.im|) ≤ c / Real.log (|ρ.im| + 2) := by
      linarith [h_step1, h_step2, h_step3]
    have h_rw : A * θ |ρ.im| / φ |ρ.im| = A * (θ |ρ.im| / φ |ρ.im|) := by ring
    rw [h_rw]
    linarith

/-- General zero-free region theorem for the Riemann zeta function (Titchmarsh, Theorem 3.10)
from an upper bound on $\zeta(\sigma + it)$ and the 3-4-1 trigonometric inequality input. -/
theorem zero_free_of_zeta_bound (θ φ : ℝ → ℝ)
    (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2) (_hθanti : AntitoneOn θ (Set.Ici 3))
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t) (_hφmono : MonotoneOn φ (Set.Ici 3))
    (_hφθ : ∀ t, 3 ≤ t → φ (2 * t) ≤ 2 * φ t)
    (_hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 → ‖riemannZeta (σ + t * Complex.I)‖ ≤ Real.exp (φ |t|))
    (h341 : ∃ C > 1, ∀ (ρ : ℂ), riemannZeta ρ = 0 → 6 ≤ |ρ.im| → 0 < ρ.re → ρ.re < 1 →
      let L := φ |ρ.im| / θ |ρ.im|
      let δ := 1 / (2 * C * L)
      0 ≤ 3 / δ - 4 / (1 + δ - ρ.re) + C * L) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ρ : ℂ), riemannZeta ρ = 0 → 6 ≤ |ρ.im| → ρ.re ≤ 1 - A * θ |ρ.im| / φ |ρ.im| := by
  obtain ⟨C, hC, h341_bound⟩ := h341
  exact zero_free_of_341_bound θ φ hθ hφ C hC h341_bound


lemma zeta_analytic_on_closedBall_1 (c : ℂ) (hc : 1 < |c.im|) :
    AnalyticOnNhd ℂ riemannZeta (Metric.closedBall c 1) := by
  exact analyticOn_riemannZeta.mono (closedBall_c_one_subset_ne_one c hc)

lemma log_Deriv_Expansion_Zeta_general
    (r1 r R1 R : ℝ)
    (hr1_pos : 0 < r1) (hr1_lt_r : r1 < r)
    (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (c : ℂ) (hc_re : 1 < c.re) (hc_im : 3 ≤ |c.im|)
    (B : ℝ) (hB : 1 < B) (h_bound : ∀ z ∈ closedBall c R, ‖riemannZeta z‖ < B)
    (hfin : (zerosetKfRc R1 c riemannZeta).Finite) :
    ∀ z ∈ closedBall c r1 \ zerosetKfRc R1 c riemannZeta,
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
    (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖riemannZeta c‖) := by
  intro z hzmem
  have h_im_gt_1 : 1 < |c.im| := by linarith
  have hζ_analytic : AnalyticOnNhd ℂ riemannZeta (closedBall c 1) := zeta_analytic_on_closedBall_1 c h_im_gt_1
  have hζ_c_ne : riemannZeta c ≠ 0 := by apply riemannZeta_ne_zero_of_one_lt_re hc_re
  have hfin_shift : (zerosetKfRc R1 (0 : ℂ) (fun u => riemannZeta (u + c) / riemannZeta c)).Finite := by
    have h_bij := fc_zeros R1 hR1_pos c riemannZeta hζ_c_ne hζ_analytic
    have himg : ((fun ρ => ρ - c) '' (zerosetKfRc R1 c riemannZeta)).Finite := hfin.image _
    simpa [h_bij] using himg
  have hz0mem : (z - c) ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun u => riemannZeta (u + c) / riemannZeta c) := by
    have hiff := DminusK r1 R1 hr1_pos hR1_pos c riemannZeta hζ_analytic hζ_c_ne (z - c)
    exact (hiff).mpr (by simpa [sub_add_cancel] using hzmem)
  have hineq0 := (final_ineq2 B hB r1 r R R1 hr1_pos hr1_lt_r hr_lt_R1 hR1_lt_R hR_lt_1 c riemannZeta hζ_analytic hζ_c_ne h_bound hfin_shift) (z - c) hz0mem
  rcases hzmem with ⟨hz_ball, hz_notin⟩
  have hr1_lt_R1' : r1 < R1 := lt_trans hr1_lt_r hr_lt_R1
  have hz_in_ball_R1 : z ∈ closedBall c R1 := by
    have hz_le_r1 : dist z c ≤ r1 := by simpa [mem_closedBall] using hz_ball
    have hr1_le_R1 : r1 ≤ R1 := le_of_lt hr1_lt_R1'
    have hz_le_R1 : dist z c ≤ R1 := le_trans hz_le_r1 hr1_le_R1
    simpa [mem_closedBall] using hz_le_R1
  have hzeta_ne : riemannZeta z ≠ 0 := by intro hz0; exact hz_notin ⟨hz_in_ball_R1, hz0⟩
  have hcancel_frac : (deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta c) / (riemannZeta z / riemannZeta c) = deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta z := by
    simpa using (frac_cancel_const (x := deriv (fun x => riemannZeta (x + c)) (z - c)) (y := riemannZeta z) (c := riemannZeta c) hζ_c_ne hzeta_ne)
  have hcancel_all : (deriv (fun x => riemannZeta (x + c)) (z - c) / riemannZeta c) / (riemannZeta z / riemannZeta c) = deriv riemannZeta z / riemannZeta z := by
    simpa [deriv_comp_add_const, sub_add_cancel] using hcancel_frac
  have hineq1 : ‖(deriv riemannZeta z / riemannZeta z) - ∑ ρ ∈ hfin_shift.toFinset, ((analyticOrderAt (fun u => riemannZeta (u + c) / riemannZeta c) ρ).toNat : ℂ) / ((z - c) - ρ)‖ ≤ (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖riemannZeta c‖) := by
    simpa [hcancel_all] using hineq0
  have hsum_eq := shifted_zeros_correspondence R1 hR1_pos c z riemannZeta hζ_c_ne hζ_analytic hfin hfin_shift
  have hineq2 : ‖(deriv riemannZeta z / riemannZeta z) - ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤ (16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖riemannZeta c‖) := by
    simpa [hsum_eq] using hineq1
  simpa [logDerivZeta] using hineq2


lemma zeros_finite_general (c : ℂ) (R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_1 : R1 < 1) (hc_re : 1 < c.re) :
    (zerosetKfRc R1 c riemannZeta).Finite := by
  let H : ℂ → ℂ := Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1
  have hH_diff : Differentiable ℂ H := by
    intro s
    rcases eq_or_ne s 1 with rfl | hs
    · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      · simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    · have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) s := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) s :=
          (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta s :=
          (differentiableAt_riemannZeta hs)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hs] with u hu using by
        simp [H, Function.update_of_ne hu]
  have hH_ana : AnalyticOnNhd ℂ H Set.univ := (Complex.analyticOnNhd_univ_iff_differentiable).mpr hH_diff
  let g : ℂ → ℂ := fun z => H (z + c)
  have hg_diff : Differentiable ℂ g := hH_diff.comp (differentiable_id.add_const c)
  have hg_ana : AnalyticOnNhd ℂ g (Metric.closedBall (0:ℂ) 1) :=
    AnalyticOnNhd.mono ((Complex.analyticOnNhd_univ_iff_differentiable).mpr hg_diff) (by intro z hz; simp)
  have hg_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, g z ≠ 0 := by
    refine ⟨0, Metric.mem_ball.mpr (by norm_num), ?_⟩
    have hc_ne : c ≠ 1 := by
      intro hc
      have : c.re = 1 := by rw [hc]; simp
      linarith
    have hζ_ne : riemannZeta c ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hc_re
    have : g 0 = H c := by simp [g]
    have h_Hc : H c = (c - 1) * riemannZeta c := by simp [H, Function.update_of_ne hc_ne]
    rw [this, h_Hc]
    apply mul_ne_zero (sub_ne_zero.mpr hc_ne) hζ_ne
  have h_fin_g := AnalyticZeroCounting.lem_Contra_finiteKR R1 hR1_pos hR1_lt_1 g hg_ana hg_nonzero
  have h_subset : zerosetKfRc R1 c riemannZeta ⊆ (fun w => w + c) '' (zerosetKfR R1 hR1_pos g) := by
    intro z hz
    rcases hz with ⟨hzball, hzero⟩
    refine ⟨z - c, ?_, by ring⟩
    constructor
    · simpa [Metric.mem_closedBall, Complex.dist_eq, sub_eq_add_neg] using hzball
    · have hz_ne : z ≠ 1 := by
        intro hz1
        have hz1_ne : riemannZeta 1 ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by norm_num)
        rw [hz1] at hzero
        exact hz1_ne hzero
      have hg_eq : g (z - c) = (z - 1) * riemannZeta z := by
        have hsum : z - c + c = z := by ring
        have : g (z - c) = H z := by simp [g, hsum]
        rw [this]
        simp [H, hz_ne]
      rw [hg_eq, hzero, mul_zero]
  exact Set.Finite.subset (h_fin_g.image _) h_subset


lemma re_one_div (z : ℂ) : (1 / z).re = z.re / (z.re^2 + z.im^2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  ring

lemma neg_re_le_norm (z : ℂ) : -z.re ≤ norm z := by
  have := Complex.re_le_norm (-z)
  rwa [Complex.neg_re, norm_neg] at this

lemma div_pow_two (x : ℝ) : x / x^2 = 1 / x := by
  by_cases h : x = 0
  · simp [h]
  · rw [pow_two, ← div_div, div_self h, one_div]

lemma abs_term_bound_general (p : Nat.Primes) (s : ℂ) :
    norm (1 - ((p : ℕ) : ℂ) ^ (-s)) ≤ 1 + ((p : ℕ) : ℝ) ^ (-s.re) := by
  let z : ℂ := ((p : ℕ) : ℂ) ^ (-s)
  have h1 : norm (1 - z) ≤ 1 + norm z := by
    simpa [sub_eq_add_neg, norm_neg] using (_root_.norm_add_le (1 : ℂ) (-z))
  have h5 : norm (((p : ℕ) : ℂ) ^ (-s)) = ((p : ℕ) : ℝ) ^ (-s.re) := abs_p_pow_s p s
  have h5z : norm z = ((p : ℕ) : ℝ) ^ (-s.re) := by simpa [z] using h5
  rw [h5z] at h1
  simpa [z] using h1

lemma cond_general (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) : 1 - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have hp_eq_one : ((p : ℕ) : ℂ) ^ (-s) = 1 := by
    rw [sub_eq_zero] at h
    exact h.symm
  have h_abs_lt : norm (((p : ℕ) : ℂ) ^ (-s)) < 1 := p_s_abs_1 p s hs
  rw [hp_eq_one] at h_abs_lt
  have : norm (1 : ℂ) = 1 := by simp [norm]
  rw [this] at h_abs_lt
  exact lt_irrefl 1 h_abs_lt

lemma abs_term_inv_bound_general (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    (1 + ((p : ℕ) : ℝ) ^ (-s.re))⁻¹ ≤ (norm (1 - ((p : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  have h1 := abs_term_bound_general p s
  have h2 := cond_general p s hs
  have h3 : 0 < norm (1 - ((p : ℕ) : ℂ) ^ (-s)) := norm_pos_iff.mpr h2
  simpa only [one_div] using (_root_.one_div_le_one_div_of_le h3 h1)

lemma abs_zeta_inequality_general (s : ℂ) (hs : 1 < s.re) :
    ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-s.re))⁻¹ ≤
    norm (riemannZeta s) := by
  have h_pos_left : ∀ p : Nat.Primes, 0 < (1 + ((p : ℕ) : ℝ) ^ (-s.re))⁻¹ := by
    intro p
    apply inv_pos.mpr
    apply add_pos zero_lt_one
    apply Real.rpow_pos_of_pos
    exact_mod_cast (p.property.pos : 0 < (p : ℕ))
  have h_pos_right : ∀ p : Nat.Primes, 0 < (norm (1 - ((p : ℕ) : ℂ) ^ (-s)))⁻¹ := by
    intro p
    apply inv_pos.mpr
    rw [norm_pos_iff]
    exact cond_general p s hs
  have h_mult_left : Multipliable (fun p : Nat.Primes => (1 + ((p : ℕ) : ℝ) ^ (-s.re))⁻¹) :=
    multipliable_positive_inv_powers (s.re) hs
  have h_mult_right : Multipliable (fun p : Nat.Primes => (norm (1 - ((p : ℕ) : ℂ) ^ (-s)))⁻¹) := by
    have h_euler := (zetaEulerprod s hs).1
    have h_nonzero : ∀ p : Nat.Primes, 1 - ((p : ℕ) : ℂ) ^ (-s) ≠ 0 := fun p => cond_general p s hs
    exact multipliable_complex_abs_inv (fun p : Nat.Primes => ((p : ℕ) : ℂ) ^ (-s)) h_euler h_nonzero
  let f : Nat.Primes → NNReal := fun p => ⟨(1 + ((p : ℕ) : ℝ) ^ (-s.re))⁻¹, le_of_lt (h_pos_left p)⟩
  let g : Nat.Primes → NNReal := fun p => ⟨(norm (1 - ((p : ℕ) : ℂ) ^ (-s)))⁻¹, le_of_lt (h_pos_right p)⟩
  have hf : Multipliable f := multipliable_real_to_nnreal _ h_pos_left h_mult_left
  have hg : Multipliable g := multipliable_real_to_nnreal _ h_pos_right h_mult_right
  have h_pointwise : ∀ p : Nat.Primes, f p ≤ g p := by
    intro p
    simp only [f, g]
    exact abs_term_inv_bound_general p s hs
  have h_nnreal_ineq : ∏' p, f p ≤ ∏' p, g p := Multipliable.tprod_le_tprod h_pointwise hf hg
  have h_convert : ∏' p, (f p : ℝ) ≤ ∏' p, (g p : ℝ) := nnreal_tprod_le_coe f g hf hg h_nnreal_ineq
  have h_eq_f : ∏' p, (f p : ℝ) = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-s.re))⁻¹ := rfl
  have h_eq_g : ∏' p, (g p : ℝ) = ∏' p : Nat.Primes, (norm (1 - ((p : ℕ) : ℂ) ^ (-s)))⁻¹ := rfl
  rw [h_eq_f, h_eq_g] at h_convert
  have h_zeta : ∏' p : Nat.Primes, (norm (1 - ((p : ℕ) : ℂ) ^ (-s)))⁻¹ = norm (riemannZeta s) := by
    exact (abs_zeta_prod_prime s hs).symm
  rw [h_zeta] at h_convert
  exact h_convert

lemma one_minus_le_inv_one_plus {x : ℝ} (_hx : 0 < x) (_hx1 : x < 1) :
    1 - x ≤ (1 + x)⁻¹ := by
  have h1 : 0 < 1 + x := by linarith
  have h4 : 1 - x ≤ 1 / (1 + x) := by
    rw [le_div_iff₀ h1]
    nlinarith
  simpa [one_div] using h4

lemma p_s_real_lt_one (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) : ((p : ℕ) : ℝ) ^ (-s.re) < 1 := by
  have hx : 1 < ((p : ℕ) : ℝ) := by exact_mod_cast (p.property.one_lt)
  have hz : -s.re < 0 := by linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg hx hz

lemma term_bound2 (p : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    1 - ((p : ℕ) : ℝ) ^ (-s.re) ≤ (1 + ((p : ℕ) : ℝ) ^ (-s.re))⁻¹ := by
  have hx : 0 < ((p : ℕ) : ℝ) ^ (-s.re) := Real.rpow_pos_of_pos (by exact_mod_cast (p.property.pos)) _
  have hx1 := p_s_real_lt_one p s hs
  exact one_minus_le_inv_one_plus hx hx1

lemma abs_zeta_ratio_eval_general (σ : ℝ) (hσ : 1 < σ) :
    norm (riemannZeta (2 * σ : ℝ) / riemannZeta σ) = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := by
  have hr : 1 < (((2 * σ : ℝ) / 2 : ℂ)).re := by
    simp
    linarith
  have hratio := zeta_ratio_identity_ofReal_div_two (2 * σ) hr
  have h_simp : ((2 * σ : ℝ) / 2 : ℝ) = σ := by ring
  have h_cast : (((2 * σ : ℝ) / 2 : ℝ) : ℂ) = (σ : ℂ) := by rw [h_simp]
  have h_cast2 : (((2 * σ : ℝ) / 2 : ℂ)) = (σ : ℂ) := by
    apply Complex.ext <;> simp
  rw [h_cast] at hratio
  rw [h_cast2] at hratio
  let w : Nat.Primes → ℂ := fun p => (1 + ((p : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹
  let u : Nat.Primes → ℝ := fun p => (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹
  have hu_mult : Multipliable u :=
    multipliable_positive_inv_powers σ hσ
  have hw_eq : w = fun p : Nat.Primes => (u p : ℂ) := by
    funext p
    have hx : 0 ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (Nat.zero_le (p : ℕ))
    have hcpow : (((((p : ℕ) : ℝ) ^ (-σ)) : ℝ) : ℂ)
        = ((p : ℕ) : ℂ) ^ (-(σ : ℂ)) := by
      simpa using (Complex.ofReal_cpow (x := ((p : ℕ) : ℝ)) (hx := hx) (y := -σ))
    calc
      w p = (1 + ((p : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹ := rfl
      _ = (1 + (((((p : ℕ) : ℝ) ^ (-σ)) : ℝ) : ℂ))⁻¹ := by
        simp [hcpow]
      _ = (((1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ : ℝ) : ℂ) := by
        simp [Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_one]
  have hw_mult : Multipliable w := by
    have hmap : Multipliable ((fun x : ℝ => (x : ℂ)) ∘ u) :=
      Multipliable.map (hf := hu_mult) Complex.ofRealHom Complex.continuous_ofReal
    simpa [hw_eq, Function.comp_def] using hmap
  have h_abs_tprod : norm (∏' p : Nat.Primes, w p) = ∏' p : Nat.Primes, norm (w p) :=
    Multipliable.norm_tprod hw_mult
  have h_abs_eq_fun : (fun p : Nat.Primes => norm (w p)) = u := by
    funext p
    have hge : 0 ≤ ((p : ℕ) : ℝ) ^ (-σ) :=
      Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le (p : ℕ))) _
    have hpos : 0 < 1 + ((p : ℕ) : ℝ) ^ (-σ) := by linarith
    have hnonneg : 0 ≤ u p := by
      have : 0 < (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := inv_pos.mpr hpos
      exact this.le
    simp [hw_eq, Complex.norm_real, abs_of_nonneg hnonneg]
  have h_abs_ratio : norm (riemannZeta (2 * σ : ℝ) / riemannZeta σ)
      = norm (∏' p : Nat.Primes, w p) := by
    simpa [w] using congrArg norm hratio
  calc
    norm (riemannZeta (2 * σ : ℝ) / riemannZeta σ)
        = norm (∏' p : Nat.Primes, w p) := h_abs_ratio
    _ = ∏' p : Nat.Primes, norm (w p) := h_abs_tprod
    _ = ∏' p : Nat.Primes, u p := by simp [h_abs_eq_fun]
    _ = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := rfl

/-- Explicit general lower bound on the norm of the Riemann zeta function for $\mathrm{Re}(s) > 1$. -/
theorem zeta_lower_bound_general (σ t : ℝ) (hσ : 1 < σ) :
    norm (riemannZeta (2 * σ : ℝ) / riemannZeta σ) ≤
      norm (riemannZeta (σ + t * Complex.I)) := by
  have hs : 1 < (σ + t * Complex.I).re := by
    simp
    exact hσ
  calc
    norm (riemannZeta (2 * σ : ℝ) / riemannZeta σ)
        = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ := abs_zeta_ratio_eval_general σ hσ
    _ ≤ norm (riemannZeta (σ + t * Complex.I)) := by
          have h_ineq := abs_zeta_inequality_general (σ + t * Complex.I) hs
          have h_re : (σ + t * Complex.I).re = σ := by simp
          rwa [h_re] at h_ineq

/-- The real part of $\zeta(x)$ for real $x > 1$ is at least $1$. -/
lemma one_le_zeta_ofReal (x : ℝ) (hx : 1 < x) : 1 ≤ (riemannZeta (x : ℂ)).re := by
  have hxC : 1 < (Complex.ofReal x).re := by simpa [Complex.ofReal_re] using hx
  have hz : riemannZeta (x : ℂ) = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) :=
    zeta_eq_tsum_one_div_nat_add_one_cpow (s := (x : ℂ)) hxC
  have hre : (riemannZeta (x : ℂ)).re = ∑' n : ℕ, 1 / ((n + 1 : ℝ) ^ x) := by
    simpa [hz, term_eq_ofRealC x] using
      (re_tsum_ofReal (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)))
  rw [hre]
  have hsum : Summable (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ x)) :=
    summable_one_div_nat_add_rpow' (x := x) hx
  have hnonneg : ∀ n : ℕ, 0 ≤ 1 / ((n + 1 : ℝ) ^ x) := terms_nonneg x
  have hrange : ∑ n ∈ Finset.range 1, (1 : ℝ) / ((n + 1 : ℝ) ^ x) = 1 := by
    simp
  have hnonneg' : ∀ n ∉ Finset.range 1, 0 ≤ (1 : ℝ) / ((n + 1 : ℝ) ^ x) := fun n _ => hnonneg n
  have hsumle := hsum.sum_le_tsum (s := Finset.range 1) hnonneg'
  rwa [hrange] at hsumle

/-- The norm of $\zeta(x)$ for real $x > 1$ is at least $1$. -/
lemma one_le_norm_zeta_ofReal (x : ℝ) (hx : 1 < x) : 1 ≤ norm (riemannZeta (x : ℂ)) := by
  have hre := one_le_zeta_ofReal x hx
  have := Complex.re_le_norm (riemannZeta (x : ℂ))
  linarith

/-- Explicit unconditional lower bound $1 / \|\zeta(\sigma)\| \le \|\zeta(\sigma + it)\|$ for any $\sigma > 1$. -/
theorem inv_norm_zeta_le_norm_zeta (σ t : ℝ) (hσ : 1 < σ) :
    1 / norm (riemannZeta (σ : ℂ)) ≤ norm (riemannZeta (σ + t * Complex.I)) := by
  have h2σ : 1 < 2 * σ := by linarith
  have h1 : 1 ≤ norm (riemannZeta (2 * σ : ℝ)) := one_le_norm_zeta_ofReal (2 * σ) h2σ
  have hpos_σ : 0 < norm (riemannZeta (σ : ℂ)) := by
    apply norm_pos_iff.mpr
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [hσ]
  have h_div_le : 1 / norm (riemannZeta (σ : ℂ)) ≤ norm (riemannZeta (2 * σ : ℝ)) / norm (riemannZeta (σ : ℂ)) := by
    exact div_le_div_of_nonneg_right h1 (le_of_lt hpos_σ)
  have h_ratio_norm : norm (riemannZeta (2 * σ : ℝ)) / norm (riemannZeta (σ : ℂ)) =
      norm (riemannZeta (2 * σ : ℝ) / riemannZeta (σ : ℂ)) := by
    rw [norm_div]
  rw [h_ratio_norm] at h_div_le
  exact le_trans h_div_le (zeta_lower_bound_general σ t hσ)


/-- Strict upper bound on $\zeta(z)$ along the full geometric disk of radius $7\theta(t)/8$,
using local regularity of $\theta$ and $\varphi$ at heights near $t$. -/
lemma zeta_bound_on_disk_general (θ φ : ℝ → ℝ)
    (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2)
    (hθloc : ∀ t t', 3 ≤ t → |t' - t| ≤ 1 → θ t / 2 ≤ θ t')
    (hφloc : ∀ t t', 3 ≤ t → |t' - t| ≤ 1 → φ t' ≤ 2 * φ t)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 → ‖riemannZeta (σ + t * Complex.I)‖ ≤ Real.exp (φ |t|))
    (t : ℝ) (ht : 6 ≤ t) (z : ℂ)
    (hz : z ∈ Metric.closedBall ((1 + θ t / 2 : ℝ) + t * Complex.I) (7 * θ t / 8)) :
    ‖riemannZeta z‖ < Real.exp (2 * φ t) + 1 := by
  have ht3 : 3 ≤ t := by linarith
  have hθt := hθ t ht3
  set c : ℂ := (1 + θ t / 2 : ℝ) + t * Complex.I
  have hz_dist : dist z c ≤ 7 * θ t / 8 := Metric.mem_closedBall.mp hz
  have h_norm : ‖z - c‖ ≤ 7 * θ t / 8 := by
    rw [dist_eq] at hz_dist
    exact hz_dist
  have h_im_dist : |z.im - t| ≤ 7 * θ t / 8 := by
    have h1 : z.im - t = (z - c).im := by simp [c]
    rw [h1]
    exact Complex.abs_im_le_norm (z - c) |>.trans h_norm
  have hR_le_half : 7 * θ t / 8 ≤ 7 / 16 := by linarith [hθt.2]
  have hR_le_1 : 7 * θ t / 8 ≤ 1 := by linarith [hR_le_half]
  have h_im_le_1 : |z.im - t| ≤ 1 := le_trans h_im_dist hR_le_1
  have h_im_gt : 5 ≤ z.im := by
    have : t - 7 * θ t / 8 ≤ z.im := by
      have := (abs_le.mp h_im_dist).1
      linarith
    linarith [hR_le_half]
  have h_abs_im : |z.im| = z.im := abs_of_pos (by linarith)
  have h_abs_im_ge3 : 3 ≤ |z.im| := by
    rw [h_abs_im]
    linarith
  have h_diff_abs : |abs z.im - t| ≤ 1 := by
    rw [h_abs_im]
    exact h_im_le_1
  have hθ_near := hθloc t |z.im| ht3 h_diff_abs
  have hφ_near := hφloc t |z.im| ht3 h_diff_abs
  have h_re_dist : |z.re - (1 + θ t / 2)| ≤ 7 * θ t / 8 := by
    have h1 : z.re - (1 + θ t / 2) = (z - c).re := by simp [c]
    rw [h1]
    exact Complex.abs_re_le_norm (z - c) |>.trans h_norm
  have h_re_bounds := abs_le.mp h_re_dist
  have hσ_ge : 1 - θ |z.im| ≤ z.re := by
    have h1 : 1 - θ t / 2 ≤ z.re := by linarith [h_re_bounds.1]
    have h2 : 1 - θ |z.im| ≤ 1 - θ t / 2 := by linarith [hθ_near]
    linarith
  have hσ_le : z.re ≤ 2 := by
    have : z.re ≤ 1 + θ t / 2 + 7 * θ t / 8 := by linarith [h_re_bounds.2]
    linarith [hθt.2]
  have hz_eq : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
  have hζ_bound := hζ z.re z.im h_abs_im_ge3 hσ_ge hσ_le
  rw [← hz_eq] at hζ_bound
  have h_exp_le : Real.exp (φ |z.im|) ≤ Real.exp (2 * φ t) :=
    Real.exp_le_exp.mpr hφ_near
  have h_lt : Real.exp (2 * φ t) < Real.exp (2 * φ t) + 1 := lt_add_one _
  exact lt_of_le_of_lt (le_trans hζ_bound h_exp_le) h_lt

lemma re_div_zero_pos (z ρ : ℂ) (h : ρ.re < z.re) : 0 ≤ (1 / (z - ρ)).re := by
  rw [re_one_div]
  have hpos : 0 < (z - ρ).re := sub_pos.mpr (by simpa using h)
  have hsq_pos : 0 < (z - ρ).re ^ 2 + (z - ρ).im ^ 2 := by
    have : 0 < (z - ρ).re ^ 2 := sq_pos_of_ne_zero (ne_of_gt hpos)
    have : 0 ≤ (z - ρ).im ^ 2 := sq_nonneg _
    positivity
  exact div_nonneg (le_of_lt hpos) (le_of_lt hsq_pos)

lemma re_div_same_im (z ρ : ℂ) (hre : ρ.re < z.re) (him : z.im = ρ.im) :
    (1 / (z - ρ)).re = 1 / (z.re - ρ.re) := by
  rw [re_one_div]
  have him_zero : (z - ρ).im = 0 := by simp [him]
  have hre_eq : (z - ρ).re = z.re - ρ.re := by simp
  have hne : z.re - ρ.re ≠ 0 := ne_of_gt (sub_pos.mpr hre)
  rw [him_zero, hre_eq]
  have : (z.re - ρ.re)^2 + (0:ℝ)^2 = (z.re - ρ.re)^2 := by ring
  rw [this]
  exact div_pow_two (z.re - ρ.re)

lemma re_sum_zeros_nonneg (S : Finset ℂ) (z : ℂ) (hz : ∀ ρ ∈ S, ρ.re < z.re) :
    0 ≤ (∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))).re := by
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro ρ hρ
  have h_div : (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)) =
      ((analyticOrderAt riemannZeta ρ).toNat : ℂ) * (1 / (z - ρ)) := by
    rw [div_eq_mul_one_div]
  rw [h_div]
  have h_re : (((analyticOrderAt riemannZeta ρ).toNat : ℂ) * (1 / (z - ρ))).re =
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * (1 / (z - ρ)).re := by
    simp
  rw [h_re]
  exact mul_nonneg (Nat.cast_nonneg _) (re_div_zero_pos z ρ (hz ρ hρ))

lemma re_sum_zeros_ge_single (S : Finset ℂ) (z ρ₀ : ℂ) (hmem : ρ₀ ∈ S)
    (hz : ∀ ρ ∈ S, ρ.re < z.re) (him : z.im = ρ₀.im)
    (hm : 1 ≤ (analyticOrderAt riemannZeta ρ₀).toNat) :
    1 / (z.re - ρ₀.re) ≤ (∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))).re := by
  rw [Complex.re_sum]
  have h_split : ∑ x ∈ S, (((analyticOrderAt riemannZeta x).toNat : ℂ) / (z - x)).re =
      (((analyticOrderAt riemannZeta ρ₀).toNat : ℂ) / (z - ρ₀)).re +
      ∑ x ∈ S.erase ρ₀, (((analyticOrderAt riemannZeta x).toNat : ℂ) / (z - x)).re := by
    exact (Finset.add_sum_erase S (fun x => (((analyticOrderAt riemannZeta x).toNat : ℂ) / (z - x)).re) hmem).symm
  rw [h_split]
  have h_nonneg : 0 ≤ ∑ x ∈ S.erase ρ₀, (((analyticOrderAt riemannZeta x).toNat : ℂ) / (z - x)).re := by
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρ_in : ρ ∈ S := Finset.mem_of_mem_erase hρ
    have h_div : (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)) =
        ((analyticOrderAt riemannZeta ρ).toNat : ℂ) * (1 / (z - ρ)) := by
      rw [div_eq_mul_one_div]
    rw [h_div]
    have h_re : (((analyticOrderAt riemannZeta ρ).toNat : ℂ) * (1 / (z - ρ))).re =
        ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * (1 / (z - ρ)).re := by
      simp
    rw [h_re]
    exact mul_nonneg (Nat.cast_nonneg _) (re_div_zero_pos z ρ (hz ρ hρ_in))
  have h_ρ0 : 1 / (z.re - ρ₀.re) ≤ (((analyticOrderAt riemannZeta ρ₀).toNat : ℂ) / (z - ρ₀)).re := by
    have h_div : (((analyticOrderAt riemannZeta ρ₀).toNat : ℂ) / (z - ρ₀)) =
        ((analyticOrderAt riemannZeta ρ₀).toNat : ℂ) * (1 / (z - ρ₀)) := by
      rw [div_eq_mul_one_div]
    rw [h_div]
    have h_re : (((analyticOrderAt riemannZeta ρ₀).toNat : ℂ) * (1 / (z - ρ₀))).re =
        ((analyticOrderAt riemannZeta ρ₀).toNat : ℝ) * (1 / (z - ρ₀)).re := by
      simp
    rw [h_re, re_div_same_im z ρ₀ (hz ρ₀ hmem) him]
    have h_pos : 0 < 1 / (z.re - ρ₀.re) := by
      have : 0 < z.re - ρ₀.re := sub_pos.mpr (hz ρ₀ hmem)
      exact one_div_pos.mpr this
    have h_m_le : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta ρ₀).toNat : ℝ) := by
      exact_mod_cast hm
    calc
      1 / (z.re - ρ₀.re) = 1 * (1 / (z.re - ρ₀.re)) := by ring
      _ ≤ ((analyticOrderAt riemannZeta ρ₀).toNat : ℝ) * (1 / (z.re - ρ₀.re)) :=
        mul_le_mul_of_nonneg_right h_m_le (le_of_lt h_pos)
  linarith

lemma neg_re_logDeriv_le_sum_bound (z : ℂ) (S : Finset ℂ) (E : ℝ)
    (h_dist : ‖logDerivZeta z - ∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ ≤ E) :
    (-logDerivZeta z).re ≤ E - (∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))).re := by
  have h_re := Complex.re_le_norm (∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)) - logDerivZeta z)
  have h_norm_eq : ‖∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)) - logDerivZeta z‖ =
      ‖logDerivZeta z - ∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ := by
    rw [← norm_neg]
    congr 1
    ring
  rw [h_norm_eq] at h_re
  have h_le : (∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)) - logDerivZeta z).re ≤ E :=
    le_trans h_re h_dist
  have h_sub_re : (∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)) - logDerivZeta z).re =
      (∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))).re - (logDerivZeta z).re := by
    simp
  rw [h_sub_re] at h_le
  rw [Complex.neg_re]
  linarith

lemma neg_re_logDeriv_le_of_nonneg (z : ℂ) (S : Finset ℂ) (E : ℝ)
    (h_dist : ‖logDerivZeta z - ∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ ≤ E)
    (hz : ∀ ρ ∈ S, ρ.re < z.re) :
    (-logDerivZeta z).re ≤ E := by
  have h1 := neg_re_logDeriv_le_sum_bound z S E h_dist
  have h2 := re_sum_zeros_nonneg S z hz
  linarith

lemma neg_re_logDeriv_le_single (z ρ₀ : ℂ) (S : Finset ℂ) (E : ℝ)
    (h_dist : ‖logDerivZeta z - ∑ ρ ∈ S, (((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ ≤ E)
    (hmem : ρ₀ ∈ S) (hz : ∀ ρ ∈ S, ρ.re < z.re) (him : z.im = ρ₀.im)
    (hm : 1 ≤ (analyticOrderAt riemannZeta ρ₀).toNat) :
    (-logDerivZeta z).re ≤ - (1 / (z.re - ρ₀.re)) + E := by
  have h1 := neg_re_logDeriv_le_sum_bound z S E h_dist
  have h2 := re_sum_zeros_ge_single S z ρ₀ hmem hz him hm
  linarith

/-- The positive geometric constant in the Borel–Carathéodory logarithmic derivative expansion. -/
noncomputable def K_geom : ℝ := 3200 + 48 / (13 * Real.log (7 / 6))

/-- Positivity of the geometric factor $K_{\mathrm{geom}} > 0$. -/
lemma K_geom_pos : 0 < K_geom := by
  have h76 : (1 : ℝ) < 7 / 6 := by norm_num
  have hlog : 0 < Real.log (7 / 6) := Real.log_pos h76
  have h13 : 0 < (13 : ℝ) := by norm_num
  have hden : 0 < 13 * Real.log (7 / 6) := mul_pos h13 hlog
  have hfrac : 0 < 48 / (13 * Real.log (7 / 6)) := div_pos (by norm_num) hden
  have : 0 < (3200 : ℝ) := by norm_num
  exact add_pos this hfrac

/-- Exact algebraic evaluation of the geometric coefficient in `log_Deriv_Expansion_Zeta_general`
with radii $r_1 = \theta/2, r = 5\theta/8, R_1 = 3\theta/4, R = 7\theta/8$. -/
lemma geom_factor_eval (θ : ℝ) (hθpos : 0 < θ) :
    let r1 := θ / 2
    let r := 5 * θ / 8
    let R1 := 3 * θ / 4
    let R := 7 * θ / 8
    16 * r^2 / ((r - r1)^3) + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) = K_geom / θ := by
  intro r1 r R1 R
  have hθne : θ ≠ 0 := ne_of_gt hθpos
  have hlog_ne : Real.log (7 / 6) ≠ 0 := by
    apply ne_of_gt
    exact Real.log_pos (by norm_num)
  have h1 : 16 * r^2 / ((r - r1)^3) = 3200 / θ := by
    dsimp [r, r1]
    have hdiff : 5 * θ / 8 - θ / 2 = θ / 8 := by linarith
    rw [hdiff]
    have : (θ / 8)^3 = θ^3 / 512 := by ring
    rw [this]
    have : (5 * θ / 8)^2 = 25 * θ^2 / 64 := by ring
    rw [this]
    field_simp
    norm_num
  have h2 : 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) = (48 / (13 * Real.log (7 / 6))) / θ := by
    dsimp [R, R1]
    have hR_div : (7 * θ / 8) / (3 * θ / 4) = 7 / 6 := by
      field_simp
      norm_num
    have hdiff : (7 * θ / 8)^2 / (3 * θ / 4) - 3 * θ / 4 = 13 * θ / 48 := by
      field_simp
      ring
    rw [hR_div, hdiff]
    field_simp
  dsimp [K_geom]
  rw [h1, h2, ← add_div]

/-- Strict ordering of the nested disk radii for any $\theta \in (0, 1/2]$. -/
lemma geom_radii_bounds (θ : ℝ) (hθpos : 0 < θ) (hθle : θ ≤ 1 / 2) :
    let r1 := θ / 2
    let r := 5 * θ / 8
    let R1 := 3 * θ / 4
    let R := 7 * θ / 8
    0 < r1 ∧ r1 < r ∧ 0 < r ∧ r < R1 ∧ 0 < R1 ∧ R1 < R ∧ R < 1 := by
  dsimp
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Classical residue bound at the pole $s = 1$: $(-(\zeta'/\zeta)(1+\delta)).\mathrm{re} \le 1/\delta + C_0$. -/
lemma neg_re_logDeriv_pole_bound :
    ∃ C₀ > 1, ∀ (δ : ℝ), 0 < δ → (-logDerivZeta ((1 : ℂ) + δ)).re ≤ 1 / δ + C₀ := by
  rcases Z0boundRe_const3 with ⟨C₀, hC₀gt1, hC₀⟩
  use C₀, hC₀gt1
  intro δ hδ
  have := hC₀ δ hδ
  linarith

/-- Recombination of the 3-4-1 trigonometric inequality $0 \le 3 Z_0 + 4 Z_1 + Z_2$
into the fundamental zero-free region inequality. -/
lemma trig_341_inequality_combine (δ t : ℝ) (hδ : 0 < δ) (σ : ℝ) (C₀ Et E2t : ℝ)
    (hZ0 : (-logDerivZeta ((1 : ℂ) + δ)).re ≤ 1 / δ + C₀)
    (hZ1 : (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re ≤ - (1 / (1 + δ - σ)) + Et)
    (hZ2 : (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re ≤ E2t) :
    0 ≤ 3 / δ - 4 / (1 + δ - σ) + (3 * C₀ + 4 * Et + E2t) := by
  have hpos := Z341pos t δ hδ
  have h3 : 3 / δ = 3 * (1 / δ) := by ring
  have h4 : 4 / (1 + δ - σ) = 4 * (1 / (1 + δ - σ)) := by ring
  rw [h3, h4]
  linarith

lemma norm_zeta_one_add_half_theta_le (θ : ℝ) (hθpos : 0 < θ) (hθle : θ ≤ 1 / 2) :
    norm (riemannZeta ((1 + θ / 2 : ℝ) : ℂ)) ≤ 3 / θ := by
  let s : ℂ := ((1 + θ / 2 : ℝ) : ℂ)
  have hs_re : 1 / 10 < s.re := by
    dsimp [s]
    have : 0 < θ / 2 := by linarith
    have : 1 < 1 + θ / 2 := by linarith
    linarith
  have hs_ne : s ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [h]; simp
    dsimp [s] at this
    linarith
  have hzb := lem_zetaBound3 s hs_re hs_ne
  have h_norm_s_sub_1 : ‖s - 1‖ = θ / 2 := by
    dsimp [s]
    have : (((1 + θ / 2 : ℝ) : ℂ) - 1) = ((θ / 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this, Complex.norm_real]
    exact abs_of_pos (by linarith)
  have h_s_re : s.re = 1 + θ / 2 := rfl
  have h_norm_s : ‖s‖ = 1 + θ / 2 := by
    dsimp [s]
    rw [Complex.norm_real]
    exact abs_of_pos (by linarith)
  have h_div_re : ‖s‖ / s.re = 1 := by
    rw [h_norm_s, h_s_re]
    exact div_self (by linarith)
  rw [h_norm_s_sub_1, h_div_re] at hzb
  have h_one_div : 1 / (θ / 2) = 2 / θ := by ring
  rw [h_one_div] at hzb
  have h_alg : 1 + 2 / θ + 1 = 2 + 2 / θ := by ring
  rw [h_alg] at hzb
  have h2_le : 2 ≤ 1 / θ := by
    have h_mul : 2 * θ ≤ 1 := by linarith
    exact (le_div_iff₀ hθpos).mpr (by linarith)
  have h_sum : 2 + 2 / θ ≤ 1 / θ + 2 / θ := by linarith
  have h_three : 1 / θ + 2 / θ = 3 / θ := by ring
  rw [h_three] at h_sum
  exact le_trans hzb h_sum

lemma inv_norm_zeta_center_le (θ t : ℝ) (hθpos : 0 < θ) (hθle : θ ≤ 1 / 2) :
    1 / norm (riemannZeta ((1 + θ / 2 : ℝ) + t * Complex.I)) ≤ 3 / θ := by
  have hσ : 1 < 1 + θ / 2 := by linarith
  have h1 : 1 / norm (riemannZeta ((1 + θ / 2 : ℝ) : ℂ)) ≤
      norm (riemannZeta ((1 + θ / 2 : ℝ) + t * Complex.I)) :=
    inv_norm_zeta_le_norm_zeta (1 + θ / 2) t hσ
  rw [one_div] at h1
  have h2 := norm_zeta_one_add_half_theta_le θ hθpos hθle
  have hpos_norm : 0 < norm (riemannZeta ((1 + θ / 2 : ℝ) + t * Complex.I)) := by
    apply norm_pos_iff.mpr
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [hσ]
  have hpos_real : 0 < norm (riemannZeta ((1 + θ / 2 : ℝ) : ℂ)) := by
    apply norm_pos_iff.mpr
    apply riemannZeta_ne_zero_of_one_lt_re
    simp [hσ]
  have h_swap : (norm (riemannZeta ((1 + θ / 2 : ℝ) + t * Complex.I)))⁻¹ ≤
      norm (riemannZeta ((1 + θ / 2 : ℝ) : ℂ)) :=
    (inv_le_comm₀ hpos_real hpos_norm).mp h1
  have h_div : 1 / norm (riemannZeta ((1 + θ / 2 : ℝ) + t * Complex.I)) =
      (norm (riemannZeta ((1 + θ / 2 : ℝ) + t * Complex.I)))⁻¹ := by rw [one_div]
  rw [h_div]
  exact le_trans h_swap h2

lemma zeta_bound_on_disk_general' (θ φ : ℝ → ℝ)
    (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2)
    (hθloc : ∀ t t', 3 ≤ t → |t' - t| ≤ 1 → θ t / 2 ≤ θ t')
    (hφloc : ∀ t t', 3 ≤ t → |t' - t| ≤ 1 → φ t' ≤ 2 * φ t)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 → ‖riemannZeta (σ + t * Complex.I)‖ ≤ Real.exp (φ |t|))
    (t : ℝ) (ht : 6 ≤ |t|) (z : ℂ)
    (hz : z ∈ Metric.closedBall ((1 + θ |t| / 2 : ℝ) + t * Complex.I) (7 * θ |t| / 8)) :
    ‖riemannZeta z‖ < Real.exp (2 * φ |t|) + 1 := by
  have ht3 : 3 ≤ |t| := by linarith
  have hθt := hθ |t| ht3
  set c : ℂ := (1 + θ |t| / 2 : ℝ) + t * Complex.I
  have hz_dist : dist z c ≤ 7 * θ |t| / 8 := Metric.mem_closedBall.mp hz
  have h_norm : ‖z - c‖ ≤ 7 * θ |t| / 8 := by
    rw [dist_eq] at hz_dist
    exact hz_dist
  have h_im_dist : |z.im - t| ≤ 7 * θ |t| / 8 := by
    have h1 : z.im - t = (z - c).im := by simp [c]
    rw [h1]
    exact Complex.abs_im_le_norm (z - c) |>.trans h_norm
  have hR_le_half : 7 * θ |t| / 8 ≤ 7 / 16 := by linarith [hθt.2]
  have hR_le_1 : 7 * θ |t| / 8 ≤ 1 := by linarith [hR_le_half]
  have h_im_le_1 : |z.im - t| ≤ 1 := le_trans h_im_dist hR_le_1
  have h_diff_abs : |abs z.im - abs t| ≤ 1 :=
    le_trans (abs_abs_sub_abs_le_abs_sub z.im t) h_im_le_1
  have h_abs_im_ge3 : 3 ≤ |z.im| := by
    have := (abs_le.mp h_diff_abs).1
    linarith
  have hθ_near := hθloc |t| |z.im| ht3 h_diff_abs
  have hφ_near := hφloc |t| |z.im| ht3 h_diff_abs
  have h_re_dist : |z.re - (1 + θ |t| / 2)| ≤ 7 * θ |t| / 8 := by
    have h1 : z.re - (1 + θ |t| / 2) = (z - c).re := by simp [c]
    rw [h1]
    exact Complex.abs_re_le_norm (z - c) |>.trans h_norm
  have h_re_bounds := abs_le.mp h_re_dist
  have hσ_ge : 1 - θ |z.im| ≤ z.re := by
    have h1 : 1 - θ |t| / 2 ≤ z.re := by linarith [h_re_bounds.1]
    have h2 : 1 - θ |z.im| ≤ 1 - θ |t| / 2 := by linarith [hθ_near]
    linarith
  have hσ_le : z.re ≤ 2 := by
    have : z.re ≤ 1 + θ |t| / 2 + 7 * θ |t| / 8 := by linarith [h_re_bounds.2]
    linarith [hθt.2]
  have hz_eq : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
  have hζ_bound := hζ z.re z.im h_abs_im_ge3 hσ_ge hσ_le
  rw [← hz_eq] at hζ_bound
  have h_exp_le : Real.exp (φ |z.im|) ≤ Real.exp (2 * φ |t|) :=
    Real.exp_le_exp.mpr hφ_near
  have h_lt : Real.exp (2 * φ |t|) < Real.exp (2 * φ |t|) + 1 := lt_add_one _
  exact lt_of_le_of_lt (le_trans hζ_bound h_exp_le) h_lt

lemma log_B_div_norm_zeta_le (θ φ : ℝ → ℝ)
    (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2)
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t)
    (hθφ : ∀ t, 3 ≤ t → Real.log (3 / θ t) ≤ φ t)
    (t : ℝ) (ht : 6 ≤ |t|) :
    Real.log ((Real.exp (2 * φ |t|) + 1) / norm (riemannZeta ((1 + θ |t| / 2 : ℝ) + t * Complex.I))) ≤
    4 * φ |t| := by
  have ht3 : 3 ≤ |t| := by linarith
  have hθpos := (hθ |t| ht3).1
  have hθle := (hθ |t| ht3).2
  have hφge := hφ |t| ht3
  have hθφ_val := hθφ |t| ht3
  set c : ℂ := (1 + θ |t| / 2 : ℝ) + t * Complex.I
  set B : ℝ := Real.exp (2 * φ |t|) + 1
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hc_re : 1 < c.re := by
    dsimp [c]
    simp
    linarith
  have hζc_pos : 0 < norm (riemannZeta c) := by
    apply norm_pos_iff.mpr
    exact riemannZeta_ne_zero_of_one_lt_re hc_re
  have hinv_le : 1 / norm (riemannZeta c) ≤ 3 / θ |t| :=
    inv_norm_zeta_center_le (θ |t|) t hθpos hθle
  have h3θ_pos : 0 < 3 / θ |t| := div_pos (by norm_num) hθpos
  have hdiv_eq : B / norm (riemannZeta c) = B * (1 / norm (riemannZeta c)) := by ring
  have hdiv_pos : 0 < B / norm (riemannZeta c) := div_pos hB_pos hζc_pos
  have hprod_le : B / norm (riemannZeta c) ≤ B * (3 / θ |t|) := by
    rw [hdiv_eq]
    exact mul_le_mul_of_nonneg_left hinv_le (le_of_lt hB_pos)
  have hlog_le1 : Real.log (B / norm (riemannZeta c)) ≤ Real.log (B * (3 / θ |t|)) :=
    Real.log_le_log hdiv_pos hprod_le
  have hlog_mul : Real.log (B * (3 / θ |t|)) = Real.log B + Real.log (3 / θ |t|) :=
    Real.log_mul (ne_of_gt hB_pos) (ne_of_gt h3θ_pos)
  have h2φ_nonneg : 0 ≤ 2 * φ |t| := by linarith
  have hexp_ge_1 : 1 ≤ Real.exp (2 * φ |t|) := by
    have := Real.exp_le_exp.mpr h2φ_nonneg
    simpa using this
  have hB_le : B ≤ 2 * Real.exp (2 * φ |t|) := by
    dsimp [B]
    linarith
  have h2_le_e : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2exp_le : 2 * Real.exp (2 * φ |t|) ≤ Real.exp 1 * Real.exp (2 * φ |t|) :=
    mul_le_mul_of_nonneg_right h2_le_e (by positivity)
  have he_mul : Real.exp 1 * Real.exp (2 * φ |t|) = Real.exp (2 * φ |t| + 1) := by
    rw [← Real.exp_add]
    ring_nf
  have hB_le_exp : B ≤ Real.exp (2 * φ |t| + 1) := by
    linarith [hB_le, h2exp_le, he_mul]
  have hlog_B : Real.log B ≤ 2 * φ |t| + 1 := by
    have hlog := Real.log_le_log hB_pos hB_le_exp
    rwa [Real.log_exp] at hlog
  have hlog_B_le : Real.log B ≤ 3 * φ |t| := by
    linarith [hlog_B, hφge]
  rw [hlog_mul] at hlog_le1
  linarith [hlog_le1, hlog_B_le, hθφ_val]

lemma logDerivZeta_expansion_bound (θ φ : ℝ → ℝ)
    (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2)
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t)
    (hθloc : ∀ t t', 3 ≤ t → |t' - t| ≤ 1 → θ t / 2 ≤ θ t')
    (hφloc : ∀ t t', 3 ≤ t → |t' - t| ≤ 1 → φ t' ≤ 2 * φ t)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 → ‖riemannZeta (σ + t * Complex.I)‖ ≤ Real.exp (φ |t|))
    (hθφ : ∀ t, 3 ≤ t → Real.log (3 / θ t) ≤ φ t)
    (t : ℝ) (ht : 6 ≤ |t|)
    (hfin : (zerosetKfRc (3 * θ |t| / 4) ((1 + θ |t| / 2 : ℝ) + t * Complex.I) riemannZeta).Finite)
    (z : ℂ) (hz_ball : z ∈ Metric.closedBall ((1 + θ |t| / 2 : ℝ) + t * Complex.I) (θ |t| / 2))
    (hz_not : z ∉ zerosetKfRc (3 * θ |t| / 4) ((1 + θ |t| / 2 : ℝ) + t * Complex.I) riemannZeta) :
    ‖logDerivZeta z - ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ)‖ ≤
      4 * K_geom * (φ |t| / θ |t|) := by
  have ht3 : 3 ≤ |t| := by linarith
  have hθpos := (hθ |t| ht3).1
  have hθle := (hθ |t| ht3).2
  have hradii := geom_radii_bounds (θ |t|) hθpos hθle
  rcases hradii with ⟨hr1_pos, hr1_lt_r, hr_pos, hr_lt_R1, hR1_pos, hR1_lt_R, hR_lt_1⟩
  set c : ℂ := (1 + θ |t| / 2 : ℝ) + t * Complex.I
  set B : ℝ := Real.exp (2 * φ |t|) + 1
  have hB_gt1 : 1 < B := by
    dsimp [B]
    have : 0 < Real.exp (2 * φ |t|) := Real.exp_pos _
    linarith
  have hc_re : 1 < c.re := by
    dsimp [c]
    simp
    linarith
  have hc_im : 3 ≤ |c.im| := by
    dsimp [c]
    simp
    linarith
  have h_bound : ∀ w ∈ Metric.closedBall c (7 * θ |t| / 8), ‖riemannZeta w‖ < B := by
    intro w hw
    exact zeta_bound_on_disk_general' θ φ hθ hθloc hφloc hζ t ht w hw
  have hz_mem : z ∈ Metric.closedBall c (θ |t| / 2) \ zerosetKfRc (3 * θ |t| / 4) c riemannZeta :=
    ⟨hz_ball, hz_not⟩
  have hexp := log_Deriv_Expansion_Zeta_general
    (θ |t| / 2) (5 * θ |t| / 8) (3 * θ |t| / 4) (7 * θ |t| / 8)
    hr1_pos hr1_lt_r hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1
    c hc_re hc_im B hB_gt1 h_bound hfin z hz_mem
  have hgeom := geom_factor_eval (θ |t|) hθpos
  rw [hgeom] at hexp
  have hlog := log_B_div_norm_zeta_le θ φ hθ hφ hθφ t ht
  have hKpos := K_geom_pos
  have h_mul_le : (K_geom / θ |t|) * Real.log (B / ‖riemannZeta c‖) ≤
      (K_geom / θ |t|) * (4 * φ |t|) := by
    apply mul_le_mul_of_nonneg_left hlog
    apply div_nonneg (le_of_lt hKpos) (le_of_lt hθpos)
  have h_rearr : (K_geom / θ |t|) * (4 * φ |t|) = 4 * K_geom * (φ |t| / θ |t|) := by
    ring
  rw [h_rearr] at h_mul_le
  exact le_trans hexp h_mul_le

lemma error_at_2t_le (θ φ : ℝ → ℝ)
    (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2)
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t)
    (hφθ : ∀ t, 3 ≤ t → φ (2 * t) ≤ 2 * φ t)
    (hθdyadic : ∀ t, 3 ≤ t → θ t ≤ 2 * θ (2 * t))
    (t : ℝ) (ht : 6 ≤ |t|) :
    4 * K_geom * (φ |2 * t| / θ |2 * t|) ≤ 16 * K_geom * (φ |t| / θ |t|) := by
  have ht3 : 3 ≤ |t| := by linarith
  have h_abs_2t : |2 * t| = 2 * |t| := by
    rw [abs_mul]
    have : |(2:ℝ)| = 2 := by norm_num
    rw [this]
  rw [h_abs_2t]
  have hφ_2t := hφθ |t| ht3
  have hθ_2t := hθdyadic |t| ht3
  have hθpos := (hθ |t| ht3).1
  have ht_ge3_2t : 3 ≤ 2 * |t| := by linarith
  have hθ2t_pos := (hθ (2 * |t|) ht_ge3_2t).1
  have hφ_nonneg : 0 ≤ φ |t| := by linarith [hφ |t| ht3]
  have hφ2t_nonneg : 0 ≤ φ (2 * |t|) := by linarith [hφ (2 * |t|) ht_ge3_2t]
  have h_inv_θ : 1 / θ (2 * |t|) ≤ 2 / θ |t| := by
    rw [div_le_div_iff₀ hθ2t_pos hθpos]
    linarith
  have h_ratio_le : φ (2 * |t|) / θ (2 * |t|) ≤ 4 * (φ |t| / θ |t|) := by
    have h1 : φ (2 * |t|) / θ (2 * |t|) = φ (2 * |t|) * (1 / θ (2 * |t|)) := by ring
    have h2 : 4 * (φ |t| / θ |t|) = (2 * φ |t|) * (2 / θ |t|) := by ring
    rw [h1, h2]
    have h_step1 : φ (2 * |t|) * (1 / θ (2 * |t|)) ≤ (2 * φ |t|) * (1 / θ (2 * |t|)) :=
      mul_le_mul_of_nonneg_right hφ_2t (by positivity)
    have h_step2 : (2 * φ |t|) * (1 / θ (2 * |t|)) ≤ (2 * φ |t|) * (2 / θ |t|) :=
      mul_le_mul_of_nonneg_left h_inv_θ (by linarith)
    exact le_trans h_step1 h_step2
  have hKpos := K_geom_pos
  have h4K_nonneg : 0 ≤ 4 * K_geom := by linarith
  have h_mul := mul_le_mul_of_nonneg_left h_ratio_le h4K_nonneg
  have h_rearr : 4 * K_geom * (4 * (φ |t| / θ |t|)) = 16 * K_geom * (φ |t| / θ |t|) := by ring
  rwa [h_rearr] at h_mul

lemma analyticOrderAt_riemannZeta_ge_one (ρ : ℂ) (hzero : riemannZeta ρ = 0) (hρim : 6 ≤ |ρ.im|) :
    1 ≤ (analyticOrderAt riemannZeta ρ).toNat := by
  have h_rho_ne_one : ρ ≠ (1 : ℂ) := by
    intro h
    have : ρ.im = 0 := by rw [h]; simp
    rw [this, abs_zero] at hρim
    norm_num at hρim
  have hAnal : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ h_rho_ne_one
  have hNotEv : ¬ (∀ᶠ z in nhds ρ, riemannZeta z = 0) :=
    riemannZeta_not_eventually_zero_of_ne_one h_rho_ne_one
  exact analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero hAnal hzero hNotEv

/-- General zero-free region theorem for the Riemann zeta function (Titchmarsh, Theorem 3.10)
from an upper bound on $\zeta(\sigma + it)$, unconditionally without extra axioms or assumptions. -/
theorem zero_free_of_zeta_bound' (θ φ : ℝ → ℝ)
    (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2) (hθanti : AntitoneOn θ (Set.Ici 3))
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t) (hφmono : MonotoneOn φ (Set.Ici 3))
    (hφθ : ∀ t, 3 ≤ t → φ (2 * t) ≤ 2 * φ t)
    (hθdyadic : ∀ t, 3 ≤ t → θ t ≤ 2 * θ (2 * t))
    (hθφ : ∀ t, 3 ≤ t → Real.log (3 / θ t) ≤ φ t)
    (hθloc : ∀ t t' : ℝ, 3 ≤ t → |t' - t| ≤ 1 → θ t / 2 ≤ θ t')
    (hφloc : ∀ t t' : ℝ, 3 ≤ t → |t' - t| ≤ 1 → φ t' ≤ 2 * φ t)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 → ‖riemannZeta (σ + t * Complex.I)‖ ≤ Real.exp (φ |t|)) :
    ∃ A : ℝ, 0 < A ∧ ∀ (ρ : ℂ), riemannZeta ρ = 0 → 6 ≤ |ρ.im| → ρ.re ≤ 1 - A * θ |ρ.im| / φ |ρ.im| := by
  have _ := hθanti
  have _ := hφmono
  rcases neg_re_logDeriv_pole_bound with ⟨C₀, hC₀gt1, hC₀⟩
  let C : ℝ := 3 * C₀ + 32 * K_geom + 3
  have hKpos := K_geom_pos
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hC_gt1 : 1 < C := by
    dsimp [C]
    have : 3 * (1 : ℝ) < 3 * C₀ := by linarith
    linarith
  have hC_gt4 : 4 < C := by
    dsimp [C]
    have : 3 * (1 : ℝ) < 3 * C₀ := by linarith
    have : 0 < 32 * K_geom := by positivity
    linarith
  apply zero_free_of_341_bound θ φ hθ hφ C hC_gt1
  intro ρ hzero hρim hρre_pos hρre_lt1
  let t := ρ.im
  have ht_ge6 : 6 ≤ |t| := hρim
  have ht_ge3 : 3 ≤ |t| := by linarith
  have hθpos := (hθ |t| ht_ge3).1
  have hθle := (hθ |t| ht_ge3).2
  have hφge := hφ |t| ht_ge3
  let L := φ |t| / θ |t|
  have hLpos : 0 < L := div_pos (by linarith) hθpos
  have hL_ge2 : 2 ≤ L := by
    dsimp [L]
    have h1 : (2 : ℝ) ≤ 1 / θ |t| := (le_div_iff₀ hθpos).mpr (by linarith)
    have h2 : 1 / θ |t| ≤ φ |t| / θ |t| := div_le_div_of_nonneg_right hφge (le_of_lt hθpos)
    exact le_trans h1 h2
  let δ := 1 / (2 * C * L)
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδ_eq : δ = θ |t| / (2 * C * φ |t|) := by
    dsimp [δ, L]
    have hCne : C ≠ 0 := ne_of_gt hCpos
    have hφne : φ |t| ≠ 0 := ne_of_gt (by linarith)
    have hθne : θ |t| ≠ 0 := ne_of_gt hθpos
    field_simp
  by_cases hcaseA : ρ.re ≤ 1 - θ |t| / 4
  · have hden_ge : θ |t| / 4 ≤ 1 + δ - ρ.re := by linarith
    have hden_pos : 0 < 1 + δ - ρ.re := by linarith
    have hfrac_le : 4 / (1 + δ - ρ.re) ≤ 16 / θ |t| := by
      have : 4 / (θ |t| / 4) = 16 / θ |t| := by ring
      rw [← this]
      exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hden_ge
    have h3δ : 3 / δ = 6 * C * L := by
      dsimp [δ]
      have hCne : C ≠ 0 := ne_of_gt hCpos
      have hLne : L ≠ 0 := ne_of_gt hLpos
      field_simp
      ring
    have h6CL_ge : 16 / θ |t| ≤ 6 * C * L := by
      have hCL_ge : 6 * C * (1 / θ |t|) ≤ 6 * C * L := by
        have : 1 / θ |t| ≤ φ |t| / θ |t| := by
          exact div_le_div_of_nonneg_right hφge (le_of_lt hθpos)
        exact mul_le_mul_of_nonneg_left this (by linarith)
      have h16_le : 16 / θ |t| ≤ 6 * C * (1 / θ |t|) := by
        have h16_36 : (16 : ℝ) ≤ 6 * C := by
          dsimp [C]
          linarith
        have hinv_pos : 0 ≤ 1 / θ |t| := le_of_lt (one_div_pos.mpr hθpos)
        have hmul := mul_le_mul_of_nonneg_right h16_36 hinv_pos
        have h1 : 16 / θ |t| = 16 * (1 / θ |t|) := by ring
        have h2 : 6 * C * (1 / θ |t|) = (6 * C) * (1 / θ |t|) := by ring
        rw [h1, h2]
        exact hmul
      exact le_trans h16_le hCL_ge
    have : 4 / (1 + δ - ρ.re) ≤ 3 / δ := by
      rw [h3δ]
      exact le_trans hfrac_le h6CL_ge
    have hCL_nonneg : 0 ≤ C * L := by positivity
    have h_res : 0 ≤ 3 / δ - 4 / (1 + δ - ρ.re) + C * L := by linarith
    exact h_res
  · push Not at hcaseA
    set c_t : ℂ := (1 + θ |t| / 2 : ℝ) + t * Complex.I
    set R1_t : ℝ := 3 * θ |t| / 4
    have hR1_pos : 0 < R1_t := by dsimp [R1_t]; linarith
    have hR1_lt1 : R1_t < 1 := by dsimp [R1_t]; linarith
    have hc_re_gt1 : 1 < c_t.re := by dsimp [c_t]; simp; linarith
    have hfin_t := zeros_finite_general c_t R1_t hR1_pos hR1_lt1 hc_re_gt1
    set S_t := hfin_t.toFinset
    have hρ_in_ball : ρ ∈ Metric.closedBall c_t R1_t := by
      rw [Metric.mem_closedBall, dist_eq]
      have h_diff : ρ - c_t = (((ρ.re - (1 + θ |t| / 2) : ℝ)) : ℂ) := by
        apply Complex.ext <;> simp [c_t, t]
      rw [h_diff, Complex.norm_real, Real.norm_eq_abs]
      have h_re_le : |ρ.re - (1 + θ |t| / 2)| ≤ R1_t := by
        rw [abs_le]
        constructor
        · dsimp [R1_t]
          linarith
        · dsimp [R1_t]
          linarith
      exact h_re_le
    have hρ_in_S : ρ ∈ S_t := by
      have h_mem : ρ ∈ zerosetKfRc R1_t c_t riemannZeta := ⟨hρ_in_ball, hzero⟩
      exact Set.Finite.mem_toFinset hfin_t |>.mpr h_mem
    set z1 : ℂ := (1 + δ) + t * Complex.I
    have hz1_ball : z1 ∈ Metric.closedBall c_t (θ |t| / 2) := by
      rw [Metric.mem_closedBall, dist_eq]
      have h_diff : z1 - c_t = (((δ - θ |t| / 2 : ℝ)) : ℂ) := by
        apply Complex.ext
        · simp [z1, c_t]
        · simp [z1, c_t]
      rw [h_diff, Complex.norm_real, Real.norm_eq_abs]
      have hδ_lt : δ < θ |t| / 2 := by
        rw [hδ_eq]
        have h_den : 2 < 2 * C * φ |t| := by
          have : 1 < C * φ |t| := by nlinarith [hC_gt1, hφge]
          linarith
        exact (div_lt_iff₀ (by positivity)).mpr (by nlinarith [hθpos])
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have hz1_not_zero : riemannZeta z1 ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_lt_re
      dsimp [z1]
      simp
      linarith
    have hz1_not_S : z1 ∉ zerosetKfRc R1_t c_t riemannZeta := fun h => hz1_not_zero h.2
    have hexp1 := logDerivZeta_expansion_bound θ φ hθ hφ hθloc hφloc hζ hθφ t ht_ge6 hfin_t z1 hz1_ball hz1_not_S
    have hz1_zeros_re : ∀ ρ' ∈ S_t, ρ'.re < z1.re := by
      intro ρ' hρ'
      have hρ'_zero : riemannZeta ρ' = 0 := by
        have : ρ' ∈ zerosetKfRc R1_t c_t riemannZeta := by
          simpa [S_t] using hρ'
        exact this.2
      have hnot1 : ¬ (1 ≤ ρ'.re) := fun h => riemannZeta_ne_zero_of_one_le_re h hρ'_zero
      push Not at hnot1
      have : z1.re = 1 + δ := by simp [z1]
      linarith
    have hz1_im_eq : z1.im = ρ.im := by simp [z1, t]
    have hm1 := analyticOrderAt_riemannZeta_ge_one ρ hzero hρim
    have hZ1_bound := neg_re_logDeriv_le_single z1 ρ S_t (4 * K_geom * L) hexp1 hρ_in_S hz1_zeros_re hz1_im_eq hm1
    have hz1_re_eq : z1.re = 1 + δ := by simp [z1]
    rw [hz1_re_eq] at hZ1_bound
    have hz1_def : z1 = (1 : ℂ) + δ + t * Complex.I := by
      apply Complex.ext <;> simp [z1]
    rw [hz1_def] at hZ1_bound
    have h_abs_2t : |2 * t| = 2 * |t| := by
      rw [abs_mul]
      norm_num
    have ht2_ge6 : 6 ≤ |2 * t| := by
      rw [h_abs_2t]
      linarith
    have ht2_ge3 : 3 ≤ |2 * t| := by linarith
    have hθ2t_pos : 0 < θ |2 * t| := (hθ |2 * t| ht2_ge3).1
    set c_2t : ℂ := (1 + θ |2 * t| / 2 : ℝ) + (2 * t : ℝ) * Complex.I
    set R1_2t : ℝ := 3 * θ |2 * t| / 4
    have hR1_2t_pos : 0 < R1_2t := by dsimp [R1_2t]; linarith [hθ2t_pos]
    have hR1_2t_lt1 : R1_2t < 1 := by dsimp [R1_2t]; have := (hθ |2 * t| ht2_ge3).2; linarith
    have hc_2t_re : 1 < c_2t.re := by
      have h_re : c_2t.re = 1 + θ |2 * t| / 2 := by
        dsimp [c_2t]
        simp
      rw [h_re]
      linarith [hθ2t_pos]
    have hfin_2t := zeros_finite_general c_2t R1_2t hR1_2t_pos hR1_2t_lt1 hc_2t_re
    set S_2t := hfin_2t.toFinset
    set z2 : ℂ := (1 + δ) + (2 * t : ℝ) * Complex.I
    have hz2_ball : z2 ∈ Metric.closedBall c_2t (θ |2 * t| / 2) := by
      rw [Metric.mem_closedBall, dist_eq]
      have h_diff : z2 - c_2t = (((δ - θ |2 * t| / 2 : ℝ)) : ℂ) := by
        apply Complex.ext
        · simp [z2, c_2t]
        · simp [z2, c_2t]
      rw [h_diff, Complex.norm_real, Real.norm_eq_abs]
      have hδ_lt_2t : δ < θ |2 * t| / 2 := by
        rw [hδ_eq]
        have hθdy := hθdyadic |t| ht_ge3
        have h4 : 4 < 2 * C * φ |t| := by nlinarith [hC_gt4, hφge]
        have hstep1 : θ |t| / (2 * C * φ |t|) ≤ (2 * θ (2 * |t|)) / (2 * C * φ |t|) :=
          div_le_div_of_nonneg_right hθdy (by positivity)
        rw [← h_abs_2t] at hstep1
        have hstep2 : (2 * θ |2 * t|) / (2 * C * φ |t|) < θ |2 * t| / 2 := by
          have : (2 * θ |2 * t|) / (2 * C * φ |t|) < (2 * θ |2 * t|) / 4 :=
            div_lt_div_of_pos_left (by linarith [hθ2t_pos]) (by norm_num) h4
          have : (2 * θ |2 * t|) / (4 : ℝ) = θ |2 * t| / 2 := by ring
          linarith
        exact lt_of_le_of_lt hstep1 hstep2
      rw [abs_le]
      constructor
      · linarith
      · linarith
    have hz2_not_zero : riemannZeta z2 ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_lt_re
      dsimp [z2]
      simp
      linarith
    have hz2_not_S : z2 ∉ zerosetKfRc R1_2t c_2t riemannZeta := fun h => hz2_not_zero h.2
    have hexp2 := logDerivZeta_expansion_bound θ φ hθ hφ hθloc hφloc hζ hθφ (2 * t) ht2_ge6 hfin_2t z2 hz2_ball hz2_not_S
    have herr2 := error_at_2t_le θ φ hθ hφ hφθ hθdyadic t ht_ge6
    have hexp2_final : ‖logDerivZeta z2 - ∑ ρ ∈ S_2t, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z2 - ρ)‖ ≤
        16 * K_geom * L := le_trans hexp2 herr2
    have hz2_zeros_re : ∀ ρ' ∈ S_2t, ρ'.re < z2.re := by
      intro ρ' hρ'
      have hρ'_zero : riemannZeta ρ' = 0 := by
        have : ρ' ∈ zerosetKfRc R1_2t c_2t riemannZeta := by
          simpa [S_2t] using hρ'
        exact this.2
      have hnot1 : ¬ (1 ≤ ρ'.re) := fun h => riemannZeta_ne_zero_of_one_le_re h hρ'_zero
      push Not at hnot1
      have : z2.re = 1 + δ := by simp [z2]
      linarith
    have hZ2_bound := neg_re_logDeriv_le_of_nonneg z2 S_2t (16 * K_geom * L) hexp2_final hz2_zeros_re
    have hz2_def : z2 = (1 : ℂ) + δ + (2 * t) * Complex.I := by
      apply Complex.ext <;> simp [z2]
    rw [hz2_def] at hZ2_bound
    have hZ0_bound := hC₀ δ hδ_pos
    have hcomb := trig_341_inequality_combine δ t hδ_pos ρ.re C₀ (4 * K_geom * L) (16 * K_geom * L)
      hZ0_bound hZ1_bound hZ2_bound
    have h_err_sum : 3 * C₀ + 4 * (4 * K_geom * L) + 16 * K_geom * L ≤ C * L := by
      dsimp [C]
      have h1 : 3 * C₀ ≤ 3 * C₀ * L := by
        have : 3 * C₀ * 1 ≤ 3 * C₀ * L :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        simpa using this
      have h2 : 4 * (4 * K_geom * L) = 16 * K_geom * L := by ring
      rw [h2]
      have : 3 * C₀ + 16 * K_geom * L + 16 * K_geom * L = 3 * C₀ + 32 * K_geom * L := by ring
      rw [this]
      have : 3 * C₀ + 32 * K_geom * L ≤ (3 * C₀ + 32 * K_geom + 3) * L := by
        have : (3 * C₀ + 32 * K_geom + 3) * L = 3 * C₀ * L + 32 * K_geom * L + 3 * L := by ring
        rw [this]
        linarith
      exact this
    have h_res : 0 ≤ 3 / δ - 4 / (1 + δ - ρ.re) + C * L := by linarith [hcomb, h_err_sum]
    exact h_res

end Erdos1201.MR.Vinogradov

namespace Erdos1201.MR

export Erdos1201.MR.Vinogradov (
  zero_free_algebra
  zero_free_width_pos
  delta_pos_of_pos
  closedBall_c_one_subset_ne_one
  zeta_analytic_on_closedBall
  zeta_bound_on_disk
  zero_free_of_341_bound
  zero_free_of_classical_subordinate
  zero_free_of_zeta_bound
  zero_free_of_zeta_bound'
  zeta_analytic_on_closedBall_1
  log_Deriv_Expansion_Zeta_general
  zeros_finite_general
  re_one_div
  neg_re_le_norm
  div_pow_two
  abs_term_bound_general
  cond_general
  abs_term_inv_bound_general
  abs_zeta_inequality_general
  one_minus_le_inv_one_plus
  p_s_real_lt_one
  term_bound2
  abs_zeta_ratio_eval_general
  zeta_lower_bound_general
  one_le_zeta_ofReal
  one_le_norm_zeta_ofReal
  inv_norm_zeta_le_norm_zeta
  norm_zeta_one_add_half_theta_le
  inv_norm_zeta_center_le
  zeta_bound_on_disk_general
  zeta_bound_on_disk_general'
  log_B_div_norm_zeta_le
  re_div_zero_pos
  re_div_same_im
  re_sum_zeros_nonneg
  re_sum_zeros_ge_single
  neg_re_logDeriv_le_sum_bound
  neg_re_logDeriv_le_of_nonneg
  neg_re_logDeriv_le_single
  K_geom
  K_geom_pos
  geom_factor_eval
  geom_radii_bounds
  logDerivZeta_expansion_bound
  error_at_2t_le
  analyticOrderAt_riemannZeta_ge_one
  neg_re_logDeriv_pole_bound
  trig_341_inequality_combine
)

end Erdos1201.MR

