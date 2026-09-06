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
   - `zero_free_of_zeta_bound`: the general zero-free region under growth bounds.
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
)

end Erdos1201.MR

