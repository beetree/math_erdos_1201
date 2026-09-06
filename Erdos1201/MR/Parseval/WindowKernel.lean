import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Mellin Window Kernel Bounds

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

This file provides elementary bounds for the Mellin kernel of a multiplicative window
(x, x(1+u)] at s = 1 + it:
`windowKernel u t = ((1+u)^{1+it} - 1) / (1+it)`.

These estimates are used in Matomäki–Radziwiłł Lemma 14.
-/

open Complex Set

namespace Erdos1201.MR

/-- Mellin kernel of the window (x, x(1+u)] at s = 1 + it: ((1+u)^{1+it} - 1)/(1+it). -/
noncomputable def windowKernel (u t : ℝ) : ℂ :=
  ((1 + u : ℂ) ^ ((1 : ℂ) + t * Complex.I) - 1) / ((1 : ℂ) + t * Complex.I)

/-- The norm of `1 + it` is `√(1 + t²)`. -/
lemma norm_one_add_mul_I (t : ℝ) : ‖(1 : ℂ) + (t : ℂ) * I‖ = Real.sqrt (1 + t ^ 2) := by
  rw [norm_def]
  have h : (1 : ℂ) + (t : ℂ) * I = ((1 : ℝ) : ℂ) + (t : ℂ) * I := by simp
  rw [h, normSq_add_mul_I]
  ring_nf

/-- The norm of `1 + it` is strictly positive. -/
lemma norm_one_add_mul_I_pos (t : ℝ) : 0 < ‖(1 : ℂ) + (t : ℂ) * I‖ := by
  rw [norm_one_add_mul_I]
  exact Real.sqrt_pos_of_pos (by positivity)

/-- Linear bound on `‖1 + it‖ ≤ 1 + |t|`. -/
lemma norm_one_add_mul_I_le_one_add_abs (t : ℝ) : ‖(1 : ℂ) + (t : ℂ) * I‖ ≤ 1 + |t| := by
  rw [norm_one_add_mul_I]
  have h1 : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
    have : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
    rw [this]
    nlinarith [abs_nonneg t]
  have h3 : 0 ≤ 1 + |t| := by positivity
  rw [← Real.sqrt_sq h3]
  exact Real.sqrt_le_sqrt h1

/-- The norm of `(1 + u)^{1 + it}` equals `1 + u` for `0 < u`. -/
lemma norm_one_add_u_cpow (u t : ℝ) (hu : 0 < u) :
    ‖(1 + u : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I)‖ = 1 + u := by
  have hu_pos : 0 < (1 + u : ℝ) := by linarith
  have hu_ne : (1 + u : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hu_pos
  rw [cpow_def_of_ne_zero hu_ne]
  have hlog : Complex.log ((1 + u : ℝ) : ℂ) = ((Real.log (1 + u) : ℝ) : ℂ) := by
    rw [← ofReal_log (by linarith)]
  have hcast : (1 + u : ℂ) = ((1 + u : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, hlog, norm_exp]
  have hre : (((Real.log (1 + u) : ℝ) : ℂ) * ((1 : ℂ) + (t : ℂ) * I)).re = Real.log (1 + u) := by
    simp
  rw [hre, Real.exp_log hu_pos]

/-- Derivative of `x ↦ exp(x · z)`. -/
lemma hasDerivAt_exp_mul (z : ℂ) (s : ℝ) :
    HasDerivAt (fun x : ℝ => exp ((x : ℂ) * z)) (z * exp ((s : ℂ) * z)) s := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) s := ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => (x : ℂ) * z) (1 * z) s := h1.mul_const z
  rw [one_mul] at h2
  have h3 := h2.cexp
  rw [mul_comm] at h3
  exact h3

/-- Derivative of `y ↦ log(1 + y)`. -/
lemma hasDerivAt_log_one_add (x : ℝ) (hx : 0 < 1 + x) :
    HasDerivAt (fun y => Real.log (1 + y)) (1 + x)⁻¹ x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have h2 : HasDerivAt Real.log (1 + x)⁻¹ (1 + x) := Real.hasDerivAt_log (ne_of_gt hx)
  have h3 : HasDerivAt (Real.log ∘ fun y => 1 + y) ((1 + x)⁻¹ * 1) x := h2.comp x h1
  rw [mul_one] at h3
  exact h3

/-- Quadratic bound on `u - log(1 + u) ≤ u²` for `0 ≤ u`. -/
lemma sub_log_one_add_le_sq (u : ℝ) (hu0 : 0 ≤ u) :
    u - Real.log (1 + u) ≤ u ^ 2 := by
  let h : ℝ → ℝ := fun x => x - Real.log (1 + x)
  have hdiff : ∀ x ∈ Icc 0 u, DifferentiableAt ℝ h x := by
    intro x hx
    have hx_pos : 0 < 1 + x := by linarith [hx.1]
    have hd_log := hasDerivAt_log_one_add x hx_pos
    have hd_h := (hasDerivAt_id x).sub hd_log
    exact hd_h.differentiableAt
  have hbound : ∀ x ∈ Icc 0 u, ‖deriv h x‖ ≤ u := by
    intro x hx
    have hx_pos : 0 < 1 + x := by linarith [hx.1]
    have hd_log := hasDerivAt_log_one_add x hx_pos
    have hd_h : HasDerivAt h (1 - (1 + x)⁻¹) x := (hasDerivAt_id x).sub hd_log
    rw [hd_h.deriv, Real.norm_eq_abs]
    have h_val : 1 - (1 + x)⁻¹ = x / (1 + x) := by
      have : (1 + x) ≠ 0 := ne_of_gt hx_pos
      field_simp
      ring
    rw [h_val]
    have hpos : 0 ≤ x / (1 + x) := by
      have : 0 ≤ x := hx.1
      positivity
    rw [abs_of_nonneg hpos]
    have hden : 1 ≤ 1 + x := by linarith [hx.1]
    calc x / (1 + x) ≤ x / 1 := div_le_div_of_nonneg_left hx.1 zero_lt_one hden
    _ = x := by ring
    _ ≤ u := hx.2
  have h_mvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc 0 u) ⟨le_rfl, hu0⟩ ⟨hu0, le_rfl⟩
  rw [sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hu0] at h_mvt
  have hh0 : h 0 = 0 := by
    dsimp [h]
    rw [add_zero, Real.log_one, sub_zero]
  rw [hh0, sub_zero] at h_mvt
  have hh_pos : 0 ≤ h u := by
    dsimp [h]
    have : Real.log (1 + u) ≤ 1 + u - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  rw [abs_of_nonneg hh_pos] at h_mvt
  calc u - Real.log (1 + u) = h u := rfl
  _ ≤ u * u := h_mvt
  _ = u ^ 2 := by ring

/-- Bound on `‖exp(x(1+it)) - 1‖` along the segment `[0, log(1+u)]`. -/
lemma norm_exp_mul_sub_one_le (u t : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (x : ℝ) (hx0 : 0 ≤ x)
    (hxL : x ≤ Real.log (1 + u)) :
    ‖exp ((x : ℂ) * ((1 : ℂ) + (t : ℂ) * I)) - 1‖ ≤ 2 * ‖(1 : ℂ) + (t : ℂ) * I‖ * x := by
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  let f : ℝ → ℂ := fun s => exp ((s : ℂ) * z)
  have hdiff : ∀ s ∈ Icc 0 x, DifferentiableAt ℝ f s := fun s _ =>
    (hasDerivAt_exp_mul z s).differentiableAt
  have hbound : ∀ s ∈ Icc 0 x, ‖deriv f s‖ ≤ 2 * ‖z‖ := by
    rintro s ⟨hs0, hsx⟩
    rw [(hasDerivAt_exp_mul z s).deriv, norm_mul, norm_exp]
    have hre : (((s : ℝ) : ℂ) * z).re = s := by
      change (((s : ℝ) : ℂ) * ((1 : ℂ) + (t : ℂ) * I)).re = s
      simp
    rw [hre]
    have hexp : Real.exp s ≤ 2 := by
      have hsL : s ≤ Real.log (1 + u) := by linarith
      have : Real.exp s ≤ Real.exp (Real.log (1 + u)) := Real.exp_le_exp.mpr hsL
      rw [Real.exp_log (by linarith)] at this
      linarith
    have : ‖z‖ * Real.exp s ≤ ‖z‖ * 2 := by
      nlinarith [norm_nonneg z]
    linarith
  have h_mvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc 0 x) ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩
  rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hx0] at h_mvt
  have hf0 : f 0 = 1 := by simp [f]
  rw [hf0] at h_mvt
  exact h_mvt

/-- Second-order bound on `exp(L·z) - 1 - L·z`. -/
lemma norm_exp_sub_one_sub_id_le (u t : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    let L := Real.log (1 + u)
    let z : ℂ := (1 : ℂ) + (t : ℂ) * I
    ‖exp ((L : ℂ) * z) - 1 - (L : ℂ) * z‖ ≤ 2 * ‖z‖ ^ 2 * u ^ 2 := by
  intro L z
  have hu_pos : 0 < 1 + u := by linarith
  have hL_nonneg : 0 ≤ L := Real.log_nonneg (by linarith)
  have hL_le_u : L ≤ u := by linarith [Real.log_le_sub_one_of_pos hu_pos]
  let g : ℝ → ℂ := fun x => exp ((x : ℂ) * z) - 1 - (x : ℂ) * z
  have hd_g : ∀ x : ℝ, HasDerivAt g (z * (exp ((x : ℂ) * z) - 1)) x := by
    intro x
    have h1 := hasDerivAt_exp_mul z x
    have h2 : HasDerivAt (fun _ : ℝ => (1 : ℂ)) (0 : ℂ) x := hasDerivAt_const x 1
    have h3 : HasDerivAt (fun y : ℝ => (y : ℂ) * z) (1 * z) x := ofRealCLM.hasDerivAt.mul_const z
    rw [one_mul] at h3
    have h4 := (h1.sub h2).sub h3
    have heq : z * exp ((x : ℂ) * z) - 0 - z = z * (exp ((x : ℂ) * z) - 1) := by ring
    rw [heq] at h4
    exact h4
  have hdiff : ∀ x ∈ Icc 0 L, DifferentiableAt ℝ g x := fun x _ =>
    (hd_g x).differentiableAt
  have hbound : ∀ x ∈ Icc 0 L, ‖deriv g x‖ ≤ 2 * ‖z‖ ^ 2 * u := by
    rintro x ⟨hx0, hxL⟩
    rw [(hd_g x).deriv, norm_mul]
    have h1 := norm_exp_mul_sub_one_le u t (by linarith) hu1 x hx0 hxL
    have hx_le_u : x ≤ u := by linarith
    have : ‖z‖ * ‖exp ((x : ℂ) * z) - 1‖ ≤ 2 * ‖z‖ ^ 2 * u := by
      nlinarith [norm_nonneg z, hx0, hx_le_u]
    exact this
  have h_mvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc 0 L) ⟨le_rfl, hL_nonneg⟩ ⟨hL_nonneg, le_rfl⟩
  rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hL_nonneg] at h_mvt
  have hg0 : g 0 = 0 := by simp [g]
  rw [hg0, sub_zero] at h_mvt
  have hpos : 0 ≤ 2 * ‖z‖ ^ 2 * u := by positivity
  have hstep : 2 * ‖z‖ ^ 2 * u * L ≤ 2 * ‖z‖ ^ 2 * u * u := mul_le_mul_of_nonneg_left hL_le_u hpos
  have heq : 2 * ‖z‖ ^ 2 * u * u = 2 * ‖z‖ ^ 2 * u ^ 2 := by ring
  linarith

/-- Decomposition of `windowKernel u t / u - 1` into second-order exponential and log remainders. -/
lemma windowKernel_div_sub_one (u t : ℝ) (hu0 : 0 < u) :
    let L := Real.log (1 + u)
    let z : ℂ := (1 : ℂ) + (t : ℂ) * I
    windowKernel u t / (u : ℂ) - 1 =
      (exp ((L : ℂ) * z) - 1 - (L : ℂ) * z) / (z * (u : ℂ)) + ((L - u : ℝ) : ℂ) / (u : ℂ) := by
  intro L z
  have hu_pos : 0 < 1 + u := by linarith
  have hu_ne : (1 + u : ℂ) ≠ 0 := by
    have : 0 < (1 + u : ℝ) := by linarith
    exact_mod_cast ne_of_gt hu_pos
  have hcpow : (1 + u : ℂ) ^ z = exp ((L : ℂ) * z) := by
    rw [cpow_def_of_ne_zero hu_ne]
    have hcast : (1 + u : ℂ) = ((1 + u : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, ← ofReal_log (by linarith)]
  have hz_ne : z ≠ 0 := by
    intro hz
    have : z.re = 0 := by rw [hz, zero_re]
    simp [z] at this
  have hu_cne : (u : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hu0
  unfold windowKernel
  have hz_def : ((1 : ℂ) + (t : ℂ) * I) = z := rfl
  rw [hz_def, hcpow]
  push_cast
  field_simp
  ring

/-- Deviation bound for normalized `windowKernel`: `‖windowKernel u t / u - 1‖ ≤ 3(1+|t|)u`. -/
lemma norm_windowKernel_div_sub_one_le (u t : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) :
    ‖windowKernel u t / (u : ℂ) - 1‖ ≤ 3 * (1 + |t|) * u := by
  have hu1' : u ≤ 1 := by linarith
  let L := Real.log (1 + u)
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  rw [windowKernel_div_sub_one u t hu0]
  have htri := norm_add_le
    ((exp ((L : ℂ) * z) - 1 - (L : ℂ) * z) / (z * (u : ℂ)))
    (((L - u : ℝ) : ℂ) / (u : ℂ))
  have hterm1 : ‖(exp ((L : ℂ) * z) - 1 - (L : ℂ) * z) / (z * (u : ℂ))‖ ≤ 2 * (1 + |t|) * u := by
    rw [norm_div, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hu0]
    have hnum := norm_exp_sub_one_sub_id_le u t hu0 hu1'
    have hz_pos := norm_one_add_mul_I_pos t
    have hden_pos : 0 < ‖z‖ * u := by positivity
    rw [div_le_iff₀ hden_pos]
    calc ‖exp ((L : ℂ) * z) - 1 - (L : ℂ) * z‖ ≤ 2 * ‖z‖ ^ 2 * u ^ 2 := hnum
    _ = 2 * ‖z‖ * u * (‖z‖ * u) := by ring
    _ ≤ 2 * (1 + |t|) * u * (‖z‖ * u) := by
      have hz_le := norm_one_add_mul_I_le_one_add_abs t
      have : 0 ≤ 2 * u * (‖z‖ * u) := by positivity
      nlinarith [norm_nonneg z, abs_nonneg t, hu0]
  have hterm2 : ‖((L - u : ℝ) : ℂ) / (u : ℂ)‖ ≤ u := by
    rw [norm_div, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu0]
    have hLu : Real.log (1 + u) ≤ u := by
      have : Real.log (1 + u) ≤ 1 + u - 1 := Real.log_le_sub_one_of_pos (by linarith)
      linarith
    have hLu_abs : |L - u| = u - L := by
      dsimp [L]
      rw [abs_sub_comm, abs_of_nonneg]
      linarith
    rw [hLu_abs]
    have hlog_bound := sub_log_one_add_le_sq u (by linarith)
    have h_eq : u - L = u - Real.log (1 + u) := rfl
    rw [h_eq, div_le_iff₀ hu0]
    calc u - Real.log (1 + u) ≤ u ^ 2 := hlog_bound
    _ = u * u := by ring
  have hterm2' : ‖((L - u : ℝ) : ℂ) / (u : ℂ)‖ ≤ (1 + |t|) * u := by
    calc ‖((L - u : ℝ) : ℂ) / (u : ℂ)‖ ≤ u := hterm2
    _ = 1 * u := by ring
    _ ≤ (1 + |t|) * u := by
      nlinarith [abs_nonneg t, hu0]
  linarith

/-- First bound: `‖windowKernel u t‖ ≤ 2 * u` for `0 < u ≤ 1`. -/
theorem norm_windowKernel_le_mul (u t : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ‖windowKernel u t‖ ≤ 2 * u := by
  let L := Real.log (1 + u)
  let z : ℂ := (1 : ℂ) + (t : ℂ) * I
  have hu_pos : 0 < 1 + u := by linarith
  have hL_nonneg : 0 ≤ L := Real.log_nonneg (by linarith)
  have hL_le_u : L ≤ u := by linarith [Real.log_le_sub_one_of_pos hu_pos]
  let f : ℝ → ℂ := fun x => exp ((x : ℂ) * z)
  have hdiff : ∀ x ∈ Icc 0 L, DifferentiableAt ℝ f x := fun x _ =>
    (hasDerivAt_exp_mul z x).differentiableAt
  have hbound : ∀ x ∈ Icc 0 L, ‖deriv f x‖ ≤ 2 * ‖z‖ := by
    rintro x ⟨hx0, hxL⟩
    rw [(hasDerivAt_exp_mul z x).deriv, norm_mul, norm_exp]
    have hre : (((x : ℝ) : ℂ) * z).re = x := by
      change (((x : ℝ) : ℂ) * ((1 : ℂ) + (t : ℂ) * I)).re = x
      simp
    rw [hre]
    have hexp : Real.exp x ≤ 2 := by
      have : Real.exp x ≤ Real.exp L := Real.exp_le_exp.mpr hxL
      rw [Real.exp_log hu_pos] at this
      linarith
    have : ‖z‖ * Real.exp x ≤ ‖z‖ * 2 := by
      nlinarith [norm_nonneg z]
    linarith
  have h_mvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc 0 L) ⟨le_rfl, hL_nonneg⟩ ⟨hL_nonneg, le_rfl⟩
  rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hL_nonneg] at h_mvt
  have hf0 : f 0 = 1 := by simp [f]
  have hfL : f L = (1 + u : ℂ) ^ z := by
    have hu_ne : (1 + u : ℂ) ≠ 0 := by
      have : 0 < (1 + u : ℝ) := by linarith
      exact_mod_cast ne_of_gt this
    rw [cpow_def_of_ne_zero hu_ne]
    have hcast : (1 + u : ℂ) = ((1 + u : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, ← ofReal_log (by linarith)]
  rw [hf0, hfL] at h_mvt
  unfold windowKernel
  have hz_def : ((1 : ℂ) + (t : ℂ) * I) = z := rfl
  rw [hz_def, norm_div]
  have hz_pos : 0 < ‖z‖ := norm_one_add_mul_I_pos t
  have h_bound : ‖(1 + u : ℂ) ^ z - 1‖ ≤ 2 * u * ‖z‖ := by
    calc ‖(1 + u : ℂ) ^ z - 1‖ ≤ 2 * ‖z‖ * L := h_mvt
    _ ≤ 2 * ‖z‖ * u := by nlinarith [norm_nonneg z]
    _ = 2 * u * ‖z‖ := by ring
  exact (div_le_iff₀ hz_pos).mpr h_bound

/-- Second bound: `‖windowKernel u t‖ ≤ 3 / √(1 + t²)` for `0 < u ≤ 1`. -/
theorem norm_windowKernel_le_div (u t : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ‖windowKernel u t‖ ≤ 3 / Real.sqrt (1 + t ^ 2) := by
  unfold windowKernel
  rw [norm_div, norm_one_add_mul_I]
  have hnum : ‖(1 + u : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I) - 1‖ ≤ 3 := by
    have htri := norm_sub_le ((1 + u : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I)) 1
    rw [norm_one_add_u_cpow u t hu0, norm_one] at htri
    linarith
  have hden_pos : 0 < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos_of_pos (by positivity)
  exact div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)

/-- Third bound (difference of normalized kernels):
`‖windowKernel u₁ t / u₁ - windowKernel u₂ t / u₂‖ ≤ 8 * (1 + |t|) * (u₁ + u₂)`. -/
theorem norm_windowKernel_div_sub_le (u₁ u₂ t : ℝ) (h1 : 0 < u₁) (h1' : u₁ ≤ 1 / 2) (h2 : 0 < u₂) (h2' : u₂ ≤ 1 / 2) :
    ‖windowKernel u₁ t / u₁ - windowKernel u₂ t / u₂‖ ≤ 8 * (1 + |t|) * (u₁ + u₂) := by
  have h_id : windowKernel u₁ t / (u₁ : ℂ) - windowKernel u₂ t / (u₂ : ℂ) =
    (windowKernel u₁ t / (u₁ : ℂ) - 1) - (windowKernel u₂ t / (u₂ : ℂ) - 1) := by ring
  rw [h_id]
  have htri := norm_sub_le (windowKernel u₁ t / (u₁ : ℂ) - 1) (windowKernel u₂ t / (u₂ : ℂ) - 1)
  have hb1 := norm_windowKernel_div_sub_one_le u₁ t h1 h1'
  have hb2 := norm_windowKernel_div_sub_one_le u₂ t h2 h2'
  calc ‖(windowKernel u₁ t / (u₁ : ℂ) - 1) - (windowKernel u₂ t / (u₂ : ℂ) - 1)‖
    ≤ ‖windowKernel u₁ t / (u₁ : ℂ) - 1‖ + ‖windowKernel u₂ t / (u₂ : ℂ) - 1‖ := htri
  _ ≤ 3 * (1 + |t|) * u₁ + 3 * (1 + |t|) * u₂ := by linarith
  _ = 3 * (1 + |t|) * (u₁ + u₂) := by ring
  _ ≤ 8 * (1 + |t|) * (u₁ + u₂) := by
    have : 0 ≤ 1 + |t| := by positivity
    have : 0 ≤ u₁ + u₂ := by linarith
    nlinarith

end Erdos1201.MR
