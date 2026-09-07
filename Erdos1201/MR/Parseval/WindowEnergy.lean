import Erdos1201.MR.Parseval.WindowTransform
import Erdos1201.MR.Parseval.PlancherelL1L2

/-!
# Window energies and the two-window Parseval identity

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
These are Matomäki–Radziwiłł auxiliary lemmas for Lemma 14 of arXiv:1501.04585v4.

This continuation combines the already available window transform and L¹ ∩ L² Plancherel
identity.  In particular, it retains the **difference** of normalized kernels, rather than
bounding the two windows separately and losing cancellation at small frequencies.

We use Fourier frequency `ξ` throughout: the Dirichlet-polynomial height is `2 * π * ξ`.
Consequently no unproved change of variables or missing factor `1 / (2 * π)` is hidden here.
The general majorant lemma explicitly requires integrability of the chosen majorant;
for our concrete envelope this is supplied by a finite-polynomial Cauchy-tail bound.
Neither Proposition 1 nor the short-interval theorem is assumed or proved in this file.

Validation status: candidate continuation, not compiler-checked in the delivery environment.
See `MR_CONTINUATION.md` and `scripts/check_mr_continuation.sh`.
-/

open MeasureTheory
open scoped BigOperators FourierTransform

namespace Erdos1201.MR

/-- Dividing the coefficients divides the whole Dirichlet polynomial, even at `c = 0`. -/
lemma dirichletPoly_div_coeff (a : ℕ → ℂ) (N : Finset ℕ) (c s : ℂ) :
    dirichletPoly (fun n => a n / c) N s = dirichletPoly a N s / c := by
  unfold dirichletPoly
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Dividing the coefficients divides the multiplicative window. -/
lemma windowFun_div_coeff (a : ℕ → ℂ) (N : Finset ℕ) (u : ℝ) (c : ℂ) (y : ℝ) :
    windowFun (fun n => a n / c) N u y = windowFun a N u y / c := by
  unfold windowFun
  rw [mul_div_assoc, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  split_ifs <;> simp

/-- The normalized difference `G_u / u - G_v / v`.

Normalization is put into the coefficients so that the existing regularity lemmas apply
without any additional Fourier-space scalar-multiplication infrastructure. -/
noncomputable def normalizedWindowDifference (a : ℕ → ℂ) (N : Finset ℕ)
    (u v y : ℝ) : ℂ :=
  windowFun (fun n => a n / (u : ℂ)) N u y -
    windowFun (fun n => a n / (v : ℂ)) N v y

/-- The difference of normalized Mellin kernels. -/
noncomputable def normalizedKernelDifference (u v t : ℝ) : ℂ :=
  windowKernel u t / (u : ℂ) - windowKernel v t / (v : ℂ)

@[simp] lemma normalizedKernelDifference_self (u t : ℝ) :
    normalizedKernelDifference u u t = 0 := by
  simp [normalizedKernelDifference]

/-- At height zero both normalized kernels are exactly one. -/
lemma normalizedKernelDifference_zero (u v : ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    normalizedKernelDifference u v 0 = 0 := by
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  simp [normalizedKernelDifference, windowKernel, huC, hvC]

lemma normalizedWindowDifference_eq (a : ℕ → ℂ) (N : Finset ℕ) (u v y : ℝ) :
    normalizedWindowDifference a N u v y =
      windowFun a N u y / (u : ℂ) - windowFun a N v y / (v : ℂ) := by
  simp only [normalizedWindowDifference, windowFun_div_coeff]

lemma integrable_normalizedWindowDifference (a : ℕ → ℂ) (N : Finset ℕ)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (hN : ∀ n ∈ N, 0 < n) :
    Integrable (normalizedWindowDifference a N u v) := by
  exact (integrable_windowFun (fun n => a n / (u : ℂ)) N u hu hN).sub
    (integrable_windowFun (fun n => a n / (v : ℂ)) N v hv hN)

lemma memLp_two_normalizedWindowDifference (a : ℕ → ℂ) (N : Finset ℕ)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (hN : ∀ n ∈ N, 0 < n) :
    MemLp (normalizedWindowDifference a N u v) 2 := by
  exact (memLp_two_windowFun (fun n => a n / (u : ℂ)) N u hu hN).sub
    (memLp_two_windowFun (fun n => a n / (v : ℂ)) N v hv hN)

/-- The modulated window is integrable; this justifies splitting its Fourier integral. -/
lemma integrable_modulated_windowFun (a : ℕ → ℂ) (N : Finset ℕ)
    (u : ℝ) (hu : 0 < u) (hN : ∀ n ∈ N, 0 < n) (ξ : ℝ) :
    Integrable (fun y : ℝ =>
      Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • windowFun a N u y) := by
  let z : ℂ := (1 : ℂ) + (2 * Real.pi * ξ) * Complex.I
  have hexpand : (fun y : ℝ =>
      Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • windowFun a N u y) =
      fun y => ∑ n ∈ N,
        (Set.Ico (Real.log n - Real.log (1 + u)) (Real.log n)).indicator
          (fun y => Complex.exp ((-z) * (y : ℂ)) * a n) y := by
    funext y
    rw [windowFun_eq_sum a N u hu hN, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro n _
    exact fourier_term_eq_indicator (a n) n u ξ y
  rw [hexpand]
  apply integrable_finsetSum
  intro n _
  exact integrable_indicator_Ico_of_continuous (by continuity)
    (Real.log n - Real.log (1 + u)) (Real.log n)

/-- Fourier transform of the normalized two-window difference.

The two windows use the same coefficient sequence and the same finite support; this is
what produces the cancelling difference of kernels. -/
theorem fourierIntegral_normalizedWindowDifference (a : ℕ → ℂ) (N : Finset ℕ)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (hN : ∀ n ∈ N, 0 < n) (ξ : ℝ) :
    Real.fourierIntegral (normalizedWindowDifference a N u v) ξ =
      dirichletPoly a N ((1 : ℂ) + (2 * Real.pi * ξ) * Complex.I) *
        normalizedKernelDifference u v (2 * Real.pi * ξ) := by
  have hsplit :
      Real.fourierIntegral (normalizedWindowDifference a N u v) ξ =
        Real.fourierIntegral (windowFun (fun n => a n / (u : ℂ)) N u) ξ -
          Real.fourierIntegral (windowFun (fun n => a n / (v : ℂ)) N v) ξ := by
    change 𝓕 (normalizedWindowDifference a N u v) ξ =
      𝓕 (windowFun (fun n => a n / (u : ℂ)) N u) ξ -
        𝓕 (windowFun (fun n => a n / (v : ℂ)) N v) ξ
    rw [Real.fourier_real_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
    simp only [normalizedWindowDifference, smul_sub]
    exact integral_sub
      (integrable_modulated_windowFun (fun n => a n / (u : ℂ)) N u hu hN ξ)
      (integrable_modulated_windowFun (fun n => a n / (v : ℂ)) N v hv hN ξ)
  rw [hsplit, fourierIntegral_windowFun _ N u hu hN ξ,
    fourierIntegral_windowFun _ N v hv hN ξ,
    dirichletPoly_div_coeff, dirichletPoly_div_coeff]
  unfold normalizedKernelDifference
  ring

/-- Exact single-window energy identity, with Mathlib's Fourier normalization. -/
theorem integral_norm_sq_windowFun_eq (a : ℕ → ℂ) (N : Finset ℕ)
    (u : ℝ) (hu : 0 < u) (hN : ∀ n ∈ N, 0 < n) :
    (∫ y : ℝ, ‖windowFun a N u y‖ ^ 2) =
      ∫ ξ : ℝ, ‖dirichletPoly a N ((1 : ℂ) + (2 * Real.pi * ξ) * Complex.I)‖ ^ 2 *
        ‖windowKernel u (2 * Real.pi * ξ)‖ ^ 2 := by
  rw [← integral_norm_sq_fourierIntegral (windowFun a N u)
    (integrable_windowFun a N u hu hN) (memLp_two_windowFun a N u hu hN)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    dsimp only
    rw [fourierIntegral_windowFun a N u hu hN ξ, norm_mul, mul_pow])

/-- Exact two-window energy identity.  The cancellation at low height is retained. -/
theorem integral_norm_sq_normalizedWindowDifference_eq (a : ℕ → ℂ) (N : Finset ℕ)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) (hN : ∀ n ∈ N, 0 < n) :
    (∫ y : ℝ, ‖normalizedWindowDifference a N u v y‖ ^ 2) =
      ∫ ξ : ℝ, ‖dirichletPoly a N ((1 : ℂ) + (2 * Real.pi * ξ) * Complex.I)‖ ^ 2 *
        ‖normalizedKernelDifference u v (2 * Real.pi * ξ)‖ ^ 2 := by
  rw [← integral_norm_sq_fourierIntegral (normalizedWindowDifference a N u v)
    (integrable_normalizedWindowDifference a N u v hu hv hN)
    (memLp_two_normalizedWindowDifference a N u v hu hv hN)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ξ => by
    dsimp only
    rw [fourierIntegral_normalizedWindowDifference a N u v hu hv hN ξ,
      norm_mul, mul_pow])

/-- Uniform bound on one normalized kernel. -/
lemma norm_normalized_windowKernel_le_two (u t : ℝ) (hu : 0 < u) (hu1 : u ≤ 1) :
    ‖windowKernel u t / (u : ℂ)‖ ≤ 2 := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  exact (div_le_iff₀ hu).mpr (norm_windowKernel_le_mul u t hu hu1)

/-- Uniform bound on the difference; no ordering between `u` and `v` is required. -/
lemma norm_normalizedKernelDifference_le_four (u v t : ℝ)
    (hu : 0 < u) (hu1 : u ≤ 1) (hv : 0 < v) (hv1 : v ≤ 1) :
    ‖normalizedKernelDifference u v t‖ ≤ 4 := by
  have htri := norm_sub_le (windowKernel u t / (u : ℂ))
    (windowKernel v t / (v : ℂ))
  have h1 := norm_normalized_windowKernel_le_two u t hu hu1
  have h2 := norm_normalized_windowKernel_le_two v t hv hv1
  unfold normalizedKernelDifference
  linarith

/-- Large-height bound, keeping both normalization denominators explicit. -/
lemma norm_normalizedKernelDifference_le_tail (u v t : ℝ)
    (hu : 0 < u) (hu1 : u ≤ 1) (hv : 0 < v) (hv1 : v ≤ 1) :
    ‖normalizedKernelDifference u v t‖ ≤
      (3 / Real.sqrt (1 + t ^ 2)) / u + (3 / Real.sqrt (1 + t ^ 2)) / v := by
  unfold normalizedKernelDifference
  refine (norm_sub_le _ _).trans ?_
  rw [norm_div, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu, abs_of_pos hv]
  exact add_le_add
    (div_le_div_of_nonneg_right (norm_windowKernel_le_div u t hu hu1) hu.le)
    (div_le_div_of_nonneg_right (norm_windowKernel_le_div v t hv hv1) hv.le)

/-- A nonnegative envelope with low-, middle-, and large-height bounds.

The tail decays like `t⁻²` for fixed positive `u,v`; the first term preserves the
small-window saving at low heights.  No ordering of the two window lengths is needed. -/
noncomputable def windowDifferenceWeight (u v t : ℝ) : ℝ :=
  min ((8 * (1 + |t|) * (u + v)) ^ 2)
    (min 16 (((3 / Real.sqrt (1 + t ^ 2)) / u +
      (3 / Real.sqrt (1 + t ^ 2)) / v) ^ 2))

lemma windowDifferenceWeight_nonneg (u v t : ℝ) :
    0 ≤ windowDifferenceWeight u v t := by
  unfold windowDifferenceWeight
  exact le_min (sq_nonneg _) (le_min (by norm_num) (sq_nonneg _))

/-- The envelope is bounded by an integrable Cauchy tail, including at height zero.

The algebraic identity is valid even for zero normalization parameters, using Lean's
usual totalized division. Positivity is needed later for the window estimates. -/
lemma windowDifferenceWeight_le_cauchy (u v t : ℝ) :
    windowDifferenceWeight u v t ≤ (3 / u + 3 / v) ^ 2 / (1 + t ^ 2) := by
  have htail : windowDifferenceWeight u v t ≤
      ((3 / Real.sqrt (1 + t ^ 2)) / u +
        (3 / Real.sqrt (1 + t ^ 2)) / v) ^ 2 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsum : (3 / Real.sqrt (1 + t ^ 2)) / u +
      (3 / Real.sqrt (1 + t ^ 2)) / v =
      (3 / u + 3 / v) / Real.sqrt (1 + t ^ 2) := by ring
  rw [hsum, div_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)] at htail
  exact htail

lemma continuous_windowDifferenceWeight (u v : ℝ) :
    Continuous (windowDifferenceWeight u v) := by
  have hden : ∀ t : ℝ, Real.sqrt (1 + t ^ 2) ≠ 0 := by
    intro t
    exact ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
  have htail : Continuous (fun t : ℝ => 3 / Real.sqrt (1 + t ^ 2)) :=
    continuous_const.div
      (Real.continuous_sqrt.comp (continuous_const.add (continuous_id.pow 2))) hden
  have hlo : Continuous (fun t : ℝ => (8 * (1 + |t|) * (u + v)) ^ 2) := by
    fun_prop
  have htailSq : Continuous (fun t : ℝ =>
      ((3 / Real.sqrt (1 + t ^ 2)) / u +
        (3 / Real.sqrt (1 + t ^ 2)) / v) ^ 2) :=
    ((htail.div_const u).add (htail.div_const v)).pow 2
  exact hlo.min (continuous_const.min htailSq)

/-- Continuity for arbitrary finite positive support, not just a consecutive block. -/
lemma continuous_dirichletPoly_one_line (a : ℕ → ℂ) (N : Finset ℕ)
    (hN : ∀ n ∈ N, 0 < n) :
    Continuous (fun t : ℝ => dirichletPoly a N ((1 : ℂ) + t * Complex.I)) := by
  unfold dirichletPoly
  apply continuous_finsetSum
  intro n hn
  simp_rw [natCast_cpow_neg_one_add_mul_I_eq_exp n (hN n hn)]
  fun_prop

/-- The finite Dirichlet polynomial times the envelope is integrable in height `t`.

This uses only `‖A(1+it)‖ ≤ ∑ ‖a n‖/n` and the Cauchy tail. It is a regularity lemma,
not the smallness estimate for these integrals required by MR. -/
theorem integrable_dirichletPoly_windowDifferenceWeight_height
    (a : ℕ → ℂ) (N : Finset ℕ) (u v : ℝ) (hN : ∀ n ∈ N, 0 < n) :
    Integrable (fun t : ℝ =>
      ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
        windowDifferenceWeight u v t) := by
  let C : ℝ := (∑ n ∈ N, ‖a n‖ / n) ^ 2 * (3 / u + 3 / v) ^ 2
  have hcont : Continuous (fun t : ℝ =>
      ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
        windowDifferenceWeight u v t) :=
    ((continuous_dirichletPoly_one_line a N hN).norm.pow 2).mul
      (continuous_windowDifferenceWeight u v)
  refine Integrable.mono' (g := fun t : ℝ => C * (1 + t ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul C) hcont.aestronglyMeasurable ?_
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg _) (windowDifferenceWeight_nonneg u v t))]
  have hpoly := pow_le_pow_left₀
    (norm_nonneg _) (norm_dirichletPoly_le a N hN t) 2
  calc
    ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I)‖ ^ 2 * windowDifferenceWeight u v t
        ≤ (∑ n ∈ N, ‖a n‖ / n) ^ 2 * windowDifferenceWeight u v t :=
          mul_le_mul_of_nonneg_right hpoly (windowDifferenceWeight_nonneg u v t)
    _ ≤ (∑ n ∈ N, ‖a n‖ / n) ^ 2 * ((3 / u + 3 / v) ^ 2 / (1 + t ^ 2)) :=
      mul_le_mul_of_nonneg_left (windowDifferenceWeight_le_cauchy u v t) (sq_nonneg _)
    _ = C * (1 + t ^ 2)⁻¹ := by dsimp [C]; ring

/-- Integrability in Fourier frequency `ξ`, where the height is `2πξ`.

This transfers integrability only. The energy identities remain in the original `ξ`
variable, so no numerical change-of-variables factor is asserted here. -/
theorem integrable_dirichletPoly_windowDifferenceWeight
    (a : ℕ → ℂ) (N : Finset ℕ) (u v : ℝ) (hN : ∀ n ∈ N, 0 < n) :
    Integrable (fun ξ : ℝ =>
      ‖dirichletPoly a N ((1 : ℂ) + (2 * Real.pi * ξ) * Complex.I)‖ ^ 2 *
        windowDifferenceWeight u v (2 * Real.pi * ξ)) := by
  have hscale : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have h := (integrable_comp_mul_left_iff
    (fun t : ℝ => ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
      windowDifferenceWeight u v t) hscale).mpr
    (integrable_dirichletPoly_windowDifferenceWeight_height a N u v hN)
  refine h.congr (Filter.Eventually.of_forall (fun ξ => ?_))
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]

/-- All three kernel regimes combined into a single pointwise square bound. -/
theorem norm_sq_normalizedKernelDifference_le_weight (u v t : ℝ)
    (hu : 0 < u) (hu1 : u ≤ 1 / 2) (hv : 0 < v) (hv1 : v ≤ 1 / 2) :
    ‖normalizedKernelDifference u v t‖ ^ 2 ≤ windowDifferenceWeight u v t := by
  have hu1' : u ≤ 1 := by linarith
  have hv1' : v ≤ 1 := by linarith
  have hlo : ‖normalizedKernelDifference u v t‖ ≤ 8 * (1 + |t|) * (u + v) :=
    norm_windowKernel_div_sub_le u v t hu hu1 hv hv1
  have hmid := norm_normalizedKernelDifference_le_four u v t hu hu1' hv hv1'
  have htail := norm_normalizedKernelDifference_le_tail u v t hu hu1' hv hv1'
  have hnonneg := norm_nonneg (normalizedKernelDifference u v t)
  have hmid2 := pow_le_pow_left₀ hnonneg hmid 2
  norm_num at hmid2
  unfold windowDifferenceWeight
  exact le_min (pow_le_pow_left₀ hnonneg hlo 2)
    (le_min hmid2 (pow_le_pow_left₀ hnonneg htail 2))

/-- A Parseval bound for any integrable spectral majorant.

The `hBint` premise must not be dropped: real Bochner integrals are totalized to zero for
nonintegrable functions.  This premise is an integrability condition, not an MR estimate. -/
theorem integral_norm_sq_normalizedWindowDifference_le_majorant
    (a : ℕ → ℂ) (N : Finset ℕ) (u v : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hN : ∀ n ∈ N, 0 < n) (B : ℝ → ℝ)
    (hB : ∀ t, ‖normalizedKernelDifference u v t‖ ^ 2 ≤ B t)
    (hBint : Integrable (fun ξ : ℝ =>
      ‖dirichletPoly a N ((1 : ℂ) + (2 * Real.pi * ξ) * Complex.I)‖ ^ 2 *
        B (2 * Real.pi * ξ))) :
    (∫ y : ℝ, ‖normalizedWindowDifference a N u v y‖ ^ 2) ≤
      ∫ ξ : ℝ, ‖dirichletPoly a N ((1 : ℂ) + (2 * Real.pi * ξ) * Complex.I)‖ ^ 2 *
        B (2 * Real.pi * ξ) := by
  rw [integral_norm_sq_normalizedWindowDifference_eq a N u v hu hv hN]
  refine integral_mono_of_nonneg ?_ hBint ?_
  · exact Filter.Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  · exact Filter.Eventually.of_forall (fun ξ =>
      mul_le_mul_of_nonneg_left (hB (2 * Real.pi * ξ)) (sq_nonneg _))

/-- Specialization to the explicit three-regime envelope.

Integrability is supplied by the Cauchy-tail lemma above, not an extra analytic
hypothesis. This is the weighted Parseval reduction, not the full MR Lemma 14. -/
theorem integral_norm_sq_normalizedWindowDifference_le_weight
    (a : ℕ → ℂ) (N : Finset ℕ) (u v : ℝ)
    (hu : 0 < u) (hu1 : u ≤ 1 / 2) (hv : 0 < v) (hv1 : v ≤ 1 / 2)
    (hN : ∀ n ∈ N, 0 < n) :
    (∫ y : ℝ, ‖normalizedWindowDifference a N u v y‖ ^ 2) ≤
      ∫ ξ : ℝ, ‖dirichletPoly a N ((1 : ℂ) + (2 * Real.pi * ξ) * Complex.I)‖ ^ 2 *
        windowDifferenceWeight u v (2 * Real.pi * ξ) := by
  exact integral_norm_sq_normalizedWindowDifference_le_majorant a N u v hu hv hN
    (windowDifferenceWeight u v)
    (fun t => norm_sq_normalizedKernelDifference_le_weight u v t hu hu1 hv hv1)
    (integrable_dirichletPoly_windowDifferenceWeight a N u v hN)

end Erdos1201.MR
