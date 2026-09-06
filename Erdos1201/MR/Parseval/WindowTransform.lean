import Mathlib
import Erdos1201.MR.Parseval.WindowKernel
import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.MR.Parseval.FourierAlias

/-!
# Fourier Transform of the Multiplicative Window Function

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module computes the explicit Fourier transform of the multiplicative-window function
`windowFun a N u y = e^{-y} · ∑_{n ∈ N} a n · 1[ e^y < n ≤ e^y (1+u) ]`.

We show that `windowFun a N u` is integrable, in $L^2$, and that its Fourier transform at $\xi$ equals
`dirichletPoly a N (1 + 2πiξ) * windowKernel u (2πξ)`.
-/

open MeasureTheory Set intervalIntegral FourierTransform


namespace Erdos1201.MR

/-- G_u(y) := e^{-y} · ∑_{n ∈ N} a n · 1[ e^y < n ≤ e^y (1+u) ], i.e. e^{-y} times the window sum S(e^y, e^y u). -/
noncomputable def windowFun (a : ℕ → ℂ) (N : Finset ℕ) (u : ℝ) (y : ℝ) : ℂ :=
  Real.exp (-y) * ∑ n ∈ N, if Real.exp y < n ∧ (n : ℝ) ≤ Real.exp y * (1 + u) then a n else 0

/-- Characterization of the multiplicative window condition `e^y < n ≤ e^y(1+u)`
as `y ∈ [log n - log(1+u), log n)`. -/
lemma exp_lt_and_le_mul_iff (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u) (y : ℝ) :
    (Real.exp y < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp y * (1 + u)) ↔
      y ∈ Ico (Real.log n - Real.log (1 + u)) (Real.log n) := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hu_pos : 0 < 1 + u := by linarith
  have hdiv_pos : 0 < (n : ℝ) / (1 + u) := div_pos hn_pos hu_pos
  rw [mem_Ico]
  have h1 : Real.exp y < (n : ℝ) ↔ y < Real.log n := (Real.lt_log_iff_exp_lt hn_pos).symm
  have h2 : (n : ℝ) ≤ Real.exp y * (1 + u) ↔ Real.log n - Real.log (1 + u) ≤ y := by
    rw [← div_le_iff₀ hu_pos]
    rw [← Real.log_le_iff_le_exp hdiv_pos]
    rw [Real.log_div (ne_of_gt hn_pos) (ne_of_gt hu_pos)]
  rw [h1, h2, and_comm]

/-- Expansion of `windowFun` as a finite sum of interval indicator functions. -/
lemma windowFun_eq_sum (a : ℕ → ℂ) (N : Finset ℕ) (u : ℝ) (hu : 0 < u) (hN : ∀ n ∈ N, 0 < n) :
    windowFun a N u =
      fun y => ∑ n ∈ N, (Ico (Real.log n - Real.log (1 + u)) (Real.log n)).indicator
        (fun y => (Real.exp (-y) : ℂ) * a n) y := by
  ext y
  unfold windowFun
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [indicator_apply]
  have h_iff := exp_lt_and_le_mul_iff n (hN n hn) u hu y
  by_cases hy : y ∈ Ico (Real.log n - Real.log (1 + u)) (Real.log n)
  · have h_cond : Real.exp y < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp y * (1 + u) := h_iff.mpr hy
    simp [hy, h_cond]
  · have h_cond : ¬(Real.exp y < (n : ℝ) ∧ (n : ℝ) ≤ Real.exp y * (1 + u)) := fun h => hy (h_iff.mp h)
    simp [hy, h_cond]

/-- Each single-term window indicator belongs to `L^p(ℝ)` for any exponent `p`. -/
lemma memLp_term (c : ℂ) (a b : ℝ) (p : ENNReal) :
    MemLp ((Ico a b).indicator (fun y => (Real.exp (-y) : ℂ) * c)) p volume := by
  let f := (Ico a b).indicator (fun y => (Real.exp (-y) : ℂ) * c)
  have hsupp : HasCompactSupport f := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    exact support_indicator_subset.trans Ico_subset_Icc_self
  have hcont : Continuous (fun y : ℝ => (Real.exp (-y) : ℂ) * c) := by
    continuity
  have hmeas : AEStronglyMeasurable f volume := by
    apply StronglyMeasurable.aestronglyMeasurable
    exact hcont.stronglyMeasurable.indicator measurableSet_Ico
  let C := Real.exp (- min a b) * ‖c‖
  have hbound : ∀ᵐ y ∂volume, ‖f y‖ ≤ C := by
    apply Filter.Eventually.of_forall
    intro y
    by_cases hy : y ∈ Ico a b
    · have hfeq : f y = (Real.exp (-y) : ℂ) * c := by simp [f, hy]
      rw [hfeq]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hy_ge : min a b ≤ y := le_trans (min_le_left a b) hy.1
      have : Real.exp (-y) ≤ Real.exp (- min a b) := by
        rw [Real.exp_le_exp]
        linarith
      nlinarith [norm_nonneg c]
    · have hfeq : f y = 0 := by simp [f, hy]
      rw [hfeq, norm_zero]
      have : 0 ≤ Real.exp (- min a b) := (Real.exp_pos _).le
      positivity
  exact HasCompactSupport.memLp_of_bound hsupp hmeas C hbound

theorem integrable_windowFun (a : ℕ → ℂ) (N : Finset ℕ) (u : ℝ) (hu : 0 < u) (hN : ∀ n ∈ N, 0 < n) :
    MeasureTheory.Integrable (windowFun a N u) := by
  rw [windowFun_eq_sum a N u hu hN]
  apply integrable_finsetSum
  intro n _
  exact memLp_one_iff_integrable.mp (memLp_term (a n) (Real.log n - Real.log (1 + u)) (Real.log n) 1)

theorem memLp_two_windowFun (a : ℕ → ℂ) (N : Finset ℕ) (u : ℝ) (hu : 0 < u) (hN : ∀ n ∈ N, 0 < n) :
    MeasureTheory.MemLp (windowFun a N u) 2 := by
  rw [windowFun_eq_sum a N u hu hN]
  apply memLp_finsetSum
  intro n _
  exact memLp_term (a n) (Real.log n - Real.log (1 + u)) (Real.log n) 2

/-- An indicator of a continuous function on a bounded interval `Ico a b` is integrable. -/
lemma integrable_indicator_Ico_of_continuous
    {g : ℝ → ℂ} (hg : Continuous g) (a b : ℝ) :
    Integrable ((Ico a b).indicator g) volume := by
  rw [integrable_indicator_iff measurableSet_Ico]
  exact (hg.integrableOn_Icc (a := a) (b := b)).mono_set Ico_subset_Icc_self

/-- Complex power `(1+u)^z` expressed as `exp(z * log(1+u))`. -/
lemma cpow_one_add_u_eq (u : ℝ) (hu : 0 < u) (z : ℂ) :
    (1 + u : ℂ) ^ z = Complex.exp (z * (Real.log (1 + u) : ℂ)) := by
  have hu_pos : 0 < 1 + u := by linarith
  have hu_ne : (1 + u : ℂ) ≠ 0 := by
    have : (1 + u : ℂ) = ((1 + u : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hu_pos)
  rw [Complex.cpow_def_of_ne_zero hu_ne]
  have hcast : (1 + u : ℂ) = ((1 + u : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, ← Complex.ofReal_log hu_pos.le, mul_comm]

/-- Natural cast power `n^(-z)` expressed as `exp((-z) * log n)`. -/
lemma natCast_cpow_neg_eq (n : ℕ) (hn : 0 < n) (z : ℂ) :
    (n : ℂ) ^ (-z) = Complex.exp ((-z) * (Real.log n : ℂ)) := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℂ) ≠ 0 := by
    have : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
    rw [this]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hn_pos)
  rw [Complex.cpow_def_of_ne_zero hn_ne]
  have hcast : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, ← Complex.ofReal_log hn_pos.le, mul_comm]

/-- Algebraic evaluation of `(exp(-z*a) - exp(-z*b)) / z` in terms of `n^(-z) * windowKernel`. -/
lemma eval_exp_diff_div (u : ℝ) (hu : 0 < u) (n : ℕ) (hn : 0 < n) (ξ : ℝ) :
    let z : ℂ := (1 : ℂ) + (2 * Real.pi * ξ) * Complex.I
    let a := Real.log n - Real.log (1 + u)
    let b := Real.log n
    (Complex.exp ((-z) * (a : ℂ)) - Complex.exp ((-z) * (b : ℂ))) / z =
      (n : ℂ) ^ (-z) * windowKernel u (2 * Real.pi * ξ) := by
  intro z a b
  have ha : (-z) * (a : ℂ) = (-z) * (Real.log n : ℂ) + z * (Real.log (1 + u) : ℂ) := by
    dsimp [a]
    push_cast
    ring
  have hb : (-z) * (b : ℂ) = (-z) * (Real.log n : ℂ) := rfl
  rw [ha, hb, Complex.exp_add]
  have hcpow_u := (cpow_one_add_u_eq u hu z).symm
  have hcpow_n := (natCast_cpow_neg_eq n hn z).symm
  rw [hcpow_u, hcpow_n]
  have hz_exp : (1 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I = z := by
    dsimp [z]
    push_cast
    ring
  have h_wk : windowKernel u (2 * Real.pi * ξ) = ((1 + u : ℂ) ^ z - 1) / z := by
    unfold windowKernel
    rw [hz_exp]
  rw [h_wk]
  ring

/-- Integral of `y ↦ exp(-z * y)` over `[a, b]`. -/
lemma integral_exp_neg_mul (z : ℂ) (hz : z ≠ 0) (a b : ℝ) :
    (∫ y in a..b, Complex.exp ((-z) * (y : ℂ))) =
      (Complex.exp ((-z) * (a : ℂ)) - Complex.exp ((-z) * (b : ℂ))) / z := by
  have hneg : -z ≠ 0 := neg_ne_zero.mpr hz
  have h := integral_exp_mul_complex (a := a) (b := b) hneg
  rw [h]
  have : (Complex.exp (-z * ↑b) - Complex.exp (-z * ↑a)) / -z =
      (Complex.exp (-z * ↑a) - Complex.exp (-z * ↑b)) / z := by
    ring
  exact this

/-- Pointwise identity rewriting the Fourier summand into an exponential indicator. -/
lemma fourier_term_eq_indicator (a_n : ℂ) (n : ℕ) (u : ℝ) (ξ : ℝ) (y : ℝ) :
    let z : ℂ := (1 : ℂ) + (2 * Real.pi * ξ) * Complex.I
    let a := Real.log n - Real.log (1 + u)
    let b := Real.log n
    Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) •
        ((Ico a b).indicator (fun y => (Real.exp (-y) : ℂ) * a_n) y) =
      (Ico a b).indicator (fun y => Complex.exp ((-z) * (y : ℂ)) * a_n) y := by
  intro z a b
  rw [indicator_apply, indicator_apply]
  by_cases hy : y ∈ Ico a b
  · simp only [hy, ↓reduceIte, smul_eq_mul]
    have hexp : (Real.exp (-y) : ℂ) = Complex.exp ((-y : ℝ) : ℂ) := Complex.ofReal_exp (-y)
    rw [hexp, ← mul_assoc, ← Complex.exp_add]
    congr 2
    dsimp [z]
    push_cast
    ring
  · simp only [hy, ↓reduceIte, smul_zero]

/-- Explicit Fourier transform of a single window term. -/
lemma fourier_term_integral (a_n : ℂ) (n : ℕ) (hn : 0 < n) (u : ℝ) (hu : 0 < u) (ξ : ℝ) :
    let z : ℂ := (1 : ℂ) + (2 * Real.pi * ξ) * Complex.I
    let a := Real.log n - Real.log (1 + u)
    let b := Real.log n
    (∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) •
        ((Ico a b).indicator (fun y => (Real.exp (-y) : ℂ) * a_n) y)) =
      (a_n * (n : ℂ) ^ (-z)) * windowKernel u (2 * Real.pi * ξ) := by
  intro z a b
  have hz_ne : z ≠ 0 := by
    intro hz
    have : z.re = 0 := by rw [hz, Complex.zero_re]
    have hz_re : z.re = 1 := by
      dsimp [z]
      simp
    rw [hz_re] at this
    norm_num at this
  have hab : a ≤ b := by
    dsimp [a, b]
    have hu_pos : 0 < Real.log (1 + u) := Real.log_pos (by linarith)
    linarith
  have h_pw (y : ℝ) : Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) •
      ((Ico a b).indicator (fun y => (Real.exp (-y) : ℂ) * a_n) y) =
      (Ico a b).indicator (fun y => Complex.exp ((-z) * (y : ℂ)) * a_n) y :=
    fourier_term_eq_indicator a_n n u ξ y
  simp_rw [h_pw]
  rw [MeasureTheory.integral_indicator measurableSet_Ico]
  rw [integral_Ico_eq_integral_Ioc]
  rw [← integral_of_le hab]
  rw [intervalIntegral.integral_mul_const]
  rw [integral_exp_neg_mul z hz_ne a b]
  rw [eval_exp_diff_div u hu n hn ξ]
  ring

/-- 𝓕 G_u (ξ) = A(1 + 2πiξ) · windowKernel u (2πξ), where A = dirichletPoly a N. -/
theorem fourierIntegral_windowFun (a : ℕ → ℂ) (N : Finset ℕ) (u : ℝ) (hu : 0 < u) (hN : ∀ n ∈ N, 0 < n) (ξ : ℝ) :
    Real.fourierIntegral (windowFun a N u) ξ =
      dirichletPoly a N ((1 : ℂ) + (2 * Real.pi * ξ) * Complex.I) * windowKernel u (2 * Real.pi * ξ) := by
  let z : ℂ := (1 : ℂ) + (2 * Real.pi * ξ) * Complex.I
  change 𝓕 (windowFun a N u) ξ = dirichletPoly a N z * windowKernel u (2 * Real.pi * ξ)
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h_exp_sum (y : ℝ) :
      Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) • windowFun a N u y =
      ∑ n ∈ N, Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) •
        ((Ico (Real.log n - Real.log (1 + u)) (Real.log n)).indicator
          (fun y => (Real.exp (-y) : ℂ) * a n) y) := by
    rw [windowFun_eq_sum a N u hu hN]
    exact Finset.smul_sum
  simp_rw [h_exp_sum]
  rw [MeasureTheory.integral_finsetSum]
  · have h_terms : ∀ n ∈ N,
        (∫ y : ℝ, Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) •
          ((Ico (Real.log n - Real.log (1 + u)) (Real.log n)).indicator
            (fun y => (Real.exp (-y) : ℂ) * a n) y)) =
        (a n * (n : ℂ) ^ (-z)) * windowKernel u (2 * Real.pi * ξ) := by
      intro n hn
      exact fourier_term_integral (a n) n (hN n hn) u hu ξ
    rw [Finset.sum_congr rfl h_terms]
    rw [← Finset.sum_mul]
    rfl
  · intro n hn
    let a_int := Real.log n - Real.log (1 + u)
    let b_int := Real.log n
    have heq : (fun y => Complex.exp (↑(-2 * Real.pi * y * ξ) * Complex.I) •
        ((Ico a_int b_int).indicator (fun y => (Real.exp (-y) : ℂ) * a n) y)) =
        (Ico a_int b_int).indicator (fun y => Complex.exp ((-z) * (y : ℂ)) * a n) := by
      ext y
      exact fourier_term_eq_indicator (a n) n u ξ y
    rw [heq]
    have hcont : Continuous (fun y : ℝ => Complex.exp ((-z) * (y : ℂ)) * a n) := by
      continuity
    exact integrable_indicator_Ico_of_continuous hcont a_int b_int

end Erdos1201.MR
