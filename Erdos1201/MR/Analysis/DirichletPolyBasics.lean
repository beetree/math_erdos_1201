import Mathlib

open intervalIntegral

/-!
# Basic Algebra and Mean Square of Finite Dirichlet Polynomials

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This file formalizes the basic algebraic properties and the exact $L^2$ mean-square expansion
for finite Dirichlet polynomials
$$ P(s) = \sum_{n \in N} a_n n^{-s} $$
on the line $\text{Re}(s) = 1$, evaluated over the interval $t \in [-T, T]$.
-/

namespace Erdos1201.MR

/-- Finite Dirichlet polynomial ∑_{n ∈ N} a n · n^{-s}. -/
noncomputable def dirichletPoly (a : ℕ → ℂ) (N : Finset ℕ) (s : ℂ) : ℂ := ∑ n ∈ N, a n * (n : ℂ) ^ (-s)

/-- Power of a product for natural casts with negative complex exponent. -/
theorem natCast_cpow_neg_mul (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (s : ℂ) :
    ((m * n : ℕ) : ℂ) ^ (-s) = (m : ℂ) ^ (-s) * (n : ℂ) ^ (-s) := by
  have _ := hm
  have _ := hn
  push_cast
  exact Complex.natCast_mul_natCast_cpow m n (-s)

/-- The complex norm of $n^{-(1 + it)}$ is $1/n$ for positive natural $n$. -/
theorem norm_natCast_cpow_neg_one_add_mul_I (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ = 1 / n := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  have h_re : (-((1 : ℂ) + (t : ℂ) * Complex.I)).re = -1 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
  rw [h_re, Real.rpow_neg_one, one_div]

/-- Pointwise triangle inequality bound for a finite Dirichlet polynomial on the line Re s = 1. -/
theorem norm_dirichletPoly_le (a : ℕ → ℂ) (N : Finset ℕ) (hN : ∀ n ∈ N, 0 < n) (t : ℝ) :
    ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I)‖ ≤ ∑ n ∈ N, ‖a n‖ / n := by
  unfold dirichletPoly
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, norm_natCast_cpow_neg_one_add_mul_I n (hN n hn) t, mul_one_div]

/-- For any complex number $z$, the squared norm equals the real part of $z \overline{z}$. -/
lemma norm_sq_eq_mul_conj_re (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg z)]

/-- Expansion of the squared norm of a finite sum in terms of pairs $f(m) \overline{f(n)}$. -/
lemma norm_sq_sum_eq_re_sum_sum {α : Type*} (N : Finset α) (f : α → ℂ) :
    ‖∑ n ∈ N, f n‖ ^ 2 = ∑ m ∈ N, ∑ n ∈ N, (f m * (starRingEnd ℂ) (f n)).re := by
  rw [norm_sq_eq_mul_conj_re]
  rw [map_sum (starRingEnd ℂ)]
  rw [Finset.sum_mul_sum]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Complex.re_sum]

/-- Splitting a double sum into diagonal $m = n$ and off-diagonal $n \ne m$ components. -/
lemma sum_sum_eq_diag_add_offdiag {α β : Type*} [DecidableEq α] [AddCommMonoid β] (N : Finset α) (g : α → α → β) :
    ∑ m ∈ N, ∑ n ∈ N, g m n = (∑ n ∈ N, g n n) + ∑ m ∈ N, ∑ n ∈ N.erase m, g m n := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.add_sum_erase N (g m) hm]

/-- Integration commutes with taking the real part of an integrable complex-valued function. -/
lemma integral_re_comm {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    (∫ t in a..b, (f t).re) = (∫ t in a..b, f t).re :=
  Complex.reCLM.intervalIntegral_comp_comm hf

/-- Continuity of $t \mapsto \exp(-i t L)$. -/
lemma continuous_exp_neg_I_mul (L : ℝ) :
    Continuous (fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (L : ℂ))) := by
  fun_prop

/-- Explicit algebraic evaluation of $(\exp(-iLT) - \exp(iLT))/(-iL) = 2 \sin(TL)/L$. -/
lemma exp_diff_div (T L : ℝ) (hL : L ≠ 0) :
    (Complex.exp (-Complex.I * (L : ℂ) * (T : ℂ)) - Complex.exp (-Complex.I * (L : ℂ) * (-T : ℂ))) /
      (-Complex.I * (L : ℂ)) = (2 * Real.sin (T * L) / L : ℂ) := by
  have hc : -Complex.I * (L : ℂ) = -(Complex.I * (L : ℂ)) := by ring
  have hT1 : -Complex.I * (L : ℂ) * (T : ℂ) = Complex.I * -((T * L : ℝ) : ℂ) := by
    push_cast; ring
  have hT2 : -Complex.I * (L : ℂ) * (-T : ℂ) = Complex.I * ((T * L : ℝ) : ℂ) := by
    push_cast; ring
  rw [hT1, hT2, hc]
  have h_div : (Complex.exp (Complex.I * -((T * L : ℝ) : ℂ)) - Complex.exp (Complex.I * ((T * L : ℝ) : ℂ))) /
      -(Complex.I * (L : ℂ)) =
      ((Complex.exp (Complex.I * ((T * L : ℝ) : ℂ)) - Complex.exp (Complex.I * -((T * L : ℝ) : ℂ))) / Complex.I) / (L : ℂ) := by
    have _ : Complex.I ≠ 0 := Complex.I_ne_zero
    have _ : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
    ring_nf
  rw [h_div]
  have h_sin : (Complex.exp (Complex.I * ((T * L : ℝ) : ℂ)) - Complex.exp (Complex.I * -((T * L : ℝ) : ℂ))) / Complex.I =
      2 * (Real.sin (T * L) : ℂ) := by
    simp only [mul_comm Complex.I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      add_sub_add_left_eq_sub, Complex.div_I, Complex.ofReal_sin]
    rw [sub_mul, mul_assoc, mul_assoc, two_mul]
    simp
  rw [h_sin]

/-- Exact integral of the complex exponential $\int_{-T}^T \exp(-i t L) dt = 2 \sin(TL)/L$. -/
lemma integral_exp_neg_I_mul (T L : ℝ) (hL : L ≠ 0) :
    ∫ t in (-T)..T, Complex.exp (-Complex.I * (t : ℂ) * (L : ℂ)) =
      (2 * Real.sin (T * L) / L : ℂ) := by
  have hc : (-Complex.I * (L : ℂ)) ≠ 0 := by
    have hI : -Complex.I ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    have hL_c : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
    exact mul_ne_zero hI hL_c
  have h_int := integral_exp_mul_complex (a := -T) (b := T) hc
  have h_eq : (fun t : ℝ => Complex.exp (-Complex.I * (t : ℂ) * (L : ℂ))) =
      (fun t : ℝ => Complex.exp ((-Complex.I * (L : ℂ)) * (t : ℂ))) := by
    ext t
    ring_nf
  rw [h_eq, h_int]
  have h_neg : ((-T : ℝ) : ℂ) = - (T : ℂ) := by push_cast; rfl
  rw [h_neg]
  exact exp_diff_div T L hL

/-- Exact integral of a constant multiple of $\exp(-i t L)$ taking real parts. -/
lemma integral_const_mul_exp_re (C : ℂ) (T L : ℝ) (hL : L ≠ 0) :
    ∫ t in (-T)..T, (C * Complex.exp (-Complex.I * (t : ℂ) * (L : ℂ))).re =
      (C * (2 * Real.sin (T * L) / L : ℂ)).re := by
  have h_cont : Continuous (fun t : ℝ => C * Complex.exp (-Complex.I * (t : ℂ) * (L : ℂ))) :=
    continuous_const.mul (continuous_exp_neg_I_mul L)
  have h_int : IntervalIntegrable (fun t : ℝ => C * Complex.exp (-Complex.I * (t : ℂ) * (L : ℂ)))
      MeasureTheory.volume (-T) T := h_cont.intervalIntegrable (-T) T
  rw [integral_re_comm h_int]
  rw [integral_const_mul]
  rw [integral_exp_neg_I_mul T L hL]

/-- Decomposition of $n^{-(1+it)}$ as $n^{-1} \exp(-i t \log n)$. -/
lemma natCast_cpow_neg_one_add_mul_I_eq_exp (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I)) =
      (1 / (n : ℂ)) * Complex.exp (-Complex.I * (t : ℂ) * (Real.log n : ℂ)) := by
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hn_pos)
  rw [Complex.cpow_def_of_ne_zero hn_ne]
  have h_log : Complex.log (n : ℂ) = (Real.log n : ℂ) := Complex.natCast_log.symm
  rw [h_log]
  have h_exp_add : (Real.log n : ℂ) * -((1 : ℂ) + (t : ℝ) * Complex.I) =
      (-(Real.log n : ℂ)) + (-Complex.I * (t : ℂ) * (Real.log n : ℂ)) := by
    push_cast; ring
  rw [h_exp_add, Complex.exp_add]
  have h_exp_log : Complex.exp (-(Real.log n : ℂ)) = 1 / (n : ℂ) := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hn_pos]
    push_cast
    rw [one_div]
  rw [h_exp_log]

/-- Complex conjugate of $\exp(-i t L)$ is $\exp(i t L)$. -/
lemma starRingEnd_exp_neg_I_mul (t L : ℝ) :
    (starRingEnd ℂ) (Complex.exp (-Complex.I * (t : ℂ) * (L : ℂ))) =
      Complex.exp (Complex.I * (t : ℂ) * (L : ℂ)) := by
  rw [← Complex.exp_conj]
  have h_conj : (starRingEnd ℂ) (-Complex.I * (t : ℂ) * (L : ℂ)) =
      Complex.I * (t : ℂ) * (L : ℂ) := by
    simp only [map_mul, map_neg, Complex.conj_I, neg_neg, Complex.conj_ofReal]
  rw [h_conj]

/-- Product of exponential terms $\exp(-it \log m) \exp(it \log n) = \exp(-it \log(m/n))$. -/
lemma exp_mul_exp_conj_log (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    Complex.exp (-Complex.I * (t : ℂ) * (Real.log m : ℂ)) *
    Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)) =
    Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / n) : ℂ)) := by
  rw [← Complex.exp_add]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_log_div : Real.log ((m : ℝ) / n) = Real.log m - Real.log n :=
    Real.log_div (ne_of_gt hm_pos) (ne_of_gt hn_pos)
  rw [h_log_div]
  push_cast
  ring_nf

/-- Algebraic reduction of the off-diagonal pair product $z_m(t) \overline{z_n(t)}$. -/
lemma off_diag_term_eq (a : ℕ → ℂ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    (a m * (m : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) *
    (starRingEnd ℂ) (a n * (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) =
    (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) *
    Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / n) : ℂ)) := by
  rw [natCast_cpow_neg_one_add_mul_I_eq_exp m hm t]
  rw [natCast_cpow_neg_one_add_mul_I_eq_exp n hn t]
  simp only [map_mul, map_div₀, map_one]
  have h_conj_n : (starRingEnd ℂ) (n : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.conj_ofReal]
  rw [h_conj_n, starRingEnd_exp_neg_I_mul]
  have h_exp := exp_mul_exp_conj_log m n hm hn t
  calc (a m * (1 / (m : ℂ) * Complex.exp (-Complex.I * ↑t * ↑(Real.log ↑m)))) *
      ((starRingEnd ℂ) (a n) * (1 / (n : ℂ) * Complex.exp (Complex.I * ↑t * ↑(Real.log ↑n))))
    _ = (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
        (Complex.exp (-Complex.I * ↑t * ↑(Real.log ↑m)) * Complex.exp (Complex.I * ↑t * ↑(Real.log ↑n))) := by
      ring
    _ = (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * ↑n)) *
        Complex.exp (-Complex.I * ↑t * ↑(Real.log (↑m / ↑n))) := by
      rw [h_exp]

/-- The logarithm $\log(m/n) \ne 0$ for positive distinct natural numbers $m \ne n$. -/
lemma log_div_ne_zero_of_ne {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Real.log ((m : ℝ) / n) ≠ 0 := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_div_pos : 0 < (m : ℝ) / n := div_pos hm_pos hn_pos
  intro h_log
  have h1 : (m : ℝ) / n = 1 := Real.eq_one_of_pos_of_log_eq_zero h_div_pos h_log
  have hmn_eq : (m : ℝ) = (n : ℝ) := (div_eq_one_iff_eq (ne_of_gt hn_pos)).mp h1
  exact hmn (Nat.cast_injective hmn_eq)

/-- Exact mean square over [-T, T]: diagonal 2T plus off-diagonal Dirichlet-kernel terms. -/
theorem integral_norm_sq_dirichletPoly (a : ℕ → ℂ) (N : Finset ℕ) (hN : ∀ n ∈ N, 0 < n) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I)‖ ^ 2 =
      2 * T * ∑ n ∈ N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 +
      ∑ m ∈ N, ∑ n ∈ N.erase m, ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) *
          (2 * Real.sin (T * Real.log ((m : ℝ) / n)) / Real.log ((m : ℝ) / n) : ℂ)).re := by
  have _ := hT
  have h_norm_sq (t : ℝ) :
      ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 =
      (∑ n ∈ N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2) +
      ∑ m ∈ N, ∑ n ∈ N.erase m, ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / n) : ℂ))).re := by
    unfold dirichletPoly
    rw [norm_sq_sum_eq_re_sum_sum]
    rw [sum_sum_eq_diag_add_offdiag]
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      have hn_pos := hN n hn
      rw [← norm_sq_eq_mul_conj_re]
      rw [norm_mul, norm_natCast_cpow_neg_one_add_mul_I n hn_pos t]
      ring
    · apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      have hm_pos := hN m hm
      have hn_in : n ∈ N := Finset.mem_of_mem_erase hn
      have hn_pos := hN n hn_in
      rw [off_diag_term_eq a m n hm_pos hn_pos t]
  have h_int_eq :
      (∫ t in (-T)..T, ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I)‖ ^ 2) =
      ∫ t in (-T)..T, ((∑ n ∈ N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2) +
        ∑ m ∈ N, ∑ n ∈ N.erase m, ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) *
          Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / n) : ℂ))).re) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact h_norm_sq t
  rw [h_int_eq]
  have h_int_diag : IntervalIntegrable (fun _ : ℝ => ∑ n ∈ N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2)
      MeasureTheory.volume (-T) T := intervalIntegrable_const
  have h_int_term (m n : ℕ) :
      IntervalIntegrable (fun t : ℝ => ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / n) : ℂ))).re)
        MeasureTheory.volume (-T) T := by
    have hc : Continuous (fun t : ℝ => ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / n) : ℂ))).re) := by
      fun_prop
    exact hc.intervalIntegrable (-T) T
  have h_int_offdiag_inner (m : ℕ) :
      IntervalIntegrable (fun t : ℝ => ∑ n ∈ N.erase m, ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / n) : ℂ))).re)
        MeasureTheory.volume (-T) T := by
    have hc : Continuous (fun t : ℝ => ∑ n ∈ N.erase m, ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / n) : ℂ))).re) := by
      apply continuous_finsetSum
      intro n _
      fun_prop
    exact hc.intervalIntegrable (-T) T
  have h_int_offdiag :
      IntervalIntegrable (fun t : ℝ => ∑ m ∈ N, ∑ n ∈ N.erase m, ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / n) : ℂ))).re)
        MeasureTheory.volume (-T) T := by
    have hc : Continuous (fun t : ℝ => ∑ m ∈ N, ∑ n ∈ N.erase m, ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) *
        Complex.exp (-Complex.I * (t : ℂ) * (Real.log ((m : ℝ) / n) : ℂ))).re) := by
      apply continuous_finsetSum
      intro m _
      apply continuous_finsetSum
      intro n _
      fun_prop
    exact hc.intervalIntegrable (-T) T
  rw [intervalIntegral.integral_add h_int_diag h_int_offdiag]
  congr 1
  · rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  · rw [intervalIntegral.integral_finsetSum (fun m _ => h_int_offdiag_inner m)]
    apply Finset.sum_congr rfl
    intro m hm
    rw [intervalIntegral.integral_finsetSum (fun n _ => h_int_term m n)]
    apply Finset.sum_congr rfl
    intro n hn
    have hm_pos := hN m hm
    have hn_in : n ∈ N := Finset.mem_of_mem_erase hn
    have hn_pos := hN n hn_in
    have hmn : m ≠ n := (Finset.ne_of_mem_erase hn).symm
    have hL : Real.log ((m : ℝ) / n) ≠ 0 := log_div_ne_zero_of_ne hm_pos hn_pos hmn
    exact integral_const_mul_exp_re (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * n)) T (Real.log ((m : ℝ) / n)) hL

/-- Pointwise upper bound on each off-diagonal integrated Dirichlet kernel term. -/
lemma off_diag_bound (am an : ℂ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (T L : ℝ) (hL : L ≠ 0) :
    ((am * (starRingEnd ℂ) an / ((m : ℂ) * n)) *
      (2 * Real.sin (T * L) / L : ℂ)).re ≤
    2 * ‖am‖ * ‖an‖ / ((m : ℝ) * n * |L|) := by
  have _ := hm
  have _ := hn
  have h_abs_L : 0 < |L| := abs_pos.mpr hL
  have h_norm_conj : ‖(starRingEnd ℂ) an‖ = ‖an‖ := RCLike.norm_conj an
  have h_re_le := Complex.re_le_norm ((am * (starRingEnd ℂ) an / ((m : ℂ) * n)) *
      (2 * Real.sin (T * L) / L : ℂ))
  refine h_re_le.trans ?_
  rw [norm_mul, norm_div, norm_mul, h_norm_conj]
  have h_m : ‖(m : ℂ) * (n : ℂ)‖ = (m : ℝ) * (n : ℝ) := by
    rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  rw [h_m]
  have h_sin_term : ‖(2 * Real.sin (T * L) / L : ℂ)‖ = 2 * |Real.sin (T * L)| / |L| := by
    rw [norm_div, norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs]
  rw [h_sin_term]
  have h_sin_le : |Real.sin (T * L)| ≤ 1 := Real.abs_sin_le_one (T * L)
  have h_frac_le : 2 * |Real.sin (T * L)| / |L| ≤ 2 / |L| := by
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt h_abs_L)
  have h_prod_le : (‖am‖ * ‖an‖ / ((m : ℝ) * (n : ℝ))) * (2 * |Real.sin (T * L)| / |L|) ≤
      (‖am‖ * ‖an‖ / ((m : ℝ) * (n : ℝ))) * (2 / |L|) := by
    exact mul_le_mul_of_nonneg_left h_frac_le (by positivity)
  refine h_prod_le.trans ?_
  rw [div_mul_div_comm]
  ring_nf
  rfl

/-- Upper bound on the mean square of a Dirichlet polynomial: diagonal plus off-diagonal kernel bounds. -/
theorem integral_norm_sq_dirichletPoly_le (a : ℕ → ℂ) (N : Finset ℕ) (hN : ∀ n ∈ N, 0 < n) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      2 * T * ∑ n ∈ N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 +
      ∑ m ∈ N, ∑ n ∈ N.erase m, 2 * ‖a m‖ * ‖a n‖ / ((m : ℝ) * n * |Real.log ((m : ℝ) / n)|) := by
  rw [integral_norm_sq_dirichletPoly a N hN T hT]
  gcongr with m hm n hn
  have hm_pos := hN m hm
  have hn_in : n ∈ N := Finset.mem_of_mem_erase hn
  have hn_pos := hN n hn_in
  have hmn : m ≠ n := (Finset.ne_of_mem_erase hn).symm
  have hL : Real.log ((m : ℝ) / n) ≠ 0 := log_div_ne_zero_of_ne hm_pos hn_pos hmn
  exact off_diag_bound (a m) (a n) m n hm_pos hn_pos T (Real.log ((m : ℝ) / n)) hL

end Erdos1201.MR
