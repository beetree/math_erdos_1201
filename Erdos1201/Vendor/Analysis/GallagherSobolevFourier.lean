module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Erdos1201.Vendor.Analysis.AdditiveCharacterGeometricSums

@[expose] public section

/-!
# Fourier identities for finite trigonometric polynomials

This module records periodicity, Parseval identities, and derivative formulas
for finite complex trigonometric polynomials with integral frequencies.
-/

namespace GallagherSobolevFourier

open scoped BigOperators
open Real Complex MeasureTheory intervalIntegral
open AdditiveCharacterGeometricSums

/-- A finite trigonometric polynomial with integral frequencies. -/
noncomputable def trigonometricPolynomial (F : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ m ∈ F, b m * additiveCharacter ((m : ℝ) * x)

/-- Orthogonality of integral additive characters on one period. -/
lemma integral_additiveCharacter_orthogonality (k : ℤ) :
    (∫ x in (0 : ℝ)..1, additiveCharacter ((k : ℝ) * x)) =
      if k = 0 then 1 else 0 := by
  split_ifs <;> simp_all +decide
  · unfold additiveCharacter
    norm_num
  · unfold additiveCharacter
    have h := @integral_exp_mul_complex 0 k
    rw [h (by norm_num [Complex.ext_iff, Real.pi_ne_zero, *])]
    norm_num [Complex.exp_ne_zero, *]
    exact sub_eq_zero_of_eq (Complex.exp_eq_one_iff.mpr ⟨k, by ring⟩)

/-- Integral-frequency trigonometric polynomials are one-periodic. -/
lemma trigonometricPolynomial_periodic (F : Finset ℤ) (b : ℤ → ℂ) :
    Function.Periodic (trigonometricPolynomial F b) 1 := by
  intro x
  unfold trigonometricPolynomial
  simp [additiveCharacter]
  exact Finset.sum_congr rfl fun i _ =>
    congr_arg _ (Complex.exp_eq_exp_iff_exists_int.mpr ⟨i, by ring⟩)

/-- Parseval's identity over one period for a finite trigonometric polynomial. -/
lemma integral_normSq_trigonometricPolynomial (F : Finset ℤ) (b : ℤ → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖trigonometricPolynomial F b x‖ ^ 2) =
      ∑ m ∈ F, ‖b m‖ ^ 2 := by
  have h_expand :
      ∫ x in (0 : ℝ)..1, ‖trigonometricPolynomial F b x‖ ^ 2 =
        ∫ x in (0 : ℝ)..1, ∑ m ∈ F, ∑ n ∈ F,
          b m * starRingEnd ℂ (b n) * additiveCharacter ((m - n : ℤ) * x) := by
    convert intervalIntegral.integral_ofReal.symm using 1
    refine intervalIntegral.integral_congr fun x _ => ?_
    have h_expand : ‖trigonometricPolynomial F b x‖ ^ 2 =
        (∑ m ∈ F, b m * additiveCharacter ((m : ℝ) * x)) *
          (∑ n ∈ F, starRingEnd ℂ (b n) * additiveCharacter (-(n : ℝ) * x)) := by
      have h_expand : ‖trigonometricPolynomial F b x‖ ^ 2 =
          (∑ m ∈ F, b m * additiveCharacter ((m : ℝ) * x)) *
            starRingEnd ℂ (∑ m ∈ F, b m * additiveCharacter ((m : ℝ) * x)) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
        rfl
      convert h_expand using 2
      simp +decide [Complex.ext_iff, Complex.exp_re, Complex.exp_im, additiveCharacter]
    convert h_expand.symm using 1
    norm_num [Finset.mul_sum _ _ _, Finset.sum_mul, mul_assoc, mul_left_comm,
      sub_mul, additiveCharacter_add]
    · exact Finset.sum_comm.trans
        (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring_nf)
    · norm_cast
  have h_fubini :
      ∫ x in (0 : ℝ)..1, (∑ m ∈ F, ∑ n ∈ F,
          b m * starRingEnd ℂ (b n) * additiveCharacter ((m - n : ℤ) * x)) =
        ∑ m ∈ F, ∑ n ∈ F, b m * starRingEnd ℂ (b n) *
          ∫ x in (0 : ℝ)..1, additiveCharacter ((m - n : ℤ) * x) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · norm_num
      · exact fun _ _ =>
          Continuous.intervalIntegrable
            (Continuous.mul continuous_const (Complex.continuous_exp.comp (by continuity))) _ _
    · exact fun _ _ => Continuous.intervalIntegrable
        (continuous_finsetSum _ fun _ _ =>
          Continuous.mul (continuous_const.mul continuous_const) <|
            Complex.continuous_exp.comp <| by continuity) _ _
  calc
    ∫ x in (0 : ℝ)..1, ‖trigonometricPolynomial F b x‖ ^ 2 =
        (↑(∫ x in (0 : ℝ)..1, ‖trigonometricPolynomial F b x‖ ^ 2) : ℂ).re := by
          norm_num
    _ = (∫ x in (0 : ℝ)..1, ∑ m ∈ F, ∑ n ∈ F,
          b m * starRingEnd ℂ (b n) * additiveCharacter ((m - n : ℤ) * x)).re :=
      congr_arg Complex.re h_expand
    _ = (∑ m ∈ F, ∑ n ∈ F, b m * starRingEnd ℂ (b n) *
          ∫ x in (0 : ℝ)..1, additiveCharacter ((m - n : ℤ) * x)).re :=
      congr_arg Complex.re h_fubini
    _ = ∑ m ∈ F, ‖b m‖ ^ 2 := by
      rw [Finset.sum_congr rfl fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by rw [integral_additiveCharacter_orthogonality]]
      norm_num [Complex.normSq, Complex.sq_norm]
      simp +decide [sub_eq_zero]
      exact Finset.sum_congr rfl fun x _ => by
        rw [Finset.sum_eq_single x] <;> aesop

/-- The derivative of a finite trigonometric polynomial. -/
lemma hasDerivAt_trigonometricPolynomial (F : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) :
    HasDerivAt (trigonometricPolynomial F b)
      (∑ m ∈ F, b m * (2 * Real.pi * Complex.I * (m : ℝ)) *
        additiveCharacter ((m : ℝ) * x)) x := by
  change HasDerivAt
    (fun x => ∑ m ∈ F, b m * additiveCharacter ((m : ℝ) * x)) _ x
  refine HasDerivAt.fun_sum fun m _ => ?_
  simpa [additiveCharacter, mul_assoc, mul_comm, mul_left_comm] using
    HasDerivAt.const_mul (b m)
      (HasDerivAt.comp x (Complex.hasDerivAt_exp _)
        (HasDerivAt.const_mul (2 * Real.pi * Complex.I * (m : ℝ))
          ((hasDerivAt_id x).ofReal_comp)))

/-- The derivative, again expressed as a trigonometric polynomial. -/
lemma deriv_trigonometricPolynomial (F : Finset ℤ) (b : ℤ → ℂ) (x : ℝ) :
    deriv (trigonometricPolynomial F b) x =
      trigonometricPolynomial F (fun m => b m * (2 * Real.pi * Complex.I * (m : ℝ))) x := by
  simpa [trigonometricPolynomial] using
    HasDerivAt.deriv (hasDerivAt_trigonometricPolynomial F b x)

/-- Parseval's identity for the derivative of a finite trigonometric polynomial. -/
lemma integral_normSq_deriv_trigonometricPolynomial (F : Finset ℤ) (b : ℤ → ℂ) :
    (∫ x in (0 : ℝ)..1, ‖deriv (trigonometricPolynomial F b) x‖ ^ 2) =
      ∑ m ∈ F, (2 * Real.pi * (m : ℝ)) ^ 2 * ‖b m‖ ^ 2 := by
  rw [intervalIntegral.integral_congr fun x _ => by
    rw [deriv_trigonometricPolynomial]]
  convert integral_normSq_trigonometricPolynomial F
    (fun m => b m * (2 * Real.pi * Complex.I * m)) using 2
  · simp
  · simp only [norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
      Complex.norm_ofNat, Real.norm_eq_abs]
    rw [abs_of_pos Real.pi_pos]
    ring_nf
    rw [sq_abs]
    ring

end GallagherSobolevFourier
