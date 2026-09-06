module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Erdos1201.Vendor.Analysis.GallagherSobolevFourier
public import Erdos1201.Vendor.Analysis.GallagherSobolevPointwise
public import Erdos1201.Vendor.Analysis.PeriodicArcIntegralBounds

@[expose] public section

/-!
# Gallagher's core additive large-sieve estimate

This module combines a pointwise Sobolev inequality, periodic arc disjointness,
and Parseval to give a log-free finite additive large-sieve estimate.
-/

namespace GallagherAdditiveLargeSieveCore

open scoped BigOperators
open Real Complex MeasureTheory intervalIntegral
open AdditiveCharacterGeometricSums GallagherSobolevFourier
open GallagherSobolevPointwise PeriodicArcIntegralBounds

/-- A finite trigonometric polynomial is continuous. -/
lemma continuous_trigonometricPolynomial (F : Finset ℤ) (b : ℤ → ℂ) :
    Continuous (trigonometricPolynomial F b) := by
  refine continuous_finsetSum _ fun _ _ => ?_
  exact continuous_const.mul <| Complex.continuous_exp.comp <| by continuity

/-- A finite trigonometric polynomial is differentiable. -/
lemma differentiable_trigonometricPolynomial (F : Finset ℤ) (b : ℤ → ℂ) :
    Differentiable ℝ (trigonometricPolynomial F b) :=
  fun x => (hasDerivAt_trigonometricPolynomial F b x).differentiableAt

/-- The derivative of a finite trigonometric polynomial is continuous. -/
lemma continuous_deriv_trigonometricPolynomial (F : Finset ℤ) (b : ℤ → ℂ) :
    Continuous (deriv (trigonometricPolynomial F b)) := by
  convert continuous_trigonometricPolynomial F
    (fun m => b m * (2 * Real.pi * Complex.I * (m : ℝ))) using 1
  exact funext fun x => deriv_trigonometricPolynomial F b x

/-- Gallagher's log-free additive large-sieve bound for a finite trigonometric
polynomial supported in the frequency interval `[-K,K]`. -/
theorem finite_additiveLargeSieve_core (F : Finset ℤ) (b : ℤ → ℂ) (K : ℝ)
    (hK : 0 ≤ K) (hF : ∀ m ∈ F, |(m : ℝ)| ≤ K)
    (R : ℕ) (θ : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : ∀ r s, r ≠ s → δ ≤ nearestIntegerDistance (θ r - θ s)) :
    (∑ r, ‖trigonometricPolynomial F b (θ r)‖ ^ 2) ≤
      (δ⁻¹ + 4 * Real.pi * K) * ∑ m ∈ F, ‖b m‖ ^ 2 := by
  have h_sum : ∑ r, ‖trigonometricPolynomial F b (θ r)‖ ^ 2 ≤
      δ⁻¹ * (∫ t in (0 : ℝ)..1, ‖trigonometricPolynomial F b t‖ ^ 2) +
        2 * (∫ t in (0 : ℝ)..1,
          ‖trigonometricPolynomial F b t‖ * ‖deriv (trigonometricPolynomial F b) t‖) := by
    refine le_trans ?_ (add_le_add
      (mul_le_mul_of_nonneg_left
        (sum_symmetricIntervalIntegral_le_period
          (g := fun t => ‖trigonometricPolynomial F b t‖ ^ 2)
          (hg := fun _ => sq_nonneg _)
          (hper := fun x => by simp [trigonometricPolynomial_periodic F b x])
          (hgi := fun _ _ => Continuous.intervalIntegrable
            (Continuous.pow (continuous_norm.comp (continuous_trigonometricPolynomial F b)) _) _ _)
          (R := R) (θ := θ) (δ := δ) hδ hδ1 hsp)
        (inv_nonneg.mpr hδ.le))
      (mul_le_mul_of_nonneg_left
        (sum_symmetricIntervalIntegral_le_period
          (g := fun t => ‖trigonometricPolynomial F b t‖ *
            ‖deriv (trigonometricPolynomial F b) t‖)
          (hg := fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (hper := fun x => by
            simp [trigonometricPolynomial, deriv_trigonometricPolynomial, mul_add,
              Complex.exp_add, additiveCharacter]
            norm_num [show ∀ x : ℤ, Complex.exp (2 * Real.pi * Complex.I * x) = 1 from
              fun x => by rw [Complex.exp_eq_one_iff]; exact ⟨x, by ring⟩])
          (hgi := fun _ _ => Continuous.intervalIntegrable
            ((continuous_trigonometricPolynomial F b).norm.mul
              (continuous_deriv_trigonometricPolynomial F b).norm) _ _)
          (R := R) (θ := θ) (δ := δ) hδ hδ1 hsp)
        zero_le_two))
    · convert Finset.sum_le_sum fun r _ =>
        pointwise_sobolev (trigonometricPolynomial F b)
          (fun x => differentiable_trigonometricPolynomial F b x)
          (continuous_deriv_trigonometricPolynomial F b) (θ r) δ hδ using 1;
        norm_num [Finset.mul_sum, Finset.sum_add_distrib]
  have h_cauchy_schwarz :
      ∫ t in (0 : ℝ)..1, ‖trigonometricPolynomial F b t‖ *
        ‖deriv (trigonometricPolynomial F b) t‖ ≤
      Real.sqrt (∫ t in (0 : ℝ)..1, ‖trigonometricPolynomial F b t‖ ^ 2) *
        Real.sqrt (∫ t in (0 : ℝ)..1, ‖deriv (trigonometricPolynomial F b) t‖ ^ 2) := by
    have h_cauchy_schwarz : ∀ (f g : ℝ → ℝ), ContinuousOn f (Set.Icc 0 1) →
        ContinuousOn g (Set.Icc 0 1) →
        (∫ t in (0 : ℝ)..1, f t * g t) ^ 2 ≤
          (∫ t in (0 : ℝ)..1, f t ^ 2) * (∫ t in (0 : ℝ)..1, g t ^ 2) := by
      intro f g hf hg
      have h_integral_const : ∫ t in (0 : ℝ)..1,
          (f t - (∫ u in (0 : ℝ)..1, f u * g u) /
            (∫ u in (0 : ℝ)..1, g u ^ 2) * g t) ^ 2 ≥ 0 :=
        intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
      by_cases h : ∫ u in (0 : ℝ)..1, g u ^ 2 = 0 <;>
        simp_all [sub_sq, mul_pow, mul_assoc, mul_comm, mul_left_comm, div_eq_inv_mul]
      · rw [intervalIntegral.integral_of_le zero_le_one] at *
        rw [MeasureTheory.integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)] at h
        · exact MeasureTheory.integral_eq_zero_of_ae (h.mono fun _ _ => by aesop)
        · exact (ContinuousOn.integrableOn_Icc (hg.pow 2)).mono_set Set.Ioc_subset_Icc_self
      · rw [intervalIntegral.integral_add, intervalIntegral.integral_sub] at h_integral_const
        · norm_num [← mul_assoc, ← sq] at *
          have hf_nonneg : 0 ≤ ∫ t in (0 : ℝ)..1, f t ^ 2 :=
            intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
          have hg_nonneg : 0 ≤ ∫ t in (0 : ℝ)..1, g t ^ 2 :=
            intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _
          nlinarith [mul_inv_cancel₀ h, mul_inv_cancel₀ (pow_ne_zero 2 h),
            hf_nonneg, hg_nonneg]
        · apply_rules [ContinuousOn.intervalIntegrable]
          rw [Set.uIcc_of_le zero_le_one]
          change ContinuousOn (f ^ 2) (Set.Icc 0 1)
          exact hf.pow 2
        · apply_rules [ContinuousOn.intervalIntegrable]
          rw [Set.uIcc_of_le zero_le_one]
          change ContinuousOn (f * (g * fun _ => 2 *
            ((∫ u in (0 : ℝ)..1, f u * g u) * (∫ u in (0 : ℝ)..1, g u ^ 2)⁻¹)))
            (Set.Icc 0 1)
          exact hf.mul (hg.mul continuousOn_const)
        · apply_rules [ContinuousOn.intervalIntegrable]
          rw [Set.uIcc_of_le zero_le_one]
          change ContinuousOn (f ^ 2 - f * (g * fun _ => 2 *
            ((∫ u in (0 : ℝ)..1, f u * g u) * (∫ u in (0 : ℝ)..1, g u ^ 2)⁻¹)))
            (Set.Icc 0 1)
          exact (hf.pow 2).sub (hf.mul (hg.mul continuousOn_const))
        · apply_rules [ContinuousOn.intervalIntegrable]
          rw [Set.uIcc_of_le zero_le_one]
          rw [← inv_pow]
          change ContinuousOn (g ^ 2 * fun _ =>
            (∫ u in (0 : ℝ)..1, f u * g u) ^ 2 *
              (∫ u in (0 : ℝ)..1, g u ^ 2)⁻¹ ^ 2) (Set.Icc 0 1)
          exact (hg.pow 2).mul continuousOn_const
    rw [← Real.sqrt_mul (intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _)]
    refine Real.le_sqrt_of_sq_le (h_cauchy_schwarz _ _ ?_ ?_)
    · exact (continuous_norm.comp (continuous_trigonometricPolynomial F b)).continuousOn
    · exact (continuous_norm.comp (continuous_deriv_trigonometricPolynomial F b)).continuousOn
  have h_parseval :
      (∫ t in (0 : ℝ)..1, ‖trigonometricPolynomial F b t‖ ^ 2) =
        ∑ m ∈ F, ‖b m‖ ^ 2 ∧
      (∫ t in (0 : ℝ)..1, ‖deriv (trigonometricPolynomial F b) t‖ ^ 2) ≤
        (2 * Real.pi * K) ^ 2 * ∑ m ∈ F, ‖b m‖ ^ 2 := by
    rw [integral_normSq_deriv_trigonometricPolynomial, Finset.mul_sum]
    exact ⟨integral_normSq_trigonometricPolynomial F b,
      Finset.sum_le_sum fun m hm => by
        apply mul_le_mul_of_nonneg_right
        · simpa [mul_pow] using mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) (hF m hm) 2) (by positivity)
        · positivity⟩
  have h_subst : ∫ t in (0 : ℝ)..1, ‖trigonometricPolynomial F b t‖ *
      ‖deriv (trigonometricPolynomial F b) t‖ ≤
      Real.sqrt (∑ m ∈ F, ‖b m‖ ^ 2) *
        Real.sqrt ((2 * Real.pi * K) ^ 2 * ∑ m ∈ F, ‖b m‖ ^ 2) :=
    h_cauchy_schwarz.trans (mul_le_mul
      (Real.sqrt_le_sqrt (by linarith [h_parseval.1]))
      (Real.sqrt_le_sqrt (by linarith [h_parseval.2]))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  refine h_sum.trans ?_
  rw [h_parseval.1, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)] at *
  nlinarith [Real.pi_pos, mul_nonneg Real.pi_pos.le hK, Real.sqrt_nonneg (∑ m ∈ F, ‖b m‖ ^ 2),
    Real.mul_self_sqrt (show 0 ≤ ∑ m ∈ F, ‖b m‖ ^ 2 by
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _), inv_pos.mpr hδ,
    mul_inv_cancel₀ hδ.ne']

end GallagherAdditiveLargeSieveCore
