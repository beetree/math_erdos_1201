import Erdos1201.Main
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Reciprocal mass of primes in a power-sized band

The original Erdős #1201 deduction is by Przemek Chojecki together with
ChatGPT 5.5. The elementary route developed here uses Chebyshev bounds rather
than the full Dickman asymptotic. All declarations have been compiler-checked.
-/

open Finset Filter Real MeasureTheory
open scoped Topology

namespace Erdos1201.SmoothRoute

noncomputable def primeBand (A B : ℝ) : Finset ℕ :=
  (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime

noncomputable def primeReciprocal (A B : ℝ) : ℝ :=
  ∑ p ∈ primeBand A B, (p : ℝ)⁻¹

noncomputable def primeLogReciprocal (A B : ℝ) : ℝ :=
  ∑ p ∈ primeBand A B, log p / p

/-- A positive linear lower bound for the Chebyshev theta function. -/
theorem eventually_theta_linear_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop, c * x ≤ Chebyshev.theta x := by
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  let d : ℝ := log 2 / 16
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨log 2 / 4, by positivity, ?_⟩
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
    (show 0 < (1 / 2 : ℝ) by norm_num)).bound hd
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with x hx hx2
  have hx0 : 0 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hlx : 0 ≤ log x := log_nonneg (by linarith)
  have hs : 0 ≤ sqrt x := sqrt_nonneg x
  have hlog : log x ≤ d * sqrt x := by
    simp only [Real.rpow_one, norm_eq_abs, abs_of_nonneg hlx,
      abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
    simpa only [Real.sqrt_eq_rpow] using hx
  have hsx : sqrt x ≤ x := (sqrt_le_left hx0).mpr (by nlinarith)
  have hladd : log (x + 2) ≤ 2 * log x := by
    calc
      log (x + 2) ≤ log (x * x) := log_le_log (by linarith) (by nlinarith)
      _ = 2 * log x := by rw [log_mul hxpos.ne' hxpos.ne']; ring
  have hlow := Chebyshev.theta_ge' (show 1 ≤ x by linarith)
  have hsq : sqrt x ^ 2 = x := sq_sqrt hx0
  have he1 : log (x + 2) ≤ 2 * d * x := by nlinarith
  have he2 : 2 * sqrt x * log x ≤ 2 * d * x := by nlinarith
  dsimp [d] at he1 he2
  nlinarith

private noncomputable def thetaCoeff (n : ℕ) : ℝ :=
  if n.Prime then log n else 0

private theorem sum_thetaCoeff (x : ℝ) :
    (∑ n ∈ Icc 0 ⌊x⌋₊, thetaCoeff n) = Chebyshev.theta x := by
  simp only [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter, thetaCoeff]

/-- Abel summation for the logarithmically weighted reciprocal prime sum. -/
theorem primeLogReciprocal_eq {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    primeLogReciprocal A B =
      Chebyshev.theta B / B - Chebyshev.theta A / A +
      ∫ t in A..B, Chebyshev.theta t / t ^ 2 := by
  have hd : deriv (fun t : ℝ => t⁻¹) = fun t => -(t ^ 2)⁻¹ := by
    funext t
    simp
  have hdiff : ∀ t ∈ Set.Icc A B, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := by
    intro t ht
    apply differentiableAt_id.inv
    linarith [ht.1]
  have hint : IntegrableOn (deriv (fun t : ℝ => t⁻¹)) (Set.Icc A B) := by
    rw [hd]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero _ ht0
    fun_prop
  have h := sum_mul_eq_sub_sub_integral_mul thetaCoeff hA.le hAB hdiff hint
  have hsum : (∑ n ∈ Ioc ⌊A⌋₊ ⌊B⌋₊, (n : ℝ)⁻¹ * thetaCoeff n) =
      primeLogReciprocal A B := by
    simp only [primeLogReciprocal, primeBand, Finset.sum_filter, thetaCoeff]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp [div_eq_mul_inv, mul_comm]
  rw [hsum] at h
  simp_rw [sum_thetaCoeff] at h
  rw [← intervalIntegral.integral_of_le hAB] at h
  rw [hd] at h
  have hi : (∫ t in A..B, -(t ^ 2)⁻¹ * Chebyshev.theta t) =
      -(∫ t in A..B, Chebyshev.theta t / t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hi] at h
  simpa [div_eq_mul_inv, mul_comm, sub_neg_eq_add] using h

private theorem theta_div_sq_intervalIntegrable {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / t ^ 2) volume A B := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAB]
  have hc : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc A B) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    apply ContinuousAt.continuousWithinAt
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht2 : t ^ 2 ≠ 0 := pow_ne_zero _ ht0
    fun_prop
  have hi := integrableOn_mul_sum_Icc thetaCoeff (m := 0) hA.le hc
  simpa only [sum_thetaCoeff, div_eq_mul_inv, mul_comm] using hi

/-- Positive theta mass forces positive reciprocal-prime mass. -/
theorem primeReciprocal_lower_bound {A B c : ℝ}
    (hA : 1 < A) (hAB : A ≤ B)
    (hlower : ∀ t ∈ Set.Icc A B, c * t ≤ Chebyshev.theta t) :
    c * (log B - log A) - log 4 ≤ log B * primeReciprocal A B := by
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := lt_of_lt_of_le hA0 hAB
  have hInt : c * (log B - log A) ≤
      ∫ t in A..B, Chebyshev.theta t / t ^ 2 := by
    have heq : (∫ t in A..B, c / t) = c * (log B - log A) := by
      simp_rw [div_eq_mul_inv]
      have hzero : (0 : ℝ) ∉ Set.uIcc A B := by
        rw [Set.uIcc_of_le hAB]
        simp only [Set.mem_Icc, not_and]
        intro ha
        linarith
      rw [intervalIntegral.integral_const_mul, integral_inv hzero]
      simp [log_div hB0.ne' hA0.ne']
    rw [← heq]
    apply intervalIntegral.integral_mono_on hAB
    · apply ContinuousOn.intervalIntegrable
      intro t ht
      have ht0 : t ≠ 0 := by
        rw [Set.uIcc_of_le hAB] at ht
        linarith [ht.1]
      exact ContinuousAt.continuousWithinAt (by fun_prop)
    · exact theta_div_sq_intervalIntegrable hA0 hAB
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hA0 ht.1
      have hc := hlower t ht
      calc
        c / t = (c * t) / t ^ 2 := by field_simp
        _ ≤ Chebyshev.theta t / t ^ 2 :=
          div_le_div_of_nonneg_right hc (sq_nonneg t)
  have hupper : Chebyshev.theta A / A ≤ log 4 := by
    apply (div_le_iff₀ hA0).mpr
    exact Chebyshev.theta_le_log4_mul_x hA0.le
  have hnonneg : 0 ≤ Chebyshev.theta B / B :=
    div_nonneg (Chebyshev.theta_nonneg B) hB0.le
  have hweighted : primeLogReciprocal A B ≤ log B * primeReciprocal A B := by
    rw [primeLogReciprocal, primeReciprocal, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hmem.2.pos
    have hpB : (p : ℝ) ≤ B :=
      (Nat.le_floor_iff hB0.le).mp (Finset.mem_Ioc.mp hmem.1).2
    have hlog := log_le_log hp0 hpB
    simpa [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right hlog (inv_nonneg.mpr hp0.le)
  rw [primeLogReciprocal_eq hA0 hAB] at hweighted
  linarith

end Erdos1201.SmoothRoute
