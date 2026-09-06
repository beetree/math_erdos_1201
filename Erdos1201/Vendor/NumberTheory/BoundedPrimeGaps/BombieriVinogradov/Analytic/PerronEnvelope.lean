module

public import Erdos1201.Vendor.NumberTheory.BoundedPrimeGaps.BombieriVinogradov.Analytic.HalfIntegerPerronKernel

@[expose] public section

/-!
# The reciprocal envelope for the finite Perron kernel

This file makes the removable value at zero in the source's reciprocal
envelope explicit. The resulting continuous function pointwise dominates the
sine quotient and agrees almost everywhere with the printed expression.

Source: `AkbaryHambrook2013v2`, Section 6, p. 17, after equation (6.3).
Semantic review: `SEM-453`.
-/

open MeasureTheory

namespace BoundedGaps.Maynard

noncomputable section

/-- The continuous representative of `min (1 / |t|) B` for nonnegative `B`.
The explicit zero branch also gives the correct boundary function at `B=0`.
-/
noncomputable def perronEnvelope (B t : ℝ) : ℝ :=
  if B = 0 then 0 else (max |t| B⁻¹)⁻¹

/-- The removable value of the reciprocal envelope is its finite height. -/
theorem perronEnvelope_zero {B : ℝ} (hB : 0 ≤ B) :
    perronEnvelope B 0 = B := by
  by_cases hB0 : B = 0
  · simp [perronEnvelope, hB0]
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    rw [perronEnvelope, ite_eq_right hB0, abs_zero,
      max_eq_right (inv_nonneg.mpr hBpos.le), inv_inv]

/-- Away from zero, the continuous envelope is the literal source minimum. -/
theorem perronEnvelope_of_ne {B t : ℝ} (hB : 0 ≤ B) (ht : t ≠ 0) :
    perronEnvelope B t = min |t|⁻¹ B := by
  by_cases hB0 : B = 0
  · simp [perronEnvelope, hB0, inv_nonneg]
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  rw [perronEnvelope, ite_eq_right hB0]
  rcases le_total |t| B⁻¹ with h | h
  · rw [max_eq_right h, inv_inv, min_eq_right]
    exact (le_inv_comm₀ hBpos (abs_pos.mpr ht)).2 h
  · rw [max_eq_left h, min_eq_left]
    exact (inv_le_comm₀ (abs_pos.mpr ht) hBpos).2 h

/-- The totalized reciprocal envelope is continuous for every nonnegative
height. -/
theorem continuous_perronEnvelope {B : ℝ} (hB : 0 ≤ B) :
    Continuous (perronEnvelope B) := by
  by_cases hB0 : B = 0
  · subst B
    unfold perronEnvelope
    simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
  change Continuous (fun t => if B = 0 then 0 else (max |t| B⁻¹)⁻¹)
  simp only [ite_eq_right hB0]
  apply Continuous.inv₀ (continuous_abs.max continuous_const)
  intro t
  exact ne_of_gt ((inv_pos.mpr hBpos).trans_le (le_max_right _ _))


private theorem abs_mul_sinc_le_self (beta t : ℝ) (hbeta : 0 ≤ beta) :
    |beta * Real.sinc (beta * t)| ≤ beta := by
  rw [abs_mul, abs_of_nonneg hbeta]
  exact mul_le_of_le_one_right hbeta (Real.abs_sinc_le_one _)

private theorem abs_mul_sinc_le_inv (beta t : ℝ) (ht : t ≠ 0) :
    |beta * Real.sinc (beta * t)| ≤ |t|⁻¹ := by
  by_cases hb : beta = 0
  · simp [hb, abs_nonneg]
  rw [Real.sinc_of_ne_zero (mul_ne_zero hb ht)]
  have hrewrite : beta * (Real.sin (beta * t) / (beta * t)) =
      Real.sin (beta * t) / t := by
    field_simp
  rw [hrewrite, abs_div, div_eq_mul_inv]
  exact mul_le_of_le_one_left (inv_nonneg.mpr (abs_nonneg t))
    (Real.abs_sin_le_one _)

/-- The continuous sine quotient is pointwise bounded by every reciprocal
envelope whose height bounds its nonnegative frequency. -/
theorem abs_mul_sinc_le_perronEnvelope
    {beta B : ℝ} (hbeta : 0 ≤ beta) (hbetaB : beta ≤ B) (t : ℝ) :
    |beta * Real.sinc (beta * t)| ≤ perronEnvelope B t := by
  have hB : 0 ≤ B := hbeta.trans hbetaB
  by_cases ht : t = 0
  · subst t
    rw [perronEnvelope_zero hB]
    simpa [abs_of_nonneg hbeta] using hbetaB
  rw [perronEnvelope_of_ne hB ht]
  exact le_min (abs_mul_sinc_le_inv beta t ht)
    ((abs_mul_sinc_le_self beta t hbeta).trans hbetaB)



end

end BoundedGaps.Maynard
