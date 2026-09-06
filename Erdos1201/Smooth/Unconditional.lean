import Erdos1201.Smooth.MeanGap
import Erdos1201.Smooth.PowerBand
import Erdos1201.Smooth.PrimeMultiples

/-!
# Unconditional smooth-number mean gap

The original Erdős #1201 deduction is by Przemek Chojecki together with
ChatGPT 5.5. This alternative route proves the smooth-number estimate needed
by that deduction using Chebyshev bounds and exact finite counting.

This is NOT a proof of the stronger `SmoothCountingInput` asymptotic. It makes
that asymptotic unnecessary for the final Erdős deduction. The MR theorem
remains an explicit hypothesis in the final wrappers below.
-/

open Filter Finset
open scoped Topology

namespace Erdos1201

/-- Increasing the smoothness cutoff can only increase the indicator. -/
theorem smoothIndicator_mono_cutoff {Y Z : ℝ} (hYZ : Y ≤ Z) (n : ℕ) :
    smoothIndicator Y n ≤ smoothIndicator Z n := by
  classical
  by_cases hY : Smooth Y n
  · have hZ : Smooth Z n := ⟨hY.1, fun p hp hd => (hY.2 p hp hd).trans hYZ⟩
    simp [smoothIndicator, hY, hZ]
  · unfold smoothIndicator
    split_ifs <;> norm_num

/-- Monotonicity of the block average in its cutoff. -/
theorem blockMean_smoothIndicator_mono {Y Z : ℝ} (hYZ : Y ≤ Z) (X : ℕ) :
    blockMean (smoothIndicator Y) X ≤ blockMean (smoothIndicator Z) X := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg X)
  exact sum_le_sum (fun n _ => smoothIndicator_mono_cutoff hYZ n)

/-- An unconditional proof of the one-sided smooth-number estimate.
There are no analytic theorem parameters in this declaration. -/
theorem smoothMeanGapInput : SmoothMeanGapInput := by
  intro β hβ0 hβ1
  let α : ℝ := (β + 1) / 2
  let γ : ℝ := (α + 1) / 2
  have hβα : β < α := by dsimp [α]; linarith
  have hαhalf : (1 / 2 : ℝ) < α := by dsimp [α]; linarith
  have hα0 : 0 < α := by linarith
  have hα1 : α < 1 := by dsimp [α]; linarith
  have hαγ : α < γ := by dsimp [γ]; linarith
  have hγ1 : γ < 1 := by dsimp [γ]; linarith
  obtain ⟨d, hd, hmass⟩ := SmoothRoute.primeReciprocal_power_lower hα0 hαγ
  have hbd := SmoothRoute.power_boundary_tendsto_zero hγ1
  refine ⟨1 - d / 2, by linarith, ?_⟩
  filter_upwards [hmass, SmoothRoute.eventually_two_mul_lt_power_sq hαhalf,
    hbd.eventually (gt_mem_nhds (show 0 < d / 2 by positivity)),
    eventually_ge_atTop (2 : ℕ)] with X hM hsize hE hX2
  have hX : 0 < X := by omega
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hcut : (X : ℝ) ^ β ≤ (X : ℝ) ^ α :=
    Real.rpow_le_rpow_of_exponent_le hX1 hβα.le
  have hbound := SmoothRoute.blockMean_le_of_primeBand (Y := (X : ℝ) ^ α)
    (B := (X : ℝ) ^ γ) hX (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hsize
  have hm := blockMean_smoothIndicator_mono hcut X
  change ((X : ℝ) ^ γ + 1) / (X : ℝ) < d / 2 at hE
  linarith

/-- The bad-density limit now needs only the qualitative MR input. -/
theorem theorem1_of_shortInterval
    (hMR : ShortIntervalInput) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0) :=
  bad_upperDensity_tendsto_zero_of_meanGap hMR smoothMeanGapInput hε

/-- The Erdős conclusion with only the qualitative MR input. -/
theorem erdos_problem_1201_of_shortInterval
    (hMR : ShortIntervalInput) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k) :=
  erdos1201_of_meanGap hMR smoothMeanGapInput hε hη

/-- The bad-density limit with no smooth-number assumption. MR is still assumed. -/
theorem theorem1_of_MR
    (hMR : QuantitativeShortIntervalInput) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0) :=
  theorem1_of_shortInterval hMR.to_shortIntervalInput hε

/-- The original conclusion with the smooth-number premise eliminated.
This is still conditional on the single displayed MR hypothesis. -/
theorem erdos_problem_1201_of_MR
    (hMR : QuantitativeShortIntervalInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k) :=
  erdos_problem_1201_of_shortInterval hMR.to_shortIntervalInput hε hη

end Erdos1201
