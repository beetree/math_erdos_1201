import Erdos1201.Smooth.PrimeBand

/-!
# Prime reciprocal mass between two powers

The original Erdős #1201 deduction is by Przemek Chojecki together with
ChatGPT 5.5. This module derives a strictly positive reciprocal-prime mass
using the proved Chebyshev--Abel estimate, without a prime number theorem.
-/

open Filter Real
open scoped Topology

namespace Erdos1201.SmoothRoute

/-- Primes between two distinct positive powers have uniformly positive
reciprocal mass for all sufficiently large scales. -/
theorem primeReciprocal_power_lower {α γ : ℝ} (hα : 0 < α) (hαγ : α < γ) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ X : ℕ in atTop,
      d ≤ primeReciprocal ((X : ℝ) ^ α) ((X : ℝ) ^ γ) := by
  obtain ⟨c, hc, ht⟩ := eventually_theta_linear_lower
  obtain ⟨T, hT⟩ := eventually_atTop.mp ht
  have hγ : 0 < γ := hα.trans hαγ
  let K : ℝ := c * (γ - α)
  have hK : 0 < K := mul_pos hc (sub_pos.mpr hαγ)
  let d : ℝ := K / (2 * γ)
  have hd : 0 < d := div_pos hK (by positivity)
  refine ⟨d, hd, ?_⟩
  have hp := (tendsto_rpow_atTop hα).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hl := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hp.eventually (eventually_ge_atTop (max T 2)),
    hl.eventually (eventually_ge_atTop (2 * log 4 / K)),
    eventually_ge_atTop (2 : ℕ)] with X hXT hXL hX2
  change max T 2 ≤ (X : ℝ) ^ α at hXT
  change 2 * log 4 / K ≤ log (X : ℝ) at hXL
  have hX1 : (1 : ℝ) < X := by exact_mod_cast hX2
  have hX0 : (0 : ℝ) < X := by linarith
  have hA : 1 < (X : ℝ) ^ α := by
    have := (le_max_right T 2).trans hXT
    linarith
  have hAB : (X : ℝ) ^ α ≤ (X : ℝ) ^ γ :=
    Real.rpow_le_rpow_of_exponent_le hX1.le hαγ.le
  have hbound := primeReciprocal_lower_bound (c := c) hA hAB
    (fun t ht => hT t ((le_max_left T 2).trans (hXT.trans ht.1)))
  rw [log_rpow hX0, log_rpow hX0] at hbound
  have hL : 0 < log (X : ℝ) := log_pos hX1
  have herror : 2 * log 4 ≤ K * log (X : ℝ) := by
    have := (div_le_iff₀ hK).mp hXL
    nlinarith
  have hKdef : K = c * (γ - α) := rfl
  have hKd : 2 * γ * d = K := by dsimp [d]; field_simp
  have hmain : γ * log (X : ℝ) * d ≤
      γ * log (X : ℝ) * primeReciprocal ((X : ℝ) ^ α) ((X : ℝ) ^ γ) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ (mul_pos hγ hL)).mp hmain

/-- A power with exponent below one is negligible relative to the scale. -/
theorem power_boundary_tendsto_zero {γ : ℝ} (hγ : γ < 1) :
    Tendsto (fun X : ℕ => ((X : ℝ) ^ γ + 1) / (X : ℝ)) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_neg_atTop (show 0 < 1 - γ by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hpow : Tendsto (fun X : ℕ => (X : ℝ) ^ γ / (X : ℝ)) atTop (𝓝 0) := by
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with X hX
    have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
    change (X : ℝ) ^ (-(1 - γ)) = (X : ℝ) ^ γ / (X : ℝ)
    rw [show -(1 - γ) = γ - 1 by ring, Real.rpow_sub hX0, Real.rpow_one]
  simpa only [add_div, add_zero] using hpow.add tendsto_one_div_atTop

/-- Every exponent above one half eventually gives a cutoff beyond sqrt(2X). -/
theorem eventually_two_mul_lt_power_sq {α : ℝ} (hα : (1 / 2 : ℝ) < α) :
    ∀ᶠ X : ℕ in atTop, 2 * (X : ℝ) < ((X : ℝ) ^ α) ^ 2 := by
  have ht := (tendsto_rpow_atTop (show 0 < 2 * α - 1 by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually (eventually_gt_atTop (2 : ℝ)),
    eventually_gt_atTop (0 : ℕ)] with X hpow hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  change 2 < (X : ℝ) ^ (2 * α - 1) at hpow
  have hh := mul_lt_mul_of_pos_right hpow hX0
  have heq : (X : ℝ) ^ (2 * α - 1) * (X : ℝ) = ((X : ℝ) ^ α) ^ 2 := by
    calc
      _ = (X : ℝ) ^ (2 * α - 1) * (X : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (X : ℝ) ^ ((2 * α - 1) + 1) := (Real.rpow_add hX0 _ _).symm
      _ = (X : ℝ) ^ (α * 2) := by congr 1; ring
      _ = _ := by rw [Real.rpow_mul hX0.le, Real.rpow_two]
  rwa [heq] at hh

end Erdos1201.SmoothRoute
