module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# A pointwise Sobolev inequality on an interval

This module bounds a differentiable complex function at the centre of an
interval by its squared mass and the product of its value and derivative.
-/

namespace GallagherSobolevPointwise

open Real Complex MeasureTheory intervalIntegral

/-- A pointwise Sobolev bound obtained by averaging the fundamental theorem of
calculus over a symmetric interval. -/
lemma pointwise_sobolev (f : ℝ → ℂ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (hf' : Continuous (deriv f)) (θ δ : ℝ) (hδ : 0 < δ) :
    ‖f θ‖ ^ 2 ≤ δ⁻¹ * (∫ t in (θ - δ/2)..(θ + δ/2), ‖f t‖ ^ 2)
        + 2 * (∫ t in (θ - δ/2)..(θ + δ/2), ‖f t‖ * ‖deriv f t‖) := by
  have h_ftc : ∀ t ∈ Set.Icc (θ - δ / 2) (θ + δ / 2), ‖f θ‖ ^ 2 ≤ ‖f t‖ ^ 2 + 2 * ∫ u in (min t θ)..(max t θ), ‖f u‖ * ‖deriv f u‖ := by
    intro t ht
    have h_ftc : ‖f θ‖^2 - ‖f t‖^2 = 2 * (∫ u in t..θ, Complex.re (star (f u) * deriv f u)) := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt]
      rotate_right
      use fun x => ‖f x‖ ^ 2 / 2
      · ring
      · intro x hx
        simpa [Complex.normSq, Complex.sq_norm, Complex.mul_re, mul_comm] using
          (HasDerivAt.norm_sq (hf x |>.hasDerivAt)).div_const 2
      · apply_rules [Continuous.intervalIntegrable]
        exact Complex.continuous_re.comp (Continuous.mul
          (Complex.continuous_conj.comp (show Continuous f from
            continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)) hf')
    cases le_total t θ <;> simp_all +decide [intervalIntegral]
    · have h_triangle : |∫ u in Set.Ioc t θ, Complex.re (star (f u) * deriv f u)| ≤ ∫ u in Set.Ioc t θ, ‖f u‖ * ‖deriv f u‖ := by
        refine (MeasureTheory.norm_integral_le_integral_norm (_ : ℝ → ℝ)).trans ?_
        refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
        · exact Filter.Eventually.of_forall fun x => norm_nonneg _
        · exact Continuous.integrableOn_Ioc (Continuous.mul
            (continuous_norm.comp (show Continuous f from
              continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt))
            (continuous_norm.comp hf'))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu using
            le_trans (Complex.abs_re_le_norm _) (by simp +decide [Complex.normSq, Complex.norm_def])
      norm_num [Complex.mul_re, Complex.mul_im] at *
      linarith [abs_le.mp h_triangle]
    · have h_triangle : |∫ x in Set.Ioc θ t, Complex.re (star (f x) * deriv f x)| ≤ ∫ x in Set.Ioc θ t, ‖f x‖ * ‖deriv f x‖ := by
        refine (MeasureTheory.norm_integral_le_integral_norm (_ : ℝ → ℝ)).trans ?_
        refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
        · exact Filter.Eventually.of_forall fun x => norm_nonneg _
        · exact Continuous.integrableOn_Ioc (Continuous.mul
            (continuous_norm.comp (show Continuous f from
              continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt))
            (continuous_norm.comp hf'))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx using
            le_trans (Complex.abs_re_le_norm _) (by simp +decide [Complex.normSq, Complex.norm_def])
      norm_num [Complex.mul_re, Complex.mul_im] at *
      linarith [abs_le.mp h_triangle]
  have h_integral_bound : ∫ t in (θ - δ / 2)..(θ + δ / 2), ‖f t‖ ^ 2 + 2 * ∫ u in (min t θ)..(max t θ), ‖f u‖ * ‖deriv f u‖ ≥ δ * ‖f θ‖ ^ 2 := by
    refine le_trans ?_ (intervalIntegral.integral_mono_on (by linarith)
      (Continuous.intervalIntegrable continuous_const _ _) ?_ h_ftc)
    · rw [intervalIntegral.integral_const]
      norm_num
    · apply_rules [Continuous.intervalIntegrable]
      refine (Continuous.pow (continuous_norm.comp (show Continuous f from
        continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)) _).add
        (continuous_const.mul ?_)
      have h_cont : Continuous (fun t => ∫ u in (0 : ℝ)..t, ‖f u‖ * ‖deriv f u‖) := by
        apply_rules [intervalIntegral.continuous_primitive]
        exact fun _ _ => Continuous.intervalIntegrable (Continuous.mul
          (continuous_norm.comp (show Continuous f from
            continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt))
          (continuous_norm.comp hf')) _ _
      convert h_cont.comp (show Continuous fun t => max t θ by continuity) |>.sub
        (h_cont.comp (show Continuous fun t => min t θ by continuity)) using 2
      · symm
        rename_i x
        change (∫ u in (0 : ℝ)..max x θ, ‖f u‖ * ‖deriv f u‖) -
          ∫ u in (0 : ℝ)..min x θ, ‖f u‖ * ‖deriv f u‖ =
          ∫ u in min x θ..max x θ, ‖f u‖ * ‖deriv f u‖
        rw [sub_eq_iff_eq_add', intervalIntegral.integral_add_adjacent_intervals] <;>
          apply_rules [Continuous.intervalIntegrable] <;>
          exact Continuous.mul (continuous_norm.comp (show Continuous f from
            continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt))
            (continuous_norm.comp hf')
  rw [intervalIntegral.integral_add] at h_integral_bound <;> norm_num at *
  · have h_integral_deriv_bound : ∫ t in (θ - δ / 2)..(θ + δ / 2), ∫ u in (min t θ)..(max t θ), ‖f u‖ * ‖deriv f u‖ ≤ ∫ t in (θ - δ / 2)..(θ + δ / 2), ∫ u in (θ - δ / 2)..(θ + δ / 2), ‖f u‖ * ‖deriv f u‖ := by
      refine intervalIntegral.integral_mono_on (by linarith) ?_
        (Continuous.intervalIntegrable continuous_const _ _) ?_
      · apply_rules [Continuous.intervalIntegrable]
        have h_cont : Continuous (fun t => ∫ u in (0 : ℝ)..t, ‖f u‖ * ‖deriv f u‖) := by
          apply_rules [intervalIntegral.continuous_primitive]
          exact fun _ _ => Continuous.intervalIntegrable (Continuous.mul
            (continuous_norm.comp (show Continuous f from
              continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt))
            (continuous_norm.comp hf')) _ _
        convert h_cont.comp (show Continuous fun t => max t θ from continuous_id.max continuous_const) |>.sub
          (h_cont.comp (show Continuous fun t => min t θ from continuous_id.min continuous_const)) using 2
        · symm
          rename_i x
          change (∫ u in (0 : ℝ)..max x θ, ‖f u‖ * ‖deriv f u‖) -
            ∫ u in (0 : ℝ)..min x θ, ‖f u‖ * ‖deriv f u‖ =
            ∫ u in min x θ..max x θ, ‖f u‖ * ‖deriv f u‖
          rw [sub_eq_iff_eq_add', intervalIntegral.integral_add_adjacent_intervals] <;>
            apply_rules [Continuous.intervalIntegrable] <;>
            exact Continuous.mul (continuous_norm.comp (show Continuous f from
              continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt))
              (continuous_norm.comp hf')
      · intro x hx₁
        refine intervalIntegral.integral_mono_interval ?_ min_le_max ?_ ?_ ?_
        · rw [le_min_iff]
          constructor <;> linarith [hx₁.1, hx₁.2, hδ.le]
        · rw [max_le_iff]
          constructor <;> linarith [hx₁.1, hx₁.2, hδ.le]
        · exact Filter.Eventually.of_forall fun u =>
            mul_nonneg (norm_nonneg (f u)) (norm_nonneg (deriv f u))
        · exact Continuous.intervalIntegrable (Continuous.mul
            (continuous_norm.comp (show Continuous f from
              continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt))
            (continuous_norm.comp hf')) _ _
    norm_num at *
    nlinarith [inv_mul_cancel_left₀ hδ.ne' (∫ t in θ - δ / 2..θ + δ / 2, ‖f t‖ ^ 2),
      inv_mul_cancel₀ hδ.ne']
  · exact Continuous.intervalIntegrable (Continuous.pow (continuous_norm.comp
      (show Continuous f from continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt)) _) _ _
  · apply_rules [Continuous.intervalIntegrable]
    have h_cont : Continuous (fun t => ∫ u in (0 : ℝ)..t, ‖f u‖ * ‖deriv f u‖) := by
      apply_rules [intervalIntegral.continuous_primitive]
      exact fun _ _ => Continuous.intervalIntegrable (Continuous.mul
          (continuous_norm.comp (show Continuous f from
            continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt))
          (continuous_norm.comp hf')) _ _
    have h_inner : Continuous (fun t => ∫ u in (min t θ)..(max t θ),
        ‖f u‖ * ‖deriv f u‖) := by
      convert h_cont.comp (show Continuous fun t => max t θ from continuous_id.max continuous_const) |>.sub
        (h_cont.comp (show Continuous fun t => min t θ from continuous_id.min continuous_const)) using 2
      rename_i x
      change (∫ u in min x θ..max x θ, ‖f u‖ * ‖deriv f u‖) =
          (∫ u in (0 : ℝ)..max x θ, ‖f u‖ * ‖deriv f u‖) -
            ∫ u in (0 : ℝ)..min x θ, ‖f u‖ * ‖deriv f u‖
      rw [eq_sub_iff_add_eq']
      have h_integrable : ∀ a b : ℝ, IntervalIntegrable
          (fun u => ‖f u‖ * ‖deriv f u‖) volume a b := fun a b =>
        Continuous.intervalIntegrable (Continuous.mul
          (continuous_norm.comp (show Continuous f from
            continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt))
          (continuous_norm.comp hf')) a b
      simpa [add_comm] using
        (intervalIntegral.integral_add_adjacent_intervals
          (h_integrable 0 (min x θ)) (h_integrable (min x θ) (max x θ)))
    exact continuous_const.mul h_inner

end GallagherSobolevPointwise
