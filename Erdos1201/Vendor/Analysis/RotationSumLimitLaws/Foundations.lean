module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Probability.CDF
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.GCongr

/-
Elementary probability and measurability facts for normalized finite rotation
sums, together with the centered Cauchy distribution function of scale
`1 / (2π)`.
-/

@[expose] public section

namespace RotationSumLimitLaws

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

/-- The centered fractional-part sawtooth. -/
def centeredFractionalSawtooth (x : ℝ) : ℝ :=
  (1 : ℝ) / 2 - Int.fract x

/-- A finite rotation sum, indexed from one through `N`. -/
def finiteRotationSum (N : ℕ) (α : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, centeredFractionalSawtooth ((k : ℝ) * α)

/-- The logarithmically normalized finite rotation sum. -/
def normalizedFiniteRotationSum (N : ℕ) (α : ℝ) : ℝ :=
  finiteRotationSum N α / Real.log (N : ℝ)

/-- The Lebesgue distribution value of a normalized finite rotation sum on
the open unit interval. -/
def rotationDistributionValue (N : ℕ) (c : ℝ) : ℝ :=
  (volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedFiniteRotationSum N α ≤ c}).toReal

/-- The centered Cauchy distribution function with scale `1 / (2π)`. -/
def centeredCauchyCDF (c : ℝ) : ℝ :=
  (1 : ℝ) / 2 + (1 / Real.pi) * Real.arctan (2 * Real.pi * c)

theorem measurable_centeredFractionalSawtooth : Measurable centeredFractionalSawtooth := by
  exact measurable_const.sub measurable_id.fract

theorem measurable_finiteRotationSum (N : ℕ) : Measurable (finiteRotationSum N) := by
  classical
  unfold finiteRotationSum
  exact Finset.measurable_fun_sum (Finset.Icc 1 N) fun k _ =>
    measurable_centeredFractionalSawtooth.comp (measurable_const.mul measurable_id)

theorem measurable_normalizedFiniteRotationSum (N : ℕ) :
    Measurable (normalizedFiniteRotationSum N) := by
  exact (measurable_finiteRotationSum N).div_const _


theorem volume_rotationDistributionEvent_le_one (N : ℕ) (c : ℝ) :
    volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedFiniteRotationSum N α ≤ c} ≤ 1 := by
  calc
    volume {α : ℝ | α ∈ Ioo (0 : ℝ) 1 ∧ normalizedFiniteRotationSum N α ≤ c}
        ≤ volume (Ioo (0 : ℝ) 1) := measure_mono fun _ hα => hα.1
    _ = 1 := by simp




/-- Lebesgue measure restricted to the open unit interval. -/
def uniformOpenUnitIntervalMeasure : Measure ℝ :=
  volume.restrict (Ioo (0 : ℝ) 1)

instance uniformOpenUnitIntervalMeasure_isProbabilityMeasure :
    IsProbabilityMeasure uniformOpenUnitIntervalMeasure where
  measure_univ := by simp [uniformOpenUnitIntervalMeasure]

/-- Uniform probability measure on the open unit interval. -/
def uniformOpenUnitInterval : ProbabilityMeasure ℝ :=
  ⟨uniformOpenUnitIntervalMeasure, inferInstance⟩

/-- The law of a normalized finite rotation sum under open-unit-interval
Lebesgue measure. -/
def normalizedRotationLaw (N : ℕ) : ProbabilityMeasure ℝ :=
  uniformOpenUnitInterval.map (measurable_normalizedFiniteRotationSum N).aemeasurable

theorem cdf_normalizedRotationLaw_eq_rotationDistributionValue (N : ℕ) (c : ℝ) :
    ProbabilityTheory.cdf (normalizedRotationLaw N : Measure ℝ) c =
      rotationDistributionValue N c := by
  rw [ProbabilityTheory.cdf_eq_real]
  change ((uniformOpenUnitIntervalMeasure.map (normalizedFiniteRotationSum N)).real (Iic c)) = _
  rw [map_measureReal_apply
    (measurable_normalizedFiniteRotationSum N) measurableSet_Iic]
  rw [show uniformOpenUnitIntervalMeasure = volume.restrict (Ioo (0 : ℝ) 1) from rfl]
  rw [measureReal_restrict_apply' measurableSet_Ioo]
  unfold rotationDistributionValue
  congr 1
  ext α
  simp [and_comm]

/-- The Stieltjes function of the centered Cauchy law of scale `1 / (2π)`. -/
def centeredCauchyStieltjes : StieltjesFunction ℝ where
  toFun := centeredCauchyCDF
  mono' := by
    intro a b hab
    unfold centeredCauchyCDF
    gcongr
  right_continuous' := by
    intro x
    apply Continuous.continuousWithinAt
    unfold centeredCauchyCDF
    fun_prop

theorem tendsto_centeredCauchyCDF_atTop :
    Tendsto centeredCauchyCDF atTop (nhds 1) := by
  have harg : Tendsto (fun c : ℝ ↦ (2 * Real.pi) * c) atTop atTop :=
    tendsto_id.const_mul_atTop (mul_pos (by positivity) Real.pi_pos)
  have hatan :
      Tendsto (fun c : ℝ ↦ Real.arctan ((2 * Real.pi) * c)) atTop
        (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp harg
  have hscaled :
      Tendsto (fun c : ℝ ↦ (1 / Real.pi) * Real.arctan ((2 * Real.pi) * c))
        atTop (nhds ((1 / Real.pi) * (Real.pi / 2))) :=
    hatan.const_mul (1 / Real.pi)
  have h := hscaled.const_add ((1 : ℝ) / 2)
  have hend :
      (1 : ℝ) / 2 + (1 / Real.pi) * (Real.pi / 2) = 1 := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [hend] at h
  change Tendsto
    (fun c : ℝ ↦ (1 : ℝ) / 2 + (1 / Real.pi) * Real.arctan (2 * Real.pi * c))
    atTop (nhds 1)
  exact h

theorem tendsto_centeredCauchyCDF_atBot :
    Tendsto centeredCauchyCDF atBot (nhds 0) := by
  have harg : Tendsto (fun c : ℝ ↦ (2 * Real.pi) * c) atBot atBot :=
    tendsto_id.const_mul_atBot (mul_pos (by positivity) Real.pi_pos)
  have hatan :
      Tendsto (fun c : ℝ ↦ Real.arctan ((2 * Real.pi) * c)) atBot
        (nhds (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp harg
  have hscaled :
      Tendsto (fun c : ℝ ↦ (1 / Real.pi) * Real.arctan ((2 * Real.pi) * c))
        atBot (nhds ((1 / Real.pi) * (-(Real.pi / 2)))) :=
    hatan.const_mul (1 / Real.pi)
  have h := hscaled.const_add ((1 : ℝ) / 2)
  have hend :
      (1 : ℝ) / 2 + (1 / Real.pi) * (-(Real.pi / 2)) = 0 := by
    field_simp [Real.pi_ne_zero]
    norm_num
  rw [hend] at h
  change Tendsto
    (fun c : ℝ ↦ (1 : ℝ) / 2 + (1 / Real.pi) * Real.arctan (2 * Real.pi * c))
    atBot (nhds 0)
  exact h

/-- The centered Cauchy measure associated to `centeredCauchyCDF`. -/
def centeredCauchyMeasure : Measure ℝ :=
  centeredCauchyStieltjes.measure

instance centeredCauchyMeasure_isProbabilityMeasure : IsProbabilityMeasure centeredCauchyMeasure := by
  refine ⟨?_⟩
  simpa [centeredCauchyMeasure] using
    (centeredCauchyStieltjes.measure_univ tendsto_centeredCauchyCDF_atBot
      tendsto_centeredCauchyCDF_atTop)

/-- The limiting centered Cauchy probability measure. -/
def centeredCauchyProbability : ProbabilityMeasure ℝ :=
  ⟨centeredCauchyMeasure, inferInstance⟩

theorem cdf_centeredCauchyMeasure :
    ProbabilityTheory.cdf centeredCauchyMeasure = centeredCauchyStieltjes := by
  exact ProbabilityTheory.cdf_measure_stieltjesFunction centeredCauchyStieltjes
    tendsto_centeredCauchyCDF_atBot tendsto_centeredCauchyCDF_atTop

theorem cdf_centeredCauchyMeasure_apply (c : ℝ) :
    ProbabilityTheory.cdf centeredCauchyMeasure c = centeredCauchyCDF c := by
  rw [cdf_centeredCauchyMeasure]
  rfl

end

end RotationSumLimitLaws
