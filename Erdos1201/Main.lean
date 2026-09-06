import Erdos1201.Quantitative
import Erdos1201.SmoothAsymptotics

/-!
# Main results for Erdős Problem #1201

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This formalization in Lean 4 reproduces their deduction.

This module exposes the final wrapper theorems:
- `Erdos1201.theorem1`: the upper density of the bad set tends to 0 as the block length
  `h → ∞`, conditional on `QuantitativeShortIntervalInput` and `SmoothCountingInput`.
- `Erdos1201.erdos_problem_1201`: the statement of Erdős Problem #1201, conditional
  on the same explicit analytic inputs.
-/

open Filter
open scoped Topology

namespace Erdos1201

/-- Theorem 1 in the original paper: the upper density of the bad set tends to 0 as block length
`h → ∞`, conditional on the quantitative short-interval hypothesis `hMR` and the smooth counting
hypothesis `hSmooth`. -/
theorem theorem1
    (hMR : QuantitativeShortIntervalInput) (hSmooth : SmoothCountingInput)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0) :=
  bad_upperDensity_tendsto_zero hMR.to_shortIntervalInput hSmooth.to_smoothMeanInput hε

/-- Erdős problem #1201 as stated in the paper: for every `ε > 0` and `η > 0`, there exists `k`
such that the lower density of the good set of `k` consecutive integers is at least `1 - η`,
conditional on `hMR` and `hSmooth`. -/
theorem erdos_problem_1201
    (hMR : QuantitativeShortIntervalInput) (hSmooth : SmoothCountingInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k) :=
  erdos1201 hMR.to_shortIntervalInput hSmooth.to_smoothMeanInput hε hη

end Erdos1201
