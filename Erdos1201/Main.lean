import Erdos1201.Quantitative
import Erdos1201.SmoothInput

/-!
# Main results for Erdős Problem #1201

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This formalization in Lean 4 reproduces their deduction.

This module exposes the wrapper theorems with an explicit analytic hypothesis:
- `Erdos1201.theorem1`: the upper density of the bad set tends to 0 as the block length
  `h → ∞`, given `QuantitativeShortIntervalInput`.
- `Erdos1201.erdos_problem_1201`: the statement of Erdős Problem #1201, given the same
  single explicit analytic input.

The smooth-number input used by the paper is proved by `Erdos1201.smoothUpperInput`
(see `Erdos1201.SmoothInput`). The unconditional theorems, which prove the short-interval
input for the smooth indicator instead of assuming it, are in `Erdos1201.Final`.
-/

open Filter
open scoped Topology

namespace Erdos1201

/-- Theorem 1 in the original paper: the upper density of the bad set tends to 0 as block length
`h → ∞`, conditional on the quantitative short-interval hypothesis `hMR`. -/
theorem theorem1
    (hMR : QuantitativeShortIntervalInput)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0) :=
  bad_upperDensity_tendsto_zero hMR.to_shortIntervalInput smoothUpperInput hε

/-- Erdős problem #1201 as stated in the paper: for every `ε > 0` and `η > 0`, there exists `k`
such that the lower density of the good set of `k` consecutive integers is at least `1 - η`,
conditional on `hMR` only. -/
theorem erdos_problem_1201
    (hMR : QuantitativeShortIntervalInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k) :=
  erdos1201 hMR.to_shortIntervalInput smoothUpperInput hε hη

end Erdos1201
