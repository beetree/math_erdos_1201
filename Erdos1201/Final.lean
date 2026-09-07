import Erdos1201.Main
import Erdos1201.MR.FinalAssembly

/-!
# Erdős Problem #1201, unconditionally

The original paper and proof for Erdős Problem #1201 are by Przemek Chojecki together with
ChatGPT 5.5. This repository formalizes their deduction in Lean 4.

The deduction takes as input the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) applied to the `X^β`-smooth indicator, stated as
`SmoothShortIntervalInput` in `Erdos1201.MR.Target`. That input is proved in
`Erdos1201.MR.FinalAssembly` (`smoothShortIntervalInput_holds`), so the final theorems
below carry no hypothesis beyond the positivity of the parameters.
-/

open Filter Topology

namespace Erdos1201

/-- Erdős problem #1201 without any analytic hypothesis: for every `ε > 0` and `η > 0` there is
`k` such that the set of integers all of whose `k` consecutive successors have a prime factor
in the window has lower density at least `1 - η`. -/
theorem erdos_problem_1201_unconditional {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k) :=
  erdos_problem_1201_of_smoothShortInterval MR.smoothShortIntervalInput_holds hε hη

/-- Theorem 1 of the paper without any analytic hypothesis: the upper density of the bad set
tends to `0` as the block length grows. -/
theorem theorem1_unconditional {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0) :=
  theorem1_of_smoothShortInterval MR.smoothShortIntervalInput_holds hε

end Erdos1201
