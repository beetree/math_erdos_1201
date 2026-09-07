import Erdos1201.Main
import Erdos1201.MR
import Erdos1201.Final

/-!
# Axiom audit for Erdős Problem #1201

The original paper and proof for Erdős Problem #1201 are by Przemek Chojecki together with ChatGPT 5.5.
This repository formalizes their deduction in Lean 4.

The modules under `Erdos1201.MR` formalize the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) for the smooth indicator and prove `SmoothShortIntervalInput`
(`Erdos1201.MR.smoothShortIntervalInput_holds`).

This file audits the single final unconditional theorem
(`Erdos1201.erdos_problem_1201_unconditional`) to verify that it depends strictly on standard
Lean core axioms (`propext`, `Classical.choice`, `Quot.sound`) and introduces no `sorry`,
`admit`, or custom axioms. The form with an explicit hypothesis, `Erdos1201.erdos_problem_1201`, is a corollary of
the same deduction.
Auxiliary lemmas and modules are compiled and verified as dependencies within the build,
but are not individually axiom-audited by this single check.
-/

-- Final unconditional theorem
#print axioms Erdos1201.erdos_problem_1201_unconditional
