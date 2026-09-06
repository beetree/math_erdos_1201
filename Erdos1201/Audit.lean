import Erdos1201.Main
import Erdos1201.MR

/-!
# Axiom audit for Erdős Problem #1201

The original paper and proof for Erdős Problem #1201 are by Przemek Chojecki together with ChatGPT 5.5.
This repository formalizes their deduction in Lean 4.

The auxiliary lemmas in `Erdos1201.MR` are adapted from the user-supplied incomplete
expert Matomäki–Radziwiłł formalization (arXiv:1501.04585v4).
These lemmas DO NOT prove `QuantitativeShortIntervalInput`.

This file audits the single final conditional theorem (`Erdos1201.erdos_problem_1201`) to
verify that it depends strictly on standard Lean core axioms (`propext`, `Classical.choice`,
`Quot.sound`) and introduces no `sorry`, `admit`, or custom axioms.
Auxiliary lemmas and modules are compiled and verified as dependencies within the build,
but are not individually axiom-audited by this single check.
-/

-- Final conditional theorem
#print axioms Erdos1201.erdos_problem_1201
