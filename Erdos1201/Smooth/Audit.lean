import Erdos1201.Smooth.Unconditional

/-!
# Enforced axiom audit for the smooth-side extension

The original Erdős #1201 deduction is by Przemek Chojecki together with
ChatGPT 5.5. These guards fail compilation if the displayed dependencies change.
They check foundational axioms, not the semantic interpretation of the theorem.
The MR hypothesis remains visible in the final wrapper theorem types.
-/

/-- info: 'Erdos1201.smoothMeanGapInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1201.smoothMeanGapInput

/-- info: 'Erdos1201.erdos_problem_1201_of_MR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1201.erdos_problem_1201_of_MR

/-- info: 'Erdos1201.theorem1_of_MR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1201.theorem1_of_MR

/-- info: 'Erdos1201.SmoothRoute.primeReciprocal_power_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1201.SmoothRoute.primeReciprocal_power_lower

/-- info: 'Erdos1201.SmoothRoute.blockMean_le_of_primeBand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Erdos1201.SmoothRoute.blockMean_le_of_primeBand

