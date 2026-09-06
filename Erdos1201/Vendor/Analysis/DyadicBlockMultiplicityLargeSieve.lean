/-
Source repository and pin: https://github.com/ericlisg/erdos731 @
cb1b58c88bf639bb87664dd96ffc327c305e160e.
Pinned source: RequestProject/Erdos731/StripBlockLargeSieve.lean.
Formal-proof author: Aristotle, Harmonic's automated theorem prover.
Informal attribution: Erdős, Graham, Ruzsa, and Straus, per
erdosproblems.com/731. License: Apache-2.0.

Local changes ledger:
- The file's sole declaration (`largeSieve_block_mult`) mentions no
  problem-specific object; it moves to the corpus intact under an honest
  name.
- Source `e`/`largeSieve_mult_arc` -> the already-landed corpus
  `AdditiveCharacterGeometricSums.additiveCharacter`/
  `AdditiveLargeSieveArcColoring.additiveLargeSieve_arc_multiplicity`.
- `largeSieve_block_mult` -> `dyadicBlock_multiplicity_largeSieve` (honest
  name matching the corpus's `DyadicBlock*` module family).
- Proof body (a `convert ... using 1` chain closed by `ring_nf; field_simp`)
  did not close at the pinned toolchain (leftover `instLE = instPreorder.toLE`
  artifact from `convert` on a `≤`-goal, plus an unclosed algebraic
  identity); replaced by an explicit `rw`/`calc` derivation of the same
  chain of inequalities (`h_arc` instantiated directly rather than via
  `convert`, then scaled by `X⁻¹` and simplified with `field_simp`) —
  mechanical elaboration repair only, same statement and conclusion.
-/
module

public import Mathlib.Tactic.FieldSimp
public import Erdos1201.Vendor.Analysis.AdditiveLargeSieveArcColoring

/-!
# The dyadic-block multiplicity additive large sieve

Specializes the arc-multiplicity large sieve
`AdditiveLargeSieveArcColoring.additiveLargeSieve_arc_multiplicity` to the
dyadic block `[X, 2X)` at arc length `δ = X⁻¹`, giving the block-average
form:

  `(1/X) ∑_{X ≤ n < 2X} |∑_i c_i e(n θ_i)|² ≤ 𝓡 (1 + 2π) ∑_i |c_i|²`,

whenever the frequencies lie in a common window of width `< 1/2` and every
`X⁻¹`-arc contains at most `𝓡` of them. (Taking `δ = X⁻¹` turns the
`δ⁻¹ + 2πN` constant, with `N = X`, into `X(1 + 2π)`, and the `1/X`
normalisation cancels the block length.)
-/

@[expose] public section

namespace DyadicBlockMultiplicityLargeSieve

open scoped BigOperators
open Real Complex
open AdditiveCharacterGeometricSums
open AdditiveLargeSieveArcColoring

/-- If all frequencies lie in a common window `[c, c+w)` of width `w < 1/2`
and every `X⁻¹`-arc contains at most `R` of them, then the block average of
the exponential-sum energy is `≤ R (1 + 2π) ∑_i |c_i|²`. -/
theorem dyadicBlock_multiplicity_largeSieve (X : ℕ) (hX : 1 ≤ X) {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (cc : ι → ℂ) (R : ℕ) (hR : 1 ≤ R)
    (c w : ℝ) (hw : w < 1 / 2) (hmem : ∀ i, c ≤ θ i ∧ θ i < c + w)
    (harc : ∀ a : ℝ,
      (Finset.univ.filter (fun i => a ≤ θ i ∧ θ i < a + (1 / (X : ℝ)))).card ≤ R) :
    (1 / (X : ℝ)) * ∑ n ∈ Finset.Ico X (2 * X), ‖∑ i, cc i * additiveCharacter (n * θ i)‖ ^ 2
      ≤ (R : ℝ) * (1 + 2 * Real.pi) * ∑ i, ‖cc i‖ ^ 2 := by
  have h_arc : (∑ n ∈ Finset.Ico X (X + X), ‖∑ i, cc i * additiveCharacter (n * θ i)‖ ^ 2)
      ≤ (R : ℝ) * ((1 / (X : ℝ))⁻¹ + 2 * Real.pi * X) * ∑ i, ‖cc i‖ ^ 2 :=
    additiveLargeSieve_arc_multiplicity X X θ cc (1 / (X : ℝ)) (by positivity)
      (by rw [div_le_iff₀] <;> norm_cast; linarith) R hR c w hw hmem harc
  have hXR : (X : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show X + X = 2 * X from (two_mul X).symm, one_div, inv_inv] at h_arc
  have h_scaled := mul_le_mul_of_nonneg_left h_arc (by positivity : (0 : ℝ) ≤ (X : ℝ)⁻¹)
  rw [one_div]
  calc (X : ℝ)⁻¹ * ∑ n ∈ Finset.Ico X (2 * X), ‖∑ i, cc i * additiveCharacter (n * θ i)‖ ^ 2
      ≤ (X : ℝ)⁻¹ * ((R : ℝ) * ((X : ℝ) + 2 * Real.pi * X) * ∑ i, ‖cc i‖ ^ 2) := h_scaled
    _ = (R : ℝ) * (1 + 2 * Real.pi) * ∑ i, ‖cc i‖ ^ 2 := by field_simp

end DyadicBlockMultiplicityLargeSieve
