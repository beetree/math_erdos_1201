/-
Source repository and pin: https://github.com/ericlisg/erdos731 @
cb1b58c88bf639bb87664dd96ffc327c305e160e.
Pinned source: RequestProject/Erdos731/StripLargeSieveMult.lean.
Formal-proof author: Aristotle, Harmonic's automated theorem prover.
Informal attribution: Erdős, Graham, Ruzsa, and Straus, per
erdosproblems.com/731. License: Apache-2.0.

Local changes ledger:
- None of this file's four declarations (`sq_sum_transpose_le`,
  `largeSieve_gallagher'`, `largeSieve_primal'`, `largeSieve_mult`) mentions
  any problem-specific object; the whole file is generic finite additive
  large-sieve machinery over an arbitrary finite frequency index, so it
  moves to the corpus intact under an honest name.
- Source `import RequestProject.Erdos731.LargeSieveMV` -> DROPPED (unused;
  `largeSieve_MV`/`additiveLargeSieve_MV` is never referenced by this file's
  own declarations, confirmed by inspection).
- Source `nid`/`e`/`largeSieve_gallagher` -> the already-landed corpus
  `AdditiveCharacterGeometricSums.nearestIntegerDistance`/`additiveCharacter`
  and `GallagherAdditiveLargeSieveWindow.finite_additiveLargeSieve_window`.
- `largeSieve_gallagher'` -> `finite_additiveLargeSieve_index` (the source
  name describes it as "the log-free dual additive large sieve, general
  finite frequency index"; renamed to avoid the bare `'` and the
  problem-local `largeSieve_gallagher` root it specializes).
- `largeSieve_primal'` -> `additiveLargeSieve_primal_index`;
  `largeSieve_mult` -> `additiveLargeSieve_multiplicity`. Same reason.
- Proofs ported verbatim modulo the renames above; no mathematical change.
  Exception: `sq_sum_transpose_le`'s closing `grind +suggestions` (closing
  `C * S = C * ∑ i, ‖(starRingEnd ℂ) (v i)‖ ^ 2`) did not close at the
  pinned toolchain; replaced by the equivalent explicit `congr 1;
  exact Finset.sum_congr rfl fun i _ => by rw [Complex.norm_conj]` —
  mechanical elaboration repair only, same conclusion.
-/
module

public import Mathlib.Tactic.Positivity
public import Erdos1201.Vendor.Analysis.GallagherAdditiveLargeSievePrimal

/-!
# The local-multiplicity additive large sieve

This module completes the multiplicity form of the finite additive large
sieve consumed by the packet-energy machinery: the primal additive
large-sieve bound
`GallagherAdditiveLargeSievePrimal.finite_additiveLargeSievePrimal`
(itself derived from the log-free window large sieve
`GallagherAdditiveLargeSieveWindow.finite_additiveLargeSieve_window` via the
`ℓ²`-operator-norm duality `AdditiveLargeSieveDuality.sq_sum_transpose_le`),
applied to each class of a coloring, combines via Cauchy-Schwarz across
classes into

* `additiveLargeSieve_multiplicity` — the **local-multiplicity** large sieve:
  if the frequencies split into `Rn` classes, each `δ`-spaced, then
  `∑_{M ≤ n < M+N} |∑_i c_i e(n θ_i)|² ≤ Rn (δ⁻¹ + 2π N) ∑_i |c_i|²`.
-/

@[expose] public section

namespace AdditiveLargeSieveMultiplicity

open scoped BigOperators
open Real Complex
open AdditiveCharacterGeometricSums

/-- **The local-multiplicity additive large sieve.** If the frequencies
`θ : ι → ℝ` split, via a coloring `col : ι → Fin Rn`, into `Rn` classes that
are each `δ`-spaced, then
`∑_{M ≤ n < M+N} |∑_i c_i e(n θ_i)|² ≤ Rn (δ⁻¹ + 2π N) ∑_i |c_i|²`. -/
theorem additiveLargeSieve_multiplicity (M N : ℕ) {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (cc : ι → ℂ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (Rn : ℕ) (col : ι → Fin Rn)
    (hcol : ∀ (i j : ι), col i = col j → i ≠ j → δ ≤ nearestIntegerDistance (θ i - θ j)) :
    (∑ n ∈ Finset.Ico M (M + N), ‖∑ i, cc i * additiveCharacter (n * θ i)‖ ^ 2)
      ≤ (Rn : ℝ) * (δ⁻¹ + 2 * Real.pi * N) * ∑ i, ‖cc i‖ ^ 2 := by
  have h_step_C : ∑ n ∈ Finset.Ico M (M + N), ‖∑ i, cc i * additiveCharacter (n * θ i)‖ ^ 2
      ≤ Rn * ∑ r : Fin Rn, ∑ n ∈ Finset.Ico M (M + N),
        ‖∑ i ∈ Finset.filter (fun i => col i = r) Finset.univ,
          cc i * additiveCharacter (n * θ i)‖ ^ 2 := by
    have h_stepB : ∀ n : ℕ, ‖∑ i, cc i * additiveCharacter (n * θ i)‖ ^ 2
        ≤ Rn * ∑ r : Fin Rn, ‖∑ i ∈ Finset.filter (fun i => col i = r) Finset.univ,
          cc i * additiveCharacter (n * θ i)‖ ^ 2 := by
      intro n
      have h_sum : ∑ i, cc i * additiveCharacter (n * θ i) =
          ∑ r : Fin Rn, ∑ i ∈ Finset.filter (fun i => col i = r) Finset.univ,
            cc i * additiveCharacter (n * θ i) := by
        rw [Finset.sum_fiberwise]
      have h_cauchy_schwarz : ∀ (x : Fin Rn → ℂ), ‖∑ r, x r‖ ^ 2 ≤ Rn * ∑ r, ‖x r‖ ^ 2 := by
        intro x
        have h_cauchy_schwarz : ‖∑ r, x r‖ ^ 2 ≤ (∑ r : Fin Rn, ‖x r‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _
        have := Finset.univ.sum_le_sum fun i _ => pow_two_nonneg (‖x i‖ - (∑ j, ‖x j‖) / Rn)
        by_cases hRn : Rn = 0 <;> simp_all +decide [sub_sq, Finset.sum_add_distrib, Finset.mul_sum _ _ _]
        · aesop
        · simp_all +decide [← Finset.mul_sum _ _ _, ← Finset.sum_mul, mul_assoc, sq]
          nlinarith [mul_div_cancel₀ (∑ i, ‖x i‖) (by positivity : (Rn : ℝ) ≠ 0)]
      exact h_sum.symm ▸ h_cauchy_schwarz _
    rw [Finset.sum_comm]
    simpa only [Finset.mul_sum _ _ _] using Finset.sum_le_sum fun n hn => h_stepB n
  have h_step_D : ∀ r : Fin Rn, ∑ n ∈ Finset.Ico M (M + N),
      ‖∑ i ∈ Finset.filter (fun i => col i = r) Finset.univ,
        cc i * additiveCharacter (n * θ i)‖ ^ 2
      ≤ (δ⁻¹ + 2 * Real.pi * N) * ∑ i ∈ Finset.filter (fun i => col i = r) Finset.univ, ‖cc i‖ ^ 2 := by
    intro r
    set S := Finset.filter (fun i => col i = r) Finset.univ with hS_def
    have hS_card : S.card ≤ Fintype.card ι := Finset.card_le_univ _
    have hS_spaced : ∀ i j : S, i ≠ j → δ ≤ nearestIntegerDistance (θ i - θ j) := by grind
    have hS_primal : ∑ n ∈ Finset.Ico M (M + N),
        ‖∑ i : S, cc i * additiveCharacter (n * θ i)‖ ^ 2
        ≤ (δ⁻¹ + 2 * Real.pi * N) * ∑ i : S, ‖cc i‖ ^ 2 := by
      convert GallagherAdditiveLargeSievePrimal.finite_additiveLargeSievePrimal M N
        (fun i : S => θ i) (fun i : S => cc i) δ hδ hδ1 hS_spaced using 1
    exact (by
    convert hS_primal using 1
    · exact Finset.sum_congr rfl fun _ _ => by rw [← Finset.sum_coe_sort]
    · rw [← Finset.sum_coe_sort])
  refine le_trans h_step_C ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (le_trans (Finset.sum_le_sum fun r _ => h_step_D r) ?_)
    (Nat.cast_nonneg _)
  rw [← Finset.mul_sum _ _ _, Finset.sum_fiberwise]

end AdditiveLargeSieveMultiplicity
