module

public import Erdos1201.Vendor.NumberTheory.HalberstamRichertMeanValue.EulerProductMajorant
public import Erdos1201.Vendor.NumberTheory.HalberstamRichertMeanValue.PrimePowerLogConvolution
public import Erdos1201.Vendor.NumberTheory.HalberstamRichertMeanValue.PrimePowerLogMassLinearBound

@[expose] public section

/-!
A fully explicit, unconditional finite Halberstam--Richert mean-value bound.
This file assembles three independently checked ingredients:

* the exact logarithmic prime-power convolution;
* the linear bound for the prime-power logarithmic mass;
* partial summation and the finite Euler-product majorant.

The first theorem uses the shifted prime-power indexing
`h (p^(j+1)) ≤ lambda1 * lambda2^j`.  The second restates the result in the
source-style indexing `h (p^nu) ≤ A * B^nu`.
-/

open scoped BigOperators
open Finset

namespace ExplicitMeanValueBound

set_option linter.dupNamespace false

/-- An explicit Halberstam--Richert mean-value theorem, with the prime-power
hypothesis indexed from the first nontrivial power. -/
theorem halberstam_richert_explicit
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ,
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j)
    (N : ℕ) (hN : 2 ≤ N) :
    HalberstamRichertMeanValue.partialSum h N ≤
      (HalberstamRichertMeanValue.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply HalberstamRichertMeanValue.halberstam_richert_of_mass_convolution
      h h0 h1 hmul hnonneg
      (W := PrimePowerLogConvolution.primePowerMass h)
      (K := HalberstamRichertMeanValue.explicitMassConstant lambda1 lambda2)
      (N := N)
  · intro p hp
    exact (HalberstamRichertMeanValue.prime_power_local_mass h p lambda1 lambda2 hp
      hnonneg h1 hlambda1 hlambda2 hlambda2_lt (hpow p hp)).1
  · exact HalberstamRichertMeanValue.explicitMassConstant_nonneg hlambda1 hlambda2
  · exact hN
  · simpa [HalberstamRichertMeanValue.logPartialSum,
        PrimePowerLogConvolution.logPartialSum] using
      (PrimePowerLogConvolution.logPartialSum_le_primePowerMass_convolution
        h hnonneg hmul N)
  · intro Q
    simpa [HalberstamRichertMeanValue.explicitMassConstant,
        PrimePowerLogConvolution.primePowerMass,
        PrimePowerLogMassLinearBound.primePowerMass,
        PrimePowerLogMassLinearBound.massConstant] using
      (PrimePowerLogMassLinearBound.primePowerMass_le_linear h lambda1 lambda2
        hlambda1 hlambda2 hlambda2_lt (fun p j hp => hpow p hp j) Q)

/-- The same theorem with the prime-power hypothesis in the source-paper
indexing `h (p^nu) ≤ A * B^nu`. -/
theorem halberstam_richert_explicit_source_indexing
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (A B : ℝ)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hB_lt : B < 2)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ nu : ℕ,
      h (p ^ nu) ≤ A * B ^ nu)
    (N : ℕ) (hN : 2 ≤ N) :
    HalberstamRichertMeanValue.partialSum h N ≤
      (HalberstamRichertMeanValue.explicitMassConstant (A * B) B + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply halberstam_richert_explicit h h0 h1 hmul hnonneg (A * B) B
      (mul_nonneg hA hB) hB hB_lt _ N hN
  intro p hp j
  calc
    h (p ^ (j + 1)) ≤ A * B ^ (j + 1) := hpow p hp (j + 1)
    _ = (A * B) * B ^ j := by rw [pow_succ]; ring

end ExplicitMeanValueBound
