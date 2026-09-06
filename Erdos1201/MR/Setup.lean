import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Arithmetic
import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.MR.Sieve.InclusionExclusion

/-!
# Setup and Definitions for Matomäki–Radziwiłł Reductions

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module fixes definitions and basic properties for the Dirichlet polynomial setup
specialized to the smooth indicator function in the Matomäki–Radziwiłł argument.
-/

namespace Erdos1201.MR

/-- Decidable instance for `HasFactorInEach` so that `siftedSet` is computable. -/
instance (J : ℕ) (R : Fin J → Finset ℕ) (n : ℕ) : Decidable (HasFactorInEach J R n) := by
  unfold HasFactorInEach
  infer_instance

/-- Primes in the closed range [P, Q]. -/
def primeRange (P Q : ℕ) : Finset ℕ := (Finset.Icc P Q).filter Nat.Prime

/-- The sifted set S_X of Section 2: integers in (X, 2X] with a prime factor in every range. -/
def siftedSet (J : ℕ) (R : Fin J → Finset ℕ) (X : ℕ) : Finset ℕ := (Finset.Ioc X (2 * X)).filter (HasFactorInEach J R)

open Classical

/-- The function f_X = indicator of X^β-smooth numbers, as a complex coefficient sequence. -/
noncomputable def fX (β : ℝ) (X : ℕ) (n : ℕ) : ℂ := (smoothIndicator ((X : ℝ) ^ β) n : ℂ)

/-- Coefficients of F(s): f_X restricted to the sifted set. -/
noncomputable def coeffF (β : ℝ) (J : ℕ) (R : Fin J → Finset ℕ) (X : ℕ) (n : ℕ) : ℂ := if n ∈ siftedSet J R X then fX β X n else 0

/-- F(s) = ∑_{X < n ≤ 2X, n ∈ S} f_X(n) n^{-s}. -/
noncomputable def F (β : ℝ) (J : ℕ) (R : Fin J → Finset ℕ) (X : ℕ) (s : ℂ) : ℂ := dirichletPoly (coeffF β J R X) (Finset.Ioc X (2 * X)) s

/-- Short prime range [e^{v/H}, e^{(v+1)/H}] intersected with [P, Q]. -/
noncomputable def shortPrimeRange (P Q : ℕ) (H : ℝ) (v : ℕ) : Finset ℕ := (primeRange P Q).filter (fun p => Real.exp (v / H) ≤ p ∧ (p : ℝ) ≤ Real.exp ((v + 1) / H))

/-- Q_{v,H}(s) = ∑_{p in the short range} f_X(p) p^{-s}. -/
noncomputable def Qpoly (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (s : ℂ) : ℂ := dirichletPoly (fX β X) (shortPrimeRange P Q H v) s

/-- The m-range (X e^{-v/H}, 2 X e^{-v/H}] as natural numbers. -/
noncomputable def cofactorRange (X : ℕ) (H : ℝ) (v : ℕ) : Finset ℕ := (Finset.Ioc 0 ⌊2 * X * Real.exp (-(v / H))⌋₊).filter (fun m => X * Real.exp (-(v / H)) < m)

/-- R_{v,H}(s) = ∑_{m in the cofactor range, m ∈ S'} f_X(m) / (ω(m; P, Q) + 1) · m^{-s}, where S' is given by a predicate. -/
noncomputable def Rpoly (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (S' : ℕ → Prop) [DecidablePred S'] (s : ℂ) : ℂ :=
  dirichletPoly (fun m => if S' m then fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1) else 0) (cofactorRange X H v) s

/-- A prime `p` with `(p : ℝ) ≤ Y` is `Y`-smooth. -/
lemma smooth_prime_of_le {Y : ℝ} {p : ℕ} (hp : p.Prime) (hpY : (p : ℝ) ≤ Y) : Smooth Y p := by
  refine ⟨hp.ne_zero, ?_⟩
  intro q hq hq_dvd
  have hqp : q = p := (Nat.dvd_prime hp).mp hq_dvd |>.resolve_left hq.ne_one
  subst hqp
  exact hpY

/-- A prime `p ≤ X^β` can be removed from `fX β X (p * m)`. -/
theorem fX_mul_of_prime_le (β : ℝ) (X p m : ℕ) (hp : p.Prime) (hm : 0 < m) (hpX : (p : ℝ) ≤ (X : ℝ) ^ β) :
    fX β X (p * m) = fX β X m := by
  have _ := hm
  unfold fX smoothIndicator
  have hsm_p : Smooth ((X : ℝ) ^ β) p := smooth_prime_of_le hp hpX
  rw [smooth_mul_iff, and_iff_right hsm_p]

/-- A prime `p ≤ X^β` evaluates to 1 under `fX β X`. -/
theorem fX_prime_eq_one (β : ℝ) (X p : ℕ) (hp : p.Prime) (hpX : (p : ℝ) ≤ (X : ℝ) ^ β) :
    fX β X p = 1 := by
  unfold fX smoothIndicator
  have hsm : Smooth ((X : ℝ) ^ β) p := smooth_prime_of_le hp hpX
  simp [hsm]

/-- The smooth indicator `fX β X n` is bounded in norm by 1. -/
theorem norm_fX_le_one (β : ℝ) (X n : ℕ) :
    ‖fX β X n‖ ≤ 1 := by
  unfold fX smoothIndicator
  split_ifs
  · simp
  · simp

/-- The sifted coefficient sequence `coeffF` is bounded in norm by 1. -/
theorem norm_coeffF_le_one (β : ℝ) (J : ℕ) (R : Fin J → Finset ℕ) (X n : ℕ) :
    ‖coeffF β J R X n‖ ≤ 1 := by
  unfold coeffF
  split_ifs with hn
  · exact norm_fX_le_one β X n
  · simp

/-- Characterization of membership in `shortPrimeRange P Q H v`. -/
theorem mem_shortPrimeRange (P Q : ℕ) (H : ℝ) (v p : ℕ) :
    p ∈ shortPrimeRange P Q H v ↔ (p.Prime ∧ P ≤ p ∧ p ≤ Q) ∧ Real.exp (v / H) ≤ p ∧ (p : ℝ) ≤ Real.exp ((v + 1) / H) := by
  unfold shortPrimeRange primeRange
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- The short prime range is a subset of the prime range `[P, Q]`. -/
theorem shortPrimeRange_subset (P Q : ℕ) (H : ℝ) (v : ℕ) :
    shortPrimeRange P Q H v ⊆ primeRange P Q := by
  unfold shortPrimeRange
  exact Finset.filter_subset _ _

end Erdos1201.MR
