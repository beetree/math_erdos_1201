module

public import Mathlib

@[expose] public section

/-!
# Exact definitions for friable-integer asymptotic estimate

This file fixes the literal finite combinatorial object and the exact
asymptotic target used by the target.  A `Finset` represents the distinct
factors: after sorting it, its elements are precisely a strictly increasing
list `a₁ < ... < aₖ`.

The quotient `M! / (n!)²` is deliberately valued in `ℚ`.  It must not be
defined with `Nat.div`: before admissibility has been proved, `(n!)²` need
not divide `M!`.
-/

open Filter Topology
open scoped BigOperators

namespace FriableIntegers

noncomputable section

/-- The literal integer interval `(n, M]` from the target. -/
def factorInterval (n M : ℕ) : Finset ℕ :=
  Finset.Ioc n M

/-- A factorization of `n!` into distinct integers in `(n, M]`. -/
def IsAdmissibleEndpoint (n M : ℕ) : Prop :=
  ∃ factors : Finset ℕ,
    factors ⊆ factorInterval n M ∧ factors.prod id = n.factorial

/-- For `n ≥ 3`, the singleton factorization `{n!}` supplies an endpoint. -/
theorem exists_admissibleEndpoint {n : ℕ} (hn : 3 ≤ n) :
    ∃ M, IsAdmissibleEndpoint n M := by
  refine ⟨n.factorial, {n.factorial}, ?_, by simp⟩
  intro a ha
  have ha' : a = n.factorial := by simpa using ha
  subst a
  simp [factorInterval, Nat.lt_factorial_self hn]

/-- The Erdős--Guy--Selfridge extremal function.  For `n ≥ 3` this is the
least possible upper endpoint, hence the least possible largest factor.
The value outside the target's domain is set to zero only to make the
function total. -/
def f (n : ℕ) : ℕ :=
  by
    classical
    exact if hn : 3 ≤ n then Nat.find (exists_admissibleEndpoint hn) else 0

/-- The exact rational constant in the target. -/
def C0 : ℝ :=
  (4029639598 : ℝ) / 25970038185

/-- The natural second-order scale `n / log n`. -/
def secondOrderScale (n : ℕ) : ℝ :=
  (n : ℝ) / Real.log (n : ℝ)

/-- The error in the target's asserted expansion. -/
def mainError (n : ℕ) : ℝ :=
  (f n : ℝ) -
    (2 * (n : ℝ) + C0 * secondOrderScale n)

/-- Literal small-`o` formulation of the main asymptotic formula. -/
def MainAsymptotic : Prop :=
  (mainError =o[atTop] secondOrderScale)

/-- Equivalent normalized-limit expression displayed in the target. -/
def MainNormalizedLimit : Prop :=
  Tendsto
    (fun n : ℕ =>
      (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) / (n : ℝ))
    atTop (nhds C0)

theorem f_spec {n : ℕ} (hn : 3 ≤ n) :
    IsAdmissibleEndpoint n (f n) := by
  classical
  rw [f, dite_eq_left hn]
  exact Nat.find_spec (exists_admissibleEndpoint hn)

theorem f_le_of_admissible {n M : ℕ} (hn : 3 ≤ n)
    (hM : IsAdmissibleEndpoint n M) :
    f n ≤ M := by
  classical
  rw [f, dite_eq_left hn]
  exact Nat.find_min' (exists_admissibleEndpoint hn) hM

theorem admissible_mono {n M M' : ℕ} (hM : M ≤ M')
    (h : IsAdmissibleEndpoint n M) :
    IsAdmissibleEndpoint n M' := by
  obtain ⟨s, hs, hprod⟩ := h
  refine ⟨s, ?_, hprod⟩
  intro a ha
  have hai := Finset.mem_Ioc.mp (hs ha)
  exact Finset.mem_Ioc.mpr ⟨hai.1, hai.2.trans hM⟩


end

end FriableIntegers
