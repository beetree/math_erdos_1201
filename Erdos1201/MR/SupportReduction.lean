import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Erdos1201.MR.Exceptional

/-!
# Finite Support Removal and Endpoint Discrepancy

The original paper and proof for Erdős Problem #1201 are by Przemek Chojecki together with
ChatGPT 5.5 (`erdos1201.pdf`).

These Matomäki–Radziwiłł auxiliary lemmas formalize finite reductions.

Boundary note: These lemmas are elementary finite combinatorial and triangle-inequality
reductions relating full interval discrepancies to restricted discrepancies, missing mass,
and precise endpoint discrepancy terms. They DO NOT prove `QuantitativeShortIntervalInput`
or the Matomäki–Radziwiłł theorem; the underlying sifted-set bounds and decay rates remain
external analytic inputs.
-/

open scoped BigOperators

namespace Erdos1201.MR

noncomputable def supportedPart (S : Set ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ S then f n else 0

noncomputable def supportIndicator (S : Set ℕ) (n : ℕ) : ℝ :=
  supportedPart S (fun _ => 1) n

noncomputable def missingIndicator (S : Set ℕ) (n : ℕ) : ℝ := by
  classical
  exact if n ∈ S then 0 else 1

noncomputable def finiteAverage (I : Finset ℕ) (f : ℕ → ℝ) (d : ℝ) : ℝ :=
  (∑ n ∈ I, f n) / d

/-- An elementary absolute-value inequality for finite real sums. -/
theorem abs_finite_sum_le {α : Type*} (T : Finset α) (u : α → ℝ) :
    |∑ x ∈ T, u x| ≤ ∑ x ∈ T, |u x| := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      linarith [abs_add_le (u a) (∑ x ∈ T, u x)]

/-- Removing a support set changes an average by at most its missing mass. -/
theorem average_restriction_error (I : Finset ℕ) (S : Set ℕ) (f : ℕ → ℝ)
    (d : ℝ) (hd : 0 < d) (hf : ∀ n ∈ I, |f n| ≤ 1) :
    |finiteAverage I f d - finiteAverage I (supportedPart S f) d| ≤
      finiteAverage I (missingIndicator S) d := by
  classical
  have hsum : |(∑ n ∈ I, f n) - (∑ n ∈ I, supportedPart S f n)| ≤
      ∑ n ∈ I, missingIndicator S n := by
    calc
      |(∑ n ∈ I, f n) - (∑ n ∈ I, supportedPart S f n)| =
          |∑ n ∈ I, (f n - supportedPart S f n)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ n ∈ I, |f n - supportedPart S f n| := abs_finite_sum_le _ _
      _ ≤ ∑ n ∈ I, missingIndicator S n := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hmem : n ∈ S
        · simp [supportedPart, missingIndicator, hmem]
        · simpa [supportedPart, missingIndicator, hmem] using hf n hn
  unfold finiteAverage
  rw [← sub_div, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hsum hd.le

/-- Exact complement identity. In particular, no unrecorded `O(1/h)` endpoint
correction is used: the total mass is `I.card / d`. -/
theorem missingAverage_eq (I : Finset ℕ) (S : Set ℕ) (d : ℝ) :
    finiteAverage I (missingIndicator S) d =
      (I.card : ℝ) / d - finiteAverage I (supportIndicator S) d := by
  classical
  unfold finiteAverage
  rw [← sub_div]
  congr 1
  calc
    (∑ n ∈ I, missingIndicator S n) = ∑ n ∈ I, (1 - supportIndicator S n) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hmem : n ∈ S <;>
        simp [missingIndicator, supportIndicator, supportedPart, hmem]
    _ = (I.card : ℝ) - ∑ n ∈ I, supportIndicator S n := by
      rw [Finset.sum_sub_distrib]
      simp

/-- Transport missing mass from the long interval to the short one. -/
theorem missingAverage_le (I J : Finset ℕ) (S : Set ℕ) (h X : ℝ) :
    finiteAverage I (missingIndicator S) h ≤
      finiteAverage J (missingIndicator S) X +
      |(I.card : ℝ) / h - (J.card : ℝ) / X| +
      |finiteAverage I (supportIndicator S) h -
        finiteAverage J (supportIndicator S) X| := by
  have hi := missingAverage_eq I S h
  have hj := missingAverage_eq J S X
  have hmass := le_abs_self ((I.card : ℝ) / h - (J.card : ℝ) / X)
  have hind := le_abs_self (-(finiteAverage I (supportIndicator S) h -
    finiteAverage J (supportIndicator S) X))
  rw [abs_neg] at hind
  linarith

/-- The elementary full-versus-restricted discrepancy bound with exact endpoint
mass discrepancy. It applies to arbitrary finite sets and positive denominators. -/
theorem average_discrepancy_bound (I J : Finset ℕ) (S : Set ℕ) (f : ℕ → ℝ)
    (h X : ℝ) (hh : 0 < h) (hX : 0 < X)
    (hI : ∀ n ∈ I, |f n| ≤ 1) (hJ : ∀ n ∈ J, |f n| ≤ 1) :
    |finiteAverage I f h - finiteAverage J f X| ≤
      |finiteAverage I (supportedPart S f) h -
        finiteAverage J (supportedPart S f) X| +
      |finiteAverage I (supportIndicator S) h -
        finiteAverage J (supportIndicator S) X| +
      2 * finiteAverage J (missingIndicator S) X +
      |(I.card : ℝ) / h - (J.card : ℝ) / X| := by
  have heI := average_restriction_error I S f h hh hI
  have heJ := average_restriction_error J S f X hX hJ
  have heJ' : |finiteAverage J (supportedPart S f) X - finiteAverage J f X| ≤
      finiteAverage J (missingIndicator S) X := by
    rw [abs_sub_comm]
    exact heJ
  have htriangle₁ := abs_sub_le (finiteAverage I f h)
    (finiteAverage I (supportedPart S f) h) (finiteAverage J f X)
  have htriangle₂ := abs_sub_le (finiteAverage I (supportedPart S f) h)
    (finiteAverage J (supportedPart S f) X) (finiteAverage J f X)
  have hmissing := missingAverage_le I J S h X
  linarith

noncomputable def discrepancy {α : Type*} (I : α → Finset ℕ) (J : Finset ℕ)
    (f : ℕ → ℝ) (h X : ℝ) (x : α) : ℝ :=
  finiteAverage (I x) f h - finiteAverage J f X

/-- A finite quantitative reduction: two restricted second moments, a long
missing-mass bound, and an endpoint bound control the full exceptional set.

The right side retains the actual energy sums. No analytic bound for them is
assumed to exist or claimed to have been proved here. -/
theorem exceptional_card_le_restricted_energies {α : Type*} [DecidableEq α] (T : Finset α)
    (I : α → Finset ℕ) (J : Finset ℕ) (S : Set ℕ) (f : ℕ → ℝ)
    (h X t ρ e : ℝ) (hh : 0 < h) (hX : 0 < X) (ht : 0 < t)
    (hI : ∀ x ∈ T, ∀ n ∈ I x, |f n| ≤ 1)
    (hJ : ∀ n ∈ J, |f n| ≤ 1)
    (hmissing : finiteAverage J (missingIndicator S) X ≤ ρ)
    (hend : ∀ x ∈ T, |((I x).card : ℝ) / h - (J.card : ℝ) / X| ≤ e) :
    ((exceptional T (discrepancy I J f h X) (2 * t + 2 * ρ + e)).card : ℝ) ≤
      (energy T (discrepancy I J (supportedPart S f) h X) +
        energy T (discrepancy I J (supportIndicator S) h X)) / t ^ 2 := by
  have hdom : ∀ x ∈ T, |discrepancy I J f h X x| ≤
      |discrepancy I J (supportedPart S f) h X x| +
      |discrepancy I J (supportIndicator S) h X x| + (2 * ρ + e) := by
    intro x hx
    have hb := average_discrepancy_bound (I x) J S f h X hh hX (hI x hx) hJ
    have he := hend x hx
    dsimp only [discrepancy]
    linarith
  simpa only [add_assoc] using
    exceptional_card_le_two_energies T (discrepancy I J f h X)
      (discrepancy I J (supportedPart S f) h X)
      (discrepancy I J (supportIndicator S) h X) t (2 * ρ + e) ht hdom

end Erdos1201.MR
