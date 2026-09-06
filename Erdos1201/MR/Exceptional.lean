import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Finite Chebyshev Estimates for Exceptional Sets

The original paper and proof for Erdős Problem #1201 are by Przemek Chojecki together with
ChatGPT 5.5 (`erdos1201.pdf`).

These auxiliary lemmas are adapted from the user-supplied incomplete expert
Matomäki–Radziwiłł formalization (specifically `MR/Exceptional.lean`).

Boundary note: These lemmas are elementary finite counting and Chebyshev estimates.
They DO NOT prove `QuantitativeShortIntervalInput` or the Matomäki–Radziwiłł theorem;
they merely provide finite $L^2$-to-cardinality reduction infrastructure.
-/

open scoped BigOperators

namespace Erdos1201.MR

noncomputable def exceptional {α : Type*} (T : Finset α) (g : α → ℝ) (t : ℝ) :
    Finset α := by
  classical
  exact T.filter (fun x => t < |g x|)

noncomputable def energy {α : Type*} (T : Finset α) (g : α → ℝ) : ℝ :=
  ∑ x ∈ T, (g x) ^ 2

@[simp] theorem mem_exceptional {α : Type*} {T : Finset α} {g : α → ℝ}
    {t : ℝ} {x : α} :
    x ∈ exceptional T g t ↔ x ∈ T ∧ t < |g x| := by
  classical
  simp [exceptional]

theorem energy_nonneg {α : Type*} (T : Finset α) (g : α → ℝ) :
    0 ≤ energy T g := by
  exact Finset.sum_nonneg (fun x hx => sq_nonneg (g x))

/-- Finite Chebyshev inequality with an explicit second moment. -/
theorem exceptional_card_le_energy {α : Type*} (T : Finset α) (g : α → ℝ)
    (t : ℝ) (ht : 0 < t) :
    ((exceptional T g t).card : ℝ) ≤ energy T g / t ^ 2 := by
  classical
  have hpoint : ∀ x ∈ exceptional T g t, t ^ 2 ≤ (g x) ^ 2 := by
    intro x hx
    have hlarge : t < |g x| := (mem_exceptional.mp hx).2
    have hprod : 0 ≤ (|g x| - t) * (|g x| + t) :=
      mul_nonneg (sub_nonneg.mpr hlarge.le) (add_nonneg (abs_nonneg _) ht.le)
    nlinarith [sq_abs (g x)]
  have hsub : exceptional T g t ⊆ T := by
    intro x hx
    exact (mem_exceptional.mp hx).1
  have htotal : ((exceptional T g t).card : ℝ) * t ^ 2 ≤ energy T g := by
    calc
      ((exceptional T g t).card : ℝ) * t ^ 2 =
          ∑ _x ∈ exceptional T g t, t ^ 2 := by simp [nsmul_eq_mul]
      _ ≤ ∑ x ∈ exceptional T g t, (g x) ^ 2 := Finset.sum_le_sum hpoint
      _ ≤ ∑ x ∈ T, (g x) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx hnot => sq_nonneg (g x))
  exact (le_div_iff₀ (pow_pos ht 2)).mpr htotal

/-- A supplied energy upper bound yields an explicit cardinality upper bound. -/
theorem exceptional_card_le_of_energy_le {α : Type*} (T : Finset α) (g : α → ℝ)
    (t V : ℝ) (ht : 0 < t) (hV : energy T g ≤ V) :
    ((exceptional T g t).card : ℝ) ≤ V / t ^ 2 := by
  exact (exceptional_card_le_energy T g t ht).trans
    (div_le_div_of_nonneg_right hV (sq_nonneg t))

/-- If a deviation is dominated by two fluctuating terms plus a deterministic
error, its exceptional set is contained in the union of the other two. -/
theorem exceptional_subset_union {α : Type*} [DecidableEq α] (T : Finset α)
    (d g r : α → ℝ) (t b : ℝ)
    (hdom : ∀ x ∈ T, |d x| ≤ |g x| + |r x| + b) :
    exceptional T d (2 * t + b) ⊆ exceptional T g t ∪ exceptional T r t := by
  classical
  intro x hx
  have hxT : x ∈ T := (mem_exceptional.mp hx).1
  have hbad : 2 * t + b < |d x| := (mem_exceptional.mp hx).2
  by_cases hg : t < |g x|
  · exact Finset.mem_union.mpr (Or.inl (mem_exceptional.mpr ⟨hxT, hg⟩))
  · by_cases hr : t < |r x|
    · exact Finset.mem_union.mpr (Or.inr (mem_exceptional.mpr ⟨hxT, hr⟩))
    · have hg' : |g x| ≤ t := le_of_not_gt hg
      have hr' : |r x| ≤ t := le_of_not_gt hr
      have hd := hdom x hxT
      exfalso
      linarith

/-- Quantitative two-energy reduction, using only finite sums. -/
theorem exceptional_card_le_two_energies {α : Type*} [DecidableEq α] (T : Finset α)
    (d g r : α → ℝ) (t b : ℝ) (ht : 0 < t)
    (hdom : ∀ x ∈ T, |d x| ≤ |g x| + |r x| + b) :
    ((exceptional T d (2 * t + b)).card : ℝ) ≤
      (energy T g + energy T r) / t ^ 2 := by
  classical
  have hnat : (exceptional T d (2 * t + b)).card ≤
      (exceptional T g t).card + (exceptional T r t).card :=
    (Finset.card_le_card (exceptional_subset_union T d g r t b hdom)).trans
      (Finset.card_union_le _ _)
  have hreal : ((exceptional T d (2 * t + b)).card : ℝ) ≤
      ((exceptional T g t).card : ℝ) + ((exceptional T r t).card : ℝ) := by
    exact_mod_cast hnat
  calc
    ((exceptional T d (2 * t + b)).card : ℝ) ≤
        ((exceptional T g t).card : ℝ) + ((exceptional T r t).card : ℝ) := hreal
    _ ≤ energy T g / t ^ 2 + energy T r / t ^ 2 :=
      add_le_add (exceptional_card_le_energy T g t ht)
        (exceptional_card_le_energy T r t ht)
    _ = (energy T g + energy T r) / t ^ 2 := by ring

end Erdos1201.MR
