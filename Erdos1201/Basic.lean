import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# Elementary objects for Erdős problem #1201

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This file is part of a Lean reproduction of that work; see `erdos1201.pdf`.
-/

open Finset Filter
open scoped BigOperators Topology

namespace Erdos1201

open Classical

/-- The paper's largest-prime-factor convention, extended to zero by the value one. -/
def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)

/-- The product has exactly `h` factors; the problem's `k` corresponds to `h = k + 1`. -/
def consecutiveProduct (n h : ℕ) : ℕ := ∏ j ∈ range h, (n + j)

/-- The exceptional set in Theorem 1. Zero is excluded throughout. -/
def badSet (ε : ℝ) (h : ℕ) : Set ℕ :=
  {n | 0 < n ∧ (largestPrimeFactor (consecutiveProduct n h) : ℝ) ≤ (n : ℝ) ^ (1 - ε)}

/-- The good set in the problem statement. -/
def goodSet (ε : ℝ) (k : ℕ) : Set ℕ :=
  {n | 0 < n ∧ (n : ℝ) ^ (1 - ε) < largestPrimeFactor (consecutiveProduct n (k + 1))}

/-- Smoothness with a real cutoff, including the requirement that the number be positive. -/
def Smooth (Y : ℝ) (n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Y

noncomputable def smoothIndicator (Y : ℝ) (n : ℕ) : ℝ :=
  if Smooth Y n then 1 else 0

/-- Complete multiplicativity is more than the short-interval theorem requires. -/
def CompletelyMultiplicative (f : ℕ → ℝ) : Prop :=
  f 1 = 1 ∧ ∀ m n, f (m * n) = f m * f n

noncomputable def shortMean (f : ℕ → ℝ) (h n : ℕ) : ℝ :=
  (∑ j ∈ range h, f (n + j)) / h

noncomputable def blockMean (f : ℕ → ℝ) (X : ℕ) : ℝ :=
  (∑ n ∈ Ico X (2 * X), f n) / X

@[simp] theorem smooth_one (Y : ℝ) : Smooth Y 1 := by
  refine ⟨by omega, ?_⟩
  intro p hp hd
  exact False.elim (hp.not_dvd_one hd)

@[simp] theorem smooth_mul_iff (Y : ℝ) (m n : ℕ) :
    Smooth Y (m * n) ↔ Smooth Y m ∧ Smooth Y n := by
  constructor
  · rintro ⟨hmn, h⟩
    have hz := mul_ne_zero_iff.mp hmn
    exact ⟨⟨hz.1, fun p hp hd => h p hp (dvd_mul_of_dvd_left hd n)⟩,
      ⟨hz.2, fun p hp hd => h p hp (dvd_mul_of_dvd_right hd m)⟩⟩
  · rintro ⟨⟨hm, hmp⟩, ⟨hn, hnp⟩⟩
    refine ⟨mul_ne_zero hm hn, ?_⟩
    intro p hp hd
    exact (hp.dvd_mul.mp hd).elim (hmp p hp) (hnp p hp)

theorem smoothIndicator_completelyMultiplicative (Y : ℝ) :
    CompletelyMultiplicative (smoothIndicator Y) := by
  classical
  constructor
  · simp [smoothIndicator]
  · intro m n
    simp only [smoothIndicator, smooth_mul_iff]
    split_ifs <;> simp_all

theorem smoothIndicator_mem_Icc (Y : ℝ) (n : ℕ) :
    smoothIndicator Y n ∈ Set.Icc (-1 : ℝ) 1 := by
  classical
  simp only [smoothIndicator]
  split_ifs <;> norm_num

theorem consecutiveProduct_pos {n h : ℕ} (hn : 0 < n) :
    0 < consecutiveProduct n h := by
  exact prod_pos (fun j _ => by omega)

theorem prime_le_largestPrimeFactor {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (hd : p ∣ n) : p ≤ largestPrimeFactor n := by
  exact (Finset.le_sup (f := id) (Nat.mem_primeFactors.mpr ⟨hp, hd, hn⟩)).trans
    (le_max_right _ _)

theorem badSet_smooth_factors {ε Y : ℝ} {h n : ℕ} (hn : n ∈ badSet ε h)
    (hY : (n : ℝ) ^ (1 - ε) ≤ Y) {j : ℕ} (hj : j < h) : Smooth Y (n + j) := by
  refine ⟨by have := hn.1; omega, ?_⟩
  intro p hp hd
  have hdprod : p ∣ consecutiveProduct n h :=
    hd.trans (dvd_prod_of_mem (fun j => n + j) (mem_range.mpr hj))
  exact (Nat.cast_le.mpr (prime_le_largestPrimeFactor hp
    (ne_of_gt (consecutiveProduct_pos hn.1)) hdprod)).trans (hn.2.trans hY)

theorem shortMean_eq_one {f : ℕ → ℝ} {h n : ℕ} (hh : 0 < h)
    (hf : ∀ j < h, f (n + j) = 1) : shortMean f h n = 1 := by
  simp [shortMean, sum_congr rfl (fun j hj => hf j (mem_range.mp hj)), ne_of_gt hh]

/-- The numerical contradiction at the heart of the paper's proof. -/
theorem mean_gap {r δ M A : ℝ} (hr : r < 1) (hδ : δ = (1 - r) / 4)
    (hM : M ≤ r + δ) (hA : |A - M| ≤ 2 * δ) : A < 1 := by
  have := (abs_le.mp hA).2
  linarith

end Erdos1201
