module

public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Erdos1201.Vendor.Analysis.GallagherAdditiveLargeSieveCore

@[expose] public section

/-!
# Windowed additive large-sieve bounds

This module specializes the centered-frequency additive large sieve to a
finite interval of consecutive integer frequencies.
-/

namespace GallagherAdditiveLargeSieveWindow

open scoped BigOperators
open Real Complex
open AdditiveCharacterGeometricSums GallagherSobolevFourier
open GallagherAdditiveLargeSieveCore

/-- A frequency window of `N` consecutive integers satisfies the log-free
additive large-sieve bound obtained by centering the window. -/
theorem finite_additiveLargeSieve_window (M : ℤ) (N : ℕ) (b : ℤ → ℂ)
    (R : ℕ) (θ : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : ∀ r s, r ≠ s → δ ≤ nearestIntegerDistance (θ r - θ s)) :
    (∑ r, ‖∑ n ∈ Finset.Ico M (M + N), b n * additiveCharacter ((n : ℝ) * θ r)‖ ^ 2)
      ≤ (δ⁻¹ + 2 * Real.pi * N) * ∑ n ∈ Finset.Ico M (M + N), ‖b n‖ ^ 2 := by
  set c : ℤ := M + (N / 2 : ℤ)
  set F' : Finset ℤ := Finset.Ico (-(N / 2 : ℤ)) (N - (N / 2 : ℤ))
  set b' : ℤ → ℂ := fun m => b (m + c)
  convert finite_additiveLargeSieve_core F' b' (N / 2) (by positivity) (fun m hm => ?_)
    R θ δ hδ hδ1 hsp using 1
  · have h_sum_eq : ∀ r, ∑ n ∈ Finset.Ico M (M + N),
        b n * additiveCharacter (n * θ r) = additiveCharacter (c * θ r) *
          ∑ m ∈ F', b' m * additiveCharacter (m * θ r) := by
      intro r
      have h_sum_eq : ∑ n ∈ Finset.Ico M (M + N), b n * additiveCharacter (n * θ r) =
          ∑ m ∈ F', b (m + c) * additiveCharacter ((m + c) * θ r) := by
        refine Finset.sum_bij (fun n hn => n - c) ?_ ?_ ?_ ?_ <;> norm_num
        · grind
        · exact fun x hx => ⟨x + c, ⟨by
              linarith [Finset.mem_Ico.mp hx, Int.mul_ediv_add_emod N 2,
                Int.emod_nonneg N two_ne_zero, Int.emod_lt_of_pos N two_pos], by
              linarith [Finset.mem_Ico.mp hx, Int.mul_ediv_add_emod N 2,
                Int.emod_nonneg N two_ne_zero, Int.emod_lt_of_pos N two_pos]⟩, by ring⟩
      rw [h_sum_eq, Finset.mul_sum]
      congr
      ext
      ring_nf
      unfold b' additiveCharacter
      ring_nf
      simpa only [mul_assoc, ← Complex.exp_add] using by push_cast; ring_nf
    simp_all [mul_comm, trigonometricPolynomial]
    norm_num [norm_additiveCharacter]
  · rw [show (Finset.Ico M (M + N) : Finset ℤ) =
        Finset.image (fun m : ℤ => m + c) F' from ?_, Finset.sum_image] <;> norm_num <;> first | ring1 | ring_nf
    ext
    norm_num
    grind
  · rw [le_div_iff₀] <;> norm_cast
    cases abs_cases m <;>
      linarith [Finset.mem_Ico.mp hm, Int.mul_ediv_add_emod N 2,
        Int.emod_nonneg N two_ne_zero, Int.emod_lt_of_pos N two_pos]

end GallagherAdditiveLargeSieveWindow
