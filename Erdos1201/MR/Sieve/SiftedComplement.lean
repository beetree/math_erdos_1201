import Mathlib
import Erdos1201.MR.Ranges
import Erdos1201.MR.Sieve.RangeSieveUpperHR

open Classical Real

/-!
# Upper Bound on the Complement of the Sifted Set

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the sieve upper bound on the complement of the sifted set $S_X$
in the dyadic interval $(X, 2X]$, corresponding to Section 9 of the paper:
$$
\# \{ n \in (X, 2X] : n \notin S_X \} \le C X \sum_{j=1}^J \frac{\log P_j}{\log Q_j}.
$$
An integer $n$ belongs to the complement $(X, 2X] \setminus S_X$ if and only if there exists
some range index $j$ such that $n$ has no prime factor in $[P_j, Q_j]$.
Applying the union bound and the Halberstam–Richert range sieve upper bound
(`card_no_prime_factor_in_Icc_le_hr'`) on each level yields the result.

## Main Results

- `RangeSystem.card_Ioc_sdiff_siftedSet_le`: The upper bound on $\#((X, 2X] \setminus S_X)$.
-/

namespace Erdos1201.MR

/-- Characterization of membership in `primeRange P Q`. -/
lemma mem_primeRange_iff {P Q p : ℕ} :
    p ∈ primeRange P Q ↔ Nat.Prime p ∧ P ≤ p ∧ p ≤ Q := by
  unfold primeRange
  simp [Finset.mem_filter, Finset.mem_Icc, and_comm (b := Nat.Prime p)]

/-- The complement of the sifted set in `(X, 2X]` is covered by the union over `j`
of integers in `(X, 2X]` having no prime factor in `[P j, Q j]`. -/
lemma sdiff_siftedSet_subset_biUnion {J : ℕ} {η : ℝ} (S : RangeSystem J η) (X : ℕ) :
    ((Finset.Ioc X (2 * X)) \ siftedSet J S.R X) ⊆
      Finset.biUnion Finset.univ (fun j : Fin J =>
        (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → S.P j ≤ p → p ≤ S.Q j → ¬ p ∣ n)) := by
  intro n hn
  rw [Finset.mem_sdiff] at hn
  rcases hn with ⟨hn_Ioc, hn_not_sifted⟩
  unfold siftedSet at hn_not_sifted
  rw [Finset.mem_filter] at hn_not_sifted
  have hn_not_factor : ¬ HasFactorInEach J S.R n := by
    intro h
    exact hn_not_sifted ⟨hn_Ioc, h⟩
  unfold HasFactorInEach at hn_not_factor
  simp only [not_forall, not_exists, not_and] at hn_not_factor
  rcases hn_not_factor with ⟨j, hj⟩
  rw [Finset.mem_biUnion]
  refine ⟨j, Finset.mem_univ j, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨hn_Ioc, ?_⟩
  intro p hp hP hpQ
  apply hj p
  rw [RangeSystem.R, mem_primeRange_iff]
  exact ⟨hp, hP, hpQ⟩

/-- Sieve upper bound on the complement of the sifted set:
the number of integers in $(X, 2X]$ outside the sifted set $S_X$ is bounded by
$C X \sum_{j=1}^J \frac{\log P_j}{\log Q_j}$ for an absolute constant $C > 0$. -/
theorem RangeSystem.card_Ioc_sdiff_siftedSet_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ), 2 ≤ X → (∀ j, S.Q j ≤ X) →
      (((Finset.Ioc X (2 * X)) \ siftedSet J S.R X).card : ℝ) ≤ C * X * ∑ j : Fin J, Real.log (S.P j) / Real.log (S.Q j) := by
  rcases card_no_prime_factor_in_Icc_le_hr' with ⟨C, hC_pos, hC_le⟩
  use C, hC_pos
  intro X hX hQX
  have h_sub := sdiff_siftedSet_subset_biUnion S X
  have h_card_sub : (((Finset.Ioc X (2 * X)) \ siftedSet J S.R X).card : ℝ) ≤
      ((Finset.biUnion Finset.univ (fun j : Fin J =>
        (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → S.P j ≤ p → p ≤ S.Q j → ¬ p ∣ n))).card : ℝ) := by
    exact_mod_cast Finset.card_le_card h_sub
  have h_biUnion_le : ((Finset.biUnion Finset.univ (fun j : Fin J =>
        (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → S.P j ≤ p → p ≤ S.Q j → ¬ p ∣ n))).card : ℝ) ≤
      ∑ j : Fin J, (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → S.P j ≤ p → p ≤ S.Q j → ¬ p ∣ n)).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have h_sum_le : (∑ j : Fin J, (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → S.P j ≤ p → p ≤ S.Q j → ¬ p ∣ n)).card : ℝ)) ≤
      ∑ j : Fin J, (C * X * Real.log (S.P j) / Real.log (S.Q j)) := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact hC_le X (S.P j) (S.Q j) (S.two_le_P j) (S.P_le_Q j) hX (hQX j)
  have h_factor : (∑ j : Fin J, (C * X * Real.log (S.P j) / Real.log (S.Q j))) =
      C * X * ∑ j : Fin J, Real.log (S.P j) / Real.log (S.Q j) := by
    simp_rw [← mul_div_assoc']
    rw [← Finset.mul_sum]
  linarith

end Erdos1201.MR
