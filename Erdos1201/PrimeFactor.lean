import Erdos1201.Basic

/-!
# Semantic bridges for the largest-prime-factor convention ($P^+$)

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This file is part of a Lean reproduction of that work; see `erdos1201.pdf`.

This module provides independently checked semantic bridges verifying that the
prime-divisor smoothness predicate `Erdos1201.Smooth` agrees with the paper's
largest-prime-factor convention `Erdos1201.largestPrimeFactor` ($P^+$):
1. `largestPrimeFactor_one`: $P^+(1) = 1$.
2. `largestPrimeFactor_of_prime`: For prime $p$, $P^+(p) = p$.
3. `smooth_iff_largestPrimeFactor_le`: For $n > 0$ and real cutoff $Y \ge 1$,
   `Smooth Y n ↔ (largestPrimeFactor n : ℝ) ≤ Y`.

Also provided are directional implications and corollaries connecting
`badSet` directly to smoothness of the consecutive product.
-/

namespace Erdos1201

/-- Semantic bridge 1: The paper's convention $P^+(1) = 1$. -/
theorem largestPrimeFactor_one : largestPrimeFactor 1 = 1 := by
  unfold largestPrimeFactor
  rw [Nat.primeFactors_one, Finset.sup_empty]
  rfl

/-- Semantic bridge 2: For prime $p$, $P^+(p) = p$. -/
theorem largestPrimeFactor_of_prime {p : ℕ} (hp : Nat.Prime p) : largestPrimeFactor p = p := by
  unfold largestPrimeFactor
  rw [hp.primeFactors, Finset.sup_singleton, id]
  exact max_eq_right hp.one_lt.le

/-- Lower bound: $1 \le P^+(n)$ for all $n \in \mathbb{N}$. -/
theorem one_le_largestPrimeFactor (n : ℕ) : 1 ≤ largestPrimeFactor n := by
  unfold largestPrimeFactor
  exact le_max_left 1 _

/-- Semantic bridge 3 (forward direction): If $(P^+(n) : \mathbb{R}) \le Y$ for positive $n$,
then $n$ is $Y$-smooth. Note that this direction holds for any $Y \in \mathbb{R}$ without
requiring $1 \le Y$ explicitly (since $1 \le P^+(n) \le Y$). -/
theorem smooth_of_largestPrimeFactor_le {Y : ℝ} {n : ℕ} (hn : 0 < n)
    (hle : (largestPrimeFactor n : ℝ) ≤ Y) : Smooth Y n := by
  refine ⟨ne_of_gt hn, ?_⟩
  intro p hp hdvd
  have h1 : p ≤ largestPrimeFactor n := prime_le_largestPrimeFactor hp (ne_of_gt hn) hdvd
  have h2 : (p : ℝ) ≤ (largestPrimeFactor n : ℝ) := Nat.cast_le.mpr h1
  exact h2.trans hle

/-- Semantic bridge 3 (backward direction): If $n$ is $Y$-smooth with real cutoff $Y \ge 1$,
then $(P^+(n) : \mathbb{R}) \le Y$. -/
theorem largestPrimeFactor_le_of_smooth {Y : ℝ} (hY : 1 ≤ Y) {n : ℕ} (hsm : Smooth Y n) :
    (largestPrimeFactor n : ℝ) ≤ Y := by
  unfold largestPrimeFactor
  rw [Nat.cast_max, Nat.cast_one, max_le_iff]
  refine ⟨hY, ?_⟩
  rcases (n.primeFactors).eq_empty_or_nonempty with hne | hne
  · rw [hne, Finset.sup_empty]
    have : (⊥ : ℕ) = 0 := rfl
    rw [this]
    push_cast
    linarith
  · obtain ⟨p, hp_mem, hsup⟩ := Finset.exists_mem_eq_sup n.primeFactors hne id
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hdvd := (Nat.mem_primeFactors.mp hp_mem).2.1
    have hle := hsm.2 p hp hdvd
    dsimp [id] at hsup
    rw [hsup]
    exact hle

/-- Semantic bridge 3: For positive $n$ and real cutoff $Y \ge 1$, `Smooth Y n` if and only if
$(P^+(n) : \mathbb{R}) \le Y$. This verifies that the prime-divisor smoothness predicate
agrees with the paper's largest-prime-factor convention. -/
theorem smooth_iff_largestPrimeFactor_le {Y : ℝ} (hY : 1 ≤ Y) {n : ℕ} (hn : 0 < n) :
    Smooth Y n ↔ (largestPrimeFactor n : ℝ) ≤ Y :=
  ⟨largestPrimeFactor_le_of_smooth hY, smooth_of_largestPrimeFactor_le hn⟩

/-- Symmetric formulation of semantic bridge 3: For positive $n$ and real cutoff $Y \ge 1$,
$(P^+(n) : \mathbb{R}) \le Y \leftrightarrow \text{Smooth } Y \, n$. -/
theorem largestPrimeFactor_le_iff_smooth {Y : ℝ} (hY : 1 ≤ Y) {n : ℕ} (hn : 0 < n) :
    (largestPrimeFactor n : ℝ) ≤ Y ↔ Smooth Y n :=
  (smooth_iff_largestPrimeFactor_le hY hn).symm

/-- Semantic bridge 3 formulated with non-zero hypothesis $n \ne 0$. -/
theorem smooth_iff_largestPrimeFactor_le' {Y : ℝ} (hY : 1 ≤ Y) {n : ℕ} (hn : n ≠ 0) :
    Smooth Y n ↔ (largestPrimeFactor n : ℝ) ≤ Y :=
  smooth_iff_largestPrimeFactor_le hY (Nat.pos_of_ne_zero hn)

/-- Corollary connecting `badSet` to smoothness of consecutive products:
for $n \in \text{badSet } \varepsilon \, h$ and cutoff $Y = n^{1 - \varepsilon} \ge 1$,
the product $\prod_{j=0}^{h-1} (n+j)$ is $Y$-smooth. -/
theorem badSet_consecutiveProduct_smooth {ε : ℝ} {h n : ℕ} (hn : n ∈ badSet ε h)
    (hY : 1 ≤ (n : ℝ) ^ (1 - ε)) :
    Smooth ((n : ℝ) ^ (1 - ε)) (consecutiveProduct n h) := by
  have hprod_pos : 0 < consecutiveProduct n h := consecutiveProduct_pos hn.1
  exact (smooth_iff_largestPrimeFactor_le hY hprod_pos).mpr hn.2

end Erdos1201
