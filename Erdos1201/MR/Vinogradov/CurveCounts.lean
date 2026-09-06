import Mathlib

/-!
# Vinogradov Curve Counts

This module provides basic combinatorial counts for Vinogradov's mean value theorem,
following Tao (254A Notes 5, Section 2).

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

noncomputable section

namespace Erdos1201.MR.Vinogradov

open scoped BigOperators

/-- The moment curve γ_k(a) = (a, a², …, a^k) as an integer vector. -/
def momentCurve (k : ℕ) (a : ℤ) : Fin k → ℤ := fun j => a ^ (j.val + 1)

/-- Sum of ℓ points of the curve. -/
def curveSum (k ℓ : ℕ) (x : Fin ℓ → ℤ) : Fin k → ℤ := ∑ i, momentCurve k (x i)

/-- Tuples with entries in {1, …, M}. -/
def tuples (ℓ M : ℕ) : Finset (Fin ℓ → ℤ) := Fintype.piFinset fun _ => Finset.Icc (1 : ℤ) M

/-- Representation count ν_{ℓ,k,M}(y). -/
def repCount (k ℓ M : ℕ) (y : Fin k → ℤ) : ℕ := ((tuples ℓ M).filter (fun x => curveSum k ℓ x = y)).card

/-- The box B = {y : |y_j| ≤ ℓ M^{j+1}}. -/
def box (k ℓ M : ℕ) : Finset (Fin k → ℤ) := Fintype.piFinset fun j => Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1))

/-- J_{ℓ,k}(M): number of solutions of γ(x₁)+⋯+γ(x_ℓ) = γ(y₁)+⋯+γ(y_ℓ) in {1..M}. -/
def J (k ℓ M : ℕ) : ℕ := (((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 = curveSum k ℓ xy.2)).card

/-- Coordinate-wise expansion of curveSum. -/
theorem curveSum_apply (k ℓ : ℕ) (x : Fin ℓ → ℤ) (j : Fin k) :
    curveSum k ℓ x j = ∑ i : Fin ℓ, (x i) ^ (j.val + 1) := by
  simp [curveSum, momentCurve, Finset.sum_apply]

/-- Characterization of membership in tuples. -/
theorem mem_tuples_iff (ℓ M : ℕ) (x : Fin ℓ → ℤ) :
    x ∈ tuples ℓ M ↔ ∀ i : Fin ℓ, 1 ≤ x i ∧ x i ≤ (M : ℤ) := by
  simp [tuples, Fintype.mem_piFinset, Finset.mem_Icc]

/-- Every curve sum of tuples with entries in {1, …, M} lies in the box B. -/
theorem curveSum_mem_box (k ℓ M : ℕ) (x : Fin ℓ → ℤ) (hx : x ∈ tuples ℓ M) : curveSum k ℓ x ∈ box k ℓ M := by
  rw [mem_tuples_iff] at hx
  rw [box, Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_Icc, curveSum_apply]
  have h_nonneg : ∀ i : Fin ℓ, 0 ≤ (x i) ^ (j.val + 1) := by
    intro i
    have : 0 ≤ x i := by linarith [(hx i).1]
    exact pow_nonneg this (j.val + 1)
  have h_le : ∀ i : Fin ℓ, (x i) ^ (j.val + 1) ≤ (M : ℤ) ^ (j.val + 1) := by
    intro i
    have hx0 : 0 ≤ x i := by linarith [(hx i).1]
    exact pow_le_pow_left₀ hx0 (hx i).2 (j.val + 1)
  have h_sum_le : (∑ i : Fin ℓ, (x i) ^ (j.val + 1)) ≤ (ℓ : ℤ) * (M : ℤ) ^ (j.val + 1) := by
    have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin ℓ)) (fun i => (x i) ^ (j.val + 1)) ((M : ℤ) ^ (j.val + 1))
      (fun i _ => h_le i)
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    exact this
  have h_sum_nonneg : 0 ≤ ∑ i : Fin ℓ, (x i) ^ (j.val + 1) := by
    exact Finset.sum_nonneg (fun i _ => h_nonneg i)
  constructor
  · linarith [h_sum_nonneg, show 0 ≤ (ℓ : ℤ) * (M : ℤ) ^ (j.val + 1) by positivity]
  · exact h_sum_le

/-- Representation count vanishes outside the bounding box. -/
theorem repCount_eq_zero_of_not_mem_box (k ℓ M : ℕ) (y : Fin k → ℤ) (hy : y ∉ box k ℓ M) :
    repCount k ℓ M y = 0 := by
  simp only [repCount, Finset.card_eq_zero]
  rw [Finset.filter_eq_empty_iff]
  intro x hx heq
  have := curveSum_mem_box k ℓ M x hx
  rw [heq] at this
  exact hy this

/-- Cardinality of {1, …, M} as an integer interval is M. -/
lemma card_Icc_one_toNat (M : ℕ) : (Finset.Icc (1 : ℤ) (M : ℤ)).card = M := by
  rw [Int.card_Icc]
  have : (M : ℤ) + 1 - 1 = (M : ℤ) := by ring
  rw [this, Int.toNat_natCast]

/-- The number of tuples with entries in {1, …, M} is M^ℓ. -/
theorem card_tuples (ℓ M : ℕ) : (tuples ℓ M).card = M ^ ℓ := by
  rw [tuples, Fintype.card_piFinset]
  simp only [card_Icc_one_toNat, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Sum of representation counts over the box equals the total number of tuples M^ℓ. -/
theorem sum_repCount (k ℓ M : ℕ) : ∑ y ∈ box k ℓ M, repCount k ℓ M y = M ^ ℓ := by
  have h_maps : Set.MapsTo (curveSum k ℓ) ↑(tuples ℓ M) ↑(box k ℓ M) := by
    intro x hx
    exact curveSum_mem_box k ℓ M x hx
  rw [← card_tuples ℓ M]
  rw [Finset.card_eq_sum_card_fiberwise h_maps]
  rfl

/-- J equals the sum of squares of representation counts. -/
theorem J_eq_sum_sq_repCount (k ℓ M : ℕ) : J k ℓ M = ∑ y ∈ box k ℓ M, (repCount k ℓ M y) ^ 2 := by
  dsimp only [J]
  have h_maps : Set.MapsTo (fun xy : (Fin ℓ → ℤ) × (Fin ℓ → ℤ) => curveSum k ℓ xy.1)
      ↑(((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 = curveSum k ℓ xy.2))
      ↑(box k ℓ M) := by
    intro xy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hxy
    exact curveSum_mem_box k ℓ M xy.1 hxy.1.1
  rw [Finset.card_eq_sum_card_fiberwise h_maps]
  apply Finset.sum_congr rfl
  intro y _
  have h_eq : {xy ∈ ((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 = curveSum k ℓ xy.2) |
        curveSum k ℓ xy.1 = y} =
      ((tuples ℓ M).filter (fun x => curveSum k ℓ x = y)) ×ˢ ((tuples ℓ M).filter (fun x => curveSum k ℓ x = y)) := by
    ext xy
    simp only [Finset.mem_filter, Finset.mem_product]
    constructor
    · rintro ⟨⟨⟨h1, h2⟩, heq⟩, hy⟩
      subst hy
      exact ⟨⟨h1, rfl⟩, ⟨h2, heq.symm⟩⟩
    · rintro ⟨⟨h1, rfl⟩, ⟨h2, heq⟩⟩
      exact ⟨⟨⟨h1, h2⟩, heq.symm⟩, rfl⟩
  rw [h_eq, Finset.card_product]
  dsimp only [repCount]
  ring

/-- Trivial upper bound on J: J ≤ M^(2ℓ). -/
theorem J_le (k ℓ M : ℕ) : J k ℓ M ≤ M ^ (2 * ℓ) := by
  dsimp only [J]
  have h1 : (((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 = curveSum k ℓ xy.2)).card ≤
      ((tuples ℓ M) ×ˢ (tuples ℓ M)).card :=
    Finset.card_filter_le _ _
  have h2 : ((tuples ℓ M) ×ˢ (tuples ℓ M)).card = (tuples ℓ M).card * (tuples ℓ M).card :=
    Finset.card_product _ _
  rw [card_tuples] at h2
  rw [h2] at h1
  have h3 : M ^ ℓ * M ^ ℓ = M ^ (2 * ℓ) := by
    rw [← pow_add]
    congr 1
    omega
  rw [h3] at h1
  exact h1

/-- Cardinality of a symmetric integer interval [-N, N] is 2N + 1. -/
lemma card_Icc_neg_self (N : ℕ) : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
  rw [Int.card_Icc]
  have : (N : ℤ) + 1 - (-(N : ℤ)) = ((2 * N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

/-- Cardinality of the bounding box B. -/
theorem card_box (k ℓ M : ℕ) : (box k ℓ M).card = ∏ j : Fin k, (2 * ℓ * M ^ (j.val + 1) + 1) := by
  rw [box, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro j _
  have h2 := card_Icc_neg_self (ℓ * M ^ (j.val + 1))
  rw [← mul_assoc] at h2
  exact h2

/-- The sum of squares of representation counts on any finset is bounded by that on the box. -/
lemma sum_sq_repCount_le_box (k ℓ M : ℕ) (s : Finset (Fin k → ℤ)) :
    ∑ x ∈ s, (repCount k ℓ M x) ^ 2 ≤ ∑ x ∈ box k ℓ M, (repCount k ℓ M x) ^ 2 := by
  have h_sub : (s ∩ box k ℓ M) ⊆ s := Finset.inter_subset_left
  have h_eq : ∑ x ∈ s, (repCount k ℓ M x) ^ 2 = ∑ x ∈ s ∩ box k ℓ M, (repCount k ℓ M x) ^ 2 := by
    apply (Finset.sum_subset h_sub _).symm
    intro x hx_s hx_not_inter
    have hx_not_box : x ∉ box k ℓ M := by
      intro h_box
      exact hx_not_inter (Finset.mem_inter.mpr ⟨hx_s, h_box⟩)
    rw [repCount_eq_zero_of_not_mem_box k ℓ M x hx_not_box, zero_pow (by omega)]
  rw [h_eq]
  exact Finset.sum_le_sum_of_subset Finset.inter_subset_right

/-- The sum of squares of shifted representation counts is bounded by J. -/
lemma sum_sq_repCount_add_le (k ℓ M : ℕ) (a : Fin k → ℤ) :
    ∑ y ∈ box k ℓ M, (repCount k ℓ M (y + a)) ^ 2 ≤ J k ℓ M := by
  have hinj : Set.InjOn (fun y => y + a) ↑(box k ℓ M) := by
    intro x _ y _ h
    exact add_right_cancel h
  rw [← Finset.sum_image (f := fun z => (repCount k ℓ M z) ^ 2) hinj]
  rw [J_eq_sum_sq_repCount]
  exact sum_sq_repCount_le_box k ℓ M ((box k ℓ M).image (fun y => y + a))

/-- Shifted representation count is bounded by J (used in Lemma 21): ∑_n ν(n) ν(n + a) ≤ J. -/
theorem sum_repCount_mul_repCount_add_le (k ℓ M : ℕ) (a : Fin k → ℤ) :
    ∑ y ∈ box k ℓ M, repCount k ℓ M y * repCount k ℓ M (y + a) ≤ J k ℓ M := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (box k ℓ M)
    (fun y => repCount k ℓ M y) (fun y => repCount k ℓ M (y + a))
  have h1 : ∑ y ∈ box k ℓ M, (repCount k ℓ M y) ^ 2 = J k ℓ M := (J_eq_sum_sq_repCount k ℓ M).symm
  have h2 : ∑ y ∈ box k ℓ M, (repCount k ℓ M (y + a)) ^ 2 ≤ J k ℓ M := sum_sq_repCount_add_le k ℓ M a
  have h_prod : (∑ y ∈ box k ℓ M, (repCount k ℓ M y) ^ 2) * ∑ y ∈ box k ℓ M, (repCount k ℓ M (y + a)) ^ 2 ≤ (J k ℓ M) ^ 2 := by
    rw [h1, sq]
    exact Nat.mul_le_mul_left (J k ℓ M) h2
  have h_sq : (∑ y ∈ box k ℓ M, repCount k ℓ M y * repCount k ℓ M (y + a)) ^ 2 ≤ (J k ℓ M) ^ 2 := by
    exact le_trans hcs h_prod
  nlinarith

/-- Every difference of two ℓ-fold curve sums has at most J representations (Cauchy–Schwarz / counting). -/
theorem card_filter_curveSum_sub_le (k ℓ M : ℕ) (v : Fin k → ℤ) :
    (((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 - curveSum k ℓ xy.2 = v)).card ≤ J k ℓ M := by
  have h_maps : Set.MapsTo (fun xy : (Fin ℓ → ℤ) × (Fin ℓ → ℤ) => curveSum k ℓ xy.2)
      ↑(((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 - curveSum k ℓ xy.2 = v))
      ↑(box k ℓ M) := by
    intro xy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hxy
    exact curveSum_mem_box k ℓ M xy.2 hxy.1.2
  have h_fiber := Finset.card_eq_sum_card_fiberwise h_maps
  rw [h_fiber]
  have h_congr : ∀ y ∈ box k ℓ M,
      {xy ∈ ((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 - curveSum k ℓ xy.2 = v) |
        curveSum k ℓ xy.2 = y}.card = repCount k ℓ M y * repCount k ℓ M (y + v) := by
    intro y _
    have h_eq : {xy ∈ ((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 - curveSum k ℓ xy.2 = v) |
          curveSum k ℓ xy.2 = y} =
        ((tuples ℓ M).filter (fun x => curveSum k ℓ x = y + v)) ×ˢ
        ((tuples ℓ M).filter (fun x => curveSum k ℓ x = y)) := by
      ext xy
      simp only [Finset.mem_filter, Finset.mem_product]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, hsub⟩, hy⟩
        have h1_sum : curveSum k ℓ xy.1 = y + v := by
          rw [hy] at hsub
          rw [sub_eq_iff_eq_add, add_comm] at hsub
          exact hsub
        exact ⟨⟨h1, h1_sum⟩, ⟨h2, hy⟩⟩
      · rintro ⟨⟨h1, h1_sum⟩, ⟨h2, hy⟩⟩
        have hsub : curveSum k ℓ xy.1 - curveSum k ℓ xy.2 = v := by
          rw [h1_sum, hy, add_sub_cancel_left]
        exact ⟨⟨⟨h1, h2⟩, hsub⟩, hy⟩
    rw [h_eq, Finset.card_product]
    dsimp only [repCount]
    ring
  rw [Finset.sum_congr rfl h_congr]
  exact sum_repCount_mul_repCount_add_le k ℓ M v

end Erdos1201.MR.Vinogradov
