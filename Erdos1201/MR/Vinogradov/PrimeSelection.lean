/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

Attribution: the original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
-/
import Mathlib
import Erdos1201.MR.Vinogradov.CurveCounts
import Erdos1201.PrimeSums

/-!
# Vinogradov Prime Selection (Tao's Lemma 14)

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes Tao's Lemma 14 (reduction of the Vinogradov mean value
count $J_{k,\ell}(M)$ to tuples with pairwise distinct reductions modulo a suitable prime $p$).
-/

noncomputable section

namespace Erdos1201.MR.Vinogradov

open scoped BigOperators
open Real

/-- J^{(p)}: solutions whose first k coordinates on each side have pairwise distinct reductions mod p. -/
def Jp (k ℓ M p : ℕ) (hk : k ≤ ℓ) : ℕ := (((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun xy => curveSum k ℓ xy.1 = curveSum k ℓ xy.2 ∧ (∀ i j : Fin k, i ≠ j → (xy.1 (Fin.castLE hk i) : ZMod p) ≠ (xy.1 (Fin.castLE hk j) : ZMod p)) ∧ (∀ i j : Fin k, i ≠ j → (xy.2 (Fin.castLE hk i) : ZMod p) ≠ (xy.2 (Fin.castLE hk j) : ZMod p)))).card

/-- For k = 1, Jp equals J because Fin 1 has no distinct pairs of indices. -/
theorem Jp_one (ℓ M p : ℕ) (h1l : 1 ≤ ℓ) : Jp 1 ℓ M p h1l = J 1 ℓ M := by
  dsimp [Jp, J]
  apply congr_arg Finset.card
  apply Finset.filter_congr
  intro xy _
  simp only [and_iff_left_iff_imp]
  intro _
  refine ⟨fun i j hij => (hij (Subsingleton.elim i j)).elim, fun i j hij => (hij (Subsingleton.elim i j)).elim⟩

/-- The bound on degenerate tuples: tuples with image cardinality < k. -/
lemma card_degenerate_tuples_le (ℓ M k : ℕ) (hk : 1 ≤ k) (hkl : k ≤ ℓ) :
    ((tuples ℓ M).filter (fun x => (Finset.image x Finset.univ).card < k)).card ≤
      k ^ ℓ * ℓ ^ k * M ^ (k - 1) := by
  have h_sub : (tuples ℓ M).filter (fun x => (Finset.image x Finset.univ).card < k) ⊆
      Finset.image (fun (gv : (Fin ℓ → Fin (k - 1)) × (Fin (k - 1) → Finset.Icc (1 : ℤ) M)) =>
        (fun i => (gv.2 (gv.1 i) : ℤ))) Finset.univ := by
    intro x hx
    simp only [Finset.mem_filter] at hx
    have hx_tup := hx.1
    have hx_card := hx.2
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    by_cases hk1 : k = 1
    · subst hk1
      exfalso
      have : 1 ≤ ℓ := by omega
      have h_nonempty : (Finset.univ : Finset (Fin ℓ)).Nonempty :=
        Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp (by omega))
      have h_img_nonempty : (Finset.image x Finset.univ).Nonempty := h_nonempty.image x
      have : 1 ≤ (Finset.image x Finset.univ).card := h_img_nonempty.card_pos
      omega
    have hk_sub_pos : 0 < k - 1 := by omega
    let A : Finset ℤ := Finset.image x Finset.univ
    have hA_sub : A ⊆ Finset.Icc (1 : ℤ) M := by
      intro y hy
      simp only [A, Finset.mem_image, Finset.mem_univ, true_and] at hy
      obtain ⟨i, rfl⟩ := hy
      rw [mem_tuples_iff] at hx_tup
      exact Finset.mem_Icc.mpr (hx_tup i)
    have hA_card : A.card ≤ k - 1 := by
      dsimp [A]
      omega
    have h_card_A : Fintype.card ↥A = A.card := Fintype.card_coe A
    have h_card_Fin : Fintype.card (Fin (k - 1)) = k - 1 := Fintype.card_fin (k - 1)
    have h_emb_le : Fintype.card ↥A ≤ Fintype.card (Fin (k - 1)) := by
      rw [h_card_A, h_card_Fin]
      exact hA_card
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le h_emb_le
    let g : Fin ℓ → Fin (k - 1) := fun i => f ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩
    let v : Fin (k - 1) → Finset.Icc (1 : ℤ) M := fun j =>
      if hj : ∃ a : ↥A, f a = j then
        ⟨(Classical.choose hj).1, hA_sub (Classical.choose hj).2⟩
      else
        ⟨1, by
          simp only [Finset.mem_Icc]
          constructor
          · rfl
          · have : 1 ≤ (M : ℤ) := by
              rw [mem_tuples_iff] at hx_tup
              have : 0 < ℓ := by omega
              have hi : Fin ℓ := ⟨0, this⟩
              have := (hx_tup hi).2
              linarith [(hx_tup hi).1]
            exact this⟩
    use (g, v)
    ext i
    dsimp [g, v]
    have hj : ∃ a : ↥A, f a = f ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩ :=
      ⟨⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩, rfl⟩
    simp only [hj, dite_true]
    have h_eq : Classical.choose hj = (⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩ : ↥A) :=
      f.injective (Classical.choose_spec hj)
    exact congr_arg (fun a : ↥A => (a.1 : ℤ)) h_eq
  have h_card_le := Finset.card_le_card h_sub
  have h_img_le := Finset.card_image_le (s := Finset.univ)
    (f := fun (gv : (Fin ℓ → Fin (k - 1)) × (Fin (k - 1) → Finset.Icc (1 : ℤ) M)) =>
      (fun i => (gv.2 (gv.1 i) : ℤ)))
  have h_univ : (Finset.univ : Finset ((Fin ℓ → Fin (k - 1)) × (Fin (k - 1) → Finset.Icc (1 : ℤ) M))).card =
      (k - 1) ^ ℓ * M ^ (k - 1) := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin]
    have h_card_Icc : Fintype.card (Finset.Icc (1 : ℤ) M) = M := by
      rw [Fintype.card_coe, card_Icc_one_toNat]
    rw [h_card_Icc, Fintype.card_fin]
  have h_tot : ((tuples ℓ M).filter (fun x => (Finset.image x Finset.univ).card < k)).card ≤
      (k - 1) ^ ℓ * M ^ (k - 1) := by
    linarith [h_card_le, h_img_le, h_univ]
  have h_pow1 : (k - 1) ^ ℓ ≤ k ^ ℓ := Nat.pow_le_pow_left (by omega) ℓ
  have h_pow2 : 1 ≤ ℓ ^ k := by
    have : 1 ≤ ℓ := by omega
    exact one_le_pow₀ this
  calc ((tuples ℓ M).filter (fun x => (Finset.image x Finset.univ).card < k)).card
    _ ≤ (k - 1) ^ ℓ * M ^ (k - 1) := h_tot
    _ ≤ (k ^ ℓ * 1) * M ^ (k - 1) := by
      have : (k - 1) ^ ℓ ≤ k ^ ℓ * 1 := by linarith [h_pow1]
      exact Nat.mul_le_mul_right (M ^ (k - 1)) this
    _ ≤ (k ^ ℓ * ℓ ^ k) * M ^ (k - 1) := by
      have : k ^ ℓ * 1 ≤ k ^ ℓ * ℓ ^ k := Nat.mul_le_mul_left (k ^ ℓ) h_pow2
      exact Nat.mul_le_mul_right (M ^ (k - 1)) this
    _ = k ^ ℓ * ℓ ^ k * M ^ (k - 1) := by ring

/-- Product of distinct primes dividing a non-zero integer divides its absolute value. -/
lemma prod_primes_dvd_natAbs {D : ℤ} (hD : D ≠ 0) (P : Finset ℕ)
    (hP_prime : ∀ p ∈ P, Nat.Prime p)
    (hP_dvd : ∀ p ∈ P, (p : ℤ) ∣ D) :
    (∏ p ∈ P, p) ≤ D.natAbs := by
  have h_dvd : (∏ p ∈ P, p) ∣ D.natAbs := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Nat.prime_iff.mp (hP_prime p hp))
    · intro p hp
      exact Int.natAbs_dvd_natAbs.mpr (hP_dvd p hp)
  exact Nat.le_of_dvd (Int.natAbs_pos.mpr hD) h_dvd

/-- Fewer than k³ primes strictly exceeding M^{1/k} can divide an integer D with |D| ≤ M^{k(k-1)}. -/
lemma card_primes_dvd_lt {k M : ℕ} (hk : 1 ≤ k) (hM : 1 < M)
    {D : ℤ} (hD : D ≠ 0) (hD_le : (D.natAbs : ℝ) ≤ (M : ℝ) ^ (k * (k - 1)))
    (P : Finset ℕ)
    (hP_prime : ∀ p ∈ P, Nat.Prime p)
    (hP_gt : ∀ p ∈ P, (M : ℝ) ^ (1 / (k : ℝ)) < (p : ℝ))
    (hP_dvd : ∀ p ∈ P, (p : ℤ) ∣ D) :
    P.card < k ^ 3 := by
  have hM_pos : 0 < (M : ℝ) := by positivity
  have hM_gt1 : 1 < (M : ℝ) := by exact_mod_cast hM
  have hk_pos : 0 < (k : ℝ) := by positivity
  by_cases hP_empty : P = ∅
  · subst hP_empty
    simp only [Finset.card_empty]
    have : 0 < k ^ 3 := by positivity
    exact this
  have h_prod_dvd : (∏ p ∈ P, p) ≤ D.natAbs := prod_primes_dvd_natAbs hD P hP_prime hP_dvd
  have h_cast_le : (∏ p ∈ P, (p : ℝ)) ≤ (D.natAbs : ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast h_prod_dvd
  have h_prod_gt : (M : ℝ) ^ ((P.card : ℝ) / (k : ℝ)) < ∏ p ∈ P, (p : ℝ) := by
    have h_card_prod : (∏ p ∈ P, (M : ℝ) ^ (1 / (k : ℝ))) = (M : ℝ) ^ ((P.card : ℝ) / (k : ℝ)) := by
      rw [Finset.prod_const, ← rpow_natCast, ← rpow_mul hM_pos.le]
      congr 1
      ring
    rw [← h_card_prod]
    have h_ne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP_empty
    refine Finset.prod_lt_prod_of_nonempty ?_ (fun p hp => hP_gt p hp) h_ne
    intro p hp
    positivity
  have h_trans : (M : ℝ) ^ ((P.card : ℝ) / (k : ℝ)) < (M : ℝ) ^ (k * (k - 1)) :=
    h_prod_gt.trans_le (h_cast_le.trans hD_le)
  rw [← Real.rpow_natCast (M : ℝ) (k * (k - 1))] at h_trans
  rw [Real.rpow_lt_rpow_left_iff hM_gt1] at h_trans
  have h_div_lt : (P.card : ℝ) < ((k * (k - 1) : ℕ) : ℝ) * (k : ℝ) := by
    rwa [div_lt_iff₀ hk_pos] at h_trans
  have h_cast_eq : ((k * (k - 1) : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hk]
    push_cast
    rfl
  have h1 : (P.card : ℝ) < (k : ℝ) * ((k : ℝ) * ((k : ℝ) - 1)) := by
    calc (P.card : ℝ) < ((k * (k - 1) : ℕ) : ℝ) * (k : ℝ) := h_div_lt
      _ = ((k : ℝ) * ((k : ℝ) - 1)) * (k : ℝ) := by rw [h_cast_eq]
      _ = (k : ℝ) * ((k : ℝ) * ((k : ℝ) - 1)) := by ring
  have h2 : (k : ℝ) * ((k : ℝ) * ((k : ℝ) - 1)) ≤ (k : ℝ) ^ 3 := by
    calc (k : ℝ) * ((k : ℝ) * ((k : ℝ) - 1)) = (k : ℝ) ^ 3 - (k : ℝ) ^ 2 := by ring
      _ ≤ (k : ℝ) ^ 3 := by
        have : 0 ≤ (k : ℝ) ^ 2 := by positivity
        linarith
  have h_lt : (P.card : ℝ) < (k : ℝ) ^ 3 := h1.trans_le h2
  exact_mod_cast h_lt

/-- M exceeds 1 when log M ≥ 100 * k^3. -/
lemma one_lt_M_of_hM {k M : ℕ} (hk : 1 ≤ k) (hM : Real.exp (100 * (k : ℝ) ^ 3) ≤ M) : 1 < M := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have : (1 : ℝ) ≤ (k : ℝ) ^ 3 := one_le_pow₀ hk1
  have h100 : (100 : ℝ) ≤ 100 * (k : ℝ) ^ 3 := by nlinarith
  have h_exp : Real.exp 100 ≤ (M : ℝ) := (Real.exp_le_exp.mpr h100).trans hM
  have : (2 : ℝ) ≤ Real.exp 100 := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have : (2 : ℝ) ≤ (M : ℝ) := this.trans h_exp
  exact_mod_cast (by linarith : 1 < (M : ℝ))

/-- Bertrand's postulate provides a prime in (k M^{1/k}, 4 k M^{1/k}]. -/
lemma exists_prime_in_range (k M : ℕ) (hk : 1 ≤ k) (hM : Real.exp (100 * (k : ℝ) ^ 3) ≤ M) :
    ∃ p : ℕ, p.Prime ∧ (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ)) < p ∧ (p : ℝ) ≤ 4 * k * (M : ℝ) ^ (1 / (k : ℝ)) := by
  let y : ℝ := (k : ℝ) * (M : ℝ) ^ (1 / (k : ℝ))
  have hy_pos : 0 < y := by
    have : 0 < (k : ℝ) := by positivity
    have : 0 < (M : ℝ) := by
      have := one_lt_M_of_hM hk hM
      positivity
    positivity
  have hy1 : 1 ≤ ⌊y⌋₊ := by
    have : 1 < (M : ℝ) := by exact_mod_cast (one_lt_M_of_hM hk hM)
    have hrpow : 1 < (M : ℝ) ^ (1 / (k : ℝ)) := Real.one_lt_rpow this (by positivity)
    have hk1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    have : 1 < y := by
      dsimp [y]
      nlinarith
    rw [Nat.one_le_floor_iff]
    linarith
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊y⌋₊ (by omega)
  refine ⟨p, hp_prime, ?_, ?_⟩
  · have : y < (p : ℝ) := by
      have : ⌊y⌋₊ < p := hp_gt
      exact Nat.lt_of_floor_lt this
    exact this
  · have h_floor_le : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy_pos.le
    calc (p : ℝ) ≤ 2 * (⌊y⌋₊ : ℝ) := by exact_mod_cast hp_le
      _ ≤ 2 * y := by linarith
      _ ≤ 4 * y := by linarith
      _ = 4 * k * (M : ℝ) ^ (1 / (k : ℝ)) := by
        dsimp [y]
        ring

/-- Unconditional proof of exists_prime_J_le for k = 1. -/
theorem exists_prime_J_le_one (ℓ M : ℕ) (h1l : 1 ≤ ℓ) (hM : Real.exp (100 * (1 : ℝ) ^ 3) ≤ M) :
    ∃ p : ℕ, p.Prime ∧ (1 : ℝ) * (M : ℝ) ^ (1 / (1 : ℝ)) < p ∧ (p : ℝ) ≤ 4 * 1 * (M : ℝ) ^ (1 / (1 : ℝ)) ∧
      (J 1 ℓ M : ℝ) ≤ (1 : ℝ) ^ 3 * Jp 1 ℓ M p h1l + 2 * (1 : ℝ) ^ ℓ * ℓ ^ 1 * M ^ (ℓ + 1 - 1) := by
  have hM' : Real.exp (100 * ((1 : ℕ) : ℝ) ^ 3) ≤ M := by
    push_cast
    exact hM
  obtain ⟨p, hp_prime, hp_gt, hp_le⟩ := exists_prime_in_range 1 M (by omega) hM'
  push_cast at hp_gt hp_le
  refine ⟨p, hp_prime, hp_gt, hp_le, ?_⟩
  rw [Jp_one ℓ M p h1l]
  have h_nonneg : 0 ≤ 2 * (1 : ℝ) ^ ℓ * (ℓ : ℝ) ^ 1 * (M : ℝ) ^ (ℓ + 1 - 1) := by positivity
  calc (J 1 ℓ M : ℝ) = (1 : ℝ) ^ 3 * (J 1 ℓ M : ℝ) := by ring
    _ ≤ (1 : ℝ) ^ 3 * (J 1 ℓ M : ℝ) + 2 * (1 : ℝ) ^ ℓ * (ℓ : ℝ) ^ 1 * (M : ℝ) ^ (ℓ + 1 - 1) := by linarith

end Erdos1201.MR.Vinogradov
