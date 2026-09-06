/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib
import Erdos1201.MR.Setup
import Erdos1201.MR.Ramare
import Erdos1201.MR.Arithmetic
import Erdos1201.MR.Decomposition.Lemma12
import Erdos1201.MR.Analysis.MeanValueTheorem

/-!
# Lemma 12 Square-Correction Term

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

open Finset
open Complex

namespace Erdos1201.MR

lemma card_multiples_Ioc (N m : ℕ) (hm : 0 < m) :
    ((Finset.Ioc 0 N).filter (fun n => m ∣ n)).card = N / m := by
  have h_eq : (Finset.Ioc 0 N).filter (fun n => m ∣ n) = (Finset.Ioc 0 (N / m)).image (fun k => k * m) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h0, hN⟩, k, rfl⟩
      refine ⟨k, ⟨?_, ?_⟩, by ring⟩
      · cases k with
        | zero => simp at h0
        | succ k' => exact Nat.zero_lt_succ _
      · rw [mul_comm] at hN
        exact (Nat.le_div_iff_mul_le hm).mpr hN
    · rintro ⟨k, ⟨h0, hkN⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, k, by ring⟩
      · exact Nat.mul_pos h0 hm
      · have hkN' := (Nat.le_div_iff_mul_le hm).mp hkN
        omega
  rw [h_eq]
  rw [Finset.card_image_of_injective]
  · exact Nat.card_Ioc 0 (N / m)
  · intro a b hab
    exact Nat.eq_of_mul_eq_mul_right hm hab

lemma card_multiples_Ioc_le (X m : ℕ) (hm : 0 < m) :
    (((Finset.Ioc X (2 * X)).filter (fun n => m ∣ n)).card : ℝ) ≤ 2 * (X : ℝ) / (m : ℝ) := by
  have h1 : (Finset.Ioc X (2 * X)).filter (fun n => m ∣ n) ⊆ (Finset.Ioc 0 (2 * X)).filter (fun n => m ∣ n) := by
    intro n
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    rintro ⟨⟨hx, h2x⟩, hdvd⟩
    exact ⟨⟨by linarith, h2x⟩, hdvd⟩
  have h2 : ((Finset.Ioc 0 (2 * X)).filter (fun n => m ∣ n)).card = (2 * X) / m := card_multiples_Ioc (2 * X) m hm
  have h3 : (((Finset.Ioc X (2 * X)).filter (fun n => m ∣ n)).card : ℝ) ≤ (((Finset.Ioc 0 (2 * X)).filter (fun n => m ∣ n)).card : ℝ) := by
    exact Nat.cast_le.mpr (Finset.card_le_card h1)
  have h4 : (((Finset.Ioc 0 (2 * X)).filter (fun n => m ∣ n)).card : ℝ) = ((2 * X) / m : ℕ) := by rw [h2]
  have h5 : (((2 * X) / m : ℕ) : ℝ) ≤ (2 * X : ℝ) / (m : ℝ) := by
    have : (((2 * X) / m : ℕ) : ℝ) * (m : ℝ) ≤ (2 * X : ℝ) := by
      calc (((2 * X) / m : ℕ) : ℝ) * (m : ℝ) = (((2 * X) / m * m : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ (2 * X : ℝ) := by exact_mod_cast (Nat.div_mul_le_self _ _)
    exact (le_div_iff₀ (by exact_mod_cast hm)).mpr this
  linarith

lemma term_le (k : ℕ) (hk : 2 ≤ k) : 1 / (k : ℝ) ^ 2 ≤ 1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ) := by
  have h_le : 1 ≤ k := by omega
  have hk1 : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by rw [Nat.cast_sub h_le, Nat.cast_one]
  rw [hk1]
  have hpos1 : 0 < (k : ℝ) - 1 := by
    have : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 1 < k)
    linarith
  have hpos2 : 0 < (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    linarith
  have h1 : (k : ℝ) - 1 ≠ 0 := ne_of_gt hpos1
  have h2 : (k : ℝ) ≠ 0 := ne_of_gt hpos2
  have heq : 1 / ((k : ℝ) - 1) - 1 / (k : ℝ) = 1 / (((k : ℝ) - 1) * (k : ℝ)) := by
    rw [div_sub_div _ _ h1 h2, mul_one, one_mul]
    congr 1
    ring
  rw [heq]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith

lemma sum_telescope (P Q : ℕ) (hPQ : P ≤ Q) :
    ∑ k ∈ Finset.Ico P (Q + 1), (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) =
      1 / ((P - 1 : ℕ) : ℝ) - 1 / (Q : ℝ) := by
  induction Q, hPQ using Nat.le_induction with
  | base =>
    simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top (le_trans hn (Nat.le_succ _))]
    rw [ih]
    have h1 : ((n + 1 - 1 : ℕ) : ℝ) = (n : ℝ) := rfl
    rw [h1]
    push_cast
    ring

lemma sum_inv_sq_le (P Q : ℕ) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    (∑ k ∈ Finset.Ico P (Q + 1), 1 / (k : ℝ) ^ 2) ≤ 1 / ((P - 1 : ℕ) : ℝ) := by
  have H : (∑ k ∈ Finset.Ico P (Q + 1), 1 / (k : ℝ) ^ 2) ≤
      ∑ k ∈ Finset.Ico P (Q + 1), (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkP : P ≤ k := (Finset.mem_Ico.mp hk).1
    have hk2 : 2 ≤ k := le_trans hP hkP
    exact term_le k hk2
  have H2 : ∑ k ∈ Finset.Ico P (Q + 1), (1 / ((k - 1 : ℕ) : ℝ) - 1 / (k : ℝ)) =
      1 / ((P - 1 : ℕ) : ℝ) - 1 / (Q : ℝ) := sum_telescope P Q hPQ
  rw [H2] at H
  have : 1 / ((P - 1 : ℕ) : ℝ) - 1 / (Q : ℝ) ≤ 1 / ((P - 1 : ℕ) : ℝ) := by
    have : 0 ≤ 1 / (Q : ℝ) := by positivity
    linarith
  exact le_trans H this

lemma sum_inv_sq_primes_le (P Q : ℕ) (hP : 2 ≤ P) :
    (∑ p ∈ primeRange P Q, 1 / (p : ℝ) ^ 2) ≤ 2 / (P : ℝ) := by
  by_cases hPQ : P ≤ Q
  · have h_le : (∑ p ∈ primeRange P Q, 1 / (p : ℝ) ^ 2) ≤ ∑ k ∈ Finset.Ico P (Q + 1), 1 / (k : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_Ico]
        have hp_in := (Finset.mem_filter.mp hp).1
        rw [Finset.mem_Icc] at hp_in
        exact ⟨hp_in.1, by omega⟩
      · intro k _ _
        positivity
    have h_tel := sum_inv_sq_le P Q hP hPQ
    have h_frac : 1 / ((P - 1 : ℕ) : ℝ) ≤ 2 / (P : ℝ) := by
      have h_le : 1 ≤ P := by omega
      have : ((P - 1 : ℕ) : ℝ) = (P : ℝ) - 1 := by rw [Nat.cast_sub h_le, Nat.cast_one]
      rw [this]
      have : (0 : ℝ) < (P : ℝ) - 1 := by
        have : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
        linarith
      rw [div_le_div_iff₀ this (by positivity)]
      have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
      linarith
    exact le_trans h_le (le_trans h_tel h_frac)
  · have : primeRange P Q = ∅ := by
      ext p
      simp [primeRange, Finset.mem_Icc]
      intro hp hq _
      omega
    rw [this, Finset.sum_empty]
    positivity

noncomputable def sqCoeff (X P Q : ℕ) (a b c : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc X (2 * X) then
    ∑ p ∈ (primeRange P Q).filter (fun p => p ^ 2 ∣ n),
      let m := n / p
      (a n / (omegaIn (primeRange P Q) m : ℂ) - b m * c p / ((omegaIn (primeRange P Q) m : ℂ) + 1))
  else 0

lemma squareCorrection_eq_sqCoeff (X P Q : ℕ) (a b c w : ℕ → ℂ) :
    (∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
      squareCorrection (primeRange P Q) a b c w p m) =
    ∑ n ∈ Finset.Ioc 0 (2 * X), sqCoeff X P Q a b c n * w n := by
  let T := Finset.Ioc X (2 * X)
  have : (∑ p ∈ primeRange P Q, ∑ m ∈ cofactors T p, squareCorrection (primeRange P Q) a b c w p m) =
      ∑ p ∈ primeRange P Q, ∑ n ∈ T.filter (fun n => p ∣ n), squareCorrection (primeRange P Q) a b c w p (n / p) := by
    apply sum_congr rfl
    intro p hp
    have hp_pos : 0 < p := Nat.Prime.pos (mem_filter.mp hp).2
    have h_eq : (∑ m ∈ cofactors T p, squareCorrection (primeRange P Q) a b c w p m) = ∑ m ∈ cofactors T p, squareCorrection (primeRange P Q) a b c w p (p * m / p) := by
      apply sum_congr rfl
      intro m _
      rw [Nat.mul_div_cancel_left m hp_pos]
    rw [h_eq]
    exact sum_cofactors T p (fun n => squareCorrection (primeRange P Q) a b c w p (n / p))
  rw [this]
  have h_swap : (∑ p ∈ primeRange P Q, ∑ n ∈ T.filter (fun n => p ∣ n), squareCorrection (primeRange P Q) a b c w p (n / p)) =
      ∑ n ∈ T, ∑ p ∈ (primeRange P Q).filter (fun p => p ∣ n), squareCorrection (primeRange P Q) a b c w p (n / p) := by
    calc
      _ = ∑ p ∈ primeRange P Q, ∑ n ∈ T, if p ∣ n then squareCorrection (primeRange P Q) a b c w p (n / p) else 0 := by
        apply sum_congr rfl
        intro p _
        rw [sum_filter]
      _ = ∑ n ∈ T, ∑ p ∈ primeRange P Q, if p ∣ n then squareCorrection (primeRange P Q) a b c w p (n / p) else 0 := sum_comm
      _ = ∑ n ∈ T, ∑ p ∈ (primeRange P Q).filter (fun p => p ∣ n), squareCorrection (primeRange P Q) a b c w p (n / p) := by
        apply sum_congr rfl
        intro n _
        rw [sum_filter]
  rw [h_swap]
  have h_inner : ∀ n ∈ T, (∑ p ∈ (primeRange P Q).filter (fun p => p ∣ n), squareCorrection (primeRange P Q) a b c w p (n / p)) =
      sqCoeff X P Q a b c n * w n := by
    intro n hn
    have hn_Ioc : n ∈ Finset.Ioc X (2 * X) := hn
    unfold sqCoeff
    rw [if_pos hn_Ioc]
    have h_eq : (primeRange P Q).filter (fun p => p ^ 2 ∣ n) = ((primeRange P Q).filter (fun p => p ∣ n)).filter (fun p => p ∣ n / p) := by
      ext p
      simp only [mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        have h2' : p * p ∣ n := by simpa [sq] using h2
        refine ⟨⟨h1, dvd_trans ⟨p, rfl⟩ h2'⟩, ?_⟩
        exact Nat.dvd_div_of_mul_dvd h2'
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, ?_⟩
        have h_mul := Nat.mul_dvd_of_dvd_div h2 h3
        simpa [sq] using h_mul
    rw [h_eq]
    conv_rhs => rw [sum_filter, Finset.sum_mul]
    apply sum_congr rfl
    intro p hp
    have hdiv : p ∣ n := (mem_filter.mp hp).2
    have hpn : p * (n / p) = n := Nat.mul_div_cancel' hdiv
    unfold squareCorrection
    split_ifs with h_p_dvd_m
    · rw [hpn]
      ring
    · simp
  have h_T_eq : (∑ n ∈ T, sqCoeff X P Q a b c n * w n) = ∑ n ∈ Finset.Ioc 0 (2 * X), sqCoeff X P Q a b c n * w n := by
    apply sum_subset
    · intro n hn
      have h1 : X < n := (mem_Ioc.mp hn).1
      exact mem_Ioc.mpr ⟨lt_of_le_of_lt (Nat.zero_le X) h1, (mem_Ioc.mp hn).2⟩
    · intro n _hn hnT
      unfold sqCoeff
      have hnot : n ∉ Finset.Ioc X (2 * X) := hnT
      simp [hnot]
  rw [← h_T_eq]
  exact sum_congr rfl h_inner

lemma norm_term_le_two (S : Finset ℕ) (a b c : ℕ → ℂ) (n p m : ℕ) (ha : ‖a n‖ ≤ 1) (hb : ‖b m‖ ≤ 1) (hc : ‖c p‖ ≤ 1)
    (h_omega : 1 ≤ omegaIn S m) :
    ‖a n / (omegaIn S m : ℂ) - b m * c p / ((omegaIn S m : ℂ) + 1)‖ ≤ 2 := by
  have H1 : ‖a n / (omegaIn S m : ℂ)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast]
    have hw_pos : 1 ≤ (omegaIn S m : ℝ) := by exact_mod_cast h_omega
    calc ‖a n‖ / (omegaIn S m : ℝ) ≤ 1 / (omegaIn S m : ℝ) := div_le_div_of_nonneg_right ha (by positivity)
      _ ≤ 1 / 1 := one_div_le_one_div_of_le zero_lt_one hw_pos
      _ = 1 := by ring
  have H2 : ‖b m * c p / ((omegaIn S m : ℂ) + 1)‖ ≤ 1 := by
    rw [norm_div, norm_mul]
    have hn1 : ‖(omegaIn S m : ℂ) + 1‖ = (omegaIn S m : ℝ) + 1 := by
      calc ‖(omegaIn S m : ℂ) + 1‖ = ‖((omegaIn S m + 1 : ℕ) : ℂ)‖ := by push_cast; rfl
        _ = ((omegaIn S m + 1 : ℕ) : ℝ) := by exact_mod_cast Complex.norm_natCast (omegaIn S m + 1)
        _ = (omegaIn S m : ℝ) + 1 := by push_cast; rfl
    rw [hn1]
    have hb1 : ‖b m‖ ≤ 1 := hb
    have hc1 : ‖c p‖ ≤ 1 := hc
    have hw1 : 1 ≤ (omegaIn S m : ℝ) + 1 := by
      have : 0 ≤ (omegaIn S m : ℝ) := Nat.cast_nonneg _
      linarith
    have hterm2 : ‖b m‖ * ‖c p‖ / ((omegaIn S m : ℝ) + 1) ≤ 1 := by
      calc ‖b m‖ * ‖c p‖ / ((omegaIn S m : ℝ) + 1) ≤ 1 * 1 / ((omegaIn S m : ℝ) + 1) := div_le_div_of_nonneg_right (mul_le_mul hb hc (by positivity) (by norm_num)) (by positivity)
        _ ≤ 1 / 1 := by
          rw [mul_one]
          exact one_div_le_one_div_of_le zero_lt_one hw1
        _ = 1 := by ring
    exact hterm2
  have hsub := norm_sub_le (a n / (omegaIn S m : ℂ)) (b m * c p / ((omegaIn S m : ℂ) + 1))
  linarith

lemma sqCoeff_norm_sq_le (X P Q : ℕ) (a b c : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (n : ℕ) :
    ‖sqCoeff X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 ≤
      if n ∈ Finset.Ioc X (2 * X) then 4 / (X : ℝ) ^ 2 * (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) ^ 2 else 0 := by
  dsimp [sqCoeff]
  split_ifs with hn
  · have h_norm : ‖∑ p ∈ (primeRange P Q).filter (fun p : ℕ => p ^ 2 ∣ n), (a n / (omegaIn (primeRange P Q) (n / p) : ℂ) - b (n / p) * c p / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1))‖ ≤
        2 * (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) := by
      have h_sum := norm_sum_le ((primeRange P Q).filter (fun p => p ^ 2 ∣ n)) (fun p => a n / (omegaIn (primeRange P Q) (n / p) : ℂ) - b (n / p) * c p / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1))
      refine h_sum.trans ?_
      have h_inner : ∀ p ∈ (primeRange P Q).filter (fun p => p ^ 2 ∣ n),
          ‖a n / (omegaIn (primeRange P Q) (n / p) : ℂ) - b (n / p) * c p / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1)‖ ≤ 2 := by
        intro p hp
        have h_p2_dvd : p ^ 2 ∣ n := (mem_filter.mp hp).2
        have h_p_dvd : p ∣ (n / p) := by
          have h_pp_dvd : p * p ∣ n := by simpa [sq] using h_p2_dvd
          exact Nat.dvd_div_of_mul_dvd h_pp_dvd
        have hp_in : p ∈ primeRange P Q := (mem_filter.mp hp).1
        have h_omega : 1 ≤ omegaIn (primeRange P Q) (n / p) := omegaIn_pos_of_selected_dvd hp_in h_p_dvd
        exact norm_term_le_two (primeRange P Q) a b c n p (n / p) (ha n) (hb _) (hc p) h_omega
      have := Finset.sum_le_sum h_inner
      simp only [Finset.sum_const, nsmul_eq_mul] at this
      rw [mul_comm] at this
      exact this
    have h_sq : ‖∑ p ∈ (primeRange P Q).filter (fun p => p ^ 2 ∣ n), (a n / (omegaIn (primeRange P Q) (n / p) : ℂ) - b (n / p) * c p / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1))‖ ^ 2 ≤
      (2 * (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ)) ^ 2 := by
      gcongr
    have h_sq_eq : (2 * (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ)) ^ 2 = 4 * (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) ^ 2 := by ring
    rw [h_sq_eq] at h_sq
    have h_div : 1 / (n : ℝ) ^ 2 ≤ 1 / (X : ℝ) ^ 2 := by
      have hn_gt : (X : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1.le
      have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by linarith [mem_Ioc.mp hn |>.1, mem_Ioc.mp hn |>.2] : 0 < X)
      have hX_pos_le : 0 ≤ (X : ℝ) := hX_pos.le
      have hX2_pos : 0 < (X : ℝ) ^ 2 := pow_pos hX_pos 2
      apply one_div_le_one_div_of_le hX2_pos
      exact pow_le_pow_left₀ hX_pos_le hn_gt 2
    calc ‖∑ p ∈ (primeRange P Q).filter (fun p => p ^ 2 ∣ n), (a n / (omegaIn (primeRange P Q) (n / p) : ℂ) - b (n / p) * c p / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1))‖ ^ 2 / (n : ℝ) ^ 2
      _ ≤ (4 * (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) ^ 2) * (1 / (n : ℝ) ^ 2) := by
        rw [div_eq_mul_one_div]
        gcongr
      _ ≤ (4 * (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) ^ 2) * (1 / (X : ℝ) ^ 2) := by
        gcongr
      _ = 4 / (X : ℝ) ^ 2 * (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) ^ 2 := by ring
  · simp

lemma sum_omega2_sq_le (X P Q : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ioc X (2 * X), (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) ^ 2) ≤
      2 * (X : ℝ) * (∑ p ∈ primeRange P Q, 1 / (p : ℝ) ^ 2) +
      2 * (X : ℝ) * (∑ p ∈ primeRange P Q, 1 / (p : ℝ) ^ 2) ^ 2 := by
  calc
    (∑ n ∈ Finset.Ioc X (2 * X), (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) ^ 2)
      = ∑ n ∈ Finset.Ioc X (2 * X), (∑ p ∈ primeRange P Q, if p ^ 2 ∣ n then (1 : ℝ) else 0) ^ 2 := by
        congr 1
        ext n
        have h_card : (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) = ∑ p ∈ primeRange P Q, if p ^ 2 ∣ n then (1 : ℝ) else 0 := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
          congr 1; ext p; split_ifs <;> simp
        rw [h_card]
      _ = ∑ n ∈ Finset.Ioc X (2 * X), ∑ p ∈ primeRange P Q, ∑ q ∈ primeRange P Q,
            (if p ^ 2 ∣ n then (1 : ℝ) else 0) * (if q ^ 2 ∣ n then (1 : ℝ) else 0) := by
        congr 1; ext n
        rw [sq, Finset.sum_mul_sum]
      _ = ∑ p ∈ primeRange P Q, ∑ q ∈ primeRange P Q, ∑ n ∈ Finset.Ioc X (2 * X),
            (if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        congr 1
        ext p
        rw [Finset.sum_comm]
        congr 1
        ext q
        apply Finset.sum_congr rfl
        intro n _
        by_cases h1 : p ^ 2 ∣ n <;> by_cases h2 : q ^ 2 ∣ n <;> simp [h1, h2]
      _ = (∑ p ∈ primeRange P Q, ∑ n ∈ Finset.Ioc X (2 * X), if p ^ 2 ∣ n then (1 : ℝ) else 0) +
          (∑ p ∈ primeRange P Q, ∑ q ∈ (primeRange P Q).erase p, ∑ n ∈ Finset.Ioc X (2 * X), if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0) := by
        have h_inner : ∀ p ∈ primeRange P Q,
            (∑ q ∈ primeRange P Q, ∑ n ∈ Finset.Ioc X (2 * X), if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0) =
            (∑ n ∈ Finset.Ioc X (2 * X), if p ^ 2 ∣ n then (1 : ℝ) else 0) +
            (∑ q ∈ (primeRange P Q).erase p, ∑ n ∈ Finset.Ioc X (2 * X), if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0) := by
          intro p hp
          rw [← Finset.add_sum_erase _ _ hp]
          congr 1
          apply Finset.sum_congr rfl
          intro n _
          simp only [and_self]
        rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib]
      _ ≤ 2 * (X : ℝ) * (∑ p ∈ primeRange P Q, 1 / (p : ℝ) ^ 2) +
          2 * (X : ℝ) * (∑ p ∈ primeRange P Q, 1 / (p : ℝ) ^ 2) ^ 2 := by
        apply add_le_add
        · have h_inner : ∀ p ∈ primeRange P Q, (∑ n ∈ Finset.Ioc X (2 * X), if p ^ 2 ∣ n then (1 : ℝ) else 0) ≤ 2 * (X : ℝ) / (p : ℝ) ^ 2 := by
            intro p hp
            have h1 : (∑ n ∈ Finset.Ioc X (2 * X), if p ^ 2 ∣ n then (1 : ℝ) else 0) = (((Finset.Ioc X (2 * X)).filter (fun n => p ^ 2 ∣ n)).card : ℝ) := by
              rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
              congr 1; ext n; split_ifs <;> push_cast <;> rfl
            rw [h1]
            have hp2 : 0 < p ^ 2 := sq_pos_of_pos (Nat.Prime.pos (mem_filter.mp hp).2)
            have := card_multiples_Ioc_le X (p ^ 2) hp2
            have hcast : ((p ^ 2 : ℕ) : ℝ) = (p : ℝ) ^ 2 := by push_cast; rfl
            rw [hcast] at this
            exact this
          have h_sum := Finset.sum_le_sum h_inner
          refine h_sum.trans_eq ?_
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _
          ring
        · have h_inner : ∀ p ∈ primeRange P Q, ∀ q ∈ (primeRange P Q).erase p,
              (∑ n ∈ Finset.Ioc X (2 * X), if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0) ≤ 2 * (X : ℝ) / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
            intro p hp q hq
            have hp_prime := (mem_filter.mp hp).2
            have hq_prime := (mem_filter.mp (mem_erase.mp hq).2).2
            have hpq_ne : p ≠ q := (mem_erase.mp hq).1.symm
            have h_lcm : ∀ n, p ^ 2 ∣ n ∧ q ^ 2 ∣ n ↔ p ^ 2 * q ^ 2 ∣ n := by
              intro n
              have hc : (p ^ 2).Coprime (q ^ 2) := Nat.Coprime.pow _ _ (hp_prime.coprime_iff_not_dvd.mpr (fun h => hpq_ne ((Nat.Prime.eq_one_or_self_of_dvd hq_prime p h).resolve_left hp_prime.ne_one)))
              constructor
              · rintro ⟨h1, h2⟩
                exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hc h1 h2
              · intro h
                exact ⟨dvd_trans ⟨q^2, rfl⟩ h, dvd_trans ⟨p^2, mul_comm _ _⟩ h⟩
            have h1 : (∑ n ∈ Finset.Ioc X (2 * X), if p ^ 2 ∣ n ∧ q ^ 2 ∣ n then (1 : ℝ) else 0) = (((Finset.Ioc X (2 * X)).filter (fun n => p ^ 2 * q ^ 2 ∣ n)).card : ℝ) := by
              simp only [h_lcm]
              have h_card : (((Finset.Ioc X (2 * X)).filter (fun n => p ^ 2 * q ^ 2 ∣ n)).card : ℝ) = (∑ n ∈ Finset.Ioc X (2 * X), if p ^ 2 * q ^ 2 ∣ n then 1 else 0 : ℕ) := by
                rw [Finset.card_eq_sum_ones, Finset.sum_filter]
              rw [h_card, Nat.cast_sum]
              congr 1; ext n; split_ifs <;> simp
            rw [h1]
            have hm : 0 < p ^ 2 * q ^ 2 := mul_pos (sq_pos_of_pos hp_prime.pos) (sq_pos_of_pos hq_prime.pos)
            have := card_multiples_Ioc_le X (p ^ 2 * q ^ 2) hm
            have hcast : ((p ^ 2 * q ^ 2 : ℕ) : ℝ) = (p : ℝ) ^ 2 * (q : ℝ) ^ 2 := by push_cast; rfl
            rw [hcast] at this
            exact this
          have h_sum := Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => h_inner p hp q hq))
          refine h_sum.trans ?_
          have h_le3 : (∑ p ∈ primeRange P Q, ∑ q ∈ (primeRange P Q).erase p, 2 * (X : ℝ) / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2)) ≤
              ∑ p ∈ primeRange P Q, ∑ q ∈ primeRange P Q, 2 * (X : ℝ) / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2) := by
            apply Finset.sum_le_sum
            intro p hp
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.erase_subset p _
            · intro q hq1 hq2
              positivity
          refine h_le3.trans_eq ?_
          calc (∑ p ∈ primeRange P Q, ∑ q ∈ primeRange P Q, 2 * (X : ℝ) / ((p : ℝ) ^ 2 * (q : ℝ) ^ 2))
            _ = 2 * (X : ℝ) * ∑ p ∈ primeRange P Q, ∑ q ∈ primeRange P Q, (1 / (p : ℝ) ^ 2) * (1 / (q : ℝ) ^ 2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro q _
              ring
            _ = 2 * (X : ℝ) * (∑ p ∈ primeRange P Q, 1 / (p : ℝ) ^ 2) ^ 2 := by
              rw [← Finset.sum_mul_sum]
              ring

theorem integral_norm_sq_squareCorrection_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X P Q : ℕ) (a b c : ℕ → ℂ) (T : ℝ) (U : Set ℝ),
      1 ≤ X → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ X → 0 ≤ T → MeasurableSet U → U ⊆ Set.Icc (-T) T →
      (∀ n, ‖a n‖ ≤ 1) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (P : ℝ) ^ 4 ≤ X →
      ∫ t in U, ‖∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
            squareCorrection (primeRange P Q) a b c (fun n => (n : ℂ) ^ (-((1 : ℂ) + t * Complex.I))) p m‖ ^ 2 ≤
        C * (T / X + 1) / P := by
  use 32 * (36 * Real.pi + 2)
  constructor
  · have : 0 < Real.pi := Real.pi_pos
    positivity
  · intro X P Q a b c T U hX hP hPQ hQX hT hU hsub ha hb hc hP4
    have h_coeff : ∀ t : ℝ,
        (∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
          squareCorrection (primeRange P Q) a b c (fun n => (n : ℂ) ^ (-((1 : ℂ) + (t : ℂ) * Complex.I))) p m) =
        dirichletPoly (sqCoeff X P Q a b c) (Finset.Ioc 0 (2 * X)) ((1 : ℂ) + t * Complex.I) := by
      intro t
      rw [squareCorrection_eq_sqCoeff]
      unfold dirichletPoly
      rfl
    have h_fun_eq : (fun t : ℝ => ‖∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
            squareCorrection (primeRange P Q) a b c (fun n => (n : ℂ) ^ (-((1 : ℂ) + (t : ℂ) * Complex.I))) p m‖ ^ 2) =
        (fun t : ℝ => ‖dirichletPoly (sqCoeff X P Q a b c) (Finset.Ioc 0 (2 * X)) ((1 : ℂ) + t * Complex.I)‖ ^ 2) := by
      ext t
      rw [h_coeff t]
    rw [h_fun_eq]
    have h_int_le := setIntegral_norm_sq_dirichletPoly_le (sqCoeff X P Q a b c) (Finset.Ioc 0 (2 * X)) (by
      intro n hn
      exact (mem_Ioc.mp hn).1) T hT U hU hsub
    have h_mvt := integral_norm_sq_dirichletPoly_subset_le (sqCoeff X P Q a b c) (Finset.Ioc 0 (2 * X)) (2 * X) (by rfl) T hT
    have h_total_int := le_trans h_int_le h_mvt
    have h_sum_le : (∑ n ∈ Finset.Ioc 0 (2 * X), ‖sqCoeff X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2) ≤
        (∑ n ∈ Finset.Ioc X (2 * X), 4 / (X : ℝ) ^ 2 * (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) ^ 2) := by
      have h1 : (∑ n ∈ Finset.Ioc 0 (2 * X), ‖sqCoeff X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2) =
          ∑ n ∈ Finset.Ioc X (2 * X), ‖sqCoeff X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
        apply (Finset.sum_subset _ _).symm
        · intro n hn
          exact mem_Ioc.mpr ⟨by linarith [mem_Ioc.mp hn |>.1], mem_Ioc.mp hn |>.2⟩
        · intro n _hn hnot
          have : sqCoeff X P Q a b c n = 0 := by
            dsimp [sqCoeff]
            simp [hnot]
          simp [this]
      rw [h1]
      apply Finset.sum_le_sum
      intro n hn
      have := sqCoeff_norm_sq_le X P Q a b c ha hb hc n
      simp [hn] at this
      exact this
    have h_omega2_le := sum_omega2_sq_le X P Q hX
    have h_prime_sum := sum_inv_sq_primes_le P Q hP
    have h_sum_le2 : (∑ n ∈ Finset.Ioc X (2 * X), 4 / (X : ℝ) ^ 2 * (((primeRange P Q).filter (fun p => p ^ 2 ∣ n)).card : ℝ) ^ 2) ≤
        4 / (X : ℝ) ^ 2 * (2 * (X : ℝ) * (2 / (P : ℝ)) + 2 * (X : ℝ) * (2 / (P : ℝ)) ^ 2) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left
      · refine h_omega2_le.trans ?_
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left h_prime_sum (by positivity)
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h_prime_sum 2) (by positivity)
      · positivity
    have h_factor_le := montgomery_factor_le T X (2 * (X : ℝ)) hT (by exact_mod_cast hX) (by linarith)
    have h_total_int' : (∫ t in U, ‖dirichletPoly (sqCoeff X P Q a b c) (Finset.Ioc 0 (2 * X)) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        (2 * T + 6 * Real.pi * (2 * (X : ℝ))) * ∑ n ∈ Finset.Ioc 0 (2 * X), ‖sqCoeff X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2 := by
      have h_cast : ((2 * X : ℕ) : ℝ) = 2 * (X : ℝ) := by push_cast; rfl
      rw [h_cast] at h_total_int
      exact h_total_int
    have h_rhs_simplify : 4 / (X : ℝ) ^ 2 * (2 * (X : ℝ) * (2 / (P : ℝ)) + 2 * (X : ℝ) * (2 / (P : ℝ)) ^ 2) =
        (8 / (X : ℝ)) * (2 / (P : ℝ) + 4 / (P : ℝ) ^ 2) := by
      have hX_pos : (X : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : 0 < X))
      calc 4 / (X : ℝ) ^ 2 * (2 * (X : ℝ) * (2 / (P : ℝ)) + 2 * (X : ℝ) * (2 / (P : ℝ)) ^ 2)
        _ = 4 / ((X : ℝ) * (X : ℝ)) * ((X : ℝ) * (4 / (P : ℝ) + 8 / (P : ℝ) ^ 2)) := by rw [sq]; ring
        _ = (4 / ((X : ℝ) * (X : ℝ)) * (X : ℝ)) * (4 / (P : ℝ) + 8 / (P : ℝ) ^ 2) := by rw [mul_assoc]
        _ = ((4 * (X : ℝ)) / ((X : ℝ) * (X : ℝ))) * (4 / (P : ℝ) + 8 / (P : ℝ) ^ 2) := by rw [div_mul_eq_mul_div]
        _ = ((4 * (X : ℝ)) / (X : ℝ) / (X : ℝ)) * (4 / (P : ℝ) + 8 / (P : ℝ) ^ 2) := by rw [div_mul_eq_div_div]
        _ = (4 / (X : ℝ)) * (4 / (P : ℝ) + 8 / (P : ℝ) ^ 2) := by rw [mul_div_cancel_right₀ 4 hX_pos]
        _ = (8 / (X : ℝ)) * (2 / (P : ℝ) + 4 / (P : ℝ) ^ 2) := by ring
    have h_P_bound : 2 / (P : ℝ) + 4 / (P : ℝ) ^ 2 ≤ 4 / (P : ℝ) := by
      have : 4 / (P : ℝ) ^ 2 ≤ 2 / (P : ℝ) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc 4 * (P : ℝ) = 2 * (2 * (P : ℝ)) := by ring
          _ ≤ 2 * ((P : ℝ) * (P : ℝ)) := by
            apply mul_le_mul_of_nonneg_left
            · nlinarith [show 2 ≤ (P : ℝ) by exact_mod_cast hP]
            · positivity
          _ = 2 * (P : ℝ) ^ 2 := by ring
      calc 2 / (P : ℝ) + 4 / (P : ℝ) ^ 2 ≤ 2 / (P : ℝ) + 2 / (P : ℝ) := add_le_add (le_refl _) this
        _ = 4 / (P : ℝ) := by ring
    have h_sum_le_final : (∑ n ∈ Finset.Ioc 0 (2 * X), ‖sqCoeff X P Q a b c n‖ ^ 2 / (n : ℝ) ^ 2) ≤
        32 / ((X : ℝ) * (P : ℝ)) := by
      refine h_sum_le.trans (h_sum_le2.trans ?_)
      rw [h_rhs_simplify]
      have : (8 / (X : ℝ)) * (2 / (P : ℝ) + 4 / (P : ℝ) ^ 2) ≤ (8 / (X : ℝ)) * (4 / (P : ℝ)) := by
        exact mul_le_mul_of_nonneg_left h_P_bound (by positivity)
      refine this.trans_eq ?_
      ring
    refine h_total_int'.trans ?_
    have h_mul_le := mul_le_mul h_factor_le h_sum_le_final (by positivity) (by positivity)
    refine h_mul_le.trans_eq ?_
    calc
      (36 * Real.pi + 2) * (X : ℝ) * (T / (X : ℝ) + 1) * (32 / ((X : ℝ) * (P : ℝ)))
      _ = 32 * (36 * Real.pi + 2) * (T / (X : ℝ) + 1) * ((X : ℝ) / ((X : ℝ) * (P : ℝ))) := by ring
      _ = 32 * (36 * Real.pi + 2) * (T / (X : ℝ) + 1) * (1 / (P : ℝ)) := by
        have hX_pos : (X : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (by linarith : 0 < X))
        rw [div_mul_eq_div_div, div_self hX_pos]
      _ = 32 * (36 * Real.pi + 2) * (T / (X : ℝ) + 1) / (P : ℝ) := by ring

end Erdos1201.MR
