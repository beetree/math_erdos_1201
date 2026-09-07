/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gemini

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.MR.Twisted.TwistedPsi
import Erdos1201.MR.Twisted.TwistedPrimeSums

open Complex Real MeasureTheory
open scoped Classical

namespace Erdos1201.MR

/-!
### Prime-power extraction lemmas
-/

lemma nonprime_primepow_in_image (A B : ℕ) (n : ℕ) (hn : n ∈ Finset.Ioc A B)
    (hpp : IsPrimePow n) (hnotp : ¬ Nat.Prime n) :
    ∃ (p k : ℕ), (p, k) ∈ (Finset.Icc 1 (Nat.sqrt B)) ×ˢ (Finset.Icc 2 (Nat.log 2 B)) ∧ p ^ k = n := by
  rw [isPrimePow_nat_iff] at hpp
  obtain ⟨p, k, hp, hk_pos, rfl⟩ := hpp
  rw [Finset.mem_Ioc] at hn
  have hk_ge2 : 2 ≤ k := by
    by_contra hlt
    have : k ≤ 1 := by omega
    have : k = 1 := by omega
    subst this
    rw [pow_one] at hnotp
    exact hnotp hp
  have hp_ge2 : 2 ≤ p := hp.two_le
  have hp_ge1 : 1 ≤ p := by omega
  have hp2_le : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk_ge2
  have hp2_le_B : p ^ 2 ≤ B := le_trans hp2_le hn.2
  have hp_le_sqrt : p ≤ Nat.sqrt B := by
    apply Nat.le_sqrt.mpr
    rwa [← sq]
  have h2k_le : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp_ge2 k
  have h2k_le_B : 2 ^ k ≤ B := le_trans h2k_le hn.2
  have hk_le_log : k ≤ Nat.log 2 B := Nat.le_log_of_pow_le (by norm_num) h2k_le_B
  refine ⟨p, k, ?_, rfl⟩
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨hp_ge1, hp_le_sqrt⟩, ⟨hk_ge2, hk_le_log⟩⟩

lemma card_nonprime_primepow_le (A B : ℕ) :
    ((Finset.Ioc A B).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)).card ≤ (Nat.sqrt B) * (Nat.log 2 B) := by
  let S := (Finset.Ioc A B).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)
  let P := (Finset.Icc 1 (Nat.sqrt B)) ×ˢ (Finset.Icc 2 (Nat.log 2 B))
  let f : ℕ × ℕ → ℕ := fun (p, k) => p ^ k
  have h_sub : S ⊆ P.image f := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨p, k, hpk, heq⟩ := nonprime_primepow_in_image A B n hn.1 hn.2.1 hn.2.2
    rw [Finset.mem_image]
    exact ⟨(p, k), hpk, heq⟩
  have h_card_S : S.card ≤ (P.image f).card := Finset.card_le_card h_sub
  have h_card_im : (P.image f).card ≤ P.card := Finset.card_image_le
  refine le_trans (le_trans h_card_S h_card_im) ?_
  rw [Finset.card_product, Nat.card_Icc]
  have h1 : Nat.sqrt B + 1 - 1 = Nat.sqrt B := by omega
  rw [h1]
  have h2 : (Finset.Icc 2 (Nat.log 2 B)).card ≤ Nat.log 2 B := by
    rw [Nat.card_Icc]
    omega
  exact Nat.mul_le_mul_left _ h2

lemma sum_inv_le_card_div {A : ℕ} (hA : 0 < A)
    (S : Finset ℕ) (hS : ∀ n ∈ S, A < n) :
    ∑ n ∈ S, (n : ℝ)⁻¹ ≤ (S.card : ℝ) / (A : ℝ) := by
  have hA_pos : 0 < (A : ℝ) := by positivity
  have h_term : ∀ n ∈ S, (n : ℝ)⁻¹ ≤ (A : ℝ)⁻¹ := by
    intro n hn
    have hn_gt : (A : ℝ) < (n : ℝ) := by exact_mod_cast (hS n hn)
    have hn_pos : 0 < (n : ℝ) := lt_trans hA_pos hn_gt
    exact (inv_le_inv₀ hn_pos hA_pos).mpr hn_gt.le
  have h_sum := Finset.sum_le_sum h_term
  refine le_trans h_sum ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv]

lemma norm_f_mul_c_le (u : ℝ) (n : ℕ) (hn : 3 ≤ n) :
    let c : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)
    let f : ℝ → ℂ := fun t => ((t : ℂ) * (Real.log t : ℂ))⁻¹
    ‖f (n : ℝ) * c n‖ ≤ (n : ℝ)⁻¹ := by
  intro c f
  dsimp [c, f]
  have hn_real : 3 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hn_gt1 : 1 < (n : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt1
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hlog_pos.le]
  have h_norm_cpow : ‖(n : ℂ) ^ (-(u : ℂ) * Complex.I)‖ = 1 := by
    have : (n : ℂ) = ((n : ℝ) : ℂ) := by simp
    rw [this]
    exact Erdos1201.MR.norm_cpow_neg_mul_I (u := u) hn_pos
  have h_norm_vm : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
    rw [Complex.norm_real, Real.norm_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))]
  rw [norm_mul, h_norm_cpow, mul_one, h_norm_vm]
  have h_vm_le := ArithmeticFunction.vonMangoldt_le_log (n := n)
  have h_mul : ((n : ℝ) * Real.log (n : ℝ))⁻¹ * ArithmeticFunction.vonMangoldt n =
      (ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)) * (n : ℝ)⁻¹ := by
    rw [mul_inv]
    ring
  rw [h_mul]
  have h_div_le : ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ) ≤ 1 := by
    rw [div_le_one₀ hlog_pos]
    exact h_vm_le
  calc (ArithmeticFunction.vonMangoldt n / Real.log (n : ℝ)) * (n : ℝ)⁻¹
      ≤ 1 * (n : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h_div_le (by positivity)
    _ = (n : ℝ)⁻¹ := one_mul _

lemma sum_split_primes (u : ℝ) (A B : ℕ) (hA : 3 ≤ A) :
    let c : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)
    let f : ℝ → ℂ := fun t => ((t : ℂ) * (Real.log t : ℂ))⁻¹
    let P := (Finset.Ioc A B).filter Nat.Prime
    let PP := (Finset.Ioc A B).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)
    ∑ n ∈ Finset.Ioc A B, f (n : ℝ) * c n - ∑ p ∈ P, (p : ℂ) ^ (-((1 : ℂ) + (u : ℂ) * Complex.I)) =
      ∑ n ∈ PP, f (n : ℝ) * c n := by
  intro c f P PP
  let S := Finset.Ioc A B
  have h_split1 : ∑ n ∈ S, f (n : ℝ) * c n =
      (∑ n ∈ S.filter IsPrimePow, f (n : ℝ) * c n) +
      (∑ n ∈ S.filter (fun n => ¬ IsPrimePow n), f (n : ℝ) * c n) := by
    rw [← Finset.sum_filter_add_sum_filter_not S IsPrimePow]
  have h_zero : ∑ n ∈ S.filter (fun n => ¬ IsPrimePow n), f (n : ℝ) * c n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [Finset.mem_filter] at hn
    dsimp [c, f]
    have hvm : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn.2
    simp [hvm]
  rw [h_zero, add_zero] at h_split1
  have h_split2 : ∑ n ∈ S.filter IsPrimePow, f (n : ℝ) * c n =
      (∑ n ∈ (S.filter IsPrimePow).filter Nat.Prime, f (n : ℝ) * c n) +
      (∑ n ∈ (S.filter IsPrimePow).filter (fun n => ¬ Nat.Prime n), f (n : ℝ) * c n) := by
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter IsPrimePow) Nat.Prime]
  have h_P_eq : (S.filter IsPrimePow).filter Nat.Prime = P := by
    ext n
    simp only [Finset.mem_filter, P, S]
    constructor
    · rintro ⟨⟨hn, _⟩, hp⟩; exact ⟨hn, hp⟩
    · rintro ⟨hn, hp⟩; exact ⟨⟨hn, hp.isPrimePow⟩, hp⟩
  have h_PP_eq : (S.filter IsPrimePow).filter (fun n => ¬ Nat.Prime n) = PP := by
    ext n
    simp only [Finset.mem_filter, PP, S]
    tauto
  rw [h_P_eq, h_PP_eq] at h_split2
  rw [h_split2] at h_split1
  have h_P_terms : ∑ n ∈ P, f (n : ℝ) * c n = ∑ p ∈ P, (p : ℂ) ^ (-((1 : ℂ) + (u : ℂ) * Complex.I)) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp3 : 3 ≤ p := by omega
    dsimp [c, f]
    have hp_real : 3 ≤ (p : ℝ) := by exact_mod_cast hp3
    have hp_pos : 0 < (p : ℝ) := by linarith
    have hp_gt1 : 1 < (p : ℝ) := by linarith
    have hlog_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt1
    have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hp.2.pos)
    have hlog_ne : (Real.log (p : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hlog_pos)
    have hvm : (ArithmeticFunction.vonMangoldt p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2, ofReal_log hp_pos.le]
    rw [hvm]
    have h_cpow : (p : ℂ) ^ (-((1 : ℂ) + (u : ℂ) * Complex.I)) =
        (p : ℂ)⁻¹ * (p : ℂ) ^ (-(u : ℂ) * Complex.I) := by
      rw [show -((1 : ℂ) + (u : ℂ) * Complex.I) = -1 + -(u : ℂ) * Complex.I by ring]
      rw [cpow_add _ _ hp_ne, cpow_neg_one]
    rw [h_cpow]
    have h_cancel : ((p : ℂ) * (Real.log (p : ℝ) : ℂ))⁻¹ * ((Real.log (p : ℝ) : ℂ) * (p : ℂ) ^ (-(u : ℂ) * Complex.I)) =
        ((Real.log (p : ℝ) : ℂ)⁻¹ * (Real.log (p : ℝ) : ℂ)) * ((p : ℂ)⁻¹ * (p : ℂ) ^ (-(u : ℂ) * Complex.I)) := by
      rw [mul_inv]
      ring
    rw [h_cancel, inv_mul_cancel₀ hlog_ne, one_mul]
  rw [h_P_terms] at h_split1
  rw [h_split1]
  ring

lemma log_two_mul_le_tpf {A : ℕ} (hA : 3 ≤ A) : Real.log (2 * (A : ℝ)) ≤ 2 * Real.log (A : ℝ) := by
  have hA_pos : 0 < (A : ℝ) := by positivity
  have h2A_le : 2 * (A : ℝ) ≤ (A : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast (by omega)
    calc 2 * (A : ℝ) ≤ (A : ℝ) * (A : ℝ) := mul_le_mul_of_nonneg_right this hA_pos.le
      _ = (A : ℝ) ^ 2 := by ring
  have hlog := Real.log_le_log (by positivity) h2A_le
  refine le_trans hlog ?_
  rw [Real.log_pow, Nat.cast_two]

lemma exp_neg_half_le {y c : ℝ} (hy : 1 ≤ y) (hc_pos : 0 < c) (hc : c ≤ 1 / 4) :
    Real.exp (- (y / 2)) ≤ Real.exp (- (y / 4)) * Real.exp (- c * y ^ (1 / 16 : ℝ)) := by
  have hy16 : y ^ (1 / 16 : ℝ) ≤ y := Erdos1201.MR.rpow_le_rpow_of_exponent_le_one hy
  have hc_mul : c * y ^ (1 / 16 : ℝ) ≤ y / 4 := by
    calc c * y ^ (1 / 16 : ℝ) ≤ c * y := mul_le_mul_of_nonneg_left hy16 hc_pos.le
      _ ≤ (1 / 4) * y := mul_le_mul_of_nonneg_right hc (by linarith)
      _ = y / 4 := by ring
  have h_exp_arg : - (y / 2) ≤ - (y / 4) + - (c * y ^ (1 / 16 : ℝ)) := by
    linarith
  have h_exp := Real.exp_le_exp.mpr h_exp_arg
  rw [Real.exp_add] at h_exp
  have : - (c * y ^ (1 / 16 : ℝ)) = - c * y ^ (1 / 16 : ℝ) := by ring
  rw [this] at h_exp
  exact h_exp

lemma y_mul_exp_neg_le {y : ℝ} (_hy : 0 ≤ y) :
    y * Real.exp (- (y / 4)) ≤ 4 := by
  have h_le := Real.add_one_le_exp (y / 4)
  have h1 : y / 4 ≤ Real.exp (y / 4) := by linarith
  have h2 : y ≤ 4 * Real.exp (y / 4) := by linarith
  calc y * Real.exp (- (y / 4)) ≤ (4 * Real.exp (y / 4)) * Real.exp (- (y / 4)) :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 4 * (Real.exp (y / 4) * Real.exp (- (y / 4))) := by ring
    _ = 4 * Real.exp (y / 4 + - (y / 4)) := by rw [← Real.exp_add]
    _ = 4 := by
      have : y / 4 + - (y / 4) = 0 := by ring
      rw [this, Real.exp_zero, mul_one]

lemma four_log_twoA_div_sqrtA_le {A : ℕ} (hA : 3 ≤ A) {c : ℝ} (hc_pos : 0 < c) (hc : c ≤ 1 / 4) :
    4 * Real.log (2 * (A : ℝ)) / Real.sqrt (A : ℝ) ≤ 32 * Real.exp (- c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  have hA_real : 3 ≤ (A : ℝ) := by exact_mod_cast hA
  have hA_pos : 0 < (A : ℝ) := by linarith
  have hlog3_gt1 : 1 < Real.log 3 := by
    have : (Real.exp 1 : ℝ) < 3 := by linarith [Real.exp_one_lt_d9]
    have := Real.log_lt_log (by positivity) this
    rwa [Real.log_exp] at this
  have hlogA_ge1 : 1 ≤ Real.log (A : ℝ) := by
    have := Real.log_le_log (by norm_num) hA_real
    linarith
  have hlog2A := log_two_mul_le_tpf hA
  have hsqrt : Real.sqrt (A : ℝ) = Real.exp (Real.log (A : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hA_pos]
    ring_nf
  rw [hsqrt]
  have hdiv : 4 * Real.log (2 * (A : ℝ)) / Real.exp (Real.log (A : ℝ) / 2) =
      4 * Real.log (2 * (A : ℝ)) * Real.exp (- (Real.log (A : ℝ) / 2)) := by
    rw [div_eq_mul_inv, Real.exp_neg]
  rw [hdiv]
  let y := Real.log (A : ℝ)
  have hy1 : 1 ≤ y := hlogA_ge1
  have hy0 : 0 ≤ y := by linarith
  have h_exp_split := exp_neg_half_le hy1 hc_pos hc
  have h_bound : 4 * Real.log (2 * (A : ℝ)) * Real.exp (- (y / 2)) ≤
      (8 * y) * (Real.exp (- (y / 4)) * Real.exp (- c * y ^ (1 / 16 : ℝ))) := by
    apply mul_le_mul
    · linarith [hlog2A]
    · exact h_exp_split
    · exact (Real.exp_pos _).le
    · positivity
  refine le_trans h_bound ?_
  have h_assoc : (8 * y) * (Real.exp (- (y / 4)) * Real.exp (- c * y ^ (1 / 16 : ℝ))) =
      8 * (y * Real.exp (- (y / 4))) * Real.exp (- c * y ^ (1 / 16 : ℝ)) := by ring
  rw [h_assoc]
  have hy_le4 := y_mul_exp_neg_le hy0
  have : 8 * (y * Real.exp (- (y / 4))) ≤ 32 := by linarith
  exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le

lemma nat_sqrt_le_two_mul_sqrt {A B : ℕ} (_hA : 3 ≤ A) (hB2A : B ≤ 2 * A) :
    (Nat.sqrt B : ℝ) ≤ 2 * Real.sqrt (A : ℝ) := by
  have hB_le : (B : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hB2A
  have h_sqrt_nat : (Nat.sqrt B : ℝ) ≤ Real.sqrt (B : ℝ) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]
    exact_mod_cast Nat.sqrt_le' B
  refine le_trans h_sqrt_nat ?_
  have h_sqrt_B : Real.sqrt (B : ℝ) ≤ Real.sqrt (2 * (A : ℝ)) := Real.sqrt_le_sqrt hB_le
  refine le_trans h_sqrt_B ?_
  rw [Real.sqrt_mul (by norm_num)]
  have h_sqrt2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    norm_num
  exact mul_le_mul_of_nonneg_right h_sqrt2 (Real.sqrt_nonneg _)

lemma nat_log2_le_two_mul_log {A B : ℕ} (_hA : 3 ≤ A) (_hAB : A < B) (hB2A : B ≤ 2 * A) :
    (Nat.log 2 B : ℝ) ≤ 2 * Real.log (2 * (A : ℝ)) := by
  have h2k_le : 2 ^ (Nat.log 2 B) ≤ B := Nat.pow_log_le_self 2 (by omega)
  have h2k_le_real : (2 : ℝ) ^ (Nat.log 2 B) ≤ (B : ℝ) := by exact_mod_cast h2k_le
  have h2A_le_B : (B : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hB2A
  have h2k_le_2A : (2 : ℝ) ^ (Nat.log 2 B) ≤ 2 * (A : ℝ) := le_trans h2k_le_real h2A_le_B
  have h_pow_eq : (2 : ℝ) ^ (Nat.log 2 B) = Real.exp ((Nat.log 2 B : ℝ) * Real.log 2) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [h_pow_eq] at h2k_le_2A
  have h_log := Real.log_le_log (Real.exp_pos _) h2k_le_2A
  rw [Real.log_exp] at h_log
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (Nat.log 2 B : ℝ) ≤ Real.log (2 * (A : ℝ)) / Real.log 2 := by
    rwa [le_div_iff₀ hlog2_pos]
  refine le_trans h1 ?_
  have h_log2A_nonneg : 0 ≤ Real.log (2 * (A : ℝ)) := by
    apply Real.log_nonneg
    have : (2 : ℝ) * (A : ℝ) ≥ 6 := by exact_mod_cast (by omega)
    linarith
  have h_inv_le : (Real.log 2)⁻¹ ≤ 2 := by
    rw [inv_le_iff_one_le_mul₀ hlog2_pos]
    linarith [Real.log_two_gt_d9]
  calc Real.log (2 * (A : ℝ)) / Real.log 2 = Real.log (2 * (A : ℝ)) * (Real.log 2)⁻¹ := by ring
    _ ≤ Real.log (2 * (A : ℝ)) * 2 := mul_le_mul_of_nonneg_left h_inv_le h_log2A_nonneg
    _ = 2 * Real.log (2 * (A : ℝ)) := by ring

lemma card_div_A_le_four_log_twoA_div_sqrtA {A B : ℕ} (hA : 3 ≤ A) (hAB : A < B) (hB2A : B ≤ 2 * A) :
    ((Nat.sqrt B : ℝ) * (Nat.log 2 B : ℝ)) / (A : ℝ) ≤ 4 * Real.log (2 * (A : ℝ)) / Real.sqrt (A : ℝ) := by
  have hA_pos : 0 < (A : ℝ) := by positivity
  have h_sqrt := nat_sqrt_le_two_mul_sqrt hA hB2A
  have h_log := nat_log2_le_two_mul_log hA hAB hB2A
  have h_log_nonneg : 0 ≤ (Nat.log 2 B : ℝ) := by positivity
  have h_mul_le : (Nat.sqrt B : ℝ) * (Nat.log 2 B : ℝ) ≤ (2 * Real.sqrt (A : ℝ)) * (2 * Real.log (2 * (A : ℝ))) :=
    mul_le_mul h_sqrt h_log h_log_nonneg (by positivity)
  have h_div_le : ((Nat.sqrt B : ℝ) * (Nat.log 2 B : ℝ)) / (A : ℝ) ≤
      ((2 * Real.sqrt (A : ℝ)) * (2 * Real.log (2 * (A : ℝ)))) / (A : ℝ) :=
    div_le_div_of_nonneg_right h_mul_le hA_pos.le
  refine le_trans h_div_le ?_
  have h_sqrt_pos : 0 < Real.sqrt (A : ℝ) := Real.sqrt_pos.mpr hA_pos
  have h_alg : ((2 * Real.sqrt (A : ℝ)) * (2 * Real.log (2 * (A : ℝ)))) / (A : ℝ) =
      4 * Real.log (2 * (A : ℝ)) / Real.sqrt (A : ℝ) := by
    have h_sq : (A : ℝ) = Real.sqrt (A : ℝ) * Real.sqrt (A : ℝ) := (Real.mul_self_sqrt hA_pos.le).symm
    calc ((2 * Real.sqrt (A : ℝ)) * (2 * Real.log (2 * (A : ℝ)))) / (A : ℝ)
        = (Real.sqrt (A : ℝ) * (4 * Real.log (2 * (A : ℝ)))) / (Real.sqrt (A : ℝ) * Real.sqrt (A : ℝ)) := by
          rw [← h_sq]; ring
      _ = 4 * Real.log (2 * (A : ℝ)) / Real.sqrt (A : ℝ) := by
          rw [mul_div_mul_left _ _ (ne_of_gt h_sqrt_pos)]
  rw [h_alg]

lemma norm_sum_primes_sub_abel_le (u : ℝ) (A B : ℕ) (hA : 3 ≤ A) (hAB : A < B) (hB2A : B ≤ 2 * A)
    {c : ℝ} (hc_pos : 0 < c) (hc : c ≤ 1 / 4) :
    let c_seq : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)
    let f : ℝ → ℂ := fun t => ((t : ℂ) * (Real.log t : ℂ))⁻¹
    let P := (Finset.Ioc A B).filter Nat.Prime
    ‖(∑ p ∈ P, (p : ℂ) ^ (-((1 : ℂ) + (u : ℂ) * Complex.I))) - ∑ n ∈ Finset.Ioc A B, f (n : ℝ) * c_seq n‖ ≤
      32 * Real.exp (- c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  intro c_seq f P
  let PP := (Finset.Ioc A B).filter (fun n => IsPrimePow n ∧ ¬ Nat.Prime n)
  have h_split := sum_split_primes u A B hA
  have h_sub_eq : (∑ p ∈ P, (p : ℂ) ^ (-((1 : ℂ) + (u : ℂ) * Complex.I))) - ∑ n ∈ Finset.Ioc A B, f (n : ℝ) * c_seq n =
      - (∑ n ∈ PP, f (n : ℝ) * c_seq n) := by
    calc (∑ p ∈ P, (p : ℂ) ^ (-((1 : ℂ) + (u : ℂ) * Complex.I))) - ∑ n ∈ Finset.Ioc A B, f (n : ℝ) * c_seq n
        = - (∑ n ∈ Finset.Ioc A B, f (n : ℝ) * c_seq n - ∑ p ∈ P, (p : ℂ) ^ (-((1 : ℂ) + (u : ℂ) * Complex.I))) := by ring
      _ = - (∑ n ∈ PP, f (n : ℝ) * c_seq n) := by rw [h_split]
  rw [h_sub_eq, norm_neg]
  have h_sum_norm : ‖∑ n ∈ PP, f (n : ℝ) * c_seq n‖ ≤ ∑ n ∈ PP, ‖f (n : ℝ) * c_seq n‖ :=
    norm_sum_le _ _
  refine le_trans h_sum_norm ?_
  have h_term_le : ∀ n ∈ PP, ‖f (n : ℝ) * c_seq n‖ ≤ (n : ℝ)⁻¹ := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    have hn3 : 3 ≤ n := by omega
    exact norm_f_mul_c_le u n hn3
  have h_sum_le_inv := Finset.sum_le_sum h_term_le
  refine le_trans h_sum_le_inv ?_
  have h_mem_gt : ∀ n ∈ PP, A < n := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    exact hn.1.1
  have h_inv_le_card := sum_inv_le_card_div (by omega) PP h_mem_gt
  refine le_trans h_inv_le_card ?_
  have h_card_le := card_nonprime_primepow_le A B
  have h_div_card : (PP.card : ℝ) / (A : ℝ) ≤ ((Nat.sqrt B : ℝ) * (Nat.log 2 B : ℝ)) / (A : ℝ) := by
    have : (PP.card : ℝ) ≤ (Nat.sqrt B : ℝ) * (Nat.log 2 B : ℝ) := by
      exact_mod_cast h_card_le
    exact div_le_div_of_nonneg_right this (by positivity)
  refine le_trans h_div_card ?_
  have h_alg_le := card_div_A_le_four_log_twoA_div_sqrtA hA hAB hB2A
  refine le_trans h_alg_le ?_
  exact four_log_twoA_div_sqrtA_le hA hc_pos hc


/-!
### Abel summation and main term integration lemmas
-/

lemma sum_Icc_zero_eq_sum_Icc_one (u : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    let c : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)
    ∑ k ∈ Finset.Icc 0 n, c k = ∑ k ∈ Finset.Icc 1 n, c k := by
  intro c
  have h_split : Finset.Icc 0 n = insert 0 (Finset.Icc 1 n) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [h_split, Finset.sum_insert]
  · dsimp [c]; simp
  · simp only [Finset.mem_Icc, not_and]; intro; omega

lemma deriv_f_eq_f' (A B : ℝ) (hA : 3 ≤ A) :
    let f : ℝ → ℂ := fun t => ((t : ℂ) * (Real.log t : ℂ))⁻¹
    let f' : ℝ → ℂ := fun t => - ((Real.log t : ℂ) + 1) / ((t : ℂ) * (Real.log t : ℂ)) ^ 2
    Set.EqOn (deriv f) f' (Set.Ioc A B) := by
  intro f f' t ht
  simp only [Set.mem_Ioc] at ht
  have ht1 : 1 < t := by linarith [ht.1]
  exact (hasDerivAt_inv_mul_log ht1).deriv

lemma integrable_deriv_f_mul_S (u : ℝ) (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) :
    let c : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)
    let f : ℝ → ℂ := fun t => ((t : ℂ) * (Real.log t : ℂ))⁻¹
    IntegrableOn (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) (Set.Ioc (A : ℝ) (B : ℝ)) := by
  intro c f
  have hA_pos : 0 ≤ (A : ℝ) := by positivity
  have hAB_real : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
  have h_diff_int := f_diff_and_int (by exact_mod_cast hA) hAB_real
  have h_int := integrableOn_mul_sum_Icc (c := c) (m := 0) hA_pos h_diff_int.2
  exact h_int.mono_set Set.Ioc_subset_Icc_self

lemma integrable_f'_mul_M (u : ℝ) (A B : ℝ) (hA : 3 ≤ A) (_hAB : A ≤ B) :
    let M : ℝ → ℂ := fun t => (t : ℂ) ^ ((1 : ℂ) - (u : ℂ) * I) / ((1 : ℂ) - (u : ℂ) * I)
    let f' : ℝ → ℂ := fun t => - ((Real.log t : ℂ) + 1) / ((t : ℂ) * (Real.log t : ℂ)) ^ 2
    IntegrableOn (fun t => f' t * M t) (Set.Ioc A B) := by
  intro M f'
  have h_cont_M : ContinuousOn M (Set.Icc A B) := by
    apply ContinuousOn.div_const
    have h_sub : Set.Icc A B ⊆ Set.Ioi 0 := by
      intro x hx; simp only [Set.mem_Icc, Set.mem_Ioi] at hx ⊢; linarith [hx.1]
    refine ContinuousOn.mono ?_ h_sub
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hs : (x : ℂ) ∈ slitPlane := by
      rw [mem_slitPlane_iff]; left; simpa using hx
    exact ((hasDerivAt_id (x : ℂ)).cpow_const hs (c := (1 : ℂ) - (u : ℂ) * I)).comp_ofReal.continuousAt
  have h_cont_f' : ContinuousOn f' (Set.Icc A B) := by
    have h_log_cont : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Set.Icc A B) := by
      apply ContinuousOn.comp continuous_ofReal.continuousOn
      · exact Real.continuousOn_log.mono (fun x hx => by
          simp only [Set.mem_Icc] at hx
          exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1]))
      · intro x _; exact Set.mem_univ _
    apply ContinuousOn.div
    · exact (h_log_cont.add continuousOn_const).neg
    · apply ContinuousOn.pow
      exact continuous_ofReal.continuousOn.mul h_log_cont
    · intro t ht
      simp only [Set.mem_Icc] at ht
      have ht_pos : 0 < t := by linarith [ht.1]
      have ht_gt1 : 1 < t := by linarith [ht.1]
      have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht_pos)
      have hlog_ne : (Real.log t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos ht_gt1))
      have : (t : ℂ) * (Real.log t : ℂ) ≠ 0 := mul_ne_zero ht_ne hlog_ne
      exact pow_ne_zero 2 this
  have h_cont : ContinuousOn (fun t => f' t * M t) (Set.Icc A B) := h_cont_f'.mul h_cont_M
  have h_int := h_cont.integrableOn_compact isCompact_Icc (μ := volume)
  exact h_int.mono_set Set.Ioc_subset_Icc_self

lemma integrable_x_mul_norm_f' (A B : ℝ) (hA : 3 ≤ A) (_hAB : A ≤ B) :
    let f' : ℝ → ℂ := fun t => - ((Real.log t : ℂ) + 1) / ((t : ℂ) * (Real.log t : ℂ)) ^ 2
    IntegrableOn (fun t => t * ‖f' t‖) (Set.Ioc A B) := by
  intro f'
  have h_cont_f' : ContinuousOn f' (Set.Icc A B) := by
    have h_log_cont : ContinuousOn (fun t : ℝ => (Real.log t : ℂ)) (Set.Icc A B) := by
      apply ContinuousOn.comp continuous_ofReal.continuousOn
      · exact Real.continuousOn_log.mono (fun x hx => by
          simp only [Set.mem_Icc] at hx
          exact Set.mem_compl_singleton_iff.mpr (by linarith [hx.1]))
      · intro x _; exact Set.mem_univ _
    apply ContinuousOn.div
    · exact (h_log_cont.add continuousOn_const).neg
    · apply ContinuousOn.pow
      exact continuous_ofReal.continuousOn.mul h_log_cont
    · intro t ht
      simp only [Set.mem_Icc] at ht
      have ht_pos : 0 < t := by linarith [ht.1]
      have ht_gt1 : 1 < t := by linarith [ht.1]
      have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht_pos)
      have hlog_ne : (Real.log t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos ht_gt1))
      have : (t : ℂ) * (Real.log t : ℂ) ≠ 0 := mul_ne_zero ht_ne hlog_ne
      exact pow_ne_zero 2 this
  have h_cont : ContinuousOn (fun t => t * ‖f' t‖) (Set.Icc A B) :=
    continuousOn_id.mul h_cont_f'.norm
  have h_int := h_cont.integrableOn_compact isCompact_Icc (μ := volume)
  exact h_int.mono_set Set.Ioc_subset_Icc_self


lemma norm_abel_sub_integral_le (u : ℝ) (A B : ℕ) (hA : 3 ≤ A) (hAB : A < B) (hB2A : B ≤ 2 * A)
    (c_ψ C_ψ : ℝ) (_hc_ψ_pos : 0 < c_ψ) (hC_ψ_pos : 0 < C_ψ)
    (h_psi : ∀ (X : ℝ), (A : ℝ) ≤ X → X ≤ 2 * A →
      ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)) -
          (X : ℂ) ^ ((1 : ℂ) - u * Complex.I) / ((1 : ℂ) - u * Complex.I)‖ ≤
        C_ψ * X * Real.exp (-c_ψ * (Real.log A) ^ (1 / 16 : ℝ))) :
    let c : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)
    let f : ℝ → ℂ := fun t => ((t : ℂ) * (Real.log t : ℂ))⁻¹
    ‖(∑ k ∈ Finset.Ioc A B, f (k : ℝ) * c k) -
        ∫ x in (A : ℝ)..(B : ℝ), (x : ℂ) ^ (-((1 : ℂ) + u * Complex.I)) / (Real.log x : ℂ)‖ ≤
      4 * C_ψ * Real.exp (-c_ψ * (Real.log A) ^ (1 / 16 : ℝ)) := by
  intro c f
  let f' : ℝ → ℂ := fun t => - ((Real.log t : ℂ) + 1) / ((t : ℂ) * (Real.log t : ℂ)) ^ 2
  let M : ℝ → ℂ := fun t => (t : ℂ) ^ ((1 : ℂ) - (u : ℂ) * I) / ((1 : ℂ) - (u : ℂ) * I)
  have hA_real : 3 ≤ (A : ℝ) := by exact_mod_cast hA
  have hB_real : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB.le
  have hB2A_real : (B : ℝ) ≤ 2 * (A : ℝ) := by exact_mod_cast hB2A
  have h_abel := abel_sum_psi u A B hA hAB.le
  dsimp only at h_abel
  have h_ibp := ibp_main_term u (A : ℝ) (B : ℝ) hA_real hB_real
  dsimp only at h_ibp
  have h_SA : ∑ k ∈ Finset.Icc 0 A, c k = ∑ k ∈ Finset.Icc 1 A, c k :=
    sum_Icc_zero_eq_sum_Icc_one u A (by omega)
  have h_SB : ∑ k ∈ Finset.Icc 0 B, c k = ∑ k ∈ Finset.Icc 1 B, c k :=
    sum_Icc_zero_eq_sum_Icc_one u B (by omega)
  have h_St : ∀ t ∈ Set.Ioc (A : ℝ) (B : ℝ),
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k := by
    intro t ht
    simp only [Set.mem_Ioc] at ht
    have ht_A : (A : ℝ) ≤ t := ht.1.le
    have h_floor : A ≤ ⌊t⌋₊ := Nat.le_floor ht_A
    have : 1 ≤ ⌊t⌋₊ := by omega
    exact sum_Icc_zero_eq_sum_Icc_one u ⌊t⌋₊ this
  have h_deriv_eq := deriv_f_eq_f' (A : ℝ) (B : ℝ) hA_real
  have h_int1_eq : ∫ t in Set.Ioc (A : ℝ) (B : ℝ), deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k =
      ∫ t in Set.Ioc (A : ℝ) (B : ℝ), f' t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp
    rw [h_deriv_eq ht, h_St t ht]
  rw [h_SA, h_SB, h_int1_eq] at h_abel
  have h_ibp_ioc : ∫ x in (A : ℝ)..(B : ℝ), f' x * M x = ∫ x in Set.Ioc (A : ℝ) (B : ℝ), f' x * M x :=
    intervalIntegral.integral_of_le hB_real
  rw [h_ibp_ioc] at h_ibp
  rw [h_abel, h_ibp]
  have h_sub : (f (B : ℝ) * ∑ k ∈ Finset.Icc 1 B, c k - f (A : ℝ) * ∑ k ∈ Finset.Icc 1 A, c k -
        ∫ t in Set.Ioc (A : ℝ) (B : ℝ), f' t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) -
      (f (B : ℝ) * M (B : ℝ) - f (A : ℝ) * M (A : ℝ) - ∫ x in Set.Ioc (A : ℝ) (B : ℝ), f' x * M x) =
      (f (B : ℝ) * ((∑ k ∈ Finset.Icc 1 B, c k) - M (B : ℝ))) -
      (f (A : ℝ) * ((∑ k ∈ Finset.Icc 1 A, c k) - M (A : ℝ))) -
      ((∫ t in Set.Ioc (A : ℝ) (B : ℝ), f' t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) -
        ∫ x in Set.Ioc (A : ℝ) (B : ℝ), f' x * M x) := by ring
  rw [h_sub]
  have h_int_S_int : IntegrableOn (fun t => f' t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) (Set.Ioc (A : ℝ) (B : ℝ)) := by
    have h_orig := integrable_deriv_f_mul_S u A B hA hAB.le
    dsimp only at h_orig
    apply h_orig.congr_fun _ measurableSet_Ioc
    intro t ht
    dsimp
    rw [h_deriv_eq ht, h_St t ht]
  have h_int_M_int := integrable_f'_mul_M u (A : ℝ) (B : ℝ) hA_real hB_real
  have h_sub_int : (∫ t in Set.Ioc (A : ℝ) (B : ℝ), f' t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) -
        ∫ x in Set.Ioc (A : ℝ) (B : ℝ), f' x * M x =
      ∫ t in Set.Ioc (A : ℝ) (B : ℝ), (f' t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k - f' t * M t) := by
    rw [← integral_sub h_int_S_int h_int_M_int]
  rw [h_sub_int]
  have h_int_factor : (fun t => f' t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k - f' t * M t) =
      (fun t => f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t)) := by
    ext t; ring
  rw [h_int_factor]
  have h_tri1 := norm_sub_le
    (f (B : ℝ) * ((∑ k ∈ Finset.Icc 1 B, c k) - M (B : ℝ)) - f (A : ℝ) * ((∑ k ∈ Finset.Icc 1 A, c k) - M (A : ℝ)))
    (∫ t in Set.Ioc (A : ℝ) (B : ℝ), f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t))
  refine le_trans h_tri1 ?_
  have h_tri2 := norm_sub_le
    (f (B : ℝ) * ((∑ k ∈ Finset.Icc 1 B, c k) - M (B : ℝ)))
    (f (A : ℝ) * ((∑ k ∈ Finset.Icc 1 A, c k) - M (A : ℝ)))
  have : ‖f (B : ℝ) * ((∑ k ∈ Finset.Icc 1 B, c k) - M (B : ℝ)) - f (A : ℝ) * ((∑ k ∈ Finset.Icc 1 A, c k) - M (A : ℝ))‖ +
      ‖∫ t in Set.Ioc (A : ℝ) (B : ℝ), f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t)‖ ≤
      ‖f (B : ℝ) * ((∑ k ∈ Finset.Icc 1 B, c k) - M (B : ℝ))‖ +
      ‖f (A : ℝ) * ((∑ k ∈ Finset.Icc 1 A, c k) - M (A : ℝ))‖ +
      ‖∫ t in Set.Ioc (A : ℝ) (B : ℝ), f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t)‖ := by
    linarith [h_tri2]
  refine le_trans this ?_
  let δ := C_ψ * Real.exp (-c_ψ * (Real.log A) ^ (1 / 16 : ℝ))
  have hδ_pos : 0 < δ := mul_pos hC_ψ_pos (Real.exp_pos _)
  have h_psi_B : ‖(∑ k ∈ Finset.Icc 1 B, c k) - M (B : ℝ)‖ ≤ δ * (B : ℝ) := by
    have h_floor_B : ⌊(B : ℝ)⌋₊ = B := Nat.floor_natCast B
    have h := h_psi (B : ℝ) hB_real hB2A_real
    rw [h_floor_B] at h
    calc ‖(∑ k ∈ Finset.Icc 1 B, c k) - M (B : ℝ)‖
        ≤ C_ψ * (B : ℝ) * Real.exp (-c_ψ * (Real.log A) ^ (1 / 16 : ℝ)) := h
      _ = δ * (B : ℝ) := by dsimp [δ]; ring
  have h_psi_A : ‖(∑ k ∈ Finset.Icc 1 A, c k) - M (A : ℝ)‖ ≤ δ * (A : ℝ) := by
    have h_floor_A : ⌊(A : ℝ)⌋₊ = A := Nat.floor_natCast A
    have h := h_psi (A : ℝ) le_rfl (by linarith)
    rw [h_floor_A] at h
    calc ‖(∑ k ∈ Finset.Icc 1 A, c k) - M (A : ℝ)‖
        ≤ C_ψ * (A : ℝ) * Real.exp (-c_ψ * (Real.log A) ^ (1 / 16 : ℝ)) := h
      _ = δ * (A : ℝ) := by dsimp [δ]; ring
  have h_term_B : ‖f (B : ℝ) * ((∑ k ∈ Finset.Icc 1 B, c k) - M (B : ℝ))‖ ≤ δ * (‖f (B : ℝ)‖ * (B : ℝ)) := by
    rw [norm_mul]
    calc ‖f (B : ℝ)‖ * ‖(∑ k ∈ Finset.Icc 1 B, c k) - M (B : ℝ)‖
        ≤ ‖f (B : ℝ)‖ * (δ * (B : ℝ)) := mul_le_mul_of_nonneg_left h_psi_B (norm_nonneg _)
      _ = δ * (‖f (B : ℝ)‖ * (B : ℝ)) := by ring
  have h_term_A : ‖f (A : ℝ) * ((∑ k ∈ Finset.Icc 1 A, c k) - M (A : ℝ))‖ ≤ δ * (‖f (A : ℝ)‖ * (A : ℝ)) := by
    rw [norm_mul]
    calc ‖f (A : ℝ)‖ * ‖(∑ k ∈ Finset.Icc 1 A, c k) - M (A : ℝ)‖
        ≤ ‖f (A : ℝ)‖ * (δ * (A : ℝ)) := mul_le_mul_of_nonneg_left h_psi_A (norm_nonneg _)
      _ = δ * (‖f (A : ℝ)‖ * (A : ℝ)) := by ring
  have h_norm_int_le := norm_integral_le_integral_norm (fun t => f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t))
    (μ := volume.restrict (Set.Ioc (A : ℝ) (B : ℝ)))
  have h_int_bound : ‖∫ t in Set.Ioc (A : ℝ) (B : ℝ), f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t)‖ ≤
      δ * ∫ x in (A : ℝ)..(B : ℝ), x * ‖f' x‖ := by
    refine le_trans h_norm_int_le ?_
    have h_ae_le : ∀ t ∈ Set.Ioc (A : ℝ) (B : ℝ),
        ‖f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t)‖ ≤ δ * (t * ‖f' t‖) := by
      intro t ht
      simp only [Set.mem_Ioc] at ht
      have ht_A : (A : ℝ) ≤ t := ht.1.le
      have ht_2A : t ≤ 2 * (A : ℝ) := le_trans ht.2 hB2A_real
      have h_psi_t := h_psi t ht_A ht_2A
      rw [norm_mul]
      calc ‖f' t‖ * ‖(∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t‖
          ≤ ‖f' t‖ * (C_ψ * t * Real.exp (-c_ψ * (Real.log A) ^ (1 / 16 : ℝ))) :=
            mul_le_mul_of_nonneg_left h_psi_t (norm_nonneg _)
        _ = δ * (t * ‖f' t‖) := by dsimp [δ]; ring
    have h_int1 : IntegrableOn (fun t => ‖f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t)‖)
        (Set.Ioc (A : ℝ) (B : ℝ)) := by
      have : (fun t => ‖f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t)‖) =
          (fun t => ‖f' t * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k - f' t * M t‖) := by
        ext t; congr 1; ring
      rw [this]
      exact (h_int_S_int.sub h_int_M_int).norm
    have h_int2 := integrable_x_mul_norm_f' (A : ℝ) (B : ℝ) hA_real hB_real
    have h_ae : (fun t => ‖f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t)‖) ≤ᵐ[volume.restrict (Set.Ioc (A : ℝ) (B : ℝ))]
        (fun t => δ * (t * ‖f' t‖)) :=
      ae_restrict_mem measurableSet_Ioc |>.mono (fun t ht => h_ae_le t ht)
    have h_mono : ∫ t in Set.Ioc (A : ℝ) (B : ℝ), ‖f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t)‖ ≤
        ∫ t in Set.Ioc (A : ℝ) (B : ℝ), δ * (t * ‖f' t‖) :=
      integral_mono_ae h_int1 (h_int2.const_mul δ) h_ae
    refine le_trans h_mono ?_
    rw [integral_const_mul]
    have h_ioc_eq : ∫ t in Set.Ioc (A : ℝ) (B : ℝ), t * ‖f' t‖ = ∫ x in (A : ℝ)..(B : ℝ), x * ‖f' x‖ := by
      rw [intervalIntegral.integral_of_le hB_real]
    rw [h_ioc_eq]
  have h_total : ‖f (B : ℝ) * ((∑ k ∈ Finset.Icc 1 B, c k) - M (B : ℝ))‖ +
      ‖f (A : ℝ) * ((∑ k ∈ Finset.Icc 1 A, c k) - M (A : ℝ))‖ +
      ‖∫ t in Set.Ioc (A : ℝ) (B : ℝ), f' t * ((∑ k ∈ Finset.Icc 1 ⌊t⌋₊, c k) - M t)‖ ≤
      δ * (‖f (B : ℝ)‖ * (B : ℝ) + ‖f (A : ℝ)‖ * (A : ℝ) + ∫ x in (A : ℝ)..(B : ℝ), x * ‖f' x‖) := by
    linarith [h_term_B, h_term_A, h_int_bound]
  refine le_trans h_total ?_
  have h_bound_le4 := boundary_and_integral_error_le (A := (A : ℝ)) (B := (B : ℝ)) hA_real hB_real hB2A_real
  calc δ * (‖f (B : ℝ)‖ * (B : ℝ) + ‖f (A : ℝ)‖ * (A : ℝ) + ∫ x in (A : ℝ)..(B : ℝ), x * ‖f' x‖)
      ≤ δ * 4 := mul_le_mul_of_nonneg_left h_bound_le4 hδ_pos.le
    _ = 4 * C_ψ * Real.exp (-c_ψ * (Real.log A) ^ (1 / 16 : ℝ)) := by dsimp [δ]; ring




theorem sum_primes_cpow_sub_integral_le (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (A B : ℕ) (u : ℝ), 3 ≤ A → A < B → B ≤ 2 * A → 1 ≤ |u| → Real.log |u| ≤ (Real.log A) ^ (5 / 4 : ℝ) →
      ‖(∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + u * Complex.I))) -
          ∫ x in (A : ℝ)..(B : ℝ), (x : ℂ) ^ (-((1 : ℂ) + u * Complex.I)) / (Real.log x : ℂ)‖ ≤
        C * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  obtain ⟨c_ψ, C_ψ, hc_ψ_pos, hC_ψ_pos, h_psi⟩ := twistedPsi_sub_main_le c₀ K hc₀ hK hζ hholo
  let c := min c_ψ (1 / 4 : ℝ)
  have hc_pos : 0 < c := lt_min hc_ψ_pos (by norm_num)
  have hc_le_quarter : c ≤ 1 / 4 := min_le_right _ _
  have hc_le_psi : c ≤ c_ψ := min_le_left _ _
  let C := 4 * C_ψ + 32
  have hC_pos : 0 < C := by dsimp [C]; linarith
  refine ⟨c, C, hc_pos, hC_pos, ?_⟩
  intro A B u hA hAB hB2A hu hlogu
  let P := (Finset.Ioc A B).filter Nat.Prime
  let c_seq : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)
  let f : ℝ → ℂ := fun t => ((t : ℂ) * (Real.log t : ℂ))⁻¹
  let S_P := ∑ p ∈ P, (p : ℂ) ^ (-((1 : ℂ) + u * Complex.I))
  let S_Abel := ∑ n ∈ Finset.Ioc A B, f (n : ℝ) * c_seq n
  let I := ∫ x in (A : ℝ)..(B : ℝ), (x : ℂ) ^ (-((1 : ℂ) + u * Complex.I)) / (Real.log x : ℂ)
  have h_split : S_P - I = (S_P - S_Abel) + (S_Abel - I) := by ring
  change ‖S_P - I‖ ≤ C * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ))
  rw [h_split]
  have h_tri := norm_add_le (S_P - S_Abel) (S_Abel - I)
  refine le_trans h_tri ?_
  have h_bound_P := norm_sum_primes_sub_abel_le u A B hA hAB hB2A hc_pos hc_le_quarter
  have h_psi_fixed : ∀ (X : ℝ), (A : ℝ) ≤ X → X ≤ 2 * A →
      ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, c_seq n) - (X : ℂ) ^ ((1 : ℂ) - u * Complex.I) / ((1 : ℂ) - u * Complex.I)‖ ≤
        C_ψ * X * Real.exp (-c_ψ * (Real.log A) ^ (1 / 16 : ℝ)) := by
    intro X hAX hX2A
    exact h_psi A X u hA hAX hX2A hu hlogu
  have h_bound_Abel := norm_abel_sub_integral_le u A B hA hAB hB2A c_ψ C_ψ hc_ψ_pos hC_ψ_pos h_psi_fixed
  have h_exp_mono : Real.exp (-c_ψ * (Real.log A) ^ (1 / 16 : ℝ)) ≤ Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have h_logA_nonneg : 0 ≤ (Real.log A) ^ (1 / 16 : ℝ) := by positivity
    have : -c_ψ ≤ -c := by linarith
    exact mul_le_mul_of_nonneg_right this h_logA_nonneg
  have h_Abel_le : ‖S_Abel - I‖ ≤ (4 * C_ψ) * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
    calc ‖S_Abel - I‖ ≤ 4 * C_ψ * Real.exp (-c_ψ * (Real.log A) ^ (1 / 16 : ℝ)) := h_bound_Abel
      _ ≤ 4 * C_ψ * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) :=
        mul_le_mul_of_nonneg_left h_exp_mono (by linarith)
  calc ‖S_P - S_Abel‖ + ‖S_Abel - I‖
      ≤ 32 * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) + (4 * C_ψ) * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) :=
        add_le_add h_bound_P h_Abel_le
    _ = C * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
      dsimp [C]; ring

theorem sum_primes_cpow_neg_one_sub_mul_I_le (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (A B : ℕ) (u : ℝ), 3 ≤ A → A < B → B ≤ 2 * A → 1 ≤ |u| → Real.log |u| ≤ (Real.log A) ^ (5 / 4 : ℝ) →
      ‖∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + u * Complex.I))‖ ≤
        3 / (|u| * Real.log A) + C * Real.exp (-c * (Real.log A) ^ (1 / 16 : ℝ)) := by
  obtain ⟨c, C, hc, hC, h_main⟩ := sum_primes_cpow_sub_integral_le c₀ K hc₀ hK hζ hholo
  exact ⟨c, C, hc, hC, sum_primes_bound_of_sub_integral c C hc hC h_main⟩

end Erdos1201.MR
