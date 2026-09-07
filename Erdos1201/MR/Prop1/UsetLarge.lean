/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Setup
import Erdos1201.MR.Arithmetic
import Erdos1201.MR.Analysis.WellSpaced
import Erdos1201.MR.Analysis.HalaszPrimes
import Erdos1201.MR.Analysis.ShortRangePrimeMassBT
import Erdos1201.MR.Prop1.UsetRBound

/-!
# Large Prime Polynomial Bound on Well-Spaced Points (Matomäki–Radziwiłł Section 8.3)

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module proves the $T_L$ bound of Proposition 1 for the large prime polynomial $Q_v$
multiplied by the cofactor polynomial $R_v$, combining Halász's inequality for primes (Lemma 11),
the short-range prime mass bound from Brun–Titchmarsh, and the pointwise bound on $R_v$ in the exceptional region.
-/

open scoped BigOperators
open Classical
open Erdos1201
open Erdos1201.MR

namespace Erdos1201.MR

lemma exp_inv_H_le_exp_half_usetlarge {H : ℝ} (hH : 2 ≤ H) : Real.exp (1 / H) ≤ Real.exp (1 / 2) := by
  apply Real.exp_le_exp.mpr
  exact one_div_le_one_div_of_le (by norm_num) hH

lemma exp_half_mul_add_one_lt_two_mul_add_one {P₀ : ℝ} (hP₀ : 3 ≤ P₀) :
    (P₀ + 1) * Real.exp (1 / 2) < 2 * P₀ + 1 := by
  have he : Real.exp (1 / 2 : ℝ) ≤ 1.65 := by
    have hpos : 0 ≤ Real.exp (1 / 2 : ℝ) := (Real.exp_pos _).le
    have h165 : 0 ≤ (1.65 : ℝ) := by norm_num
    rw [← sq_le_sq₀ hpos h165]
    have h_sq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [h_sq]
    have : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
    linarith
  calc (P₀ + 1) * Real.exp (1 / 2)
    _ ≤ (P₀ + 1) * 1.65 := by nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    _ = 1.65 * P₀ + 1.65 := by ring
    _ < 2 * P₀ + 1 := by linarith

lemma shortPrimeRange_subset_Ioc_prime_usetlarge (P Q : ℕ) (H : ℝ) (v : ℕ)
    (hH : 2 ≤ H) (P₀ : ℕ) (hP₀_le : (P₀ : ℝ) < Real.exp ((v : ℝ) / H))
    (hP₀_ge : Real.exp ((v : ℝ) / H) ≤ (P₀ : ℝ) + 1) (hP₀_3 : 3 ≤ P₀) :
    shortPrimeRange P Q H v ⊆ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime := by
  intro p hp
  rw [mem_shortPrimeRange] at hp
  rw [Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨?_, ?_⟩, hp.1.1⟩
  · have : (P₀ : ℝ) < (p : ℝ) := hP₀_le.trans_le hp.2.1
    exact_mod_cast this
  · have hp_lt : (p : ℝ) < Real.exp (((v : ℝ) + 1) / H) := hp.2.2
    have h_add : ((v : ℝ) + 1) / H = (v : ℝ) / H + 1 / H := by ring
    rw [h_add, Real.exp_add] at hp_lt
    have h_exp1 : Real.exp (1 / H) ≤ Real.exp (1 / 2) := exp_inv_H_le_exp_half_usetlarge hH
    have h_expv : Real.exp ((v : ℝ) / H) ≤ (P₀ : ℝ) + 1 := hP₀_ge
    have h_exp_mul : Real.exp ((v : ℝ) / H) * Real.exp (1 / H) ≤ ((P₀ : ℝ) + 1) * Real.exp (1 / 2) :=
      mul_le_mul h_expv h_exp1 (Real.exp_pos _).le (by linarith)
    have h_2P₀ : ((P₀ : ℝ) + 1) * Real.exp (1 / 2) < 2 * (P₀ : ℝ) + 1 := by
      have : (3 : ℝ) ≤ (P₀ : ℝ) := by exact_mod_cast hP₀_3
      exact exp_half_mul_add_one_lt_two_mul_add_one this
    have hp_lt_cast : (p : ℝ) < ((2 * P₀ + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have : p < 2 * P₀ + 1 := by exact_mod_cast hp_lt_cast
    omega

lemma dirichletPoly_eq_Qpoly_usetlarge (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (P₀ : ℕ)
    (hsub : shortPrimeRange P Q H v ⊆ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime) (s : ℂ) :
    dirichletPoly (fun p => if p ∈ shortPrimeRange P Q H v then fX β X p else 0)
      ((Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime) s =
    Qpoly β X P Q H v s := by
  unfold Qpoly dirichletPoly
  set f : ℕ → ℂ := fun p => (if p ∈ shortPrimeRange P Q H v then fX β X p else 0) * (p : ℂ) ^ (-s)
  have h_sum : ∑ x ∈ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime, f x = ∑ x ∈ shortPrimeRange P Q H v, f x := by
    apply (Finset.sum_subset hsub ?_).symm
    intro x _hx hnot
    dsimp [f]
    simp [hnot]
  rw [h_sum]
  apply Finset.sum_congr rfl
  intro x hx
  dsimp [f]
  simp [hx]

lemma sum_norm_sq_coeff_le (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (P₀ : ℕ)
    (hP₀_pos : 0 < Real.log (P₀ : ℝ))
    (hsub : shortPrimeRange P Q H v ⊆ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime) :
    (∑ p ∈ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime,
      ‖if p ∈ shortPrimeRange P Q H v then fX β X p else 0‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P₀)) ≤
    (1 / Real.log P₀) * ∑ p ∈ shortPrimeRange P Q H v, (1 : ℝ) / (p : ℝ) ^ 2 := by
  set S := shortPrimeRange P Q H v
  set T := (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime
  have h_eq : (∑ p ∈ T, ‖if p ∈ S then fX β X p else 0‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P₀)) =
      ∑ p ∈ S, ‖if p ∈ S then fX β X p else 0‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P₀) := by
    apply (Finset.sum_subset hsub ?_).symm
    intro x _hx hnot
    simp [hnot]
  rw [h_eq]
  have h_eq2 : (∑ p ∈ S, ‖if p ∈ S then fX β X p else 0‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P₀)) =
      ∑ p ∈ S, ‖fX β X p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P₀) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [hx]
  rw [h_eq2]
  have h_term : ∀ p ∈ S, ‖fX β X p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P₀) ≤ (1 / Real.log P₀) * ((1 : ℝ) / (p : ℝ) ^ 2) := by
    intro p hp
    have hp_norm := norm_fX_le_one β X p
    have hp_sq : ‖fX β X p‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (fX β X p)]
    rw [mem_shortPrimeRange] at hp
    have hp_prime := hp.1.1
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hp2_pos : 0 < (p : ℝ) ^ 2 * Real.log P₀ := mul_pos (sq_pos_of_pos hp_pos) hP₀_pos
    calc ‖fX β X p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P₀)
        ≤ 1 / ((p : ℝ) ^ 2 * Real.log P₀) := div_le_div_of_nonneg_right hp_sq hp2_pos.le
      _ = (1 / Real.log P₀) * ((1 : ℝ) / (p : ℝ) ^ 2) := by ring
  have h_sum := Finset.sum_le_sum h_term
  rw [← Finset.mul_sum] at h_sum
  exact h_sum

lemma sum_inv_sq_le_inv_P₀_mul_sum_inv (P Q : ℕ) (H : ℝ) (v : ℕ) (P₀ : ℕ)
    (hP₀_pos : 0 < (P₀ : ℝ)) (hP₀_le : (P₀ : ℝ) < Real.exp ((v : ℝ) / H)) :
    (∑ p ∈ shortPrimeRange P Q H v, (1 : ℝ) / (p : ℝ) ^ 2) ≤
    (1 / (P₀ : ℝ)) * ∑ p ∈ shortPrimeRange P Q H v, (1 : ℝ) / (p : ℝ) := by
  have h_term : ∀ p ∈ shortPrimeRange P Q H v, (1 : ℝ) / (p : ℝ) ^ 2 ≤ (1 / (P₀ : ℝ)) * ((1 : ℝ) / (p : ℝ)) := by
    intro p hp
    rw [mem_shortPrimeRange] at hp
    have hp_pos : 0 < (p : ℝ) := by exact_mod_cast hp.1.1.pos
    have hp_ge : (P₀ : ℝ) ≤ (p : ℝ) := hP₀_le.le.trans hp.2.1
    have h_prod : (P₀ : ℝ) * (p : ℝ) ≤ (p : ℝ) ^ 2 := by
      calc (P₀ : ℝ) * (p : ℝ) ≤ (p : ℝ) * (p : ℝ) := mul_le_mul_of_nonneg_right hp_ge hp_pos.le
        _ = (p : ℝ) ^ 2 := (sq (p : ℝ)).symm
    have hp2_pos : 0 < (P₀ : ℝ) * (p : ℝ) := mul_pos hP₀_pos hp_pos
    calc (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 / ((P₀ : ℝ) * (p : ℝ)) := one_div_le_one_div_of_le hp2_pos h_prod
      _ = (1 / (P₀ : ℝ)) * ((1 : ℝ) / (p : ℝ)) := by ring
  have h_sum := Finset.sum_le_sum h_term
  rw [← Finset.mul_sum] at h_sum
  exact h_sum

lemma cancel_P₀_bound (P₀ : ℕ) (hP₀_pos : 0 < (P₀ : ℝ)) (hlogP₀_pos : 0 < Real.log (P₀ : ℝ))
    (E S_sum : ℝ) :
    ((P₀ : ℝ) + (P₀ : ℝ) * E) * ((1 / Real.log (P₀ : ℝ)) * ((1 / (P₀ : ℝ)) * S_sum)) =
    (1 + E) * (1 / Real.log (P₀ : ℝ)) * S_sum := by
  have hP0 : (P₀ : ℝ) ≠ 0 := hP₀_pos.ne'
  have hlog : Real.log (P₀ : ℝ) ≠ 0 := hlogP₀_pos.ne'
  calc ((P₀ : ℝ) + (P₀ : ℝ) * E) * ((1 / Real.log (P₀ : ℝ)) * ((1 / (P₀ : ℝ)) * S_sum))
      = ((P₀ : ℝ) * (1 + E)) * ((1 / (P₀ : ℝ)) * ((1 / Real.log (P₀ : ℝ)) * S_sum)) := by ring
    _ = ((P₀ : ℝ) * (1 / (P₀ : ℝ))) * ((1 + E) * (1 / Real.log (P₀ : ℝ)) * S_sum) := by ring
    _ = 1 * ((1 + E) * (1 / Real.log (P₀ : ℝ)) * S_sum) := by rw [mul_one_div_cancel hP0]
    _ = (1 + E) * (1 / Real.log (P₀ : ℝ)) * S_sum := by ring

lemma inv_log_P₀_le_two_mul_H_div_v (H : ℝ) (v : ℕ) (P₀ : ℕ)
    (hH_pos : 0 < H) (hv_pos : 0 < (v : ℝ)) (hP₀_2 : 2 ≤ P₀)
    (hP₀_ge : Real.exp ((v : ℝ) / H) ≤ (P₀ : ℝ) + 1) :
    1 / Real.log (P₀ : ℝ) ≤ 2 * (H / (v : ℝ)) := by
  set x := Real.exp ((v : ℝ) / H) with hx_def
  have hx_pos : 0 < x := Real.exp_pos _
  have hP₀_pos : 0 < (P₀ : ℝ) := by exact_mod_cast (by omega : 0 < P₀)
  have hP₀_ge_2 : (2 : ℝ) ≤ (P₀ : ℝ) := by exact_mod_cast hP₀_2
  have h_x_le_sq : x ≤ (P₀ : ℝ) ^ 2 := by
    calc x ≤ (P₀ : ℝ) + 1 := hP₀_ge
      _ ≤ (P₀ : ℝ) + (P₀ : ℝ) := by linarith
      _ = 2 * (P₀ : ℝ) := by ring
      _ ≤ (P₀ : ℝ) * (P₀ : ℝ) := mul_le_mul_of_nonneg_right hP₀_ge_2 hP₀_pos.le
      _ = (P₀ : ℝ) ^ 2 := (sq _).symm
  have h_log_le : Real.log x ≤ Real.log ((P₀ : ℝ) ^ 2) :=
    Real.log_le_log hx_pos h_x_le_sq
  have h_log_sq : Real.log ((P₀ : ℝ) ^ 2) = 2 * Real.log (P₀ : ℝ) := by
    rw [Real.log_pow, Nat.cast_two]
  rw [hx_def, Real.log_exp, h_log_sq] at h_log_le
  have h_v2H_le : (v : ℝ) / (2 * H) ≤ Real.log (P₀ : ℝ) := by
    calc (v : ℝ) / (2 * H) = ((v : ℝ) / H) / 2 := by ring
      _ ≤ (2 * Real.log (P₀ : ℝ)) / 2 := div_le_div_of_nonneg_right h_log_le (by norm_num)
      _ = Real.log (P₀ : ℝ) := by ring
  have h_v2H_pos : 0 < (v : ℝ) / (2 * H) := div_pos hv_pos (by linarith)
  have h_inv := one_div_le_one_div_of_le h_v2H_pos h_v2H_le
  have h_eq : 1 / ((v : ℝ) / (2 * H)) = 2 * (H / (v : ℝ)) := by
    rw [one_div_div]
    ring
  exact h_inv.trans_eq h_eq

lemma inv_P_le_cube_div_sqrt (P : ℕ) (hP : 2 ≤ P) :
    (1 : ℝ) / (P : ℝ) ≤ (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by
  have hP_pos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hsqrt_pos : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.mpr hP_pos
  have h_sqrt_le : Real.sqrt (P : ℝ) ≤ (P : ℝ) := by
    have h1 : 1 ≤ (P : ℝ) := by exact_mod_cast (by omega : 1 ≤ P)
    calc Real.sqrt (P : ℝ) ≤ Real.sqrt ((P : ℝ) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          nlinarith
      _ = (P : ℝ) := Real.sqrt_sq (by positivity)
  have h_inv_le : 1 / (P : ℝ) ≤ 1 / Real.sqrt (P : ℝ) :=
    one_div_le_one_div_of_le hsqrt_pos h_sqrt_le
  have h_cube : 1 ≤ (1 + Real.log (P : ℝ)) ^ 3 := by
    have h1 : (1 : ℝ) ≤ 1 + Real.log (P : ℝ) := by
      have : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P))
      linarith
    calc (1 : ℝ) = (1 : ℝ) ^ 3 := by norm_num
      _ ≤ (1 + Real.log (P : ℝ)) ^ 3 := by gcongr
  calc 1 / (P : ℝ) ≤ 1 / Real.sqrt (P : ℝ) := h_inv_le
    _ = 1 * (1 / Real.sqrt (P : ℝ)) := by ring
    _ ≤ (1 + Real.log (P : ℝ)) ^ 3 * (1 / Real.sqrt (P : ℝ)) :=
        mul_le_mul_of_nonneg_right h_cube (by positivity)
    _ = (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by ring

lemma sum_le_insert_sum {α : Type*} [DecidableEq α] (s t : Finset α) (a : α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsub : s ⊆ insert a t) :
    ∑ x ∈ s, f x ≤ f a + ∑ x ∈ t, f x := by
  have h1 : ∑ x ∈ s, f x ≤ ∑ x ∈ insert a t, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => hf x)
  refine h1.trans ?_
  by_cases ha : a ∈ t
  · rw [Finset.insert_eq_of_mem ha]
    have : 0 ≤ f a := hf a
    linarith
  · rw [Finset.sum_insert ha]

lemma shortPrimeRange_subset_insert_caseA (P Q : ℕ) (H : ℝ) (v : ℕ)
    (hP : 2 ≤ P) (hH_pos : 0 < H) (hv : (v : ℝ) < H * Real.log (P : ℝ)) :
    shortPrimeRange P Q H v ⊆ insert P ((Finset.Ioc ⌊(P : ℝ)⌋₊ ⌊(P : ℝ) * Real.exp (1 / H)⌋₊).filter Nat.Prime) := by
  intro p hp
  rw [mem_shortPrimeRange] at hp
  have hpP : P ≤ p := hp.1.2.1
  have hp_prime : Nat.Prime p := hp.1.1
  have hp_lt : (p : ℝ) < Real.exp (((v : ℝ) + 1) / H) := hp.2.2
  have h_v1 : ((v : ℝ) + 1) / H ≤ Real.log (P : ℝ) + 1 / H := by
    have h_div : (v : ℝ) / H ≤ (H * Real.log (P : ℝ)) / H :=
      div_le_div_of_nonneg_right hv.le hH_pos.le
    calc ((v : ℝ) + 1) / H = (v : ℝ) / H + 1 / H := by ring
      _ ≤ (H * Real.log (P : ℝ)) / H + 1 / H := by linarith [h_div]
      _ = Real.log (P : ℝ) + 1 / H := by rw [mul_div_cancel_left₀ _ hH_pos.ne']
  have hP_pos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hexp : Real.exp (((v : ℝ) + 1) / H) ≤ (P : ℝ) * Real.exp (1 / H) := by
    calc Real.exp (((v : ℝ) + 1) / H) ≤ Real.exp (Real.log (P : ℝ) + 1 / H) := Real.exp_le_exp.mpr h_v1
      _ = Real.exp (Real.log (P : ℝ)) * Real.exp (1 / H) := Real.exp_add _ _
      _ = (P : ℝ) * Real.exp (1 / H) := by rw [Real.exp_log hP_pos]
  have hp_le_exp : (p : ℝ) ≤ (P : ℝ) * Real.exp (1 / H) := hp_lt.le.trans hexp
  have hp_le_floor : p ≤ ⌊(P : ℝ) * Real.exp (1 / H)⌋₊ := Nat.le_floor hp_le_exp
  rcases eq_or_lt_of_le hpP with heq | hlt
  · subst heq
    exact Finset.mem_insert_self P _
  · refine Finset.mem_insert_of_mem ?_
    rw [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, hp_le_floor⟩, hp_prime⟩
    rw [Nat.floor_natCast]
    exact hlt

lemma shortPrimeRange_subset_insert_caseB (P Q : ℕ) (H : ℝ) (v : ℕ) :
    let x := Real.exp ((v : ℝ) / H)
    let M := ⌊x⌋₊
    shortPrimeRange P Q H v ⊆ insert M ((Finset.Ioc M ⌊x * Real.exp (1 / H)⌋₊).filter Nat.Prime) := by
  intro x M p hp
  rw [mem_shortPrimeRange] at hp
  have hp_prime : Nat.Prime p := hp.1.1
  have hp_ge_x : x ≤ (p : ℝ) := hp.2.1
  have hp_lt : (p : ℝ) < Real.exp (((v : ℝ) + 1) / H) := hp.2.2
  have h_v1 : Real.exp (((v : ℝ) + 1) / H) = x * Real.exp (1 / H) := by
    dsimp [x]
    have : ((v : ℝ) + 1) / H = (v : ℝ) / H + 1 / H := by ring
    rw [this, Real.exp_add]
  rw [h_v1] at hp_lt
  have hp_floor : p ≤ ⌊x * Real.exp (1 / H)⌋₊ := Nat.le_floor hp_lt.le
  have hx_pos : 0 ≤ x := (Real.exp_pos _).le
  have hM_le_p : M ≤ p := by
    dsimp [M]
    exact Nat.floor_le_of_le hp_ge_x
  rcases eq_or_lt_of_le hM_le_p with heq | hlt
  · subst heq
    exact Finset.mem_insert_self M _
  · refine Finset.mem_insert_of_mem ?_
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hlt, hp_floor⟩, hp_prime⟩

lemma cube_exp_neg_mono {x u : ℝ} (hx : 5 ≤ x) (hu : 0 ≤ u) :
    (1 + x + u) ^ 3 * Real.exp (- ((x + u) / 2)) ≤ (1 + x) ^ 3 * Real.exp (- (x / 2)) := by
  have hx1 : 0 < 1 + x := by linarith
  have hx6 : 6 ≤ 1 + x := by linarith
  have h_frac : u / (1 + x) ≤ u / 6 := by
    exact div_le_div_of_nonneg_left hu (by norm_num) hx6
  have h_exp1 : 1 + u / 6 ≤ Real.exp (u / 6) := by
    linarith [Real.add_one_le_exp (u / 6)]
  have h_base : 1 + u / (1 + x) ≤ Real.exp (u / 6) := by linarith
  have h_cube : (1 + u / (1 + x)) ^ 3 ≤ Real.exp (u / 2) := by
    calc (1 + u / (1 + x)) ^ 3 ≤ (Real.exp (u / 6)) ^ 3 := by
          have : 0 ≤ 1 + u / (1 + x) := by positivity
          gcongr
      _ = Real.exp (3 * (u / 6)) := by rw [← Real.exp_nat_mul]; rfl
      _ = Real.exp (u / 2) := by ring_nf
  have h_id : 1 + x + u = (1 + x) * (1 + u / (1 + x)) := by
    have : (1 + x) * (1 + u / (1 + x)) = (1 + x) + (1 + x) * (u / (1 + x)) := by ring
    rw [this, mul_div_cancel₀ u hx1.ne']
  rw [h_id, mul_pow]
  have h_exp_split : Real.exp (- ((x + u) / 2)) = Real.exp (- (x / 2)) * Real.exp (- (u / 2)) := by
    have : - ((x + u) / 2) = - (x / 2) + - (u / 2) := by ring
    rw [this, Real.exp_add]
  rw [h_exp_split]
  have h_reorder : (1 + x) ^ 3 * (1 + u / (1 + x)) ^ 3 * (Real.exp (- (x / 2)) * Real.exp (- (u / 2))) =
      ((1 + x) ^ 3 * Real.exp (- (x / 2))) * ((1 + u / (1 + x)) ^ 3 * Real.exp (- (u / 2))) := by ring
  rw [h_reorder]
  have h_cancel : (1 + u / (1 + x)) ^ 3 * Real.exp (- (u / 2)) ≤ 1 := by
    calc (1 + u / (1 + x)) ^ 3 * Real.exp (- (u / 2))
        ≤ Real.exp (u / 2) * Real.exp (- (u / 2)) :=
          mul_le_mul_of_nonneg_right h_cube (Real.exp_pos _).le
      _ = Real.exp (u / 2 + - (u / 2)) := by rw [← Real.exp_add]
      _ = 1 := by
        have : u / 2 + - (u / 2) = 0 := by ring
        rw [this, Real.exp_zero]
  have h_nonneg : 0 ≤ (1 + x) ^ 3 * Real.exp (- (x / 2)) := by positivity
  calc ((1 + x) ^ 3 * Real.exp (- (x / 2))) * ((1 + u / (1 + x)) ^ 3 * Real.exp (- (u / 2)))
      ≤ ((1 + x) ^ 3 * Real.exp (- (x / 2))) * 1 :=
        mul_le_mul_of_nonneg_left h_cancel h_nonneg
    _ = (1 + x) ^ 3 * Real.exp (- (x / 2)) := mul_one _

lemma cube_exp_neg_le_three_thousand (y : ℝ) (P : ℕ) (hP : 2 ≤ P) (hP_log : Real.log (P : ℝ) ≤ 5)
    (hy_le : (1 + y) ^ 3 * Real.exp (- (y / 2)) ≤ 216) :
    (1 + y) ^ 3 * Real.exp (- (y / 2)) ≤ 3000 * ((1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
  have hP_pos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hsqrt_pos : 0 < Real.sqrt (P : ℝ) := Real.sqrt_pos.mpr hP_pos
  have he5 : Real.exp (5 : ℝ) < 169 := by
    have he1 : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
    have he5_calc : Real.exp (5 : ℝ) = (Real.exp 1) ^ 5 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he5_calc]
    calc (Real.exp 1) ^ 5 ≤ (2.72 : ℝ) ^ 5 := by
          have : 0 ≤ Real.exp 1 := (Real.exp_pos _).le
          gcongr
      _ < 169 := by norm_num
  have hP_le_169 : (P : ℝ) < 169 := by
    calc (P : ℝ) = Real.exp (Real.log (P : ℝ)) := (Real.exp_log hP_pos).symm
      _ ≤ Real.exp 5 := Real.exp_le_exp.mpr hP_log
      _ < 169 := he5
  have hsqrt_le : Real.sqrt (P : ℝ) ≤ 13 := by
    rw [← Real.sqrt_lt_sqrt_iff hP_pos.le] at hP_le_169
    have : Real.sqrt 169 = 13 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
      norm_num
    rw [this] at hP_le_169
    exact hP_le_169.le
  have h_cube : 1 ≤ (1 + Real.log (P : ℝ)) ^ 3 := by
    have h1 : (1 : ℝ) ≤ 1 + Real.log (P : ℝ) := by
      have : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P))
      linarith
    calc (1 : ℝ) = (1 : ℝ) ^ 3 := by norm_num
      _ ≤ (1 + Real.log (P : ℝ)) ^ 3 := by gcongr
  have h216 : 216 ≤ 3000 / Real.sqrt (P : ℝ) := by
    rw [le_div_iff₀ hsqrt_pos]
    nlinarith
  calc (1 + y) ^ 3 * Real.exp (- (y / 2))
      ≤ 216 := hy_le
    _ ≤ 3000 / Real.sqrt (P : ℝ) := h216
    _ = 3000 * (1 / Real.sqrt (P : ℝ)) := by ring
    _ ≤ 3000 * ((1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
        have : 1 / Real.sqrt (P : ℝ) ≤ (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by
          calc 1 / Real.sqrt (P : ℝ) = 1 * (1 / Real.sqrt (P : ℝ)) := by ring
            _ ≤ (1 + Real.log (P : ℝ)) ^ 3 * (1 / Real.sqrt (P : ℝ)) :=
                mul_le_mul_of_nonneg_right h_cube (by positivity)
            _ = (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by ring
        nlinarith

lemma sum_inv_primes_shortPrimeRange_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (P Q : ℕ) (H : ℝ) (v : ℕ),
      2 ≤ P → P ≤ Q → 2 ≤ H → H ≤ Real.sqrt (P : ℝ) →
      v ∈ Finset.Icc ⌊H * Real.log (P : ℝ)⌋₊ ⌈H * Real.log (Q : ℝ)⌉₊ →
      (∑ p ∈ shortPrimeRange P Q H v, (1 : ℝ) / (p : ℝ)) ≤
        C * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
  obtain ⟨C_bt, hC_bt_pos, h_bt⟩ := sum_inv_primes_short_range_le_bt
  let C := 3000 * C_bt + 2
  have hC_pos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC_pos, ?_⟩
  intro P Q H v hP hPQ hH hH_le hv
  have hH_pos : 0 < H := by linarith
  have hP_pos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hP_log_nonneg : 0 ≤ Real.log (P : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P))
  have h_bt_P := h_bt (P : ℝ) H (by exact_mod_cast hP) (by linarith) hH_le
  by_cases hv_lt : (v : ℝ) < H * Real.log (P : ℝ)
  · -- Case A
    have h_sub := shortPrimeRange_subset_insert_caseA P Q H v hP hH_pos hv_lt
    have h_insert := sum_le_insert_sum (shortPrimeRange P Q H v)
      ((Finset.Ioc ⌊(P : ℝ)⌋₊ ⌊(P : ℝ) * Real.exp (1 / H)⌋₊).filter Nat.Prime) P (fun p => 1 / (p : ℝ))
      (fun x => by positivity) h_sub
    have h_inv_P := inv_P_le_cube_div_sqrt P hP
    have h_comb : (1 : ℝ) / (P : ℝ) + (∑ p ∈ (Finset.Ioc ⌊(P : ℝ)⌋₊ ⌊(P : ℝ) * Real.exp (1 / H)⌋₊).filter Nat.Prime, 1 / (p : ℝ))
        ≤ (C_bt + 1) * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
      calc (1 : ℝ) / (P : ℝ) + (∑ p ∈ (Finset.Ioc ⌊(P : ℝ)⌋₊ ⌊(P : ℝ) * Real.exp (1 / H)⌋₊).filter Nat.Prime, 1 / (p : ℝ))
          ≤ (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) + C_bt * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) :=
            add_le_add h_inv_P h_bt_P
        _ ≤ (C_bt + 1) * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
            have : 0 ≤ 1 / (H * Real.log (P : ℝ)) := by positivity
            have : 0 ≤ (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by positivity
            nlinarith
    refine h_insert.trans (h_comb.trans ?_)
    dsimp [C]
    have hp1 : 0 ≤ 1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by positivity
    have : C_bt + 1 ≤ 3000 * C_bt + 2 := by linarith
    exact mul_le_mul_of_nonneg_right this hp1
  · -- Case B
    have hv_ge : H * Real.log (P : ℝ) ≤ (v : ℝ) := not_lt.mp hv_lt
    set x := Real.exp ((v : ℝ) / H) with hx_def
    have hx_pos : 0 < x := Real.exp_pos _
    have hx_ge_P : (P : ℝ) ≤ x := by
      calc (P : ℝ) = Real.exp (Real.log (P : ℝ)) := (Real.exp_log hP_pos).symm
        _ ≤ Real.exp ((v : ℝ) / H) := by
            apply Real.exp_le_exp.mpr
            rw [le_div_iff₀ hH_pos]
            linarith [hv_ge]
    have hP4 : (4 : ℝ) ≤ (P : ℝ) := by
      have : (2 : ℝ) ≤ Real.sqrt (P : ℝ) := hH.trans hH_le
      have h_sq := (sq_le_sq₀ (by norm_num) (Real.sqrt_pos.mpr hP_pos).le).mpr this
      rw [Real.sq_sqrt hP_pos.le] at h_sq
      linarith
    have hx_ge_4 : 4 ≤ x := hP4.trans hx_ge_P
    set M := ⌊x⌋₊ with hM_def
    have hM_pos : 0 < M := by
      have : 4 ≤ M := Nat.le_floor hx_ge_4
      omega
    have hM_pos_real : 0 < (M : ℝ) := by exact_mod_cast hM_pos
    have h_sub := shortPrimeRange_subset_insert_caseB P Q H v
    have h_insert := sum_le_insert_sum (shortPrimeRange P Q H v)
      ((Finset.Ioc M ⌊x * Real.exp (1 / H)⌋₊).filter Nat.Prime) M (fun p => 1 / (p : ℝ))
      (fun x => by positivity) h_sub
    have hx_ge_2 : 2 ≤ x := by
      have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
      linarith
    have hH_le_sqrt_x : H ≤ Real.sqrt x := by
      refine hH_le.trans ?_
      exact Real.sqrt_le_sqrt hx_ge_P
    have h_bt_x := h_bt x H hx_ge_2 (by linarith) hH_le_sqrt_x
    have hlogx_eq : Real.log x = (v : ℝ) / H := Real.log_exp _
    have h_inv_v : 1 / (H * Real.log x) ≤ 1 / (H * Real.log (P : ℝ)) := by
      rw [hlogx_eq]
      have : H * ((v : ℝ) / H) = (v : ℝ) := mul_div_cancel₀ _ hH_pos.ne'
      rw [this]
      have hP_log_pos : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
      have : 0 < H * Real.log (P : ℝ) := mul_pos hH_pos hP_log_pos
      exact one_div_le_one_div_of_le this hv_ge
    have h_cube_x : (1 + Real.log x) ^ 3 / Real.sqrt x ≤ 3000 * ((1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
      set y := (v : ℝ) / H with hy_def
      have h_sqrt_exp : 1 / Real.sqrt x = Real.exp (- (y / 2)) := by
        have h1 : Real.sqrt x = Real.exp (y / 2) := by
          have : y / 2 = Real.log x / 2 := by rw [hlogx_eq]
          rw [this, ← Real.log_sqrt hx_pos.le, Real.exp_log (Real.sqrt_pos.mpr hx_pos)]
        rw [h1, Real.exp_neg, one_div]
      by_cases hP_log5 : Real.log (P : ℝ) ≤ 5
      · have hy_mono : (1 + y) ^ 3 * Real.exp (- (y / 2)) ≤ 216 := by
          by_cases hy5 : 5 ≤ y
          · have h_app := cube_exp_neg_mono (x := 5) (u := y - 5) (by norm_num) (by linarith)
            have h1 : 1 + 5 + (y - 5) = 1 + y := by ring
            have h2 : (5 + (y - 5)) / 2 = y / 2 := by ring
            rw [h1, h2] at h_app
            have h6_3 : (1 + (5 : ℝ)) ^ 3 = 216 := by norm_num
            have he5 : Real.exp (- (5 / 2 : ℝ)) ≤ 1 := by
              rw [← Real.exp_zero]
              exact Real.exp_le_exp.mpr (by norm_num)
            calc (1 + y) ^ 3 * Real.exp (- (y / 2))
                ≤ (1 + 5) ^ 3 * Real.exp (- (5 / 2 : ℝ)) := h_app
              _ ≤ 216 * 1 := by
                  rw [h6_3]
                  refine mul_le_mul_of_nonneg_left he5 (by norm_num)
              _ = 216 := mul_one _
          · have h1y : 1 + y ≤ 6 := by linarith
            have h_cube : (1 + y) ^ 3 ≤ 216 := by
              calc (1 + y) ^ 3 ≤ (6 : ℝ) ^ 3 := by
                    have : 0 ≤ 1 + y := by positivity
                    gcongr
                _ = 216 := by norm_num
            have he : Real.exp (- (y / 2)) ≤ 1 := by
              rw [← Real.exp_zero]
              refine Real.exp_le_exp.mpr ?_
              have : 0 ≤ y / 2 := by positivity
              linarith
            calc (1 + y) ^ 3 * Real.exp (- (y / 2))
                ≤ 216 * 1 := mul_le_mul h_cube he (by positivity) (by norm_num)
              _ = 216 := mul_one _
        have h_bound := cube_exp_neg_le_three_thousand y P hP hP_log5 hy_mono
        calc (1 + Real.log x) ^ 3 / Real.sqrt x
            = (1 + y) ^ 3 * (1 / Real.sqrt x) := by rw [hlogx_eq]; ring
          _ = (1 + y) ^ 3 * Real.exp (- (y / 2)) := by rw [h_sqrt_exp]
          _ ≤ 3000 * ((1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := h_bound
      · have hP_log5_gt : 5 < Real.log (P : ℝ) := not_le.mp hP_log5
        have hy_ge_logP : Real.log (P : ℝ) ≤ y := by
          dsimp [y]
          exact (le_div_iff₀ hH_pos).mpr (by rw [mul_comm]; exact hv_ge)
        set u := y - Real.log (P : ℝ) with hu_def
        have hu_nonneg : 0 ≤ u := by linarith
        have h_app := cube_exp_neg_mono (x := Real.log (P : ℝ)) (u := u) hP_log5_gt.le hu_nonneg
        have h1 : 1 + Real.log (P : ℝ) + u = 1 + y := by dsimp [u]; ring
        have h2 : (Real.log (P : ℝ) + u) / 2 = y / 2 := by dsimp [u]; ring
        rw [h1, h2] at h_app
        have h_sqrt_P : 1 / Real.sqrt (P : ℝ) = Real.exp (- (Real.log (P : ℝ) / 2)) := by
          have h1 : Real.sqrt (P : ℝ) = Real.exp (Real.log (P : ℝ) / 2) := by
            rw [← Real.log_sqrt hP_pos.le, Real.exp_log (Real.sqrt_pos.mpr hP_pos)]
          rw [h1, Real.exp_neg, one_div]
        calc (1 + Real.log x) ^ 3 / Real.sqrt x
            = (1 + y) ^ 3 * (1 / Real.sqrt x) := by rw [hlogx_eq]; ring
          _ = (1 + y) ^ 3 * Real.exp (- (y / 2)) := by rw [h_sqrt_exp]
          _ ≤ (1 + Real.log (P : ℝ)) ^ 3 * Real.exp (- (Real.log (P : ℝ) / 2)) := h_app
          _ = (1 + Real.log (P : ℝ)) ^ 3 * (1 / Real.sqrt (P : ℝ)) := by rw [h_sqrt_P]
          _ = (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by ring
          _ ≤ 3000 * ((1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
              have : 0 ≤ (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by positivity
              linarith
    have h_bt_x_bound : (∑ p ∈ (Finset.Ioc M ⌊x * Real.exp (1 / H)⌋₊).filter Nat.Prime, 1 / (p : ℝ))
        ≤ 3000 * C_bt * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
      calc (∑ p ∈ (Finset.Ioc M ⌊x * Real.exp (1 / H)⌋₊).filter Nat.Prime, 1 / (p : ℝ))
          ≤ C_bt * (1 / (H * Real.log x) + (1 + Real.log x) ^ 3 / Real.sqrt x) := h_bt_x
        _ ≤ C_bt * (1 / (H * Real.log (P : ℝ)) + 3000 * ((1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ))) := by
            refine mul_le_mul_of_nonneg_left (add_le_add h_inv_v h_cube_x) hC_bt_pos.le
        _ ≤ 3000 * C_bt * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
            have : 0 ≤ 1 / (H * Real.log (P : ℝ)) := by positivity
            have : 0 ≤ (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by positivity
            nlinarith
    have h_inv_M : (1 : ℝ) / (M : ℝ) ≤ 2 * ((1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
      have hx_sub1 : x - 1 < (M : ℝ) := Nat.sub_one_lt_floor x
      have hx_div2 : x / 2 ≤ x - 1 := by linarith
      have hM_ge : (P : ℝ) / 2 ≤ (M : ℝ) := by
        calc (P : ℝ) / 2 ≤ x / 2 := by linarith
          _ ≤ x - 1 := hx_div2
          _ ≤ (M : ℝ) := hx_sub1.le
      have h_inv : 1 / (M : ℝ) ≤ 2 / (P : ℝ) := by
        have : 0 < (P : ℝ) / 2 := by positivity
        have h := one_div_le_one_div_of_le this hM_ge
        have : 1 / ((P : ℝ) / 2) = 2 / (P : ℝ) := by ring
        rwa [this] at h
      have h_inv_P := inv_P_le_cube_div_sqrt P hP
      calc 1 / (M : ℝ) ≤ 2 / (P : ℝ) := h_inv
        _ = 2 * (1 / (P : ℝ)) := by ring
        _ ≤ 2 * ((1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) :=
            mul_le_mul_of_nonneg_left h_inv_P (by norm_num)
    refine h_insert.trans ?_
    calc (1 : ℝ) / (M : ℝ) + (∑ p ∈ (Finset.Ioc M ⌊x * Real.exp (1 / H)⌋₊).filter Nat.Prime, 1 / (p : ℝ))
        ≤ 2 * ((1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) +
          3000 * C_bt * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) :=
            add_le_add h_inv_M h_bt_x_bound
      _ ≤ C * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) := by
          dsimp [C]
          have : 0 ≤ 1 / (H * Real.log (P : ℝ)) := by positivity
          have : 0 ≤ (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by positivity
          nlinarith





lemma exp_neg_bound_eight {k y : ℝ} (hk : 0 < k) (hy : 0 < y) :
    y ^ 2 * Real.exp (- (k * y ^ (1 / 4 : ℝ))) ≤ 8 ^ 8 / k ^ 8 := by
  set t := k * y ^ (1 / 4 : ℝ) with ht_def
  have hy14_pos : 0 < y ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hy _
  have ht_pos : 0 < t := mul_pos hk hy14_pos
  set u := t / 8 with hu_def
  have hu_pos : 0 < u := div_pos ht_pos (by norm_num)
  have hu_le_exp : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
  have hu8 : u ^ 8 ≤ (Real.exp u) ^ 8 := by
    have : 0 ≤ u := hu_pos.le
    gcongr
  have hexp8 : (Real.exp u) ^ 8 = Real.exp (8 * u) := by
    rw [← Real.exp_nat_mul]
    rfl
  have h8u : 8 * u = t := by
    dsimp [u]
    ring
  rw [hexp8, h8u] at hu8
  have hu8_eq : u ^ 8 = t ^ 8 / 8 ^ 8 := by
    dsimp [u]
    ring
  rw [hu8_eq] at hu8
  have ht8_eq : t ^ 8 = k ^ 8 * y ^ 2 := by
    dsimp [t]
    rw [mul_pow]
    have h_rpow : (y ^ (1 / 4 : ℝ)) ^ 8 = y ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]
      norm_num
    rw [h_rpow]
  rw [ht8_eq] at hu8
  have h_exp_pos : 0 < Real.exp t := Real.exp_pos t
  have h_frac_pos : 0 < (k ^ 8 * y ^ 2) / 8 ^ 8 := by
    have : 0 < k ^ 8 := by positivity
    have : 0 < y ^ 2 := sq_pos_of_pos hy
    positivity
  have h_inv := one_div_le_one_div_of_le h_frac_pos hu8
  rw [one_div_div, one_div (Real.exp t), ← Real.exp_neg] at h_inv
  have h_mul : y ^ 2 * Real.exp (- t) ≤ y ^ 2 * (8 ^ 8 / (k ^ 8 * y ^ 2)) :=
    mul_le_mul_of_nonneg_left h_inv (by positivity)
  have hy2_ne : y ^ 2 ≠ 0 := (sq_pos_of_pos hy).ne'
  have h_cancel : y ^ 2 * (8 ^ 8 / (k ^ 8 * y ^ 2)) = 8 ^ 8 / k ^ 8 := by
    field_simp
  rw [h_cancel] at h_mul
  exact h_mul

lemma halasz_factor_bound (c₁₁ : ℝ) (hc₁₁ : 0 < c₁₁) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (P P₀ : ℕ) (T : ℝ),
      4 ≤ P → 3 ≤ P₀ → 3 ≤ T → (P : ℝ) / 4 ≤ (P₀ : ℝ) →
      Real.exp (-c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P₀ : ℝ) * T)) ^ 2 ≤
        C * (Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2) := by
  set k := c₁₁ * (2 : ℝ) ^ (-(3 / 4 : ℝ)) with hk_def
  have hk_pos : 0 < k := mul_pos hc₁₁ (Real.rpow_pos_of_pos (by norm_num) _)
  let c := k / 2
  have hc_pos : 0 < c := half_pos hk_pos
  have hc_le_c11_half : c ≤ c₁₁ / 2 := by
    dsimp [c, k]
    have : (2 : ℝ) ^ (-(3 / 4 : ℝ)) ≤ 1 := by
      rw [← Real.rpow_zero 2]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    nlinarith
  let C₁ := 4 * Real.exp (2 * c₁₁)
  have hC₁_pos : 0 < C₁ := by dsimp [C₁]; positivity
  let C₂ := 8 ^ 8 / (k / 2) ^ 8
  have hC₂_pos : 0 < C₂ := by dsimp [C₂]; positivity
  let C := max C₁ C₂
  have hC_pos : 0 < C := lt_max_of_lt_left hC₁_pos
  refine ⟨c, C, hc_pos, hC_pos, ?_⟩
  intro P P₀ T hP hP₀_3 hT hP₀_ge
  have hP_pos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hP₀_pos : 0 < (P₀ : ℝ) := by exact_mod_cast (by omega : 0 < P₀)
  have hT_pos : 0 < T := by linarith
  have hPT_pos : 0 < (P : ℝ) * T := mul_pos hP_pos hT_pos
  have hP₀T_pos : 0 < (P₀ : ℝ) * T := mul_pos hP₀_pos hT_pos
  have hPT_ge_12 : 12 ≤ (P : ℝ) * T := by
    have : (4 : ℝ) * 3 ≤ (P : ℝ) * T := mul_le_mul (by exact_mod_cast hP) hT (by norm_num) (by positivity)
    linarith
  have hlogPT_pos : 0 < Real.log ((P : ℝ) * T) := Real.log_pos (by linarith)
  have hlogP₀T_pos : 0 < Real.log ((P₀ : ℝ) * T) := by
    have : 9 ≤ (P₀ : ℝ) * T := by
      have : (3 : ℝ) * 3 ≤ (P₀ : ℝ) * T := mul_le_mul (by exact_mod_cast hP₀_3) hT (by norm_num) (by positivity)
      linarith
    exact Real.log_pos (by linarith)
  have hlogP₀_pos : 0 < Real.log (P₀ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P₀))
  have hlogP_pos : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P))
  set Hterm := Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 with hH_def
  have hH_nonneg : 0 ≤ Hterm := by dsimp [Hterm]; positivity
  by_cases hcase : (P₀ : ℝ) ≤ (P : ℝ) * T
  · -- Case 1: P₀ ≤ PT
    have hP₀T_le_sq : (P₀ : ℝ) * T ≤ ((P : ℝ) * T) ^ 2 := by
      have h1 : (P₀ : ℝ) * T ≤ ((P : ℝ) * T) * T := mul_le_mul_of_nonneg_right hcase hT_pos.le
      have h2 : ((P : ℝ) * T) * T ≤ ((P : ℝ) * T) * ((P : ℝ) * T) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 1 ≤ (P : ℝ) := by exact_mod_cast (by omega : 1 ≤ P)
        calc T = 1 * T := by ring
          _ ≤ (P : ℝ) * T := mul_le_mul_of_nonneg_right this hT_pos.le
      have h3 : ((P : ℝ) * T) * ((P : ℝ) * T) = ((P : ℝ) * T) ^ 2 := by ring
      linarith
    have hlogP₀T_le_2logPT : Real.log ((P₀ : ℝ) * T) ≤ 2 * Real.log ((P : ℝ) * T) := by
      have h := Real.log_le_log hP₀T_pos hP₀T_le_sq
      rw [Real.log_pow, Nat.cast_two] at h
      exact h
    have h_sq_le : (Real.log ((P₀ : ℝ) * T)) ^ 2 ≤ 4 * (Real.log ((P : ℝ) * T)) ^ 2 := by
      have : (Real.log ((P₀ : ℝ) * T)) ^ 2 ≤ (2 * Real.log ((P : ℝ) * T)) ^ 2 := by
        have : 0 ≤ Real.log ((P₀ : ℝ) * T) := hlogP₀T_pos.le
        gcongr
      have h4 : (2 * Real.log ((P : ℝ) * T)) ^ 2 = 4 * (Real.log ((P : ℝ) * T)) ^ 2 := by ring
      rwa [h4] at this
    have hrpow_le : (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ) ≤ 2 * (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) := by
      have h_rpow := Real.rpow_le_rpow hlogP₀T_pos.le hlogP₀T_le_2logPT (by norm_num : 0 ≤ (3 / 4 : ℝ))
      rw [Real.mul_rpow (by norm_num) hlogPT_pos.le] at h_rpow
      have h2_34 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
        have : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        rwa [Real.rpow_one] at this
      calc (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)
          ≤ (2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) := h_rpow
        _ ≤ 2 * (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_right h2_34 (by positivity)
    have hlogP₀_ge : Real.log (P : ℝ) - Real.log 4 ≤ Real.log (P₀ : ℝ) := by
      have : (P : ℝ) / 4 = (P : ℝ) * (1 / 4) := by ring
      rw [← Real.log_div hP_pos.ne' (by norm_num)]
      exact Real.log_le_log (by positivity) hP₀_ge
    have hlog4_le : Real.log 4 ≤ 2 := by
      rw [← Real.log_exp 2]
      apply Real.log_le_log (by norm_num)
      have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (Real.exp 1) ^ 2 := by nlinarith
        _ = Real.exp 2 := by rw [sq, ← Real.exp_add]; ring_nf
    have h_exp_le : -c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ) ≤
        -(c₁₁ / 2) * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) + 2 * c₁₁ := by
      set A := Real.log (P : ℝ) with hA_def
      set B := Real.log ((P : ℝ) * T) with hB_def
      set A₀ := Real.log (P₀ : ℝ) with hA₀_def
      set B₀ := Real.log ((P₀ : ℝ) * T) with hB₀_def
      have hB_rpow_pos : 0 < B ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hlogPT_pos _
      have hB₀_rpow_pos : 0 < B₀ ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hlogP₀T_pos _
      have hB_rpow_ge_1 : 1 ≤ B ^ (3 / 4 : ℝ) := by
        have hlogPT_ge_1 : 1 ≤ B := by
          have he6 : Real.exp 1 ≤ 12 := Real.exp_one_lt_d9.le.trans (by norm_num)
          rw [← Real.log_exp 1]
          exact Real.log_le_log (Real.exp_pos 1) (he6.trans hPT_ge_12)
        rw [← Real.rpow_zero B]
        have : 0 ≤ (3 / 4 : ℝ) := by norm_num
        exact Real.rpow_le_rpow_of_exponent_le hlogPT_ge_1 this
      have h_frac1 : (A - 2) / (2 * B ^ (3 / 4 : ℝ)) ≤ A₀ / B₀ ^ (3 / 4 : ℝ) := by
        have h_num : A - 2 ≤ A₀ := by linarith [hlogP₀_ge, hlog4_le]
        have h_den : B₀ ^ (3 / 4 : ℝ) ≤ 2 * B ^ (3 / 4 : ℝ) := hrpow_le
        have h_den_pos : 0 < 2 * B ^ (3 / 4 : ℝ) := by positivity
        rw [div_le_div_iff₀ h_den_pos hB₀_rpow_pos]
        by_cases hA2 : A - 2 ≤ 0
        · have hA₀_nonneg : 0 ≤ A₀ := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P₀))
          have : (A - 2) * B₀ ^ (3 / 4 : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hA2 hB₀_rpow_pos.le
          have : 0 ≤ A₀ * (2 * B ^ (3 / 4 : ℝ)) := mul_nonneg hA₀_nonneg h_den_pos.le
          linarith
        · have : 0 ≤ A - 2 := by linarith
          nlinarith
      have h_mult : -c₁₁ * (A₀ / B₀ ^ (3 / 4 : ℝ)) ≤ -c₁₁ * ((A - 2) / (2 * B ^ (3 / 4 : ℝ))) := by
        have : 0 ≤ c₁₁ := hc₁₁.le
        nlinarith
      have h_split : -c₁₁ * ((A - 2) / (2 * B ^ (3 / 4 : ℝ))) =
          -(c₁₁ / 2) * A / B ^ (3 / 4 : ℝ) + c₁₁ / B ^ (3 / 4 : ℝ) := by ring
      rw [h_split] at h_mult
      have h_c_le : c₁₁ / B ^ (3 / 4 : ℝ) ≤ 2 * c₁₁ := by
        have : c₁₁ / B ^ (3 / 4 : ℝ) ≤ c₁₁ / 1 := div_le_div_of_nonneg_left hc₁₁.le (by norm_num) hB_rpow_ge_1
        rw [div_one] at this
        linarith
      calc -c₁₁ * A₀ / B₀ ^ (3 / 4 : ℝ)
          = -c₁₁ * (A₀ / B₀ ^ (3 / 4 : ℝ)) := by ring
        _ ≤ -(c₁₁ / 2) * A / B ^ (3 / 4 : ℝ) + c₁₁ / B ^ (3 / 4 : ℝ) := h_mult
        _ ≤ -(c₁₁ / 2) * A / B ^ (3 / 4 : ℝ) + 2 * c₁₁ := by linarith
    have h_exp_bound : Real.exp (-c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) ≤
        Real.exp (2 * c₁₁) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) := by
      have h := Real.exp_le_exp.mpr h_exp_le
      rw [Real.exp_add] at h
      have h_c_mono : -(c₁₁ / 2) * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) ≤
          -c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) := by
        calc -(c₁₁ / 2) * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)
            = -(c₁₁ / 2) * (Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) := by ring
          _ ≤ -c * (Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) :=
              mul_le_mul_of_nonneg_right (by linarith [hc_le_c11_half]) (by positivity)
          _ = -c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) := by ring
      have h_exp_c := Real.exp_le_exp.mpr h_c_mono
      calc Real.exp (-c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ))
          ≤ Real.exp (-(c₁₁ / 2) * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * Real.exp (2 * c₁₁) := h
        _ ≤ Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * Real.exp (2 * c₁₁) :=
            mul_le_mul_of_nonneg_right h_exp_c (Real.exp_pos _).le
        _ = Real.exp (2 * c₁₁) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) := by ring
    have h1 : Real.exp (-c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P₀ : ℝ) * T)) ^ 2 ≤
        C₁ * Hterm := by
      calc Real.exp (-c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P₀ : ℝ) * T)) ^ 2
          ≤ (Real.exp (2 * c₁₁) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ))) *
            (4 * (Real.log ((P : ℝ) * T)) ^ 2) :=
              mul_le_mul h_exp_bound h_sq_le (sq_nonneg _) (by positivity)
        _ = (4 * Real.exp (2 * c₁₁)) *
            (Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2) := by ring
        _ = C₁ * Hterm := rfl
    have hC₁_le : C₁ ≤ C := le_max_left _ _
    exact h1.trans (mul_le_mul_of_nonneg_right hC₁_le hH_nonneg)
  · -- Case 2: PT < P₀
    have hcase_gt : (P : ℝ) * T < (P₀ : ℝ) := not_le.mp hcase
    have hT_lt_P₀ : T < (P₀ : ℝ) := by
      calc T = 1 * T := by ring
        _ ≤ (P : ℝ) * T := by
            refine mul_le_mul_of_nonneg_right ?_ hT_pos.le
            exact_mod_cast (by omega : 1 ≤ P)
        _ < (P₀ : ℝ) := hcase_gt
    have hP₀T_lt_sq : (P₀ : ℝ) * T < (P₀ : ℝ) ^ 2 := by
      rw [sq]
      exact mul_lt_mul_of_pos_left hT_lt_P₀ hP₀_pos
    have hlogP₀T_le_2logP₀ : Real.log ((P₀ : ℝ) * T) ≤ 2 * Real.log (P₀ : ℝ) := by
      have h := Real.log_le_log hP₀T_pos hP₀T_lt_sq.le
      rw [Real.log_pow, Nat.cast_two] at h
      exact h
    have h_sq_le : (Real.log ((P₀ : ℝ) * T)) ^ 2 ≤ 4 * (Real.log (P₀ : ℝ)) ^ 2 := by
      have : (Real.log ((P₀ : ℝ) * T)) ^ 2 ≤ (2 * Real.log (P₀ : ℝ)) ^ 2 := by
        have : 0 ≤ Real.log ((P₀ : ℝ) * T) := hlogP₀T_pos.le
        gcongr
      have h4 : (2 * Real.log (P₀ : ℝ)) ^ 2 = 4 * (Real.log (P₀ : ℝ)) ^ 2 := by ring
      rwa [h4] at this
    have hrpow_le : (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log (P₀ : ℝ)) ^ (3 / 4 : ℝ) := by
      have h_rpow := Real.rpow_le_rpow hlogP₀T_pos.le hlogP₀T_le_2logP₀ (by norm_num : 0 ≤ (3 / 4 : ℝ))
      rw [Real.mul_rpow (by norm_num) hlogP₀_pos.le] at h_rpow
      exact h_rpow
    have h_frac_ge : (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ) ≤
        Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ) := by
      have hlogP₀T_rpow_pos : 0 < (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hlogP₀T_pos _
      have h2_pos : 0 < (2 : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      have hrpowP₀_pos : 0 < (Real.log (P₀ : ℝ)) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hlogP₀_pos _
      have h_prod_pos : 0 < (2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log (P₀ : ℝ)) ^ (3 / 4 : ℝ) := mul_pos h2_pos hrpowP₀_pos
      have h_div_le : Real.log (P₀ : ℝ) / ((2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log (P₀ : ℝ)) ^ (3 / 4 : ℝ)) ≤
          Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ) :=
        div_le_div_of_nonneg_left hlogP₀_pos.le hlogP₀T_rpow_pos hrpow_le
      have h1 : Real.log (P₀ : ℝ) / (Real.log (P₀ : ℝ)) ^ (3 / 4 : ℝ) = (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ) := by
        calc Real.log (P₀ : ℝ) / (Real.log (P₀ : ℝ)) ^ (3 / 4 : ℝ)
            = (Real.log (P₀ : ℝ)) ^ (1 : ℝ) / (Real.log (P₀ : ℝ)) ^ (3 / 4 : ℝ) := by rw [Real.rpow_one]
          _ = (Real.log (P₀ : ℝ)) ^ ((1 : ℝ) - (3 / 4 : ℝ)) := by rw [← Real.rpow_sub hlogP₀_pos]
          _ = (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ) := by norm_num
      have h2 : (2 : ℝ) ^ (-(3 / 4 : ℝ)) = 1 / (2 : ℝ) ^ (3 / 4 : ℝ) := by
        rw [Real.rpow_neg (by norm_num), one_div]
      have h_simp : Real.log (P₀ : ℝ) / ((2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log (P₀ : ℝ)) ^ (3 / 4 : ℝ)) =
          (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ) := by
        calc Real.log (P₀ : ℝ) / ((2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log (P₀ : ℝ)) ^ (3 / 4 : ℝ))
            = (1 / (2 : ℝ) ^ (3 / 4 : ℝ)) * (Real.log (P₀ : ℝ) / (Real.log (P₀ : ℝ)) ^ (3 / 4 : ℝ)) := by ring
          _ = (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ) := by rw [← h2, h1]
      rwa [h_simp] at h_div_le
    have h_exp_le : Real.exp (-c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) ≤
        Real.exp (- (k * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ))) := by
      apply Real.exp_le_exp.mpr
      have h1 : -c₁₁ * (Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) ≤
          -c₁₁ * ((2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonpos_left h_frac_ge (neg_nonpos.mpr hc₁₁.le)
      have h_eq : -c₁₁ * ((2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ)) =
          - (k * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ)) := by dsimp [k]; ring
      rw [h_eq] at h1
      calc -c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)
          = -c₁₁ * (Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) := by ring
        _ ≤ - (k * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ)) := h1
    have hP_lt_P₀ : (P : ℝ) < (P₀ : ℝ) := by
      calc (P : ℝ) = (P : ℝ) * 1 := by ring
        _ ≤ (P : ℝ) * T := by
            refine mul_le_mul_of_nonneg_left ?_ hP_pos.le
            linarith
        _ < (P₀ : ℝ) := hcase_gt
    have hlogP_lt_logP₀ : Real.log (P : ℝ) < Real.log (P₀ : ℝ) := Real.log_lt_log hP_pos hP_lt_P₀
    have h_exp_split : Real.exp (- (k * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ))) =
        Real.exp (- ((k / 2) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ))) *
        Real.exp (- ((k / 2) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ))) := by
      have h_sum : - (k * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ)) =
          (- ((k / 2) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ))) +
          (- ((k / 2) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ))) := by ring
      rw [h_sum, Real.exp_add]
    have h_exp_P : Real.exp (- ((k / 2) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ))) ≤
        Real.exp (- c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have h1 : (Real.log (P : ℝ)) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) ≤ (Real.log (P : ℝ)) ^ (1 / 4 : ℝ) := by
        have h_PT_ge_P : (P : ℝ) ≤ (P : ℝ) * T := by
          calc (P : ℝ) = (P : ℝ) * 1 := by ring
            _ ≤ (P : ℝ) * T := mul_le_mul_of_nonneg_left (by linarith) hP_pos.le
        have h_log_le : Real.log (P : ℝ) ≤ Real.log ((P : ℝ) * T) := Real.log_le_log hP_pos h_PT_ge_P
        have h_rpow_le : (Real.log (P : ℝ)) ^ (3 / 4 : ℝ) ≤ (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow hlogP_pos.le h_log_le (by norm_num)
        have h_pos_rpow : 0 < (Real.log (P : ℝ)) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hlogP_pos _
        calc Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)
            ≤ Real.log (P : ℝ) / (Real.log (P : ℝ)) ^ (3 / 4 : ℝ) :=
              div_le_div_of_nonneg_left hlogP_pos.le h_pos_rpow h_rpow_le
          _ = (Real.log (P : ℝ)) ^ (1 : ℝ) / (Real.log (P : ℝ)) ^ (3 / 4 : ℝ) := by rw [Real.rpow_one]
          _ = (Real.log (P : ℝ)) ^ (1 / 4 : ℝ) := by
              rw [← Real.rpow_sub hlogP_pos]
              norm_num
      have h2 : - ((k / 2) * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ)) ≤ - ((k / 2) * (Real.log (P : ℝ)) ^ (1 / 4 : ℝ)) := by
        have h_le : (Real.log (P : ℝ)) ^ (1 / 4 : ℝ) ≤ (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ) :=
          Real.rpow_le_rpow hlogP_pos.le hlogP_lt_logP₀.le (by norm_num)
        have h_pos : 0 ≤ k / 2 := by positivity
        exact neg_le_neg (mul_le_mul_of_nonneg_left h_le h_pos)
      have h3 : - ((k / 2) * (Real.log (P : ℝ)) ^ (1 / 4 : ℝ)) ≤
          - ((k / 2) * (Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ))) := by
        have h_pos : 0 ≤ k / 2 := by positivity
        exact neg_le_neg (mul_le_mul_of_nonneg_left h1 h_pos)
      have h_trans := h2.trans h3
      have h_c : - ((k / 2) * (Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ))) =
          - c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) := by
        dsimp [c]; ring
      rwa [h_c] at h_trans
    have hk2_pos : 0 < k / 2 := by positivity
    have h_eight := exp_neg_bound_eight hk2_pos hlogP₀_pos
    have h_prod_eight : (Real.log (P₀ : ℝ)) ^ 2 * Real.exp (- (k * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ))) ≤
        (8 ^ 8 / (k / 2) ^ 8) * Real.exp (- c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) := by
      rw [h_exp_split, ← mul_assoc]
      exact mul_le_mul h_eight h_exp_P (Real.exp_pos _).le (by positivity)
    have he2_le_12 : Real.exp 2 ≤ 12 := by
      have he : Real.exp 1 ≤ 2.72 := Real.exp_one_lt_d9.le.trans (by norm_num)
      have h_sq : Real.exp 2 = (Real.exp 1) ^ 2 := by rw [sq, ← Real.exp_add]; ring_nf
      rw [h_sq]
      have he_nonneg : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
      calc (Real.exp 1) ^ 2 = (Real.exp 1) * (Real.exp 1) := sq (Real.exp 1)
        _ ≤ (2.72 : ℝ) * 2.72 := mul_le_mul he he he_nonneg (by norm_num)
        _ ≤ 12 := by norm_num
    have h2_le_log : (2 : ℝ) ≤ Real.log ((P : ℝ) * T) := by
      rw [← Real.log_exp 2]
      exact Real.log_le_log (Real.exp_pos 2) (he2_le_12.trans hPT_ge_12)
    have h4_le_sq : (4 : ℝ) ≤ (Real.log ((P : ℝ) * T)) ^ 2 := by
      calc (4 : ℝ) = (2 : ℝ) * 2 := by norm_num
        _ ≤ Real.log ((P : ℝ) * T) * Real.log ((P : ℝ) * T) :=
          mul_le_mul h2_le_log h2_le_log (by norm_num) (by positivity)
        _ = (Real.log ((P : ℝ) * T)) ^ 2 := (sq _).symm
    have h2 : Real.exp (-c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P₀ : ℝ) * T)) ^ 2 ≤
        C₂ * Hterm := by
      calc Real.exp (-c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P₀ : ℝ) * T)) ^ 2
          ≤ Real.exp (- (k * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ))) * (4 * (Real.log (P₀ : ℝ)) ^ 2) :=
            mul_le_mul h_exp_le h_sq_le (sq_nonneg _) (Real.exp_pos _).le
        _ = 4 * ((Real.log (P₀ : ℝ)) ^ 2 * Real.exp (- (k * (Real.log (P₀ : ℝ)) ^ (1 / 4 : ℝ)))) := by ring
        _ ≤ 4 * ((8 ^ 8 / (k / 2) ^ 8) * Real.exp (- c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left h_prod_eight (by norm_num)
        _ = (8 ^ 8 / (k / 2) ^ 8) * (4 * Real.exp (- c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ))) := by ring
        _ ≤ (8 ^ 8 / (k / 2) ^ 8) * (Real.exp (- c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hC₂_pos.le
            have hp_exp : 0 ≤ Real.exp (- c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) := (Real.exp_pos _).le
            calc 4 * Real.exp (- c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ))
                = Real.exp (- c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * 4 := by ring
              _ ≤ Real.exp (- c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 :=
                  mul_le_mul_of_nonneg_left h4_le_sq hp_exp
        _ = C₂ * Hterm := rfl
    have hC₂_le : C₂ ≤ C := le_max_right _ _
    exact h2.trans (mul_le_mul_of_nonneg_right hC₂_le hH_nonneg)



lemma three_le_P₀ (P Q : ℕ) (H : ℝ) (v : ℕ) (hP : 4 ≤ P) (hH : 2 ≤ H)
    (p : ℕ) (hp : p ∈ shortPrimeRange P Q H v) :
    3 ≤ ⌈Real.exp ((v : ℝ) / H)⌉₊ - 1 := by
  have hP_pos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  rw [mem_shortPrimeRange] at hp
  have hpP : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.2.1
  have hp_prime : Nat.Prime p := hp.1.1
  have hp_ge_5 : 5 ≤ (p : ℝ) := by
    have : 4 ≤ p := by omega
    have : 5 ≤ p := by
      rcases eq_or_lt_of_le this with rfl | hgt
      · exfalso; revert hp_prime; decide
      · exact hgt
    exact_mod_cast this
  have hp_lt : (p : ℝ) < Real.exp (((v : ℝ) + 1) / H) := hp.2.2
  set x := Real.exp ((v : ℝ) / H) with hx_def
  have hx_pos : 0 < x := Real.exp_pos _
  have h_add : ((v : ℝ) + 1) / H = (v : ℝ) / H + 1 / H := by ring
  rw [h_add, Real.exp_add] at hp_lt
  have he1 : Real.exp (1 / H) ≤ 1.65 := by
    have h1 : Real.exp (1 / H) ≤ Real.exp (1 / 2) := by
      apply Real.exp_le_exp.mpr
      exact one_div_le_one_div_of_le (by norm_num) hH
    have h2 : Real.exp (1 / 2 : ℝ) ≤ 1.65 := by
      have hpos : 0 ≤ Real.exp (1 / 2 : ℝ) := (Real.exp_pos _).le
      have h165 : 0 ≤ (1.65 : ℝ) := by norm_num
      rw [← sq_le_sq₀ hpos h165]
      have h_sq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
        rw [sq, ← Real.exp_add]
        ring_nf
      rw [h_sq]
      have : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
      linarith
    linarith
  have h5_lt : (5 : ℝ) < 1.65 * x := by
    calc (5 : ℝ) ≤ (p : ℝ) := hp_ge_5
      _ < x * Real.exp (1 / H) := hp_lt
      _ ≤ x * 1.65 := mul_le_mul_of_nonneg_left he1 hx_pos.le
      _ = 1.65 * x := mul_comm _ _
  have hx_gt_3 : 3 < x := by linarith
  have hceil : 4 ≤ ⌈x⌉₊ := by
    have : (3 : ℝ) < (⌈x⌉₊ : ℝ) := hx_gt_3.trans_le (Nat.le_ceil x)
    exact_mod_cast this
  omega

lemma P_div_four_le_P₀ (P Q : ℕ) (H : ℝ) (v : ℕ) (hP : 4 ≤ P) (hH : 2 ≤ H)
    (p : ℕ) (hp : p ∈ shortPrimeRange P Q H v) :
    (P : ℝ) / 4 ≤ ((⌈Real.exp ((v : ℝ) / H)⌉₊ - 1 : ℕ) : ℝ) := by
  have hP_pos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  rw [mem_shortPrimeRange] at hp
  have hpP : (P : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1.2.1
  have hp_lt : (p : ℝ) < Real.exp (((v : ℝ) + 1) / H) := hp.2.2
  set x := Real.exp ((v : ℝ) / H) with hx_def
  have hx_pos : 0 < x := Real.exp_pos _
  have h_add : ((v : ℝ) + 1) / H = (v : ℝ) / H + 1 / H := by ring
  rw [h_add, Real.exp_add] at hp_lt
  have he1 : Real.exp (1 / H) ≤ 1.65 := by
    have h1 : Real.exp (1 / H) ≤ Real.exp (1 / 2) := by
      apply Real.exp_le_exp.mpr
      exact one_div_le_one_div_of_le (by norm_num) hH
    have h2 : Real.exp (1 / 2 : ℝ) ≤ 1.65 := by
      have hpos : 0 ≤ Real.exp (1 / 2 : ℝ) := (Real.exp_pos _).le
      have h165 : 0 ≤ (1.65 : ℝ) := by norm_num
      rw [← sq_le_sq₀ hpos h165]
      have h_sq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
        rw [sq, ← Real.exp_add]
        ring_nf
      rw [h_sq]
      have : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
      linarith
    linarith
  have hP_lt_165x : (P : ℝ) < 1.65 * x := by
    calc (P : ℝ) ≤ (p : ℝ) := hpP
      _ < x * Real.exp (1 / H) := hp_lt
      _ ≤ x * 1.65 := mul_le_mul_of_nonneg_left he1 hx_pos.le
      _ = 1.65 * x := mul_comm _ _
  have hx_gt_2 : 2 ≤ x := by
    have : (4 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceil_pos : 1 ≤ ⌈x⌉₊ := by
    have : (2 : ℝ) ≤ (⌈x⌉₊ : ℝ) := hx_gt_2.trans (Nat.le_ceil x)
    have : 2 ≤ ⌈x⌉₊ := by exact_mod_cast this
    omega
  have h_cast : ((⌈x⌉₊ - 1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) - 1 := by
    push_cast [hceil_pos]
    rfl
  rw [h_cast]
  have h_sub1 : (P : ℝ) / 4 ≤ x - 1 := by
    calc (P : ℝ) / 4 ≤ 1.65 * x / 4 := by linarith [hP_lt_165x]
      _ = 0.4125 * x := by ring
      _ ≤ x - 1 := by linarith
  linarith

lemma P₀_bounds {x : ℝ} (hx : 3 < x) :
    let P₀ := ⌈x⌉₊ - 1
    (P₀ : ℝ) < x ∧ x ≤ (P₀ : ℝ) + 1 := by
  intro P₀
  have hceil : 4 ≤ ⌈x⌉₊ := by
    have : (3 : ℝ) < (⌈x⌉₊ : ℝ) := hx.trans_le (Nat.le_ceil x)
    exact_mod_cast this
  have h_one_le : 1 ≤ ⌈x⌉₊ := by omega
  have h_cast : (P₀ : ℝ) = (⌈x⌉₊ : ℝ) - 1 := by
    dsimp [P₀]
    push_cast [h_one_le]
    rfl
  refine ⟨?_, ?_⟩
  · rw [h_cast]
    have h1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  · rw [h_cast]
    have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    linarith



lemma Qpoly_empty {β : ℝ} {X P Q : ℕ} {H : ℝ} {v : ℕ} (s : ℂ)
    (h : shortPrimeRange P Q H v = ∅) :
    Qpoly β X P Q H v s = 0 := by
  unfold Qpoly dirichletPoly
  rw [h, Finset.sum_empty]

lemma sum_wellSpaced_norm_sq_Qpoly_le (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (T : ℝ) (𝒯 : Finset ℝ),
      3 / 4 ≤ β → β < 1 → 16 ≤ X → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ (X : ℝ) ^ β → 2 ≤ H → H ≤ Real.sqrt (P : ℝ) →
      v ∈ Finset.Icc ⌊H * Real.log (P : ℝ)⌋₊ ⌈H * Real.log (Q : ℝ)⌉₊ →
      3 ≤ T → T ≤ (X : ℝ) → WellSpaced 𝒯 → (∀ t ∈ 𝒯, |t| ≤ T) →
      (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) *
          ((H / (v : ℝ)) * (1 + 𝒯.card * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2)) := by
  obtain ⟨c₁₁, C₁₁, hc₁₁_pos, hC₁₁_pos, h_halasz⟩ := sum_wellSpaced_norm_sq_prime_poly_le c₀ K hc₀ hK hζ hholo
  obtain ⟨c, C_ratio, hc_pos, hC_ratio_pos, h_ratio⟩ := halasz_factor_bound c₁₁ hc₁₁_pos
  obtain ⟨C_bt, hC_bt_pos, h_bt⟩ := sum_inv_primes_shortPrimeRange_le
  let C := 2 * C₁₁ * (C_ratio + 1) * C_bt
  have hC_pos : 0 < C := by dsimp [C]; positivity
  refine ⟨c, C, hc_pos, hC_pos, ?_⟩
  intro β X P Q H v T 𝒯 hβ hβ1 hX hP hPQ hQX hH hH_le hv hT hTX hwell ht_le
  have hH_pos : 0 < H := by linarith
  have hP_pos : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hP_ge_4 : 4 ≤ P := by
    have : (2 : ℝ) ≤ Real.sqrt (P : ℝ) := hH.trans hH_le
    have h_sq := (sq_le_sq₀ (by norm_num) (Real.sqrt_pos.mpr hP_pos).le).mpr this
    rw [Real.sq_sqrt hP_pos.le] at h_sq
    exact_mod_cast (by linarith : (4 : ℝ) ≤ (P : ℝ))
  by_cases h_empty : shortPrimeRange P Q H v = ∅
  · have h_zero : ∀ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2 = 0 := by
      intro t ht
      rw [Qpoly_empty _ h_empty, norm_zero, sq, mul_zero]
    rw [Finset.sum_congr rfl h_zero, Finset.sum_const_zero]
    have hp1 : 0 ≤ 1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by positivity
    have hp2 : 0 ≤ H / (v : ℝ) := by positivity
    have hp3 : 0 ≤ 1 + 𝒯.card * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 := by positivity
    positivity
  · have h_nonempty : (shortPrimeRange P Q H v).Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    obtain ⟨p₀, hp₀⟩ := h_nonempty
    set x := Real.exp ((v : ℝ) / H) with hx_def
    have hx_pos : 0 < x := Real.exp_pos _
    set P₀ := ⌈x⌉₊ - 1 with hP₀_def
    have hP₀_3 : 3 ≤ P₀ := three_le_P₀ P Q H v hP_ge_4 hH p₀ hp₀
    have hx_gt_3 : 3 < x := by
      have : 3 ≤ ⌈x⌉₊ - 1 := hP₀_3
      have : 4 ≤ ⌈x⌉₊ := by omega
      have h4 : (4 : ℝ) ≤ (⌈x⌉₊ : ℝ) := by exact_mod_cast this
      have hceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    have hP₀_bds := P₀_bounds hx_gt_3
    have hP₀_le : (P₀ : ℝ) < x := hP₀_bds.1
    have hP₀_ge : x ≤ (P₀ : ℝ) + 1 := hP₀_bds.2
    have hP₀_4 : (P : ℝ) / 4 ≤ (P₀ : ℝ) := P_div_four_le_P₀ P Q H v hP_ge_4 hH p₀ hp₀
    have hsub : shortPrimeRange P Q H v ⊆ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime :=
      shortPrimeRange_subset_Ioc_prime_usetlarge P Q H v hH P₀ hP₀_le hP₀_ge hP₀_3
    have hP₀_pos : 0 < (P₀ : ℝ) := by exact_mod_cast (by omega : 0 < P₀)
    have hlogP₀_pos : 0 < Real.log (P₀ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < P₀))
    set a_coeff : ℕ → ℂ := fun p => if p ∈ shortPrimeRange P Q H v then fX β X p else 0
    have h_dir_eq : ∀ t, dirichletPoly a_coeff ((Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I) =
        Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) := fun t => dirichletPoly_eq_Qpoly_usetlarge β X P Q H v P₀ hsub _
    have h_hal := h_halasz P₀ a_coeff T 𝒯 hP₀_3 hT hwell ht_le
    have h_rewrite_sum : (∑ t ∈ 𝒯, ‖dirichletPoly a_coeff ((Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I)‖ ^ 2) =
        ∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun t ht => by rw [h_dir_eq t])
    rw [h_rewrite_sum] at h_hal
    have h_coeff_le := sum_norm_sq_coeff_le β X P Q H v P₀ hlogP₀_pos hsub
    have h_inv_sq := sum_inv_sq_le_inv_P₀_mul_sum_inv P Q H v P₀ hP₀_pos hP₀_le
    have h_sum_inv := h_bt P Q H v (by exact_mod_cast hP) hPQ hH hH_le hv
    set E := Real.exp (-c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P₀ : ℝ) * T)) ^ 2 with hE_def
    set S_primes := ∑ p ∈ shortPrimeRange P Q H v, (1 : ℝ) / (p : ℝ) with hS_def
    have h_coeff_comb : (∑ p ∈ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime,
        ‖a_coeff p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log (P₀ : ℝ))) ≤
        (1 / Real.log (P₀ : ℝ)) * ((1 / (P₀ : ℝ)) * S_primes) := by
      calc (∑ p ∈ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime,
          ‖a_coeff p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log (P₀ : ℝ)))
          ≤ (1 / Real.log (P₀ : ℝ)) * ∑ p ∈ shortPrimeRange P Q H v, (1 : ℝ) / (p : ℝ) ^ 2 := h_coeff_le
        _ ≤ (1 / Real.log (P₀ : ℝ)) * ((1 / (P₀ : ℝ)) * S_primes) :=
            mul_le_mul_of_nonneg_left h_inv_sq (by positivity)
    have h_hal_comb : (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C₁₁ * (((P₀ : ℝ) + (P₀ : ℝ) * ((𝒯.card : ℝ) * E)) * ((1 / Real.log (P₀ : ℝ)) * ((1 / (P₀ : ℝ)) * S_primes))) := by
      have h1 : ((P₀ : ℝ) + (𝒯.card : ℝ) * (P₀ : ℝ) * Real.exp (-c₁₁ * Real.log (P₀ : ℝ) / (Real.log ((P₀ : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P₀ : ℝ) * T)) ^ 2) =
          (P₀ : ℝ) + (P₀ : ℝ) * ((𝒯.card : ℝ) * E) := by
        dsimp [E]; ring
      rw [h1] at h_hal
      have hp_P0 : 0 ≤ (P₀ : ℝ) + (P₀ : ℝ) * ((𝒯.card : ℝ) * E) := by positivity
      have h_prod : ((P₀ : ℝ) + (P₀ : ℝ) * ((𝒯.card : ℝ) * E)) * (∑ p ∈ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime,
          ‖a_coeff p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log (P₀ : ℝ))) ≤
          ((P₀ : ℝ) + (P₀ : ℝ) * ((𝒯.card : ℝ) * E)) * ((1 / Real.log (P₀ : ℝ)) * ((1 / (P₀ : ℝ)) * S_primes)) :=
            mul_le_mul_of_nonneg_left h_coeff_comb hp_P0
      calc (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2)
          ≤ C₁₁ * (((P₀ : ℝ) + (P₀ : ℝ) * ((𝒯.card : ℝ) * E)) * (∑ p ∈ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime,
            ‖a_coeff p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log (P₀ : ℝ)))) := by
              rw [← mul_assoc]
              exact h_hal
        _ ≤ C₁₁ * (((P₀ : ℝ) + (P₀ : ℝ) * ((𝒯.card : ℝ) * E)) * ((1 / Real.log (P₀ : ℝ)) * ((1 / (P₀ : ℝ)) * S_primes))) :=
            mul_le_mul_of_nonneg_left h_prod hC₁₁_pos.le
    have h_cancel := cancel_P₀_bound P₀ hP₀_pos hlogP₀_pos ((𝒯.card : ℝ) * E) S_primes
    rw [h_cancel] at h_hal_comb
    have hv_pos : 0 < (v : ℝ) := by
      by_contra! hv0
      have hv_le_0 : v ≤ 0 := by exact_mod_cast hv0
      have hv0_nat : v = 0 := by omega
      have hp0_mem := hp₀
      rw [mem_shortPrimeRange] at hp0_mem
      have hp0_lt := hp0_mem.2.2
      rw [hv0_nat] at hp0_lt
      push_cast at hp0_lt
      have h1H : (0 + 1 : ℝ) / H = 1 / H := by ring
      rw [h1H] at hp0_lt
      have he1 : Real.exp (1 / H) ≤ 1.65 := by
        have h1 : Real.exp (1 / H) ≤ Real.exp (1 / 2) := by
          apply Real.exp_le_exp.mpr
          exact one_div_le_one_div_of_le (by norm_num) hH
        have h2 : Real.exp (1 / 2 : ℝ) ≤ 1.65 := by
          have hpos : 0 ≤ Real.exp (1 / 2 : ℝ) := (Real.exp_pos _).le
          have h165 : 0 ≤ (1.65 : ℝ) := by norm_num
          rw [← sq_le_sq₀ hpos h165]
          have h_sq : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
            rw [sq, ← Real.exp_add]
            ring_nf
          rw [h_sq]
          have : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
          linarith
        linarith
      have hp0_ge_4 : (4 : ℝ) ≤ (p₀ : ℝ) := by
        have : 4 ≤ P := hP_ge_4
        have : P ≤ p₀ := hp0_mem.1.2.1
        exact_mod_cast (by omega : 4 ≤ p₀)
      linarith
    have h_inv_log := inv_log_P₀_le_two_mul_H_div_v H v P₀ hH_pos hv_pos (by omega) hP₀_ge
    set Hterm := Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 with hHterm_def
    have hHterm_nonneg : 0 ≤ Hterm := mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
    have h_ratio_app := h_ratio P P₀ T hP_ge_4 hP₀_3 hT hP₀_4
    have h_card_E : (1 : ℝ) + (𝒯.card : ℝ) * E ≤ (C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm) := by
      have hp_card : 0 ≤ (𝒯.card : ℝ) := Nat.cast_nonneg _
      have h1 : (𝒯.card : ℝ) * E ≤ C_ratio * (𝒯.card : ℝ) * Hterm := by
        calc (𝒯.card : ℝ) * E ≤ (𝒯.card : ℝ) * (C_ratio * Hterm) :=
              mul_le_mul_of_nonneg_left h_ratio_app hp_card
          _ = C_ratio * (𝒯.card : ℝ) * Hterm := by ring
      calc (1 : ℝ) + (𝒯.card : ℝ) * E
          ≤ 1 + C_ratio * (𝒯.card : ℝ) * Hterm := by linarith [h1]
        _ ≤ (C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm) := by
            have : 0 ≤ C_ratio := hC_ratio_pos.le
            have : 0 ≤ (𝒯.card : ℝ) * Hterm := mul_nonneg hp_card hHterm_nonneg
            nlinarith
    have h_reorder : C₁₁ * ((1 + (𝒯.card : ℝ) * E) * (1 / Real.log (P₀ : ℝ)) * S_primes) ≤
        C * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) *
          ((H / (v : ℝ)) * (1 + 𝒯.card * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2)) := by
      have h_cr : 0 ≤ C_ratio + 1 := by linarith [hC_ratio_pos]
      have h_card_term : 0 ≤ 1 + (𝒯.card : ℝ) * Hterm := by
        have : 0 ≤ (𝒯.card : ℝ) * Hterm := mul_nonneg (Nat.cast_nonneg _) hHterm_nonneg
        linarith
      have hp_card : 0 ≤ (C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm) :=
        mul_nonneg h_cr h_card_term
      have hp_inv : 0 ≤ 1 / Real.log (P₀ : ℝ) := one_div_nonneg.mpr hlogP₀_pos.le
      have hp_2Hv : 0 ≤ 2 * (H / (v : ℝ)) :=
        mul_nonneg (by norm_num) (div_nonneg hH_pos.le (Nat.cast_nonneg _))
      have hp_prod : 0 ≤ (C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm) * (2 * (H / (v : ℝ))) :=
        mul_nonneg hp_card hp_2Hv
      have hp_S : 0 ≤ S_primes :=
        Finset.sum_nonneg (fun p _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))
      have h1 : (1 + (𝒯.card : ℝ) * E) * (1 / Real.log (P₀ : ℝ)) ≤ (C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm) * (2 * (H / (v : ℝ))) := by
        calc (1 + (𝒯.card : ℝ) * E) * (1 / Real.log (P₀ : ℝ))
            ≤ ((C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm)) * (1 / Real.log (P₀ : ℝ)) :=
              mul_le_mul_of_nonneg_right h_card_E hp_inv
          _ ≤ ((C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm)) * (2 * (H / (v : ℝ))) :=
              mul_le_mul_of_nonneg_left h_inv_log hp_card
      have h2 : ((1 + (𝒯.card : ℝ) * E) * (1 / Real.log (P₀ : ℝ))) * S_primes ≤
          ((C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm) * (2 * (H / (v : ℝ)))) *
            (C_bt * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ))) := by
        calc ((1 + (𝒯.card : ℝ) * E) * (1 / Real.log (P₀ : ℝ))) * S_primes
            ≤ ((C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm) * (2 * (H / (v : ℝ)))) * S_primes :=
              mul_le_mul_of_nonneg_right h1 hp_S
          _ ≤ ((C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm) * (2 * (H / (v : ℝ)))) *
              (C_bt * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ))) :=
              mul_le_mul_of_nonneg_left h_sum_inv hp_prod
      calc C₁₁ * ((1 + (𝒯.card : ℝ) * E) * (1 / Real.log (P₀ : ℝ)) * S_primes)
          ≤ C₁₁ * (((C_ratio + 1) * (1 + (𝒯.card : ℝ) * Hterm) * (2 * (H / (v : ℝ)))) *
              (C_bt * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)))) :=
            mul_le_mul_of_nonneg_left h2 hC₁₁_pos.le
        _ = (2 * C₁₁ * (C_ratio + 1) * C_bt) *
            (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) *
            ((H / (v : ℝ)) * (1 + (𝒯.card : ℝ) * Hterm)) := by ring
        _ = C * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) *
            ((H / (v : ℝ)) * (1 + (𝒯.card : ℝ) * Hterm)) := by
              rfl
        _ = C * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) *
            ((H / (v : ℝ)) * (1 + 𝒯.card * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2)) := by
              rw [hHterm_def, mul_assoc (𝒯.card : ℝ)]
    exact h_hal_comb.trans h_reorder


/-- Proposition 1 (large primes, Section 8.3 of Matomäki-Radziwiłł):
$T_L$ bound for the large-prime polynomial multiplied by the cofactor polynomial. -/
theorem sum_large_prime_poly_mul_le (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (T τ Z : ℝ) (𝒯 : Finset ℝ),
      3 / 4 ≤ β → β < 1 → 16 ≤ X → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ (X : ℝ) ^ β → 2 ≤ H → H ≤ Real.sqrt P →
      v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊ →
      3 ≤ T → T ≤ X → 1 ≤ τ → WellSpaced 𝒯 → (∀ t ∈ 𝒯, τ ≤ |t| ∧ |t| ≤ T) →
      (Q : ℝ) < Z → 4 ≤ Z → Z ≤ Real.sqrt X → Real.log X ≤ (Real.log (Z - 1)) ^ (5 / 4 : ℝ) →
      (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C * ((Real.log X + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
          (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
          ((H / (v : ℝ)) * (1 + 𝒯.card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2)) := by
  obtain ⟨c_R, C_R, hc_R_pos, hC_R_pos, h_Rv⟩ := norm_Rv_le_of_region c₀ K hc₀ hK hζ hholo
  obtain ⟨c_Q, C_Q, hc_Q_pos, hC_Q_pos, h_Qpoly⟩ := sum_wellSpaced_norm_sq_Qpoly_le c₀ K hc₀ hK hζ hholo
  let c := min c_R c_Q
  let C := C_R ^ 2 * C_Q
  have hc_pos : 0 < c := lt_min hc_R_pos hc_Q_pos
  have hC_pos : 0 < C := mul_pos (sq_pos_of_pos hC_R_pos) hC_Q_pos
  refine ⟨c, C, hc_pos, hC_pos, ?_⟩
  intro β X P Q H v T τ Z 𝒯 hβ hβ1 hX hP hPQ hQX hH hHP hv hT hTX hτ hwell ht_bounds hQZ hZ hZX hlogX
  have ht_le : ∀ t ∈ 𝒯, |t| ≤ T := fun t ht => (ht_bounds t ht).2
  have ht_ge : ∀ t ∈ 𝒯, τ ≤ |t| := fun t ht => (ht_bounds t ht).1
  have ht_le_X : ∀ t ∈ 𝒯, |t| ≤ X := fun t ht => (ht_le t ht).trans (by exact_mod_cast hTX)
  have hc_le_c_R : c ≤ c_R := min_le_left _ _
  have hc_le_c_Q : c ≤ c_Q := min_le_right _ _
  have hH_ge1 : 1 ≤ H := by linarith [hH]
  have hRv_t : ∀ t ∈ 𝒯,
      ‖dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ≤
        C_R * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) := by
    intro t ht
    have h1 := h_Rv β X P Q H v t τ Z hβ hβ1 hX hP hPQ hQX hH_ge1 hv hτ (ht_ge t ht) (ht_le_X t ht) hQZ hZ hZX hlogX
    have hZ_sub1_gt_one : 1 < Z - 1 := by linarith
    have h_log_Zsub1_pos : 0 < Real.log (Z - 1) := Real.log_pos hZ_sub1_gt_one
    have h_rpow_nonneg : 0 ≤ (Real.log (Z - 1)) ^ (1 / 16 : ℝ) :=
      Real.rpow_nonneg h_log_Zsub1_pos.le _
    have h_exp_mono : Real.exp (-c_R * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) ≤ Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have : -c_R ≤ -c := by linarith [hc_le_c_R]
      exact mul_le_mul_of_nonneg_right this h_rpow_nonneg
    have h_logX_nonneg : 0 ≤ Real.log (X : ℝ) + 2 := by
      have : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
      linarith
    have h_mono : ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c_R * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
            + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ≤
        ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
            + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) := by
      refine add_le_add (add_le_add ?_ le_rfl) le_rfl
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl h_exp_mono) h_logX_nonneg
    refine h1.trans (mul_le_mul_of_nonneg_left h_mono hC_R_pos.le)
  have h_summand : ∀ t ∈ 𝒯,
      ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
          (C_R ^ 2 * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2) := by
    intro t ht
    rw [norm_mul, mul_pow]
    have hR := hRv_t t ht
    have hB_nonneg : 0 ≤ C_R * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) :=
      (norm_nonneg _).trans hR
    have hR_sq : ‖dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        (C_R * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ))) ^ 2 := by
      rw [sq, sq]
      exact mul_le_mul hR hR (norm_nonneg _) hB_nonneg
    have h_prod_sq : (C_R * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ))) ^ 2 =
        C_R ^ 2 * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 := mul_pow C_R _ 2
    rw [h_prod_sq] at hR_sq
    exact mul_le_mul_of_nonneg_left hR_sq (sq_nonneg _)
  have h_sum_le :
      (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2) *
          (C_R ^ 2 * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2) := by
    calc (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2)
        ≤ ∑ t ∈ 𝒯, (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
          (C_R ^ 2 * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2)) :=
          Finset.sum_le_sum (fun t ht => h_summand t ht)
      _ = (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2) *
          (C_R ^ 2 * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2) := by
          rw [← Finset.sum_mul]
  have hQ_bound := h_Qpoly β X P Q H v T 𝒯 hβ hβ1 hX hP hPQ hQX hH hHP hv hT (by exact_mod_cast hTX) hwell ht_le
  have hP_gt_one : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hlogP_pos : 0 < Real.log (P : ℝ) := Real.log_pos hP_gt_one
  have hPT_gt_one : 1 < (P : ℝ) * T := by
    have : (2 : ℝ) * 3 ≤ (P : ℝ) * T := mul_le_mul (by exact_mod_cast hP) (by linarith) (by norm_num) (by positivity)
    linarith
  have hlogPT_pos : 0 < Real.log ((P : ℝ) * T) := Real.log_pos hPT_gt_one
  have h_rpowPT_pos : 0 < (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hlogPT_pos _
  have h_expQ_mono : Real.exp (-c_Q * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) ≤
      Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have : -c_Q ≤ -c := by linarith [hc_le_c_Q]
    have : -c_Q * Real.log (P : ℝ) ≤ -c * Real.log (P : ℝ) :=
      mul_le_mul_of_nonneg_right this hlogP_pos.le
    exact div_le_div_of_nonneg_right this h_rpowPT_pos.le
  have h_card_sq_nonneg : 0 ≤ (𝒯.card : ℝ) * (Real.log ((P : ℝ) * T)) ^ 2 := by
    have : 0 ≤ (𝒯.card : ℝ) := Nat.cast_nonneg _
    have : 0 ≤ (Real.log ((P : ℝ) * T)) ^ 2 := sq_nonneg _
    positivity
  have h_term1 : 1 + (𝒯.card : ℝ) * Real.exp (-c_Q * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 ≤
      1 + (𝒯.card : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 := by
    have : (𝒯.card : ℝ) * Real.exp (-c_Q * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 =
        Real.exp (-c_Q * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * ((𝒯.card : ℝ) * (Real.log ((P : ℝ) * T)) ^ 2) := by ring
    rw [this]
    have : (𝒯.card : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 =
        Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * ((𝒯.card : ℝ) * (Real.log ((P : ℝ) * T)) ^ 2) := by ring
    rw [this]
    refine add_le_add le_rfl (mul_le_mul_of_nonneg_right h_expQ_mono h_card_sq_nonneg)
  have hHv_nonneg : 0 ≤ H / (v : ℝ) := div_nonneg (by linarith) (Nat.cast_nonneg v)
  have hBT_nonneg : 0 ≤ 1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) := by
    have h1 : 0 ≤ 1 / (H * Real.log (P : ℝ)) := div_nonneg (by norm_num) (mul_nonneg (by linarith) hlogP_pos.le)
    have h2 : 0 ≤ (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ) :=
      div_nonneg (by positivity) (Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < P))).le
    exact add_nonneg h1 h2
  have h_mono_Q :
      C_Q * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) *
        ((H / (v : ℝ)) * (1 + 𝒯.card * Real.exp (-c_Q * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2)) ≤
      C_Q * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) *
        ((H / (v : ℝ)) * (1 + 𝒯.card * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_Q_pos.le hBT_nonneg)
    exact mul_le_mul_of_nonneg_left h_term1 hHv_nonneg
  have hQ_final : (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      C_Q * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) *
        ((H / (v : ℝ)) * (1 + 𝒯.card * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2)) :=
    hQ_bound.trans h_mono_Q
  have hR_sq_nonneg : 0 ≤ C_R ^ 2 * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h_prod_le := mul_le_mul_of_nonneg_right hQ_final hR_sq_nonneg
  calc (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2)
      ≤ (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ^ 2) *
          (C_R ^ 2 * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2) := h_sum_le
    _ ≤ (C_Q * (1 / (H * Real.log (P : ℝ)) + (1 + Real.log (P : ℝ)) ^ 3 / Real.sqrt (P : ℝ)) *
        ((H / (v : ℝ)) * (1 + 𝒯.card * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2))) *
        (C_R ^ 2 * ((Real.log (X : ℝ) + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2) := h_prod_le
    _ = C * ((Real.log X + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
          (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
          ((H / (v : ℝ)) * (1 + 𝒯.card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2)) := by
      set R_val := ((Real.log X + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2
      set BT_val := (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P)
      set V_val := ((H / (v : ℝ)) * (1 + 𝒯.card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2))
      dsimp [C]
      ring

end Erdos1201.MR
