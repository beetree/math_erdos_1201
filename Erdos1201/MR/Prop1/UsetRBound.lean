/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gemini

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Setup
import Erdos1201.MR.Arithmetic
import Erdos1201.MR.Prop1.RPointwise
import Erdos1201.MR.Twisted.TwistedPrimeSumsFinal
import Erdos1201.MR.Sieve.SmoothTailExp

/-!
# Pointwise Bound on the Cofactor Polynomial $R_v$ in the Exceptional Region

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the pointwise bound on the cofactor polynomial $R_{v,H}(1+it)$
at height $|t| \ge \tau$ (paper Section 8.3, first half of the $T_L$ argument).
-/

open Real
open scoped Classical
open Erdos1201
open Erdos1201.MR

namespace Erdos1201.MR

/-- The cofactor range $(X e^{-v/H}, 2X e^{-v/H}]$ coincides with the natural interval
$(\lfloor y \rfloor_+, \lfloor 2y \rfloor_+]$. -/
lemma cofactorRange_eq_Ioc (X : ℕ) (H : ℝ) (v : ℕ) :
    let y := (X : ℝ) * Real.exp (-(v / H))
    cofactorRange X H v = Finset.Ioc ⌊y⌋₊ ⌊2 * y⌋₊ := by
  intro y
  ext m
  unfold cofactorRange
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  have hy : 0 ≤ y := by positivity
  have h2y : 2 * (X : ℝ) * Real.exp (-(v / H)) = 2 * y := by ring
  rw [h2y]
  constructor
  · rintro ⟨⟨hm0, hm2y⟩, hym⟩
    refine ⟨(Nat.floor_lt hy).mpr hym, hm2y⟩
  · rintro ⟨hYm, hm2y⟩
    have hym : y < (m : ℝ) := (Nat.floor_lt hy).mp hYm
    have hm0 : 0 < m := by
      have : 0 ≤ ⌊y⌋₊ := Nat.zero_le _
      omega
    exact ⟨⟨hm0, hm2y⟩, hym⟩

/-- $\lfloor 2y \rfloor_+$ is either $2\lfloor y \rfloor_+$ or $2\lfloor y \rfloor_+ + 1$. -/
lemma floor_two_mul_le (y : ℝ) (hy : 0 ≤ y) :
    ⌊2 * y⌋₊ = 2 * ⌊y⌋₊ ∨ ⌊2 * y⌋₊ = 2 * ⌊y⌋₊ + 1 := by
  have h1 : 2 * ⌊y⌋₊ ≤ ⌊2 * y⌋₊ := by
    rw [Nat.le_floor_iff (by positivity)]
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le hy) (by norm_num)
  have h2 : ⌊2 * y⌋₊ < 2 * ⌊y⌋₊ + 2 := by
    rw [Nat.floor_lt (by positivity)]
    push_cast
    calc 2 * y < 2 * ((⌊y⌋₊ : ℝ) + 1) := mul_lt_mul_of_pos_left (Nat.lt_floor_add_one y) (by norm_num)
      _ = 2 * (⌊y⌋₊ : ℝ) + 2 := by ring
  omega

/-- Adjoining the successor to an `Ioc` interval. -/
lemma Ioc_succ (a b : ℕ) (_h : a ≤ b) :
    Finset.Ioc a (b + 1) = insert (b + 1) (Finset.Ioc a b) := by
  ext x
  simp only [Finset.mem_Ioc, Finset.mem_insert]
  omega

/-- Splitting prime filter on an `Ioc` interval extended by one element. -/
lemma filter_prime_Ioc_succ (A : ℕ) :
    (Finset.Ioc A (2 * A + 1)).filter Nat.Prime =
      if Nat.Prime (2 * A + 1) then
        insert (2 * A + 1) ((Finset.Ioc A (2 * A)).filter Nat.Prime)
      else
        (Finset.Ioc A (2 * A)).filter Nat.Prime := by
  have h_split : Finset.Ioc A (2 * A + 1) = insert (2 * A + 1) (Finset.Ioc A (2 * A)) :=
    Ioc_succ A (2 * A) (by omega)
  rw [h_split, Finset.filter_insert]

/-- Bounding the norm of the prime sum on `(A, 2A+1]` by that on `(A, 2A]` plus the extra term. -/
lemma norm_prime_sum_Ioc_succ_le (A : ℕ) (t : ℝ) (E : ℝ) (hA : 0 < A)
    (hS : ‖∑ p ∈ (Finset.Ioc A (2 * A)).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤ E) :
    ‖∑ p ∈ (Finset.Ioc A (2 * A + 1)).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤
      E + 1 / (2 * (A : ℝ) + 1) := by
  have _ := hA
  let f : ℕ → ℂ := fun p => (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))
  rw [filter_prime_Ioc_succ A]
  split_ifs with _hp
  · have hnotmem : 2 * A + 1 ∉ (Finset.Ioc A (2 * A)).filter Nat.Prime := by
      simp only [Finset.mem_filter, Finset.mem_Ioc, not_and]
      omega
    rw [Finset.sum_insert hnotmem]
    have h_tri := norm_add_le (f (2 * A + 1)) (∑ p ∈ (Finset.Ioc A (2 * A)).filter Nat.Prime, f p)
    have hf : ‖f (2 * A + 1)‖ = 1 / (2 * (A : ℝ) + 1) := by
      dsimp [f]
      have hpos : 0 < 2 * A + 1 := by omega
      have h_norm := norm_natCast_cpow_neg_one_add_mul_I (2 * A + 1) hpos t
      have : ((2 * A + 1 : ℕ) : ℝ) = 2 * (A : ℝ) + 1 := by push_cast; rfl
      rwa [this] at h_norm
    calc ‖f (2 * A + 1) + ∑ p ∈ (Finset.Ioc A (2 * A)).filter Nat.Prime, f p‖
        ≤ ‖f (2 * A + 1)‖ + ‖∑ p ∈ (Finset.Ioc A (2 * A)).filter Nat.Prime, f p‖ := h_tri
      _ ≤ 1 / (2 * (A : ℝ) + 1) + E := by linarith [hf, hS]
      _ = E + 1 / (2 * (A : ℝ) + 1) := add_comm _ _
  · have hpos : 0 ≤ 1 / (2 * (A : ℝ) + 1) := by positivity
    linarith [hS, hpos]

/-- The coefficients $c(m) = f_X(m) / (\omega(m) + 1)$ are bounded in norm by 1. -/
lemma norm_c_le_one (β : ℝ) (X P Q m : ℕ) :
    ‖fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ≤ 1 := by
  rw [norm_div]
  have h_num := norm_fX_le_one β X m
  have h_denom : 1 ≤ ‖(omegaIn (primeRange P Q) m : ℂ) + 1‖ := by
    have : (omegaIn (primeRange P Q) m : ℂ) + 1 = ((omegaIn (primeRange P Q) m + 1 : ℕ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_natCast]
    have : 1 ≤ omegaIn (primeRange P Q) m + 1 := by omega
    exact_mod_cast this
  have hpos : 0 < ‖(omegaIn (primeRange P Q) m : ℂ) + 1‖ := by positivity
  exact (div_le_one₀ hpos).mpr (h_num.trans h_denom)

/-- Divisors from `primeRange P Q` in $p m$ are those in $m$ when $p > Q$. -/
lemma divisorsIn_primeRange_mul (P Q p m : ℕ) (hp : p.Prime) (hpQ : Q < p) :
    divisorsIn (primeRange P Q) (p * m) = divisorsIn (primeRange P Q) m := by
  ext q
  simp only [mem_divisorsIn, primeRange, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨hP, hQ⟩, hq_prime⟩, hdvd⟩
    rcases hq_prime.dvd_mul.mp hdvd with hqp | hqm
    · have : q = p := (Nat.dvd_prime hp).mp hqp |>.resolve_left hq_prime.ne_one
      subst this
      omega
    · exact ⟨⟨⟨hP, hQ⟩, hq_prime⟩, hqm⟩
  · rintro ⟨hq, hdvd⟩
    exact ⟨hq, dvd_mul_of_dvd_right hdvd p⟩

/-- $\omega$ count in `primeRange P Q` is unchanged under multiplying by $p > Q$. -/
lemma omegaIn_primeRange_mul (P Q p m : ℕ) (hp : p.Prime) (hpQ : Q < p) :
    omegaIn (primeRange P Q) (p * m) = omegaIn (primeRange P Q) m := by
  unfold omegaIn
  rw [divisorsIn_primeRange_mul P Q p m hp hpQ]

/-- When $p > X^\beta$, $p m$ is not $X^\beta$-smooth so $f_X(pm) = 0$. -/
lemma fX_mul_of_prime_gt (β : ℝ) (X p m : ℕ) (hp : p.Prime) (_hm : 0 < m) (hpX : (X : ℝ) ^ β < (p : ℝ)) :
    fX β X (p * m) = 0 := by
  unfold fX smoothIndicator
  have h_not_smooth : ¬ Smooth ((X : ℝ) ^ β) (p * m) := by
    intro hsm
    have hp_dvd : p ∣ p * m := dvd_mul_right p m
    have hp_le := hsm.2 p hp hp_dvd
    linarith
  simp [h_not_smooth]

/-- Factorization of coefficients for prime $p > Z > Q$. -/
lemma c_fac (β : ℝ) (X P Q : ℕ) (Z : ℝ) (hQZ : (Q : ℝ) < Z)
    (p m : ℕ) (hp : p.Prime) (hpZ : Z < (p : ℝ)) (hm : 0 < m) :
    let c : ℕ → ℂ := fun k => fX β X k / ((omegaIn (primeRange P Q) k : ℂ) + 1)
    c (p * m) = if (p : ℝ) ≤ (X : ℝ) ^ β then c m else 0 := by
  intro c
  dsimp [c]
  have hpQ : Q < p := by
    have : (Q : ℝ) < (p : ℝ) := hQZ.trans hpZ
    exact_mod_cast this
  have h_omega : omegaIn (primeRange P Q) (p * m) = omegaIn (primeRange P Q) m :=
    omegaIn_primeRange_mul P Q p m hp hpQ
  rw [h_omega]
  split_ifs with hpX
  · rw [fX_mul_of_prime_le β X p m hp hm hpX]
  · have hpX_gt : (X : ℝ) ^ β < (p : ℝ) := lt_of_not_ge hpX
    rw [fX_mul_of_prime_gt β X p m hp hm hpX_gt]
    simp

/-- Lower bound $\log X \ge 32$ derived from the region hypothesis. -/
lemma thirty_two_le_log_of_hyp (X : ℕ) (Z : ℝ) (hX : 16 ≤ X) (_hZ4 : 4 ≤ Z) (hZX : Z ≤ Real.sqrt X)
    (hlog : Real.log X ≤ (Real.log (Z - 1)) ^ (5 / 4 : ℝ)) : 32 ≤ Real.log X := by
  have hX_pos : 0 < (X : ℝ) := by positivity
  have hX16 : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX_pos : 0 < Real.log X := by
    have : Real.log 16 ≤ Real.log X := Real.log_le_log (by norm_num) hX16
    have : 0 < Real.log 16 := Real.log_pos (by norm_num)
    linarith
  have hZ1_pos : 0 < Z - 1 := by linarith
  have hZ1_gt1 : 1 < Z - 1 := by linarith
  have hlogZ1_pos : 0 < Real.log (Z - 1) := Real.log_pos hZ1_gt1
  have hZ1_lt_sqrt : Z - 1 < Real.sqrt X := by linarith
  have hlogZ1_le : Real.log (Z - 1) ≤ (1 / 2 : ℝ) * Real.log X := by
    have h1 : Real.log (Z - 1) ≤ Real.log (Real.sqrt X) :=
      Real.log_le_log hZ1_pos (le_of_lt hZ1_lt_sqrt)
    have h2 : Real.log (Real.sqrt X) = (1 / 2 : ℝ) * Real.log X := by
      rw [Real.log_sqrt hX_pos.le]
      ring
    rwa [h2] at h1
  have h_rpow : (Real.log (Z - 1)) ^ (5 / 4 : ℝ) ≤ ((1 / 2 : ℝ) * Real.log X) ^ (5 / 4 : ℝ) :=
    Real.rpow_le_rpow hlogZ1_pos.le hlogZ1_le (by norm_num)
  have h_split : ((1 / 2 : ℝ) * Real.log X) ^ (5 / 4 : ℝ) =
      (1 / 2 : ℝ) ^ (5 / 4 : ℝ) * (Real.log X) ^ (5 / 4 : ℝ) := by
    apply Real.mul_rpow (by norm_num) hlogX_pos.le
  rw [h_split] at h_rpow
  have h_trans : Real.log X ≤ (1 / 2 : ℝ) ^ (5 / 4 : ℝ) * (Real.log X) ^ (5 / 4 : ℝ) :=
    hlog.trans h_rpow
  have h_54 : (5 / 4 : ℝ) = 1 + (1 / 4 : ℝ) := by norm_num
  have h_rpow_split : (Real.log X) ^ (5 / 4 : ℝ) = Real.log X * (Real.log X) ^ (1 / 4 : ℝ) := by
    nth_rewrite 1 [h_54]
    rw [Real.rpow_add hlogX_pos, Real.rpow_one]
  rw [h_rpow_split] at h_trans
  have h_cancel : 1 ≤ (1 / 2 : ℝ) ^ (5 / 4 : ℝ) * (Real.log X) ^ (1 / 4 : ℝ) := by
    have h_mul : Real.log X * 1 ≤ Real.log X * ((1 / 2 : ℝ) ^ (5 / 4 : ℝ) * (Real.log X) ^ (1 / 4 : ℝ)) := by
      calc Real.log X * 1 = Real.log X := mul_one _
        _ ≤ (1 / 2 : ℝ) ^ (5 / 4 : ℝ) * (Real.log X * (Real.log X) ^ (1 / 4 : ℝ)) := h_trans
        _ = Real.log X * ((1 / 2 : ℝ) ^ (5 / 4 : ℝ) * (Real.log X) ^ (1 / 4 : ℝ)) := by ring
    exact (mul_le_mul_iff_of_pos_left hlogX_pos).mp h_mul
  have h_two_pow : (2 : ℝ) ^ (5 / 4 : ℝ) ≤ (Real.log X) ^ (1 / 4 : ℝ) := by
    have h_half : (1 / 2 : ℝ) ^ (5 / 4 : ℝ) = ((2 : ℝ) ^ (5 / 4 : ℝ))⁻¹ := by
      rw [one_div, Real.inv_rpow (by norm_num)]
    rw [h_half] at h_cancel
    have h2pos : (0 : ℝ) < (2 : ℝ) ^ (5 / 4 : ℝ) := by positivity
    rw [← div_eq_inv_mul, one_le_div₀ h2pos] at h_cancel
    exact h_cancel
  have h_pow4 : ((2 : ℝ) ^ (5 / 4 : ℝ)) ^ (4 : ℝ) ≤ ((Real.log X) ^ (1 / 4 : ℝ)) ^ (4 : ℝ) :=
    Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) h_two_pow (by norm_num)
  rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul hlogX_pos.le] at h_pow4
  have h_num1 : (5 / 4 : ℝ) * 4 = 5 := by norm_num
  have h_num2 : (1 / 4 : ℝ) * 4 = 1 := by norm_num
  rw [h_num1, h_num2, Real.rpow_one] at h_pow4
  have h_2_5 : (2 : ℝ) ^ (5 : ℝ) = 32 := by norm_num
  rwa [h_2_5] at h_pow4

/-- Lower bound $\log (Z - 1) \ge 16$. -/
lemma sixteen_le_logZ1 (X : ℕ) (Z : ℝ) (hZ : 4 ≤ Z) (hlogX : 32 ≤ Real.log X)
    (hlog : Real.log X ≤ (Real.log (Z - 1)) ^ (5 / 4 : ℝ)) :
    16 ≤ Real.log (Z - 1) := by
  have _ := hZ
  have h32_le : (32 : ℝ) ≤ (Real.log (Z - 1)) ^ (5 / 4 : ℝ) := hlogX.trans hlog
  have hZ1_gt1 : 1 < Z - 1 := by linarith
  have hu_pos : 0 < Real.log (Z - 1) := Real.log_pos hZ1_gt1
  have h_pow : (32 : ℝ) ^ (4 / 5 : ℝ) ≤ ((Real.log (Z - 1)) ^ (5 / 4 : ℝ)) ^ (4 / 5 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) h32_le (by norm_num)
  have h32_eq : (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) := by norm_num
  rw [h32_eq, ← Real.rpow_mul (by norm_num)] at h_pow
  have h_num1 : (5 : ℝ) * (4 / 5 : ℝ) = 4 := by norm_num
  rw [h_num1] at h_pow
  rw [← Real.rpow_mul hu_pos.le] at h_pow
  have h_num2 : (5 / 4 : ℝ) * (4 / 5 : ℝ) = 1 := by norm_num
  rw [h_num2, Real.rpow_one] at h_pow
  have h24 : (2 : ℝ) ^ (4 : ℝ) = 16 := by norm_num
  rwa [h24] at h_pow

/-- Lower bound on $\exp(-v/H)$ in terms of $(e Q)^{-1}$. -/
lemma inv_exp_mul_le_exp_neg_v_div_H (H : ℝ) (Q v : ℕ) (hH : 1 ≤ H) (hQ : 2 ≤ Q)
    (hv : v ≤ ⌈H * Real.log Q⌉₊) :
    (Real.exp 1 * (Q : ℝ))⁻¹ ≤ Real.exp (-(v / H)) := by
  have _ := hQ
  have hH_pos : 0 < H := by linarith
  have h_ceil : (v : ℝ) ≤ H * Real.log Q + 1 := by
    have : (v : ℝ) ≤ (⌈H * Real.log Q⌉₊ : ℝ) := by exact_mod_cast hv
    have h_ceil_le : (⌈H * Real.log Q⌉₊ : ℝ) < H * Real.log Q + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have h_div : (v : ℝ) / H ≤ Real.log Q + 1 := by
    have : (v : ℝ) / H ≤ (H * Real.log Q + 1) / H := div_le_div_of_nonneg_right h_ceil hH_pos.le
    have h_eq : (H * Real.log Q + 1) / H = Real.log Q + 1 / H := by
      rw [add_div, mul_div_cancel_left₀ _ hH_pos.ne']
    have h_inv : 1 / H ≤ 1 := by
      rw [div_le_iff₀ hH_pos]
      linarith
    linarith
  have h_neg : -(Real.log Q + 1) ≤ -((v : ℝ) / H) := by linarith
  have h_exp : Real.exp (-(Real.log Q + 1)) ≤ Real.exp (-((v : ℝ) / H)) :=
    Real.exp_le_exp.mpr h_neg
  have h_exp_eq : Real.exp (-(Real.log Q + 1)) = (Real.exp 1 * (Q : ℝ))⁻¹ := by
    have hQ_pos : 0 < (Q : ℝ) := by positivity
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hQ_pos]
    rw [mul_comm, mul_inv]
  rwa [h_exp_eq] at h_exp

/-- Lower bound $y \ge \sqrt{X} / e$. -/
lemma sqrtX_div_e_le_y (X P Q : ℕ) (H : ℝ) (v : ℕ) (Z : ℝ)
    (hX : 16 ≤ X) (hP : 2 ≤ P) (hPQ : P ≤ Q) (hH : 1 ≤ H)
    (hv : v ≤ ⌈H * Real.log Q⌉₊) (hQZ : (Q : ℝ) < Z) (hZX : Z ≤ Real.sqrt X) :
    let y := (X : ℝ) * Real.exp (-(v / H))
    (Real.sqrt X) / (Real.exp 1) ≤ y := by
  intro y
  have _ := hX
  have hQ : 2 ≤ Q := hP.trans hPQ
  have h_exp := inv_exp_mul_le_exp_neg_v_div_H H Q v hH hQ hv
  have hX_pos : 0 < (X : ℝ) := by positivity
  have hsqrtX_pos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX_pos
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have _hQ_pos : 0 < (Q : ℝ) := by positivity
  have h_mul : (X : ℝ) * (Real.exp 1 * (Q : ℝ))⁻¹ ≤ (X : ℝ) * Real.exp (-(v / H)) :=
    mul_le_mul_of_nonneg_left h_exp hX_pos.le
  have hy_eq : (X : ℝ) * Real.exp (-(v / H)) = y := rfl
  rw [hy_eq] at h_mul
  have h_div : (X : ℝ) / (Real.exp 1 * (Q : ℝ)) ≤ y := by
    rw [div_eq_mul_inv]
    exact h_mul
  refine le_trans ?_ h_div
  have hQ_le_sqrt : (Q : ℝ) ≤ Real.sqrt X := hQZ.le.trans hZX
  have h_denom_le : Real.exp 1 * (Q : ℝ) ≤ Real.exp 1 * Real.sqrt X :=
    mul_le_mul_of_nonneg_left hQ_le_sqrt he_pos.le
  have h_denom_pos : 0 < Real.exp 1 * (Q : ℝ) := by positivity
  have h_div_le : (X : ℝ) / (Real.exp 1 * Real.sqrt X) ≤ (X : ℝ) / (Real.exp 1 * (Q : ℝ)) :=
    div_le_div_of_nonneg_left hX_pos.le h_denom_pos h_denom_le
  have h_cancel : (X : ℝ) / (Real.exp 1 * Real.sqrt X) = (Real.sqrt X) / (Real.exp 1) := by
    have hX_sqrt : (X : ℝ) = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX_pos.le).symm
    nth_rewrite 1 [hX_sqrt]
    have : Real.sqrt X * Real.sqrt X / (Real.exp 1 * Real.sqrt X) =
        (Real.sqrt X / Real.exp 1) * (Real.sqrt X / Real.sqrt X) := by ring
    rw [this, div_self hsqrtX_pos.ne', mul_one]
  rwa [h_cancel] at h_div_le

/-- Lower bound $Y \ge \sqrt{X} / (2e)$. -/
lemma sqrtX_div_2e_le_Y (X Y : ℕ) (y : ℝ) (hX : 16 ≤ X) (hyX : (Real.sqrt X) / (Real.exp 1) ≤ y)
    (hY : Y = ⌊y⌋₊) (hlogX : 32 ≤ Real.log X) :
    (Real.sqrt X) / (2 * Real.exp 1) ≤ (Y : ℝ) := by
  have _ := hX
  have he_lt3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hX_pos : 0 < (X : ℝ) := by positivity
  have hsqrtX_eq : Real.sqrt X = Real.exp ((1 / 2 : ℝ) * Real.log X) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX_pos]
    congr 1
    ring
  have h16_le : 16 ≤ (1 / 2 : ℝ) * Real.log X := by linarith
  have h_exp16 : Real.exp 16 ≤ Real.sqrt X := by
    rw [hsqrtX_eq]
    exact Real.exp_le_exp.mpr h16_le
  have h_17_le : 17 ≤ Real.exp 16 := by
    have h1 := Real.add_one_le_exp (16 : ℝ)
    linarith
  have _hsqrtX_ge17 : 17 ≤ Real.sqrt X := by linarith
  have h_half_ge1 : 1 ≤ (Real.sqrt X) / (2 * Real.exp 1) := by
    have : 2 * Real.exp 1 < 6 := by linarith
    have : (6 : ℝ) < 17 := by norm_num
    have : 2 * Real.exp 1 ≤ Real.sqrt X := by linarith
    rw [one_le_div₀ (by positivity)]
    exact this
  have _hy_ge : (Real.sqrt X) / (2 * Real.exp 1) + 1 ≤ y := by
    have : (Real.sqrt X) / (2 * Real.exp 1) + (Real.sqrt X) / (2 * Real.exp 1) = (Real.sqrt X) / (Real.exp 1) := by ring
    linarith
  rw [hY]
  have h_floor_ge : y - 1 ≤ (⌊y⌋₊ : ℝ) := by
    have := Nat.sub_one_lt_floor y
    linarith
  linarith

/-- $Y \ge 2$ follows from $\sqrt{X} / (2e) \le Y$. -/
lemma two_le_Y (X Y : ℕ) (hY : (Real.sqrt X) / (2 * Real.exp 1) ≤ (Y : ℝ))
    (hsqrtX : 17 ≤ Real.sqrt X) : 2 ≤ Y := by
  have _he_lt3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h_bound : (2 : ℝ) ≤ (Real.sqrt X) / (2 * Real.exp 1) := by
    have : 2 * (2 * Real.exp 1) < 12 := by linarith
    have : (12 : ℝ) ≤ 17 := by norm_num
    have : 2 * (2 * Real.exp 1) ≤ Real.sqrt X := by linarith
    rw [le_div_iff₀ (by positivity)]
    exact this
  have h_le : (2 : ℝ) ≤ (Y : ℝ) := h_bound.trans hY
  exact_mod_cast h_le

/-- $Y \le X$. -/
lemma Y_le_X (X : ℕ) (H : ℝ) (v : ℕ) (hH : 0 < H) (hv : 0 ≤ (v : ℝ)) :
    (⌊(X : ℝ) * Real.exp (-(v / H))⌋₊ : ℝ) ≤ (X : ℝ) := by
  have hy_nonneg : 0 ≤ (X : ℝ) * Real.exp (-(v / H)) := by positivity
  have h_floor : (⌊(X : ℝ) * Real.exp (-(v / H))⌋₊ : ℝ) ≤ (X : ℝ) * Real.exp (-(v / H)) :=
    Nat.floor_le hy_nonneg
  have h_exp_le1 : Real.exp (-(v / H)) ≤ 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (v : ℝ) / H := div_nonneg hv hH.le
    linarith
  have h_mul_le : (X : ℝ) * Real.exp (-(v / H)) ≤ (X : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left h_exp_le1 (by positivity)
  rw [mul_one] at h_mul_le
  exact h_floor.trans h_mul_le

/-- $\log(2Y) + 1 \le \log X + 2$. -/
lemma log_two_mul_Y_add_one_le (X Y : ℕ) (hY_pos : 0 < Y) (hY_le : (Y : ℝ) ≤ (X : ℝ)) :
    Real.log (2 * (Y : ℝ)) + 1 ≤ Real.log X + 2 := by
  have h2Y_pos : 0 < 2 * (Y : ℝ) := by positivity
  have hX_pos : 0 < (X : ℝ) := by
    have : 0 < (Y : ℝ) := by exact_mod_cast hY_pos
    linarith
  have h2Y_le_2X : 2 * (Y : ℝ) ≤ 2 * (X : ℝ) := by linarith
  have h_log : Real.log (2 * (Y : ℝ)) ≤ Real.log (2 * (X : ℝ)) :=
    Real.log_le_log h2Y_pos h2Y_le_2X
  have h_log2X : Real.log (2 * (X : ℝ)) = Real.log 2 + Real.log X :=
    Real.log_mul (by norm_num) hX_pos.ne'
  have h_log2_lt1 : Real.log 2 < 1 := by
    rw [← Real.log_exp 1]
    apply Real.log_lt_log (by norm_num)
    have := Real.exp_one_gt_d9
    linarith
  linarith

/-- $1/Y \le 6/Z$. -/
lemma inv_Y_le (Y : ℕ) (Z : ℝ) (hZ : 4 ≤ Z) (hYZ : Z / (2 * Real.exp 1) ≤ (Y : ℝ)) :
    (1 : ℝ) / (Y : ℝ) ≤ 6 / Z := by
  have he_lt3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have hZ_pos : 0 < Z := by linarith
  have h1 : (1 : ℝ) / (Y : ℝ) ≤ 1 / (Z / (2 * Real.exp 1)) :=
    one_div_le_one_div_of_le (by positivity) hYZ
  rw [one_div_div] at h1
  have h3 : (2 * Real.exp 1) / Z ≤ 6 / Z := by
    have : 2 * Real.exp 1 ≤ 6 := by linarith
    exact div_le_div_of_nonneg_right this hZ_pos.le
  exact h1.trans h3

/-- $1/(Z-1) \le \exp(-c (\log(Z-1))^{1/16})$. -/
lemma inv_Z1_le_exp (Z : ℝ) (c : ℝ) (_hZ : 4 ≤ Z) (hlogZ1 : 16 ≤ Real.log (Z - 1))
    (_hc0 : 0 < c) (hc1 : c ≤ 1) :
    1 / (Z - 1) ≤ Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by
  have hZ1_pos : 0 < Z - 1 := by linarith
  have hu_pos : 0 < Real.log (Z - 1) := by linarith
  have h16_le : (16 : ℝ) ≤ Real.log (Z - 1) := hlogZ1
  have hu_15_16 : 1 ≤ (Real.log (Z - 1)) ^ (15 / 16 : ℝ) := by
    have h1 : (16 : ℝ) ^ (15 / 16 : ℝ) ≤ (Real.log (Z - 1)) ^ (15 / 16 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h16_le (by norm_num)
    have h2 : (16 : ℝ) ^ (15 / 16 : ℝ) = ((2 : ℝ) ^ (4 : ℝ)) ^ (15 / 16 : ℝ) := by norm_num
    rw [h2, ← Real.rpow_mul (by norm_num)] at h1
    have h3 : (4 : ℝ) * (15 / 16 : ℝ) = (15 / 4 : ℝ) := by norm_num
    rw [h3] at h1
    have h4 : (1 : ℝ) ≤ (2 : ℝ) ^ (15 / 4 : ℝ) := by
      have : (2 : ℝ) ^ (0 : ℝ) ≤ (2 : ℝ) ^ (15 / 4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      rwa [Real.rpow_zero] at this
    linarith
  have hc_le_pow : c ≤ (Real.log (Z - 1)) ^ (15 / 16 : ℝ) := hc1.trans hu_15_16
  have h_mul : c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ) ≤ Real.log (Z - 1) := by
    calc c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)
        ≤ (Real.log (Z - 1)) ^ (15 / 16 : ℝ) * (Real.log (Z - 1)) ^ (1 / 16 : ℝ) :=
          mul_le_mul_of_nonneg_right hc_le_pow (by positivity)
      _ = (Real.log (Z - 1)) ^ (15 / 16 + 1 / 16 : ℝ) := by
        rw [← Real.rpow_add hu_pos]
      _ = Real.log (Z - 1) := by
        have : (15 / 16 : ℝ) + 1 / 16 = 1 := by norm_num
        rw [this, Real.rpow_one]
  have h_exp : Real.exp (-(Real.log (Z - 1))) ≤ Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h_inv : Real.exp (-(Real.log (Z - 1))) = 1 / (Z - 1) := by
    rw [Real.exp_neg, Real.exp_log hZ1_pos, one_div]
  rwa [h_inv] at h_exp

/-- Bound on prime sums over intervals $(a, b]$ with $Z \le a < b \le 2a$. -/
lemma hstar_bound (c_prime C_prime : ℝ) (_hc_prime : 0 < c_prime) (hC_prime : 0 < C_prime)
    (h_prime_sum : ∀ (A B : ℕ) (u : ℝ), 3 ≤ A → A < B → B ≤ 2 * A → 1 ≤ |u| →
      Real.log |u| ≤ (Real.log A) ^ (5 / 4 : ℝ) →
      ‖∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + u * Complex.I))‖ ≤
        3 / (|u| * Real.log A) + C_prime * Real.exp (-c_prime * (Real.log A) ^ (1 / 16 : ℝ)))
    (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hcc_prime : c ≤ c_prime)
    (X : ℕ) (t τ Z : ℝ) (_hX : 16 ≤ X) (hZ : 4 ≤ Z) (hlogZ1 : 16 ≤ Real.log (Z - 1))
    (hlogX_le : Real.log X ≤ (Real.log (Z - 1)) ^ (5 / 4 : ℝ))
    (hτ : 1 ≤ τ) (ht_ge : τ ≤ |t|) (ht_le : |t| ≤ X)
    (a b : ℝ) (hZa : Z ≤ a) (hab : a < b) (hb2a : b ≤ 2 * a) :
    let E := (C_prime + 4) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)))
    ‖∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤ E := by
  intro E
  have _ := hc0
  have hZ1_gt1 : 1 < Z - 1 := by linarith
  have hlogZ1_pos : 0 < Real.log (Z - 1) := Real.log_pos hZ1_gt1
  have ht_ge1 : 1 ≤ |t| := hτ.trans ht_ge
  have ht_pos : 0 < |t| := by linarith
  have _hτ_pos : 0 < τ := by linarith
  have hX_pos : 0 < (X : ℝ) := by
    have : 0 < |t| := ht_pos
    linarith
  have hlogt_le : Real.log |t| ≤ Real.log X := Real.log_le_log ht_pos ht_le
  let A := ⌊a⌋₊
  let B := ⌊b⌋₊
  change ‖∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤ E
  have hb_pos : 0 ≤ b := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hA3 : 3 ≤ A := by
    have h4a : (4 : ℝ) ≤ a := hZ.trans hZa
    have : 4 ≤ ⌊a⌋₊ := (Nat.le_floor_iff ha0).mpr h4a
    omega
  have hA_pos : 0 < A := by omega
  have _hA_real_pos : 0 < (A : ℝ) := by positivity
  have hZA : Z - 1 ≤ (A : ℝ) := by
    have : a - 1 < (⌊a⌋₊ : ℝ) := Nat.sub_one_lt_floor a
    linarith
  have hlogZA : Real.log (Z - 1) ≤ Real.log A := Real.log_le_log (by linarith) hZA
  have _hlogA_pos : 0 < Real.log A := hlogZ1_pos.trans_le hlogZA
  have hlogt_le_A : Real.log |t| ≤ (Real.log A) ^ (5 / 4 : ℝ) := by
    have h1 : (Real.log (Z - 1)) ^ (5 / 4 : ℝ) ≤ (Real.log A) ^ (5 / 4 : ℝ) :=
      Real.rpow_le_rpow hlogZ1_pos.le hlogZA (by norm_num)
    linarith
  have hAB : A ≤ B := Nat.floor_le_floor hab.le
  have hB_le_2A1 : B ≤ 2 * A + 1 := by
    have h1 : (B : ℝ) ≤ b := Nat.floor_le hb_pos
    have h2 : b ≤ 2 * a := hb2a
    have h3 : 2 * a < 2 * ((A : ℝ) + 1) := by
      have := Nat.lt_floor_add_one a
      linarith
    have h4 : (B : ℝ) < 2 * (A : ℝ) + 2 := by linarith
    have : (2 * (A : ℝ) + 2) = ((2 * A + 2 : ℕ) : ℝ) := by push_cast; rfl
    rw [this] at h4
    have : B < 2 * A + 2 := by exact_mod_cast h4
    omega
  have h_case_le : ∀ B', A < B' → B' ≤ 2 * A →
      ‖∑ p ∈ (Finset.Ioc A B').filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤
        3 / (τ * Real.log (Z - 1)) + C_prime * Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by
    intro B' hAB' hB'2A
    have h_main := h_prime_sum A B' t hA3 hAB' hB'2A ht_ge1 hlogt_le_A
    refine h_main.trans ?_
    have h_term1 : 3 / (|t| * Real.log A) ≤ 3 / (τ * Real.log (Z - 1)) := by
      have h_denom : τ * Real.log (Z - 1) ≤ |t| * Real.log A := by
        exact mul_le_mul ht_ge hlogZA hlogZ1_pos.le (by linarith)
      have h_dpos : 0 < τ * Real.log (Z - 1) := by positivity
      exact div_le_div_of_nonneg_left (by norm_num) h_dpos h_denom
    have h_term2 : C_prime * Real.exp (-c_prime * (Real.log A) ^ (1 / 16 : ℝ)) ≤
        C_prime * Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by
      have h_exp : Real.exp (-c_prime * (Real.log A) ^ (1 / 16 : ℝ)) ≤
          Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by
        apply Real.exp_le_exp.mpr
        have h1 : (Real.log (Z - 1)) ^ (1 / 16 : ℝ) ≤ (Real.log A) ^ (1 / 16 : ℝ) :=
          Real.rpow_le_rpow hlogZ1_pos.le hlogZA (by norm_num)
        have h2 : c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ) ≤ c_prime * (Real.log A) ^ (1 / 16 : ℝ) :=
          mul_le_mul hcc_prime h1 (by positivity) (by linarith)
        linarith
      exact mul_le_mul_of_nonneg_left h_exp hC_prime.le
    linarith
  rcases lt_or_eq_of_le hAB with hAB_lt | hAB_eq
  · by_cases hB2A : B ≤ 2 * A
    · have h_le := h_case_le B hAB_lt hB2A
      refine h_le.trans ?_
      dsimp [E]
      have h3_eq : 3 / (τ * Real.log (Z - 1)) = 3 * (1 / (τ * Real.log (Z - 1))) := by ring
      have _h1 : 0 ≤ 1 / (τ * Real.log (Z - 1)) := by positivity
      have _h2 : 0 ≤ Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by positivity
      have _h3 : 0 ≤ C_prime * (1 / (τ * Real.log (Z - 1))) := by positivity
      have _h4 : 0 ≤ 4 * Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by positivity
      have h_expand : (C_prime + 4) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) =
          C_prime * (1 / (τ * Real.log (Z - 1))) + 4 * (1 / (τ * Real.log (Z - 1))) +
          C_prime * Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) +
          4 * Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by ring
      rw [h_expand, h3_eq]
      linarith
    · have hB_eq : B = 2 * A + 1 := by omega
      rw [hB_eq]
      have hA_lt_2A : A < 2 * A := by omega
      have h_2A_le_2A : 2 * A ≤ 2 * A := le_rfl
      have h_sum_2A := h_case_le (2 * A) hA_lt_2A h_2A_le_2A
      have h_succ := norm_prime_sum_Ioc_succ_le A t _ hA_pos h_sum_2A
      refine h_succ.trans ?_
      have h_extra : 1 / (2 * (A : ℝ) + 1) ≤ Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by
        have h_2A1 : (Z - 1) ≤ 2 * (A : ℝ) + 1 := by linarith
        have h_inv1 : 1 / (2 * (A : ℝ) + 1) ≤ 1 / (Z - 1) :=
          one_div_le_one_div_of_le (by linarith) h_2A1
        have h_inv2 := inv_Z1_le_exp Z c hZ hlogZ1 hc0 hc1
        exact h_inv1.trans h_inv2
      dsimp [E]
      have h3_eq : 3 / (τ * Real.log (Z - 1)) = 3 * (1 / (τ * Real.log (Z - 1))) := by ring
      have _h1 : 0 ≤ 1 / (τ * Real.log (Z - 1)) := by positivity
      have _h2 : 0 ≤ Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by positivity
      have _h3 : 0 ≤ C_prime * (1 / (τ * Real.log (Z - 1))) := by positivity
      have _h4 : 0 ≤ 3 * Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by positivity
      have h_expand : (C_prime + 4) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) =
          C_prime * (1 / (τ * Real.log (Z - 1))) + 4 * (1 / (τ * Real.log (Z - 1))) +
          C_prime * Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) +
          1 * Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) +
          3 * Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by ring
      rw [h_expand, h3_eq]
      linarith
  · rw [hAB_eq, Finset.Ioc_self]
    simp only [Finset.filter_empty, Finset.sum_empty, norm_zero]
    dsimp [E]
    have _h1 : 0 ≤ 1 / (τ * Real.log (Z - 1)) := by positivity
    have _h2 : 0 ≤ Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by positivity
    have _h3 : 0 ≤ C_prime + 4 := by linarith
    positivity

/-- Equivalence of the smooth number filter on $(Y, 2Y]$. -/
lemma filter_smooth_eq (Y : ℕ) (Z : ℝ) (hZ : 0 ≤ Z) (_hY : 1 ≤ Y) :
    (Finset.Ioc Y (2 * Y)).filter (fun n => ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Z) =
      (Finset.Ioc 0 (2 * Y)).filter (fun n => n ∈ Nat.smoothNumbers (⌊Z⌋₊ + 1) ∧ (Y : ℝ) < (n : ℝ)) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hYn, hn2Y⟩, hsm⟩
    have hn0 : n ≠ 0 := by omega
    have h1 : 0 < n ∧ n ≤ 2 * Y := ⟨by omega, hn2Y⟩
    have h2 : n ∈ Nat.smoothNumbers (⌊Z⌋₊ + 1) := by
      rw [Nat.mem_smoothNumbers, and_iff_right hn0]
      intro p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
      have hp_dvd : p ∣ n := Nat.dvd_of_mem_primeFactorsList hp
      have hp_le := hsm p hp_prime hp_dvd
      have : p ≤ ⌊Z⌋₊ := Nat.le_floor hp_le
      omega
    have h3 : (Y : ℝ) < (n : ℝ) := by exact_mod_cast hYn
    exact ⟨h1, h2, h3⟩
  · rintro ⟨⟨hn0, hn2Y⟩, hsm, hYn⟩
    have hn_pos : 0 < n := hn0
    have hYn_nat : Y < n := by exact_mod_cast hYn
    have h1 : Y < n ∧ n ≤ 2 * Y := ⟨hYn_nat, hn2Y⟩
    have h2 : ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Z := by
      rw [Nat.mem_smoothNumbers] at hsm
      intro p hp hp_dvd
      have hp_mem : p ∈ n.primeFactorsList := by
        rw [Nat.mem_primeFactorsList hn_pos.ne']
        exact ⟨hp, hp_dvd⟩
      have hp_lt := hsm.2 p hp_mem
      have : p ≤ ⌊Z⌋₊ := by omega
      exact (Nat.le_floor_iff hZ).mp this
    exact ⟨h1, h2⟩

/-- Tail exponent inequality $\exp(-\log Y / (2 \log Z)) \le e \exp(-\log X / (4 \log Z))$. -/
lemma exp_tail_le (X Y : ℕ) (Z : ℝ) (hZ : 4 ≤ Z) (hX : 16 ≤ X) (_hlogX : 32 ≤ Real.log X)
    (hY : (Real.sqrt X) / (2 * Real.exp 1) ≤ (Y : ℝ)) :
    Real.exp (-(Real.log Y) / (2 * Real.log Z)) ≤ Real.exp 1 * Real.exp (-(Real.log X) / (4 * Real.log Z)) := by
  have _ := hX
  have hX_pos : 0 < (X : ℝ) := by positivity
  have hsqrtX_pos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX_pos
  have he_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have h2e_pos : 0 < 2 * Real.exp 1 := by positivity
  have hdiv_pos : 0 < (Real.sqrt X) / (2 * Real.exp 1) := by positivity
  have hZ_gt1 : 1 < Z := by linarith
  have _hlogZ_pos : 0 < Real.log Z := Real.log_pos hZ_gt1
  have hlogY_ge : (1 / 2 : ℝ) * Real.log X - (Real.log 2 + 1) ≤ Real.log Y := by
    have h1 : Real.log ((Real.sqrt X) / (2 * Real.exp 1)) ≤ Real.log Y :=
      Real.log_le_log hdiv_pos hY
    have h2 : Real.log ((Real.sqrt X) / (2 * Real.exp 1)) =
        Real.log (Real.sqrt X) - Real.log (2 * Real.exp 1) :=
      Real.log_div hsqrtX_pos.ne' h2e_pos.ne'
    have h3 : Real.log (Real.sqrt X) = (1 / 2 : ℝ) * Real.log X := by
      rw [Real.log_sqrt hX_pos.le]
      ring
    have h4 : Real.log (2 * Real.exp 1) = Real.log 2 + 1 := by
      rw [Real.log_mul (by norm_num) he_pos.ne', Real.log_exp]
    linarith
  have h_sub_le : (Real.log 2 + 1) / (2 * Real.log Z) ≤ 1 := by
    have _h_log4 : 1 < Real.log 4 := by
      rw [← Real.log_exp 1]
      apply Real.log_lt_log (Real.exp_pos 1)
      have := Real.exp_one_lt_d9
      linarith
    have h_log2 : Real.log 2 + 1 ≤ 2 * Real.log Z := by
      have h4Z : Real.log 4 ≤ Real.log Z := Real.log_le_log (by norm_num) hZ
      have _h4_eq : Real.log 4 = 2 * Real.log 2 := by
        have : (4 : ℝ) = 2 * 2 := by norm_num
        rw [this, Real.log_mul (by norm_num) (by norm_num)]
        ring
      linarith
    rw [div_le_one₀ (by positivity)]
    exact h_log2
  have h_exp_bound : -(Real.log Y) / (2 * Real.log Z) ≤
      -(Real.log X) / (4 * Real.log Z) + 1 := by
    have h_div_ge : ((1 / 2 : ℝ) * Real.log X - (Real.log 2 + 1)) / (2 * Real.log Z) ≤
        (Real.log Y) / (2 * Real.log Z) :=
      div_le_div_of_nonneg_right hlogY_ge (by positivity)
    have h_split : ((1 / 2 : ℝ) * Real.log X - (Real.log 2 + 1)) / (2 * Real.log Z) =
        (Real.log X) / (4 * Real.log Z) - (Real.log 2 + 1) / (2 * Real.log Z) := by
      ring
    rw [h_split] at h_div_ge
    rw [neg_div, neg_div]
    linarith
  calc Real.exp (-(Real.log Y) / (2 * Real.log Z))
      ≤ Real.exp (-(Real.log X) / (4 * Real.log Z) + 1) := Real.exp_le_exp.mpr h_exp_bound
    _ = Real.exp (-(Real.log X) / (4 * Real.log Z)) * Real.exp 1 := Real.exp_add _ _
    _ = Real.exp 1 * Real.exp (-(Real.log X) / (4 * Real.log Z)) := mul_comm _ _

/-- Smooth reciprocal sum bound on $(Y, 2Y]$. -/
lemma smooth_tail_bound (C_smooth : ℝ) (hC_smooth : 0 < C_smooth)
    (h_smooth_sum : ∀ (Q N : ℕ) (Z : ℝ), 2 ≤ Q → 1 ≤ Z →
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ Nat.smoothNumbers (Q + 1) ∧ Z < n), (1 : ℝ) / n) ≤
        C_smooth * Real.exp (-(Real.log Z) / (2 * Real.log Q)) * (Real.log Q) ^ (6 : ℝ))
    (X Y : ℕ) (Z : ℝ) (hX : 16 ≤ X) (hZ : 4 ≤ Z) (hlogX : 32 ≤ Real.log X)
    (hY2 : 2 ≤ Y) (hY_ge : (Real.sqrt X) / (2 * Real.exp 1) ≤ (Y : ℝ)) :
    (∑ n ∈ (Finset.Ioc Y (2 * Y)).filter (fun n => ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Z), (1 : ℝ) / n) ≤
      (3 * C_smooth) * Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ) := by
  let Q' := ⌊Z⌋₊
  have hZ0 : 0 ≤ Z := by linarith
  have hY1 : 1 ≤ Y := by omega
  rw [filter_smooth_eq Y Z hZ0 hY1]
  have h4Z : (4 : ℝ) ≤ Z := hZ
  have h4Q' : 4 ≤ Q' := (Nat.le_floor_iff hZ0).mpr h4Z
  have hQ'_ge2 : 2 ≤ Q' := by omega
  have hY_ge1 : 1 ≤ (Y : ℝ) := by exact_mod_cast hY1
  have h_tail := h_smooth_sum Q' (2 * Y) (Y : ℝ) hQ'_ge2 hY_ge1
  refine h_tail.trans ?_
  have hQ'_pos : 0 < (Q' : ℝ) := by positivity
  have hQ'_le_Z : (Q' : ℝ) ≤ Z := Nat.floor_le hZ0
  have _hZ_pos : 0 < Z := by linarith
  have hZ_gt1 : 1 < Z := by linarith
  have hQ'_gt1 : 1 < (Q' : ℝ) := by
    have : (4 : ℝ) ≤ (Q' : ℝ) := by exact_mod_cast h4Q'
    linarith
  have hlogQ'_pos : 0 < Real.log (Q' : ℝ) := Real.log_pos hQ'_gt1
  have _hlogZ_pos : 0 < Real.log Z := Real.log_pos hZ_gt1
  have hlogQ'_le_Z : Real.log (Q' : ℝ) ≤ Real.log Z := Real.log_le_log hQ'_pos hQ'_le_Z
  have h_rpow_log : (Real.log (Q' : ℝ)) ^ (6 : ℝ) ≤ (Real.log Z) ^ (6 : ℝ) :=
    Real.rpow_le_rpow hlogQ'_pos.le hlogQ'_le_Z (by norm_num)
  have _hY_real_pos : 0 < (Y : ℝ) := by positivity
  have hY_gt1 : 1 < (Y : ℝ) := by
    have : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY2
    linarith
  have hlogY_pos : 0 < Real.log (Y : ℝ) := Real.log_pos hY_gt1
  have h_exp1 : Real.exp (-(Real.log (Y : ℝ)) / (2 * Real.log (Q' : ℝ))) ≤
      Real.exp (-(Real.log (Y : ℝ)) / (2 * Real.log Z)) := by
    apply Real.exp_le_exp.mpr
    have h1 : 2 * Real.log (Q' : ℝ) ≤ 2 * Real.log Z := by linarith
    have h2 : 0 < 2 * Real.log (Q' : ℝ) := by positivity
    have h3 : 1 / (2 * Real.log Z) ≤ 1 / (2 * Real.log (Q' : ℝ)) :=
      one_div_le_one_div_of_le h2 h1
    have h4 : (Real.log (Y : ℝ)) * (1 / (2 * Real.log Z)) ≤ (Real.log (Y : ℝ)) * (1 / (2 * Real.log (Q' : ℝ))) :=
      mul_le_mul_of_nonneg_left h3 hlogY_pos.le
    have h_div1 : (Real.log (Y : ℝ)) * (1 / (2 * Real.log Z)) = (Real.log (Y : ℝ)) / (2 * Real.log Z) := by ring
    have h_div2 : (Real.log (Y : ℝ)) * (1 / (2 * Real.log (Q' : ℝ))) = (Real.log (Y : ℝ)) / (2 * Real.log (Q' : ℝ)) := by ring
    rw [h_div1, h_div2] at h4
    rw [neg_div, neg_div]
    linarith
  have h_exp2 := exp_tail_le X Y Z hZ hX hlogX hY_ge
  have h_exp_trans : Real.exp (-(Real.log (Y : ℝ)) / (2 * Real.log (Q' : ℝ))) ≤
      Real.exp 1 * Real.exp (-(Real.log X) / (4 * Real.log Z)) :=
    h_exp1.trans h_exp2
  have he_lt3 : Real.exp 1 ≤ 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h_exp3 : Real.exp 1 * Real.exp (-(Real.log X) / (4 * Real.log Z)) ≤
      3 * Real.exp (-(Real.log X) / (4 * Real.log Z)) :=
    mul_le_mul_of_nonneg_right he_lt3 (by positivity)
  have h_exp_final : Real.exp (-(Real.log (Y : ℝ)) / (2 * Real.log (Q' : ℝ))) ≤
      3 * Real.exp (-(Real.log X) / (4 * Real.log Z)) :=
    h_exp_trans.trans h_exp3
  have h_mul1 : C_smooth * Real.exp (-(Real.log (Y : ℝ)) / (2 * Real.log (Q' : ℝ))) ≤
      C_smooth * (3 * Real.exp (-(Real.log X) / (4 * Real.log Z))) :=
    mul_le_mul_of_nonneg_left h_exp_final hC_smooth.le
  have h_term_final : C_smooth * Real.exp (-(Real.log (Y : ℝ)) / (2 * Real.log (Q' : ℝ))) * (Real.log (Q' : ℝ)) ^ (6 : ℝ) ≤
      (3 * C_smooth) * Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ) := by
    have _hA : 0 ≤ C_smooth * Real.exp (-(Real.log (Y : ℝ)) / (2 * Real.log (Q' : ℝ))) := by positivity
    have hB : 0 ≤ (Real.log (Q' : ℝ)) ^ (6 : ℝ) := by positivity
    calc C_smooth * Real.exp (-(Real.log (Y : ℝ)) / (2 * Real.log (Q' : ℝ))) * (Real.log (Q' : ℝ)) ^ (6 : ℝ)
        ≤ (C_smooth * (3 * Real.exp (-(Real.log X) / (4 * Real.log Z)))) * (Real.log (Q' : ℝ)) ^ (6 : ℝ) :=
          mul_le_mul_of_nonneg_right h_mul1 hB
      _ ≤ (C_smooth * (3 * Real.exp (-(Real.log X) / (4 * Real.log Z)))) * (Real.log Z) ^ (6 : ℝ) := by
          have hpos_C : 0 ≤ C_smooth * (3 * Real.exp (-(Real.log X) / (4 * Real.log Z))) := by positivity
          exact mul_le_mul_of_nonneg_left h_rpow_log hpos_C
      _ = (3 * C_smooth) * Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ) := by ring
  exact h_term_final

/-- Splitting of the Dirichlet polynomial on the cofactor range. -/
lemma dirichletPoly_cofactorRange_le (c : ℕ → ℂ) (hc : ∀ m, ‖c m‖ ≤ 1) (X : ℕ) (H : ℝ) (v : ℕ) (t : ℝ)
    (hY2 : 2 ≤ ⌊(X : ℝ) * Real.exp (-(v / H))⌋₊) :
    let y := (X : ℝ) * Real.exp (-(v / H))
    let Y := ⌊y⌋₊
    ‖dirichletPoly c (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ≤
      ‖dirichletPoly c (Finset.Ioc Y (2 * Y)) ((1 : ℂ) + t * Complex.I)‖ + 1 / (Y : ℝ) := by
  intro y Y
  have hy : 0 ≤ y := by positivity
  have h_range : cofactorRange X H v = Finset.Ioc Y ⌊2 * y⌋₊ :=
    cofactorRange_eq_Ioc X H v
  have h_cases : ⌊2 * y⌋₊ = 2 * Y ∨ ⌊2 * y⌋₊ = 2 * Y + 1 :=
    floor_two_mul_le y hy
  rcases h_cases with h2Y | h2Y1
  · rw [h_range, h2Y]
    have : 0 ≤ 1 / (Y : ℝ) := by positivity
    linarith
  · rw [h_range, h2Y1]
    have h_split : Finset.Ioc Y (2 * Y + 1) = insert (2 * Y + 1) (Finset.Ioc Y (2 * Y)) :=
      Ioc_succ Y (2 * Y) (by omega)
    rw [h_split]
    have hnotmem : 2 * Y + 1 ∉ Finset.Ioc Y (2 * Y) := by
      simp only [Finset.mem_Ioc, not_and]
      omega
    unfold dirichletPoly
    rw [Finset.sum_insert hnotmem]
    have h_tri := norm_add_le (c (2 * Y + 1) * ((2 * Y + 1 : ℕ) : ℂ) ^ (-((1 : ℂ) + t * Complex.I)))
      (∑ x ∈ Finset.Ioc Y (2 * Y), c x * (x : ℂ) ^ (-((1 : ℂ) + t * Complex.I)))
    refine h_tri.trans ?_
    have h_term : ‖c (2 * Y + 1) * ((2 * Y + 1 : ℕ) : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤ 1 / (Y : ℝ) := by
      rw [norm_mul]
      have hpos : 0 < 2 * Y + 1 := by omega
      have h_cpow := norm_natCast_cpow_neg_one_add_mul_I (2 * Y + 1) hpos t
      rw [h_cpow]
      have hc_le := hc (2 * Y + 1)
      have h_denom_pos : 0 < ((2 * Y + 1 : ℕ) : ℝ) := by positivity
      have h_mul : ‖c (2 * Y + 1)‖ * (1 / ((2 * Y + 1 : ℕ) : ℝ)) ≤ 1 / ((2 * Y + 1 : ℕ) : ℝ) := by
        have := mul_le_mul_of_nonneg_right hc_le (one_div_nonneg.mpr h_denom_pos.le)
        rwa [one_mul] at this
      refine h_mul.trans ?_
      have hY_le : (Y : ℝ) ≤ ((2 * Y + 1 : ℕ) : ℝ) := by
        have : Y ≤ 2 * Y + 1 := by omega
        exact_mod_cast this
      have hY_pos : 0 < (Y : ℝ) := Nat.cast_pos.mpr (by have : 2 ≤ Y := hY2; omega)
      exact one_div_le_one_div_of_le hY_pos hY_le
    linarith

/-- $Z \le X^\beta$ from $Z \le \sqrt{X}$ and $3/4 \le \beta$. -/
lemma Z_le_X_rpow_beta (X : ℕ) (β : ℝ) (Z : ℝ) (_hX : 16 ≤ X) (hβ : 3 / 4 ≤ β)
    (hZX : Z ≤ Real.sqrt X) : Z ≤ (X : ℝ) ^ β := by
  have _hX_pos : 0 < (X : ℝ) := by positivity
  have hX1 : 1 ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have h_sqrt : Real.sqrt X = (X : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have h_exp : (1 / 2 : ℝ) ≤ β := by linarith
  have h_rpow : (X : ℝ) ^ (1 / 2 : ℝ) ≤ (X : ℝ) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hX1 h_exp
  rw [h_sqrt] at hZX
  exact hZX.trans h_rpow

/-- Linear combination of three non-negative terms. -/
lemma combine_three_terms (C_E C_tail C A1 A2 A3 : ℝ)
    (hCE : C_E ≤ C) (h10 : 10 ≤ C) (hC_tail : C_tail ≤ C)
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) :
    C_E * A1 + 10 * A2 + C_tail * A3 ≤ C * (A1 + A2 + A3) := by
  have h1 : C_E * A1 ≤ C * A1 := mul_le_mul_of_nonneg_right hCE hA1
  have h2 : 10 * A2 ≤ C * A2 := mul_le_mul_of_nonneg_right h10 hA2
  have h3 : C_tail * A3 ≤ C * A3 := mul_le_mul_of_nonneg_right hC_tail hA3
  calc C_E * A1 + 10 * A2 + C_tail * A3
      ≤ C * A1 + C * A2 + C * A3 := by linarith
    _ = C * (A1 + A2 + A3) := by ring

/-- Main theorem: pointwise bound on the cofactor polynomial $R_v$ at height $|t| \ge \tau$. -/
theorem norm_Rv_le_of_region (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (t τ Z : ℝ),
      3 / 4 ≤ β → β < 1 → 16 ≤ X → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ (X : ℝ) ^ β → 1 ≤ H →
      v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊ → 1 ≤ τ → τ ≤ |t| → |t| ≤ X →
      (Q : ℝ) < Z → 4 ≤ Z → Z ≤ Real.sqrt X → Real.log X ≤ (Real.log (Z - 1)) ^ (5 / 4 : ℝ) →
      ‖dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ≤
        C * ((Real.log X + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) := by
  obtain ⟨c_prime, C_prime, hc_prime, hC_prime, h_prime_sum⟩ :=
    sum_primes_cpow_neg_one_sub_mul_I_le c₀ K hc₀ hK hζ hholo
  obtain ⟨C_smooth, hC_smooth, h_smooth_sum⟩ := sum_smooth_tail_le_exp
  let c := min c_prime 1
  have hc : 0 < c := lt_min hc_prime (by norm_num)
  have hc1 : c ≤ 1 := min_le_right _ _
  have hcc_prime : c ≤ c_prime := min_le_left _ _
  let C_E := C_prime + 4
  let C_tail := 3 * C_smooth
  let C := max C_E (max 10 C_tail) + 1
  have hC : 0 < C := by
    have : 0 < C_E := by dsimp [C_E]; linarith
    have : 0 < max C_E (max 10 C_tail) := lt_of_lt_of_le this (le_max_left _ _)
    linarith
  refine ⟨c, C, hc, hC, ?_⟩
  intro β X P Q H v t τ Z hβ_ge _hβ_lt hX hP hPQ _hQX hH hv hτ ht_ge ht_le hQZ hZ hZX hlogX_le
  have hlogX : 32 ≤ Real.log X := thirty_two_le_log_of_hyp X Z hX hZ hZX hlogX_le
  have hlogZ1 : 16 ≤ Real.log (Z - 1) := sixteen_le_logZ1 X Z hZ hlogX hlogX_le
  let y := (X : ℝ) * Real.exp (-(v / H))
  let Y := ⌊y⌋₊
  have hv_le : v ≤ ⌈H * Real.log Q⌉₊ := (Finset.mem_Icc.mp hv).2
  have hy_ge : (Real.sqrt X) / (Real.exp 1) ≤ y :=
    sqrtX_div_e_le_y X P Q H v Z hX hP hPQ hH hv_le hQZ hZX
  have hY_ge : (Real.sqrt X) / (2 * Real.exp 1) ≤ (Y : ℝ) :=
    sqrtX_div_2e_le_Y X Y y hX hy_ge rfl hlogX
  have hsqrtX_eq : Real.sqrt X = Real.exp ((1 / 2 : ℝ) * Real.log X) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by positivity)]
    congr 1
    ring
  have h16_le : 16 ≤ (1 / 2 : ℝ) * Real.log X := by linarith
  have h_exp16 : Real.exp 16 ≤ Real.sqrt X := by
    rw [hsqrtX_eq]
    exact Real.exp_le_exp.mpr h16_le
  have h_17_le : 17 ≤ Real.exp 16 := by
    have h1 := Real.add_one_le_exp (16 : ℝ)
    linarith
  have h17_le : 17 ≤ Real.sqrt X := h_17_le.trans h_exp16
  have hY2 : 2 ≤ Y := two_le_Y X Y hY_ge h17_le
  have hY_pos : 0 < Y := by omega
  have hv_nonneg : 0 ≤ (v : ℝ) := by positivity
  have hY_le_X : (Y : ℝ) ≤ (X : ℝ) := Y_le_X X H v (by linarith) hv_nonneg
  have hlog2Y : Real.log (2 * (Y : ℝ)) + 1 ≤ Real.log X + 2 :=
    log_two_mul_Y_add_one_le X Y hY_pos hY_le_X
  have hYZ : Z / (2 * Real.exp 1) ≤ (Y : ℝ) := by
    have h1 : Z / (2 * Real.exp 1) ≤ (Real.sqrt X) / (2 * Real.exp 1) :=
      div_le_div_of_nonneg_right hZX (by positivity)
    exact h1.trans hY_ge
  have hinvY : (1 : ℝ) / (Y : ℝ) ≤ 6 / Z := inv_Y_le Y Z hZ hYZ
  let c_poly : ℕ → ℂ := fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
  have hc_poly : ∀ m, ‖c_poly m‖ ≤ 1 := fun m => norm_c_le_one β X P Q m
  have hZ_3 : 3 ≤ Z := by linarith
  have hZW : Z ≤ (X : ℝ) ^ β := Z_le_X_rpow_beta X β Z hX hβ_ge hZX
  have ht_ge1 : 1 ≤ |t| := hτ.trans ht_ge
  let E := C_E * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)))
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    have : 0 ≤ C_E := by dsimp [C_E]; linarith
    have : 0 ≤ 1 / (τ * Real.log (Z - 1)) := by positivity
    have : 0 ≤ Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by positivity
    positivity
  have hfac : ∀ (p m : ℕ), Nat.Prime p → Z < (p : ℝ) → 0 < m →
      c_poly (p * m) = if (p : ℝ) ≤ (X : ℝ) ^ β then c_poly m else 0 :=
    fun p m hp hpZ hm => c_fac β X P Q Z hQZ p m hp hpZ hm
  have hstar : ∀ (a b : ℝ), Z ≤ a → a < b → b ≤ 2 * a →
      ‖∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤ E :=
    fun a b hZa hab hb2a => hstar_bound c_prime C_prime hc_prime hC_prime h_prime_sum
      c hc hc1 hcc_prime X t τ Z hX hZ hlogZ1 hlogX_le hτ ht_ge ht_le a b hZa hab hb2a
  have h_main_poly := norm_dirichletPoly_le_of_prime_sums c_poly c_poly Y Z ((X : ℝ) ^ β) t E
    hc_poly hc_poly hZ_3 hZW hY2 ht_ge1 hE_nonneg hfac hstar
  have h_range_split := dirichletPoly_cofactorRange_le c_poly hc_poly X H v t hY2
  have h_smooth_bound := smooth_tail_bound C_smooth hC_smooth h_smooth_sum X Y Z hX hZ hlogX hY2 hY_ge
  let A1 := (Real.log X + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)))
  let A2 := 1 / Z
  let A3 := Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)
  have hA1 : 0 ≤ A1 := by
    dsimp [A1]
    have : 0 ≤ Real.log X + 2 := by linarith
    have : 0 ≤ 1 / (τ * Real.log (Z - 1)) := by positivity
    have : 0 ≤ Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by positivity
    positivity
  have hA2 : 0 ≤ A2 := by dsimp [A2]; positivity
  have hA3 : 0 ≤ A3 := by
    dsimp [A3]
    have : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
    positivity
  have hCE_le : C_E ≤ C := le_of_lt (lt_of_le_of_lt (le_max_left _ _) (lt_add_one _))
  have h10_le : 10 ≤ C := by
    have h1 : 10 ≤ max 10 C_tail := le_max_left _ _
    have h2 : max 10 C_tail ≤ max C_E (max 10 C_tail) := le_max_right _ _
    exact le_of_lt (lt_of_le_of_lt (h1.trans h2) (lt_add_one _))
  have hC_tail_le : C_tail ≤ C := by
    have h1 : C_tail ≤ max 10 C_tail := le_max_right _ _
    have h2 : max 10 C_tail ≤ max C_E (max 10 C_tail) := le_max_right _ _
    exact le_of_lt (lt_of_le_of_lt (h1.trans h2) (lt_add_one _))
  have h_comb := combine_three_terms C_E C_tail C A1 A2 A3 hCE_le h10_le hC_tail_le hA1 hA2 hA3
  refine h_range_split.trans ?_
  refine le_trans (add_le_add_left h_main_poly (1 / (Y : ℝ))) ?_
  have h_term1_le : (Real.log (2 * (Y : ℝ)) + 1) * E ≤ C_E * A1 := by
    dsimp [E, A1]
    have h_factor : 0 ≤ 1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by
      have : 0 < τ := by linarith
      have : 0 < Real.log (Z - 1) := by linarith [hlogZ1]
      have _h1 : 0 ≤ 1 / (τ * Real.log (Z - 1)) := by positivity
      have _h2 : 0 ≤ Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)) := by positivity
      linarith
    have h_log_mul : (Real.log (2 * (Y : ℝ)) + 1) *
        (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) ≤
        (Real.log X + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) :=
      mul_le_mul_of_nonneg_right hlog2Y h_factor
    have : (Real.log (2 * (Y : ℝ)) + 1) *
        (C_E * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)))) =
        C_E * ((Real.log (2 * (Y : ℝ)) + 1) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ)))) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h_log_mul (by dsimp [C_E]; linarith)
  have h_Z_terms : 4 / Z + 1 / (Y : ℝ) ≤ 10 * A2 := by
    dsimp [A2]
    calc 4 / Z + 1 / (Y : ℝ) ≤ 4 / Z + 6 / Z := by linarith [hinvY]
      _ = 10 / Z := by ring
      _ = 10 * (1 / Z) := by ring
  calc (Real.log (2 * (Y : ℝ)) + 1) * E + 4 / Z +
        (∑ n ∈ (Finset.Ioc Y (2 * Y)).filter (fun n => ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Z), (1 : ℝ) / n) +
        1 / (Y : ℝ)
      = (Real.log (2 * (Y : ℝ)) + 1) * E + (4 / Z + 1 / (Y : ℝ)) +
        (∑ n ∈ (Finset.Ioc Y (2 * Y)).filter (fun n => ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Z), (1 : ℝ) / n) := by ring
    _ ≤ C_E * A1 + 10 * A2 + C_tail * A3 := by
        have : (3 * C_smooth) * Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ) = C_tail * A3 := by
          dsimp [C_tail, A3]
          ring
        rw [← this]
        linarith [h_term1_le, h_Z_terms, h_smooth_bound]
    _ ≤ C * (A1 + A2 + A3) := h_comb
    _ = C * ((Real.log X + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
              + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) := rfl

end Erdos1201.MR
