/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

Attribution: the original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
-/
import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Setup
import Erdos1201.MR.Arithmetic
import Erdos1201.MR.Ramare
import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.MR.Analysis.MeanValueTheorem
import Erdos1201.MR.Analysis.ShortRangePrimeMassBT

open scoped BigOperators Real
open MeasureTheory intervalIntegral Erdos1201.MR

/-!
# Matomäki–Radziwiłł Lemma 12: Decomposition into Short-Range Bilinear Polynomials

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes Matomäki–Radziwiłł Lemma 12 (arXiv:1501.04585v4, Section 5), which
decomposes the mean square of the Dirichlet polynomial $F(s) = \sum_{X < n \le 2X} a_n n^{-s}$
on the line $\text{Re}(s) = 1$ over a measurable subset $U \subseteq [-T, T]$ into the sum
of short bilinear forms $Q_{v,H}(s) R_{v,H}(s)$ and three error terms: boundary terms
$E_1$ bounded by $O((T/X+1)/H)$, square terms $E_2$ bounded by $O((T/X+1)/P)$, and the
unsifted polynomial $E_3$ bounded by $O((T/X+1) \cdot \text{card}(\text{unsifted})/X)$.
-/

namespace Erdos1201.MR

/-- `‖a + b‖^2 ≤ 2 ‖a‖^2 + 2 ‖b‖^2` for complex numbers. -/
lemma norm_add_sq_le_two_mul (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    nlinarith [norm_nonneg (a + b), norm_nonneg a, norm_nonneg b]
  have h3 : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have : 0 ≤ (‖a‖ - ‖b‖) ^ 2 := sq_nonneg _
    nlinarith
  exact h2.trans h3

/-- `‖a + b + c‖^2 ≤ 3 (‖a‖^2 + ‖b‖^2 + ‖c‖^2)` for complex numbers. -/
lemma norm_add_three_sq_le (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h1 : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    have := norm_add_le (a + b) c
    have := norm_add_le a b
    linarith
  have h2 : ‖a + b + c‖ ^ 2 ≤ (‖a‖ + ‖b‖ + ‖c‖) ^ 2 := by
    have _h_nonneg : 0 ≤ ‖a + b + c‖ := norm_nonneg _
    have _h_sum_nonneg : 0 ≤ ‖a‖ + ‖b‖ + ‖c‖ := by positivity
    nlinarith
  have h3 : (‖a‖ + ‖b‖ + ‖c‖) ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
    have _h_ab : 0 ≤ (‖a‖ - ‖b‖) ^ 2 := sq_nonneg _
    have _h_bc : 0 ≤ (‖b‖ - ‖c‖) ^ 2 := sq_nonneg _
    have _h_ca : 0 ≤ (‖c‖ - ‖a‖) ^ 2 := sq_nonneg _
    nlinarith
  exact h2.trans h3

/-- `‖a + b + c + d‖^2 ≤ 4 (‖a‖^2 + ‖b‖^2 + ‖c‖^2 + ‖d‖^2)` for complex numbers. -/
lemma norm_add_four_sq_le (a b c d : ℂ) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h1 : ‖(a + b) + (c + d)‖ ^ 2 ≤ 2 * ‖a + b‖ ^ 2 + 2 * ‖c + d‖ ^ 2 :=
    norm_add_sq_le_two_mul (a + b) (c + d)
  calc ‖a + b + c + d‖ ^ 2
    _ = ‖(a + b) + (c + d)‖ ^ 2 := by ring_nf
    _ ≤ 2 * ‖a + b‖ ^ 2 + 2 * ‖c + d‖ ^ 2 := h1
    _ ≤ 2 * (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) + 2 * (2 * ‖c‖ ^ 2 + 2 * ‖d‖ ^ 2) := by
      linarith [norm_add_sq_le_two_mul a b, norm_add_sq_le_two_mul c d]
    _ = 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by ring

/-- Cauchy-Schwarz for finite sum of complex numbers: `‖∑ v ∈ V, w v‖^2 ≤ V.card * ∑ v ∈ V, ‖w v‖^2`. -/
lemma norm_sum_sq_le_card_mul_sum_sq {α : Type*} (V : Finset α) (w : α → ℂ) :
    ‖∑ v ∈ V, w v‖ ^ 2 ≤ (V.card : ℝ) * ∑ v ∈ V, ‖w v‖ ^ 2 := by
  have h1 : ‖∑ v ∈ V, w v‖ ≤ ∑ v ∈ V, ‖w v‖ := norm_sum_le V w
  have h2 : ‖∑ v ∈ V, w v‖ ^ 2 ≤ (∑ v ∈ V, ‖w v‖) ^ 2 := by
    have _h_lhs_nonneg : 0 ≤ ‖∑ v ∈ V, w v‖ := norm_nonneg _
    have _h_rhs_nonneg : 0 ≤ ∑ v ∈ V, ‖w v‖ := by positivity
    nlinarith
  have h3 : (∑ v ∈ V, ‖w v‖) ^ 2 ≤ (V.card : ℝ) * ∑ v ∈ V, ‖w v‖ ^ 2 := by
    have h_cs := Finset.sum_mul_sq_le_sq_mul_sq V (fun _ => (1 : ℝ)) (fun v => ‖w v‖)
    simp only [one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, one_mul] at h_cs
    exact h_cs
  exact h2.trans h3

/-- Log 2 is bounded below by 1/2 since e < 4. -/
lemma half_lt_log_two : (1 : ℝ) / 2 < Real.log 2 := by
  have hexp : Real.exp 1 < 4 := by
    have := Real.exp_one_lt_three
    linarith
  have hlog : Real.log (Real.exp 1) < Real.log 4 := by
    apply Real.log_lt_log (Real.exp_pos 1) hexp
  rw [Real.log_exp] at hlog
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have hmul : (4 : ℝ) = 2 * 2 := by norm_num
    rw [hmul, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [h4] at hlog
  linarith

/-- The number of short ranges v is bounded by `5 * H * log Q`. -/
lemma card_Icc_log_le (H : ℝ) (P Q : ℕ) (hH : 1 ≤ H) (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    (((Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊).card : ℝ)) ≤ 5 * (H * Real.log Q) := by
  have _hlog2 := half_lt_log_two
  have hP_real : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hQ_real : (P : ℝ) ≤ Q := by exact_mod_cast hPQ
  have h2Q : (2 : ℝ) ≤ Q := hP_real.trans hQ_real
  have _hlog2_le : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) h2Q
  have hlogQ_pos : 0 < Real.log Q := by linarith
  have hH_pos : 0 < H := by linarith
  have hHlogQ_pos : 0 < H * Real.log Q := mul_pos hH_pos hlogQ_pos
  have h_bound : 2 ≤ 4 * (H * Real.log Q) := by
    calc 2 = 4 * ((1 : ℝ) / 2) := by ring
    _ ≤ 4 * Real.log 2 := by linarith
    _ ≤ 4 * (1 * Real.log Q) := by
      gcongr
      linarith
    _ ≤ 4 * (H * Real.log Q) := by
      gcongr
  have h_card : (Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊).card ≤ ⌈H * Real.log Q⌉₊ + 1 := by
    rw [Nat.card_Icc]
    exact Nat.sub_le _ _
  have h_card_real : (((Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊).card : ℝ)) ≤
      (⌈H * Real.log Q⌉₊ : ℝ) + 1 := by
    exact_mod_cast h_card
  have _h_ceil : (⌈H * Real.log Q⌉₊ : ℝ) < H * Real.log Q + 1 := Nat.ceil_lt_add_one hHlogQ_pos.le
  calc (((Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊).card : ℝ))
    _ ≤ (⌈H * Real.log Q⌉₊ : ℝ) + 1 := h_card_real
    _ ≤ (H * Real.log Q + 1) + 1 := by linarith
    _ = H * Real.log Q + 2 := by ring
    _ ≤ H * Real.log Q + 4 * (H * Real.log Q) := by linarith
    _ = 5 * (H * Real.log Q) := by ring

/-- Continuity of a single Dirichlet power summand t ↦ n^{-(1 + it)}. -/
lemma continuous_cpow_term_l12 (n : ℕ) (hn : 0 < n) :
    Continuous (fun t : ℝ => (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) := by
  have h_eq : (fun t : ℝ => (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) =
      (fun t : ℝ => (1 / (n : ℂ)) * Complex.exp (-Complex.I * (t : ℂ) * ((Real.log n : ℝ) : ℂ))) := by
    ext t
    exact natCast_cpow_neg_one_add_mul_I_eq_exp n hn t
  rw [h_eq]
  fun_prop

/-- Continuity of a finite Dirichlet polynomial on the line Re s = 1. -/
lemma continuous_dirichletPoly_l12 (a : ℕ → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    Continuous (fun t : ℝ => dirichletPoly a S ((1 : ℂ) + (t : ℝ) * Complex.I)) := by
  unfold dirichletPoly
  apply continuous_finsetSum
  intro n hn
  exact continuous_const.mul (continuous_cpow_term_l12 n (hS n hn))

/-- Continuity of the squared norm of a Dirichlet polynomial. -/
lemma continuous_norm_sq_dirichletPoly (a : ℕ → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    Continuous (fun t : ℝ => ‖dirichletPoly a S ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) :=
  (continuous_dirichletPoly_l12 a S hS).norm.pow 2

/-- Integrability on compact intervals for the squared norm of a Dirichlet polynomial. -/
lemma integrableOn_norm_sq_dirichletPoly (a : ℕ → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (T : ℝ) :
    IntegrableOn (fun t : ℝ => ‖dirichletPoly a S ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) (Set.Icc (-T) T) :=
  (continuous_norm_sq_dirichletPoly a S hS).continuousOn.integrableOn_Icc

/-- For non-negative integrable functions on `[-T, T]`, the integral over a subset `U ⊆ [-T, T]`
is bounded by the interval integral. -/
theorem setIntegral_norm_sq_dirichletPoly_le (a : ℕ → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    (T : ℝ) (hT : 0 ≤ T) (U : Set ℝ) (_hU : MeasurableSet U) (hsub : U ⊆ Set.Icc (-T) T) :
    ∫ t in U, ‖dirichletPoly a S ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
      ∫ t in (-T)..T, ‖dirichletPoly a S ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
  let f : ℝ → ℝ := fun t => ‖dirichletPoly a S ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2
  have hf : ∀ t, 0 ≤ f t := fun _ => sq_nonneg _
  have hint : IntegrableOn f (Set.Icc (-T) T) := integrableOn_norm_sq_dirichletPoly a S hS T
  have h_le : ∫ t in U, f t ≤ ∫ t in Set.Icc (-T) T, f t := by
    apply setIntegral_mono_set hint.integrable (ae_of_all _ hf) hsub.eventuallyLE
  have h_neg_le : -T ≤ T := by linarith
  have h_int_eq : ∫ t in Set.Icc (-T) T, f t = ∫ t in Set.Ioc (-T) T, f t := by
    rw [← integral_Icc_eq_integral_Ioc]
  have h_interval : ∫ t in (-T)..T, f t = ∫ t in Set.Ioc (-T) T, f t :=
    integral_of_le h_neg_le
  linarith

/-- Linear factor bound for Montgomery's mean value theorem. -/
lemma montgomery_factor_le (T X N : ℝ) (hT : 0 ≤ T) (hX : 1 ≤ X) (hN : N ≤ 6 * X) :
    2 * T + 6 * Real.pi * N ≤ (36 * Real.pi + 2) * X * (T / X + 1) := by
  have hX_pos : 0 < X := by linarith
  have _hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have _h1 : 6 * Real.pi * N ≤ 36 * Real.pi * X := by
    calc 6 * Real.pi * N ≤ 6 * Real.pi * (6 * X) := by gcongr
    _ = 36 * Real.pi * X := by ring
  have _h2 : (36 * Real.pi + 2) * X * (T / X + 1) = (36 * Real.pi + 2) * T + (36 * Real.pi + 2) * X := by
    have : X * (T / X + 1) = T + X := by
      rw [mul_add, mul_div_cancel₀ T hX_pos.ne', mul_one]
    rw [mul_assoc, this, mul_add]
  have _h3 : 2 * T ≤ (36 * Real.pi + 2) * T := by
    nlinarith
  have _h4 : 36 * Real.pi * X ≤ (36 * Real.pi + 2) * X := by
    nlinarith
  linarith

/-- Montgomery's mean value theorem on an arbitrary sub-finset `S ⊆ (0, N]`. -/
theorem integral_norm_sq_dirichletPoly_subset_le (a : ℕ → ℂ) (S : Finset ℕ) (N : ℕ)
    (hS : S ⊆ Finset.Ioc 0 N) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, ‖dirichletPoly a S ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (2 * T + 6 * Real.pi * N) * ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  let a' : ℕ → ℂ := fun n => if n ∈ S then a n else 0
  have h_poly : ∀ s : ℂ, dirichletPoly a S s = dirichletPoly a' (Finset.Ioc 0 N) s := by
    intro s
    unfold dirichletPoly
    rw [← Finset.sum_subset hS]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [a', hn]
    · intro n _hn hnot
      simp [a', hnot]
  have h_int_eq : (∫ t in (-T)..T, ‖dirichletPoly a S ((1 : ℂ) + t * Complex.I)‖ ^ 2) =
      ∫ t in (-T)..T, ‖dirichletPoly a' (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp
    rw [h_poly]
  rw [h_int_eq]
  have h_mvt := integral_norm_sq_dirichletPoly_le_mul a' N T hT
  refine h_mvt.trans ?_
  have h_sum_eq : (∑ n ∈ Finset.Ioc 0 N, ‖a' n‖ ^ 2 / (n : ℝ) ^ 2) =
      ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
    rw [← Finset.sum_subset hS]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [a', hn]
    · intro n _hn hnot
      simp [a', hnot]
  rw [h_sum_eq]

/-- Mean square bound for `F(s)` on `(X, 2X]` via Montgomery's mean value theorem. -/
theorem integral_norm_sq_F_le_mul (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X : ℕ) (hX : 1 ≤ X)
    (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, ‖dirichletPoly a (Finset.Ioc X (2 * X)) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (36 * Real.pi + 2) * (T / (X : ℝ) + 1) := by
  let S := Finset.Ioc X (2 * X)
  have hS_sub : S ⊆ Finset.Ioc 0 (2 * X) := by
    intro n hn
    simp only [S, Finset.mem_Ioc] at hn ⊢
    exact ⟨by linarith, hn.2⟩
  let a' : ℕ → ℂ := fun n => if n ∈ S then a n else 0
  have h_poly : ∀ s : ℂ, dirichletPoly a S s = dirichletPoly a' (Finset.Ioc 0 (2 * X)) s := by
    intro s
    unfold dirichletPoly
    rw [← Finset.sum_subset hS_sub]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [a', hn]
    · intro n _hn hnot
      simp [a', hnot]
  have h_int_eq : (∫ t in (-T)..T, ‖dirichletPoly a S ((1 : ℂ) + t * Complex.I)‖ ^ 2) =
      ∫ t in (-T)..T, ‖dirichletPoly a' (Finset.Ioc 0 (2 * X)) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp
    rw [h_poly]
  rw [h_int_eq]
  have h_mvt := integral_norm_sq_dirichletPoly_le_mul a' (2 * X) T hT
  refine h_mvt.trans ?_
  have h_sum_eq : (∑ n ∈ Finset.Ioc 0 (2 * X), ‖a' n‖ ^ 2 / (n : ℝ) ^ 2) =
      ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
    rw [← Finset.sum_subset hS_sub]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [a', hn]
    · intro n _hn hnot
      simp [a', hnot]
  rw [h_sum_eq]
  have h_sum_le : (∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ 1 / (X : ℝ) := by
    have h_term : ∀ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / ((X : ℝ) ^ 2) := by
      intro n hn
      simp only [S, Finset.mem_Ioc] at hn
      have _hn_gt : (X : ℝ) < n := by exact_mod_cast hn.1
      have _hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
      have _hn_pos : 0 < (n : ℝ) := by linarith
      have hn2_ge : (X : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
        nlinarith
      have ha_le : ‖a n‖ ^ 2 ≤ 1 := by
        have := ha n
        have : 0 ≤ ‖a n‖ := norm_nonneg _
        nlinarith
      have : ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right ha_le (by positivity)
      refine this.trans ?_
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hn2_ge
    have h_card : S.card = X := by
      dsimp [S]
      rw [Nat.card_Ioc]
      omega
    have h_sum := Finset.sum_le_sum h_term
    have h_const : (∑ _n ∈ S, (1 : ℝ) / (X : ℝ) ^ 2) = (X : ℝ) * (1 / (X : ℝ) ^ 2) := by
      simp [h_card, nsmul_eq_mul]
    rw [h_const] at h_sum
    refine h_sum.trans_eq ?_
    have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
    field_simp
  have h_factor := montgomery_factor_le T (X : ℝ) (2 * (X : ℝ)) hT (by exact_mod_cast hX) (by linarith)
  have _h_pos : 0 ≤ 2 * T + 6 * Real.pi * (2 * (X : ℝ)) := by
    have : 0 ≤ Real.pi := Real.pi_pos.le
    have : 0 < (X : ℝ) := by exact_mod_cast hX
    positivity
  have h_mul := mul_le_mul h_factor h_sum_le (by
    apply Finset.sum_nonneg
    intro i _
    positivity) (by
    have : 0 < (X : ℝ) := by exact_mod_cast hX
    have : 0 ≤ T / (X : ℝ) := div_nonneg hT (by positivity)
    have : 0 ≤ Real.pi := Real.pi_pos.le
    positivity)
  push_cast
  refine h_mul.trans_eq ?_
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
  have : (36 * Real.pi + 2) * (X : ℝ) * (T / (X : ℝ) + 1) * (1 / (X : ℝ)) =
      (36 * Real.pi + 2) * (T / (X : ℝ) + 1) := by
    calc (36 * Real.pi + 2) * (X : ℝ) * (T / (X : ℝ) + 1) * (1 / (X : ℝ))
      _ = (36 * Real.pi + 2) * (T / (X : ℝ) + 1) * ((X : ℝ) * (1 / (X : ℝ))) := by ring
      _ = (36 * Real.pi + 2) * (T / (X : ℝ) + 1) * 1 := by rw [mul_one_div_cancel hX_pos.ne']
      _ = (36 * Real.pi + 2) * (T / (X : ℝ) + 1) := by ring
  exact this

/-- The unsifted set in `(X, 2X]`: integers having no prime factor in `[P, Q]`. -/
def unsiftedSet (X P Q : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)

/-- Mean square bound for the unsifted component `E₃(s)` via Montgomery's mean value theorem. -/
theorem integral_norm_sq_unsifted_le (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (X P Q : ℕ) (hX : 1 ≤ X)
    (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, ‖dirichletPoly a (unsiftedSet X P Q) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (36 * Real.pi + 2) * (T / (X : ℝ) + 1) * (((unsiftedSet X P Q).card : ℝ) / (X : ℝ)) := by
  let S := unsiftedSet X P Q
  have hS_sub : S ⊆ Finset.Ioc 0 (2 * X) := by
    intro n hn
    simp only [S, unsiftedSet, Finset.mem_filter, Finset.mem_Ioc] at hn
    simp only [Finset.mem_Ioc]
    exact ⟨by linarith, hn.1.2⟩
  let a' : ℕ → ℂ := fun n => if n ∈ S then a n else 0
  have h_poly : ∀ s : ℂ, dirichletPoly a S s = dirichletPoly a' (Finset.Ioc 0 (2 * X)) s := by
    intro s
    unfold dirichletPoly
    rw [← Finset.sum_subset hS_sub]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [a', hn]
    · intro n _hn hnot
      simp [a', hnot]
  have h_int_eq : (∫ t in (-T)..T, ‖dirichletPoly a S ((1 : ℂ) + t * Complex.I)‖ ^ 2) =
      ∫ t in (-T)..T, ‖dirichletPoly a' (Finset.Ioc 0 (2 * X)) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    dsimp
    rw [h_poly]
  rw [h_int_eq]
  have h_mvt := integral_norm_sq_dirichletPoly_le_mul a' (2 * X) T hT
  refine h_mvt.trans ?_
  have h_sum_eq : (∑ n ∈ Finset.Ioc 0 (2 * X), ‖a' n‖ ^ 2 / (n : ℝ) ^ 2) =
      ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
    rw [← Finset.sum_subset hS_sub]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [a', hn]
    · intro n _hn hnot
      simp [a', hnot]
  rw [h_sum_eq]
  have h_sum_le : (∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2) ≤ ((S.card : ℝ) / (X : ℝ)) * (1 / (X : ℝ)) := by
    have h_term : ∀ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / ((X : ℝ) ^ 2) := by
      intro n hn
      simp only [S, unsiftedSet, Finset.mem_filter, Finset.mem_Ioc] at hn
      have _hn_gt : (X : ℝ) < n := by exact_mod_cast hn.1.1
      have _hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
      have _hn_pos : 0 < (n : ℝ) := by linarith
      have hn2_ge : (X : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
        nlinarith
      have ha_le : ‖a n‖ ^ 2 ≤ 1 := by
        have := ha n
        have : 0 ≤ ‖a n‖ := norm_nonneg _
        nlinarith
      have : ‖a n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right ha_le (by positivity)
      refine this.trans ?_
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hn2_ge
    have h_sum := Finset.sum_le_sum h_term
    have h_const : (∑ _n ∈ S, (1 : ℝ) / (X : ℝ) ^ 2) = (S.card : ℝ) * (1 / (X : ℝ) ^ 2) := by
      simp [nsmul_eq_mul]
    rw [h_const] at h_sum
    refine h_sum.trans_eq ?_
    have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
    field_simp
  have h_factor := montgomery_factor_le T (X : ℝ) (2 * (X : ℝ)) hT (by exact_mod_cast hX) (by linarith)
  have _h_pos : 0 ≤ 2 * T + 6 * Real.pi * (2 * (X : ℝ)) := by
    have : 0 ≤ Real.pi := Real.pi_pos.le
    have : 0 < (X : ℝ) := by exact_mod_cast hX
    positivity
  have h_mul := mul_le_mul h_factor h_sum_le (by
    apply Finset.sum_nonneg
    intro i _
    positivity) (by
    have : 0 < (X : ℝ) := by exact_mod_cast hX
    have : 0 ≤ T / (X : ℝ) := div_nonneg hT (by positivity)
    have : 0 ≤ Real.pi := Real.pi_pos.le
    positivity)
  push_cast
  refine h_mul.trans_eq ?_
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
  have : (36 * Real.pi + 2) * (X : ℝ) * (T / (X : ℝ) + 1) * (((S.card : ℝ) / (X : ℝ)) * (1 / (X : ℝ))) =
      (36 * Real.pi + 2) * (T / (X : ℝ) + 1) * (((S.card : ℝ) / (X : ℝ))) := by
    calc (36 * Real.pi + 2) * (X : ℝ) * (T / (X : ℝ) + 1) * (((S.card : ℝ) / (X : ℝ)) * (1 / (X : ℝ)))
      _ = (36 * Real.pi + 2) * (T / (X : ℝ) + 1) * (((S.card : ℝ) / (X : ℝ))) * ((X : ℝ) * (1 / (X : ℝ))) := by ring
      _ = (36 * Real.pi + 2) * (T / (X : ℝ) + 1) * (((S.card : ℝ) / (X : ℝ))) * 1 := by rw [mul_one_div_cancel hX_pos.ne']
      _ = (36 * Real.pi + 2) * (T / (X : ℝ) + 1) * (((S.card : ℝ) / (X : ℝ))) := by ring
  exact this

/-- Exact Ramaré identity for the Dirichlet polynomial `F(s)` on `(X, 2X]`. -/
theorem F_eq_ramare (X P Q : ℕ) (a b c : ℕ → ℂ) (s : ℂ)
    (hfactor : ∀ p m, p ∈ primeRange P Q → ¬ p ∣ m → a (p * m) = b m * c p) :
    dirichletPoly a (Finset.Ioc X (2 * X)) s =
      (∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
        (b m * c p) * ((p * m : ℕ) : ℂ) ^ (-s) / ((omegaIn (primeRange P Q) m : ℂ) + 1)) +
      (∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
        squareCorrection (primeRange P Q) a b c (fun n => (n : ℂ) ^ (-s)) p m) +
      ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => omegaIn (primeRange P Q) n = 0),
        a n * (n : ℂ) ^ (-s) := by
  let T := Finset.Ioc X (2 * X)
  let S := primeRange P Q
  let w : ℕ → ℂ := fun n => (n : ℂ) ^ (-s)
  have hS : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hfac : ∀ p ∈ S, ∀ m, ¬p ∣ m → a (p * m) = b m * c p := by
    intro p hp m hpm
    exact hfactor p m hp hpm
  have h := ramare_with_square_correction T S a b c w hS hfac
  exact h

end Erdos1201.MR
