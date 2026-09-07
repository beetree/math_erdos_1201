/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.Basic
import Erdos1201.Density
import Erdos1201.MR.Target
import Erdos1201.MR.Setup
import Erdos1201.MR.Parseval.Lemma14
import Erdos1201.MR.Decomposition.MediumAverage
import Erdos1201.MR.Prop1.Assembly
import Erdos1201.MR.Prop1.RangeInstance
import Erdos1201.MR.Vinogradov.ZeroFreeInstance
import Erdos1201.MR.Analysis.MeanValueTheorem
import Erdos1201.MR.Decomposition.Lemma12

open scoped BigOperators Real Topology ComplexInnerProductSpace
open Filter Finset MeasureTheory intervalIntegral
open Erdos1201
open Classical

namespace Erdos1201.MR

/-! ### Arithmetic and Dirichlet Polynomial Helpers -/

lemma dirichletPoly_fX_eq_Fu (β : ℝ) (X : ℕ) (s : ℂ) :
    dirichletPoly (fun n => if n ∈ Finset.Ioc X (2 * X) then fX β X n else 0)
      (Finset.Ioc X (2 * X)) s = Fu β X s := by
  unfold Fu dirichletPoly
  apply Finset.sum_congr rfl
  intro n hn
  simp [hn]

lemma dirichletPoly_fX_eq_Fu_fn (β : ℝ) (X : ℕ) :
    dirichletPoly (fun n => if n ∈ Finset.Ioc X (2 * X) then fX β X n else 0)
      (Finset.Ioc X (2 * X)) = Fu β X := by
  ext s
  exact dirichletPoly_fX_eq_Fu β X s

lemma fX_real (β : ℝ) (X n : ℕ) : (starRingEnd ℂ) (fX β X n) = fX β X n := by
  unfold fX smoothIndicator
  split_ifs <;> simp

lemma conj_cpow_nat {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-s)) = (n : ℂ) ^ (-(starRingEnd ℂ s)) := by
  have hn_ne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Complex.cpow_neg, Complex.cpow_neg, map_inv₀]
  congr 1
  rw [Complex.cpow_def, Complex.cpow_def]
  simp only [hn_ne, ↓reduceIte]
  rw [← Complex.exp_conj, map_mul]
  congr 1
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn_pos.le]
  rw [hlog, Complex.conj_ofReal]

lemma conj_Fu (β : ℝ) (X : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (Fu β X ((1 : ℂ) + (t : ℂ) * Complex.I)) =
      Fu β X ((1 : ℂ) + (-t : ℂ) * Complex.I) := by
  unfold Fu dirichletPoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, fX_real]
  have hn_pos : 0 < n := by
    rw [Finset.mem_Ioc] at hn
    omega
  have h_conj_s : (starRingEnd ℂ) ((1 : ℂ) + (t : ℂ) * Complex.I) = (1 : ℂ) + (-t : ℂ) * Complex.I := by
    simp
  rw [conj_cpow_nat hn_pos, h_conj_s]

lemma norm_Fu_neg (β : ℝ) (X : ℕ) (t : ℝ) :
    ‖Fu β X ((1 : ℂ) + (-t : ℂ) * Complex.I)‖ = ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ := by
  have := conj_Fu β X t
  have h := congrArg norm this
  rw [Complex.norm_conj] at h
  exact h.symm

lemma sum_inv_Ioc_le_one {X : ℕ} (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ioc X (2 * X), 1 / (n : ℝ)) ≤ 1 := by
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
  have h_le : ∀ n ∈ Finset.Ioc X (2 * X), 1 / (n : ℝ) ≤ 1 / (X : ℝ) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    apply one_div_le_one_div_of_le hX_pos
    exact_mod_cast hn.1.le
  have h_sum := Finset.sum_le_sum h_le
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc] at h_sum
  have : 2 * X - X = X := by omega
  rw [this] at h_sum
  have : (X : ℝ) * (1 / (X : ℝ)) = 1 := by
    rw [mul_one_div, div_self hX_pos.ne']
  linarith

lemma M_bound_le_one (β : ℝ) (X : ℕ) (hX : 1 ≤ X) :
    (∑ n ∈ Finset.Ioc X (2 * X), ‖fX β X n‖ / (n : ℝ)) ≤ 1 := by
  have h_le : ∀ n ∈ Finset.Ioc X (2 * X), ‖fX β X n‖ / (n : ℝ) ≤ 1 / (n : ℝ) := by
    intro n _
    have hn_pos : 0 ≤ (n : ℝ) := by positivity
    exact div_le_div_of_nonneg_right (norm_fX_le_one β X n) hn_pos
  have h_sum := Finset.sum_le_sum h_le
  exact h_sum.trans (sum_inv_Ioc_le_one hX)

/-! ### Continuous & Piecewise Constant Integration Machinery -/

lemma setIntegral_Ioc_eq_setIntegral_Ico (a b : ℝ) (f : ℝ → ℝ) :
    ∫ x in Set.Ioc a b, f x = ∫ x in Set.Ico a b, f x := by
  apply setIntegral_congr_set
  exact Ioo_ae_eq_Ioc.symm.trans Ioo_ae_eq_Ico

lemma integral_Ioc_const {a b : ℝ} (hab : a ≤ b) (c : ℝ) :
    ∫ _x in Set.Ioc a b, c = c * (b - a) := by
  simp [hab]
  ring

lemma setIntegral_Ioc_const_of_eqOn {a b : ℝ} (hab : a ≤ b) (c : ℝ) (f : ℝ → ℝ)
    (hf : Set.EqOn f (fun _ => c) (Set.Ico a b)) :
    ∫ x in Set.Ioc a b, f x = c * (b - a) := by
  rw [setIntegral_Ioc_eq_setIntegral_Ico]
  rw [setIntegral_congr_fun measurableSet_Ico hf]
  rw [← setIntegral_Ioc_eq_setIntegral_Ico]
  exact integral_Ioc_const hab c

lemma intervalIntegral_const_of_eqOn {a b : ℝ} (hab : a ≤ b) (c : ℝ) (f : ℝ → ℝ)
    (hf : Set.EqOn f (fun _ => c) (Set.Ico a b)) :
    ∫ x in a..b, f x = c * (b - a) := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_Ioc_const_of_eqOn hab c f hf

lemma intervalIntegrable_of_eqOn {a b : ℝ} (hab : a ≤ b) (c : ℝ) (f : ℝ → ℝ)
    (hf : Set.EqOn f (fun _ => c) (Set.Ico a b)) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have h_meas_eq : volume.restrict (Set.Ioc a b) = volume.restrict (Set.Ico a b) :=
    Measure.restrict_congr_set (Ioo_ae_eq_Ioc.symm.trans Ioo_ae_eq_Ico)
  rw [IntegrableOn, h_meas_eq]
  have h_const : Integrable (fun _ : ℝ => c) (volume.restrict (Set.Ico a b)) :=
    integrableOn_const (hs := measure_Ico_lt_top.ne)
  refine Integrable.congr h_const ?_
  refine (ae_restrict_iff' measurableSet_Ico).mpr (Filter.Eventually.of_forall ?_)
  intro x hx
  exact (hf hx).symm

lemma integral_Ico_const_sum {X : ℕ} (f : ℝ → ℝ) (c : ℕ → ℝ)
    (h_eq : ∀ k ∈ Finset.Ico X (2 * X), Set.EqOn f (fun _ => c (k + 1)) (Set.Ico (k : ℝ) ((k : ℝ) + 1))) :
    ∫ x in (X : ℝ)..(2 * (X : ℝ)), f x = ∑ k ∈ Finset.Ico X (2 * X), c (k + 1) := by
  have hX2X : X ≤ 2 * X := Nat.le_mul_of_pos_left _ (by norm_num)
  have h_int : ∀ k ∈ Set.Ico X (2 * X), IntervalIntegrable f volume ((k : ℝ)) ((k + 1 : ℕ) : ℝ) := by
    intro k hk
    have hk_le : (k : ℝ) ≤ (k : ℝ) + 1 := by linarith
    have h_eq_k : Set.EqOn f (fun _ => c (k + 1)) (Set.Ico (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
      push_cast
      exact h_eq k (Finset.mem_Ico.mpr hk)
    exact intervalIntegrable_of_eqOn (by push_cast; linarith) (c (k + 1)) f h_eq_k
  have h_adj := sum_integral_adjacent_intervals_Ico (f := f) (μ := volume)
    (a := fun k => (k : ℝ)) hX2X (fun k hk => h_int k hk)
  have h_terms : (∑ k ∈ Finset.Ico X (2 * X), ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x) =
      ∑ k ∈ Finset.Ico X (2 * X), c (k + 1) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk_le : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by simp
    have h_eq_k : Set.EqOn f (fun _ => c (k + 1)) (Set.Ico (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
      push_cast
      exact h_eq k hk
    rw [intervalIntegral_const_of_eqOn hk_le (c (k + 1)) f h_eq_k]
    push_cast
    ring
  rw [h_terms] at h_adj
  push_cast at h_adj
  exact h_adj.symm

lemma sum_Ico_succ {α : Type*} [AddCommMonoid α] (c : ℕ → α) (a b : ℕ) :
    (∑ k ∈ Finset.Ico a b, c (k + 1)) = ∑ n ∈ Finset.Ioc a b, c n := by
  refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_Ioc]
    omega
  · intro k1 _ k2 _ h
    omega
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    refine ⟨n - 1, ?_, by omega⟩
    rw [Finset.mem_Ico]
    omega
  · intro k _
    rfl

lemma sum_Ioc_le_sum_Ioc (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (X M : ℕ) (hM : M ≤ 2 * X) :
    (∑ n ∈ Finset.Ioc X M, c n) ≤ ∑ n ∈ Finset.Ioc X (2 * X), c n := by
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hc n)
  intro n hn
  rw [Finset.mem_Ioc] at hn ⊢
  exact ⟨hn.1, hn.2.trans hM⟩

lemma norm_sq_ofReal (r : ℝ) : ‖(r : ℂ)‖ ^ 2 = r ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma cast_sub_one_add {n h : ℕ} (hn : 1 ≤ n) :
    ((n + h - 1 : ℕ) : ℝ) = (n : ℝ) + (h : ℝ) - 1 := by
  have : 1 ≤ n + h := by omega
  rw [Nat.cast_sub this]
  push_cast
  ring

lemma floor_add_nat_of_mem_Ico {n h : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Ico ((n : ℝ) - 1) (n : ℝ)) :
    ⌊x + (h : ℝ)⌋₊ = n + h - 1 := by
  have h1 : ((n + h - 1 : ℕ) : ℝ) ≤ x + (h : ℝ) := by
    rw [cast_sub_one_add hn]
    linarith [hx.1]
  have h2 : x + (h : ℝ) < (((n + h - 1 : ℕ) : ℝ) + 1) := by
    rw [cast_sub_one_add hn]
    linarith [hx.2]
  exact Nat.floor_eq_on_Ico (n + h - 1) (x + h) ⟨h1, h2⟩

lemma filter_Ioc_eq_Ico {n h : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Ico ((n : ℝ) - 1) (n : ℝ)) :
    (Finset.Ioc 0 ⌊x + (h : ℝ)⌋₊).filter (fun m : ℕ => x < (m : ℝ)) =
      Finset.Ico n (n + h) := by
  rw [floor_add_nat_of_mem_Ico hn hx]
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨_hm0, hm_le⟩, hxm⟩
    refine ⟨?_, by omega⟩
    by_contra! h_contra
    have : (m : ℝ) + 1 ≤ (n : ℝ) := by
      have : m + 1 ≤ n := by omega
      exact_mod_cast this
    have : (n : ℝ) - 1 < (m : ℝ) := lt_of_le_of_lt hx.1 hxm
    linarith
  · rintro ⟨hnm, hmh⟩
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith [hx.2]

lemma windowSum_eq_sum_Ico (a : ℕ → ℂ) {n h : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Set.Ico ((n : ℝ) - 1) (n : ℝ)) :
    windowSum a x (x + (h : ℝ)) = ∑ m ∈ Finset.Ico n (n + h), a m := by
  unfold windowSum
  rw [filter_Ioc_eq_Ico hn hx]

lemma sum_Ico_eq_sum_range (f : ℕ → ℝ) (n h : ℕ) :
    (∑ m ∈ Finset.Ico n (n + h), f m) = ∑ j ∈ Finset.range h, f (n + j) := by
  have h_bij : (Finset.range h).sum (fun j => f (n + j)) =
      (Finset.Ico n (n + h)).sum f := by
    rw [← Finset.sum_image (fun i _ j _ hij => Nat.add_left_cancel hij)]
    congr 1
    ext m
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · rintro ⟨hnm, hmh⟩; exact ⟨m - n, by omega, by omega⟩
  exact h_bij.symm

lemma sum_Ico_a_eq_shortMean (β : ℝ) (X : ℕ) (n h : ℕ)
    (hnX : X < n) (hnh : n + h ≤ 2 * X + 1) :
    let a := fun m => if m ∈ Finset.Ioc X (2 * X) then fX β X m else 0
    (∑ m ∈ Finset.Ico n (n + h), a m) =
      ((h : ℝ) * shortMean (smoothIndicator ((X : ℝ) ^ β)) h n : ℂ) := by
  intro a
  have h_eq : ∀ m ∈ Finset.Ico n (n + h), a m = (smoothIndicator ((X : ℝ) ^ β) m : ℂ) := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    have hm_ioc : m ∈ Finset.Ioc X (2 * X) := by
      rw [Finset.mem_Ioc]
      omega
    dsimp [a, fX]
    simp [hm_ioc]
  rw [Finset.sum_congr rfl h_eq]
  push_cast
  rw [← Complex.ofReal_sum]
  rw [sum_Ico_eq_sum_range]
  by_cases hh : h = 0
  · simp [hh]
  · have hh_pos : 0 < (h : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hh
    have h_sm : (h : ℝ) * shortMean (smoothIndicator ((X : ℝ) ^ β)) h n =
        ∑ j ∈ Finset.range h, smoothIndicator ((X : ℝ) ^ β) (n + j) := by
      unfold shortMean
      rw [mul_div_cancel₀ _ hh_pos.ne']
    rw [← h_sm]
    push_cast
    rfl

lemma windowSum_div_eq_shortMean (β : ℝ) (X : ℕ) (n h : ℕ)
    (hnX : X < n) (hnh : n + h ≤ 2 * X + 1) (hh : 1 ≤ h) {x : ℝ}
    (hx : x ∈ Set.Ico ((n : ℝ) - 1) (n : ℝ)) :
    let a := fun m => if m ∈ Finset.Ioc X (2 * X) then fX β X m else 0
    windowSum a x (x + (h : ℝ)) / (h : ℂ) =
      (shortMean (smoothIndicator ((X : ℝ) ^ β)) h n : ℂ) := by
  intro a
  have hn : 1 ≤ n := by omega
  rw [windowSum_eq_sum_Ico a hn hx]
  rw [sum_Ico_a_eq_shortMean β X n h hnX hnh]
  have hh_ne : (h : ℂ) ≠ 0 := by
    have : (h : ℝ) ≠ 0 := by exact_mod_cast (by omega : h ≠ 0)
    exact_mod_cast this
  push_cast
  rw [mul_div_cancel_left₀ _ hh_ne]

/-- The master discretization theorem: the sum of squared differences of short means on `(X, M]`
is bounded by the interval integral of the variance of window sums. -/
theorem sum_sq_shortMean_sub_le_integral (β : ℝ) (X : ℕ) (h₁ h₂ M : ℕ)
    (hh₁ : 1 ≤ h₁) (h12 : h₁ ≤ h₂) (hM : M + h₂ ≤ 2 * X + 1) :
    let a := fun m => if m ∈ Finset.Ioc X (2 * X) then fX β X m else 0
    (∑ n ∈ Finset.Ioc X M,
      (shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n - shortMean (smoothIndicator ((X : ℝ) ^ β)) h₂ n) ^ 2) ≤
    ∫ x in (X : ℝ)..(2 * (X : ℝ)),
      ‖windowSum a x (x + (h₁ : ℝ)) / (h₁ : ℂ) - windowSum a x (x + (h₂ : ℝ)) / (h₂ : ℂ)‖ ^ 2 := by
  intro a
  let f := fun x : ℝ =>
    ‖windowSum a x (x + (h₁ : ℝ)) / (h₁ : ℂ) - windowSum a x (x + (h₂ : ℝ)) / (h₂ : ℂ)‖ ^ 2
  let c := fun n : ℕ =>
    ‖(∑ m ∈ Finset.Ico n (n + h₁), a m) / (h₁ : ℂ) -
      (∑ m ∈ Finset.Ico n (n + h₂), a m) / (h₂ : ℂ)‖ ^ 2
  have hc_nonneg : ∀ n, 0 ≤ c n := fun n => sq_nonneg _
  have h_eq : ∀ k ∈ Finset.Ico X (2 * X), Set.EqOn f (fun _ => c (k + 1)) (Set.Ico (k : ℝ) ((k : ℝ) + 1)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have h_k1 : 1 ≤ k + 1 := by omega
    intro x hx
    dsimp [f, c]
    have hx_ico : x ∈ Set.Ico (((k + 1 : ℕ) : ℝ) - 1) ((k + 1 : ℕ) : ℝ) := by
      push_cast
      have : ((k : ℝ) + 1) - 1 = (k : ℝ) := by ring
      rwa [this]
    rw [windowSum_eq_sum_Ico a h_k1 hx_ico, windowSum_eq_sum_Ico a h_k1 hx_ico]
  have h_int_eq := integral_Ico_const_sum f c h_eq
  have h_sum_succ := sum_Ico_succ c X (2 * X)
  rw [h_sum_succ] at h_int_eq
  have hM_le : M ≤ 2 * X := by omega
  have h_sub_le := sum_Ioc_le_sum_Ioc c hc_nonneg X M hM_le
  rw [← h_int_eq] at h_sub_le
  refine le_trans ?_ h_sub_le
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Ioc] at hn
  have hnX : X < n := hn.1
  have hnh1 : n + h₁ ≤ 2 * X + 1 := by omega
  have hnh2 : n + h₂ ≤ 2 * X + 1 := by omega
  dsimp [c]
  rw [sum_Ico_a_eq_shortMean β X n h₁ hnX hnh1, sum_Ico_a_eq_shortMean β X n h₂ hnX hnh2]
  have hh1_ne : (h₁ : ℂ) ≠ 0 := by
    have : (h₁ : ℝ) ≠ 0 := by exact_mod_cast (by omega : h₁ ≠ 0)
    exact_mod_cast this
  have hh2_ne : (h₂ : ℂ) ≠ 0 := by
    have : (h₂ : ℝ) ≠ 0 := by exact_mod_cast (by omega : h₂ ≠ 0)
    exact_mod_cast this
  have h_cancel1 : ((h₁ : ℝ) * shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n : ℂ) / (h₁ : ℂ) =
      (shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n : ℂ) := by
    push_cast
    rw [mul_div_cancel_left₀ _ hh1_ne]
  have h_cancel2 : ((h₂ : ℝ) * shortMean (smoothIndicator ((X : ℝ) ^ β)) h₂ n : ℂ) / (h₂ : ℂ) =
      (shortMean (smoothIndicator ((X : ℝ) ^ β)) h₂ n : ℂ) := by
    push_cast
    rw [mul_div_cancel_left₀ _ hh2_ne]
  rw [h_cancel1, h_cancel2]
  have h_sub_real : (shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n : ℂ) -
      (shortMean (smoothIndicator ((X : ℝ) ^ β)) h₂ n : ℂ) =
      ((shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n - shortMean (smoothIndicator ((X : ℝ) ^ β)) h₂ n : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h_sub_real, norm_sq_ofReal]

/-! ### Chebyshev and Counting Machinery -/

lemma card_filter_le_sum_sq {α : Type*} (s : Finset α) (g : α → ℝ) (c : ℝ) (hc : 0 < c) :
    ((s.filter (fun x => c ≤ |g x|)).card : ℝ) * c ^ 2 ≤ ∑ x ∈ s, (g x) ^ 2 := by
  have h1 : ((s.filter (fun x => c ≤ |g x|)).card : ℝ) * c ^ 2 =
      ∑ x ∈ s.filter (fun x => c ≤ |g x|), c ^ 2 := by
    rw [sum_const, nsmul_eq_mul]
  rw [h1]
  have h2 : ∀ x ∈ s.filter (fun x => c ≤ |g x|), c ^ 2 ≤ (g x) ^ 2 := by
    intro x hx
    rw [mem_filter] at hx
    have hc_le : c ≤ |g x| := hx.2
    have h_sq : c ^ 2 ≤ |g x| ^ 2 := pow_le_pow_left₀ hc.le hc_le 2
    rwa [sq_abs] at h_sq
  have h3 := sum_le_sum h2
  refine h3.trans ?_
  apply sum_le_sum_of_subset_of_nonneg
  · exact filter_subset _ _
  · intro x _ _
    exact sq_nonneg (g x)

lemma card_filter_le_of_sum_sq {α : Type*} (s : Finset α) (g : α → ℝ) (c : ℝ) (hc : 0 < c) :
    ((s.filter (fun x => c ≤ |g x|)).card : ℝ) ≤ (∑ x ∈ s, (g x) ^ 2) / c ^ 2 := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  rw [le_div_iff₀ hc2]
  exact card_filter_le_sum_sq s g c hc

lemma intervalCount_le_split (A : Set ℕ) (X M : ℕ) (hXM : X ≤ M) (hM2X : M ≤ 2 * X) :
    intervalCount A X (2 * X) ≤ ((Finset.Ioc X M).filter (· ∈ A)).card + (2 * X - M) := by
  have h_add := intervalCount_add A hXM hM2X
  have h_le2 := intervalCount_le A M (2 * X)
  have h_def : intervalCount A X M = ((Finset.Ioc X M).filter (· ∈ A)).card := rfl
  rw [h_add, h_def]
  omega

lemma filter_subset_of_triangle {α : Type*} (s : Finset α) (s₁ s₂ : α → ℝ) (μ : ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (h_approx : ∀ x ∈ s, |s₂ x - μ| ≤ δ / 4) :
    s.filter (fun x => δ < |s₁ x - μ|) ⊆ s.filter (fun x => δ / 2 ≤ |s₁ x - s₂ x|) := by
  intro x hx
  rw [mem_filter] at hx ⊢
  refine ⟨hx.1, ?_⟩
  have h1 : δ < |s₁ x - μ| := hx.2
  have h2 : |s₂ x - μ| ≤ δ / 4 := h_approx x hx.1
  have h_tri : |s₁ x - μ| ≤ |s₁ x - s₂ x| + |s₂ x - μ| := by
    have : s₁ x - μ = (s₁ x - s₂ x) + (s₂ x - μ) := by ring
    rw [this]
    exact abs_add_le _ _
  linarith

lemma card_filter_delta_le {α : Type*} (s : Finset α) (s₁ s₂ : α → ℝ) (μ : ℝ) (δ : ℝ) (hδ : 0 < δ)
    (h_approx : ∀ x ∈ s, |s₂ x - μ| ≤ δ / 4) :
    ((s.filter (fun x => δ < |s₁ x - μ|)).card : ℝ) ≤ (∑ x ∈ s, (s₁ x - s₂ x) ^ 2) / (δ / 2) ^ 2 := by
  have h_sub := filter_subset_of_triangle s s₁ s₂ μ δ hδ.le h_approx
  have h_card : ((s.filter (fun x => δ < |s₁ x - μ|)).card : ℝ) ≤
      ((s.filter (fun x => δ / 2 ≤ |s₁ x - s₂ x|)).card : ℝ) := by
    exact_mod_cast card_le_card h_sub
  have h_cheb := card_filter_le_of_sum_sq s (fun x => s₁ x - s₂ x) (δ / 2) (by linarith)
  exact h_card.trans h_cheb

lemma Ioc_sub_one_eq_Ico (n h : ℕ) (hn : 1 ≤ n) :
    Finset.Ioc (n - 1) (n - 1 + h) = Finset.Ico n (n + h) := by
  ext m
  simp only [Finset.mem_Ioc, Finset.mem_Ico]
  omega

lemma sum_Ioc_sub_one_eq_sum_range (f : ℕ → ℝ) (n h : ℕ) (hn : 1 ≤ n) :
    (∑ m ∈ Finset.Ioc (n - 1) (n - 1 + h), f m) = ∑ j ∈ Finset.range h, f (n + j) := by
  rw [Ioc_sub_one_eq_Ico n h hn]
  have h_bij : (Finset.range h).sum (fun j => f (n + j)) =
      (Finset.Ico n (n + h)).sum f := by
    rw [← Finset.sum_image (fun i _ j _ hij => Nat.add_left_cancel hij)]
    congr 1
    ext m
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · rintro ⟨hnm, hmh⟩; exact ⟨m - n, by omega, by omega⟩
  exact h_bij.symm

lemma shortMean_eq_sum_Ioc (f : ℕ → ℝ) (n h : ℕ) (hn : 1 ≤ n) :
    shortMean f h n = (∑ m ∈ Finset.Ioc (n - 1) (n - 1 + h), f m) / (h : ℝ) := by
  unfold shortMean
  rw [sum_Ioc_sub_one_eq_sum_range f n h hn]

/-- Bound on `intervalCount` by the interval variance integral and the tail length. -/
theorem intervalCount_le_variance_integral (β : ℝ) (X h₁ h₂ M : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hXM : X ≤ M) (hh₁ : 1 ≤ h₁) (h12 : h₁ ≤ h₂) (hM : M + h₂ ≤ 2 * X + 1)
    (h_approx : ∀ n ∈ Finset.Ioc X M,
      |shortMean (smoothIndicator ((X : ℝ) ^ β)) h₂ n - blockMean (smoothIndicator ((X : ℝ) ^ β)) X| ≤ δ / 4) :
    let a := fun m => if m ∈ Finset.Ioc X (2 * X) then fX β X m else 0
    (intervalCount {n | δ < |shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n -
        blockMean (smoothIndicator ((X : ℝ) ^ β)) X|} X (2 * X) : ℝ) ≤
      (∫ x in (X : ℝ)..(2 * (X : ℝ)),
        ‖windowSum a x (x + (h₁ : ℝ)) / (h₁ : ℂ) - windowSum a x (x + (h₂ : ℝ)) / (h₂ : ℂ)‖ ^ 2) /
          (δ / 2) ^ 2 + (2 * X - M : ℕ) := by
  intro a
  set A := {n | δ < |shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n -
    blockMean (smoothIndicator ((X : ℝ) ^ β)) X|}
  have hM2X : M ≤ 2 * X := by omega
  have h_split := intervalCount_le_split A X M hXM hM2X
  have h_split_real : (intervalCount A X (2 * X) : ℝ) ≤
      (((Finset.Ioc X M).filter (· ∈ A)).card : ℝ) + (2 * X - M : ℕ) := by
    exact_mod_cast h_split
  refine h_split_real.trans ?_
  have h_card_le := card_filter_delta_le (Finset.Ioc X M)
    (fun n => shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n)
    (fun n => shortMean (smoothIndicator ((X : ℝ) ^ β)) h₂ n)
    (blockMean (smoothIndicator ((X : ℝ) ^ β)) X) δ hδ h_approx
  have h_int_le := sum_sq_shortMean_sub_le_integral β X h₁ h₂ M hh₁ h12 hM
  have h_div_le : (∑ n ∈ Finset.Ioc X M,
      (shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n - shortMean (smoothIndicator ((X : ℝ) ^ β)) h₂ n) ^ 2) /
        (δ / 2) ^ 2 ≤
      (∫ x in (X : ℝ)..(2 * (X : ℝ)),
        ‖windowSum a x (x + (h₁ : ℝ)) / (h₁ : ℂ) - windowSum a x (x + (h₂ : ℝ)) / (h₂ : ℂ)‖ ^ 2) /
          (δ / 2) ^ 2 := by
    have h_den_pos : 0 < (δ / 2) ^ 2 := by positivity
    exact div_le_div_of_nonneg_right h_int_le (le_of_lt h_den_pos)
  have hA_def : ((Finset.Ioc X M).filter (· ∈ A)) =
      (Finset.Ioc X M).filter (fun x => δ < |shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ x -
        blockMean (smoothIndicator ((X : ℝ) ^ β)) X|) := rfl
  rw [hA_def]
  linarith [h_card_le, h_div_le]

/-! ### Reduction of MediumAverage to shortMean -/

lemma shortMean_sub_blockMean_le_of_medium (β : ℝ) (X h₂ : ℕ) (C_M : ℝ)
    (hCM : ∀ (β : ℝ) (X x y : ℕ), 3 / 4 ≤ β → β < 1 → 16 ≤ X → X ≤ x → x ≤ 2 * X →
      (X : ℝ) / (Real.log X) ^ (1 / 5 : ℝ) ≤ y → y ≤ X →
      |(∑ n ∈ Finset.Ioc x (x + y), smoothIndicator ((X : ℝ) ^ β) n) / (y : ℝ) -
        blockMean (smoothIndicator ((X : ℝ) ^ β)) X| ≤ C_M / (Real.log X) ^ (4 / 5 : ℝ))
    (hβ : 3 / 4 ≤ β) (hβ1 : β < 1) (hX16 : 16 ≤ X)
    (hy_lower : (X : ℝ) / (Real.log X) ^ (1 / 5 : ℝ) ≤ h₂) (hy_leX : h₂ ≤ X)
    {n : ℕ} (hnX : X < n) (hn2X : n ≤ 2 * X + 1) :
    |shortMean (smoothIndicator ((X : ℝ) ^ β)) h₂ n - blockMean (smoothIndicator ((X : ℝ) ^ β)) X| ≤
      C_M / (Real.log X) ^ (4 / 5 : ℝ) := by
  have hn_ge1 : 1 ≤ n := by omega
  rw [shortMean_eq_sum_Ioc (smoothIndicator ((X : ℝ) ^ β)) n h₂ hn_ge1]
  have hx_geX : X ≤ n - 1 := by omega
  have hx_le2X : n - 1 ≤ 2 * X := by omega
  exact hCM β X (n - 1) h₂ hβ hβ1 hX16 hx_geX hx_le2X hy_lower hy_leX

/-! ### Parseval & Lemma 14 Bounds on fX -/

theorem variance_fX_le : ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (X : ℕ) (h₁ h₂ T₀ : ℝ),
    1 ≤ X → 1 ≤ h₁ → h₁ ≤ h₂ → h₂ ≤ (X : ℝ) / 8 → 1 ≤ T₀ →
    let a := fun n => if n ∈ Finset.Ioc X (2 * X) then fX β X n else 0
    (1 / (X : ℝ)) * ∫ x in (X : ℝ)..(2 * X), ‖windowSum a x (x + h₁) / h₁ -
        windowSum a x (x + h₂) / h₂‖ ^ 2 ≤
      C * (T₀ ^ 4 * (h₂ / (X : ℝ)) ^ 2 +
        ∫ t in {t : ℝ | T₀ ≤ |t|}, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
          min 1 (((X : ℝ) / (h₁ * t)) ^ 2)) := by
  obtain ⟨C, hC_pos, hC⟩ := variance_windowSum_le
  refine ⟨C, hC_pos, ?_⟩
  intro β X h₁ h₂ T₀ hX hh₁ h12 h2X hT₀ a
  let N := Finset.Ioc X (2 * X)
  have hN_pos : ∀ n ∈ N, 0 < n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    omega
  have hsupp : ∀ n, n ∉ N → a n = 0 := by
    intro n hn
    dsimp [a, N]
    split_ifs with h_mem
    · contradiction
    · rfl
  have h_var := hC a N X h₁ h₂ T₀ hN_pos hX hh₁ h12 h2X hT₀ hsupp
  have h_poly : dirichletPoly a N = Fu β X := dirichletPoly_fX_eq_Fu_fn β X
  rw [h_poly] at h_var
  have h_a_eq : (∑ n ∈ N, ‖a n‖ / (n : ℝ)) = ∑ n ∈ N, ‖fX β X n‖ / (n : ℝ) := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp [a, N]
    split_ifs with h_mem
    · rfl
    · contradiction
  have h_sum_le : (∑ n ∈ N, ‖a n‖ / (n : ℝ)) ≤ 1 := by
    rw [h_a_eq]
    exact M_bound_le_one β X hX
  have h_sum_nonneg : 0 ≤ ∑ n ∈ N, ‖a n‖ / (n : ℝ) := by
    apply Finset.sum_nonneg
    intro n _
    positivity
  have h_sum_sq : (∑ n ∈ N, ‖a n‖ / (n : ℝ)) ^ 2 ≤ 1 := by
    nlinarith
  have h_term1 : T₀ ^ 4 * (h₂ / (X : ℝ)) ^ 2 * (∑ n ∈ N, ‖a n‖ / (n : ℝ)) ^ 2 ≤
      T₀ ^ 4 * (h₂ / (X : ℝ)) ^ 2 := by
    have h_pos : 0 ≤ T₀ ^ 4 * (h₂ / (X : ℝ)) ^ 2 := by positivity
    nlinarith
  have h_combined : T₀ ^ 4 * (h₂ / (X : ℝ)) ^ 2 * (∑ n ∈ N, ‖a n‖ / (n : ℝ)) ^ 2 +
      ∫ t in {t : ℝ | T₀ ≤ |t|}, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
        min 1 (((X : ℝ) / (h₁ * t)) ^ 2) ≤
      T₀ ^ 4 * (h₂ / (X : ℝ)) ^ 2 +
      ∫ t in {t : ℝ | T₀ ≤ |t|}, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
        min 1 (((X : ℝ) / (h₁ * t)) ^ 2) := by
    linarith
  exact h_var.trans (mul_le_mul_of_nonneg_left h_combined hC_pos.le)

theorem integral_variance_fX_le : ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (X : ℕ) (h₁ h₂ T₀ : ℝ),
    1 ≤ X → 1 ≤ h₁ → h₁ ≤ h₂ → h₂ ≤ (X : ℝ) / 8 → 1 ≤ T₀ →
    let a := fun n => if n ∈ Finset.Ioc X (2 * X) then fX β X n else 0
    ∫ x in (X : ℝ)..(2 * X), ‖windowSum a x (x + h₁) / h₁ -
        windowSum a x (x + h₂) / h₂‖ ^ 2 ≤
      C * (X : ℝ) * (T₀ ^ 4 * (h₂ / (X : ℝ)) ^ 2 +
        ∫ t in {t : ℝ | T₀ ≤ |t|}, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
          min 1 (((X : ℝ) / (h₁ * t)) ^ 2)) := by
  obtain ⟨C, hC_pos, hC⟩ := variance_fX_le
  refine ⟨C, hC_pos, ?_⟩
  intro β X h₁ h₂ T₀ hX hh₁ h12 h2X hT₀ a
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
  have h_bound := hC β X h₁ h₂ T₀ hX hh₁ h12 h2X hT₀
  dsimp [a] at h_bound ⊢
  have h_mul := mul_le_mul_of_nonneg_left h_bound hX_pos.le
  have h_cancel : (X : ℝ) * ((1 / (X : ℝ)) * ∫ x in (X : ℝ)..(2 * X),
      ‖windowSum a x (x + h₁) / h₁ - windowSum a x (x + h₂) / h₂‖ ^ 2) =
      ∫ x in (X : ℝ)..(2 * X),
      ‖windowSum a x (x + h₁) / h₁ - windowSum a x (x + h₂) / h₂‖ ^ 2 := by
    rw [← mul_assoc, mul_one_div_cancel hX_pos.ne', one_mul]
  rw [h_cancel] at h_mul
  have h_assoc : (X : ℝ) * (C * (T₀ ^ 4 * (h₂ / (X : ℝ)) ^ 2 +
      ∫ t in {t : ℝ | T₀ ≤ |t|}, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
        min 1 (((X : ℝ) / (h₁ * t)) ^ 2))) =
      C * (X : ℝ) * (T₀ ^ 4 * (h₂ / (X : ℝ)) ^ 2 +
      ∫ t in {t : ℝ | T₀ ≤ |t|}, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
        min 1 (((X : ℝ) / (h₁ * t)) ^ 2)) := by ring
  rwa [h_assoc] at h_mul

/-- Full reduction theorem from Chebyshev exception count to the weighted frequency integral `W`
and tail boundary `2X - M`. -/
theorem intervalCount_le_variance_bound (β : ℝ) (X h₁ h₂ M : ℕ) (δ T₀ : ℝ) (hδ : 0 < δ)
    (h_int_bound : (intervalCount {n | δ < |shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n -
        blockMean (smoothIndicator ((X : ℝ) ^ β)) X|} X (2 * X) : ℝ) ≤
      (∫ x in (X : ℝ)..(2 * (X : ℝ)),
        ‖windowSum (fun n => if n ∈ Finset.Ioc X (2 * X) then fX β X n else 0) x (x + (h₁ : ℝ)) / (h₁ : ℂ) -
          windowSum (fun n => if n ∈ Finset.Ioc X (2 * X) then fX β X n else 0) x (x + (h₂ : ℝ)) / (h₂ : ℂ)‖ ^ 2) /
            (δ / 2) ^ 2 + (2 * X - M : ℕ))
    (C : ℝ)
    (hC : ∫ x in (X : ℝ)..(2 * (X : ℝ)),
      ‖windowSum (fun n => if n ∈ Finset.Ioc X (2 * X) then fX β X n else 0) x (x + (h₁ : ℝ)) / (h₁ : ℂ) -
        windowSum (fun n => if n ∈ Finset.Ioc X (2 * X) then fX β X n else 0) x (x + (h₂ : ℝ)) / (h₂ : ℂ)‖ ^ 2 ≤
      C * (X : ℝ) * (T₀ ^ 4 * ((h₂ : ℝ) / (X : ℝ)) ^ 2 +
        ∫ t in {t : ℝ | T₀ ≤ |t|}, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
          min 1 (((X : ℝ) / ((h₁ : ℝ) * t)) ^ 2))) :
    (intervalCount {n | δ < |shortMean (smoothIndicator ((X : ℝ) ^ β)) h₁ n -
        blockMean (smoothIndicator ((X : ℝ) ^ β)) X|} X (2 * X) : ℝ) ≤
      (C * (X : ℝ) * (T₀ ^ 4 * ((h₂ : ℝ) / (X : ℝ)) ^ 2 +
        ∫ t in {t : ℝ | T₀ ≤ |t|}, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
          min 1 (((X : ℝ) / ((h₁ : ℝ) * t)) ^ 2))) / (δ / 2) ^ 2 + (2 * X - M : ℕ) := by
  have h_den_pos : 0 < (δ / 2) ^ 2 := by positivity
  have h_div_le : (∫ x in (X : ℝ)..(2 * (X : ℝ)),
      ‖windowSum (fun n => if n ∈ Finset.Ioc X (2 * X) then fX β X n else 0) x (x + (h₁ : ℝ)) / (h₁ : ℂ) -
        windowSum (fun n => if n ∈ Finset.Ioc X (2 * X) then fX β X n else 0) x (x + (h₂ : ℝ)) / (h₂ : ℂ)‖ ^ 2) /
          (δ / 2) ^ 2 ≤
      (C * (X : ℝ) * (T₀ ^ 4 * ((h₂ : ℝ) / (X : ℝ)) ^ 2 +
        ∫ t in {t : ℝ | T₀ ≤ |t|}, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
          min 1 (((X : ℝ) / ((h₁ : ℝ) * t)) ^ 2))) / (δ / 2) ^ 2 :=
    div_le_div_of_nonneg_right hC (le_of_lt h_den_pos)
  linarith [h_int_bound, h_div_le]

end Erdos1201.MR
