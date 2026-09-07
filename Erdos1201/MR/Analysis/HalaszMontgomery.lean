/-
Copyright (c) 2026 Przemek Chojecki, ChatGPT 5.5. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Przemek Chojecki, ChatGPT 5.5
-/
import Mathlib
import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.MR.Analysis.WellSpaced
import Erdos1201.MR.Analysis.PhaseSumDyadic
import Erdos1201.Vendor.NumberTheory.BoundedPrimeGaps.BombieriVinogradov.Analytic.AdditiveLargeSieve.FiniteDuality

/-!
# Halász-Montgomery Inequality

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

open Complex Finset Real

namespace Erdos1201.MR

-- Step 1
lemma a_mul_cpow_eq_div_mul_exp (a : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    a n * (n : ℂ) ^ (-(1 + t * Complex.I)) = (a n / (n : ℂ)) * Complex.exp (-Complex.I * t * Real.log (n : ℝ)) := by
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  rw [Complex.cpow_def_of_ne_zero hn_ne]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    have h1 : (n : ℂ) = ((n : ℝ) : ℂ) := by push_cast; rfl
    rw [h1, Complex.ofReal_log (by positivity)]
  rw [hlog]
  have h_exp : (Real.log (n : ℝ) : ℂ) * -(1 + t * Complex.I) = -(Real.log (n : ℝ) : ℂ) + -Complex.I * t * Real.log (n : ℝ) := by ring
  rw [h_exp, Complex.exp_add]
  have h_exp_neg : Complex.exp (-(Real.log (n : ℝ) : ℂ)) = 1 / (n : ℂ) := by
    have : (-(Real.log (n : ℝ) : ℂ)) = ((-Real.log (n : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, ← Complex.ofReal_exp]
    have h2 : Real.exp (-Real.log (n : ℝ)) = 1 / (n : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by positivity), one_div]
    rw [h2]
    push_cast
    rfl
  rw [h_exp_neg]
  ring

-- Step 2
lemma step2_fiber_left (S : Finset ℝ) (hS : WellSpaced S) (r : ℝ) (k : ℕ) :
    ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k ∧ s < r)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro s1 hs1 s2 hs2
  rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hs1 hs2
  rcases hs1 with ⟨⟨hs1_S, hne1⟩, hs1_k, hs1_lt⟩
  rcases hs2 with ⟨⟨hs2_S, hne2⟩, hs2_k, hs2_lt⟩
  by_contra hne
  have h_well := hS s1 hs1_S s2 hs2_S hne
  have hk1 : (k : ℝ) ≤ |r - s1| ∧ |r - s1| < (k + 1 : ℝ) := (Nat.floor_eq_iff (abs_nonneg _)).mp hs1_k
  have hk2 : (k : ℝ) ≤ |r - s2| ∧ |r - s2| < (k + 1 : ℝ) := (Nat.floor_eq_iff (abs_nonneg _)).mp hs2_k
  have h1_eq : |r - s1| = r - s1 := abs_of_pos (sub_pos.mpr hs1_lt)
  have h2_eq : |r - s2| = r - s2 := abs_of_pos (sub_pos.mpr hs2_lt)
  rw [h1_eq] at hk1
  rw [h2_eq] at hk2
  have h_dist : |s1 - s2| < 1 := by
    rw [abs_lt]
    constructor
    · linarith [hk1.2, hk2.1]
    · linarith [hk1.1, hk2.2]
  linarith

lemma step2_fiber_right (S : Finset ℝ) (hS : WellSpaced S) (r : ℝ) (k : ℕ) :
    ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k ∧ r < s)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro s1 hs1 s2 hs2
  rw [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_singleton] at hs1 hs2
  rcases hs1 with ⟨⟨hs1_S, hne1⟩, hs1_k, hs1_lt⟩
  rcases hs2 with ⟨⟨hs2_S, hne2⟩, hs2_k, hs2_lt⟩
  by_contra hne
  have h_well := hS s1 hs1_S s2 hs2_S hne
  have hk1 : (k : ℝ) ≤ |r - s1| ∧ |r - s1| < (k + 1 : ℝ) := (Nat.floor_eq_iff (abs_nonneg _)).mp hs1_k
  have hk2 : (k : ℝ) ≤ |r - s2| ∧ |r - s2| < (k + 1 : ℝ) := (Nat.floor_eq_iff (abs_nonneg _)).mp hs2_k
  have h1_eq : |r - s1| = s1 - r := by rw [abs_of_neg (sub_neg.mpr hs1_lt)]; ring
  have h2_eq : |r - s2| = s2 - r := by rw [abs_of_neg (sub_neg.mpr hs2_lt)]; ring
  rw [h1_eq] at hk1
  rw [h2_eq] at hk2
  have h_dist : |s1 - s2| < 1 := by
    rw [abs_lt]
    constructor
    · linarith [hk1.2, hk2.1]
    · linarith [hk1.1, hk2.2]
  linarith

lemma step2_fiber (S : Finset ℝ) (hS : WellSpaced S) (r : ℝ) (k : ℕ) :
    ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k)).card ≤ 2 := by
  have h_split : ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k)) =
      ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k ∧ s < r)) ∪
      ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k ∧ r < s)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hx_S, hx_ne⟩, hx_k⟩
      rcases lt_trichotomy x r with hlt | heq | hgt
      · left; exact ⟨⟨hx_S, hx_ne⟩, hx_k, hlt⟩
      · exfalso; exact hx_ne heq
      · right; exact ⟨⟨hx_S, hx_ne⟩, hx_k, hgt⟩
    · rintro (⟨⟨hx_S, hx_ne⟩, hx_k, hlt⟩ | ⟨⟨hx_S, hx_ne⟩, hx_k, hgt⟩)
      · exact ⟨⟨hx_S, hx_ne⟩, hx_k⟩
      · exact ⟨⟨hx_S, hx_ne⟩, hx_k⟩
  rw [h_split]
  have h_disj : Disjoint ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k ∧ s < r))
                         ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k ∧ r < s)) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb heq
    rw [Finset.mem_filter] at ha hb
    linarith [ha.2.2, hb.2.2]
  rw [Finset.card_union_of_disjoint h_disj]
  have h1 := step2_fiber_left S hS r k
  have h2 := step2_fiber_right S hS r k
  linarith

lemma sum_harmonic_le_one_add_log (n : ℕ) :
    ∑ j ∈ Finset.Icc (1 : ℕ) n, (1 : ℝ) / j ≤ 1 + Real.log n := by
  by_cases hn : n = 0
  · subst hn
    have : Finset.Icc (1 : ℕ) 0 = ∅ := rfl
    rw [this, Finset.sum_empty]
    simp
  have h_eq : (∑ j ∈ Finset.Icc (1 : ℕ) n, (1 : ℝ) / j) = (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    refine Finset.sum_congr rfl fun j _ => by simp [div_eq_inv_mul]
  rw [h_eq]
  exact _root_.harmonic_le_one_add_log n

lemma sum_inv_abs_sub_le (S : Finset ℝ) (hS : WellSpaced S) (T : ℝ) (hT : 2 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T) (r : ℝ) (hr : r ∈ S) :
    ∑ s ∈ S \ {r}, (1 : ℝ) / |r - s| ≤ 2 * (1 + Real.log (2 * T + 1)) := by
  set K := ⌊2 * T⌋₊ with hK_def
  have hK_ge : 1 ≤ K := by
    rw [hK_def]
    by_contra h
    have hk0 : ⌊2 * T⌋₊ = 0 := by omega
    have hlt := ((Nat.floor_eq_iff (by linarith)).mp hk0).2
    norm_num at hlt
    linarith
  have h_maps : ∀ s ∈ S \ {r}, ⌊|r - s|⌋₊ ∈ Finset.Icc 1 K := by
    intro s hs
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hs
    rw [Finset.mem_Icc]
    constructor
    · have hne : r ≠ s := ne_comm.mp hs.2
      have hdist := hS r hr s hs.1 hne
      by_contra h
      have hk0 : ⌊|r - s|⌋₊ = 0 := by omega
      have hlt := ((Nat.floor_eq_iff (abs_nonneg _)).mp hk0).2
      norm_num at hlt
      linarith
    · rw [hK_def]
      have : |r - s| ≤ 2 * T := by
        calc |r - s| ≤ |r| + |s| := abs_sub r s
          _ ≤ T + T := add_le_add (hST r hr) (hST s hs.1)
          _ = 2 * T := by ring
      exact Nat.floor_le_floor this
  have h_fib := Finset.sum_fiberwise_of_maps_to (g := fun s => ⌊|r - s|⌋₊) (t := Finset.Icc 1 K)
    h_maps (fun s => (1 : ℝ) / |r - s|)
  rw [← h_fib]
  have h_step : ∀ k ∈ Finset.Icc 1 K,
      ∑ s ∈ (S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k), (1 : ℝ) / |r - s| ≤ 2 / (k : ℝ) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk.1
    have h_term_le : ∀ s ∈ (S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k), (1 : ℝ) / |r - s| ≤ 1 / (k : ℝ) := by
      intro s hs
      rw [Finset.mem_filter] at hs
      have hk_le : (k : ℝ) ≤ |r - s| := (Nat.floor_eq_iff (abs_nonneg _)).mp hs.2 |>.1
      exact div_le_div_of_nonneg_left zero_le_one hk_pos hk_le
    have h_sum_le := Finset.sum_le_card_nsmul ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k))
      (fun s => (1 : ℝ) / |r - s|) (1 / (k : ℝ)) h_term_le
    have h_card := step2_fiber S hS r k
    calc ∑ s ∈ (S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k), (1 : ℝ) / |r - s|
        ≤ ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k)).card • (1 / (k : ℝ)) := h_sum_le
      _ = (((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k)).card : ℝ) * (1 / (k : ℝ)) := nsmul_eq_mul _ _
      _ ≤ 2 * (1 / (k : ℝ)) := mul_le_mul_of_nonneg_right (by exact_mod_cast h_card) (by positivity)
      _ = 2 / (k : ℝ) := mul_one_div 2 (k : ℝ)
  have h_sum_all := Finset.sum_le_sum h_step
  refine h_sum_all.trans ?_
  have h_pull : ∑ k ∈ Finset.Icc 1 K, 2 / (k : ℝ) = 2 * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [h_pull]
  have h_harm := sum_harmonic_le_one_add_log K
  have h_log_le : Real.log (K : ℝ) ≤ Real.log (2 * T + 1) := by
    apply Real.log_le_log (Nat.cast_pos.mpr hK_ge)
    have : (K : ℝ) ≤ 2 * T := Nat.floor_le (by linarith)
    linarith
  linarith

-- Step 3
lemma one_le_two_mul_log {T : ℝ} (hT : 2 ≤ T) : 1 ≤ 2 * Real.log T := by
  have h2 : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  linarith

lemma log_two_mul_add_one_le {T : ℝ} (hT : 2 ≤ T) : Real.log (2 * T + 1) ≤ 3 * Real.log T := by
  have hT0 : 0 < T := by linarith
  have h2T1 : 2 * T + 1 ≤ 4 * T := by linarith
  have h4T0 : 0 < 2 * T + 1 := by linarith
  have h1 : Real.log (2 * T + 1) ≤ Real.log (4 * T) := Real.log_le_log h4T0 h2T1
  have h4T_eq : 4 * T = 2 * 2 * T := by ring
  rw [h4T_eq] at h1
  have hlog4T : Real.log (2 * 2 * T) = Real.log 2 + Real.log 2 + Real.log T := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog4T] at h1
  have hlog2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  linarith

lemma log_eight_mul_le {T : ℝ} (hT : 2 ≤ T) : Real.log (8 * T) ≤ 4 * Real.log T := by
  have h8T_eq : 8 * T = 2 * 2 * 2 * T := by ring
  have hlog8T : Real.log (8 * T) = Real.log 2 + Real.log 2 + Real.log 2 + Real.log T := by
    rw [h8T_eq, Real.log_mul (by norm_num) (by linarith),
        Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num)]
  rw [hlog8T]
  have hlog2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
  linarith

lemma sqrt_two_mul_le {T : ℝ} (_hT : 0 ≤ T) : Real.sqrt (2 * T) ≤ 2 * Real.sqrt T := by
  rw [Real.sqrt_mul (by norm_num)]
  have h2 : Real.sqrt 2 ≤ 2 := by
    have : (2 : ℝ) = Real.sqrt 4 := by norm_num
    rw [this]
    exact Real.sqrt_le_sqrt (by norm_num)
  exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg T)

lemma norm_sum_exp_neg_eq_norm_sum_exp_pos (N : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))‖ =
    ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * (-t : ℂ) * (Real.log (n : ℝ) : ℂ))‖ := by
  have h_conj : (starRingEnd ℂ) (∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) =
      ∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * (-t : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_I, neg_neg, Complex.conj_ofReal]
    push_cast
    ring
  rw [← Complex.norm_conj, h_conj]

lemma norm_sum_exp_abs_le (C₀ : ℝ)
    (hC₀ : ∀ (N : ℕ) (τ : ℝ), 1 ≤ N → 1 ≤ τ →
      ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-((τ * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
        C₀ * ((N : ℝ) / τ + Real.sqrt τ * Real.log (4 * τ)))
    (N : ℕ) (t : ℝ) (hN : 1 ≤ N) (ht : 1 ≤ |t|) :
    ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))‖ ≤
      C₀ * ((N : ℝ) / |t| + Real.sqrt |t| * Real.log (4 * |t|)) := by
  rcases le_total 0 t with ht_pos | ht_neg
  · rw [abs_of_nonneg ht_pos]
    rw [abs_of_nonneg ht_pos] at ht
    have h_eq : (∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))) =
        ∑ n ∈ Finset.Ioc 0 N, Complex.exp (-((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      push_cast
      ring
    rw [h_eq]
    exact hC₀ N t hN ht
  · rw [abs_of_nonpos ht_neg]
    rw [abs_of_nonpos ht_neg] at ht
    rw [norm_sum_exp_neg_eq_norm_sum_exp_pos]
    have h_eq : (∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * (-t : ℂ) * (Real.log (n : ℝ) : ℂ))) =
        ∑ n ∈ Finset.Ioc 0 N, Complex.exp (-(((-t) * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro n _
      congr 1
      push_cast
      ring
    rw [h_eq]
    exact hC₀ N (-t) hN ht

lemma norm_sum_exp_diag (N : ℕ) :
    ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * (0 : ℂ) * (Real.log (n : ℝ) : ℂ))‖ = (N : ℝ) := by
  have h_eq : (∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * (0 : ℂ) * (Real.log (n : ℝ) : ℂ))) = (N : ℂ) := by
    have : (fun n : ℕ => Complex.exp (-Complex.I * (0 : ℂ) * (Real.log (n : ℝ) : ℂ))) = fun _ => 1 := by
      ext n
      have : -Complex.I * (0 : ℂ) * (Real.log (n : ℝ) : ℂ) = 0 := by ring
      rw [this, Complex.exp_zero]
    rw [this, Finset.sum_const, Nat.card_Ioc, tsub_zero, nsmul_one]
  rw [h_eq, Complex.norm_natCast]

lemma step3_row_sum_bound (C₀ : ℝ) (hC₀_nonneg : 0 ≤ C₀)
    (hC₀ : ∀ (N : ℕ) (τ : ℝ), 1 ≤ N → 1 ≤ τ →
      ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-((τ * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
        C₀ * ((N : ℝ) / τ + Real.sqrt τ * Real.log (4 * τ)))
    (N : ℕ) (T : ℝ) (S : Finset ℝ) (hN : 1 ≤ N) (hT : 2 ≤ T) (hS : WellSpaced S)
    (hST : ∀ t ∈ S, |t| ≤ T) (r : ℝ) (hr : r ∈ S) :
    (∑ s ∈ S, ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * ((s - r : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))‖) ≤
      (2 + 10 * C₀) * ((N : ℝ) + (S.card : ℝ) * Real.sqrt T) * Real.log T := by
  have hT_pos : 0 < T := by linarith
  have hlogT_pos : 0 < Real.log T := by
    have : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
    linarith
  have h1_le_2logT := one_le_two_mul_log hT
  have h_split : S = {r} ∪ (S \ {r}) := (Finset.union_sdiff_of_subset (Finset.singleton_subset_iff.mpr hr)).symm
  have h_disj : Disjoint ({r} : Finset ℝ) (S \ {r}) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    rw [Finset.mem_singleton] at ha
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hb
    rintro rfl
    exact hb.2 ha
  nth_rw 1 [h_split]
  rw [Finset.sum_union h_disj, Finset.sum_singleton]
  have h_diag : ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * ((r - r : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))‖ = (N : ℝ) := by
    have : ((r - r : ℝ) : ℂ) = 0 := by push_cast; ring
    rw [this, norm_sum_exp_diag]
  rw [h_diag]
  have h_offdiag_term : ∀ s ∈ S \ {r},
      ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * ((s - r : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))‖ ≤
        C₀ * ((N : ℝ) / |r - s| + 8 * Real.sqrt T * Real.log T) := by
    intro s hs
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hs
    have hne : s ≠ r := hs.2
    have hdist : 1 ≤ |s - r| := hS s hs.1 r hr hne
    have h_bound := norm_sum_exp_abs_le C₀ hC₀ N (s - r) hN hdist
    have h_abs_comm : |s - r| = |r - s| := abs_sub_comm s r
    rw [h_abs_comm] at h_bound
    refine h_bound.trans ?_
    have h_le_2T : |r - s| ≤ 2 * T := by
      calc |r - s| ≤ |r| + |s| := abs_sub r s
        _ ≤ T + T := add_le_add (hST r hr) (hST s hs.1)
        _ = 2 * T := by ring
    have h_sqrt_le : Real.sqrt |r - s| ≤ 2 * Real.sqrt T := by
      apply (Real.sqrt_le_sqrt h_le_2T).trans
      exact sqrt_two_mul_le (by linarith)
    have h_log_le : Real.log (4 * |r - s|) ≤ 4 * Real.log T := by
      have h4_pos : 0 < 4 * |r - s| := by
        rw [← h_abs_comm]
        have : 0 < |s - r| := by linarith
        positivity
      have h4_le : 4 * |r - s| ≤ 8 * T := by linarith
      apply (Real.log_le_log h4_pos h4_le).trans
      exact log_eight_mul_le hT
    have h_prod_le : Real.sqrt |r - s| * Real.log (4 * |r - s|) ≤ (2 * Real.sqrt T) * (4 * Real.log T) := by
      apply mul_le_mul h_sqrt_le h_log_le
      · have : 1 ≤ 4 * |r - s| := by
          rw [← h_abs_comm]
          linarith
        exact Real.log_nonneg this
      · positivity
    have h_prod_eq : (2 * Real.sqrt T) * (4 * Real.log T) = 8 * Real.sqrt T * Real.log T := by ring
    rw [h_prod_eq] at h_prod_le
    gcongr
  have h_sum_offdiag : (∑ s ∈ S \ {r}, ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * ((s - r : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))‖) ≤
      ∑ s ∈ S \ {r}, C₀ * ((N : ℝ) / |r - s| + 8 * Real.sqrt T * Real.log T) :=
    Finset.sum_le_sum h_offdiag_term
  have h_total : (N : ℝ) + (∑ s ∈ S \ {r}, ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * ((s - r : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))‖) ≤
      (N : ℝ) + ∑ s ∈ S \ {r}, C₀ * ((N : ℝ) / |r - s| + 8 * Real.sqrt T * Real.log T) := by linarith
  refine h_total.trans ?_
  have h_expand_sum : (∑ s ∈ S \ {r}, C₀ * ((N : ℝ) / |r - s| + 8 * Real.sqrt T * Real.log T)) =
      C₀ * (N : ℝ) * (∑ s ∈ S \ {r}, (1 : ℝ) / |r - s|) +
      (C₀ * (8 * Real.sqrt T * Real.log T)) * ((S \ {r}).card : ℝ) := by
    have h_term (s : ℝ) : C₀ * ((N : ℝ) / |r - s| + 8 * Real.sqrt T * Real.log T) =
        (C₀ * (N : ℝ) * ((1 : ℝ) / |r - s|)) + (C₀ * (8 * Real.sqrt T * Real.log T)) := by ring
    simp_rw [h_term, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [h_expand_sum]
  have h_harm := sum_inv_abs_sub_le S hS T hT hST r hr
  have h_harm_log : 2 * (1 + Real.log (2 * T + 1)) ≤ 10 * Real.log T := by
    have h_log2T1 := log_two_mul_add_one_le hT
    linarith
  have h_first_part : C₀ * (N : ℝ) * (∑ s ∈ S \ {r}, (1 : ℝ) / |r - s|) ≤ 10 * C₀ * (N : ℝ) * Real.log T := by
    have h_le : (∑ s ∈ S \ {r}, (1 : ℝ) / |r - s|) ≤ 10 * Real.log T := h_harm.trans h_harm_log
    have h_nonneg : 0 ≤ C₀ * (N : ℝ) := by positivity
    nlinarith
  have h_card_le : ((S \ {r}).card : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have h_second_part : (C₀ * (8 * Real.sqrt T * Real.log T)) * ((S \ {r}).card : ℝ) ≤
      8 * C₀ * (S.card : ℝ) * Real.sqrt T * Real.log T := by
    have h_coeff_nonneg : 0 ≤ C₀ * (8 * Real.sqrt T * Real.log T) := by positivity
    have := mul_le_mul_of_nonneg_left h_card_le h_coeff_nonneg
    nlinarith
  have h_diag_le : (N : ℝ) ≤ 2 * (N : ℝ) * Real.log T := by
    have : (N : ℝ) * 1 ≤ (N : ℝ) * (2 * Real.log T) := mul_le_mul_of_nonneg_left h1_le_2logT (by positivity)
    linarith
  have h_second_le : 8 * C₀ * (S.card : ℝ) * Real.sqrt T * Real.log T ≤
      (2 + 10 * C₀) * (S.card : ℝ) * Real.sqrt T * Real.log T := by
    have h_le : 8 * C₀ ≤ 2 + 10 * C₀ := by linarith
    have h_prod_nonneg : 0 ≤ (S.card : ℝ) * Real.sqrt T * Real.log T :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg T)) (le_of_lt hlogT_pos)
    have := mul_le_mul_of_nonneg_right h_le h_prod_nonneg
    linarith
  have h_sum_combine : (N : ℝ) + (10 * C₀ * (N : ℝ) * Real.log T + 8 * C₀ * (S.card : ℝ) * Real.sqrt T * Real.log T) ≤
      (2 + 10 * C₀) * ((N : ℝ) + (S.card : ℝ) * Real.sqrt T) * Real.log T := by
    calc (N : ℝ) + (10 * C₀ * (N : ℝ) * Real.log T + 8 * C₀ * (S.card : ℝ) * Real.sqrt T * Real.log T)
        ≤ 2 * (N : ℝ) * Real.log T + 10 * C₀ * (N : ℝ) * Real.log T +
          (2 + 10 * C₀) * (S.card : ℝ) * Real.sqrt T * Real.log T := by linarith [h_diag_le, h_second_le]
      _ = (2 + 10 * C₀) * ((N : ℝ) + (S.card : ℝ) * Real.sqrt T) * Real.log T := by ring
  calc (N : ℝ) + (C₀ * (N : ℝ) * (∑ s ∈ S \ {r}, (1 : ℝ) / |r - s|) + (C₀ * (8 * Real.sqrt T * Real.log T)) * ((S \ {r}).card : ℝ))
      ≤ (N : ℝ) + (10 * C₀ * (N : ℝ) * Real.log T + 8 * C₀ * (S.card : ℝ) * Real.sqrt T * Real.log T) := by
        linarith [h_first_part, h_second_part]
    _ ≤ (2 + 10 * C₀) * ((N : ℝ) + (S.card : ℝ) * Real.sqrt T) * Real.log T := h_sum_combine

-- Step 4
lemma norm_sq_sum_le_schur {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C : ι → κ → ℂ) (K : ι → ι → ℝ)
    (hK : ∀ r s, ‖∑ n, star (C r n) * C s n‖ ≤ K r s)
    (hK_symm : ∀ r s, K r s = K s r)
    (A : ℝ) (hA : ∀ r, ∑ s, K r s ≤ A)
    (v : ι → ℂ) :
    (∑ n, ‖∑ r, C r n * v r‖ ^ 2) ≤ A * ∑ r, ‖v r‖ ^ 2 := by
  set L : ℝ := ∑ n, ‖∑ r, C r n * v r‖ ^ 2 with hL_def
  have hL_nonneg : 0 ≤ L := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hL_cast : (L : ℂ) = ∑ n, star (∑ r, C r n * v r) * (∑ s, C s n * v s) := by
    rw [hL_def, ofReal_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [← normSq_eq_norm_sq, normSq_eq_conj_mul_self]
    rfl
  have hL_expand : (L : ℂ) = ∑ r, ∑ s, star (v r) * v s * (∑ n, star (C r n) * C s n) := by
    rw [hL_cast]
    have h1 (n : κ) : star (∑ r, C r n * v r) = ∑ r, star (v r) * star (C r n) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro r _
      exact star_mul (C r n) (v r)
    simp_rw [h1, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hL_norm : L = ‖(L : ℂ)‖ := (Complex.norm_of_nonneg hL_nonneg).symm
  have h_norm_le : ‖(L : ℂ)‖ ≤ ∑ r, ∑ s, ‖star (v r) * v s * (∑ n, star (C r n) * C s n)‖ := by
    rw [hL_expand]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => norm_sum_le _ _)
  have h_term_le : ∀ r s, ‖star (v r) * v s * (∑ n, star (C r n) * C s n)‖ ≤
      ((‖v r‖ ^ 2 + ‖v s‖ ^ 2) / 2) * K r s := by
    intro r s
    rw [norm_mul, norm_mul]
    have h_conj_v : ‖star (v r)‖ = ‖v r‖ := by
      rw [Complex.star_def, Complex.norm_conj]
    rw [h_conj_v]
    have h_am_gm : ‖v r‖ * ‖v s‖ ≤ (‖v r‖ ^ 2 + ‖v s‖ ^ 2) / 2 := by
      have : 0 ≤ (‖v r‖ - ‖v s‖) ^ 2 := sq_nonneg _
      linarith
    have h_K_nonneg : 0 ≤ K r s := (norm_nonneg _).trans (hK r s)
    exact mul_le_mul h_am_gm (hK r s) (norm_nonneg _) (by positivity)
  have h_bound : ‖(L : ℂ)‖ ≤ ∑ r, ∑ s, ((‖v r‖ ^ 2 + ‖v s‖ ^ 2) / 2) * K r s := by
    apply h_norm_le.trans
    apply Finset.sum_le_sum
    intro r _
    apply Finset.sum_le_sum
    intro s _
    exact h_term_le r s
  have h_split : (∑ r, ∑ s, ((‖v r‖ ^ 2 + ‖v s‖ ^ 2) / 2) * K r s) =
      (1 / 2 : ℝ) * (∑ r, ‖v r‖ ^ 2 * ∑ s, K r s) + (1 / 2 : ℝ) * (∑ s, ‖v s‖ ^ 2 * ∑ r, K r s) := by
    have h_term (r s : ι) : ((‖v r‖ ^ 2 + ‖v s‖ ^ 2) / 2) * K r s =
        (1 / 2 * ‖v r‖ ^ 2) * K r s + (1 / 2 * ‖v s‖ ^ 2) * K r s := by ring
    simp_rw [h_term, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : (∑ r, (1 / 2 * ‖v r‖ ^ 2) * ∑ s, K r s) = (1 / 2 : ℝ) * ∑ r, ‖v r‖ ^ 2 * ∑ s, K r s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    have h2 : (∑ r, ∑ s, (1 / 2 * ‖v s‖ ^ 2) * K r s) = (1 / 2 : ℝ) * ∑ s, ‖v s‖ ^ 2 * ∑ r, K r s := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [h1, h2]
  have h_symm_sum : (∑ s, ‖v s‖ ^ 2 * ∑ r, K r s) = ∑ r, ‖v r‖ ^ 2 * ∑ s, K r s := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact hK_symm j i
  rw [h_symm_sum] at h_split
  have h_comb : (∑ r, ∑ s, ((‖v r‖ ^ 2 + ‖v s‖ ^ 2) / 2) * K r s) = ∑ r, ‖v r‖ ^ 2 * ∑ s, K r s := by
    calc (∑ r, ∑ s, ((‖v r‖ ^ 2 + ‖v s‖ ^ 2) / 2) * K r s)
        = (1 / 2 : ℝ) * (∑ r, ‖v r‖ ^ 2 * ∑ s, K r s) + (1 / 2 : ℝ) * (∑ r, ‖v r‖ ^ 2 * ∑ s, K r s) := h_split
      _ = ∑ r, ‖v r‖ ^ 2 * ∑ s, K r s := by ring
  rw [hL_norm]
  apply h_bound.trans
  rw [h_comb]
  have h_A_bound : (∑ r, ‖v r‖ ^ 2 * ∑ s, K r s) ≤ ∑ r, ‖v r‖ ^ 2 * A := by
    apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left (hA r) (sq_nonneg _)
  apply h_A_bound.trans
  rw [← Finset.sum_mul]
  ring_nf
  rfl

lemma sum_C_mul_w_eq_dirichletPoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    (∑ n : ↥(Finset.Ioc 0 N),
      Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n.1 : ℝ) : ℂ)) * (a n.1 / (n.1 : ℂ))) =
    dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I) := by
  rw [dirichletPoly]
  have h_coe := (Finset.sum_coe_sort (Finset.Ioc 0 N)
    (fun n => Complex.exp (-Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ)) * (a n / (n : ℂ)))).symm
  rw [← h_coe]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Ioc] at hn
  have hn_pos : 0 < n := hn.1
  have h := a_mul_cpow_eq_div_mul_exp a n hn_pos t
  rw [h]
  ring

lemma sum_norm_sq_w_eq (a : ℕ → ℂ) (N : ℕ) :
    (∑ n : ↥(Finset.Ioc 0 N), ‖a n.1 / (n.1 : ℂ)‖ ^ 2) =
    ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  have h_coe := (Finset.sum_coe_sort (Finset.Ioc 0 N) (fun n => ‖a n / (n : ℂ)‖ ^ 2)).symm
  rw [← h_coe]
  apply Finset.sum_congr rfl
  intro n _
  rw [norm_div, Complex.norm_natCast, div_pow]

/-- The Halász–Montgomery inequality for Dirichlet polynomials on the 1-line (Matomäki–Radziwiłł Lemma 9). -/
theorem sum_wellSpaced_norm_sq_le_halasz :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (N : ℕ) (T : ℝ) (S : Finset ℝ), 1 ≤ N → 2 ≤ T → WellSpaced S → (∀ t ∈ S, |t| ≤ T) →
      (∑ t ∈ S, ‖dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C * (N + S.card * Real.sqrt T) * Real.log T * ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := norm_sum_Ioc_exp_neg_log_le
  refine ⟨2 + 10 * C₀, by positivity, ?_⟩
  intro a N T S hN hT hS hST
  let ι := ↥S
  let κ := ↥(Finset.Ioc 0 N)
  let C_mat : ι → κ → ℂ := fun r n =>
    Complex.exp (-Complex.I * (r.1 : ℂ) * (Real.log (n.1 : ℝ) : ℂ))
  let K : ι → ι → ℝ := fun r s =>
    ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * ((s.1 - r.1 : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))‖
  have h_star_mul (r s : ι) (n : κ) :
      star (C_mat r n) * C_mat s n =
      Complex.exp (-Complex.I * ((s.1 - r.1 : ℝ) : ℂ) * (Real.log (n.1 : ℝ) : ℂ)) := by
    dsimp [C_mat]
    rw [← Complex.exp_conj]
    have : (starRingEnd ℂ) (-Complex.I * (r.1 : ℂ) * (Real.log (n.1 : ℝ) : ℂ)) =
        Complex.I * (r.1 : ℂ) * (Real.log (n.1 : ℝ) : ℂ) := by
      simp only [map_mul, map_neg, Complex.conj_I, neg_neg, Complex.conj_ofReal]
    rw [this, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hK (r s : ι) : ‖∑ n, star (C_mat r n) * C_mat s n‖ ≤ K r s := by
    dsimp [K]
    have h_eq : (∑ n : κ, (starRingEnd ℂ) (C_mat r n) * C_mat s n) =
        ∑ n : κ, Complex.exp (-Complex.I * ((s.1 - r.1 : ℝ) : ℂ) * (Real.log (n.1 : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n _
      exact h_star_mul r s n
    rw [h_eq]
    have h_coe := Finset.sum_coe_sort (Finset.Ioc 0 N)
      (fun n => Complex.exp (-Complex.I * ((s.1 - r.1 : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ)))
    rw [h_coe]
  have hK_symm (r s : ι) : K r s = K s r := by
    dsimp [K]
    have h_eq : (∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * ((r.1 - s.1 : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))) =
        ∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * (-((s.1 - r.1 : ℝ)) : ℂ) * (Real.log (n : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro n _
      congr 2
      push_cast
      ring
    rw [h_eq, ← norm_sum_exp_neg_eq_norm_sum_exp_pos]
  let A : ℝ := (2 + 10 * C₀) * ((N : ℝ) + (S.card : ℝ) * Real.sqrt T) * Real.log T
  have hA (r : ι) : ∑ s, K r s ≤ A := by
    dsimp [K, A]
    have h_coe := Finset.sum_coe_sort S
      (fun s => ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-Complex.I * ((s - r.1 : ℝ) : ℂ) * (Real.log (n : ℝ) : ℂ))‖)
    rw [h_coe]
    exact step3_row_sum_bound C₀ (le_of_lt hC₀_pos) hC₀ N T S hN hT hS hST r.1 r.2
  have h_dual := norm_sq_sum_le_schur C_mat K hK hK_symm A hA
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    have : 0 ≤ Real.log T := by
      have : (1/2 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hT
      linarith
    positivity
  let w : κ → ℂ := fun n => a n.1 / (n.1 : ℂ)
  have h_trans := BoundedGaps.Maynard.AdditiveLargeSieve.finite_transpose_l2_bound C_mat hA_nonneg h_dual w
  have h_LHS : (∑ r : ι, ‖∑ n : κ, C_mat r n * w n‖ ^ 2) =
      ∑ t ∈ S, ‖dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    have h1 : (fun r : ι => ‖∑ n : κ, C_mat r n * w n‖ ^ 2) =
        (fun r : ι => ‖dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + r.1 * Complex.I)‖ ^ 2) := by
      ext r
      rw [sum_C_mul_w_eq_dirichletPoly a N r.1]
    simp_rw [h1]
    exact Finset.sum_coe_sort S (fun t => ‖dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I)‖ ^ 2)
  have h_RHS : (∑ n : κ, ‖w n‖ ^ 2) = ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
    sum_norm_sq_w_eq a N
  rw [h_LHS, h_RHS] at h_trans
  exact h_trans

end Erdos1201.MR
