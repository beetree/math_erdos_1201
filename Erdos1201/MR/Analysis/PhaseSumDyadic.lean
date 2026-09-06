import Mathlib
import Erdos1201.Basic
import Erdos1201.PrimeSums
import Erdos1201.SmoothBound
import Erdos1201.MR.Analysis.KusminLandau
import Erdos1201.MR.Analysis.VanDerCorput
import Erdos1201.MR.Analysis.VanDerCorputSubblock

/-!
# The phase sum `∑_{n ≤ N} n^{-iτ}` over a complete range

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

The main result `norm_sum_Ioc_exp_neg_log_le` bounds `∑_{0 < n ≤ N} exp(-iτ log n)` by
`C (N/τ + √τ log(4τ))`: the range `n ≤ ⌈τ⌉` is covered by dyadic blocks and the van der Corput
bound, the range `n > ⌈τ⌉` by a single application of the Kusmin–Landau inequality.
-/

open Real Complex Finset

namespace Erdos1201.MR

lemma hl4 : (1:ℝ) ≤ Real.log 4 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  calc Real.exp 1 ≤ (2.8 : ℝ) := Real.exp_one_lt_d9.le.trans (by norm_num)
    _ ≤ 4 := by norm_num

lemma hl2_half : (1/2:ℝ) ≤ Real.log 2 := by
  have h_log4 : Real.log 4 = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow (2:ℝ) 2]
    norm_cast
  linarith [hl4, h_log4]

lemma inv_log2_le_two : 1 / Real.log 2 ≤ 2 := by
  have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [div_le_iff₀ h1]
  linarith [hl2_half]

lemma J_bound (τ : ℝ) (hτ : 1 ≤ τ) (J : ℕ) (hJ : (2 : ℝ) ^ (J - 1) ≤ 2 * τ) :
    (J : ℝ) ≤ 3 * Real.log (4 * τ) := by
  by_cases h : J = 0
  · subst h
    simp
    have : 0 ≤ Real.log (4 * τ) := Real.log_nonneg (by linarith)
    positivity
  have h1 : Real.log ((2 : ℝ) ^ (J - 1)) ≤ Real.log (2 * τ) := by
    apply Real.log_le_log (by positivity) hJ
  have h2 : Real.log ((2 : ℝ) ^ (J - 1)) = (J - 1 : ℕ) * Real.log 2 := by
    exact Real.log_pow (2:ℝ) (J - 1)
  rw [h2] at h1
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : ((J - 1 : ℕ) : ℝ) ≤ Real.log (2 * τ) / Real.log 2 := by
    exact le_div_iff₀ hl2 |>.mpr h1
  have h4 : (J : ℝ) = ((J - 1 : ℕ) : ℝ) + 1 := by
    have : J - 1 + 1 = J := Nat.sub_add_cancel (Nat.pos_of_ne_zero h)
    nth_rw 1 [← this]
    push_cast
    rfl
  rw [h4]
  have h5 : Real.log (2 * τ) / Real.log 2 + 1 = Real.log (4 * τ) / Real.log 2 := by
    have h_log2τ : Real.log (2 * τ) + Real.log 2 = Real.log (4 * τ) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      ring
    calc Real.log (2 * τ) / Real.log 2 + 1 = (Real.log (2 * τ) + Real.log 2) / Real.log 2 := by
          rw [add_div, div_self (ne_of_gt hl2)]
      _ = Real.log (4 * τ) / Real.log 2 := by rw [h_log2τ]
  have h6 : Real.log (4 * τ) / Real.log 2 ≤ 2 * Real.log (4 * τ) := by
    have h_nonneg : 0 ≤ Real.log (4 * τ) := Real.log_nonneg (by linarith)
    have h_inv : 1 / Real.log 2 ≤ 2 := inv_log2_le_two
    calc Real.log (4 * τ) / Real.log 2 = (1 / Real.log 2) * Real.log (4 * τ) := by ring
      _ ≤ 2 * Real.log (4 * τ) := mul_le_mul_of_nonneg_right h_inv h_nonneg
  have h_add : ((J - 1 : ℕ) : ℝ) + 1 ≤ Real.log (2 * τ) / Real.log 2 + 1 := by
    gcongr
  calc ((J - 1 : ℕ) : ℝ) + 1 ≤ Real.log (2 * τ) / Real.log 2 + 1 := h_add
    _ = Real.log (4 * τ) / Real.log 2 := h5
    _ ≤ 2 * Real.log (4 * τ) := h6
    _ ≤ 3 * Real.log (4 * τ) := by linarith [Real.log_nonneg (show 1 ≤ 4 * τ by linarith)]

lemma norm_sum_Ioc_two_pow_le (C τ : ℝ)
    (hC : ∀ M : ℕ, 1 ≤ M → ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((τ * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ C * (Real.sqrt τ + (M : ℝ) / Real.sqrt τ))
    (hC_pos : 0 ≤ C) (K : ℕ) (hτ : 1 ≤ τ) :
    ‖∑ n ∈ Finset.Ioc 0 (2^K : ℕ), Complex.exp (-((τ * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      1 + K * C * (Real.sqrt τ + ((2^K : ℕ) : ℝ) / Real.sqrt τ) := by
  induction K with
  | zero =>
    have : Finset.Ioc 0 1 = {1} := rfl
    rw [pow_zero, this, Finset.sum_singleton]
    simp
  | succ K ih =>
    have h_split : Finset.Ioc 0 (2^(K+1) : ℕ) = Finset.Ioc 0 (2^K : ℕ) ∪ Finset.Ioc (2^K : ℕ) (2^(K+1) : ℕ) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Ioc]
      omega
    have h_disj : Disjoint (Finset.Ioc 0 (2^K : ℕ)) (Finset.Ioc (2^K : ℕ) (2^(K+1) : ℕ)) := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb
      rw [Finset.mem_Ioc] at ha hb
      omega
    rw [h_split, Finset.sum_union h_disj]
    have h_tri := norm_add_le (∑ n ∈ Finset.Ioc 0 (2^K : ℕ), Complex.exp (-((τ * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I))
                              (∑ n ∈ Finset.Ioc (2^K : ℕ) (2^(K+1) : ℕ), Complex.exp (-((τ * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I))
    have h_step : (2 ^ (K + 1) : ℕ) = 2 * 2 ^ K := by omega
    have h_M_ge_1 : 1 ≤ 2^K := Nat.one_le_two_pow
    have h_sum2 := hC (2^K) h_M_ge_1
    rw [← h_step] at h_sum2
    have h_add2 : ‖∑ n ∈ Finset.Ioc 0 (2^K : ℕ), Complex.exp (-((τ * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ + ‖∑ n ∈ Finset.Ioc (2^K : ℕ) (2^(K+1) : ℕ), Complex.exp (-((τ * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ 1 + (K : ℝ) * C * (Real.sqrt τ + ((2^K : ℕ) : ℝ) / Real.sqrt τ) + C * (Real.sqrt τ + ((2^K : ℕ) : ℝ) / Real.sqrt τ) := by
      exact add_le_add ih h_sum2
    calc ‖_ + _‖ ≤ ‖∑ n ∈ Finset.Ioc 0 (2^K : ℕ), _‖ + ‖∑ n ∈ Finset.Ioc (2^K : ℕ) (2^(K+1) : ℕ), _‖ := h_tri
      _ ≤ 1 + (K : ℝ) * C * (Real.sqrt τ + ((2^K : ℕ) : ℝ) / Real.sqrt τ) + C * (Real.sqrt τ + ((2^K : ℕ) : ℝ) / Real.sqrt τ) := h_add2
      _ = 1 + (K + 1 : ℝ) * C * (Real.sqrt τ + ((2^K : ℕ) : ℝ) / Real.sqrt τ) := by push_cast; ring
      _ ≤ 1 + (K + 1 : ℝ) * C * (Real.sqrt τ + ((2^(K+1) : ℕ) : ℝ) / Real.sqrt τ) := by
        have : ((2^K : ℕ) : ℝ) ≤ ((2^(K+1) : ℕ) : ℝ) := by
          norm_cast
          omega
        have hh : (Real.sqrt τ + ((2^K : ℕ) : ℝ) / Real.sqrt τ) ≤ (Real.sqrt τ + ((2^(K+1) : ℕ) : ℝ) / Real.sqrt τ) := by
          gcongr
        have h_nonneg : 0 ≤ (K + 1 : ℝ) * C := by positivity
        have hl : (K + 1 : ℝ) * C * (Real.sqrt τ + ((2^K : ℕ) : ℝ) / Real.sqrt τ) ≤ (K + 1 : ℝ) * C * (Real.sqrt τ + ((2^(K+1) : ℕ) : ℝ) / Real.sqrt τ) := mul_le_mul_of_nonneg_left hh h_nonneg
        exact add_le_add le_rfl hl
      _ = 1 + ((K + 1 : ℕ) : ℝ) * C * (Real.sqrt τ + ((2^(K+1) : ℕ) : ℝ) / Real.sqrt τ) := by push_cast; rfl

