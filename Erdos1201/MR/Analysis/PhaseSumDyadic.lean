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


/-- Dyadic head: for `1 ≤ n ≤ 2τ` the phase sum over `(0, n]` is `O(√τ log(4τ))`. -/
lemma norm_sum_Ioc_le_of_le_two_mul (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (M : ℕ) (t : ℝ), 1 ≤ M → 1 ≤ t →
      ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (Real.sqrt t + (M : ℝ) / Real.sqrt t))
    (hC' : ∀ (M M' : ℕ) (t : ℝ), 1 ≤ M → M < M' → M' ≤ 2 * M → 1 ≤ t →
      ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (Real.sqrt t + (M : ℝ) / Real.sqrt t))
    (τ : ℝ) (hτ : 1 ≤ τ) (n : ℕ) (hn1 : 1 ≤ n) (hn : (n : ℝ) ≤ 2 * τ) :
    ‖∑ m ∈ Finset.Ioc 0 n, Complex.exp (-((τ * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      1 + 9 * C * Real.sqrt τ * Real.log (4 * τ) := by
  set L := Nat.log 2 n with hL
  have hpow_le : 2 ^ L ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hlt : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2L : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have hM1 : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hsqrt_pos : 0 < Real.sqrt τ := Real.sqrt_pos.mpr (by linarith)
  have hτ_sqrt : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt (by linarith)
  have hpowR : ((2 ^ L : ℕ) : ℝ) ≤ 2 * τ := by
    have : ((2 ^ L : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpow_le
    linarith
  have hfrac : ((2 ^ L : ℕ) : ℝ) / Real.sqrt τ ≤ 2 * Real.sqrt τ := by
    rw [div_le_iff₀ hsqrt_pos]
    calc ((2 ^ L : ℕ) : ℝ) ≤ 2 * τ := hpowR
      _ = 2 * Real.sqrt τ * Real.sqrt τ := by rw [mul_assoc, hτ_sqrt]
  have hbr : Real.sqrt τ + ((2 ^ L : ℕ) : ℝ) / Real.sqrt τ ≤ 3 * Real.sqrt τ := by linarith
  have hbr0 : 0 ≤ Real.sqrt τ + ((2 ^ L : ℕ) : ℝ) / Real.sqrt τ := by positivity
  have hhead := norm_sum_Ioc_two_pow_le C τ (fun M hM => hC M τ hM hτ) hC0 L hτ
  have hL_bound : ((L + 1 : ℕ) : ℝ) ≤ 3 * Real.log (4 * τ) := by
    apply J_bound τ hτ (L + 1)
    simp only [Nat.add_sub_cancel]
    exact_mod_cast hpowR
  have hlog0 : 0 ≤ Real.log (4 * τ) := Real.log_nonneg (by linarith)
  have hsplit : Finset.Ioc 0 n = Finset.Ioc 0 (2 ^ L) ∪ Finset.Ioc (2 ^ L) n := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Ioc 0 (2 ^ L)) (Finset.Ioc (2 ^ L) n) := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb
    rw [Finset.mem_Ioc] at ha hb
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have htail : ‖∑ m ∈ Finset.Ioc (2 ^ L) n,
      Complex.exp (-((τ * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      C * (Real.sqrt τ + ((2 ^ L : ℕ) : ℝ) / Real.sqrt τ) := by
    rcases Nat.lt_or_ge (2 ^ L) n with h | h
    · exact hC' (2 ^ L) n τ hM1 h (by omega) hτ
    · have : Finset.Ioc (2 ^ L) n = ∅ := Finset.Ioc_eq_empty (by omega)
      rw [this, Finset.sum_empty, norm_zero]
      positivity
  calc ‖_ + _‖
      ≤ ‖∑ m ∈ Finset.Ioc (0 : ℕ) (2 ^ L), Complex.exp (-((τ * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ +
        ‖∑ m ∈ Finset.Ioc (2 ^ L) n, Complex.exp (-((τ * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ :=
          norm_add_le _ _
    _ ≤ (1 + (L : ℝ) * C * (Real.sqrt τ + ((2 ^ L : ℕ) : ℝ) / Real.sqrt τ)) +
        C * (Real.sqrt τ + ((2 ^ L : ℕ) : ℝ) / Real.sqrt τ) := add_le_add hhead htail
    _ = 1 + ((L + 1 : ℕ) : ℝ) * C * (Real.sqrt τ + ((2 ^ L : ℕ) : ℝ) / Real.sqrt τ) := by
        push_cast
        ring
    _ ≤ 1 + (3 * Real.log (4 * τ)) * C * (3 * Real.sqrt τ) := by
        have h1 : ((L + 1 : ℕ) : ℝ) * C * (Real.sqrt τ + ((2 ^ L : ℕ) : ℝ) / Real.sqrt τ) ≤
            (3 * Real.log (4 * τ)) * C * (3 * Real.sqrt τ) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hL_bound hC0) hbr hbr0
          positivity
        linarith
    _ = 1 + 9 * C * Real.sqrt τ * Real.log (4 * τ) := by ring

/-- Kusmin–Landau tail: for `τ ≤ a < N`, the phase sum over `(a, N]` is at most `4πN/τ + 1`. -/
lemma norm_sum_Ioc_le_of_le (τ : ℝ) (hτ : 1 ≤ τ) (a N : ℕ) (ha : τ ≤ a) (haN : a < N) :
    ‖∑ m ∈ Finset.Ioc a N, Complex.exp (-((τ * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      4 * Real.pi * N / τ + 1 := by
  have hτ0 : 0 < τ := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi1 : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hN_pos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hIcc : Finset.Ioc a N = Finset.Icc (a + 1) N := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hIcc]
  simp_rw [exp_phase_eq τ]
  set δ : ℝ := τ / (4 * Real.pi * N) with hδ
  have hδ_pos : 0 < δ := by positivity
  have key := norm_sum_exp_le_of_monotone_diff (vdc_g τ) (a + 1) N (by omega) δ hδ_pos ?_ ?_ ?_ ?_
  · calc _ ≤ 1 / δ + 1 := key
      _ = 4 * Real.pi * N / τ + 1 := by
        rw [hδ]
        field_simp
  · intro n hn _
    have h1 : 1 ≤ n := by omega
    have := vdc_d_neg τ hτ0 n h1
    simpa [vdc_d] using this
  · intro n hn _
    have h1 : 1 ≤ n := by omega
    have := vdc_d_mono τ hτ0 n h1
    simp only [vdc_d] at this
    exact this
  · intro n hn hnN
    have h1 : 1 ≤ n := by omega
    have habs := abs_vdc_d_eq τ hτ0 n h1
    have hlog := log_one_add_inv_ge n h1
    have hnR : (n : ℝ) ≤ N := by exact_mod_cast hnN.le
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast h1
    show δ ≤ |vdc_d τ n|
    rw [habs, hδ]
    have e : τ / (2 * Real.pi) * (1 / (2 * (n : ℝ))) = τ / (4 * Real.pi * n) := by
      field_simp
      ring
    calc τ / (4 * Real.pi * N) ≤ τ / (4 * Real.pi * n) :=
          div_le_div_of_nonneg_left hτ0.le (by positivity) (by nlinarith)
      _ = τ / (2 * Real.pi) * (1 / (2 * (n : ℝ))) := e.symm
      _ ≤ τ / (2 * Real.pi) * Real.log (1 + 1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
  · intro n hn _
    have h1 : 1 ≤ n := by omega
    have habs := abs_vdc_d_eq τ hτ0 n h1
    have hlog := log_one_add_inv_le n h1
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast h1
    have hτn : τ ≤ n := by
      have : (a : ℝ) ≤ n := by exact_mod_cast (show a ≤ n by omega)
      linarith
    show |vdc_d τ n| ≤ 1 / 2
    rw [habs]
    calc τ / (2 * Real.pi) * Real.log (1 + 1 / (n : ℝ))
        ≤ τ / (2 * Real.pi) * (1 / (n : ℝ)) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = τ / n / (2 * Real.pi) := by ring
      _ ≤ 1 / (2 * Real.pi) := by
          gcongr
          rw [div_le_one hn_pos]
          exact hτn
      _ ≤ 1 / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith

/-- The complete-range phase sum bound `‖∑_{0<n≤N} n^{-iτ}‖ ≤ C (N/τ + √τ log(4τ))`. -/
theorem norm_sum_Ioc_exp_neg_log_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (τ : ℝ), 1 ≤ N → 1 ≤ τ →
      ‖∑ n ∈ Finset.Ioc 0 N, Complex.exp (-((τ * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
        C * ((N : ℝ) / τ + Real.sqrt τ * Real.log (4 * τ)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := norm_sum_exp_neg_log_mul_I_le
  obtain ⟨C₂, hC₂, h₂⟩ := norm_sum_exp_neg_log_mul_I_subblock_le
  set C := max C₁ C₂ with hCdef
  have hC0 : 0 ≤ C := le_trans hC₁.le (le_max_left _ _)
  have h₁' : ∀ (M : ℕ) (t : ℝ), 1 ≤ M → 1 ≤ t →
      ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := fun M t hM ht =>
    (h₁ M t hM ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have h₂' : ∀ (M M' : ℕ) (t : ℝ), 1 ≤ M → M < M' → M' ≤ 2 * M → 1 ≤ t →
      ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := fun M M' t hM hMM' hM' ht =>
    (h₂ M M' t hM hMM' hM' ht).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  refine ⟨9 * C + 4 * Real.pi + 2, by positivity, ?_⟩
  intro N τ hN hτ
  have hτ0 : 0 < τ := by linarith
  have hS1 : 1 ≤ Real.sqrt τ * Real.log (4 * τ) := by
    have h1 : 1 ≤ Real.sqrt τ := Real.one_le_sqrt.mpr hτ
    have h2 : 1 ≤ Real.log (4 * τ) := by
      calc (1 : ℝ) ≤ Real.log 4 := hl4
        _ ≤ Real.log (4 * τ) := Real.log_le_log (by norm_num) (by linarith)
    nlinarith
  have hR0 : 0 ≤ (N : ℝ) / τ := by positivity
  have hCR : 0 ≤ C * ((N : ℝ) / τ) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  set n₀ := ⌈τ⌉₊ with hn₀
  have hn₀R : τ ≤ (n₀ : ℝ) := Nat.le_ceil τ
  have hn₀lt : (n₀ : ℝ) < τ + 1 := Nat.ceil_lt_add_one hτ0.le
  have hn₀1 : 1 ≤ n₀ := by
    have : (1 : ℝ) ≤ n₀ := hτ.trans hn₀R
    exact_mod_cast this
  have hn₀2 : (n₀ : ℝ) ≤ 2 * τ := by linarith
  rcases Nat.lt_or_ge n₀ N with hlt | hge
  · have hsplit : Finset.Ioc 0 N = Finset.Ioc 0 n₀ ∪ Finset.Ioc n₀ N := by
      ext x
      simp only [Finset.mem_union, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Ioc 0 n₀) (Finset.Ioc n₀ N) := by
      rw [Finset.disjoint_iff_ne]
      intro a ha b hb
      rw [Finset.mem_Ioc] at ha hb
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have hhead := norm_sum_Ioc_le_of_le_two_mul C hC0 h₁' h₂' τ hτ n₀ hn₀1 hn₀2
    have htail := norm_sum_Ioc_le_of_le τ hτ n₀ N hn₀R hlt
    calc ‖_ + _‖ ≤ ‖∑ m ∈ Finset.Ioc 0 n₀, Complex.exp (-((τ * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ +
          ‖∑ m ∈ Finset.Ioc n₀ N, Complex.exp (-((τ * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ :=
            norm_add_le _ _
      _ ≤ (1 + 9 * C * Real.sqrt τ * Real.log (4 * τ)) + (4 * Real.pi * N / τ + 1) :=
            add_le_add hhead htail
      _ ≤ (9 * C + 4 * Real.pi + 2) * ((N : ℝ) / τ + Real.sqrt τ * Real.log (4 * τ)) := by
            have e : 4 * Real.pi * (N : ℝ) / τ = 4 * Real.pi * ((N : ℝ) / τ) := by ring
            rw [e]
            nlinarith
  · have hNR : (N : ℝ) ≤ 2 * τ := by
      have : (N : ℝ) ≤ n₀ := by exact_mod_cast hge
      linarith
    have hhead := norm_sum_Ioc_le_of_le_two_mul C hC0 h₁' h₂' τ hτ N hN hNR
    calc _ ≤ 1 + 9 * C * Real.sqrt τ * Real.log (4 * τ) := hhead
      _ ≤ (9 * C + 4 * Real.pi + 2) * ((N : ℝ) / τ + Real.sqrt τ * Real.log (4 * τ)) := by
            nlinarith

end Erdos1201.MR
