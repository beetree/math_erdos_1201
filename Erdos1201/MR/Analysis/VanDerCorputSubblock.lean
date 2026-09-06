import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Pi.Bounds
import Erdos1201.MR.Analysis.KusminLandau
import Erdos1201.MR.Analysis.VanDerCorput

/-!
# Van der Corput Second Derivative Bound for Sub-blocks

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the van der Corput second-derivative bound for sub-blocks of dyadic exponential sums
of the form `∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I)` with `M < M' ≤ 2 * M`.
-/

open Real Complex Finset

namespace Erdos1201.MR

/-- The cardinality of a sub-block `(M, M']` with `M < M' ≤ 2 * M` is at most `M`. -/
lemma card_Ioc_subblock_le (M M' : ℕ) (_hMM' : M < M') (hM' : M' ≤ 2 * M) :
    (Finset.Ioc M M').card ≤ M := by
  rw [Nat.card_Ioc]
  omega

/-- Trivial bound on sub-block exponential sum by the block size `M`. -/
lemma norm_sum_exp_phase_subblock_le_card (M M' : ℕ) (t : ℝ) (hMM' : M < M') (hM' : M' ≤ 2 * M) :
    ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ (M : ℝ) := by
  have h1 := norm_sum_le (Finset.Ioc M M') (fun m => Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I))
  have h2 : ∑ m ∈ Finset.Ioc M M', ‖Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤ (M : ℝ) := by
    have : ∀ m ∈ Finset.Ioc M M', ‖Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ = 1 :=
      fun m _ => norm_exp_phase t m
    rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]
    have hcard := card_Ioc_subblock_le M M' hMM' hM'
    exact_mod_cast hcard
  linarith

/-- Bound for sub-blocks when `t` is large (`M^2 ≤ t`). -/
lemma norm_sum_exp_phase_subblock_of_large_t (M M' : ℕ) (t : ℝ) (hM : 1 ≤ M)
    (hMM' : M < M') (hM' : M' ≤ 2 * M) (ht : (M : ℝ) ^ 2 ≤ t) :
    ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      1 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  have ht_pos : 0 < t := by
    have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
    have : 0 < (M : ℝ) ^ 2 := by positivity
    linarith
  have hM_le_sqrt : (M : ℝ) ≤ Real.sqrt t := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg M)]
    exact Real.sqrt_le_sqrt ht
  have hcard := norm_sum_exp_phase_subblock_le_card M M' t hMM' hM'
  have h_sqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hdiv_nonneg : 0 ≤ (M : ℝ) / Real.sqrt t := div_nonneg (Nat.cast_nonneg M) h_sqrt_pos.le
  calc ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖
    _ ≤ (M : ℝ) := hcard
    _ ≤ Real.sqrt t := hM_le_sqrt
    _ ≤ Real.sqrt t + (M : ℝ) / Real.sqrt t := le_add_of_nonneg_right hdiv_nonneg
    _ = 1 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by ring

/-- Rewriting `Ioc M M'` as `Icc (M + 1) M'`. -/
lemma Ioc_eq_Icc_succ_right (M M' : ℕ) :
    Finset.Ioc M M' = Finset.Icc (M + 1) M' := by
  ext x
  simp only [mem_Ioc, mem_Icc]
  omega

/-- Bound for sub-blocks when `t` is small (`t ≤ π * M`). -/
lemma norm_sum_exp_phase_subblock_of_small_t (M M' : ℕ) (t : ℝ) (hM : 1 ≤ M)
    (_hMM' : M < M') (hM' : M' ≤ 2 * M) (ht1 : 1 ≤ t) (ht_small : t ≤ Real.pi * (M : ℝ)) :
    ‖∑ m ∈ Finset.Icc (M + 1) M', Complex.exp (2 * Real.pi * Complex.I * ((vdc_g t m : ℝ) : ℂ))‖ ≤
      (8 * Real.pi + 1) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  have ht_pos : 0 < t := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hab : M + 1 ≤ M' := by omega
  set δ := t / (8 * Real.pi * (M : ℝ))
  have hδ_pos : 0 < δ := by positivity
  have hneg : ∀ n, M + 1 ≤ n → n < M' → vdc_g t (n + 1) - vdc_g t n < 0 := by
    intro n hn _
    exact vdc_d_neg t ht_pos n (by omega)
  have hmono : ∀ n, M + 1 ≤ n → n + 1 < M' →
      vdc_g t (n + 1) - vdc_g t n ≤ vdc_g t (n + 2) - vdc_g t (n + 1) := by
    intro n hn _
    exact vdc_d_mono t ht_pos n (by omega)
  have hlow : ∀ n, M + 1 ≤ n → n < M' → δ ≤ |vdc_g t (n + 1) - vdc_g t n| := by
    intro n hn hnM'
    have hn1 : 1 ≤ n := by omega
    change δ ≤ |vdc_d t n|
    rw [abs_vdc_d_eq t ht_pos n hn1]
    have hlog := log_one_add_inv_ge n hn1
    have hn_le : (n : ℝ) ≤ 2 * (M : ℝ) := by
      have : n ≤ 2 * M := by omega
      exact_mod_cast this
    have h1 : 1 / (4 * (M : ℝ)) ≤ 1 / (2 * (n : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    have hlog_ge : 1 / (4 * (M : ℝ)) ≤ Real.log (1 + 1 / (n : ℝ)) := h1.trans hlog
    have ht2pi_nonneg : 0 ≤ t / (2 * Real.pi) := by positivity
    calc δ = (t / (2 * Real.pi)) * (1 / (4 * (M : ℝ))) := by
           simp only [δ]; ring
      _ ≤ (t / (2 * Real.pi)) * Real.log (1 + 1 / (n : ℝ)) :=
           mul_le_mul_of_nonneg_left hlog_ge ht2pi_nonneg
  have hhalf : ∀ n, M + 1 ≤ n → n < M' → |vdc_g t (n + 1) - vdc_g t n| ≤ 1 / 2 := by
    intro n hn _
    have hn1 : 1 ≤ n := by omega
    change |vdc_d t n| ≤ 1 / 2
    rw [abs_vdc_d_eq t ht_pos n hn1]
    have hlog := log_one_add_inv_le n hn1
    have hM_le_n : (M : ℝ) ≤ (n : ℝ) := by
      have : M ≤ n := by omega
      exact_mod_cast this
    have h1 : 1 / (n : ℝ) ≤ 1 / (M : ℝ) := one_div_le_one_div_of_le hM_pos hM_le_n
    have hlog_le : Real.log (1 + 1 / (n : ℝ)) ≤ 1 / (M : ℝ) := hlog.trans h1
    have ht2pi_nonneg : 0 ≤ t / (2 * Real.pi) := by positivity
    have hmul : (t / (2 * Real.pi)) * Real.log (1 + 1 / (n : ℝ)) ≤ (t / (2 * Real.pi)) * (1 / (M : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_le ht2pi_nonneg
    have h_cancel : (t / (2 * Real.pi)) * (1 / (M : ℝ)) = t / (2 * Real.pi * (M : ℝ)) := by ring
    rw [h_cancel] at hmul
    have ht_div : t / (2 * Real.pi * (M : ℝ)) ≤ 1 / 2 := by
      have h2piM_pos : 0 < 2 * Real.pi * (M : ℝ) := by positivity
      rw [div_le_iff₀ h2piM_pos]
      linarith
    linarith
  have hKL := norm_sum_exp_le_of_monotone_diff (vdc_g t) (M + 1) M' hab δ hδ_pos hneg hmono hlow hhalf
  have h_one_div_δ : 1 / δ = 8 * Real.pi * (M : ℝ) / t := by
    simp only [δ]
    field_simp
  have h_sqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have ht_ge_sqrt : Real.sqrt t ≤ t := by
    have : 1 ≤ Real.sqrt t := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt ht1
    calc Real.sqrt t ≤ Real.sqrt t * Real.sqrt t := by nlinarith
      _ = t := Real.mul_self_sqrt (by linarith)
  have h_div_le : 8 * Real.pi * (M : ℝ) / t ≤ 8 * Real.pi * ((M : ℝ) / Real.sqrt t) := by
    have h1 : 1 / t ≤ 1 / Real.sqrt t := one_div_le_one_div_of_le h_sqrt_pos ht_ge_sqrt
    have h2 : 0 ≤ 8 * Real.pi * (M : ℝ) := by positivity
    calc 8 * Real.pi * (M : ℝ) / t = (8 * Real.pi * (M : ℝ)) * (1 / t) := by ring
      _ ≤ (8 * Real.pi * (M : ℝ)) * (1 / Real.sqrt t) := mul_le_mul_of_nonneg_left h1 h2
      _ = 8 * Real.pi * ((M : ℝ) / Real.sqrt t) := by ring
  have h_one_le_sqrt : 1 ≤ Real.sqrt t := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ht1
  have hM_div_nonneg : 0 ≤ (M : ℝ) / Real.sqrt t := div_nonneg (by positivity) (by positivity)
  have hsqrt_nonneg : 0 ≤ Real.sqrt t := by positivity
  calc ‖∑ m ∈ Finset.Icc (M + 1) M', Complex.exp (2 * Real.pi * Complex.I * ((vdc_g t m : ℝ) : ℂ))‖
    _ ≤ 1 / δ + 1 := hKL
    _ = 8 * Real.pi * (M : ℝ) / t + 1 := by rw [h_one_div_δ]
    _ ≤ 8 * Real.pi * ((M : ℝ) / Real.sqrt t) + Real.sqrt t := by linarith [h_div_le, h_one_le_sqrt]
    _ ≤ (8 * Real.pi + 1) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
         nlinarith [hpi, hM_div_nonneg, hsqrt_nonneg]

lemma norm_sum_exp_phase_subblock_of_small_t' (M M' : ℕ) (t : ℝ) (hM : 1 ≤ M)
    (hMM' : M < M') (hM' : M' ≤ 2 * M) (ht1 : 1 ≤ t) (ht_small : t ≤ Real.pi * (M : ℝ)) :
    ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (8 * Real.pi + 1) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  have heq : ∀ m ∈ Finset.Ioc M M',
      Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * ((vdc_g t m : ℝ) : ℂ)) :=
    fun m _ => exp_phase_eq t m
  rw [sum_congr rfl heq, Ioc_eq_Icc_succ_right]
  exact norm_sum_exp_phase_subblock_of_small_t M M' t hM hMM' hM' ht1 ht_small

/-- Bound for each fiber in the phase partition for a sub-block. -/
lemma norm_sum_exp_fiber_subblock_le (M M' : ℕ) (t : ℝ) (hM : 1 ≤ M)
    (_hMM' : M < M') (hM' : M' ≤ 2 * M) (ht1 : 1 ≤ t)
    (_ht_med1 : Real.pi * (M : ℝ) < t) (ht_med2 : t < (M : ℝ) ^ 2)
    (δ : ℝ) (hδ : δ = Real.sqrt t / (8 * Real.pi * (M : ℝ)))
    (k : ℤ) (tag : Fin 3) :
    let s := (Finset.Ioc M M').filter (fun m => vdc_class (vdc_d t m) δ = (k, tag))
    ‖∑ m ∈ s, Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1 := by
  intro s
  have ht_pos : 0 < t := by linarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have h_sqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hδ_pos : 0 < δ := by rw [hδ]; positivity
  have h_sqrt_lt_M : Real.sqrt t < (M : ℝ) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg M)]
    exact Real.sqrt_lt_sqrt (by positivity) ht_med2
  have hδ_half : δ < 1 / 2 := by
    rw [hδ]
    have h1 : Real.sqrt t / (8 * Real.pi * (M : ℝ)) < (M : ℝ) / (8 * Real.pi * (M : ℝ)) :=
      div_lt_div_of_pos_right h_sqrt_lt_M (by positivity)
    have h2 : (M : ℝ) / (8 * Real.pi * (M : ℝ)) = 1 / (8 * Real.pi) := by
      field_simp
    have h3 : (1 : ℝ) / (8 * Real.pi) < 1 / 2 := by
      have : (2 : ℝ) < 8 * Real.pi := by nlinarith [pi_gt_three]
      exact one_div_lt_one_div_of_lt (by norm_num) this
    linarith
  have h_one_div_δ : 1 / δ = 8 * Real.pi * (M : ℝ) / Real.sqrt t := by
    rw [hδ]; field_simp
  have h_exp_eq : ∀ m ∈ s,
      Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * (((vdc_g t m + (k : ℝ) * (m : ℝ)) : ℝ) : ℂ)) := by
    intro m hm
    have hm_Ioc := (Finset.mem_filter.mp hm).1
    rw [exp_phase_eq t m, exp_phase_shift (vdc_g t m) k m]
  rw [sum_congr rfl h_exp_eq]
  have h_dist : (8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t =
      8 * Real.pi * (M : ℝ) / Real.sqrt t + 8 * (M : ℝ) / Real.sqrt t := by ring
  by_cases hs : s.Nonempty
  · have hconv := vdc_class_convex k tag δ hδ_pos hδ_half
    have hmono : ∀ x y, M ≤ x → x ≤ y → y ≤ M' → vdc_d t x ≤ vdc_d t y :=
      fun x y hx hxy _ => vdc_d_mono_on t ht_pos M hM hx hxy
    have ⟨a, b, ha, hab, hb, heq⟩ := filter_Ioc_eq_Icc_of_convex_mono_on (vdc_d t) M M' hmono
      (fun d => vdc_class d δ = (k, tag)) hconv hs
    have hs_eq : s = Finset.Icc a b := heq
    rw [hs_eq]
    set h := fun m => vdc_g t m + (k : ℝ) * (m : ℝ)
    have h_diff_eq : ∀ n, h (n + 1) - h n = vdc_d t n + (k : ℝ) := by
      intro n
      simp only [h, vdc_d]
      push_cast
      ring
    have h_diff_mono : ∀ n, a ≤ n → n + 1 < b →
        h (n + 1) - h n ≤ h (n + 2) - h (n + 1) := by
      intro n hn hnb
      rw [h_diff_eq n, h_diff_eq (n + 1)]
      have : 1 ≤ n := by omega
      have hstep := vdc_d_mono t ht_pos n this
      linarith
    fin_cases tag
    · have h_norm_le : ‖∑ m ∈ Finset.Icc a b, Complex.exp (2 * Real.pi * Complex.I * ((h m : ℝ) : ℂ))‖ ≤
          ((Finset.Icc a b).card : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have : ∀ m ∈ Finset.Icc a b, ‖Complex.exp (2 * Real.pi * Complex.I * ((h m : ℝ) : ℂ))‖ = 1 :=
          fun m _ => norm_exp_two_pi_I_mul (h m)
        rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]
      have ha_in : a ∈ s := by rw [hs_eq]; exact mem_Icc.mpr ⟨le_rfl, hab⟩
      have hb_in : b ∈ s := by rw [hs_eq]; exact mem_Icc.mpr ⟨hab, le_rfl⟩
      have ha_class := (Finset.mem_filter.mp ha_in).2
      have hb_class := (Finset.mem_filter.mp hb_in).2
      have ha_0 := (vdc_class_zero_iff (vdc_d t a) δ hδ_half k).mp ha_class
      have hb_0 := (vdc_class_zero_iff (vdc_d t b) δ hδ_half k).mp hb_class
      have hsub : vdc_d t b - vdc_d t a ≤ 2 * δ := by linarith [ha_0.1, hb_0.2]
      have hstep : ∀ m, M ≤ m → m < 2 * M → t / (32 * Real.pi * (M : ℝ) ^ 2) ≤ vdc_d t (m + 1) - vdc_d t m :=
        fun m hm1 hm2 => vdc_d_diff_ge t ht_pos M hM m hm1 hm2
      have hcard := card_Icc_le_of_d_sub_le t ht_pos M hM a b ha.le (le_trans hb hM') hab hstep δ hδ_pos hsub
      have h_δ_eval : 64 * Real.pi * δ * (M : ℝ) ^ 2 / t = 8 * (M : ℝ) / Real.sqrt t := by
        rw [hδ]
        exact delta_eval_simp t (M : ℝ) ht_pos hM_pos
      rw [h_δ_eval] at hcard
      have h8pi_pos : 0 ≤ 8 * Real.pi * (M : ℝ) / Real.sqrt t := by positivity
      have h8_pos : 0 ≤ 8 * (M : ℝ) / Real.sqrt t := by positivity
      rw [h_dist]
      linarith [h_norm_le, hcard]
    · have hKL := norm_sum_exp_le_of_monotone_diff h a b hab δ hδ_pos
      have hneg : ∀ n, a ≤ n → n < b → h (n + 1) - h n < 0 := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_1 := (vdc_class_one_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        linarith [hn_1.2]
      have hlow : ∀ n, a ≤ n → n < b → δ ≤ |h (n + 1) - h n| := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_1 := (vdc_class_one_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        have : vdc_d t n + (k : ℝ) < 0 := by linarith [hn_1.2]
        rw [abs_of_neg this]
        linarith [hn_1.2]
      have hhalf : ∀ n, a ≤ n → n < b → |h (n + 1) - h n| ≤ 1 / 2 := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_1 := (vdc_class_one_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        have : vdc_d t n + (k : ℝ) < 0 := by linarith [hn_1.2]
        rw [abs_of_neg this]
        linarith [hn_1.1]
      have hKL_bound := hKL hneg h_diff_mono hlow hhalf
      rw [h_one_div_δ] at hKL_bound
      have h8pi_pos : 0 ≤ 8 * Real.pi * (M : ℝ) / Real.sqrt t := by positivity
      have h8_pos : 0 ≤ 8 * (M : ℝ) / Real.sqrt t := by positivity
      rw [h_dist]
      linarith
    · have hKL_pos := norm_sum_exp_le_of_monotone_diff_pos h a b hab δ hδ_pos
      have hpos : ∀ n, a ≤ n → n < b → 0 < h (n + 1) - h n := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_2 := (vdc_class_two_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        linarith [hn_2.1]
      have hlow : ∀ n, a ≤ n → n < b → δ ≤ h (n + 1) - h n := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_2 := (vdc_class_two_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        linarith [hn_2.1]
      have hhalf : ∀ n, a ≤ n → n < b → h (n + 1) - h n ≤ 1 / 2 := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_2 := (vdc_class_two_iff (vdc_d t n) δ hδ_pos k).mp hn_class
        linarith [hn_2.2]
      have hKL_bound := hKL_pos hpos h_diff_mono hlow hhalf
      rw [h_one_div_δ] at hKL_bound
      have h8pi_pos : 0 ≤ 8 * Real.pi * (M : ℝ) / Real.sqrt t := by positivity
      have h8_pos : 0 ≤ 8 * (M : ℝ) / Real.sqrt t := by positivity
      rw [h_dist]
      linarith
  · have : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    rw [this, sum_empty, norm_zero]
    have : 0 ≤ (8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1 := by positivity
    linarith

/-- Bound for sub-blocks in the medium range `π * M < t < M^2`. -/
lemma norm_sum_exp_phase_of_medium_t_subblock (M M' : ℕ) (t : ℝ) (hM : 1 ≤ M)
    (hMM' : M < M') (hM' : M' ≤ 2 * M) (ht1 : 1 ≤ t)
    (ht_med1 : Real.pi * (M : ℝ) < t) (ht_med2 : t < (M : ℝ) ^ 2) :
    ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      250 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  have ht_pos : 0 < t := by linarith
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  set δ := Real.sqrt t / (8 * Real.pi * (M : ℝ))
  set K := Nat.floor (t / (2 * Real.pi * (M : ℝ)) + 1)
  set T : Finset (ℕ × Fin 3) := (Finset.range (K + 1)) ×ˢ (Finset.univ : Finset (Fin 3))
  have h_maps : ∀ m ∈ Finset.Ioc M M', ((vdc_k (vdc_d t m)).toNat, vdc_tag (vdc_d t m) δ) ∈ T := by
    intro m hm
    simp only [T, mem_product, mem_univ, and_true, mem_range]
    have hm_Ioc2M : m ∈ Finset.Ioc M (2 * M) := by
      rw [Finset.mem_Ioc] at hm ⊢
      exact ⟨hm.1, le_trans hm.2 hM'⟩
    have hk_mem := vdc_k_mem_Icc t ht_pos M hM m hm_Ioc2M
    simp only [mem_Icc] at hk_mem
    have h_toNat_le : (vdc_k (vdc_d t m)).toNat ≤ K := by
      change (vdc_k (vdc_d t m)).toNat ≤ (⌊t / (2 * Real.pi * (M : ℝ)) + 1⌋).toNat
      exact Int.toNat_le_toNat hk_mem.2
    omega
  set g_class : ℕ → ℕ × Fin 3 := fun m => ((vdc_k (vdc_d t m)).toNat, vdc_tag (vdc_d t m) δ)
  have h_fiber := Finset.sum_fiberwise_of_maps_to h_maps
    (fun m => Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I))
  have h_tri : ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      ∑ j ∈ T, ‖∑ m ∈ Finset.Ioc M M' with g_class m = j,
        Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ := by
    rw [← h_fiber]
    exact norm_sum_le T _
  have h_term_bound : ∀ j ∈ T, ‖∑ m ∈ Finset.Ioc M M' with g_class m = j,
      Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1 := by
    intro j _
    rcases j with ⟨k_nat, tag⟩
    set k : ℤ := (k_nat : ℤ)
    have heq_fiber : ∀ m ∈ Finset.Ioc M M',
        (g_class m = (k_nat, tag)) ↔ (vdc_class (vdc_d t m) δ = (k, tag)) := by
      intro m hm
      have hm_Ioc2M : m ∈ Finset.Ioc M (2 * M) := by
        rw [Finset.mem_Ioc] at hm ⊢
        exact ⟨hm.1, le_trans hm.2 hM'⟩
      have hk_mem := vdc_k_mem_Icc t ht_pos M hM m hm_Ioc2M
      simp only [mem_Icc] at hk_mem
      have h_toNat : (vdc_k (vdc_d t m)).toNat = k_nat ↔ vdc_k (vdc_d t m) = k := by
        constructor
        · intro h
          have : ((vdc_k (vdc_d t m)).toNat : ℤ) = (k_nat : ℤ) := by exact_mod_cast h
          rwa [Int.toNat_of_nonneg hk_mem.1] at this
        · intro h; rw [h]; rfl
      simp only [g_class, vdc_class, Prod.mk.injEq, h_toNat]
    have h_filter_eq : (Finset.Ioc M M').filter (fun m => g_class m = (k_nat, tag)) =
        (Finset.Ioc M M').filter (fun m => vdc_class (vdc_d t m) δ = (k, tag)) := by
      ext m
      simp only [mem_filter]
      constructor
      · intro ⟨hm1, hm2⟩; exact ⟨hm1, (heq_fiber m hm1).mp hm2⟩
      · intro ⟨hm1, hm2⟩; exact ⟨hm1, (heq_fiber m hm1).mpr hm2⟩
    rw [h_filter_eq]
    exact norm_sum_exp_fiber_subblock_le M M' t hM hMM' hM' ht1 ht_med1 ht_med2 δ rfl k tag
  have h_sum_le : ∑ j ∈ T, ‖∑ m ∈ Finset.Ioc M M' with g_class m = j,
      Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)‖ ≤
      (T.card : ℝ) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) := by
    have h_const : ∑ j ∈ T, ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) =
        (T.card : ℝ) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) := by
      simp only [sum_const, nsmul_eq_mul]
    rw [← h_const]
    exact sum_le_sum h_term_bound
  have h_card_le := card_T_le M t hM ht1
  have h_B_nonneg : 0 ≤ (8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1 := by positivity
  have h_mult_le : (T.card : ℝ) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) ≤
      3 * (t / (2 * Real.pi * (M : ℝ)) + 2) * ((8 * Real.pi + 8) * (M : ℝ) / Real.sqrt t + 1) :=
    mul_le_mul_of_nonneg_right h_card_le h_B_nonneg
  have h_alg := medium_algebra_bound M t hM ht1 ht_med2
  linarith [h_tri, h_sum_le, h_mult_le, h_alg]

/-- Van der Corput second derivative bound for sub-blocks (M, M'] with M < M' ≤ 2 * M. -/
theorem norm_sum_exp_neg_log_mul_I_subblock_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (M M' : ℕ) (t : ℝ), 1 ≤ M → M < M' → M' ≤ 2 * M → 1 ≤ t →
      ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I)‖ ≤
        C * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by
  refine ⟨250, by norm_num, ?_⟩
  intro M M' t hM hMM' hM' ht
  have h_sum_nonneg : 0 ≤ Real.sqrt t + (M : ℝ) / Real.sqrt t := by positivity
  by_cases ht_large : (M : ℝ) ^ 2 ≤ t
  · have h := norm_sum_exp_phase_subblock_of_large_t M M' t hM hMM' hM' ht_large
    calc ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I)‖
      _ ≤ 1 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := h
      _ ≤ 250 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by nlinarith
  · have ht_large' : t < (M : ℝ) ^ 2 := lt_of_not_ge ht_large
    by_cases ht_small : t ≤ Real.pi * (M : ℝ)
    · have h := norm_sum_exp_phase_subblock_of_small_t' M M' t hM hMM' hM' ht ht_small
      have hpi4 := Real.pi_lt_four
      have : 8 * Real.pi + 1 ≤ 250 := by nlinarith [hpi4]
      calc ‖∑ m ∈ Finset.Ioc M M', Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I)‖
        _ ≤ (8 * Real.pi + 1) * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := h
        _ ≤ 250 * (Real.sqrt t + (M : ℝ) / Real.sqrt t) := by nlinarith
    · have ht_small' : Real.pi * (M : ℝ) < t := lt_of_not_ge ht_small
      exact norm_sum_exp_phase_of_medium_t_subblock M M' t hM hMM' hM' ht ht_small' ht_large'

end Erdos1201.MR
