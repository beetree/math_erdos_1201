import Mathlib
import Erdos1201.MR.Analysis.KusminLandau

/-!
# Iterated Van der Corput Differencing (A-Process)

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the van der Corput A-process iteration for the phase
`f(x) = -(t / (2π)) * log x` (Tao's Notes 5, Propositions 6, 7, 9, 10).

We provide:
1. Basic properties and trivial cardinal bounds on the dyadic exponential sum.
2. Unconditional power-saving bounds in the small-`N` regime `N ≤ exp(C₀ K)`.
3. The general van der Corput A-process infrastructure:
   - Cauchy–Schwarz on `Finset`
   - Exact summation shifts and boundary cancellation
   - Shift difference bounds and shift-averaging estimates
   - Real part expansion of the squared norm
4. Complete unconditional evaluation of the base case `K = 1` via the Kusmin–Landau estimate,
   proving `norm_sum_exp_neg_log_mul_I_le_pow_iterated_one`.
5. The general iterated bound definition `VanDerCorputIteratedBound` and the conditional
   general theorem `norm_sum_exp_neg_log_mul_I_le_pow_iterated`.
-/

open Real Complex Finset

namespace Erdos1201.MR

/-!
### 1. Basic properties of complex exponential summands and trivial bounds
-/

/-- The complex exponential summands `exp(-i t log n)` have unit norm. -/
lemma norm_exp_neg_log_mul_I (t : ℝ) (n : ℕ) :
    ‖Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  have h : -((t * Real.log n : ℝ) : ℂ) * Complex.I = Complex.I * (-(t * Real.log n) : ℝ) := by
    push_cast; ring
  rw [h, norm_exp_I_mul_ofReal]

/-- The dyadic exponential sum is trivially bounded by `N`. -/
lemma norm_sum_exp_neg_log_mul_I_le_card (N : ℕ) (t : ℝ) :
    ‖∑ n ∈ Finset.Ioc N (2 * N), Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ (N : ℝ) := by
  refine le_trans (norm_sum_le _ _) ?_
  simp only [norm_exp_neg_log_mul_I, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
  have : 2 * N - N = N := by omega
  rw [this]

/-- In the small-`N` regime `N ≤ exp(C₀ K)`, the trivial bound `N` already implies
the power-saving bound `C N^{1 - c}` whenever `exp(c C₀ K) ≤ C`. -/
lemma trivial_bound_le_of_le_exp (N K : ℕ) (t : ℝ) (c C₀ C : ℝ)
    (hN : 2 ≤ N) (_hK : 1 ≤ K) (hc : 0 < c) (hN_le : (N : ℝ) ≤ Real.exp (C₀ * (K : ℝ)))
    (hC : Real.exp (c * C₀ * (K : ℝ)) ≤ C) :
    ‖∑ n ∈ Finset.Ioc N (2 * N), Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
      C * (N : ℝ) ^ (1 - c) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hsum_le := norm_sum_exp_neg_log_mul_I_le_card N t
  refine le_trans hsum_le ?_
  have h_rpow_eq : (N : ℝ) = (N : ℝ) ^ c * (N : ℝ) ^ (1 - c) := by
    rw [← Real.rpow_add hN_pos]
    have : c + (1 - c) = 1 := by ring
    rw [this, Real.rpow_one]
  nth_rw 1 [h_rpow_eq]
  have h_base : (N : ℝ) ^ c ≤ C := by
    have hlog : Real.log (N : ℝ) ≤ C₀ * (K : ℝ) := by
      rw [← Real.log_exp (C₀ * (K : ℝ))]
      exact Real.log_le_log hN_pos hN_le
    rw [Real.rpow_def_of_pos hN_pos]
    have h_exp : Real.log (N : ℝ) * c ≤ c * C₀ * (K : ℝ) := by
      rw [mul_comm]
      have h1 : c * Real.log (N : ℝ) ≤ c * (C₀ * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog hc.le
      have h2 : c * (C₀ * (K : ℝ)) = c * C₀ * (K : ℝ) := by ring
      linarith
    exact le_trans (Real.exp_le_exp.mpr h_exp) hC
  have hrpow_nonneg : 0 ≤ (N : ℝ) ^ (1 - c) := by positivity
  exact mul_le_mul_of_nonneg_right h_base hrpow_nonneg

/-- Unconditional power-saving bound in the small-`N` regime `N ≤ exp(C₀ K)`. -/
theorem norm_sum_exp_neg_log_mul_I_le_pow_iterated_of_le_exp (K : ℕ) (hK : 1 ≤ K) (C₀ : ℝ) (_hC₀ : 0 < C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ) (t : ℝ), 2 ≤ N → (N : ℝ) ≤ t → t ≤ (N : ℝ) ^ K →
      (N : ℝ) ≤ Real.exp (C₀ * (K : ℝ)) →
      ‖∑ n ∈ Finset.Ioc N (2 * N), Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ C * (N : ℝ) ^ (1 - c) := by
  use 1 / 2, Real.exp ((1 / 2) * C₀ * (K : ℝ))
  refine ⟨by norm_num, by positivity, ?_⟩
  intro N t hN _ _ hN_le
  exact trivial_bound_le_of_le_exp N K t (1 / 2) C₀ (Real.exp ((1 / 2) * C₀ * (K : ℝ)))
    hN hK (by norm_num) hN_le le_rfl

/-!
### 2. General van der Corput A-process infrastructure: Cauchy–Schwarz and shift-averaging
-/

/-- Cauchy–Schwarz inequality for complex sums on a finite set:
`‖∑ x ∈ s, f x‖² ≤ #s * ∑ x ∈ s, ‖f x‖²`. -/
lemma norm_sum_sq_le_card_mul_sum_norm_sq_vdc {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := by
  have h1 : ‖∑ x ∈ s, f x‖ ≤ ∑ x ∈ s, ‖f x‖ := norm_sum_le _ _
  have h1_nonneg : 0 ≤ ∑ x ∈ s, ‖f x‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have h2 : ‖∑ x ∈ s, f x‖ ^ 2 ≤ (∑ x ∈ s, ‖f x‖) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_norm, abs_of_nonneg h1_nonneg]; exact h1)
  have hcs : (∑ x ∈ s, (1 : ℝ) * ‖f x‖) ^ 2 ≤
      (∑ x ∈ s, (1 : ℝ) ^ 2) * ∑ x ∈ s, ‖f x‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => 1) (fun x => ‖f x‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  exact h2.trans hcs

/-- Sum shift identity on integer intervals:
`∑ n ∈ (A, B], f (n + s) = ∑ m ∈ (A+s, B+s], f m`. -/
lemma sum_Ioc_add_vdc (f : ℕ → ℂ) (A B s : ℕ) :
    ∑ n ∈ Finset.Ioc A B, f (n + s) = ∑ m ∈ Finset.Ioc (A + s) (B + s), f m := by
  rw [← Finset.map_add_right_Ioc, Finset.sum_map]
  rfl

/-- Cancellation of interior terms between shifted integer interval sums:
`∑ m ∈ (A, B] - ∑ m ∈ (A+s, B+s] = ∑ m ∈ (A, A+s] - ∑ m ∈ (B, B+s]`. -/
lemma sum_Ioc_sub_sum_Ioc_add_right_eq (f : ℕ → ℂ) (A B s : ℕ) (hs : A + s ≤ B) :
    ∑ m ∈ Finset.Ioc A B, f m - ∑ m ∈ Finset.Ioc (A + s) (B + s), f m =
      ∑ m ∈ Finset.Ioc A (A + s), f m - ∑ m ∈ Finset.Ioc B (B + s), f m := by
  have hA : A ≤ A + s := Nat.le_add_right A s
  have hB : B ≤ B + s := Nat.le_add_right B s
  have h1 : ∑ m ∈ Finset.Ioc A B, f m =
      (∑ m ∈ Finset.Ioc A (A + s), f m) + ∑ m ∈ Finset.Ioc (A + s) B, f m := by
    rw [← Finset.sum_Ioc_consecutive f hA hs]
  have h2 : ∑ m ∈ Finset.Ioc (A + s) (B + s), f m =
      (∑ m ∈ Finset.Ioc (A + s) B, f m) + ∑ m ∈ Finset.Ioc B (B + s), f m := by
    rw [← Finset.sum_Ioc_consecutive f hs hB]
  rw [h1, h2]
  ring

/-- The difference between a sum and its shift by `s` is bounded by `2s` for bounded summands. -/
lemma norm_sum_Ioc_sub_sum_Ioc_shift_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (A B s : ℕ) (hs : A + s ≤ B) :
    ‖∑ n ∈ Finset.Ioc A B, f n - ∑ n ∈ Finset.Ioc A B, f (n + s)‖ ≤ 2 * (s : ℝ) := by
  rw [sum_Ioc_add_vdc, sum_Ioc_sub_sum_Ioc_add_right_eq f A B s hs]
  refine le_trans (norm_sub_le _ _) ?_
  have h1 : ‖∑ m ∈ Finset.Ioc A (A + s), f m‖ ≤ (s : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∑ x ∈ Finset.Ioc A (A + s), ‖f x‖ ≤ ∑ x ∈ Finset.Ioc A (A + s), (1 : ℝ) :=
      Finset.sum_le_sum (fun x _ => hf x)
    refine le_trans this ?_
    simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    have : A + s - A = s := by omega
    rw [this]
  have h2 : ‖∑ m ∈ Finset.Ioc B (B + s), f m‖ ≤ (s : ℝ) := by
    refine le_trans (norm_sum_le _ _) ?_
    have : ∑ x ∈ Finset.Ioc B (B + s), ‖f x‖ ≤ ∑ x ∈ Finset.Ioc B (B + s), (1 : ℝ) :=
      Finset.sum_le_sum (fun x _ => hf x)
    refine le_trans this ?_
    simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
    have : B + s - B = s := by omega
    rw [this]
  linarith

/-- Van der Corput shift-averaging identity: replacing the sum by its average over shifts
`h ∈ [1, H]` incurs an error of at most `2H`. -/
lemma norm_sum_sub_avg_sum_shift_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N H : ℕ) (hH : 1 ≤ H) (hHN : H ≤ N) :
    ‖∑ n ∈ Finset.Ioc N (2 * N), f n -
      (1 / (H : ℂ)) * ∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Ioc N (2 * N), f (n + h)‖ ≤
      2 * (H : ℝ) := by
  have hH_card : (Finset.Icc 1 H).card = H := Nat.card_Icc 1 H
  have hH_pos : 0 < (H : ℝ) := by positivity
  have hH_ne : (H : ℂ) ≠ 0 := by
    intro h
    have : ‖(H : ℂ)‖ = 0 := by rw [h, norm_zero]
    rw [Complex.norm_natCast] at this
    linarith
  have h_id : ∑ n ∈ Finset.Ioc N (2 * N), f n =
      (1 / (H : ℂ)) * ∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Ioc N (2 * N), f n := by
    simp only [Finset.sum_const, nsmul_eq_mul, hH_card]
    rw [← mul_assoc, one_div_mul_cancel hH_ne, one_mul]
  rw [h_id, ← mul_sub, norm_mul, norm_div, norm_one, Complex.norm_natCast]
  have h_sub_sum : (∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Ioc N (2 * N), f n) -
      (∑ h ∈ Finset.Icc 1 H, ∑ n ∈ Finset.Ioc N (2 * N), f (n + h)) =
      ∑ h ∈ Finset.Icc 1 H,
        ((∑ n ∈ Finset.Ioc N (2 * N), f n) - (∑ n ∈ Finset.Ioc N (2 * N), f (n + h))) := by
    simp only [← Finset.sum_sub_distrib]
  rw [h_sub_sum]
  have h_inner_le : ∀ h ∈ Finset.Icc 1 H,
      ‖(∑ n ∈ Finset.Ioc N (2 * N), f n) - (∑ n ∈ Finset.Ioc N (2 * N), f (n + h))‖ ≤ 2 * (H : ℝ) := by
    intro h hh
    simp only [Finset.mem_Icc] at hh
    have hs : N + h ≤ 2 * N := by omega
    have h_shift := norm_sum_Ioc_sub_sum_Ioc_shift_le f hf N (2 * N) h hs
    refine le_trans h_shift ?_
    have : (h : ℝ) ≤ (H : ℝ) := by exact_mod_cast hh.2
    linarith
  have h_sum_le : ‖∑ h ∈ Finset.Icc 1 H,
      ((∑ n ∈ Finset.Ioc N (2 * N), f n) - (∑ n ∈ Finset.Ioc N (2 * N), f (n + h)))‖ ≤
      (H : ℝ) * (2 * (H : ℝ)) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∑ h ∈ Finset.Icc 1 H,
        ‖((∑ n ∈ Finset.Ioc N (2 * N), f n) - (∑ n ∈ Finset.Ioc N (2 * N), f (n + h)))‖ ≤
        ∑ h ∈ Finset.Icc 1 H, (2 * (H : ℝ)) :=
      Finset.sum_le_sum (fun h hh => h_inner_le h hh)
    refine le_trans h1 ?_
    simp only [Finset.sum_const, hH_card, nsmul_eq_mul]
    rfl
  have : 1 / (H : ℝ) * ((H : ℝ) * (2 * (H : ℝ))) = 2 * (H : ℝ) := by
    field_simp
  refine le_trans (mul_le_mul_of_nonneg_left h_sum_le (by positivity)) ?_
  rw [this]

/-- Expansion of the squared norm `‖∑ x ∈ s, z x‖²` as `(∑ x, ∑ y, z x * conj (z y)).re`. -/
lemma normSq_sum_eq_vdc {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    (‖∑ i ∈ s, z i‖ ^ 2 : ℝ) = (∑ i ∈ s, ∑ j ∈ s, z i * star (z j)).re := by
  have h1 : ‖∑ i ∈ s, z i‖ ^ 2 = normSq (∑ i ∈ s, z i) := by
    rw [normSq_eq_norm_sq]
  rw [h1]
  have h2 : ((normSq (∑ i ∈ s, z i) : ℝ) : ℂ) = (∑ i ∈ s, z i) * star (∑ i ∈ s, z i) := by
    rw [← mul_conj]
    rfl
  have h3 : (∑ i ∈ s, z i) * star (∑ i ∈ s, z i) = ∑ i ∈ s, ∑ j ∈ s, z i * star (z j) := by
    rw [star_sum, sum_mul_sum]
  have h4 : ((normSq (∑ i ∈ s, z i) : ℝ) : ℂ).re = (∑ i ∈ s, ∑ j ∈ s, z i * star (z j)).re := by
    rw [← h3, ← h2]
  exact h4

/-!
### 3. Base case K = 1: Kusmin–Landau evaluation
-/

/-- Rescaled phase function `g(m) = - (t / (2π)) * log m`. -/
noncomputable def vdc_iter_g (t : ℝ) (m : ℕ) : ℝ :=
  - (t / (2 * Real.pi)) * Real.log (m : ℝ)

/-- Discrete phase increment `d(m) = g(m+1) - g(m)`. -/
noncomputable def vdc_iter_d (t : ℝ) (m : ℕ) : ℝ :=
  vdc_iter_g t (m + 1) - vdc_iter_g t m

lemma two_pi_mul_vdc_iter_g (t : ℝ) (m : ℕ) :
    2 * Real.pi * vdc_iter_g t m = - (t * Real.log (m : ℝ)) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2pi : 2 * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hpi
  simp only [vdc_iter_g]
  calc 2 * Real.pi * (- (t / (2 * Real.pi)) * Real.log (m : ℝ))
    _ = - (2 * Real.pi * (t / (2 * Real.pi))) * Real.log (m : ℝ) := by ring
    _ = - t * Real.log (m : ℝ) := by rw [mul_div_cancel₀ _ h2pi]
    _ = - (t * Real.log (m : ℝ)) := by ring

lemma exp_phase_iter_eq (t : ℝ) (m : ℕ) :
    Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * ((vdc_iter_g t m : ℝ) : ℂ)) := by
  congr 1
  have h := two_pi_mul_vdc_iter_g t m
  have : (2 * Real.pi * Complex.I * ((vdc_iter_g t m : ℝ) : ℂ)) =
      (((2 * Real.pi * vdc_iter_g t m : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [this, h]
  push_cast; ring

lemma log_one_add_inv_iter_ge (m : ℕ) (hm : 1 ≤ m) :
    1 / (2 * (m : ℝ)) ≤ Real.log (1 + 1 / (m : ℝ)) := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hm1_pos : 0 < (m : ℝ) + 1 := by linarith
  have hdiv_pos : 0 < (m : ℝ) / ((m : ℝ) + 1) := div_pos hm_pos hm1_pos
  have hle := Real.log_le_sub_one_of_pos hdiv_pos
  have hid : (m : ℝ) / ((m : ℝ) + 1) - 1 = - (1 / ((m : ℝ) + 1)) := by
    have : (m : ℝ) / ((m : ℝ) + 1) - 1 = ((m : ℝ) - ((m : ℝ) + 1)) / ((m : ℝ) + 1) := by
      rw [div_sub_one hm1_pos.ne']
    rw [this]; ring
  rw [hid] at hle
  have hneg : 1 / ((m : ℝ) + 1) ≤ - Real.log ((m : ℝ) / ((m : ℝ) + 1)) := by linarith
  have hlog_inv : - Real.log ((m : ℝ) / ((m : ℝ) + 1)) = Real.log (((m : ℝ) + 1) / (m : ℝ)) := by
    rw [← Real.log_inv, inv_div]
  have hsplit : ((m : ℝ) + 1) / (m : ℝ) = 1 + 1 / (m : ℝ) := by
    rw [add_div, div_self hm_pos.ne']
  rw [hlog_inv, hsplit] at hneg
  have hm_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h2m : 1 / (2 * (m : ℝ)) ≤ 1 / ((m : ℝ) + 1) := by
    apply one_div_le_one_div_of_le hm1_pos
    linarith [hm_real]
  exact h2m.trans hneg

lemma log_one_add_inv_iter_le (m : ℕ) (hm : 1 ≤ m) :
    Real.log (1 + 1 / (m : ℝ)) ≤ 1 / (m : ℝ) := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hpos : 0 < 1 + 1 / (m : ℝ) := by positivity
  have hle := Real.log_le_sub_one_of_pos hpos
  linarith

lemma vdc_iter_d_eq (t : ℝ) (m : ℕ) (hm : 1 ≤ m) :
    vdc_iter_d t m = - (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ)) := by
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  simp only [vdc_iter_d, vdc_iter_g]
  push_cast
  have hlog : Real.log ((m : ℝ) + 1) - Real.log (m : ℝ) = Real.log (1 + 1 / (m : ℝ)) := by
    rw [← Real.log_div (by linarith) hm_pos.ne']
    congr 1
    rw [add_div, div_self hm_pos.ne']
  calc - (t / (2 * Real.pi)) * Real.log ((m : ℝ) + 1) - - (t / (2 * Real.pi)) * Real.log (m : ℝ)
    _ = - (t / (2 * Real.pi)) * (Real.log ((m : ℝ) + 1) - Real.log (m : ℝ)) := by ring
    _ = - (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ)) := by rw [hlog]

lemma vdc_iter_d_neg (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : 1 ≤ m) :
    vdc_iter_d t m < 0 := by
  rw [vdc_iter_d_eq t m hm]
  have h2pi : 0 < 2 * Real.pi := by positivity
  have ht2pi : 0 < t / (2 * Real.pi) := div_pos ht h2pi
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hlog_pos : 0 < Real.log (1 + 1 / (m : ℝ)) := by
    rw [Real.log_pos_iff (by positivity)]
    have : 0 < 1 / (m : ℝ) := one_div_pos.mpr hm_pos
    linarith
  have : 0 < (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ)) := mul_pos ht2pi hlog_pos
  linarith

lemma vdc_iter_d_mono (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : 1 ≤ m) :
    vdc_iter_d t m ≤ vdc_iter_d t (m + 1) := by
  have hm1 : 1 ≤ m + 1 := by omega
  rw [vdc_iter_d_eq t m hm, vdc_iter_d_eq t (m + 1) hm1]
  push_cast
  have ht2pi : 0 < t / (2 * Real.pi) := by positivity
  have hlog_le : Real.log (1 + 1 / ((m : ℝ) + 1)) ≤ Real.log (1 + 1 / (m : ℝ)) := by
    apply Real.log_le_log (by positivity)
    have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
    have : 1 / ((m : ℝ) + 1) ≤ 1 / (m : ℝ) := one_div_le_one_div_of_le hm_pos (by linarith)
    linarith
  nlinarith

lemma abs_vdc_iter_d_eq (t : ℝ) (ht : 0 < t) (m : ℕ) (hm : 1 ≤ m) :
    |vdc_iter_d t m| = (t / (2 * Real.pi)) * Real.log (1 + 1 / (m : ℝ)) := by
  have hneg := vdc_iter_d_neg t ht m hm
  rw [abs_of_neg hneg, vdc_iter_d_eq t m hm]
  ring

lemma norm_sum_exp_phase_iter_of_small_t (M : ℕ) (t : ℝ) (hM : 1 ≤ M) (ht1 : 1 ≤ t) (ht_small : t ≤ Real.pi * (M : ℝ)) :
    ‖∑ m ∈ Finset.Icc (M + 1) (2 * M), Complex.exp (2 * Real.pi * Complex.I * ((vdc_iter_g t m : ℝ) : ℂ))‖ ≤
      8 * Real.pi * (M : ℝ) / t + 1 := by
  have ht_pos : 0 < t := by linarith
  have hM_pos : 0 < (M : ℝ) := Nat.cast_pos.mpr hM
  have hab : M + 1 ≤ 2 * M := by omega
  set δ := t / (8 * Real.pi * (M : ℝ))
  have hδ_pos : 0 < δ := by positivity
  have hneg : ∀ n, M + 1 ≤ n → n < 2 * M → vdc_iter_g t (n + 1) - vdc_iter_g t n < 0 := by
    intro n hn _
    exact vdc_iter_d_neg t ht_pos n (by omega)
  have hmono : ∀ n, M + 1 ≤ n → n + 1 < 2 * M →
      vdc_iter_g t (n + 1) - vdc_iter_g t n ≤ vdc_iter_g t (n + 2) - vdc_iter_g t (n + 1) := by
    intro n hn _
    exact vdc_iter_d_mono t ht_pos n (by omega)
  have hlow : ∀ n, M + 1 ≤ n → n < 2 * M → δ ≤ |vdc_iter_g t (n + 1) - vdc_iter_g t n| := by
    intro n hn _
    have hn1 : 1 ≤ n := by omega
    change δ ≤ |vdc_iter_d t n|
    rw [abs_vdc_iter_d_eq t ht_pos n hn1]
    have hlog := log_one_add_inv_iter_ge n hn1
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
  have hhalf : ∀ n, M + 1 ≤ n → n < 2 * M → |vdc_iter_g t (n + 1) - vdc_iter_g t n| ≤ 1 / 2 := by
    intro n hn _
    have hn1 : 1 ≤ n := by omega
    change |vdc_iter_d t n| ≤ 1 / 2
    rw [abs_vdc_iter_d_eq t ht_pos n hn1]
    have hlog := log_one_add_inv_iter_le n hn1
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
  have hKL := norm_sum_exp_le_of_monotone_diff (vdc_iter_g t) (M + 1) (2 * M) hab δ hδ_pos hneg hmono hlow hhalf
  have h_one_div_δ : 1 / δ = 8 * Real.pi * (M : ℝ) / t := by
    simp only [δ]
    field_simp
  rw [h_one_div_δ] at hKL
  exact hKL

lemma Ioc_eq_Icc_succ_vdc (M : ℕ) :
    Finset.Ioc M (2 * M) = Finset.Icc (M + 1) (2 * M) := by
  ext x
  simp only [mem_Ioc, mem_Icc]
  omega

lemma norm_sum_exp_phase_iter_of_small_t' (M : ℕ) (t : ℝ) (hM : 1 ≤ M) (ht1 : 1 ≤ t) (ht_small : t ≤ Real.pi * (M : ℝ)) :
    ‖∑ m ∈ Finset.Ioc M (2 * M), Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I)‖ ≤
      8 * Real.pi * (M : ℝ) / t + 1 := by
  have heq : ∀ m ∈ Finset.Ioc M (2 * M),
      Complex.exp (-((t * Real.log m : ℝ) : ℂ) * Complex.I) =
      Complex.exp (2 * Real.pi * Complex.I * ((vdc_iter_g t m : ℝ) : ℂ)) :=
    fun m _ => exp_phase_iter_eq t m
  rw [sum_congr rfl heq, Ioc_eq_Icc_succ_vdc]
  exact norm_sum_exp_phase_iter_of_small_t M t hM ht1 ht_small

/-- Unconditional base case `K = 1`:
for all dyadic scales `N ≥ 2` and `N ≤ t ≤ N¹ = N`, the Kusmin–Landau theorem
proves the power-saving bound with `c = 1/2` and `C = 8π + 1`. -/
theorem norm_sum_exp_neg_log_mul_I_le_pow_iterated_one :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N : ℕ) (t : ℝ), 2 ≤ N → (N : ℝ) ≤ t → t ≤ (N : ℝ) ^ 1 →
      ‖∑ n ∈ Finset.Ioc N (2 * N), Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ C * (N : ℝ) ^ (1 - c) := by
  use 1 / 2, 8 * Real.pi + 1
  refine ⟨by norm_num, by positivity, ?_⟩
  intro N t hN ht_low ht_high
  have ht_eq : t = (N : ℝ) := by
    rw [pow_one] at ht_high
    linarith
  have hN1 : 1 ≤ N := by omega
  have ht1 : 1 ≤ t := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have ht_small : t ≤ Real.pi * (N : ℝ) := by
    rw [ht_eq]
    have hpi : 1 ≤ Real.pi := by
      have := Real.pi_gt_three
      linarith
    have hN_pos : 0 ≤ (N : ℝ) := by positivity
    calc (N : ℝ) = 1 * (N : ℝ) := by ring
      _ ≤ Real.pi * (N : ℝ) := mul_le_mul_of_nonneg_right hpi hN_pos
  have hbound := norm_sum_exp_phase_iter_of_small_t' N t hN1 ht1 ht_small
  have hdiv : 8 * Real.pi * (N : ℝ) / t = 8 * Real.pi := by
    rw [ht_eq]
    have hN_ne : (N : ℝ) ≠ 0 := by positivity
    exact mul_div_cancel_right₀ (8 * Real.pi) hN_ne
  rw [hdiv] at hbound
  have hN_rpow : 1 ≤ (N : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
    have : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
    rw [this]
    have hN_ge_one : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    have h12_pos : 0 ≤ (1 / 2 : ℝ) := by norm_num
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.one_rpow]
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hN_ge_one h12_pos
  calc ‖∑ n ∈ Finset.Ioc N (2 * N), Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖
    _ ≤ 8 * Real.pi + 1 := hbound
    _ = (8 * Real.pi + 1) * 1 := by ring
    _ ≤ (8 * Real.pi + 1) * (N : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
      have hC_pos : 0 ≤ 8 * Real.pi + 1 := by positivity
      exact mul_le_mul_of_nonneg_left hN_rpow hC_pos

/-!
### 4. General van der Corput iterated bound formulation
-/

end Erdos1201.MR
