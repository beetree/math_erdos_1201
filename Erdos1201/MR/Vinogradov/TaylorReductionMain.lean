import Mathlib
import Erdos1201.MR.Vinogradov.TaylorReduction

/-!
# Deduction of the Vinogradov Exponential Sum Estimate from the Bilinear Estimate

This module formalizes Terence Tao's deduction of the Vinogradov exponential sum estimate
from the bilinear exponential sum estimate (Notes 5, Section 2, 'Let us see how Theorem 2(ii)
follows from Theorem 11') in the regime $N^{k-1} \le t \le N^k$ with $k \ge 10$.

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

open Real Finset Complex Erdos1201.MR.Vinogradov

noncomputable section

namespace Erdos1201.MR.Vinogradov

/-! ### Part 1: Floor Properties of $M = \lfloor N^{1/4} \rfloor$ -/

/-- For $N \ge 16$, the shift parameter $M = \lfloor N^{1/4} \rfloor$ is at least 2. -/
lemma floor_rpow_quarter_ge_two {N : ℕ} (hN : (16 : ℝ) ≤ (N : ℝ)) :
    2 ≤ Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)) := by
  have hpos : (0 : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by positivity
  rw [Nat.le_floor_iff hpos]
  have h16 : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
    have : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
    rw [this, ← rpow_mul (by norm_num)]
    norm_num
  push_cast
  rw [h16]
  exact rpow_le_rpow (by norm_num) hN (by norm_num)

/-- Upper bound $M \le N^{1/4}$. -/
lemma floor_rpow_quarter_le {N : ℕ} :
    (Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)) : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
  Nat.floor_le (by positivity)

/-- Lower bound $M \ge N^{1/4} / 2$ for $N \ge 16$. -/
lemma floor_rpow_quarter_ge_half {N : ℕ} (hN : (16 : ℝ) ≤ (N : ℝ)) :
    (N : ℝ) ^ (1 / 4 : ℝ) / 2 ≤ (Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)) : ℝ) := by
  have h2 : 2 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    have h16 : (2 : ℝ) = (16 : ℝ) ^ (1 / 4 : ℝ) := by
      have : (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
      rw [this, ← rpow_mul (by norm_num)]
      norm_num
    rw [h16]
    exact rpow_le_rpow (by norm_num) hN (by norm_num)
  have hlt := Nat.lt_floor_add_one ((N : ℝ) ^ (1 / 4 : ℝ))
  linarith

/-- $M^2 \le N$ for all $N \ge 1$. -/
lemma floor_rpow_quarter_sq_le {N : ℕ} (hN : 1 ≤ N) :
    (Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ))) ^ 2 ≤ N := by
  have hM : (Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)) : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Nat.floor_le (by positivity)
  have hsq : (Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)) : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℝ) := by
    have : (Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)) : ℝ) ^ 2 = (Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)) : ℝ) ^ (2 : ℝ) := by
      exact (rpow_two _).symm
    rw [this]
    refine rpow_le_rpow (by positivity) hM (by norm_num)
  have hrew : ((N : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℝ) = (N : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← rpow_mul (by positivity)]
    norm_num
  rw [hrew] at hsq
  have hN1 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) := by
    have : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
    nth_rw 2 [this]
    refine rpow_le_rpow_of_exponent_le ?_ (by norm_num)
    exact_mod_cast hN
  have h_comb : (Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)) : ℝ) ^ 2 ≤ (N : ℝ) := hsq.trans hN1
  exact_mod_cast h_comb

/-! ### Part 2: Bilinear Shift Averaging and Sum Swapping -/

/-- Swapping summation order between dyadic interval and shift parameters. -/
lemma sum_avg_swap (f : ℕ → ℂ) (N M : ℕ) :
    (1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, ∑ n ∈ Ioc N (2 * N), f (n + a * b) =
    ∑ n ∈ Ioc N (2 * N), (1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b) := by
  have h_comm : (∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, ∑ n ∈ Ioc N (2 * N), f (n + a * b)) =
      ∑ n ∈ Ioc N (2 * N), ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b) := by
    simp_rw [sum_comm (s := Icc 1 M) (t := Ioc N (2 * N))]
  rw [h_comm, mul_sum]

/-- Reduction of exponential sum to point-wise bilinear average bounds. -/
lemma norm_sum_le_of_avg_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N M : ℕ)
    (hM : 1 ≤ M) (hMN : M ^ 2 ≤ N) (B : ℝ)
    (hB : ∀ n ∈ Ioc N (2 * N), ‖(1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b)‖ ≤ B) :
    ‖∑ n ∈ Ioc N (2 * N), f n‖ ≤ (N : ℝ) * B + 2 * (M : ℝ) ^ 2 := by
  let A := (1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, ∑ n ∈ Ioc N (2 * N), f (n + a * b)
  have h_diff := norm_sum_sub_avg_sum_shift_le f hf N M hM hMN
  have h_tri : ‖∑ n ∈ Ioc N (2 * N), f n‖ ≤ ‖A‖ + 2 * (M : ℝ) ^ 2 := by
    have := norm_le_norm_sub_add (∑ n ∈ Ioc N (2 * N), f n) A
    linarith
  have hA_swap : A = ∑ n ∈ Ioc N (2 * N), (1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b) :=
    sum_avg_swap f N M
  have hA_norm : ‖A‖ ≤ (N : ℝ) * B := by
    rw [hA_swap]
    refine le_trans (norm_sum_le _ _) ?_
    have h_card : ∑ x ∈ Ioc N (2 * N), B = (N : ℝ) * B := by
      simp only [sum_const, Nat.card_Ioc, nsmul_eq_mul]
      have : 2 * N - N = N := by omega
      rw [this]
    rw [← h_card]
    exact sum_le_sum hB
  linarith

/-! ### Part 3: Selection of Indices for Bilinear Estimate -/

/-- Subset of indices in `Fin (3 * k)` where Taylor coefficients have optimal sizes. -/
def taylor_indices (k : ℕ) : Finset (Fin (3 * k)) :=
  univ.filter fun j : Fin (3 * k) =>
    k + k / 4 ≤ j.val ∧ j.val < k + k / 4 + (k + 9) / 10

/-- Cardinality of `taylor_indices k` is at least $k / 10$. -/
lemma taylor_indices_card (k : ℕ) (hk : 10 ≤ k) :
    (k : ℝ) / 10 ≤ ((taylor_indices k).card : ℝ) := by
  have _h_bound : k + k / 4 + (k + 9) / 10 ≤ 3 * k := by omega
  have h_map : (taylor_indices k).card = (k + 9) / 10 := by
    have h_bij : (taylor_indices k) = (Ico (k + k / 4) (k + k / 4 + (k + 9) / 10)).attach.image
        (fun ⟨n, hn⟩ => ⟨n, by
          rw [mem_Ico] at hn
          omega⟩) := by
      ext ⟨j, hj⟩
      simp only [taylor_indices, mem_filter, mem_univ, true_and, mem_image, mem_attach, true_and,
        Subtype.exists, mem_Ico]
      constructor
      · intro h
        exact ⟨j, h, rfl⟩
      · rintro ⟨n, hn, heq⟩
        injection heq with heq1
        subst heq1
        exact hn
    rw [h_bij, card_image_of_injective]
    · simp only [card_attach, Nat.card_Ico, add_tsub_cancel_left]
    · intro ⟨x, hx⟩ ⟨y, hy⟩ h
      injection h with h1
      exact Subtype.ext h1
  rw [h_map]
  have : (k : ℝ) / 10 ≤ ((k + 9) / 10 : ℕ) := by
    have : k ≤ 10 * ((k + 9) / 10) := by omega
    have h1 : (k : ℝ) ≤ 10 * (((k + 9) / 10 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  exact this

/-- Upper exponent bound for indices in `taylor_indices k`. -/
lemma taylor_index_upper_exponent {k : ℕ} (hk : 10 ≤ k) {j : Fin (3 * k)} (hj : j ∈ taylor_indices k) :
    (k : ℝ) - ((j.val + 1 : ℕ) : ℝ) ≤ - (1 / 120 : ℝ) * ((j.val + 1 : ℕ) : ℝ) := by
  simp only [taylor_indices, mem_filter, mem_univ, true_and] at hj
  have _hj_ge : k + k / 4 + 1 ≤ j.val + 1 := by omega
  have _hj_le : j.val + 1 ≤ k + k / 4 + (k + 9) / 10 := by omega
  have h1 : j.val + 1 ≤ 120 * (j.val + 1 - k) := by
    have : k + k / 4 + (k + 9) / 10 ≤ 120 * (k / 4 + 1) := by omega
    omega
  have h1r : ((j.val + 1 : ℕ) : ℝ) ≤ 120 * (((j.val + 1 - k : ℕ) : ℝ)) := by
    exact_mod_cast h1
  have hk_le : k ≤ j.val + 1 := by omega
  have h_sub : ((j.val + 1 - k : ℕ) : ℝ) = ((j.val + 1 : ℕ) : ℝ) - (k : ℝ) := Nat.cast_sub hk_le
  rw [h_sub] at h1r
  linarith

/-- Lower exponent bound for indices in `taylor_indices k`. -/
lemma taylor_index_lower_exponent {k : ℕ} (hk : 10 ≤ k) {j : Fin (3 * k)} (hj : j ∈ taylor_indices k) :
    (k : ℝ) / 10 ≤ (k : ℝ) - 1 - (61 / 120 : ℝ) * ((j.val + 1 : ℕ) : ℝ) := by
  simp only [taylor_indices, mem_filter, mem_univ, true_and] at hj
  have hj_le : j.val + 1 ≤ k + k / 4 + (k + 9) / 10 := by omega
  have h_k4 : 4 * (k / 4) ≤ k := Nat.mul_div_le k 4
  have h_k4r : 4 * ((k / 4 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h_k4
  have h_k10 : 10 * ((k + 9) / 10) ≤ k + 9 := Nat.mul_div_le (k + 9) 10
  have h_k10r : 10 * (((k + 9) / 10 : ℕ) : ℝ) ≤ (k : ℝ) + 9 := by exact_mod_cast h_k10
  have h_cast : ((j.val + 1 : ℕ) : ℝ) = (j.val : ℝ) + 1 := by push_cast; rfl
  rw [h_cast]
  have h1 : (j.val : ℝ) + 1 ≤ (k : ℝ) + ((k / 4 : ℕ) : ℝ) + (((k + 9) / 10 : ℕ) : ℝ) := by
    have : j.val + 1 ≤ k + k / 4 + (k + 9) / 10 := hj_le
    have h1' : ((j.val + 1 : ℕ) : ℝ) ≤ (((k + k / 4 + (k + 9) / 10 : ℕ) : ℝ)) := by exact_mod_cast this
    push_cast at h1'
    exact h1'
  have hk_real : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

lemma rpow_neg_quarter_le {N M : ℕ} (hN : 2 ≤ N) (hM : 2 ≤ M) (hMN : (M : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ))
    (p : ℝ) (hp : 0 ≤ p) :
    (N : ℝ) ^ (- (p / 4)) ≤ (M : ℝ) ^ (- p) := by
  have hM_pos : (0 : ℝ) < (M : ℝ) := by positivity
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hlogM : Real.log (M : ℝ) ≤ (1 / 4 : ℝ) * Real.log (N : ℝ) := by
    rw [← Real.log_rpow hN_pos]
    exact Real.log_le_log hM_pos hMN
  have h_exp : - (p / 4) * Real.log (N : ℝ) ≤ - p * Real.log (M : ℝ) := by
    have : - (p / 4) * Real.log (N : ℝ) = - p * ((1 / 4 : ℝ) * Real.log (N : ℝ)) := by ring
    rw [this]
    have : - p ≤ 0 := by linarith
    nlinarith
  rw [rpow_def_of_pos hN_pos, rpow_def_of_pos hM_pos]
  have h_exp' : Real.log (N : ℝ) * - (p / 4) ≤ Real.log (M : ℝ) * - p := by
    linarith
  exact Real.exp_le_exp.mpr h_exp'

/-! ### Part 4: Taylor Coefficients and Size Bounds -/

/-- The Taylor coefficient $\alpha_j = -\frac{t}{2\pi} \frac{(-1)^j}{(j+1) n^{j+1}}$. -/
def taylor_coeff (t : ℝ) (n : ℕ) (k : ℕ) (j : Fin (3 * k)) : ℝ :=
  - (t / (2 * Real.pi)) * ((-1 : ℝ) ^ j.val / (((j.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ (j.val + 1)))

lemma abs_taylor_coeff (t : ℝ) (n : ℕ) (k : ℕ) (j : Fin (3 * k))
    (ht : 0 < t) (hn : 0 < n) :
    |taylor_coeff t n k j| = t / (2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ (j.val + 1)) := by
  simp only [taylor_coeff, abs_mul, abs_neg]
  have htpi : |t / (2 * Real.pi)| = t / (2 * Real.pi) := by
    apply abs_of_pos
    positivity
  have hpow : |(-1 : ℝ) ^ j.val| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have hden : |((j.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ (j.val + 1)| = ((j.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ (j.val + 1) := by
    apply abs_of_pos
    positivity
  rw [htpi, abs_div, hpow, hden]
  ring

lemma abs_taylor_coeff_le_rpow_N {t : ℝ} {n N k : ℕ} {j : Fin (3 * k)}
    (ht : t ≤ (N : ℝ) ^ k) (hn : N ≤ n) (hN : 2 ≤ N) (ht_pos : 0 < t) :
    |taylor_coeff t n k j| ≤ (N : ℝ) ^ ((k : ℝ) - ((j.val + 1 : ℕ) : ℝ)) := by
  have hn_pos : 0 < n := by omega
  rw [abs_taylor_coeff t n k j ht_pos hn_pos]
  have hpi : 1 ≤ 2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) := by
    have : 1 ≤ (2 * Real.pi : ℝ) := by
      have : 3 < Real.pi := Real.pi_gt_three
      linarith
    have hj : 1 ≤ ((j.val + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    nlinarith
  have hnN : (N : ℝ) ^ (j.val + 1) ≤ (n : ℝ) ^ (j.val + 1) := by
    have : N ^ (j.val + 1) ≤ n ^ (j.val + 1) := Nat.pow_le_pow_left hn (j.val + 1)
    exact_mod_cast this
  have h_den : (N : ℝ) ^ (j.val + 1) ≤ 2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ (j.val + 1) := by
    have : (N : ℝ) ^ (j.val + 1) = 1 * (N : ℝ) ^ (j.val + 1) := by ring
    rw [this]
    refine mul_le_mul hpi hnN (by positivity) (by positivity)
  have h_div : t / (2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ (j.val + 1)) ≤
      (N : ℝ) ^ k / (N : ℝ) ^ (j.val + 1) := by
    refine div_le_div₀ (by positivity) ht (by positivity) h_den
  refine h_div.trans ?_
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  rw [← rpow_natCast (N : ℝ) k, ← rpow_natCast (N : ℝ) (j.val + 1)]
  rw [← rpow_sub hN_pos]

lemma abs_taylor_coeff_le_M_rpow {t : ℝ} {n N k M : ℕ} {j : Fin (3 * k)}
    (hk : 10 ≤ k) (hN : 2 ≤ N) (hn : N ≤ n) (ht : t ≤ (N : ℝ) ^ k) (ht_pos : 0 < t)
    (hM : 2 ≤ M) (hMN : (M : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ)) (hj : j ∈ taylor_indices k) :
    |taylor_coeff t n k j| ≤ (M : ℝ) ^ (- (1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ)) := by
  have h1 := abs_taylor_coeff_le_rpow_N (j := j) ht hn hN ht_pos
  have h2 := taylor_index_upper_exponent hk hj
  have _hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have h_rpow_le : (N : ℝ) ^ ((k : ℝ) - ((j.val + 1 : ℕ) : ℝ)) ≤
      (N : ℝ) ^ (- (1 / 120 : ℝ) * ((j.val + 1 : ℕ) : ℝ)) := by
    refine rpow_le_rpow_of_exponent_le ?_ h2
    exact_mod_cast (by omega : 1 ≤ N)
  have h3 : (N : ℝ) ^ (- (1 / 120 : ℝ) * ((j.val + 1 : ℕ) : ℝ)) ≤
      (M : ℝ) ^ (- (1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ)) := by
    have hp : 0 ≤ (1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ) := by positivity
    have h_quarter : - ((1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ) / 4) =
        - (1 / 120 : ℝ) * ((j.val + 1 : ℕ) : ℝ) := by ring
    have h_bound := rpow_neg_quarter_le hN hM hMN ((1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ)) hp
    have h_assoc : - ((1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ)) = - (1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ) := by ring
    rw [h_quarter] at h_bound
    rw [h_assoc] at h_bound
    exact h_bound
  exact h1.trans (h_rpow_le.trans h3)

lemma log_abs_taylor_coeff (t : ℝ) (n : ℕ) (k : ℕ) (j : Fin (3 * k))
    (ht : 0 < t) (hn : 0 < n) :
    Real.log (|taylor_coeff t n k j|) =
      Real.log t - Real.log (2 * Real.pi) - Real.log ((j.val + 1 : ℕ) : ℝ) - ((j.val + 1 : ℕ) : ℝ) * Real.log (n : ℝ) := by
  rw [abs_taylor_coeff t n k j ht hn]
  have hden_pos : 0 < 2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ (j.val + 1) := by positivity
  rw [Real.log_div ht.ne' hden_pos.ne']
  have h1 : 0 < 2 * Real.pi * ((j.val + 1 : ℕ) : ℝ) := by positivity
  have h2 : 0 < (n : ℝ) ^ (j.val + 1) := by positivity
  rw [Real.log_mul h1.ne' h2.ne']
  have hpi : 0 < 2 * Real.pi := by positivity
  have hj : 0 < ((j.val + 1 : ℕ) : ℝ) := by positivity
  rw [Real.log_mul hpi.ne' hj.ne']
  have _hn_pos : 0 < (n : ℝ) := by positivity
  rw [Real.log_pow (n : ℝ) (j.val + 1)]
  push_cast
  ring

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have : (2 : ℝ) ≤ Real.exp 1 := by
    have : (2.7 : ℝ) ≤ Real.exp 1 := by
      linarith [Real.exp_one_gt_d9]
    linarith
  rw [← Real.log_exp 1]
  exact Real.log_le_log (by norm_num) this

lemma log_two_pi_le_eight : Real.log (2 * Real.pi) ≤ 8 := by
  have hpi : 2 * Real.pi ≤ Real.exp 8 := by
    have : Real.pi ≤ 4 := by linarith [Real.pi_le_four]
    have : (2 * Real.pi : ℝ) ≤ 8 := by linarith
    have : (8 : ℝ) ≤ Real.exp 8 := by
      have := Real.add_one_le_exp (8 : ℝ)
      linarith
    linarith
  rw [← Real.log_exp 8]
  exact Real.log_le_log (by positivity) hpi

lemma log_nat_le (n : ℕ) : Real.log (n : ℝ) ≤ (n : ℝ) := by
  by_cases hn : 0 < n
  · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have := Real.log_le_sub_one_of_pos hn_pos
    linarith
  · have : n = 0 := by omega
    subst this
    simp

lemma M_rpow_le_abs_taylor_coeff {t : ℝ} {n N k M : ℕ} {j : Fin (3 * k)}
    (hk : 10 ≤ k) (hN : 16 ≤ N) (hn : n ≤ 2 * N) (hn_pos : 0 < n)
    (ht : (N : ℝ) ^ (k - 1) ≤ t) (ht_pos : 0 < t)
    (hlogN : 100 * (k : ℝ) ^ 2 ≤ Real.log (N : ℝ))
    (hM_ge : (N : ℝ) ^ (1 / 4 : ℝ) / 2 ≤ (M : ℝ)) (hM : 2 ≤ M)
    (hj : j ∈ taylor_indices k) :
    (M : ℝ) ^ (- (2 - 1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ)) ≤ |taylor_coeff t n k j| := by
  have hM_pos : 0 < (M : ℝ) := by positivity
  have hN_pos : 0 < (N : ℝ) := by positivity
  have _hj_pos : 0 < ((j.val + 1 : ℕ) : ℝ) := by positivity
  have hn_pos_r : 0 < (n : ℝ) := by exact_mod_cast hn_pos
  have h_log_abs := log_abs_taylor_coeff t n k j ht_pos hn_pos
  have h_log_t : ((k : ℝ) - 1) * Real.log (N : ℝ) ≤ Real.log t := by
    have hN1 : 0 < (N : ℝ) ^ (k - 1) := by positivity
    have h1 := Real.log_le_log hN1 ht
    rw [Real.log_pow (N : ℝ) (k - 1)] at h1
    have h_sub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have : 1 ≤ k := by omega
      rw [Nat.cast_sub this, Nat.cast_one]
    rw [h_sub] at h1
    linarith
  have h_log_n : Real.log (n : ℝ) ≤ Real.log 2 + Real.log (N : ℝ) := by
    have : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn
    have h1 := Real.log_le_log hn_pos_r this
    rw [Real.log_mul (by norm_num) hN_pos.ne'] at h1
    exact h1
  have h_log_M : (1 / 4 : ℝ) * Real.log (N : ℝ) - Real.log 2 ≤ Real.log (M : ℝ) := by
    have h_div_pos : 0 < (N : ℝ) ^ (1 / 4 : ℝ) / 2 := by positivity
    have h1 := Real.log_le_log h_div_pos hM_ge
    rw [Real.log_div (by positivity) (by norm_num)] at h1
    rw [Real.log_rpow hN_pos] at h1
    exact h1
  have _h_log_two_pi := log_two_pi_le_eight
  have _h_log_j := log_nat_le (j.val + 1)
  have _h_log_two := log_two_le_one
  have _h_idx_low := taylor_index_lower_exponent hk hj
  have _hj_le_3k : ((j.val + 1 : ℕ) : ℝ) ≤ 3 * (k : ℝ) := by
    have : j.val < 3 * k := j.isLt
    have : j.val + 1 ≤ 3 * k := by omega
    exact_mod_cast this
  have _hk_real : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h_exp_order : - (2 - 1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ) * Real.log (M : ℝ) ≤
      Real.log (|taylor_coeff t n k j|) := by
    have h_M_bound : - (2 - 1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ) * Real.log (M : ℝ) ≤
        - (2 - 1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ) * ((1 / 4 : ℝ) * Real.log (N : ℝ) - Real.log 2) := by
      have : - (2 - 1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ) ≤ 0 := by
        have : 0 ≤ (2 - 1 / 30 : ℝ) := by norm_num
        nlinarith
      nlinarith
    refine h_M_bound.trans ?_
    rw [h_log_abs]
    have _h_n_term : - ((j.val + 1 : ℕ) : ℝ) * (Real.log 2 + Real.log (N : ℝ)) ≤
        - ((j.val + 1 : ℕ) : ℝ) * Real.log (n : ℝ) := by nlinarith
    have _h_lin : - (2 - 1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ) * ((1 / 4 : ℝ) * Real.log (N : ℝ) - Real.log 2) ≤
        ((k : ℝ) - 1) * Real.log (N : ℝ) - 8 - ((j.val + 1 : ℕ) : ℝ) - ((j.val + 1 : ℕ) : ℝ) * (Real.log 2 + Real.log (N : ℝ)) := by
      have : (k : ℝ) * 10 ≤ 100 * (k : ℝ) ^ 2 := by nlinarith
      have : (k : ℝ) * 10 ≤ Real.log (N : ℝ) := by linarith
      nlinarith
    linarith
  rw [rpow_def_of_pos hM_pos]
  have ht_coeff_pos : 0 < |taylor_coeff t n k j| := by
    have : taylor_coeff t n k j ≠ 0 := by
      rw [taylor_coeff]
      have : t / (2 * Real.pi) ≠ 0 := by positivity
      have h_pow : (-1 : ℝ) ^ j.val ≠ 0 := by
        intro h
        have := abs_pow (-1 : ℝ) j.val
        rw [h, abs_zero, abs_neg, abs_one, one_pow] at this
        norm_num at this
      have h_den : ((j.val + 1 : ℕ) : ℝ) * (n : ℝ) ^ (j.val + 1) ≠ 0 := by positivity
      exact mul_ne_zero (neg_ne_zero.mpr this) (div_ne_zero h_pow h_den)
    exact abs_pos.mpr this
  rw [← exp_log ht_coeff_pos]
  have h_swap : Real.log (M : ℝ) * (- (2 - 1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ)) =
      - (2 - 1 / 30 : ℝ) * ((j.val + 1 : ℕ) : ℝ) * Real.log (M : ℝ) := by ring
  rw [h_swap]
  exact exp_le_exp.mpr h_exp_order

/-! ### Part 5: Exponential Splitting and Taylor Remainder -/

lemma phase_split (t : ℝ) (n : ℕ) (k : ℕ) (α : Fin (3 * k) → ℝ) (a b : ℝ) :
    Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi * (∑ j : Fin (3 * k), α j * a ^ (j.val + 1) * b ^ (j.val + 1)) : ℝ) : ℂ)) =
    Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) *
    Complex.exp (2 * Real.pi * Complex.I * (∑ j : Fin (3 * k), α j * a ^ (j.val + 1) * b ^ (j.val + 1))) := by
  have h_add : Complex.I * ((- t * Real.log n + 2 * Real.pi * (∑ j : Fin (3 * k), α j * a ^ (j.val + 1) * b ^ (j.val + 1)) : ℝ) : ℂ) =
      (-((t * Real.log n : ℝ) : ℂ) * Complex.I) +
      (2 * Real.pi * Complex.I * (∑ j : Fin (3 * k), α j * a ^ (j.val + 1) * b ^ (j.val + 1))) := by
    push_cast
    ring
  rw [h_add, Complex.exp_add]

lemma norm_bilinear_rotated (t : ℝ) (n M k : ℕ) (α : Fin (3 * k) → ℝ) :
    ‖(1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M,
      Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi * (∑ j : Fin (3 * k), α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) : ℝ) : ℂ))‖ =
    ‖(1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M,
      Complex.exp (2 * Real.pi * Complex.I * (∑ j : Fin (3 * k), α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)))‖ := by
  have h_split : ∀ a b : ℕ, Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi * (∑ j : Fin (3 * k), α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) : ℝ) : ℂ)) =
      Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) *
      Complex.exp (2 * Real.pi * Complex.I * (∑ j : Fin (3 * k), α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1))) :=
    fun a b => phase_split t n k α (a : ℝ) (b : ℝ)
  simp_rw [h_split, ← mul_sum]
  have h_factor : (1 / (M : ℂ) ^ 2) * (Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) *
      ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, Complex.exp (2 * Real.pi * Complex.I * (∑ j : Fin (3 * k), α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)))) =
      Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) *
      ((1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, Complex.exp (2 * Real.pi * Complex.I * (∑ j : Fin (3 * k), α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)))) := by
    ring
  rw [h_factor, norm_mul]
  have h_mod1 : ‖Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    have : -((t * Real.log n : ℝ) : ℂ) * Complex.I = Complex.I * (-(t * Real.log n) : ℝ) := by
      push_cast; ring
    rw [this, norm_exp_I_mul_ofReal]
  rw [h_mod1, one_mul]

lemma taylor_phase_eq (t : ℝ) (n : ℕ) (k : ℕ) (a b : ℕ) :
    2 * Real.pi * (∑ j : Fin (3 * k), taylor_coeff t n k j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) =
    - t * ∑ i ∈ range (3 * k), (-1 : ℝ) ^ i * ((a * b : ℝ) / (n : ℝ)) ^ (i + 1) / ((i : ℝ) + 1) := by
  have _hpi : 2 * Real.pi ≠ 0 := by positivity
  rw [mul_sum, mul_sum]
  rw [← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl (fun j _ => ?_)
  simp only [taylor_coeff]
  rw [mul_assoc (- (t / (2 * Real.pi)) * _)]
  rw [← mul_pow]
  have hab_cast : (a : ℝ) * (b : ℝ) = (a * b : ℝ) := by rfl
  rw [hab_cast]
  have h_div : ((a * b : ℝ) / (n : ℝ)) ^ (j.val + 1) = ((a * b : ℝ)) ^ (j.val + 1) / (n : ℝ) ^ (j.val + 1) :=
    div_pow _ _ _
  rw [h_div]
  have hj_cast : ((j.val + 1 : ℕ) : ℝ) = (j.val : ℝ) + 1 := by push_cast; rfl
  rw [hj_cast]
  field_simp

lemma taylor_remainder_bound (n : ℕ) (a b : ℕ) (k : ℕ) (N : ℕ)
    (hN : 16 ≤ N) (hn : N ≤ n) (ha : a ≤ Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)))
    (hb : b ≤ Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ))) :
    |Real.log ((n : ℝ) + (a * b : ℝ)) - Real.log (n : ℝ) -
      ∑ i ∈ range (3 * k), (-1 : ℝ) ^ i * ((a * b : ℝ) / (n : ℝ)) ^ (i + 1) / ((i : ℝ) + 1)| ≤
      2 * ((N : ℝ) ^ (- (1 / 2 : ℝ))) ^ (3 * k + 1) := by
  let M := Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ))
  have hM_le : (M : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := Nat.floor_le (by positivity)
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hab_le : (a * b : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    have ha_r : (a : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      exact le_trans (by exact_mod_cast ha) hM_le
    have hb_r : (b : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
      exact le_trans (by exact_mod_cast hb) hM_le
    have : (a * b : ℝ) = (a : ℝ) * (b : ℝ) := by rfl
    rw [this]
    have h_prod : (a : ℝ) * (b : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ) :=
      mul_le_mul ha_r hb_r (by positivity) (by positivity)
    refine h_prod.trans ?_
    rw [← rpow_add hN_pos]
    have : (1 / 4 : ℝ) + 1 / 4 = 1 / 2 := by norm_num
    rw [this]
  have _hN12_lt_N : (N : ℝ) ^ (1 / 2 : ℝ) < (N : ℝ) := by
    have : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
    nth_rw 2 [this]
    refine rpow_lt_rpow_of_exponent_lt ?_ (by norm_num)
    exact_mod_cast (by omega : 1 < N)
  have hab_lt_n : (a * b : ℝ) < (n : ℝ) := by
    have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hab_div_le : (a * b : ℝ) / (n : ℝ) ≤ (N : ℝ) ^ (- (1 / 2 : ℝ)) := by
    have h1 : (a * b : ℝ) / (n : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / (N : ℝ) := by
      refine div_le_div₀ (by positivity) hab_le (by positivity) (by exact_mod_cast hn)
    refine h1.trans ?_
    have hN1 : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
    nth_rw 2 [hN1]
    rw [← rpow_sub hN_pos]
    have : (1 / 2 : ℝ) - 1 = - (1 / 2 : ℝ) := by norm_num
    rw [this]
  have _hN_half_le : (N : ℝ) ^ (- (1 / 2 : ℝ)) ≤ 1 / 2 := by
    have h16 : (16 : ℝ) ^ (- (1 / 2 : ℝ)) = 1 / 4 := by
      have : (16 : ℝ) = (4 : ℝ) ^ (2 : ℝ) := by norm_num
      rw [this, ← rpow_mul (by norm_num)]
      norm_num
    have h_mono : (N : ℝ) ^ (- (1 / 2 : ℝ)) ≤ (16 : ℝ) ^ (- (1 / 2 : ℝ)) := by
      refine rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hN) (by norm_num)
    linarith
  have _hab_div_lt_one : (a * b : ℝ) / (n : ℝ) < 1 := by
    linarith
  have h_taylor := abs_log_add_sub_log_sub_sum_le hn_pos (by positivity) hab_lt_n (3 * k)
  refine h_taylor.trans ?_
  have h_denom : 1 / 2 ≤ 1 - (a * b : ℝ) / (n : ℝ) := by
    linarith
  have h_pow_le : ((a * b : ℝ) / (n : ℝ)) ^ (3 * k + 1) ≤ ((N : ℝ) ^ (- (1 / 2 : ℝ))) ^ (3 * k + 1) :=
    pow_le_pow_left₀ (by positivity) hab_div_le _
  have h_div_bound : ((a * b : ℝ) / (n : ℝ)) ^ (3 * k + 1) / (1 - (a * b : ℝ) / (n : ℝ)) ≤
      ((N : ℝ) ^ (- (1 / 2 : ℝ))) ^ (3 * k + 1) / (1 / 2) := by
    refine div_le_div₀ (by positivity) h_pow_le (by norm_num) h_denom
  have h_half : ((N : ℝ) ^ (- (1 / 2 : ℝ))) ^ (3 * k + 1) / (1 / 2) =
      2 * ((N : ℝ) ^ (- (1 / 2 : ℝ))) ^ (3 * k + 1) := by ring
  rw [h_half] at h_div_bound
  exact h_div_bound

lemma rpow_neg_k_plus_one_div_two_le_half {N k : ℕ} (hN : 2 ≤ N) (hk : 10 ≤ k) :
    (N : ℝ) ^ (- ((k + 1 : ℝ) / 2)) ≤ 1 / 2 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hk1 : (1 : ℝ) ≤ (k + 1 : ℝ) / 2 := by
    have : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have h_exp : (N : ℝ) ^ (1 : ℝ) ≤ (N : ℝ) ^ ((k + 1 : ℝ) / 2) := by
    refine rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) hk1
  rw [rpow_one] at h_exp
  have h2_le : (2 : ℝ) ≤ (N : ℝ) ^ ((k + 1 : ℝ) / 2) := hN2.trans h_exp
  have h_inv : ((N : ℝ) ^ ((k + 1 : ℝ) / 2))⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [inv_eq_one_div]
    refine one_div_le_one_div_of_le (by positivity) h2_le
  rw [inv_eq_one_div] at h_inv
  rw [rpow_neg hN_pos.le, inv_eq_one_div]
  exact h_inv

lemma single_shift_error_le (t : ℝ) (n k N a b : ℕ)
    (h16_N : 16 ≤ N) (hnN : N ≤ n) (ha : a ≤ Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)))
    (hb : b ≤ Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ))) (ht_pos : 0 < t) (ht2 : t ≤ (N : ℝ) ^ k)
    (hk : 10 ≤ k) (c : ℝ) (hc : 0 < c) (hc_le : c ≤ 1 / 4) :
    ‖Complex.exp (-((t * Real.log (n + a * b : ℕ) : ℝ) : ℂ) * Complex.I) -
      Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi *
        (∑ j : Fin (3 * k), taylor_coeff t n k j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) : ℝ) : ℂ))‖ ≤
      4 * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by
  have hN_pos : 0 < (N : ℝ) := by positivity
  have h_taylor := taylor_remainder_bound n a b k N h16_N hnN ha hb
  have h_phase := taylor_phase_eq t n k a b
  let θ₁ := - t * Real.log (n + a * b : ℕ)
  let θ₂ := - t * Real.log n + 2 * Real.pi * (∑ j : Fin (3 * k), taylor_coeff t n k j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1))
  have h_f_eq : Complex.exp (-((t * Real.log (n + a * b : ℕ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * (θ₁ : ℂ)) := by
    congr 1
    have : -((t * Real.log (n + a * b : ℕ) : ℝ) : ℂ) * Complex.I = Complex.I * (θ₁ : ℝ) := by
      dsimp [θ₁]; push_cast; ring
    rw [this]
  rw [h_f_eq]
  have h_diff_eq : θ₁ - θ₂ = - t * (Real.log ((n : ℝ) + (a * b : ℝ)) - Real.log (n : ℝ) -
      ∑ i ∈ range (3 * k), (-1 : ℝ) ^ i * ((a * b : ℝ) / (n : ℝ)) ^ (i + 1) / ((i : ℝ) + 1)) := by
    dsimp [θ₁, θ₂]
    rw [h_phase]
    push_cast
    ring
  have h_diff_le : |θ₁ - θ₂| ≤ 2 * t * ((N : ℝ) ^ (- (1 / 2 : ℝ))) ^ (3 * k + 1) := by
    rw [h_diff_eq, abs_mul, abs_neg, abs_of_pos ht_pos]
    have := mul_le_mul_of_nonneg_left h_taylor ht_pos.le
    linarith
  have h_pow_rew : ((N : ℝ) ^ (- (1 / 2 : ℝ))) ^ (3 * k + 1) = (N : ℝ) ^ (- ((3 * k + 1 : ℝ) / 2)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN_pos.le]
    congr 1
    push_cast
    ring
  rw [h_pow_rew] at h_diff_le
  have h_prod_le : 2 * t * (N : ℝ) ^ (- ((3 * k + 1 : ℝ) / 2)) ≤ 2 * (N : ℝ) ^ (- ((k + 1 : ℝ) / 2)) := by
    have h1 : 2 * t * (N : ℝ) ^ (- ((3 * k + 1 : ℝ) / 2)) ≤ 2 * (N : ℝ) ^ k * (N : ℝ) ^ (- ((3 * k + 1 : ℝ) / 2)) := by
      have : t * (N : ℝ) ^ (- ((3 * k + 1 : ℝ) / 2)) ≤ (N : ℝ) ^ k * (N : ℝ) ^ (- ((3 * k + 1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_right ht2 (by positivity)
      linarith
    refine h1.trans ?_
    rw [mul_assoc]
    rw [← Real.rpow_natCast (N : ℝ) k]
    rw [← Real.rpow_add hN_pos]
    have : (k : ℝ) + - ((3 * k + 1 : ℝ) / 2) = - ((k + 1 : ℝ) / 2) := by ring
    rw [this]
  have h2N : 2 ≤ N := by omega
  have h_half := rpow_neg_k_plus_one_div_two_le_half h2N hk
  have h_diff_le_one : |θ₁ - θ₂| ≤ 1 := by
    linarith [h_diff_le, h_prod_le, h_half]
  have h_lip := norm_exp_I_mul_sub_exp_I_mul_le h_diff_le_one
  refine h_lip.trans ?_
  have h_final_step : 2 * |θ₁ - θ₂| ≤ 4 * (N : ℝ) ^ (- ((k + 1 : ℝ) / 2)) := by
    linarith [h_diff_le, h_prod_le]
  have h_exp_comp : (N : ℝ) ^ (- ((k + 1 : ℝ) / 2)) ≤ (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by
    refine rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) ?_
    have _hk_r : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have _hk2 : 1 ≤ (k : ℝ) ^ 2 := by nlinarith
    have h_c_le : c / (k : ℝ) ^ 2 ≤ 1 / 4 := by
      have : c / (k : ℝ) ^ 2 ≤ c / 1 := by
        refine div_le_div₀ hc.le (by linarith) (by norm_num) (by nlinarith)
      have : c / 1 = c := by ring
      linarith
    have h_k_ge : (k + 1 : ℝ) / 2 ≥ 11 / 2 := by linarith
    have : - c / (k : ℝ) ^ 2 = - (c / (k : ℝ) ^ 2) := by ring
    rw [this]
    linarith
  linarith [h_final_step, h_exp_comp]

lemma bilinear_avg_diff_le (t : ℝ) (n k N M : ℕ)
    (h16_N : 16 ≤ N) (hnN : N ≤ n) (hM_two : 2 ≤ M)
    (hM_le : (M : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ))
    (ht_pos : 0 < t) (ht2 : t ≤ (N : ℝ) ^ k) (hk : 10 ≤ k)
    (c : ℝ) (hc : 0 < c) (hc_le : c ≤ 1 / 4) :
    ‖(1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M,
      (Complex.exp (-((t * Real.log (n + a * b : ℕ) : ℝ) : ℂ) * Complex.I) -
       Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi *
         (∑ j : Fin (3 * k), taylor_coeff t n k j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) : ℝ) : ℂ)))‖ ≤
      4 * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by
  have hM_card : (Icc 1 M).card = M := Nat.card_Icc 1 M
  have h_norm_div : ‖(1 / (M : ℂ) ^ 2)‖ = 1 / (M : ℝ) ^ 2 := by
    rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
  rw [norm_mul, h_norm_div]
  have h_sum_le : ‖∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M,
      (Complex.exp (-((t * Real.log (n + a * b : ℕ) : ℝ) : ℂ) * Complex.I) -
       Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi *
         (∑ j : Fin (3 * k), taylor_coeff t n k j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) : ℝ) : ℂ)))‖ ≤
      (M : ℝ) ^ 2 * (4 * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) := by
    refine le_trans (norm_sum_le _ _) ?_
    have h1 : ∑ a ∈ Icc 1 M, ‖∑ b ∈ Icc 1 M,
        (Complex.exp (-((t * Real.log (n + a * b : ℕ) : ℝ) : ℂ) * Complex.I) -
         Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi *
           (∑ j : Fin (3 * k), taylor_coeff t n k j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) : ℝ) : ℂ)))‖ ≤
        ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, (4 * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) := by
      refine sum_le_sum (fun a ha => ?_)
      refine le_trans (norm_sum_le _ _) ?_
      exact sum_le_sum (fun b hb => by
        simp only [mem_Icc] at ha hb
        have ha_le : (a : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := le_trans (by exact_mod_cast ha.2) hM_le
        have hb_le : (b : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := le_trans (by exact_mod_cast hb.2) hM_le
        have ha_floor : a ≤ Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)) := by
          rw [Nat.le_floor_iff (by positivity)]
          exact ha_le
        have hb_floor : b ≤ Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ)) := by
          rw [Nat.le_floor_iff (by positivity)]
          exact hb_le
        exact single_shift_error_le t n k N a b h16_N hnN ha_floor hb_floor ht_pos ht2 hk c hc hc_le)
    refine le_trans h1 ?_
    simp only [sum_const, hM_card, nsmul_eq_mul]
    have : (M : ℝ) * ((M : ℝ) * (4 * (N : ℝ) ^ (- c / (k : ℝ) ^ 2))) =
        (M : ℝ) ^ 2 * (4 * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) := by ring
    rw [this]
  have hM_ne : (M : ℝ) ≠ 0 := by positivity
  have : 1 / (M : ℝ) ^ 2 * ((M : ℝ) ^ 2 * (4 * (N : ℝ) ^ (- c / (k : ℝ) ^ 2))) =
      4 * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by
    rw [← mul_assoc, one_div_mul_cancel (pow_ne_zero 2 hM_ne), one_mul]
  refine le_trans (mul_le_mul_of_nonneg_left h_sum_le (by positivity)) ?_
  rw [this]

lemma bilinear_inner_bound (t : ℝ) (n k N M : ℕ) (c₁ C₁ : ℝ)
    (hc₁ : 0 < c₁) (hC₁ : 0 < C₁)
    (h_bilin : ∀ (k M : ℕ) (α : Fin k → ℝ), 1 ≤ k → 2 ≤ M →
      (1 / 30 : ℝ) * (k : ℝ) ≤ ((univ.filter fun j : Fin k =>
        (M : ℝ) ^ (-(2 - 1 / 30 : ℝ) * (j.val + 1)) ≤ |α j| ∧
        |α j| ≤ (M : ℝ) ^ (-(1 / 30 : ℝ) * (j.val + 1))).card : ℝ) →
      ‖(1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M,
        Complex.exp (2 * Real.pi * Complex.I * (∑ j : Fin k, α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)))‖ ≤
        C₁ * (M : ℝ) ^ (-c₁ / (k : ℝ) ^ 2))
    (h16_N : 16 ≤ N) (hn : N < n ∧ n ≤ 2 * N) (ht1 : (N : ℝ) ^ (k - 1) ≤ t) (ht2 : t ≤ (N : ℝ) ^ k)
    (ht_pos : 0 < t) (hk : 10 ≤ k) (hlogN : 100 * (k : ℝ) ^ 2 ≤ Real.log (N : ℝ))
    (hM_two : 2 ≤ M) (hM_le : (M : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ)) (hM_ge : (N : ℝ) ^ (1 / 4 : ℝ) / 2 ≤ (M : ℝ))
    (c : ℝ) (hc_le_c1 : c ≤ c₁ / 36) :
    ‖(1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M,
      Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi *
        (∑ j : Fin (3 * k), taylor_coeff t n k j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) : ℝ) : ℂ))‖ ≤
      (C₁ * (2 : ℝ) ^ c₁) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  let α := taylor_coeff t n k
  have h_bilin_cond : ((1 / 30 : ℝ) * (3 * k : ℕ) ≤
      ((univ.filter fun j : Fin (3 * k) =>
        (M : ℝ) ^ (-(2 - 1 / 30 : ℝ) * (j.val + 1)) ≤ |α j| ∧
        |α j| ≤ (M : ℝ) ^ (-(1 / 30 : ℝ) * (j.val + 1))).card : ℝ)) := by
    have h_sub : taylor_indices k ⊆ univ.filter fun j : Fin (3 * k) =>
        (M : ℝ) ^ (-(2 - 1 / 30 : ℝ) * (j.val + 1)) ≤ |α j| ∧
        |α j| ≤ (M : ℝ) ^ (-(1 / 30 : ℝ) * (j.val + 1)) := by
      intro j hj
      simp only [mem_filter, mem_univ, true_and]
      have hn_pos : 0 < n := by omega
      have h_low := M_rpow_le_abs_taylor_coeff hk h16_N hn.2 hn_pos ht1 ht_pos hlogN hM_ge hM_two hj
      have h_up := abs_taylor_coeff_le_M_rpow hk (by omega) hn.1.le ht2 ht_pos hM_two hM_le hj
      have hj_cast : ((j.val + 1 : ℕ) : ℝ) = (j.val : ℝ) + 1 := by push_cast; rfl
      rw [hj_cast] at h_low h_up
      exact ⟨h_low, h_up⟩
    have h_card_le : ((taylor_indices k).card : ℝ) ≤
        ((univ.filter fun j : Fin (3 * k) =>
          (M : ℝ) ^ (-(2 - 1 / 30 : ℝ) * (j.val + 1)) ≤ |α j| ∧
          |α j| ≤ (M : ℝ) ^ (-(1 / 30 : ℝ) * (j.val + 1))).card : ℝ) := by
      exact_mod_cast card_le_card h_sub
    have h_card_idx := taylor_indices_card k hk
    have : (1 / 30 : ℝ) * (3 * k : ℕ) = (k : ℝ) / 10 := by
      push_cast; ring
    rw [this]
    exact h_card_idx.trans h_card_le
  have h_bilin_res := h_bilin (3 * k) M α (by omega) hM_two h_bilin_cond
  have h_rot := norm_bilinear_rotated t n M k α
  have h_bilin_rot : ‖(1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M,
      Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi * (∑ j : Fin (3 * k), α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) : ℝ) : ℂ))‖ ≤
      C₁ * (M : ℝ) ^ (-c₁ / ((3 * k : ℕ) : ℝ) ^ 2) := by
    rw [h_rot]
    exact h_bilin_res
  have h_M_pow : (M : ℝ) ^ (-c₁ / ((3 * k : ℕ) : ℝ) ^ 2) ≤
      (2 : ℝ) ^ c₁ * (N : ℝ) ^ (-c / (k : ℝ) ^ 2) := by
    have h3k : ((3 * k : ℕ) : ℝ) ^ 2 = 9 * (k : ℝ) ^ 2 := by
      push_cast; ring
    rw [h3k, neg_div]
    have h_div_pos : 0 < (N : ℝ) ^ (1 / 4 : ℝ) / 2 := by positivity
    have h_M_le_exp : (M : ℝ) ^ (- (c₁ / (9 * (k : ℝ) ^ 2))) ≤
        ((N : ℝ) ^ (1 / 4 : ℝ) / 2) ^ (- (c₁ / (9 * (k : ℝ) ^ 2))) := by
      refine rpow_le_rpow_of_nonpos h_div_pos hM_ge ?_
      have : 0 < c₁ / (9 * (k : ℝ) ^ 2) := by positivity
      linarith
    refine h_M_le_exp.trans ?_
    rw [Real.div_rpow (by positivity) (by norm_num)]
    rw [← Real.rpow_mul hN_pos.le]
    have h_exp_eq : (1 / 4 : ℝ) * (- (c₁ / (9 * (k : ℝ) ^ 2))) = - (c₁ / 36) / (k : ℝ) ^ 2 := by
      ring
    rw [h_exp_eq]
    have h_two_rpow : (2 : ℝ) ^ (- (c₁ / (9 * (k : ℝ) ^ 2))) = ((2 : ℝ) ^ (c₁ / (9 * (k : ℝ) ^ 2)))⁻¹ := by
      rw [rpow_neg (by norm_num)]
    rw [h_two_rpow]
    have h_div_inv : (N : ℝ) ^ (- (c₁ / 36) / (k : ℝ) ^ 2) / ((2 : ℝ) ^ (c₁ / (9 * (k : ℝ) ^ 2)))⁻¹ =
        (2 : ℝ) ^ (c₁ / (9 * (k : ℝ) ^ 2)) * (N : ℝ) ^ (- (c₁ / 36) / (k : ℝ) ^ 2) := by
      rw [div_inv_eq_mul, mul_comm]
    rw [h_div_inv]
    have h2_le : (2 : ℝ) ^ (c₁ / (9 * (k : ℝ) ^ 2)) ≤ (2 : ℝ) ^ c₁ := by
      refine rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hk10 : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have : (1 : ℝ) ≤ 9 * (k : ℝ) ^ 2 := by nlinarith
      have : c₁ / (9 * (k : ℝ) ^ 2) ≤ c₁ / 1 := by
        refine div_le_div₀ hc₁.le (by linarith) (by norm_num) (by nlinarith)
      linarith
    have hN_pow_le : (N : ℝ) ^ (- (c₁ / 36) / (k : ℝ) ^ 2) ≤ (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by
      refine rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) ?_
      have hk2_pos : 0 < (k : ℝ) ^ 2 := by positivity
      have : - (c₁ / 36) / (k : ℝ) ^ 2 = - ((c₁ / 36) / (k : ℝ) ^ 2) := by ring
      rw [this]
      have : - c / (k : ℝ) ^ 2 = - (c / (k : ℝ) ^ 2) := by ring
      rw [this]
      rw [neg_le_neg_iff]
      rw [div_le_div_iff_of_pos_right hk2_pos]
      exact hc_le_c1
    exact mul_le_mul h2_le hN_pow_le (by positivity) (by positivity)
  refine h_bilin_rot.trans ?_
  have : C₁ * (M : ℝ) ^ (-c₁ / ((3 * k : ℕ) : ℝ) ^ 2) ≤ (C₁ * (2 : ℝ) ^ c₁) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by
    calc C₁ * (M : ℝ) ^ (-c₁ / ((3 * k : ℕ) : ℝ) ^ 2)
      _ ≤ C₁ * ((2 : ℝ) ^ c₁ * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left h_M_pow hC₁.le
      _ = (C₁ * (2 : ℝ) ^ c₁) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by ring
  exact this

/-! ### Part 6: Main Theorem -/

/-- Terence Tao's deduction of the Vinogradov exponential sum estimate from the
bilinear estimate (Notes 5, Section 2). -/
theorem vinogradov_expsum_regime_of_bilinear (h : BilinearEstimate (1 / 30)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N k : ℕ) (t : ℝ), 2 ≤ N → 10 ≤ k → (N : ℝ) ^ (k - 1) ≤ t → t ≤ (N : ℝ) ^ k →
      ‖∑ n ∈ Finset.Ioc N (2 * N), Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ C * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  rcases h with ⟨c₁, C₁, hc₁, hC₁, h_bilin⟩
  let c := min (c₁ / 36) (1 / 4 : ℝ)
  have hc : 0 < c := lt_min (by linarith) (by norm_num)
  let C₀ : ℝ := 100
  have _hC₀ : 0 < C₀ := by norm_num
  let C₂ : ℝ := C₁ * (2 : ℝ) ^ c₁ + 6
  have _hC₂ : 0 < C₂ := by
    have : 0 < (2 : ℝ) ^ c₁ := rpow_pos_of_pos (by norm_num) c₁
    positivity
  let C := max (Real.exp (c * C₀)) C₂
  have hC : 0 < C := lt_max_of_lt_left (Real.exp_pos _)
  use c, C, hc, hC
  intro N k t hN hk ht1 ht2
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have ht_pos : (0 : ℝ) < t := by
    have : 0 < (N : ℝ) ^ (k - 1) := by positivity
    linarith
  by_cases h_regime : (N : ℝ) ≤ Real.exp (C₀ * (k : ℝ) ^ 2)
  · have hcC : Real.exp (c * C₀) ≤ C := le_max_left _ _
    exact trivial_bound_le_of_le_exp N k t c C₀ C hN (by omega) hc h_regime hcC
  · have h_regime' : Real.exp (C₀ * (k : ℝ) ^ 2) < (N : ℝ) := not_le.mp h_regime
    have hlogN : C₀ * (k : ℝ) ^ 2 ≤ Real.log (N : ℝ) := by
      rw [← Real.log_exp (C₀ * (k : ℝ) ^ 2)]
      exact (Real.log_lt_log (Real.exp_pos _) h_regime').le
    have _hk_10 : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have _hk2_100 : (100 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
    have h16_N : 16 ≤ N := by
      have : Real.exp (C₀ * 100) ≤ (N : ℝ) := by
        refine le_trans ?_ h_regime'.le
        exact Real.exp_le_exp.mpr (by nlinarith)
      have : (16 : ℝ) ≤ Real.exp (C₀ * 100) := by
        have : (16 : ℝ) ≤ Real.exp 4 := by
          have : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
          have h27 : (16 : ℝ) ≤ (2.7 : ℝ) ^ 4 := by norm_num
          have hexp4 : (Real.exp 1) ^ 4 = Real.exp 4 := by
            rw [← Real.exp_nat_mul]
            norm_num
          rw [← hexp4]
          exact le_trans h27 (pow_le_pow_left₀ (by norm_num) this 4)
        refine le_trans this ?_
        exact Real.exp_le_exp.mpr (by norm_num)
      exact_mod_cast (by linarith : (16 : ℝ) ≤ (N : ℝ))
    let M := Nat.floor ((N : ℝ) ^ (1 / 4 : ℝ))
    have hM_two : 2 ≤ M := floor_rpow_quarter_ge_two (by exact_mod_cast h16_N)
    have hM_one : 1 ≤ M := by omega
    have hMN : M ^ 2 ≤ N := floor_rpow_quarter_sq_le (by omega)
    have hM_le : (M : ℝ) ≤ (N : ℝ) ^ (1 / 4 : ℝ) := floor_rpow_quarter_le
    have hM_ge : (N : ℝ) ^ (1 / 4 : ℝ) / 2 ≤ (M : ℝ) := floor_rpow_quarter_ge_half (by exact_mod_cast h16_N)
    let f := fun m : ℕ => Complex.exp (-((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)
    have hf : ∀ n, ‖f n‖ ≤ 1 := fun n => by
      simp only [f]
      exact (norm_exp_neg_log_mul_I t n).le
    have h_inner_bound : ∀ n ∈ Ioc N (2 * N),
        ‖(1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b)‖ ≤
          (C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by
      intro n hn
      rw [mem_Ioc] at hn
      let g := fun a b : ℕ => Complex.exp (Complex.I * ((- t * Real.log n + 2 * Real.pi *
        (∑ j : Fin (3 * k), taylor_coeff t n k j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1)) : ℝ) : ℂ))
      have h_term1_le := bilinear_inner_bound t n k N M c₁ C₁ hc₁ hC₁ h_bilin h16_N hn ht1 ht2 ht_pos hk hlogN hM_two hM_le hM_ge c (min_le_left _ _)
      have h_diff_avg := bilinear_avg_diff_le t n k N M h16_N hn.1.le hM_two hM_le ht_pos ht2 hk c hc (min_le_right _ _)
      have h_decomp : (1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, f (n + a * b) =
          ((1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, g a b) +
          (1 / (M : ℂ) ^ 2) * ∑ a ∈ Icc 1 M, ∑ b ∈ Icc 1 M, (f (n + a * b) - g a b) := by
        rw [← mul_add, ← sum_add_distrib]
        refine congr_arg _ (sum_congr rfl fun a _ => ?_)
        rw [← sum_add_distrib]
        refine sum_congr rfl fun b _ => ?_
        ring
      rw [h_decomp]
      refine le_trans (norm_add_le _ _) ?_
      have : (C₁ * (2 : ℝ) ^ c₁) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) + 4 * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) =
          (C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2) := by ring
      rw [← this]
      exact add_le_add h_term1_le h_diff_avg
    have h_avg_bound := norm_sum_le_of_avg_bound f hf N M hM_one hMN
        ((C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) h_inner_bound
    refine h_avg_bound.trans ?_
    have h_term1_N : (N : ℝ) * ((C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) =
        (C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      have : (N : ℝ) * ((C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) =
          (C₁ * (2 : ℝ) ^ c₁ + 4) * ((N : ℝ) * (N : ℝ) ^ (- c / (k : ℝ) ^ 2)) := by ring
      rw [this]
      congr 1
      have hN1 : (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
      nth_rw 1 [hN1]
      rw [← rpow_add hN_pos]
      ring_nf
    rw [h_term1_N]
    have h_term2_N : 2 * (M : ℝ) ^ 2 ≤ 2 * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      have hM2 : (M : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
        have : (M : ℝ) ^ 2 ≤ ((N : ℝ) ^ (1 / 4 : ℝ)) ^ (2 : ℝ) := by
          have : (M : ℝ) ^ 2 = (M : ℝ) ^ (2 : ℝ) := (rpow_two _).symm
          rw [this]
          exact rpow_le_rpow (by positivity) hM_le (by norm_num)
        refine this.trans ?_
        rw [← rpow_mul (by positivity)]
        norm_num
      have hN12 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
        refine rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ N)) ?_
        have : c ≤ 1 / 4 := min_le_right _ _
        have : c / (k : ℝ) ^ 2 ≤ 1 / 4 := by
          have : 0 < (k : ℝ) ^ 2 := by positivity
          have : (1 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
          have : c / (k : ℝ) ^ 2 ≤ c / 1 := div_le_div₀ hc.le (by linarith) (by norm_num) (by nlinarith)
          linarith
        linarith
      nlinarith
    have h_sum_terms : (C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) + 2 * (M : ℝ) ^ 2 ≤
        C₂ * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
      have : (C₁ * (2 : ℝ) ^ c₁ + 4) * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) + 2 * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) =
          C₂ * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
        dsimp [C₂]
        ring
      linarith
    refine h_sum_terms.trans ?_
    have hC_ge : C₂ ≤ C := le_max_right _ _
    exact mul_le_mul_of_nonneg_right hC_ge (by positivity)

end Erdos1201.MR.Vinogradov
