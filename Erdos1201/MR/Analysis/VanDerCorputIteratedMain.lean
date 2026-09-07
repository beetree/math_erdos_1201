import Mathlib
import Erdos1201.MR.Analysis.WeylDifferencing
import Erdos1201.MR.Analysis.LogIteratedDifferences
import Erdos1201.MR.Analysis.KusminLandau
import Erdos1201.MR.Analysis.VanDerCorput
import Erdos1201.MR.Analysis.VanDerCorputSubblock

/-!
# Iterated Van der Corput Differencing (A-Process)

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the general van der Corput A-process (iterated Weyl differencing)
for the phase `f(x) = -(t / (2π)) * log x` on integer sub-blocks `(N, M]` with `N < M ≤ 2N`.

We provide:
1. The $m$-fold differenced phase function `vdc_phase t m h n` and the corresponding
   differenced exponential sums `vdc_S t m h a b`.
2. The fundamental Weyl differencing recurrence `norm_sq_vdc_S_le_weyl`, reducing
   the squared norm `‖S_m‖²` to the average of `‖S_{m+1}‖`.
3. Shift-vector algebra preserving the component bounds and coordinate products.
4. Consecutive difference identities and sharp upper and lower derivative bounds
   `abs_vdc_consec_diff_bounds` derived from `abs_logIterDiff_bounds`.
5. The complete, unconditional evaluation of the base case `K = 1`
   (`norm_sum_exp_neg_log_mul_I_le_pow_iterated_one_main`) via the Kusmin–Landau estimate.
-/

open Real Complex Finset

namespace Erdos1201.MR

/-!
### 1. General Differenced Phase and Exponential Sums
-/

/-- The $m$-fold differenced phase function `g_h(n) = -(t / (2π)) * logIterDiff m h n`. -/
noncomputable def vdc_phase (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (n : ℕ) : ℝ :=
  - (t / (2 * Real.pi)) * logIterDiff m h (n : ℝ)

/-- Step difference identity: `g_h(n + k) - g_h(n) = g_{(h, k)}(n)`. -/
lemma vdc_phase_diff (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (k : ℕ) (n : ℕ) :
    vdc_phase t m h (n + k) - vdc_phase t m h n =
    vdc_phase t (m + 1) (Fin.snoc h k) n := by
  dsimp [vdc_phase]
  have h_succ := logIterDiff_succ_eq m h k (n : ℝ)
  push_cast
  calc - (t / (2 * Real.pi)) * logIterDiff m h ((n : ℝ) + (k : ℝ)) - - (t / (2 * Real.pi)) * logIterDiff m h (n : ℝ)
    _ = - (t / (2 * Real.pi)) * (logIterDiff m h ((n : ℝ) + (k : ℝ)) - logIterDiff m h (n : ℝ)) := by ring
    _ = - (t / (2 * Real.pi)) * logIterDiff (m + 1) (Fin.snoc h k) (n : ℝ) := by rw [h_succ]

/-- The $m$-fold differenced exponential sum `S_m(I, h) = ∑_{n ∈ (a, b]} e(g_h(n))`. -/
noncomputable def vdc_S (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (a b : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * Complex.I * ((vdc_phase t m h n : ℝ) : ℂ))

/-- At depth 0, `vdc_S` coincides with the original exponential sum `∑ n, exp(-i t log n)`. -/
lemma vdc_S_zero_eq (t : ℝ) (a b : ℕ) :
    vdc_S t 0 (fun x => x.elim0) a b =
    ∑ n ∈ Finset.Ioc a b, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) := by
  dsimp [vdc_S, vdc_phase, logIterDiff]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  have h_cancel : 2 * Real.pi * (- (t / (2 * Real.pi)) * Real.log (n : ℝ)) = -(t * Real.log (n : ℝ)) := by
    calc 2 * Real.pi * (- (t / (2 * Real.pi)) * Real.log (n : ℝ))
      _ = - (2 * Real.pi * (t / (2 * Real.pi))) * Real.log (n : ℝ) := by ring
      _ = - t * Real.log (n : ℝ) := by rw [mul_div_cancel₀ _ hpi]
      _ = -(t * Real.log (n : ℝ)) := by ring
  have : (2 * Real.pi * Complex.I * ((- (t / (2 * Real.pi)) * Real.log (n : ℝ) : ℝ) : ℂ)) =
      (((2 * Real.pi * (- (t / (2 * Real.pi)) * Real.log (n : ℝ))) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, h_cancel]
  push_cast; ring

/-- Van der Corput Weyl differencing step: bounds `‖S_m‖²` in terms of `S_{m+1}`. -/
theorem norm_sq_vdc_S_le_weyl (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (a b : ℕ) (hab : a ≤ b) (H : ℕ) (hH : 1 ≤ H) :
    ‖vdc_S t m h a b‖ ^ 2 ≤
      (((b - a : ℕ) : ℝ) + H) / H * (((b - a : ℕ) : ℝ) + 2 * ∑ k ∈ Finset.Ioo 0 H,
        ‖vdc_S t (m + 1) (Fin.snoc h k) a (b - k)‖) := by
  have hweyl := norm_sq_sum_exp_le_weyl (vdc_phase t m h) a b hab H hH
  have heq : ∀ k ∈ Finset.Ioo 0 H,
      ‖∑ n ∈ Finset.Ioc a (b - k), Complex.exp (2 * Real.pi * Complex.I * ((vdc_phase t m h (n + k) - vdc_phase t m h n : ℝ) : ℂ))‖ =
      ‖vdc_S t (m + 1) (Fin.snoc h k) a (b - k)‖ := by
    intro k _
    dsimp [vdc_S]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [vdc_phase_diff]
  have h_sum_rw : (∑ h_1 ∈ Finset.Ioo 0 H,
      ‖∑ n ∈ Finset.Ioc a (b - h_1), Complex.exp (2 * Real.pi * Complex.I * ((vdc_phase t m h (n + h_1) - vdc_phase t m h n : ℝ) : ℂ))‖) =
      ∑ k ∈ Finset.Ioo 0 H, ‖vdc_S t (m + 1) (Fin.snoc h k) a (b - k)‖ :=
    Finset.sum_congr rfl heq
  rw [h_sum_rw] at hweyl
  exact hweyl

/-!
### 2. Step Vector Operations
-/

/-- Appending 1 to a step vector preserves the lower bound `1 ≤ h i`. -/
lemma fin_snoc_one_ge_one (m : ℕ) (h : Fin m → ℕ) (hpos : ∀ i, 1 ≤ h i) :
    ∀ i : Fin (m + 1), 1 ≤ (Fin.snoc (α := fun _ => ℕ) h 1) i := by
  intro i
  obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
  · rw [Fin.snoc_castSucc]
    exact hpos j
  · rw [Fin.snoc_last]

/-- Appending 1 to a step vector preserves the upper bound `h i ≤ N`. -/
lemma fin_snoc_one_le (m : ℕ) (h : Fin m → ℕ) {N : ℕ} (hh : ∀ i, h i ≤ N) (hN : 1 ≤ N) :
    ∀ i : Fin (m + 1), (Fin.snoc (α := fun _ => ℕ) h 1) i ≤ N := by
  intro i
  obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
  · rw [Fin.snoc_castSucc]
    exact hh j
  · rw [Fin.snoc_last]
    exact hN

/-- Appending 1 preserves the coordinate product: `∏ (snoc h 1) = ∏ h`. -/
lemma prod_fin_snoc_one (m : ℕ) (h : Fin m → ℕ) :
    ∏ i : Fin (m + 1), (((Fin.snoc (α := fun _ => ℕ) h 1) i : ℕ) : ℝ) = ∏ i : Fin m, (h i : ℝ) := by
  have hsnoc := Fin.prod_snoc (1 : ℝ) (fun i : Fin m => (h i : ℝ))
  have heq : (fun i : Fin (m + 1) => (((Fin.snoc (α := fun _ => ℕ) h 1) i : ℕ) : ℝ)) =
      Fin.snoc (α := fun _ => ℝ) (fun i : Fin m => (h i : ℝ)) 1 := by
    ext i
    obtain ⟨j, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    · rw [Fin.snoc_last, Fin.snoc_last]
      push_cast
      rfl
  rw [heq, hsnoc, mul_one]

/-!
### 3. Consecutive Differences and Sharp Derivative Bounds
-/

/-- Consecutive difference of the differenced phase. -/
lemma vdc_consec_diff_eq (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (n : ℕ) :
    vdc_phase t m h (n + 1) - vdc_phase t m h n =
    - (t / (2 * Real.pi)) * logIterDiff (m + 1) (Fin.snoc h 1) (n : ℝ) := by
  have := vdc_phase_diff t m h 1 n
  dsimp [vdc_phase] at this
  exact this

/-- Absolute value of the consecutive difference. -/
lemma abs_vdc_consec_diff_eq (t : ℝ) (ht : 0 ≤ t) (m : ℕ) (h : Fin m → ℕ) (n : ℕ) :
    |vdc_phase t m h (n + 1) - vdc_phase t m h n| =
    (t / (2 * Real.pi)) * |logIterDiff (m + 1) (Fin.snoc h 1) (n : ℝ)| := by
  rw [vdc_consec_diff_eq, abs_mul, abs_neg]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have ht_div : 0 ≤ t / (2 * Real.pi) := div_nonneg ht hpi
  rw [abs_of_nonneg ht_div]

/-- Sharp bounds on consecutive differences:
`(t / 2π) * m! ∏ h_i / ((m+3)N)^{m+1} ≤ |Δ g_h(n)| ≤ (t / 2π) * m! ∏ h_i / N^{m+1}`. -/
lemma abs_vdc_consec_diff_bounds (t : ℝ) (ht : 0 ≤ t) (m : ℕ) (h : Fin m → ℕ)
    (hpos : ∀ i, 1 ≤ h i) (N : ℕ) (hN : 1 ≤ N) (hh : ∀ i, h i ≤ N)
    (n : ℕ) (hn1 : N ≤ n) (hn2 : (n : ℝ) ≤ 2 * N) :
    (t / (2 * Real.pi)) * ((m.factorial : ℝ) * (∏ i, (h i : ℝ)) / ((m + 3 : ℝ) * N) ^ (m + 1)) ≤
      |vdc_phase t m h (n + 1) - vdc_phase t m h n| ∧
    |vdc_phase t m h (n + 1) - vdc_phase t m h n| ≤
      (t / (2 * Real.pi)) * ((m.factorial : ℝ) * (∏ i, (h i : ℝ)) / (N : ℝ) ^ (m + 1)) := by
  have hm1 : 1 ≤ m + 1 := by omega
  have hpos' := fin_snoc_one_ge_one m h hpos
  have hh' := fin_snoc_one_le m h hh hN
  have hn_cast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hbounds := abs_logIterDiff_bounds (m + 1) hm1 (Fin.snoc h 1) hpos' N hN hh' (n : ℝ) hn_cast hn2
  have hprod := prod_fin_snoc_one m h
  have hcast : (↑(m + 1) + (2 : ℝ)) = (m + 3 : ℝ) := by push_cast; ring
  have hfact : (m + 1 - 1).factorial = m.factorial := rfl
  rw [hfact, hcast, hprod] at hbounds
  rw [abs_vdc_consec_diff_eq t ht m h n]
  have ht2pi : 0 ≤ t / (2 * Real.pi) := by positivity
  constructor
  · exact mul_le_mul_of_nonneg_left hbounds.1 ht2pi
  · exact mul_le_mul_of_nonneg_left hbounds.2 ht2pi

/-!
### 4. Base Case K = 1: Kusmin–Landau Evaluation for Sub-blocks
-/

/--
The `K = 1` base case of the iterated van der Corput estimate for sub-blocks.
Follows from the Kusmin-Landau estimate applied to the phase `g(n) = -(t/2π) log n`.
-/
theorem norm_sum_exp_neg_log_mul_I_le_pow_iterated_one_main :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N M : ℕ) (t : ℝ), 2 ≤ N → N < M → M ≤ 2 * N → (N : ℝ) ≤ t → t ≤ (N : ℝ) ^ 1 →
      ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ C * (N : ℝ) ^ (1 - c) := by
  obtain ⟨C₀, hC₀, hbound⟩ := norm_sum_exp_neg_log_mul_I_subblock_le
  use 1 / 2, C₀ * 2
  refine ⟨by norm_num, mul_pos hC₀ (by norm_num), ?_⟩
  intro N M t hN hNM hM2 ht_low ht_high
  have ht_eq : t = (N : ℝ) := by
    rw [pow_one] at ht_high
    exact le_antisymm ht_high ht_low
  have hN1 : 1 ≤ N := by omega
  have ht1 : 1 ≤ t := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    linarith
  have h_bound := hbound N M t hN1 hNM hM2 ht1
  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hsqrt_ne : Real.sqrt (N : ℝ) ≠ 0 := by positivity
  have hsqrt_eq : (N : ℝ) / Real.sqrt (N : ℝ) = Real.sqrt (N : ℝ) := by
    rw [div_eq_iff hsqrt_ne]
    exact (Real.mul_self_sqrt hN_pos.le).symm
  have hp : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  calc ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖
    _ ≤ C₀ * (Real.sqrt t + (N : ℝ) / Real.sqrt t) := h_bound
    _ = C₀ * (Real.sqrt (N : ℝ) + (N : ℝ) / Real.sqrt (N : ℝ)) := by rw [ht_eq]
    _ = C₀ * (Real.sqrt (N : ℝ) + Real.sqrt (N : ℝ)) := by rw [hsqrt_eq]
    _ = (C₀ * 2) * Real.sqrt (N : ℝ) := by ring
    _ = (C₀ * 2) * (N : ℝ) ^ (1 - (1 / 2 : ℝ)) := by
      rw [hp, Real.sqrt_eq_rpow]

end Erdos1201.MR
