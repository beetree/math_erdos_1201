import Mathlib
import Erdos1201.Vendor.NumberTheory.PNT.ZetaBounds

/-!
# Control of the Riemann Zeta Function by Dyadic Exponential Sums

This module proves Tao's Proposition 1 in a sharp-cutoff form:
near the 1-line, the Riemann zeta function is controlled by dyadic exponential sums of $n^{-it}$.

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

open scoped BigOperators
open Complex

namespace Erdos1201.MR.Vinogradov

/-! ### Summation by Parts / Abel Summation -/

/-- Summation by parts for finite sums: norm bound on a sum with monotonically non-increasing weights. -/
lemma norm_sum_range_by_parts_le {K : ℕ} (hK : 0 < K)
    (f : ℕ → ℝ) (g : ℕ → ℂ) (B : ℝ)
    (hf_pos : 0 ≤ f (K - 1))
    (hf_mono : ∀ i < K - 1, f (i + 1) ≤ f i)
    (h_partial : ∀ k, 0 < k → k ≤ K → ‖∑ j ∈ Finset.range k, g j‖ ≤ B) :
    ‖∑ i ∈ Finset.range K, (f i : ℂ) * g i‖ ≤ f 0 * B := by
  have h_id := Finset.sum_range_by_parts (R := ℂ) (M := ℂ) (fun i => (f i : ℂ)) g K
  simp only [smul_eq_mul] at h_id
  rw [h_id]
  have h_norm_sub : ‖(f (K - 1) : ℂ) * ∑ i ∈ Finset.range K, g i -
      ∑ i ∈ Finset.range (K - 1), ((f (i + 1) : ℂ) - (f i : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j‖ ≤
    ‖(f (K - 1) : ℂ) * ∑ i ∈ Finset.range K, g i‖ +
    ‖∑ i ∈ Finset.range (K - 1), ((f (i + 1) : ℂ) - (f i : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j‖ :=
    norm_sub_le _ _
  refine le_trans h_norm_sub ?_
  have h_term1 : ‖(f (K - 1) : ℂ) * ∑ i ∈ Finset.range K, g i‖ ≤ f (K - 1) * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hf_pos]
    exact mul_le_mul_of_nonneg_left (h_partial K hK le_rfl) hf_pos
  have h_term2 : ‖∑ i ∈ Finset.range (K - 1), ((f (i + 1) : ℂ) - (f i : ℂ)) * ∑ j ∈ Finset.range (i + 1), g j‖ ≤
      ∑ i ∈ Finset.range (K - 1), (f i - f (i + 1)) * B := by
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [norm_mul]
    have h_diff_neg : (f (i + 1) : ℂ) - (f i : ℂ) = -((f i - f (i + 1) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h_diff_neg, norm_neg, Complex.norm_real]
    have h_diff_nonneg : 0 ≤ f i - f (i + 1) := by
      linarith [hf_mono i hi]
    rw [Real.norm_of_nonneg h_diff_nonneg]
    have hi_pos : 0 < i + 1 := by omega
    have hi_le : i + 1 ≤ K := by omega
    exact mul_le_mul_of_nonneg_left (h_partial (i + 1) hi_pos hi_le) h_diff_nonneg
  have h_tel : ∑ i ∈ Finset.range (K - 1), (f i - f (i + 1)) = f 0 - f (K - 1) := by
    exact Finset.sum_range_sub' f (K - 1)
  have h_sum_mul : ∑ i ∈ Finset.range (K - 1), (f i - f (i + 1)) * B = (f 0 - f (K - 1)) * B := by
    rw [← Finset.sum_mul, h_tel]
  rw [h_sum_mul] at h_term2
  linarith

/-- Identification of `Finset.Ioc` with `Finset.Ico` shifted by 1. -/
lemma Ioc_eq_Ico_succ (a b : ℕ) : Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) := by
  ext x
  simp only [Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-- Reindexing a sum over `Finset.Ioc N M` into `Finset.range (M - N)`. -/
lemma sum_Ioc_eq_sum_range (N M : ℕ) (F : ℕ → ℂ) :
    ∑ n ∈ Finset.Ioc N M, F n = ∑ i ∈ Finset.range (M - N), F (N + 1 + i) := by
  rw [Ioc_eq_Ico_succ, Finset.sum_Ico_eq_sum_range]
  have : M + 1 - (N + 1) = M - N := by omega
  rw [this]

/-- Abel summation on `Finset.Ioc N M` with weights $n^{-\sigma}$. -/
lemma norm_sum_Ioc_weighted_le {N M : ℕ} (hNM : N < M)
    (σ : ℝ) (hσ : 0 ≤ σ) (e : ℕ → ℂ) (B : ℝ)
    (h_partial : ∀ m, N < m → m ≤ M → ‖∑ n ∈ Finset.Ioc N m, e n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc N M, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * e n‖ ≤ (N + 1 : ℝ) ^ (-σ) * B := by
  let K := M - N
  have hK : 0 < K := by omega
  let f := fun i : ℕ => (N + 1 + i : ℝ) ^ (-σ)
  let g := fun i : ℕ => e (N + 1 + i)
  have h_sum_eq : (∑ n ∈ Finset.Ioc N M, (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * e n) =
      ∑ i ∈ Finset.range K, (f i : ℂ) * g i := by
    rw [sum_Ioc_eq_sum_range N M fun n => (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * e n]
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [f, g]
    push_cast
    rfl
  rw [h_sum_eq]
  have hf_pos : 0 ≤ f (K - 1) := by
    dsimp [f]
    positivity
  have hf_mono : ∀ i < K - 1, f (i + 1) ≤ f i := by
    intro i _
    dsimp [f]
    apply Real.rpow_le_rpow_of_nonpos (by positivity)
    · gcongr
      exact_mod_cast Nat.le_succ i
    · linarith
  have h_part : ∀ k, 0 < k → k ≤ K → ‖∑ j ∈ Finset.range k, g j‖ ≤ B := by
    intro k hk hkK
    have h_eq : ∑ j ∈ Finset.range k, g j = ∑ n ∈ Finset.Ioc N (N + k), e n := by
      rw [sum_Ioc_eq_sum_range]
      have : N + k - N = k := by omega
      rw [this]
    rw [h_eq]
    apply h_partial (N + k) (by omega) (by omega)
  have := norm_sum_range_by_parts_le hK f g B hf_pos hf_mono h_part
  have h_f0 : f 0 = (N + 1 : ℝ) ^ (-σ) := by
    dsimp [f]
    congr 1
    push_cast
    ring
  rwa [h_f0] at this

/-! ### Dyadic Interval Decomposition -/

/-- Telescoping partition of an interval into sub-intervals. -/
lemma sum_Ioc_telescoping (K : ℕ) (a : ℕ → ℕ) (ha : ∀ j < K, a j ≤ a (j + 1)) (F : ℕ → ℂ) :
    ∑ j ∈ Finset.range K, ∑ n ∈ Finset.Ioc (a j) (a (j + 1)), F n =
      ∑ n ∈ Finset.Ioc (a 0) (a K), F n := by
  induction K with
  | zero =>
    simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih (fun j hj => ha j (by omega))]
    exact Finset.sum_Ioc_consecutive F (by
      clear ih
      induction K with
      | zero => rfl
      | succ K ihK =>
        have h1 : a 0 ≤ a K := ihK (fun j hj => ha j (by omega))
        have h2 : a K ≤ a (K + 1) := ha K (by omega)
        exact le_trans h1 h2
    ) (ha K (by omega))

/-- Any downward-closed set of natural numbers is an initial segment `Finset.range s.card`. -/
lemma range_eq_of_downward_closed (s : Finset ℕ) (h_down : ∀ i j, i ≤ j → j ∈ s → i ∈ s) :
    s = Finset.range s.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro j hj
    rw [Finset.mem_range]
    have h_sub : Finset.range (j + 1) ⊆ s := by
      intro i hi
      rw [Finset.mem_range] at hi
      exact h_down i j (by omega) hj
    have := Finset.card_le_card h_sub
    rw [Finset.card_range] at this
    omega
  · simp

/-- Logarithmic bound on the number of dyadic blocks below $x \le t^2$. -/
lemma card_filter_two_pow_lt {x : ℕ} (hx : 4 ≤ x) {t : ℝ} (ht : 2 ≤ |t|) (hxt : (x : ℝ) ≤ t ^ 2) :
    let s := (Finset.range x).filter (fun j => 2 ^ j < x)
    (s.card : ℝ) ≤ 6 * Real.log |t| := by
  intro s
  have hlog2_pos : 0 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hlog2_ge : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have ht_ge2 : (2 : ℝ) ≤ |t| := ht
  have ht_pos : 0 < |t| := by linarith
  have hlogt_ge : Real.log 2 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht_ge2
  have h0_mem : 0 ∈ s := by
    rw [Finset.mem_filter, Finset.mem_range]
    omega
  have hm_pos : 1 ≤ s.card := by
    have := Finset.card_pos.mpr ⟨0, h0_mem⟩
    omega
  have h_range : s = Finset.range s.card := by
    apply range_eq_of_downward_closed
    intro i j hij hj
    rw [Finset.mem_filter, Finset.mem_range] at hj ⊢
    have h2i : 2 ^ i < x := by
      have : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hij
      exact lt_of_le_of_lt this hj.2
    have hix : i < x := by
      have : i < 2 ^ i := Nat.lt_pow_self (by norm_num)
      omega
    exact ⟨hix, h2i⟩
  have h_pred_mem : s.card - 1 ∈ s := by
    rw [h_range, Finset.mem_range, Finset.card_range]
    omega
  rw [Finset.mem_filter] at h_pred_mem
  have h2_pred : 2 ^ (s.card - 1) < x := h_pred_mem.2
  have h2_pred_lt : (2 : ℝ) ^ (s.card - 1) < |t| ^ 2 := by
    have h1 : ((2 ^ (s.card - 1) : ℕ) : ℝ) < (x : ℝ) := by exact_mod_cast h2_pred
    have h2 : ((2 ^ (s.card - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (s.card - 1) := by push_cast; rfl
    rw [h2] at h1
    have h3 : (x : ℝ) ≤ |t| ^ 2 := by
      rw [sq_abs]
      exact hxt
    exact lt_of_lt_of_le h1 h3
  have h_log_lt : Real.log ((2 : ℝ) ^ (s.card - 1)) < Real.log (|t| ^ 2) := by
    apply Real.log_lt_log (by positivity) h2_pred_lt
  have h_log_pow : Real.log ((2 : ℝ) ^ (s.card - 1)) = (s.card - 1 : ℝ) * Real.log 2 := by
    have : (2 : ℝ) ^ (s.card - 1) = (2 : ℝ) ^ ((s.card - 1 : ℕ) : ℝ) := by rw [Real.rpow_natCast]
    rw [this, Real.log_rpow (by norm_num)]
    congr 1
    rw [Nat.cast_sub hm_pos, Nat.cast_one]
  rw [h_log_pow] at h_log_lt
  have h_log_t2 : Real.log (|t| ^ 2) = 2 * Real.log |t| := by
    have : |t| ^ 2 = |t| ^ (2 : ℝ) := by rw [Real.rpow_two]
    rw [this, Real.log_rpow ht_pos]
  rw [h_log_t2] at h_log_lt
  have hm1_nonneg : 0 ≤ (s.card - 1 : ℝ) := by
    have : (1 : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hm_pos
    linarith
  have h_m1_le : (s.card - 1 : ℝ) ≤ 4 * Real.log |t| := by
    calc (s.card - 1 : ℝ) = (s.card - 1 : ℝ) * (1 / 2) / (1 / 2) := by ring
    _ ≤ (s.card - 1 : ℝ) * Real.log 2 / (1 / 2) := by
      have : (s.card - 1 : ℝ) * (1 / 2) ≤ (s.card - 1 : ℝ) * Real.log 2 := by
        exact mul_le_mul_of_nonneg_left hlog2_ge hm1_nonneg
      linarith
    _ ≤ 2 * Real.log |t| / (1 / 2) := by
      have : (s.card - 1 : ℝ) * Real.log 2 ≤ 2 * Real.log |t| := le_of_lt h_log_lt
      linarith
    _ = 4 * Real.log |t| := by ring
  have h_m : (s.card : ℝ) = (s.card - 1 : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hm_pos).symm
  have h_one_le : (1 : ℝ) ≤ 2 * Real.log |t| := by
    calc (1 : ℝ) = 2 * (1 / 2) := by norm_num
    _ ≤ 2 * Real.log 2 := by linarith
    _ ≤ 2 * Real.log |t| := by linarith
  rw [h_m]
  linarith

/-! ### Euler–Maclaurin Tail Bounds -/

/-- Bound on the first tail term $x^{1-s}/(s-1)$. -/
lemma tail_term1_le {σ t : ℝ} (hσ1 : 3 / 4 ≤ σ) (hσ2 : σ ≤ 1) (ht : 2 ≤ |t|)
    {N : ℕ} (hNpos : 0 < N) (hNle : (N : ℝ) ≤ t ^ 2) :
    ‖(- (N : ℂ) ^ (1 - (σ + t * Complex.I))) / (1 - (σ + t * Complex.I))‖ ≤ 1 := by
  have ht_pos : 0 < |t| := by linarith
  have ht_one : 1 ≤ |t| := by linarith
  have ht2 : t ^ 2 = |t| ^ 2 := by rw [sq_abs]
  have h_im : |t| ≤ ‖1 - (σ + t * Complex.I : ℂ)‖ := by
    have := Complex.abs_im_le_norm (1 - (σ + t * Complex.I : ℂ))
    simp only [Complex.sub_im, Complex.one_im, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.I_im, mul_one,
      zero_add, zero_sub, add_zero] at this
    rwa [abs_neg] at this
  have h_denom : 0 < ‖1 - (σ + t * Complex.I : ℂ)‖ := lt_of_lt_of_le ht_pos h_im
  rw [norm_div, norm_neg]
  have h_re : (1 - (σ + t * Complex.I : ℂ)).re = 1 - σ := by simp
  rw [Complex.norm_natCast_cpow_of_pos hNpos, h_re]
  have h_exp_nonneg : 0 ≤ 1 - σ := by linarith
  have hN_le_t2 : (N : ℝ) ≤ |t| ^ (2 : ℝ) := by
    rw [Real.rpow_two, ← ht2]
    exact hNle
  have h1 : (N : ℝ) ^ (1 - σ) ≤ (|t| ^ (2 : ℝ)) ^ (1 - σ) := by
    apply Real.rpow_le_rpow (by positivity) hN_le_t2 h_exp_nonneg
  rw [← Real.rpow_mul (by positivity)] at h1
  have h_exp_le1 : 2 * (1 - σ) ≤ 1 := by linarith
  have h2 : |t| ^ (2 * (1 - σ)) ≤ |t| ^ (1 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le ht_one h_exp_le1
  rw [Real.rpow_one] at h2
  have h_num : (N : ℝ) ^ (1 - σ) ≤ |t| := le_trans h1 h2
  exact (div_le_one h_denom).mpr (le_trans h_num h_im)

/-- Bound on the second tail term $x^{-s}/2$. -/
lemma tail_term2_le {σ t : ℝ} (hσ1 : 3 / 4 ≤ σ) {N : ℕ} (hN : 1 ≤ N) :
    ‖(- (N : ℂ) ^ (-(σ + t * Complex.I))) / 2‖ ≤ 1 / 2 := by
  have hNpos : 0 < N := by omega
  have hN_ge : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [norm_div, norm_neg, Complex.norm_natCast_cpow_of_pos hNpos]
  have : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [this]
  simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, add_zero]
  have h_rpow : (N : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN_ge (by linarith)
  linarith

/-- Bound on the integral remainder term from `ZetaBnd_aux1`. -/
lemma tail_term3_le {σ t : ℝ} (hσ1 : 3 / 4 ≤ σ) (hσ2 : σ ≤ 1) (ht : 2 ≤ |t|)
    {N : ℕ} (hN_floor : N = ⌊t ^ 2⌋₊) :
    ‖(σ + t * I : ℂ) * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I : ℂ) + 1)‖ ≤ 6 := by
  have ht_pos : 0 < |t| := by linarith
  have ht_one : 1 ≤ |t| := by linarith
  have ht2 : (4 : ℝ) ≤ t ^ 2 := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
    _ ≤ |t| ^ 2 := by nlinarith
    _ = t ^ 2 := sq_abs t
  have hN_ge4 : 4 ≤ N := by
    rw [hN_floor]
    exact Nat.le_floor ht2
  have hN_pos : 1 ≤ N := by omega
  have hN_posR : (0 : ℝ) < (N : ℝ) := by positivity
  have hσ_mem : σ ∈ Set.Ioc 0 2 := ⟨by linarith, by linarith⟩
  have h_aux := ZetaBnd_aux1 N hN_pos hσ_mem ht
  have h_floor_lt : t ^ 2 < (N : ℝ) + 1 := by
    rw [hN_floor]
    exact Nat.lt_floor_add_one (t ^ 2)
  have hN_ge_half : t ^ 2 / 2 ≤ (N : ℝ) := by
    have : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
      have : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN_ge4
      linarith
    linarith
  have ht2_pos : 0 < t ^ 2 := by positivity
  have h_inv : (N : ℝ)⁻¹ ≤ 2 / t ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hN_posR]
    calc (1 : ℝ) = (2 / t ^ 2) * (t ^ 2 / 2) := by
          rw [div_mul_div_comm, mul_comm 2 (t ^ 2)]
          exact (div_self (by positivity)).symm
    _ ≤ (2 / t ^ 2) * (N : ℝ) := by
          apply mul_le_mul_of_nonneg_left hN_ge_half
          positivity
  have h_rpow_inv : (N : ℝ) ^ (-σ) = ((N : ℝ)⁻¹) ^ σ := by
    rw [Real.rpow_neg (by positivity), Real.inv_rpow (by positivity)]
  have h_rpow_le : ((N : ℝ)⁻¹) ^ σ ≤ (2 / t ^ 2) ^ σ := by
    exact Real.rpow_le_rpow (by positivity) h_inv (by linarith)
  have ht2_eq : t ^ 2 = |t| ^ (2 : ℝ) := by
    rw [← sq_abs t, Real.rpow_two]
  have h_div_rpow : (2 / t ^ 2) ^ σ = (2 : ℝ) ^ σ * (|t| ^ (2 : ℝ)) ^ (-σ) := by
    rw [ht2_eq, div_eq_mul_inv, Real.mul_rpow (by norm_num) (by positivity),
      Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
  have h_2_rpow : (2 : ℝ) ^ σ ≤ 2 := by
    have : (2 : ℝ) ^ σ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ2
    rwa [Real.rpow_one] at this
  have h_t_rpow : (|t| ^ (2 : ℝ)) ^ (-σ) = |t| ^ (-2 * σ) := by
    rw [← Real.rpow_mul (by positivity)]
    ring_nf
  have h_N_rpow_final : (N : ℝ) ^ (-σ) ≤ 2 * |t| ^ (-2 * σ) := by
    rw [h_rpow_inv]
    refine le_trans h_rpow_le ?_
    rw [h_div_rpow, h_t_rpow]
    exact mul_le_mul_of_nonneg_right h_2_rpow (by positivity)
  have h_prod : 2 * |t| * (N : ℝ) ^ (-σ) ≤ 2 * |t| * (2 * |t| ^ (-2 * σ)) := by
    gcongr
  have h_simp : 2 * |t| * (2 * |t| ^ (-2 * σ)) = 4 * (|t| * |t| ^ (-2 * σ)) := by ring
  have h_t_mul : |t| * |t| ^ (-2 * σ) = |t| ^ (1 - 2 * σ) := by
    have : |t| = |t| ^ (1 : ℝ) := Real.rpow_one |t| |>.symm
    nth_rewrite 1 [this]
    rw [← Real.rpow_add ht_pos]
    ring_nf
  have h_exp_neg : 1 - 2 * σ ≤ 0 := by linarith
  have h_t_le1 : |t| ^ (1 - 2 * σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht_one h_exp_neg
  have h_num_le : 2 * |t| * (N : ℝ) ^ (-σ) ≤ 4 := by
    refine le_trans h_prod ?_
    rw [h_simp, h_t_mul]
    linarith
  have h_denom_ge : 3 / 4 ≤ σ := hσ1
  have h_final : 2 * |t| * (N : ℝ) ^ (-σ) / σ ≤ 6 := by
    have h_div : 2 * |t| * (N : ℝ) ^ (-σ) / σ ≤ 4 / (3 / 4) := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    have h43 : (4 : ℝ) / (3 / 4) = 16 / 3 := by norm_num
    linarith
  exact le_trans h_aux h_final

/-- Expansion of $n^{-s}$ as $n^{-\sigma} e^{-i t \log n}$. -/
lemma one_div_natCast_cpow_eq {n : ℕ} (hn : 1 ≤ n) (σ t : ℝ) :
    1 / (n : ℂ) ^ (σ + t * I : ℂ) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I) := by
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hn_ne : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn_pos)
  rw [one_div, ← Complex.cpow_neg, Complex.cpow_def]
  simp only [hn_ne, ↓reduceIte]
  have hlog : Complex.log (n : ℂ) = ((Real.log (n : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (by positivity)]
  rw [hlog]
  have h_exp : (Real.log (n : ℝ) : ℂ) * -(σ + t * I : ℂ) =
      ((-σ * Real.log (n : ℝ) : ℝ) : ℂ) + (-((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h_exp, Complex.exp_add]
  congr 1
  rw [← Complex.ofReal_exp]
  congr 1
  rw [Real.rpow_def_of_pos hn_pos]
  ring_nf

/-- Splitting a sum over `Finset.range (x + 1)` into $n = 0, 1$ and $1 < n \le x$. -/
lemma range_succ_eq_union (x : ℕ) (hx : 1 ≤ x) (F : ℕ → ℂ) :
    ∑ n ∈ Finset.range (x + 1), F n = F 0 + F 1 + ∑ n ∈ Finset.Ioc 1 x, F n := by
  have h_range : Finset.range (x + 1) = {0} ∪ Finset.Ico 1 (x + 1) := by
    ext a; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
    omega
  have h_disj1 : Disjoint ({0} : Finset ℕ) (Finset.Ico 1 (x + 1)) := by
    simp only [Finset.disjoint_singleton_left, Finset.mem_Ico]; omega
  rw [h_range, Finset.sum_union h_disj1, Finset.sum_singleton]
  have h_ico : Finset.Ico 1 (x + 1) = {1} ∪ Finset.Ico 2 (x + 1) := by
    ext a; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]; omega
  have h_disj2 : Disjoint ({1} : Finset ℕ) (Finset.Ico 2 (x + 1)) := by
    simp only [Finset.disjoint_singleton_left, Finset.mem_Ico]; omega
  rw [h_ico, Finset.sum_union h_disj2, Finset.sum_singleton]
  have h_ioc : Finset.Ico 2 (x + 1) = Finset.Ioc 1 x := by
    ext a; simp only [Finset.mem_Ico, Finset.mem_Ioc]; omega
  rw [h_ioc, add_assoc]

/-- Norm of $e^{-i \theta}$ is 1 for real $\theta$. -/
lemma norm_exp_I_eq_one (θ : ℝ) :
    ‖Complex.exp (-((θ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  have : (-((θ : ℝ) : ℂ) * Complex.I).re = 0 := by
    simp only [mul_re, neg_re, ofReal_re, I_re, mul_zero, neg_im, ofReal_im, I_im, mul_one,
      sub_zero, neg_zero]
  rw [this, Real.exp_zero]

/-! ### Main Theorem -/

/--
Tao's Proposition 1 in explicit sharp-cutoff form:
for $3/4 \le \sigma \le 1$ and $|t| \ge 2$, if all dyadic exponential sums
$N^{-\sigma} \|\sum_{N < n \le M} n^{-it}\|$ are bounded by $E$ for $1 \le N \le t^2$ and $N < M \le 2N$,
then $\|\zeta(\sigma + it)\| \le C (1 + E \log |t|)$.
-/
theorem norm_riemannZeta_le_dyadic_expsums :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ t : ℝ), 3 / 4 ≤ σ → σ ≤ 1 → 2 ≤ |t| →
      ∀ (E : ℝ), (∀ (N : ℕ) (_ : 1 ≤ N ∧ (N : ℝ) ≤ t ^ 2) (M : ℕ) (_ : N < M ∧ M ≤ 2 * N),
        (N : ℝ) ^ (-σ) * ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ E) →
      ‖riemannZeta (σ + t * Complex.I)‖ ≤ C * (1 + Real.log |t| * E) := by
  refine ⟨9, by norm_num, ?_⟩
  intro σ t hσ1 hσ2 ht E hE
  have ht_pos : 0 < |t| := by linarith
  have ht2 : (4 : ℝ) ≤ t ^ 2 := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
    _ ≤ |t| ^ 2 := by nlinarith
    _ = t ^ 2 := sq_abs t
  have ht2_pos : 0 < t ^ 2 := by positivity
  have hlogt_pos : 0 < Real.log |t| := by
    have : (1 : ℝ) < 2 := by norm_num
    have h1 : 0 < Real.log 2 := Real.log_pos this
    have h2 : Real.log 2 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
    linarith
  -- Nonnegativity of E
  have hE_ge1 : 1 ≤ E := by
    have ht2_nat : ((1 : ℕ) : ℝ) ≤ t ^ 2 := by
      have : ((1 : ℕ) : ℝ) = 1 := by norm_num
      rw [this]
      linarith
    have h1 := hE 1 ⟨le_rfl, ht2_nat⟩ 2 ⟨by omega, by omega⟩
    have hIoc : Finset.Ioc 1 2 = {2} := by
      ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega
    rw [hIoc, Finset.sum_singleton] at h1
    have h2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h2] at h1
    have h_norm := norm_exp_I_eq_one (t * Real.log 2)
    have h_rpow : ((1 : ℕ) : ℝ) ^ (-σ) = 1 := by
      have : ((1 : ℕ) : ℝ) = 1 := by norm_num
      rw [this, Real.one_rpow]
    rw [h_norm, h_rpow, one_mul] at h1
    exact h1
  have hE_nonneg : 0 ≤ E := by linarith
  set x := ⌊t ^ 2⌋₊
  have hx4 : 4 ≤ x := Nat.le_floor ht2
  have hx_pos : 1 ≤ x := by omega
  have hx_posR : (0 : ℝ) < (x : ℝ) := by positivity
  have hxt : (x : ℝ) ≤ t ^ 2 := Nat.floor_le (by positivity)
  set s := σ + t * Complex.I
  have hs_re : 0 < s.re := by
    dsimp [s]
    simp only [ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
      add_zero]
    linarith
  have hs_ne1 : s ≠ 1 := by
    intro h
    have : s.im = 0 := by rw [h]; simp
    dsimp [s] at this
    simp only [ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one, zero_add,
      add_zero] at this
    have : |t| = 0 := by rw [this, abs_zero]
    linarith
  have h_zeta_eq : riemannZeta s = riemannZeta0 x s := (Zeta0EqZeta (by omega) hs_re hs_ne1).symm
  rw [h_zeta_eq]
  have h_bnd4 : ‖riemannZeta0 x s‖ ≤ ‖∑ n ∈ Finset.range (x + 1), 1 / (n : ℂ) ^ s‖ +
      ‖(- (x : ℂ) ^ (1 - s)) / (1 - s)‖ +
      ‖(- (x : ℂ) ^ (-s)) / 2‖ +
      ‖s * ∫ u in Set.Ioi (x : ℝ), (⌊u⌋ + 1 / 2 - u) / (u : ℂ) ^ (s + 1)‖ := norm_add₄_le
  have ht1 := tail_term1_le hσ1 hσ2 ht (by omega) hxt
  have ht2_bnd := tail_term2_le (t := t) hσ1 (by omega)
  have ht3 := tail_term3_le hσ1 hσ2 ht rfl
  have h_tail_sum : ‖(- (x : ℂ) ^ (1 - s)) / (1 - s)‖ + ‖(- (x : ℂ) ^ (-s)) / 2‖ +
      ‖s * ∫ u in Set.Ioi (x : ℝ), (⌊u⌋ + 1 / 2 - u) / (u : ℂ) ^ (s + 1)‖ ≤ 8 := by
    linarith
  have h_range_sum : ∑ n ∈ Finset.range (x + 1), 1 / (n : ℂ) ^ s =
      1 + ∑ n ∈ Finset.Ioc 1 x, 1 / (n : ℂ) ^ s := by
    have h_split := range_succ_eq_union x hx_pos (fun n => 1 / (n : ℂ) ^ s)
    rw [h_split]
    have hs_ne0 : s ≠ 0 := by
      intro hs0
      have : s.re = 0 := by rw [hs0]; rfl
      linarith
    have h0 : (0 : ℂ) ^ s = 0 := Complex.zero_cpow hs_ne0
    rw [Nat.cast_zero, Nat.cast_one, h0, div_zero, Complex.one_cpow, div_one, zero_add]
  have h_norm_sum_le : ‖∑ n ∈ Finset.range (x + 1), 1 / (n : ℂ) ^ s‖ ≤
      1 + ‖∑ n ∈ Finset.Ioc 1 x, 1 / (n : ℂ) ^ s‖ := by
    rw [h_range_sum]
    refine le_trans (norm_add_le (1 : ℂ) _) ?_
    rw [norm_one]
  -- Now decompose the sum over Ioc 1 x
  set F := fun n : ℕ => (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)
  have h_sum_F : ∑ n ∈ Finset.Ioc 1 x, 1 / (n : ℂ) ^ s = ∑ n ∈ Finset.Ioc 1 x, F n := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    exact one_div_natCast_cpow_eq (by omega) σ t
  rw [h_sum_F] at h_norm_sum_le
  set a := fun j : ℕ => min (2 ^ j) x
  have ha_mono : ∀ j < x, a j ≤ a (j + 1) := by
    intro j _
    dsimp [a]
    have : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have ha0 : a 0 = 1 := by
    dsimp [a]
    omega
  have hax : a x = x := by
    dsimp [a]
    have : x < 2 ^ x := Nat.lt_pow_self (by norm_num)
    omega
  have h_tel := sum_Ioc_telescoping x a ha_mono F
  rw [ha0, hax] at h_tel
  rw [← h_tel] at h_norm_sum_le
  have h_norm_tel_le : ‖∑ j ∈ Finset.range x, ∑ n ∈ Finset.Ioc (a j) (a (j + 1)), F n‖ ≤
      ∑ j ∈ Finset.range x, ‖∑ n ∈ Finset.Ioc (a j) (a (j + 1)), F n‖ :=
    norm_sum_le _ _
  set s_set := (Finset.range x).filter (fun j => 2 ^ j < x)
  have h_block_le : ∀ j ∈ Finset.range x, ‖∑ n ∈ Finset.Ioc (a j) (a (j + 1)), F n‖ ≤
      if j ∈ s_set then E else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    split_ifs with hjs
    · rw [Finset.mem_filter] at hjs
      have h2j : 2 ^ j < x := hjs.2
      have haj : a j = 2 ^ j := by
        dsimp [a]; omega
      have haj1 : a (j + 1) = min (2 ^ (j + 1)) x := rfl
      rw [haj, haj1]
      set N := 2 ^ j
      set M := min (2 ^ (j + 1)) x
      have hNM : N < M := by
        dsimp [N, M]
        have : 2 ^ j < 2 ^ (j + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      have hM_le : M ≤ 2 * N := by
        dsimp [N, M]
        have : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        omega
      have hN_ge1 : 1 ≤ N := by
        dsimp [N]
        exact Nat.one_le_two_pow
      have hN_posR : (0 : ℝ) < (N : ℝ) := by positivity
      have hN_le_t2 : (N : ℝ) ≤ t ^ 2 := by
        dsimp [N]
        exact le_trans (by exact_mod_cast (le_of_lt h2j)) hxt
      have h_partial : ∀ m, N < m → m ≤ M →
          ‖∑ n ∈ Finset.Ioc N m, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤
            (N : ℝ) ^ σ * E := by
        intro m hNm hmM
        have hm_le2N : m ≤ 2 * N := le_trans hmM hM_le
        have h_hyp := hE N ⟨hN_ge1, hN_le_t2⟩ m ⟨hNm, hm_le2N⟩
        have h_prod := mul_le_mul_of_nonneg_left h_hyp (by positivity : 0 ≤ (N : ℝ) ^ σ)
        rw [← mul_assoc, ← Real.rpow_add hN_posR] at h_prod
        have : σ + -σ = 0 := by ring
        rw [this, Real.rpow_zero, one_mul] at h_prod
        exact h_prod
      have h_weighted := norm_sum_Ioc_weighted_le hNM σ (by linarith)
        (fun n => Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I))
        ((N : ℝ) ^ σ * E) h_partial
      refine le_trans h_weighted ?_
      have h_N_le : (N + 1 : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ) := by
        apply Real.rpow_le_rpow_of_nonpos hN_posR (by linarith) (by linarith)
      have h_bound_mul : (N + 1 : ℝ) ^ (-σ) * ((N : ℝ) ^ σ * E) ≤
          (N : ℝ) ^ (-σ) * ((N : ℝ) ^ σ * E) := by
        apply mul_le_mul_of_nonneg_right h_N_le
        positivity
      refine le_trans h_bound_mul ?_
      rw [← mul_assoc, ← Real.rpow_add hN_posR]
      have : -σ + σ = 0 := by ring
      rw [this, Real.rpow_zero, one_mul]
    · rw [Finset.mem_filter] at hjs
      simp only [Finset.mem_range, not_and, not_lt] at hjs
      have h2j : x ≤ 2 ^ j := hjs hj
      have haj : a j = x := by
        dsimp [a]; omega
      have haj1 : a (j + 1) = x := by
        dsimp [a]
        have : x ≤ 2 ^ (j + 1) := by
          have : 2 ^ j ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        omega
      rw [haj, haj1]
      have : Finset.Ioc x x = ∅ := Finset.Ioc_self x
      rw [this, Finset.sum_empty, norm_zero]
  have h_sum_filter : ∑ j ∈ Finset.range x, ‖∑ n ∈ Finset.Ioc (a j) (a (j + 1)), F n‖ ≤
      (s_set.card : ℝ) * E := by
    refine le_trans (Finset.sum_le_sum h_block_le) ?_
    rw [← Finset.sum_filter]
    have : (Finset.range x).filter (fun j => j ∈ s_set) = s_set := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, s_set]
      tauto
    rw [this, Finset.sum_const, nsmul_eq_mul]
  have h_card := card_filter_two_pow_lt hx4 ht hxt
  have h_main_sum_le : ‖∑ j ∈ Finset.range x, ∑ n ∈ Finset.Ioc (a j) (a (j + 1)), F n‖ ≤
      6 * Real.log |t| * E := by
    refine le_trans h_norm_tel_le ?_
    refine le_trans h_sum_filter ?_
    exact mul_le_mul_of_nonneg_right h_card hE_nonneg
  have h_total_zeta : ‖riemannZeta0 x s‖ ≤ 9 + 6 * Real.log |t| * E := by
    linarith
  have h_final_step : 9 + 6 * Real.log |t| * E ≤ 9 * (1 + Real.log |t| * E) := by
    calc 9 + 6 * Real.log |t| * E ≤ 9 + 9 * Real.log |t| * E := by
          gcongr
          linarith
    _ = 9 * (1 + Real.log |t| * E) := by ring
  exact le_trans h_total_zeta h_final_step

end Erdos1201.MR.Vinogradov
