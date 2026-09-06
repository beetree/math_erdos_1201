/-
Copyright (c) 2026 Przemek Chojecki, ChatGPT 5.5. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Przemek Chojecki, ChatGPT 5.5
-/
import Mathlib
import Erdos1201.MR.Polynomials.PrimePowerCoefficients
import Erdos1201.MR.Analysis.DiscreteMeanValue
import Erdos1201.MR.Analysis.DyadicPrimeSums
import Erdos1201.MR.Analysis.WellSpaced
import Erdos1201.MR.Analysis.DirichletPolyBasics

/-!
# Matomäki–Radziwiłł Lemma 8: Large Values of Prime Polynomials via Moments

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module proves Lemma 8 of Matomäki–Radziwiłł (large values of prime polynomials
via the $2k$-th moment and the discrete mean value theorem).
-/

open scoped BigOperators
open Classical

namespace Erdos1201.MR

/-- The $k$-th power coefficient of a Dirichlet polynomial supported on a finset $P$. -/
def primePolyCoeff (a : ℕ → ℂ) (P : Finset ℕ) (k : ℕ) (n : ℕ) : ℂ :=
  ∑ v ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun v => ∏ i, v i = n), ∏ i, a (v i)

/-- Extended coefficient sequence equal to `primePolyCoeff` on `tupleProducts P k` and 0 elsewhere. -/
def momCoeff (a : ℕ → ℂ) (P : Finset ℕ) (k : ℕ) (n : ℕ) : ℂ :=
  if n ∈ tupleProducts P k then primePolyCoeff a P k n else 0

/-- The $k$-th power of a finite Dirichlet polynomial expanded over tuple products. -/
theorem dirichletPoly_pow_eq (a : ℕ → ℂ) (P : Finset ℕ) (k : ℕ) (s : ℂ) (_hP : ∀ p ∈ P, 0 < p) :
    (dirichletPoly a P s) ^ k = ∑ n ∈ tupleProducts P k, (primePolyCoeff a P k n) * (n : ℂ) ^ (-s) := by
  dsimp [dirichletPoly]
  rw [sum_pow_piFinset]
  have hprod (v : Fin k → ℕ) :
      (∏ i : Fin k, (a (v i) * (v i : ℂ) ^ (-s))) =
      (∏ i : Fin k, a (v i)) * ((∏ i : Fin k, v i : ℕ) : ℂ) ^ (-s) := by
    rw [Finset.prod_mul_distrib, prod_natCast_cpow Finset.univ v (-s)]
  simp_rw [hprod]
  set s_tuples := Fintype.piFinset (fun _ : Fin k => P)
  set g := fun (v : Fin k → ℕ) => ∏ i : Fin k, v i
  have h_maps : ∀ v ∈ s_tuples, g v ∈ tupleProducts P k := by
    intro v hv
    exact Finset.mem_image_of_mem g hv
  have h_fib := Finset.sum_fiberwise_of_maps_to h_maps
    (fun v => (∏ i : Fin k, a (v i)) * ((g v : ℕ) : ℂ) ^ (-s))
  rw [← h_fib]
  apply Finset.sum_congr rfl
  intro n _hn
  dsimp [primePolyCoeff]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  have hvg : g v = n := (Finset.mem_filter.mp hv).2
  rw [hvg]

/-- All products of $k$ elements bounded by $P_{max}$ lie in `Ioc 0 (P_{max}^k)`. -/
lemma tupleProducts_subset_Ioc {P : Finset ℕ} (k : ℕ) {P_max : ℕ}
    (h_pos : ∀ p ∈ P, 0 < p) (h_le : ∀ p ∈ P, p ≤ P_max) :
    tupleProducts P k ⊆ Finset.Ioc 0 (P_max ^ k) := by
  intro n hn
  rw [tupleProducts, Finset.mem_image] at hn
  obtain ⟨v, hv, rfl⟩ := hn
  rw [Finset.mem_Ioc]
  constructor
  · apply Finset.prod_pos
    intro i _
    have hvi : v i ∈ P := Fintype.mem_piFinset.mp hv i
    exact h_pos (v i) hvi
  · have h_le_prod : ∏ i : Fin k, v i ≤ ∏ _i : Fin k, P_max := by
      apply Finset.prod_le_prod
      · intro i _
        have hvi : v i ∈ P := Fintype.mem_piFinset.mp hv i
        exact le_of_lt (h_pos (v i) hvi)
      · intro i _
        have hvi : v i ∈ P := Fintype.mem_piFinset.mp hv i
        exact h_le (v i) hvi
    simpa using h_le_prod

/-- Dirichlet polynomial with coefficients `momCoeff` over `Ioc 0 N`. -/
lemma dirichletPoly_momCoeff_eq (a : ℕ → ℂ) (P : Finset ℕ) (k : ℕ) (s : ℂ)
    (N : ℕ) (h_sub : tupleProducts P k ⊆ Finset.Ioc 0 N) :
    dirichletPoly (momCoeff a P k) (Finset.Ioc 0 N) s =
      ∑ n ∈ tupleProducts P k, (primePolyCoeff a P k n) * (n : ℂ) ^ (-s) := by
  dsimp [dirichletPoly]
  rw [← Finset.sum_subset h_sub]
  · apply Finset.sum_congr rfl
    intro n hn
    dsimp [momCoeff]
    split_ifs
    rfl
  · intro n _hn_Ioc hn_not
    dsimp [momCoeff]
    split_ifs
    simp

/-- Dirichlet polynomial with coefficients `momCoeff` coincides with $(P(s))^k$. -/
lemma dirichletPoly_momCoeff_eq_pow (a : ℕ → ℂ) (P : Finset ℕ) (k : ℕ) (s : ℂ)
    (hP : ∀ p ∈ P, 0 < p) (N : ℕ) (h_sub : tupleProducts P k ⊆ Finset.Ioc 0 N) :
    dirichletPoly (momCoeff a P k) (Finset.Ioc 0 N) s = (dirichletPoly a P s) ^ k := by
  rw [dirichletPoly_momCoeff_eq a P k s N h_sub]
  exact (dirichletPoly_pow_eq a P k s hP).symm

/-- Sum of squared coefficients divided by $n^2$ bounded by tupleCount sum. -/
lemma sum_momCoeff_sq_div_sq_le (a : ℕ → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (P : Finset ℕ) (k : ℕ)
    (N : ℕ) (h_sub : tupleProducts P k ⊆ Finset.Ioc 0 N) :
    ∑ n ∈ Finset.Ioc 0 N, ‖momCoeff a P k n‖ ^ 2 / (n : ℝ) ^ 2 ≤
      ∑ n ∈ tupleProducts P k, ((tupleCount P k n : ℝ) / n) ^ 2 := by
  have h_split : ∑ n ∈ Finset.Ioc 0 N, ‖momCoeff a P k n‖ ^ 2 / (n : ℝ) ^ 2 =
      ∑ n ∈ tupleProducts P k, ‖primePolyCoeff a P k n‖ ^ 2 / (n : ℝ) ^ 2 := by
    rw [← Finset.sum_subset h_sub]
    · apply Finset.sum_congr rfl
      intro n hn
      dsimp [momCoeff]
      split_ifs
      rfl
    · intro n _hn_Ioc hn_not
      dsimp [momCoeff]
      split_ifs
      simp
  rw [h_split]
  apply Finset.sum_le_sum
  intro n _hn
  have h_norm : ‖primePolyCoeff a P k n‖ ≤ (tupleCount P k n : ℝ) := by
    dsimp [primePolyCoeff, tupleCount]
    refine (norm_sum_le _ _).trans ?_
    have h1 : (∑ v ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun v => ∏ i, v i = n), ∏ i, ‖a (v i)‖) ≤
        ∑ v ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun v => ∏ i, v i = n), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      rw [← Finset.prod_const_one]
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => ha (v i))
    have h2 : (∑ v ∈ (Fintype.piFinset fun _ : Fin k => P).filter (fun v => ∏ i, v i = n), (1 : ℝ)) =
        (((Fintype.piFinset fun _ : Fin k => P).filter (fun v => ∏ i, v i = n)).card : ℝ) := by
      simp
    refine (Finset.sum_le_sum fun v _ => ?_).trans (h1.trans_eq h2)
    rw [norm_prod]
  have h_sq : ‖primePolyCoeff a P k n‖ ^ 2 ≤ (tupleCount P k n : ℝ) ^ 2 := by
    nlinarith [norm_nonneg (primePolyCoeff a P k n)]
  have h_div : ((tupleCount P k n : ℝ) / n) ^ 2 = (tupleCount P k n : ℝ) ^ 2 / (n : ℝ) ^ 2 := by ring
  rw [h_div]
  exact div_le_div_of_nonneg_right h_sq (sq_nonneg _)

/-- Mean-square coefficient bound for prime polynomials over $(P, 2P]$. -/
lemma sum_momCoeff_sq_primes_le (a : ℕ → ℂ) (ha : ∀ p, ‖a p‖ ≤ 1) (P : ℕ) (hP : 2 ≤ P) (k : ℕ) :
    let P_set := (Finset.Ioc P (2 * P)).filter Nat.Prime
    let N := (2 * P) ^ k
    ∑ n ∈ Finset.Ioc 0 N, ‖momCoeff a P_set k n‖ ^ 2 / (n : ℝ) ^ 2 ≤
      (k.factorial : ℝ) / (P : ℝ) ^ k * (4 / Real.log (P : ℝ)) ^ k := by
  intro P_set N
  have h_pos : ∀ p ∈ P_set, 0 < p := by
    intro p hp
    have : P < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    omega
  have h_le : ∀ p ∈ P_set, p ≤ 2 * P := by
    intro p hp
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  have h_sub : tupleProducts P_set k ⊆ Finset.Ioc 0 N := tupleProducts_subset_Ioc k h_pos h_le
  have h_le1 := sum_momCoeff_sq_div_sq_le a ha P_set k N h_sub
  have hP_pos : 0 < (P : ℝ) := by positivity
  have hprime : ∀ p ∈ P_set, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have hlow : ∀ p ∈ P_set, (P : ℝ) ≤ p := by
    intro p hp
    have : P < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    exact_mod_cast (by omega : P ≤ p)
  have h_le2 := sum_sq_tupleCount_div_le P_set k (P : ℝ) hP_pos hprime hlow
  have h_inv := sum_inv_primes_Ioc_two_mul_le P hP
  have h_pow_le : (∑ p ∈ P_set, (1 : ℝ) / p) ^ k ≤ (4 / Real.log (P : ℝ)) ^ k := by
    gcongr
  have h_le3 : (k.factorial : ℝ) / (P : ℝ) ^ k * (∑ p ∈ P_set, (1 : ℝ) / p) ^ k ≤
      (k.factorial : ℝ) / (P : ℝ) ^ k * (4 / Real.log (P : ℝ)) ^ k := by
    exact mul_le_mul_of_nonneg_left h_pow_le (by positivity)
  exact h_le1.trans (h_le2.trans h_le3)

/-- Raw discrete mean value bound on well-spaced points. -/
theorem card_wellSpaced_prime_poly_raw_bound (P : ℕ) (a : ℕ → ℂ) (T V : ℝ) (S : Finset ℝ) (k : ℕ)
    (hP : 2 ≤ P) (hT : 1 ≤ T) (_hV : 1 ≤ V) (_hk : 1 ≤ k) (ha : ∀ p, ‖a p‖ ≤ 1)
    (hS : WellSpaced S) (hST : ∀ t ∈ S, |t| ≤ T)
    (hV_le : ∀ t ∈ S, V⁻¹ ≤ ‖dirichletPoly a ((Finset.Ioc P (2 * P)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I)‖) :
    (S.card : ℝ) ≤ 100 * (T + ((2 * P : ℕ) ^ k : ℝ)) * Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) *
      ((k.factorial : ℝ) / (P : ℝ) ^ k * (4 / Real.log (P : ℝ)) ^ k) * V ^ (2 * k) := by
  set N := (2 * P) ^ k
  have hN : 1 ≤ N := by
    dsimp [N]
    have : 1 ≤ 2 * P := by omega
    exact one_le_pow₀ this
  have h_dmv := sum_wellSpaced_norm_sq_dirichletPoly_le (momCoeff a ((Finset.Ioc P (2 * P)).filter Nat.Prime) k) N hN T hT S hS hST
  set P_set := (Finset.Ioc P (2 * P)).filter Nat.Prime
  have h_pos : ∀ p ∈ P_set, 0 < p := by
    intro p hp
    have : P < p := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    omega
  have h_le : ∀ p ∈ P_set, p ≤ 2 * P := by
    intro p hp
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
  have h_sub : tupleProducts P_set k ⊆ Finset.Ioc 0 N := tupleProducts_subset_Ioc k h_pos h_le
  have h_poly_eq (t : ℝ) :
      dirichletPoly (momCoeff a P_set k) (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I) =
      (dirichletPoly a P_set ((1 : ℂ) + t * Complex.I)) ^ k :=
    dirichletPoly_momCoeff_eq_pow a P_set k _ h_pos N h_sub
  have h_term_lb (t : ℝ) (ht : t ∈ S) :
      (V⁻¹ : ℝ) ^ (2 * k) ≤ ‖dirichletPoly (momCoeff a P_set k) (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    rw [h_poly_eq t, norm_pow, ← pow_mul]
    have hV_inv_nonneg : 0 ≤ (V⁻¹ : ℝ) := by positivity
    have hV_t := hV_le t ht
    rw [mul_comm 2 k]
    gcongr
  have h_sum_lb : (S.card : ℝ) * (V⁻¹ : ℝ) ^ (2 * k) ≤
      ∑ t ∈ S, ‖dirichletPoly (momCoeff a P_set k) (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    have h_c : (∑ _t ∈ S, (V⁻¹ : ℝ) ^ (2 * k)) = (S.card : ℝ) * (V⁻¹ : ℝ) ^ (2 * k) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← h_c]
    exact Finset.sum_le_sum h_term_lb
  have h_coeff_le := sum_momCoeff_sq_primes_le a ha P hP k
  have h_dmv_trans : (S.card : ℝ) * (V⁻¹ : ℝ) ^ (2 * k) ≤
      100 * (T + (N : ℝ)) * Real.log (2 * (N : ℝ)) * ((k.factorial : ℝ) / (P : ℝ) ^ k * (4 / Real.log (P : ℝ)) ^ k) := by
    refine h_sum_lb.trans (h_dmv.trans ?_)
    have hN_ge_one : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have h_two_N : 1 ≤ 2 * (N : ℝ) := by linarith
    have h_log_nonneg : 0 ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg h_two_N
    have h_nonneg : 0 ≤ 100 * (T + (N : ℝ)) * Real.log (2 * (N : ℝ)) := by positivity
    exact mul_le_mul_of_nonneg_left h_coeff_le h_nonneg
  have hV_pos : 0 < V := by linarith
  have h_mul_V : ((S.card : ℝ) * (V⁻¹ : ℝ) ^ (2 * k)) * V ^ (2 * k) ≤
      (100 * (T + (N : ℝ)) * Real.log (2 * (N : ℝ)) * ((k.factorial : ℝ) / (P : ℝ) ^ k * (4 / Real.log (P : ℝ)) ^ k)) * V ^ (2 * k) := by
    exact mul_le_mul_of_nonneg_right h_dmv_trans (by positivity)
  have h_cancel : ((S.card : ℝ) * (V⁻¹ : ℝ) ^ (2 * k)) * V ^ (2 * k) = (S.card : ℝ) := by
    rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (ne_of_gt hV_pos), one_pow, mul_one]
  rw [h_cancel] at h_mul_V
  have hN_eq : (N : ℝ) = ((2 * P : ℕ) ^ k : ℝ) := by
    dsimp [N]
    push_cast
    rfl
  rw [hN_eq] at h_mul_V
  exact h_mul_V

/-- Pointwise bound on powers of $V$ in terms of $T^{2 \log V / \log P} V^2$. -/
lemma V_pow_le (V T : ℝ) (P : ℕ) (k : ℕ) (hV : 1 ≤ V) (hT : 1 ≤ T) (hP : 2 ≤ P)
    (hk : (k : ℝ) - 1 ≤ Real.log T / Real.log (P : ℝ)) :
    V ^ (2 * k) ≤ T ^ (2 * Real.log V / Real.log (P : ℝ)) * V ^ 2 := by
  have hV_pos : 0 < V := by linarith
  have hT_pos : 0 < T := by linarith
  have hP_gt_one : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have _hlogP_pos : 0 < Real.log (P : ℝ) := Real.log_pos hP_gt_one
  have hlogV_nonneg : 0 ≤ Real.log V := Real.log_nonneg hV
  have _hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  by_cases hk0 : k = 0
  · subst hk0
    simp
    have : 0 ≤ 2 * Real.log V / Real.log (P : ℝ) := by positivity
    have : 1 ≤ T ^ (2 * Real.log V / Real.log (P : ℝ)) := Real.one_le_rpow hT this
    nlinarith
  · have hk_ge_1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have h_split : 2 * k = 2 * (k - 1) + 2 := by omega
    rw [h_split, pow_add]
    have h_k_sub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk_ge_1, Nat.cast_one]
    have h_exp1 : V ^ (2 * (k - 1)) = Real.exp ((2 * ((k : ℝ) - 1)) * Real.log V) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hV_pos]
      congr 1
      push_cast
      rw [h_k_sub]
      ring
    have h_exp2 : T ^ (2 * Real.log V / Real.log (P : ℝ)) =
        Real.exp ((2 * Real.log V / Real.log (P : ℝ)) * Real.log T) := by
      rw [Real.rpow_def_of_pos hT_pos]
      congr 1
      ring
    rw [h_exp1, h_exp2]
    have h_le : 2 * ((k : ℝ) - 1) * Real.log V ≤ (2 * Real.log V / Real.log (P : ℝ)) * Real.log T := by
      have : 2 * ((k : ℝ) - 1) ≤ 2 * (Real.log T / Real.log (P : ℝ)) := by linarith
      have h1 : 2 * ((k : ℝ) - 1) * Real.log V ≤ 2 * (Real.log T / Real.log (P : ℝ)) * Real.log V := by
        exact mul_le_mul_of_nonneg_right this hlogV_nonneg
      have h2 : 2 * (Real.log T / Real.log (P : ℝ)) * Real.log V =
          (2 * Real.log V / Real.log (P : ℝ)) * Real.log T := by ring
      linarith
    have h_exp_le : Real.exp (2 * ((k : ℝ) - 1) * Real.log V) ≤
        Real.exp ((2 * Real.log V / Real.log (P : ℝ)) * Real.log T) := Real.exp_le_exp.mpr h_le
    exact mul_le_mul_of_nonneg_right h_exp_le (by positivity)

/-- Geometric bound on $(T + (2P)^k)/P^k \le 2 \cdot 2^k$. -/
lemma T_add_pow_two_P_div_le (T : ℝ) (P : ℕ) (k : ℕ) (hT : 1 ≤ T) (hP : 2 ≤ P) (_hk : 1 ≤ k)
    (hk_ceil : Real.log T / Real.log (P : ℝ) ≤ (k : ℝ)) :
    (T + ((2 * P : ℕ) ^ k : ℝ)) / (P : ℝ) ^ k ≤ 2 * 2 ^ k := by
  have hP_gt_one : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hlogP_pos : 0 < Real.log (P : ℝ) := Real.log_pos hP_gt_one
  have hT_pos : 0 < T := by linarith
  have hPk_pos : 0 < (P : ℝ) ^ k := by positivity
  have h_log_T_le : Real.log T ≤ (k : ℝ) * Real.log (P : ℝ) := by
    exact (div_le_iff₀ hlogP_pos).mp hk_ceil
  have h_T_le_Pk : T ≤ (P : ℝ) ^ k := by
    rw [← Real.exp_log hT_pos]
    have h_exp : (P : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log (P : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity)]
      ring_nf
    rw [h_exp]
    exact Real.exp_le_exp.mpr h_log_T_le
  have h_div_le_one : T / (P : ℝ) ^ k ≤ 1 := by
    exact (div_le_one₀ hPk_pos).mpr h_T_le_Pk
  have h_two_P : ((2 * P : ℕ) ^ k : ℝ) = 2 ^ k * (P : ℝ) ^ k := by
    push_cast
    ring
  have h_frac_eq : (T + ((2 * P : ℕ) ^ k : ℝ)) / (P : ℝ) ^ k =
      T / (P : ℝ) ^ k + 2 ^ k := by
    rw [h_two_P, add_div, mul_div_cancel_right₀ _ (ne_of_gt hPk_pos)]
  rw [h_frac_eq]
  have h_one_le_two_k : (1 : ℝ) ≤ 2 ^ k := by
    have : (1 : ℝ) ≤ 2 := by norm_num
    exact one_le_pow₀ this
  linarith

/-- Logarithmic bound on $\log(2 (2P)^k) \le 4 k \log P$. -/
lemma log_two_mul_pow_two_P_le (P : ℕ) (k : ℕ) (hP : 2 ≤ P) (hk : 1 ≤ k) :
    Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) ≤ 4 * (k : ℝ) * Real.log (P : ℝ) := by
  have hP_gt_one : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hlogP_pos : 0 < Real.log (P : ℝ) := Real.log_pos hP_gt_one
  have hlog2_le_logP : Real.log 2 ≤ Real.log (P : ℝ) := by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    exact Real.log_le_log (by norm_num) this
  have _hlog2_pos : 0 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h2Pk_pos : 0 < ((2 * P : ℕ) ^ k : ℝ) := by positivity
  have h_eq : Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) =
      Real.log 2 + (k : ℝ) * (Real.log 2 + Real.log (P : ℝ)) := by
    rw [Real.log_mul two_ne_zero (ne_of_gt h2Pk_pos)]
    have : ((2 * P : ℕ) ^ k : ℝ) = (2 * (P : ℝ)) ^ k := by push_cast; rfl
    rw [this, Real.log_pow, Real.log_mul two_ne_zero (by positivity)]
  rw [h_eq]
  have hk_real : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have h1 : Real.log 2 ≤ (k : ℝ) * Real.log (P : ℝ) := by
    calc Real.log 2 ≤ Real.log (P : ℝ) := hlog2_le_logP
    _ = 1 * Real.log (P : ℝ) := by ring
    _ ≤ (k : ℝ) * Real.log (P : ℝ) := mul_le_mul_of_nonneg_right hk_real hlogP_pos.le
  have h2 : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * Real.log (P : ℝ) :=
    mul_le_mul_of_nonneg_left hlog2_le_logP (by positivity)
  linarith

/-- Linear bound $k \le 3^{k-1}$. -/
lemma k_le_pow_three (k : ℕ) (hk : 1 ≤ k) : (k : ℝ) ≤ 3 ^ (k - 1) := by
  induction' k using Nat.strong_induction_on with k ih
  rcases k with _ | k
  · contradiction
  rcases k with _ | k
  · simp
  · have hk2 : 1 ≤ k + 1 := by omega
    have ih1 := ih (k + 1) (by omega) hk2
    have h_sub : k + 2 - 1 = k + 1 := rfl
    have h_sub' : k + 1 - 1 = k := rfl
    rw [h_sub]
    rw [h_sub'] at ih1
    have : ((k + 2 : ℕ) : ℝ) ≤ 3 * ((k + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    refine this.trans ?_
    have h3 : 3 * ((k + 1 : ℕ) : ℝ) ≤ 3 * (3 ^ k : ℝ) := by
      exact mul_le_mul_of_nonneg_left ih1 (by norm_num)
    have h_pow : 3 * (3 ^ k : ℝ) = 3 ^ (k + 1) := by
      rw [pow_succ]
      ring
    rwa [h_pow] at h3

/-- Numerical bound relating $\log 2$ to quadratic growth. -/
lemma num_bound_log2 : 3 * (8 / (5 * Real.log 2)) ≤ (Real.log 2 + 2) ^ 2 := by
  have hlog2_lb : (69 : ℝ) / 100 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h_lhs : 3 * (8 / (5 * Real.log 2)) < 3 * (8 / (5 * (69 / 100))) := by
    have : 5 * (69 / 100 : ℝ) < 5 * Real.log 2 := by linarith
    have : 8 / (5 * Real.log 2) < 8 / (5 * (69 / 100)) := by
      exact div_lt_div_of_pos_left (by norm_num) (by linarith) this
    linarith
  have h_rhs : ( (69 / 100 : ℝ) + 2 ) ^ 2 < (Real.log 2 + 2) ^ 2 := by
    have : 0 ≤ (69 / 100 : ℝ) + 2 := by norm_num
    have : (69 / 100 : ℝ) + 2 < Real.log 2 + 2 := by linarith
    nlinarith
  have h_num : 3 * (8 / (5 * (69 / 100 : ℝ))) ≤ ( (69 / 100 : ℝ) + 2 ) ^ 2 := by
    norm_num
  linarith

/-- Geometric-to-exponential absorption: $k (8 / (5 \log P))^{k-1} \le \exp(2 (\log T / \log P) \log(\log T + 2))$. -/
lemma k_mul_ratio_le_exp (P : ℕ) (T : ℝ) (k : ℕ) (hP : 2 ≤ P) (hT : 1 ≤ T) (hk : 1 ≤ k)
    (hk_ceil : k = ⌈Real.log T / Real.log (P : ℝ)⌉₊) :
    (k : ℝ) * (8 / (5 * Real.log (P : ℝ))) ^ (k - 1) ≤
      Real.exp (2 * (Real.log T / Real.log (P : ℝ)) * Real.log (Real.log T + 2)) := by
  set x := Real.log T / Real.log (P : ℝ)
  have hP_gt_one : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hlogP_pos : 0 < Real.log (P : ℝ) := Real.log_pos hP_gt_one
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  have _hx_nonneg : 0 ≤ x := div_nonneg hlogT_nonneg hlogP_pos.le
  have hlog2_le_logP : Real.log 2 ≤ Real.log (P : ℝ) := by
    have : (2 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    exact Real.log_le_log (by norm_num) this
  have _hlog2_pos : 0 < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  by_cases hk1 : k = 1
  · subst hk1
    have h1 : (1 : ℝ) ≤ Real.exp (2 * x * Real.log (Real.log T + 2)) := by
      have h2 : 0 ≤ 2 * x * Real.log (Real.log T + 2) := by
        have : 0 ≤ Real.log (Real.log T + 2) := by
          apply Real.log_nonneg
          linarith
        positivity
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (2 * x * Real.log (Real.log T + 2)) := Real.exp_le_exp.mpr h2
    simpa using h1
  · have hk_ge_2 : 2 ≤ k := by omega
    have hk_ge_1 : 1 ≤ k := by omega
    have h_cast : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hk_ge_1, Nat.cast_one]
    have hk_sub_lt_x : (k : ℝ) - 1 < x := by
      by_contra! h_le
      rw [h_cast] at h_le
      have h_ceil_le : ⌈x⌉₊ ≤ k - 1 := Nat.ceil_le.mpr h_le
      omega
    have h1_lt_x : 1 < x := by
      have : (1 : ℝ) ≤ (k : ℝ) - 1 := by
        have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge_2
        linarith
      exact this.trans_lt hk_sub_lt_x
    have hlogP_lt_logT : Real.log (P : ℝ) < Real.log T := by
      have := (lt_div_iff₀ hlogP_pos).mp h1_lt_x
      linarith
    have _hlog2_lt_logT : Real.log 2 < Real.log T := hlog2_le_logP.trans_lt hlogP_lt_logT
    have h_denom : 5 * Real.log 2 ≤ 5 * Real.log (P : ℝ) := by linarith
    have h_div : 8 / (5 * Real.log (P : ℝ)) ≤ 8 / (5 * Real.log 2) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) h_denom
    have h_step1 : 3 * (8 / (5 * Real.log (P : ℝ))) ≤ 3 * (8 / (5 * Real.log 2)) := by linarith
    have h_step2 := num_bound_log2
    have h_step3 : (Real.log 2 + 2) ^ 2 ≤ (Real.log T + 2) ^ 2 := by
      have : 0 ≤ Real.log 2 + 2 := by linarith
      have : Real.log 2 + 2 ≤ Real.log T + 2 := by linarith
      nlinarith
    have h_base_le : 3 * (8 / (5 * Real.log (P : ℝ))) ≤ (Real.log T + 2) ^ 2 :=
      h_step1.trans (h_step2.trans h_step3)
    have h_pow_le : (3 * (8 / (5 * Real.log (P : ℝ)))) ^ (k - 1) ≤
        ((Real.log T + 2) ^ 2) ^ (k - 1) := by
      have : 0 ≤ 3 * (8 / (5 * Real.log (P : ℝ))) := by positivity
      gcongr
    have h_k_le := k_le_pow_three k hk
    have h_mul_le : (k : ℝ) * (8 / (5 * Real.log (P : ℝ))) ^ (k - 1) ≤
        (3 ^ (k - 1) : ℝ) * (8 / (5 * Real.log (P : ℝ))) ^ (k - 1) :=
      mul_le_mul_of_nonneg_right h_k_le (by positivity)
    have h_mul_eq : (3 ^ (k - 1) : ℝ) * (8 / (5 * Real.log (P : ℝ))) ^ (k - 1) =
        (3 * (8 / (5 * Real.log (P : ℝ)))) ^ (k - 1) := by
      rw [← mul_pow]
    rw [h_mul_eq] at h_mul_le
    have h_chain := h_mul_le.trans h_pow_le
    refine h_chain.trans ?_
    have h_log_T_add_2_pos : 0 < Real.log T + 2 := by linarith
    have h_sq_pow : ((Real.log T + 2) ^ 2) ^ (k - 1) =
        (Real.log T + 2) ^ (2 * (k - 1)) := by
      rw [← pow_mul]
    rw [h_sq_pow]
    have h_k_sub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      rw [Nat.cast_sub hk_ge_1, Nat.cast_one]
    have h_rpow : (Real.log T + 2) ^ (2 * (k - 1)) =
        Real.exp ((2 * ((k : ℝ) - 1)) * Real.log (Real.log T + 2)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos h_log_T_add_2_pos]
      congr 1
      push_cast
      rw [← h_cast]
      ring
    rw [h_rpow]
    have h_exp_mono : 2 * ((k : ℝ) - 1) * Real.log (Real.log T + 2) ≤
        2 * x * Real.log (Real.log T + 2) := by
      have : 0 ≤ Real.log (Real.log T + 2) := by
        apply Real.log_nonneg
        linarith
      have : 2 * ((k : ℝ) - 1) ≤ 2 * x := by linarith
      exact mul_le_mul_of_nonneg_right this (by positivity)
    exact Real.exp_le_exp.mpr h_exp_mono

/-- Trivial bound on well-spaced card when $T = 1$. -/
lemma card_wellSpaced_le_of_T_eq_one (S : Finset ℝ) (hS : WellSpaced S) (hST : ∀ t ∈ S, |t| ≤ 1) :
    (S.card : ℝ) ≤ 200 := by
  have h_dmv := sum_wellSpaced_norm_sq_dirichletPoly_le (fun _ => (1 : ℂ)) 1 le_rfl 1 le_rfl S hS hST
  have h_ioc : (Finset.Ioc 0 1 : Finset ℕ) = {1} := by decide
  have h_poly (t : ℝ) : dirichletPoly (fun _ => (1 : ℂ)) (Finset.Ioc 0 1) ((1 : ℂ) + t * Complex.I) = 1 := by
    rw [h_ioc]
    dsimp [dirichletPoly]
    rw [Finset.sum_singleton]
    have : ((1 : ℕ) : ℂ) = (1 : ℂ) := by norm_num
    rw [this, Complex.one_cpow, mul_one]
  have h_sum : (∑ t ∈ S, ‖dirichletPoly (fun _ => (1 : ℂ)) (Finset.Ioc 0 1) ((1 : ℂ) + t * Complex.I)‖ ^ 2) = (S.card : ℝ) := by
    simp_rw [h_poly, norm_one, one_pow]
    simp
  rw [h_sum] at h_dmv
  have h_rhs_sum : (∑ n ∈ (Finset.Ioc 0 1 : Finset ℕ), ‖(1 : ℂ)‖ ^ 2 / (n : ℝ) ^ 2) = 1 := by
    rw [h_ioc, Finset.sum_singleton]
    norm_num
  rw [h_rhs_sum] at h_dmv
  have _hlog2_le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos zero_lt_two
    linarith
  refine h_dmv.trans ?_
  have : (100 : ℝ) * (1 + (1 : ℝ)) * Real.log (2 * (1 : ℝ)) * 1 = 200 * Real.log 2 := by ring_nf
  push_cast at this ⊢
  rw [this]
  linarith

/-- Matomäki–Radziwiłł Lemma 8: large values of prime Dirichlet polynomials via moments. -/
theorem card_wellSpaced_large_prime_poly_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : ℕ) (a : ℕ → ℂ) (T V : ℝ) (S : Finset ℝ),
      2 ≤ P → 1 ≤ T → 1 ≤ V → (∀ p, ‖a p‖ ≤ 1) → WellSpaced S → (∀ t ∈ S, |t| ≤ T) →
      (∀ t ∈ S, V⁻¹ ≤ ‖dirichletPoly a ((Finset.Ioc P (2 * P)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I)‖) →
      (S.card : ℝ) ≤ C * T ^ (2 * Real.log V / Real.log P) * V ^ 2 *
        Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T + 2)) * 5 ^ ⌈Real.log T / Real.log P⌉₊ * (⌈Real.log T / Real.log P⌉₊).factorial := by
  use 2000
  refine ⟨by norm_num, ?_⟩
  intro P a T V S hP hT hV ha hS hST hV_le
  set x := Real.log T / Real.log (P : ℝ)
  set k := ⌈x⌉₊
  have hk_def : k = ⌈x⌉₊ := rfl
  have hP_gt_one : 1 < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hlogP_pos : 0 < Real.log (P : ℝ) := Real.log_pos hP_gt_one
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  have hx_nonneg : 0 ≤ x := div_nonneg hlogT_nonneg hlogP_pos.le
  have hT_pos : 0 < T := by linarith
  have _hV_pos : 0 < V := by linarith
  by_cases hk0 : k = 0
  · -- Case k = 0: implies T = 1
    have h_ceil_zero : ⌈x⌉₊ = 0 := by rw [← hk_def, hk0]
    have hx_le_zero : x ≤ 0 := by
      have := Nat.ceil_le.mp (le_of_eq h_ceil_zero)
      exact_mod_cast this
    have hx_zero : x = 0 := le_antisymm hx_le_zero hx_nonneg
    have hlogT_zero : Real.log T = 0 := by
      have : x * Real.log (P : ℝ) = 0 := by rw [hx_zero, zero_mul]
      dsimp [x] at this
      rwa [div_mul_cancel₀ _ (ne_of_gt hlogP_pos)] at this
    have hT1 : T = 1 := by
      have := Real.exp_log hT_pos
      rw [hlogT_zero, Real.exp_zero] at this
      exact this.symm
    have hST1 : ∀ t ∈ S, |t| ≤ 1 := by
      intro t ht
      have := hST t ht
      rwa [hT1] at this
    have h_card_le := card_wellSpaced_le_of_T_eq_one S hS hST1
    have h_RHS : 200 ≤ (2000 : ℝ) * T ^ (2 * Real.log V / Real.log (P : ℝ)) * V ^ 2 *
        Real.exp (2 * x * Real.log (Real.log T + 2)) * 5 ^ k * (k.factorial : ℝ) := by
      have hT_pow : T ^ (2 * Real.log V / Real.log (P : ℝ)) = 1 := by
        rw [hT1, Real.one_rpow]
      have hk_pow : (5 : ℝ) ^ k = 1 := by rw [hk0, pow_zero]
      have hk_fact : (k.factorial : ℝ) = 1 := by rw [hk0, Nat.factorial_zero, Nat.cast_one]
      have hexp : Real.exp (2 * x * Real.log (Real.log T + 2)) = 1 := by
        rw [hx_zero]
        ring_nf
        exact Real.exp_zero
      rw [hT_pow, hk_pow, hk_fact, hexp]
      have _hV2 : 1 ≤ V ^ 2 := by
        nlinarith
      nlinarith
    exact h_card_le.trans h_RHS
  · -- Case k ≥ 1
    have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have h_raw := card_wellSpaced_prime_poly_raw_bound P a T V S k hP hT hV hk ha hS hST hV_le
    have hk_ceil_le : x ≤ (k : ℝ) := Nat.le_ceil x
    have h_ceil_eq : k = ⌈x⌉₊ := rfl
    have hk_ceil_ge : (k : ℝ) - 1 ≤ x := by
      have hk_ge_1 : 1 ≤ k := hk
      have h_cast : (k : ℝ) - 1 = ((k - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hk_ge_1, Nat.cast_one]
      by_contra! h_lt
      rw [h_cast] at h_lt
      have h_ceil_le : ⌈x⌉₊ ≤ k - 1 := Nat.ceil_le.mpr h_lt.le
      omega
    have hV_pow := V_pow_le V T P k hV hT hP hk_ceil_ge
    have h_geom := T_add_pow_two_P_div_le T P k hT hP hk hk_ceil_le
    have h_log := log_two_mul_pow_two_P_le P k hP hk
    have h_ratio := k_mul_ratio_le_exp P T k hP hT hk h_ceil_eq
    have _hPk_pos : 0 < (P : ℝ) ^ k := by positivity
    have h_fact_nonneg : 0 ≤ (k.factorial : ℝ) := by positivity
    have h_inner_le : 100 * ((T + ((2 * P : ℕ) ^ k : ℝ)) / (P : ℝ) ^ k) * Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) * (4 / Real.log (P : ℝ)) ^ k ≤
        1280 * Real.exp (2 * x * Real.log (Real.log T + 2)) * 5 ^ k := by
      have h1 : 100 * ((T + ((2 * P : ℕ) ^ k : ℝ)) / (P : ℝ) ^ k) ≤ 100 * (2 * 2 ^ k) := by
        exact mul_le_mul_of_nonneg_left h_geom (by norm_num)
      have h2 : Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) ≤ 4 * (k : ℝ) * Real.log (P : ℝ) := h_log
      have h3 : 100 * ((T + ((2 * P : ℕ) ^ k : ℝ)) / (P : ℝ) ^ k) * Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) ≤
          (100 * (2 * 2 ^ k)) * (4 * (k : ℝ) * Real.log (P : ℝ)) := by
        have : 0 ≤ 100 * ((T + ((2 * P : ℕ) ^ k : ℝ)) / (P : ℝ) ^ k) := by positivity
        have : 0 ≤ Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) := by
          have : 1 ≤ 2 * ((2 * P : ℕ) ^ k : ℝ) := by
            have : 1 ≤ ((2 * P : ℕ) ^ k : ℝ) := by
              have : 1 ≤ 2 * P := by omega
              exact_mod_cast one_le_pow₀ this
            linarith
          exact Real.log_nonneg this
        gcongr
      have h4 : 100 * ((T + ((2 * P : ℕ) ^ k : ℝ)) / (P : ℝ) ^ k) * Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) * (4 / Real.log (P : ℝ)) ^ k ≤
          (100 * (2 * 2 ^ k)) * (4 * (k : ℝ) * Real.log (P : ℝ)) * (4 / Real.log (P : ℝ)) ^ k := by
        have : 0 ≤ (4 / Real.log (P : ℝ)) ^ k := by positivity
        gcongr
      refine h4.trans ?_
      have h_pow_split : (4 / Real.log (P : ℝ)) ^ k = (4 / Real.log (P : ℝ)) * (4 / Real.log (P : ℝ)) ^ (k - 1) := by
        have : k = (k - 1) + 1 := by omega
        nth_rw 1 [this]
        rw [pow_succ]
        ring
      have h_2_pow_split : (2 : ℝ) ^ k = 2 * (2 : ℝ) ^ (k - 1) := by
        have : k = (k - 1) + 1 := by omega
        nth_rw 1 [this]
        rw [pow_succ]
        ring
      have h_5_pow_split : (5 : ℝ) ^ k = 5 * (5 : ℝ) ^ (k - 1) := by
        have : k = (k - 1) + 1 := by omega
        nth_rw 1 [this]
        rw [pow_succ]
        ring
      have h_alg : (100 * (2 * (2 : ℝ) ^ k)) * (4 * (k : ℝ) * Real.log (P : ℝ)) * (4 / Real.log (P : ℝ)) ^ k =
          (6400 : ℝ) * (5 : ℝ) ^ (k - 1) * ((k : ℝ) * (8 / (5 * Real.log (P : ℝ))) ^ (k - 1)) := by
        rw [h_pow_split, h_2_pow_split]
        have hlogP_ne : Real.log (P : ℝ) ≠ 0 := ne_of_gt hlogP_pos
        have h_pow_prod : (2 : ℝ) ^ (k - 1) * (4 / Real.log (P : ℝ)) ^ (k - 1) =
            (8 / Real.log (P : ℝ)) ^ (k - 1) := by
          rw [← mul_pow]
          ring_nf
        have h_pow_five : (8 / Real.log (P : ℝ)) ^ (k - 1) =
            (5 : ℝ) ^ (k - 1) * (8 / (5 * Real.log (P : ℝ))) ^ (k - 1) := by
          rw [← mul_pow]
          congr 1
          ring
        calc (100 * (2 * (2 * (2 : ℝ) ^ (k - 1)))) * (4 * (k : ℝ) * Real.log (P : ℝ)) *
            ((4 / Real.log (P : ℝ)) * (4 / Real.log (P : ℝ)) ^ (k - 1)) =
            (100 * 2 * 2 * 4 * 4) * (Real.log (P : ℝ) * (1 / Real.log (P : ℝ))) * (k : ℝ) *
            ((2 : ℝ) ^ (k - 1) * (4 / Real.log (P : ℝ)) ^ (k - 1)) := by ring
        _ = 6400 * 1 * (k : ℝ) * (8 / Real.log (P : ℝ)) ^ (k - 1) := by
          rw [mul_one_div_cancel hlogP_ne, h_pow_prod]
          ring
        _ = (6400 : ℝ) * (5 : ℝ) ^ (k - 1) * ((k : ℝ) * (8 / (5 * Real.log (P : ℝ))) ^ (k - 1)) := by
          rw [h_pow_five]
          ring
      rw [h_alg]
      have h_ratio_mul : (6400 : ℝ) * (5 : ℝ) ^ (k - 1) * ((k : ℝ) * (8 / (5 * Real.log (P : ℝ))) ^ (k - 1)) ≤
          (6400 : ℝ) * (5 : ℝ) ^ (k - 1) * Real.exp (2 * x * Real.log (Real.log T + 2)) := by
        have : 0 ≤ (6400 : ℝ) * (5 : ℝ) ^ (k - 1) := by positivity
        gcongr
      have h_eq_target : (6400 : ℝ) * (5 : ℝ) ^ (k - 1) * Real.exp (2 * x * Real.log (Real.log T + 2)) =
          1280 * Real.exp (2 * x * Real.log (Real.log T + 2)) * 5 ^ k := by
        rw [h_5_pow_split]
        ring
      exact h_ratio_mul.trans_eq h_eq_target
    have h_coeff_total : 100 * (T + ((2 * P : ℕ) ^ k : ℝ)) * Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) *
        ((k.factorial : ℝ) / (P : ℝ) ^ k * (4 / Real.log (P : ℝ)) ^ k) ≤
        1280 * Real.exp (2 * x * Real.log (Real.log T + 2)) * 5 ^ k * (k.factorial : ℝ) := by
      have h_reorg : 100 * (T + ((2 * P : ℕ) ^ k : ℝ)) * Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) *
          ((k.factorial : ℝ) / (P : ℝ) ^ k * (4 / Real.log (P : ℝ)) ^ k) =
          (100 * ((T + ((2 * P : ℕ) ^ k : ℝ)) / (P : ℝ) ^ k) * Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) * (4 / Real.log (P : ℝ)) ^ k) * (k.factorial : ℝ) := by ring
      rw [h_reorg]
      have : (100 * ((T + ((2 * P : ℕ) ^ k : ℝ)) / (P : ℝ) ^ k) * Real.log (2 * ((2 * P : ℕ) ^ k : ℝ)) * (4 / Real.log (P : ℝ)) ^ k) * (k.factorial : ℝ) ≤
          (1280 * Real.exp (2 * x * Real.log (Real.log T + 2)) * 5 ^ k) * (k.factorial : ℝ) :=
        mul_le_mul_of_nonneg_right h_inner_le h_fact_nonneg
      exact this
    have h_combine := h_raw.trans (mul_le_mul h_coeff_total hV_pow (by positivity) (by positivity))
    refine h_combine.trans ?_
    have h_factor : 1280 * Real.exp (2 * x * Real.log (Real.log T + 2)) * 5 ^ k * (k.factorial : ℝ) *
        (T ^ (2 * Real.log V / Real.log (P : ℝ)) * V ^ 2) =
        1280 * T ^ (2 * Real.log V / Real.log (P : ℝ)) * V ^ 2 *
        Real.exp (2 * x * Real.log (Real.log T + 2)) * 5 ^ k * (k.factorial : ℝ) := by ring
    rw [h_factor]
    have h_nonneg_all : 0 ≤ T ^ (2 * Real.log V / Real.log (P : ℝ)) * V ^ 2 *
        Real.exp (2 * x * Real.log (Real.log T + 2)) * 5 ^ k * (k.factorial : ℝ) := by positivity
    have h_const : (1280 : ℝ) ≤ 2000 := by norm_num
    have h_final : 1280 * (T ^ (2 * Real.log V / Real.log (P : ℝ)) * V ^ 2 *
        Real.exp (2 * x * Real.log (Real.log T + 2)) * 5 ^ k * (k.factorial : ℝ)) ≤
        2000 * (T ^ (2 * Real.log V / Real.log (P : ℝ)) * V ^ 2 *
        Real.exp (2 * x * Real.log (Real.log T + 2)) * 5 ^ k * (k.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right h_const h_nonneg_all
    linarith

end Erdos1201.MR
