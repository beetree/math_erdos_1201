/-
Copyright (c) 2026 Przemek Chojecki, ChatGPT 5.5. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Przemek Chojecki, ChatGPT 5.5
-/
import Mathlib
import Erdos1201.MR.Twisted.TwistedBounds
import Erdos1201.MR.Twisted.TwistedChebyshev
import Erdos1201.MR.Twisted.TwistedPrimeSums
import Erdos1201.MR.Analysis.WellSpaced
import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.MR.Analysis.HalaszMontgomery

/-!
# Halász Inequality for Primes

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes Lemma 11 of the paper (Halász inequality for primes in dyadic intervals)
for an abstract zero-free region, using duality and smoothed twisted Chebyshev sums.
-/

open Complex Real
open scoped BigOperators ComplexConjugate

namespace Erdos1201.MR

variable {ι κ : Type*}

private lemma norm_sum_mul_sq_le (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have hnorm : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    calc
      _ ≤ ∑ i ∈ s, ‖a i * b i‖ := norm_sum_le _ _
      _ = ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by simp_rw [Complex.norm_mul]
  calc
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ * ‖b i‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun i _ =>
        mul_nonneg (norm_nonneg (a i)) (norm_nonneg (b i)))).mpr hnorm
    _ ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖)

private lemma complex_norm_sq_cast (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

private lemma energy_nonneg (s : Finset ι) (f : ι → ℂ) :
    0 ≤ ∑ i ∈ s, ‖f i‖ ^ 2 :=
  Finset.sum_nonneg fun i _ => sq_nonneg ‖f i‖

private lemma matrix_energy_as_pairing [Fintype ι] [Fintype κ]
    (C : ι → κ → ℂ) (w : κ → ℂ) :
    (((∑ r, ‖∑ n, C r n * w n‖ ^ 2 : ℝ) : ℂ)) =
      ∑ n, w n * ∑ r, C r n * star (∑ n', C r n' * w n') := by
  calc
    (((∑ r, ‖∑ n, C r n * w n‖ ^ 2 : ℝ) : ℂ)) =
        ∑ r, star (∑ n, C r n * w n) * ∑ n, C r n * w n := by
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro r _
      exact complex_norm_sq_cast _
    _ = ∑ r, ∑ n, star (∑ n', C r n' * w n') * (C r n * w n) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ n, ∑ r, star (∑ n', C r n' * w n') * (C r n * w n) := by
      rw [Finset.sum_comm]
    _ = ∑ n, ∑ r, w n * (C r n * star (∑ n', C r n' * w n')) := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = ∑ n, w n * ∑ r, C r n * star (∑ n', C r n' * w n') := by
      simp_rw [Finset.mul_sum]

/-- Finite complex transpose duality for squared ℓ2 sums. -/
theorem duality_sum_sq
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → κ → ℂ) {D : ℝ} (hD : 0 ≤ D)
    (h_dual : ∀ η : ι → ℂ,
      (∑ k, ‖∑ i, η i * x i k‖ ^ 2) ≤ D * ∑ i, ‖η i‖ ^ 2)
    (b : κ → ℂ) :
    (∑ i, ‖∑ k, b k * x i k‖ ^ 2) ≤ D * ∑ k, ‖b k‖ ^ 2 := by
  let z : ι → ℂ := fun i => ∑ k, x i k * b k
  let v : ι → ℂ := fun i => star (z i)
  let L : ℝ := ∑ i, ‖z i‖ ^ 2
  let W : ℝ := ∑ k, ‖b k‖ ^ 2
  let R : ℝ := ∑ k, ‖∑ i, v i * x i k‖ ^ 2
  have hz_eq (i : ι) : z i = ∑ k, b k * x i k := by
    dsimp [z]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hL_eq : (∑ i, ‖∑ k, b k * x i k‖ ^ 2) = L := by
    dsimp [L]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hz_eq]
  have hL : 0 ≤ L := energy_nonneg Finset.univ z
  have hW : 0 ≤ W := energy_nonneg Finset.univ b
  have hpair : (L : ℂ) = ∑ k, b k * ∑ i, x i k * star (z i) := by
    dsimp only [L, z]
    exact matrix_energy_as_pairing x b
  have hpair2 : (L : ℂ) = ∑ k, b k * ∑ i, v i * x i k := by
    rw [hpair]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp [v]
    ring
  have hcs : L ^ 2 ≤ W * R := by
    calc
      L ^ 2 = ‖(L : ℂ)‖ ^ 2 := by rw [Complex.norm_of_nonneg hL]
      _ = ‖∑ k, b k * ∑ i, v i * x i k‖ ^ 2 := by rw [hpair2]
      _ ≤ W * R := norm_sum_mul_sq_le Finset.univ b (fun k => ∑ i, v i * x i k)
  have hR : R ≤ D * L := by
    calc
      R ≤ D * ∑ i, ‖v i‖ ^ 2 := h_dual v
      _ = D * L := by
        dsimp only [L, v]
        simp_rw [Complex.star_def, Complex.norm_conj]
  have hsq : L ^ 2 ≤ (D * W) * L := by
    calc
      L ^ 2 ≤ W * R := hcs
      _ ≤ W * (D * L) := mul_le_mul_of_nonneg_left hR hW
      _ = (D * W) * L := by ring
  have hmain : L ≤ D * W := by
    rcases hL.eq_or_lt with hLzero | hLpos
    · rw [← hLzero]
      exact mul_nonneg hD hW
    · rw [← mul_le_mul_iff_right₀ hLpos]
      simpa only [pow_two, mul_assoc, mul_comm] using hsq
  rw [hL_eq]
  exact hmain


/-! ### Well-Spaced Inverse Square Sums -/

lemma sum_inv_sq_le_two_sub_inv : ∀ K : ℕ, 1 ≤ K →
    ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 - 1 / (K : ℝ) := by
  intro K
  induction' K with K ih
  · intro h; omega
  · intro h
    by_cases hK1 : K = 0
    · subst hK1
      simp only [zero_add, Finset.Icc_self, Finset.sum_singleton, Nat.cast_one,
        one_pow, div_self, ne_eq, one_ne_zero, not_false_eq_true]
      norm_num
    have hK_ge : 1 ≤ K := by omega
    have h_split : Finset.Icc 1 (K + 1) = (Finset.Icc 1 K) ∪ {K + 1} := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]; omega
    have h_disj : Disjoint (Finset.Icc 1 K) {K + 1} := by
      rw [Finset.disjoint_singleton_right]
      simp only [Finset.mem_Icc, not_and, not_le]; intro; omega
    rw [h_split, Finset.sum_union h_disj, Finset.sum_singleton]
    have ih_val := ih hK_ge
    have h_step1 : (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2) + 1 / ((K + 1 : ℕ) : ℝ) ^ 2 ≤
        (2 - 1 / (K : ℝ)) + 1 / ((K + 1 : ℕ) : ℝ) ^ 2 := by
      linarith
    refine le_trans h_step1 ?_
    have hK_pos : 0 < (K : ℝ) := by positivity
    have hK1_pos : 0 < ((K + 1 : ℕ) : ℝ) := by positivity
    have h_step : (1 : ℝ) / ((K + 1 : ℕ) : ℝ) ^ 2 + 1 / ((K + 1 : ℕ) : ℝ) ≤ 1 / (K : ℝ) := by
      have h_eq : (1 : ℝ) / ((K + 1 : ℕ) : ℝ) ^ 2 + 1 / ((K + 1 : ℕ) : ℝ) = (((K + 1 : ℕ) : ℝ) + 1) / ((K + 1 : ℕ) : ℝ) ^ 2 := by
        have : ((K + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
        ring
      rw [h_eq]
      rw [div_le_div_iff₀ (by positivity) hK_pos]
      push_cast
      nlinarith
    linarith [h_step]

lemma sum_inv_sq_le_two (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 := by
  by_cases hK : 1 ≤ K
  · have h := sum_inv_sq_le_two_sub_inv K hK
    have : 0 ≤ (1 : ℝ) / (K : ℝ) := by positivity
    linarith
  · have : K = 0 := by omega
    subst this
    simp

lemma sum_wellSpaced_inv_sq_sub_le (S : Finset ℝ) (hS : WellSpaced S) (r : ℝ) (hr : r ∈ S) :
    ∑ s ∈ S \ {r}, (1 : ℝ) / (r - s) ^ 2 ≤ 4 := by
  by_cases h_empty : S \ {r} = ∅
  · rw [h_empty, Finset.sum_empty]; norm_num
  set K := (S \ {r}).sup (fun s => ⌊|r - s|⌋₊) with hK_def
  have hK_ge : 1 ≤ K := by
    obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr h_empty
    have hs_mem := hs
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hs
    have hdist := hS r hr s hs.1 (ne_comm.mp hs.2)
    have hk_pos : 1 ≤ ⌊|r - s|⌋₊ := by
      by_contra h
      have hk0 : ⌊|r - s|⌋₊ = 0 := by omega
      have hlt := ((Nat.floor_eq_iff (abs_nonneg _)).mp hk0).2
      norm_num at hlt
      linarith
    have hk_le : ⌊|r - s|⌋₊ ≤ K := Finset.le_sup (f := fun s => ⌊|r - s|⌋₊) hs_mem
    omega
  have h_maps : ∀ s ∈ S \ {r}, ⌊|r - s|⌋₊ ∈ Finset.Icc 1 K := by
    intro s hs
    have hs_mem := hs
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hs
    have hdist := hS r hr s hs.1 (ne_comm.mp hs.2)
    have h1 : 1 ≤ ⌊|r - s|⌋₊ := by
      by_contra h
      have hk0 : ⌊|r - s|⌋₊ = 0 := by omega
      have hlt := ((Nat.floor_eq_iff (abs_nonneg _)).mp hk0).2
      norm_num at hlt
      linarith
    have h2 : ⌊|r - s|⌋₊ ≤ K := Finset.le_sup (f := fun s => ⌊|r - s|⌋₊) hs_mem
    rw [Finset.mem_Icc]
    exact ⟨h1, h2⟩
  have h_fib := Finset.sum_fiberwise_of_maps_to (g := fun s => ⌊|r - s|⌋₊) (t := Finset.Icc 1 K)
    h_maps (fun s => (1 : ℝ) / (r - s) ^ 2)
  rw [← h_fib]
  have h_step : ∀ k ∈ Finset.Icc 1 K,
      ∑ s ∈ (S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k), (1 : ℝ) / (r - s) ^ 2 ≤ 2 / (k : ℝ) ^ 2 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk.1
    have h_term_le : ∀ s ∈ (S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k), (1 : ℝ) / (r - s) ^ 2 ≤ 1 / (k : ℝ) ^ 2 := by
      intro s hs
      rw [Finset.mem_filter] at hs
      have hk_le : (k : ℝ) ≤ |r - s| := (Nat.floor_eq_iff (abs_nonneg _)).mp hs.2 |>.1
      have hk_sq : (k : ℝ) ^ 2 ≤ (r - s) ^ 2 := by
        have : (k : ℝ) ^ 2 ≤ |r - s| ^ 2 := by nlinarith
        rwa [sq_abs] at this
      have h_pos : 0 < (r - s) ^ 2 := by linarith [sq_pos_of_pos hk_pos, hk_sq]
      exact (one_div_le_one_div (by linarith) (by positivity)).mpr hk_sq
    have h_sum_le := Finset.sum_le_card_nsmul ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k))
      (fun s => (1 : ℝ) / (r - s) ^ 2) (1 / (k : ℝ) ^ 2) h_term_le
    have h_card := step2_fiber S hS r k
    calc ∑ s ∈ (S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k), (1 : ℝ) / (r - s) ^ 2
        ≤ ((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k)).card • (1 / (k : ℝ) ^ 2) := h_sum_le
      _ = (((S \ {r}).filter (fun s => ⌊|r - s|⌋₊ = k)).card : ℝ) * (1 / (k : ℝ) ^ 2) := nsmul_eq_mul _ _
      _ ≤ 2 * (1 / (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_right (by exact_mod_cast h_card) (by positivity)
      _ = 2 / (k : ℝ) ^ 2 := mul_one_div 2 ((k : ℝ) ^ 2)
  have h_sum_all := Finset.sum_le_sum h_step
  refine h_sum_all.trans ?_
  have h_pull : ∑ k ∈ Finset.Icc 1 K, 2 / (k : ℝ) ^ 2 = 2 * ∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [h_pull]
  have h_bound := sum_inv_sq_le_two K
  linarith


/-! ### Monotonicity of Zero-Free Region and Log Bounds -/

lemma hzeta_mono {c₀ c₀' K : ℝ} (hle : c₀' ≤ c₀)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2) :
    ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀' / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2 := by
  intro σ t ht hσ hσ2
  refine hζ σ t ht ?_ hσ2
  have hlog : 0 < Real.log |t| := Real.log_pos (by linarith)
  have hpow : 0 < (Real.log |t|) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hdiv : c₀' / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) :=
    div_le_div_of_nonneg_right hle hpow.le
  linarith

lemma hholo_mono {c₀ c₀' : ℝ} (hle : c₀' ≤ c₀)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      ((Set.Icc (1 - c₀' / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1}) := by
  intro T hT
  have hH := hholo T hT
  refine hH.mono ?_
  intro z hz
  simp only [Set.mem_sdiff, Complex.mem_reProdIm, Set.mem_Icc, Set.mem_singleton_iff] at hz ⊢
  refine ⟨⟨?_, hz.1.2⟩, hz.2⟩
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have hpow : 0 < (Real.log T) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hlog _
  have hdiv : c₀' / (Real.log T) ^ (3 / 4 : ℝ) ≤ c₀ / (Real.log T) ^ (3 / 4 : ℝ) :=
    div_le_div_of_nonneg_right hle hpow.le
  refine ⟨by linarith [hz.1.1.1], hz.1.1.2⟩

lemma log_lt_three_mul_rpow_third {x : ℝ} (hx : 1 ≤ x) :
    Real.log x < 3 * x ^ (1 / 3 : ℝ) := by
  have hx_pos : 0 < x := by linarith
  have hpos : 0 < x ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hx_pos _
  have h_le : Real.log (x ^ (1 / 3 : ℝ)) ≤ x ^ (1 / 3 : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hpos
  have h_lt : Real.log (x ^ (1 / 3 : ℝ)) < x ^ (1 / 3 : ℝ) := by linarith
  rw [Real.log_rpow hx_pos (1 / 3 : ℝ)] at h_lt
  linarith

lemma k_mul_log_sq_le_of_ge {K x : ℝ} (hK : 1 ≤ K) (hx : (9 * K) ^ 3 ≤ x) :
    K * (Real.log x) ^ 2 ≤ x := by
  have h9K : 1 ≤ 9 * K := by linarith
  have hx_ge_one : 1 ≤ x := by
    have h1 : 1 ≤ (9 * K) ^ 3 := by
      have : (1 : ℝ) = 1 ^ 3 := by norm_num
      rw [this]
      exact pow_le_pow_left₀ (by norm_num) h9K 3
    linarith
  have h_log := log_lt_three_mul_rpow_third hx_ge_one
  have h_log_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx_ge_one
  have h_sq : (Real.log x) ^ 2 ≤ (3 * x ^ (1 / 3 : ℝ)) ^ 2 := by
    nlinarith [h_log]
  have h_sq_calc : (3 * x ^ (1 / 3 : ℝ)) ^ 2 = 9 * x ^ (2 / 3 : ℝ) := by
    have : (3 * x ^ (1 / 3 : ℝ)) ^ 2 = 9 * (x ^ (1 / 3 : ℝ)) ^ 2 := by ring
    rw [this, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    congr 1
    norm_num
  rw [h_sq_calc] at h_sq
  have h_mul : K * (Real.log x) ^ 2 ≤ 9 * K * x ^ (2 / 3 : ℝ) := by
    nlinarith
  refine h_mul.trans ?_
  have hx_third : 9 * K ≤ x ^ (1 / 3 : ℝ) := by
    have h_pow := Real.rpow_le_rpow (by positivity) hx (by norm_num : 0 ≤ (1 / 3 : ℝ))
    have h_simpl : ((9 * K) ^ 3) ^ (1 / 3 : ℝ) = 9 * K := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rwa [h_simpl] at h_pow
  have h_step : 9 * K * x ^ (2 / 3 : ℝ) ≤ x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) := by
    have : 0 ≤ x ^ (2 / 3 : ℝ) := by positivity
    nlinarith
  refine h_step.trans ?_
  rw [← Real.rpow_add (by positivity)]
  have : (1 / 3 : ℝ) + 2 / 3 = 1 := by norm_num
  rw [this, Real.rpow_one]


/-! ### Complex Power and Duality Identifications -/

lemma conj_cpow_mul_I (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (starRingEnd ℂ) ((n : ℂ) ^ ((t : ℂ) * Complex.I)) = (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [Complex.cpow_def_of_ne_zero hn_ne]
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn_pos.le]
  rw [hlog, ← Complex.exp_conj]
  have h_exp : (starRingEnd ℂ) ((Real.log (n : ℝ) : ℂ) * ((t : ℂ) * Complex.I)) =
      (Complex.log (n : ℂ)) * (-(t : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, map_mul, Complex.conj_ofReal, Complex.conj_I, hlog]
    ring
  rw [h_exp, ← Complex.cpow_def_of_ne_zero hn_ne]

lemma cpow_sub_mul_I (n : ℕ) (hn : 0 < n) (t t' : ℝ) :
    (n : ℂ) ^ (-((t' - t : ℝ) : ℂ) * Complex.I) = (n : ℂ) ^ ((t : ℂ) * Complex.I) * (n : ℂ) ^ (-(t' : ℂ) * Complex.I) := by
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  have h_exp : -((t' - t : ℝ) : ℂ) * Complex.I = ((t : ℂ) * Complex.I) + (-(t' : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h_exp, Complex.cpow_add _ _ hn_ne]

lemma norm_sq_sum_cpow_eq (S : Finset ℝ) (η : ℝ → ℂ) (n : ℕ) (hn : 0 < n) :
    ((‖∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ S, ∑ t' ∈ S, η t * (starRingEnd ℂ) (η t') * (n : ℂ) ^ (-((t' - t : ℝ) : ℂ) * Complex.I) := by
  have h_cast : ((‖∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
      (∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)) * (starRingEnd ℂ) (∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  rw [h_cast]
  have h_star : (starRingEnd ℂ) (∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)) =
      ∑ t ∈ S, (starRingEnd ℂ) (η t) * (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, conj_cpow_mul_I n hn]
  rw [h_star, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  refine Finset.sum_congr rfl fun t' _ => ?_
  rw [cpow_sub_mul_I n hn t t']
  ring

lemma cpow_neg_one_add_mul_I (p : ℕ) (hp : 0 < p) (t : ℝ) :
    (p : ℂ) ^ (-((1 : ℂ) + (t : ℂ) * Complex.I)) = 1 / (p : ℂ) * (p : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp)
  have h_exp : -((1 : ℂ) + (t : ℂ) * Complex.I) = -1 + (-(t : ℂ) * Complex.I) := by ring
  rw [h_exp, Complex.cpow_add _ _ hp_ne]
  congr 1
  rw [Complex.cpow_neg_one, one_div]

lemma term_factor (a : ℕ → ℂ) (p : ℕ) (hp : 0 < p) (t : ℝ) (hlog : 0 < Real.log (p : ℝ)) :
    a p * (p : ℂ) ^ (-((1 : ℂ) + (t : ℂ) * Complex.I)) =
      (a p / (p : ℂ) / (Real.sqrt (Real.log (p : ℝ)) : ℂ)) *
        ((p : ℂ) ^ (-(t : ℂ) * Complex.I) * (Real.sqrt (Real.log (p : ℝ)) : ℂ)) := by
  rw [cpow_neg_one_add_mul_I p hp t]
  have hsqrt_ne : (Real.sqrt (Real.log (p : ℝ)) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (Real.log (p : ℝ)) := Real.sqrt_pos.mpr hlog
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt this)
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hp)
  field_simp

lemma norm_sq_b_le (a : ℕ → ℂ) (p P : ℕ) (hP : 3 ≤ P) (hp : P < p) :
    ‖a p / (p : ℂ) / (Real.sqrt (Real.log (p : ℝ)) : ℂ)‖ ^ 2 ≤
      ‖a p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P) := by
  have hP_gt1 : (1 : ℝ) < (P : ℝ) := by exact_mod_cast (by omega : 1 < P)
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogP_pos : 0 < Real.log P := Real.log_pos hP_gt1
  have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt1
  have hlog_le : Real.log P ≤ Real.log (p : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hp.le
  rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hlogp_pos)]
  rw [Complex.norm_natCast]
  have : (‖a p‖ / (p : ℝ) / Real.sqrt (Real.log (p : ℝ))) ^ 2 =
      ‖a p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log (p : ℝ)) := by
    have : (‖a p‖ / (p : ℝ) / Real.sqrt (Real.log (p : ℝ))) ^ 2 =
        (‖a p‖ / (p : ℝ)) ^ 2 / (Real.sqrt (Real.log (p : ℝ))) ^ 2 := div_pow _ _ 2
    rw [this, div_pow, Real.sq_sqrt hlogp_pos.le]
    ring
  rw [this]
  have h_denom : (p : ℝ) ^ 2 * Real.log P ≤ (p : ℝ) ^ 2 * Real.log (p : ℝ) := by
    have : 0 ≤ (p : ℝ) ^ 2 := by positivity
    nlinarith
  have h_denom_pos : 0 < (p : ℝ) ^ 2 * Real.log P := by positivity
  exact div_le_div_of_nonneg_left (sq_nonneg _) h_denom_pos h_denom


/-! ### Chebyshev Bounds and Prime to Smooth Sum Comparison -/

lemma log_lt_two_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Real.log x < 2 * Real.sqrt x := by
  have hpos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h_lt : Real.log (Real.sqrt x) < Real.sqrt x := by
    have h_le := Real.log_le_sub_one_of_pos hpos
    linarith
  have h_eq : Real.log (Real.sqrt x) = (1 / 2 : ℝ) * Real.log x := by
    rw [Real.sqrt_eq_rpow, Real.log_rpow hx]
  rw [h_eq] at h_lt
  linarith

lemma sum_Icc_vonMangoldt_le (P : ℕ) (hP : 3 ≤ P) :
    ∑ n ∈ Finset.Icc 1 (8 * P), (ArithmeticFunction.vonMangoldt n : ℝ) ≤ 60 * (P : ℝ) := by
  have hP_pos : 0 < (P : ℝ) := by
    have : (3 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  have h8P_ge : 1 ≤ ((8 * P : ℕ) : ℝ) := by
    have : 1 ≤ 8 * P := by omega
    exact_mod_cast this
  have h_psi := Chebyshev.psi_le h8P_ge
  have h_sets : Finset.Icc 1 (8 * P) = Finset.Ioc 0 (8 * P) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have h_eq : ∑ n ∈ Finset.Icc 1 (8 * P), (ArithmeticFunction.vonMangoldt n : ℝ) =
      Chebyshev.psi ((8 * P : ℕ) : ℝ) := by
    rw [Chebyshev.psi, Nat.floor_natCast, h_sets]
  rw [h_eq]
  refine h_psi.trans ?_
  have h8P_pos : 0 < ((8 * P : ℕ) : ℝ) := by
    have : 0 < 8 * P := by omega
    exact_mod_cast this
  have h_log_bound := log_lt_two_mul_sqrt h8P_pos
  have h_second : 2 * Real.sqrt ((8 * P : ℕ) : ℝ) * Real.log ((8 * P : ℕ) : ℝ) ≤
      4 * ((8 * P : ℕ) : ℝ) := by
    calc
      2 * Real.sqrt ((8 * P : ℕ) : ℝ) * Real.log ((8 * P : ℕ) : ℝ)
        ≤ 2 * Real.sqrt ((8 * P : ℕ) : ℝ) * (2 * Real.sqrt ((8 * P : ℕ) : ℝ)) := by
          have : 0 ≤ 2 * Real.sqrt ((8 * P : ℕ) : ℝ) := by positivity
          nlinarith [h_log_bound]
      _ = 4 * (Real.sqrt ((8 * P : ℕ) : ℝ)) ^ 2 := by ring
      _ = 4 * ((8 * P : ℕ) : ℝ) := by rw [Real.sq_sqrt (by positivity)]
  have h_first : Real.log 4 * ((8 * P : ℕ) : ℝ) ≤ 2 * ((8 * P : ℕ) : ℝ) := by
    have hlog4 : Real.log 4 ≤ 2 := by
      rw [Real.log_four_eq]
      have : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have : 0 ≤ ((8 * P : ℕ) : ℝ) := by positivity
    nlinarith
  push_cast at h_first h_second ⊢
  linarith

lemma prime_sum_le_smooth_sum (ν : ℝ → ℝ) (P : ℕ) (_hP : 3 ≤ P) (X₀ : ℝ)
    (hX₀_below : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * P → Smooth1 ν (1 / 2) (n / X₀) = 1)
    (h_nonneg : ∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n * Smooth1 ν (1 / 2) (n / X₀))
    (S : Finset ℝ) (η : ℝ → ℂ) :
    ∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, Real.log p * ‖∑ t ∈ S, η t * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 (8 * P), ArithmeticFunction.vonMangoldt n * Smooth1 ν (1 / 2) (n / X₀) *
        ‖∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 := by
  let PrimesP := (Finset.Ioc P (2 * P)).filter Nat.Prime
  have h_sub : PrimesP ⊆ Finset.Icc 1 (8 * P) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Finset.mem_Icc]
    refine ⟨by omega, by omega⟩
  have h_term_eq : ∀ p ∈ PrimesP,
      Real.log p * ‖∑ t ∈ S, η t * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 =
      ArithmeticFunction.vonMangoldt p * Smooth1 ν (1 / 2) (p / X₀) *
        ‖∑ t ∈ S, η t * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have hp_prime : p.Prime := hp.2
    have hp_pos : 1 ≤ p := by omega
    have hp_le : p ≤ 2 * P := hp.1.2
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp_prime]
    rw [hX₀_below p hp_pos hp_le]
    ring
  rw [Finset.sum_congr rfl h_term_eq]
  refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
  intro n _ hn_not
  have : 0 ≤ ArithmeticFunction.vonMangoldt n * Smooth1 ν (1 / 2) (n / X₀) := h_nonneg n
  positivity

lemma twistedSum_eq_sum (ν : ℝ → ℝ) (ε X u : ℝ) (P : ℕ)
    (h_supp : ∀ n : ℕ, 8 * P < n → Smooth1 ν ε (n / X) = 0) :
    twistedSum ν ε X u = ∑ n ∈ Finset.Icc 1 (8 * P),
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I) * (Smooth1 ν ε (n / X) : ℂ) := by
  dsimp [twistedSum]
  rw [tsum_eq_sum]
  intro n hn
  rw [Finset.mem_Icc] at hn
  by_cases hn0 : n = 0
  · subst hn0
    rw [ArithmeticFunction.map_zero]
    simp
  · have hn_gt : 8 * P < n := by omega
    have h_zero := h_supp n hn_gt
    simp [h_zero]

lemma smooth_sum_eq_sum_twisted (ν : ℝ → ℝ) (ε X₀ : ℝ) (P : ℕ)
    (h_tsum : ∀ u, twistedSum ν ε X₀ u = ∑ n ∈ Finset.Icc 1 (8 * P),
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I) * (Smooth1 ν ε (n / X₀) : ℂ))
    (S : Finset ℝ) (η : ℝ → ℂ) :
    ((∑ n ∈ Finset.Icc 1 (8 * P), ArithmeticFunction.vonMangoldt n * Smooth1 ν ε (n / X₀) *
        ‖∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ t ∈ S, ∑ t' ∈ S, η t * (starRingEnd ℂ) (η t') * twistedSum ν ε X₀ (t' - t) := by
  rw [Complex.ofReal_sum]
  have h_step1 : (∑ n ∈ Finset.Icc 1 (8 * P),
        ((ArithmeticFunction.vonMangoldt n * Smooth1 ν ε (n / X₀) *
          ‖∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ)) =
      ∑ n ∈ Finset.Icc 1 (8 * P), (ArithmeticFunction.vonMangoldt n : ℂ) * ((Smooth1 ν ε (n / X₀) : ℂ) *
        (∑ t ∈ S, ∑ t' ∈ S, η t * (starRingEnd ℂ) (η t') * (n : ℂ) ^ (-((t' - t : ℝ) : ℂ) * Complex.I))) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h_prod : ((ArithmeticFunction.vonMangoldt n * Smooth1 ν ε (n / X₀) *
          ‖∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
        (ArithmeticFunction.vonMangoldt n : ℂ) * ((Smooth1 ν ε (n / X₀) : ℂ) *
          ((‖∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ)) := by
      push_cast; ring
    rw [h_prod, norm_sq_sum_cpow_eq S η n (by omega)]
  rw [h_step1]
  simp_rw [mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t' _
  rw [h_tsum (t' - t)]
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

lemma sum_pair_split (s : Finset ℝ) (f : ℝ → ℝ → ℂ) :
    ∑ t ∈ s, ∑ t' ∈ s, f t t' = (∑ t ∈ s, f t t) + ∑ t ∈ s, ∑ t' ∈ s \ {t}, f t t' := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have : s = insert t (s \ {t}) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases h : x = t
      · left; exact h
      · right; exact ⟨hx, h⟩
    · rintro (rfl | ⟨hx, _⟩)
      · exact ht
      · exact hx
  nth_rw 1 [this]
  rw [Finset.sum_insert (by simp)]

lemma sum_sdiff_singleton_eq {α M : Type*} [AddCommMonoid M] [DecidableEq α]
    (s : Finset α) (t : α) (ht : t ∈ s) (g : α → M) :
    ∑ t' ∈ s \ {t}, g t' = ∑ t' ∈ s, if t' = t then 0 else g t' := by
  have : s = insert t (s \ {t}) := by
    ext x
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · intro hx
      by_cases h : x = t
      · left; exact h
      · right; exact ⟨hx, h⟩
    · rintro (rfl | ⟨hx, _⟩)
      · exact ht
      · exact hx
  nth_rw 2 [this]
  rw [Finset.sum_insert (by simp)]
  simp only [↓reduceIte, zero_add]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
  simp only [hx.2, ↓reduceIte]

lemma sum_offdiag_sq_le (S : Finset ℝ) (hS : WellSpaced S) (η : ℝ → ℂ) :
    ∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2) ≤ 4 * ∑ t ∈ S, ‖η t‖ ^ 2 := by
  have h_symm : ∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t'‖ ^ 2 * (1 / (t - t') ^ 2) =
      ∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ ^ 2 * (1 / (t - t') ^ 2) := by
    have h1 : (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t'‖ ^ 2 * (1 / (t - t') ^ 2)) =
        ∑ t ∈ S, ∑ t' ∈ S, if t' = t then 0 else ‖η t'‖ ^ 2 * (1 / (t - t') ^ 2) := by
      apply Finset.sum_congr rfl; intro t ht; exact sum_sdiff_singleton_eq S t ht _
    have h2 : (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ ^ 2 * (1 / (t - t') ^ 2)) =
        ∑ t ∈ S, ∑ t' ∈ S, if t' = t then 0 else ‖η t‖ ^ 2 * (1 / (t - t') ^ 2) := by
      apply Finset.sum_congr rfl; intro t ht; exact sum_sdiff_singleton_eq S t ht _
    rw [h1, h2, Finset.sum_comm]
    apply Finset.sum_congr rfl; intro t' _
    apply Finset.sum_congr rfl; intro t _
    by_cases h : t' = t
    · subst h; rfl
    · have hne : t ≠ t' := ne_comm.mp h
      simp only [h, hne, ↓reduceIte]
      have : (t - t') ^ 2 = (t' - t) ^ 2 := by ring
      rw [this]
  have h_le : ∀ t ∈ S, ∀ t' ∈ S \ {t},
      ‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2) ≤
        (1 / 2) * (‖η t‖ ^ 2 + ‖η t'‖ ^ 2) * (1 / (t - t') ^ 2) := by
    intro t _ t' _
    have h2 : ‖η t‖ * ‖η t'‖ ≤ (1 / 2) * (‖η t‖ ^ 2 + ‖η t'‖ ^ 2) := by
      have : 0 ≤ (‖η t‖ - ‖η t'‖) ^ 2 := sq_nonneg _
      nlinarith
    have hpos : 0 ≤ 1 / (t - t') ^ 2 := by positivity
    nlinarith
  have h_sum_le : ∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2) ≤
      ∑ t ∈ S, ∑ t' ∈ S \ {t}, (1 / 2) * (‖η t‖ ^ 2 + ‖η t'‖ ^ 2) * (1 / (t - t') ^ 2) :=
    Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun t' ht' => h_le t ht t' ht'
  refine h_sum_le.trans ?_
  have h_split : (∑ t ∈ S, ∑ t' ∈ S \ {t}, (1 / 2 : ℝ) * (‖η t‖ ^ 2 + ‖η t'‖ ^ 2) * (1 / (t - t') ^ 2)) =
      (1 / 2 : ℝ) * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ ^ 2 * (1 / (t - t') ^ 2)) +
      (1 / 2 : ℝ) * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t'‖ ^ 2 * (1 / (t - t') ^ 2)) := by
    have h1 : ∀ t t', (1 / 2 : ℝ) * (‖η t‖ ^ 2 + ‖η t'‖ ^ 2) * (1 / (t - t') ^ 2) =
        (1 / 2 : ℝ) * (‖η t‖ ^ 2 * (1 / (t - t') ^ 2)) + (1 / 2 : ℝ) * (‖η t'‖ ^ 2 * (1 / (t - t') ^ 2)) := by
      intro t t'; ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h_split, h_symm]
  have h_comb : (1 / 2 : ℝ) * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ ^ 2 * (1 / (t - t') ^ 2)) +
      (1 / 2) * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ ^ 2 * (1 / (t - t') ^ 2)) =
      ∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ ^ 2 * (1 / (t - t') ^ 2) := by ring
  rw [h_comb]
  have h_pull : (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ ^ 2 * (1 / (t - t') ^ 2)) =
      ∑ t ∈ S, ‖η t‖ ^ 2 * (∑ t' ∈ S \ {t}, 1 / (t - t') ^ 2) := by
    apply Finset.sum_congr rfl; intro t _; rw [Finset.mul_sum]
  rw [h_pull]
  have h_step : ∀ t ∈ S, ‖η t‖ ^ 2 * (∑ t' ∈ S \ {t}, 1 / (t - t') ^ 2) ≤ ‖η t‖ ^ 2 * 4 := by
    intro t ht
    have := sum_wellSpaced_inv_sq_sub_le S hS t ht
    exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have h_final := Finset.sum_le_sum h_step
  refine h_final.trans ?_
  rw [← Finset.sum_mul]
  ring_nf; rfl

lemma sum_prod_norm_le_card_mul_sum_sq (S : Finset ℝ) (η : ℝ → ℂ) :
    ∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ ≤ (S.card : ℝ) * ∑ t ∈ S, ‖η t‖ ^ 2 := by
  have h_le : ∀ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ ≤ ∑ t' ∈ S, ‖η t‖ * ‖η t'‖ := by
    intro t ht
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro x hx; simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx; exact hx.1
    · intro x _ _; positivity
  have h_sum : ∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ ≤ ∑ t ∈ S, ∑ t' ∈ S, ‖η t‖ * ‖η t'‖ :=
    Finset.sum_le_sum h_le
  refine h_sum.trans ?_
  have h_prod : (∑ t ∈ S, ∑ t' ∈ S, ‖η t‖ * ‖η t'‖) = (∑ t ∈ S, ‖η t‖) ^ 2 := by
    rw [sq, ← Finset.sum_mul_sum]
  rw [h_prod]
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun t => ‖η t‖)
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one, one_pow] at h_cs
  exact h_cs

lemma mellin_smooth1_bound {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν) (suppν : ν.support ⊆ Set.Icc (1 / 2) 2) :
    ∃ C_M : ℝ, 0 < C_M ∧ ∀ (u : ℝ) (_hu : u ≠ 0),
      ‖mellin (fun x => (Smooth1 ν (1 / 2) x : ℂ)) (1 - u * Complex.I)‖ ≤ 2 * C_M / u ^ 2 := by
  obtain ⟨C, Cpos, hC⟩ := MellinOfSmooth1b diffν suppν
  refine ⟨C, Cpos, ?_⟩
  intro u _hu
  let s : ℂ := 1 - u * Complex.I
  have hs_re : s.re = 1 := by simp [s]
  have hs1 : (1 / 2 : ℝ) ≤ s.re := by linarith [hs_re]
  have hs2 : s.re ≤ 2 := by linarith [hs_re]
  have h_bound := hC (1 / 2) (by norm_num) s hs1 hs2 (1 / 2) (by norm_num) (by norm_num)
  have h_norm_s : ‖s‖ ^ 2 = 1 + u ^ 2 := by
    have : ‖s‖ ^ 2 = Complex.normSq s := by rw [Complex.normSq_eq_norm_sq]
    rw [this]
    simp [s, Complex.normSq]
    ring
  have h_u2_le : u ^ 2 ≤ ‖s‖ ^ 2 := by rw [h_norm_s]; linarith
  have hu2_pos : 0 < u ^ 2 := sq_pos_of_ne_zero _hu
  have hs_pos : 0 < ‖s‖ ^ 2 := by linarith
  have h_inv : (‖s‖ ^ 2)⁻¹ ≤ (u ^ 2)⁻¹ := (inv_le_inv₀ hs_pos hu2_pos).mpr h_u2_le
  calc ‖mellin (fun x => (Smooth1 ν (1 / 2) x : ℂ)) (1 - u * Complex.I)‖
      ≤ C * ((1 / 2 : ℝ) * ‖s‖ ^ 2)⁻¹ := h_bound
    _ = 2 * C * (‖s‖ ^ 2)⁻¹ := by
      have : ((1 / 2 : ℝ) * ‖s‖ ^ 2)⁻¹ = 2 * (‖s‖ ^ 2)⁻¹ := by
        rw [mul_inv, inv_div]; norm_num
      rw [this]; ring
    _ ≤ 2 * C * (u ^ 2)⁻¹ := mul_le_mul_of_nonneg_left h_inv (by positivity)
    _ = 2 * C / u ^ 2 := by rw [div_eq_mul_inv]

lemma norm_cpow_one_sub_mul_I {X u : ℝ} (hX : 0 < X) :
    ‖(X : ℂ) ^ ((1 : ℂ) - (u : ℂ) * Complex.I)‖ = X := by
  have hre : ((1 : ℂ) - (u : ℂ) * Complex.I).re = 1 := by simp
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hre, Real.rpow_one]

lemma log2_lt_one : Real.log 2 < 1 := by
  linarith [Real.log_two_lt_d9]

lemma log2_pos : 0 < Real.log 2 := by
  exact Real.log_pos (by norm_num)

lemma one_sub_half_log2_pos : 0 < 1 - Real.log 2 / 2 := by
  linarith [Real.log_two_lt_d9]

lemma ratio_le_four : (1 + Real.log 2) / (1 - Real.log 2 / 2) ≤ 4 := by
  have hpos := one_sub_half_log2_pos
  rw [div_le_iff₀ hpos]
  have := log2_lt_one
  linarith

lemma log_prod_le {K P T : ℝ} (hK : 1 ≤ K) (_hP : 3 ≤ P) (_hT : 3 ≤ T) :
    let B_K := 3 * Real.log (9 * K) / Real.log 9 + 5
    Real.log ((9 * K) ^ 3 * (P * T) ^ 5) ≤ B_K * Real.log (P * T) := by
  intro B_K
  have h9K : 1 ≤ 9 * K := by linarith
  have h9K_pos : 0 < 9 * K := by linarith
  have hPT_ge : (9 : ℝ) ≤ P * T := by
    nlinarith
  have hPT_pos : 0 < P * T := by linarith
  have hlog9_pos : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hlogPT_ge : Real.log 9 ≤ Real.log (P * T) := Real.log_le_log (by norm_num) hPT_ge
  have h_log_T' : Real.log ((9 * K) ^ 3 * (P * T) ^ 5) = 3 * Real.log (9 * K) + 5 * Real.log (P * T) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow (9 * K) 3, Real.log_pow (P * T) 5]
    push_cast; ring
  rw [h_log_T']
  have h_pos : 0 ≤ 3 * Real.log (9 * K) / Real.log 9 :=
    div_nonneg (by nlinarith [Real.log_nonneg h9K]) hlog9_pos.le
  have h1 : 3 * Real.log (9 * K) ≤ (3 * Real.log (9 * K) / Real.log 9) * Real.log (P * T) := by
    calc 3 * Real.log (9 * K)
        = (3 * Real.log (9 * K) / Real.log 9) * Real.log 9 := (div_mul_cancel₀ _ (ne_of_gt hlog9_pos)).symm
      _ ≤ (3 * Real.log (9 * K) / Real.log 9) * Real.log (P * T) := mul_le_mul_of_nonneg_left hlogPT_ge h_pos
  dsimp [B_K]
  have : (3 * Real.log (9 * K) / Real.log 9 + 5) * Real.log (P * T) =
      (3 * Real.log (9 * K) / Real.log 9) * Real.log (P * T) + 5 * Real.log (P * T) := by ring
  rw [this]
  linarith

lemma theta_bk_le {c₀' B_K logT' logPT : ℝ}
    (hc₀' : 0 < c₀') (_hBK : 1 ≤ B_K) (hlogT' : 0 < logT') (hlogPT : 0 < logPT)
    (h_le : logT' ≤ B_K * logPT) :
    (c₀' / B_K ^ (3 / 4 : ℝ)) / logPT ^ (3 / 4 : ℝ) ≤ c₀' / logT' ^ (3 / 4 : ℝ) := by
  have hpow_le : logT' ^ (3 / 4 : ℝ) ≤ (B_K * logPT) ^ (3 / 4 : ℝ) :=
    rpow_le_rpow hlogT'.le h_le (by norm_num)
  have hmul_pow : (B_K * logPT) ^ (3 / 4 : ℝ) = B_K ^ (3 / 4 : ℝ) * logPT ^ (3 / 4 : ℝ) :=
    Real.mul_rpow (by linarith) hlogPT.le
  rw [hmul_pow] at hpow_le
  have h_div : (c₀' / B_K ^ (3 / 4 : ℝ)) / logPT ^ (3 / 4 : ℝ) =
      c₀' / (B_K ^ (3 / 4 : ℝ) * logPT ^ (3 / 4 : ℝ)) := by
    ring
  rw [h_div]
  exact div_le_div_of_nonneg_left hc₀'.le (rpow_pos_of_pos hlogT' _) hpow_le

lemma exp_bound_of_c_le_half {c P PT : ℝ} (_hc : 0 < c) (hc_le : c ≤ 1 / 2)
    (hP : 3 ≤ P) (hPT : (9 : ℝ) ≤ PT) :
    1 ≤ P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) * (Real.log PT) ^ 2 := by
  have hlogPT_pos : 0 < Real.log PT := Real.log_pos (by linarith)
  have hlogPT_ge : 1 ≤ Real.log PT := by
    have : (Real.exp 1 : ℝ) ≤ 9 := by
      have := Real.exp_one_lt_d9
      linarith
    have h9 : (Real.exp 1 : ℝ) ≤ PT := le_trans this hPT
    have := Real.log_le_log (by positivity) h9
    rwa [Real.log_exp] at this
  have hpow_ge : 1 ≤ (Real.log PT) ^ (3 / 4 : ℝ) := by
    have : (1 : ℝ) = (1 : ℝ) ^ (3 / 4 : ℝ) := by norm_num
    rw [this]
    exact rpow_le_rpow (by norm_num) hlogPT_ge (by norm_num)
  have hdiv_le : c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) ≤ (1 / 2 : ℝ) * Real.log P := by
    have hlogP_pos : 0 < Real.log P := Real.log_pos (by linarith)
    have : c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) ≤ c * Real.log P / 1 := by
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpow_ge
    rw [div_one] at this
    have : c * Real.log P ≤ (1 / 2 : ℝ) * Real.log P := mul_le_mul_of_nonneg_right hc_le hlogP_pos.le
    linarith
  have h_neg_div : -(c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) = -c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) := by ring
  have hexp_ge : Real.exp (- ((1 / 2 : ℝ) * Real.log P)) ≤ Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have := neg_le_neg hdiv_le
    rwa [h_neg_div] at this
  have h_P_pow : Real.exp (- ((1 / 2 : ℝ) * Real.log P)) = P ^ (- (1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos (by linarith)]
    congr 1
    ring
  rw [h_P_pow] at hexp_ge
  have h_mul : 1 ≤ P * P ^ (- (1 / 2 : ℝ)) := by
    nth_rw 1 [← Real.rpow_one P]
    rw [← Real.rpow_add (by linarith)]
    have : (1 : ℝ) + - (1 / 2 : ℝ) = (1 / 2 : ℝ) := by norm_num
    rw [this]
    have h1 : (1 : ℝ) ≤ (1 : ℝ) ^ (1 / 2 : ℝ) := by norm_num
    have h2 : (1 : ℝ) ^ (1 / 2 : ℝ) ≤ P ^ (1 / 2 : ℝ) :=
      rpow_le_rpow (by norm_num) (by linarith : (1 : ℝ) ≤ P) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    exact le_trans h1 h2
  have hlog_sq_ge : 1 ≤ (Real.log PT) ^ 2 := by
    nlinarith
  have h_step : 1 ≤ P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) := by
    calc (1 : ℝ) ≤ P * P ^ (- (1 / 2 : ℝ)) := h_mul
      _ ≤ P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hexp_ge (by positivity)
  calc (1 : ℝ) ≤ (1 : ℝ) * 1 := by norm_num
    _ ≤ (P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ))) * (Real.log PT) ^ 2 :=
      mul_le_mul h_step hlog_sq_ge (by norm_num) (by positivity)
    _ = P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) * (Real.log PT) ^ 2 := by ring

lemma sum_subtype_eq {α M : Type*} [AddCommMonoid M] (s : Finset α) (f : α → M) :
    (∑ x : ↥s, f ↑x) = ∑ x ∈ s, f x := by
  have : (∑ x : ↥s, f ↑x) = ∑ x ∈ s.attach, f ↑x := rfl
  rw [this, Finset.sum_attach]

lemma duality_applied (P : ℕ) (hP : 3 ≤ P) (a : ℕ → ℂ) (S : Finset ℝ) (D : ℝ) (hD : 0 ≤ D)
    (h_dual : ∀ (η : ℝ → ℂ),
      (∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, Real.log p * ‖∑ t ∈ S, η t * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) ≤
        D * ∑ t ∈ S, ‖η t‖ ^ 2) :
    (∑ t ∈ S, ‖dirichletPoly a ((Finset.Ioc P (2 * P)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      D * ∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, ‖a p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P) := by
  let PrimesP := (Finset.Ioc P (2 * P)).filter Nat.Prime
  let x : ↥S → ↥PrimesP → ℂ := fun i k => ((k : ℕ) : ℂ) ^ (-((i : ℝ) : ℂ) * Complex.I) * (Real.sqrt (Real.log ((k : ℕ) : ℝ)) : ℂ)
  let b : ↥PrimesP → ℂ := fun k => a (k : ℕ) / ((k : ℕ) : ℂ) / (Real.sqrt (Real.log ((k : ℕ) : ℝ)) : ℂ)
  have h_dual_sub : ∀ η : ↥S → ℂ, (∑ k : ↥PrimesP, ‖∑ i : ↥S, η i * x i k‖ ^ 2) ≤ D * ∑ i : ↥S, ‖η i‖ ^ 2 := by
    intro η
    let η_ext : ℝ → ℂ := fun t => if ht : t ∈ S then starRingEnd ℂ (η ⟨t, ht⟩) else 0
    have h_dual_ext := h_dual η_ext
    have h_left : (∑ k : ↥PrimesP, ‖∑ i : ↥S, η i * x i k‖ ^ 2) =
        ∑ p ∈ PrimesP, Real.log p * ‖∑ t ∈ S, η_ext t * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 := by
      have h_fun_eq : (∑ k : ↥PrimesP, ‖∑ i : ↥S, η i * x i k‖ ^ 2) =
          ∑ k : ↥PrimesP, (fun (n : ℕ) => Real.log (n : ℝ) * ‖∑ t ∈ S, η_ext t * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) (k : ℕ) := by
        apply Finset.sum_congr rfl
        intro k _
        have hk_mem := k.2
        rw [Finset.mem_filter, Finset.mem_Ioc] at hk_mem
        have hk_pos : 0 < (k : ℕ) := by omega
        have hk_gt1 : (1 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < (k : ℕ))
        have hlogk_pos : 0 < Real.log ((k : ℕ) : ℝ) := Real.log_pos hk_gt1
        have hsqrt_pos : 0 < Real.sqrt (Real.log ((k : ℕ) : ℝ)) := Real.sqrt_pos.mpr hlogk_pos
        have hx_term : (∑ i : ↥S, η i * x i k) =
            (Real.sqrt (Real.log ((k : ℕ) : ℝ)) : ℂ) * ∑ i : ↥S, η i * ((k : ℕ) : ℂ) ^ (-((i : ℝ) : ℂ) * Complex.I) := by
          dsimp [x]
          have : (∑ i : ↥S, η i * (((k : ℕ) : ℂ) ^ (-((i : ℝ) : ℂ) * Complex.I) * (Real.sqrt (Real.log ((k : ℕ) : ℝ)) : ℂ))) =
              (Real.sqrt (Real.log ((k : ℕ) : ℝ)) : ℂ) * ∑ i : ↥S, η i * ((k : ℕ) : ℂ) ^ (-((i : ℝ) : ℂ) * Complex.I) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          exact this
        rw [hx_term, norm_mul, mul_pow]
        have : ‖(Real.sqrt (Real.log ((k : ℕ) : ℝ)) : ℂ)‖ ^ 2 = Real.log ((k : ℕ) : ℝ) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsqrt_pos, Real.sq_sqrt hlogk_pos.le]
        rw [this]
        congr 1
        have h_sum_conj : ‖∑ i : ↥S, η i * ((k : ℕ) : ℂ) ^ (-((i : ℝ) : ℂ) * Complex.I)‖ =
            ‖starRingEnd ℂ (∑ i : ↥S, η i * ((k : ℕ) : ℂ) ^ (-((i : ℝ) : ℂ) * Complex.I))‖ := by
          rw [Complex.norm_conj]
        rw [h_sum_conj]
        have h_star_sum : (starRingEnd ℂ) (∑ i : ↥S, η i * ((k : ℕ) : ℂ) ^ (-((i : ℝ) : ℂ) * Complex.I)) =
            ∑ i : ↥S, (starRingEnd ℂ) (η i) * ((k : ℕ) : ℂ) ^ (((i : ℝ) : ℂ) * Complex.I) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_mul]
          have h_cpow : (starRingEnd ℂ) (((k : ℕ) : ℂ) ^ (-((i : ℝ) : ℂ) * Complex.I)) = ((k : ℕ) : ℂ) ^ (((i : ℝ) : ℂ) * Complex.I) := by
            have hn_ne : ((k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hk_pos)
            have hn_pos : 0 < ((k : ℕ) : ℝ) := Nat.cast_pos.mpr hk_pos
            rw [Complex.cpow_def_of_ne_zero hn_ne]
            have hlog : Complex.log ((k : ℕ) : ℂ) = (Real.log ((k : ℕ) : ℝ) : ℂ) := by
              rw [← Complex.ofReal_natCast, Complex.ofReal_log hn_pos.le]
            rw [hlog, ← Complex.exp_conj]
            have h_exp : (starRingEnd ℂ) ((Real.log ((k : ℕ) : ℝ) : ℂ) * (-((i : ℝ) : ℂ) * Complex.I)) =
                (Complex.log ((k : ℕ) : ℂ)) * (((i : ℝ) : ℂ) * Complex.I) := by
              rw [map_mul, Complex.conj_ofReal, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, hlog]
              ring
            rw [h_exp, ← Complex.cpow_def_of_ne_zero hn_ne]
          rw [h_cpow]
        rw [h_star_sum]
        have h_sub_eq : (∑ i : ↥S, (starRingEnd ℂ) (η i) * ((k : ℕ) : ℂ) ^ (((i : ℝ) : ℂ) * Complex.I)) =
            ∑ t ∈ S, η_ext t * ((k : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
          have : (∑ i : ↥S, (starRingEnd ℂ) (η i) * ((k : ℕ) : ℂ) ^ (((i : ℝ) : ℂ) * Complex.I)) =
              ∑ i : ↥S, (fun t => η_ext t * ((k : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I)) (i : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            dsimp [η_ext]
            split_ifs with h
            · congr
            · exact (h i.2).elim
          rw [this]
          exact sum_subtype_eq S (fun t => η_ext t * ((k : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I))
        rw [h_sub_eq]
      rw [h_fun_eq]
      exact sum_subtype_eq PrimesP (fun (n : ℕ) => Real.log (n : ℝ) * ‖∑ t ∈ S, η_ext t * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2)
    have h_right : (∑ i : ↥S, ‖η i‖ ^ 2) = ∑ t ∈ S, ‖η_ext t‖ ^ 2 := by
      have : (∑ i : ↥S, ‖η i‖ ^ 2) = ∑ i : ↥S, (fun t => ‖η_ext t‖ ^ 2) (i : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [η_ext]
        split_ifs with h
        · rw [Complex.norm_conj]
        · exact (h i.2).elim
      rw [this]
      exact sum_subtype_eq S (fun t => ‖η_ext t‖ ^ 2)
    rw [h_left, h_right]
    exact h_dual_ext
  have h_duality := duality_sum_sq x hD h_dual_sub b
  have h_primal : (∑ i : ↥S, ‖∑ k : ↥PrimesP, b k * x i k‖ ^ 2) =
      ∑ t ∈ S, ‖dirichletPoly a PrimesP ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    have h_outer : (∑ i : ↥S, ‖∑ k : ↥PrimesP, b k * x i k‖ ^ 2) =
        ∑ i : ↥S, (fun t => ‖dirichletPoly a PrimesP ((1 : ℂ) + t * Complex.I)‖ ^ 2) (i : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      have h_inner : (∑ k : ↥PrimesP, b k * x i k) =
          ∑ k : ↥PrimesP, (fun (p : ℕ) => a p * (p : ℂ) ^ (-((1 : ℂ) + ((i : ℝ) : ℂ) * Complex.I))) (k : ℕ) := by
        apply Finset.sum_congr rfl
        intro k _
        have hk_mem := k.2
        rw [Finset.mem_filter, Finset.mem_Ioc] at hk_mem
        have hk_pos : 0 < (k : ℕ) := by omega
        have hk_gt1 : (1 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < (k : ℕ))
        have hlogk_pos : 0 < Real.log ((k : ℕ) : ℝ) := Real.log_pos hk_gt1
        have h_term := term_factor a (k : ℕ) hk_pos (i : ℝ) hlogk_pos
        dsimp [b, x]
        rw [h_term]
      rw [h_inner]
      have h_sub := sum_subtype_eq PrimesP (fun (p : ℕ) => a p * (p : ℂ) ^ (-((1 : ℂ) + ((i : ℝ) : ℂ) * Complex.I)))
      exact congr_arg (fun z => ‖z‖ ^ 2) h_sub
    rw [h_outer]
    exact sum_subtype_eq S (fun t => ‖dirichletPoly a PrimesP ((1 : ℂ) + t * Complex.I)‖ ^ 2)
  rw [h_primal] at h_duality
  refine h_duality.trans ?_
  have h_b_sum : (∑ k : ↥PrimesP, ‖b k‖ ^ 2) ≤ ∑ p ∈ PrimesP, ‖a p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P) := by
    have h_b_eq : (∑ k : ↥PrimesP, ‖b k‖ ^ 2) ≤ ∑ k : ↥PrimesP, (fun (p : ℕ) => ‖a p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P)) (k : ℕ) := by
      apply Finset.sum_le_sum
      intro k _
      have hk_mem := k.2
      rw [Finset.mem_filter, Finset.mem_Ioc] at hk_mem
      dsimp [b]
      exact norm_sq_b_le a (k : ℕ) P hP hk_mem.1.1
    have h_att := sum_subtype_eq PrimesP (fun (p : ℕ) => ‖a p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P))
    rwa [h_att] at h_b_eq
  exact mul_le_mul_of_nonneg_left h_b_sum hD

lemma phi_ge_one' {K : ℝ} (hK : 1 ≤ K) :
    ∀ t, 3 ≤ t → 1 ≤ K * (Real.log t) ^ 2 := by
  intro t ht
  have hlog3 : 1 < Real.log 3 := logt_gt_one (le_refl 3)
  have hlogt : 1 < Real.log t := lt_of_lt_of_le hlog3 (Real.log_le_log (by norm_num) ht)
  have hsq : 1 ≤ (Real.log t) ^ 2 := by nlinarith
  nlinarith

lemma phi_mono' {K : ℝ} (hK : 0 ≤ K) :
    MonotoneOn (fun t => K * (Real.log t) ^ 2) (Set.Ici 3) := by
  intro x hx y hy hxy
  have hx3 : (3 : ℝ) ≤ x := hx
  have hy3 : (3 : ℝ) ≤ y := hy
  have hx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hy_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlog_le : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  have hsq_le : (Real.log x) ^ 2 ≤ (Real.log y) ^ 2 := sq_le_sq' (by linarith) hlog_le
  exact mul_le_mul_of_nonneg_left hsq_le hK

lemma x0_bounds (P : ℕ) (hP : 3 ≤ P) :
    let X₀ := (2 * (P : ℝ)) / (1 - Real.log 2 / 2)
    3 < X₀ ∧ (P : ℝ) ≤ X₀ ∧ X₀ ≤ 4 * (P : ℝ) := by
  intro X₀
  have hdenom_pos := one_sub_half_log2_pos
  have h1 : 3 < X₀ := by
    dsimp [X₀]
    have : (3 : ℝ) < 2 * (P : ℝ) := by exact_mod_cast (by omega : 3 < 2 * P)
    have : 2 * (P : ℝ) ≤ (2 * (P : ℝ)) / (1 - Real.log 2 / 2) := by
      rw [le_div_iff₀ hdenom_pos]
      have := log2_pos
      nlinarith
    linarith
  have h2 : (P : ℝ) ≤ X₀ := by
    dsimp [X₀]
    rw [le_div_iff₀ hdenom_pos]
    have := log2_pos
    nlinarith
  have h3 : X₀ ≤ 4 * (P : ℝ) := by
    dsimp [X₀]
    rw [div_le_iff₀ hdenom_pos]
    have := log2_lt_one
    nlinarith
  exact ⟨h1, h2, h3⟩

lemma t_prime_bounds {K P T : ℝ} (hK : 1 ≤ K) (hP : 3 ≤ P) (hT : 3 ≤ T) :
    let T' := (9 * K) ^ 3 * (P * T) ^ 5
    3 < T' ∧ (9 * K) ^ 3 ≤ T' ∧ 4 * T + 3 ≤ T' := by
  intro T'
  have h9K : (9 : ℝ) ≤ 9 * K := by linarith
  have hPT : (9 : ℝ) ≤ P * T := by nlinarith
  have h9K_pow : (9 : ℝ) ^ 3 ≤ (9 * K) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) h9K 3
  have hPT_pow : (9 : ℝ) ^ 5 ≤ (P * T) ^ 5 :=
    pow_le_pow_left₀ (by norm_num) hPT 5
  have h9K_pos : (0 : ℝ) < (9 * K) ^ 3 := by positivity
  have hPT_pos : (0 : ℝ) < (P * T) ^ 5 := by positivity
  have h1 : 3 < T' := by
    dsimp [T']
    have h_large : (9 : ℝ) ^ 3 * (9 : ℝ) ^ 5 ≤ (9 * K) ^ 3 * (P * T) ^ 5 :=
      mul_le_mul h9K_pow hPT_pow (by positivity) h9K_pos.le
    have : (3 : ℝ) < (9 : ℝ) ^ 3 * (9 : ℝ) ^ 5 := by norm_num
    linarith
  have h2 : (9 * K) ^ 3 ≤ T' := by
    dsimp [T']
    have : 1 ≤ (P * T) ^ 5 := by
      have : (1 : ℝ) ≤ (9 : ℝ) ^ 5 := by norm_num
      linarith
    calc (9 * K) ^ 3 = (9 * K) ^ 3 * 1 := by ring
      _ ≤ (9 * K) ^ 3 * (P * T) ^ 5 := mul_le_mul_of_nonneg_left this h9K_pos.le
  have h3 : 4 * T + 3 ≤ T' := by
    dsimp [T']
    have hT_pos : 0 < T := by linarith
    have h4T : 4 * T + 3 ≤ 5 * T := by linarith
    have hPT_ge_1 : 1 ≤ P * T := by linarith
    have h5T : 5 * T ≤ (P * T) ^ 2 := by
      have : (P * T) ^ 2 = P ^ 2 * T ^ 2 := by ring
      rw [this]
      have hP2 : 5 ≤ P ^ 2 := by nlinarith
      have hT2 : T ≤ T ^ 2 := by nlinarith
      nlinarith
    have h25 : (P * T) ^ 2 ≤ (P * T) ^ 5 :=
      pow_le_pow_right₀ hPT_ge_1 (by norm_num)
    have h_ge : 5 * T ≤ (P * T) ^ 5 := le_trans h5T h25
    have h9K3_ge1 : 1 ≤ (9 * K) ^ 3 := by
      have : (1 : ℝ) ≤ (9 : ℝ) ^ 3 := by norm_num
      linarith
    calc 4 * T + 3 ≤ 5 * T := h4T
      _ ≤ (P * T) ^ 5 := h_ge
      _ = 1 * (P * T) ^ 5 := by ring
      _ ≤ (9 * K) ^ 3 * (P * T) ^ 5 := mul_le_mul_of_nonneg_right h9K3_ge1 (by positivity)
  exact ⟨h1, h2, h3⟩

lemma error_term1_le_one {K P T X₀ : ℝ} (hK : 1 ≤ K) (hP : 3 ≤ P) (hT : 3 ≤ T)
    (hX₀_pos : 0 < X₀) (hX₀_le : X₀ ≤ 4 * P) :
    let T' := (9 * K) ^ 3 * (P * T) ^ 5
    X₀ * Real.log X₀ / ((1 / 2 : ℝ) * T') ≤ 1 := by
  intro T'
  have hPT_ge_9 : (9 : ℝ) ≤ P * T := by nlinarith
  have hlogX₀ : Real.log X₀ ≤ X₀ := by
    linarith [Real.log_le_sub_one_of_pos hX₀_pos]
  have hX₀_le_PT : X₀ ≤ 4 * (P * T) := by
    calc X₀ ≤ 4 * P := hX₀_le
      _ = 4 * P * 1 := by ring
      _ ≤ 4 * P * T := mul_le_mul_of_nonneg_left (by linarith : 1 ≤ T) (by positivity)
      _ = 4 * (P * T) := by ring
  have h_denom : 32 * (P * T) ^ 2 ≤ T' := by
    dsimp [T']
    have h9K3 : 1 ≤ (9 * K) ^ 3 := by
      have : (1 : ℝ) ≤ (9 : ℝ) ^ 3 := by norm_num
      have : (9 : ℝ) ≤ 9 * K := by linarith
      have h_pow := pow_le_pow_left₀ (by norm_num) this 3
      linarith
    have hPT3 : (9 : ℝ) ^ 3 ≤ (P * T) ^ 3 := pow_le_pow_left₀ (by norm_num) hPT_ge_9 3
    have hPT5 : (9 : ℝ) ^ 3 * (P * T) ^ 2 ≤ (P * T) ^ 5 := by
      have : (P * T) ^ 5 = (P * T) ^ 3 * (P * T) ^ 2 := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hPT3 (by positivity)
    calc 32 * (P * T) ^ 2 ≤ 729 * (P * T) ^ 2 := by nlinarith
      _ = (9 : ℝ) ^ 3 * (P * T) ^ 2 := by norm_num
      _ ≤ (P * T) ^ 5 := hPT5
      _ = 1 * (P * T) ^ 5 := by ring
      _ ≤ (9 * K) ^ 3 * (P * T) ^ 5 := mul_le_mul_of_nonneg_right h9K3 (by positivity)
  have hT'_pos : 0 < T' := by dsimp [T']; positivity
  have : X₀ * Real.log X₀ / ((1 / 2 : ℝ) * T') = 2 * (X₀ * Real.log X₀) / T' := by ring
  rw [this]
  rw [div_le_one₀ hT'_pos]
  calc 2 * (X₀ * Real.log X₀) ≤ 2 * (X₀ * X₀) := by
        have := mul_le_mul_of_nonneg_left hlogX₀ hX₀_pos.le
        linarith
    _ ≤ 2 * ((4 * (P * T)) * (4 * (P * T))) := by
        have := mul_le_mul hX₀_le_PT hX₀_le_PT hX₀_pos.le (by positivity)
        linarith
    _ = 32 * (P * T) ^ 2 := by ring
    _ ≤ T' := h_denom

lemma error_term3_le {c σ₂ P PT X₀ : ℝ} (_hc_pos : 0 < c) (hc_le : c ≤ 1 - σ₂)
    (hP : 3 ≤ P) (hPT : (9 : ℝ) ≤ PT) (hX₀_ge : P ≤ X₀) (hX₀_le : X₀ ≤ 4 * P) :
    X₀ ^ σ₂ / (1 / 2 : ℝ) ≤
      8 * P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) * (Real.log PT) ^ 2 := by
  have hP_pos : 0 < P := by linarith
  have hX₀_pos : 0 < X₀ := by linarith
  have hlogP_pos : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogPT_pos : 0 < Real.log PT := Real.log_pos (by linarith)
  have hlogPT_ge1 : 1 ≤ Real.log PT := by
    have : (Real.exp 1 : ℝ) ≤ 9 := by
      have := Real.exp_one_lt_d9; linarith
    have : (Real.exp 1 : ℝ) ≤ PT := le_trans this hPT
    have := Real.log_le_log (by positivity) this
    rwa [Real.log_exp] at this
  have hpow_ge1 : 1 ≤ (Real.log PT) ^ (3 / 4 : ℝ) := by
    have : (1 : ℝ) = (1 : ℝ) ^ (3 / 4 : ℝ) := by norm_num
    rw [this]
    exact Real.rpow_le_rpow (by norm_num) hlogPT_ge1 (by norm_num)
  have hsq_ge1 : 1 ≤ (Real.log PT) ^ 2 := by nlinarith
  have hc_div_le : c / (Real.log PT) ^ (3 / 4 : ℝ) ≤ 1 - σ₂ := by
    calc c / (Real.log PT) ^ (3 / 4 : ℝ) ≤ c / 1 :=
        div_le_div_of_nonneg_left _hc_pos.le (by norm_num) hpow_ge1
      _ = c := div_one c
      _ ≤ 1 - σ₂ := hc_le
  have h_div_mul : (c / (Real.log PT) ^ (3 / 4 : ℝ)) * Real.log P = c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) := by ring
  have h_step : c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) ≤ (1 - σ₂) * Real.log P := by
    rw [← h_div_mul]
    exact mul_le_mul_of_nonneg_right hc_div_le hlogP_pos.le
  have h_exp_arg : -(1 - σ₂) * Real.log P ≤ -c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) := by
    have this1 := neg_le_neg h_step
    have h_neg1 : -((1 - σ₂) * Real.log P) = -(1 - σ₂) * Real.log P := by ring
    have h_neg2 : -(c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) = -c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) := by ring
    rwa [h_neg1, h_neg2] at this1
  have h_rpow : X₀ ^ σ₂ = Real.exp (Real.log X₀ * σ₂) := Real.rpow_def_of_pos hX₀_pos σ₂
  have h_alg : Real.log X₀ * σ₂ = Real.log X₀ + -(1 - σ₂) * Real.log X₀ := by ring
  have h_exp_split : Real.exp (Real.log X₀ * σ₂) = X₀ * Real.exp (-(1 - σ₂) * Real.log X₀) := by
    rw [h_alg, Real.exp_add, Real.exp_log hX₀_pos]
  rw [h_rpow, h_exp_split]
  have hlog_le : Real.log P ≤ Real.log X₀ := Real.log_le_log hP_pos hX₀_ge
  have h_arg_le : -(1 - σ₂) * Real.log X₀ ≤ -(1 - σ₂) * Real.log P := by
    have : 0 ≤ 1 - σ₂ := by linarith
    nlinarith
  have h_exp_le : Real.exp (-(1 - σ₂) * Real.log X₀) ≤ Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) :=
    le_trans (Real.exp_le_exp.mpr h_arg_le) (Real.exp_le_exp.mpr h_exp_arg)
  have h_div_half : X₀ * Real.exp (-(1 - σ₂) * Real.log X₀) / (1 / 2 : ℝ) =
      2 * (X₀ * Real.exp (-(1 - σ₂) * Real.log X₀)) := by ring
  rw [h_div_half]
  have h_le_step : 2 * (X₀ * Real.exp (-(1 - σ₂) * Real.log X₀)) ≤
      8 * P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) := by
    calc 2 * (X₀ * Real.exp (-(1 - σ₂) * Real.log X₀))
        = 2 * X₀ * Real.exp (-(1 - σ₂) * Real.log X₀) := by ring
      _ ≤ 2 * (4 * P) * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) :=
        mul_le_mul (by linarith) h_exp_le (by positivity) (by positivity)
      _ = 8 * P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) := by ring
  calc 2 * (X₀ * Real.exp (-(1 - σ₂) * Real.log X₀))
      ≤ 8 * P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) := h_le_step
    _ = 8 * P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) * 1 := by ring
    _ ≤ 8 * P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) * (Real.log PT) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq_ge1 (by positivity)

lemma error_term2_le {c c₀' B_K K P PT T' X₀ : ℝ}
    (hc₀'_pos : 0 < c₀') (hBK_ge1 : 1 ≤ B_K)
    (hc_le : c ≤ c₀' / B_K ^ (3 / 4 : ℝ)) (hK : 0 ≤ K)
    (hP : 3 ≤ P) (hPT : (9 : ℝ) ≤ PT)
    (hT' : 3 ≤ T') (hlogT'_le : Real.log T' ≤ B_K * Real.log PT)
    (hX₀_ge : P ≤ X₀) (hX₀_le : X₀ ≤ 4 * P) :
    let θ : ℝ → ℝ := fun t => c₀' / (Real.log t) ^ (3 / 4 : ℝ)
    let φ : ℝ → ℝ := fun t => K * (Real.log t) ^ 2
    X₀ ^ (1 - θ T') * φ T' / (1 / 2 : ℝ) ≤
      8 * K * B_K ^ 2 * P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) * (Real.log PT) ^ 2 := by
  intro θ φ
  have hP_pos : 0 < P := by linarith
  have hX₀_pos : 0 < X₀ := by linarith
  have hlogP_pos : 0 < Real.log P := Real.log_pos (by linarith)
  have hlogPT_pos : 0 < Real.log PT := Real.log_pos (by linarith)
  have hlogT'_pos : 0 < Real.log T' := Real.log_pos (by linarith)
  have htheta_le := theta_bk_le hc₀'_pos hBK_ge1 hlogT'_pos hlogPT_pos hlogT'_le
  have hc_div_le : c / (Real.log PT) ^ (3 / 4 : ℝ) ≤ θ T' := by
    have hpow_pos : 0 < (Real.log PT) ^ (3 / 4 : ℝ) := rpow_pos_of_pos hlogPT_pos _
    have : c / (Real.log PT) ^ (3 / 4 : ℝ) ≤ (c₀' / B_K ^ (3 / 4 : ℝ)) / (Real.log PT) ^ (3 / 4 : ℝ) :=
      div_le_div_of_nonneg_right hc_le hpow_pos.le
    dsimp [θ]
    exact le_trans this htheta_le
  have h_div_mul : (c / (Real.log PT) ^ (3 / 4 : ℝ)) * Real.log P = c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) := by ring
  have h_step : c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) ≤ θ T' * Real.log P := by
    rw [← h_div_mul]
    exact mul_le_mul_of_nonneg_right hc_div_le hlogP_pos.le
  have h_exp_arg : -θ T' * Real.log P ≤ -c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) := by
    have this1 := neg_le_neg h_step
    have h_neg1 : -(θ T' * Real.log P) = -θ T' * Real.log P := by ring
    have h_neg2 : -(c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) = -c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ) := by ring
    rwa [h_neg1, h_neg2] at this1
  have h_rpow : X₀ ^ (1 - θ T') = Real.exp (Real.log X₀ * (1 - θ T')) := Real.rpow_def_of_pos hX₀_pos (1 - θ T')
  have h_alg : Real.log X₀ * (1 - θ T') = Real.log X₀ + -θ T' * Real.log X₀ := by ring
  have h_exp_split : Real.exp (Real.log X₀ * (1 - θ T')) = X₀ * Real.exp (-θ T' * Real.log X₀) := by
    rw [h_alg, Real.exp_add, Real.exp_log hX₀_pos]
  rw [h_rpow, h_exp_split]
  have hlog_le : Real.log P ≤ Real.log X₀ := Real.log_le_log hP_pos hX₀_ge
  have hθ_nonneg : 0 ≤ θ T' := by dsimp [θ]; positivity
  have h_arg_le : -θ T' * Real.log X₀ ≤ -θ T' * Real.log P := by
    nlinarith
  have h_exp_le : Real.exp (-θ T' * Real.log X₀) ≤ Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) :=
    le_trans (Real.exp_le_exp.mpr h_arg_le) (Real.exp_le_exp.mpr h_exp_arg)
  have hphi_le : φ T' ≤ K * B_K ^ 2 * (Real.log PT) ^ 2 := by
    dsimp [φ]
    have hsq : (Real.log T') ^ 2 ≤ (B_K * Real.log PT) ^ 2 :=
      sq_le_sq' (by linarith) hlogT'_le
    have h_distrib : (B_K * Real.log PT) ^ 2 = B_K ^ 2 * (Real.log PT) ^ 2 := by ring
    rw [h_distrib] at hsq
    have : K * (Real.log T') ^ 2 ≤ K * (B_K ^ 2 * (Real.log PT) ^ 2) :=
      mul_le_mul_of_nonneg_left hsq hK
    calc K * (Real.log T') ^ 2 ≤ K * (B_K ^ 2 * (Real.log PT) ^ 2) := this
      _ = K * B_K ^ 2 * (Real.log PT) ^ 2 := by ring
  have h_div_half : (X₀ * Real.exp (-θ T' * Real.log X₀)) * φ T' / (1 / 2 : ℝ) =
      2 * (X₀ * Real.exp (-θ T' * Real.log X₀) * φ T') := by ring
  rw [h_div_half]
  have h_le_step : 2 * (X₀ * Real.exp (-θ T' * Real.log X₀) * φ T') ≤
      8 * K * B_K ^ 2 * P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) * (Real.log PT) ^ 2 := by
    have h2 : X₀ * Real.exp (-θ T' * Real.log X₀) ≤ (4 * P) * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) :=
      mul_le_mul hX₀_le h_exp_le (by positivity) (by linarith)
    have h_prod := mul_le_mul h2 hphi_le (by dsimp [φ]; positivity) (by positivity)
    calc 2 * (X₀ * Real.exp (-θ T' * Real.log X₀) * φ T')
        ≤ 2 * ((4 * P) * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) * (K * B_K ^ 2 * (Real.log PT) ^ 2)) :=
        mul_le_mul_of_nonneg_left h_prod (by norm_num)
      _ = 8 * K * B_K ^ 2 * P * Real.exp (-c * Real.log P / (Real.log PT) ^ (3 / 4 : ℝ)) * (Real.log PT) ^ 2 := by ring
  exact h_le_step

lemma twistedSum_zero_re_le (ν : ℝ → ℝ) (ε X : ℝ) (P : ℕ) (hP : 3 ≤ P)
    (h_supp : ∀ n : ℕ, 8 * P < n → Smooth1 ν ε (n / X) = 0)
    (h_smooth_le : ∀ n ∈ Finset.Icc 1 (8 * P), Smooth1 ν ε (n / X) ≤ 1) :
    (twistedSum ν ε X 0).re ≤ 60 * (P : ℝ) := by
  have h_eq : twistedSum ν ε X 0 = ∑ n ∈ Finset.Icc 1 (8 * P),
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(0 : ℂ) * Complex.I) * (Smooth1 ν ε (n / X) : ℂ) :=
    twistedSum_eq_sum ν ε X 0 P h_supp
  rw [h_eq]
  have h_term : ∀ n ∈ Finset.Icc 1 (8 * P),
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(0 : ℂ) * Complex.I) * (Smooth1 ν ε (n / X) : ℂ) =
        ((ArithmeticFunction.vonMangoldt n * Smooth1 ν ε (n / X) : ℝ) : ℂ) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have : -(0 : ℂ) * Complex.I = 0 := by ring
    rw [this, Complex.cpow_zero]
    push_cast; ring
  have h_sum_cast : (∑ n ∈ Finset.Icc 1 (8 * P),
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(0 : ℂ) * Complex.I) * (Smooth1 ν ε (n / X) : ℂ)) =
      ((∑ n ∈ Finset.Icc 1 (8 * P), ArithmeticFunction.vonMangoldt n * Smooth1 ν ε (n / X) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl h_term
  rw [h_sum_cast, Complex.ofReal_re]
  have h_le : (∑ n ∈ Finset.Icc 1 (8 * P), ArithmeticFunction.vonMangoldt n * Smooth1 ν ε (n / X)) ≤
      ∑ n ∈ Finset.Icc 1 (8 * P), ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_le_sum
    intro n hn
    have h1 := h_smooth_le n hn
    have h2 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    calc ArithmeticFunction.vonMangoldt n * Smooth1 ν ε (n / X)
        ≤ ArithmeticFunction.vonMangoldt n * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = ArithmeticFunction.vonMangoldt n := mul_one _
  refine h_le.trans ?_
  exact sum_Icc_vonMangoldt_le P hP

lemma norm_eta_conj_mul (a b c : ℂ) :
    ‖a * (starRingEnd ℂ) b * c‖ = ‖a‖ * ‖b‖ * ‖c‖ := by
  rw [norm_mul, norm_mul, Complex.norm_conj]

lemma re_le_norm (z : ℂ) : z.re ≤ ‖z‖ :=
  le_trans (le_abs_self z.re) (Complex.abs_re_le_norm z)

lemma smooth1_props (ν : ℝ → ℝ) (suppν : ν.support ⊆ Set.Icc (1 / 2) 2)
    (νnonneg : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) (P : ℕ) (hP : 3 ≤ P) :
    let X₀ := (2 * (P : ℝ)) / (1 - Real.log 2 / 2)
    (∀ n : ℕ, 1 ≤ n → n ≤ 2 * P → Smooth1 ν (1 / 2) (n / X₀) = 1) ∧
    (∀ n : ℕ, 8 * P < n → Smooth1 ν (1 / 2) (n / X₀) = 0) ∧
    (∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n * Smooth1 ν (1 / 2) (n / X₀)) ∧
    (∀ n ∈ Finset.Icc 1 (8 * P), Smooth1 ν (1 / 2) ((n : ℝ) / X₀) ≤ 1) := by
  intro X₀
  obtain ⟨c₁, hc₁_pos, hc₁_eq, hc₁⟩ := Smooth1Properties_below suppν mass_one
  obtain ⟨c₂, hc₂_pos, hc₂_eq, hc₂⟩ := Smooth1Properties_above suppν
  have hX₀_pos : 0 < X₀ := by
    dsimp [X₀]
    have : 0 < (P : ℝ) := by exact_mod_cast (by omega : 0 < P)
    have : 0 < 1 - Real.log 2 / 2 := one_sub_half_log2_pos
    positivity
  have h1 : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * P → Smooth1 ν (1 / 2) (n / X₀) = 1 := by
    intro n hn1 hn2
    have hn_pos : 0 < ((n : ℝ) / X₀) := by
      have : 0 < (n : ℝ) := by exact_mod_cast hn1
      positivity
    have hn_le : (n : ℝ) / X₀ ≤ 1 - c₁ * (1 / 2) := by
      rw [div_le_iff₀ hX₀_pos, hc₁_eq]
      dsimp [X₀]
      have hdenom := one_sub_half_log2_pos
      have h_cancel : (1 - Real.log 2 * (1 / 2 : ℝ)) * (2 * (P : ℝ) / (1 - Real.log 2 / 2)) = 2 * (P : ℝ) := by
        have h_eq : 1 - Real.log 2 * (1 / 2 : ℝ) = 1 - Real.log 2 / 2 := by ring
        rw [h_eq, mul_div_cancel₀ _ (ne_of_gt hdenom)]
      rw [h_cancel]
      exact_mod_cast hn2
    exact hc₁ (1 / 2) (n / X₀) (by norm_num) hn_pos hn_le
  have h2 : ∀ n : ℕ, 8 * P < n → Smooth1 ν (1 / 2) (n / X₀) = 0 := by
    intro n hn
    have h_ratio := ratio_le_four
    have hX₀_bound : X₀ * (1 + Real.log 2) ≤ 8 * (P : ℝ) := by
      dsimp [X₀]
      have hpos := one_sub_half_log2_pos
      have : (2 * (P : ℝ)) / (1 - Real.log 2 / 2) * (1 + Real.log 2) =
          (2 * (P : ℝ)) * ((1 + Real.log 2) / (1 - Real.log 2 / 2)) := by ring
      rw [this]
      have : (2 * (P : ℝ)) * ((1 + Real.log 2) / (1 - Real.log 2 / 2)) ≤ (2 * (P : ℝ)) * 4 :=
        mul_le_mul_of_nonneg_left h_ratio (by positivity)
      linarith
    have h_c2_half : 1 + c₂ * (1 / 2 : ℝ) = 1 + Real.log 2 := by
      rw [hc₂_eq]; ring
    have h_ge : 1 + c₂ * (1 / 2 : ℝ) ≤ (n : ℝ) / X₀ := by
      rw [h_c2_half]
      rw [le_div_iff₀ hX₀_pos]
      have : (8 * (P : ℝ)) < (n : ℝ) := by exact_mod_cast hn
      linarith
    have h_eps : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by
      refine ⟨by norm_num, by norm_num⟩
    exact hc₂ (1 / 2) (n / X₀) h_eps h_ge
  have h3 : ∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n * Smooth1 ν (1 / 2) (n / X₀) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp [ArithmeticFunction.map_zero]
    · have hn_pos : 0 < (n : ℝ) / X₀ := by
        have : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
        positivity
      have h_vm := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have h_sm := Smooth1Nonneg νnonneg hn_pos (by norm_num : (0 : ℝ) < 1 / 2)
      exact mul_nonneg h_vm h_sm
  have h4 : ∀ n ∈ Finset.Icc 1 (8 * P), Smooth1 ν (1 / 2) ((n : ℝ) / X₀) ≤ 1 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn_pos : 0 < (n : ℝ) / X₀ := by
      have : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
      positivity
    exact Smooth1LeOne νnonneg mass_one (by norm_num) hn_pos
  exact ⟨h1, h2, h3, h4⟩

set_option maxHeartbeats 800000 in
theorem sum_wellSpaced_norm_sq_prime_poly_le (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (P : ℕ) (a : ℕ → ℂ) (T : ℝ) (S : Finset ℝ), 3 ≤ P → 3 ≤ T → WellSpaced S → (∀ t ∈ S, |t| ≤ T) →
      (∑ t ∈ S, ‖dirichletPoly a ((Finset.Ioc P (2 * P)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C * ((P : ℝ) + S.card * P * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2) *
          ∑ p ∈ (Finset.Ioc P (2 * P)).filter Nat.Prime, ‖a p‖ ^ 2 / ((p : ℝ) ^ 2 * Real.log P) := by
  obtain ⟨ν, diffν, νnonneg_all, suppν, mass_one_ici⟩ := SmoothExistence
  have diffν1 : ContDiff ℝ 1 ν := diffν.of_le (by simp)
  have νnonneg : ∀ x > 0, 0 ≤ ν x := fun x _ => νnonneg_all x
  have mass_one : ∫ x in Set.Ioi 0, ν x / x = 1 := by rwa [← MeasureTheory.integral_Ici_eq_integral_Ioi]
  obtain ⟨C_M, hCM_pos, hCM⟩ := mellin_smooth1_bound diffν1 suppν
  obtain ⟨σ₂, σ₂_pos, σ₂_lt_one, h_holo_zeta⟩ := holo_zeta_of_smallT
  let θ₀ := (1 - σ₂) / 2
  have hθ₀_pos : 0 < θ₀ := by dsimp [θ₀]; linarith
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog3_34_pos : 0 < (Real.log 3) ^ (3 / 4 : ℝ) := rpow_pos_of_pos hlog3_pos _
  let c₀' := min c₀ (min ((1 / 2 : ℝ) * (Real.log 3) ^ (3 / 4 : ℝ)) (θ₀ * (Real.log 3) ^ (3 / 4 : ℝ)))
  have hc₀'_pos : 0 < c₀' := by
    dsimp [c₀']
    have : 0 < (1 / 2 : ℝ) * (Real.log 3) ^ (3 / 4 : ℝ) := mul_pos (by norm_num) hlog3_34_pos
    have : 0 < θ₀ * (Real.log 3) ^ (3 / 4 : ℝ) := mul_pos hθ₀_pos hlog3_34_pos
    positivity
  have hc₀'_le_c₀ : c₀' ≤ c₀ := min_le_left _ _
  have hc₀'_le_half : c₀' ≤ (1 / 2 : ℝ) * (Real.log 3) ^ (3 / 4 : ℝ) :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hc₀'_le_theta0 : c₀' ≤ θ₀ * (Real.log 3) ^ (3 / 4 : ℝ) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hζ' := hzeta_mono hc₀'_le_c₀ hζ
  have hholo' := hholo_mono hc₀'_le_c₀ hholo
  let θ : ℝ → ℝ := fun t => c₀' / (Real.log t) ^ (3 / 4 : ℝ)
  let φ : ℝ → ℝ := fun t => K * (Real.log t) ^ 2
  have hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2 := by
    intro t ht
    have ht_pos : 0 < Real.log t := Real.log_pos (by linarith)
    have h1 : 0 < θ t := by dsimp [θ]; positivity
    have hlog3_le : (Real.log 3) ^ (3 / 4 : ℝ) ≤ (Real.log t) ^ (3 / 4 : ℝ) :=
      rpow_le_rpow (Real.log_pos (by norm_num)).le (Real.log_le_log (by norm_num) ht) (by norm_num)
    have h2 : θ t ≤ 1 / 2 := by
      dsimp [θ]
      calc c₀' / (Real.log t) ^ (3 / 4 : ℝ)
          ≤ ((1 / 2 : ℝ) * (Real.log 3) ^ (3 / 4 : ℝ)) / (Real.log t) ^ (3 / 4 : ℝ) :=
            div_le_div_of_nonneg_right hc₀'_le_half (by positivity)
        _ ≤ ((1 / 2 : ℝ) * (Real.log 3) ^ (3 / 4 : ℝ)) / (Real.log 3) ^ (3 / 4 : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) hlog3_34_pos hlog3_le
        _ = 1 / 2 := by
            rw [mul_div_cancel_right₀ _ (ne_of_gt hlog3_34_pos)]
    exact ⟨h1, h2⟩
  have hθanti : AntitoneOn θ (Set.Ici 3) := theta_antitone hc₀'_pos.le
  have hφ : ∀ t, 3 ≤ t → 1 ≤ φ t := phi_ge_one' hK
  have hφmono : MonotoneOn φ (Set.Ici 3) := phi_mono' (by linarith)
  obtain ⟨C_tw, hCtw_pos, h_tw⟩ :=
    twistedSum_sub_main_le_of_holo ν diffν1 suppν νnonneg mass_one σ₂ σ₂_pos σ₂_lt_one h_holo_zeta
      θ φ hθ hθanti hφ hφmono hζ' hholo'
  let B_K := 3 * Real.log (9 * K) / Real.log 9 + 5
  have hBK_ge1 : 1 ≤ B_K := by
    dsimp [B_K]
    have : 0 ≤ 3 * Real.log (9 * K) / Real.log 9 := by
      have h9K : 1 ≤ 9 * K := by linarith
      have : 0 ≤ Real.log (9 * K) := Real.log_nonneg h9K
      have : 0 < Real.log 9 := Real.log_pos (by norm_num)
      positivity
    linarith
  let c := min (c₀' / B_K ^ (3 / 4 : ℝ)) (min (1 - σ₂) (1 / 2 : ℝ))
  have hc_pos : 0 < c := by
    dsimp [c]
    have : 0 < c₀' / B_K ^ (3 / 4 : ℝ) := div_pos hc₀'_pos (rpow_pos_of_pos (by linarith) _)
    have : 0 < 1 - σ₂ := by linarith
    have : 0 < (1 / 2 : ℝ) := by norm_num
    positivity
  have hc_le_BK : c ≤ c₀' / B_K ^ (3 / 4 : ℝ) := min_le_left _ _
  have hc_le_sigma2 : c ≤ 1 - σ₂ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc_le_half : c ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  let C := max (60 + 32 * C_M) (C_tw * (9 + 8 * K * B_K ^ 2)) + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    have : 0 < 60 + 32 * C_M := by positivity
    have : 0 ≤ max (60 + 32 * C_M) (C_tw * (9 + 8 * K * B_K ^ 2)) := by
      refine le_trans (by positivity) (le_max_left _ _)
    linarith
  refine ⟨c, C, hc_pos, hC_pos, ?_⟩
  intro P a T S hP hT hS hS_le
  let PrimesP := (Finset.Ioc P (2 * P)).filter Nat.Prime
  let D := C * ((P : ℝ) + (S.card : ℝ) * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2)
  have hD : 0 ≤ D := by
    dsimp [D]
    have : 0 ≤ (P : ℝ) := by positivity
    have : 0 ≤ (S.card : ℝ) := by positivity
    positivity
  apply duality_applied P hP a S D hD
  intro η
  let X₀ := (2 * (P : ℝ)) / (1 - Real.log 2 / 2)
  obtain ⟨h_below, h_supp, h_vm_sm_nonneg, h_sm_le_one⟩ :=
    smooth1_props ν suppν νnonneg mass_one P hP
  obtain ⟨hX₀_gt3, hX₀_geP, hX₀_le4P⟩ := x0_bounds P hP
  have hX₀_pos : 0 < X₀ := by linarith
  have hP_real : (3 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hPT_ge9 : (9 : ℝ) ≤ (P : ℝ) * T := by nlinarith
  let T' := (9 * K) ^ 3 * ((P : ℝ) * T) ^ 5
  obtain ⟨hT'_gt3, hT'_ge9K, hT'_ge4T⟩ := t_prime_bounds hK hP_real hT
  have hT'_ge3 : 3 ≤ T' := hT'_gt3.le
  have h_prime_le_smooth :=
    prime_sum_le_smooth_sum ν P hP X₀ h_below (fun n => h_vm_sm_nonneg n) S η
  refine h_prime_le_smooth.trans ?_
  have h_tsum_eq : ∀ u, twistedSum ν (1 / 2) X₀ u = ∑ n ∈ Finset.Icc 1 (8 * P),
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I) * (Smooth1 ν (1 / 2) (n / X₀) : ℂ) :=
    fun u => twistedSum_eq_sum ν (1 / 2) X₀ u P h_supp
  have h_smooth_eq := smooth_sum_eq_sum_twisted ν (1 / 2) X₀ P h_tsum_eq S η
  have h_re_eq : (∑ n ∈ Finset.Icc 1 (8 * P), ArithmeticFunction.vonMangoldt n * Smooth1 ν (1 / 2) (n / X₀) *
      ‖∑ t ∈ S, η t * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) =
      (∑ t ∈ S, ∑ t' ∈ S, η t * (starRingEnd ℂ) (η t') * twistedSum ν (1 / 2) X₀ (t' - t)).re := by
    have := congr_arg Complex.re h_smooth_eq
    rwa [Complex.ofReal_re] at this
  rw [h_re_eq]
  have h_split := sum_pair_split S (fun t t' => η t * (starRingEnd ℂ) (η t') * twistedSum ν (1 / 2) X₀ (t' - t))
  rw [h_split, Complex.add_re]
  have h_sub_zero : (∑ t ∈ S, η t * (starRingEnd ℂ) (η t) * twistedSum ν (1 / 2) X₀ (t - t)) =
      ∑ t ∈ S, η t * (starRingEnd ℂ) (η t) * twistedSum ν (1 / 2) X₀ 0 := by
    apply Finset.sum_congr rfl
    intro t _
    rw [sub_self]
  rw [h_sub_zero]
  have h_diag_eq : (∑ t ∈ S, η t * (starRingEnd ℂ) (η t) * twistedSum ν (1 / 2) X₀ 0).re =
      (twistedSum ν (1 / 2) X₀ 0).re * ∑ t ∈ S, ‖η t‖ ^ 2 := by
    have h1 : (∑ t ∈ S, η t * (starRingEnd ℂ) (η t) * twistedSum ν (1 / 2) X₀ 0) =
        (twistedSum ν (1 / 2) X₀ 0) * ∑ t ∈ S, ((‖η t‖ ^ 2 : ℝ) : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      have : η t * (starRingEnd ℂ) (η t) = ((‖η t‖ ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
        ring
      rw [this]
      ring
    rw [h1, ← Complex.ofReal_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [h_diag_eq]
  have h_diag_le : (twistedSum ν (1 / 2) X₀ 0).re * (∑ t ∈ S, ‖η t‖ ^ 2) ≤
      (60 * (P : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 := by
    have h_re := twistedSum_zero_re_le ν (1 / 2) X₀ P hP h_supp h_sm_le_one
    have h_sum_nonneg : 0 ≤ ∑ t ∈ S, ‖η t‖ ^ 2 := energy_nonneg S η
    exact mul_le_mul_of_nonneg_right h_re h_sum_nonneg
  have h_offdiag_re_le : (∑ t ∈ S, ∑ t' ∈ S \ {t}, η t * (starRingEnd ℂ) (η t') * twistedSum ν (1 / 2) X₀ (t' - t)).re ≤
      ∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * ‖twistedSum ν (1 / 2) X₀ (t' - t)‖ := by
    calc (∑ t ∈ S, ∑ t' ∈ S \ {t}, η t * (starRingEnd ℂ) (η t') * twistedSum ν (1 / 2) X₀ (t' - t)).re
        ≤ ‖∑ t ∈ S, ∑ t' ∈ S \ {t}, η t * (starRingEnd ℂ) (η t') * twistedSum ν (1 / 2) X₀ (t' - t)‖ :=
          re_le_norm _
      _ ≤ ∑ t ∈ S, ‖∑ t' ∈ S \ {t}, η t * (starRingEnd ℂ) (η t') * twistedSum ν (1 / 2) X₀ (t' - t)‖ :=
          norm_sum_le S _
      _ ≤ ∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t * (starRingEnd ℂ) (η t') * twistedSum ν (1 / 2) X₀ (t' - t)‖ :=
          Finset.sum_le_sum fun t _ => norm_sum_le (S \ {t}) _
      _ = ∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * ‖twistedSum ν (1 / 2) X₀ (t' - t)‖ := by
          apply Finset.sum_congr rfl; intro t _
          apply Finset.sum_congr rfl; intro t' _
          exact norm_eta_conj_mul (η t) (η t') _
  have h_offdiag_term : ∀ t ∈ S, ∀ t' ∈ S \ {t},
      ‖twistedSum ν (1 / 2) X₀ (t' - t)‖ ≤
        8 * C_M * (P : ℝ) * (1 / (t - t') ^ 2) +
          C_tw * (9 + 8 * K * B_K ^ 2) * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 := by
    intro t ht t' ht'
    rw [Finset.mem_sdiff, Finset.mem_singleton] at ht'
    have hne : t' ≠ t := ht'.2
    have ht'_in : t' ∈ S := ht'.1
    let u := t' - t
    have hu_ne : u ≠ 0 := sub_ne_zero.mpr hne
    have hu_le2T : |u| ≤ 2 * T := by
      have h1 : |t| ≤ T := hS_le t ht
      have h2 : |t'| ≤ T := hS_le t' ht'_in
      calc |u| = |t' - t| := rfl
        _ ≤ |t'| + |t| := abs_sub t' t
        _ ≤ T + T := add_le_add h2 h1
        _ = 2 * T := by ring
    have h2u3 : 2 * |u| + 3 ≤ T' := by
      calc 2 * |u| + 3 ≤ 2 * (2 * T) + 3 := by linarith
        _ = 4 * T + 3 := by ring
        _ ≤ T' := hT'_ge4T
    have hphiT' : φ T' ≤ T' := k_mul_log_sq_le_of_ge hK hT'_ge9K
    have hthetaT' : θ T' ≤ (1 - σ₂) / 2 := by
      dsimp [θ]
      have hlogT'_pos : 0 < Real.log T' := Real.log_pos (by linarith)
      have hlogT'_34_pos : 0 < (Real.log T') ^ (3 / 4 : ℝ) := rpow_pos_of_pos hlogT'_pos _
      have hlog3_le : (Real.log 3) ^ (3 / 4 : ℝ) ≤ (Real.log T') ^ (3 / 4 : ℝ) :=
        rpow_le_rpow (Real.log_pos (by norm_num)).le (Real.log_le_log (by norm_num) hT'_ge3) (by norm_num)
      calc c₀' / (Real.log T') ^ (3 / 4 : ℝ)
          ≤ (θ₀ * (Real.log 3) ^ (3 / 4 : ℝ)) / (Real.log T') ^ (3 / 4 : ℝ) :=
            div_le_div_of_nonneg_right hc₀'_le_theta0 hlogT'_34_pos.le
        _ ≤ (θ₀ * (Real.log 3) ^ (3 / 4 : ℝ)) / (Real.log 3) ^ (3 / 4 : ℝ) :=
            div_le_div_of_nonneg_left (mul_nonneg hθ₀_pos.le hlog3_34_pos.le) hlog3_34_pos hlog3_le
        _ = θ₀ := by rw [mul_div_cancel_right₀ _ (ne_of_gt hlog3_34_pos)]
        _ = (1 - σ₂) / 2 := rfl
    have h_diff := h_tw X₀ hX₀_gt3 (1 / 2) (by norm_num) (by norm_num) u T' hT'_gt3 h2u3 hphiT' hthetaT'
    let main := mellin (fun x => (Smooth1 ν (1 / 2) x : ℂ)) (1 - u * Complex.I) * (X₀ : ℂ) ^ ((1 : ℂ) - u * Complex.I)
    have h_tri : ‖twistedSum ν (1 / 2) X₀ u‖ ≤ ‖main‖ + ‖twistedSum ν (1 / 2) X₀ u - main‖ := by
      have : twistedSum ν (1 / 2) X₀ u = main + (twistedSum ν (1 / 2) X₀ u - main) := by ring
      calc ‖twistedSum ν (1 / 2) X₀ u‖ = ‖main + (twistedSum ν (1 / 2) X₀ u - main)‖ := congr_arg norm this
        _ ≤ ‖main‖ + ‖twistedSum ν (1 / 2) X₀ u - main‖ := norm_add_le _ _
    refine h_tri.trans ?_
    have h_main_le : ‖main‖ ≤ 8 * C_M * (P : ℝ) * (1 / (t - t') ^ 2) := by
      dsimp [main]
      rw [norm_mul, norm_cpow_one_sub_mul_I hX₀_pos]
      have h_m := hCM u hu_ne
      have hu_sq : u ^ 2 = (t - t') ^ 2 := by
        dsimp [u]; ring
      rw [hu_sq] at h_m
      calc ‖mellin (fun x => (Smooth1 ν (1 / 2) x : ℂ)) (1 - u * Complex.I)‖ * X₀
          ≤ (2 * C_M / (t - t') ^ 2) * (4 * (P : ℝ)) :=
            mul_le_mul h_m hX₀_le4P (by positivity) (by positivity)
        _ = 8 * C_M * (P : ℝ) * (1 / (t - t') ^ 2) := by ring
    have h_err1 := error_term1_le_one hK hP_real hT hX₀_pos hX₀_le4P
    have h_err1' : X₀ * Real.log X₀ / ((1 / 2 : ℝ) * T') ≤
        (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 :=
      le_trans h_err1 (exp_bound_of_c_le_half hc_pos hc_le_half hP_real hPT_ge9)
    have h_log_le : Real.log T' ≤ B_K * Real.log ((P : ℝ) * T) :=
      log_prod_le hK hP_real hT
    have h_err2 := error_term2_le hc₀'_pos hBK_ge1 hc_le_BK (by linarith : 0 ≤ K) hP_real hPT_ge9 hT'_ge3 h_log_le hX₀_geP hX₀_le4P
    have h_err3 := error_term3_le hc_pos hc_le_sigma2 hP_real hPT_ge9 hX₀_geP hX₀_le4P
    have h_err_sum : X₀ * Real.log X₀ / ((1 / 2 : ℝ) * T') + X₀ ^ (1 - θ T') * φ T' / (1 / 2 : ℝ) + X₀ ^ σ₂ / (1 / 2 : ℝ) ≤
        (9 + 8 * K * B_K ^ 2) * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 := by
      calc X₀ * Real.log X₀ / ((1 / 2 : ℝ) * T') + X₀ ^ (1 - θ T') * φ T' / (1 / 2 : ℝ) + X₀ ^ σ₂ / (1 / 2 : ℝ)
          ≤ ((P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2) +
            (8 * K * B_K ^ 2 * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2) +
            (8 * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2) := by
              have h12 := add_le_add h_err1' h_err2
              exact add_le_add h12 h_err3
        _ = (9 + 8 * K * B_K ^ 2) * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 := by ring
    have h_diff_le : ‖twistedSum ν (1 / 2) X₀ u - main‖ ≤
        C_tw * (9 + 8 * K * B_K ^ 2) * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 := by
      calc ‖twistedSum ν (1 / 2) X₀ u - main‖
          ≤ C_tw * (X₀ * Real.log X₀ / ((1 / 2 : ℝ) * T') + X₀ ^ (1 - θ T') * φ T' / (1 / 2 : ℝ) + X₀ ^ σ₂ / (1 / 2 : ℝ)) := h_diff
        _ ≤ C_tw * ((9 + 8 * K * B_K ^ 2) * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2) :=
          mul_le_mul_of_nonneg_left h_err_sum hCtw_pos.le
        _ = C_tw * (9 + 8 * K * B_K ^ 2) * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2 := by ring
    exact add_le_add h_main_le h_diff_le
  let E := C_tw * (9 + 8 * K * B_K ^ 2) * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2
  have h_prod_le : ∀ t ∈ S, ∀ t' ∈ S \ {t},
      ‖η t‖ * ‖η t'‖ * ‖twistedSum ν (1 / 2) X₀ (t' - t)‖ ≤
        8 * C_M * (P : ℝ) * (‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2)) + E * (‖η t‖ * ‖η t'‖) := by
    intro t ht t' ht'
    have ht_nonneg : 0 ≤ ‖η t‖ * ‖η t'‖ := by positivity
    have h_term := h_offdiag_term t ht t' ht'
    have h_term' : ‖twistedSum ν (1 / 2) X₀ (t' - t)‖ ≤ 8 * C_M * (P : ℝ) * (1 / (t - t') ^ 2) + E := h_term
    calc ‖η t‖ * ‖η t'‖ * ‖twistedSum ν (1 / 2) X₀ (t' - t)‖
        ≤ ‖η t‖ * ‖η t'‖ * (8 * C_M * (P : ℝ) * (1 / (t - t') ^ 2) + E) :=
          mul_le_mul_of_nonneg_left h_term' ht_nonneg
      _ = 8 * C_M * (P : ℝ) * (‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2)) + E * (‖η t‖ * ‖η t'‖) := by ring
  have h_sum_le1 : (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * ‖twistedSum ν (1 / 2) X₀ (t' - t)‖) ≤
      ∑ t ∈ S, ∑ t' ∈ S \ {t}, (8 * C_M * (P : ℝ) * (‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2)) + E * (‖η t‖ * ‖η t'‖)) :=
    Finset.sum_le_sum fun t ht => Finset.sum_le_sum fun t' ht' => h_prod_le t ht t' ht'
  have h_sum_split : (∑ t ∈ S, ∑ t' ∈ S \ {t}, (8 * C_M * (P : ℝ) * (‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2)) + E * (‖η t‖ * ‖η t'‖))) =
      8 * C_M * (P : ℝ) * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2)) +
        E * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖) := by
    have h_inner : ∀ t ∈ S,
        (∑ t' ∈ S \ {t}, (8 * C_M * (P : ℝ) * (‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2)) + E * (‖η t‖ * ‖η t'‖))) =
        (∑ t' ∈ S \ {t}, 8 * C_M * (P : ℝ) * (‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2))) +
        (∑ t' ∈ S \ {t}, E * (‖η t‖ * ‖η t'‖)) :=
      fun t _ => Finset.sum_add_distrib
    have h1 : (∑ t ∈ S, ∑ t' ∈ S \ {t}, (8 * C_M * (P : ℝ) * (‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2)) + E * (‖η t‖ * ‖η t'‖))) =
        (∑ t ∈ S, ∑ t' ∈ S \ {t}, 8 * C_M * (P : ℝ) * (‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2))) +
        (∑ t ∈ S, ∑ t' ∈ S \ {t}, E * (‖η t‖ * ‖η t'‖)) := by
      rw [Finset.sum_congr rfl h_inner, Finset.sum_add_distrib]
    rw [h1]
    congr 1
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.mul_sum]
  have hK_pos : 0 ≤ K := by linarith
  have hBK_pos : 0 ≤ B_K := by linarith
  have hE_pos : 0 ≤ E := by
    dsimp [E]
    have : 0 ≤ 9 + 8 * K * B_K ^ 2 := by positivity
    positivity
  have h_bound1 := sum_offdiag_sq_le S hS η
  have h_c1_nonneg : 0 ≤ 8 * C_M * (P : ℝ) := by positivity
  have h_term1_le : 8 * C_M * (P : ℝ) * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2)) ≤
      (32 * C_M * (P : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 := by
    calc 8 * C_M * (P : ℝ) * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2))
        ≤ 8 * C_M * (P : ℝ) * (4 * ∑ t ∈ S, ‖η t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h_bound1 h_c1_nonneg
      _ = (32 * C_M * (P : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 := by ring
  have h_bound2 := sum_prod_norm_le_card_mul_sum_sq S η
  have h_term2_le : E * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖) ≤
      (E * (S.card : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 := by
    calc E * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖)
        ≤ E * ((S.card : ℝ) * ∑ t ∈ S, ‖η t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h_bound2 hE_pos
      _ = (E * (S.card : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 := by ring
  have h_offdiag_le : (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * ‖twistedSum ν (1 / 2) X₀ (t' - t)‖) ≤
      (32 * C_M * (P : ℝ) + E * (S.card : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 := by
    calc (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * ‖twistedSum ν (1 / 2) X₀ (t' - t)‖)
        ≤ 8 * C_M * (P : ℝ) * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * (1 / (t - t') ^ 2)) +
            E * (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖) := by
          rw [← h_sum_split]
          exact h_sum_le1
      _ ≤ (32 * C_M * (P : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 + (E * (S.card : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 :=
          add_le_add h_term1_le h_term2_le
      _ = (32 * C_M * (P : ℝ) + E * (S.card : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 := by ring
  have h_total : 60 * (P : ℝ) * (∑ t ∈ S, ‖η t‖ ^ 2) + (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * ‖twistedSum ν (1 / 2) X₀ (t' - t)‖) ≤
      (60 * (P : ℝ) + 32 * C_M * (P : ℝ) + E * (S.card : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 := by
    calc 60 * (P : ℝ) * (∑ t ∈ S, ‖η t‖ ^ 2) + (∑ t ∈ S, ∑ t' ∈ S \ {t}, ‖η t‖ * ‖η t'‖ * ‖twistedSum ν (1 / 2) X₀ (t' - t)‖)
        ≤ 60 * (P : ℝ) * (∑ t ∈ S, ‖η t‖ ^ 2) + (32 * C_M * (P : ℝ) + E * (S.card : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 :=
          add_le_add (le_refl _) h_offdiag_le
      _ = (60 * (P : ℝ) + 32 * C_M * (P : ℝ) + E * (S.card : ℝ)) * ∑ t ∈ S, ‖η t‖ ^ 2 := by ring
  refine (add_le_add h_diag_le h_offdiag_re_le).trans (h_total.trans ?_)
  have h_sum_nonneg : 0 ≤ ∑ t ∈ S, ‖η t‖ ^ 2 := energy_nonneg S η
  refine mul_le_mul_of_nonneg_right ?_ h_sum_nonneg
  have hC1 : 60 + 32 * C_M ≤ C := by
    dsimp [C]
    have : 60 + 32 * C_M ≤ max (60 + 32 * C_M) (C_tw * (9 + 8 * K * B_K ^ 2)) := le_max_left _ _
    linarith
  have hC2 : C_tw * (9 + 8 * K * B_K ^ 2) ≤ C := by
    dsimp [C]
    have : C_tw * (9 + 8 * K * B_K ^ 2) ≤ max (60 + 32 * C_M) (C_tw * (9 + 8 * K * B_K ^ 2)) := le_max_right _ _
    linarith
  let F := (S.card : ℝ) * (P : ℝ) * Real.exp (-c * Real.log (P : ℝ) / (Real.log ((P : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P : ℝ) * T)) ^ 2
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_pos _).le) (sq_nonneg _)
  have hE_eq : E * (S.card : ℝ) = (C_tw * (9 + 8 * K * B_K ^ 2)) * F := by
    dsimp [E, F]; ring
  calc 60 * (P : ℝ) + 32 * C_M * (P : ℝ) + E * (S.card : ℝ)
      = (60 + 32 * C_M) * (P : ℝ) + (C_tw * (9 + 8 * K * B_K ^ 2)) * F := by
        rw [hE_eq]; ring
    _ ≤ C * (P : ℝ) + C * F :=
        add_le_add (mul_le_mul_of_nonneg_right hC1 (Nat.cast_nonneg P)) (mul_le_mul_of_nonneg_right hC2 hF_nonneg)
    _ = C * ((P : ℝ) + F) := by ring
    _ = D := rfl

