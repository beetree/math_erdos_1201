/-
Copyright (c) 2026 Przemek Chojecki, ChatGPT 5.5. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Przemek Chojecki, ChatGPT 5.5
-/
import Mathlib
import Erdos1201.MR.Setup
import Erdos1201.MR.Analysis.WellSpaced
import Erdos1201.MR.Analysis.HalaszMontgomery
import Erdos1201.MR.Arithmetic
import Erdos1201.MR.Prop1.E1

/-!
# Matomäki–Radziwiłł Proposition 1: Small Prime Polynomial Bound on Well-Spaced Points

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the $T_S$ part of the $U$-part bound (paper Section 8.3, display
"By Lemma 9"): on well-spaced heights $\mathcal{T}$ where the prime polynomial $Q_v$ is bounded
by $\varepsilon$, the sum of $|Q_v R_v|^2$ over $\mathcal{T}$ is bounded by
$C \varepsilon^2 \log T (1 + |\mathcal{T}| \sqrt{T} e^{v/H} / X)$.
-/

namespace Erdos1201.MR

/-- Rewriting a Dirichlet polynomial on a subset $S \subseteq (0, N]$ as a sum on $(0, N]$ with extended coefficients. -/
lemma dirichletPoly_subset_eq (a : ℕ → ℂ) (S : Finset ℕ) (N : ℕ) (hS : S ⊆ Finset.Ioc 0 N) (s : ℂ) :
    dirichletPoly a S s =
      dirichletPoly (fun n => if n ∈ S then a n else 0) (Finset.Ioc 0 N) s := by
  unfold dirichletPoly
  rw [← Finset.sum_subset hS]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [hn]
  · intro n _hn hnot
    simp [hnot]

/-- Rewriting the coefficient norm sum for a subset $S \subseteq (0, N]$ extended by zero. -/
lemma sum_norm_sq_div_sq_subset_eq (a : ℕ → ℂ) (S : Finset ℕ) (N : ℕ) (hS : S ⊆ Finset.Ioc 0 N) :
    (∑ n ∈ Finset.Ioc 0 N, ‖if n ∈ S then a n else 0‖ ^ 2 / (n : ℝ) ^ 2) =
      ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  rw [← Finset.sum_subset hS]
  · apply Finset.sum_congr rfl
    intro n hn
    simp [hn]
  · intro n _hn hnot
    simp [hnot]

/-- Bounding the sum of squared norms of products when one factor is uniformly bounded by $\varepsilon$. -/
lemma sum_norm_sq_mul_le (𝒯 : Finset ℝ) (Q R : ℝ → ℂ) (ε : ℝ)
    (hQ : ∀ t ∈ 𝒯, ‖Q t‖ ≤ ε) :
    (∑ t ∈ 𝒯, ‖Q t * R t‖ ^ 2) ≤ ε ^ 2 * ∑ t ∈ 𝒯, ‖R t‖ ^ 2 := by
  have h_term : ∀ t ∈ 𝒯, ‖Q t * R t‖ ^ 2 ≤ ε ^ 2 * ‖R t‖ ^ 2 := by
    intro t ht
    rw [norm_mul, mul_pow]
    have h1 : ‖Q t‖ ^ 2 ≤ ε ^ 2 := by
      have : 0 ≤ ‖Q t‖ := norm_nonneg _
      nlinarith [hQ t ht]
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have h_sum := Finset.sum_le_sum h_term
  rw [← Finset.mul_sum] at h_sum
  exact h_sum

/-- Inclusion of the cofactor range $(X e^{-v/H}, 2 X e^{-v/H}]$ into $(0, \lfloor 2 X e^{-v/H} \rfloor_+]$. -/
lemma cofactorRange_subset_Ioc (X : ℕ) (H : ℝ) (v : ℕ) :
    cofactorRange X H v ⊆ Finset.Ioc 0 ⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊ := by
  intro m hm
  unfold cofactorRange at hm
  exact (Finset.mem_filter.mp hm).1

/-- When the upper bound $\lfloor 2 X e^{-v/H} \rfloor_+$ vanishes, the cofactor range is empty. -/
lemma cofactorRange_eq_empty_of_floor_zero (X : ℕ) (H : ℝ) (v : ℕ)
    (hN : ⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊ = 0) :
    cofactorRange X H v = ∅ := by
  have hS_sub := cofactorRange_subset_Ioc X H v
  rw [hN, Finset.Ioc_self] at hS_sub
  exact Finset.subset_empty.mp hS_sub

/-- Algebraic reduction of the Halász–Montgomery factor $(N + |\mathcal{T}| \sqrt{T}) \cdot (2 e^{v/H} / X) \le 4 (1 + |\mathcal{T}| \sqrt{T} e^{v/H} / X)$. -/
lemma cofactor_halasz_factor_le (X : ℕ) (H : ℝ) (v : ℕ) (T : ℝ) (card_T : ℝ)
    (hX : 1 ≤ X) (hcard : 0 ≤ card_T) :
    let N : ℝ := (⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊ : ℝ)
    (N + card_T * Real.sqrt T) * (2 * Real.exp (v / H) / (X : ℝ)) ≤
      4 * (1 + card_T * Real.sqrt T * Real.exp (v / H) / (X : ℝ)) := by
  intro N
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
  have hN_le : N ≤ 2 * (X : ℝ) * Real.exp (-(v / H)) := Nat.floor_le (by positivity)
  have hexp_mul : Real.exp (-(v / H)) * Real.exp (v / H) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h_first : N * (2 * Real.exp (v / H) / (X : ℝ)) ≤ 4 := by
    have h_le := mul_le_mul_of_nonneg_right hN_le (by positivity : 0 ≤ 2 * Real.exp (v / H) / (X : ℝ))
    refine h_le.trans ?_
    have : 2 * (X : ℝ) * Real.exp (-(v / H)) * (2 * Real.exp (v / H) / (X : ℝ)) =
        4 * ((X : ℝ) / (X : ℝ)) * (Real.exp (-(v / H)) * Real.exp (v / H)) := by ring
    rw [this, div_self (ne_of_gt hX_pos), hexp_mul]
    ring_nf
    rfl
  have h_second : card_T * Real.sqrt T * (2 * Real.exp (v / H) / (X : ℝ)) =
      2 * (card_T * Real.sqrt T * Real.exp (v / H) / (X : ℝ)) := by ring
  have h_nonneg_Z : 0 ≤ card_T * Real.sqrt T * Real.exp (v / H) / (X : ℝ) := by positivity
  calc (N + card_T * Real.sqrt T) * (2 * Real.exp (v / H) / (X : ℝ))
    _ = N * (2 * Real.exp (v / H) / (X : ℝ)) + card_T * Real.sqrt T * (2 * Real.exp (v / H) / (X : ℝ)) := by ring
    _ ≤ 4 + 2 * (card_T * Real.sqrt T * Real.exp (v / H) / (X : ℝ)) := by linarith [h_first, h_second]
    _ ≤ 4 + 4 * (card_T * Real.sqrt T * Real.exp (v / H) / (X : ℝ)) := by linarith [h_nonneg_Z]
    _ = 4 * (1 + card_T * Real.sqrt T * Real.exp (v / H) / (X : ℝ)) := by ring

/-- The $T_S$ part of the $U$-part (paper Section 8.3, display "By Lemma 9"):
on well-spaced heights where the prime polynomial is tiny, the product $Q_v R_v$ is bounded. -/
theorem sum_small_prime_poly_mul_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℕ) (P Q : ℕ) (H : ℝ) (v : ℕ) (b c : ℕ → ℂ) (T ε : ℝ) (𝒯 : Finset ℝ),
      1 ≤ X → 1 ≤ H → 2 ≤ T → 0 ≤ ε → WellSpaced 𝒯 → (∀ t ∈ 𝒯, |t| ≤ T) → (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      (∀ t ∈ 𝒯, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ≤ ε) →
      (∑ t ∈ 𝒯, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C * ε ^ 2 * Real.log T * (1 + 𝒯.card * Real.sqrt T * Real.exp (v / H) / X) := by
  obtain ⟨C_H, hC_H_pos, h_halasz⟩ := sum_wellSpaced_norm_sq_le_halasz
  refine ⟨4 * C_H, by positivity, ?_⟩
  intro X P Q H v b c T ε 𝒯 hX hH hT hε h𝒯 h𝒯_le hb _hc hQ_le
  let Qv (t : ℝ) : ℂ := dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)
  let b_omega : ℕ → ℂ := fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
  let Rv (t : ℝ) : ℂ := dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)
  have h_sum_QR := sum_norm_sq_mul_le 𝒯 Qv Rv ε hQ_le
  set N := ⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊ with hN_def
  by_cases hN0 : N = 0
  · have hS_empty : cofactorRange X H v = ∅ := cofactorRange_eq_empty_of_floor_zero X H v hN0
    have hRv_zero (t : ℝ) : Rv t = 0 := by
      dsimp [Rv, dirichletPoly]
      rw [hS_empty, Finset.sum_empty]
    have h_lhs : (∑ t ∈ 𝒯, ‖Qv t * Rv t‖ ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [hRv_zero t, mul_zero, norm_zero, zero_pow (by norm_num)]
    rw [h_lhs]
    have hlogT : 0 ≤ Real.log T := by
      have : (1 : ℝ) ≤ T := by linarith
      exact Real.log_nonneg this
    have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
    have h_frac : 0 ≤ (𝒯.card : ℝ) * Real.sqrt T * Real.exp (v / H) / (X : ℝ) := by positivity
    have h_sum : 0 ≤ 1 + (𝒯.card : ℝ) * Real.sqrt T * Real.exp (v / H) / (X : ℝ) := by linarith
    have h_sq : 0 ≤ ε ^ 2 := sq_nonneg ε
    have hC_pos : 0 < 4 * C_H := by positivity
    positivity
  · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    let a : ℕ → ℂ := fun m => if m ∈ cofactorRange X H v then b_omega m else 0
    have hS_sub : cofactorRange X H v ⊆ Finset.Ioc 0 N := cofactorRange_subset_Ioc X H v
    have hRv_eq (t : ℝ) : Rv t = dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I) :=
      dirichletPoly_subset_eq b_omega (cofactorRange X H v) N hS_sub ((1 : ℂ) + t * Complex.I)
    have h_sum_Rv_eq : (∑ t ∈ 𝒯, ‖Rv t‖ ^ 2) =
        ∑ t ∈ 𝒯, ‖dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t _
      rw [hRv_eq t]
    have h_halasz_app := h_halasz a N T 𝒯 hN1 hT h𝒯 h𝒯_le
    rw [← h_sum_Rv_eq] at h_halasz_app
    have h_sum_sq_eq : (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2) =
        ∑ m ∈ cofactorRange X H v, ‖b_omega m‖ ^ 2 / (m : ℝ) ^ 2 :=
      sum_norm_sq_div_sq_subset_eq b_omega (cofactorRange X H v) N hS_sub
    rw [h_sum_sq_eq] at h_halasz_app
    have h_sum_b := sum_norm_sq_b_div_omega_le X H v P Q b hb hX
    have h_halasz_bound : (∑ t ∈ 𝒯, ‖Rv t‖ ^ 2) ≤
        C_H * (N + (𝒯.card : ℝ) * Real.sqrt T) * Real.log T * (2 * Real.exp (v / H) / (X : ℝ)) := by
      refine h_halasz_app.trans ?_
      have h_factor_nonneg : 0 ≤ C_H * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * Real.log T := by
        have : 0 < Real.log T := by
          have : (1 : ℝ) < T := by linarith
          exact Real.log_pos this
        positivity
      exact mul_le_mul_of_nonneg_left h_sum_b h_factor_nonneg
    have h_alg := cofactor_halasz_factor_le X H v T (𝒯.card : ℝ) hX (Nat.cast_nonneg _)
    have h_Rv_le_4 : (∑ t ∈ 𝒯, ‖Rv t‖ ^ 2) ≤
        (4 * C_H) * Real.log T * (1 + (𝒯.card : ℝ) * Real.sqrt T * Real.exp (v / H) / (X : ℝ)) := by
      refine h_halasz_bound.trans ?_
      have hlogT_nonneg : 0 ≤ Real.log T := by
        have : (1 : ℝ) ≤ T := by linarith
        exact Real.log_nonneg this
      have h_reorder : C_H * ((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * Real.log T * (2 * Real.exp (v / H) / (X : ℝ)) =
          C_H * Real.log T * (((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * (2 * Real.exp (v / H) / (X : ℝ))) := by ring
      rw [h_reorder]
      have h1 : C_H * Real.log T * (((N : ℝ) + (𝒯.card : ℝ) * Real.sqrt T) * (2 * Real.exp (v / H) / (X : ℝ))) ≤
          C_H * Real.log T * (4 * (1 + (𝒯.card : ℝ) * Real.sqrt T * Real.exp (v / H) / (X : ℝ))) :=
        mul_le_mul_of_nonneg_left h_alg (by positivity)
      refine h1.trans ?_
      have : C_H * Real.log T * (4 * (1 + (𝒯.card : ℝ) * Real.sqrt T * Real.exp (v / H) / (X : ℝ))) =
          (4 * C_H) * Real.log T * (1 + (𝒯.card : ℝ) * Real.sqrt T * Real.exp (v / H) / (X : ℝ)) := by ring
      rw [this]
    refine h_sum_QR.trans ?_
    have h_mul_eps := mul_le_mul_of_nonneg_left h_Rv_le_4 (sq_nonneg ε)
    refine h_mul_eps.trans ?_
    have : ε ^ 2 * ((4 * C_H) * Real.log T * (1 + (𝒯.card : ℝ) * Real.sqrt T * Real.exp (v / H) / (X : ℝ))) =
        (4 * C_H) * ε ^ 2 * Real.log T * (1 + (𝒯.card : ℝ) * Real.sqrt T * Real.exp (v / H) / (X : ℝ)) := by ring
    rw [this]

end Erdos1201.MR
