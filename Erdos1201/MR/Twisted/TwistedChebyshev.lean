/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gemini

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Erdos1201.Vendor.NumberTheory.PNT.MediumPNT

namespace Erdos1201.MR

open Complex Real MeasureTheory Set Filter Function

/-- Complex power of a positive natural with purely imaginary exponent has norm 1. -/
lemma norm_natCast_cpow_neg_mul_I (n : ℕ) (hn : 0 < n) (u : ℝ) :
    ‖(n : ℂ) ^ (-(u : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  have h_re : (-(u : ℂ) * Complex.I).re = 0 := by
    simp only [neg_mul, neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, neg_zero]
  rw [h_re, rpow_zero]

/-- Norm equality for twisted Dirichlet series terms with an extra factor. -/
lemma norm_twisted_term1 (m : ℕ) (hm : 0 < m) (u : ℝ) (y : ℝ) :
    ‖(ArithmeticFunction.vonMangoldt m : ℂ) * (m : ℂ) ^ (-(u : ℂ) * I) * (y : ℂ)‖ =
      ‖ArithmeticFunction.vonMangoldt m‖ * ‖y‖ := by
  simp only [norm_mul, norm_natCast_cpow_neg_mul_I m hm u, mul_one, Complex.norm_real]

/-- Norm equality for twisted Dirichlet series terms. -/
lemma norm_twisted_term2 (m : ℕ) (hm : 0 < m) (u : ℝ) :
    ‖(ArithmeticFunction.vonMangoldt m : ℂ) * (m : ℂ) ^ (-(u : ℂ) * I)‖ =
      ‖ArithmeticFunction.vonMangoldt m‖ := by
  simp only [norm_mul, norm_natCast_cpow_neg_mul_I m hm u, mul_one, Complex.norm_real]

/-- The nnnorm of the twisted Dirichlet term equals that of the untwisted term. -/
lemma twisted_term_nnnorm (n : ℕ) (u σ t : ℝ) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) / (n : ℂ) ^ ((σ : ℂ) + t * I)‖₊ =
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + t * I)‖₊ := by
  by_cases hn : n = 0
  · simp [hn]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
  simp only [nnnorm_div, nnnorm_mul]
  have h_twist : ‖(n : ℂ) ^ (-(u : ℂ) * I)‖₊ = 1 := by
    exact Subtype.ext (norm_natCast_cpow_neg_mul_I n hn_pos u)
  rw [h_twist, mul_one]

/-- Factorization of shifted Dirichlet series terms into a twist and a base term. -/
lemma term_twist_eq (n : ℕ) (σ t u : ℝ) :
    (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) ^ ((σ : ℂ) + ((t + u : ℝ) : ℂ) * I) =
    (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) / (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn_ne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h_exp : ((σ : ℂ) + ((t + u : ℝ) : ℂ) * I) = ((σ : ℂ) + (t : ℂ) * I) + (u : ℂ) * I := by
    push_cast; ring
  rw [h_exp, Complex.cpow_add _ _ hn_ne]
  rw [div_mul_eq_div_mul_one_div]
  rw [one_div, ← Complex.cpow_neg, neg_mul]
  ring

attribute [fun_prop] Continuous.const_cpow

set_option backward.isDefEq.respectTransparency false in
lemma twistedChebyshevDirichlet_aux_tsum_integral {SmoothingF : ℝ → ℝ}
    (diffSmoothingF : ContDiff ℝ 1 SmoothingF)
    (SmoothingFpos : ∀ x > 0, 0 ≤ SmoothingF x)
    (suppSmoothingF : support SmoothingF ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ (x : ℝ) in Ioi 0, SmoothingF x / x = 1) {X : ℝ}
    (X_pos : 0 < X) {ε : ℝ} (εpos : 0 < ε)
    (ε_lt_one : ε < 1) {σ : ℝ} (σ_gt : 1 < σ) (σ_le : σ ≤ 2) (u : ℝ) :
    ∫ (t : ℝ),
      ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) / (n : ℂ) ^ (σ + t * I) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + t * I) * (X : ℂ) ^ (σ + t * I) =
    ∑' (n : ℕ),
      ∫ (t : ℝ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) / (n : ℂ) ^ (σ + ↑t * I) *
        mellin (fun x ↦ ↑(Smooth1 SmoothingF ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + t * I) := by
  have cont_mellin_smooth : Continuous fun (a : ℝ) ↦
      mellin (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) (σ + ↑a * I) := by
    rw [← continuousOn_univ]
    refine ContinuousOn.comp' ?_ ?_ ?_ (t := {z : ℂ | 0 < z.re })
    · refine continuousOn_of_forall_continuousAt ?_
      intro z hz
      exact (Smooth1MellinDifferentiable diffSmoothingF suppSmoothingF ⟨εpos, ε_lt_one⟩
        SmoothingFpos mass_one hz).continuousAt
    · fun_prop
    · simp only [mapsTo_univ_iff, mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero,
        ofReal_im, I_im, mul_one, sub_self, add_zero, forall_const]; linarith

  have abs_two : ∀ a : ℝ, ∀ i : ℕ, ‖(i : ℂ) ^ ((σ : ℂ) + ↑a * I)‖₊ = i ^ σ := by
    intro a i
    simp_rw [← norm_toNNReal]
    rw [norm_natCast_cpow_of_re_ne_zero _ (by simp only [add_re, ofReal_re, mul_re, I_re, mul_zero,
      ofReal_im, I_im, mul_one, sub_self, add_zero, ne_eq]; linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, Real.toNNReal_of_nonneg <| rpow_nonneg (y := σ) (x := i) (by linarith)]
    norm_cast

  rw [MeasureTheory.integral_tsum]
  · have x_neq_zero : X ≠ 0 := by linarith
    intro i
    by_cases i_eq_zero : i = 0
    · simpa [i_eq_zero] using aestronglyMeasurable_const
    · apply Continuous.aestronglyMeasurable
      fun_prop (disch := simp [i_eq_zero, x_neq_zero])
  · rw [← lt_top_iff_ne_top]
    simp_rw [enorm_mul, enorm_eq_nnnorm, twisted_term_nnnorm, nnnorm_div, ← norm_toNNReal,
      Complex.norm_cpow_eq_rpow_re_of_pos X_pos, norm_toNNReal, abs_two]
    simp only [nnnorm_real, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]
    simp_rw [MeasureTheory.lintegral_mul_const' (r := ↑(X ^ σ).toNNReal) (hr := by simp),
      ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top ?_ ENNReal.coe_lt_top

    conv =>
      arg 1
      arg 1
      intro i
      rw [MeasureTheory.lintegral_const_mul' (hr := by simp)]

    rw [ENNReal.tsum_mul_right]
    apply WithTop.mul_lt_top
    · rw [WithTop.lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
      push_cast
      convert (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := σ)
        (by simp only [ofReal_re]; linarith)).norm
      rw [LSeries.term_def]
      split_ifs with h <;> simp [h]
    · simp_rw [← enorm_eq_nnnorm]
      rw [← MeasureTheory.hasFiniteIntegral_iff_enorm]
      exact SmoothedChebyshevDirichlet_aux_integrable diffSmoothingF SmoothingFpos suppSmoothingF
            mass_one εpos ε_lt_one σ_gt σ_le |>.hasFiniteIntegral

/-- The twisted Chebyshev integrand. -/
noncomputable def twistedIntegrand (ν : ℝ → ℝ) (ε X u : ℝ) : ℂ → ℂ :=
  fun s => (- deriv riemannZeta s) / riemannZeta s * mellin (fun x => (Smooth1 ν ε x : ℂ)) (s - u * Complex.I) * (X : ℂ) ^ (s - u * Complex.I)

/-- The twisted smoothed Chebyshev function defined as a vertical line integral. -/
noncomputable def twistedChebyshev (ν : ℝ → ℝ) (ε X u : ℝ) : ℂ :=
  VerticalIntegral' (twistedIntegrand ν ε X u) (1 + (Real.log X)⁻¹)

/-- The twisted smoothed sum over von Mangoldt weighted prime powers. -/
noncomputable def twistedSum (ν : ℝ → ℝ) (ε X u : ℝ) : ℂ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I) * (Smooth1 ν ε (n / X) : ℂ)

local notation "Λ" => ArithmeticFunction.vonMangoldt

set_option backward.isDefEq.respectTransparency false in
theorem twistedChebyshev_eq_twistedSum (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν) (νnonneg : ∀ x > 0, 0 ≤ ν x) (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (mass_one : ∫ x in Set.Ioi (0 : ℝ), ν x / x = 1) {X : ℝ} (X_gt : 3 < X) {ε : ℝ} (εpos : 0 < ε) (ε_lt_one : ε < 1) (u : ℝ) :
    twistedChebyshev ν ε X u = twistedSum ν ε X u := by
  dsimp [twistedChebyshev, twistedIntegrand, VerticalIntegral', VerticalIntegral]
  set σ : ℝ := 1 + (Real.log X)⁻¹
  have log_gt : 1 < Real.log X := logt_gt_one X_gt.le
  have σ_gt : 1 < σ := by
    simp only [σ]
    have : 0 < (Real.log X)⁻¹ := by
      simp only [inv_pos]
      linarith
    linarith
  have σ_le : σ ≤ 2 := by
    simp only [σ]
    have : (Real.log X)⁻¹ < 1 := inv_lt_one_of_one_lt₀ log_gt
    linarith
  have shift_int : (∫ (t : ℝ), (-deriv riemannZeta (σ + ↑t * I)) / riemannZeta (σ + ↑t * I) *
        mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I - ↑u * I) * (X : ℂ) ^ (σ + ↑t * I - ↑u * I)) =
      ∫ (t : ℝ), (-deriv riemannZeta (σ + ↑(t + u) * I)) / riemannZeta (σ + ↑(t + u) * I) *
        mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) * (X : ℂ) ^ (σ + ↑t * I) := by
    rw [← integral_add_right_eq_self (fun (t : ℝ) ↦ (-deriv riemannZeta (σ + ↑t * I)) / riemannZeta (σ + ↑t * I) *
        mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I - ↑u * I) * (X : ℂ) ^ (σ + ↑t * I - ↑u * I)) u]
    congr 1
    ext t
    have h_shift : (σ : ℂ) + ((t + u : ℝ) : ℂ) * I - (u : ℂ) * I = (σ : ℂ) + (t : ℂ) * I := by
      push_cast; ring
    rw [h_shift]
  rw [shift_int]
  calc
    _ = 1 / (2 * π * I) * (I * ∫ (t : ℝ), ∑' n, (Λ n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, ∫ (t : ℝ), (Λ n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) / (n : ℂ) ^ (σ + ↑t * I) *
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) * X ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π * I) * (I * ∑' n, (Λ n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = 1 / (2 * π) * (∑' n, (Λ n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, (Λ n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        (X / (n : ℂ)) ^ (σ + ↑t * I)) := ?_
    _ = ∑' n, (Λ n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) * (1 / (2 * π) * ∫ (t : ℝ),
      mellin (fun x ↦ ↑(Smooth1 ν ε x)) (σ + ↑t * I) *
        ((n : ℂ) / X) ^ (-(σ + ↑t * I))) := ?_
    _ = _ := ?_
  · congr; ext t
    have hre : 1 < (σ + ↑(t + u) * I).re := by
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
      exact σ_gt
    rw [LogDerivativeDirichlet _ hre]
    rw [← tsum_mul_right, ← tsum_mul_right]
    congr 1; ext n
    rw [term_twist_eq]
  · congr
    exact twistedChebyshevDirichlet_aux_tsum_integral diffν νnonneg suppν mass_one
      (X := X) (by linarith) εpos ε_lt_one σ_gt σ_le u
  · field_simp; congr 1; ext n; rw [← MeasureTheory.integral_const_mul]; congr 1; ext t
    by_cases n_ne_zero : n = 0
    · simp [n_ne_zero]
    rw [mul_div_assoc, mul_assoc]
    congr 1
    rw [(div_eq_iff ?_).mpr]
    · have := @mul_cpow_ofReal_nonneg (a := X / (n : ℝ)) (b := (n : ℝ)) (r := σ + I * t) ?_ ?_
      · push_cast at this ⊢
        rw [← this, div_mul_cancel₀]
        · simp only [ne_eq, Nat.cast_eq_zero, n_ne_zero, not_false_eq_true]
      · apply div_nonneg (by linarith : 0 ≤ X); simp
      · simp
    · simp only [ne_eq, cpow_eq_zero_iff, Nat.cast_eq_zero, n_ne_zero, false_and,
        not_false_eq_true]
  · conv => rw [← mul_assoc, div_mul]; lhs; lhs; rhs; simp
  · rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  · have ht (t : ℝ) : -(σ + t * I) = (-1) * (σ + t * I) := by simp
    have hn (n : ℂ) : (n / X) ^ (-1 : ℂ) = X / n := by simp [cpow_neg_one]
    have (n : ℕ) : (log ((n : ℂ) / (X : ℂ)) * -1).im = 0 := by
      simp [Complex.log_im, arg_eq_zero_iff, div_nonneg (Nat.cast_nonneg _) (by linarith : 0 ≤ X)]
    have h (n : ℕ) (t : ℝ) : ((n : ℂ) / X) ^ ((-1 : ℂ) * (σ + t * I)) =
        ((n / X) ^ (-1 : ℂ)) ^ (σ + ↑t * I) := by
      rw [cpow_mul] <;> {rw [this n]; simp [Real.pi_pos, Real.pi_nonneg]}
    conv => rhs; lhs; intro n; rhs; rhs; rhs; intro t; rhs; rw [ht t, h n t]; lhs; rw [hn]
  · congr 1
    ext n
    by_cases n_zero : n = 0
    · simp [n_zero]
    have n_pos : 0 < n := by
      simpa only [n_zero, gt_iff_lt, false_or] using (Nat.eq_zero_or_pos n)
    congr 1
    have := mellinInv_mellin_eq σ (f := fun x ↦ (Smooth1 ν ε x : ℂ)) (x := n / X)
      ?_ ?_ ?_ ?_
    · beta_reduce at this
      dsimp [mellinInv, VerticalIntegral] at this
      convert! this using 4
      · norm_cast
      · rw [mul_comm]
        norm_cast
    · exact div_pos (by exact_mod_cast n_pos) (by linarith : 0 < X)
    · apply Smooth1MellinConvergent diffν suppν ⟨εpos, ε_lt_one⟩ νnonneg mass_one
      simp only [ofReal_re]
      linarith
    · dsimp [VerticalIntegrable]
      apply SmoothedChebyshevDirichlet_aux_integrable diffν νnonneg suppν mass_one εpos ε_lt_one σ_gt σ_le
    · refine ContinuousAt.comp (g := ofReal) RCLike.continuous_ofReal.continuousAt ?_
      exact Smooth1ContinuousAt diffν νnonneg suppν εpos (by positivity)

/-- Reindexing a finite sum starting from 1 to 0 when the zero term vanishes. -/
lemma sum_Icc_one_eq_zero (f : ℕ → ℂ) (hf0 : f 0 = 0) (k : ℕ) :
    (∑ n ∈ Finset.Icc 1 k, f n) = ∑ n ∈ Finset.Icc 0 k, f n := by
  by_cases hk : k = 0
  · simp [hk, hf0]
  have h_insert : Finset.Icc 0 k = insert 0 (Finset.Icc 1 k) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [h_insert, Finset.sum_insert]
  · rw [hf0, zero_add]
  · simp only [Finset.mem_Icc, nonpos_iff_eq_zero, one_ne_zero, false_and, not_false_eq_true]

/-- Splitting a finite sum into a head part and an intermediate block. -/
lemma sum_Icc_twisted_split (f : ℕ → ℂ) (hf0 : f 0 = 0) (n₀ : ℕ) {X : ℝ} (X_pos : 0 < X)
    (hn₀ : n₀ ≤ ⌊X + 1⌋₊) :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n) =
      (∑ x ∈ Finset.range n₀, f x) +
      ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), f (x + n₀) := by
  rw [sum_Icc_one_eq_zero f hf0]
  have h_floor : ⌊X⌋₊ + 1 = ⌊X + 1⌋₊ := (Nat.floor_add_one X_pos.le).symm
  rw [← Nat.range_succ_eq_Icc_zero, h_floor]
  nth_rw 1 [show ⌊X + 1⌋₊ = n₀ + (⌊X + 1⌋₊ - n₀) by omega]
  rw [Finset.sum_range_add]
  simp only [add_comm n₀]

/-- Splitting a shifted infinite series into a finite range and a remainder. -/
lemma tsum_split_interval (f : ℕ → ℂ) (hf : Summable f) (n₀ n₁ : ℕ) (h : n₀ ≤ n₁) :
    (∑' n, f (n + n₀)) = (∑ n ∈ Finset.range (n₁ - n₀), f (n + n₀)) + ∑' n, f (n + n₁) := by
  have h_shift (k : ℕ) : Summable (fun n ↦ f (n + k)) := hf.comp_injective (add_left_injective k)
  have h_eq : (∑' n, (fun n ↦ f (n + n₀)) n) =
      (∑ n ∈ Finset.range (n₁ - n₀), f (n + n₀)) + ∑' n, f (n + n₁) := by
    rw [← Summable.sum_add_tsum_nat_add' (k := n₁ - n₀)]
    · congr 1
      apply tsum_congr
      intro n
      congr 1
      omega
    · have : (fun n => f (n + (n₁ - n₀) + n₀)) = (fun n => f (n + n₁)) := by
        ext n; congr 1; omega
      rw [this]
      exact h_shift n₁
  exact h_eq

/-- Splitting an infinite series into a head finite sum and a tail series. -/
lemma tsum_split_head (f : ℕ → ℂ) (hf : Summable f) (n₀ : ℕ) :
    (∑' n, f n) = (∑ n ∈ Finset.range n₀, f n) + ∑' n, f (n + n₀) := by
  have h := tsum_split_interval f hf 0 n₀ (Nat.zero_le n₀)
  simpa using h

/-- Evaluating a tail series when all terms past index n₁ vanish. -/
lemma tsum_split_tail (f : ℕ → ℂ) (hf : Summable f) (n₁ : ℕ)
    (h_zero : ∀ n, f (n + 1 + n₁) = 0) :
    (∑' n, f (n + n₁)) = f n₁ := by
  have h_shift : Summable (fun n ↦ f (n + n₁)) := hf.comp_injective (add_left_injective n₁)
  rw [Summable.tsum_eq_zero_add h_shift]
  have : (fun n => f (n + 1 + n₁)) = (fun _ => 0) := by
    ext n; exact h_zero n
  rw [this, tsum_zero, add_zero, zero_add]

/-- Three-part decomposition of a compactly supported infinite series. -/
lemma tsum_split_three (f : ℕ → ℂ) (hf : Summable f) (n₀ n₁ : ℕ) (hn : n₀ ≤ n₁)
    (h_zero : ∀ n, f (n + 1 + n₁) = 0) :
    (∑' n, f n) = (∑ n ∈ Finset.range n₀, f n) + (∑ n ∈ Finset.range (n₁ - n₀), f (n + n₀)) + f n₁ := by
  rw [tsum_split_head f hf n₀]
  rw [tsum_split_interval f hf n₀ n₁ hn]
  rw [tsum_split_tail f hf n₁ h_zero]
  ring

/-- Auxiliary estimate bounding the difference between the twisted sum and the truncated finite sum. -/
theorem twistedSum_close_aux (SmoothingF : ℝ → ℝ)
    (c₁ : ℝ) (c₁_pos : 0 < c₁) (c₁_lt : c₁ < 1)
    (c₂ : ℝ) (c₂_pos : 0 < c₂) (c₂_lt : c₂ < 2)
    (hc₂ : ∀ (ε x : ℝ), ε ∈ Ioo 0 1 → 1 + c₂ * ε ≤ x → Smooth1 SmoothingF ε x = 0)
    (C : ℝ) (C_eq : C = 6 * (3 * c₁ + c₂))
    (ε : ℝ) (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    (X : ℝ) (X_pos : 0 < X) (X_gt_three : 3 < X)
    (X_bound_1 : 1 ≤ X * ε * c₁) (X_bound_2 : 1 ≤ X * ε * c₂)
    (smooth1BddAbove : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≤ 1)
    (smooth1BddBelow : ∀ (n : ℕ), 0 < n → Smooth1 SmoothingF ε (↑n / X) ≥ 0)
    (smoothIs1 : ∀ (n : ℕ), 0 < n → ↑n ≤ X * (1 - c₁ * ε) →
      Smooth1 SmoothingF ε (↑n / X) = 1)
    (smoothIs0 : ∀ (n : ℕ), 1 + c₂ * ε ≤ ↑n / X → Smooth1 SmoothingF ε (↑n / X) = 0)
    (u : ℝ) :
  ‖twistedSum SmoothingF ε X u -
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)‖ ≤
    C * ε * X * Real.log X := by

  let n₀ := ⌈X * (1 - c₁ * ε)⌉₊

  have n₀_pos : 0 < n₀ := by
    simp only [Nat.ceil_pos, n₀]
    subst C_eq
    simp_all only [mem_Ioo, and_imp, ge_iff_le, implies_true, mul_pos_iff_of_pos_left, sub_pos]
    exact mul_lt_one_of_nonneg_of_lt_one_left c₁_pos.le c₁_lt ε_lt_one.le

  have n₀_inside_le_X : X * (1 - c₁ * ε) ≤ X := by
    nth_rewrite 2 [← mul_one X]
    apply mul_le_mul_of_nonneg_left _ X_pos.le
    apply sub_le_self
    positivity

  have n₀_le : n₀ ≤ X * ((1 - c₁ * ε)) + 1 := by
    simp only [n₀]
    exact le_of_lt (Nat.ceil_lt_add_one (by bound))

  have n₀_gt : X * ((1 - c₁ * ε)) ≤ n₀ := by
    simp only [n₀]
    exact Nat.le_ceil (X * (1 - c₁ * ε))

  let n₁ := ⌊X * (1 + c₂ * ε)⌋₊

  have n₁_pos : 0 < n₁ := by
    dsimp only [n₁]
    apply Nat.le_floor
    rw [Nat.succ_eq_add_one, zero_add]
    norm_cast
    apply one_le_mul_of_one_le_of_one_le (by linarith)
    apply le_add_of_nonneg_right
    positivity

  have le_n₁ : X * (1 + c₂ * ε) - 1 ≤ n₁ := by
    simp only [tsub_le_iff_right, n₁]
    exact le_of_lt (Nat.lt_floor_add_one (X * (1 + c₂ * ε)))

  have n₁_le : (n₁ : ℝ) ≤ X * (1 + c₂ * ε) := by
    simp only [n₁]
    exact Nat.floor_le (by bound)

  have n₀_le_n₁ : n₀ ≤ n₁ := by
    exact_mod_cast le_imp_le_of_le_of_le n₀_le le_n₁ (by linarith)

  have n₁_sub_n₀ : (n₁ : ℝ) - n₀ ≤ X * ε * (c₂ + c₁) := by
    calc
      (n₁ : ℝ) - n₀ ≤ X * (1 + c₂ * ε) - n₀ := by
                        exact sub_le_sub_right n₁_le ↑n₀
       _            ≤ X * (1 + c₂ * ε) - (X * (1 - c₁ * ε)) := by
          exact tsub_le_tsub_left n₀_gt (X * (1 + c₂ * ε))
       _            = X * ε * (c₂ + c₁) := by ring

  set f : ℕ → ℂ := fun n ↦ (Λ n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I) * (Smooth1 SmoothingF ε (n / X) : ℂ)
  set g : ℕ → ℂ := fun n ↦ (Λ n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * I)

  have sumΛ : Summable f := by
    apply summable_of_ne_finset_zero (s := Finset.range ⌈(1 + c₂ * ε) * X⌉₊)
    intro a ha
    have : 1 + c₂ * ε ≤ a / X := (le_div_iff₀ X_pos).mpr (Nat.ceil_le.mp (not_lt.mp (Finset.mem_range.not.mp ha)))
    have hF : Smooth1 SmoothingF ε (a / X) = 0 := hc₂ ε (a / X) ⟨ε_pos, ε_lt_one⟩ this
    dsimp [f]
    rw [hF, Complex.ofReal_zero, mul_zero]

  have h_tail_zero : ∀ n, f (n + 1 + n₁) = 0 := by
    intro n
    dsimp [f]
    have hF0 : Smooth1 SmoothingF ε ((n + 1 + n₁ : ℕ) / X) = 0 := by
      apply smoothIs0 (n + 1 + n₁)
      rw [le_div_iff₀ X_pos]
      push_cast
      linarith
    rw [hF0, Complex.ofReal_zero, mul_zero]

  have h_tsum_split := tsum_split_three f sumΛ n₀ n₁ n₀_le_n₁ h_tail_zero

  have X_le_floor_add_one : X ≤ ↑⌊X + 1⌋₊ := by
    rw [Nat.floor_add_one (by linarith), Nat.cast_add, Nat.cast_one]
    apply le_trans <| Nat.le_ceil X
    exact_mod_cast Nat.ceil_le_floor_add_one X

  have floor_X_add_one_le_self : ↑⌊X + 1⌋₊ ≤ X + 1 := Nat.floor_le (by positivity)

  have hn₀_le_floor : n₀ ≤ ⌊X + 1⌋₊ := by
    dsimp only [n₀]
    exact Nat.ceil_le.mpr (by linarith)

  have h_sum_split := sum_Icc_twisted_split g (by simp [g]) n₀ X_pos hn₀_le_floor

  have h_cancel : (∑ n ∈ Finset.range n₀, f n) = ∑ n ∈ Finset.range n₀, g n := by
    apply Finset.sum_congr rfl
    intro n hn
    obtain rfl | n_zero := eq_or_ne n 0
    · simp [f, g]
    · have hF1 : Smooth1 SmoothingF ε (n / X) = 1 := by
        apply smoothIs1 n (Nat.zero_lt_of_ne_zero n_zero)
        simp only [Finset.mem_range, n₀] at hn
        exact Nat.lt_ceil.mp hn |>.le
      dsimp [f, g]
      rw [hF1, Complex.ofReal_one, mul_one]

  have vonBnd1 :
    ∀ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ ≤ Real.log (X * (1 + c₂ * ε)) := by
    intro n hn
    have n_add_n0_le_n1: ((n + n₀ : ℕ) : ℝ) ≤ n₁ := by
      rw [Finset.mem_range] at hn
      exact_mod_cast (by omega : n + n₀ ≤ n₁)
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑(n + n₀)) := by
      rw [Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      apply ArithmeticFunction.vonMangoldt_le_log
    have inter2: Real.log (↑(n + n₀)) ≤ Real.log (↑n₁) := by
      have : 0 < ((n + n₀ : ℕ) : ℝ) := by positivity
      exact Real.log_le_log this n_add_n0_le_n1
    have inter3: Real.log (↑n₁) ≤ Real.log (X * (1 + c₂ * ε)) := by
      have : 0 < (n₁ : ℝ) := by positivity
      exact Real.log_le_log this n₁_le
    exact le_trans inter1 (le_trans inter2 inter3)

  have bnd1 :
    ∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖Smooth1 SmoothingF ε (↑(n + n₀) / X)‖
    ≤ (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) := by
    have : (n₁ - n₀) * Real.log (X * (1 + c₂ * ε)) =
        (∑ n ∈ Finset.range (n₁ - n₀), Real.log (X * (1 + c₂ * ε))) := by
      rw [← Nat.cast_sub]
      · nth_rewrite 1 [← Finset.card_range (n₁ - n₀)]
        rw [Finset.cast_card, Finset.sum_const, smul_one_mul]
        exact Eq.symm (Finset.sum_const (Real.log (X * (1 + c₂ * ε))))
      exact n₀_le_n₁
    rw [this]
    apply Finset.sum_le_sum
    intro n hn
    rw [← mul_one (Real.log (X * (1 + c₂ * ε)))]
    apply mul_le_mul (vonBnd1 _ hn) _ (norm_nonneg _) (log_nonneg (by bound))
    rw [Real.norm_of_nonneg]
    · apply smooth1BddAbove _ (by omega)
    apply smooth1BddBelow _ (by omega)

  have bnd2 :
    ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ ≤ (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) := by
    have : (⌊X + 1⌋₊ - n₀) * Real.log (X + 1) =
        (∑ n ∈ Finset.range (⌊X + 1⌋₊ - n₀), Real.log (X + 1)) := by
      rw [← Nat.cast_sub]
      · nth_rewrite 1 [← Finset.card_range (⌊X + 1⌋₊ - n₀)]
        rw [Finset.cast_card, Finset.sum_const, smul_one_mul]
        exact Eq.symm (Finset.sum_const (Real.log (X + 1)))
      simp only [Nat.ceil_le, n₀]
      exact Preorder.le_trans (X * (1 - c₁ * ε)) X (↑⌊X + 1⌋₊) n₀_inside_le_X
        X_le_floor_add_one
    rw [this]
    apply Finset.sum_le_sum
    intro n hn
    have n_add_n0_le_X_add_one: (n : ℝ) + n₀ ≤ X + 1 := by
      rw [Finset.mem_range] at hn
      rw [← add_le_add_iff_right (-↑n₀), add_assoc, ← sub_eq_add_neg, sub_self, add_zero,
        ← sub_eq_add_neg]
      have temp: (n : ℝ) < ⌊X + 1⌋₊ - n₀ := by
        rw [← Nat.cast_sub, Nat.cast_lt]
        · exact hn
        simp only [Nat.ceil_le, n₀]
        exact le_trans n₀_inside_le_X X_le_floor_add_one
      have : ↑⌊X + 1⌋₊ - ↑n₀ ≤ X + 1 - ↑n₀ := by
        apply sub_le_sub_right floor_X_add_one_le_self
      exact le_of_lt (lt_of_le_of_lt' this temp)
    have inter1: ‖ Λ (n + n₀)‖ ≤ Real.log (↑n + ↑n₀) := by
      rw [Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, ← Nat.cast_add]
      apply ArithmeticFunction.vonMangoldt_le_log
    apply le_trans inter1
    exact_mod_cast Real.log_le_log (by positivity) (n_add_n0_le_X_add_one)

  clear vonBnd1

  have inter1 : Real.log (X * (1 + c₂ * ε)) ≤ Real.log (3 * X) := by
    apply Real.log_le_log (by positivity)
    have const_le_2: 1 + c₂ * ε ≤ 3 := by
      have : (3 : ℝ) = 1 + 2 := by ring
      rw [this]
      apply add_le_add_right
      rw [← mul_one 2]
      exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    rw [mul_comm]
    exact mul_le_mul const_le_2 (by rfl) (by positivity) (by positivity)

  change ‖(∑' n, f n) - (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, g n)‖ ≤ _
  rw [h_tsum_split, h_sum_split]
  calc
    _ = ‖∑ n ∈ Finset.range (n₁ - n₀), f (n + n₀) -
          ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), g (x + n₀) +
          f n₁‖ := by
      rw [h_cancel]
      congr 1
      ring
    _ ≤ (∑ n ∈ Finset.range (n₁ - n₀), ‖f (n + n₀)‖) +
        ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖g (x + n₀)‖ +
        ‖f n₁‖ := by
      apply norm_add_le_of_le
      · apply norm_sub_le_of_le
        · apply norm_sum_le_of_le
          intro b hb; rfl
        · apply norm_sum_le_of_le
          intro b hb; rfl
      · rfl
    _ = (∑ n ∈ Finset.range (n₁ - n₀), ‖Λ (n + n₀)‖ * ‖Smooth1 SmoothingF ε (↑(n + n₀) / X)‖) +
        ∑ x ∈ Finset.range (⌊X + 1⌋₊ - n₀), ‖Λ (x + n₀)‖ +
        ‖Λ n₁‖ * ‖Smooth1 SmoothingF ε (↑n₁ / X)‖ := by
      congr 1
      · congr 1
        · apply Finset.sum_congr rfl
          intro n hn
          dsimp [f]
          apply norm_twisted_term1
          omega
        · apply Finset.sum_congr rfl
          intro x hx
          dsimp [g]
          apply norm_twisted_term2
          omega
      · dsimp [f]
        apply norm_twisted_term1
        exact n₁_pos
    _ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * Real.log X + Real.log (3 * X) := by
      apply add_le_add
      · apply le_trans <| add_le_add bnd1 bnd2
        rw [(by ring : 2 * (X * ε * (3 * c₁ + c₂)) = 2 * (X * ε * (c₁ + c₂)) + 4 * (X * ε * c₁)), add_mul]
        apply add_le_add
        · calc
            _ ≤ (X * ε * (c₂ + c₁)) * (Real.log (X) + Real.log (3)) := by
              apply mul_le_mul n₁_sub_n₀ _ (log_nonneg (by linarith)) (by positivity)
              rw [← Real.log_mul (by positivity) (by positivity)]
              nth_rewrite 3 [mul_comm]
              exact inter1
            _ ≤ 2 * ((X * ε * (c₂ + c₁)) * Real.log X) := by
              rw [two_mul, mul_add]
              bound
            _ = _ := by ring
        calc
          _ ≤ 2 * (X * ε * c₁) * (Real.log (X) + Real.log (3)) := by
            apply mul_le_mul _ _ (log_nonneg (by linarith)) (by positivity)
            · rw [(by ring : 2 * (X * ε * c₁) = (X * (1 + ε * c₁)) - (X * (1 - ε * c₁)))]
              apply sub_le_sub
              · apply le_trans floor_X_add_one_le_self
                ring_nf
                rw [add_comm, add_le_add_iff_left]
                exact X_bound_1
              nth_rewrite 2 [mul_comm]
              exact n₀_gt
            rw [← Real.log_mul (by positivity) (by norm_num), mul_comm]
            exact Real.log_le_log (by positivity) (by linarith)
          _ = 2 * (X * ε * c₁ * Real.log X) + 2 * (X * ε * c₁ * Real.log 3) := by ring
          _ ≤ 2 * (X * ε * c₁ * Real.log X) + 2 * (X * ε * c₁ * Real.log X) := by gcongr
          _ = _ := by ring
      · apply le_trans _ inter1
        rw [← mul_one (Real.log (X * (1 + c₂ * ε)))]
        apply mul_le_mul _ _ (norm_nonneg _) (log_nonneg (by bound))
        · rw [Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          exact le_trans ArithmeticFunction.vonMangoldt_le_log <|
            Real.log_le_log (mod_cast n₁_pos) n₁_le
        rw [Real.norm_of_nonneg <| smooth1BddBelow _ n₁_pos]
        apply smooth1BddAbove _ n₁_pos
    _ ≤ 2 * (X * ε * (3 * c₁ + c₂)) * (Real.log X + (Real.log X + Real.log 3)) := by
      rw [← Real.log_mul (by positivity) (by positivity), mul_comm X 3]
      nth_rewrite 2 [mul_add]
      apply add_le_add_right
      nth_rewrite 1 [← one_mul (Real.log (3 * X))]
      apply mul_le_mul_of_nonneg_right _ (log_nonneg (by linarith))
      linarith
    _ = 4 * (X * ε * (3 * c₁ + c₂)) * Real.log X +
          2 * (X * ε * (3 * c₁ + c₂)) * Real.log 3 := by ring
    _ ≤ 4 * (X * ε * (3 * c₁ + c₂)) * Real.log X +
          2 * (X * ε * (3 * c₁ + c₂)) * Real.log X := by gcongr
    _ = _ := by
      rw [C_eq]
      ring

/-- Closeness estimate between the twisted sum and the truncated finite sum. -/
theorem twistedSum_close (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν) (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x) (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    ∃ C > 0, ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (_ : 2 < X * ε) (u : ℝ),
      ‖twistedSum ν ε X u - ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(u : ℂ) * Complex.I)‖ ≤ C * ε * X * Real.log X := by
  have _ := diffν
  obtain ⟨c₁, c₁_pos, c₁_eq, hc₁⟩ := Smooth1Properties_below suppν mass_one
  obtain ⟨c₂, c₂_pos, c₂_eq, hc₂⟩ := Smooth1Properties_above suppν

  have c₁_lt : c₁ < 1 := by
    rw [c₁_eq]
    exact lt_trans (Real.log_two_lt_d9) (by norm_num)

  have c₂_lt : c₂ < 2 := by
    rw [c₂_eq]
    nth_rewrite 3 [← mul_one 2]
    apply mul_lt_mul'
    · rfl
    · exact lt_trans (Real.log_two_lt_d9) (by norm_num)
    · exact Real.log_nonneg (by norm_num)
    · positivity

  let C : ℝ := 6 * (3 * c₁ + c₂)
  have C_eq : C = 6 * (3 * c₁ + c₂) := rfl
  clear_value C

  have Cpos : 0 < C := by
    rw [C_eq]
    positivity

  refine ⟨C, Cpos, fun X X_gt_three ε εpos ε_lt_one X_bound u ↦ ?_⟩

  have X_pos : 0 < X := by linarith

  have n_on_X_pos {n : ℕ} (npos : 0 < n) : 0 < (n : ℝ) / X := by
    have : (0 : ℝ) < n := by exact_mod_cast npos
    positivity

  have smooth1BddAbove (n : ℕ) (npos : 0 < n) :
      Smooth1 ν ε (n / X) ≤ 1 :=
    Smooth1LeOne νnonneg mass_one εpos (n_on_X_pos npos)

  have smooth1BddBelow (n : ℕ) (npos : 0 < n) :
      Smooth1 ν ε (n / X) ≥ 0 :=
    Smooth1Nonneg νnonneg (n_on_X_pos npos) εpos

  have smoothIs1 (n : ℕ) (npos : 0 < n) (n_le : (n : ℝ) ≤ X * (1 - c₁ * ε)) :
      Smooth1 ν ε (↑n / X) = 1 := by
    apply hc₁ (ε := ε) (n / X) εpos (n_on_X_pos npos)
    exact (div_le_iff₀' X_pos).mpr n_le

  have smoothIs0 (n : ℕ) (n_le : (1 + c₂ * ε) ≤ (n : ℝ) / X) :
      Smooth1 ν ε (↑n / X) = 0 :=
    hc₂ (ε := ε) (n / X) ⟨εpos, ε_lt_one⟩ n_le

  have X_bound_1 : 1 ≤ X * ε * c₁ := by
    rw [c₁_eq, ← div_le_iff₀]
    · have : 1 / Real.log 2 < 2 := by
        nth_rewrite 2 [← one_div_one_div 2]
        rw [one_div_lt_one_div]
        · exact lt_of_le_of_lt (by norm_num) (Real.log_two_gt_d9)
        · exact Real.log_pos (by norm_num)
        norm_num
      exact le_of_lt (gt_trans X_bound this)
    exact Real.log_pos (by norm_num)

  have X_bound_2 : 1 ≤ X * ε * c₂ := by
    rw [c₂_eq, ← div_le_iff₀]
    · have : 1 / (2 * Real.log 2) < 2 := by
        nth_rewrite 3 [← one_div_one_div 2]
        · rw [one_div_lt_one_div, ← one_mul (1 / 2)]
          · apply mul_lt_mul
            · norm_num
            · apply le_of_lt
              exact lt_trans (by norm_num) (Real.log_two_gt_d9)
            repeat norm_num
          · norm_num
            exact Real.log_pos (by norm_num)
          · norm_num
      exact le_of_lt (gt_trans X_bound this)
    norm_num
    exact Real.log_pos (by norm_num)

  exact twistedSum_close_aux ν c₁ c₁_pos c₁_lt c₂ c₂_pos c₂_lt hc₂ C C_eq ε
    εpos ε_lt_one X X_pos X_gt_three X_bound_1 X_bound_2 smooth1BddAbove smooth1BddBelow
    smoothIs1 smoothIs0 u

end Erdos1201.MR
