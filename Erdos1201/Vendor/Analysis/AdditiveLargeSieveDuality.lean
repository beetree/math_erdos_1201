module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `ℓ²`-operator-norm duality for a finite complex matrix

If a quadratic form bound holds for the transpose of a finite complex matrix,
the same bound holds for the matrix itself: the nonzero singular values of `M`
and `Mᵀ` coincide. Source provenance is recorded in the campaign report.
-/

namespace AdditiveLargeSieveDuality

open scoped BigOperators
open Complex

/-- If the transpose quadratic form of a finite complex matrix `M` is bounded
by `C`, so is the primal one. -/
theorem sq_sum_transpose_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : ι → κ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ b : ι → ℂ, ∑ k, ‖∑ i, M i k * b i‖ ^ 2 ≤ C * ∑ i, ‖b i‖ ^ 2) :
    ∀ c : κ → ℂ, ∑ i, ‖∑ k, M i k * c k‖ ^ 2 ≤ C * ∑ k, ‖c k‖ ^ 2 := by
  intro c
  set v : ι → ℂ := fun i => ∑ k, M i k * c k with hv_def
  set w : κ → ℂ := fun k => ∑ i, (starRingEnd ℂ) (M i k) * v i with hw_def
  set S : ℝ := ∑ i, ‖v i‖ ^ 2 with hS_def
  have hS_nonneg : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc_nonneg : 0 ≤ ∑ k, ‖c k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hw_nonneg : 0 ≤ ∑ k, ‖w k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- The key identity `∑ i, v i * conj (v i) = ∑ k, c k * conj (w k)`, obtained by
  -- expanding `w`, swapping the order of summation, and regrouping.
  have hconj_w : ∀ k, (starRingEnd ℂ) (w k) = ∑ i, M i k * (starRingEnd ℂ) (v i) := by
    intro k
    rw [hw_def]
    simp only [map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  have key : ∑ i, v i * (starRingEnd ℂ) (v i) = ∑ k, c k * (starRingEnd ℂ) (w k) := by
    simp only [hconj_w, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∑ k : κ, c k * (M i k * (starRingEnd ℂ) (v i))
        = (starRingEnd ℂ) (v i) * ∑ k, M i k * c k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, hv_def]
    ring
  have hS_eq : (S : ℂ) = ∑ k, c k * (starRingEnd ℂ) (w k) := by
    rw [← key, hS_def]
    push_cast
    exact Finset.sum_congr rfl fun i _ => by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq]
  have hS_le : S ≤ ‖∑ k, c k * (starRingEnd ℂ) (w k)‖ := by
    rw [← hS_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS_nonneg]
  have hcs : ‖∑ k, c k * (starRingEnd ℂ) (w k)‖
      ≤ Real.sqrt (∑ k, ‖c k‖ ^ 2) * Real.sqrt (∑ k, ‖w k‖ ^ 2) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ k, ‖c k * (starRingEnd ℂ) (w k)‖ = ‖c k‖ * ‖w k‖ := by
      intro k
      rw [norm_mul, Complex.norm_conj]
    simp only [hterm]
    have hsq : (∑ k, ‖c k‖ * ‖w k‖) ^ 2 ≤ (∑ k, ‖c k‖ ^ 2) * ∑ k, ‖w k‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have hnonneg : 0 ≤ ∑ k, ‖c k‖ * ‖w k‖ :=
      Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hnonneg, Real.sqrt_mul hc_nonneg] at this
  have h_w : ∑ k, ‖w k‖ ^ 2 ≤ C * S := by
    have := h (fun i => starRingEnd ℂ (v i))
    have heq1 : ∑ k, ‖∑ i, M i k * (starRingEnd ℂ) (v i)‖ ^ 2 = ∑ k, ‖w k‖ ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hconj_w k, Complex.norm_conj]
    have heq2 : ∑ i, ‖(starRingEnd ℂ) (v i)‖ ^ 2 = S := by
      simp only [Complex.norm_conj, hS_def]
    rwa [heq1, heq2] at this
  by_cases hS_zero : S = 0
  · rw [hS_zero]; positivity
  · have hS_pos : 0 < S := lt_of_le_of_ne hS_nonneg (Ne.symm hS_zero)
    have hchain : S ≤ Real.sqrt (∑ k, ‖c k‖ ^ 2) * Real.sqrt (∑ k, ‖w k‖ ^ 2) :=
      hS_le.trans hcs
    have hsqrtw : Real.sqrt (∑ k, ‖w k‖ ^ 2) ≤ Real.sqrt (C * S) :=
      Real.sqrt_le_sqrt h_w
    have hsqrtCS : Real.sqrt (C * S) = Real.sqrt C * Real.sqrt S := Real.sqrt_mul hC S
    have hSsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS_pos
    have step1 : Real.sqrt S * Real.sqrt S
        ≤ Real.sqrt (∑ k, ‖c k‖ ^ 2) * Real.sqrt C * Real.sqrt S := by
      rw [Real.mul_self_sqrt hS_nonneg]
      calc S ≤ Real.sqrt (∑ k, ‖c k‖ ^ 2) * Real.sqrt (∑ k, ‖w k‖ ^ 2) := hchain
        _ ≤ Real.sqrt (∑ k, ‖c k‖ ^ 2) * Real.sqrt (C * S) :=
            mul_le_mul_of_nonneg_left hsqrtw (Real.sqrt_nonneg _)
        _ = Real.sqrt (∑ k, ‖c k‖ ^ 2) * Real.sqrt C * Real.sqrt S := by
            rw [hsqrtCS, mul_assoc]
    have step2 : Real.sqrt S ≤ Real.sqrt (∑ k, ‖c k‖ ^ 2) * Real.sqrt C :=
      le_of_mul_le_mul_right step1 hSsqrt_pos
    have step3 : S ≤ (Real.sqrt (∑ k, ‖c k‖ ^ 2) * Real.sqrt C) ^ 2 := by
      calc S = Real.sqrt S ^ 2 := (Real.sq_sqrt hS_nonneg).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) step2 2
    have step4 : (Real.sqrt (∑ k, ‖c k‖ ^ 2) * Real.sqrt C) ^ 2 = (∑ k, ‖c k‖ ^ 2) * C := by
      rw [mul_pow, Real.sq_sqrt hc_nonneg, Real.sq_sqrt hC]
    rw [step4, mul_comm] at step3
    exact step3

end AdditiveLargeSieveDuality
