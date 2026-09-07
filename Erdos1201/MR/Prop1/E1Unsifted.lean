import Mathlib
import Erdos1201.MR.Ranges
import Erdos1201.MR.Decomposition.Lemma12Assembly
import Erdos1201.MR.Decomposition.Lemma12
import Erdos1201.MR.Prop1.E1

/-!
# Matomäki–Radziwiłł Proposition 1: Exceptional Set E1 Unsifted Bound

This module establishes the upper bound for the integral over $T_1 = \text{Tset } \langle 0, hJ \rangle$
of the unsifted Dirichlet polynomial $|F_u(\beta, X, 1 + it)|^2$, corresponding to Section 8.1
of Matomäki–Radziwiłł (arXiv:1501.04585v4).

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

open Erdos1201.MR MeasureTheory

namespace Erdos1201.MR

/-- Factorisation of `fX β X (p * m)` into `fX β X m * fX β X p` when `p ∈ primeRange P Q`
and `Q ≤ X^β` and `¬ p ∣ m`. -/
lemma factor_fX_coeff (β : ℝ) (X : ℕ) (P Q : ℕ) (hQX : (Q : ℝ) ≤ (X : ℝ) ^ β)
    {p m : ℕ} (hp : p ∈ primeRange P Q) (hpm : ¬ p ∣ m) :
    fX β X (p * m) = fX β X m * fX β X p := by
  have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp_le_Q : p ≤ Q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  have hp_le_X : (p : ℝ) ≤ (X : ℝ) ^ β := by
    have : (p : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hp_le_Q
    linarith
  have hm_pos : 0 < m := by
    by_contra hm
    have : m = 0 := by omega
    subst this
    exact hpm (dvd_zero p)
  have hfX_pm : fX β X (p * m) = fX β X m := fX_mul_of_prime_le β X p m hp_prime hm_pos hp_le_X
  have hfX_p : fX β X p = 1 := fX_prime_eq_one β X p hp_prime hp_le_X
  rw [hfX_pm, hfX_p, mul_one]

/-- Uniform integral bound for the unsifted polynomial $F_u$ on the exceptional set
$T_1 = \text{Tset } \langle 0, hJ \rangle$ (Matomäki–Radziwiłł arXiv:1501.04585v4, Section 8.1). -/
theorem integral_Tset_zero_le_unsifted {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ), 3 / 4 ≤ β → β < 1 → 2 ≤ X → 0 ≤ T₀ → T₀ ≤ T →
      (∀ j, (S.Q j : ℝ) ≤ (X : ℝ) ^ β) → (S.Q ⟨0, hJ⟩ : ℝ) ^ 4 ≤ X → 1 ≤ S.Hj hJ ⟨0, hJ⟩ → S.Hj hJ ⟨0, hJ⟩ ≤ Real.sqrt (S.P ⟨0, hJ⟩) →
      ∫ t in S.Tset hJ β X T₀ T ⟨0, hJ⟩, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (T / ((X : ℝ) / S.Q ⟨0, hJ⟩) + 1) * ((Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η))
        + C * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange (S.P ⟨0, hJ⟩) (S.Q ⟨0, hJ⟩), ¬ p ∣ n)).card : ℝ) / X := by
  obtain ⟨C_L12, hC_L12_pos, hL12⟩ := integral_norm_sq_F_le_sum_QR
  have h_alpha_pos : 0 < alpha η 1 := alpha_pos η hη0 hη 1 (by norm_num)
  let C_1 := C_L12 * (12 + 24 * Real.pi) * (3 * (1 / (2 * alpha η 1) + 1))
  let C_2 := 2 * C_L12
  let C := max (C_1 + C_2) C_L12 + 1
  have hC_pos : 0 < C := by
    have : 0 < C_L12 := hC_L12_pos
    have : 0 < max (C_1 + C_2) C_L12 := lt_of_lt_of_le hC_L12_pos (le_max_right _ _)
    linarith
  use C
  refine ⟨hC_pos, ?_⟩
  intro J S hJ β X T₀ T hβ hβ1 hX hT0 hT hQX_all hQ4 hH1 hHP
  let P := S.P ⟨0, hJ⟩
  let Q := S.Q ⟨0, hJ⟩
  let H := S.Hj hJ ⟨0, hJ⟩
  let V := S.Ij hJ ⟨0, hJ⟩
  have hP_pos : 0 < (P : ℝ) := by
    have := S.two_le_P ⟨0, hJ⟩
    exact_mod_cast (by omega : 0 < P)
  have hQ_gt1 : (1 : ℝ) < (Q : ℝ) := by
    have := (S.two_le_P ⟨0, hJ⟩).trans (S.P_le_Q ⟨0, hJ⟩)
    exact_mod_cast (by omega : 1 < Q)
  have hlogQ_pos : 0 < Real.log (Q : ℝ) := Real.log_pos hQ_gt1
  have hW_pos : 0 < (Real.log (Q : ℝ)) ^ (1 / 3 : ℝ) / (P : ℝ) ^ (1 / 6 - η) :=
    div_pos (Real.rpow_pos_of_pos hlogQ_pos _) (Real.rpow_pos_of_pos hP_pos _)
  let W := (Real.log (Q : ℝ)) ^ (1 / 3 : ℝ) / (P : ℝ) ^ (1 / 6 - η)
  have hX1 : 1 ≤ X := by omega
  have hP2 : 2 ≤ P := S.two_le_P ⟨0, hJ⟩
  have hPQ : P ≤ Q := S.P_le_Q ⟨0, hJ⟩
  have hQX : (Q : ℝ) ≤ X := by
    have hQ_ge2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hP2.trans hPQ
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by linarith
    have hQ2 : (1 : ℝ) ≤ (Q : ℝ) * (Q : ℝ) := by nlinarith
    have hQ3 : (1 : ℝ) ≤ (Q : ℝ) * ((Q : ℝ) * (Q : ℝ)) := by nlinarith
    have h4 : (Q : ℝ) ^ 4 = (Q : ℝ) * ((Q : ℝ) * ((Q : ℝ) * (Q : ℝ))) := by ring
    have h_le : (Q : ℝ) ≤ (Q : ℝ) ^ 4 := by
      rw [h4]
      nlinarith
    exact h_le.trans hQ4
  have hP4 : (P : ℝ) ^ 4 ≤ X := by
    have hPQ_r : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
    have : (P : ℝ) ^ 4 ≤ (Q : ℝ) ^ 4 := by
      have : 0 ≤ (P : ℝ) := by positivity
      gcongr
    exact this.trans hQ4
  have hT_pos : 0 ≤ T := hT0.trans hT
  let U := S.Tset hJ β X T₀ T ⟨0, hJ⟩
  have hU_meas : MeasurableSet U := S.measurableSet_Tset hJ β X T₀ T ⟨0, hJ⟩
  have hU_sub : U ⊆ Set.Icc (-T) T := by
    intro t ht
    have ht_in := ht.1
    exact ⟨by linarith [hT0, ht_in.1], ht_in.2⟩
  let a := fX β X
  let b := fX β X
  let c := fX β X
  have ha : ∀ n, ‖a n‖ ≤ 1 := fun n => norm_fX_le_one β X n
  have hb : ∀ m, ‖b m‖ ≤ 1 := fun m => norm_fX_le_one β X m
  have hc : ∀ p, ‖c p‖ ≤ 1 := fun p => norm_fX_le_one β X p
  have hfactor : ∀ p m, p ∈ primeRange P Q → ¬ p ∣ m → a (p * m) = b m * c p :=
    fun p m hp hpm => factor_fX_coeff β X P Q (hQX_all ⟨0, hJ⟩) hp hpm
  have h_l12 := hL12 X P Q H a b c T U hX1 hP2 hPQ hQX hP4 hH1 hT_pos hU_meas hU_sub ha hb hc hfactor
  change ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      C_L12 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
          C_L12 * (T / X + 1) * (1 / H + 1 / (P : ℝ) + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) at h_l12
  have h_sum_QR_v : ∀ v ∈ V,
      ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        Real.exp (-2 * (alpha η 1) * v / H) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) :=
    fun v hv => integral_norm_sq_QR_v_le S hJ β X T₀ T hX1 hT0 hT hH1 b hb v hv
  have h_sum_le : (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      (∑ v ∈ V, Real.exp (-2 * (alpha η 1) * v / H)) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) := by
    have h_sum_ineq := Finset.sum_le_sum h_sum_QR_v
    rw [← Finset.sum_mul] at h_sum_ineq
    exact h_sum_ineq
  have hH_def : H = (P : ℝ) ^ (1 / 6 - η) / (Real.log (Q : ℝ)) ^ (1 / 3 : ℝ) := by
    dsimp [H, P, Q]
    unfold RangeSystem.Hj
    have : (((⟨0, hJ⟩ : Fin J).val + 1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
    rw [this, one_mul]
  have h_H_sum := H_logQ_sum_exp_le hη0 hη P Q hP2 hPQ H hH1 hH_def
  have h_term1_le : C_L12 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      C_1 * (T / ((X : ℝ) / Q) + 1) * W := by
    have h_mul1 : C_L12 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C_L12 * (H * Real.log Q) * ((∑ v ∈ V, Real.exp (-2 * (alpha η 1) * v / H)) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1))) := by
      have hH_logQ : 0 ≤ C_L12 * (H * Real.log Q) := by
        have : 0 ≤ Real.log (Q : ℝ) := le_of_lt hlogQ_pos
        positivity
      exact mul_le_mul_of_nonneg_left h_sum_le hH_logQ
    have h_rearrange : C_L12 * (H * Real.log Q) * ((∑ v ∈ V, Real.exp (-2 * (alpha η 1) * v / H)) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1))) =
        (C_L12 * (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) * ((H * Real.log Q) * (∑ v ∈ V, Real.exp (-2 * (alpha η 1) * v / H))) := by ring
    rw [h_rearrange] at h_mul1
    have h_mul2 : (C_L12 * (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) * ((H * Real.log Q) * (∑ v ∈ V, Real.exp (-2 * (alpha η 1) * v / H))) ≤
        (C_L12 * (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) * (3 * (1 / (2 * alpha η 1) + 1) * W) := by
      have h_pre_nonneg : 0 ≤ C_L12 * (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1) := by positivity
      exact mul_le_mul_of_nonneg_left h_H_sum h_pre_nonneg
    have h_alg : (C_L12 * (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) * (3 * (1 / (2 * alpha η 1) + 1) * W) =
        C_1 * (T / ((X : ℝ) / Q) + 1) * W := by
      dsimp [C_1]
      ring
    rw [h_alg] at h_mul2
    exact h_mul1.trans h_mul2
  have h_X_Q : T / (X : ℝ) + 1 ≤ T / ((X : ℝ) / Q) + 1 := by
    have h1 : T / (X : ℝ) ≤ T / ((X : ℝ) / Q) := by
      have h_div_Q : T / ((X : ℝ) / Q) = T * (Q : ℝ) / (X : ℝ) := div_div_eq_mul_div T (X : ℝ) (Q : ℝ)
      rw [h_div_Q]
      have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (show 1 ≤ Q by omega)
      have : T * 1 ≤ T * (Q : ℝ) := mul_le_mul_of_nonneg_left hQ1 hT_pos
      rw [mul_one] at this
      exact div_le_div_of_nonneg_right this (by positivity)
    linarith
  have h1H_eq : 1 / H = W := one_div_H_eq P Q η H hH_def
  have h1P_le : 1 / (P : ℝ) ≤ W := by
    rw [← h1H_eq]
    exact one_div_P_le_one_div_H P H hP2 hH1 hHP
  have h_1H_1P : 1 / H + 1 / (P : ℝ) ≤ 2 * W := by
    linarith [h1H_eq]
  have h_term2_split : C_L12 * (T / X + 1) * (1 / H + 1 / (P : ℝ) + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) =
      C_L12 * (T / X + 1) * (1 / H + 1 / (P : ℝ)) + C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by
    ring
  have h_term2_le : C_L12 * (T / X + 1) * (1 / H + 1 / (P : ℝ)) ≤ C_2 * (T / ((X : ℝ) / Q) + 1) * W := by
    have h_nonneg : 0 ≤ C_L12 := le_of_lt hC_L12_pos
    have h1 : C_L12 * (T / X + 1) ≤ C_L12 * (T / ((X : ℝ) / Q) + 1) :=
      mul_le_mul_of_nonneg_left h_X_Q h_nonneg
    have h2 : (C_L12 * (T / X + 1)) * (1 / H + 1 / (P : ℝ)) ≤ (C_L12 * (T / ((X : ℝ) / Q) + 1)) * (2 * W) := by
      have : 0 ≤ 1 / H + 1 / (P : ℝ) := by positivity
      have h_left_nonneg : 0 ≤ C_L12 * (T / X + 1) := by positivity
      exact mul_le_mul h1 h_1H_1P this (by positivity)
    calc C_L12 * (T / X + 1) * (1 / H + 1 / (P : ℝ))
      _ ≤ C_L12 * (T / ((X : ℝ) / Q) + 1) * (2 * W) := h2
      _ = C_2 * (T / ((X : ℝ) / Q) + 1) * W := by
        dsimp [C_2]
        ring
  have h_sum_main : C_1 * (T / ((X : ℝ) / Q) + 1) * W + C_2 * (T / ((X : ℝ) / Q) + 1) * W ≤
      C * (T / ((X : ℝ) / Q) + 1) * W := by
    have h_factor : C_1 * (T / ((X : ℝ) / Q) + 1) * W + C_2 * (T / ((X : ℝ) / Q) + 1) * W =
        (C_1 + C_2) * ((T / ((X : ℝ) / Q) + 1) * W) := by ring
    rw [h_factor]
    have hC_ge : C_1 + C_2 ≤ C := by
      have : C_1 + C_2 ≤ max (C_1 + C_2) C_L12 := le_max_left _ _
      linarith
    have h_prod_nonneg : 0 ≤ (T / ((X : ℝ) / Q) + 1) * W := by positivity
    calc (C_1 + C_2) * ((T / ((X : ℝ) / Q) + 1) * W)
      _ ≤ C * ((T / ((X : ℝ) / Q) + 1) * W) := mul_le_mul_of_nonneg_right hC_ge h_prod_nonneg
      _ = C * (T / ((X : ℝ) / Q) + 1) * W := by ring
  have h_unsifted_le : C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X ≤
      C * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by
    have hC_ge_L12 : C_L12 ≤ C := by
      have : C_L12 ≤ max (C_1 + C_2) C_L12 := le_max_right _ _
      linarith
    have h_card_pos : 0 ≤ (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by positivity
    have h_TX_pos : 0 ≤ T / (X : ℝ) + 1 := by positivity
    have : 0 ≤ (T / (X : ℝ) + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by positivity
    calc C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X
      _ = C_L12 * ((T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := by ring
      _ ≤ C * ((T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) :=
        mul_le_mul_of_nonneg_right hC_ge_L12 this
      _ = C * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by ring
  have h_step_bound : ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      C * (T / ((X : ℝ) / Q) + 1) * W +
        C * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by
    calc ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2
      _ ≤ C_L12 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
          C_L12 * (T / X + 1) * (1 / H + 1 / (P : ℝ) + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := h_l12
      _ = C_L12 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
          (C_L12 * (T / X + 1) * (1 / H + 1 / (P : ℝ)) + C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := by rw [h_term2_split]
      _ ≤ C_1 * (T / ((X : ℝ) / Q) + 1) * W +
          (C_2 * (T / ((X : ℝ) / Q) + 1) * W + C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := by
        linarith [h_term1_le, h_term2_le]
      _ = (C_1 * (T / ((X : ℝ) / Q) + 1) * W + C_2 * (T / ((X : ℝ) / Q) + 1) * W) +
          C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by ring
      _ ≤ C * (T / ((X : ℝ) / Q) + 1) * W +
          C * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by
        linarith [h_sum_main, h_unsifted_le]
  exact h_step_bound

end Erdos1201.MR
