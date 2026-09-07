import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Ranges
import Erdos1201.MR.Decomposition.Lemma12Assembly
import Erdos1201.MR.Decomposition.Lemma12
import Erdos1201.MR.Polynomials.MomentComputation
import Erdos1201.MR.Analysis.MeanValueTheorem

open MeasureTheory intervalIntegral
open scoped BigOperators Real

/-!
# Matomäki–Radziwiłł Proposition 1: Level Set Ej Integral Bound

This module establishes bounds for the integral over $T_j = \text{Tset } j$
of the Dirichlet polynomial $|F(\beta, J, \mathcal{R}, X, 1 + it)|^2$ for $j \ge 1$
($j \ge 2$ in 1-based indexing), corresponding to Section 8.2 of Matomäki–Radziwiłł (arXiv:1501.04585v4).

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

namespace Erdos1201.MR

/-- Difference of successive α parameters: α_i - α_j ≤ -η / (2 (j+1)²) for i + 1 = j. -/
lemma alpha_sub_succ_le {J : ℕ} {η : ℝ} (hη0 : 0 < η) {i j : Fin J} (hij : i.val + 1 = j.val) :
    alpha η (i.val + 1) - alpha η (j.val + 1) ≤ - (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) := by
  have hi_ge1 : 1 ≤ i.val + 1 := by omega
  have hj_eq : j.val + 1 = (i.val + 1) + 1 := by omega
  rw [hj_eq]
  have h_diff := alpha_succ_sub_alpha η hη0 (i.val + 1) hi_ge1
  linarith

/-- Exponent inequality in paper Section 8.2:
`2 (v / H_j) (α_i - α_j + η / (4 (j+1)²)) ≤ - (η / (2 (j+1)²)) (v / H_j)`. -/
lemma exponent_ineq_le {J : ℕ} {η : ℝ} (hη0 : 0 < η) {i j : Fin J} (hij : i.val + 1 = j.val)
    {v : ℝ} {H : ℝ} (hv : 0 ≤ v) (hH : 0 < H) :
    2 * (v / H) * (alpha η (i.val + 1) - alpha η (j.val + 1) + η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) ≤
      - (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) * (v / H) := by
  have h_alpha := alpha_sub_succ_le hη0 hij
  have hj_pos : 0 < ((j.val + 1 : ℕ) : ℝ) := by
    have : 1 ≤ j.val + 1 := by omega
    exact Nat.cast_pos.mpr this
  have hj2_pos : 0 < ((j.val + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have h_bracket : alpha η (i.val + 1) - alpha η (j.val + 1) + η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2) ≤
      - (η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) := by
    have h_split : - (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) + η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2) =
        - (η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) := by ring
    calc alpha η (i.val + 1) - alpha η (j.val + 1) + η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2)
      _ ≤ - (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) + η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2) := by linarith [h_alpha]
      _ = - (η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) := h_split
  have hvH : 0 ≤ v / H := div_nonneg hv (le_of_lt hH)
  have h_mul := mul_le_mul_of_nonneg_left h_bracket hvH
  calc 2 * (v / H) * (alpha η (i.val + 1) - alpha η (j.val + 1) + η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2))
    _ = 2 * ((v / H) * (alpha η (i.val + 1) - alpha η (j.val + 1) + η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2))) := by ring
    _ ≤ 2 * ((v / H) * (- (η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2)))) := by linarith
    _ = - (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) * (v / H) := by ring

/-- Size of the index set I_j is bounded by 5 H_j log Q_j. -/
lemma RangeSystem.card_Ij_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (j : Fin J)
    (hH : 1 ≤ S.Hj hJ j) :
    (((S.Ij hJ j).card : ℝ)) ≤ 5 * (S.Hj hJ j * Real.log (S.Q j)) :=
  card_Icc_log_le (S.Hj hJ j) (S.P j) (S.Q j) hH (S.two_le_P j) (S.P_le_Q j)

/-- Consequence of condition (3) on exponential decay of prime levels. -/
lemma RangeSystem.exp_neg_eta_cond3_le {J : ℕ} {η : ℝ} (S : RangeSystem J η)
    (hη0 : 0 < η) {i j : Fin J} (hij : i.val + 1 = j.val) :
    - (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) * Real.log (S.P j) ≤
      - 4 * Real.log (S.Q i) := by
  have hcond := S.cond3 j i hij
  have hj_pos : 0 < ((j.val + 1 : ℕ) : ℝ) := by
    have : 1 ≤ j.val + 1 := by omega
    exact Nat.cast_pos.mpr this
  have hj2_pos : 0 < ((j.val + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have h_factor_pos : 0 < η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have h_log_pos : 0 ≤ 16 * Real.log ((j.val + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j.val + 1)
    exact mul_nonneg (by norm_num) (Real.log_nonneg this)
  have h_bound1 : (8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i) ≤ Real.log (S.P j) := by
    linarith [hcond, h_log_pos]
  have h_mul := mul_le_mul_of_nonneg_left h_bound1 (le_of_lt h_factor_pos)
  have h_alg : (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) * ((8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i)) =
      4 * Real.log (S.Q i) := by
    calc (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) * ((8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i))
      _ = (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2) * (8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η)) * Real.log (S.Q i) := by ring
      _ = 4 * Real.log (S.Q i) := by
        have h_cancel : η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2) * (8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) = 4 := by
          field_simp
          ring
        rw [h_cancel]
  rw [h_alg] at h_mul
  linarith

/-- Exponentiated consequence of condition (3): exp(-η/(2(j+1)²) log P_j) ≤ (Q_i)^{-4}. -/
lemma RangeSystem.cond3_decay_power_le {J : ℕ} {η : ℝ} (S : RangeSystem J η)
    (hη0 : 0 < η) {i j : Fin J} (hij : i.val + 1 = j.val) :
    Real.exp (- (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2)) * Real.log (S.P j)) ≤
      (S.Q i : ℝ) ^ (-4 : ℝ) := by
  have h_exp_le := Real.exp_le_exp.mpr (S.exp_neg_eta_cond3_le hη0 hij)
  have hQi_pos : 0 < (S.Q i : ℝ) := by
    have : 2 ≤ S.Q i := (S.two_le_P i).trans (S.P_le_Q i)
    positivity
  have h_rpow : (S.Q i : ℝ) ^ (-4 : ℝ) = Real.exp (-4 * Real.log (S.Q i)) := by
    rw [Real.rpow_def_of_pos hQi_pos]
    ring_nf
  rw [h_rpow]
  exact h_exp_le

/-- The level set T_j is contained in the symmetric interval [-T, T] when 0 ≤ T₀ ≤ T. -/
lemma RangeSystem.Tset_subset_Icc_neg {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T) :
    S.Tset hJ β X T₀ T j ⊆ Set.Icc (-T) T := by
  intro t ht
  have ht_Icc := ht.1
  have ht_T0 : T₀ ≤ t := ht_Icc.1
  have ht_T : t ≤ T := ht_Icc.2
  have h_nonneg_t : 0 ≤ t := hT0.trans ht_T0
  have h_neg_T_le : -T ≤ t := by linarith
  exact ⟨h_neg_T_le, ht_T⟩

/-- On T_j, level j is good: each short prime polynomial is exponentially small. -/
lemma RangeSystem.Tset_good {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) {t : ℝ} (ht : t ∈ S.Tset hJ β X T₀ T j)
    (v : ℕ) (hv : v ∈ S.Ij hJ j) :
    ‖Qpoly β X (S.P j) (S.Q j) (S.Hj hJ j) v ((1 : ℂ) + t * Complex.I)‖ ≤
      Real.exp (-(alpha η (j.val + 1)) * v / S.Hj hJ j) :=
  ht.2.1 v hv

/-- On T_j, any strictly smaller level i < j is not good: there exists r ∈ I_i where Q is large. -/
lemma RangeSystem.Tset_not_good_prev {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j i : Fin J) (hij : i < j)
    {t : ℝ} (ht : t ∈ S.Tset hJ β X T₀ T j) :
    ¬ S.Good hJ β X i t :=
  ht.2.2 i hij

/-- On T_j, for i < j, the negation of Good yields an index r ∈ I_i with large Dirichlet polynomial.
This provides the partition T_j = ⋃_{r ∈ I_i} T_{j,r} used in Section 8.2. -/
lemma RangeSystem.Tset_exists_violating_r {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j i : Fin J) (hij : i < j)
    {t : ℝ} (ht : t ∈ S.Tset hJ β X T₀ T j) :
    ∃ r ∈ S.Ij hJ i,
      Real.exp (-(alpha η (i.val + 1)) * r / S.Hj hJ i) <
        ‖Qpoly β X (S.P i) (S.Q i) (S.Hj hJ i) r ((1 : ℂ) + t * Complex.I)‖ := by
  have h_not := S.Tset_not_good_prev hJ β X T₀ T j i hij ht
  unfold Good at h_not
  by_contra h_all
  apply h_not
  intro r hr
  by_contra h_gt
  have h_lt : Real.exp (-(alpha η (i.val + 1)) * r / S.Hj hJ i) <
      ‖Qpoly β X (S.P i) (S.Q i) (S.Hj hJ i) r ((1 : ℂ) + t * Complex.I)‖ := lt_of_not_ge h_gt
  exact h_all ⟨r, hr, h_lt⟩

lemma exp_div_H_le_three_mul_Q (H : ℝ) (Q : ℕ) (v : ℕ) (hH : 1 ≤ H) (hQ : 1 ≤ Q)
    (hv : v ≤ ⌈H * Real.log Q⌉₊) :
    Real.exp (v / H) ≤ 3 * (Q : ℝ) := by
  have hH_pos : 0 < H := by linarith
  have hQ_pos : 0 < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hlogQ_nonneg : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg (by exact_mod_cast hQ)
  have hHlogQ_nonneg : 0 ≤ H * Real.log (Q : ℝ) := mul_nonneg (by linarith) hlogQ_nonneg
  have hv_le : (v : ℝ) ≤ H * Real.log (Q : ℝ) + 1 := by
    have h1 : (v : ℝ) ≤ (⌈H * Real.log (Q : ℝ)⌉₊ : ℝ) := by exact_mod_cast hv
    have h2 : (⌈H * Real.log (Q : ℝ)⌉₊ : ℝ) < H * Real.log (Q : ℝ) + 1 :=
      Nat.ceil_lt_add_one hHlogQ_nonneg
    linarith
  have h_div : (v : ℝ) / H ≤ Real.log (Q : ℝ) + 1 := by
    calc (v : ℝ) / H
      _ ≤ (H * Real.log (Q : ℝ) + 1) / H := div_le_div_of_nonneg_right hv_le (le_of_lt hH_pos)
      _ = Real.log (Q : ℝ) + 1 / H := by
        rw [add_div, mul_div_cancel_left₀ (Real.log (Q : ℝ)) hH_pos.ne']
      _ ≤ Real.log (Q : ℝ) + 1 := by
        have : 1 / H ≤ 1 := by
          rw [div_le_iff₀ hH_pos]
          linarith
        linarith
  have h_exp := Real.exp_le_exp.mpr h_div
  rw [Real.exp_add, Real.exp_log hQ_pos] at h_exp
  have h_e3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  calc Real.exp (v / H)
    _ ≤ (Q : ℝ) * Real.exp 1 := h_exp
    _ ≤ (Q : ℝ) * 3 := mul_le_mul_of_nonneg_left (le_of_lt h_e3) (le_of_lt hQ_pos)
    _ = 3 * (Q : ℝ) := by ring

lemma norm_b_div_omega_le_one (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (P Q m : ℕ) :
    ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ≤ 1 := by
  rw [norm_div]
  have h_eq : (omegaIn (primeRange P Q) m : ℂ) + 1 = ((omegaIn (primeRange P Q) m + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [h_eq, Complex.norm_natCast]
  have h_den : 1 ≤ ((omegaIn (primeRange P Q) m + 1 : ℕ) : ℝ) := by
    have : 1 ≤ omegaIn (primeRange P Q) m + 1 := by omega
    exact_mod_cast this
  have h_num := hb m
  have h_den_pos : 0 < ((omegaIn (primeRange P Q) m + 1 : ℕ) : ℝ) := by linarith
  exact (div_le_iff₀ h_den_pos).mpr (by linarith)

lemma sum_norm_sq_b_div_omega_le (X : ℕ) (H : ℝ) (v : ℕ) (P Q : ℕ) (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hX : 1 ≤ X) :
    (∑ m ∈ cofactorRange X H v, ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2) ≤
      2 * Real.exp (v / H) / (X : ℝ) := by
  let S := cofactorRange X H v
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
  have hexp_pos : 0 < Real.exp (-(v / H)) := Real.exp_pos _
  have hprod_pos : 0 < (X : ℝ) * Real.exp (-(v / H)) := mul_pos hX_pos hexp_pos
  have h_bound_m : ∀ m ∈ S, ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2 ≤
      1 / (X * Real.exp (-(v / H))) ^ 2 := by
    intro m hm
    dsimp [S] at hm
    unfold cofactorRange at hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    have hm_gt : X * Real.exp (-(v / H)) < (m : ℝ) := hm.2
    have hm_sq : (X * Real.exp (-(v / H))) ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith [hm_gt, hprod_pos]
    have h_norm : ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 ≤ 1 := by
      have := norm_b_div_omega_le_one b hb P Q m
      nlinarith [norm_nonneg (b m / ((omegaIn (primeRange P Q) m : ℂ) + 1))]
    have h1 : ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right h_norm (by positivity)
    have h2 : 1 / (m : ℝ) ^ 2 ≤ 1 / (X * Real.exp (-(v / H))) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hm_sq
    exact h1.trans h2
  have h_sum := Finset.sum_le_sum h_bound_m
  have h_card_sum : (∑ _m ∈ S, 1 / (X * Real.exp (-(v / H))) ^ 2) =
      (S.card : ℝ) * (1 / (X * Real.exp (-(v / H))) ^ 2) := by
    simp [nsmul_eq_mul]
  rw [h_card_sum] at h_sum
  have hS_sub : S ⊆ Finset.Ioc 0 ⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊ := by
    intro m hm
    dsimp [S] at hm
    unfold cofactorRange at hm
    exact (Finset.mem_filter.mp hm).1
  have h_card_le : (S.card : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(v / H)) := by
    have h1 : S.card ≤ (Finset.Ioc 0 ⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊).card := Finset.card_le_card hS_sub
    rw [Nat.card_Ioc, Nat.sub_zero] at h1
    have h2 : (⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊ : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(v / H)) :=
      Nat.floor_le (by positivity)
    exact (Nat.cast_le.mpr h1).trans h2
  have h_nonneg : 0 ≤ 1 / (X * Real.exp (-(v / H))) ^ 2 := by positivity
  have h_mul_card := mul_le_mul_of_nonneg_right h_card_le h_nonneg
  have h_alg : 2 * (X : ℝ) * Real.exp (-(v / H)) * (1 / (X * Real.exp (-(v / H))) ^ 2) =
      2 * Real.exp (v / H) / (X : ℝ) := by
    have h_sq : (X * Real.exp (-(v / H))) ^ 2 = (X * Real.exp (-(v / H))) * (X * Real.exp (-(v / H))) := sq _
    rw [h_sq, div_mul_eq_div_mul_one_div, ← mul_assoc]
    have h_cancel : 2 * (X : ℝ) * Real.exp (-(v / H)) * (1 / (X * Real.exp (-(v / H)))) = 2 := by
      calc 2 * (X : ℝ) * Real.exp (-(v / H)) * (1 / (X * Real.exp (-(v / H))))
        _ = 2 * ((X : ℝ) * Real.exp (-(v / H)) * (1 / (X * Real.exp (-(v / H))))) := by ring
        _ = 2 * 1 := by rw [mul_one_div_cancel hprod_pos.ne']
        _ = 2 := by ring
    rw [h_cancel]
    have h_exp_neg : Real.exp (-(v / H)) = (Real.exp (v / H))⁻¹ := Real.exp_neg _
    rw [h_exp_neg]
    rw [div_mul_eq_div_mul_one_div]
    field_simp
  calc (∑ m ∈ S, ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2)
    _ ≤ (S.card : ℝ) * (1 / (X * Real.exp (-(v / H))) ^ 2) := h_sum
    _ ≤ 2 * (X : ℝ) * Real.exp (-(v / H)) * (1 / (X * Real.exp (-(v / H))) ^ 2) := h_mul_card
    _ = 2 * Real.exp (v / H) / (X : ℝ) := h_alg

lemma integral_norm_sq_Rv_le (X P Q : ℕ) (H : ℝ) (v : ℕ) (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (T : ℝ)
    (hT : 0 ≤ T) (hX : 1 ≤ X) (hQ : 1 ≤ Q) (hH : 1 ≤ H) (hv : v ≤ ⌈H * Real.log Q⌉₊) :
    ∫ t in (-T)..T, ‖dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1) := by
  let S := cofactorRange X H v
  let N := ⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊
  have hS_sub : S ⊆ Finset.Ioc 0 N := by
    intro m hm
    dsimp [S] at hm
    unfold cofactorRange at hm
    exact (Finset.mem_filter.mp hm).1
  have h_mvt := integral_norm_sq_dirichletPoly_subset_le (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) S N hS_sub T hT
  have h_sum := sum_norm_sq_b_div_omega_le X H v P Q b hb hX
  have hN_le : (N : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(v / H)) := Nat.floor_le (by positivity)
  have h_factor : 2 * T + 6 * Real.pi * (N : ℝ) ≤ 2 * T + 12 * Real.pi * (X : ℝ) * Real.exp (-(v / H)) := by
    have : 6 * Real.pi * (N : ℝ) ≤ 6 * Real.pi * (2 * (X : ℝ) * Real.exp (-(v / H))) :=
      mul_le_mul_of_nonneg_left hN_le (by positivity)
    linarith
  have h_sum_nonneg : 0 ≤ ∑ m ∈ S, ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    positivity
  have h_prod_le := mul_le_mul h_factor h_sum h_sum_nonneg (by positivity)
  have h_exp_mul : Real.exp (-(v / H)) * Real.exp (v / H) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
  have h_alg : (2 * T + 12 * Real.pi * (X : ℝ) * Real.exp (-(v / H))) * (2 * Real.exp (v / H) / (X : ℝ)) =
      4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi := by
    calc (2 * T + 12 * Real.pi * (X : ℝ) * Real.exp (-(v / H))) * (2 * Real.exp (v / H) / (X : ℝ))
      _ = 2 * T * (2 * Real.exp (v / H) / (X : ℝ)) + 12 * Real.pi * (X : ℝ) * Real.exp (-(v / H)) * (2 * Real.exp (v / H) / (X : ℝ)) := by ring
      _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi * ((X : ℝ) * (Real.exp (-(v / H)) * Real.exp (v / H)) / (X : ℝ)) := by ring
      _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi * ((X : ℝ) * 1 / (X : ℝ)) := by rw [h_exp_mul]
      _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi * ((X : ℝ) / (X : ℝ)) := by ring
      _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi * 1 := by rw [div_self hX_pos.ne']
      _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi := by ring
  have h_exp_Q := exp_div_H_le_three_mul_Q H Q v hH hQ hv
  have h_term_T : 4 * T * Real.exp (v / H) / (X : ℝ) ≤ 12 * (T / ((X : ℝ) / Q)) := by
    have h_div_Q : T / ((X : ℝ) / Q) = T * (Q : ℝ) / (X : ℝ) := div_div_eq_mul_div T (X : ℝ) (Q : ℝ)
    rw [h_div_Q]
    have h1 : 4 * T * Real.exp (v / H) ≤ 4 * T * (3 * (Q : ℝ)) :=
      mul_le_mul_of_nonneg_left h_exp_Q (by positivity)
    have : 4 * T * (3 * (Q : ℝ)) = 12 * (T * (Q : ℝ)) := by ring
    rw [this] at h1
    have h2 : 4 * T * Real.exp (v / H) / (X : ℝ) ≤ 12 * (T * (Q : ℝ)) / (X : ℝ) :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have : 12 * (T * (Q : ℝ)) / (X : ℝ) = 12 * (T * (Q : ℝ) / (X : ℝ)) := by ring
    linarith
  have h_final : 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi ≤ (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1) := by
    calc 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi
      _ ≤ 12 * (T / ((X : ℝ) / Q)) + 24 * Real.pi := by linarith
      _ ≤ 12 * (T / ((X : ℝ) / Q)) + 24 * Real.pi * (T / ((X : ℝ) / Q)) + (12 + 24 * Real.pi) := by
        have : 0 ≤ 24 * Real.pi * (T / ((X : ℝ) / Q)) := by positivity
        linarith
      _ = (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1) := by ring
  calc ∫ t in (-T)..T, ‖dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) S ((1 : ℂ) + t * Complex.I)‖ ^ 2
    _ ≤ (2 * T + 6 * Real.pi * (N : ℝ)) * ∑ m ∈ S, ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2 := h_mvt
    _ ≤ (2 * T + 12 * Real.pi * (X : ℝ) * Real.exp (-(v / H))) * (2 * Real.exp (v / H) / (X : ℝ)) := h_prod_le
    _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi := h_alg
    _ ≤ (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1) := h_final

/-- Pointwise bound on the product |Q_v R_v|^2 on T_j for any level j. -/
lemma RangeSystem.norm_sq_QR_v_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) (v : ℕ) (hv : v ∈ S.Ij hJ j)
    (b : ℕ → ℂ) (t : ℝ) (ht : t ∈ S.Tset hJ β X T₀ T j) :
    let P := S.P j
    let Q := S.Q j
    let H := S.Hj hJ j
    ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
        dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H) *
        ‖dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
  intro P Q H
  rw [norm_mul, mul_pow]
  have ht_good := S.Tset_good hJ β X T₀ T j ht v hv
  change ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ≤
    Real.exp (-(alpha η (j.val + 1)) * v / H) at ht_good
  have hQ_sq : ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H) := by
    have h1 : ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        (Real.exp (-(alpha η (j.val + 1)) * v / H)) ^ 2 := by
      nlinarith [norm_nonneg (dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I))]
    have h2 : (Real.exp (-(alpha η (j.val + 1)) * v / H)) ^ 2 = Real.exp (-2 * (alpha η (j.val + 1)) * v / H) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rwa [h2] at h1
  exact mul_le_mul_of_nonneg_right hQ_sq (sq_nonneg _)

/-- Integral bound on the bilinear term |Q_v R_v|^2 on T_j for any level j with absolute constant 12 + 24π. -/
lemma RangeSystem.integral_norm_sq_QR_v_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hX : 1 ≤ X) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T)
    (j : Fin J) (hH : 1 ≤ S.Hj hJ j) (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (v : ℕ) (hv : v ∈ S.Ij hJ j) :
    let P := S.P j
    let Q := S.Q j
    let H := S.Hj hJ j
    let U := S.Tset hJ β X T₀ T j
    ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
        dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) := by
  intro P Q H U
  have hT_nonneg : 0 ≤ T := hT0.trans hT
  have hU_sub : U ⊆ Set.Icc (-T) T := by
    intro t ht
    have ht_in := ht.1
    exact ⟨by linarith [hT0, ht_in.1], ht_in.2⟩
  have hU_meas : MeasurableSet U := S.measurableSet_Tset hJ β X T₀ T j
  let c := fX β X
  let b_omega := fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
  let Qv (t : ℝ) := dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)
  let Rv (t : ℝ) := dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)
  have h_pt_le : ∀ t ∈ U, ‖Qv t * Rv t‖ ^ 2 ≤ Real.exp (-2 * (alpha η (j.val + 1)) * v / H) * ‖Rv t‖ ^ 2 := by
    intro t ht
    exact S.norm_sq_QR_v_le hJ β X T₀ T j v hv b t ht
  have hCont_Rv : Continuous (fun t => ‖Rv t‖ ^ 2) := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_dirichletPoly_l12
    intro n hn
    unfold cofactorRange at hn
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  have hCont_Qv : Continuous (fun t => ‖Qv t‖ ^ 2) := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_dirichletPoly_l12
    intro n hn
    unfold shortPrimeRange primeRange at hn
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    have := hn.1.2.two_le
    omega
  have hCont_QR : Continuous (fun t => ‖Qv t * Rv t‖ ^ 2) := by
    have : (fun t => ‖Qv t * Rv t‖ ^ 2) = (fun t => ‖Qv t‖ ^ 2 * ‖Rv t‖ ^ 2) := by
      ext t
      rw [norm_mul, mul_pow]
    rw [this]
    exact hCont_Qv.mul hCont_Rv
  have hInt_QR : IntegrableOn (fun t => ‖Qv t * Rv t‖ ^ 2) U :=
    hCont_QR.integrableOn_Icc.mono_set hU_sub
  have hInt_Rv : IntegrableOn (fun t => ‖Rv t‖ ^ 2) U :=
    hCont_Rv.integrableOn_Icc.mono_set hU_sub
  have hInt_exp_Rv : IntegrableOn (fun t => Real.exp (-2 * (alpha η (j.val + 1)) * v / H) * ‖Rv t‖ ^ 2) U :=
    hInt_Rv.const_mul _
  have h_step1 : ∫ t in U, ‖Qv t * Rv t‖ ^ 2 ≤
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H) * ∫ t in U, ‖Rv t‖ ^ 2 := by
    have h1 := setIntegral_mono_on hInt_QR hInt_exp_Rv hU_meas h_pt_le
    rw [MeasureTheory.integral_const_mul] at h1
    exact h1
  have h_step2 : ∫ t in U, ‖Rv t‖ ^ 2 ≤ ∫ t in (-T)..T, ‖Rv t‖ ^ 2 := by
    apply setIntegral_norm_sq_dirichletPoly_le b_omega (cofactorRange X H v) (by
      intro n hn
      unfold cofactorRange at hn
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1) T hT_nonneg U hU_meas hU_sub
  have hQ_ge1 : 1 ≤ Q := by
    have : 2 ≤ Q := (S.two_le_P j).trans (S.P_le_Q j)
    omega
  have hv_le : v ≤ ⌈H * Real.log Q⌉₊ := (Finset.mem_Icc.mp hv).2
  have h_step3 := integral_norm_sq_Rv_le X P Q H v b hb T hT_nonneg hX hQ_ge1 hH hv_le
  calc ∫ t in U, ‖Qv t * Rv t‖ ^ 2
    _ ≤ Real.exp (-2 * (alpha η (j.val + 1)) * v / H) * ∫ t in U, ‖Rv t‖ ^ 2 := h_step1
    _ ≤ Real.exp (-2 * (alpha η (j.val + 1)) * v / H) * ∫ t in (-T)..T, ‖Rv t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h_step2 (by positivity)
    _ ≤ Real.exp (-2 * (alpha η (j.val + 1)) * v / H) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) :=
      mul_le_mul_of_nonneg_left h_step3 (by positivity)

/-- Sum over v ∈ I_j of the bilinear bounds on T_j. -/
lemma RangeSystem.sum_integral_norm_sq_QR_v_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hX : 1 ≤ X) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T)
    (j : Fin J) (hH : 1 ≤ S.Hj hJ j) (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) :
    let P := S.P j
    let Q := S.Q j
    let H := S.Hj hJ j
    let U := S.Tset hJ β X T₀ T j
    (∑ v ∈ S.Ij hJ j,
      ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      (∑ v ∈ S.Ij hJ j, Real.exp (-2 * (alpha η (j.val + 1)) * v / H)) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) := by
  intro P Q H U
  have h_term : ∀ v ∈ S.Ij hJ j,
      ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        Real.exp (-2 * (alpha η (j.val + 1)) * v / H) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) :=
    fun v hv => S.integral_norm_sq_QR_v_le hJ β X T₀ T hX hT0 hT j hH b hb v hv
  have h_sum := Finset.sum_le_sum h_term
  rw [← Finset.sum_mul] at h_sum
  exact h_sum

/-- Uniform bilinear moment bound on level sets T_j with absolute constant C = 12 + 24π. -/
theorem integral_norm_sq_QR_v_le_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
      (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) (b : ℕ → ℂ) (v : ℕ),
      1 ≤ X → 0 ≤ T₀ → T₀ ≤ T → 1 ≤ S.Hj hJ j → (∀ m, ‖b m‖ ≤ 1) → v ∈ S.Ij hJ j →
      let P := S.P j
      let Q := S.Q j
      let H := S.Hj hJ j
      let U := S.Tset hJ β X T₀ T j
      ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        Real.exp (-2 * (alpha η (j.val + 1)) * v / H) * (C * (T / ((X : ℝ) / Q) + 1)) := by
  use 12 + 24 * Real.pi
  refine ⟨by positivity, ?_⟩
  intro J η S hJ β X T₀ T j b v hX hT0 hT hH hb hv
  exact S.integral_norm_sq_QR_v_le hJ β X T₀ T hX hT0 hT j hH b hb v hv

/-- Mean square bound for F on T_j via Montgomery's mean value theorem with uniform absolute constant C = 36π + 2. -/
theorem RangeSystem.integral_Tset_norm_sq_F_le_uniform {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) (hX : 1 ≤ X) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T) :
    ∫ t in S.Tset hJ β X T₀ T j, ‖F β J S.R X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (36 * Real.pi + 2) * (T / (X : ℝ) + 1) := by
  have hT_nonneg : 0 ≤ T := hT0.trans hT
  have h_sub := S.Tset_subset_Icc_neg hJ β X T₀ T j hT0 hT
  have h_meas := S.measurableSet_Tset hJ β X T₀ T j
  have h_pos_n : ∀ n ∈ Finset.Ioc X (2 * X), 0 < n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    omega
  have h_set_le := setIntegral_norm_sq_dirichletPoly_le (coeffF β J S.R X) (Finset.Ioc X (2 * X))
    h_pos_n T hT_nonneg (S.Tset hJ β X T₀ T j) h_meas h_sub
  have h_coeff_le : ∀ n, ‖coeffF β J S.R X n‖ ≤ 1 := norm_coeffF_le_one β J S.R X
  have h_F_le := integral_norm_sq_F_le_mul (coeffF β J S.R X) h_coeff_le X hX T hT_nonneg
  unfold F
  exact h_set_le.trans h_F_le

end Erdos1201.MR
