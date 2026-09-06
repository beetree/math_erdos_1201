import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Ranges

open MeasureTheory

/-!
# Decomposition of the Mean Square Integral of $F$ into Levels $T_j$ and Exceptional Set $U$

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes equation (24) of Matomäki–Radziwiłł: the integral of the squared norm
$\|F(1+it)\|^2$ over the height interval $[T_0, T]$ splits into the sum of integrals over
the disjoint level sets $T_j$ and the integral over the exceptional set $U$.
-/

namespace Erdos1201.MR

/-- Continuity of $t \mapsto F(\beta, J, R, X, 1 + it)$ in $t$. -/
lemma continuous_F (β : ℝ) (J : ℕ) (R : Fin J → Finset ℕ) (X : ℕ) :
    Continuous (fun t : ℝ => F β J R X ((1 : ℂ) + t * Complex.I)) := by
  unfold F dirichletPoly
  apply continuous_finsetSum
  intro n hn
  rw [Finset.mem_Ioc] at hn
  have hn_pos : 0 < n := by omega
  have h_term := continuous_cpow_term n hn_pos
  exact continuous_const.mul h_term

/-- Continuity of $t \mapsto \|F(\beta, J, R, X, 1 + it)\|^2$ in $t$. -/
lemma continuous_norm_sq_F (β : ℝ) (J : ℕ) (R : Fin J → Finset ℕ) (X : ℕ) :
    Continuous (fun t : ℝ => ‖F β J R X ((1 : ℂ) + t * Complex.I)‖ ^ 2) :=
  (continuous_F β J R X).norm.pow 2

/-- Integrability of $t \mapsto \|F(\beta, J, R, X, 1 + it)\|^2$ on any compact interval $[T_0, T]$. -/
lemma integrableOn_norm_sq_F_Icc (β : ℝ) (J : ℕ) (R : Fin J → Finset ℕ) (X : ℕ) (T₀ T : ℝ) :
    IntegrableOn (fun t : ℝ => ‖F β J R X ((1 : ℂ) + t * Complex.I)‖ ^ 2) (Set.Icc T₀ T) :=
  (continuous_norm_sq_F β J R X).integrableOn_Icc

/-- Each level set $T_j$ is contained in the interval $[T_0, T]$. -/
lemma RangeSystem.Tset_subset_Icc {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) :
    S.Tset hJ β X T₀ T j ⊆ Set.Icc T₀ T := fun _ ht => ht.1

/-- The exceptional set $U$ is contained in the interval $[T_0, T]$. -/
lemma RangeSystem.Uset_subset_Icc {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) :
    S.Uset hJ β X T₀ T ⊆ Set.Icc T₀ T := fun _ ht => ht.1

/-- The union of all level sets $T_j$ is contained in the interval $[T_0, T]$. -/
lemma RangeSystem.iUnion_Tset_subset_Icc {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) :
    (⋃ j : Fin J, S.Tset hJ β X T₀ T j) ⊆ Set.Icc T₀ T :=
  Set.iUnion_subset (S.Tset_subset_Icc hJ β X T₀ T)

/-- Decomposition of the mean square integral over $[T_0, T]$ into the sum of integrals
over the disjoint level sets $T_j$ and the integral over the exceptional set $U$ (paper (24)). -/
theorem RangeSystem.integral_Icc_eq_sum_Tset_add_Uset {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hT : T₀ ≤ T) (R : Fin J → Finset ℕ) :
    ∫ t in Set.Icc T₀ T, ‖F β J R X ((1 : ℂ) + t * Complex.I)‖ ^ 2 =
      (∑ j : Fin J, ∫ t in S.Tset hJ β X T₀ T j, ‖F β J R X ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
      ∫ t in S.Uset hJ β X T₀ T, ‖F β J R X ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
  have _ := hT
  let f : ℝ → ℝ := fun t => ‖F β J R X ((1 : ℂ) + t * Complex.I)‖ ^ 2
  have hf_Icc : IntegrableOn f (Set.Icc T₀ T) := integrableOn_norm_sq_F_Icc β J R X T₀ T
  rw [S.Icc_eq_iUnion_Tset_union_Uset hJ β X T₀ T]
  have h_disj_union : Disjoint (⋃ j : Fin J, S.Tset hJ β X T₀ T j) (S.Uset hJ β X T₀ T) := by
    rw [Set.disjoint_iUnion_left]
    intro j
    exact S.disjoint_Tset_Uset hJ β X T₀ T j
  have h_meas_U : MeasurableSet (S.Uset hJ β X T₀ T) := S.measurableSet_Uset hJ β X T₀ T
  have hf_union_T : IntegrableOn f (⋃ j : Fin J, S.Tset hJ β X T₀ T j) :=
    hf_Icc.mono_set (S.iUnion_Tset_subset_Icc hJ β X T₀ T)
  have hf_U : IntegrableOn f (S.Uset hJ β X T₀ T) :=
    hf_Icc.mono_set (S.Uset_subset_Icc hJ β X T₀ T)
  rw [setIntegral_union h_disj_union h_meas_U hf_union_T hf_U]
  congr 1
  have h_biUnion_eq : (⋃ j : Fin J, S.Tset hJ β X T₀ T j) =
      ⋃ j ∈ (Finset.univ : Finset (Fin J)), S.Tset hJ β X T₀ T j := by
    simp only [Finset.mem_univ, Set.iUnion_true]
  rw [h_biUnion_eq]
  have h_meas_T : ∀ j ∈ (Finset.univ : Finset (Fin J)), MeasurableSet (S.Tset hJ β X T₀ T j) :=
    fun j _ => S.measurableSet_Tset hJ β X T₀ T j
  have h_pair_T : ((Finset.univ : Finset (Fin J)) : Set (Fin J)).Pairwise
      (Function.onFun Disjoint (S.Tset hJ β X T₀ T)) := by
    intro i _ j _ hij
    exact S.pairwise_disjoint_Tset hJ β X T₀ T hij
  have hf_T : ∀ j ∈ (Finset.univ : Finset (Fin J)), IntegrableOn f (S.Tset hJ β X T₀ T j) :=
    fun j _ => hf_Icc.mono_set (S.Tset_subset_Icc hJ β X T₀ T j)
  exact integral_biUnion_finset (Finset.univ : Finset (Fin J)) h_meas_T h_pair_T hf_T

end Erdos1201.MR
