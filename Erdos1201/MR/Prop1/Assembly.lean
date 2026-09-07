import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Ranges
import Erdos1201.MR.Setup
import Erdos1201.MR.Prop1.Split
import Erdos1201.MR.Prop1.E1Unsifted
import Erdos1201.MR.Prop1.EjUnsifted
import Erdos1201.MR.Prop1.UsetAssembly
import Erdos1201.MR.Sieve.RangeSieveUpperHR
import Erdos1201.MR.Parseval.WindowEnergy

open MeasureTheory Classical
open scoped BigOperators Real

namespace Erdos1201.MR

/-!
# Proposition 1 Assembly for the Unsifted Polynomial

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the assembly of Proposition 1 of Matomäki–Radziwiłł for the unsifted polynomial `Fu β X`:
1. Continuity and integrability of `Fu` on compact intervals;
2. Decomposition of the mean square integral over $[T_0, T]$ into the sum of integrals over level sets $T_j$ and the exceptional set $U$;
3. Sum of level set integrals $\sum_j \int_{T_j} \|Fu\|^2$ bounded by the primary error term, decay terms, prime reciprocals, and sieve bounds;
4. The master level-set sum theorem `RangeSystem.integral_sum_Tset_norm_sq_Fu_le`;
5. The master Proposition 1 theorem for the unsifted polynomial `RangeSystem.integral_Icc_norm_sq_Fu_le`.
-/

/-- Continuity of $t \mapsto Fu(\beta, X, 1 + it)$ in $t$. -/
lemma continuous_Fu (β : ℝ) (X : ℕ) :
    Continuous (fun t : ℝ => Fu β X ((1 : ℂ) + t * Complex.I)) := by
  unfold Fu
  apply continuous_dirichletPoly_one_line
  intro n hn
  rw [Finset.mem_Ioc] at hn
  omega

/-- Continuity of $t \mapsto \|Fu(\beta, X, 1 + it)\|^2$ in $t$. -/
lemma continuous_norm_sq_Fu (β : ℝ) (X : ℕ) :
    Continuous (fun t : ℝ => ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2) :=
  (continuous_Fu β X).norm.pow 2

/-- Integrability of $t \mapsto \|Fu(\beta, X, 1 + it)\|^2$ on any compact interval $[T_0, T]$. -/
lemma integrableOn_norm_sq_Fu_Icc (β : ℝ) (X : ℕ) (T₀ T : ℝ) :
    IntegrableOn (fun t : ℝ => ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2) (Set.Icc T₀ T) :=
  (continuous_norm_sq_Fu β X).integrableOn_Icc

/-- Decomposition of the mean square integral of $F_u$ over $[T_0, T]$ into the sum of integrals
over the disjoint level sets $T_j$ and the integral over the exceptional set $U$. -/
theorem RangeSystem.integral_Icc_eq_sum_Tset_add_Uset_Fu {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hT : T₀ ≤ T) :
    ∫ t in Set.Icc T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 =
      (∑ j : Fin J, ∫ t in S.Tset hJ β X T₀ T j, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
      ∫ t in S.Uset hJ β X T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
  have _ := hT
  let f : ℝ → ℝ := fun t => ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2
  have hf_Icc : IntegrableOn f (Set.Icc T₀ T) := integrableOn_norm_sq_Fu_Icc β X T₀ T
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

/-- Upper bound on $1 / (j+1)^2 \le 1/j - 1/(j+1)$ for $j \ge 1$. -/
lemma inv_sq_succ_le_sub (j : ℕ) (hj : 1 ≤ j) :
    1 / (((j + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ) := by
  have hj_pos : 0 < (j : ℝ) := by positivity
  have hj1_pos : 0 < ((j + 1 : ℕ) : ℝ) := by positivity
  have h_sub : 1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ) = 1 / ((j : ℝ) * ((j + 1 : ℕ) : ℝ)) := by
    rw [div_sub_div _ _ hj_pos.ne' hj1_pos.ne']
    push_cast
    ring
  rw [h_sub]
  have h_le : (j : ℝ) * ((j + 1 : ℕ) : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by
    have : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j ≤ j + 1)
    nlinarith
  have h_prod_pos : 0 < (j : ℝ) * ((j + 1 : ℕ) : ℝ) := mul_pos hj_pos hj1_pos
  exact one_div_le_one_div_of_le h_prod_pos h_le

/-- Telescoping sum of $f(j) - f(j+1)$. -/
lemma sum_Ico_sub_telescope (f : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.Ico 1 (n + 1), (f j - f (j + 1))) = f 1 - f (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    rw [ih]
    ring

/-- Sum of $1 / (j+1)^2$ over $j \in [1, J)$ is at most 1. -/
lemma sum_Ico_inv_sq_le_one (J : ℕ) :
    (∑ j ∈ Finset.Ico 1 J, (1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ 2)) ≤ 1 := by
  rcases J with _ | J
  · simp
  · have h_term : ∀ j ∈ Finset.Ico 1 (J + 1), (1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (j : ℝ) - 1 / ((j + 1 : ℕ) : ℝ) := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      exact inv_sq_succ_le_sub j hj.1
    have h_sum := Finset.sum_le_sum h_term
    have h_tel := sum_Ico_sub_telescope (fun n => 1 / (n : ℝ)) J
    rw [h_tel] at h_sum
    have h_pos : 0 ≤ 1 / ((J + 1 : ℕ) : ℝ) := by positivity
    simp only [Nat.cast_one, div_one] at h_sum
    linarith

/-- Re-indexing a sum over positive elements of `Fin J` to `Ico 1 J`. -/
lemma sum_Fin_pos_eq_Ico {J : ℕ} (f : ℕ → ℝ) :
    (∑ j ∈ (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val), f j.val) = ∑ k ∈ Finset.Ico 1 J, f k := by
  have h_map : Finset.map ⟨Fin.val, Fin.val_injective⟩ ((Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val)) = Finset.Ico 1 J := by
    ext k
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk,
      Finset.mem_Ico]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨hj, j.isLt⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨k, h2⟩, h1, rfl⟩
  rw [← h_map, Finset.sum_map]
  rfl

/-- The sum of $1 / (j+1)^2$ over positive $j : \text{Fin } J$ is at most 1. -/
lemma sum_Fin_inv_sq_le_one (J : ℕ) :
    (∑ j ∈ (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val), (1 : ℝ) / (((j.val + 1 : ℕ) : ℝ) ^ 2)) ≤ 1 := by
  have h := sum_Fin_pos_eq_Ico (fun k => (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2)) (J := J)
  rw [h]
  exact sum_Ico_inv_sq_le_one J

/-- Splitting a sum over `Fin J` into $j = 0$ and $j \ge 1$. -/
lemma sum_univ_eq_zero_add_filter {J : ℕ} (hJ : 0 < J) (f : Fin J → ℝ) :
    (∑ j : Fin J, f j) = f ⟨0, hJ⟩ + ∑ j ∈ (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val), f j := by
  have h_split : (Finset.univ : Finset (Fin J)) = {⟨0, hJ⟩} ∪ (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val) := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, true_and]
    constructor
    · intro _
      rcases j with ⟨val, hval⟩
      by_cases h0 : val = 0
      · left; ext; exact h0
      · right; exact Nat.one_le_iff_ne_zero.mpr h0
    · intro _; trivial
  have h_disj : Disjoint ({⟨0, hJ⟩} : Finset (Fin J)) ((Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val)) := by
    rw [Finset.disjoint_singleton_left]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    norm_num
  nth_rw 1 [h_split]
  rw [Finset.sum_union h_disj, Finset.sum_singleton]

/-- The predecessor shift mapping $j \mapsto j - 1$ embeds into `Fin J`. -/
lemma sum_Fin_succ_le_univ {J : ℕ} (g : Fin J → ℝ) (hg : ∀ k, 0 ≤ g k) :
    (∑ j ∈ (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val),
      g ⟨j.val - 1, by omega⟩) ≤ ∑ k : Fin J, g k := by
  let s := (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val)
  let t := (Finset.univ : Finset (Fin J)).filter (fun k => k.val + 1 < J)
  have h_bij : (∑ j ∈ s, g ⟨j.val - 1, by omega⟩) = ∑ k ∈ t, g k := by
    apply Finset.sum_bij (fun j hj => ⟨j.val - 1, by
      rw [Finset.mem_filter] at hj
      omega⟩)
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨Finset.mem_univ _, by dsimp; omega⟩
    · intro j1 hj1 j2 hj2 h_eq
      rw [Finset.mem_filter] at hj1 hj2
      have h1 : 1 ≤ j1.val := hj1.2
      have h2 : 1 ≤ j2.val := hj2.2
      have h_val : (⟨j1.val - 1, by omega⟩ : Fin J).val = (⟨j2.val - 1, by omega⟩ : Fin J).val :=
        congrArg Fin.val h_eq
      dsimp at h_val
      ext
      omega
    · intro k hk
      rw [Finset.mem_filter] at hk
      refine ⟨⟨k.val + 1, by omega⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, by dsimp; omega⟩
      · ext
        dsimp
    · intro a ha
      rfl
  rw [h_bij]
  apply Finset.sum_le_univ_sum_of_nonneg
  intro k
  exact hg k

/-- Bound $1 / P_j \le (j+2)^6 / \sqrt{P_j}$. -/
lemma one_div_Pj_le_sq {J : ℕ} {η : ℝ} (S : RangeSystem J η) (j : Fin J) :
    1 / (S.P j : ℝ) ≤ (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j)) := by
  have hP : 2 ≤ S.P j := S.two_le_P j
  have hP_pos : 0 < (S.P j : ℝ) := by exact_mod_cast (by omega : 0 < S.P j)
  have hsqrt_pos : 0 < Real.sqrt (S.P j) := Real.sqrt_pos_of_pos hP_pos
  have hP1 : (1 : ℝ) ≤ (S.P j : ℝ) := by exact_mod_cast (by omega : 1 ≤ S.P j)
  have hsqrt_le : Real.sqrt (S.P j) ≤ (S.P j : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc (S.P j : ℝ) = (S.P j : ℝ) * 1 := by ring
      _ ≤ (S.P j : ℝ) * (S.P j : ℝ) := mul_le_mul_of_nonneg_left hP1 (by positivity)
      _ = (S.P j : ℝ) ^ 2 := by ring
  have h_inv : 1 / (S.P j : ℝ) ≤ 1 / Real.sqrt (S.P j) :=
    one_div_le_one_div_of_le hsqrt_pos hsqrt_le
  have h_num : (1 : ℝ) ≤ (((j.val + 2 : ℕ) : ℝ) ^ 6) := by
    have : (1 : ℝ) ≤ ((j.val + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j.val + 2)
    calc (1 : ℝ) = (1 : ℝ) ^ 6 := by norm_num
      _ ≤ ((j.val + 2 : ℕ) : ℝ) ^ 6 := by gcongr
  calc 1 / (S.P j : ℝ)
    _ ≤ 1 / Real.sqrt (S.P j) := h_inv
    _ = 1 * (1 / Real.sqrt (S.P j)) := by ring
    _ ≤ (((j.val + 2 : ℕ) : ℝ) ^ 6) * (1 / Real.sqrt (S.P j)) :=
      mul_le_mul_of_nonneg_right h_num (by positivity)
    _ = (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j)) := by ring

/-- Helper for the $Q_i$ decay term for $j \ge 1$. -/
noncomputable def termQ {J : ℕ} {η : ℝ} (S : RangeSystem J η) (j : Fin J) : ℝ :=
  if h : 1 ≤ j.val then
    ((j.val + 1 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.Q ⟨j.val - 1, by omega⟩)
  else 0

lemma termQ_eq {J : ℕ} {η : ℝ} (S : RangeSystem J η) (j : Fin J) (hj : 1 ≤ j.val) :
    termQ S j = ((j.val + 1 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.Q ⟨j.val - 1, by omega⟩) := by
  unfold termQ
  split_ifs
  rfl

/-- The decay term $(j+1)^6 / \sqrt{Q_i}$ is bounded by $(i+2)^6 / \sqrt{P_i}$. -/
lemma termQ_le_term {J : ℕ} {η : ℝ} (S : RangeSystem J η) (j : Fin J) (hj : 1 ≤ j.val) :
    let i : Fin J := ⟨j.val - 1, by omega⟩
    termQ S j ≤ (((i.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P i)) := by
  rw [termQ_eq S j hj]
  intro i
  have h_val : j.val + 1 = i.val + 2 := by
    dsimp [i]
    omega
  have h_num : (((j.val + 1 : ℕ) : ℝ) ^ 6) = (((i.val + 2 : ℕ) : ℝ) ^ 6) := by
    congr 1
    exact_mod_cast h_val
  rw [h_num]
  have hPQ : S.P i ≤ S.Q i := S.P_le_Q i
  have hP2 : 2 ≤ S.P i := S.two_le_P i
  have hP_pos : 0 < (S.P i : ℝ) := by exact_mod_cast (by omega : 0 < S.P i)
  have hsqrt_pos : 0 < Real.sqrt (S.P i) := Real.sqrt_pos_of_pos hP_pos
  have hPQ_r : (S.P i : ℝ) ≤ (S.Q i : ℝ) := by exact_mod_cast hPQ
  have hsqrt_le : Real.sqrt (S.P i) ≤ Real.sqrt (S.Q i) :=
    Real.sqrt_le_sqrt hPQ_r
  have h_inv : 1 / Real.sqrt (S.Q i) ≤ 1 / Real.sqrt (S.P i) :=
    one_div_le_one_div_of_le hsqrt_pos hsqrt_le
  have h_pos : 0 ≤ ((i.val + 2 : ℕ) : ℝ) ^ 6 := by positivity
  calc (((i.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.Q i))
    _ = (((i.val + 2 : ℕ) : ℝ) ^ 6) * (1 / Real.sqrt (S.Q i)) := by ring
    _ ≤ (((i.val + 2 : ℕ) : ℝ) ^ 6) * (1 / Real.sqrt (S.P i)) :=
      mul_le_mul_of_nonneg_left h_inv h_pos
    _ = (((i.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P i)) := by ring

/-- The sum of $(j+1)^6 / \sqrt{Q_i}$ over positive $j$ is bounded by $\sum_k (k+2)^6 / \sqrt{P_k}$. -/
lemma sum_termQ_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) :
    (∑ j ∈ (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val), termQ S j) ≤
    ∑ k : Fin J, (((k.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P k)) := by
  let g : Fin J → ℝ := fun k => (((k.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P k))
  have hg_nonneg : ∀ k, 0 ≤ g k := fun k => by positivity
  have h_le : ∀ j ∈ (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val),
      termQ S j ≤ g ⟨j.val - 1, by omega⟩ := by
    intro j hj
    rw [Finset.mem_filter] at hj
    exact termQ_le_term S j hj.2
  have h_sum := Finset.sum_le_sum h_le
  have h_univ := sum_Fin_succ_le_univ g hg_nonneg
  exact h_sum.trans h_univ

/-- The sum of $1 / P_j$ over positive $j$ is bounded by $\sum_k (k+2)^6 / \sqrt{P_k}$. -/
lemma sum_termC_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) :
    (∑ j ∈ (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val),
      (1 / (S.P j : ℝ))) ≤
    ∑ k : Fin J, (((k.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P k)) := by
  let g : Fin J → ℝ := fun k => (((k.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P k))
  have h_le : ∀ j ∈ (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val),
      1 / (S.P j : ℝ) ≤ g j := by
    intro j _
    exact one_div_Pj_le_sq S j
  have h_sum := Finset.sum_le_sum h_le
  apply h_sum.trans
  apply Finset.sum_le_univ_sum_of_nonneg
  intro k
  positivity

/-- Halberstam–Richert sieve bound on the unsifted fraction on $(X, 2X]$. -/
lemma card_unsifted_div_X_le' :
    ∃ C : ℝ, 0 < C ∧ ∀ (X P Q : ℕ), 2 ≤ P → P ≤ Q → 2 ≤ X → Q ≤ X →
      (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / (X : ℝ) ≤
        C * Real.log P / Real.log Q := by
  obtain ⟨C, hC_pos, h_hr⟩ := card_no_prime_factor_in_Icc_le_hr'
  use C, hC_pos
  intro X P Q hP hPQ hX hQX
  have h_eq : (Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n) =
      (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n) :=
    filter_primeRange_eq_primes X P Q
  rw [h_eq]
  have h_card := h_hr X P Q hP hPQ hX hQX
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have h_div := div_le_div_of_nonneg_right h_card hX_pos.le
  refine h_div.trans ?_
  have : C * (X : ℝ) * Real.log (P : ℝ) / Real.log (Q : ℝ) / (X : ℝ) =
      C * Real.log (P : ℝ) / Real.log (Q : ℝ) := by
    calc C * (X : ℝ) * Real.log (P : ℝ) / Real.log (Q : ℝ) / (X : ℝ)
      _ = (C * Real.log (P : ℝ) / Real.log (Q : ℝ)) * (X : ℝ) / (X : ℝ) := by ring
      _ = (C * Real.log (P : ℝ) / Real.log (Q : ℝ)) * ((X : ℝ) / (X : ℝ)) := by ring
      _ = (C * Real.log (P : ℝ) / Real.log (Q : ℝ)) * 1 := by rw [div_self (ne_of_gt hX_pos)]
      _ = C * Real.log (P : ℝ) / Real.log (Q : ℝ) := by ring
  rw [this]

/-- $Q_j \le X$ when $Q_j \le X^\beta$ and $\beta < 1$. -/
lemma Qj_le_X {J : ℕ} {η : ℝ} (S : RangeSystem J η) (j : Fin J) (β : ℝ) (X : ℕ)
    (hβ : β < 1) (hX : 16 ≤ X) (hQX : (S.Q j : ℝ) ≤ (X : ℝ) ^ β) :
    S.Q j ≤ X := by
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have h_rpow : (X : ℝ) ^ β ≤ (X : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1 hβ.le
  rw [Real.rpow_one] at h_rpow
  have h_le : (S.Q j : ℝ) ≤ (X : ℝ) := hQX.trans h_rpow
  exact_mod_cast h_le

/-- The sum of unsifted fractions over all ranges is bounded by $C_{HR} \sum \log P_j / \log Q_j$. -/
lemma sum_unsifted_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (C_HR : ℝ)
    (hHR : ∀ (X P Q : ℕ), 2 ≤ P → P ≤ Q → 2 ≤ X → Q ≤ X →
      (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / (X : ℝ) ≤
        C_HR * Real.log P / Real.log Q)
    (β : ℝ) (X : ℕ) (hβ : β < 1) (hX : 16 ≤ X)
    (hQX_all : ∀ j, (S.Q j : ℝ) ≤ (X : ℝ) ^ β) :
    (∑ j : Fin J, (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange (S.P j) (S.Q j), ¬ p ∣ n)).card : ℝ) / (X : ℝ)) ≤
      C_HR * ∑ j : Fin J, Real.log (S.P j) / Real.log (S.Q j) := by
  have h_term : ∀ j : Fin J,
      (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange (S.P j) (S.Q j), ¬ p ∣ n)).card : ℝ) / (X : ℝ) ≤
        C_HR * Real.log (S.P j) / Real.log (S.Q j) := by
    intro j
    have hP2 : 2 ≤ S.P j := S.two_le_P j
    have hPQ : S.P j ≤ S.Q j := S.P_le_Q j
    have hX2 : 2 ≤ X := by omega
    have hQX : S.Q j ≤ X := Qj_le_X S j β X hβ hX (hQX_all j)
    exact hHR X (S.P j) (S.Q j) hP2 hPQ hX2 hQX
  have h_sum : (∑ j : Fin J, (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange (S.P j) (S.Q j), ¬ p ∣ n)).card : ℝ) / (X : ℝ)) ≤
      ∑ j : Fin J, C_HR * Real.log (S.P j) / Real.log (S.Q j) :=
    Finset.sum_le_sum (fun j _ => h_term j)
  have h_factor : (∑ j : Fin J, C_HR * Real.log (S.P j) / Real.log (S.Q j)) =
      C_HR * ∑ j : Fin J, Real.log (S.P j) / Real.log (S.Q j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_factor] at h_sum
  exact h_sum

/-- Elementary scaling: $T/X \le T/(X/Q)$ when $Q \ge 1$. -/
lemma div_div_self_le {T X Q : ℝ} (hT : 0 ≤ T) (hX : 0 < X) (hQ : 1 ≤ Q) :
    T / X ≤ T / (X / Q) := by
  rw [div_div_eq_mul_div]
  have : T * 1 ≤ T * Q := mul_le_mul_of_nonneg_left hQ hT
  rw [mul_one] at this
  exact div_le_div_of_nonneg_right this hX.le

/-- Linear algebra lemma collecting level-set constants. -/
lemma real_assembly_bound (A B W K L U₀ U_succ C_E1 C_Ej C_HR M C : ℝ)
    (_hA_nonneg : 0 ≤ A) (hB_nonneg : 0 ≤ B) (hBA : B ≤ A)
    (hW_nonneg : 0 ≤ W) (_hK_nonneg : 0 ≤ K) (_hL_nonneg : 0 ≤ L)
    (hU₀_nonneg : 0 ≤ U₀) (hU_succ_nonneg : 0 ≤ U_succ)
    (hU_sum : U₀ + U_succ ≤ C_HR * L)
    (hE1_M : C_E1 ≤ M) (hEj_M : C_Ej ≤ M) (hM_nonneg : 0 ≤ M)
    (hC_2M : 2 * M ≤ C) (hC_MHR : M * C_HR ≤ C)
    (_hE1_nonneg : 0 ≤ C_E1) (_hEj_nonneg : 0 ≤ C_Ej) :
    (C_E1 * A * W + C_E1 * B * U₀) + C_Ej * B * (W + 2 * K + U_succ) ≤
      C * (A * W + B * (K + L)) := by
  have h1 : C_E1 * A * W ≤ M * A * W := by
    have : 0 ≤ A * W := by positivity
    nlinarith
  have h2 : C_Ej * B * W ≤ M * A * W := by
    have h_BW : B * W ≤ A * W := mul_le_mul_of_nonneg_right hBA hW_nonneg
    have : C_Ej * (B * W) ≤ M * (B * W) := by
      have : 0 ≤ B * W := by positivity
      nlinarith
    have : M * (B * W) ≤ M * (A * W) := mul_le_mul_of_nonneg_left h_BW hM_nonneg
    linarith
  have h3 : 2 * C_Ej * B * K ≤ C * B * K := by
    have : 0 ≤ B * K := by positivity
    calc 2 * C_Ej * B * K = C_Ej * (2 * (B * K)) := by ring
      _ ≤ M * (2 * (B * K)) := by nlinarith
      _ = (2 * M) * (B * K) := by ring
      _ ≤ C * (B * K) := mul_le_mul_of_nonneg_right hC_2M (by positivity)
      _ = C * B * K := by ring
  have h4 : C_E1 * B * U₀ + C_Ej * B * U_succ ≤ C * B * L := by
    have h_U : C_E1 * U₀ + C_Ej * U_succ ≤ M * (C_HR * L) := by
      calc C_E1 * U₀ + C_Ej * U_succ
        _ ≤ M * U₀ + M * U_succ := by
          have : C_E1 * U₀ ≤ M * U₀ := mul_le_mul_of_nonneg_right hE1_M hU₀_nonneg
          have : C_Ej * U_succ ≤ M * U_succ := mul_le_mul_of_nonneg_right hEj_M hU_succ_nonneg
          linarith
        _ = M * (U₀ + U_succ) := by ring
        _ ≤ M * (C_HR * L) := mul_le_mul_of_nonneg_left hU_sum hM_nonneg
    calc C_E1 * B * U₀ + C_Ej * B * U_succ
      _ = B * (C_E1 * U₀ + C_Ej * U_succ) := by ring
      _ ≤ B * (M * (C_HR * L)) := mul_le_mul_of_nonneg_left h_U hB_nonneg
      _ = (M * C_HR) * (B * L) := by ring
      _ ≤ C * (B * L) := mul_le_mul_of_nonneg_right hC_MHR (by positivity)
      _ = C * B * L := by ring
  calc (C_E1 * A * W + C_E1 * B * U₀) + C_Ej * B * (W + 2 * K + U_succ)
    _ = (C_E1 * A * W + C_Ej * B * W) + (2 * C_Ej * B * K) + (C_E1 * B * U₀ + C_Ej * B * U_succ) := by ring
    _ ≤ (M * A * W + M * A * W) + (C * B * K) + (C * B * L) := by linarith [h1, h2, h3, h4]
    _ = (2 * M) * (A * W) + C * B * (K + L) := by ring
    _ ≤ C * (A * W) + C * B * (K + L) := by
      have : 0 ≤ A * W := by positivity
      have : (2 * M) * (A * W) ≤ C * (A * W) := mul_le_mul_of_nonneg_right hC_2M (by positivity)
      linarith
    _ = C * (A * W + B * (K + L)) := by ring

/-- Algebraic assembly lemma combining the level sets bound and exceptional set bound. -/
lemma real_prop1_total_bound (A B W UX K L C_T C_U C : ℝ)
    (hB_nonneg : 0 ≤ B) (hBA : B ≤ A) (hW_nonneg : 0 ≤ W) (hUX_nonneg : 0 ≤ UX)
    (hKL_nonneg : 0 ≤ K + L)
    (hCT_le : C_T ≤ C) (hCU_le : C_U ≤ C) (_hCT_nonneg : 0 ≤ C_T) (hCU_nonneg : 0 ≤ C_U)
    (I_T I_U : ℝ)
    (hI_T : I_T ≤ C_T * (A * W + B * (K + L)))
    (hI_U : I_U ≤ C_U * (B * UX)) :
    I_T + I_U ≤ C * (A * (W + UX) + B * (K + L)) := by
  have hA_nonneg : 0 ≤ A := hB_nonneg.trans hBA
  have hAW_nonneg : 0 ≤ A * W := mul_nonneg hA_nonneg hW_nonneg
  have hAUX_nonneg : 0 ≤ A * UX := mul_nonneg hA_nonneg hUX_nonneg
  have hBKL_nonneg : 0 ≤ B * (K + L) := mul_nonneg hB_nonneg hKL_nonneg
  have hBUX_le : B * UX ≤ A * UX := mul_le_mul_of_nonneg_right hBA hUX_nonneg
  have hCU_BUX_le : C_U * (B * UX) ≤ C_U * (A * UX) := mul_le_mul_of_nonneg_left hBUX_le hCU_nonneg
  have h1 : C_T * (A * W) ≤ C * (A * W) := mul_le_mul_of_nonneg_right hCT_le hAW_nonneg
  have h2 : C_U * (A * UX) ≤ C * (A * UX) := mul_le_mul_of_nonneg_right hCU_le hAUX_nonneg
  have h3 : C_T * (B * (K + L)) ≤ C * (B * (K + L)) := mul_le_mul_of_nonneg_right hCT_le hBKL_nonneg
  calc I_T + I_U
    _ ≤ C_T * (A * W + B * (K + L)) + C_U * (B * UX) := add_le_add hI_T hI_U
    _ ≤ C_T * (A * W + B * (K + L)) + C_U * (A * UX) := by linarith [hCU_BUX_le]
    _ = C_T * (A * W) + C_U * (A * UX) + C_T * (B * (K + L)) := by ring
    _ ≤ C * (A * W) + C * (A * UX) + C * (B * (K + L)) := by linarith [h1, h2, h3]
    _ = C * (A * (W + UX) + B * (K + L)) := by ring


/-- Master bound for the sum of integrals of $\|F_u\|^2$ over all level sets $T_j$.
This combines the $j = 0$ bound (`integral_Tset_zero_le_unsifted`), the $j \ge 1$ bound
(`integral_Tset_succ_le_unsifted`), and the Halberstam–Richert sieve bound (`card_no_prime_factor_in_Icc_le_hr'`). -/
theorem RangeSystem.integral_sum_Tset_norm_sq_Fu_le {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ),
      3 / 4 ≤ β → β < 1 → 16 ≤ X → (Real.log X) ^ (1 / 15 : ℝ) ≤ T₀ → T₀ ≤ T → T ≤ X →
      (∀ j, (S.Q j : ℝ) ≤ (X : ℝ) ^ β) → (∀ j, (S.Q j : ℝ) ^ 4 ≤ X) →
      (∀ j, 2 ≤ S.Hj hJ j ∧ S.Hj hJ j ≤ Real.sqrt (S.P j)) → (∀ j, 2 ≤ Real.log (S.P j)) → (∀ j, 2 ≤ Real.log (Real.log (S.Q j))) →
      (∑ j : Fin J, ∫ t in S.Tset hJ β X T₀ T j, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C * ((T / ((X : ℝ) / S.Q ⟨0, hJ⟩) + 1) * ((Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η))
          + (T / X + 1) * ∑ j : Fin J, (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j) + Real.log (S.P j) / Real.log (S.Q j))) := by
  obtain ⟨C_E1, hC_E1_pos, hE1⟩ := integral_Tset_zero_le_unsifted hη0 hη
  obtain ⟨C_Ej, hC_Ej_pos, hEj⟩ := integral_Tset_succ_le_unsifted hη0 hη
  obtain ⟨C_HR, hC_HR_pos, hHR⟩ := card_unsifted_div_X_le'
  let M := max C_E1 C_Ej
  have hM_pos : 0 < M := lt_of_lt_of_le hC_E1_pos (le_max_left _ _)
  let C := max (2 * M) (M * C_HR) + 1
  have hC_pos : 0 < C := by
    have : 0 < max (2 * M) (M * C_HR) := lt_of_lt_of_le (by positivity) (le_max_left _ _)
    linarith
  have h2M_le : 2 * M ≤ C := by
    have : 2 * M ≤ max (2 * M) (M * C_HR) := le_max_left _ _
    linarith
  have hMHR_le : M * C_HR ≤ C := by
    have : M * C_HR ≤ max (2 * M) (M * C_HR) := le_max_right _ _
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro J S hJ β X T₀ T hβ hβ1 hX hT0_bound hT0T hTX hQX_all hQ4 hH hP hloglogQ
  have hX_ge2 : 2 ≤ X := by omega
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hT0_nonneg : 0 ≤ T₀ := by
    have : 0 ≤ (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) := by positivity
    exact this.trans hT0_bound
  have hT_nonneg : 0 ≤ T := hT0_nonneg.trans hT0T
  have hQ0_ge1 : (1 : ℝ) ≤ (S.Q ⟨0, hJ⟩ : ℝ) := by
    have : 1 ≤ S.Q ⟨0, hJ⟩ := by
      have := S.P_le_Q ⟨0, hJ⟩
      have := S.two_le_P ⟨0, hJ⟩
      omega
    exact_mod_cast this
  let A := T / ((X : ℝ) / S.Q ⟨0, hJ⟩) + 1
  let B := T / (X : ℝ) + 1
  let W := (Real.log (S.Q ⟨0, hJ⟩ : ℝ)) ^ (1 / 3 : ℝ) / (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η)
  let K := ∑ k : Fin J, (((k.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P k))
  let L := ∑ j : Fin J, Real.log (S.P j) / Real.log (S.Q j)
  let U (j : Fin J) := (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange (S.P j) (S.Q j), ¬ p ∣ n)).card : ℝ) / (X : ℝ)
  let U₀ := U ⟨0, hJ⟩
  set s_succ := (Finset.univ : Finset (Fin J)).filter (fun j => 1 ≤ j.val)
  let U_succ := ∑ j ∈ s_succ, U j
  have hA_nonneg : 0 ≤ A := by positivity
  have hB_nonneg : 0 ≤ B := by positivity
  have hBA : B ≤ A := by
    have := div_div_self_le hT_nonneg hX_pos hQ0_ge1
    dsimp [A, B]
    linarith
  have hW_nonneg : 0 ≤ W := by positivity
  have hK_nonneg : 0 ≤ K := Finset.sum_nonneg (fun _ _ => by positivity)
  have hL_nonneg : 0 ≤ L := Finset.sum_nonneg (fun _ _ => by positivity)
  have hU₀_nonneg : 0 ≤ U₀ := by positivity
  have hU_succ_nonneg : 0 ≤ U_succ := Finset.sum_nonneg (fun _ _ => by positivity)
  have h_U_split : U₀ + U_succ = ∑ j : Fin J, U j := (sum_univ_eq_zero_add_filter hJ U).symm
  have hU_sum : U₀ + U_succ ≤ C_HR * L := by
    rw [h_U_split]
    exact sum_unsifted_le S C_HR hHR β X hβ1 hX hQX_all
  have h_E1_bound := hE1 J S hJ β X T₀ T hβ hβ1 hX_ge2 hT0_nonneg hT0T hQX_all (hQ4 ⟨0, hJ⟩)
    (by linarith [(hH ⟨0, hJ⟩).1]) (hH ⟨0, hJ⟩).2
  have h_E1_bound' : ∫ t in S.Tset hJ β X T₀ T ⟨0, hJ⟩, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      C_E1 * A * W + C_E1 * B * U₀ := by
    refine h_E1_bound.trans (le_of_eq ?_)
    dsimp [A, B, W, U₀, U]
    ring
  have h_succ_bound : ∀ (j : Fin J) (hj : j ∈ s_succ),
      ∫ t in S.Tset hJ β X T₀ T j, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C_Ej * B * (W * (1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) + termQ S j + 1 / (S.P j : ℝ) + U j) := by
    intro j hj
    have hj_ge : 1 ≤ j.val := (Finset.mem_filter.mp hj).2
    have hi_bound : j.val - 1 < J := by omega
    let i : Fin J := ⟨j.val - 1, hi_bound⟩
    have hi_succ : i.val + 1 = j.val := by
      show j.val - 1 + 1 = j.val
      omega
    have h_app := hEj J S hJ β X T₀ T j i hi_succ hβ hβ1 hX_ge2 hT0_nonneg hT0T hTX hQX_all hH hP hloglogQ (hQ4 j)
    have h_termQ_rw : ((j.val + 1 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.Q i) = termQ S j := by
      rw [termQ_eq S j hj_ge]
    rw [h_termQ_rw] at h_app
    have h_W_rw : (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (((j.val + 1 : ℕ) : ℝ) ^ 2 * (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η)) =
        W * (1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) := by
      dsimp [W]
      ring
    rw [h_W_rw] at h_app
    exact h_app
  have h_sum_succ_le : (∑ j ∈ s_succ, ∫ t in S.Tset hJ β X T₀ T j, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      ∑ j ∈ s_succ, (C_Ej * B * (W * (1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) + termQ S j + 1 / (S.P j : ℝ) + U j)) :=
    Finset.sum_le_sum h_succ_bound
  have h_sum_succ : (∑ j ∈ s_succ, ∫ t in S.Tset hJ β X T₀ T j, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      C_Ej * B * (W + 2 * K + U_succ) := by
    refine h_sum_succ_le.trans ?_
    rw [← Finset.mul_sum]
    have h_split_sum : (∑ j ∈ s_succ, (W * (1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) + termQ S j + 1 / (S.P j : ℝ) + U j)) =
        W * (∑ j ∈ s_succ, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) +
        (∑ j ∈ s_succ, termQ S j) + (∑ j ∈ s_succ, 1 / (S.P j : ℝ)) + U_succ := by
      simp only [add_assoc]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.mul_sum]
    rw [h_split_sum]
    have h_sq_sum := sum_Fin_inv_sq_le_one J
    have h_termQ := sum_termQ_le S
    have h_termC := sum_termC_le S
    have h_W_le : W * (∑ j ∈ s_succ, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) ≤ W := by
      calc W * (∑ j ∈ s_succ, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2))
        _ ≤ W * 1 := mul_le_mul_of_nonneg_left h_sq_sum hW_nonneg
        _ = W := mul_one W
    have h_inner_le : W * (∑ j ∈ s_succ, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) +
        (∑ j ∈ s_succ, termQ S j) + (∑ j ∈ s_succ, 1 / (S.P j : ℝ)) + U_succ ≤
        W + 2 * K + U_succ := by
      calc W * (∑ j ∈ s_succ, 1 / (((j.val + 1 : ℕ) : ℝ) ^ 2)) +
            (∑ j ∈ s_succ, termQ S j) + (∑ j ∈ s_succ, 1 / (S.P j : ℝ)) + U_succ
        _ ≤ W + K + K + U_succ := by linarith [h_W_le, h_termQ, h_termC]
        _ = W + 2 * K + U_succ := by ring
    have h_pre_nonneg : 0 ≤ C_Ej * B := by positivity
    exact mul_le_mul_of_nonneg_left h_inner_le h_pre_nonneg
  have h_total := sum_univ_eq_zero_add_filter hJ (fun j => ∫ t in S.Tset hJ β X T₀ T j, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2)
  rw [h_total]
  have h_alg := real_assembly_bound A B W K L U₀ U_succ C_E1 C_Ej C_HR M C
    hA_nonneg hB_nonneg hBA hW_nonneg hK_nonneg hL_nonneg hU₀_nonneg hU_succ_nonneg
    hU_sum (le_max_left _ _) (le_max_right _ _) (by positivity) h2M_le hMHR_le
    (by positivity) (by positivity)
  have h_add := add_le_add h_E1_bound' h_sum_succ
  have h_main := h_add.trans h_alg
  refine h_main.trans ?_
  have h_KL_rw : K + L = ∑ j : Fin J, (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j) + Real.log (S.P j) / Real.log (S.Q j)) := by
    dsimp [K, L]
    rw [Finset.sum_add_distrib]
  rw [h_KL_rw]

/-- Master theorem: Proposition 1 of Matomäki–Radziwiłł for the unsifted polynomial `Fu β X`.
This combines the level-set integrals $\sum_j \int_{T_j} \|Fu\|^2$ (`RangeSystem.integral_sum_Tset_norm_sq_Fu_le`)
and the exceptional set integral $\int_U \|Fu\|^2$ (`RangeSystem.integral_Uset_le_unsifted`)
via the partition identity `RangeSystem.integral_Icc_eq_sum_Tset_add_Uset_Fu`. -/
theorem RangeSystem.integral_Icc_norm_sq_Fu_le (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1}))
    {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ),
      3 / 4 ≤ β → β < 1 → 16 ≤ X → (Real.log X) ^ (1 / 15 : ℝ) ≤ T₀ → T₀ ≤ T → T ≤ X →
      (∀ j, (S.Q j : ℝ) ≤ (X : ℝ) ^ β) → (∀ j, (S.Q j : ℝ) ^ 4 ≤ X) →
      (∀ j, 2 ≤ S.Hj hJ j ∧ S.Hj hJ j ≤ Real.sqrt (S.P j)) → (∀ j, 2 ≤ Real.log (S.P j)) → (∀ j, 2 ≤ Real.log (Real.log (S.Q j))) →
      (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) →
      (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) →
      ∫ t in Set.Icc T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * ((T / ((X : ℝ) / S.Q ⟨0, hJ⟩) + 1) * ((Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) + (Real.log X) ^ (-(1 / 400 : ℝ)))
          + (T / X + 1) * ∑ j : Fin J, (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j) + Real.log (S.P j) / Real.log (S.Q j))) := by
  obtain ⟨C_T, hC_T_pos, hT_part⟩ := RangeSystem.integral_sum_Tset_norm_sq_Fu_le hη0 hη
  obtain ⟨C_U, hC_U_pos, hU_part⟩ := RangeSystem.integral_Uset_le_unsifted c₀ K hc₀ hK hζ hholo hη0 hη
  let C := max C_T C_U
  have hC_pos : 0 < C := lt_of_lt_of_le hC_T_pos (le_max_left _ _)
  refine ⟨C, hC_pos, ?_⟩
  intro J S hJ β X T₀ T hβ hβ1 hX hT0_bound hT0T hTX hQX_all hQ4 hH hP hloglogQ hQ_exp hP_last
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hT0_nonneg : 0 ≤ T₀ := by
    have : 0 ≤ (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) := by positivity
    exact this.trans hT0_bound
  have hT_nonneg : 0 ≤ T := hT0_nonneg.trans hT0T
  have hQ0_ge1 : (1 : ℝ) ≤ (S.Q ⟨0, hJ⟩ : ℝ) := by
    have : 1 ≤ S.Q ⟨0, hJ⟩ := by
      have := S.P_le_Q ⟨0, hJ⟩
      have := S.two_le_P ⟨0, hJ⟩
      omega
    exact_mod_cast this
  let A := T / ((X : ℝ) / S.Q ⟨0, hJ⟩) + 1
  let B := T / (X : ℝ) + 1
  let W := (Real.log (S.Q ⟨0, hJ⟩ : ℝ)) ^ (1 / 3 : ℝ) / (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η)
  let UX := (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))
  let K_sum := ∑ k : Fin J, (((k.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P k))
  let L := ∑ j : Fin J, Real.log (S.P j) / Real.log (S.Q j)
  have hB_nonneg : 0 ≤ B := by positivity
  have hBA : B ≤ A := by
    have := div_div_self_le hT_nonneg hX_pos hQ0_ge1
    dsimp [A, B]
    linarith
  have hW_nonneg : 0 ≤ W := by positivity
  have hUX_nonneg : 0 ≤ UX := by positivity
  have hK_nonneg : 0 ≤ K_sum := Finset.sum_nonneg (fun _ _ => by positivity)
  have hL_nonneg : 0 ≤ L := Finset.sum_nonneg (fun _ _ => by positivity)
  have hKL_nonneg : 0 ≤ K_sum + L := add_nonneg hK_nonneg hL_nonneg
  have hCT_le : C_T ≤ C := le_max_left _ _
  have hCU_le : C_U ≤ C := le_max_right _ _
  have hCU_nonneg : 0 ≤ C_U := hC_U_pos.le
  let I_T := ∑ j : Fin J, ∫ t in S.Tset hJ β X T₀ T j, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2
  let I_U := ∫ t in S.Uset hJ β X T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2
  have hI_T : I_T ≤ C_T * (A * W + B * (K_sum + L)) := by
    have h_bound := hT_part J S hJ β X T₀ T hβ hβ1 hX hT0_bound hT0T hTX hQX_all hQ4 hH hP hloglogQ
    refine h_bound.trans (le_of_eq ?_)
    have h_KL_rw : ∑ j : Fin J, (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j) + Real.log (S.P j) / Real.log (S.Q j)) = K_sum + L := by
      dsimp [K_sum, L]
      rw [Finset.sum_add_distrib]
    dsimp [I_T, A, B, W]
    rw [h_KL_rw]
  have hI_U : I_U ≤ C_U * (B * UX) := by
    have hH_left : ∀ j, 2 ≤ S.Hj hJ j := fun j => (hH j).1
    have hH_right : ∀ j, S.Hj hJ j ≤ Real.sqrt (S.P j) := fun j => (hH j).2
    have h_bound := hU_part J S hJ β X T₀ T hβ hβ1 hX hT0_bound hT0T hTX hH_left hQ_exp hH_right hP_last
    refine h_bound.trans (le_of_eq ?_)
    dsimp [I_U, B, UX]
    ring
  have h_split := S.integral_Icc_eq_sum_Tset_add_Uset_Fu hJ β X T₀ T hT0T
  rw [h_split]
  have h_total := real_prop1_total_bound A B W UX K_sum L C_T C_U C
    hB_nonneg hBA hW_nonneg hUX_nonneg hKL_nonneg hCT_le hCU_le hC_T_pos.le hCU_nonneg
    I_T I_U hI_T hI_U
  refine h_total.trans (le_of_eq ?_)
  have h_KL_rw : K_sum + L = ∑ j : Fin J, (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j) + Real.log (S.P j) / Real.log (S.Q j)) := by
    dsimp [K_sum, L]
    rw [Finset.sum_add_distrib]
  dsimp [A, B, W, UX]
  rw [h_KL_rw]

end Erdos1201.MR
