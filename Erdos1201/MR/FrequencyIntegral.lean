/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Ranges
import Erdos1201.MR.Setup
import Erdos1201.MR.Prop1.Assembly
import Erdos1201.MR.Analysis.MeanValueTheorem
import Erdos1201.MR.Prop1.Ej
import Erdos1201.MR.Decomposition.Lemma12
import Erdos1201.MR.Parseval.Lemma14

open MeasureTheory Set ENNReal
open scoped BigOperators Real

namespace Erdos1201.MR

/-!
# Weighted Frequency Integral Bound for Fu

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

This module proves the bound on the weighted mean square integral of `Fu β X (1 + it)`
appearing in Lemma 14 of Matomäki–Radziwiłł (arXiv:1501.04585v4).
-/

lemma fX_real_freq (β : ℝ) (X n : ℕ) : (starRingEnd ℂ) (fX β X n) = fX β X n := by
  unfold fX Erdos1201.smoothIndicator
  split_ifs <;> simp

lemma conj_cpow_nat_freq {n : ℕ} (hn : 0 < n) (s : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ (-s)) = (n : ℂ) ^ (-(starRingEnd ℂ s)) := by
  have hn_ne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Complex.cpow_neg, Complex.cpow_neg, map_inv₀]
  congr 1
  rw [Complex.cpow_def, Complex.cpow_def]
  simp only [hn_ne, ↓reduceIte]
  rw [← Complex.exp_conj, map_mul]
  congr 1
  have hlog : Complex.log (n : ℂ) = (Real.log (n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log hn_pos.le]
  rw [hlog, Complex.conj_ofReal]

lemma conj_Fu_freq (β : ℝ) (X : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (Fu β X ((1 : ℂ) + (t : ℂ) * Complex.I)) =
      Fu β X ((1 : ℂ) + (-t : ℂ) * Complex.I) := by
  unfold Fu dirichletPoly
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [map_mul, fX_real_freq]
  have hn_pos : 0 < n := by
    rw [Finset.mem_Ioc] at hn
    omega
  have h_conj_s : (starRingEnd ℂ) ((1 : ℂ) + (t : ℂ) * Complex.I) = (1 : ℂ) + (-t : ℂ) * Complex.I := by
    simp
  rw [conj_cpow_nat_freq hn_pos, h_conj_s]

/-- Norm of $Fu$ is symmetric under $t \mapsto -t$. -/
lemma norm_Fu_neg_freq (β : ℝ) (X : ℕ) (t : ℝ) :
    ‖Fu β X ((1 : ℂ) + (-t : ℝ) * Complex.I)‖ = ‖Fu β X ((1 : ℂ) + (t : ℝ) * Complex.I)‖ := by
  have := conj_Fu_freq β X t
  have h := congrArg norm this
  rw [Complex.norm_conj] at h
  have h_cast : ((1 : ℂ) + (-t : ℝ) * Complex.I) = (1 : ℂ) + (-t : ℂ) * Complex.I := by
    push_cast; rfl
  rw [h_cast]
  exact h.symm

/-- The frequency weight function is even. -/
lemma freqWeight_even (X h₁ t : ℝ) :
    min 1 ((X / (h₁ * (-t))) ^ 2) = min 1 ((X / (h₁ * t)) ^ 2) := by
  have : (h₁ * (-t)) = -(h₁ * t) := by ring
  rw [this, div_neg, neg_sq]

/-- Decomposition of $\{t : ℝ \mid c \le |t|\} = (-\infty, -c] \cup [c, \infty)$ for $c \ge 0$. -/
lemma set_abs_ge_eq (c : ℝ) (hc : 0 ≤ c) :
    {t : ℝ | c ≤ |t|} = Iic (-c) ∪ Ici c := by
  ext t
  simp only [mem_ofPred_eq, mem_union, mem_Iic, mem_Ici]
  constructor
  · intro h
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht] at h
      exact Or.inr h
    · rw [abs_of_nonpos ht] at h
      exact Or.inl (by linarith)
  · rintro (h | h)
    · have : 0 ≤ -t := by linarith
      rw [← abs_neg, abs_of_nonneg this]
      linarith
    · have : 0 ≤ t := hc.trans h
      rw [abs_of_nonneg this]
      exact h

lemma disjoint_Iic_Ici_of_pos {c : ℝ} (hc : 0 < c) :
    Disjoint (Iic (-c)) (Ici c) := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  simp only [mem_Iic] at hx1
  simp only [mem_Ici] at hx2
  linarith

lemma integral_Iic_eq_integral_Ici_of_even (f : ℝ → ℝ) (hf : ∀ t, f (-t) = f t) (c : ℝ) :
    ∫ t in Iic (-c), f t = ∫ t in Ici c, f t := by
  have h1 : ∫ t in Iic (-c), f t = ∫ t in Ioi c, f (-t) := by
    rw [integral_comp_neg_Ioi]
  have h2 : ∫ t in Ioi c, f (-t) = ∫ t in Ioi c, f t := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    exact hf t
  have h3 : ∫ t in Ioi c, f t = ∫ t in Ici c, f t := by
    apply setIntegral_congr_set
    exact Ioi_ae_eq_Ici
  rw [h1, h2, h3]

lemma integral_abs_ge_eq_two_mul (f : ℝ → ℝ) (hf : ∀ t, f (-t) = f t) (c : ℝ) (hc : 0 < c)
    (hf_int : IntegrableOn f {t : ℝ | c ≤ |t|}) :
    ∫ t in {t : ℝ | c ≤ |t|}, f t = 2 * ∫ t in Ici c, f t := by
  have hset_eq := set_abs_ge_eq c hc.le
  rw [hset_eq] at hf_int ⊢
  have h_disj := disjoint_Iic_Ici_of_pos hc
  have h_int_add := setIntegral_union h_disj measurableSet_Ici
    (hf_int.mono_set subset_union_left) (hf_int.mono_set subset_union_right)
  rw [h_int_add, integral_Iic_eq_integral_Ici_of_even f hf c]
  ring

lemma one_le_log_X_rpow_fifteen (X : ℕ) (hX : 16 ≤ X) :
    1 ≤ (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) := by
  have h_log_gt := log_X_gt_one hX
  have h_rpow := Real.rpow_le_rpow (by norm_num) h_log_gt.le (by norm_num : (0 : ℝ) ≤ 1 / 15)
  rw [Real.one_rpow] at h_rpow
  exact h_rpow

lemma integrableOn_norm_sq_Fu_mul_wgt (β : ℝ) (X : ℕ) (h₁ : ℝ) (T₀ : ℝ)
    (hX : 1 ≤ X) (hh₁ : 0 < h₁) (hT₀ : 1 ≤ T₀) :
    IntegrableOn (fun t : ℝ => ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 * min 1 (((X : ℝ) / (h₁ * t)) ^ 2))
      {t : ℝ | T₀ ≤ |t|} := by
  have hN : ∀ n ∈ Finset.Ioc X (2 * X), 0 < n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    omega
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
  have h_int := integrableOn_weighted_dirichletPoly (fX β X) (Finset.Ioc X (2 * X)) T₀ (X : ℝ) h₁
    hN hT₀ hX_pos hh₁
  exact h_int

/-- Trivial mean square bound on Fu for any subset of $[-T, T]$. -/
lemma setIntegral_norm_sq_Fu_le_trivial (β : ℝ) (X : ℕ) (hX : 1 ≤ X) (T : ℝ) (hT : 0 ≤ T)
    (U : Set ℝ) (hU_meas : MeasurableSet U) (hU_sub : U ⊆ Set.Icc (-T) T) :
    ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (36 * Real.pi + 2) * (T / (X : ℝ) + 1) := by
  have h_pos_n : ∀ n ∈ Finset.Ioc X (2 * X), 0 < n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    omega
  have h_set_le := setIntegral_norm_sq_dirichletPoly_le (fX β X) (Finset.Ioc X (2 * X))
    h_pos_n T hT U hU_meas hU_sub
  have h_coeff_le : ∀ n, ‖fX β X n‖ ≤ 1 := norm_fX_le_one β X
  have h_F_le := integral_norm_sq_F_le_mul (fX β X) h_coeff_le X hX T hT
  unfold Fu
  exact h_set_le.trans h_F_le

lemma exists_pow_two_le_and_le {u : ℝ} (hu : 1 ≤ u) :
    ∃ k : ℕ, (2 : ℝ) ^ k ≤ u ∧ u ≤ (2 : ℝ) ^ (k + 1) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_u : 0 ≤ Real.log u := Real.log_nonneg hu
  set x := Real.log u / Real.log 2
  set k := ⌊x⌋₊
  have hk_le : (k : ℝ) ≤ x := Nat.floor_le (by positivity)
  have h_lt : x < (k : ℝ) + 1 := Nat.lt_floor_add_one x
  have h1 : (k : ℝ) * Real.log 2 ≤ Real.log u := by
    rwa [le_div_iff₀ hlog2_pos] at hk_le
  have h2 : Real.log u < ((k : ℝ) + 1) * Real.log 2 := by
    rwa [div_lt_iff₀ hlog2_pos] at h_lt
  have hu_pos : 0 < u := by linarith
  have h_exp1 : (2 : ℝ) ^ k ≤ u := by
    have : Real.log ((2 : ℝ) ^ k) = (k : ℝ) * Real.log 2 := by
      rw [Real.log_pow, mul_comm]
    rw [← Real.log_le_log_iff (by positivity) hu_pos, this]
    exact h1
  have h_exp2 : u ≤ (2 : ℝ) ^ (k + 1) := by
    have : Real.log ((2 : ℝ) ^ (k + 1)) = ((k : ℝ) + 1) * Real.log 2 := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [← Real.log_le_log_iff hu_pos (by positivity), this]
    exact h2.le
  exact ⟨k, h_exp1, h_exp2⟩

/-- Decomposition of $[T_0, \infty)$ into $[T_0, Y]$ and dyadic pieces $[2^k Y, 2^{k+1} Y] \cap [T_0, \infty)$. -/
lemma Ici_subset_Icc_union_iUnion (T₀ Y : ℝ) (hY : 0 < Y) :
    Set.Ici T₀ ⊆ Set.Icc T₀ Y ∪ ⋃ (k : ℕ), (Set.Icc ((2 : ℝ) ^ k * Y) ((2 : ℝ) ^ (k + 1) * Y) ∩ Set.Ici T₀) := by
  intro t ht
  simp only [Set.mem_Ici] at ht
  by_cases hle : t ≤ Y
  · exact Or.inl ⟨ht, hle⟩
  · have hYt : Y < t := not_le.mp hle
    have hu : 1 ≤ t / Y := by
      rw [one_le_div₀ hY]
      exact hYt.le
    obtain ⟨k, hk1, hk2⟩ := exists_pow_two_le_and_le hu
    refine Or.inr ?_
    rw [Set.mem_iUnion]
    refine ⟨k, ?_⟩
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
    refine ⟨⟨(le_div_iff₀ hY).mp hk1, (div_le_iff₀ hY).mp hk2⟩, ht⟩

def equiv_nat_Ici (k₀ : ℕ) : ℕ ≃ Set.Ici k₀ where
  toFun m := ⟨k₀ + m, Nat.le_add_right k₀ m⟩
  invFun x := x.val - k₀
  left_inv m := Nat.add_sub_self_left k₀ m
  right_inv x := Subtype.ext (Nat.add_sub_of_le x.property)

lemma hasSum_ite_Ici (k₀ : ℕ) :
    HasSum (fun k : ℕ => if k₀ ≤ k then (1 / (2 : ℝ)) ^ k else 0) ((1 / 2 : ℝ) ^ k₀ * 2) := by
  let f : ℕ → ℝ := fun k => if k₀ ≤ k then (1 / 2 : ℝ) ^ k else 0
  have hsupp : Function.support f ⊆ Set.Ici k₀ := by
    intro k hk
    simp only [Function.mem_support, ne_eq] at hk
    by_contra! h
    have : ¬ (k₀ ≤ k) := h
    have : f k = 0 := ite_eq_right_iff.mpr (fun hle => (this hle).elim)
    contradiction
  have h1 : HasSum f ((1 / 2 : ℝ) ^ k₀ * 2) ↔ HasSum (f ∘ Subtype.val) ((1 / 2 : ℝ) ^ k₀ * 2) :=
    (hasSum_subtype_iff_of_support_subset hsupp).symm
  rw [h1]
  rw [← (equiv_nat_Ici k₀).hasSum_iff]
  have h_comp : ((f ∘ Subtype.val) ∘ (equiv_nat_Ici k₀)) = fun m : ℕ => (1 / 2 : ℝ) ^ (k₀ + m) := by
    ext m
    change (if k₀ ≤ k₀ + m then (1 / 2 : ℝ) ^ (k₀ + m) else 0) = (1 / 2 : ℝ) ^ (k₀ + m)
    simp
  rw [h_comp]
  have h := hasSum_geometric_two.mul_left ((1 / (2 : ℝ)) ^ k₀)
  have h_eq : (fun m : ℕ => (1 / (2 : ℝ)) ^ k₀ * (1 / (2 : ℝ)) ^ m) =
      (fun m : ℕ => (1 / (2 : ℝ)) ^ (k₀ + m)) := by
    ext m
    rw [← pow_add]
  rwa [h_eq] at h

lemma tsum_ite_Ici (k₀ : ℕ) :
    ∑' (k : ℕ), (if k₀ ≤ k then (1 / (2 : ℝ)) ^ k else 0) = (1 / 2 : ℝ) ^ k₀ * 2 :=
  (hasSum_ite_Ici k₀).tsum_eq

lemma exists_pow_two_gt (h₁ : ℝ) : ∃ k : ℕ, h₁ < (2 : ℝ) ^ (k + 1) := by
  obtain ⟨n, hn⟩ := exists_nat_gt h₁
  refine ⟨n, ?_⟩
  have hn_lt : (n : ℝ) < (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.lt_pow_self (by norm_num : 1 < 2) : n < 2 ^ n)
  have h_le : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) := by
    have : (2 : ℝ) ^ n * 1 ≤ (2 : ℝ) ^ n * 2 :=
      mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
    ring_nf at this ⊢
    exact this
  linarith

lemma tsum_ite_pow_two_gt_le {h₁ : ℝ} (hh₁ : 1 ≤ h₁) :
    ∑' (k : ℕ), (if h₁ < (2 : ℝ) ^ (k + 1) then (1 / (2 : ℝ)) ^ k else 0) ≤ 4 / h₁ := by
  have h1_pos : 0 < h₁ := by linarith
  have h_ex := exists_pow_two_gt h₁
  set k₀ := Nat.find h_ex
  have hk0_prop : h₁ < (2 : ℝ) ^ (k₀ + 1) := Nat.find_spec h_ex
  have h_iff : ∀ k : ℕ, h₁ < (2 : ℝ) ^ (k + 1) ↔ k₀ ≤ k := by
    intro k
    constructor
    · intro hk
      exact Nat.find_le hk
    · intro hk
      have h_mono : (2 : ℝ) ^ (k₀ + 1) ≤ (2 : ℝ) ^ (k + 1) := by
        have : (1 : ℝ) ≤ 2 := by norm_num
        have : k₀ + 1 ≤ k + 1 := by omega
        exact pow_le_pow_right₀ (by norm_num) this
      exact hk0_prop.trans_le h_mono
  have h_fun_eq : (fun k : ℕ => if h₁ < (2 : ℝ) ^ (k + 1) then (1 / (2 : ℝ)) ^ k else 0) =
      (fun k : ℕ => if k₀ ≤ k then (1 / (2 : ℝ)) ^ k else 0) := by
    ext k
    simp_rw [h_iff]
  rw [h_fun_eq, tsum_ite_Ici k₀]
  rcases Nat.eq_zero_or_pos k₀ with hk0 | hk0
  · rw [hk0]
    have h_pow0 : (1 / (2 : ℝ)) ^ 0 * 2 = 2 := by ring
    rw [h_pow0]
    have : (2 : ℝ) ≤ 4 / h₁ := by
      have hk0_lt : h₁ < 2 := by
        have := hk0_prop
        rw [hk0] at this
        simpa using this
      rw [le_div_iff₀ h1_pos]
      linarith
    linarith
  · have h_split : (2 : ℝ) ^ (k₀ + 1) = 2 * (2 : ℝ) ^ k₀ := by
      rw [pow_succ, mul_comm]
    rw [h_split] at hk0_prop
    have h_pow_pos : 0 < 2 * (2 : ℝ) ^ k₀ := by positivity
    have h_inv : (2 * (2 : ℝ) ^ k₀)⁻¹ < h₁⁻¹ :=
      inv_lt_inv₀ h_pow_pos h1_pos |>.mpr hk0_prop
    have h_inv_split : (2 * (2 : ℝ) ^ k₀)⁻¹ = (1 / 2 : ℝ) * (1 / (2 : ℝ)) ^ k₀ := by
      rw [one_div, mul_inv, ← inv_pow]
    rw [h_inv_split] at h_inv
    have h_bound : (1 / (2 : ℝ)) ^ k₀ * 2 ≤ 4 / h₁ := by
      calc (1 / (2 : ℝ)) ^ k₀ * 2 = 4 * ((1 / 2 : ℝ) * (1 / (2 : ℝ)) ^ k₀) := by ring
        _ ≤ 4 * h₁⁻¹ := mul_le_mul_of_nonneg_left h_inv.le (by norm_num)
        _ = 4 / h₁ := by rw [div_eq_mul_inv]
    exact h_bound

lemma tsum_geometric_two_mul_three :
    ∑' (k : ℕ), 3 * (1 / (2 : ℝ)) ^ k = 6 := by
  have h := (hasSum_geometric_two.mul_left 3).tsum_eq
  have : (3 : ℝ) * 2 = 6 := by norm_num
  rwa [this] at h

lemma tsum_ite_pow_two_le_six (h₁ : ℝ) :
    ∑' (k : ℕ), (if (2 : ℝ) ^ (k + 1) ≤ h₁ then 3 * (1 / (2 : ℝ)) ^ k else 0) ≤ 6 := by
  have h_nn : ∀ k, 0 ≤ if (2 : ℝ) ^ (k + 1) ≤ h₁ then 3 * (1 / (2 : ℝ)) ^ k else 0 := by
    intro k
    split_ifs <;> positivity
  have h_le : ∀ k, (if (2 : ℝ) ^ (k + 1) ≤ h₁ then 3 * (1 / (2 : ℝ)) ^ k else 0) ≤
      3 * (1 / (2 : ℝ)) ^ k := by
    intro k
    split_ifs
    · rfl
    · positivity
  have h_geom_summable : Summable (fun k : ℕ => 3 * (1 / (2 : ℝ)) ^ k) :=
    hasSum_geometric_two.summable.mul_left 3
  have h_summable : Summable (fun k => if (2 : ℝ) ^ (k + 1) ≤ h₁ then 3 * (1 / (2 : ℝ)) ^ k else 0) :=
    Summable.of_nonneg_of_le h_nn h_le h_geom_summable
  have h_sum := h_summable.tsum_le_tsum h_le h_geom_summable
  rw [tsum_geometric_two_mul_three] at h_sum
  exact h_sum

/-- Lintegral master inequality: for non-negative $g$ on $E \subseteq s_0 \cup \bigcup_k s_k$,
$\int_E g \le b_0 + \sum_k b_k$. -/
lemma setIntegral_le_of_subset_union_iUnion {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg_nonneg : 0 ≤ᵐ[μ] g) {E s₀ : Set α} {s : ℕ → Set α}
    (hsub : E ⊆ s₀ ∪ ⋃ k, s k)
    (hg_int_E : IntegrableOn g E μ)
    (b₀ : ℝ) (hb₀_nonneg : 0 ≤ b₀) (h_int_s₀ : ∫ x in s₀, g x ∂μ ≤ b₀)
    (b : ℕ → ℝ) (hb_nonneg : ∀ k, 0 ≤ b k) (hb_sum : Summable b)
    (h_int_s : ∀ k, ∫ x in s k, g x ∂μ ≤ b k)
    (hg_int_s₀ : IntegrableOn g s₀ μ)
    (hg_int_s : ∀ k, IntegrableOn g (s k) μ) :
    ∫ x in E, g x ∂μ ≤ b₀ + ∑' k, b k := by
  have h_linE : ENNReal.ofReal (∫ x in E, g x ∂μ) = ∫⁻ x in E, ENNReal.ofReal (g x) ∂μ := by
    have hgE_nonneg : 0 ≤ᵐ[μ.restrict E] g := ae_restrict_of_ae hg_nonneg
    exact ofReal_integral_eq_lintegral_ofReal hg_int_E hgE_nonneg
  have h_lin_sub : ∫⁻ x in E, ENNReal.ofReal (g x) ∂μ ≤
      ∫⁻ x in s₀ ∪ ⋃ k, s k, ENNReal.ofReal (g x) ∂μ :=
    lintegral_mono_set hsub
  have h_lin_union : ∫⁻ x in s₀ ∪ ⋃ k, s k, ENNReal.ofReal (g x) ∂μ ≤
      (∫⁻ x in s₀, ENNReal.ofReal (g x) ∂μ) + ∫⁻ x in ⋃ k, s k, ENNReal.ofReal (g x) ∂μ :=
    lintegral_union_le (fun x => ENNReal.ofReal (g x)) s₀ (⋃ k, s k)
  have h_lin_iUnion : ∫⁻ x in ⋃ k, s k, ENNReal.ofReal (g x) ∂μ ≤
      ∑' k, ∫⁻ x in s k, ENNReal.ofReal (g x) ∂μ :=
    lintegral_iUnion_le s (fun x => ENNReal.ofReal (g x))
  have h_s₀_eq : ∫⁻ x in s₀, ENNReal.ofReal (g x) ∂μ = ENNReal.ofReal (∫ x in s₀, g x ∂μ) := by
    have hgs₀_nonneg : 0 ≤ᵐ[μ.restrict s₀] g := ae_restrict_of_ae hg_nonneg
    exact (ofReal_integral_eq_lintegral_ofReal hg_int_s₀ hgs₀_nonneg).symm
  have h_s_eq : ∀ k, ∫⁻ x in s k, ENNReal.ofReal (g x) ∂μ = ENNReal.ofReal (∫ x in s k, g x ∂μ) := by
    intro k
    have hgsk_nonneg : 0 ≤ᵐ[μ.restrict (s k)] g := ae_restrict_of_ae hg_nonneg
    exact (ofReal_integral_eq_lintegral_ofReal (hg_int_s k) hgsk_nonneg).symm
  have h_s₀_le : ENNReal.ofReal (∫ x in s₀, g x ∂μ) ≤ ENNReal.ofReal b₀ :=
    ofReal_le_ofReal h_int_s₀
  have h_s_le : ∀ k, ENNReal.ofReal (∫ x in s k, g x ∂μ) ≤ ENNReal.ofReal (b k) :=
    fun k => ofReal_le_ofReal (h_int_s k)
  have h_tsum_le : ∑' k, ENNReal.ofReal (∫ x in s k, g x ∂μ) ≤ ∑' k, ENNReal.ofReal (b k) :=
    ENNReal.tsum_le_tsum h_s_le
  have h_tsum_b : ∑' k, ENNReal.ofReal (b k) = ENNReal.ofReal (∑' k, b k) :=
    (ofReal_tsum_of_nonneg hb_nonneg hb_sum).symm
  have h_sum_b_nn : 0 ≤ ∑' k, b k := tsum_nonneg hb_nonneg
  have h_total_lin : ENNReal.ofReal (∫ x in E, g x ∂μ) ≤
      ENNReal.ofReal (b₀ + ∑' k, b k) := by
    rw [ofReal_add hb₀_nonneg h_sum_b_nn]
    calc ENNReal.ofReal (∫ x in E, g x ∂μ)
      _ ≤ (∫⁻ x in s₀, ENNReal.ofReal (g x) ∂μ) + ∫⁻ x in ⋃ k, s k, ENNReal.ofReal (g x) ∂μ :=
        h_linE.trans_le (h_lin_sub.trans h_lin_union)
      _ ≤ ENNReal.ofReal b₀ + ∑' k, ENNReal.ofReal (b k) := by
        rw [h_s₀_eq]
        have h_rest : ∑' k, ∫⁻ x in s k, ENNReal.ofReal (g x) ∂μ ≤ ∑' k, ENNReal.ofReal (b k) := by
          have : (fun k => ∫⁻ x in s k, ENNReal.ofReal (g x) ∂μ) =
              fun k => ENNReal.ofReal (∫ x in s k, g x ∂μ) := by
            ext k
            exact h_s_eq k
          rw [this]
          exact h_tsum_le
        exact add_le_add h_s₀_le (h_lin_iUnion.trans h_rest)
      _ = ENNReal.ofReal b₀ + ENNReal.ofReal (∑' k, b k) := by rw [h_tsum_b]
  have h_sum_b_nonneg : 0 ≤ b₀ + ∑' k, b k := add_nonneg hb₀_nonneg h_sum_b_nn
  exact (ofReal_le_ofReal_iff h_sum_b_nonneg).mp h_total_lin

lemma pow_four_inv_mul_pow_two (k : ℕ) :
    (1 / (4 : ℝ)) ^ k * (2 : ℝ) ^ k = (1 / (2 : ℝ)) ^ k := by
  have : (1 / (4 : ℝ)) = (1 / (2 : ℝ)) * (1 / (2 : ℝ)) := by norm_num
  rw [this, mul_pow, mul_assoc]
  have h_inv : (1 / (2 : ℝ)) ^ k * (2 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    have : (1 / (2 : ℝ)) * 2 = 1 := by norm_num
    rw [this, one_pow]
  rw [h_inv, mul_one]

lemma pow_four_inv_mul_three_mul_pow_two (k : ℕ) :
    (1 / (4 : ℝ)) ^ k * (3 * (2 : ℝ) ^ k) = 3 * (1 / (2 : ℝ)) ^ k := by
  calc (1 / (4 : ℝ)) ^ k * (3 * (2 : ℝ) ^ k) = 3 * ((1 / (4 : ℝ)) ^ k * (2 : ℝ) ^ k) := by ring
    _ = 3 * (1 / (2 : ℝ)) ^ k := by rw [pow_four_inv_mul_pow_two]

lemma pow_four_inv_mul_four_mul_pow_two (k : ℕ) :
    (1 / (4 : ℝ)) ^ k * (4 * (2 : ℝ) ^ k) = 4 * (1 / (2 : ℝ)) ^ k := by
  calc (1 / (4 : ℝ)) ^ k * (4 * (2 : ℝ) ^ k) = 4 * ((1 / (4 : ℝ)) ^ k * (2 : ℝ) ^ k) := by ring
    _ = 4 * (1 / (2 : ℝ)) ^ k := by rw [pow_four_inv_mul_pow_two]

lemma prop1_factor_bound (T X Q₀ h₁ : ℝ) (A B D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hX : 0 < X) (hh₁ : 1 ≤ h₁) (hQ₀ : 0 < Q₀) (hQh₁ : Q₀ ≤ h₁)
    (k : ℕ) (hT_eq : T = (2 : ℝ) ^ (k + 1) * (X / h₁)) :
    (T / (X / Q₀) + 1) * (A + B) + (T / X + 1) * D ≤ (3 * (2 : ℝ) ^ k) * (A + B + D) := by
  have hh1_pos : 0 < h₁ := by linarith
  have h_TQ : T / (X / Q₀) ≤ (2 : ℝ) ^ (k + 1) := by
    rw [hT_eq]
    have : (2 : ℝ) ^ (k + 1) * (X / h₁) / (X / Q₀) = (2 : ℝ) ^ (k + 1) * (Q₀ / h₁) := by
      field_simp
    rw [this]
    have h_div_le : Q₀ / h₁ ≤ 1 := by rwa [div_le_one hh1_pos]
    have : (2 : ℝ) ^ (k + 1) * (Q₀ / h₁) ≤ (2 : ℝ) ^ (k + 1) * 1 :=
      mul_le_mul_of_nonneg_left h_div_le (by positivity)
    linarith
  have h_TX : T / X ≤ (2 : ℝ) ^ (k + 1) := by
    rw [hT_eq]
    have : (2 : ℝ) ^ (k + 1) * (X / h₁) / X = (2 : ℝ) ^ (k + 1) / h₁ := by
      field_simp
    rw [this]
    have : (2 : ℝ) ^ (k + 1) / h₁ ≤ (2 : ℝ) ^ (k + 1) / 1 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hh₁
    linarith
  have h_two_pow : (2 : ℝ) ^ (k + 1) + 1 ≤ 3 * (2 : ℝ) ^ k := by
    have : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ, mul_comm]
    rw [this]
    have : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
      have : (2 : ℝ) ^ 0 ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
      simpa using this
    linarith
  have h1 : T / (X / Q₀) + 1 ≤ 3 * (2 : ℝ) ^ k := by linarith
  have h2 : T / X + 1 ≤ 3 * (2 : ℝ) ^ k := by linarith
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  calc (T / (X / Q₀) + 1) * (A + B) + (T / X + 1) * D
    _ ≤ (3 * (2 : ℝ) ^ k) * (A + B) + (3 * (2 : ℝ) ^ k) * D :=
      add_le_add (mul_le_mul_of_nonneg_right h1 hAB) (mul_le_mul_of_nonneg_right h2 hD)
    _ = (3 * (2 : ℝ) ^ k) * (A + B + D) := by ring

lemma prop1_factor_bound_zero (X Q₀ h₁ : ℝ) (A B D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hX : 0 < X) (hh₁ : 1 ≤ h₁) (hQ₀ : 0 < Q₀) (hQh₁ : Q₀ ≤ h₁) :
    let T := X / h₁
    (T / (X / Q₀) + 1) * (A + B) + (T / X + 1) * D ≤ 2 * (A + B + D) := by
  intro T
  have hh1_pos : 0 < h₁ := by linarith
  have h_TQ : T / (X / Q₀) ≤ 1 := by
    dsimp [T]
    have : (X / h₁) / (X / Q₀) = Q₀ / h₁ := by field_simp
    rw [this]
    exact div_le_one_of_le₀ hQh₁ hh1_pos.le
  have h_TX : T / X ≤ 1 := by
    dsimp [T]
    have : (X / h₁) / X = 1 / h₁ := by field_simp
    rw [this]
    exact div_le_one_of_le₀ hh₁ hh1_pos.le
  have h1 : T / (X / Q₀) + 1 ≤ 2 := by linarith
  have h2 : T / X + 1 ≤ 2 := by linarith
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  calc (T / (X / Q₀) + 1) * (A + B) + (T / X + 1) * D
    _ ≤ 2 * (A + B) + 2 * D :=
      add_le_add (mul_le_mul_of_nonneg_right h1 hAB) (mul_le_mul_of_nonneg_right h2 hD)
    _ = 2 * (A + B + D) := by ring

lemma trivial_factor_bound (T X h₁ : ℝ) (hX : 0 < X) (hh₁_pos : 0 < h₁)
    (k : ℕ) (hT_eq : T = (2 : ℝ) ^ (k + 1) * (X / h₁)) (hk : h₁ < (2 : ℝ) ^ (k + 1)) :
    T / X + 1 ≤ 4 * (2 : ℝ) ^ k / h₁ := by
  have h_TX : T / X = (2 : ℝ) ^ (k + 1) / h₁ := by
    rw [hT_eq]
    have : (2 : ℝ) ^ (k + 1) * (X / h₁) / X = (2 : ℝ) ^ (k + 1) / h₁ * (X / X) := by ring
    rw [this, div_self hX.ne', mul_one]
  have h_one_lt : 1 < (2 : ℝ) ^ (k + 1) / h₁ := by
    rwa [one_lt_div₀ hh₁_pos]
  have : T / X + 1 ≤ 2 * ((2 : ℝ) ^ (k + 1) / h₁) := by
    rw [h_TX]
    linarith
  refine this.trans_eq ?_
  have : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by rw [pow_succ, mul_comm]
  rw [this]
  ring

lemma freqWeight_le_pow_four (k : ℕ) (X : ℕ) (hX : 16 ≤ X) (h₁ : ℝ) (hh₁ : 1 ≤ h₁) (t : ℝ)
    (ht : (2 : ℝ) ^ k * ((X : ℝ) / h₁) ≤ t) :
    min 1 (((X : ℝ) / (h₁ * t)) ^ 2) ≤ (1 / (4 : ℝ)) ^ k := by
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hh1_pos : 0 < h₁ := by linarith
  have h_base_pos : 0 < (X : ℝ) / h₁ := div_pos hX_pos hh1_pos
  have h_pow_pos : 0 < (2 : ℝ) ^ k := by positivity
  have ht_pos : 0 < t := lt_of_lt_of_le (mul_pos h_pow_pos h_base_pos) ht
  have h_prod : (2 : ℝ) ^ k * (X : ℝ) ≤ h₁ * t := by
    calc (2 : ℝ) ^ k * (X : ℝ) = (2 : ℝ) ^ k * (h₁ * ((X : ℝ) / h₁)) := by
          rw [mul_div_cancel₀ _ hh1_pos.ne']
      _ = h₁ * ((2 : ℝ) ^ k * ((X : ℝ) / h₁)) := by ring
      _ ≤ h₁ * t := mul_le_mul_of_nonneg_left ht hh1_pos.le
  have h_div : (X : ℝ) / (h₁ * t) ≤ (1 / (2 : ℝ)) ^ k := by
    have h1 : (X : ℝ) / (h₁ * t) ≤ (X : ℝ) / ((2 : ℝ) ^ k * (X : ℝ)) := by
      exact div_le_div_of_nonneg_left hX_pos.le (by positivity) h_prod
    have h2 : (X : ℝ) / ((2 : ℝ) ^ k * (X : ℝ)) = (1 / (2 : ℝ)) ^ k := by
      have : (X : ℝ) / ((2 : ℝ) ^ k * (X : ℝ)) = (1 / (2 : ℝ) ^ k) * ((X : ℝ) / (X : ℝ)) := by ring
      rw [this, div_self hX_pos.ne', mul_one]
      rw [one_div, one_div, ← inv_pow]
    exact h1.trans_eq h2
  have h_div_nonneg : 0 ≤ (X : ℝ) / (h₁ * t) := by positivity
  have h_sq : ((X : ℝ) / (h₁ * t)) ^ 2 ≤ ((1 / (2 : ℝ)) ^ k) ^ 2 :=
    pow_le_pow_left₀ h_div_nonneg h_div 2
  have h_four : ((1 / (2 : ℝ)) ^ k) ^ 2 = (1 / (4 : ℝ)) ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul]
    have : ((1 / (2 : ℝ)) ^ 2) = (1 / (4 : ℝ)) := by norm_num
    rw [this]
  rw [h_four] at h_sq
  exact (min_le_right _ _).trans h_sq

theorem weighted_mean_sq_Fu_le (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1}))
    {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (h₁ : ℝ),
      3 / 4 ≤ β → β < 1 → 16 ≤ X → 1 ≤ h₁ → (S.Q ⟨0, hJ⟩ : ℝ) ≤ h₁ → h₁ ≤ X →
      (∀ j, (S.Q j : ℝ) ≤ (X : ℝ) ^ β) → (∀ j, (S.Q j : ℝ) ^ 4 ≤ X) →
      (∀ j, 2 ≤ S.Hj hJ j ∧ S.Hj hJ j ≤ Real.sqrt (S.P j)) → (∀ j, 2 ≤ Real.log (S.P j)) → (∀ j, 2 ≤ Real.log (Real.log (S.Q j))) →
      (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) →
      (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) →
      ∫ t in {t : ℝ | (Real.log X) ^ (1 / 15 : ℝ) ≤ |t|}, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 * min 1 (((X : ℝ) / (h₁ * t)) ^ 2) ≤
        C * ((Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) + (Real.log X) ^ (-(1 / 400 : ℝ))
          + (∑ j : Fin J, (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j) + Real.log (S.P j) / Real.log (S.Q j))) + 1 / h₁ ^ 2) := by
  obtain ⟨C₁, hC₁_pos, hProp1⟩ := RangeSystem.integral_Icc_norm_sq_Fu_le c₀ K hc₀ hK hζ hholo hη0 hη
  let C := 16 * C₁ + 32 * (36 * Real.pi + 2)
  have hC_pos : 0 < C := by
    have : 0 < 36 * Real.pi + 2 := by positivity
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro J S hJ β X h₁ hβ hβ1 hX hh₁ hQh₁ h1X hQX hQ4 hH hP hloglogQ hQ_exp hP_last
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hh1_pos : 0 < h₁ := by linarith
  have hQ0_pos : 0 < (S.Q ⟨0, hJ⟩ : ℝ) := by
    have : 2 ≤ S.P ⟨0, hJ⟩ := S.two_le_P ⟨0, hJ⟩
    have : S.P ⟨0, hJ⟩ ≤ S.Q ⟨0, hJ⟩ := S.P_le_Q ⟨0, hJ⟩
    have : 0 < S.Q ⟨0, hJ⟩ := by omega
    exact_mod_cast this
  set T₀ := (Real.log (X : ℝ)) ^ (1 / 15 : ℝ)
  have hT₀_ge1 : 1 ≤ T₀ := one_le_log_X_rpow_fifteen X hX
  have hT₀_pos : 0 < T₀ := by linarith
  have hY_pos : 0 < (X : ℝ) / h₁ := div_pos hX_pos hh1_pos

  set g : ℝ → ℝ := fun t => ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 * min 1 (((X : ℝ) / (h₁ * t)) ^ 2)
  have hg_even : ∀ t, g (-t) = g t := by
    intro t; dsimp [g]
    rw [norm_Fu_neg_freq, freqWeight_even]
  have hg_int : IntegrableOn g {t : ℝ | T₀ ≤ |t|} :=
    integrableOn_norm_sq_Fu_mul_wgt β X h₁ T₀ (by omega) hh1_pos hT₀_ge1
  have h_symm : ∫ t in {t : ℝ | T₀ ≤ |t|}, g t = 2 * ∫ t in Set.Ici T₀, g t :=
    integral_abs_ge_eq_two_mul g hg_even T₀ hT₀_pos hg_int

  set s₀ := Set.Icc T₀ ((X : ℝ) / h₁)
  set s := fun k : ℕ => Set.Icc ((2 : ℝ) ^ k * ((X : ℝ) / h₁)) ((2 : ℝ) ^ (k + 1) * ((X : ℝ) / h₁)) ∩ Set.Ici T₀
  have hsub : Set.Ici T₀ ⊆ s₀ ∪ ⋃ k, s k := Ici_subset_Icc_union_iUnion T₀ ((X : ℝ) / h₁) hY_pos
  have hg_nonneg : 0 ≤ᵐ[volume] g := Filter.Eventually.of_forall (fun _ => mul_nonneg (sq_nonneg _) (by positivity))

  have hs₀_sub_Ici : s₀ ⊆ Set.Ici T₀ := fun _ ht => ht.1
  have hsk_sub_Ici : ∀ k, s k ⊆ Set.Ici T₀ := fun _ _ ht => ht.2
  have hIci_sub_abs : Set.Ici T₀ ⊆ {t : ℝ | T₀ ≤ |t|} := by
    intro t ht
    simp only [mem_Ici] at ht
    simp only [Set.mem_ofPred_eq]
    have : 0 < t := by linarith
    rw [abs_of_pos this]
    exact ht
  have hg_int_E : IntegrableOn g (Set.Ici T₀) := hg_int.mono_set hIci_sub_abs
  have hg_int_s₀ : IntegrableOn g s₀ := hg_int_E.mono_set hs₀_sub_Ici
  have hg_int_s : ∀ k, IntegrableOn g (s k) := fun k => hg_int_E.mono_set (hsk_sub_Ici k)

  set A := (Real.log (S.Q ⟨0, hJ⟩ : ℝ)) ^ (1 / 3 : ℝ) / (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η)
  set B := (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))
  set D := ∑ j : Fin J, (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j) + Real.log (S.P j) / Real.log (S.Q j))
  set E := A + B + D
  have hA_nn : 0 ≤ A := by positivity
  have hB_nn : 0 ≤ B := by positivity
  have hD_nn : 0 ≤ D := Finset.sum_nonneg (fun _ _ => by positivity)
  have hE_nn : 0 ≤ E := add_nonneg (add_nonneg hA_nn hB_nn) hD_nn

  set b₀ := 2 * C₁ * E
  have hb₀_nn : 0 ≤ b₀ := mul_nonneg (by linarith) hE_nn

  have h_int_s₀ : ∫ t in s₀, g t ≤ b₀ := by
    by_cases h_empty : (X : ℝ) / h₁ < T₀
    · have : s₀ = ∅ := Set.Icc_eq_empty (by linarith)
      rw [this, setIntegral_empty]
      exact hb₀_nn
    · have hT0T : T₀ ≤ (X : ℝ) / h₁ := not_lt.mp h_empty
      have hTX : (X : ℝ) / h₁ ≤ (X : ℝ) := by
        have : (X : ℝ) / h₁ ≤ (X : ℝ) / 1 := div_le_div_of_nonneg_left hX_pos.le (by norm_num) hh₁
        rwa [div_one] at this
      have hT0_bound : (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) ≤ T₀ := le_rfl
      have h_wgt : ∀ t ∈ s₀, g t ≤ ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
        intro t _
        dsimp [g]
        have : min 1 (((X : ℝ) / (h₁ * t)) ^ 2) ≤ 1 := min_le_left _ _
        nlinarith [sq_nonneg ‖Fu β X ((1 : ℂ) + t * Complex.I)‖]
      have h_mono := setIntegral_mono_on hg_int_s₀
        (integrableOn_norm_sq_Fu_Icc β X T₀ ((X : ℝ) / h₁)) measurableSet_Icc h_wgt
      have h_prop1 := hProp1 J S hJ β X T₀ ((X : ℝ) / h₁) hβ hβ1 hX hT0_bound hT0T hTX
        hQX hQ4 hH hP hloglogQ hQ_exp hP_last
      have h_factor := prop1_factor_bound_zero (X : ℝ) (S.Q ⟨0, hJ⟩ : ℝ) h₁ A B D
        hA_nn hB_nn hD_nn hX_pos hh₁ hQ0_pos hQh₁
      dsimp [s₀] at h_mono ⊢
      refine h_mono.trans (h_prop1.trans ?_)
      have : C₁ * (((X : ℝ) / h₁ / ((X : ℝ) / (S.Q ⟨0, hJ⟩ : ℝ)) + 1) * (A + B) + ((X : ℝ) / h₁ / (X : ℝ) + 1) * D) ≤
          C₁ * (2 * (A + B + D)) :=
        mul_le_mul_of_nonneg_left h_factor hC₁_pos.le
      refine this.trans_eq ?_
      dsimp [b₀, E]
      ring

  set b₁ := fun k : ℕ => if (2 : ℝ) ^ (k + 1) ≤ h₁ then 3 * (1 / (2 : ℝ)) ^ k * (C₁ * E) else 0
  set b₂ := fun k : ℕ => if h₁ < (2 : ℝ) ^ (k + 1) then (36 * Real.pi + 2) * (4 / h₁) * (1 / (2 : ℝ)) ^ k else 0
  set b := fun k : ℕ => b₁ k + b₂ k
  have hb₁_nn : ∀ k, 0 ≤ b₁ k := by
    intro k; dsimp [b₁]; split_ifs <;> positivity
  have hb₂_nn : ∀ k, 0 ≤ b₂ k := by
    intro k; dsimp [b₂]; split_ifs <;> positivity
  have hb_nn : ∀ k, 0 ≤ b k := fun k => add_nonneg (hb₁_nn k) (hb₂_nn k)

  have h_int_s : ∀ k, ∫ t in s k, g t ≤ b k := by
    intro k
    have h_wgt : ∀ t ∈ s k, g t ≤ (1 / (4 : ℝ)) ^ k * ‖Fu β X ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
      intro t ht
      dsimp [g]
      have ht_ge : (2 : ℝ) ^ k * ((X : ℝ) / h₁) ≤ t := ht.1.1
      have hw := freqWeight_le_pow_four k X hX h₁ hh₁ t ht_ge
      have := mul_le_mul_of_nonneg_left hw (sq_nonneg ‖Fu β X ((1 : ℂ) + (t : ℝ) * Complex.I)‖)
      linarith
    have h_int_Fu : IntegrableOn (fun (t : ℝ) => ‖Fu β X ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) (s k) :=
      (integrableOn_norm_sq_Fu_Icc β X ((2 : ℝ) ^ k * ((X : ℝ) / h₁)) ((2 : ℝ) ^ (k + 1) * ((X : ℝ) / h₁))).mono_set
        (fun (t : ℝ) (ht : t ∈ s k) => ht.1)
    have h_step1 : ∫ t in s k, g t ≤ (1 / (4 : ℝ)) ^ k * ∫ t in s k, ‖Fu β X ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
      have h_mono := setIntegral_mono_on (hg_int_s k) (h_int_Fu.const_mul _)
        (measurableSet_Icc.inter measurableSet_Ici) h_wgt
      rw [integral_const_mul] at h_mono
      exact h_mono
    by_cases hk : (2 : ℝ) ^ (k + 1) ≤ h₁
    · have hb₂_zero : b₂ k = 0 := by
        dsimp [b₂]
        split_ifs with h
        · linarith
        · rfl
      have hb_eq : b k = 3 * (1 / (2 : ℝ)) ^ k * (C₁ * E) := by
        dsimp [b, b₁]
        split_ifs
        rw [hb₂_zero, add_zero]
      by_cases h_empty : (2 : ℝ) ^ (k + 1) * ((X : ℝ) / h₁) < T₀
      · have h_sk_empty : s k = ∅ := by
          ext t
          simp only [s, mem_inter_iff, mem_Icc, mem_Ici, mem_empty_iff_false, iff_false, not_and]
          intro ⟨_, ht2⟩ ht_T0
          linarith
        rw [h_sk_empty, setIntegral_empty, hb_eq]
        positivity
      · have hT0T : T₀ ≤ (2 : ℝ) ^ (k + 1) * ((X : ℝ) / h₁) := not_lt.mp h_empty
        set T := (2 : ℝ) ^ (k + 1) * ((X : ℝ) / h₁)
        have hTX : T ≤ (X : ℝ) := by
          dsimp [T]
          calc (2 : ℝ) ^ (k + 1) * ((X : ℝ) / h₁) ≤ h₁ * ((X : ℝ) / h₁) :=
                mul_le_mul_of_nonneg_right hk (by positivity)
            _ = (X : ℝ) := by rw [mul_div_cancel₀ _ hh1_pos.ne']
        have hsk_sub : s k ⊆ Set.Icc T₀ T := by
          intro t ht
          exact ⟨ht.2, ht.1.2⟩
        have h_Fu_le : ∫ t in s k, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
            ∫ t in Set.Icc T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
          apply setIntegral_mono_set
          · exact integrableOn_norm_sq_Fu_Icc β X T₀ T
          · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
          · exact Filter.Eventually.of_forall hsk_sub
        have h_prop1 := hProp1 J S hJ β X T₀ T hβ hβ1 hX le_rfl hT0T hTX
          hQX hQ4 hH hP hloglogQ hQ_exp hP_last
        have h_factor := prop1_factor_bound T (X : ℝ) (S.Q ⟨0, hJ⟩ : ℝ) h₁ A B D
          hA_nn hB_nn hD_nn hX_pos hh₁ hQ0_pos hQh₁ k rfl
        have h_tot := h_Fu_le.trans (h_prop1.trans (mul_le_mul_of_nonneg_left h_factor hC₁_pos.le))
        have h_mul := mul_le_mul_of_nonneg_left h_tot (by positivity : 0 ≤ (1 / (4 : ℝ)) ^ k)
        refine h_step1.trans (h_mul.trans ?_)
        rw [hb_eq]
        have h_assoc : (1 / (4 : ℝ)) ^ k * (C₁ * ((3 * (2 : ℝ) ^ k) * (A + B + D))) =
            ((1 / (4 : ℝ)) ^ k * (3 * (2 : ℝ) ^ k)) * (C₁ * (A + B + D)) := by ring
        rw [h_assoc, pow_four_inv_mul_three_mul_pow_two]
    · have hk_gt : h₁ < (2 : ℝ) ^ (k + 1) := not_le.mp hk
      have hb₁_zero : b₁ k = 0 := by
        dsimp [b₁]
        split_ifs
        rfl
      have hb_eq : b k = (36 * Real.pi + 2) * (4 / h₁) * (1 / (2 : ℝ)) ^ k := by
        dsimp [b, b₂]
        split_ifs
        rw [hb₁_zero, zero_add]
      set T := (2 : ℝ) ^ (k + 1) * ((X : ℝ) / h₁)
      have hT_nonneg : 0 ≤ T := by positivity
      have hsk_sub_neg : s k ⊆ Set.Icc (-T) T := by
        intro t ht
        have ht1 : 0 ≤ t := by
          have : 0 ≤ (2 : ℝ) ^ k * ((X : ℝ) / h₁) := by positivity
          exact this.trans ht.1.1
        exact ⟨by linarith, ht.1.2⟩
      have h_triv := setIntegral_norm_sq_Fu_le_trivial β X (by omega) T hT_nonneg (s k)
        (measurableSet_Icc.inter measurableSet_Ici) hsk_sub_neg
      have h_factor := trivial_factor_bound T (X : ℝ) h₁ hX_pos hh1_pos k rfl hk_gt
      have h_pi_nn : 0 ≤ 36 * Real.pi + 2 := by positivity
      have h_tot := h_triv.trans (mul_le_mul_of_nonneg_left h_factor h_pi_nn)
      have h_mul := mul_le_mul_of_nonneg_left h_tot (by positivity : 0 ≤ (1 / (4 : ℝ)) ^ k)
      refine h_step1.trans (h_mul.trans ?_)
      rw [hb_eq]
      have : (1 / (4 : ℝ)) ^ k * ((36 * Real.pi + 2) * (4 * (2 : ℝ) ^ k / h₁)) =
          (36 * Real.pi + 2) * (1 / h₁) * ((1 / (4 : ℝ)) ^ k * (4 * (2 : ℝ) ^ k)) := by ring
      rw [this, pow_four_inv_mul_four_mul_pow_two]
      have h_ring : (36 * Real.pi + 2) * (1 / h₁) * (4 * (1 / (2 : ℝ)) ^ k) =
          (36 * Real.pi + 2) * (4 / h₁) * (1 / (2 : ℝ)) ^ k := by ring
      rw [h_ring]

  have h_summable_geom : Summable (fun k : ℕ => (1 / (2 : ℝ)) ^ k) := hasSum_geometric_two.summable
  have h_summable_b₁ : Summable b₁ := by
    have h_le : ∀ k, b₁ k ≤ (C₁ * E) * (3 * (1 / (2 : ℝ)) ^ k) := by
      intro k
      dsimp [b₁]
      split_ifs
      · ring_nf; rfl
      · positivity
    have h_maj : Summable (fun k => (C₁ * E) * (3 * (1 / (2 : ℝ)) ^ k)) :=
      (h_summable_geom.mul_left 3).mul_left (C₁ * E)
    exact Summable.of_nonneg_of_le hb₁_nn h_le h_maj
  have h_summable_b₂ : Summable b₂ := by
    have h_le : ∀ k, b₂ k ≤ ((36 * Real.pi + 2) * (4 / h₁)) * (1 / (2 : ℝ)) ^ k := by
      intro k
      dsimp [b₂]
      split_ifs
      · rfl
      · positivity
    have h_maj : Summable (fun k => ((36 * Real.pi + 2) * (4 / h₁)) * (1 / (2 : ℝ)) ^ k) :=
      h_summable_geom.mul_left _
    exact Summable.of_nonneg_of_le hb₂_nn h_le h_maj
  have hb_sum : Summable b := h_summable_b₁.add h_summable_b₂

  have h_tsum_b₁ : ∑' k, b₁ k ≤ 6 * C₁ * E := by
    have h_eq : (fun k => b₁ k) = fun k => (C₁ * E) * (if (2 : ℝ) ^ (k + 1) ≤ h₁ then 3 * (1 / (2 : ℝ)) ^ k else 0) := by
      ext k
      dsimp [b₁]
      split_ifs <;> ring
    rw [h_eq, tsum_mul_left]
    have h_six := tsum_ite_pow_two_le_six h₁
    have := mul_le_mul_of_nonneg_left h_six (by positivity : 0 ≤ C₁ * E)
    linarith
  have h_tsum_b₂ : ∑' k, b₂ k ≤ (36 * Real.pi + 2) * 16 / h₁ ^ 2 := by
    have h_eq : (fun k => b₂ k) = fun k => ((36 * Real.pi + 2) * (4 / h₁)) * (if h₁ < (2 : ℝ) ^ (k + 1) then (1 / (2 : ℝ)) ^ k else 0) := by
      ext k
      dsimp [b₂]
      split_ifs <;> ring
    rw [h_eq, tsum_mul_left]
    have h_tail := tsum_ite_pow_two_gt_le hh₁
    have h_pi_nn : 0 ≤ (36 * Real.pi + 2) * (4 / h₁) := by positivity
    have h_mul := mul_le_mul_of_nonneg_left h_tail h_pi_nn
    refine h_mul.trans ?_
    have : (36 * Real.pi + 2) * (4 / h₁) * (4 / h₁) = (36 * Real.pi + 2) * 16 / h₁ ^ 2 := by
      ring
    rw [this]
  have h_tsum_b : ∑' k, b k ≤ 6 * C₁ * E + (36 * Real.pi + 2) * 16 / h₁ ^ 2 := by
    have h_tsum_eq : ∑' k, b k = (∑' k, b₁ k) + (∑' k, b₂ k) :=
      (h_summable_b₁.hasSum.add h_summable_b₂.hasSum).tsum_eq
    rw [h_tsum_eq]
    exact add_le_add h_tsum_b₁ h_tsum_b₂

  have h_int_Ici := setIntegral_le_of_subset_union_iUnion hg_nonneg hsub hg_int_E
    b₀ hb₀_nn h_int_s₀ b hb_nn hb_sum h_int_s hg_int_s₀ hg_int_s
  have h_Ici_bound : ∫ t in Set.Ici T₀, g t ≤ 8 * C₁ * E + 16 * (36 * Real.pi + 2) / h₁ ^ 2 := by
    dsimp [b₀] at h_int_Ici
    have : 16 * (36 * Real.pi + 2) / h₁ ^ 2 = (36 * Real.pi + 2) * 16 / h₁ ^ 2 := by ring
    rw [this]
    linarith [h_int_Ici, h_tsum_b]
  rw [h_symm]
  have h_two_mul : 2 * ∫ t in Set.Ici T₀, g t ≤ 2 * (8 * C₁ * E + 16 * (36 * Real.pi + 2) / h₁ ^ 2) :=
    mul_le_mul_of_nonneg_left h_Ici_bound (by norm_num)
  refine h_two_mul.trans ?_
  have h_final : 2 * (8 * C₁ * E + 16 * (36 * Real.pi + 2) / h₁ ^ 2) ≤ C * (E + 1 / h₁ ^ 2) := by
    dsimp [C]
    have : 2 * (8 * C₁ * E + 16 * (36 * Real.pi + 2) / h₁ ^ 2) =
        16 * C₁ * E + 32 * (36 * Real.pi + 2) * (1 / h₁ ^ 2) := by ring
    rw [this]
    have : (16 * C₁ + 32 * (36 * Real.pi + 2)) * (E + 1 / h₁ ^ 2) =
        16 * C₁ * E + 32 * (36 * Real.pi + 2) * (1 / h₁ ^ 2) +
          (16 * C₁ * (1 / h₁ ^ 2) + 32 * (36 * Real.pi + 2) * E) := by ring
    rw [this]
    have : 0 ≤ 16 * C₁ * (1 / h₁ ^ 2) + 32 * (36 * Real.pi + 2) * E := by positivity
    linarith
  refine h_final.trans_eq ?_
  rfl

end Erdos1201.MR
