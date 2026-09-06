/-
Copyright (c) 2026 Przemek Chojecki, ChatGPT 5.5. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Przemek Chojecki, ChatGPT 5.5
-/
import Mathlib

/-!
# Well-Spaced Point Sets for Short Interval Reductions

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This file provides the reduction to well-spaced point sets used throughout Matomäki–Radziwiłł
Section 8, replacing an integral of a nonnegative bounded function over a set $U \subseteq [-T, T]$
by sums over at most two well-spaced finite point subsets.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Erdos1201.MR

/-- A finset of reals is well-spaced if distinct elements differ by at least 1. -/
def WellSpaced (S : Finset ℝ) : Prop := ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|

/-- The $k$-th unit interval covering $[-T, T]$, defined as $[-T + k, -T + k + 1)$. -/
def I (T : ℝ) (k : ℕ) : Set ℝ := Set.Ico (-T + k) (-T + k + 1)

/-- Unit intervals with strictly ordered indices are disjoint. -/
lemma disjoint_I_of_lt (T : ℝ) {j k : ℕ} (h : j < k) : Disjoint (I T j) (I T k) := by
  rw [Set.disjoint_iff]
  intro x ⟨⟨_, hj2⟩, ⟨hk1, _⟩⟩
  have hjk : (j : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt h
  have : -T + (j : ℝ) + 1 ≤ -T + k := by linarith
  linarith

/-- The family of unit intervals $I(T, k)$ is pairwise disjoint. -/
lemma pairwise_disjoint_I (T : ℝ) : Pairwise fun j k ↦ Disjoint (I T j) (I T k) := by
  intro j k hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact disjoint_I_of_lt T hlt
  · exact (disjoint_I_of_lt T hlt).symm

/-- Any point in $[-T, T]$ is covered by one of the unit intervals
$I(T, k)$ for $k \in \{0, \dots, \lceil 2T \rceil\}$. -/
lemma exists_mem_I_of_mem_Icc (T : ℝ) {x : ℝ} (hx : x ∈ Set.Icc (-T) T) :
    ∃ k ∈ Finset.range (⌈2 * T⌉₊ + 1), x ∈ I T k := by
  have hx1 : -T ≤ x := hx.1
  have hx2 : x ≤ T := hx.2
  have h0 : 0 ≤ x + T := by linarith
  have h2T : x + T ≤ 2 * T := by linarith
  set k := ⌊x + T⌋₊ with hk_def
  use k
  have h_le_N : x + T ≤ ⌈2 * T⌉₊ := by
    apply le_trans h2T
    exact Nat.le_ceil (2 * T)
  have hk_lt : k < ⌈2 * T⌉₊ + 1 := by
    have : k ≤ ⌈2 * T⌉₊ := by
      rw [hk_def]
      exact Nat.floor_le_of_le h_le_N
    omega
  refine ⟨Finset.mem_range.mpr hk_lt, ?_⟩
  dsimp [I]
  constructor
  · have : (k : ℝ) ≤ x + T := Nat.floor_le h0
    linarith
  · have : x + T < (k : ℝ) + 1 := Nat.lt_floor_add_one (x + T)
    linarith

/-- A set $U \subseteq [-T, T]$ is the disjoint union of its intersections with the unit intervals. -/
lemma biUnion_inter_I_eq (T : ℝ) {U : Set ℝ} (hUT : U ⊆ Set.Icc (-T) T) :
    (⋃ k ∈ Finset.range (⌈2 * T⌉₊ + 1), U ∩ I T k) = U := by
  ext x
  simp only [mem_iUnion, exists_prop, mem_inter_iff]
  constructor
  · rintro ⟨k, _, hxU, _⟩
    exact hxU
  · intro hxU
    obtain ⟨k, hk, hxI⟩ := exists_mem_I_of_mem_Icc T (hUT hxU)
    exact ⟨k, hk, hxU, hxI⟩

/-- Points belonging to intervals of the same parity differ by at least 1. -/
lemma one_le_abs_sub_of_same_parity (T : ℝ) {k₁ k₂ : ℕ} (hne : k₁ ≠ k₂)
    (heven : (Even k₁ ∧ Even k₂) ∨ (Odd k₁ ∧ Odd k₂))
    {x y : ℝ} (hx : x ∈ I T k₁) (hy : y ∈ I T k₂) : 1 ≤ |x - y| := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hdiff : k₁ + 2 ≤ k₂ := by
      rcases heven with ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩ | ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
      · rw [← Nat.two_mul, ← Nat.two_mul] at hlt ⊢; omega
      · omega
    have hdiff_real : (k₁ : ℝ) + 2 ≤ k₂ := by exact_mod_cast hdiff
    have hx_ub : x < -T + k₁ + 1 := hx.2
    have hy_lb : -T + k₂ ≤ y := hy.1
    have : 1 ≤ y - x := by linarith
    have : y - x ≤ |y - x| := le_abs_self _
    rw [abs_sub_comm]
    linarith
  · have hdiff : k₂ + 2 ≤ k₁ := by
      rcases heven with ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩ | ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
      · rw [← Nat.two_mul, ← Nat.two_mul] at hlt ⊢; omega
      · omega
    have hdiff_real : (k₂ : ℝ) + 2 ≤ k₁ := by exact_mod_cast hdiff
    have hy_ub : y < -T + k₂ + 1 := hy.2
    have hx_lb : -T + k₁ ≤ x := hx.1
    have : 1 ≤ x - y := by linarith
    have : x - y ≤ |x - y| := le_abs_self _
    linarith

/-- The integral of a nonnegative function bounded by $C$ over a subset of a unit interval
is bounded by $C$. -/
lemma setIntegral_le_const_of_subset_Ico_one {F : ℝ → ℝ} {s : Set ℝ} (hs : MeasurableSet s)
    (hF : ∀ t, 0 ≤ F t) {a : ℝ} (hs_sub : s ⊆ Ico a (a + 1))
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hFC : ∀ x ∈ s, F x ≤ C) :
    ∫ x in s, F x ≤ C := by
  have hs_vol_le : volume s ≤ volume (Ico a (a + 1)) := measure_mono hs_sub
  rw [Real.volume_Ico] at hs_vol_le
  have h_diff : (a + 1) - a = 1 := by ring
  rw [h_diff, ENNReal.ofReal_one] at hs_vol_le
  have hs_lt_top : volume s < ∞ := lt_of_le_of_lt hs_vol_le ENNReal.one_lt_top
  have h_norm : ∀ x ∈ s, ‖F x‖ ≤ C := by
    intro x hx
    rw [Real.norm_of_nonneg (hF x)]
    exact hFC x hx
  have h_bound := norm_setIntegral_le_of_norm_le_const hs_lt_top h_norm
  have h_int_nonneg : 0 ≤ ∫ x in s, F x := setIntegral_nonneg hs (fun x _ ↦ hF x)
  rw [Real.norm_of_nonneg h_int_nonneg] at h_bound
  have h_real_le : (volume s).toReal ≤ 1 := by
    have h_toReal := (ENNReal.toReal_le_toReal hs_lt_top.ne ENNReal.one_ne_top).mpr hs_vol_le
    simpa using h_toReal
  have h_mul : C * (volume s).toReal ≤ C * 1 := mul_le_mul_of_nonneg_left h_real_le hC_nonneg
  rw [mul_one] at h_mul
  exact le_trans h_bound h_mul

/-- In any nonempty subset $s$ of a unit interval, there exists a point $t \in s$
such that the integral of $F$ over $s$ is at most $F(t) + \delta$. -/
lemma exists_point_le_setIntegral_add (F : ℝ → ℝ) (s : Set ℝ) (hs_meas : MeasurableSet s)
    (hF_nonneg : ∀ t, 0 ≤ F t) (B : ℝ) (hFb : ∀ t, F t ≤ B)
    {a : ℝ} (hs_sub : s ⊆ Ico a (a + 1)) (hs_nonempty : s.Nonempty)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ t ∈ s, ∫ x in s, F x ≤ F t + δ := by
  have hE_nonempty : (F '' s).Nonempty := hs_nonempty.image F
  have hE_bdd : BddAbove (F '' s) := by
    refine ⟨B, ?_⟩
    rintro y ⟨x, _, rfl⟩
    exact hFb x
  set M := sSup (F '' s) with hM_def
  have hM_ub : ∀ x ∈ s, F x ≤ M := fun x hx ↦ le_csSup hE_bdd (mem_image_of_mem F hx)
  obtain ⟨x0, hx0⟩ := hs_nonempty
  have hM_nonneg : 0 ≤ M := le_trans (hF_nonneg x0) (hM_ub x0 hx0)
  have h_int_le_M : ∫ x in s, F x ≤ M :=
    setIntegral_le_const_of_subset_Ico_one hs_meas hF_nonneg hs_sub hM_nonneg hM_ub
  have h_lt_M : M - δ < M := sub_lt_self M hδ
  obtain ⟨y, hyE, hlt_y⟩ := exists_lt_of_lt_csSup hE_nonempty h_lt_M
  obtain ⟨t, ht, rfl⟩ := hyE
  use t, ht
  have : M ≤ F t + δ := by linarith
  exact le_trans h_int_le_M this

/-- A bounded measurable function is integrable on a set of finite measure. -/
lemma integrableOn_of_bounded_of_measure_lt_top {F : ℝ → ℝ} {s : Set ℝ} (hFm : Measurable F)
    {B : ℝ} (hFb : ∀ t, F t ≤ B) (hF_nonneg : ∀ t, 0 ≤ F t)
    (hs_vol : volume s < ∞) :
    IntegrableOn F s volume := by
  refine IntegrableOn.of_bound hs_vol hFm.aestronglyMeasurable (max B 0) ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (hF_nonneg x)]
  exact le_trans (hFb x) (le_max_left B 0)

/-- Main theorem: Well-spaced point sets reduction for integrals over a bounded measurable set. -/
theorem exists_wellSpaced_of_integral (F : ℝ → ℝ) (U : Set ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hU : MeasurableSet U) (hUT : U ⊆ Set.Icc (-T) T) (hF : ∀ t, 0 ≤ F t)
    (hFm : Measurable F) (hFb : ∃ B, ∀ t, F t ≤ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ S₁ S₂ : Finset ℝ, WellSpaced S₁ ∧ WellSpaced S₂ ∧ (↑S₁ ⊆ U) ∧ (↑S₂ ⊆ U) ∧
      S₁.card ≤ ⌈2 * T⌉₊ + 1 ∧ S₂.card ≤ ⌈2 * T⌉₊ + 1 ∧
      ∫ t in U, F t ≤ (∑ t ∈ S₁, F t) + (∑ t ∈ S₂, F t) + ε := by
  classical
  have _ := hT
  obtain ⟨B, hB⟩ := hFb
  set N := ⌈2 * T⌉₊ with hN_def
  set K := Finset.range (N + 1) with hK_def
  have hN_pos : (0 : ℝ) < (N + 1 : ℝ) := by positivity
  set δ : ℝ := ε / (N + 1 : ℝ) with hδ_def
  have hδ_pos : 0 < δ := div_pos hε hN_pos

  have h_choice : ∀ k, (U ∩ I T k).Nonempty →
      { t : ℝ // t ∈ U ∩ I T k ∧ ∫ x in U ∩ I T k, F x ≤ F t + δ } := by
    intro k hne
    have hs_sub : U ∩ I T k ⊆ Ico (-T + k) (-T + k + 1) := inter_subset_right
    have hs_meas : MeasurableSet (U ∩ I T k) := hU.inter measurableSet_Ico
    have h_ex := exists_point_le_setIntegral_add F (U ∩ I T k) hs_meas hF B hB hs_sub hne δ hδ_pos
    exact Classical.indefiniteDescription _ h_ex

  let g : ℕ → ℝ := fun k ↦
    if h : (U ∩ I T k).Nonempty then (h_choice k h).val else 0

  have hg_spec : ∀ k (h : (U ∩ I T k).Nonempty),
      g k ∈ U ∩ I T k ∧ ∫ x in U ∩ I T k, F x ≤ F (g k) + δ := by
    intro k h
    dsimp [g]
    simp only [h, dite_true]
    exact (h_choice k h).property

  have hg_mem_I : ∀ k (h : (U ∩ I T k).Nonempty), g k ∈ I T k :=
    fun k h ↦ (hg_spec k h).1.2

  have hg_mem_U : ∀ k (h : (U ∩ I T k).Nonempty), g k ∈ U :=
    fun k h ↦ (hg_spec k h).1.1

  have hg_inj : ∀ j k, (U ∩ I T j).Nonempty → (U ∩ I T k).Nonempty → g j = g k → j = k := by
    intro j k hj hk h_eq
    by_contra hne
    have h_disj := pairwise_disjoint_I T hne
    have hj_in : g j ∈ I T j := hg_mem_I j hj
    have hk_in : g k ∈ I T k := hg_mem_I k hk
    rw [h_eq] at hj_in
    have : g k ∈ I T j ∩ I T k := ⟨hj_in, hk_in⟩
    exact Set.disjoint_iff.mp h_disj this

  set K_good := K.filter (fun k ↦ (U ∩ I T k).Nonempty) with hK_good_def
  set K_even := K_good.filter Even with hK_even_def
  set K_odd := K_good.filter (fun k ↦ ¬ Even k) with hK_odd_def

  set S₁ := K_even.image g with hS₁_def
  set S₂ := K_odd.image g with hS₂_def

  refine ⟨S₁, S₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- WellSpaced S₁
    intro s hs t ht hne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    have hj_good : (U ∩ I T j).Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
    have hk_good : (U ∩ I T k).Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    have hj_even : Even j := (Finset.mem_filter.mp hj).2
    have hk_even : Even k := (Finset.mem_filter.mp hk).2
    have hjk_ne : j ≠ k := by
      rintro rfl
      exact hne rfl
    exact one_le_abs_sub_of_same_parity T hjk_ne (Or.inl ⟨hj_even, hk_even⟩) (hg_mem_I j hj_good) (hg_mem_I k hk_good)
  · -- WellSpaced S₂
    intro s hs t ht hne
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht
    have hj_good : (U ∩ I T j).Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
    have hk_good : (U ∩ I T k).Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    have hj_odd : Odd j := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hj).2
    have hk_odd : Odd k := Nat.not_even_iff_odd.mp (Finset.mem_filter.mp hk).2
    have hjk_ne : j ≠ k := by
      rintro rfl
      exact hne rfl
    exact one_le_abs_sub_of_same_parity T hjk_ne (Or.inr ⟨hj_odd, hk_odd⟩) (hg_mem_I j hj_good) (hg_mem_I k hk_good)
  · -- ↑S₁ ⊆ U
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    have hk_good : (U ∩ I T k).Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    exact hg_mem_U k hk_good
  · -- ↑S₂ ⊆ U
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
    have hk_good : (U ∩ I T k).Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
    exact hg_mem_U k hk_good
  · -- S₁.card ≤ ⌈2 * T⌉₊ + 1
    have h1 : S₁.card ≤ K_even.card := Finset.card_image_le
    have h2 : K_even.card ≤ K.card := by
      apply le_trans (Finset.card_filter_le K_good Even)
      exact Finset.card_filter_le K _
    have h3 : K.card = N + 1 := Finset.card_range (N + 1)
    omega
  · -- S₂.card ≤ ⌈2 * T⌉₊ + 1
    have h1 : S₂.card ≤ K_odd.card := Finset.card_image_le
    have h2 : K_odd.card ≤ K.card := by
      apply le_trans (Finset.card_filter_le K_good _)
      exact Finset.card_filter_le K _
    have h3 : K.card = N + 1 := Finset.card_range (N + 1)
    omega
  · -- ∫ t in U, F t ≤ (∑ t ∈ S₁, F t) + (∑ t ∈ S₂, F t) + ε
    have h_cov : (⋃ k ∈ K, U ∩ I T k) = U := biUnion_inter_I_eq T hUT
    have h_int_decomp : ∫ t in U, F t = ∑ k ∈ K, ∫ t in U ∩ I T k, F t := by
      trans ∫ t in ⋃ k ∈ K, U ∩ I T k, F t
      · rw [h_cov]
      · apply integral_biUnion_finset K
        · intro i _
          exact hU.inter measurableSet_Ico
        · intro j _ k _ hne
          exact (pairwise_disjoint_I T hne).mono inter_subset_right inter_subset_right
        · intro i _
          have hs_sub : U ∩ I T i ⊆ Ico (-T + i) (-T + i + 1) := inter_subset_right
          have hs_vol_le : volume (U ∩ I T i) ≤ volume (Ico (-T + i) (-T + i + 1)) := measure_mono hs_sub
          rw [Real.volume_Ico] at hs_vol_le
          have h_diff : (-T + (i : ℝ) + 1) - (-T + i) = 1 := by ring
          rw [h_diff, ENNReal.ofReal_one] at hs_vol_le
          have hs_vol_lt : volume (U ∩ I T i) < ∞ := lt_of_le_of_lt hs_vol_le ENNReal.one_lt_top
          exact integrableOn_of_bounded_of_measure_lt_top hFm hB hF hs_vol_lt

    have h_sum_good : ∑ k ∈ K, ∫ t in U ∩ I T k, F t = ∑ k ∈ K_good, ∫ t in U ∩ I T k, F t := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro k hk hnot_good
      have h_empty : U ∩ I T k = ∅ := by
        simp only [Finset.mem_filter, not_and] at hnot_good
        have := hnot_good hk
        exact not_nonempty_iff_eq_empty.mp this
      rw [h_empty, setIntegral_empty]

    have h_le_good : ∑ k ∈ K_good, ∫ t in U ∩ I T k, F t ≤ ∑ k ∈ K_good, (F (g k) + δ) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk_good : (U ∩ I T k).Nonempty := (Finset.mem_filter.mp hk).2
      exact (hg_spec k hk_good).2

    have h_sum_split : ∑ k ∈ K_good, (F (g k) + δ) = (∑ k ∈ K_good, F (g k)) + (K_good.card : ℝ) * δ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

    have h_good_le_eps : (K_good.card : ℝ) * δ ≤ ε := by
      have h_card_le : (K_good.card : ℝ) ≤ (N + 1 : ℝ) := by
        have : K_good.card ≤ K.card := Finset.card_filter_le K _
        have hK_card : K.card = N + 1 := Finset.card_range (N + 1)
        rw [hK_card] at this
        exact_mod_cast this
      have h_mul_le : (K_good.card : ℝ) * δ ≤ (N + 1 : ℝ) * δ := mul_le_mul_of_nonneg_right h_card_le (le_of_lt hδ_pos)
      have h_cancel : (N + 1 : ℝ) * δ = ε := by
        dsimp [δ]
        rw [mul_div_cancel₀ ε (ne_of_gt hN_pos)]
      linarith

    have h_part : ∑ k ∈ K_good, F (g k) = (∑ k ∈ K_even, F (g k)) + (∑ k ∈ K_odd, F (g k)) := by
      have := Finset.sum_filter_add_sum_filter_not K_good (fun k ↦ Even k) (fun k ↦ F (g k))
      exact this.symm

    have h_inj_even : ∀ x ∈ K_even, ∀ y ∈ K_even, g x = g y → x = y := by
      intro x hx y hy h_eq
      have hx_good : (U ∩ I T x).Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      have hy_good : (U ∩ I T y).Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
      exact hg_inj x y hx_good hy_good h_eq

    have h_inj_odd : ∀ x ∈ K_odd, ∀ y ∈ K_odd, g x = g y → x = y := by
      intro x hx y hy h_eq
      have hx_good : (U ∩ I T x).Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      have hy_good : (U ∩ I T y).Nonempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2
      exact hg_inj x y hx_good hy_good h_eq

    rw [Finset.sum_image h_inj_even]
    rw [Finset.sum_image h_inj_odd]
    linarith

end Erdos1201.MR
