import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Ranges
import Erdos1201.MR.Setup
import Erdos1201.MR.Analysis.WellSpaced
import Erdos1201.MR.Polynomials.PrimePolyMoments

/-!
# Matomäki–Radziwiłł: Cardinality of Well-Spaced Subsets of Uset

This module establishes the upper bound for the cardinality of any well-spaced subset
of the exceptional set $U$, corresponding to Proposition 1 / Lemma 8 of
Matomäki–Radziwiłł (arXiv:1501.04585v4).

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

open scoped BigOperators
open Classical

namespace Erdos1201.MR

lemma log_sixteen_gt_exp_one : Real.exp 1 < Real.log 16 := by
  have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    rw [h16, Real.log_pow (2 : ℝ) 4]
    push_cast
    ring
  have hlog2 := Real.log_two_gt_d9
  have he := Real.exp_one_lt_d9
  linarith

lemma one_le_log_log_sixteen : 1 ≤ Real.log (Real.log 16) := by
  have h := log_sixteen_gt_exp_one
  have h_exp_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hlog := Real.log_lt_log h_exp_pos h
  rw [Real.log_exp] at hlog
  linarith

lemma one_le_log_log {X : ℕ} (hX : 16 ≤ X) : 1 ≤ Real.log (Real.log (X : ℝ)) := by
  have h16 : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog16_pos : 0 < Real.log 16 := by
    have := log_sixteen_gt_exp_one
    positivity
  have hlog_le : Real.log 16 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) h16
  have hloglog_le : Real.log (Real.log 16) ≤ Real.log (Real.log (X : ℝ)) :=
    Real.log_le_log hlog16_pos hlog_le
  exact one_le_log_log_sixteen.trans hloglog_le

lemma log_add_two_le_log_add_one {y : ℝ} (hy : 2 ≤ y) :
    Real.log (y + 2) ≤ Real.log y + 1 := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h_mul : y + 2 ≤ Real.exp 1 * y := by
    calc y + 2 ≤ y + y := by linarith
    _ = 2 * y := by ring
    _ ≤ Real.exp 1 * y := by nlinarith
  have hy_pos : 0 < y := by linarith
  have h_pos : 0 < y + 2 := by linarith
  have hlog := Real.log_le_log h_pos h_mul
  rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hy_pos), Real.log_exp] at hlog
  linarith

lemma log_add_one_le_log_add_one {p : ℝ} (hp : 1 ≤ p) :
    Real.log (p + 1) ≤ Real.log p + 1 := by
  have hp_pos : 0 < p := by linarith
  have hp1_pos : 0 < p + 1 := by linarith
  have h_le : p + 1 ≤ Real.exp 1 * p := by
    have he : 2 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc p + 1 ≤ p + p := by linarith
    _ = 2 * p := by ring
    _ ≤ Real.exp 1 * p := by nlinarith
  have hlog := Real.log_le_log hp1_pos h_le
  rw [Real.log_mul (ne_of_gt (Real.exp_pos 1)) (ne_of_gt hp_pos), Real.log_exp] at hlog
  linarith

lemma log_sub_one_ge_sub_one {y : ℝ} (hy : Real.exp 1 ≤ y) :
    Real.log y - 1 ≤ Real.log (y - 1) := by
  have he : 2 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have _hy2 : 2 ≤ y := he.trans hy
  have hpos : 0 < (1 / 2 : ℝ) * y := by positivity
  have h_le : (1 / 2 : ℝ) * y ≤ y - 1 := by linarith
  have hlog := Real.log_le_log hpos h_le
  have hy_pos : 0 < y := by positivity
  rw [Real.log_mul (by norm_num) (ne_of_gt hy_pos)] at hlog
  have _hlog2_lt : Real.log 2 < 1 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (by norm_num) (by linarith [Real.exp_one_gt_d9])
  have hlog_half : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  rw [hlog_half] at hlog
  linarith

lemma vH_ge_one {η L logP vH : ℝ}
    (hη0 : 0 < η) (_hη : η < 1 / 6) (hL : 1 ≤ L)
    (hlogP : (20 / η) * L ≤ logP)
    (hvH : logP - 1 ≤ vH) :
    1 ≤ vH := by
  have : 6 < 1 / η := by
    rw [lt_div_iff₀ hη0]
    linarith
  have : 120 < 20 / η := by
    calc 120 = 20 * 6 := by norm_num
    _ < 20 * (1 / η) := by nlinarith
    _ = 20 / η := by ring
  have _h2 : (20 / η) * 1 ≤ (20 / η) * L :=
    mul_le_mul_of_nonneg_left hL (by positivity)
  linarith

lemma two_le_nineteen_div_eta_mul_log_log {η L : ℝ}
    (hη0 : 0 < η) (_hη : η < 1 / 6) (hL : 1 ≤ L) :
    2 ≤ (19 / η) * L := by
  have h1 : 6 < 1 / η := by
    rw [lt_div_iff₀ hη0]
    linarith
  have h2 : 114 < 19 / η := by
    calc 114 = 19 * 6 := by norm_num
    _ < 19 * (1 / η) := by nlinarith
    _ = 19 / η := by ring
  have _h3 : 114 < (19 / η) * L := by
    calc 114 = 114 * 1 := by ring
    _ < (19 / η) * 1 := by linarith
    _ ≤ (19 / η) * L := mul_le_mul_of_nonneg_left hL (by positivity)
  linarith

lemma five_le_of_two_le_log {P₀ : ℕ} (h : 2 ≤ Real.log (P₀ : ℝ)) : 5 ≤ P₀ := by
  have he_sq : (Real.exp 1) ^ 2 = Real.exp 2 := by
    have : (2 : ℝ) = 1 + 1 := by norm_num
    rw [this, Real.exp_add, sq]
  have _he2 : 7.38 < Real.exp 2 := by
    rw [← he_sq]
    have : (2.718 : ℝ) ^ 2 < (Real.exp 1) ^ 2 := by
      nlinarith [Real.exp_pos 1, Real.exp_one_gt_d9]
    linarith
  have h5_lt_exp2 : (5 : ℝ) < Real.exp 2 := by linarith
  have hlog5 : Real.log 5 < 2 := by
    have := Real.log_lt_log (by norm_num) h5_lt_exp2
    rw [Real.log_exp] at this
    exact this
  have hP₀_pos : 0 < (P₀ : ℝ) := by
    by_contra hc
    have : (P₀ : ℝ) = 0 := by linarith [show 0 ≤ (P₀ : ℝ) by positivity]
    rw [this, Real.log_zero] at h
    linarith
  have h5_lt_P₀ : (5 : ℝ) < (P₀ : ℝ) := by
    have : Real.log 5 < Real.log (P₀ : ℝ) := hlog5.trans_le h
    exact (Real.log_lt_log_iff (by norm_num) hP₀_pos).mp this
  exact (Nat.cast_lt.mp h5_lt_P₀).le

lemma card_Icc_floor_ceil_le (a b : ℝ) (hb : 0 ≤ b) :
    (((Finset.Icc ⌊a⌋₊ ⌈b⌉₊).card : ℝ) ≤ b + 2) := by
  by_cases h : ⌊a⌋₊ ≤ ⌈b⌉₊
  · rw [Nat.card_Icc]
    have _h_ceil : (⌈b⌉₊ : ℝ) < b + 1 := Nat.ceil_lt_add_one hb
    have h_sub : ((⌈b⌉₊ + 1 - ⌊a⌋₊ : ℕ) : ℝ) ≤ (⌈b⌉₊ + 1 : ℕ) := by
      exact_mod_cast Nat.sub_le (⌈b⌉₊ + 1) ⌊a⌋₊
    push_cast at h_sub
    linarith
  · rw [Finset.Icc_eq_empty_of_lt (not_le.mp h)]
    simp
    linarith

lemma exp_half_lt : Real.exp (1 / 2) < 1.65 := by
  have hpos : 0 ≤ Real.exp (1 / 2) := (Real.exp_pos _).le
  have h165 : 0 ≤ (1.65 : ℝ) := by norm_num
  rw [← sq_lt_sq₀ hpos h165]
  have h_sq : (Real.exp (1 / 2)) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [h_sq]
  have _h2 : Real.exp 1 < 2.72 := Real.exp_one_lt_d9.trans (by norm_num)
  have _h3 : (1.65 : ℝ) ^ 2 = 2.7225 := by norm_num
  linarith

lemma exp_inv_H_le_exp_half {H : ℝ} (hH : 2 ≤ H) : Real.exp (1 / H) ≤ Real.exp (1 / 2) := by
  apply Real.exp_le_exp.mpr
  have _hHpos : 0 < H := by linarith
  exact one_div_le_one_div_of_le (by norm_num) hH

lemma exp_half_mul_add_one_le {P₀ : ℝ} (hP₀ : 5 ≤ P₀) :
    (P₀ + 1) * Real.exp (1 / 2) ≤ 2 * P₀ := by
  have _he := exp_half_lt
  calc (P₀ + 1) * Real.exp (1 / 2)
    _ ≤ (P₀ + 1) * 1.65 := by nlinarith [Real.exp_pos (1 / 2)]
    _ = 1.65 * P₀ + 1.65 := by ring
    _ ≤ 1.65 * P₀ + 0.35 * P₀ := by nlinarith
    _ = 2 * P₀ := by ring

lemma shortPrimeRange_subset_Ioc_prime (P Q : ℕ) (H : ℝ) (v : ℕ)
    (hH : 2 ≤ H) (P₀ : ℕ) (hP₀_le : (P₀ : ℝ) < Real.exp ((v : ℝ) / H))
    (hP₀_ge : Real.exp ((v : ℝ) / H) ≤ (P₀ : ℝ) + 1) (hP₀_5 : 5 ≤ P₀) :
    shortPrimeRange P Q H v ⊆ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime := by
  intro p hp
  rw [mem_shortPrimeRange] at hp
  rw [Finset.mem_filter, Finset.mem_Ioc]
  refine ⟨⟨?_, ?_⟩, hp.1.1⟩
  · have : (P₀ : ℝ) < (p : ℝ) := hP₀_le.trans_le hp.2.1
    exact_mod_cast this
  · have hp_lt : (p : ℝ) < Real.exp (((v : ℝ) + 1) / H) := hp.2.2
    have h_add : ((v : ℝ) + 1) / H = (v : ℝ) / H + 1 / H := by ring
    rw [h_add, Real.exp_add] at hp_lt
    have h_exp1 : Real.exp (1 / H) ≤ Real.exp (1 / 2) := exp_inv_H_le_exp_half hH
    have h_expv : Real.exp ((v : ℝ) / H) ≤ (P₀ : ℝ) + 1 := hP₀_ge
    have h_exp_mul : Real.exp ((v : ℝ) / H) * Real.exp (1 / H) ≤ ((P₀ : ℝ) + 1) * Real.exp (1 / 2) :=
      mul_le_mul h_expv h_exp1 (Real.exp_pos _).le (by linarith)
    have h_2P₀ : ((P₀ : ℝ) + 1) * Real.exp (1 / 2) ≤ 2 * (P₀ : ℝ) := by
      have : (5 : ℝ) ≤ (P₀ : ℝ) := by exact_mod_cast hP₀_5
      exact exp_half_mul_add_one_le this
    have _hp_le : (p : ℝ) < 2 * (P₀ : ℝ) := by linarith
    have : p ≤ 2 * P₀ := by
      have : (p : ℝ) ≤ (2 * P₀ : ℕ) := by
        push_cast
        linarith
      exact_mod_cast this
    exact this

lemma dirichletPoly_eq_Qpoly (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (P₀ : ℕ)
    (hsub : shortPrimeRange P Q H v ⊆ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime) (s : ℂ) :
    dirichletPoly (fun p => if p ∈ shortPrimeRange P Q H v then fX β X p else 0)
      ((Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime) s =
    Qpoly β X P Q H v s := by
  unfold Qpoly dirichletPoly
  set f : ℕ → ℂ := fun p => (if p ∈ shortPrimeRange P Q H v then fX β X p else 0) * (p : ℂ) ^ (-s)
  have h_sum : ∑ x ∈ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime, f x = ∑ x ∈ shortPrimeRange P Q H v, f x := by
    apply (Finset.sum_subset hsub ?_).symm
    intro x _hx hnot
    dsimp [f]
    rw [ite_eq_right hnot, zero_mul]
  rw [h_sum]
  apply Finset.sum_congr rfl
  intro x hx
  dsimp [f]
  rw [ite_eq_left hx]

lemma norm_a_le_one (β : ℝ) (X P Q : ℕ) (H : ℝ) (v p : ℕ) :
    ‖if p ∈ shortPrimeRange P Q H v then fX β X p else 0‖ ≤ 1 := by
  split_ifs with _h
  · exact norm_fX_le_one β X p
  · simp

lemma WellSpaced.filter {s : Finset ℝ} (hs : WellSpaced s) (p : ℝ → Prop) [DecidablePred p] :
    WellSpaced (s.filter p) := by
  intro x hx y hy hne
  rw [Finset.mem_filter] at hx hy
  exact hs x hx.1 y hy.1 hne

lemma not_good_iff {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (j : Fin J) (t : ℝ) :
    ¬ S.Good hJ β X j t ↔
      ∃ v ∈ S.Ij hJ j, Real.exp (-(alpha η (j.val + 1)) * v / S.Hj hJ j) <
        ‖Qpoly β X (S.P j) (S.Q j) (S.Hj hJ j) v ((1 : ℂ) + t * Complex.I)‖ := by
  unfold RangeSystem.Good
  simp only [not_forall, not_le, exists_prop]

lemma card_le_sum_card_filter {α : Type*} [DecidableEq α] (s : Finset α) {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (p : ι → α → Prop) [∀ i, DecidablePred (p i)]
    (h_cov : ∀ x ∈ s, ∃ i ∈ I, p i x) :
    s.card ≤ ∑ i ∈ I, (s.filter (p i)).card := by
  have h_sub : s ⊆ I.biUnion (fun i => s.filter (p i)) := by
    intro x hx
    rcases h_cov x hx with ⟨i, hi, hpi⟩
    rw [Finset.mem_biUnion]
    exact ⟨i, hi, Finset.mem_filter.mpr ⟨hx, hpi⟩⟩
  have h1 := Finset.card_le_card h_sub
  have h2 := Finset.card_biUnion_le (s := I) (t := fun i => s.filter (p i))
  exact h1.trans h2

lemma log_P0_ge_nineteen_div_eta {η L logP vH P0 : ℝ}
    (hη0 : 0 < η) (_hη : η < 1 / 6) (hL : 1 ≤ L)
    (hlogP : (20 / η) * L ≤ logP)
    (hvH : logP - 1 ≤ vH)
    (hP0_log : vH - 1 ≤ Real.log P0) :
    (19 / η) * L ≤ Real.log P0 := by
  have h_inv : 6 < 1 / η := by
    rw [lt_div_iff₀ hη0]
    linarith
  have _h_6L : 6 < (1 / η) * L := by
    calc 6 = 6 * 1 := by ring
    _ < (1 / η) * 1 := by linarith
    _ ≤ (1 / η) * L := mul_le_mul_of_nonneg_left hL (by linarith)
  have _h20 : (20 / η) * L = (19 / η) * L + (1 / η) * L := by ring
  linarith

lemma factor1_exp_le {α η L vH logP : ℝ}
    (_hα_pos : 0 < α) (hα_le : α ≤ 1 / 4)
    (_hη_pos : 0 < η) (hL : 1 ≤ L)
    (hlogP : (19 / η) * L ≤ logP)
    (hvH : vH ≤ logP + 1) :
    2 * (α * vH) / logP ≤ 2 * α + η / 38 := by
  have hlogP_pos : 0 < logP := by
    have : 0 < (19 / η) * L := by positivity
    linarith
  have h_div : vH / logP ≤ 1 + 1 / logP := by
    have : vH / logP ≤ (logP + 1) / logP := div_le_div_of_nonneg_right hvH hlogP_pos.le
    have : (logP + 1) / logP = 1 + 1 / logP := by
      rw [add_div, div_self (ne_of_gt hlogP_pos)]
    linarith
  have h_mul : 2 * (α * vH) / logP = (2 * α) * (vH / logP) := by ring
  rw [h_mul]
  have h_step1 : (2 * α) * (vH / logP) ≤ (2 * α) * (1 + 1 / logP) :=
    mul_le_mul_of_nonneg_left h_div (by linarith)
  have h_step2 : (2 * α) * (1 + 1 / logP) = 2 * α + (2 * α) / logP := by ring
  rw [h_step2] at h_step1
  have h_step3 : (2 * α) / logP ≤ (1 / 2 : ℝ) / logP := by
    exact div_le_div_of_nonneg_right (by linarith) hlogP_pos.le
  have h_step4 : (1 / 2 : ℝ) / logP ≤ η / (38 * L) := by
    have h19 : 0 < (19 / η) * L := by positivity
    have h_inv : 1 / logP ≤ 1 / ((19 / η) * L) := one_div_le_one_div_of_le h19 hlogP
    have h_half : (1 / 2 : ℝ) / logP = (1 / 2) * (1 / logP) := by ring
    have h_rhs : η / (38 * L) = (1 / 2) * (1 / ((19 / η) * L)) := by
      have : (19 / η) * L = (19 * L) / η := by ring
      rw [this, one_div_div]
      ring
    rw [h_half, h_rhs]
    exact mul_le_mul_of_nonneg_left h_inv (by norm_num)
  have _h_step5 : η / (38 * L) ≤ η / 38 := by
    have : (38 : ℝ) ≤ 38 * L := by linarith
    have h38 : 0 < (38 : ℝ) := by norm_num
    have _h38L : 0 < 38 * L := by positivity
    have h_inv : 1 / (38 * L) ≤ 1 / 38 := one_div_le_one_div_of_le h38 this
    have : η / (38 * L) = η * (1 / (38 * L)) := by ring
    have : η / 38 = η * (1 / 38) := by ring
    nlinarith
  linarith

lemma V_sq_bound {α vH logQ sqrtLogX : ℝ}
    (_hα_pos : 0 ≤ α) (hα_le : α ≤ 1 / 4)
    (hvH : vH ≤ logQ + 1)
    (hlogQ_nonneg : 0 ≤ logQ)
    (hlogQ : logQ ≤ sqrtLogX) :
    Real.exp (2 * α * vH) ≤ Real.exp 1 * Real.exp sqrtLogX := by
  have h1 : 2 * α ≤ 1 / 2 := by linarith
  have h2 : 0 ≤ 2 * α := by linarith
  have h_prod : 2 * α * vH ≤ (1 / 2 : ℝ) * (logQ + 1) := by
    calc 2 * α * vH
      _ ≤ (2 * α) * (logQ + 1) := by
        have := mul_le_mul_of_nonneg_left hvH h2
        linarith
      _ ≤ (1 / 2 : ℝ) * (logQ + 1) := mul_le_mul_of_nonneg_right h1 (by linarith)
  have h_prod2 : (1 / 2 : ℝ) * (logQ + 1) ≤ sqrtLogX + 1 := by
    linarith
  have h_exp := Real.exp_le_exp.mpr (h_prod.trans h_prod2)
  rw [Real.exp_add, mul_comm (Real.exp sqrtLogX)] at h_exp
  exact h_exp

lemma factor3_exp_le {η L logT logP : ℝ}
    (_hη_pos : 0 < η) (hL : 1 ≤ L)
    (hlogP : (19 / η) * L ≤ logP)
    (hlogT : 0 ≤ logT)
    (hlog_add : Real.log (logT + 2) ≤ L + 1) :
    2 * (logT / logP) * Real.log (logT + 2) ≤ (4 * η / 19) * logT := by
  have _hlogP_pos : 0 < logP := by
    have : 0 < (19 / η) * L := by positivity
    linarith
  have h19 : 0 < (19 / η) * L := by positivity
  have h_quot : Real.log (logT + 2) / logP ≤ (L + 1) / ((19 / η) * L) := by
    have h_inv : 1 / logP ≤ 1 / ((19 / η) * L) := one_div_le_one_div_of_le h19 hlogP
    have _h_log_pos : 0 ≤ Real.log (logT + 2) := by
      have : 1 ≤ logT + 2 := by linarith
      exact Real.log_nonneg this
    have : Real.log (logT + 2) / logP = Real.log (logT + 2) * (1 / logP) := by ring
    have h_rhs : (L + 1) / ((19 / η) * L) = (L + 1) * (1 / ((19 / η) * L)) := by ring
    rw [this, h_rhs]
    exact mul_le_mul hlog_add h_inv (by positivity) (by linarith)
  have h_ratio : (L + 1) / ((19 / η) * L) ≤ 2 * η / 19 := by
    have : (L + 1) / ((19 / η) * L) = (η / 19) * ((L + 1) / L) := by
      have : (19 / η) * L = (19 * L) / η := by ring
      rw [this, div_div_eq_mul_div]
      ring
    rw [this]
    have h_L1 : (L + 1) / L ≤ 2 := by
      have : (L + 1) / L = 1 + 1 / L := by
        rw [add_div, div_self (by linarith)]
      rw [this]
      have : 1 / L ≤ 1 := by
        rw [one_div]
        have := one_div_le_one_div_of_le (by linarith) hL
        norm_num at this
        exact this
      linarith
    have : (η / 19) * ((L + 1) / L) ≤ (η / 19) * 2 :=
      mul_le_mul_of_nonneg_left h_L1 (by positivity)
    linarith
  have h_comb : Real.log (logT + 2) / logP ≤ 2 * η / 19 := h_quot.trans h_ratio
  have h_rew : 2 * (logT / logP) * Real.log (logT + 2) = (2 * logT) * (Real.log (logT + 2) / logP) := by ring
  rw [h_rew]
  have := mul_le_mul_of_nonneg_left h_comb (by linarith : 0 ≤ 2 * logT)
  linarith

lemma five_pow_mul_factorial_le_pow (k : ℕ) :
    (5 : ℝ) ^ k * (k.factorial : ℝ) ≤ (5 * (k : ℝ)) ^ k := by
  have h_fact : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
    exact_mod_cast Nat.factorial_le_pow k
  have h_mul : (5 : ℝ) ^ k * (k.factorial : ℝ) ≤ (5 : ℝ) ^ k * (k : ℝ) ^ k :=
    mul_le_mul_of_nonneg_left h_fact (by positivity)
  rw [← mul_pow] at h_mul
  exact h_mul

lemma factor4_exp_le {η L logT logX : ℝ} {k : ℕ}
    (_hη_pos : 0 < η) (_hη : η < 1 / 6) (hL : 1 ≤ L)
    (hlogX : Real.exp 1 ≤ logX) (hL_eq : L = Real.log logX)
    (hlogT_nonneg : 0 ≤ logT) (hlogT_le : logT ≤ logX)
    (hk_le : (k : ℝ) ≤ (η / 19) * (logT / L) + 1)
    (hk_pos : 1 ≤ k) :
    (5 * (k : ℝ)) ^ k ≤ Real.exp ((3 * η / 19) * logT) * Real.exp 2 * logX := by
  have _hk_rpos : 0 < (k : ℝ) := by positivity
  have h5k_pos : 0 < 5 * (k : ℝ) := by positivity
  have hlogX_pos : 0 < logX := by linarith [Real.exp_pos 1]
  have h_pow : (5 * (k : ℝ)) ^ k = Real.exp (k * Real.log (5 * k)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos h5k_pos]
    ring_nf
  rw [h_pow]
  have _hu_le : (η / 19) * (logT / L) ≤ logX := by
    have h1 : η / 19 ≤ 1 := by linarith
    have h2 : logT / L ≤ logX := by
      have _ : logT ≤ logX := hlogT_le
      have _ : 1 ≤ L := hL
      have hLpos : 0 < L := by linarith
      have : logT / L ≤ logX / L := div_le_div_of_nonneg_right hlogT_le hLpos.le
      have : logX / L ≤ logX / 1 := by
        apply div_le_div_of_nonneg_left hlogX_pos.le (by norm_num) hL
      linarith
    have _ : 0 ≤ logT / L := div_nonneg hlogT_nonneg (by linarith)
    have : (η / 19) * (logT / L) ≤ 1 * logX := mul_le_mul h1 h2 (by positivity) (by linarith)
    linarith
  have _hk_le_logX1 : (k : ℝ) ≤ logX + 1 := by linarith
  have h5k_le : 5 * (k : ℝ) ≤ Real.exp 2 * logX := by
    have _he1 : 2.718 < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have he_sq : (Real.exp 1) ^ 2 = Real.exp 2 := by
      have : (2 : ℝ) = 1 + 1 := by norm_num
      rw [this, Real.exp_add, sq]
    have _he2 : 7.38 < Real.exp 2 := by
      rw [← he_sq]
      have : (2.718 : ℝ) ^ 2 < (Real.exp 1) ^ 2 := by
        nlinarith [Real.exp_pos 1]
      linarith
    have _hy_ge : 2.718 ≤ logX := by linarith
    have : 5 * (logX + 1) ≤ Real.exp 2 * logX := by
      have : 5 ≤ (Real.exp 2 - 5) * logX := by
        calc 5 ≤ (7.38 - 5) * 2.718 := by norm_num
        _ ≤ (Real.exp 2 - 5) * logX := by nlinarith
      linarith
    linarith
  have h_log_5k : Real.log (5 * (k : ℝ)) ≤ L + 2 := by
    have hlog_exp2 : Real.log (Real.exp 2 * logX) = 2 + Real.log logX := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos 2)) (ne_of_gt hlogX_pos), Real.log_exp]
    have := Real.log_le_log h5k_pos h5k_le
    rw [hlog_exp2, ← hL_eq] at this
    linarith
  have h_prod : (k : ℝ) * Real.log (5 * k) ≤ (3 * η / 19) * logT + L + 2 := by
    have h5k_ge1 : 1 ≤ 5 * (k : ℝ) := by
      have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
      linarith
    have h_u_nonneg : 0 ≤ (η / 19) * (logT / L) + 1 := by
      have _ : 0 ≤ logT / L := div_nonneg hlogT_nonneg (by linarith)
      positivity
    have h1 : (k : ℝ) * Real.log (5 * k) ≤ ((η / 19) * (logT / L) + 1) * (L + 2) :=
      mul_le_mul hk_le h_log_5k (Real.log_nonneg h5k_ge1) h_u_nonneg
    have h2 : ((η / 19) * (logT / L) + 1) * (L + 2) = (η / 19) * logT * ((L + 2) / L) + L + 2 := by
      have : L ≠ 0 := by linarith
      field_simp
      ring
    rw [h2] at h1
    have h3 : (L + 2) / L ≤ 3 := by
      have : (L + 2) / L = 1 + 2 / L := by
        rw [add_div, div_self (by linarith)]
      rw [this]
      have : 2 / L ≤ 2 := by
        have : 2 / L = 2 * (1 / L) := by ring
        rw [this]
        have h_inv : 1 / L ≤ 1 := by
          rw [one_div]
          have := one_div_le_one_div_of_le (by linarith) hL
          norm_num at this
          exact this
        linarith
      linarith
    have h_nonneg_factor : 0 ≤ (η / 19) * logT := by
      have : 0 ≤ η / 19 := by linarith
      exact mul_nonneg this hlogT_nonneg
    have h4 : (η / 19) * logT * ((L + 2) / L) ≤ (η / 19) * logT * 3 :=
      mul_le_mul_of_nonneg_left h3 h_nonneg_factor
    have : (η / 19) * logT * 3 = (3 * η / 19) * logT := by ring
    linarith
  have h_exp := Real.exp_le_exp.mpr h_prod
  have h_split : Real.exp ((3 * η / 19) * logT + L + 2) =
      Real.exp ((3 * η / 19) * logT) * Real.exp 2 * logX := by
    rw [add_assoc, Real.exp_add, Real.exp_add, hL_eq, Real.exp_log hlogX_pos]
    ring
  rw [h_split] at h_exp
  exact h_exp

lemma factor4_bound_all_k {η L logT logX : ℝ} {k : ℕ}
    (hη_pos : 0 < η) (hη : η < 1 / 6) (hL : 1 ≤ L)
    (hlogX : Real.exp 1 ≤ logX) (hL_eq : L = Real.log logX)
    (hlogT_nonneg : 0 ≤ logT) (hlogT_le : logT ≤ logX)
    (hk_le : (k : ℝ) ≤ (η / 19) * (logT / L) + 1) :
    (5 : ℝ) ^ k * (k.factorial : ℝ) ≤ Real.exp ((3 * η / 19) * logT) * Real.exp 2 * logX := by
  by_cases hk : k = 0
  · subst hk
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    have he1 : 1 ≤ Real.exp 1 := by
      have : (0 : ℝ) ≤ 1 := by norm_num
      exact Real.one_le_exp this
    have _hX1 : 1 ≤ logX := he1.trans hlogX
    have _he2 : 1 ≤ Real.exp 2 := by
      have : (0 : ℝ) ≤ 2 := by norm_num
      exact Real.one_le_exp this
    have _h_exp1 : 1 ≤ Real.exp ((3 * η / 19) * logT) := by
      have : 0 ≤ (3 * η / 19) * logT := by
        have : 0 ≤ 3 * η / 19 := by linarith
        exact mul_nonneg this hlogT_nonneg
      exact Real.one_le_exp this
    have _h_prod1 : 1 ≤ Real.exp ((3 * η / 19) * logT) * Real.exp 2 := by
      nlinarith
    nlinarith
  · have hk_pos : 1 ≤ k := by omega
    have h_fact : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
      exact_mod_cast Nat.factorial_le_pow k
    have h_mul : (5 : ℝ) ^ k * (k.factorial : ℝ) ≤ (5 : ℝ) ^ k * (k : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left h_fact (by positivity)
    rw [← mul_pow] at h_mul
    have h_main := factor4_exp_le hη_pos hη hL hlogX hL_eq hlogT_nonneg hlogT_le hk_le hk_pos
    exact h_mul.trans h_main

lemma ceil_div_le {logT logP η L : ℝ} (hlogT : 0 ≤ logT)
    (hlogP_pos : 0 < logP) (hlogP_ge : (19 / η) * L ≤ logP)
    (h19 : 0 < (19 / η) * L) :
    (⌈logT / logP⌉₊ : ℝ) ≤ (η / 19) * (logT / L) + 1 := by
  have hx_nonneg : 0 ≤ logT / logP := div_nonneg hlogT hlogP_pos.le
  have _h_ceil : (⌈logT / logP⌉₊ : ℝ) < logT / logP + 1 := Nat.ceil_lt_add_one hx_nonneg
  have h_div : logT / logP ≤ (η / 19) * (logT / L) := by
    have h_inv : 1 / logP ≤ 1 / ((19 / η) * L) := one_div_le_one_div_of_le h19 hlogP_ge
    have h1 : logT / logP = logT * (1 / logP) := by ring
    have h2 : (η / 19) * (logT / L) = logT * (1 / ((19 / η) * L)) := by
      have : (19 / η) * L = (19 * L) / η := by ring
      rw [this, one_div_div]
      ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left h_inv hlogT
  linarith

lemma alpha_bound_sum {η : ℝ} {J : ℕ} (hη0 : 0 < η) (hJ : 0 < J) :
    2 * alpha η J + η / 38 + 4 * η / 19 + 3 * η / 19 ≤ 1 / 2 - η := by
  unfold alpha
  have _hJ_pos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have : 0 < 1 / (2 * (J : ℝ)) := by positivity
  have h_add : 1 < 1 + 1 / (2 * (J : ℝ)) := by linarith
  have _h_mul : η * 1 < η * (1 + 1 / (2 * (J : ℝ))) := mul_lt_mul_of_pos_left h_add hη0
  have _h_le : η ≤ (61 / 38 : ℝ) * η := by
    have : (1 : ℝ) ≤ 61 / 38 := by norm_num
    nlinarith
  linarith

lemma T_pow_bound {T η : ℝ} {J : ℕ} (hT : 1 ≤ T) (hη0 : 0 < η) (hJ : 0 < J) :
    T ^ (2 * alpha η J + η / 38) * T ^ (4 * η / 19) * T ^ (3 * η / 19) ≤ T ^ (1 / 2 - η) := by
  have hT_pos : 0 < T := by linarith
  rw [← Real.rpow_add hT_pos, ← Real.rpow_add hT_pos]
  have h_le := alpha_bound_sum hη0 hJ
  exact Real.rpow_le_rpow_of_exponent_le hT h_le

lemma exp_one_mul_exp_two : Real.exp 1 * Real.exp 2 = Real.exp 3 := by
  rw [← Real.exp_add]
  norm_num

lemma combine_four_factors {C₈ T1 V2 E3 K4 T_pow V_exp T_e3 T_e4 T η logX : ℝ}
    (hT1 : T1 ≤ T_pow)
    (hV2 : V2 ≤ Real.exp 1 * V_exp)
    (hE3 : E3 ≤ T_e3)
    (hK4 : K4 ≤ T_e4 * Real.exp 2 * logX)
    (hT_comb : T_pow * T_e3 * T_e4 ≤ T ^ (1 / 2 - η))
    (hC₈_pos : 0 ≤ C₈)
    (_hT1_pos : 0 ≤ T1) (hV2_pos : 0 ≤ V2) (hE3_pos : 0 ≤ E3) (hK4_pos : 0 ≤ K4)
    (_hT_pow_pos : 0 ≤ T_pow) (hV_exp_pos : 0 ≤ V_exp)
    (_hT_e3_pos : 0 ≤ T_e3) (_hT_e4_pos : 0 ≤ T_e4)
    (hlogX_pos : 0 ≤ logX) :
    C₈ * T1 * V2 * E3 * K4 ≤
      (C₈ * Real.exp 3) * T ^ (1 / 2 - η) * V_exp * logX := by
  have h_prod1 : C₈ * T1 ≤ C₈ * T_pow := mul_le_mul_of_nonneg_left hT1 hC₈_pos
  have h_prod2 : C₈ * T1 * V2 ≤ C₈ * T_pow * (Real.exp 1 * V_exp) :=
    mul_le_mul h_prod1 hV2 hV2_pos (by positivity)
  have h_prod3 : C₈ * T1 * V2 * E3 ≤ C₈ * T_pow * (Real.exp 1 * V_exp) * T_e3 :=
    mul_le_mul h_prod2 hE3 hE3_pos (by positivity)
  have h_prod4 : C₈ * T1 * V2 * E3 * K4 ≤
      C₈ * T_pow * (Real.exp 1 * V_exp) * T_e3 * (T_e4 * Real.exp 2 * logX) :=
    mul_le_mul h_prod3 hK4 hK4_pos (by positivity)
  have h_rearrange : C₈ * T_pow * (Real.exp 1 * V_exp) * T_e3 * (T_e4 * Real.exp 2 * logX) =
      (C₈ * (Real.exp 1 * Real.exp 2)) * (T_pow * T_e3 * T_e4) * V_exp * logX := by ring
  have h_rearrange2 : (C₈ * (Real.exp 1 * Real.exp 2)) * (T_pow * T_e3 * T_e4) * V_exp * logX =
      (C₈ * Real.exp 3) * (T_pow * T_e3 * T_e4) * V_exp * logX := by
    rw [exp_one_mul_exp_two]
  rw [h_rearrange, h_rearrange2] at h_prod4
  have h_final : (C₈ * Real.exp 3) * (T_pow * T_e3 * T_e4) * V_exp * logX ≤
      (C₈ * Real.exp 3) * T ^ (1 / 2 - η) * V_exp * logX := by
    have h_main : (C₈ * Real.exp 3) * (T_pow * T_e3 * T_e4) ≤ (C₈ * Real.exp 3) * T ^ (1 / 2 - η) :=
      mul_le_mul_of_nonneg_left hT_comb (by positivity)
    have h_nonneg_mul : 0 ≤ V_exp * logX := mul_nonneg hV_exp_pos hlogX_pos
    have := mul_le_mul_of_nonneg_right h_main h_nonneg_mul
    ring_nf at this ⊢
    exact this
  exact h_prod4.trans h_final

lemma sum_const_le {α : Type*} (s : Finset α) (f : α → ℝ) (B : ℝ)
    (hf : ∀ x ∈ s, f x ≤ B) :
    ∑ x ∈ s, f x ≤ (s.card : ℝ) * B := by
  have h := Finset.sum_le_card_nsmul s f B hf
  simpa using h

/-- Matomäki–Radziwiłł Proposition 1: cardinality of well-spaced subset of exceptional set Uset. -/
theorem RangeSystem.card_wellSpaced_subset_Uset_le {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) (𝒯 : Finset ℝ),
      16 ≤ X → 1 ≤ T₀ → T₀ ≤ T → T ≤ X → WellSpaced 𝒯 → (↑𝒯 ⊆ S.Uset hJ β X T₀ T) →
      (∀ j, 2 ≤ S.Hj hJ j) → (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) →
      (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) →
      (𝒯.card : ℝ) ≤ C * (S.Hj hJ ⟨J - 1, by omega⟩ * Real.log (S.Q ⟨J - 1, by omega⟩) + 2) *
        T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X := by
  rcases card_wellSpaced_large_prime_poly_le with ⟨C₈, hC₈_pos, hlem8⟩
  use C₈ * Real.exp 3
  refine ⟨by positivity, ?_⟩
  intro J S hJ β X T₀ T 𝒯 hX hT₀ hT0T hTX h𝒯 h𝒯_sub hH hQ hP
  let j_last : Fin J := ⟨J - 1, by omega⟩
  let H := S.Hj hJ j_last
  let P := S.P j_last
  let Q := S.Q j_last
  let α := alpha η J
  have hj_val : j_last.val + 1 = J := by
    show (J - 1) + 1 = J
    omega
  have hα_eq : alpha η (j_last.val + 1) = α := by rw [hj_val]
  have hα_pos : 0 < α := alpha_pos η hη0 hη J (by omega)
  have hα_le : α ≤ 1 / 4 := by
    have := alpha_le η hη0 J
    linarith
  have hH2 : 2 ≤ H := hH j_last
  have hH_pos : 0 < H := by linarith
  have h1T : 1 ≤ T := hT₀.trans hT0T
  have hlogT_nonneg : 0 ≤ Real.log T := Real.log_nonneg h1T
  have hT_pos : 0 < T := by linarith
  have hlogX_exp : Real.exp 1 < Real.log X := by
    have h16 : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
    have h16_log : Real.exp 1 < Real.log 16 := log_sixteen_gt_exp_one
    have : Real.log 16 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) h16
    linarith
  have hlogX_ge_exp1 : Real.exp 1 ≤ Real.log X := hlogX_exp.le
  have hlogX_pos : 0 < Real.log X := by linarith [Real.exp_pos 1]
  have hL_ge : 1 ≤ Real.log (Real.log X) := one_le_log_log hX
  have hlogT_le : Real.log T ≤ Real.log X := by
    have : (T : ℝ) ≤ (X : ℝ) := hTX
    exact Real.log_le_log hT_pos this
  have hQ_ge_2 : 2 ≤ (Q : ℝ) := by
    have : 2 ≤ Q := (S.two_le_P j_last).trans (S.P_le_Q j_last)
    exact_mod_cast this
  have hlogQ_le : Real.log Q ≤ Real.sqrt (Real.log X) := by
    have hQ_le := hQ j_last
    have hQ_pos : 0 < (Q : ℝ) := by linarith
    have := Real.log_le_log hQ_pos hQ_le
    rw [Real.log_exp] at this
    exact this
  have hlogQ_nonneg : 0 ≤ Real.log Q := by
    have := Real.log_le_log (by norm_num) hQ_ge_2
    have : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    linarith
  have hlogP_ge : (20 / η) * Real.log (Real.log X) ≤ Real.log P := by
    have hpos : 0 < (Real.log X) ^ (20 / η) := Real.rpow_pos_of_pos hlogX_pos _
    have hlog := Real.log_le_log hpos hP
    rw [Real.log_rpow hlogX_pos] at hlog
    exact hlog
  have h19_ge_2 : 2 ≤ (19 / η) * Real.log (Real.log X) :=
    two_le_nineteen_div_eta_mul_log_log hη0 hη hL_ge
  let p_pred (v : ℕ) (t : ℝ) : Prop :=
    Real.exp (-(alpha η (j_last.val + 1)) * (v : ℝ) / H) <
      ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖
  have h_cov : ∀ t ∈ 𝒯, ∃ v ∈ S.Ij hJ j_last, p_pred v t := by
    intro t ht
    have ht_sub : t ∈ S.Uset hJ β X T₀ T := h𝒯_sub (Finset.mem_coe.mpr ht)
    have ht_not_good : ¬ S.Good hJ β X j_last t := ht_sub.2 j_last
    rw [not_good_iff] at ht_not_good
    exact ht_not_good
  have h_card_nat : 𝒯.card ≤ ∑ v ∈ S.Ij hJ j_last, (𝒯.filter (p_pred v)).card :=
    card_le_sum_card_filter 𝒯 (S.Ij hJ j_last) p_pred h_cov
  have h_card_le : (𝒯.card : ℝ) ≤ ∑ v ∈ S.Ij hJ j_last, ((𝒯.filter (p_pred v)).card : ℝ) := by
    have : (𝒯.card : ℝ) ≤ ((∑ v ∈ S.Ij hJ j_last, (𝒯.filter (p_pred v)).card : ℕ) : ℝ) := Nat.cast_le.mpr h_card_nat
    rw [Nat.cast_sum] at this
    exact this
  have h_v_bound : ∀ v ∈ S.Ij hJ j_last,
      ((𝒯.filter (p_pred v)).card : ℝ) ≤
        (C₈ * Real.exp 3) * T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X := by
    intro v hv
    have hv_floor : ⌊H * Real.log P⌋₊ ≤ v := (Finset.mem_Icc.mp hv).1
    have hv_ceil : v ≤ ⌈H * Real.log Q⌉₊ := (Finset.mem_Icc.mp hv).2
    have hv_r : (⌊H * Real.log P⌋₊ : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv_floor
    have h_sub_floor : H * Real.log P - 1 ≤ (⌊H * Real.log P⌋₊ : ℝ) := (Nat.sub_one_lt_floor _).le
    have hv_floor_r : H * Real.log P - 1 ≤ (v : ℝ) := h_sub_floor.trans hv_r
    have hv_ceil_r : (v : ℝ) ≤ H * Real.log Q + 1 := by
      have : (v : ℝ) ≤ (⌈H * Real.log Q⌉₊ : ℝ) := by exact_mod_cast hv_ceil
      have hceil : (⌈H * Real.log Q⌉₊ : ℝ) < H * Real.log Q + 1 :=
        Nat.ceil_lt_add_one (by positivity)
      linarith
    let vH := (v : ℝ) / H
    have hvH_ge_P : Real.log P - 1 ≤ vH := by
      have : (H * Real.log P - 1) / H ≤ vH := div_le_div_of_nonneg_right hv_floor_r hH_pos.le
      have h_sub : (H * Real.log P - 1) / H = Real.log P - 1 / H := by
        rw [sub_div, mul_div_cancel_left₀ (Real.log P) (ne_of_gt hH_pos)]
      have h_inv : 1 / H ≤ 1 := by
        have : 1 / H ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hH2
        linarith
      linarith
    have hvH_le_Q : vH ≤ Real.log Q + 1 := by
      have : vH ≤ (H * Real.log Q + 1) / H :=
        div_le_div_of_nonneg_right hv_ceil_r hH_pos.le
      have h_add : (H * Real.log Q + 1) / H = Real.log Q + 1 / H := by
        rw [add_div, mul_div_cancel_left₀ (Real.log Q) (ne_of_gt hH_pos)]
      have h_inv : 1 / H ≤ 1 := by
        have : 1 / H ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hH2
        linarith
      linarith
    have hvH_ge_1 : 1 ≤ vH := vH_ge_one hη0 hη hL_ge hlogP_ge hvH_ge_P
    have hexp_ge_e : Real.exp 1 ≤ Real.exp vH := Real.exp_le_exp.mpr hvH_ge_1
    let P₀ := ⌈Real.exp vH⌉₊ - 1
    have hceil_ge_1 : 1 ≤ ⌈Real.exp vH⌉₊ := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
    have hP₀_cast : (P₀ : ℝ) = (⌈Real.exp vH⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hceil_ge_1, Nat.cast_one]
    have hP₀_lt : (P₀ : ℝ) < Real.exp vH := by
      rw [hP₀_cast]
      have := Nat.ceil_lt_add_one (Real.exp_pos vH).le
      linarith
    have hP₀_ge : Real.exp vH - 1 ≤ (P₀ : ℝ) := by
      rw [hP₀_cast]
      have := Nat.le_ceil (Real.exp vH)
      linarith
    have hP₀_add_one_ge : Real.exp vH ≤ (P₀ : ℝ) + 1 := by linarith
    have h_log_sub : vH - 1 ≤ Real.log (Real.exp vH - 1) := by
      have := log_sub_one_ge_sub_one hexp_ge_e
      rwa [Real.log_exp] at this
    have hP₀_log_step : vH - 1 ≤ Real.log (P₀ : ℝ) := by
      have hpos : 0 < Real.exp vH - 1 := by
        have he : 2 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        have : 2 ≤ Real.exp vH := he.trans hexp_ge_e
        linarith
      have := Real.log_le_log hpos hP₀_ge
      exact h_log_sub.trans this
    have hP₀_log : (19 / η) * Real.log (Real.log X) ≤ Real.log (P₀ : ℝ) :=
      log_P0_ge_nineteen_div_eta hη0 hη hL_ge hlogP_ge hvH_ge_P hP₀_log_step
    have hP₀_log_ge_2 : 2 ≤ Real.log (P₀ : ℝ) := h19_ge_2.trans hP₀_log
    have hP₀_ge_5 : 5 ≤ P₀ := five_le_of_two_le_log hP₀_log_ge_2
    have hP₀_ge_2 : 2 ≤ P₀ := le_trans (by norm_num) hP₀_ge_5
    have hsub : shortPrimeRange P Q H v ⊆ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime :=
      shortPrimeRange_subset_Ioc_prime P Q H v hH2 P₀ hP₀_lt hP₀_add_one_ge hP₀_ge_5
    let V := Real.exp (α * vH)
    let a_coeff : ℕ → ℂ := fun p => if p ∈ shortPrimeRange P Q H v then fX β X p else 0
    let 𝒯_v := 𝒯.filter (p_pred v)
    have hV_ge_1 : 1 ≤ V := by
      apply Real.one_le_exp
      positivity
    have ha_le_1 : ∀ p, ‖a_coeff p‖ ≤ 1 := fun p => norm_a_le_one β X P Q H v p
    have h𝒯_v_ws : WellSpaced 𝒯_v := WellSpaced.filter h𝒯 _
    have h𝒯_v_T : ∀ t ∈ 𝒯_v, |t| ≤ T := by
      intro t ht
      rw [Finset.mem_filter] at ht
      have ht_U := h𝒯_sub (Finset.mem_coe.mpr ht.1)
      have ht_Icc : t ∈ Set.Icc T₀ T := ht_U.1
      have ht_nonneg : 0 ≤ t := by linarith [ht_Icc.1]
      rw [abs_of_nonneg ht_nonneg]
      exact ht_Icc.2
    have hV_le : ∀ t ∈ 𝒯_v, V⁻¹ ≤
        ‖dirichletPoly a_coeff ((Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I)‖ := by
      intro t ht
      rw [Finset.mem_filter] at ht
      have ht_pred : p_pred v t := ht.2
      change Real.exp (-(alpha η (j_last.val + 1)) * (v : ℝ) / H) <
        ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ at ht_pred
      rw [hα_eq] at ht_pred
      have h_inv : V⁻¹ = Real.exp (-(α * vH)) := by rw [← Real.exp_neg]
      have h_neg_eq : -(α * vH) = -(α * (v : ℝ) / H) := by ring
      have h_neg_eq2 : -α * (v : ℝ) / H = -(α * (v : ℝ) / H) := by ring
      rw [h_neg_eq] at h_inv
      rw [h_inv]
      have h_poly := dirichletPoly_eq_Qpoly β X P Q H v P₀ hsub ((1 : ℂ) + t * Complex.I)
      rw [h_poly]
      rw [h_neg_eq2] at ht_pred
      exact ht_pred.le
    have hlem8_inst := hlem8 P₀ a_coeff T V 𝒯_v hP₀_ge_2 h1T hV_ge_1 ha_le_1 h𝒯_v_ws h𝒯_v_T hV_le
    have hlogP₀_pos : 0 < Real.log (P₀ : ℝ) := by linarith
    have hvH_le_P0 : vH ≤ Real.log (P₀ : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (P₀ : ℝ) := by
        exact_mod_cast (by omega : 1 ≤ P₀)
      have _h_add := log_add_one_le_log_add_one this
      have : Real.log (Real.exp vH) ≤ Real.log ((P₀ : ℝ) + 1) :=
        Real.log_le_log (Real.exp_pos _) hP₀_add_one_ge
      rw [Real.log_exp] at this
      linarith
    have h_fac1_exp := factor1_exp_le hα_pos hα_le hη0 hL_ge hP₀_log hvH_le_P0
    have hlogV : Real.log V = α * vH := Real.log_exp _
    rw [← hlogV] at h_fac1_exp
    have h_fac1 : T ^ (2 * Real.log V / Real.log (P₀ : ℝ)) ≤ T ^ (2 * α + η / 38) :=
      Real.rpow_le_rpow_of_exponent_le h1T h_fac1_exp
    have hV_sq : V ^ 2 = Real.exp (2 * α * vH) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    have h_fac2_step := V_sq_bound hα_pos.le hα_le hvH_le_Q hlogQ_nonneg hlogQ_le
    have h_fac2 : V ^ 2 ≤ Real.exp 1 * Real.exp (Real.sqrt (Real.log X)) := by
      rw [hV_sq]
      exact h_fac2_step
    have hlogT_add2 : Real.log (Real.log T + 2) ≤ Real.log (Real.log X) + 1 := by
      have : 2 ≤ Real.log X := by
        have he : 2 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
        linarith
      have h_sum_le : Real.log T + 2 ≤ Real.log X + 2 := by linarith
      have h_step := log_add_two_le_log_add_one this
      have h_pos : 0 < Real.log T + 2 := by linarith
      have h_le := Real.log_le_log h_pos h_sum_le
      exact h_le.trans h_step
    have h_fac3_exp := factor3_exp_le hη0 hL_ge hP₀_log hlogT_nonneg hlogT_add2
    have h_fac3 : Real.exp (2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2)) ≤
        T ^ (4 * η / 19) := by
      have := Real.exp_le_exp.mpr h_fac3_exp
      have h_rpow : Real.exp ((4 * η / 19) * Real.log T) = T ^ (4 * η / 19) := by
        rw [Real.rpow_def_of_pos hT_pos, mul_comm]
      rw [h_rpow] at this
      exact this
    have hk_le : ((⌈Real.log T / Real.log (P₀ : ℝ)⌉₊ : ℕ) : ℝ) ≤
        (η / 19) * (Real.log T / Real.log (Real.log X)) + 1 := by
      have h19 : 0 < (19 / η) * Real.log (Real.log X) := by positivity
      exact ceil_div_le hlogT_nonneg hlogP₀_pos hP₀_log h19
    have h_fac4_step := factor4_bound_all_k hη0 hη hL_ge hlogX_ge_exp1 rfl hlogT_nonneg hlogT_le hk_le
    have h_fac4 : (5 : ℝ) ^ ⌈Real.log T / Real.log (P₀ : ℝ)⌉₊ *
        (⌈Real.log T / Real.log (P₀ : ℝ)⌉₊.factorial : ℝ) ≤
        T ^ (3 * η / 19) * Real.exp 2 * Real.log X := by
      have h_rpow : Real.exp ((3 * η / 19) * Real.log T) = T ^ (3 * η / 19) := by
        rw [Real.rpow_def_of_pos hT_pos, mul_comm]
      rw [h_rpow] at h_fac4_step
      exact h_fac4_step
    have hT_comb : T ^ (2 * α + η / 38) * T ^ (4 * η / 19) * T ^ (3 * η / 19) ≤ T ^ (1 / 2 - η) :=
      T_pow_bound h1T hη0 (by omega)
    have h_comb_le := combine_four_factors h_fac1 h_fac2 h_fac3 h_fac4 hT_comb hC₈_pos.le
      (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity)
      hlogX_pos.le
    have h_reassoc : C₈ * T ^ (2 * Real.log V / Real.log (P₀ : ℝ)) * V ^ 2 *
        Real.exp (2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2)) *
        5 ^ ⌈Real.log T / Real.log (P₀ : ℝ)⌉₊ *
        (⌈Real.log T / Real.log (P₀ : ℝ)⌉₊.factorial : ℝ) =
        C₈ * T ^ (2 * Real.log V / Real.log (P₀ : ℝ)) * V ^ 2 *
        Real.exp (2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2)) *
        ((5 : ℝ) ^ ⌈Real.log T / Real.log (P₀ : ℝ)⌉₊ *
        (⌈Real.log T / Real.log (P₀ : ℝ)⌉₊.factorial : ℝ)) := by ring
    rw [h_reassoc] at hlem8_inst
    exact hlem8_inst.trans h_comb_le
  have h_sum_le : ∑ v ∈ S.Ij hJ j_last, ((𝒯.filter (p_pred v)).card : ℝ) ≤
      ((S.Ij hJ j_last).card : ℝ) *
        ((C₈ * Real.exp 3) * T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X) :=
    sum_const_le (S.Ij hJ j_last) _ _ h_v_bound
  have h_I_card : (((S.Ij hJ j_last).card : ℝ) ≤ H * Real.log Q + 2) := by
    unfold RangeSystem.Ij
    exact card_Icc_floor_ceil_le (H * Real.log P) (H * Real.log Q) (by positivity)
  have h_target : ((S.Ij hJ j_last).card : ℝ) *
      ((C₈ * Real.exp 3) * T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X) ≤
      (C₈ * Real.exp 3) * (H * Real.log Q + 2) *
        T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X := by
    have h_nonneg : 0 ≤ T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X := by positivity
    have h_Cpos : 0 ≤ C₈ * Real.exp 3 := by positivity
    have h_mul1 : (C₈ * Real.exp 3) * ((S.Ij hJ j_last).card : ℝ) ≤
        (C₈ * Real.exp 3) * (H * Real.log Q + 2) :=
      mul_le_mul_of_nonneg_left h_I_card h_Cpos
    have h_mul2 := mul_le_mul_of_nonneg_right h_mul1 h_nonneg
    have h_eq_lhs : ((S.Ij hJ j_last).card : ℝ) *
        ((C₈ * Real.exp 3) * T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X) =
        (C₈ * Real.exp 3) * ((S.Ij hJ j_last).card : ℝ) *
        (T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X) := by ring
    have h_eq_rhs : (C₈ * Real.exp 3) * (H * Real.log Q + 2) *
        T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X =
        (C₈ * Real.exp 3) * (H * Real.log Q + 2) *
        (T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X) := by ring
    rw [h_eq_lhs, h_eq_rhs]
    exact h_mul2
  exact h_card_le.trans (h_sum_le.trans h_target)

end Erdos1201.MR
