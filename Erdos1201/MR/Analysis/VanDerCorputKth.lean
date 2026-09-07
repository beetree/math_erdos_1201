import Mathlib
import Erdos1201.MR.Analysis.VanDerCorputSecondIterated

/-!
# Van der Corput k-th Derivative Test and Iterated Exponential Sums

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the discrete $k$-th derivative test for exponential sums (Graham–Kolesnik Thm 2.8)
by induction on $k \ge 2$, using Weyl differencing and the second-derivative test as base case.
-/

open Real Complex Finset

namespace Erdos1201.MR


lemma norm_vdc_S_eq_zero_of_lt {t : ℝ} {m : ℕ} {h : Fin m → ℕ} {a b : ℕ} (hba : b < a) :
    ‖vdc_S t m h a b‖ = 0 := by
  dsimp [vdc_S]
  have : Finset.Ioc a b = ∅ := Finset.Ioc_eq_empty (by omega)
  rw [this, sum_empty, norm_zero]

lemma le_sqrt_add_sqrt_of_sq_le (x A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : x ^ 2 ≤ A + B) :
    x ≤ Real.sqrt A + Real.sqrt B := by
  have h_cross : 0 ≤ 2 * Real.sqrt A * Real.sqrt B := by positivity
  have h_sq : A + B ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
    calc A + B = (Real.sqrt A) ^ 2 + (Real.sqrt B) ^ 2 := by
           rw [Real.sq_sqrt hA, Real.sq_sqrt hB]
      _ ≤ (Real.sqrt A) ^ 2 + 2 * Real.sqrt A * Real.sqrt B + (Real.sqrt B) ^ 2 := by linarith
      _ = (Real.sqrt A + Real.sqrt B) ^ 2 := by ring
  have h_trans : x ^ 2 ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := h.trans h_sq
  have h_nonneg : 0 ≤ Real.sqrt A + Real.sqrt B := by positivity
  nlinarith

lemma sum_Ioo_rpow_le (H : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    ∑ j ∈ Finset.Ioo 0 H, (j : ℝ) ^ p ≤ (H : ℝ) * (H : ℝ) ^ p := by
  have hcard : ((Finset.Ioo 0 H).card : ℝ) ≤ (H : ℝ) := by
    have : (Finset.Ioo 0 H).card ≤ H := by
      rw [Nat.card_Ioo]
      omega
    exact_mod_cast this
  have h_le : ∀ j ∈ Finset.Ioo 0 H, (j : ℝ) ^ p ≤ (H : ℝ) ^ p := by
    intro j hj
    have hj_pos : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hj_le : (j : ℝ) ≤ (H : ℝ) := by
      have : j < H := (mem_Ioo.mp hj).2
      exact_mod_cast this.le
    exact Real.rpow_le_rpow hj_pos hj_le hp
  have h_sum := Finset.sum_le_card_nsmul (Finset.Ioo 0 H) (fun j => (j : ℝ) ^ p) ((H : ℝ) ^ p) h_le
  refine h_sum.trans ?_
  have : (((Finset.Ioo 0 H).card • (H : ℝ) ^ p) : ℝ) = ((Finset.Ioo 0 H).card : ℝ) * (H : ℝ) ^ p := by
    simp only [nsmul_eq_mul]
  rw [this]
  have : 0 ≤ (H : ℝ) ^ p := Real.rpow_nonneg (Nat.cast_nonneg H) p
  exact mul_le_mul_of_nonneg_right hcard this

lemma rpow_sub_rpow_ge_deriv (j : ℕ) (hj : 1 ≤ j) (e : ℝ) (he : 0 < e) (he1 : e < 1) :
    (1 - e) * (j : ℝ) ^ (-e) ≤ (j : ℝ) ^ (1 - e) - ((j - 1 : ℕ) : ℝ) ^ (1 - e) := by
  set a : ℝ := ((j - 1 : ℕ) : ℝ)
  set b : ℝ := (j : ℝ)
  have hab : a < b := by
    dsimp [a, b]
    have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub hj]
      push_cast; rfl
    rw [hcast]
    linarith
  have h1e_pos : 0 < 1 - e := by linarith
  have hfc : ContinuousOn (fun x => x ^ (1 - e)) (Set.Icc a b) := by
    apply Continuous.continuousOn
    exact continuous_rpow_const h1e_pos.le
  have hff' : ∀ x ∈ Set.Ioo a b, HasDerivAt (fun x => x ^ (1 - e)) ((1 - e) * x ^ (-e)) x := by
    intro x hx
    have hx_pos : 0 < x := by
      have ha_nonneg : 0 ≤ a := Nat.cast_nonneg (j - 1)
      linarith [hx.1]
    have hx_ne : x ≠ 0 := hx_pos.ne'
    have hderiv := Real.hasDerivAt_rpow_const (Or.inl hx_ne) (p := 1 - e)
    have hp_sub : 1 - e - 1 = -e := by ring
    rw [hp_sub] at hderiv
    exact hderiv
  obtain ⟨c, hc, h_mvt⟩ := exists_hasDerivAt_eq_slope (fun x => x ^ (1 - e)) (fun x => (1 - e) * x ^ (-e)) hab hfc hff'
  have hba : b - a = 1 := by
    have hcast : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by
      rw [Nat.cast_sub hj]
      push_cast; rfl
    dsimp [a, b]
    linarith
  rw [hba, div_one] at h_mvt
  rw [← h_mvt]
  have hc_le_b : c ≤ (j : ℝ) := hc.2.le
  have hc_pos : 0 < c := by
    have ha_nonneg : 0 ≤ a := Nat.cast_nonneg (j - 1)
    linarith [hc.1]
  have h_mono : (j : ℝ) ^ (-e) ≤ c ^ (-e) := by
    have hneg : -e ≤ 0 := by linarith
    exact Real.rpow_le_rpow_of_nonpos hc_pos hc_le_b hneg
  nlinarith

lemma sum_telescoping_rpow (H : ℕ) (e : ℝ) (_he : 0 < e) (he1 : e < 1) :
    ∑ j ∈ Finset.Ioo 0 H, (((j : ℝ) ^ (1 - e)) - (((j - 1 : ℕ) : ℝ) ^ (1 - e))) ≤ (H : ℝ) ^ (1 - e) := by
  have h_eq_ico : Finset.Ioo 0 H = Finset.Ico 1 H := by
    ext x; simp only [mem_Ioo, mem_Ico]; omega
  rw [h_eq_ico]
  by_cases hH : H ≤ 1
  · rw [Finset.Ico_eq_empty_of_le hH, sum_empty]
    positivity
  have hH_gt : 1 < H := not_le.mp hH
  set f : ℕ → ℝ := fun n => (n : ℝ) ^ (1 - e)
  have h_sum : ∑ j ∈ Finset.Ico 1 H, (((j : ℝ) ^ (1 - e)) - (((j - 1 : ℕ) : ℝ) ^ (1 - e))) =
      ∑ k ∈ Finset.Ico 0 (H - 1), (f (k + 1) - f k) := by
    have h_add := (Finset.sum_Ico_add (fun j => f j - f (j - 1)) 0 (H - 1) 1).symm
    have h01 : 0 + 1 = 1 := by omega
    have hH1 : H - 1 + 1 = H := by omega
    rw [h01, hH1] at h_add
    rw [h_add]
    refine sum_congr rfl fun x _ => ?_
    dsimp [f]
    have h1 : 1 + x = x + 1 := by omega
    have h2 : x + 1 - 1 = x := by omega
    rw [h1, h2]
  rw [h_sum, sum_Ico_sub f (by omega)]
  have hf0 : f 0 = 0 := by
    dsimp [f]
    rw [Nat.cast_zero, Real.zero_rpow (by linarith)]
  rw [hf0, sub_zero]
  dsimp [f]
  apply Real.rpow_le_rpow (by positivity)
  · have : ((H - 1 : ℕ) : ℝ) ≤ (H : ℝ) := by
      have : H - 1 ≤ H := by omega
      exact_mod_cast this
    exact this
  · linarith

lemma sum_Ioo_rpow_neg_le (H : ℕ) (e : ℝ) (he : 0 < e) (he2 : e ≤ 1 / 2) :
    ∑ j ∈ Finset.Ioo 0 H, (j : ℝ) ^ (-e) ≤ 2 * (H : ℝ) ^ (1 - e) := by
  have he1 : e < 1 := by linarith
  have h1e_pos : 0 < 1 - e := by linarith
  have h_step : ∀ j ∈ Finset.Ioo 0 H,
      (j : ℝ) ^ (-e) ≤ 2 * (((j : ℝ) ^ (1 - e)) - (((j - 1 : ℕ) : ℝ) ^ (1 - e))) := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Ioo.mp hj).1
    have h_deriv := rpow_sub_rpow_ge_deriv j hj1 e he he1
    calc (j : ℝ) ^ (-e) = (1 / (1 - e)) * ((1 - e) * (j : ℝ) ^ (-e)) := by
           rw [← mul_assoc, one_div_mul_cancel h1e_pos.ne', one_mul]
      _ ≤ 2 * ((1 - e) * (j : ℝ) ^ (-e)) := by
        have h_inv : 1 / (1 - e) ≤ 2 := by
          rw [div_le_iff₀ h1e_pos]
          linarith
        have : 0 ≤ (1 - e) * (j : ℝ) ^ (-e) := by positivity
        exact mul_le_mul_of_nonneg_right h_inv this
      _ ≤ 2 * (((j : ℝ) ^ (1 - e)) - (((j - 1 : ℕ) : ℝ) ^ (1 - e))) :=
        mul_le_mul_of_nonneg_left h_deriv (by norm_num)
  have h_sum := Finset.sum_le_sum h_step
  refine h_sum.trans ?_
  rw [← mul_sum]
  have h_tel := sum_telescoping_rpow H e he he1
  exact mul_le_mul_of_nonneg_left h_tel (by norm_num)

lemma H_mul_lam_le (H : ℝ) (lam : ℝ) (hlam : 0 < lam) (K : ℝ)
    (hH : H ≤ 2 * lam ^ (- (1 / (K - 1)))) :
    H * lam ≤ 2 * lam ^ (1 - 1 / (K - 1)) := by
  have h1 : H * lam ≤ (2 * lam ^ (- (1 / (K - 1)))) * lam :=
    mul_le_mul_of_nonneg_right hH hlam.le
  refine h1.trans ?_
  have h_rw : (2 * lam ^ (- (1 / (K - 1)))) * lam = 2 * (lam ^ (- (1 / (K - 1))) * lam ^ (1 : ℝ)) := by
    rw [Real.rpow_one]
    ring
  rw [h_rw, ← Real.rpow_add hlam]
  have : - (1 / (K - 1)) + 1 = 1 - 1 / (K - 1) := by ring
  rw [this]

lemma H_mul_lam_ge (H : ℝ) (lam : ℝ) (hlam : 0 < lam) (K : ℝ)
    (hH : lam ^ (- (1 / (K - 1))) ≤ H) :
    lam ^ (1 - 1 / (K - 1)) ≤ H * lam := by
  have h1 : lam ^ (- (1 / (K - 1))) * lam ≤ H * lam :=
    mul_le_mul_of_nonneg_right hH hlam.le
  refine le_trans ?_ h1
  have h_rw : lam ^ (- (1 / (K - 1))) * lam = lam ^ (- (1 / (K - 1))) * lam ^ (1 : ℝ) := by
    rw [Real.rpow_one]
  rw [h_rw, ← Real.rpow_add hlam]
  have : - (1 / (K - 1)) + 1 = 1 - 1 / (K - 1) := by ring
  rw [this]

lemma H_mul_lam_rpow_le (H : ℝ) (hH : 0 ≤ H) (lam : ℝ) (hlam : 0 < lam) (K : ℝ) (hK : 4 ≤ K)
    (hH_le : H ≤ 2 * lam ^ (- (1 / (K - 1)))) :
    (H * lam) ^ (1 / (K - 2)) ≤ 2 * lam ^ (1 / (K - 1)) := by
  have hK2_pos : 0 < K - 2 := by linarith
  have h_le := H_mul_lam_le H lam hlam K hH_le
  have h_pos : 0 ≤ H * lam := mul_nonneg hH hlam.le
  have h_rpow := Real.rpow_le_rpow h_pos h_le (by positivity : 0 ≤ 1 / (K - 2))
  refine h_rpow.trans ?_
  have hlam_pow_pos : 0 < lam ^ (1 - 1 / (K - 1)) := Real.rpow_pos_of_pos hlam _
  rw [Real.mul_rpow (by norm_num) hlam_pow_pos.le]
  have h2_le : (2 : ℝ) ^ (1 / (K - 2)) ≤ 2 := by
    have h1 : 1 / (K - 2) ≤ 1 := by
      rw [div_le_one hK2_pos]
      linarith
    calc (2 : ℝ) ^ (1 / (K - 2)) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 := Real.rpow_one 2
  have h_pow_pow : (lam ^ (1 - 1 / (K - 1))) ^ (1 / (K - 2)) = lam ^ (1 / (K - 1)) := by
    rw [← Real.rpow_mul hlam.le]
    have : (1 - 1 / (K - 1)) * (1 / (K - 2)) = 1 / (K - 1) := by
      have h1 : K - 1 ≠ 0 := by linarith
      have h2 : K - 2 ≠ 0 := by linarith
      field_simp
      ring
    rw [this]
  rw [h_pow_pow]
  have : 0 ≤ lam ^ (1 / (K - 1)) := by positivity
  exact mul_le_mul_of_nonneg_right h2_le this

lemma H_mul_lam_rpow_neg_le (H : ℝ) (lam : ℝ) (hlam : 0 < lam) (K : ℝ) (hK : 4 ≤ K)
    (hH : lam ^ (- (1 / (K - 1))) ≤ H) :
    (H * lam) ^ (- (1 / (K - 2))) ≤ lam ^ (- (1 / (K - 1))) := by
  have h_ge := H_mul_lam_ge H lam hlam K hH
  have h_base_pos : 0 < lam ^ (1 - 1 / (K - 1)) := Real.rpow_pos_of_pos hlam _
  have h_neg : - (1 / (K - 2)) ≤ 0 := by
    have hpos : 0 < K - 2 := by linarith
    have : 0 ≤ 1 / (K - 2) := one_div_nonneg.mpr hpos.le
    linarith
  have h_rpow := Real.rpow_le_rpow_of_nonpos h_base_pos h_ge h_neg
  refine le_trans h_rpow ?_
  have h_pow_pow : (lam ^ (1 - 1 / (K - 1))) ^ (- (1 / (K - 2))) = lam ^ (- (1 / (K - 1))) := by
    rw [← Real.rpow_mul hlam.le]
    have : (1 - 1 / (K - 1)) * (- (1 / (K - 2))) = - (1 / (K - 1)) := by
      have h1 : K - 1 ≠ 0 := by linarith
      have h2 : K - 2 ≠ 0 := by linarith
      field_simp
      ring
    rw [this]
  rw [h_pow_pow]

lemma ceil_props (X : ℝ) (hX1 : 1 ≤ X) (N : ℕ) (hXN : X < (N : ℝ)) :
    let H := Nat.ceil X
    1 ≤ H ∧ H ≤ N ∧ X ≤ (H : ℝ) ∧ (H : ℝ) ≤ 2 * X := by
  intro H
  have hH_ge1 : 1 ≤ H := by
    dsimp [H]
    have h1 : 1 = Nat.ceil (1 : ℝ) := Nat.ceil_one.symm
    rw [h1]
    exact Nat.ceil_le_ceil hX1
  have hH_leN : H ≤ N := by
    dsimp [H]
    exact Nat.ceil_le.mpr hXN.le
  have hH_geX : X ≤ (H : ℝ) := Nat.le_ceil X
  have hH_le2X : (H : ℝ) ≤ 2 * X := by
    have h1 : (H : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  exact ⟨hH_ge1, hH_leN, hH_geX, hH_le2X⟩

lemma one_le_rpow_neg_of_le_one (x : ℝ) (hx_pos : 0 < x) (hx1 : x ≤ 1) (p : ℝ) (hp : p ≤ 0) :
    1 ≤ x ^ p := by
  calc (1 : ℝ) = (1 : ℝ) ^ p := (Real.one_rpow p).symm
    _ ≤ x ^ p := Real.rpow_le_rpow_of_nonpos hx_pos hx1 hp

lemma sqrt_mul_sq_rpow (N : ℝ) (hN : 0 ≤ N) (lam : ℝ) (hlam : 0 ≤ lam) (p : ℝ) :
    Real.sqrt (N ^ 2 * lam ^ p) = N * lam ^ (p / 2) := by
  rw [Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN, Real.sqrt_eq_rpow, ← Real.rpow_mul hlam]
  ring_nf

lemma sqrt_mul_rpow_rpow (N : ℝ) (hN : 0 ≤ N) (q : ℝ) (lam : ℝ) (hlam : 0 ≤ lam) (p : ℝ) :
    Real.sqrt (N ^ q * lam ^ p) = N ^ (q / 2) * lam ^ (p / 2) := by
  rw [Real.sqrt_mul (Real.rpow_nonneg hN q), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
      ← Real.rpow_mul hN, ← Real.rpow_mul hlam]
  ring_nf


lemma fin_snoc_mem_bounds {m : ℕ} {h : Fin m → ℕ} {N : ℕ} (hpos : ∀ i, 1 ≤ h i) (hh : ∀ i, h i ≤ N)
    {j : ℕ} (hj1 : 1 ≤ j) (hjN : j ≤ N) :
    (∀ i : Fin (m + 1), 1 ≤ (Fin.snoc (α := fun _ => ℕ) h j) i) ∧
    (∀ i : Fin (m + 1), (Fin.snoc (α := fun _ => ℕ) h j) i ≤ N) := by
  constructor
  · intro i
    obtain ⟨i0, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · rw [Fin.snoc_castSucc]; exact hpos i0
    · rw [Fin.snoc_last]; exact hj1
  · intro i
    obtain ⟨i0, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
    · rw [Fin.snoc_castSucc]; exact hh i0
    · rw [Fin.snoc_last]; exact hjN


lemma vdc_trivial_large_lam (S : ℝ) (N : ℝ) (hS : S ≤ N) (hN : 0 ≤ N) (lam : ℝ) (hlam : 1 ≤ lam)
    (E₁ E₂ : ℝ) (hE₁ : 0 ≤ E₁) (_hE₂ : 0 ≤ E₂) (C : ℝ) (hC : 1 ≤ C) :
    S ≤ C * (N * lam ^ E₁ + N ^ E₂ * lam ^ (-E₁)) := by
  have h1 : 1 ≤ lam ^ E₁ := by
    calc (1 : ℝ) = (1 : ℝ) ^ E₁ := (Real.one_rpow E₁).symm
      _ ≤ lam ^ E₁ := Real.rpow_le_rpow (by norm_num) hlam hE₁
  have hN_le : N ≤ N * lam ^ E₁ := by
    calc N = N * 1 := by ring
      _ ≤ N * lam ^ E₁ := mul_le_mul_of_nonneg_left h1 hN
  have hpos2 : 0 ≤ N ^ E₂ * lam ^ (-E₁) := by positivity
  have hsum : N ≤ N * lam ^ E₁ + N ^ E₂ * lam ^ (-E₁) := by linarith
  have hbracket_nonneg : 0 ≤ N * lam ^ E₁ + N ^ E₂ * lam ^ (-E₁) := by positivity
  calc S ≤ N := hS
    _ ≤ 1 * (N * lam ^ E₁ + N ^ E₂ * lam ^ (-E₁)) := by rw [one_mul]; exact hsum
    _ ≤ C * (N * lam ^ E₁ + N ^ E₂ * lam ^ (-E₁)) :=
      mul_le_mul_of_nonneg_right hC hbracket_nonneg


lemma vdc_trivial_small_lam (S : ℝ) (N : ℝ) (hS : S ≤ N) (hN : 2 ≤ N) (lam : ℝ) (hlam : 0 < lam)
    (K : ℝ) (hK : 4 ≤ K) (hsmall : N ≤ lam ^ (- (1 / (K - 1)))) (C : ℝ) (hC : 1 ≤ C) :
    S ≤ C * (N * lam ^ (1 / (2 * K - 2)) + N ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2)))) := by
  have hN_pos : 0 < N := by linarith
  have hN_ge1 : 1 ≤ N := by linarith
  have hK1_pos : 0 < K - 1 := by linarith
  have hK_pos : 0 < K := by linarith
  have h_pow_half : (lam ^ (- (1 / (K - 1)))) ^ (1 / 2 : ℝ) = lam ^ (- (1 / (2 * K - 2))) := by
    rw [← Real.rpow_mul hlam.le]
    have : - (1 / (K - 1)) * (1 / 2) = - (1 / (2 * K - 2)) := by
      have : K - 1 ≠ 0 := by linarith
      field_simp
    rw [this]
  have hN_half : N ^ (1 / 2 : ℝ) ≤ (lam ^ (- (1 / (K - 1)))) ^ (1 / 2 : ℝ) := by
    apply Real.rpow_le_rpow (by positivity) hsmall (by norm_num)
  rw [h_pow_half] at hN_half
  have h_invK_le_half : 1 / K ≤ 1 / 2 := by
    rw [div_le_iff₀ hK_pos]
    linarith
  have hN_invK : N ^ (1 / K) ≤ N ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN_ge1 h_invK_le_half
  have hN_le_lam : N ^ (1 / K) ≤ lam ^ (- (1 / (2 * K - 2))) := hN_invK.trans hN_half
  have hN_split : N = N ^ (1 - 1 / K) * N ^ (1 / K) := by
    rw [← Real.rpow_add hN_pos]
    have : 1 - 1 / K + 1 / K = 1 := by ring
    rw [this, Real.rpow_one]
  have hN_le_term2 : N ≤ N ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2))) := by
    nth_rw 1 [hN_split]
    have : 0 ≤ N ^ (1 - 1 / K) := by positivity
    exact mul_le_mul_of_nonneg_left hN_le_lam this
  have hpos1 : 0 ≤ N * lam ^ (1 / (2 * K - 2)) := by positivity
  have hsum : N ≤ N * lam ^ (1 / (2 * K - 2)) + N ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2))) := by linarith
  have hbracket_nonneg : 0 ≤ N * lam ^ (1 / (2 * K - 2)) + N ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2))) := by positivity
  calc S ≤ N := hS
    _ ≤ 1 * (N * lam ^ (1 / (2 * K - 2)) + N ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2)))) := by rw [one_mul]; exact hsum
    _ ≤ C * (N * lam ^ (1 / (2 * K - 2)) + N ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2)))) :=
      mul_le_mul_of_nonneg_right hC hbracket_nonneg


lemma vdc_inner_sum_bound (H : ℕ) (hH1 : 1 ≤ H) (lam : ℝ) (hlam : 0 < lam)
    (K : ℝ) (hK : 4 ≤ K) (hH_le : (H : ℝ) ≤ 2 * lam ^ (- (1 / (K - 1))))
    (hH_ge : lam ^ (- (1 / (K - 1))) ≤ (H : ℝ))
    (N : ℝ) (hN : 0 ≤ N) (C' : ℝ) (hC' : 0 ≤ C')
    (f : ℕ → ℝ)
    (hf : ∀ j ∈ Finset.Ioo 0 H,
      f j ≤ C' * (N * ((j : ℝ) * lam) ^ (1 / (K - 2)) +
        N ^ (1 - 2 / K) * ((j : ℝ) * lam) ^ (- (1 / (K - 2))))) :
    ∑ j ∈ Finset.Ioo 0 H, f j ≤
      2 * C' * (H : ℝ) * (N * lam ^ (1 / (K - 1)) + N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1)))) := by
  have hH_pos : 0 < (H : ℝ) := by
    have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    linarith
  have hK2_pos : 0 < K - 2 := by linarith
  have h_split : ∀ j ∈ Finset.Ioo 0 H,
      ((j : ℝ) * lam) ^ (1 / (K - 2)) = (j : ℝ) ^ (1 / (K - 2)) * lam ^ (1 / (K - 2)) ∧
      ((j : ℝ) * lam) ^ (- (1 / (K - 2))) = (j : ℝ) ^ (- (1 / (K - 2))) * lam ^ (- (1 / (K - 2))) := by
    intro j hj
    have hj_pos : 0 < (j : ℝ) := Nat.cast_pos.mpr (mem_Ioo.mp hj).1
    constructor
    · exact Real.mul_rpow hj_pos.le hlam.le
    · exact Real.mul_rpow hj_pos.le hlam.le
  have h_term_le : ∀ j ∈ Finset.Ioo 0 H,
      f j ≤ C' * N * lam ^ (1 / (K - 2)) * (j : ℝ) ^ (1 / (K - 2)) +
        C' * N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 2))) * (j : ℝ) ^ (- (1 / (K - 2))) := by
    intro j hj
    have h1 := hf j hj
    have h2 := h_split j hj
    rw [h2.1, h2.2] at h1
    calc f j ≤ C' * (N * ((j : ℝ) ^ (1 / (K - 2)) * lam ^ (1 / (K - 2))) +
                     N ^ (1 - 2 / K) * ((j : ℝ) ^ (- (1 / (K - 2))) * lam ^ (- (1 / (K - 2))))) := h1
      _ = C' * N * lam ^ (1 / (K - 2)) * (j : ℝ) ^ (1 / (K - 2)) +
          C' * N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 2))) * (j : ℝ) ^ (- (1 / (K - 2))) := by ring
  have h_sum_le := Finset.sum_le_sum h_term_le
  refine h_sum_le.trans ?_
  rw [Finset.sum_add_distrib, ← mul_sum, ← mul_sum]
  have h_sum1 := sum_Ioo_rpow_le H (1 / (K - 2)) (by positivity)
  have h_e_pos : 0 < 1 / (K - 2) := by positivity
  have h_e_half : 1 / (K - 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ hK2_pos]
    linarith
  have h_sum2 := sum_Ioo_rpow_neg_le H (1 / (K - 2)) h_e_pos h_e_half
  have h_comb1 : C' * N * lam ^ (1 / (K - 2)) * ∑ j ∈ Finset.Ioo 0 H, (j : ℝ) ^ (1 / (K - 2)) ≤
      C' * N * lam ^ (1 / (K - 2)) * ((H : ℝ) * (H : ℝ) ^ (1 / (K - 2))) := by
    have : 0 ≤ C' * N * lam ^ (1 / (K - 2)) := by positivity
    exact mul_le_mul_of_nonneg_left h_sum1 this
  have h_comb2 : C' * N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 2))) * ∑ j ∈ Finset.Ioo 0 H, (j : ℝ) ^ (- (1 / (K - 2))) ≤
      C' * N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 2))) * (2 * (H : ℝ) ^ (1 - 1 / (K - 2))) := by
    have : 0 ≤ C' * N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 2))) := by positivity
    exact mul_le_mul_of_nonneg_left h_sum2 this
  have h_step_lam1 : lam ^ (1 / (K - 2)) * ((H : ℝ) * (H : ℝ) ^ (1 / (K - 2))) =
      (H : ℝ) * ((H : ℝ) * lam) ^ (1 / (K - 2)) := by
    rw [Real.mul_rpow hH_pos.le hlam.le]
    ring
  have h_H_pow : (H : ℝ) ^ (1 - 1 / (K - 2)) = (H : ℝ) * (H : ℝ) ^ (- (1 / (K - 2))) := by
    have : (H : ℝ) ^ (1 - 1 / (K - 2)) = (H : ℝ) ^ (1 + - (1 / (K - 2))) := rfl
    rw [this, Real.rpow_add hH_pos, Real.rpow_one]
  have h_step_lam2 : lam ^ (- (1 / (K - 2))) * (2 * (H : ℝ) ^ (1 - 1 / (K - 2))) =
      2 * (H : ℝ) * ((H : ℝ) * lam) ^ (- (1 / (K - 2))) := by
    rw [h_H_pow, Real.mul_rpow hH_pos.le hlam.le]
    ring
  have h_eq_rhs1 : C' * N * lam ^ (1 / (K - 2)) * ((H : ℝ) * (H : ℝ) ^ (1 / (K - 2))) =
      C' * N * (H : ℝ) * ((H : ℝ) * lam) ^ (1 / (K - 2)) := by
    calc C' * N * lam ^ (1 / (K - 2)) * ((H : ℝ) * (H : ℝ) ^ (1 / (K - 2))) =
           (C' * N) * (lam ^ (1 / (K - 2)) * ((H : ℝ) * (H : ℝ) ^ (1 / (K - 2)))) := by ring
      _ = (C' * N) * ((H : ℝ) * ((H : ℝ) * lam) ^ (1 / (K - 2))) := by rw [h_step_lam1]
      _ = C' * N * (H : ℝ) * ((H : ℝ) * lam) ^ (1 / (K - 2)) := by ring
  have h_eq_rhs2 : C' * N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 2))) * (2 * (H : ℝ) ^ (1 - 1 / (K - 2))) =
      2 * C' * N ^ (1 - 2 / K) * (H : ℝ) * ((H : ℝ) * lam) ^ (- (1 / (K - 2))) := by
    calc C' * N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 2))) * (2 * (H : ℝ) ^ (1 - 1 / (K - 2))) =
           (C' * N ^ (1 - 2 / K)) * (lam ^ (- (1 / (K - 2))) * (2 * (H : ℝ) ^ (1 - 1 / (K - 2)))) := by ring
      _ = (C' * N ^ (1 - 2 / K)) * (2 * (H : ℝ) * ((H : ℝ) * lam) ^ (- (1 / (K - 2)))) := by rw [h_step_lam2]
      _ = 2 * C' * N ^ (1 - 2 / K) * (H : ℝ) * ((H : ℝ) * lam) ^ (- (1 / (K - 2))) := by ring
  rw [h_eq_rhs1] at h_comb1
  rw [h_eq_rhs2] at h_comb2
  have h_bound1 := H_mul_lam_rpow_le (H : ℝ) hH_pos.le lam hlam K hK hH_le
  have h_bound2 := H_mul_lam_rpow_neg_le (H : ℝ) lam hlam K hK hH_ge
  have h_final1 : C' * N * (H : ℝ) * ((H : ℝ) * lam) ^ (1 / (K - 2)) ≤
      2 * C' * (H : ℝ) * N * lam ^ (1 / (K - 1)) := by
    have : 0 ≤ C' * N * (H : ℝ) := by positivity
    calc C' * N * (H : ℝ) * ((H : ℝ) * lam) ^ (1 / (K - 2)) ≤
           (C' * N * (H : ℝ)) * (2 * lam ^ (1 / (K - 1))) :=
             mul_le_mul_of_nonneg_left h_bound1 this
      _ = 2 * C' * (H : ℝ) * N * lam ^ (1 / (K - 1)) := by ring
  have h_final2 : 2 * C' * N ^ (1 - 2 / K) * (H : ℝ) * ((H : ℝ) * lam) ^ (- (1 / (K - 2))) ≤
      2 * C' * (H : ℝ) * N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1))) := by
    have : 0 ≤ 2 * C' * N ^ (1 - 2 / K) * (H : ℝ) := by positivity
    calc 2 * C' * N ^ (1 - 2 / K) * (H : ℝ) * ((H : ℝ) * lam) ^ (- (1 / (K - 2))) ≤
           (2 * C' * N ^ (1 - 2 / K) * (H : ℝ)) * lam ^ (- (1 / (K - 1))) :=
             mul_le_mul_of_nonneg_left h_bound2 this
      _ = 2 * C' * (H : ℝ) * N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1))) := by ring
  linarith




lemma vdc_weyl_algebra (N : ℝ) (hN : 2 ≤ N) (H : ℝ) (hH : 1 ≤ H) (hHN : H ≤ N)
    (ba : ℝ) (hba0 : 0 ≤ ba) (hbaN : ba ≤ N)
    (lam : ℝ) (hlam : 0 < lam) (K : ℝ) (_hK : 4 ≤ K)
    (hH_ge : lam ^ (- (1 / (K - 1))) ≤ H)
    (C' : ℝ) (hC' : 0 ≤ C')
    (Sigma : ℝ) (_hSigma0 : 0 ≤ Sigma)
    (hSigma : Sigma ≤ 2 * C' * H * (N * lam ^ (1 / (K - 1)) + N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1))))) :
    ((ba + H) / H) * (ba + 2 * Sigma) ≤
      (2 + 8 * C') * N ^ 2 * lam ^ (1 / (K - 1)) + 8 * C' * N ^ (2 - 2 / K) * lam ^ (- (1 / (K - 1))) := by
  have hH_pos : 0 < H := by linarith
  have hN_pos : 0 < N := by linarith
  have h_frac_le : (ba + H) / H ≤ 2 * N / H := by
    rw [div_le_div_iff_of_pos_right hH_pos]
    linarith
  have h_inner_le : ba + 2 * Sigma ≤
      N + 4 * C' * H * (N * lam ^ (1 / (K - 1)) + N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1)))) := by
    linarith
  have h_mult_le : ((ba + H) / H) * (ba + 2 * Sigma) ≤
      (2 * N / H) * (N + 4 * C' * H * (N * lam ^ (1 / (K - 1)) + N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1))))) := by
    have h1 : 0 ≤ (ba + H) / H := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left h_inner_le h1) ?_
    have h2 : 0 ≤ N + 4 * C' * H * (N * lam ^ (1 / (K - 1)) + N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1)))) := by positivity
    exact mul_le_mul_of_nonneg_right h_frac_le h2
  refine h_mult_le.trans ?_
  have h_expand : (2 * N / H) * (N + 4 * C' * H * (N * lam ^ (1 / (K - 1)) + N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1))))) =
      2 * N ^ 2 * (1 / H) + 8 * C' * N ^ 2 * lam ^ (1 / (K - 1)) + 8 * C' * (N * N ^ (1 - 2 / K)) * lam ^ (- (1 / (K - 1))) := by
    have : (2 * N / H) * N = 2 * N ^ 2 * (1 / H) := by ring
    have : (2 * N / H) * (4 * C' * H * (N * lam ^ (1 / (K - 1)))) = 8 * C' * N ^ 2 * lam ^ (1 / (K - 1)) := by
      calc (2 * N / H) * (4 * C' * H * (N * lam ^ (1 / (K - 1)))) =
             (2 * N / H * (4 * C' * H * N)) * lam ^ (1 / (K - 1)) := by ring
        _ = (8 * C' * N ^ 2) * lam ^ (1 / (K - 1)) := by
          have : 2 * N / H * (4 * C' * H * N) = 8 * C' * N ^ 2 := by
            field_simp
            ring
          rw [this]
        _ = 8 * C' * N ^ 2 * lam ^ (1 / (K - 1)) := by ring
    have : (2 * N / H) * (4 * C' * H * (N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1))))) =
        8 * C' * (N * N ^ (1 - 2 / K)) * lam ^ (- (1 / (K - 1))) := by
      calc (2 * N / H) * (4 * C' * H * (N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1))))) =
             (2 * N / H * (4 * C' * H)) * (N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1)))) := by ring
        _ = (8 * C' * N) * (N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1)))) := by
          have : 2 * N / H * (4 * C' * H) = 8 * C' * N := by
            field_simp
            ring
          rw [this]
        _ = 8 * C' * (N * N ^ (1 - 2 / K)) * lam ^ (- (1 / (K - 1))) := by ring
    calc (2 * N / H) * (N + 4 * C' * H * (N * lam ^ (1 / (K - 1)) + N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1))))) =
           (2 * N / H) * N + (2 * N / H) * (4 * C' * H * (N * lam ^ (1 / (K - 1)))) +
           (2 * N / H) * (4 * C' * H * (N ^ (1 - 2 / K) * lam ^ (- (1 / (K - 1))))) := by ring
      _ = 2 * N ^ 2 * (1 / H) + 8 * C' * N ^ 2 * lam ^ (1 / (K - 1)) + 8 * C' * (N * N ^ (1 - 2 / K)) * lam ^ (- (1 / (K - 1))) := by
        linarith
  rw [h_expand]
  have h_invH_le : 1 / H ≤ lam ^ (1 / (K - 1)) := by
    have h1 : 1 / H ≤ 1 / lam ^ (- (1 / (K - 1))) :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlam _) hH_ge
    have h2 : 1 / lam ^ (- (1 / (K - 1))) = lam ^ (1 / (K - 1)) := by
      rw [one_div, ← Real.rpow_neg hlam.le, neg_neg]
    rwa [h2] at h1
  have h_term1_le : 2 * N ^ 2 * (1 / H) ≤ 2 * N ^ 2 * lam ^ (1 / (K - 1)) := by
    have : 0 ≤ 2 * N ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left h_invH_le this
  have h_NN_pow : N * N ^ (1 - 2 / K) = N ^ (2 - 2 / K) := by
    calc N * N ^ (1 - 2 / K) = N ^ (1 : ℝ) * N ^ (1 - 2 / K) := by rw [Real.rpow_one]
      _ = N ^ (1 + (1 - 2 / K)) := by rw [← Real.rpow_add hN_pos]
      _ = N ^ (2 - 2 / K) := by
        have : 1 + (1 - 2 / K) = 2 - 2 / K := by ring
        rw [this]
  rw [h_NN_pow]
  linarith


lemma norm_vdc_S_le_card_diff (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (a b : ℕ) :
    ‖vdc_S t m h a b‖ ≤ ((b - a : ℕ) : ℝ) := norm_vdc_S_le_card t m h a b

lemma norm_vdc_S_le_kth_step (k : ℕ) (hk : 2 ≤ k)
    (ih : ∀ K₀, ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (N a b : ℕ),
      0 < t → m + k ≤ K₀ → (∀ i, 1 ≤ h i) → (∀ i, h i ≤ N) → 2 ≤ N → N ≤ a → a ≤ b → b ≤ 2 * N →
      ‖vdc_S t m h a b‖ ≤ C * ((N : ℝ) * (vdcLam t m h N k) ^ (1 / (2 * (2 : ℝ) ^ (k - 1) - 2)) +
        (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k - 1)) * (vdcLam t m h N k) ^ (-(1 / (2 * (2 : ℝ) ^ (k - 1) - 2))))) :
    ∀ K₀, ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (N a b : ℕ),
      0 < t → m + (k + 1) ≤ K₀ → (∀ i, 1 ≤ h i) → (∀ i, h i ≤ N) → 2 ≤ N → N ≤ a → a ≤ b → b ≤ 2 * N →
      ‖vdc_S t m h a b‖ ≤ C * ((N : ℝ) * (vdcLam t m h N (k + 1)) ^ (1 / (2 * (2 : ℝ) ^ k - 2)) +
        (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ k) * (vdcLam t m h N (k + 1)) ^ (-(1 / (2 * (2 : ℝ) ^ k - 2)))) := by
  intro K₀
  obtain ⟨C', hC'_pos, hC'⟩ := ih K₀
  set C := max 1 (Real.sqrt (2 + 8 * C') + Real.sqrt (8 * C'))
  have hC_pos : 0 < C := by
    have : (0 : ℝ) < 1 := by norm_num
    exact this.trans_le (le_max_left 1 _)
  have hC_ge1 : 1 ≤ C := le_max_left 1 _
  have hC_ge_sqrt : Real.sqrt (2 + 8 * C') + Real.sqrt (8 * C') ≤ C := le_max_right _ _
  have hC_ge_s1 : Real.sqrt (2 + 8 * C') ≤ C := by
    have : 0 ≤ Real.sqrt (8 * C') := Real.sqrt_nonneg _
    linarith
  have hC_ge_s2 : Real.sqrt (8 * C') ≤ C := by
    have : 0 ≤ Real.sqrt (2 + 8 * C') := Real.sqrt_nonneg _
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro t m h N a b ht hm hpos hh hN hna hab hnb
  set lam := vdcLam t m h N (k + 1)
  set K := (2 : ℝ) ^ k
  have hK_ge4 : 4 ≤ K := by
    dsimp [K]
    calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      _ ≤ (2 : ℝ) ^ k := by
        have : (1 : ℝ) ≤ 2 := by norm_num
        exact pow_le_pow_right₀ this hk
  have hlam_pos : 0 < lam := by
    dsimp [vdcLam, lam]
    have ht_div : 0 < t / (2 * Real.pi) := by positivity
    have hprod_pos : 0 < ∏ i, (h i : ℝ) := prod_h_pos m h hpos
    positivity
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hN_ge2 : 2 ≤ (N : ℝ) := by exact_mod_cast hN
  by_cases hab_eq : a = b
  · subst hab_eq
    dsimp [vdc_S]
    rw [Finset.Ioc_self, Finset.sum_empty, norm_zero]
    have hterm1 : 0 ≤ (N : ℝ) * lam ^ (1 / (2 * K - 2)) := mul_nonneg (by positivity) (Real.rpow_nonneg hlam_pos.le _)
    have hterm2 : 0 ≤ (N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2))) :=
      mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hlam_pos.le _)
    exact mul_nonneg hC_pos.le (add_nonneg hterm1 hterm2)
  have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
  have h_norm_card := norm_vdc_S_le_card_diff t m h a b
  have hba_le_N : ((b - a : ℕ) : ℝ) ≤ (N : ℝ) := by
    have : b - a ≤ N := by omega
    exact_mod_cast this
  have h_norm_le_N : ‖vdc_S t m h a b‖ ≤ (N : ℝ) := h_norm_card.trans hba_le_N
  by_cases hlam_ge1 : 1 ≤ lam
  · have hE1_pos : 0 ≤ 1 / (2 * K - 2) := by
      have : 0 < 2 * K - 2 := by linarith
      positivity
    have hE2_pos : 0 ≤ 1 - 1 / K := by
      have : 1 / K ≤ 1 := by
        have : 1 ≤ K := by linarith
        rw [div_le_one (by linarith)]
        linarith
      linarith
    exact vdc_trivial_large_lam ‖vdc_S t m h a b‖ (N : ℝ) h_norm_le_N (by positivity) lam hlam_ge1
      (1 / (2 * K - 2)) (1 - 1 / K) hE1_pos hE2_pos C hC_ge1
  have hlam_lt1 : lam < 1 := lt_of_not_ge hlam_ge1
  set X := lam ^ (- (1 / (K - 1)))
  by_cases hX_geN : (N : ℝ) ≤ X
  · exact vdc_trivial_small_lam ‖vdc_S t m h a b‖ (N : ℝ) h_norm_le_N hN_ge2 lam hlam_pos K hK_ge4 hX_geN C hC_ge1
  have hX_ltN : X < (N : ℝ) := lt_of_not_ge hX_geN
  have hX_ge1 : 1 ≤ X := by
    have h_neg : - (1 / (K - 1)) ≤ 0 := by
      have : 0 < K - 1 := by linarith
      have : 0 ≤ 1 / (K - 1) := by positivity
      linarith
    exact one_le_rpow_neg_of_le_one lam hlam_pos hlam_lt1.le (- (1 / (K - 1))) h_neg
  have h_ceil := ceil_props X hX_ge1 N hX_ltN
  set H := Nat.ceil X
  have hH1 : 1 ≤ H := h_ceil.1
  have hHN : H ≤ N := h_ceil.2.1
  have hH_geX : X ≤ (H : ℝ) := h_ceil.2.2.1
  have hH_le2X : (H : ℝ) ≤ 2 * X := h_ceil.2.2.2
  have hweyl := norm_sq_vdc_S_le_weyl t m h a b hab H hH1
  set Sigma := ∑ j ∈ Finset.Ioo 0 H, ‖vdc_S t (m + 1) (Fin.snoc h j) a (b - j)‖
  have hSigma0 : 0 ≤ Sigma := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h_inner_term : ∀ j ∈ Finset.Ioo 0 H,
      ‖vdc_S t (m + 1) (Fin.snoc h j) a (b - j)‖ ≤
        C' * ((N : ℝ) * ((j : ℝ) * lam) ^ (1 / (K - 2)) +
          (N : ℝ) ^ (1 - 2 / K) * ((j : ℝ) * lam) ^ (- (1 / (K - 2)))) := by
    intro j hj
    have hj0 : 0 < j := (mem_Ioo.mp hj).1
    have hjH : j < H := (mem_Ioo.mp hj).2
    have hjN : j ≤ N := by omega
    have hj1 : 1 ≤ j := hj0
    have h_snoc_bounds := fin_snoc_mem_bounds hpos hh hj1 hjN
    have hlam_snoc := vdcLam_snoc t m h N (k + 1) (by omega) j
    have h_k_eq : k + 1 - 1 = k := by omega
    rw [h_k_eq] at hlam_snoc
    by_cases habj : a ≤ b - j
    · have hbj2N : b - j ≤ 2 * N := by omega
      have hIH := hC' t (m + 1) (Fin.snoc h j) N a (b - j) ht (by omega) h_snoc_bounds.1 h_snoc_bounds.2 hN hna habj hbj2N
      rw [hlam_snoc] at hIH
      have hK_half : (2 : ℝ) ^ (k - 1) = K / 2 := by
        dsimp [K]
        have : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1 + 1) := by congr 1; omega
        rw [this, pow_succ]
        ring
      have h_exp1 : 1 / (2 * (2 : ℝ) ^ (k - 1) - 2) = 1 / (K - 2) := by
        rw [hK_half]
        have : 2 * (K / 2) - 2 = K - 2 := by ring
        rw [this]
      have h_exp2 : 1 - 1 / (2 : ℝ) ^ (k - 1) = 1 - 2 / K := by
        rw [hK_half]
        have : 1 / (K / 2) = 2 / K := by ring
        rw [this]
      rw [h_exp1, h_exp2] at hIH
      exact hIH
    · have hbj_lt_a : b - j < a := lt_of_not_ge habj
      have hzero := norm_vdc_S_eq_zero_of_lt (t := t) (m := m + 1) (h := Fin.snoc h j) (a := a) (b := b - j) hbj_lt_a
      rw [hzero]
      have h1 : 0 ≤ ((j : ℝ) * lam) ^ (1 / (K - 2)) := Real.rpow_nonneg (by positivity) _
      have h2 : 0 ≤ ((j : ℝ) * lam) ^ (- (1 / (K - 2))) := Real.rpow_nonneg (by positivity) _
      have h3 : 0 ≤ (N : ℝ) ^ (1 - 2 / K) := Real.rpow_nonneg (by positivity) _
      have hterm1 : 0 ≤ (N : ℝ) * ((j : ℝ) * lam) ^ (1 / (K - 2)) := mul_nonneg (by positivity) h1
      have hterm2 : 0 ≤ (N : ℝ) ^ (1 - 2 / K) * ((j : ℝ) * lam) ^ (- (1 / (K - 2))) := mul_nonneg h3 h2
      exact mul_nonneg hC'_pos.le (add_nonneg hterm1 hterm2)
  have h_sigma_bound := vdc_inner_sum_bound H hH1 lam hlam_pos K hK_ge4 hH_le2X hH_geX (N : ℝ) (by positivity) C' hC'_pos.le
    (fun j => ‖vdc_S t (m + 1) (Fin.snoc h j) a (b - j)‖) h_inner_term
  have h_alg := vdc_weyl_algebra (N : ℝ) hN_ge2 (H : ℝ) (by exact_mod_cast hH1) (by exact_mod_cast hHN)
    ((b - a : ℕ) : ℝ) (by positivity) hba_le_N lam hlam_pos K hK_ge4 hH_geX C' hC'_pos.le Sigma hSigma0 h_sigma_bound
  have h_sq_le : ‖vdc_S t m h a b‖ ^ 2 ≤
      (2 + 8 * C') * (N : ℝ) ^ 2 * lam ^ (1 / (K - 1)) + 8 * C' * (N : ℝ) ^ (2 - 2 / K) * lam ^ (- (1 / (K - 1))) :=
    hweyl.trans h_alg
  set A := (2 + 8 * C') * (N : ℝ) ^ 2 * lam ^ (1 / (K - 1))
  set B := 8 * C' * (N : ℝ) ^ (2 - 2 / K) * lam ^ (- (1 / (K - 1)))
  have hA_nonneg : 0 ≤ A := by positivity
  have hB_nonneg : 0 ≤ B := by positivity
  have h_sqrt_le := le_sqrt_add_sqrt_of_sq_le ‖vdc_S t m h a b‖ A B hA_nonneg hB_nonneg h_sq_le
  have h_sqrt_A : Real.sqrt A = Real.sqrt (2 + 8 * C') * (N : ℝ) * lam ^ (1 / (2 * K - 2)) := by
    dsimp [A]
    have h1 : (2 + 8 * C') * (N : ℝ) ^ 2 * lam ^ (1 / (K - 1)) = (2 + 8 * C') * ((N : ℝ) ^ 2 * lam ^ (1 / (K - 1))) := by ring
    rw [h1, Real.sqrt_mul (by positivity), sqrt_mul_sq_rpow (N : ℝ) (by positivity) lam hlam_pos.le (1 / (K - 1))]
    have : (1 / (K - 1)) / 2 = 1 / (2 * K - 2) := by
      have : K - 1 ≠ 0 := by linarith
      field_simp
    rw [this]
    ring
  have h_sqrt_B : Real.sqrt B = Real.sqrt (8 * C') * (N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2))) := by
    dsimp [B]
    have h1 : 8 * C' * (N : ℝ) ^ (2 - 2 / K) * lam ^ (- (1 / (K - 1))) = 8 * C' * ((N : ℝ) ^ (2 - 2 / K) * lam ^ (- (1 / (K - 1)))) := by ring
    rw [h1, Real.sqrt_mul (by positivity), sqrt_mul_rpow_rpow (N : ℝ) (by positivity) (2 - 2 / K) lam hlam_pos.le (- (1 / (K - 1)))]
    have hq : (2 - 2 / K) / 2 = 1 - 1 / K := by ring
    have hp : (- (1 / (K - 1))) / 2 = - (1 / (2 * K - 2)) := by
      have : K - 1 ≠ 0 := by linarith
      field_simp
    rw [hq, hp]
    ring
  rw [h_sqrt_A, h_sqrt_B] at h_sqrt_le
  have h_term1_final : Real.sqrt (2 + 8 * C') * (N : ℝ) * lam ^ (1 / (2 * K - 2)) ≤
      C * ((N : ℝ) * lam ^ (1 / (2 * K - 2))) := by
    have : 0 ≤ (N : ℝ) * lam ^ (1 / (2 * K - 2)) := by positivity
    calc Real.sqrt (2 + 8 * C') * (N : ℝ) * lam ^ (1 / (2 * K - 2)) =
           Real.sqrt (2 + 8 * C') * ((N : ℝ) * lam ^ (1 / (2 * K - 2))) := by ring
      _ ≤ C * ((N : ℝ) * lam ^ (1 / (2 * K - 2))) := mul_le_mul_of_nonneg_right hC_ge_s1 this
  have h_term2_final : Real.sqrt (8 * C') * (N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2))) ≤
      C * ((N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2)))) := by
    have : 0 ≤ (N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2))) := by positivity
    calc Real.sqrt (8 * C') * (N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2))) =
           Real.sqrt (8 * C') * ((N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2)))) := by ring
      _ ≤ C * ((N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2)))) := mul_le_mul_of_nonneg_right hC_ge_s2 this
  calc ‖vdc_S t m h a b‖ ≤ Real.sqrt (2 + 8 * C') * (N : ℝ) * lam ^ (1 / (2 * K - 2)) +
                           Real.sqrt (8 * C') * (N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2))) := h_sqrt_le
    _ ≤ C * ((N : ℝ) * lam ^ (1 / (2 * K - 2))) + C * ((N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2)))) :=
         add_le_add h_term1_final h_term2_final
    _ = C * ((N : ℝ) * lam ^ (1 / (2 * K - 2)) + (N : ℝ) ^ (1 - 1 / K) * lam ^ (- (1 / (2 * K - 2)))) := by ring


lemma norm_vdc_S_le_kth_two (K₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (N a b : ℕ),
    0 < t → m + 2 ≤ K₀ → (∀ i, 1 ≤ h i) → (∀ i, h i ≤ N) → 2 ≤ N → N ≤ a → a ≤ b → b ≤ 2 * N →
    ‖vdc_S t m h a b‖ ≤ C * ((N : ℝ) * (vdcLam t m h N 2) ^ (1 / (2 * (2 : ℝ) ^ (2 - 1) - 2)) +
      (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (2 - 1)) * (vdcLam t m h N 2) ^ (-(1 / (2 * (2 : ℝ) ^ (2 - 1) - 2)))) := by
  obtain ⟨C, hC_pos, hC⟩ := norm_vdc_S_le_second K₀
  refine ⟨C, hC_pos, ?_⟩
  intro t m h N a b ht hm hpos hh hN hna hab hnb
  have hm_le : m ≤ K₀ := by omega
  have hbound := hC t m h N a b ht hm_le hpos hh hN hna hab hnb
  have hlam_pos : 0 < vdcLam t m h N 2 := by
    dsimp [vdcLam]
    have ht_div : 0 < t / (2 * Real.pi) := by positivity
    have hprod_pos : 0 < ∏ i, (h i : ℝ) := prod_h_pos m h hpos
    positivity
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hN_ge_one : 1 ≤ (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hsqrt_lam : Real.sqrt (vdcLam t m h N 2) = (vdcLam t m h N 2) ^ (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow (vdcLam t m h N 2)
  have hinv_sqrt_lam : 1 / Real.sqrt (vdcLam t m h N 2) = (vdcLam t m h N 2) ^ (-(1 / 2 : ℝ)) := by
    rw [hsqrt_lam, Real.rpow_neg hlam_pos.le, one_div]
  have h_rpow_N : 1 ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 2 : ℝ) := by rw [Real.one_rpow]
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hN_ge_one (by norm_num)
  have h_second_term : 1 / Real.sqrt (vdcLam t m h N 2) ≤
      (N : ℝ) ^ (1 / 2 : ℝ) * (vdcLam t m h N 2) ^ (-(1 / 2 : ℝ)) := by
    rw [hinv_sqrt_lam]
    calc (vdcLam t m h N 2) ^ (-(1 / 2 : ℝ)) = 1 * (vdcLam t m h N 2) ^ (-(1 / 2 : ℝ)) := by ring
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (vdcLam t m h N 2) ^ (-(1 / 2 : ℝ)) := by
        have : 0 ≤ (vdcLam t m h N 2) ^ (-(1 / 2 : ℝ)) := by positivity
        exact mul_le_mul_of_nonneg_right h_rpow_N this
  have hexp1 : (1 / (2 * (2 : ℝ) ^ (2 - 1) - 2)) = (1 / 2 : ℝ) := by norm_num
  have hexp2 : (1 - 1 / (2 : ℝ) ^ (2 - 1)) = (1 / 2 : ℝ) := by norm_num
  rw [hexp1, hexp2]
  refine hbound.trans ?_
  apply mul_le_mul_of_nonneg_left _ hC_pos.le
  rw [hsqrt_lam] at h_second_term ⊢
  linarith [h_second_term]


lemma norm_vdc_S_le_kth_all (k : ℕ) (hk : 2 ≤ k) :
    ∀ K₀, ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (N a b : ℕ),
      0 < t → m + k ≤ K₀ → (∀ i, 1 ≤ h i) → (∀ i, h i ≤ N) → 2 ≤ N → N ≤ a → a ≤ b → b ≤ 2 * N →
      ‖vdc_S t m h a b‖ ≤ C * ((N : ℝ) * (vdcLam t m h N k) ^ (1 / (2 * (2 : ℝ) ^ (k - 1) - 2)) +
        (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k - 1)) * (vdcLam t m h N k) ^ (-(1 / (2 * (2 : ℝ) ^ (k - 1) - 2)))) := by
  induction k, hk using Nat.le_induction with
  | base =>
    intro K₀
    exact norm_vdc_S_le_kth_two K₀
  | succ n hn ih =>
    exact norm_vdc_S_le_kth_step n hn ih

theorem norm_vdc_S_le_kth (K₀ k : ℕ) (hk : 2 ≤ k) : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (N a b : ℕ),
    0 < t → m + k ≤ K₀ → (∀ i, 1 ≤ h i) → (∀ i, h i ≤ N) → 2 ≤ N → N ≤ a → a ≤ b → b ≤ 2 * N →
    ‖vdc_S t m h a b‖ ≤ C * ((N : ℝ) * (vdcLam t m h N k) ^ (1 / (2 * (2 : ℝ) ^ (k - 1) - 2)) +
      (N : ℝ) ^ (1 - 1 / (2 : ℝ) ^ (k - 1)) * (vdcLam t m h N k) ^ (-(1 / (2 * (2 : ℝ) ^ (k - 1) - 2)))) :=
  norm_vdc_S_le_kth_all k hk K₀


/-!
### Auxiliary lemmas for the iterated exponential sum bound

These lemmas provide the partition of the parameter range `[N, N^K]` into dyadic derivative
scales and the scaling of the natural phase derivative size `vdcLam`.
-/

/-- Natural size of the phase derivative at depth `m = 0` (un-differenced exponential sum). -/
lemma vdcLam_zero (t : ℝ) (N k : ℕ) :
    vdcLam t 0 (fun x => x.elim0) N k = (t / (2 * Real.pi)) * ((k - 1).factorial : ℝ) / (N : ℝ) ^ k := by
  dsimp [vdcLam]
  have : (∏ i : Fin 0, ((i.elim0 : ℕ) : ℝ)) = 1 := by simp
  have h1 : 0 + k - 1 = k - 1 := by omega
  have h2 : 0 + k = k := by omega
  rw [this, h1, h2]
  ring

/-- Decomposition of the frequency exponent `r = log t / log N` into derivative scale `k`.
For any `t ∈ [N, N^K]`, the index `k = ⌊r + 3/10⌋ + 1` satisfies `2 ≤ k ≤ K + 1` and
`k - 13/10 ≤ r < k - 3/10`, ensuring both terms in the $k$-th derivative bound achieve a power saving. -/
lemma floor_log_bounds (N : ℕ) (hN : 2 ≤ N) (t : ℝ) (K : ℕ) (_hK : 1 ≤ K)
    (htN : (N : ℝ) ≤ t) (htK : t ≤ (N : ℝ) ^ K) :
    let r := Real.log t / Real.log (N : ℝ)
    let k := Nat.floor (r + 3 / 10) + 1
    2 ≤ k ∧ k ≤ K + 1 ∧
    (k : ℝ) - 13 / 10 ≤ r ∧ r < (k : ℝ) - 3 / 10 := by
  intro r k
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hN_ge2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN_pos : 0 < Real.log (N : ℝ) := by
    rw [Real.log_pos_iff hN_pos.le]
    linarith
  have ht_pos : 0 < t := by linarith
  have hr_ge1 : 1 ≤ r := by
    dsimp [r]
    rw [le_div_iff₀ hlogN_pos]
    have : Real.log (N : ℝ) ≤ Real.log t := Real.log_le_log hN_pos htN
    linarith
  have hr_leK : r ≤ (K : ℝ) := by
    dsimp [r]
    rw [div_le_iff₀ hlogN_pos]
    have h1 : Real.log t ≤ Real.log ((N : ℝ) ^ K) := Real.log_le_log ht_pos htK
    have h2 : Real.log ((N : ℝ) ^ K) = (K : ℝ) * Real.log (N : ℝ) := by
      rw [← Real.rpow_natCast, Real.log_rpow hN_pos]
    linarith
  have hr_plus_pos : 0 ≤ r + 3 / 10 := by linarith
  have hfloor_ge1 : 1 ≤ Nat.floor (r + 3 / 10) := by
    have h1 : (1 : ℝ) ≤ r + 3 / 10 := by linarith
    have h2 : (1 : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
    rw [h2] at h1
    exact Nat.le_floor h1
  have hfloor_leK : Nat.floor (r + 3 / 10) ≤ K := by
    have h1 : r + 3 / 10 < ((K + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have h2 := (Nat.floor_lt hr_plus_pos).mpr h1
    omega
  have hk_ge2 : 2 ≤ k := by
    dsimp [k]; omega
  have hk_leK1 : k ≤ K + 1 := by
    dsimp [k]; omega
  have h_floor_le : (Nat.floor (r + 3 / 10) : ℝ) ≤ r + 3 / 10 := Nat.floor_le hr_plus_pos
  have h_lt_floor : r + 3 / 10 < (Nat.floor (r + 3 / 10) : ℝ) + 1 := Nat.lt_floor_add_one (r + 3 / 10)
  have hk_cast : (k : ℝ) = (Nat.floor (r + 3 / 10) : ℝ) + 1 := by
    dsimp [k]
    push_cast
    ring
  refine ⟨hk_ge2, hk_leK1, ?_, ?_⟩
  · linarith [h_lt_floor, hk_cast]
  · linarith [h_floor_le, hk_cast]

/-- The logarithmic base power identity `N^(log t / log N) = t`. -/
lemma rpow_log_div_log (N : ℕ) (hN : 2 ≤ N) (t : ℝ) (ht : 0 < t) :
    (N : ℝ) ^ (Real.log t / Real.log (N : ℝ)) = t := by
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hN_ge2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN_ne : Real.log (N : ℝ) ≠ 0 := by
    have : 1 < (N : ℝ) := by linarith
    exact Real.log_ne_zero_of_pos_of_ne_one hN_pos this.ne'
  rw [Real.rpow_def_of_pos hN_pos]
  have : Real.log (N : ℝ) * (Real.log t / Real.log (N : ℝ)) = Real.log t := by
    rw [mul_comm]
    exact div_mul_cancel₀ (Real.log t) hlogN_ne
  rw [this, Real.exp_log ht]

/-- Bounds on `t / N^k` in terms of powers of `N` from the exponent bounds on `r = log t / log N`. -/
lemma t_div_pow_bounds (N : ℕ) (hN : 2 ≤ N) (t : ℝ) (k : ℕ) (r : ℝ)
    (hr : r = Real.log t / Real.log (N : ℝ)) (ht : 0 < t)
    (h_low : (k : ℝ) - 13 / 10 ≤ r) (h_high : r ≤ (k : ℝ) - 3 / 10) :
    (N : ℝ) ^ (- (13 / 10 : ℝ)) ≤ t / (N : ℝ) ^ k ∧ t / (N : ℝ) ^ k ≤ (N : ℝ) ^ (- (3 / 10 : ℝ)) := by
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hN_ge1 : 1 ≤ (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have ht_eq : t = (N : ℝ) ^ r := by
    rw [hr]
    exact (rpow_log_div_log N hN t ht).symm
  have hNk_rpow : ((N : ℝ) ^ k : ℝ) = (N : ℝ) ^ (k : ℝ) := by rw [Real.rpow_natCast]
  have hdiv : t / (N : ℝ) ^ k = (N : ℝ) ^ (r - (k : ℝ)) := by
    rw [ht_eq, hNk_rpow, ← Real.rpow_sub hN_pos]
  rw [hdiv]
  constructor
  · have : -(13 / 10 : ℝ) ≤ r - (k : ℝ) := by linarith
    exact Real.rpow_le_rpow_of_exponent_le hN_ge1 this
  · have : r - (k : ℝ) ≤ -(3 / 10 : ℝ) := by linarith
    exact Real.rpow_le_rpow_of_exponent_le hN_ge1 this


/-- Unconditional base case `K = 1` of the iterated van der Corput power-saving bound on sub-blocks. -/
theorem norm_sum_exp_neg_log_mul_I_le_pow_iterated_one_kth :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N M : ℕ) (t : ℝ), 2 ≤ N → N < M → M ≤ 2 * N → (N : ℝ) ≤ t → t ≤ (N : ℝ) ^ 1 →
      ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ C * (N : ℝ) ^ (1 - c) :=
  norm_sum_exp_neg_log_mul_I_le_pow_iterated_one_main

/-- Second-derivative constant at depth $K_0$. -/
noncomputable def second_const (K₀ : ℕ) : ℝ :=
  Classical.choose (norm_vdc_S_le_second K₀)

lemma second_const_pos (K₀ : ℕ) : 0 < second_const K₀ :=
  (Classical.choose_spec (norm_vdc_S_le_second K₀)).1

/-- Discrete $k$-th derivative constant at depth $K_0$ for $k \ge 2$. -/
noncomputable def kth_const (K₀ k : ℕ) : ℝ :=
  if hk : 2 ≤ k then
    Classical.choose (norm_vdc_S_le_kth K₀ k hk)
  else 1

lemma kth_const_pos (K₀ k : ℕ) : 0 < kth_const K₀ k := by
  dsimp [kth_const]
  split_ifs with h
  · exact (Classical.choose_spec (norm_vdc_S_le_kth K₀ k h)).1
  · norm_num

/-- Bound constant for scale $k \in [2, K_0]$. -/
noncomputable def step_const (K₀ k : ℕ) : ℝ :=
  if k = 2 then
    let A2 := 1 / (2 * Real.pi)
    second_const K₀ * (Real.sqrt A2 + A2 ^ (-(1 / 2 : ℝ)))
  else if 2 ≤ k then
    let A_k := ((k - 1).factorial : ℝ) / (2 * Real.pi)
    let K_val := (2 : ℝ) ^ (k - 1)
    let E_k := 1 / (2 * K_val - 2)
    kth_const K₀ k * (A_k ^ E_k + A_k ^ (-E_k))
  else 1

lemma step_const_pos (K₀ k : ℕ) : 0 < step_const K₀ k := by
  dsimp [step_const]
  split_ifs
  · have hA2 : 0 < 1 / (2 * Real.pi) := by positivity
    have hs : 0 < Real.sqrt (1 / (2 * Real.pi)) := Real.sqrt_pos.mpr hA2
    have hp : 0 < (1 / (2 * Real.pi)) ^ (-(1 / 2 : ℝ)) := by positivity
    exact mul_pos (second_const_pos K₀) (add_pos hs hp)
  · have hAk : 0 < ((k - 1).factorial : ℝ) / (2 * Real.pi) := by positivity
    have hp1 : 0 < (((k - 1).factorial : ℝ) / (2 * Real.pi)) ^ (1 / (2 * (2 : ℝ) ^ (k - 1) - 2)) := by positivity
    have hp2 : 0 < (((k - 1).factorial : ℝ) / (2 * Real.pi)) ^ (-(1 / (2 * (2 : ℝ) ^ (k - 1) - 2))) := by positivity
    exact mul_pos (kth_const_pos K₀ k) (add_pos hp1 hp2)
  · norm_num

/-- Uniform constant for the iterated van der Corput exponential sum bound up to power $K$. -/
noncomputable def vdc_iterated_const (K : ℕ) (hK : 1 ≤ K) : ℝ :=
  have hs : (Finset.Icc 2 (K + 1)).Nonempty := Finset.nonempty_Icc.mpr (by omega)
  (Finset.Icc 2 (K + 1)).sup' hs (step_const (K + 1))

lemma vdc_iterated_const_pos (K : ℕ) (hK : 1 ≤ K) : 0 < vdc_iterated_const K hK := by
  have hs : (Finset.Icc 2 (K + 1)).Nonempty := Finset.nonempty_Icc.mpr (by omega)
  have h2 : 2 ∈ Finset.Icc 2 (K + 1) := by simp; omega
  have hle := Finset.le_sup' (step_const (K + 1)) h2
  exact (step_const_pos (K + 1) 2).trans_le hle

lemma step_const_le_iterated (K : ℕ) (hK : 1 ≤ K) (k : ℕ) (hk : k ∈ Finset.Icc 2 (K + 1)) :
    step_const (K + 1) k ≤ vdc_iterated_const K hK :=
  Finset.le_sup' (step_const (K + 1)) hk

lemma rpow_le_rpow_of_mul_le (A : ℝ) (hA : 0 ≤ A) (N : ℝ) (hN : 0 ≤ N) (a p : ℝ) (hp : 0 ≤ p)
    (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ A * N ^ a) :
    x ^ p ≤ A ^ p * N ^ (a * p) := by
  have h1 := Real.rpow_le_rpow hx0 hx hp
  have h2 : (A * N ^ a) ^ p = A ^ p * (N ^ a) ^ p := Real.mul_rpow hA (Real.rpow_nonneg hN a)
  have h3 : (N ^ a) ^ p = N ^ (a * p) := (Real.rpow_mul hN a p).symm
  rw [h2, h3] at h1
  exact h1

lemma rpow_le_rpow_neg_of_le_mul (A : ℝ) (hA : 0 < A) (N : ℝ) (hN : 0 < N) (a p : ℝ) (hp : p ≤ 0)
    (x : ℝ) (hx : A * N ^ a ≤ x) :
    x ^ p ≤ A ^ p * N ^ (a * p) := by
  have hbase_pos : 0 < A * N ^ a := mul_pos hA (Real.rpow_pos_of_pos hN a)
  have h1 := Real.rpow_le_rpow_of_nonpos hbase_pos hx hp
  have h2 : (A * N ^ a) ^ p = A ^ p * (N ^ a) ^ p := Real.mul_rpow hA.le (Real.rpow_nonneg hN.le a)
  have h3 : (N ^ a) ^ p = N ^ (a * p) := (Real.rpow_mul hN.le a p).symm
  rw [h2, h3] at h1
  exact h1

lemma mul_rpow_le_rpow_of_exp_le (N : ℝ) (hN : 1 ≤ N) (exp : ℝ) (A : ℝ) (hA : 0 ≤ A)
    (x : ℝ) (hx : x ≤ A * N ^ exp) (c : ℝ) (hexp : exp ≤ 1 - c) :
    x ≤ A * N ^ (1 - c) := by
  refine hx.trans ?_
  have : N ^ exp ≤ N ^ (1 - c) := Real.rpow_le_rpow_of_exponent_le hN hexp
  exact mul_le_mul_of_nonneg_left this hA

lemma c_le_three_twentieth (K : ℕ) (_hK : 1 ≤ K) :
    let c := 1 / (30 * (2 : ℝ) ^ (K + 1))
    1 - (3 / 20 : ℝ) ≤ 1 - c ∧ (13 / 20 : ℝ) ≤ 1 - c := by
  intro c
  have hK1 : 2 ≤ K + 1 := by omega
  have hpow : (4 : ℝ) ≤ (2 : ℝ) ^ (K + 1) := by
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ (K + 1) := pow_le_pow_right₀ (by norm_num) hK1
  have hc : c ≤ 1 / 120 := by
    dsimp [c]
    have : (120 : ℝ) ≤ 30 * (2 : ℝ) ^ (K + 1) := by linarith
    exact one_div_le_one_div_of_le (by norm_num) this
  constructor
  · linarith
  · linarith

lemma c_le_kth_exponents (K k : ℕ) (hk3 : 3 ≤ k) (hkK : k ≤ K + 1) :
    let c := 1 / (30 * (2 : ℝ) ^ (K + 1))
    let K_val := (2 : ℝ) ^ (k - 1)
    let E := 1 / (2 * K_val - 2)
    1 + (- (3 / 10 : ℝ)) * E ≤ 1 - c ∧
    (1 - 1 / K_val) + (- (13 / 10 : ℝ)) * (-E) ≤ 1 - c := by
  intro c K_val E
  have hk1_ge2 : 2 ≤ k - 1 := by omega
  have hk1_leK : k - 1 ≤ K := by omega
  have hK_val_ge4 : (4 : ℝ) ≤ K_val := by
    dsimp [K_val]
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by norm_num) hk1_ge2
  have hK_val_le : K_val ≤ (2 : ℝ) ^ K := by
    dsimp [K_val]
    exact pow_le_pow_right₀ (by norm_num) hk1_leK
  have hK1_pow : (2 : ℝ) ^ (K + 1) = 2 * (2 : ℝ) ^ K := by
    rw [pow_succ]
    ring
  have hK_val_pos : 0 < K_val := by positivity
  have hdenom1_pos : 0 < 2 * K_val - 2 := by linarith
  have hKm1_pos : 0 < K_val - 1 := by linarith
  have _hc_pos : 0 < c := by
    dsimp [c]
    positivity
  have h_bound_c : c ≤ 1 / (60 * K_val) := by
    dsimp [c]
    rw [hK1_pow]
    have : (60 * K_val) ≤ 30 * (2 * (2 : ℝ) ^ K) := by linarith
    exact one_div_le_one_div_of_le (by positivity) this
  constructor
  · have hE_eq : (- (3 / 10 : ℝ)) * E = - (3 / (20 * (K_val - 1))) := by
      dsimp [E]
      have : 2 * K_val - 2 = 2 * (K_val - 1) := by ring
      rw [this]
      field_simp
      ring
    rw [hE_eq]
    suffices c ≤ 3 / (20 * (K_val - 1)) by linarith
    calc c ≤ 1 / (60 * K_val) := h_bound_c
      _ ≤ 3 / (20 * (K_val - 1)) := by
        have : (20 * (K_val - 1)) ≤ 3 * (60 * K_val) := by linarith
        have h1 : 0 < 20 * (K_val - 1) := by linarith
        have h2 : 0 < 60 * K_val := by linarith
        rw [div_le_div_iff₀ h2 h1]
        linarith
  · have hE_eq : (- (13 / 10 : ℝ)) * (-E) = 13 / (20 * (K_val - 1)) := by
      dsimp [E]
      have : 2 * K_val - 2 = 2 * (K_val - 1) := by ring
      rw [this]
      field_simp
      ring
    rw [hE_eq]
    have h_alg : (1 - 1 / K_val) + 13 / (20 * (K_val - 1)) =
        1 - (7 * K_val - 20) / (20 * K_val * (K_val - 1)) := by
      have : K_val ≠ 0 := hK_val_pos.ne'
      have : K_val - 1 ≠ 0 := hKm1_pos.ne'
      field_simp
      ring
    rw [h_alg]
    suffices c ≤ (7 * K_val - 20) / (20 * K_val * (K_val - 1)) by linarith
    have hnum : 2 * K_val ≤ 7 * K_val - 20 := by linarith
    have h_le_step : 1 / (10 * (K_val - 1)) ≤ (7 * K_val - 20) / (20 * K_val * (K_val - 1)) := by
      have h1 : (2 * K_val) / (20 * K_val * (K_val - 1)) = 1 / (10 * (K_val - 1)) := by
        have : (2 * K_val) / (20 * K_val * (K_val - 1)) =
            (2 * K_val * 1) / (2 * K_val * (10 * (K_val - 1))) := by ring
        rw [this, mul_div_mul_left _ _ (by positivity : 2 * K_val ≠ 0)]
      rw [← h1]
      have hden : 0 < 20 * K_val * (K_val - 1) := by positivity
      exact div_le_div_of_nonneg_right hnum hden.le
    refine le_trans ?_ h_le_step
    calc c ≤ 1 / (60 * K_val) := h_bound_c
      _ ≤ 1 / (10 * (K_val - 1)) := by
        have : 10 * (K_val - 1) ≤ 60 * K_val := by linarith
        have h1 : 0 < 10 * (K_val - 1) := by linarith
        exact one_div_le_one_div_of_le h1 this

lemma vdc_bound_k_two (K : ℕ) (hK : 1 ≤ K) (N M : ℕ) (t : ℝ)
    (hN : 2 ≤ N) (hNM : N < M) (hM : M ≤ 2 * N) (htN : (N : ℝ) ≤ t) (htK : t ≤ (N : ℝ) ^ K)
    (hk2 : Nat.floor (Real.log t / Real.log (N : ℝ) + 3 / 10) + 1 = 2) :
    let c := 1 / (30 * (2 : ℝ) ^ (K + 1))
    let C := vdc_iterated_const K hK
    ‖vdc_S t 0 (fun x => x.elim0) N M‖ ≤ C * (N : ℝ) ^ (1 - c) := by
  intro c C
  set r := Real.log t / Real.log (N : ℝ)
  have h_bounds := floor_log_bounds N hN t K hK htN htK
  dsimp [r] at h_bounds
  have hr_low : (2 : ℝ) - 13 / 10 ≤ r := by
    have := h_bounds.2.2.1
    rw [hk2] at this
    exact this
  have hr_high : r ≤ (2 : ℝ) - 3 / 10 := by
    have := h_bounds.2.2.2
    rw [hk2] at this
    exact this.le
  have ht_pos : 0 < t := by
    have : 0 < (N : ℝ) := by positivity
    linarith
  have ht_pow := t_div_pow_bounds N hN t 2 r rfl ht_pos hr_low hr_high
  set lam := vdcLam t 0 (fun x => x.elim0) N 2
  have hlam_eq : lam = (1 / (2 * Real.pi)) * (t / (N : ℝ) ^ 2) := by
    dsimp [lam]
    rw [vdcLam_zero]
    ring
  have hA2_pos : 0 < 1 / (2 * Real.pi) := by positivity
  have hlam_pos : 0 < lam := by
    rw [hlam_eq]
    positivity
  have hlam_low : (1 / (2 * Real.pi)) * (N : ℝ) ^ (- (13 / 10 : ℝ)) ≤ lam := by
    rw [hlam_eq]
    exact mul_le_mul_of_nonneg_left ht_pow.1 hA2_pos.le
  have hlam_high : lam ≤ (1 / (2 * Real.pi)) * (N : ℝ) ^ (- (3 / 10 : ℝ)) := by
    rw [hlam_eq]
    exact mul_le_mul_of_nonneg_left ht_pow.2 hA2_pos.le
  set C2 := second_const (K + 1)
  have hC2_spec := (Classical.choose_spec (norm_vdc_S_le_second (K + 1))).2
  have h_sum_le := hC2_spec t 0 (fun x => x.elim0) N N M ht_pos (by omega)
    (fun i => i.elim0) (fun i => i.elim0) hN (le_refl N) hNM.le hM
  change ‖vdc_S t 0 (fun x => x.elim0) N M‖ ≤ C2 * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) at h_sum_le
  have h_sqrt_lam : Real.sqrt lam = lam ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow lam
  rw [h_sqrt_lam] at h_sum_le
  have h_inv_sqrt : 1 / lam ^ (1 / 2 : ℝ) = lam ^ (- (1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hlam_pos.le, one_div]
  rw [h_inv_sqrt] at h_sum_le
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hN_ge1 : 1 ≤ (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hc_exps := c_le_three_twentieth K hK
  have h_term1_rpow : lam ^ (1 / 2 : ℝ) ≤
      (1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) * (N : ℝ) ^ ((- (3 / 10 : ℝ)) * (1 / 2 : ℝ)) :=
    rpow_le_rpow_of_mul_le (1 / (2 * Real.pi)) hA2_pos.le (N : ℝ) hN_pos.le (- (3 / 10 : ℝ))
      (1 / 2 : ℝ) (by norm_num) lam hlam_pos.le hlam_high
  have h_exp1_num : (- (3 / 10 : ℝ)) * (1 / 2 : ℝ) = - (3 / 20 : ℝ) := by ring
  rw [h_exp1_num] at h_term1_rpow
  have h_term1_mul : (N : ℝ) * lam ^ (1 / 2 : ℝ) ≤
      (1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 - (3 / 20 : ℝ)) := by
    calc (N : ℝ) * lam ^ (1 / 2 : ℝ) ≤ (N : ℝ) * ((1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (- (3 / 20 : ℝ))) :=
           mul_le_mul_of_nonneg_left h_term1_rpow hN_pos.le
      _ = (1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) * ((N : ℝ) * (N : ℝ) ^ (- (3 / 20 : ℝ))) := by ring
      _ = (1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 - (3 / 20 : ℝ)) := by
        have h_N_mul : (N : ℝ) * (N : ℝ) ^ (- (3 / 20 : ℝ)) = (N : ℝ) ^ (1 - (3 / 20 : ℝ)) := by
          calc (N : ℝ) * (N : ℝ) ^ (- (3 / 20 : ℝ)) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (- (3 / 20 : ℝ)) := by rw [Real.rpow_one]
            _ = (N : ℝ) ^ (1 + - (3 / 20 : ℝ)) := by rw [← Real.rpow_add hN_pos]
            _ = (N : ℝ) ^ (1 - (3 / 20 : ℝ)) := by ring_nf
        rw [h_N_mul]
  have hA2_half_nonneg : 0 ≤ (1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) := by positivity
  have h_term1_final : (N : ℝ) * lam ^ (1 / 2 : ℝ) ≤
      (1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 - c) :=
    mul_rpow_le_rpow_of_exp_le (N : ℝ) hN_ge1 (1 - 3 / 20) ((1 / (2 * Real.pi)) ^ (1 / 2 : ℝ))
      hA2_half_nonneg ((N : ℝ) * lam ^ (1 / 2 : ℝ)) h_term1_mul c hc_exps.1
  have h_term2_rpow : lam ^ (- (1 / 2 : ℝ)) ≤
      (1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ)) * (N : ℝ) ^ ((- (13 / 10 : ℝ)) * (- (1 / 2 : ℝ))) :=
    rpow_le_rpow_neg_of_le_mul (1 / (2 * Real.pi)) hA2_pos (N : ℝ) hN_pos (- (13 / 10 : ℝ))
      (- (1 / 2 : ℝ)) (by norm_num) lam hlam_low
  have h_exp2_num : (- (13 / 10 : ℝ)) * (- (1 / 2 : ℝ)) = (13 / 20 : ℝ) := by ring
  rw [h_exp2_num] at h_term2_rpow
  have hA2_neghalf_nonneg : 0 ≤ (1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ)) := by positivity
  have h_term2_final : lam ^ (- (1 / 2 : ℝ)) ≤
      (1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ)) * (N : ℝ) ^ (1 - c) :=
    mul_rpow_le_rpow_of_exp_le (N : ℝ) hN_ge1 (13 / 20) ((1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ)))
      hA2_neghalf_nonneg (lam ^ (- (1 / 2 : ℝ))) h_term2_rpow c hc_exps.2
  have h_sum_bracket : (N : ℝ) * lam ^ (1 / 2 : ℝ) + lam ^ (- (1 / 2 : ℝ)) ≤
      ((1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) + (1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ))) * (N : ℝ) ^ (1 - c) := by
    calc (N : ℝ) * lam ^ (1 / 2 : ℝ) + lam ^ (- (1 / 2 : ℝ)) ≤
           (1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 - c) + (1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ)) * (N : ℝ) ^ (1 - c) :=
             add_le_add h_term1_final h_term2_final
      _ = ((1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) + (1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ))) * (N : ℝ) ^ (1 - c) := by ring
  have h_total : ‖vdc_S t 0 (fun x => x.elim0) N M‖ ≤
      (second_const (K + 1) * ((1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) + (1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ)))) *
      (N : ℝ) ^ (1 - c) := by
    calc ‖vdc_S t 0 (fun x => x.elim0) N M‖ ≤ C2 * ((N : ℝ) * lam ^ (1 / 2 : ℝ) + lam ^ (- (1 / 2 : ℝ))) := h_sum_le
      _ ≤ C2 * (((1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) + (1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ))) * (N : ℝ) ^ (1 - c)) :=
        mul_le_mul_of_nonneg_left h_sum_bracket (second_const_pos (K + 1)).le
      _ = (second_const (K + 1) * ((1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) + (1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ)))) * (N : ℝ) ^ (1 - c) := by ring
  have h_step2 : step_const (K + 1) 2 =
      second_const (K + 1) * ((1 / (2 * Real.pi)) ^ (1 / 2 : ℝ) + (1 / (2 * Real.pi)) ^ (- (1 / 2 : ℝ))) := by
    dsimp [step_const]
    congr 2
    exact Real.sqrt_eq_rpow (1 / (2 * Real.pi))
  rw [← h_step2] at h_total
  have h2_mem : 2 ∈ Finset.Icc 2 (K + 1) := by simp; omega
  have h_step_le_C : step_const (K + 1) 2 ≤ C := step_const_le_iterated K hK 2 h2_mem
  have hN_rpow_pos : 0 ≤ (N : ℝ) ^ (1 - c) := Real.rpow_nonneg hN_pos.le (1 - c)
  refine h_total.trans ?_
  exact mul_le_mul_of_nonneg_right h_step_le_C hN_rpow_pos

lemma vdc_bound_k_of_three_le (K : ℕ) (hK : 1 ≤ K) (N M : ℕ) (t : ℝ)
    (hN : 2 ≤ N) (hNM : N < M) (hM : M ≤ 2 * N) (htN : (N : ℝ) ≤ t) (htK : t ≤ (N : ℝ) ^ K)
    (k : ℕ) (hk : Nat.floor (Real.log t / Real.log (N : ℝ) + 3 / 10) + 1 = k) (hk3 : 3 ≤ k) :
    let c := 1 / (30 * (2 : ℝ) ^ (K + 1))
    let C := vdc_iterated_const K hK
    ‖vdc_S t 0 (fun x => x.elim0) N M‖ ≤ C * (N : ℝ) ^ (1 - c) := by
  intro c C
  set r := Real.log t / Real.log (N : ℝ)
  have h_bounds := floor_log_bounds N hN t K hK htN htK
  dsimp [r] at h_bounds
  have hkK : k ≤ K + 1 := by
    have := h_bounds.2.1
    rw [hk] at this
    exact this
  have hk2 : 2 ≤ k := by omega
  have hr_low : (k : ℝ) - 13 / 10 ≤ r := by
    have := h_bounds.2.2.1
    rw [hk] at this
    exact this
  have hr_high : r ≤ (k : ℝ) - 3 / 10 := by
    have := h_bounds.2.2.2
    rw [hk] at this
    exact this.le
  have ht_pos : 0 < t := by
    have : 0 < (N : ℝ) := by positivity
    linarith
  have ht_pow := t_div_pow_bounds N hN t k r rfl ht_pos hr_low hr_high
  set lam := vdcLam t 0 (fun x => x.elim0) N k
  set Ak := ((k - 1).factorial : ℝ) / (2 * Real.pi)
  have hlam_eq : lam = Ak * (t / (N : ℝ) ^ k) := by
    dsimp [lam, Ak]
    rw [vdcLam_zero]
    ring
  have hAk_pos : 0 < Ak := by
    dsimp [Ak]
    positivity
  have hlam_pos : 0 < lam := by
    rw [hlam_eq]
    positivity
  have hlam_low : Ak * (N : ℝ) ^ (- (13 / 10 : ℝ)) ≤ lam := by
    rw [hlam_eq]
    exact mul_le_mul_of_nonneg_left ht_pow.1 hAk_pos.le
  have hlam_high : lam ≤ Ak * (N : ℝ) ^ (- (3 / 10 : ℝ)) := by
    rw [hlam_eq]
    exact mul_le_mul_of_nonneg_left ht_pow.2 hAk_pos.le
  set K_val := (2 : ℝ) ^ (k - 1)
  set E := 1 / (2 * K_val - 2)
  have hk_const_eq : kth_const (K + 1) k = Classical.choose (norm_vdc_S_le_kth (K + 1) k hk2) := by
    dsimp [kth_const]
    split_ifs
    rfl
  have hk_spec := (Classical.choose_spec (norm_vdc_S_le_kth (K + 1) k hk2)).2
  have h_sum_le := hk_spec t 0 (fun x => x.elim0) N N M ht_pos (by omega)
    (fun i => i.elim0) (fun i => i.elim0) hN (le_refl N) hNM.le hM
  change ‖vdc_S t 0 (fun x => x.elim0) N M‖ ≤
    Classical.choose (norm_vdc_S_le_kth (K + 1) k hk2) *
      ((N : ℝ) * lam ^ E + (N : ℝ) ^ (1 - 1 / K_val) * lam ^ (-E)) at h_sum_le
  rw [← hk_const_eq] at h_sum_le
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hN_ge1 : 1 ≤ (N : ℝ) := by
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have _hK_val_ge4 : (4 : ℝ) ≤ K_val := by
    dsimp [K_val]
    have : 2 ≤ k - 1 := by omega
    calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (2 : ℝ) ^ (k - 1) := pow_le_pow_right₀ (by norm_num) this
  have hE_pos : 0 < E := by
    dsimp [E]
    have : 0 < 2 * K_val - 2 := by linarith [_hK_val_ge4]
    exact one_div_pos.mpr this
  have hc_exps := c_le_kth_exponents K k hk3 hkK
  have h_term1_rpow : lam ^ E ≤ Ak ^ E * (N : ℝ) ^ ((- (3 / 10 : ℝ)) * E) :=
    rpow_le_rpow_of_mul_le Ak hAk_pos.le (N : ℝ) hN_pos.le (- (3 / 10 : ℝ))
      E hE_pos.le lam hlam_pos.le hlam_high
  have h_term1_mul : (N : ℝ) * lam ^ E ≤ Ak ^ E * (N : ℝ) ^ (1 + (- (3 / 10 : ℝ)) * E) := by
    calc (N : ℝ) * lam ^ E ≤ (N : ℝ) * (Ak ^ E * (N : ℝ) ^ ((- (3 / 10 : ℝ)) * E)) :=
           mul_le_mul_of_nonneg_left h_term1_rpow hN_pos.le
      _ = Ak ^ E * ((N : ℝ) * (N : ℝ) ^ ((- (3 / 10 : ℝ)) * E)) := by ring
      _ = Ak ^ E * (N : ℝ) ^ (1 + (- (3 / 10 : ℝ)) * E) := by
        have h_N_mul : (N : ℝ) * (N : ℝ) ^ ((- (3 / 10 : ℝ)) * E) = (N : ℝ) ^ (1 + (- (3 / 10 : ℝ)) * E) := by
          calc (N : ℝ) * (N : ℝ) ^ ((- (3 / 10 : ℝ)) * E) = (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ ((- (3 / 10 : ℝ)) * E) := by rw [Real.rpow_one]
            _ = (N : ℝ) ^ ((1 : ℝ) + (- (3 / 10 : ℝ)) * E) := by rw [← Real.rpow_add hN_pos]
        rw [h_N_mul]
  have hAk_E_nonneg : 0 ≤ Ak ^ E := Real.rpow_nonneg hAk_pos.le E
  have h_term1_final : (N : ℝ) * lam ^ E ≤ Ak ^ E * (N : ℝ) ^ (1 - c) :=
    mul_rpow_le_rpow_of_exp_le (N : ℝ) hN_ge1 (1 + (- (3 / 10 : ℝ)) * E) (Ak ^ E)
      hAk_E_nonneg ((N : ℝ) * lam ^ E) h_term1_mul c hc_exps.1
  have h_neg_E : -E ≤ 0 := by linarith
  have h_term2_rpow : lam ^ (-E) ≤ Ak ^ (-E) * (N : ℝ) ^ ((- (13 / 10 : ℝ)) * (-E)) :=
    rpow_le_rpow_neg_of_le_mul Ak hAk_pos (N : ℝ) hN_pos (- (13 / 10 : ℝ))
      (-E) h_neg_E lam hlam_low
  have h_term2_mul : (N : ℝ) ^ (1 - 1 / K_val) * lam ^ (-E) ≤
      Ak ^ (-E) * (N : ℝ) ^ ((1 - 1 / K_val) + (- (13 / 10 : ℝ)) * (-E)) := by
    have h_coeff_nonneg : 0 ≤ (N : ℝ) ^ (1 - 1 / K_val) := by positivity
    calc (N : ℝ) ^ (1 - 1 / K_val) * lam ^ (-E) ≤
           (N : ℝ) ^ (1 - 1 / K_val) * (Ak ^ (-E) * (N : ℝ) ^ ((- (13 / 10 : ℝ)) * (-E))) :=
             mul_le_mul_of_nonneg_left h_term2_rpow h_coeff_nonneg
      _ = Ak ^ (-E) * ((N : ℝ) ^ (1 - 1 / K_val) * (N : ℝ) ^ ((- (13 / 10 : ℝ)) * (-E))) := by ring
      _ = Ak ^ (-E) * (N : ℝ) ^ ((1 - 1 / K_val) + (- (13 / 10 : ℝ)) * (-E)) := by
        rw [← Real.rpow_add hN_pos]
  have hAk_negE_nonneg : 0 ≤ Ak ^ (-E) := Real.rpow_nonneg hAk_pos.le (-E)
  have h_term2_final : (N : ℝ) ^ (1 - 1 / K_val) * lam ^ (-E) ≤ Ak ^ (-E) * (N : ℝ) ^ (1 - c) :=
    mul_rpow_le_rpow_of_exp_le (N : ℝ) hN_ge1 ((1 - 1 / K_val) + (- (13 / 10 : ℝ)) * (-E)) (Ak ^ (-E))
      hAk_negE_nonneg ((N : ℝ) ^ (1 - 1 / K_val) * lam ^ (-E)) h_term2_mul c hc_exps.2
  have h_sum_bracket : (N : ℝ) * lam ^ E + (N : ℝ) ^ (1 - 1 / K_val) * lam ^ (-E) ≤
      (Ak ^ E + Ak ^ (-E)) * (N : ℝ) ^ (1 - c) := by
    calc (N : ℝ) * lam ^ E + (N : ℝ) ^ (1 - 1 / K_val) * lam ^ (-E) ≤
           Ak ^ E * (N : ℝ) ^ (1 - c) + Ak ^ (-E) * (N : ℝ) ^ (1 - c) :=
             add_le_add h_term1_final h_term2_final
      _ = (Ak ^ E + Ak ^ (-E)) * (N : ℝ) ^ (1 - c) := by ring
  have h_total : ‖vdc_S t 0 (fun x => x.elim0) N M‖ ≤
      (kth_const (K + 1) k * (Ak ^ E + Ak ^ (-E))) * (N : ℝ) ^ (1 - c) := by
    calc ‖vdc_S t 0 (fun x => x.elim0) N M‖ ≤
           kth_const (K + 1) k * ((N : ℝ) * lam ^ E + (N : ℝ) ^ (1 - 1 / K_val) * lam ^ (-E)) := h_sum_le
      _ ≤ kth_const (K + 1) k * ((Ak ^ E + Ak ^ (-E)) * (N : ℝ) ^ (1 - c)) :=
        mul_le_mul_of_nonneg_left h_sum_bracket (kth_const_pos (K + 1) k).le
      _ = (kth_const (K + 1) k * (Ak ^ E + Ak ^ (-E))) * (N : ℝ) ^ (1 - c) := by ring
  have h_step_k : step_const (K + 1) k = kth_const (K + 1) k * (Ak ^ E + Ak ^ (-E)) := by
    dsimp [step_const]
    split_ifs with h2
    · omega
    · rfl
  rw [← h_step_k] at h_total
  have hk_mem : k ∈ Finset.Icc 2 (K + 1) := by simp; omega
  have h_step_le_C : step_const (K + 1) k ≤ C := step_const_le_iterated K hK k hk_mem
  have hN_rpow_pos : 0 ≤ (N : ℝ) ^ (1 - c) := Real.rpow_nonneg hN_pos.le (1 - c)
  refine h_total.trans ?_
  exact mul_le_mul_of_nonneg_right h_step_le_C hN_rpow_pos

/-- Iterated van der Corput exponential sum bound on dyadic blocks for general $K \ge 1$. -/
theorem norm_sum_exp_neg_log_mul_I_le_pow_iterated (K : ℕ) (hK : 1 ≤ K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (N M : ℕ) (t : ℝ), 2 ≤ N → N < M → M ≤ 2 * N → (N : ℝ) ≤ t → t ≤ (N : ℝ) ^ K →
      ‖∑ n ∈ Finset.Ioc N M, Complex.exp (-((t * Real.log n : ℝ) : ℂ) * Complex.I)‖ ≤ C * (N : ℝ) ^ (1 - c) := by
  set c := 1 / (30 * (2 : ℝ) ^ (K + 1))
  set C := vdc_iterated_const K hK
  refine ⟨c, C, ?_, vdc_iterated_const_pos K hK, ?_⟩
  · dsimp [c]; positivity
  intro N M t hN hNM hM htN htK
  have ht_pos : 0 < t := by
    have : 0 < (N : ℝ) := by positivity
    linarith
  have h_rw := (vdc_S_zero_eq t N M).symm
  rw [h_rw]
  set r := Real.log t / Real.log (N : ℝ)
  set k := Nat.floor (r + 3 / 10) + 1
  have h_bounds := floor_log_bounds N hN t K hK htN htK
  by_cases hk2 : k = 2
  · exact vdc_bound_k_two K hK N M t hN hNM hM htN htK hk2
  · have hk3 : 3 ≤ k := by
      have : 2 ≤ k := h_bounds.1
      omega
    exact vdc_bound_k_of_three_le K hK N M t hN hNM hM htN htK k rfl hk3

end Erdos1201.MR

