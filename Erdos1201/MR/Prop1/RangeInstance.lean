import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Ranges

open scoped BigOperators

/-!
# Explicit Range System Instance for Proposition 1

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module constructs an explicit range system satisfying the separation conditions (2), (3)
and all properties required by Proposition 1 and the short-interval deduction.
-/

namespace Erdos1201.MR

lemma ceil_le_floor_of_sub_ge_two {x y : ℝ} (hx : 0 ≤ x) (h : x + 2 ≤ y) :
    ⌈x⌉₊ ≤ ⌊y⌋₊ := by
  have h_ceil : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx
  have h_floor : y - 1 < (⌊y⌋₊ : ℝ) := Nat.sub_one_lt_floor y
  have : (⌈x⌉₊ : ℝ) ≤ (⌊y⌋₊ : ℝ) := by linarith
  exact Nat.cast_le.mp this

lemma exp_add_two_le_exp_of_add_one_le {x y : ℝ} (hx : 1 ≤ x) (h : x + 1 ≤ y) :
    Real.exp x + 2 ≤ Real.exp y := by
  have he : (1.7 : ℝ) ≤ Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9]
  have he_x : Real.exp 1 ≤ Real.exp x := Real.exp_le_exp.mpr hx
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h_diff : (2 : ℝ) ≤ (Real.exp 1 - 1) * Real.exp x := by nlinarith
  have h_mul : Real.exp x + 2 ≤ Real.exp 1 * Real.exp x := by linarith
  have h_exp_add : Real.exp 1 * Real.exp x = Real.exp (x + 1) := by
    rw [← Real.exp_add, add_comm]
  have h_le : Real.exp (x + 1) ≤ Real.exp y := Real.exp_le_exp.mpr h
  linarith

noncomputable def kappa (η : ℝ) : ℝ := 200 / (η * (1 / 6 - η))

noncomputable def E_seq (η : ℝ) (h : ℕ) (j : ℕ) : ℝ :=
  let L := Real.log (h : ℝ)
  let Q₀ := ⌊Real.exp (L / Real.log L)⌋₊
  let ℓ₁ := Real.log (Q₀ : ℝ)
  if j = 0 then (kappa η) * Real.log L
  else
    let k : ℝ := ((j + 1 : ℕ) : ℝ)
    (100 : ℝ) ^ (j + 1) * k ^ (4 * (j + 1)) * ℓ₁ ^ j / η ^ (j + 1)

noncomputable def F_seq (η : ℝ) (h : ℕ) (j : ℕ) : ℝ :=
  let L := Real.log (h : ℝ)
  let Q₀ := ⌊Real.exp (L / Real.log L)⌋₊
  let ℓ₁ := Real.log (Q₀ : ℝ)
  if j = 0 then L / Real.log L
  else
    let k : ℝ := ((j + 1 : ℕ) : ℝ)
    (100 : ℝ) ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1) / η ^ (j + 1)

noncomputable def P_seq (η : ℝ) (h : ℕ) (j : ℕ) : ℕ :=
  ⌈Real.exp (E_seq η h j)⌉₊

noncomputable def Q_seq (η : ℝ) (h : ℕ) (j : ℕ) : ℕ :=
  ⌊Real.exp (F_seq η h j)⌋₊

lemma log_P_seq_ge (η : ℝ) (h : ℕ) (j : ℕ) :
    E_seq η h j ≤ Real.log (P_seq η h j : ℝ) := by
  have h_exp_pos : 0 < Real.exp (E_seq η h j) := Real.exp_pos _
  have h_le : Real.exp (E_seq η h j) ≤ (P_seq η h j : ℝ) := Nat.le_ceil _
  have h_log := Real.log_le_log h_exp_pos h_le
  rwa [Real.log_exp] at h_log

lemma log_Q_seq_le (η : ℝ) (h : ℕ) (j : ℕ) (hF : 0 ≤ F_seq η h j) :
    Real.log (Q_seq η h j : ℝ) ≤ F_seq η h j := by
  have h_floor : (Q_seq η h j : ℝ) ≤ Real.exp (F_seq η h j) := Nat.floor_le (Real.exp_pos _).le
  have h_pos : 0 < (Q_seq η h j : ℝ) := by
    have : 1 ≤ Real.exp (F_seq η h j) := Real.one_le_exp hF
    exact Nat.cast_pos.mpr ((Nat.one_le_floor_iff (Real.exp (F_seq η h j))).mpr this)
  have h_log := Real.log_le_log h_pos h_floor
  rwa [Real.log_exp] at h_log

lemma Q_zero_le_h (η : ℝ) (h : ℕ) (h16 : 16 ≤ h) :
    (Q_seq η h 0 : ℝ) ≤ (h : ℝ) := by
  dsimp [Q_seq, F_seq]
  have h_floor : (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) ≤
      Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ))) :=
    Nat.floor_le (Real.exp_pos _).le
  have h16_r : (16 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h16
  have hlog16 : Real.exp 1 < Real.log 16 := by
    have h16' : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
    have hlog16' : Real.log 16 = 4 * Real.log 2 := by
      rw [h16', Real.log_pow (2 : ℝ) 4]
      push_cast
      ring
    have hlog2 := Real.log_two_gt_d9
    have he := Real.exp_one_lt_d9
    linarith
  have hlogh : Real.exp 1 < Real.log (h : ℝ) := by
    have := Real.log_le_log (by norm_num) h16_r
    linarith
  have hlog_log : 1 < Real.log (Real.log (h : ℝ)) := by
    have hlog := Real.log_lt_log (Real.exp_pos 1) hlogh
    rwa [Real.log_exp] at hlog
  have hlogh_pos : 0 < Real.log (h : ℝ) := by
    have : 0 < Real.exp 1 := Real.exp_pos 1
    linarith
  have hdiv : Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)) ≤ Real.log (h : ℝ) := by
    have h1 : 1 ≤ Real.log (Real.log (h : ℝ)) := hlog_log.le
    exact div_le_self hlogh_pos.le h1
  have hexp_le : Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ))) ≤ (h : ℝ) := by
    have := Real.exp_le_exp.mpr hdiv
    have hpos : 0 < (h : ℝ) := by linarith
    rwa [Real.exp_log hpos] at this
  exact h_floor.trans hexp_le


lemma F_seq_eq_mul_E_seq (η : ℝ) (h : ℕ) (j : ℕ) (hj : 1 ≤ j) :
    let L := Real.log (h : ℝ)
    let Q₀ := ⌊Real.exp (L / Real.log L)⌋₊
    let ℓ₁ := Real.log (Q₀ : ℝ)
    F_seq η h j = ((j + 1 : ℕ) : ℝ) ^ 2 * ℓ₁ * E_seq η h j := by
  dsimp [F_seq, E_seq]
  have hj0 : ¬ j = 0 := by omega
  simp only [hj0, ↓reduceIte]
  set k : ℝ := ((j + 1 : ℕ) : ℝ)
  set L := Real.log (h : ℝ)
  set Q₀ := ⌊Real.exp (L / Real.log L)⌋₊
  set ℓ₁ := Real.log (Q₀ : ℝ)
  have hk_pow : k ^ (4 * (j + 1) + 2) = k ^ (4 * (j + 1)) * k ^ 2 := by
    rw [pow_add]
  have hℓ_pow : ℓ₁ ^ (j + 1) = ℓ₁ ^ j * ℓ₁ := by
    rw [pow_succ]
  rw [hk_pow, hℓ_pow]
  ring

lemma one_le_E_seq_succ {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j : ℕ) (hj : 1 ≤ j) :
    1 ≤ E_seq η h j := by
  dsimp [E_seq]
  have hj0 : ¬ j = 0 := by omega
  simp only [hj0, ↓reduceIte]
  have h100 : (1 : ℝ) ≤ 100 ^ (j + 1) := by
    have : (1 : ℝ) ≤ 100 := by norm_num
    exact one_le_pow₀ this
  have hk : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ (4 * (j + 1)) := by
    have : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j + 1)
    exact one_le_pow₀ this
  have hℓ : (1 : ℝ) ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) ^ j :=
    one_le_pow₀ h_ℓ₁
  have h_num1 : (1 : ℝ) ≤ 100 ^ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ (4 * (j + 1)) := by
    have := mul_le_mul h100 hk (by positivity) (by positivity)
    linarith
  have h_num : (1 : ℝ) ≤ 100 ^ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ (4 * (j + 1)) *
      Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) ^ j := by
    have := mul_le_mul h_num1 hℓ (by positivity) (by positivity)
    linarith
  have h_denom : η ^ (j + 1) ≤ 1 := by
    have : η ≤ 1 := by linarith
    exact pow_le_one₀ hη0.le this
  have h_denom_pos : 0 < η ^ (j + 1) := by positivity
  have : η ^ (j + 1) ≤ 100 ^ (j + 1) * ((j + 1 : ℕ) : ℝ) ^ (4 * (j + 1)) *
      Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) ^ j :=
    h_denom.trans h_num
  exact (one_le_div₀ h_denom_pos).mpr this

lemma two_le_P_seq {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_E0 : 1 ≤ E_seq η h 0) (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j : ℕ) : 2 ≤ P_seq η h j := by
  dsimp [P_seq]
  by_cases hj : j = 0
  · subst hj
    have he : Real.exp 1 ≤ Real.exp (E_seq η h 0) := Real.exp_le_exp.mpr h_E0
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h_le : (2 : ℝ) ≤ (⌈Real.exp (E_seq η h 0)⌉₊ : ℝ) := by
      have := Nat.le_ceil (Real.exp (E_seq η h 0))
      linarith
    exact Nat.cast_le.mp h_le
  · have hj_pos : 1 ≤ j := by omega
    have h_E := one_le_E_seq_succ hη0 hη h h_ℓ₁ j hj_pos
    have he : Real.exp 1 ≤ Real.exp (E_seq η h j) := Real.exp_le_exp.mpr h_E
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h_le : (2 : ℝ) ≤ (⌈Real.exp (E_seq η h j)⌉₊ : ℝ) := by
      have := Nat.le_ceil (Real.exp (E_seq η h j))
      linarith
    exact Nat.cast_le.mp h_le

lemma P_seq_le_Q_seq {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_EF0 : E_seq η h 0 + 1 ≤ F_seq η h 0) (h_E0 : 1 ≤ E_seq η h 0)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j : ℕ) : P_seq η h j ≤ Q_seq η h j := by
  dsimp [P_seq, Q_seq]
  by_cases hj : j = 0
  · subst hj
    have h_exp := exp_add_two_le_exp_of_add_one_le h_E0 h_EF0
    have h_pos : 0 ≤ Real.exp (E_seq η h 0) := (Real.exp_pos _).le
    exact ceil_le_floor_of_sub_ge_two h_pos h_exp
  · have hj_pos : 1 ≤ j := by omega
    have h_F := F_seq_eq_mul_E_seq η h j hj_pos
    have h_E_ge := one_le_E_seq_succ hη0 hη h h_ℓ₁ j hj_pos
    have hE_pos : 0 < E_seq η h j := by linarith
    have h_mul : 4 * E_seq η h j ≤ F_seq η h j := by
      rw [h_F]
      have hj2 : (4 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ j + 1)
        nlinarith
      have hℓ : (1 : ℝ) ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) := h_ℓ₁
      have h_prod : 4 ≤ ((j + 1 : ℕ) : ℝ) ^ 2 * Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) := by
        have := mul_le_mul hj2 hℓ (by positivity) (by positivity)
        linarith
      have := mul_le_mul_of_nonneg_right h_prod hE_pos.le
      linarith
    have h_add_one : E_seq η h j + 1 ≤ F_seq η h j := by linarith [h_mul, h_E_ge]
    have h_exp := exp_add_two_le_exp_of_add_one_le h_E_ge h_add_one
    have h_pos : 0 ≤ Real.exp (E_seq η h j) := (Real.exp_pos _).le
    exact ceil_le_floor_of_sub_ge_two h_pos h_exp


lemma cond3_base {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (hℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) :
    (8 * ((2 : ℕ) : ℝ) ^ 2 / η) * Real.log (Q_seq η h 0 : ℝ) + 16 * Real.log ((2 : ℕ) : ℝ) ≤ E_seq η h 1 := by
  dsimp [E_seq, Q_seq, F_seq]
  set ℓ₁ := Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)
  have h_lhs : (8 * ((2 : ℕ) : ℝ) ^ 2 / η) * ℓ₁ + 16 * Real.log 2 ≤
      (32 / η + 16 * Real.log 2) * ℓ₁ := by
    have : 16 * Real.log 2 ≤ 16 * Real.log 2 * ℓ₁ := by
      have : 0 ≤ 16 * Real.log 2 := by positivity
      nlinarith
    linarith
  have hlog2_lt : Real.log 2 < 1 := by
    have : Real.log 2 < Real.log (Real.exp 1) := by
      apply Real.log_lt_log (by norm_num)
      linarith [Real.exp_one_gt_d9]
    rwa [Real.log_exp] at this
  have h_eta_sq : 0 < η ^ 2 := by positivity
  have h_bound1 : 32 / η ≤ 192 / η ^ 2 := by
    rw [div_le_div_iff₀ hη0 h_eta_sq]
    nlinarith
  have h_bound2 : 16 ≤ 1000000 / η ^ 2 := by
    have : 16 * η ^ 2 ≤ 1000000 := by nlinarith
    exact (le_div_iff₀ h_eta_sq).mpr this
  have h_coeff : 32 / η + 16 * Real.log 2 ≤ (100 : ℝ) ^ 2 * 2 ^ 8 / η ^ 2 := by
    have h100 : (100 : ℝ) ^ 2 * 2 ^ 8 = 2560000 := by norm_num
    rw [h100]
    calc 32 / η + 16 * Real.log 2
      _ ≤ 32 / η + 16 := by linarith
      _ ≤ 192 / η ^ 2 + 1000000 / η ^ 2 := by linarith
      _ = 1000192 / η ^ 2 := by ring
      _ ≤ 2560000 / η ^ 2 := by
        apply div_le_div_of_nonneg_right _ h_eta_sq.le
        norm_num
  have h_rhs : (32 / η + 16 * Real.log 2) * ℓ₁ ≤ (100 : ℝ) ^ 2 * 2 ^ 8 * ℓ₁ ^ 1 / η ^ 2 := by
    rw [pow_one, mul_div_right_comm]
    have : 0 ≤ ℓ₁ := by linarith
    exact mul_le_mul_of_nonneg_right h_coeff this
  linarith


lemma cond3_succ {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (i : ℕ) (hi : 1 ≤ i) :
    let j := i + 1
    let k : ℝ := ((j + 1 : ℕ) : ℝ)
    (8 * k ^ 2 / η) * F_seq η h i + 16 * Real.log k ≤ E_seq η h j := by
  dsimp [F_seq, E_seq]
  have hi0 : ¬ i = 0 := by omega
  have hj0 : ¬ (i + 1) = 0 := by omega
  simp only [hi0, ↓reduceIte]
  set k : ℝ := (((i + 1) + 1 : ℕ) : ℝ)
  set ki : ℝ := ((i + 1 : ℕ) : ℝ)
  set ℓ₁ := Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)
  have hk_ge : 3 ≤ k := by
    dsimp [k]
    have : (3 : ℕ) ≤ (i + 1) + 1 := by omega
    exact_mod_cast this
  have hki_le_k : ki ≤ k := by
    dsimp [ki, k]
    have : i + 1 ≤ (i + 1) + 1 := by omega
    exact_mod_cast this
  have hki_pos : 0 < ki := by
    dsimp [ki]
    have : 0 < i + 1 := by omega
    exact Nat.cast_pos.mpr this
  have hpow_le : ki ^ (4 * (i + 1) + 2) ≤ k ^ (4 * (i + 1) + 2) :=
    pow_le_pow_left₀ hki_pos.le hki_le_k _
  have h4k : 4 * (i + 1 + 1) = 2 + (4 * (i + 1) + 2) := by ring
  have hk_split : k ^ (4 * (i + 1 + 1)) = k ^ 2 * k ^ (4 * (i + 1) + 2) := by
    rw [h4k, pow_add]
  have h_bound_E : (100 / η) * k ^ 2 * (100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1)) ≤
      100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) * ℓ₁ ^ (i + 1) / η ^ (i + 1 + 1) := by
    rw [hk_split, pow_succ' 100 (i + 1), pow_succ' η (i + 1)]
    have h_div1 : (100 / η) * k ^ 2 * (100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1)) =
        (100 * 100 ^ (i + 1)) * (k ^ 2 * ki ^ (4 * (i + 1) + 2)) * ℓ₁ ^ (i + 1) / (η * η ^ (i + 1)) := by ring
    rw [h_div1]
    have h_k_prod : k ^ 2 * ki ^ (4 * (i + 1) + 2) ≤ k ^ 2 * k ^ (4 * (i + 1) + 2) :=
      mul_le_mul_of_nonneg_left hpow_le (by positivity)
    have h_prod : (100 * 100 ^ (i + 1)) * (k ^ 2 * ki ^ (4 * (i + 1) + 2)) * ℓ₁ ^ (i + 1) ≤
        (100 * 100 ^ (i + 1)) * (k ^ 2 * k ^ (4 * (i + 1) + 2)) * ℓ₁ ^ (i + 1) := by
      have h1 : 0 ≤ (100 : ℝ) * 100 ^ (i + 1) := by positivity
      have h2 : 0 ≤ ℓ₁ ^ (i + 1) := by
        have : 0 ≤ ℓ₁ := by linarith
        positivity
      have := mul_le_mul_of_nonneg_left h_k_prod h1
      exact mul_le_mul_of_nonneg_right this h2
    have h_denom_pos : 0 < η * η ^ (i + 1) := by positivity
    exact div_le_div_of_nonneg_right h_prod h_denom_pos.le
  have hF_ge1 : 1 ≤ 100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1) := by
    have h100 : (1 : ℝ) ≤ 100 ^ (i + 1) := one_le_pow₀ (by norm_num)
    have hki : (1 : ℝ) ≤ ki ^ (4 * (i + 1) + 2) := by
      dsimp [ki]
      have : (1 : ℕ) ≤ i + 1 := by omega
      have : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast this
      exact one_le_pow₀ this
    have hℓ : (1 : ℝ) ≤ ℓ₁ ^ (i + 1) := one_le_pow₀ h_ℓ₁
    have h_num1 : (1 : ℝ) ≤ 100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) := by
      have := mul_le_mul h100 hki (by positivity) (by positivity)
      linarith
    have h_num : (1 : ℝ) ≤ 100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) := by
      have := mul_le_mul h_num1 hℓ (by positivity) (by positivity)
      linarith
    have h_denom : η ^ (i + 1) ≤ 1 := by
      have : η ≤ 1 := by linarith
      exact pow_le_one₀ hη0.le this
    have h_denom_pos : 0 < η ^ (i + 1) := by positivity
    have : η ^ (i + 1) ≤ 100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) := h_denom.trans h_num
    exact (one_le_div₀ h_denom_pos).mpr this
  have hk_pos : 0 < k := by linarith
  have hlog_lt : Real.log k < k := (Real.log_le_sub_one_of_pos hk_pos).trans_lt (by linarith)
  have h_split : (100 / η) * k ^ 2 * (100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1)) =
      (8 * k ^ 2 / η) * (100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1)) +
      (92 * k ^ 2 / η) * (100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1)) := by ring
  rw [h_split] at h_bound_E
  have h_comp : 16 * Real.log k ≤ (92 * k ^ 2 / η) * (100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1)) := by
    have h1 : 16 * Real.log k < 16 * k := by linarith
    have h_k2 : k ≤ k ^ 2 := by nlinarith
    have h_eta : (1 : ℝ) ≤ 1 / η := by
      have : η < 1 := by linarith
      have := one_lt_one_div hη0 this
      linarith
    have h2 : 16 * k ≤ (92 * k ^ 2 / η) * (100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1)) := by
      have h_div : (92 * k ^ 2 / η) * (100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1)) =
          92 * k ^ 2 * (1 / η) * (100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1)) := by ring
      rw [h_div]
      calc 16 * k
        _ ≤ 16 * k ^ 2 := by nlinarith
        _ = 16 * k ^ 2 * 1 * 1 := by ring
        _ ≤ 92 * k ^ 2 * (1 / η) * (100 ^ (i + 1) * ki ^ (4 * (i + 1) + 2) * ℓ₁ ^ (i + 1) / η ^ (i + 1)) := by
          have h_part : 16 * k ^ 2 ≤ 92 * k ^ 2 := by nlinarith
          have h_step1 : 16 * k ^ 2 * 1 ≤ 92 * k ^ 2 * (1 / η) := by
            have := mul_le_mul h_part h_eta (by positivity) (by positivity)
            linarith
          have h_pos2 : 0 ≤ 92 * k ^ 2 * (1 / η) := by positivity
          exact mul_le_mul h_step1 hF_ge1 (by positivity) h_pos2
    linarith
  linarith

lemma cond3_seq {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j i : ℕ) (hij : i + 1 = j) :
    (8 * ((j + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (Q_seq η h i : ℝ) + 16 * Real.log ((j + 1 : ℕ) : ℝ) ≤
      Real.log (P_seq η h j : ℝ) := by
  have hP := log_P_seq_ge η h j
  by_cases hi : i = 0
  · subst hi
    have hj1 : j = 1 := by omega
    subst hj1
    have h_base := cond3_base hη0 hη h h_ℓ₁
    exact h_base.trans hP
  · have hi_pos : 1 ≤ i := by omega
    subst hij
    have hF_pos : 0 ≤ F_seq η h i := by
      dsimp [F_seq]
      simp only [hi, ↓reduceIte]
      positivity
    have hQ := log_Q_seq_le η h i hF_pos
    have h_succ := cond3_succ hη0 hη h h_ℓ₁ i hi_pos
    have h_coeff_pos : 0 ≤ 8 * ((i + 1 + 1 : ℕ) : ℝ) ^ 2 / η := by positivity
    have h_mul := mul_le_mul_of_nonneg_left hQ h_coeff_pos
    linarith

lemma log_ge_of_ge_ceil_exp (C : ℝ) (h : ℕ) (hh : ⌈Real.exp C⌉₊ ≤ h) :
    C ≤ Real.log (h : ℝ) := by
  have h_exp_pos : 0 < Real.exp C := Real.exp_pos C
  have h_le : Real.exp C ≤ (⌈Real.exp C⌉₊ : ℝ) := Nat.le_ceil (Real.exp C)
  have hh_r : (⌈Real.exp C⌉₊ : ℝ) ≤ (h : ℝ) := Nat.cast_le.mpr hh
  have h_trans : Real.exp C ≤ (h : ℝ) := h_le.trans hh_r
  have h_log := Real.log_le_log h_exp_pos h_trans
  rwa [Real.log_exp] at h_log

lemma log_F_seq_succ {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j : ℕ) (hj : 1 ≤ j) :
    let k : ℝ := ((j + 1 : ℕ) : ℝ)
    let ℓ₁ := Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)
    Real.log (F_seq η h j) ≤ 100 * k + (4 * k + 2) * k + k * ℓ₁ + k / η := by
  intro k ℓ₁
  dsimp [F_seq]
  have hj0 : ¬ j = 0 := by omega
  simp only [hj0, ↓reduceIte]
  have hk_pos : 0 < k := by
    dsimp [k]
    have : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < j + 1)
    exact this
  have h100 : (0 : ℝ) < 100 ^ (j + 1) := by positivity
  have hk_pow : (0 : ℝ) < k ^ (4 * (j + 1) + 2) := by positivity
  have hℓ : (0 : ℝ) < ℓ₁ ^ (j + 1) := by positivity
  have h_div : 100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1) / η ^ (j + 1) =
      100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1) * (1 / η) ^ (j + 1) := by
    rw [one_div_pow]
    ring
  rw [h_div]
  have hinv_pos : 0 < 1 / η := by positivity
  have h1 : 0 < 100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) := by positivity
  have h2' : 0 < 100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1) := by positivity
  rw [Real.log_mul h2'.ne' (pow_ne_zero (j + 1) hinv_pos.ne')]
  rw [Real.log_mul h1.ne' (pow_ne_zero (j + 1) (by linarith : 0 < ℓ₁).ne')]
  rw [Real.log_mul (pow_ne_zero (j + 1) (by norm_num : (0:ℝ) < 100).ne') (pow_ne_zero (4 * (j + 1) + 2) hk_pos.ne')]
  rw [Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  have l100 : Real.log 100 ≤ 100 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have lk : Real.log k ≤ k := (Real.log_le_sub_one_of_pos hk_pos).trans (by linarith)
  have lℓ : Real.log ℓ₁ ≤ ℓ₁ := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have linv : Real.log (1 / η) ≤ 1 / η := (Real.log_le_sub_one_of_pos hinv_pos).trans (by linarith)
  have h_cast1 : (((j + 1 : ℕ) : ℝ)) = k := rfl
  have h_cast2 : (((4 * (j + 1) + 2 : ℕ) : ℝ)) = 4 * k + 2 := by
    dsimp [k]
    push_cast
    ring
  rw [h_cast1, h_cast2]
  have h_div2 : k * (1 / η) = k / η := mul_one_div k η
  have m1 : k * Real.log 100 ≤ 100 * k := by
    have := mul_le_mul_of_nonneg_left l100 hk_pos.le
    linarith
  have m2 : (4 * k + 2) * Real.log k ≤ (4 * k + 2) * k := by
    have : 0 ≤ 4 * k + 2 := by positivity
    exact mul_le_mul_of_nonneg_left lk this
  have m3 : k * Real.log ℓ₁ ≤ k * ℓ₁ := mul_le_mul_of_nonneg_left lℓ hk_pos.le
  have m4 : k * Real.log (1 / η) ≤ k / η := by
    have := mul_le_mul_of_nonneg_left linv hk_pos.le
    rwa [h_div2] at this
  linarith

lemma cond2_succ_algebra (k : ℝ) (hk : 3 ≤ k) (ℓ₁ : ℝ) (hℓ₁ : 1 ≤ ℓ₁) (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) :
    (4 * k ^ 2 / η) * (100 * k + (4 * k + 2) * k + k * ℓ₁ + k / η) + 1 ≤
      100 ^ 2 * (k - 1) ^ 4 * ℓ₁ / η ^ 2 := by
  have hk_pos : 0 < k := by linarith
  have h_eta_inv : 1 ≤ 1 / η := by
    have : η < 1 := by linarith
    have := one_lt_one_div hη0 this
    linarith
  have h_k2 : k ≤ k ^ 2 := by nlinarith
  have h1 : 100 * k ≤ 100 * k ^ 2 * ℓ₁ / η := by
    have hk2 : 100 * k ≤ 100 * k ^ 2 := by nlinarith
    have hprod : 1 ≤ ℓ₁ * (1 / η) := by
      have := mul_le_mul hℓ₁ h_eta_inv (by linarith) (by linarith)
      linarith
    have h1' : 100 * k * 1 ≤ (100 * k ^ 2) * (ℓ₁ * (1 / η)) :=
      mul_le_mul hk2 hprod (by positivity) (by positivity)
    calc 100 * k
      _ = 100 * k * 1 := by ring
      _ ≤ (100 * k ^ 2) * (ℓ₁ * (1 / η)) := h1'
      _ = 100 * k ^ 2 * ℓ₁ / η := by ring
  have h2 : (4 * k + 2) * k ≤ 6 * k ^ 2 * ℓ₁ / η := by
    have h6 : 4 * k + 2 ≤ 6 * k := by linarith
    have hk2 : (4 * k + 2) * k ≤ 6 * k ^ 2 := by nlinarith
    have hprod : 1 ≤ ℓ₁ * (1 / η) := by
      have := mul_le_mul hℓ₁ h_eta_inv (by linarith) (by linarith)
      linarith
    have h2' : (4 * k + 2) * k * 1 ≤ (6 * k ^ 2) * (ℓ₁ * (1 / η)) :=
      mul_le_mul hk2 hprod (by positivity) (by positivity)
    calc (4 * k + 2) * k
      _ = (4 * k + 2) * k * 1 := by ring
      _ ≤ (6 * k ^ 2) * (ℓ₁ * (1 / η)) := h2'
      _ = 6 * k ^ 2 * ℓ₁ / η := by ring
  have h3 : k * ℓ₁ ≤ 1 * k ^ 2 * ℓ₁ / η := by
    have hk2 : k ≤ k ^ 2 := by nlinarith
    have h_prod : k * ℓ₁ ≤ k ^ 2 * ℓ₁ := mul_le_mul_of_nonneg_right hk2 (by linarith)
    have h3' : (k * ℓ₁) * 1 ≤ (k ^ 2 * ℓ₁) * (1 / η) :=
      mul_le_mul h_prod h_eta_inv (by positivity) (by positivity)
    calc k * ℓ₁
      _ = (k * ℓ₁) * 1 := by ring
      _ ≤ (k ^ 2 * ℓ₁) * (1 / η) := h3'
      _ = 1 * k ^ 2 * ℓ₁ / η := by ring
  have h4 : k / η ≤ 1 * k ^ 2 * ℓ₁ / η := by
    have hk2 : k ≤ k ^ 2 := by nlinarith
    have h_prod : k * 1 ≤ k ^ 2 * ℓ₁ := mul_le_mul hk2 hℓ₁ (by linarith) (by positivity)
    have : 0 ≤ 1 / η := by positivity
    have h4' : (k * 1) * (1 / η) ≤ (k ^ 2 * ℓ₁) * (1 / η) :=
      mul_le_mul_of_nonneg_right h_prod this
    calc k / η
      _ = (k * 1) * (1 / η) := by ring
      _ ≤ (k ^ 2 * ℓ₁) * (1 / η) := h4'
      _ = 1 * k ^ 2 * ℓ₁ / η := by ring
  have h_paren : 100 * k + (4 * k + 2) * k + k * ℓ₁ + k / η ≤ 108 * k ^ 2 * ℓ₁ / η := by
    have : 100 * k + (4 * k + 2) * k + k * ℓ₁ + k / η ≤
        100 * k ^ 2 * ℓ₁ / η + 6 * k ^ 2 * ℓ₁ / η + 1 * k ^ 2 * ℓ₁ / η + 1 * k ^ 2 * ℓ₁ / η := by linarith
    have h_ring : 100 * k ^ 2 * ℓ₁ / η + 6 * k ^ 2 * ℓ₁ / η + 1 * k ^ 2 * ℓ₁ / η + 1 * k ^ 2 * ℓ₁ / η =
        108 * k ^ 2 * ℓ₁ / η := by ring
    linarith
  have h_prod : (4 * k ^ 2 / η) * (100 * k + (4 * k + 2) * k + k * ℓ₁ + k / η) ≤
      432 * k ^ 4 * ℓ₁ / η ^ 2 := by
    have h_coeff : 0 ≤ 4 * k ^ 2 / η := by positivity
    have := mul_le_mul_of_nonneg_left h_paren h_coeff
    calc (4 * k ^ 2 / η) * (100 * k + (4 * k + 2) * k + k * ℓ₁ + k / η)
      _ ≤ (4 * k ^ 2 / η) * (108 * k ^ 2 * ℓ₁ / η) := this
      _ = 432 * k ^ 4 * ℓ₁ / η ^ 2 := by ring
  have hk4 : (81 : ℝ) ≤ k ^ 4 := by
    have h3 : (3 : ℝ) ^ 4 ≤ k ^ 4 := pow_le_pow_left₀ (by norm_num) hk 4
    have : (3 : ℝ) ^ 4 = 81 := by norm_num
    rwa [this] at h3
  have h_eta2 : (36 : ℝ) ≤ 1 / η ^ 2 := by
    have h6 : (6 : ℝ) ≤ 1 / η := by
      have := one_div_le_one_div_of_le hη0 hη.le
      linarith
    have h36 : (6 : ℝ) ^ 2 ≤ (1 / η) ^ 2 := pow_le_pow_left₀ (by norm_num) h6 2
    rw [one_div_pow] at h36
    have : (6 : ℝ) ^ 2 = 36 := by norm_num
    rwa [this] at h36
  have h_one : (1 : ℝ) ≤ 193 * k ^ 4 * ℓ₁ / η ^ 2 := by
    have hA : (1 : ℝ) ≤ 193 := by norm_num
    have hB : (1 : ℝ) ≤ 81 * 1 * 36 := by norm_num
    have hC : 81 * 1 * 36 ≤ k ^ 4 * ℓ₁ * (1 / η ^ 2) := by
      have h1 : 81 * 1 ≤ k ^ 4 * ℓ₁ := mul_le_mul hk4 hℓ₁ (by norm_num) (by positivity)
      exact mul_le_mul h1 h_eta2 (by norm_num) (by positivity)
    have : (1 : ℝ) ≤ 193 * (k ^ 4 * ℓ₁ * (1 / η ^ 2)) := by
      have : (1 : ℝ) ≤ 193 * (81 * 1 * 36) := by norm_num
      have h_mul := mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 193)
      linarith
    calc (1 : ℝ)
      _ ≤ 193 * (k ^ 4 * ℓ₁ * (1 / η ^ 2)) := this
      _ = 193 * k ^ 4 * ℓ₁ / η ^ 2 := by ring
  have h_sum : (4 * k ^ 2 / η) * (100 * k + (4 * k + 2) * k + k * ℓ₁ + k / η) + 1 ≤
      625 * k ^ 4 * ℓ₁ / η ^ 2 := by
    calc (4 * k ^ 2 / η) * (100 * k + (4 * k + 2) * k + k * ℓ₁ + k / η) + 1
      _ ≤ 432 * k ^ 4 * ℓ₁ / η ^ 2 + 193 * k ^ 4 * ℓ₁ / η ^ 2 := by linarith
      _ = 625 * k ^ 4 * ℓ₁ / η ^ 2 := by ring
  have h_k_sub : k ≤ 2 * (k - 1) := by linarith
  have h_k4_le : k ^ 4 ≤ 16 * (k - 1) ^ 4 := by
    have : 0 ≤ k - 1 := by linarith
    have h2 : k ^ 4 ≤ (2 * (k - 1)) ^ 4 := pow_le_pow_left₀ hk_pos.le h_k_sub 4
    have h_pow : (2 * (k - 1)) ^ 4 = 16 * (k - 1) ^ 4 := by ring
    rwa [h_pow] at h2
  have h625 : 625 * k ^ 4 ≤ 10000 * (k - 1) ^ 4 := by
    calc 625 * k ^ 4
      _ ≤ 625 * (16 * (k - 1) ^ 4) := by nlinarith
      _ = 10000 * (k - 1) ^ 4 := by ring
  have h_pow_100 : 10000 * (k - 1) ^ 4 ≤ 100 ^ 2 * (k - 1) ^ 4 := by
    have : (10000 : ℝ) = 100 ^ 2 := by norm_num
    rw [this]
  have h_rhs_step : 625 * k ^ 4 * ℓ₁ / η ^ 2 ≤ 100 ^ 2 * (k - 1) ^ 4 * ℓ₁ / η ^ 2 := by
    have : 0 ≤ ℓ₁ / η ^ 2 := by positivity
    have h_le : 625 * k ^ 4 ≤ 100 ^ 2 * (k - 1) ^ 4 := h625.trans h_pow_100
    have := mul_le_mul_of_nonneg_right h_le this
    calc 625 * k ^ 4 * ℓ₁ / η ^ 2
      _ = (625 * k ^ 4) * (ℓ₁ / η ^ 2) := by ring
      _ ≤ (100 ^ 2 * (k - 1) ^ 4) * (ℓ₁ / η ^ 2) := this
      _ = 100 ^ 2 * (k - 1) ^ 4 * ℓ₁ / η ^ 2 := by ring
  have h_goal : (4 * k ^ 2 / η) * (100 * k + (4 * k + 2) * k + k * ℓ₁ + k / η) + 1 ≤
      100 ^ 2 * (k - 1) ^ 4 * ℓ₁ / η ^ 2 := h_sum.trans h_rhs_step
  exact h_goal

lemma bound_Ei (i : ℕ) (hi : 1 ≤ i) (ℓ₁ : ℝ) (hℓ₁ : 1 ≤ ℓ₁) (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) :
    let ki : ℝ := ((i + 1 : ℕ) : ℝ)
    100 ^ 2 * ki ^ 4 * ℓ₁ / η ^ 2 ≤
      100 ^ (i + 1) * ki ^ (4 * (i + 1)) * ℓ₁ ^ i / η ^ (i + 1) := by
  intro ki
  have hki_ge : (2 : ℝ) ≤ ki := by
    dsimp [ki]
    have : (2 : ℕ) ≤ i + 1 := by omega
    exact_mod_cast this
  have hki_pos : 0 < ki := by linarith
  have h100 : (100 : ℝ) ^ 2 ≤ 100 ^ (i + 1) := by
    apply pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ i + 1)
  have hki_pow : ki ^ 4 ≤ ki ^ (4 * (i + 1)) := by
    apply pow_le_pow_right₀ (by linarith) (by omega : 4 ≤ 4 * (i + 1))
  have hℓ : ℓ₁ ≤ ℓ₁ ^ i := by
    simpa using pow_le_pow_right₀ hℓ₁ hi
  have h_div : 1 / η ^ 2 ≤ 1 / η ^ (i + 1) := by
    rw [← one_div_pow, ← one_div_pow]
    have h_inv : (1 : ℝ) ≤ 1 / η := by
      have : η < 1 := by linarith
      have := one_lt_one_div hη0 this
      linarith
    apply pow_le_pow_right₀ h_inv (by omega : 2 ≤ i + 1)
  have h_num1 : 100 ^ 2 * ki ^ 4 ≤ 100 ^ (i + 1) * ki ^ (4 * (i + 1)) :=
    mul_le_mul h100 hki_pow (by positivity) (by positivity)
  have h_num2 : 100 ^ 2 * ki ^ 4 * ℓ₁ ≤ 100 ^ (i + 1) * ki ^ (4 * (i + 1)) * ℓ₁ ^ i :=
    mul_le_mul h_num1 hℓ (by linarith) (by positivity)
  have : 0 ≤ 1 / η ^ 2 := by positivity
  have h_prod : (100 ^ 2 * ki ^ 4 * ℓ₁) * (1 / η ^ 2) ≤
      (100 ^ (i + 1) * ki ^ (4 * (i + 1)) * ℓ₁ ^ i) * (1 / η ^ (i + 1)) :=
    mul_le_mul h_num2 h_div this (by positivity)
  calc 100 ^ 2 * ki ^ 4 * ℓ₁ / η ^ 2
    _ = (100 ^ 2 * ki ^ 4 * ℓ₁) * (1 / η ^ 2) := by ring
    _ ≤ (100 ^ (i + 1) * ki ^ (4 * (i + 1)) * ℓ₁ ^ i) * (1 / η ^ (i + 1)) := h_prod
    _ = 100 ^ (i + 1) * ki ^ (4 * (i + 1)) * ℓ₁ ^ i / η ^ (i + 1) := by ring

lemma cond2_succ {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (i : ℕ) (hi : 1 ≤ i) :
    let j := i + 1
    (4 * ((j + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (F_seq η h j) + 1 ≤ E_seq η h i := by
  intro j
  set k : ℝ := ((j + 1 : ℕ) : ℝ)
  set ℓ₁ := Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)
  have hj_pos : 1 ≤ j := by omega
  have h_logF := log_F_seq_succ hη0 hη h h_ℓ₁ j hj_pos
  have hk_ge : 3 ≤ k := by
    dsimp [k, j]
    have : (3 : ℕ) ≤ i + 1 + 1 := by omega
    exact_mod_cast this
  have h_alg := cond2_succ_algebra k hk_ge ℓ₁ h_ℓ₁ η hη0 hη
  have h_coeff : 0 ≤ 4 * k ^ 2 / η := by positivity
  have h_step1 : (4 * k ^ 2 / η) * Real.log (F_seq η h j) + 1 ≤
      (4 * k ^ 2 / η) * (100 * k + (4 * k + 2) * k + k * ℓ₁ + k / η) + 1 := by
    have := mul_le_mul_of_nonneg_left h_logF h_coeff
    linarith
  have h_step2 := h_step1.trans h_alg
  have h_k_sub : k - 1 = ((i + 1 : ℕ) : ℝ) := by
    dsimp [k, j]
    push_cast
    ring
  rw [h_k_sub] at h_step2
  have h_bound := bound_Ei i hi ℓ₁ h_ℓ₁ η hη0 hη
  have h_trans := h_step2.trans h_bound
  dsimp [E_seq]
  have hi0 : ¬ i = 0 := by omega
  simp only [hi0, ↓reduceIte]
  exact h_trans

lemma two_le_E_seq {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_logL : 4 + 1 / η ≤ Real.log (Real.log (h : ℝ)))
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (i : ℕ) : 2 ≤ E_seq η h i := by
  by_cases hi : i = 0
  · subst hi
    dsimp [E_seq, kappa]
    have h_eta_lt : η * (1 / 6 - η) < η * (1 / 6) := by
      have : 1 / 6 - η < 1 / 6 := by linarith
      exact mul_lt_mul_of_pos_left this hη0
    have h_eta_lt' : η * (1 / 6 - η) < η / 6 := by
      have : η * (1 / 6) = η / 6 := by ring
      rwa [this] at h_eta_lt
    have h_denom_pos : 0 < η * (1 / 6 - η) := by
      have : 0 < 1 / 6 - η := by linarith
      positivity
    have h_kappa : 1200 / η < 200 / (η * (1 / 6 - η)) := by
      have h_div : 1200 / η = 200 / (η / 6) := by ring
      rw [h_div]
      exact div_lt_div_of_pos_left (by norm_num) (by positivity) h_eta_lt'
    have h_logL_ge : 4 ≤ Real.log (Real.log (h : ℝ)) := by
      have : 0 < 1 / η := by positivity
      linarith
    have h_logL_pos : 0 ≤ Real.log (Real.log (h : ℝ)) := by linarith
    have h1200 : (2 : ℝ) ≤ (1200 / η) * 4 := by
      have : (6 : ℝ) ≤ 1 / η := by
        have := one_div_le_one_div_of_le hη0 hη.le
        have h_num : (1 : ℝ) / (1 / 6) = 6 := by norm_num
        rwa [h_num] at this
      have : (7200 : ℝ) ≤ 1200 / η := by
        calc (7200 : ℝ)
          _ = 1200 * 6 := by norm_num
          _ ≤ 1200 * (1 / η) := mul_le_mul_of_nonneg_left this (by norm_num)
          _ = 1200 / η := by ring
      linarith
    have h_prod1 : (1200 / η) * 4 ≤ (1200 / η) * Real.log (Real.log (h : ℝ)) :=
      mul_le_mul_of_nonneg_left h_logL_ge (by positivity)
    have h_prod2 : (1200 / η) * Real.log (Real.log (h : ℝ)) ≤ (200 / (η * (1 / 6 - η))) * Real.log (Real.log (h : ℝ)) :=
      mul_le_mul_of_nonneg_right h_kappa.le h_logL_pos
    linarith
  · have hi_pos : 1 ≤ i := by omega
    have := one_le_E_seq_succ hη0 hη h h_ℓ₁ i hi_pos
    dsimp [E_seq]
    simp only [hi, ↓reduceIte]
    have h100 : (10000 : ℝ) ≤ 100 ^ (i + 1) := by
      have : (100 : ℝ) ^ 2 ≤ 100 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega : 2 ≤ i + 1)
      linarith
    have hk : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) ^ (4 * (i + 1)) := by
      have : (1 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ i + 1)
      exact one_le_pow₀ this
    have hℓ : (1 : ℝ) ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) ^ i :=
      one_le_pow₀ h_ℓ₁
    have h_denom : η ^ (i + 1) ≤ 1 := pow_le_one₀ hη0.le (by linarith)
    have h_denom_pos : 0 < η ^ (i + 1) := by positivity
    have h_num : (2 : ℝ) ≤ 100 ^ (i + 1) * ((i + 1 : ℕ) : ℝ) ^ (4 * (i + 1)) *
        Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) ^ i := by
      have : (2 : ℝ) ≤ 10000 * 1 * 1 := by norm_num
      have h1 : 10000 * 1 ≤ 100 ^ (i + 1) * ((i + 1 : ℕ) : ℝ) ^ (4 * (i + 1)) :=
        mul_le_mul h100 hk (by norm_num) (by positivity)
      have h2 : 10000 * 1 * 1 ≤ 100 ^ (i + 1) * ((i + 1 : ℕ) : ℝ) ^ (4 * (i + 1)) *
          Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) ^ i :=
        mul_le_mul h1 hℓ (by norm_num) (by positivity)
      linarith
    have h_div_le : (2 : ℝ) ≤ (100 ^ (i + 1) * ((i + 1 : ℕ) : ℝ) ^ (4 * (i + 1)) *
        Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) ^ i) / η ^ (i + 1) := by
      have h_step : (2 : ℝ) * η ^ (i + 1) ≤ 100 ^ (i + 1) * ((i + 1 : ℕ) : ℝ) ^ (4 * (i + 1)) *
          Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) ^ i := by
        calc (2 : ℝ) * η ^ (i + 1)
          _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left h_denom (by norm_num)
          _ = 2 := by ring
          _ ≤ 100 ^ (i + 1) * ((i + 1 : ℕ) : ℝ) ^ (4 * (i + 1)) *
              Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) ^ i := h_num
      exact (le_div_iff₀ h_denom_pos).mpr h_step
    exact h_div_le

lemma log_F_seq_one {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) :
    let ℓ₁ := Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)
    Real.log (F_seq η h 1) ≤ 220 + 2 * Real.log ℓ₁ + 2 / η := by
  intro ℓ₁
  dsimp [F_seq]
  have h100 : (0 : ℝ) < 100 ^ 2 := by positivity
  have h2 : (0 : ℝ) < (2 : ℝ) ^ 10 := by positivity
  have hℓ : (0 : ℝ) < ℓ₁ ^ 2 := by positivity
  have h_div : 100 ^ 2 * (2 : ℝ) ^ 10 * ℓ₁ ^ 2 / η ^ 2 =
      100 ^ 2 * (2 : ℝ) ^ 10 * ℓ₁ ^ 2 * (1 / η) ^ 2 := by
    rw [one_div_pow]
    ring
  rw [h_div]

  have hinv_pos : 0 < 1 / η := by positivity
  have h1 : 0 < 100 ^ 2 * (2 : ℝ) ^ 10 := by positivity
  have h2' : 0 < 100 ^ 2 * (2 : ℝ) ^ 10 * ℓ₁ ^ 2 := by positivity
  rw [Real.log_mul h2'.ne' (pow_ne_zero 2 hinv_pos.ne')]
  rw [Real.log_mul h1.ne' (pow_ne_zero 2 (by linarith : 0 < ℓ₁).ne')]
  rw [Real.log_mul (pow_ne_zero 2 (by norm_num : (0:ℝ) < 100).ne') (pow_ne_zero 10 (by norm_num : (0:ℝ) < 2).ne')]
  rw [Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  have l100 : Real.log 100 ≤ 100 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have l2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have linv : Real.log (1 / η) ≤ 1 / η := (Real.log_le_sub_one_of_pos hinv_pos).trans (by linarith)
  have h_div2 : (2 : ℝ) * (1 / η) = 2 / η := mul_one_div 2 η
  linarith

lemma cond2_base_algebra (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) (L : ℝ) (hL : 4 + 1 / η ≤ Real.log L) :
    (16 / η) * (220 + 2 * Real.log L + 2 / η) + 1 ≤ (200 / (η * (1 / 6 - η))) * Real.log L := by
  have h_eta_lt : η * (1 / 6 - η) < η * (1 / 6) := by
    have : 1 / 6 - η < 1 / 6 := by linarith
    exact mul_lt_mul_of_pos_left this hη0
  have h_eta_lt' : η * (1 / 6 - η) < η / 6 := by
    have : η * (1 / 6) = η / 6 := by ring
    rwa [this] at h_eta_lt
  have h_denom_pos : 0 < η * (1 / 6 - η) := by
    have : 0 < 1 / 6 - η := by linarith
    positivity
  have h_kappa : 1200 / η < 200 / (η * (1 / 6 - η)) := by
    have h_div : 1200 / η = 200 / (η / 6) := by ring
    rw [h_div]
    exact div_lt_div_of_pos_left (by norm_num) (by positivity) h_eta_lt'
  have h_logL_pos : 0 < Real.log L := by
    have : 0 < 4 + 1 / η := by positivity
    linarith
  have h_E0_step : (1200 / η) * Real.log L ≤ (200 / (η * (1 / 6 - η))) * Real.log L :=
    mul_le_mul_of_nonneg_right h_kappa.le h_logL_pos.le
  have h_diff : (16 / η) * (220 + 2 * Real.log L + 2 / η) + 1 ≤ (1200 / η) * Real.log L := by
    have h1 : 4 ≤ Real.log L := by
      have : 0 < 1 / η := by positivity
      linarith
    have h2 : 1 / η ≤ Real.log L := by linarith
    have h_eta_le : η ≤ 1 / 6 := hη.le
    have h_32 : 32 / η ≤ 32 * Real.log L := by
      have h_div : 32 / η = 32 * (1 / η) := by ring
      rw [h_div]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have h_poly : 3520 + 32 / η + η ≤ 1168 * Real.log L := by
      calc 3520 + 32 / η + η
        _ ≤ 3520 + 32 * Real.log L + 1 / 6 := by linarith [h_32, h_eta_le]
        _ = 3520 + 1 / 6 + 32 * Real.log L := by ring
        _ ≤ 1000 * 4 + 32 * Real.log L := by linarith
        _ ≤ 1000 * Real.log L + 32 * Real.log L := by linarith [h1]
        _ = 1032 * Real.log L := by ring
        _ ≤ 1168 * Real.log L := by linarith
    have h_div_eta : (3520 + 32 / η + η) / η ≤ (1168 * Real.log L) / η :=
      div_le_div_of_nonneg_right h_poly hη0.le
    have h_lhs_eq : (16 / η) * (220 + 2 * Real.log L + 2 / η) + 1 =
        (3520 + 32 / η + η) / η + (32 / η) * Real.log L := by
      have h_ring1 : (16 / η) * (220 + 2 * Real.log L + 2 / η) + 1 =
          (3520 + 32 * Real.log L + 32 / η + η) / η := by
        have : 1 = η / η := (div_self hη0.ne').symm
        rw [this]
        ring
      have h_ring2 : (3520 + 32 / η + η) / η + (32 / η) * Real.log L =
          (3520 + 32 * Real.log L + 32 / η + η) / η := by ring
      rw [h_ring1, h_ring2]
    rw [h_lhs_eq]
    have h_rhs_eq : (1200 / η) * Real.log L = (1168 * Real.log L) / η + (32 / η) * Real.log L := by ring
    rw [h_rhs_eq]
    linarith
  linarith

lemma cond2_base {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ) (h16 : 16 ≤ h)
    (h_logL : 4 + 1 / η ≤ Real.log (Real.log (h : ℝ)))
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) :
    (16 / η) * Real.log (F_seq η h 1) + 1 ≤ E_seq η h 0 := by
  set L := Real.log (h : ℝ)
  set ℓ₁ := Real.log (⌊Real.exp (L / Real.log L)⌋₊ : ℝ)
  have h_log_F1 := log_F_seq_one hη0 hη h h_ℓ₁
  have hQ0_le := Q_zero_le_h η h h16
  have h_pos : 0 < (⌊Real.exp (L / Real.log L)⌋₊ : ℝ) := by
    have h16_r : (16 : ℝ) ≤ (h : ℝ) := by exact_mod_cast h16
    have hlogh : 0 < L := by
      have h16_pos : (1 : ℝ) < 16 := by norm_num
      have := Real.log_pos h16_pos
      have hle := Real.log_le_log (by norm_num) h16_r
      linarith
    have hlog_log : 0 ≤ Real.log L := by
      have h4 : 4 ≤ Real.log L := by
        have : 0 < 1 / η := by positivity
        linarith
      linarith
    have hdiv_nonneg : 0 ≤ L / Real.log L := div_nonneg hlogh.le hlog_log
    have h_exp_ge1 : 1 ≤ Real.exp (L / Real.log L) := Real.one_le_exp hdiv_nonneg
    exact Nat.cast_pos.mpr ((Nat.one_le_floor_iff _).mpr h_exp_ge1)
  have h_ℓ₁_le : ℓ₁ ≤ L := Real.log_le_log h_pos hQ0_le

  have h_log_ℓ₁_le : Real.log ℓ₁ ≤ Real.log L := by
    have : 0 < ℓ₁ := by linarith
    exact Real.log_le_log this h_ℓ₁_le
  have h_step : Real.log (F_seq η h 1) ≤ 220 + 2 * Real.log L + 2 / η := by
    calc Real.log (F_seq η h 1)
      _ ≤ 220 + 2 * Real.log ℓ₁ + 2 / η := h_log_F1
      _ ≤ 220 + 2 * Real.log L + 2 / η := by linarith
  have h_coeff : 0 ≤ 16 / η := by positivity
  have h_mul := mul_le_mul_of_nonneg_left h_step h_coeff
  have h_alg := cond2_base_algebra η hη0 hη L h_logL
  dsimp [E_seq, kappa]
  linarith

lemma div_le_of_inv_mul_le {A B C : ℝ} (hB : 0 < B) (hC : 0 < C)
    (h_le : (1 / C) * A ≤ B) : A / B ≤ C := by
  have h_mul : A ≤ C * B := by
    calc A
      _ = C * ((1 / C) * A) := by
        rw [← mul_assoc, mul_one_div_cancel hC.ne', one_mul]
      _ ≤ C * B := mul_le_mul_of_nonneg_left h_le hC.le
  exact (div_le_iff₀ hB).mpr h_mul

lemma div_le_of_nonpos {A B C : ℝ} (hB : 0 < B) (hC : 0 ≤ C) (hA : A ≤ 0) :
    A / B ≤ C := by
  have : A / B ≤ 0 := div_nonpos_of_nonpos_of_nonneg hA hB.le
  linarith

lemma two_le_Q_seq_succ {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j : ℕ) (hj : 1 ≤ j) : 2 ≤ Q_seq η h j := by
  dsimp [Q_seq]
  have hj_pos : 1 ≤ j := hj
  have h_F := F_seq_eq_mul_E_seq η h j hj_pos
  have h_E_ge := one_le_E_seq_succ hη0 hη h h_ℓ₁ j hj_pos
  have h_mul : 1 ≤ F_seq η h j := by
    rw [h_F]
    have hj2 : (4 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ j + 1)
      nlinarith
    have h_prod : 1 ≤ ((j + 1 : ℕ) : ℝ) ^ 2 * Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) := by
      have := mul_le_mul hj2 h_ℓ₁ (by positivity) (by positivity)
      linarith
    have := mul_le_mul h_prod h_E_ge (by positivity) (by positivity)
    linarith
  have h_exp : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h_mono : Real.exp 1 ≤ Real.exp (F_seq η h j) := Real.exp_le_exp.mpr h_mul
  have h2 : (2 : ℝ) ≤ Real.exp (F_seq η h j) := h_exp.trans h_mono
  exact Nat.le_floor h2

lemma cond2_seq {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ) (h16 : 16 ≤ h)
    (h_logL : 4 + 1 / η ≤ Real.log (Real.log (h : ℝ)))
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j i : ℕ) (hij : i + 1 = j) :
    Real.log (Real.log (Q_seq η h j : ℝ)) / (Real.log (P_seq η h i : ℝ) - 1) ≤
      η / (4 * ((j + 1 : ℕ) : ℝ) ^ 2) := by
  set A := Real.log (Real.log (Q_seq η h j : ℝ))
  set B := Real.log (P_seq η h i : ℝ) - 1
  set C := η / (4 * ((j + 1 : ℕ) : ℝ) ^ 2)
  have hC_pos : 0 < C := by positivity
  have hP := log_P_seq_ge η h i
  have hE_two := two_le_E_seq hη0 hη h h_logL h_ℓ₁ i
  have hB_pos : 0 < B := by
    dsimp [B]
    linarith [hE_two, hP]
  by_cases hA : A ≤ 0
  · exact div_le_of_nonpos hB_pos hC_pos.le hA
  · have hA_pos : 0 < A := not_le.mp hA
    have hF_pos : 0 ≤ F_seq η h j := by
      by_cases hj : j = 0
      · subst hj
        omega
      · dsimp [F_seq]
        simp only [hj, ↓reduceIte]
        positivity
    have hQ_le := log_Q_seq_le η h j hF_pos
    have hj_ge1 : 1 ≤ j := by omega
    have h2_Q := two_le_Q_seq_succ hη0 hη h h_ℓ₁ j hj_ge1
    have h_logQ_pos : 0 < Real.log (Q_seq η h j : ℝ) := by
      have : (1 : ℝ) < (Q_seq η h j : ℝ) := by
        have : (2 : ℝ) ≤ (Q_seq η h j : ℝ) := by exact_mod_cast h2_Q
        linarith
      exact Real.log_pos this
    have h_log_logQ_le : A ≤ Real.log (F_seq η h j) := Real.log_le_log h_logQ_pos hQ_le
    have h_invC : 1 / C = 4 * ((j + 1 : ℕ) : ℝ) ^ 2 / η := by
      dsimp [C]
      rw [one_div_div]
    have h_inv_F : (1 / C) * Real.log (F_seq η h j) ≤ B := by
      rw [h_invC]
      by_cases hi : i = 0
      · subst hi
        have hj1 : j = 1 := by omega
        subst hj1
        have h_base := cond2_base hη0 hη h h16 h_logL h_ℓ₁
        have : (16 / η) * Real.log (F_seq η h 1) ≤ Real.log (P_seq η h 0 : ℝ) - 1 := by linarith [h_base, hP]
        have h16_eq : 4 * ((1 + 1 : ℕ) : ℝ) ^ 2 / η = 16 / η := by ring
        rwa [h16_eq]
      · have hi_pos : 1 ≤ i := by omega
        subst hij
        have h_succ := cond2_succ hη0 hη h h_ℓ₁ i hi_pos
        have : (4 * ((i + 1 + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (F_seq η h (i + 1)) ≤
            Real.log (P_seq η h i : ℝ) - 1 := by linarith [h_succ, hP]
        exact this
    have h_inv_A : (1 / C) * A ≤ B := by
      have h_coeff : 0 ≤ 1 / C := by positivity
      have := mul_le_mul_of_nonneg_left h_log_logQ_le h_coeff
      exact this.trans h_inv_F
    exact div_le_of_inv_mul_le hB_pos hC_pos h_inv_A




noncomputable def makeRangeSystem {η : ℝ} (h : ℕ) (J : ℕ)
    (h_two_P : ∀ j : Fin J, 2 ≤ P_seq η h j.val)
    (h_P_Q : ∀ j : Fin J, P_seq η h j.val ≤ Q_seq η h j.val)
    (h_c2 : ∀ (j i : Fin J), i.val + 1 = j.val → Real.log (Real.log (Q_seq η h j.val : ℝ)) / (Real.log (P_seq η h i.val : ℝ) - 1) ≤ η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2))
    (h_c3 : ∀ (j i : Fin J), i.val + 1 = j.val → (8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (Q_seq η h i.val : ℝ) + 16 * Real.log ((j.val + 1 : ℕ) : ℝ) ≤ Real.log (P_seq η h j.val : ℝ)) :
    RangeSystem J η where
  P := fun j => P_seq η h j.val
  Q := fun j => Q_seq η h j.val
  two_le_P := h_two_P
  P_le_Q := h_P_Q
  cond2 := h_c2
  cond3 := h_c3


lemma sum_telescope_ri (n : ℕ) :
    ∑ i : Fin n, (1 / ((i.val : ℝ) + 1) - 1 / ((i.val : ℝ) + 2)) = 1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h_last : ((Fin.last n).val : ℝ) = (n : ℝ) := by simp
    have h_cast : (fun i : Fin n => (1 / ((i.castSucc.val : ℝ) + 1) - 1 / ((i.castSucc.val : ℝ) + 2))) =
        (fun i : Fin n => (1 / ((i.val : ℝ) + 1) - 1 / ((i.val : ℝ) + 2))) := by
      ext i
      simp
    rw [h_last, h_cast, ih]
    push_cast
    ring

lemma sum_telescope_le_one (n : ℕ) :
    ∑ i : Fin n, (1 / ((i.val : ℝ) + 1) - 1 / ((i.val : ℝ) + 2)) ≤ 1 := by
  rw [sum_telescope_ri]
  have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  linarith

lemma sum_geom_two (n : ℕ) :
    ∑ i : Fin n, ((1 / 2 : ℝ) ^ (i.val + 1)) = 1 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h_last : ((Fin.last n).val : ℕ) = n := by simp
    have h_cast : (fun i : Fin n => ((1 / 2 : ℝ) ^ (i.castSucc.val + 1))) =
        (fun i : Fin n => ((1 / 2 : ℝ) ^ (i.val + 1))) := by
      ext i
      simp
    rw [h_last, h_cast, ih]
    ring

lemma sum_geom_two_le_one (n : ℕ) :
    ∑ i : Fin n, ((1 / 2 : ℝ) ^ (i.val + 1)) ≤ 1 := by
  rw [sum_geom_two]
  have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  linarith

lemma sum_split_Fin {n : ℕ} (f g : Fin (n + 1) → ℝ) (ε : ℝ)
    (h0 : f 0 + g 0 ≤ ε / 2)
    (hf : ∑ i : Fin n, f i.succ ≤ ε / 4)
    (hg : ∑ i : Fin n, g i.succ ≤ ε / 4) :
    (∑ i : Fin (n + 1), (f i + g i)) ≤ ε := by
  rw [Finset.sum_add_distrib, Fin.sum_univ_succ, Fin.sum_univ_succ]
  linarith


noncomputable def rangeJSet (η : ℝ) (h : ℕ) (X : ℕ) : Finset ℕ :=
  let M := ⌊Real.exp (Real.sqrt (Real.log (X : ℝ)))⌋₊ + 3
  (Finset.range M).filter (fun j => 1 ≤ j ∧ (Q_seq η h (j - 1) : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))))

lemma rangeJSet_nonempty {η : ℝ} (h : ℕ) (X : ℕ)
    (h_Q0 : (Q_seq η h 0 : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ)))) :
    (rangeJSet η h X).Nonempty := by
  use 1
  dsimp [rangeJSet]
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨?_, by omega, h_Q0⟩
  omega

noncomputable def J_val (η : ℝ) (h : ℕ) (X : ℕ)
    (h_Q0 : (Q_seq η h 0 : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ)))) : ℕ :=
  (rangeJSet η h X).max' (rangeJSet_nonempty h X h_Q0)

lemma J_val_ge_one {η : ℝ} (h : ℕ) (X : ℕ)
    (h_Q0 : (Q_seq η h 0 : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ)))) :
    1 ≤ J_val η h X h_Q0 := by
  have h_mem := Finset.max'_mem (rangeJSet η h X) (rangeJSet_nonempty h X h_Q0)
  dsimp [rangeJSet] at h_mem
  rw [Finset.mem_filter] at h_mem
  exact h_mem.2.1

lemma J_val_pos {η : ℝ} (h : ℕ) (X : ℕ)
    (h_Q0 : (Q_seq η h 0 : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ)))) :
    0 < J_val η h X h_Q0 := by
  have := J_val_ge_one h X h_Q0
  omega

lemma Q_J_sub_one_le {η : ℝ} (h : ℕ) (X : ℕ)
    (h_Q0 : (Q_seq η h 0 : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ)))) :
    (Q_seq η h (J_val η h X h_Q0 - 1) : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) := by
  have h_mem := Finset.max'_mem (rangeJSet η h X) (rangeJSet_nonempty h X h_Q0)
  dsimp [rangeJSet] at h_mem
  rw [Finset.mem_filter] at h_mem
  exact h_mem.2.2

lemma log_log_ge_of_ge_ceil_exp_exp (C : ℝ) (h : ℕ) (hh : ⌈Real.exp (Real.exp C)⌉₊ ≤ h) :
    C ≤ Real.log (Real.log (h : ℝ)) := by
  have h1 : Real.exp C ≤ Real.log (h : ℝ) := log_ge_of_ge_ceil_exp (Real.exp C) h hh
  have h_exp_pos : 0 < Real.exp C := Real.exp_pos C
  have h_log := Real.log_le_log h_exp_pos h1
  rwa [Real.log_exp] at h_log

lemma exp_div_ge (u : ℝ) (hu : 0 < u) : u / 4 ≤ Real.exp u / u := by
  have h1 : u / 2 ≤ Real.exp (u / 2) := by
    have := Real.add_one_le_exp (u / 2)
    linarith
  have h2 : (u / 2) ^ 2 ≤ (Real.exp (u / 2)) ^ 2 := by
    have : 0 ≤ u / 2 := by linarith
    nlinarith
  have h3 : (Real.exp (u / 2)) ^ 2 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h4 : u ^ 2 / 4 ≤ Real.exp u := by
    have : (u / 2) ^ 2 = u ^ 2 / 4 := by ring
    linarith [h2, h3]
  have h5 : (u ^ 2 / 4) / u ≤ Real.exp u / u := div_le_div_of_nonneg_right h4 hu.le
  have h6 : (u ^ 2 / 4) / u = u / 4 := by
    have : u ≠ 0 := by linarith
    field_simp
  rwa [h6] at h5

lemma log_floor_exp_ge (t : ℝ) (ht : 2 ≤ t) :
    t - 1 ≤ Real.log (⌊Real.exp t⌋₊ : ℝ) := by
  have he : 1 ≤ Real.exp 1 - 1 := by linarith [Real.exp_one_gt_d9]
  have ht1 : 1 ≤ t - 1 := by linarith
  have he_t : Real.exp 1 ≤ Real.exp (t - 1) := Real.exp_le_exp.mpr ht1
  have he2 : 1 ≤ Real.exp (t - 1) := by linarith [Real.exp_one_gt_d9]
  have h_diff : 1 ≤ (Real.exp 1 - 1) * Real.exp (t - 1) := by nlinarith
  have h_mul : Real.exp (t - 1) + 1 ≤ Real.exp 1 * Real.exp (t - 1) := by linarith
  have h_exp_add : Real.exp 1 * Real.exp (t - 1) = Real.exp t := by
    rw [← Real.exp_add]
    have : 1 + (t - 1) = t := by ring
    rw [this]
  have h_floor_ge : Real.exp (t - 1) ≤ (⌊Real.exp t⌋₊ : ℝ) := by
    have h_sub : Real.exp t - 1 < (⌊Real.exp t⌋₊ : ℝ) := Nat.sub_one_lt_floor (Real.exp t)
    linarith [h_mul, h_exp_add]
  have h_pos : 0 < Real.exp (t - 1) := Real.exp_pos _
  have h_log := Real.log_le_log h_pos h_floor_ge
  rwa [Real.log_exp] at h_log

lemma exp_div_ge_sq (u : ℝ) (hu : 0 < u) : u ^ 2 / 27 ≤ Real.exp u / u := by
  have h1 : u / 3 ≤ Real.exp (u / 3) := by
    have := Real.add_one_le_exp (u / 3)
    linarith
  have h2 : (u / 3) ^ 3 ≤ (Real.exp (u / 3)) ^ 3 := by
    have : 0 ≤ u / 3 := by linarith
    have hsq : (u / 3) ^ 2 ≤ (Real.exp (u / 3)) ^ 2 := by nlinarith
    nlinarith
  have h3 : (Real.exp (u / 3)) ^ 3 = Real.exp u := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have h4 : u ^ 3 / 27 ≤ Real.exp u := by
    have : (u / 3) ^ 3 = u ^ 3 / 27 := by ring
    linarith [h2, h3]
  have h5 : (u ^ 3 / 27) / u ≤ Real.exp u / u := div_le_div_of_nonneg_right h4 hu.le
  have h6 : (u ^ 3 / 27) / u = u ^ 2 / 27 := by
    have : u ≠ 0 := by linarith
    field_simp
  rwa [h6] at h5

lemma pos_of_one_le_log {x : ℕ} (h : 1 ≤ Real.log (x : ℝ)) : 0 < (x : ℝ) := by
  have : x ≠ 0 := by
    rintro rfl
    simp only [Nat.cast_zero, Real.log_zero] at h
    linarith
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero this)

lemma Q_seq_le_P_seq_succ {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j : ℕ) :
    Q_seq η h j ≤ P_seq η h (j + 1) := by
  cases j with
  | zero =>
    have h_cond := cond3_base hη0 hη h h_ℓ₁
    have h_P1 : E_seq η h 1 ≤ Real.log (P_seq η h 1 : ℝ) := log_P_seq_ge η h 1
    have h_Q0_pos : 0 < (Q_seq η h 0 : ℝ) := pos_of_one_le_log h_ℓ₁
    have h_P1_pos : 0 < (P_seq η h 1 : ℝ) := by
      have : 0 < Real.exp (E_seq η h 1) := Real.exp_pos _
      exact this.trans_le (Nat.le_ceil _)
    have h_coeff : 1 ≤ 8 * ((2 : ℕ) : ℝ) ^ 2 / η := by
      have h32 : 8 * ((2 : ℕ) : ℝ) ^ 2 = (32 : ℝ) := by norm_num
      rw [h32]
      have : 1 ≤ 1 / η := by
        have : η < 1 := by linarith
        exact (one_lt_one_div hη0 this).le
      have : (32 : ℝ) * 1 ≤ 32 * (1 / η) := mul_le_mul_of_nonneg_left this (by norm_num)
      have : 32 * (1 / η) = 32 / η := by ring
      linarith
    have h_logQ0_ge : 0 ≤ Real.log (Q_seq η h 0 : ℝ) := by
      have : Real.log (Q_seq η h 0 : ℝ) = Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) := rfl
      linarith [h_ℓ₁]
    have h_log_le : Real.log (Q_seq η h 0 : ℝ) ≤ Real.log (P_seq η h 1 : ℝ) := by
      have h1 : Real.log (Q_seq η h 0 : ℝ) ≤ (8 * ((2 : ℕ) : ℝ) ^ 2 / η) * Real.log (Q_seq η h 0 : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right h_coeff h_logQ0_ge
      have h2 : (8 * ((2 : ℕ) : ℝ) ^ 2 / η) * Real.log (Q_seq η h 0 : ℝ) ≤
          (8 * ((2 : ℕ) : ℝ) ^ 2 / η) * Real.log (Q_seq η h 0 : ℝ) + 16 * Real.log 2 := by
        have : 0 ≤ 16 * Real.log 2 := by positivity
        linarith
      linarith [h1, h2, h_cond, h_P1]
    have := (Real.log_le_log_iff h_Q0_pos h_P1_pos).mp h_log_le
    exact Nat.cast_le.mp this
  | succ j =>
    have hj_pos : 1 ≤ j + 1 := by omega
    have h_cond := cond3_succ hη0 hη h h_ℓ₁ (j + 1) hj_pos
    have h_F : 0 ≤ F_seq η h (j + 1) := by
      rw [F_seq_eq_mul_E_seq η h (j + 1) hj_pos]
      have : 0 ≤ ((j + 1 + 1 : ℕ) : ℝ) ^ 2 := by positivity
      have : 0 ≤ E_seq η h (j + 1) := by linarith [one_le_E_seq_succ hη0 hη h h_ℓ₁ (j + 1) hj_pos]
      positivity
    have h_logQ := log_Q_seq_le η h (j + 1) h_F
    have h_P : E_seq η h (j + 1 + 1) ≤ Real.log (P_seq η h (j + 1 + 1) : ℝ) := log_P_seq_ge η h (j + 1 + 1)
    have h_Q_pos : 0 < (Q_seq η h (j + 1) : ℝ) := by
      have : 0 < Real.exp (F_seq η h (j + 1)) := Real.exp_pos _
      have : 1 ≤ Real.exp (F_seq η h (j + 1)) := Real.one_le_exp h_F
      exact Nat.cast_pos.mpr ((Nat.one_le_floor_iff _).mpr this)
    have h_P_pos : 0 < (P_seq η h (j + 1 + 1) : ℝ) := by
      have : 0 < Real.exp (E_seq η h (j + 1 + 1)) := Real.exp_pos _
      exact this.trans_le (Nat.le_ceil _)
    set k : ℝ := (((j + 1 + 1) + 1 : ℕ) : ℝ)
    have hk_ge : (3 : ℝ) ≤ k := by
      dsimp [k]
      have : 3 ≤ j + 1 + 1 + 1 := by omega
      exact_mod_cast this
    have h_coeff : 1 ≤ 8 * k ^ 2 / η := by
      have h_eta : 1 ≤ 1 / η := by
        have : η < 1 := by linarith
        exact (one_lt_one_div hη0 this).le
      have hk2 : (9 : ℝ) ≤ k ^ 2 := by nlinarith
      have : (1 : ℝ) ≤ 8 * 9 := by norm_num
      have : (1 : ℝ) ≤ (8 * k ^ 2) * (1 / η) := by nlinarith
      have : (8 * k ^ 2) * (1 / η) = 8 * k ^ 2 / η := by ring
      linarith
    have h_log_le : Real.log (Q_seq η h (j + 1) : ℝ) ≤ Real.log (P_seq η h (j + 1 + 1) : ℝ) := by
      have h1 : Real.log (Q_seq η h (j + 1) : ℝ) ≤ F_seq η h (j + 1) := h_logQ
      have h2 : F_seq η h (j + 1) ≤ (8 * k ^ 2 / η) * F_seq η h (j + 1) := by
        simpa using mul_le_mul_of_nonneg_right h_coeff h_F
      have h3 : (8 * k ^ 2 / η) * F_seq η h (j + 1) ≤ (8 * k ^ 2 / η) * F_seq η h (j + 1) + 16 * Real.log k := by
        have : 0 ≤ 16 * Real.log k := by
          have : 1 ≤ k := by linarith
          have := Real.log_nonneg this
          positivity
        linarith
      linarith [h1, h2, h3, h_cond, h_P]
    have := (Real.log_le_log_iff h_Q_pos h_P_pos).mp h_log_le
    exact Nat.cast_le.mp this

lemma Q_seq_le_succ {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_EF0 : E_seq η h 0 + 1 ≤ F_seq η h 0) (h_E0 : 1 ≤ E_seq η h 0)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j : ℕ) :
    Q_seq η h j ≤ Q_seq η h (j + 1) :=
  (Q_seq_le_P_seq_succ hη0 hη h h_ℓ₁ j).trans (P_seq_le_Q_seq hη0 hη h h_EF0 h_E0 h_ℓ₁ (j + 1))

lemma Q_seq_mono_add {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_EF0 : E_seq η h 0 + 1 ≤ F_seq η h 0) (h_E0 : 1 ≤ E_seq η h 0)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (a : ℕ) (d : ℕ) :
    Q_seq η h a ≤ Q_seq η h (a + d) := by
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact ih.trans (Q_seq_le_succ hη0 hη h h_EF0 h_E0 h_ℓ₁ _)

lemma Q_seq_mono {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_EF0 : E_seq η h 0 + 1 ≤ F_seq η h 0) (h_E0 : 1 ≤ E_seq η h 0)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    {a b : ℕ} (hab : a ≤ b) :
    Q_seq η h a ≤ Q_seq η h b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact Q_seq_mono_add hη0 hη h h_EF0 h_E0 h_ℓ₁ a d

lemma two_le_log_P_seq {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_logL : 4 + 1 / η ≤ Real.log (Real.log (h : ℝ)))
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j : ℕ) :
    2 ≤ Real.log (P_seq η h j : ℝ) :=
  (two_le_E_seq hη0 hη h h_logL h_ℓ₁ j).trans (log_P_seq_ge η h j)

lemma two_le_log_log_Q_seq {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_EF0 : E_seq η h 0 + 1 ≤ F_seq η h 0) (h_E0 : 1 ≤ E_seq η h 0)
    (_h_logL : 4 + 1 / η ≤ Real.log (Real.log (h : ℝ)))
    (h_ℓ₁ : Real.exp 2 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j : ℕ) :
    2 ≤ Real.log (Real.log (Q_seq η h j : ℝ)) := by
  have h_ℓ₁_one : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) := by
    have : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    linarith
  cases j with
  | zero =>
    have : Real.log (Q_seq η h 0 : ℝ) = Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ) := rfl
    rw [this]
    have he2_pos : 0 < Real.exp 2 := Real.exp_pos 2
    have h_log := Real.log_le_log he2_pos h_ℓ₁
    rwa [Real.log_exp] at h_log
  | succ j =>
    have h_PQ : P_seq η h (j + 1) ≤ Q_seq η h (j + 1) :=
      P_seq_le_Q_seq hη0 hη h h_EF0 h_E0 h_ℓ₁_one (j + 1)
    have h_P_pos : 0 < (P_seq η h (j + 1) : ℝ) := by
      have : 0 < Real.exp (E_seq η h (j + 1)) := Real.exp_pos _
      exact this.trans_le (Nat.le_ceil _)
    have h_log_le : Real.log (P_seq η h (j + 1) : ℝ) ≤ Real.log (Q_seq η h (j + 1) : ℝ) :=
      Real.log_le_log h_P_pos (Nat.cast_le.mpr h_PQ)
    have h_E : E_seq η h (j + 1) ≤ Real.log (P_seq η h (j + 1) : ℝ) := log_P_seq_ge η h (j + 1)
    have h_bound := bound_Ei (j + 1) (by omega) (Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) h_ℓ₁_one η hη0 hη
    set ki : ℝ := ((j + 1 + 1 : ℕ) : ℝ)
    have hk_ge : 2 ≤ ki := by
      dsimp [ki]
      have : 2 ≤ j + 1 + 1 := by omega
      exact_mod_cast this
    have h_inv : 6 < 1 / η := by
      have h1 : (1 : ℝ) / (1 / 6) < 1 / η := one_div_lt_one_div_of_lt hη0 hη
      have h2 : (1 : ℝ) / (1 / 6) = 6 := by norm_num
      rwa [h2] at h1
    have h_36 : 36 < 1 / η ^ 2 := by
      have : 6 ^ 2 < (1 / η) ^ 2 := by
        have : (0 : ℝ) ≤ 6 := by norm_num
        nlinarith
      have : (1 / η) ^ 2 = 1 / η ^ 2 := by ring
      linarith
    have h_exp2_le : Real.exp 2 ≤ 100 ^ 2 * ki ^ 4 * (Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) / η ^ 2 := by
      have he2 : Real.exp 2 ≤ 10 := by
        have h_add : (2 : ℝ) = 1 + 1 := by ring
        rw [h_add, Real.exp_add]
        have : Real.exp 1 < 2.8 := Real.exp_one_lt_d9.trans (by norm_num)
        have : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
        nlinarith
      have hki : 16 ≤ ki ^ 4 := by
        have : 4 ≤ ki ^ 2 := by nlinarith
        have : 16 ≤ (ki ^ 2) ^ 2 := by nlinarith
        have : (ki ^ 2) ^ 2 = ki ^ 4 := by ring
        linarith
      have h_ineq : 100 ^ 2 * 16 * 1 * 36 ≤
          100 ^ 2 * ki ^ 4 * (Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) * (1 / η ^ 2) := by
        have h1 : (100 : ℝ) ^ 2 * 16 * 1 ≤ 100 ^ 2 * ki ^ 4 * (Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) := by
          have : (100 : ℝ) ^ 2 * 16 ≤ 100 ^ 2 * ki ^ 4 := by nlinarith
          nlinarith
        have h2 : (36 : ℝ) ≤ 1 / η ^ 2 := h_36.le
        exact mul_le_mul h1 h2 (by norm_num) (by positivity)
      have h_div : 100 ^ 2 * ki ^ 4 * (Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) * (1 / η ^ 2) =
          100 ^ 2 * ki ^ 4 * (Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) / η ^ 2 := by ring
      have hprod : (10 : ℝ) ≤ 100 ^ 2 * 16 * 1 * 36 := by norm_num
      linarith
    have h_E_val : E_seq η h (j + 1) = 100 ^ (j + 1 + 1) * ki ^ (4 * (j + 1 + 1)) *
        (Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) ^ (j + 1) / η ^ (j + 1 + 1) := by
      rfl
    have h_bound' : 100 ^ 2 * ki ^ 4 * (Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)) / η ^ 2 ≤
        E_seq η h (j + 1) := by
      rw [h_E_val]
      exact h_bound
    have h_trans : Real.exp 2 ≤ Real.log (Q_seq η h (j + 1) : ℝ) := by
      linarith [h_exp2_le, h_bound', h_E, h_log_le]
    have he2_pos : 0 < Real.exp 2 := Real.exp_pos 2
    have h_final := Real.log_le_log he2_pos h_trans
    rwa [Real.log_exp] at h_final

lemma sum_piece4 (n : ℕ) (g : Fin (n + 1) → ℝ) (ℓ₁ ε : ℝ) (hε : 0 < ε) (hℓ₁ : 16 / ε ≤ ℓ₁)
    (hg : ∀ i : Fin n, g i.succ ≤ (4 / ℓ₁) * (1 / ((i.val : ℝ) + 1) - 1 / ((i.val : ℝ) + 2))) :
    ∑ i : Fin n, g i.succ ≤ ε / 4 := by
  have h_sum_le : ∑ i : Fin n, g i.succ ≤ ∑ i : Fin n, (4 / ℓ₁) * (1 / ((i.val : ℝ) + 1) - 1 / ((i.val : ℝ) + 2)) :=
    Finset.sum_le_sum (fun i _ => hg i)
  rw [← Finset.mul_sum] at h_sum_le
  have h_tel := sum_telescope_le_one n
  have h_coeff : 0 ≤ 4 / ℓ₁ := by
    have : 0 < 16 / ε := by positivity
    have : 0 < ℓ₁ := this.trans_le hℓ₁
    positivity
  have h_mul := mul_le_mul_of_nonneg_left h_tel h_coeff
  have : (4 / ℓ₁) * 1 = 4 / ℓ₁ := by ring
  rw [this] at h_mul
  have h_trans := h_sum_le.trans h_mul
  have h_final : 4 / ℓ₁ ≤ ε / 4 := by
    have h_ℓ₁_pos : 0 < ℓ₁ := by
      have : 0 < 16 / ε := by positivity
      exact this.trans_le hℓ₁
    rw [div_le_iff₀ h_ℓ₁_pos]
    have : 4 ≤ (ε / 4) * (16 / ε) := by
      have : (ε / 4) * (16 / ε) = 4 := by
        have : ε ≠ 0 := by linarith
        field_simp
        ring
      linarith
    have : (ε / 4) * (16 / ε) ≤ (ε / 4) * ℓ₁ := mul_le_mul_of_nonneg_left hℓ₁ (by positivity)
    linarith
  exact h_trans.trans h_final

lemma sum_piece3 (n : ℕ) (f : Fin (n + 1) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hf : ∀ i : Fin n, f i.succ ≤ (ε / 4) * ((1 / 2 : ℝ) ^ (i.val + 1))) :
    ∑ i : Fin n, f i.succ ≤ ε / 4 := by
  have h_sum_le : ∑ i : Fin n, f i.succ ≤ ∑ i : Fin n, (ε / 4) * ((1 / 2 : ℝ) ^ (i.val + 1)) :=
    Finset.sum_le_sum (fun i _ => hf i)
  rw [← Finset.mul_sum] at h_sum_le
  have h_geom := sum_geom_two_le_one n
  have h_coeff : 0 ≤ ε / 4 := by positivity
  have h_mul := mul_le_mul_of_nonneg_left h_geom h_coeff
  have : (ε / 4) * 1 = ε / 4 := by ring
  rw [this] at h_mul
  exact h_sum_le.trans h_mul

lemma X_pow_beta (X : ℕ) (hlogX : 16 ≤ Real.log (X : ℝ)) (β : ℝ) (hβ : 3 / 4 ≤ β) :
    Real.exp (Real.sqrt (Real.log (X : ℝ))) ≤ (X : ℝ) ^ β := by
  have hX_pos : 0 < (X : ℝ) := by
    have : X ≠ 0 := by
      rintro rfl
      simp only [Nat.cast_zero, Real.log_zero] at hlogX
      linarith
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero this)
  have hsqrt : Real.sqrt (Real.log (X : ℝ)) ≤ β * Real.log (X : ℝ) := by
    have h1 : Real.sqrt (Real.log (X : ℝ)) ≤ (3 / 4) * Real.log (X : ℝ) := by
      have hsq : Real.sqrt (Real.log (X : ℝ)) * Real.sqrt (Real.log (X : ℝ)) = Real.log (X : ℝ) :=
        Real.mul_self_sqrt (by linarith)
      have h4 : 4 ≤ Real.sqrt (Real.log (X : ℝ)) := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]
        nlinarith
      have : Real.sqrt (Real.log (X : ℝ)) ≤ (3 / 4) * (Real.sqrt (Real.log (X : ℝ)) * Real.sqrt (Real.log (X : ℝ))) := by
        nlinarith
      rwa [hsq] at this
    have h2 : (3 / 4) * Real.log (X : ℝ) ≤ β * Real.log (X : ℝ) :=
      mul_le_mul_of_nonneg_right hβ (by linarith)
    exact h1.trans h2
  rw [Real.rpow_def_of_pos hX_pos]
  have h_comm : β * Real.log (X : ℝ) = Real.log (X : ℝ) * β := by ring
  rw [h_comm] at hsqrt
  exact Real.exp_le_exp.mpr hsqrt

lemma X_pow_4 (X : ℕ) (hlogX : 16 ≤ Real.log (X : ℝ)) :
    (Real.exp (Real.sqrt (Real.log (X : ℝ)))) ^ 4 ≤ (X : ℝ) := by
  have hX_pos : 0 < (X : ℝ) := by
    have : X ≠ 0 := by
      rintro rfl
      simp only [Nat.cast_zero, Real.log_zero] at hlogX
      linarith
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero this)
  have h4 : 4 * Real.sqrt (Real.log (X : ℝ)) ≤ Real.log (X : ℝ) := by
    have hsq : Real.sqrt (Real.log (X : ℝ)) * Real.sqrt (Real.log (X : ℝ)) = Real.log (X : ℝ) :=
      Real.mul_self_sqrt (by linarith)
    have h_ge4 : 4 ≤ Real.sqrt (Real.log (X : ℝ)) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]
      nlinarith
    have : 4 * Real.sqrt (Real.log (X : ℝ)) ≤ Real.sqrt (Real.log (X : ℝ)) * Real.sqrt (Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_right h_ge4 (Real.sqrt_nonneg _)
    rwa [hsq] at this
  have h_exp : (Real.exp (Real.sqrt (Real.log (X : ℝ)))) ^ 4 =
      Real.exp (4 * Real.sqrt (Real.log (X : ℝ))) := by
    rw [← Real.exp_nat_mul]
    push_cast
    rfl
  rw [h_exp]
  have h_le := Real.exp_le_exp.mpr h4
  rwa [Real.exp_log hX_pos] at h_le

lemma J_P_bound (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) (J : ℕ) (hJ3 : 3 ≤ J)
    (X : ℕ) (hX : 16 ≤ X) (loglogX : 1 ≤ Real.log (Real.log (X : ℝ)))
    (F_J E_J_sub_1 : ℝ)
    (h_cond2 : (4 * ((J + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log F_J + 1 ≤ E_J_sub_1)
    (h_F_gt : Real.sqrt (Real.log (X : ℝ)) < F_J) :
    Real.log (X : ℝ) ^ (20 / η) ≤ Real.exp E_J_sub_1 := by
  have hX_r : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogX_pos : 1 < Real.log (X : ℝ) := by
    have h1 : Real.exp 1 < Real.log 16 := by
      have h16' : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      have hlog16' : Real.log 16 = 4 * Real.log 2 := by
        rw [h16', Real.log_pow (2 : ℝ) 4]
        push_cast
        ring
      have hlog2 := Real.log_two_gt_d9
      have he := Real.exp_one_lt_d9
      linarith
    have he1 : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have : Real.log 16 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) hX_r
    linarith
  have hsqrt_pos : 0 < Real.sqrt (Real.log (X : ℝ)) := Real.sqrt_pos.mpr (by linarith)
  have hlog_F : (1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)) < Real.log F_J := by
    have h1 : Real.log (Real.sqrt (Real.log (X : ℝ))) < Real.log F_J :=
      Real.log_lt_log hsqrt_pos h_F_gt
    rw [Real.sqrt_eq_rpow, Real.log_rpow (by linarith)] at h1
    exact h1
  have h_J_coeff : 64 / η ≤ 4 * ((J + 1 : ℕ) : ℝ) ^ 2 / η := by
    have : (4 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) := by
      have : 4 ≤ J + 1 := by omega
      exact_mod_cast this
    have : (16 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    have : (64 : ℝ) ≤ 4 * ((J + 1 : ℕ) : ℝ) ^ 2 := by linarith
    exact div_le_div_of_nonneg_right this hη0.le
  have h_step1 : (64 / η) * ((1 / 2 : ℝ) * Real.log (Real.log (X : ℝ))) ≤
      (4 * ((J + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log F_J := by
    have h_half_pos : 0 ≤ (1 / 2 : ℝ) * Real.log (Real.log (X : ℝ)) := by positivity
    exact mul_le_mul h_J_coeff hlog_F.le h_half_pos (by positivity)
  have h_32 : (32 / η) * Real.log (Real.log (X : ℝ)) ≤ (4 * ((J + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log F_J := by
    have : (64 / η) * ((1 / 2 : ℝ) * Real.log (Real.log (X : ℝ))) =
        (32 / η) * Real.log (Real.log (X : ℝ)) := by ring
    rwa [← this]
  have h_20_le_32 : (20 / η) * Real.log (Real.log (X : ℝ)) ≤ (32 / η) * Real.log (Real.log (X : ℝ)) := by
    have : 20 / η ≤ 32 / η := by
      exact div_le_div_of_nonneg_right (by norm_num) hη0.le
    exact mul_le_mul_of_nonneg_right this (by linarith)
  have h_exp_bound : Real.log (Real.log (X : ℝ)) * (20 / η) ≤ E_J_sub_1 := by
    have : (32 / η) * Real.log (Real.log (X : ℝ)) ≤ E_J_sub_1 := by linarith [h_32, h_cond2]
    have : (20 / η) * Real.log (Real.log (X : ℝ)) ≤ E_J_sub_1 := h_20_le_32.trans this
    rw [mul_comm] at this
    exact this
  rw [Real.rpow_def_of_pos (by linarith)]
  exact Real.exp_le_exp.mpr h_exp_bound

lemma cond9_le (L : ℝ) (hL1 : Real.exp 1 ≤ L) (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6)
    (Q₀ P₀ : ℝ) (hlogQ₀ : Real.log Q₀ ≤ L) (hlogQ₀_ge : 0 ≤ Real.log Q₀)
    (hP₀ : Real.exp ((200 / (η * (1 / 6 - η))) * Real.log L) ≤ P₀)
    (ε : ℝ) (hε : 0 < ε) (hL_eps : 1 / ε ≤ L) :
    (Real.log Q₀) ^ (1 / 3 : ℝ) / P₀ ^ (1 / 6 - η) ≤ ε := by
  have hL_pos : 0 < L := by
    have : 0 < Real.exp 1 := Real.exp_pos 1
    linarith
  have h1_le_L : 1 ≤ L := by
    have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  have h_eta_sub : 0 < 1 / 6 - η := by linarith
  have h_sub_ne : 1 / 6 - η ≠ 0 := by linarith
  have h_simp_exp : (200 / (η * (1 / 6 - η))) * (1 / 6 - η) = 200 / η := by
    have h_div : 200 / (η * (1 / 6 - η)) = (200 / η) / (1 / 6 - η) := by
      rw [div_mul_eq_div_div]
    rw [h_div, div_mul_cancel₀ _ h_sub_ne]
  have h_inv_eta : 6 < 1 / η := by
    have h1 : (1 : ℝ) / (1 / 6) < 1 / η := one_div_lt_one_div_of_lt hη0 hη
    have h2 : (1 : ℝ) / (1 / 6) = 6 := by norm_num
    rwa [h2] at h1
  have h_200_eta : 1200 < 200 / η := by
    have : 200 * 6 < 200 * (1 / η) := mul_lt_mul_of_pos_left h_inv_eta (by norm_num)
    have : 200 * (1 / η) = 200 / η := by ring
    linarith
  have h_rpow_P : (Real.exp ((200 / (η * (1 / 6 - η))) * Real.log L)) ^ (1 / 6 - η) ≤ P₀ ^ (1 / 6 - η) := by
    have h_pos : 0 ≤ Real.exp ((200 / (η * (1 / 6 - η))) * Real.log L) := (Real.exp_pos _).le
    exact Real.rpow_le_rpow h_pos hP₀ h_eta_sub.le
  have h_exp_mul : (Real.exp ((200 / (η * (1 / 6 - η))) * Real.log L)) ^ (1 / 6 - η) =
      L ^ (200 / η) := by
    rw [← Real.exp_mul]
    have : ((200 / (η * (1 / 6 - η))) * Real.log L) * (1 / 6 - η) =
        Real.log L * (200 / η) := by
      calc ((200 / (η * (1 / 6 - η))) * Real.log L) * (1 / 6 - η)
        _ = ((200 / (η * (1 / 6 - η))) * (1 / 6 - η)) * Real.log L := by ring
        _ = (200 / η) * Real.log L := by rw [h_simp_exp]
        _ = Real.log L * (200 / η) := by ring
    rw [this]
    exact (Real.rpow_def_of_pos hL_pos (200 / η)).symm
  rw [h_exp_mul] at h_rpow_P
  have h_top : (Real.log Q₀) ^ (1 / 3 : ℝ) ≤ L ^ (1 / 3 : ℝ) := by
    exact Real.rpow_le_rpow hlogQ₀_ge hlogQ₀ (by norm_num)
  have h_div_le : (Real.log Q₀) ^ (1 / 3 : ℝ) / P₀ ^ (1 / 6 - η) ≤
      L ^ (1 / 3 : ℝ) / L ^ (200 / η) := by
    have h_num_pos : 0 ≤ L ^ (1 / 3 : ℝ) := by positivity
    have h_denom_pos : 0 < L ^ (200 / η) := Real.rpow_pos_of_pos hL_pos _
    have hP0_pos : 0 < P₀ := (Real.exp_pos _).trans_le hP₀
    have hdenom_P : 0 < P₀ ^ (1 / 6 - η) := Real.rpow_pos_of_pos hP0_pos _
    have h1 : (Real.log Q₀) ^ (1 / 3 : ℝ) / P₀ ^ (1 / 6 - η) ≤
        L ^ (1 / 3 : ℝ) / P₀ ^ (1 / 6 - η) :=
      div_le_div_of_nonneg_right h_top hdenom_P.le
    have h2 : L ^ (1 / 3 : ℝ) / P₀ ^ (1 / 6 - η) ≤
        L ^ (1 / 3 : ℝ) / L ^ (200 / η) :=
      div_le_div_of_nonneg_left h_num_pos h_denom_pos h_rpow_P
    exact h1.trans h2
  have h_sub_pow : L ^ (1 / 3 : ℝ) / L ^ (200 / η) = L ^ (1 / 3 - 200 / η) := by
    rw [← Real.rpow_sub hL_pos]
  rw [h_sub_pow] at h_div_le
  have h_exp_neg : 1 / 3 - 200 / η ≤ -1 := by linarith
  have h_L_neg : L ^ (1 / 3 - 200 / η) ≤ L ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le h1_le_L h_exp_neg
  have h_L_inv : L ^ (-1 : ℝ) = 1 / L := by
    rw [Real.rpow_neg_one, one_div]
  rw [h_L_inv] at h_L_neg
  have h_one_div_L : 1 / L ≤ ε := by
    have h_eps_pos : 0 < 1 / ε := by positivity
    have := one_div_le_one_div_of_le h_eps_pos hL_eps
    rwa [one_div_one_div] at this
  exact h_div_le.trans (h_L_neg.trans h_one_div_L)

lemma Hj_zero_le_sqrt_P (P Q : ℝ) (hP : 2 ≤ P) (hQ : Real.exp 1 ≤ Q) (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) :
    P ^ (1 / 6 - η) / (Real.log Q) ^ (1 / 3 : ℝ) ≤ Real.sqrt P := by
  have hlogQ : 1 ≤ Real.log Q := by
    have h1 : Real.log (Real.exp 1) ≤ Real.log Q := Real.log_le_log (Real.exp_pos 1) hQ
    rwa [Real.log_exp] at h1
  have hdenom : (1 : ℝ) ≤ (Real.log Q) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hlogQ (by norm_num)
  have hdenom_pos : 0 < (Real.log Q) ^ (1 / 3 : ℝ) := by positivity
  have hP1 : 1 ≤ P := by linarith
  have h_exp : 1 / 6 - η ≤ 1 / 2 := by linarith
  have hP_pow : P ^ (1 / 6 - η) ≤ P ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hP1 h_exp
  rw [Real.sqrt_eq_rpow]
  calc P ^ (1 / 6 - η) / (Real.log Q) ^ (1 / 3 : ℝ)
    _ ≤ P ^ (1 / 6 - η) / 1 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hdenom
    _ = P ^ (1 / 6 - η) := by ring
    _ ≤ P ^ (1 / (2 : ℝ)) := hP_pow

lemma Hj_succ_le_sqrt_P (k : ℝ) (hk : 2 ≤ k) (ℓ₁ : ℝ) (hℓ₁ : 1 ≤ ℓ₁)
    (P₀ P : ℝ) (hP₀_pos : 0 < P₀) (hP₀ : Real.log P₀ ≤ 6 * k ^ 4 * ℓ₁)
    (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6)
    (E : ℝ) (hE : 100 ^ 2 * k ^ 4 * ℓ₁ / η ^ 2 ≤ E)
    (hP : Real.exp E ≤ P) (Q₀ : ℝ) (hlogQ₀ : 1 ≤ Real.log Q₀) :
    k ^ 2 * P₀ ^ (1 / 6 - η) / (Real.log Q₀) ^ (1 / 3 : ℝ) ≤ Real.sqrt P := by
  have hk_pos : 0 < k := by linarith
  have hdenom : (1 : ℝ) ≤ (Real.log Q₀) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hlogQ₀ (by norm_num)
  have hlogk : Real.log k ≤ k := (Real.log_le_sub_one_of_pos hk_pos).trans (by linarith)
  have hk_le_k4 : k ≤ k ^ 4 := by
    have hk2 : k ≤ k ^ 2 := by nlinarith
    have hk4 : k ^ 2 ≤ k ^ 4 := by
      have : (k ^ 2) ^ 2 = k ^ 4 := by ring
      have : 1 ≤ k ^ 2 := by nlinarith
      nlinarith
    linarith
  have hlogk_le : Real.log k ≤ k ^ 4 := hlogk.trans hk_le_k4
  have hlogk_mul : 2 * Real.log k ≤ 2 * k ^ 4 * ℓ₁ := by
    have : 2 * Real.log k ≤ 2 * k ^ 4 := by linarith
    have : 2 * k ^ 4 ≤ 2 * k ^ 4 * ℓ₁ := by nlinarith
    linarith
  have hP₀_exp : (1 / 6 - η) * Real.log P₀ ≤ 1 * k ^ 4 * ℓ₁ := by
    have h1 : 1 / 6 - η ≤ 1 / 6 := by linarith
    have h2 : 0 < 6 * k ^ 4 * ℓ₁ := by positivity
    have h3 : (1 / 6 - η) * Real.log P₀ ≤ (1 / 6) * (6 * k ^ 4 * ℓ₁) := by
      rcases le_total 0 (Real.log P₀) with hp | hn
      · exact mul_le_mul h1 hP₀ hp (by norm_num)
      · have : (1 / 6 - η) * Real.log P₀ ≤ 0 := by
          have : 0 ≤ 1 / 6 - η := by linarith
          nlinarith
        linarith
    calc (1 / 6 - η) * Real.log P₀
      _ ≤ (1 / 6) * (6 * k ^ 4 * ℓ₁) := h3
      _ = 1 * k ^ 4 * ℓ₁ := by ring
  have h_sum_log : Real.log (k ^ 2 * P₀ ^ (1 / 6 - η)) ≤ 3 * k ^ 4 * ℓ₁ := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow, Real.log_rpow hP₀_pos]
    linarith
  have h_inv : 6 < 1 / η := by
    have h1 : (1 : ℝ) / (1 / 6) < 1 / η := one_div_lt_one_div_of_lt hη0 hη
    have h2 : (1 : ℝ) / (1 / 6) = 6 := by norm_num
    rwa [h2] at h1
  have h_36 : 36 < 1 / η ^ 2 := by
    have : 6 ^ 2 < (1 / η) ^ 2 := by
      have : (0 : ℝ) ≤ 6 := by norm_num
      nlinarith
    have : (1 / η) ^ 2 = 1 / η ^ 2 := by ring
    linarith
  have h_E_bound : 6 * k ^ 4 * ℓ₁ ≤ E := by
    have h_prod : 6 ≤ 100 ^ 2 / η ^ 2 := by
      have h100 : (6 : ℝ) ≤ 100 ^ 2 * 36 := by norm_num
      have h_div : 100 ^ 2 * (1 / η ^ 2) = 100 ^ 2 / η ^ 2 := by ring
      have h_mul := mul_le_mul_of_nonneg_left h_36.le (by positivity : 0 ≤ (100 : ℝ) ^ 2)
      linarith
    calc 6 * k ^ 4 * ℓ₁
      _ = 6 * (k ^ 4 * ℓ₁) := by ring
      _ ≤ (100 ^ 2 / η ^ 2) * (k ^ 4 * ℓ₁) := mul_le_mul_of_nonneg_right h_prod (by positivity)
      _ = 100 ^ 2 * k ^ 4 * ℓ₁ / η ^ 2 := by ring
      _ ≤ E := hE
  have h_half_E : 3 * k ^ 4 * ℓ₁ ≤ E / 2 := by linarith
  have h_log_le_half_E : Real.log (k ^ 2 * P₀ ^ (1 / 6 - η)) ≤ E / 2 := h_sum_log.trans h_half_E
  have h_exp_le : k ^ 2 * P₀ ^ (1 / 6 - η) ≤ Real.exp (E / 2) := by
    have := Real.exp_le_exp.mpr h_log_le_half_E
    rwa [Real.exp_log (by positivity)] at this
  have h_exp_half : Real.exp (E / 2) = Real.sqrt (Real.exp E) := by
    rw [Real.sqrt_eq_rpow]
    have : E / 2 = E * (1 / 2 : ℝ) := by ring
    rw [this, Real.exp_mul]
  have h_sqrt_exp : Real.exp (E / 2) ≤ Real.sqrt P := by
    rw [h_exp_half]
    exact Real.sqrt_le_sqrt hP
  have h_top : k ^ 2 * P₀ ^ (1 / 6 - η) ≤ Real.sqrt P := h_exp_le.trans h_sqrt_exp
  calc k ^ 2 * P₀ ^ (1 / 6 - η) / (Real.log Q₀) ^ (1 / 3 : ℝ)
    _ ≤ k ^ 2 * P₀ ^ (1 / 6 - η) / 1 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hdenom
    _ = k ^ 2 * P₀ ^ (1 / 6 - η) := by ring
    _ ≤ Real.sqrt P := h_top

lemma two_le_Hj {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (j : Fin J)
    (h_two_le_C : 2 ≤ (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) / (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ)) :
    2 ≤ S.Hj hJ j := by
  dsimp [RangeSystem.Hj]
  have h_k_ge1 : 1 ≤ ((j.val + 1 : ℕ) : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by
      have : 1 ≤ j.val + 1 := by omega
      exact_mod_cast this
    nlinarith
  have h_pos : 0 ≤ (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) / (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) := by linarith
  have h_mul : 1 * 2 ≤ ((j.val + 1 : ℕ) : ℝ) ^ 2 *
      ((S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) / (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ)) :=
    mul_le_mul h_k_ge1 h_two_le_C (by norm_num) (by positivity)
  have : ((j.val + 1 : ℕ) : ℝ) ^ 2 * (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) / (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) =
      ((j.val + 1 : ℕ) : ℝ) ^ 2 * ((S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) / (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ)) := by ring
  rw [this]
  linarith

lemma F_seq_ge_self (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (j : ℕ) (hj : 2 ≤ j) :
    (j : ℝ) < F_seq η h j := by
  dsimp [F_seq]
  have hj0 : j ≠ 0 := by omega
  simp only [hj0, ↓reduceIte]
  set k : ℝ := ((j + 1 : ℕ) : ℝ)
  set ℓ₁ := Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ)
  have hk : 1 ≤ k := by
    dsimp [k]
    have : 1 ≤ j + 1 := by omega
    exact_mod_cast this
  have hk_pow : 1 ≤ k ^ (4 * (j + 1) + 2) := one_le_pow₀ hk
  have hℓ₁_pow : 1 ≤ ℓ₁ ^ (j + 1) := one_le_pow₀ h_ℓ₁
  have h_eta : 1 ≤ 1 / η := by
    have : η < 1 := by linarith
    have := one_lt_one_div hη0 this
    linarith
  have h_eta_pow : 1 ≤ (1 / η) ^ (j + 1) := one_le_pow₀ h_eta
  have h_div_eta : 1 ≤ 1 / η ^ (j + 1) := by
    rw [← one_div_pow]
    exact h_eta_pow
  have h100_gt : (j + 1 : ℝ) < 100 ^ (j + 1) := by
    have h_two : (j + 1 : ℝ) < (2 : ℝ) ^ (j + 1) := by
      have : j + 1 < 2 ^ (j + 1) := Nat.lt_pow_self (by norm_num)
      exact_mod_cast this
    have h_pow_le : (2 : ℝ) ^ (j + 1) ≤ 100 ^ (j + 1) := by
      apply pow_le_pow_left₀ (by norm_num) (by norm_num) (j + 1)
    exact h_two.trans_le h_pow_le
  have h100_pos : 0 ≤ (100 : ℝ) ^ (j + 1) := by positivity
  have h1 : 100 ^ (j + 1) ≤ 100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) := by
    simpa using mul_le_mul_of_nonneg_left hk_pow h100_pos
  have h2 : 100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) ≤
      100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1) := by
    have : 0 ≤ 100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) := by positivity
    simpa using mul_le_mul_of_nonneg_left hℓ₁_pow this
  have h3 : 100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1) ≤
      100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1) * (1 / η ^ (j + 1)) := by
    have h_pos : 0 ≤ 100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1) := by positivity
    calc 100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1)
      _ = (100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1)) * 1 := by ring
      _ ≤ (100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1)) * (1 / η ^ (j + 1)) :=
        mul_le_mul_of_nonneg_left h_div_eta h_pos
  have h_prod : (j : ℝ) < (100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1)) * (1 / η ^ (j + 1)) := by
    have : (j : ℝ) < (j + 1 : ℝ) := by linarith
    have : (j : ℝ) < 100 ^ (j + 1) := this.trans h100_gt
    have h_le := h1.trans (h2.trans h3)
    exact this.trans_le h_le
  calc (j : ℝ)
    _ < (100 ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1)) * (1 / η ^ (j + 1)) := h_prod
    _ = (100 : ℝ) ^ (j + 1) * k ^ (4 * (j + 1) + 2) * ℓ₁ ^ (j + 1) / η ^ (j + 1) := by ring

lemma exists_F_seq_gt (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (t : ℝ) :
    ∃ j : ℕ, 2 ≤ j ∧ t < F_seq η h j := by
  use ⌈t⌉₊ + 2
  refine ⟨by omega, ?_⟩
  have hj : 2 ≤ ⌈t⌉₊ + 2 := by omega
  have h_gt := F_seq_ge_self η hη0 hη h h_ℓ₁ (⌈t⌉₊ + 2) hj
  have : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  have : (⌈t⌉₊ : ℝ) < ((⌈t⌉₊ + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  linarith

lemma exists_J (η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (t : ℝ) (ht : F_seq η h 2 ≤ t) :
    ∃ J : ℕ, 3 ≤ J ∧ F_seq η h (J - 1) ≤ t ∧ t < F_seq η h J := by
  have h_ex : ∃ j, 2 ≤ j ∧ t < F_seq η h j := exists_F_seq_gt η hη0 hη h h_ℓ₁ t
  set P : ℕ → Prop := fun j => 2 ≤ j ∧ t < F_seq η h j
  have : DecidablePred P := Classical.decPred P
  set J := Nat.find h_ex
  have hJ_spec : 2 ≤ J ∧ t < F_seq η h J := Nat.find_spec h_ex
  have hJ3 : 3 ≤ J := by
    by_contra h_lt
    have hJ2 : J = 2 := by omega
    have h_spec := hJ_spec.2
    rw [hJ2] at h_spec
    linarith
  have h_F_prev : F_seq η h (J - 1) ≤ t := by
    by_contra h_gt
    have h_lt : J - 1 < J := by omega
    have h_not := Nat.find_min h_ex h_lt
    have h_P : 2 ≤ J - 1 ∧ t < F_seq η h (J - 1) := ⟨by omega, not_le.mp h_gt⟩
    exact h_not h_P
  exact ⟨J, hJ3, h_F_prev, hJ_spec.2⟩

lemma f_succ_bound (i : ℕ) (ε ℓ₁ η : ℝ) (hε : 0 < ε) (hη0 : 0 < η) (hη : η < 1 / 6)
    (hℓ₁ : 1 ≤ ℓ₁) (hℓ₁_eps : 4 / ε ≤ 1400 * ℓ₁) :
    let k : ℝ := ((i + 1 + 1 : ℕ) : ℝ)
    let E : ℝ := 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) * ℓ₁ ^ (i + 1) / η ^ (i + 1 + 1)
    ((i + 1 + 2 : ℕ) : ℝ) ^ 6 / (E / 2) ≤ (ε / 4) * (1 / 2) ^ (i + 1) := by
  intro k E
  have hk_ge : 2 ≤ k := by
    dsimp [k]
    have : 2 ≤ i + 1 + 1 := by omega
    exact_mod_cast this
  have hk_pos : 0 < k := by linarith
  have h_k_pow : k ^ 6 ≤ k ^ (4 * (i + 1 + 1)) := by
    apply pow_le_pow_right₀ (by linarith) (by omega : 6 ≤ 4 * (i + 1 + 1))
  have h_add : ((i + 1 + 2 : ℕ) : ℝ) ≤ 2 * k := by
    dsimp [k]
    push_cast
    linarith
  have h_pow6 : ((i + 1 + 2 : ℕ) : ℝ) ^ 6 ≤ 64 * k ^ 6 := by
    have h1 : 0 ≤ ((i + 1 + 2 : ℕ) : ℝ) := by positivity
    have h2 : ((i + 1 + 2 : ℕ) : ℝ) ^ 6 ≤ (2 * k) ^ 6 := pow_le_pow_left₀ h1 h_add 6
    have h3 : (2 * k) ^ 6 = 64 * k ^ 6 := by ring
    rwa [h3] at h2
  have h_100 : (100 : ℝ) ^ (i + 1 + 1) = 10000 * 100 ^ i := by
    have : i + 1 + 1 = i + 2 := by omega
    rw [this, pow_add, pow_two]
    ring
  have h_100_ge : 5000 * (2 : ℝ) ^ (i + 1) ≤ (100 : ℝ) ^ (i + 1 + 1) := by
    rw [h_100]
    have h_pow : (2 : ℝ) ^ i ≤ (100 : ℝ) ^ i := by
      apply pow_le_pow_left₀ (by norm_num) (by norm_num) i
    have : (2 : ℝ) ^ (i + 1) = 2 * (2 : ℝ) ^ i := by ring
    rw [this]
    calc (5000 : ℝ) * (2 * (2 : ℝ) ^ i)
      _ = 10000 * (2 : ℝ) ^ i := by ring
      _ ≤ 10000 * (100 : ℝ) ^ i := mul_le_mul_of_nonneg_left h_pow (by norm_num)
  have h_ell : ℓ₁ ≤ ℓ₁ ^ (i + 1) := by
    simpa using pow_le_pow_right₀ hℓ₁ (by omega : 1 ≤ i + 1)
  have h_eta2 : (36 : ℝ) ≤ 1 / η ^ (i + 1 + 1) := by
    have h6 : 6 ≤ 1 / η := by
      have := one_div_le_one_div_of_le hη0 hη.le
      linarith
    have h36 : (6 : ℝ) ^ 2 ≤ (1 / η) ^ 2 := pow_le_pow_left₀ (by norm_num) h6 2
    have : (1 / η) ^ 2 ≤ (1 / η) ^ (i + 1 + 1) := by
      have : 1 ≤ 1 / η := by linarith
      apply pow_le_pow_right₀ this (by omega : 2 ≤ i + 1 + 1)
    rw [← one_div_pow]
    have : (6 : ℝ) ^ 2 = 36 := by norm_num
    linarith
  have h_E_prod : (5000 * (2 : ℝ) ^ (i + 1)) * k ^ 6 * ℓ₁ * 36 ≤
      100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) * ℓ₁ ^ (i + 1) * (1 / η ^ (i + 1 + 1)) := by
    have h1 : (5000 * (2 : ℝ) ^ (i + 1)) * k ^ 6 ≤ 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) :=
      mul_le_mul h_100_ge h_k_pow (by positivity) (by positivity)
    have h2 : (5000 * (2 : ℝ) ^ (i + 1)) * k ^ 6 * ℓ₁ ≤
        100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) * ℓ₁ ^ (i + 1) :=
      mul_le_mul h1 h_ell (by linarith) (by positivity)
    exact mul_le_mul h2 h_eta2 (by norm_num) (by positivity)
  have h_E_div : 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) * ℓ₁ ^ (i + 1) * (1 / η ^ (i + 1 + 1)) = E := by
    dsimp [E]
    ring
  rw [h_E_div] at h_E_prod
  have h_prod2 : 2812 * ((64 * k ^ 6) * ((2 : ℝ) ^ (i + 1) * ℓ₁)) ≤
      (5000 * (2 : ℝ) ^ (i + 1)) * k ^ 6 * ℓ₁ * 36 := by
    calc 2812 * ((64 * k ^ 6) * ((2 : ℝ) ^ (i + 1) * ℓ₁))
      _ = (2812 * 64) * (k ^ 6 * (2 : ℝ) ^ (i + 1) * ℓ₁) := by ring
      _ ≤ (5000 * 36) * (k ^ 6 * (2 : ℝ) ^ (i + 1) * ℓ₁) := by
        have : (2812 : ℝ) * 64 ≤ 5000 * 36 := by norm_num
        exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = (5000 * (2 : ℝ) ^ (i + 1)) * k ^ 6 * ℓ₁ * 36 := by ring
  have h_ring_num : 2812 * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * ((2 : ℝ) ^ (i + 1) * ℓ₁)) ≤
      (5000 * (2 : ℝ) ^ (i + 1)) * k ^ 6 * ℓ₁ * 36 := by
    have : ((i + 1 + 2 : ℕ) : ℝ) ^ 6 * ((2 : ℝ) ^ (i + 1) * ℓ₁) ≤ (64 * k ^ 6) * ((2 : ℝ) ^ (i + 1) * ℓ₁) :=
      mul_le_mul_of_nonneg_right h_pow6 (by positivity)
    have h_prod1 : 2812 * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * ((2 : ℝ) ^ (i + 1) * ℓ₁)) ≤
        2812 * ((64 * k ^ 6) * ((2 : ℝ) ^ (i + 1) * ℓ₁)) :=
      mul_le_mul_of_nonneg_left this (by norm_num)
    exact h_prod1.trans h_prod2
  have h_E_step : 2800 * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * ((2 : ℝ) ^ (i + 1) * ℓ₁)) ≤ E := by
    have : 2800 * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * ((2 : ℝ) ^ (i + 1) * ℓ₁)) ≤
        2812 * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * ((2 : ℝ) ^ (i + 1) * ℓ₁)) := by
      have : 0 ≤ ((i + 1 + 2 : ℕ) : ℝ) ^ 6 * ((2 : ℝ) ^ (i + 1) * ℓ₁) := by positivity
      nlinarith
    exact this.trans (h_ring_num.trans h_E_prod)
  have h_half_E : 1400 * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * ((2 : ℝ) ^ (i + 1) * ℓ₁)) ≤ E / 2 := by
    linarith [h_E_step]
  have h_eps_bound : (4 / ε) * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * (2 : ℝ) ^ (i + 1)) ≤ E / 2 := by
    have : (4 / ε) * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * (2 : ℝ) ^ (i + 1)) ≤
        (1400 * ℓ₁) * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * (2 : ℝ) ^ (i + 1)) := by
      have : 0 ≤ (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * (2 : ℝ) ^ (i + 1)) := by positivity
      exact mul_le_mul_of_nonneg_right hℓ₁_eps this
    have h_comm : (1400 * ℓ₁) * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * (2 : ℝ) ^ (i + 1)) =
        1400 * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * ((2 : ℝ) ^ (i + 1) * ℓ₁)) := by ring
    rw [h_comm] at this
    exact this.trans h_half_E
  have h_E_half_pos : 0 < E / 2 := by
    dsimp [E]
    positivity
  rw [div_le_iff₀ h_E_half_pos]
  have h_pow_half : (ε / 4) * (1 / 2 : ℝ) ^ (i + 1) = (ε / 4) / (2 : ℝ) ^ (i + 1) := by
    rw [one_div_pow]
    ring
  rw [h_pow_half]
  have h_pos : 0 < (ε / 4) / (2 : ℝ) ^ (i + 1) := by positivity
  rw [← div_le_iff₀' h_pos]
  have : ((i + 1 + 2 : ℕ) : ℝ) ^ 6 / ((ε / 4) / (2 : ℝ) ^ (i + 1)) =
      (4 / ε) * (((i + 1 + 2 : ℕ) : ℝ) ^ 6 * (2 : ℝ) ^ (i + 1)) := by
    have : ε ≠ 0 := by linarith
    have : (2 : ℝ) ^ (i + 1) ≠ 0 := by positivity
    field_simp
  rwa [this]

lemma g_succ_bound (i : ℕ) (ℓ₁ η : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6)
    (hℓ₁ : 1 ≤ ℓ₁) :
    let k : ℝ := ((i + 1 + 1 : ℕ) : ℝ)
    let E : ℝ := 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) * ℓ₁ ^ (i + 1) / η ^ (i + 1 + 1)
    let F : ℝ := 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1) + 2) * ℓ₁ ^ (i + 1 + 1) / η ^ (i + 1 + 1)
    let P := ⌈Real.exp E⌉₊
    let Q := ⌊Real.exp F⌋₊
    Real.log (P : ℝ) / Real.log (Q : ℝ) ≤ (4 / ℓ₁) * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
  intro k E F P Q
  have hk_ge : 2 ≤ k := by
    dsimp [k]
    have : 2 ≤ i + 1 + 1 := by omega
    exact_mod_cast this
  have hk_pos : 0 < k := by linarith
  have hE_pos : 0 < E := by
    dsimp [E]
    positivity
  have hE1 : 1 ≤ E := by
    dsimp [E]
    have h1 : (1 : ℝ) ≤ (100 : ℝ) ^ (i + 1 + 1) := one_le_pow₀ (by norm_num)
    have h2 : 1 ≤ k ^ (4 * (i + 1 + 1)) := one_le_pow₀ (by linarith)
    have h3 : 1 ≤ ℓ₁ ^ (i + 1) := one_le_pow₀ hℓ₁
    have h4 : 1 ≤ 1 / η ^ (i + 1 + 1) := by
      have : 1 ≤ 1 / η := by
        have : η < 1 := by linarith
        have := one_lt_one_div hη0 this
        linarith
      rw [← one_div_pow]
      exact one_le_pow₀ this
    have h12 : (1 : ℝ) ≤ 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) := mul_le_mul h1 h2 (by positivity) (by positivity)
    have h123 : (1 : ℝ) ≤ 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) * ℓ₁ ^ (i + 1) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) * ℓ₁ ^ (i + 1) := mul_le_mul h12 h3 (by positivity) (by positivity)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1)) * ℓ₁ ^ (i + 1)) * (1 / η ^ (i + 1 + 1)) :=
        mul_le_mul h123 h4 (by positivity) (by positivity)
      _ = E := by dsimp [E]; ring
  have hF_ge2 : 2 ≤ F := by
    dsimp [F]
    have : (2 : ℝ) ≤ (100 : ℝ) ^ (i + 1 + 1) := by
      have : (2 : ℝ) ≤ 100 ^ 2 := by norm_num
      have : (100 : ℝ) ^ 2 ≤ 100 ^ (i + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have h2 : 1 ≤ k ^ (4 * (i + 1 + 1) + 2) := one_le_pow₀ (by linarith)
    have h3 : 1 ≤ ℓ₁ ^ (i + 1 + 1) := one_le_pow₀ hℓ₁
    have h4 : 1 ≤ 1 / η ^ (i + 1 + 1) := by
      have : 1 ≤ 1 / η := by
        have : η < 1 := by linarith
        have := one_lt_one_div hη0 this
        linarith
      rw [← one_div_pow]
      exact one_le_pow₀ this
    have ha : (2 : ℝ) ≤ 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1) + 2) := by
      calc (2 : ℝ) = 2 * 1 := by ring
        _ ≤ 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1) + 2) := mul_le_mul this h2 (by positivity) (by positivity)
    have hb : (2 : ℝ) ≤ 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1) + 2) * ℓ₁ ^ (i + 1 + 1) := by
      calc (2 : ℝ) = 2 * 1 := by ring
        _ ≤ 100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1) + 2) * ℓ₁ ^ (i + 1 + 1) := mul_le_mul ha h3 (by positivity) (by positivity)
    calc (2 : ℝ) = 2 * 1 := by ring
      _ ≤ (100 ^ (i + 1 + 1) * k ^ (4 * (i + 1 + 1) + 2) * ℓ₁ ^ (i + 1 + 1)) * (1 / η ^ (i + 1 + 1)) :=
        mul_le_mul hb h4 (by positivity) (by positivity)
      _ = F := by dsimp [F]; ring
  have hP_le : (P : ℝ) ≤ Real.exp (2 * E) := by
    dsimp [P]
    have h_ceil : (⌈Real.exp E⌉₊ : ℝ) < Real.exp E + 1 := Nat.ceil_lt_add_one (Real.exp_pos E).le
    have h_one : 1 ≤ Real.exp E := by
      have : Real.exp 0 ≤ Real.exp E := Real.exp_le_exp.mpr (by linarith)
      rwa [Real.exp_zero] at this
    have h_two : Real.exp E + 1 ≤ 2 * Real.exp E := by linarith
    have h_exp_two : 2 * Real.exp E ≤ Real.exp (2 * E) := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have : 2 * Real.exp E ≤ Real.exp 1 * Real.exp E := mul_le_mul_of_nonneg_right h2 (Real.exp_pos E).le
      rw [← Real.exp_add] at this
      have h_add : 1 + E ≤ 2 * E := by linarith
      exact this.trans (Real.exp_le_exp.mpr h_add)
    linarith
  have hP_pos : 0 < (P : ℝ) := by
    dsimp [P]
    have : 0 < Real.exp E := Real.exp_pos E
    exact this.trans_le (Nat.le_ceil _)
  have hlogP : Real.log (P : ℝ) ≤ 2 * E := by
    have h_log := Real.log_le_log hP_pos hP_le
    rwa [Real.log_exp] at h_log
  have hlogQ : F / 2 ≤ Real.log (Q : ℝ) := by
    dsimp [Q]
    have h_floor := log_floor_exp_ge F hF_ge2
    have : F / 2 ≤ F - 1 := by linarith
    exact this.trans h_floor
  have hlogQ_pos : 0 < Real.log (Q : ℝ) := by
    have : 0 < F / 2 := by linarith
    exact this.trans_le hlogQ
  have h_div_le : Real.log (P : ℝ) / Real.log (Q : ℝ) ≤ (2 * E) / (F / 2) := by
    have h_top_nonneg : 0 ≤ Real.log (P : ℝ) := by
      have : 1 ≤ Real.exp E := by
        have := Real.exp_le_exp.mpr (by linarith : 0 ≤ E)
        rwa [Real.exp_zero] at this
      have : 1 ≤ (⌈Real.exp E⌉₊ : ℝ) := this.trans (Nat.le_ceil _)
      exact Real.log_nonneg this
    have h1 : Real.log (P : ℝ) / Real.log (Q : ℝ) ≤ (2 * E) / Real.log (Q : ℝ) :=
      div_le_div_of_nonneg_right hlogP hlogQ_pos.le
    have h2 : (2 * E) / Real.log (Q : ℝ) ≤ (2 * E) / (F / 2) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) hlogQ
    exact h1.trans h2
  have h_ratio : (2 * E) / (F / 2) = 4 / (k ^ 2 * ℓ₁) := by
    have h_F_eq : F = E * (k ^ 2 * ℓ₁) := by
      dsimp [E, F]
      have : 4 * (i + 1 + 1) + 2 = 4 * (i + 1 + 1) + 2 := rfl
      have h_pow_k : k ^ (4 * (i + 1 + 1) + 2) = k ^ (4 * (i + 1 + 1)) * k ^ 2 := by
        rw [pow_add]
      have h_pow_ell : ℓ₁ ^ (i + 1 + 1) = ℓ₁ ^ (i + 1) * ℓ₁ := by
        have : i + 1 + 1 = (i + 1) + 1 := by omega
        rw [this, pow_add, pow_one]
      rw [h_pow_k, h_pow_ell]
      ring
    rw [h_F_eq]
    have : E ≠ 0 := by linarith
    have : k ^ 2 * ℓ₁ ≠ 0 := by positivity
    field_simp
    ring
  rw [h_ratio] at h_div_le
  have h_geom : 1 / (k ^ 2) ≤ 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2) := by
    have hk_eq : k = (i : ℝ) + 2 := by
      dsimp [k]
      push_cast
      ring
    rw [hk_eq]
    have h_prod : ((i : ℝ) + 1) * ((i : ℝ) + 2) ≤ ((i : ℝ) + 2) ^ 2 := by
      have : 0 ≤ (i : ℝ) := by positivity
      nlinarith
    have h_pos1 : 0 < ((i : ℝ) + 1) * ((i : ℝ) + 2) := by positivity
    have h_one_div := one_div_le_one_div_of_le h_pos1 h_prod
    have h_ring : 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2)) = 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2) := by
      have : (i : ℝ) + 1 ≠ 0 := by positivity
      have : (i : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring
    rwa [h_ring] at h_one_div
  have h_final : 4 / (k ^ 2 * ℓ₁) ≤ (4 / ℓ₁) * (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)) := by
    have : 4 / (k ^ 2 * ℓ₁) = (4 / ℓ₁) * (1 / k ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left h_geom (by positivity)
  exact h_div_le.trans h_final

lemma base_f_g_bound (η ε L : ℝ) (hη0 : 0 < η) (hη : η < 1 / 6) (hε : 0 < ε)
    (hL : Real.exp 16 ≤ L)
    (hf0 : 256 / ε ≤ Real.exp ((100 / (η * (1 / 6 - η))) * Real.log L))
    (hg0 : 432 * (200 / (η * (1 / 6 - η))) / ε ≤ Real.log L) :
    let kappa := 200 / (η * (1 / 6 - η))
    let E₀ := kappa * Real.log L
    let F₀ := L / Real.log L
    let P₀ := ⌈Real.exp E₀⌉₊
    let Q₀ := ⌊Real.exp F₀⌋₊
    ((0 + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (P₀ : ℝ) + Real.log (P₀ : ℝ) / Real.log (Q₀ : ℝ) ≤ ε / 2 := by
  intro kappa E₀ F₀ P₀ Q₀
  have hlogL : 16 ≤ Real.log L := by
    have h_log := Real.log_le_log (Real.exp_pos 16) hL
    rwa [Real.log_exp] at h_log
  have hL_pos : 0 < L := (Real.exp_pos 16).trans_le hL
  have hlogL_pos : 0 < Real.log L := by linarith
  have hkappa_pos : 0 < kappa := by
    dsimp [kappa]
    have : 0 < 1 / 6 - η := by linarith
    positivity
  have hE₀_pos : 0 < E₀ := by
    dsimp [E₀]
    positivity
  have hE₀_ge1 : 1 ≤ E₀ := by
    dsimp [E₀]
    have : 1 ≤ kappa := by
      dsimp [kappa]
      have : η * (1 / 6 - η) < 1 := by
        have : η < 1 := by linarith
        have : 1 / 6 - η < 1 := by linarith
        nlinarith
      have : 1 < 200 / (η * (1 / 6 - η)) := by
        have h_pos : 0 < η * (1 / 6 - η) := by
          have : 0 < 1 / 6 - η := by linarith
          positivity
        rw [one_lt_div h_pos]
        linarith
      linarith
    nlinarith
  have hP₀_pos : 0 < (P₀ : ℝ) := by
    dsimp [P₀]
    have : 0 < Real.exp E₀ := Real.exp_pos _
    exact this.trans_le (Nat.le_ceil _)
  have h_sqrt_P₀ : Real.exp (E₀ / 2) ≤ Real.sqrt (P₀ : ℝ) := by
    dsimp [P₀]
    have h1 : Real.exp E₀ ≤ (⌈Real.exp E₀⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : Real.sqrt (Real.exp E₀) ≤ Real.sqrt (⌈Real.exp E₀⌉₊ : ℝ) := Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt (Real.exp E₀) = Real.exp (E₀ / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      ring_nf
    rwa [h3] at h2
  have h_half_E₀ : E₀ / 2 = (100 / (η * (1 / 6 - η))) * Real.log L := by
    dsimp [E₀, kappa]
    ring
  have h_f0_denom : 256 / ε ≤ Real.sqrt (P₀ : ℝ) := by
    rw [← h_half_E₀] at hf0
    exact hf0.trans h_sqrt_P₀
  have h_sqrt_pos : 0 < Real.sqrt (P₀ : ℝ) := by
    have : 0 < 256 / ε := by positivity
    exact this.trans_le h_f0_denom
  have h_f0_le : ((0 + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (P₀ : ℝ) ≤ ε / 4 := by
    have h64 : ((0 + 2 : ℕ) : ℝ) ^ 6 = 64 := by norm_num
    rw [h64]
    rw [div_le_iff₀ h_sqrt_pos]
    have h_eps_pos : 0 < ε / 4 := by positivity
    rw [← div_le_iff₀' h_eps_pos]
    have : (64 : ℝ) / (ε / 4) = 256 / ε := by
      have : ε ≠ 0 := by linarith
      field_simp
      ring
    rw [this]
    exact h_f0_denom
  have hF₀_ge4 : 4 ≤ F₀ := by
    dsimp [F₀]
    have h_exp := exp_div_ge (Real.log L) hlogL_pos
    rw [Real.exp_log hL_pos] at h_exp
    have : (4 : ℝ) ≤ Real.log L / 4 := by linarith
    exact this.trans h_exp
  have hlogQ₀ : F₀ / 2 ≤ Real.log (Q₀ : ℝ) := by
    dsimp [Q₀]
    have h_ge2 : 2 ≤ F₀ := by linarith
    have h_floor := log_floor_exp_ge F₀ h_ge2
    have : F₀ / 2 ≤ F₀ - 1 := by linarith
    exact this.trans h_floor
  have hlogQ₀_pos : 0 < Real.log (Q₀ : ℝ) := by
    have : 0 < F₀ / 2 := by linarith
    exact this.trans_le hlogQ₀
  have hP₀_le : (P₀ : ℝ) ≤ Real.exp (2 * E₀) := by
    dsimp [P₀]
    have h_ceil : (⌈Real.exp E₀⌉₊ : ℝ) < Real.exp E₀ + 1 := Nat.ceil_lt_add_one (Real.exp_pos E₀).le
    have h_one : 1 ≤ Real.exp E₀ := by
      have : Real.exp 0 ≤ Real.exp E₀ := Real.exp_le_exp.mpr (by linarith)
      rwa [Real.exp_zero] at this
    have h_two : Real.exp E₀ + 1 ≤ 2 * Real.exp E₀ := by linarith
    have h_exp_two : 2 * Real.exp E₀ ≤ Real.exp (2 * E₀) := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have : 2 * Real.exp E₀ ≤ Real.exp 1 * Real.exp E₀ := mul_le_mul_of_nonneg_right h2 (Real.exp_pos E₀).le
      rw [← Real.exp_add] at this
      have h_add : 1 + E₀ ≤ 2 * E₀ := by linarith
      exact this.trans (Real.exp_le_exp.mpr h_add)
    linarith
  have hlogP₀ : Real.log (P₀ : ℝ) ≤ 2 * E₀ := by
    have h_log := Real.log_le_log hP₀_pos hP₀_le
    rwa [Real.log_exp] at h_log
  have h_g0_div : Real.log (P₀ : ℝ) / Real.log (Q₀ : ℝ) ≤ (2 * E₀) / (F₀ / 2) := by
    have h1 : Real.log (P₀ : ℝ) / Real.log (Q₀ : ℝ) ≤ (2 * E₀) / Real.log (Q₀ : ℝ) :=
      div_le_div_of_nonneg_right hlogP₀ hlogQ₀_pos.le
    have h2 : (2 * E₀) / Real.log (Q₀ : ℝ) ≤ (2 * E₀) / (F₀ / 2) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) hlogQ₀
    exact h1.trans h2
  have h_g0_ratio : (2 * E₀) / (F₀ / 2) = 4 * kappa * (Real.log L) ^ 2 / L := by
    dsimp [E₀, F₀]
    have : Real.log L ≠ 0 := by linarith
    have : L ≠ 0 := by linarith
    field_simp
    ring
  rw [h_g0_ratio] at h_g0_div
  have h_sq := exp_div_ge_sq (Real.log L) hlogL_pos
  rw [Real.exp_log hL_pos] at h_sq
  have h_sq_div : (Real.log L) ^ 2 / L ≤ 27 / Real.log L := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 27)] at h_sq
    rw [div_le_iff₀ hL_pos]
    have h_ring : L / Real.log L * 27 = 27 / Real.log L * L := by ring
    rw [h_ring] at h_sq
    exact h_sq
  have h_step_g0 : 4 * kappa * (Real.log L) ^ 2 / L ≤ 108 * kappa / Real.log L := by
    have : 4 * kappa * (Real.log L) ^ 2 / L = (4 * kappa) * ((Real.log L) ^ 2 / L) := by ring
    rw [this]
    have h_prod := mul_le_mul_of_nonneg_left h_sq_div (by positivity : 0 ≤ 4 * kappa)
    have : (4 * kappa) * (27 / Real.log L) = 108 * kappa / Real.log L := by ring
    rwa [this] at h_prod
  have h_g0_le : 108 * kappa / Real.log L ≤ ε / 4 := by
    rw [div_le_iff₀ hlogL_pos]
    have h_pos : 0 < ε / 4 := by positivity
    rw [← div_le_iff₀' h_pos]
    have : (108 * kappa) / (ε / 4) = 432 * kappa / ε := by
      have : ε ≠ 0 := by linarith
      field_simp
      ring
    rw [this]
    exact hg0
  have h_g0_final := h_g0_div.trans (h_step_g0.trans h_g0_le)
  linarith

lemma log_P0_le_six_k_pow4_ell1 {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (hL : Real.exp 16 ≤ Real.log (h : ℝ))
    (hu : 54 * (kappa η) / 48 ≤ Real.log (Real.log (h : ℝ)))
    (k : ℝ) (hk : 2 ≤ k) :
    Real.log (P_seq η h 0 : ℝ) ≤ 6 * k ^ 4 * Real.log (Q_seq η h 0 : ℝ) := by
  set L := Real.log (h : ℝ)
  set u := Real.log L
  have hlogL : 16 ≤ u := by
    have h_log := Real.log_le_log (Real.exp_pos 16) hL
    rwa [Real.log_exp] at h_log
  have hL_pos : 0 < L := (Real.exp_pos 16).trans_le hL
  have hu_pos : 0 < u := by linarith
  have hF₀_ge4 : 4 ≤ L / u := by
    have h_exp := exp_div_ge u hu_pos
    have : (4 : ℝ) ≤ u / 4 := by linarith
    have hL_eq : Real.exp u = L := Real.exp_log hL_pos
    rw [hL_eq] at h_exp
    exact this.trans h_exp
  have hlogQ₀ : (L / u) / 2 ≤ Real.log (Q_seq η h 0 : ℝ) := by
    dsimp [Q_seq, F_seq]
    have h_ge2 : 2 ≤ L / u := by linarith
    have h_floor := log_floor_exp_ge (L / u) h_ge2
    have : (L / u) / 2 ≤ L / u - 1 := by linarith
    exact this.trans h_floor
  have hE₀_ge1 : 1 ≤ (kappa η) * u := by
    have hkap : 1 ≤ kappa η := by
      dsimp [kappa]
      have : η * (1 / 6 - η) < 1 := by
        have : η < 1 := by linarith
        have : 1 / 6 - η < 1 := by linarith
        nlinarith
      have : 1 < 200 / (η * (1 / 6 - η)) := by
        have h_pos : 0 < η * (1 / 6 - η) := by
          have : 0 < 1 / 6 - η := by linarith
          positivity
        rw [one_lt_div h_pos]
        linarith
      linarith
    have : 1 ≤ u := by linarith
    nlinarith
  have hP₀_pos : 0 < (P_seq η h 0 : ℝ) := by
    dsimp [P_seq, E_seq]
    have : 0 < Real.exp ((kappa η) * u) := Real.exp_pos _
    exact this.trans_le (Nat.le_ceil _)
  have hP₀_le : (P_seq η h 0 : ℝ) ≤ Real.exp (2 * ((kappa η) * u)) := by
    dsimp [P_seq, E_seq]
    have h_ceil : (⌈Real.exp ((kappa η) * u)⌉₊ : ℝ) < Real.exp ((kappa η) * u) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have h_one : 1 ≤ Real.exp ((kappa η) * u) := by
      have : (0 : ℝ) ≤ (kappa η) * u := by linarith [hE₀_ge1]
      have := Real.exp_le_exp.mpr this
      rwa [Real.exp_zero] at this
    have h_two : Real.exp ((kappa η) * u) + 1 ≤ 2 * Real.exp ((kappa η) * u) := by linarith
    have h_exp_two : 2 * Real.exp ((kappa η) * u) ≤ Real.exp (2 * ((kappa η) * u)) := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have : 2 * Real.exp ((kappa η) * u) ≤ Real.exp 1 * Real.exp ((kappa η) * u) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      rw [← Real.exp_add] at this
      have h_add : 1 + (kappa η) * u ≤ 2 * ((kappa η) * u) := by linarith [hE₀_ge1]
      exact this.trans (Real.exp_le_exp.mpr h_add)
    linarith
  have hlogP₀ : Real.log (P_seq η h 0 : ℝ) ≤ 2 * ((kappa η) * u) := by
    have h_log := Real.log_le_log hP₀_pos hP₀_le
    rwa [Real.log_exp] at h_log
  have h_sq := exp_div_ge_sq u hu_pos
  have hL_eq : Real.exp u = L := Real.exp_log hL_pos
  rw [hL_eq] at h_sq
  have h_sq_div : u ^ 2 / L ≤ 27 / u := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 27)] at h_sq
    rw [div_le_iff₀ hL_pos]
    have h_ring : L / u * 27 = 27 / u * L := by ring
    rw [h_ring] at h_sq
    exact h_sq
  have h_2kap : 2 * (kappa η) * (u ^ 2 / L) ≤ 48 := by
    have h_step : 2 * (kappa η) * (u ^ 2 / L) ≤ 54 * (kappa η) / u := by
      have : 2 * (kappa η) * (u ^ 2 / L) = (2 * kappa η) * (u ^ 2 / L) := by ring
      rw [this]
      have hkap_nonneg : 0 ≤ 2 * kappa η := by
        dsimp [kappa]
        have : 0 < 1 / 6 - η := by linarith
        positivity
      have h_prod := mul_le_mul_of_nonneg_left h_sq_div hkap_nonneg
      have : (2 * kappa η) * (27 / u) = 54 * (kappa η) / u := by ring
      rwa [this] at h_prod
    have h_le48 : 54 * (kappa η) / u ≤ 48 := by
      rw [div_le_iff₀ hu_pos]
      have h48_pos : 0 < (48 : ℝ) := by norm_num
      rw [← div_le_iff₀' h48_pos]
      exact hu
    exact h_step.trans h_le48
  have h_ring_ratio : 2 * ((kappa η) * u) = (2 * (kappa η) * (u ^ 2 / L)) * (L / u) := by
    have : u ≠ 0 := by linarith
    have : L ≠ 0 := by linarith
    field_simp
  have h_2kap_Lu : 2 * ((kappa η) * u) ≤ 48 * (L / u) := by
    rw [h_ring_ratio]
    have hLu_pos : 0 ≤ L / u := by positivity
    exact mul_le_mul_of_nonneg_right h_2kap hLu_pos
  have h_48_Lu : 48 * (L / u) = 96 * ((L / u) / 2) := by ring
  rw [h_48_Lu] at h_2kap_Lu
  have h_96_le : 96 * ((L / u) / 2) ≤ 96 * Real.log (Q_seq η h 0 : ℝ) :=
    mul_le_mul_of_nonneg_left hlogQ₀ (by norm_num)
  have h_k4 : 16 ≤ k ^ 4 := by
    have : (2 : ℝ) ^ 4 ≤ k ^ 4 := pow_le_pow_left₀ (by norm_num) hk 4
    norm_num at this
    exact this
  have h_96_k4 : (96 : ℝ) ≤ 6 * k ^ 4 := by linarith
  have h_logQ_pos : 0 ≤ Real.log (Q_seq η h 0 : ℝ) := by
    have : 0 < (L / u) / 2 := by positivity
    linarith [hlogQ₀]
  have h_trans1 : 96 * Real.log (Q_seq η h 0 : ℝ) ≤ 6 * k ^ 4 * Real.log (Q_seq η h 0 : ℝ) :=
    mul_le_mul_of_nonneg_right h_96_k4 h_logQ_pos
  exact hlogP₀.trans (h_2kap_Lu.trans (h_96_le.trans h_trans1))

lemma Hj_le_sqrt_P {J : ℕ} {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (h : ℕ)
    (h_E0 : 1 ≤ E_seq η h 0)
    (h_ℓ₁ : 1 ≤ Real.log (⌊Real.exp (Real.log (h : ℝ) / Real.log (Real.log (h : ℝ)))⌋₊ : ℝ))
    (hL16 : Real.exp 16 ≤ Real.log (h : ℝ))
    (hu_48 : 54 * (kappa η) / 48 ≤ Real.log (Real.log (h : ℝ)))
    (S : RangeSystem J η) (hJ : 0 < J)
    (hS_P : ∀ j, S.P j = P_seq η h j.val)
    (hS_Q : ∀ j, S.Q j = Q_seq η h j.val)
    (j : Fin J) :
    S.Hj hJ j ≤ Real.sqrt (S.P j) := by
  dsimp [RangeSystem.Hj]
  rw [hS_P j, hS_P ⟨0, hJ⟩, hS_Q ⟨0, hJ⟩]
  by_cases hj : j.val = 0
  · have hj_eq : ((j.val + 1 : ℕ) : ℝ) ^ 2 = 1 := by
      rw [hj]
      norm_num
    rw [hj_eq, one_mul]
    rw [hj]
    have hP2 : 2 ≤ (P_seq η h 0 : ℝ) := by
      have := two_le_P_seq hη0 hη h h_E0 h_ℓ₁ 0
      exact_mod_cast this
    have hQ_pos : 0 < (Q_seq η h 0 : ℝ) := pos_of_one_le_log h_ℓ₁
    have hQ_e : Real.exp 1 ≤ (Q_seq η h 0 : ℝ) := by
      have : Real.exp 1 ≤ Real.exp (Real.log (Q_seq η h 0 : ℝ)) := Real.exp_le_exp.mpr h_ℓ₁
      rwa [Real.exp_log hQ_pos] at this
    exact Hj_zero_le_sqrt_P (P_seq η h 0 : ℝ) (Q_seq η h 0 : ℝ) hP2 hQ_e η hη0 hη
  · have hj_pos : 1 ≤ j.val := by omega
    set k : ℝ := ((j.val + 1 : ℕ) : ℝ)
    have hk : 2 ≤ k := by
      dsimp [k]
      have : 2 ≤ j.val + 1 := by omega
      exact_mod_cast this
    set ℓ₁ := Real.log (Q_seq η h 0 : ℝ)
    have hP₀_pos : 0 < (P_seq η h 0 : ℝ) := by
      have : 0 < Real.exp (E_seq η h 0) := Real.exp_pos _
      exact this.trans_le (Nat.le_ceil _)
    have hP₀_le := log_P0_le_six_k_pow4_ell1 hη0 hη h hL16 hu_48 k hk
    have h_bound := bound_Ei j.val hj_pos ℓ₁ h_ℓ₁ η hη0 hη
    have hE : 100 ^ 2 * k ^ 4 * ℓ₁ / η ^ 2 ≤ E_seq η h j.val := by
      dsimp [E_seq]
      have hj0 : ¬ j.val = 0 := by omega
      simp only [hj0, ↓reduceIte]
      exact h_bound
    have hP : Real.exp (E_seq η h j.val) ≤ (P_seq η h j.val : ℝ) := Nat.le_ceil _
    exact Hj_succ_le_sqrt_P k hk ℓ₁ h_ℓ₁ (P_seq η h 0 : ℝ) (P_seq η h j.val : ℝ)
      hP₀_pos hP₀_le η hη0 hη (E_seq η h j.val) hE hP (Q_seq η h 0 : ℝ) h_ℓ₁

theorem exists_rangeSystem {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) (ε : ℝ) (hε : 0 < ε) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ β : ℝ, 3 / 4 ≤ β → β < 1 →
      ∃ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J),
        (S.Q ⟨0, hJ⟩ : ℝ) ≤ h ∧
        (∀ j, (S.Q j : ℝ) ≤ (X : ℝ) ^ β) ∧ (∀ j, (S.Q j : ℝ) ^ 4 ≤ X) ∧
        (∀ j, 2 ≤ S.Hj hJ j ∧ S.Hj hJ j ≤ Real.sqrt (S.P j)) ∧ (∀ j, 2 ≤ Real.log (S.P j)) ∧ (∀ j, 2 ≤ Real.log (Real.log (S.Q j))) ∧
        (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) ∧
        (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) ∧
        (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) ≤ ε ∧
        (∑ j : Fin J, (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j) + Real.log (S.P j) / Real.log (S.Q j))) ≤ ε := by
  have h_eta_sub : 0 < 1 / 6 - η := by linarith
  have hkap_pos : 0 < kappa η := by
    dsimp [kappa]
    positivity
  have hkap_nonneg : 0 ≤ kappa η := hkap_pos.le
  set C_h := 4 + 1 / η + 8 * (16 / ε + 1) + 8 * (Real.exp 2 + 1) + 1 / ε + 16 +
    27 * (kappa η + 1) + (2 / kappa η) * (256 / ε + 2) + 432 * kappa η / ε +
    54 * kappa η / 48 + 100
  set h₀ := ⌈Real.exp (Real.exp C_h)⌉₊ + 100
  use h₀
  intro h hh
  have h16 : 16 ≤ h := by omega
  have h_ceil_exp : ⌈Real.exp (Real.exp C_h)⌉₊ ≤ h := by omega
  set L := Real.log (h : ℝ)
  set u := Real.log L
  have hu_ge : C_h ≤ u := log_log_ge_of_ge_ceil_exp_exp C_h h h_ceil_exp
  have hu_pos : 0 < u := by
    have : (100 : ℝ) ≤ C_h := by
      dsimp [C_h]
      have : 0 ≤ 4 + 1 / η := by positivity
      have : 0 ≤ 8 * (16 / ε + 1) := by positivity
      have : 0 ≤ 8 * (Real.exp 2 + 1) := by positivity
      have : 0 ≤ 1 / ε := by positivity
      have : 0 ≤ 16 := by norm_num
      have : 0 ≤ 27 * (kappa η + 1) := by linarith [hkap_nonneg]
      have : 0 ≤ (2 / kappa η) * (256 / ε + 2) := by positivity
      have : 0 ≤ 432 * kappa η / ε := by positivity
      have : 0 ≤ 54 * kappa η / 48 := by linarith [hkap_nonneg]
      linarith
    linarith
  have hL_pos : 0 < L := by
    have : 0 < (h : ℝ) := by exact_mod_cast (by omega : 0 < h)
    have h1 : 16 ≤ (h : ℝ) := by exact_mod_cast h16
    have : (1 : ℝ) < Real.log 16 := by
      have h16' : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
      have : Real.log 16 = 4 * Real.log 2 := by
        rw [h16', Real.log_pow (2 : ℝ) 4]
        push_cast
        ring
      have hlog2 := Real.log_two_gt_d9
      linarith
    have : 1 < L := by
      have : Real.log 16 ≤ L := Real.log_le_log (by norm_num) h1
      linarith
    linarith
  have h_logL : 4 + 1 / η ≤ u := by
    have : 4 + 1 / η ≤ C_h := by
      dsimp [C_h]
      have : 0 ≤ 8 * (16 / ε + 1) := by positivity
      have : 0 ≤ 8 * (Real.exp 2 + 1) := by positivity
      have : 0 ≤ 1 / ε := by positivity
      have : 0 ≤ 16 := by norm_num
      have : 0 ≤ 27 * (kappa η + 1) := by linarith [hkap_nonneg]
      have : 0 ≤ (2 / kappa η) * (256 / ε + 2) := by positivity
      have : 0 ≤ 432 * kappa η / ε := by positivity
      have : 0 ≤ 54 * kappa η / 48 := by linarith [hkap_nonneg]
      linarith
    exact this.trans hu_ge
  have hu16 : 16 ≤ u := by
    have : (16 : ℝ) ≤ C_h := by
      dsimp [C_h]
      have : 0 ≤ 4 + 1 / η := by positivity
      have : 0 ≤ 8 * (16 / ε + 1) := by positivity
      have : 0 ≤ 8 * (Real.exp 2 + 1) := by positivity
      have : 0 ≤ 1 / ε := by positivity
      have : 0 ≤ 27 * (kappa η + 1) := by linarith [hkap_nonneg]
      have : 0 ≤ (2 / kappa η) * (256 / ε + 2) := by positivity
      have : 0 ≤ 432 * kappa η / ε := by positivity
      have : 0 ≤ 54 * kappa η / 48 := by linarith [hkap_nonneg]
      linarith
    exact this.trans hu_ge
  have hL16 : Real.exp 16 ≤ L := by
    have h_exp := Real.exp_le_exp.mpr hu16
    have hL_eq : Real.exp u = L := Real.exp_log hL_pos
    rwa [hL_eq] at h_exp
  have h_e_16 : Real.exp 1 ≤ Real.exp 16 := Real.exp_le_exp.mpr (by norm_num)
  have hL1 : Real.exp 1 ≤ L := h_e_16.trans hL16
  have hu_48 : 54 * kappa η / 48 ≤ u := by
    have : 54 * kappa η / 48 ≤ C_h := by
      dsimp [C_h]
      have : 0 ≤ 4 + 1 / η := by positivity
      have : 0 ≤ 8 * (16 / ε + 1) := by positivity
      have : 0 ≤ 8 * (Real.exp 2 + 1) := by positivity
      have : 0 ≤ 1 / ε := by positivity
      have : 0 ≤ 16 := by norm_num
      have : 0 ≤ 27 * (kappa η + 1) := by linarith [hkap_nonneg]
      have : 0 ≤ (2 / kappa η) * (256 / ε + 2) := by positivity
      have : 0 ≤ 432 * kappa η / ε := by positivity
      linarith
    exact this.trans hu_ge
  have h_u_kap : 27 * (kappa η + 1) ≤ u := by
    have : 27 * (kappa η + 1) ≤ C_h := by
      dsimp [C_h]
      have : 0 ≤ 4 + 1 / η := by positivity
      have : 0 ≤ 8 * (16 / ε + 1) := by positivity
      have : 0 ≤ 8 * (Real.exp 2 + 1) := by positivity
      have : 0 ≤ 1 / ε := by positivity
      have : 0 ≤ 16 := by norm_num
      have : 0 ≤ (2 / kappa η) * (256 / ε + 2) := by positivity
      have : 0 ≤ 432 * kappa η / ε := by positivity
      have : 0 ≤ 54 * kappa η / 48 := by linarith [hkap_nonneg]
      linarith
    exact this.trans hu_ge
  have h_EF0 : E_seq η h 0 + 1 ≤ F_seq η h 0 := by
    dsimp [E_seq, F_seq]
    have h_u_sq : u ≤ u ^ 2 := by
      have : (1 : ℝ) ≤ u := by linarith
      nlinarith
    have h_top_le : (kappa η * u + 1) * u ≤ (kappa η + 1) * u ^ 2 := by
      calc (kappa η * u + 1) * u
        _ = kappa η * u ^ 2 + u := by ring
        _ ≤ kappa η * u ^ 2 + u ^ 2 := by linarith
        _ = (kappa η + 1) * u ^ 2 := by ring
    have h_sq := exp_div_ge_sq u hu_pos
    have hL_eq : Real.exp u = L := Real.exp_log hL_pos
    rw [hL_eq] at h_sq
    have h_sq_div : u ^ 2 / L ≤ 27 / u := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 27)] at h_sq
      rw [div_le_iff₀ hL_pos]
      have h_ring : L / u * 27 = 27 / u * L := by ring
      rw [h_ring] at h_sq
      exact h_sq
    have h_kap_le : (kappa η + 1) * (u ^ 2 / L) ≤ 1 := by
      have h1 : (kappa η + 1) * (u ^ 2 / L) ≤ (kappa η + 1) * (27 / u) :=
        mul_le_mul_of_nonneg_left h_sq_div (by linarith [hkap_nonneg])
      have h2 : (kappa η + 1) * (27 / u) = 27 * (kappa η + 1) / u := by ring
      rw [h2] at h1
      have h3 : 27 * (kappa η + 1) / u ≤ 1 := by
        rw [div_le_one₀ hu_pos]
        exact h_u_kap
      exact h1.trans h3
    have h_prod_le : (kappa η + 1) * u ^ 2 ≤ L := by
      have : (kappa η + 1) * (u ^ 2 / L) * L ≤ 1 * L :=
        mul_le_mul_of_nonneg_right h_kap_le hL_pos.le
      have h_cancel : (kappa η + 1) * (u ^ 2 / L) * L = (kappa η + 1) * u ^ 2 := by
        have : L ≠ 0 := by linarith
        field_simp
      rwa [h_cancel, one_mul] at this
    have h_div_u : (kappa η * u + 1) * u / u ≤ L / u :=
      div_le_div_of_nonneg_right (h_top_le.trans h_prod_le) hu_pos.le
    have h_cancel2 : (kappa η * u + 1) * u / u = kappa η * u + 1 := by
      have : u ≠ 0 := by linarith
      field_simp
    rwa [h_cancel2] at h_div_u
  have h_E0 : 1 ≤ E_seq η h 0 := by
    dsimp [E_seq]
    have hkap : 1 ≤ kappa η := by
      dsimp [kappa]
      have : η * (1 / 6 - η) < 1 := by
        have : η < 1 := by linarith
        have : 1 / 6 - η < 1 := by linarith
        nlinarith
      have : 1 < 200 / (η * (1 / 6 - η)) := by
        have h_pos : 0 < η * (1 / 6 - η) := by
          have : 0 < 1 / 6 - η := by linarith
          positivity
        rw [one_lt_div h_pos]
        linarith
      linarith
    have : 1 ≤ u := by linarith
    nlinarith
  have h_16_eps : 16 / ε ≤ Real.log (Q_seq η h 0 : ℝ) := by
    have h_exp := exp_div_ge u hu_pos
    have hL_eq : Real.exp u = L := Real.exp_log hL_pos
    rw [hL_eq] at h_exp
    have hF_div : u / 8 ≤ (L / u) / 2 := by
      have : (u / 4) / 2 ≤ (L / u) / 2 := div_le_div_of_nonneg_right h_exp (by norm_num)
      have h_ring : (u / 4) / 2 = u / 8 := by ring
      rwa [h_ring] at this
    have h_floor := log_floor_exp_ge (L / u) (by linarith : 2 ≤ L / u)
    have : (L / u) / 2 ≤ L / u - 1 := by linarith
    have hlogQ : (L / u) / 2 ≤ Real.log (Q_seq η h 0 : ℝ) := this.trans h_floor
    have hu_16 : 16 / ε ≤ u / 8 := by
      have : 8 * (16 / ε + 1) ≤ C_h := by
        dsimp [C_h]
        have : 0 ≤ 4 + 1 / η := by positivity
        have : 0 ≤ 8 * (Real.exp 2 + 1) := by positivity
        have : 0 ≤ 1 / ε := by positivity
        have : 0 ≤ 16 := by norm_num
        have : 0 ≤ 27 * (kappa η + 1) := by linarith [hkap_nonneg]
        have : 0 ≤ (2 / kappa η) * (256 / ε + 2) := by positivity
        have : 0 ≤ 432 * kappa η / ε := by positivity
        have : 0 ≤ 54 * kappa η / 48 := by linarith [hkap_nonneg]
        linarith
      have : 8 * (16 / ε + 1) ≤ u := this.trans hu_ge
      linarith
    exact hu_16.trans (hF_div.trans hlogQ)
  have h_ℓ₁_exp2 : Real.exp 2 ≤ Real.log (Q_seq η h 0 : ℝ) := by
    have h_exp := exp_div_ge u hu_pos
    have hL_eq : Real.exp u = L := Real.exp_log hL_pos
    rw [hL_eq] at h_exp
    have hF_div : u / 8 ≤ (L / u) / 2 := by
      have : (u / 4) / 2 ≤ (L / u) / 2 := div_le_div_of_nonneg_right h_exp (by norm_num)
      have h_ring : (u / 4) / 2 = u / 8 := by ring
      rwa [h_ring] at this
    have h_floor := log_floor_exp_ge (L / u) (by linarith : 2 ≤ L / u)
    have : (L / u) / 2 ≤ L / u - 1 := by linarith
    have hlogQ : (L / u) / 2 ≤ Real.log (Q_seq η h 0 : ℝ) := this.trans h_floor
    have hu_exp2 : Real.exp 2 ≤ u / 8 := by
      have : 8 * (Real.exp 2 + 1) ≤ C_h := by
        dsimp [C_h]
        have : 0 ≤ 4 + 1 / η := by positivity
        have : 0 ≤ 8 * (16 / ε + 1) := by positivity
        have : 0 ≤ 1 / ε := by positivity
        have : 0 ≤ 16 := by norm_num
        have : 0 ≤ 27 * (kappa η + 1) := by linarith [hkap_nonneg]
        have : 0 ≤ (2 / kappa η) * (256 / ε + 2) := by positivity
        have : 0 ≤ 432 * kappa η / ε := by positivity
        have : 0 ≤ 54 * kappa η / 48 := by linarith [hkap_nonneg]
        linarith
      have : 8 * (Real.exp 2 + 1) ≤ u := this.trans hu_ge
      linarith
    exact hu_exp2.trans (hF_div.trans hlogQ)
  have h_ℓ₁ : 1 ≤ Real.log (Q_seq η h 0 : ℝ) := by
    have : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
    exact this.trans h_ℓ₁_exp2
  have hℓ₁_eps : 4 / ε ≤ 1400 * Real.log (Q_seq η h 0 : ℝ) := by
    have h1 : 4 / ε ≤ 1400 * (16 / ε) := by
      have : (4 : ℝ) / ε ≤ (1400 * 16) / ε := by
        have : (4 : ℝ) ≤ 1400 * 16 := by norm_num
        exact div_le_div_of_nonneg_right this hε.le
      have h_ring : (1400 * 16 : ℝ) / ε = 1400 * (16 / ε) := by ring
      rwa [h_ring] at this
    have h2 : 1400 * (16 / ε) ≤ 1400 * Real.log (Q_seq η h 0 : ℝ) :=
      mul_le_mul_of_nonneg_left h_16_eps (by norm_num)
    exact h1.trans h2
  have hf0 : 256 / ε ≤ Real.exp ((100 / (η * (1 / 6 - η))) * Real.log L) := by
    have h_eq : (100 / (η * (1 / 6 - η))) * Real.log L = (kappa η / 2) * u := by
      dsimp [kappa]
      ring
    rw [h_eq]
    have h_lin : 256 / ε ≤ (kappa η / 2) * u := by
      have : (2 / kappa η) * (256 / ε + 2) ≤ C_h := by
        dsimp [C_h]
        have : 0 ≤ 4 + 1 / η := by positivity
        have : 0 ≤ 8 * (16 / ε + 1) := by positivity
        have : 0 ≤ 8 * (Real.exp 2 + 1) := by positivity
        have : 0 ≤ 1 / ε := by positivity
        have : 0 ≤ 16 := by norm_num
        have : 0 ≤ 27 * (kappa η + 1) := by linarith [hkap_nonneg]
        have : 0 ≤ 432 * kappa η / ε := by positivity
        have : 0 ≤ 54 * kappa η / 48 := by linarith [hkap_nonneg]
        linarith
      have h_step : (2 / kappa η) * (256 / ε + 2) ≤ u := this.trans hu_ge
      have h_mul := mul_le_mul_of_nonneg_left h_step (by positivity : 0 ≤ kappa η / 2)
      have h_cancel : (kappa η / 2) * ((2 / kappa η) * (256 / ε + 2)) = 256 / ε + 2 := by
        have : kappa η ≠ 0 := by positivity
        field_simp
      rw [h_cancel] at h_mul
      linarith
    have h_exp_ge : (kappa η / 2) * u ≤ Real.exp ((kappa η / 2) * u) := by
      linarith [Real.add_one_le_exp ((kappa η / 2) * u)]
    exact h_lin.trans h_exp_ge
  have hg0 : 432 * (200 / (η * (1 / 6 - η))) / ε ≤ Real.log L := by
    change 432 * kappa η / ε ≤ u
    have : 432 * kappa η / ε ≤ C_h := by
      dsimp [C_h]
      have : 0 ≤ 4 + 1 / η := by positivity
      have : 0 ≤ 8 * (16 / ε + 1) := by positivity
      have : 0 ≤ 8 * (Real.exp 2 + 1) := by positivity
      have : 0 ≤ 1 / ε := by positivity
      have : 0 ≤ 16 := by norm_num
      have : 0 ≤ 27 * (kappa η + 1) := by linarith [hkap_nonneg]
      have : 0 ≤ (2 / kappa η) * (256 / ε + 2) := by positivity
      have : 0 ≤ 54 * kappa η / 48 := by linarith [hkap_nonneg]
      linarith
    exact this.trans hu_ge
  set C_X := (F_seq η h 2) ^ 2 + 100
  set X₀ := ⌈Real.exp C_X⌉₊ + 100
  use X₀
  intro X hX_ge β hβ hβ1
  have hX16 : 16 ≤ X := by omega
  have h_ceil_X : ⌈Real.exp C_X⌉₊ ≤ X := by omega
  have h_logX_ge : C_X ≤ Real.log (X : ℝ) := log_ge_of_ge_ceil_exp C_X X h_ceil_X
  have hlogX16 : 16 ≤ Real.log (X : ℝ) := by
    have : (16 : ℝ) ≤ C_X := by
      dsimp [C_X]
      have : 0 ≤ (F_seq η h 2) ^ 2 := by positivity
      linarith
    exact this.trans h_logX_ge
  have hloglogX : 1 ≤ Real.log (Real.log (X : ℝ)) := by
    have : (Real.exp 1 : ℝ) ≤ 16 := by linarith [Real.exp_one_lt_d9]
    have : Real.exp 1 ≤ Real.log (X : ℝ) := this.trans hlogX16
    have h_log := Real.log_le_log (Real.exp_pos 1) this
    rwa [Real.log_exp] at h_log
  have ht_ge : F_seq η h 2 ≤ Real.sqrt (Real.log (X : ℝ)) := by
    have hF_pos : 0 ≤ F_seq η h 2 := by
      dsimp [F_seq]
      positivity
    rw [Real.le_sqrt hF_pos (by linarith)]
    have : (F_seq η h 2) ^ 2 ≤ C_X := by dsimp [C_X]; linarith
    exact this.trans h_logX_ge
  obtain ⟨J, hJ3, h_F_prev, h_F_gt⟩ := exists_J η hη0 hη h h_ℓ₁ (Real.sqrt (Real.log (X : ℝ))) ht_ge
  have hJ : 0 < J := by omega
  have h_two_P : ∀ j : Fin J, 2 ≤ P_seq η h j.val := fun j =>
    two_le_P_seq hη0 hη h h_E0 h_ℓ₁ j.val
  have h_P_Q : ∀ j : Fin J, P_seq η h j.val ≤ Q_seq η h j.val := fun j =>
    P_seq_le_Q_seq hη0 hη h h_EF0 h_E0 h_ℓ₁ j.val
  have h_c2 : ∀ (j i : Fin J), i.val + 1 = j.val →
      Real.log (Real.log (Q_seq η h j.val : ℝ)) / (Real.log (P_seq η h i.val : ℝ) - 1) ≤
        η / (4 * ((j.val + 1 : ℕ) : ℝ) ^ 2) := fun j i hij =>
    cond2_seq hη0 hη h h16 h_logL h_ℓ₁ j.val i.val hij
  have h_c3 : ∀ (j i : Fin J), i.val + 1 = j.val →
      (8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (Q_seq η h i.val : ℝ) + 16 * Real.log ((j.val + 1 : ℕ) : ℝ) ≤
        Real.log (P_seq η h j.val : ℝ) := fun j i hij =>
    cond3_seq hη0 hη h h_ℓ₁ j.val i.val hij
  set S : RangeSystem J η := makeRangeSystem h J h_two_P h_P_Q h_c2 h_c3
  have hS_P : ∀ j : Fin J, S.P j = P_seq η h j.val := fun _ => rfl
  have hS_Q : ∀ j : Fin J, S.Q j = Q_seq η h j.val := fun _ => rfl
  have h_goal1 : (S.Q ⟨0, hJ⟩ : ℝ) ≤ h := by
    calc (S.Q ⟨0, hJ⟩ : ℝ)
      _ = (Q_seq η h 0 : ℝ) := rfl
      _ ≤ (h : ℝ) := Q_zero_le_h η h h16
  have h_goal7 : ∀ j : Fin J, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) := by
    intro j
    have hj_val : j.val ≤ J - 1 := by omega
    have hQ_mono := Q_seq_mono hη0 hη h h_EF0 h_E0 h_ℓ₁ hj_val
    have hQ_floor : (Q_seq η h (J - 1) : ℝ) ≤ Real.exp (F_seq η h (J - 1)) :=
      Nat.floor_le (Real.exp_pos _).le
    have hF_exp : Real.exp (F_seq η h (J - 1)) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) :=
      Real.exp_le_exp.mpr h_F_prev
    calc (S.Q j : ℝ)
      _ = (Q_seq η h j.val : ℝ) := rfl
      _ ≤ (Q_seq η h (J - 1) : ℝ) := by exact_mod_cast hQ_mono
      _ ≤ Real.exp (F_seq η h (J - 1)) := hQ_floor
      _ ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) := hF_exp
  have h_goal2 : ∀ j : Fin J, (S.Q j : ℝ) ≤ (X : ℝ) ^ β := by
    intro j
    have h7 := h_goal7 j
    have h_beta := X_pow_beta X hlogX16 β hβ
    exact h7.trans h_beta
  have h_goal3 : ∀ j : Fin J, (S.Q j : ℝ) ^ 4 ≤ X := by
    intro j
    have h7 := h_goal7 j
    have h_nonneg : 0 ≤ (S.Q j : ℝ) := by positivity
    have h4_pow : (S.Q j : ℝ) ^ 4 ≤ (Real.exp (Real.sqrt (Real.log (X : ℝ)))) ^ 4 :=
      pow_le_pow_left₀ h_nonneg h7 4
    have h4_X := X_pow_4 X hlogX16
    exact h4_pow.trans h4_X
  have hQ_pos : 0 < (Q_seq η h 0 : ℝ) := pos_of_one_le_log h_ℓ₁
  have hlogQ0_le_L : Real.log (Q_seq η h 0 : ℝ) ≤ L := by
    have : (Q_seq η h 0 : ℝ) ≤ (h : ℝ) := Q_zero_le_h η h h16
    have h_log := Real.log_le_log hQ_pos this
    exact h_log
  have hP0_exp : Real.exp ((200 / (η * (1 / 6 - η))) * Real.log L) ≤ (P_seq η h 0 : ℝ) := by
    dsimp [P_seq, E_seq, kappa]
    exact Nat.le_ceil _
  have hL_two : 1 / (1 / 2 : ℝ) ≤ L := by
    have : 1 / (1 / 2 : ℝ) = 2 := by norm_num
    rw [this]
    have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    exact this.trans hL1
  have h_cond9_half := cond9_le L hL1 η hη0 hη (Q_seq η h 0 : ℝ) (P_seq η h 0 : ℝ)
    hlogQ0_le_L (by linarith) hP0_exp (1 / 2) (by norm_num) hL_two
  have hA_pos : 0 < (Real.log (Q_seq η h 0 : ℝ)) ^ (1 / 3 : ℝ) := by
    have : 0 < Real.log (Q_seq η h 0 : ℝ) := by linarith
    positivity
  have hB_pos : 0 < (P_seq η h 0 : ℝ) ^ (1 / 6 - η) := by
    have : 0 < (P_seq η h 0 : ℝ) := by
      have : 2 ≤ P_seq η h 0 := two_le_P_seq hη0 hη h h_E0 h_ℓ₁ 0
      exact_mod_cast (by omega : 0 < P_seq η h 0)
    positivity
  have h_two_le_C : 2 ≤ (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) / (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) := by
    change 2 ≤ (P_seq η h 0 : ℝ) ^ (1 / 6 - η) / (Real.log (Q_seq η h 0 : ℝ)) ^ (1 / 3 : ℝ)
    rw [div_le_iff₀ hB_pos] at h_cond9_half
    have h1 : 2 * (Real.log (Q_seq η h 0 : ℝ)) ^ (1 / 3 : ℝ) ≤ (P_seq η h 0 : ℝ) ^ (1 / 6 - η) := by linarith
    rwa [le_div_iff₀ hA_pos]
  have h_goal4 : ∀ j : Fin J, 2 ≤ S.Hj hJ j ∧ S.Hj hJ j ≤ Real.sqrt (S.P j) := by
    intro j
    refine ⟨two_le_Hj S hJ j h_two_le_C, ?_⟩
    exact Hj_le_sqrt_P hη0 hη h h_E0 h_ℓ₁ hL16 hu_48 S hJ hS_P hS_Q j
  have h_goal5 : ∀ j : Fin J, 2 ≤ Real.log (S.P j) := by
    intro j
    rw [hS_P j]
    exact two_le_log_P_seq hη0 hη h h_logL h_ℓ₁ j.val
  have h_goal6 : ∀ j : Fin J, 2 ≤ Real.log (Real.log (S.Q j)) := by
    intro j
    rw [hS_Q j]
    exact two_le_log_log_Q_seq hη0 hη h h_EF0 h_E0 h_logL h_ℓ₁_exp2 j.val
  have h_sub_add : J - 1 + 1 = J := by omega
  have h_cond2_raw := cond2_succ hη0 hη h h_ℓ₁ (J - 1) (by omega)
  dsimp only at h_cond2_raw
  rw [h_sub_add] at h_cond2_raw
  have h_bound := J_P_bound η hη0 hη J hJ3 X hX16 hloglogX (F_seq η h J) (E_seq η h (J - 1)) h_cond2_raw h_F_gt
  have hP_ceil : Real.exp (E_seq η h (J - 1)) ≤ (P_seq η h (J - 1) : ℝ) := Nat.le_ceil _
  have h_goal8 : Real.log (X : ℝ) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) := by
    rw [hS_P ⟨J - 1, by omega⟩]
    exact h_bound.trans hP_ceil
  have hL_eps : 1 / ε ≤ L := by
    have : 1 / ε ≤ C_h := by
      dsimp [C_h]
      have : 0 ≤ 4 + 1 / η := by positivity
      have : 0 ≤ 8 * (16 / ε + 1) := by positivity
      have : 0 ≤ 8 * (Real.exp 2 + 1) := by positivity
      have : 0 ≤ 16 := by norm_num
      have : 0 ≤ 27 * (kappa η + 1) := by linarith [hkap_nonneg]
      have : 0 ≤ (2 / kappa η) * (256 / ε + 2) := by positivity
      have : 0 ≤ 432 * kappa η / ε := by positivity
      have : 0 ≤ 54 * kappa η / 48 := by linarith [hkap_nonneg]
      linarith
    have : 1 / ε ≤ u := this.trans hu_ge
    have h_exp : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hL_eq : Real.exp u = L := Real.exp_log hL_pos
    rw [hL_eq] at h_exp
    linarith
  have h_goal9 : (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) ≤ ε := by
    rw [hS_Q ⟨0, hJ⟩, hS_P ⟨0, hJ⟩]
    exact cond9_le L hL1 η hη0 hη (Q_seq η h 0 : ℝ) (P_seq η h 0 : ℝ)
      hlogQ0_le_L (by linarith) hP0_exp ε hε hL_eps
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 := ⟨J - 1, by omega⟩
  set f : Fin (n + 1) → ℝ := fun j => ((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j)
  set g : Fin (n + 1) → ℝ := fun j => Real.log (S.P j) / Real.log (S.Q j)
  have h0 : f 0 + g 0 ≤ ε / 2 := by
    dsimp [f, g]
    rw [hS_P 0, hS_Q 0]
    exact base_f_g_bound η ε L hη0 hη hε hL16 hf0 hg0
  have hf : ∑ i : Fin n, f i.succ ≤ ε / 4 := by
    apply sum_piece3 n f ε hε
    intro i
    dsimp [f]
    rw [hS_P i.succ]
    set m := i.val
    have hm_eq : i.succ.val = m + 1 := rfl
    rw [hm_eq]
    set k : ℝ := ((m + 1 + 1 : ℕ) : ℝ)
    set E : ℝ := 100 ^ (m + 1 + 1) * k ^ (4 * (m + 1 + 1)) * (Real.log (Q_seq η h 0 : ℝ)) ^ (m + 1) / η ^ (m + 1 + 1)
    have hE_pos : 0 < E := by
      dsimp [E]
      have : 0 < 100 ^ (m + 1 + 1) := by positivity
      have : 0 < k ^ (4 * (m + 1 + 1)) := by positivity
      have : 0 < (Real.log (Q_seq η h 0 : ℝ)) ^ (m + 1) := by positivity
      have : 0 < η ^ (m + 1 + 1) := by positivity
      positivity
    have h_half_E_pos : 0 < E / 2 := by linarith
    have h_exp_half : E / 2 ≤ Real.exp (E / 2) := by linarith [Real.add_one_le_exp (E / 2)]
    have h_exp_eq : Real.exp (E / 2) = Real.sqrt (Real.exp E) := by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
      ring_nf
    have hE_eq : E_seq η h (m + 1) = E := rfl
    have h_sqrt_exp : Real.sqrt (Real.exp E) ≤ Real.sqrt (P_seq η h (m + 1) : ℝ) := by
      rw [← hE_eq]
      exact Real.sqrt_le_sqrt (Nat.le_ceil _)
    have h_denom : E / 2 ≤ Real.sqrt (P_seq η h (m + 1) : ℝ) :=
      h_exp_half.trans (h_exp_eq.trans_le h_sqrt_exp)
    have h_div : ((m + 1 + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (P_seq η h (m + 1) : ℝ) ≤ ((m + 1 + 2 : ℕ) : ℝ) ^ 6 / (E / 2) :=
      div_le_div_of_nonneg_left (by positivity) h_half_E_pos h_denom
    have h_bound := f_succ_bound m ε (Real.log (Q_seq η h 0 : ℝ)) η hε hη0 hη h_ℓ₁ hℓ₁_eps
    exact h_div.trans h_bound
  have hg : ∑ i : Fin n, g i.succ ≤ ε / 4 := by
    apply sum_piece4 n g (Real.log (Q_seq η h 0 : ℝ)) ε hε h_16_eps
    intro i
    dsimp [g]
    rw [hS_P i.succ, hS_Q i.succ]
    have hm_eq : i.succ.val = i.val + 1 := rfl
    rw [hm_eq]
    have h_g_bound := g_succ_bound i.val (Real.log (Q_seq η h 0 : ℝ)) η hη0 hη h_ℓ₁
    have hE_eq : E_seq η h (i.val + 1) =
        100 ^ (i.val + 1 + 1) * ((i.val + 1 + 1 : ℕ) : ℝ) ^ (4 * (i.val + 1 + 1)) *
          (Real.log (Q_seq η h 0 : ℝ)) ^ (i.val + 1) / η ^ (i.val + 1 + 1) := rfl
    have hF_eq : F_seq η h (i.val + 1) =
        100 ^ (i.val + 1 + 1) * ((i.val + 1 + 1 : ℕ) : ℝ) ^ (4 * (i.val + 1 + 1) + 2) *
          (Real.log (Q_seq η h 0 : ℝ)) ^ (i.val + 1 + 1) / η ^ (i.val + 1 + 1) := rfl
    dsimp [P_seq, Q_seq]
    rw [hE_eq, hF_eq]
    exact h_g_bound
  have h_goal10 : (∑ j : Fin (n + 1), (((j.val + 2 : ℕ) : ℝ) ^ 6 / Real.sqrt (S.P j) + Real.log (S.P j) / Real.log (S.Q j))) ≤ ε :=
    sum_split_Fin f g ε h0 hf hg
  refine ⟨n + 1, S, hJ, h_goal1, h_goal2, h_goal3, h_goal4, h_goal5, h_goal6, h_goal7, h_goal8, h_goal9, h_goal10⟩

end Erdos1201.MR

