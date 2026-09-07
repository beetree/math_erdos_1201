/-
The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.MR.Vinogradov.MeanValueTheorem
import Erdos1201.MR.Vinogradov.HolderReduction
import Erdos1201.MR.Vinogradov.LinearBilinearSum
import Erdos1201.MR.Vinogradov.TaylorReduction
import Erdos1201.MR.Vinogradov.CurveCounts

/-!
# Vinogradov Bilinear Exponential Sum Estimate (Tao Theorem 11)

This module proves Tao's Theorem 11 (`bilinearEstimate`), completing the assembly of the
bilinear estimate from:
1. The Hölder reduction to box sums (`HolderReduction.lean`),
2. The coordinatewise single-variable bounds (`LinearBilinearSum.lean`),
3. The Vinogradov mean value theorem bound for `jnorm` (`MeanValueTheorem.lean`).
-/

noncomputable section

namespace Erdos1201.MR.Vinogradov

open scoped BigOperators

/-! ### Part 1: Identification of Bilinear Sums -/

lemma bilinearForm_momentCurve (k : ℕ) (α : Fin k → ℝ) (a b : ℕ) :
    bilinearForm k α (momentCurve k (a : ℤ)) (momentCurve k (b : ℤ)) =
    ∑ j : Fin k, α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1) := by
  dsimp [bilinearForm, momentCurve]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  rfl

lemma Icc_int_eq_map (M : ℕ) :
    Finset.Icc (1 : ℤ) (M : ℤ) = (Finset.Icc 1 M).map ⟨(↑), Nat.cast_injective⟩ := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · intro hx
    refine ⟨x.toNat, ?_, ?_⟩
    · have : 0 ≤ x := by linarith [hx.1]
      omega
    · have : 0 ≤ x := by linarith [hx.1]
      exact Int.toNat_of_nonneg this
  · rintro ⟨n, hn, rfl⟩
    constructor <;> omega

lemma sum_Icc_nat_to_int {α : Type*} [AddCommMonoid α] (M : ℕ) (f : ℤ → α) :
    ∑ a ∈ Finset.Icc (1 : ℤ) M, f a = ∑ a ∈ Finset.Icc (1 : ℕ) M, f a := by
  rw [Icc_int_eq_map, Finset.sum_map]
  rfl

lemma bilinearSum_eq (k M : ℕ) (α : Fin k → ℝ) :
    (1 / (M : ℂ) ^ 2) * ∑ a ∈ Finset.Icc (1 : ℕ) M, ∑ b ∈ Finset.Icc (1 : ℕ) M,
      Complex.exp (2 * Real.pi * Complex.I * (∑ j : Fin k, α j * (a : ℝ) ^ (j.val + 1) * (b : ℝ) ^ (j.val + 1))) =
    bilinearSum k M α := by
  dsimp [bilinearSum]
  rw [sum_Icc_nat_to_int]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [sum_Icc_nat_to_int]
  apply Finset.sum_congr rfl
  intro b hb
  rw [bilinearForm_momentCurve]

/-! ### Part 2: Coordinatewise Factorization of Box Sums -/

lemma exp_bilinearForm (k : ℕ) (α : Fin k → ℝ) (x y : Fin k → ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * (bilinearForm k α x y : ℂ)) =
    ∏ j : Fin k, Complex.exp (2 * Real.pi * Complex.I * (α j * (x j : ℝ) * (y j : ℝ) : ℂ)) := by
  dsimp [bilinearForm]
  push_cast
  rw [Finset.mul_sum, Complex.exp_sum]

lemma sum_y_box_exp (k ℓ M : ℕ) (α : Fin k → ℝ) (x : Fin k → ℤ) :
    (∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * (bilinearForm k α x y : ℂ))) =
    ∏ j : Fin k, ∑ y ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
      Complex.exp (2 * Real.pi * Complex.I * (α j * (x j : ℝ) * (y : ℝ) : ℂ)) := by
  have h_exp : (∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * (bilinearForm k α x y : ℂ))) =
      ∑ y ∈ box k ℓ M, ∏ j : Fin k, Complex.exp (2 * Real.pi * Complex.I * (α j * (x j : ℝ) * (y j : ℝ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro y _
    exact exp_bilinearForm k α x y
  rw [h_exp]
  dsimp [box]
  exact (Finset.prod_univ_sum
    (fun j : Fin k => Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)))
    (fun j y => Complex.exp (2 * Real.pi * Complex.I * (α j * (x j : ℝ) * (y : ℝ) : ℂ)))).symm

lemma sum_box_exp_factor (k ℓ M : ℕ) (α : Fin k → ℝ) :
    (∑ x ∈ box k ℓ M, ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * (bilinearForm k α x y : ℂ))‖) =
    ∏ j : Fin k, ∑ x ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
      ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
        Complex.exp (2 * Real.pi * Complex.I * (α j * (x : ℝ) * (y : ℝ) : ℂ))‖ := by
  have h_inner : ∀ x ∈ box k ℓ M,
      ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * (bilinearForm k α x y : ℂ))‖ =
      ∏ j : Fin k, ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
        Complex.exp (2 * Real.pi * Complex.I * (α j * (x j : ℝ) * (y : ℝ) : ℂ))‖ := by
    intro x _
    rw [sum_y_box_exp, norm_prod]
  have h_rewrite : (∑ x ∈ box k ℓ M, ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * (bilinearForm k α x y : ℂ))‖) =
      ∑ x ∈ box k ℓ M, ∏ j : Fin k, ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
        Complex.exp (2 * Real.pi * Complex.I * (α j * (x j : ℝ) * (y : ℝ) : ℂ))‖ :=
    Finset.sum_congr rfl h_inner
  rw [h_rewrite]
  dsimp [box]
  exact (Finset.prod_univ_sum
    (fun j : Fin k => Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)))
    (fun j x => ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
      Complex.exp (2 * Real.pi * Complex.I * (α j * (x : ℝ) * (y : ℝ) : ℂ))‖)).symm

/-! ### Part 3: Coordinatewise Bounds -/

lemma sum_norm_sum_exp_mul_trivial (M ℓ j : ℕ) (α : ℝ) (hM : 2 ≤ M) (hℓ : 1 ≤ ℓ) :
    let L := ℓ * M ^ (j + 1)
    (∑ x ∈ Finset.Icc (-(L : ℤ)) L,
        ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖) ≤
      9 * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j + 1)) := by
  intro L
  have hL1 : 1 ≤ L := by
    dsimp [L]
    have : 1 ≤ M ^ (j + 1) := one_le_pow₀ (by omega)
    nlinarith
  have h_inner : ∀ x ∈ Finset.Icc (-(L : ℤ)) L,
      ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖ ≤ 2 * (L : ℝ) + 1 := by
    intro x _
    have h_card : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
      rw [Int.card_Icc]
      omega
    calc ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖
      _ ≤ ∑ y ∈ Finset.Icc (-(L : ℤ)) L, ‖Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖ :=
        norm_sum_le _ _
      _ = ∑ y ∈ Finset.Icc (-(L : ℤ)) L, (1 : ℝ) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        have : (2 * Real.pi * Complex.I * (α * x * y) : ℂ) =
            (2 * Real.pi * (α * x * y) : ℝ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I]
      _ = 2 * (L : ℝ) + 1 := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one, h_card]
        push_cast
        rfl
  have h_sum_le : (∑ x ∈ Finset.Icc (-(L : ℤ)) L,
        ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖) ≤
      (2 * (L : ℝ) + 1) * (2 * (L : ℝ) + 1) := by
    calc ∑ x ∈ Finset.Icc (-(L : ℤ)) L, ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖
      _ ≤ ∑ x ∈ Finset.Icc (-(L : ℤ)) L, (2 * (L : ℝ) + 1) := Finset.sum_le_sum h_inner
      _ = (2 * (L : ℝ) + 1) * (2 * (L : ℝ) + 1) := by
        have h_card : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
          rw [Int.card_Icc]
          omega
        simp only [Finset.sum_const, nsmul_eq_mul, h_card]
        push_cast
        ring
  have h_2L1 : 2 * (L : ℝ) + 1 ≤ 3 * (L : ℝ) := by
    have : 1 ≤ (L : ℝ) := by exact_mod_cast hL1
    linarith
  have h_prod_le : (2 * (L : ℝ) + 1) * (2 * (L : ℝ) + 1) ≤ (3 * (L : ℝ)) * (3 * (L : ℝ)) := by
    have : 0 ≤ 2 * (L : ℝ) + 1 := by positivity
    nlinarith
  refine h_sum_le.trans ?_
  refine h_prod_le.trans ?_
  have hL_eq : (L : ℝ) = (ℓ : ℝ) * (M : ℝ) ^ (j + 1) := by
    dsimp [L]
    push_cast
    rfl
  rw [hL_eq]
  have : (3 * ((ℓ : ℝ) * (M : ℝ) ^ (j + 1))) * (3 * ((ℓ : ℝ) * (M : ℝ) ^ (j + 1))) =
      9 * (ℓ : ℝ) ^ 2 * ((M : ℝ) ^ (j + 1)) ^ 2 := by ring
  rw [this]
  have h_pow_sq : ((M : ℝ) ^ (j + 1)) ^ 2 = (M : ℝ) ^ (2 * (j + 1)) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [h_pow_sq]

lemma exp_neg_mul_one_add_mul_le (c₀ x : ℝ) (hc₀ : 0 < c₀) (hx : 0 ≤ x) :
    Real.exp (-x) * (1 + (2 / c₀) * x) ≤ 1 + 2 / c₀ := by
  have h1 : 1 + (2 / c₀) * x ≤ (1 + 2 / c₀) * (1 + x) := by
    have : (1 + 2 / c₀) * (1 + x) = 1 + (2 / c₀) * x + (x + (2 / c₀)) := by ring
    have hx_c : 0 ≤ x + 2 / c₀ := by positivity
    linarith
  have h2 : 1 + x ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  have h_exp_pos : 0 < Real.exp x := Real.exp_pos x
  have h_comb : 1 + (2 / c₀) * x ≤ (1 + 2 / c₀) * Real.exp x := by
    calc 1 + (2 / c₀) * x ≤ (1 + 2 / c₀) * (1 + x) := h1
      _ ≤ (1 + 2 / c₀) * Real.exp x := by
        refine mul_le_mul_of_nonneg_left h2 ?_
        positivity
  rw [Real.exp_neg]
  rw [mul_comm, ← div_eq_mul_inv]
  exact (div_le_iff₀ h_exp_pos).mpr h_comb

lemma absorb_log_M (M m : ℕ) (c₀ : ℝ) (hM : 2 ≤ M) (_hm : 1 ≤ m) (hc₀ : 0 < c₀) :
    (M : ℝ) ^ (-c₀ * (m : ℝ)) * (1 + (m : ℝ) * Real.log (M : ℝ)) ≤
      (1 + 2 / c₀) * (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) := by
  have hM_pos : 0 < (M : ℝ) := by positivity
  set x := (c₀ / 2) * (m : ℝ) * Real.log (M : ℝ) with hx_def
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    have : 1 ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
    have : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg this
    positivity
  have h_exp_x : (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) = Real.exp (-x) := by
    rw [Real.rpow_def_of_pos hM_pos]
    congr 1
    dsimp [x]
    ring
  have h_split : (M : ℝ) ^ (-c₀ * (m : ℝ)) =
      (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) * (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) := by
    rw [← Real.rpow_add hM_pos]
    congr 1
    ring
  rw [h_split]
  have h_reassoc : (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) * (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) *
      (1 + (m : ℝ) * Real.log (M : ℝ)) =
      (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) * ((M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) * (1 + (m : ℝ) * Real.log (M : ℝ))) := by ring
  rw [h_reassoc]
  have h_term2 : (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) * (1 + (m : ℝ) * Real.log (M : ℝ)) ≤ 1 + 2 / c₀ := by
    rw [h_exp_x]
    have h_log_eq : (m : ℝ) * Real.log (M : ℝ) = (2 / c₀) * x := by
      dsimp [x]
      field_simp
    rw [h_log_eq]
    exact exp_neg_mul_one_add_mul_le c₀ x hc₀ hx_nonneg
  calc (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) * ((M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) * (1 + (m : ℝ) * Real.log (M : ℝ)))
    _ ≤ (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) * (1 + 2 / c₀) := by
      refine mul_le_mul_of_nonneg_left h_term2 ?_
      positivity
    _ = (1 + 2 / c₀) * (M : ℝ) ^ (-(c₀ / 2) * (m : ℝ)) := by ring

/-! ### Part 4: Combinatorial Sums and Power Identities -/

lemma nat_div_two_succ_succ (n : ℕ) :
    (n + 1) * (n + 2) / 2 = (n + 1) + n * (n + 1) / 2 := by
  have : (n + 1) * (n + 2) = n * (n + 1) + (n + 1) * 2 := by
    rw [mul_add, mul_comm (n + 1) n]
  rw [this, Nat.add_mul_div_right _ _ (by norm_num : 0 < 2)]
  omega

lemma sum_pos_finset_ge (S : Finset ℕ) (hS : ∀ x ∈ S, 1 ≤ x) :
    S.card * (S.card + 1) / 2 ≤ ∑ x ∈ S, x := by
  induction' hn : S.card using Nat.strong_induction_on with n ih generalizing S
  rcases n with _|n
  · have : S = ∅ := Finset.card_eq_zero.mp hn
    subst this
    simp
  · have h_ne : S.Nonempty := Finset.card_pos.mp (hn.symm ▸ Nat.succ_pos n)
    let m := S.max' h_ne
    have hm : m ∈ S := Finset.max'_mem S h_ne
    let S' := S.erase m
    have hS'_card : S'.card = n := by
      rw [Finset.card_erase_of_mem hm, hn]
      rfl
    have hm_gt : ∀ x ∈ S', x < m := fun x hx =>
      Finset.mem_erase.mp hx |>.1.lt_of_le (Finset.le_max' S x (Finset.mem_erase.mp hx |>.2))
    have hS'_sub : S' ⊆ Finset.Ico 1 m := by
      intro x hx
      rw [Finset.mem_Ico]
      exact ⟨hS x (Finset.mem_of_mem_erase hx), hm_gt x hx⟩
    have hS'_le := Finset.card_le_card hS'_sub
    rw [Nat.card_Ico] at hS'_le
    have hm_ge1 : 1 ≤ m := hS m hm
    have : n ≤ m - 1 := hS'_card ▸ hS'_le
    have hm_ge : n + 1 ≤ m := by omega
    have hS'_pos : ∀ x ∈ S', 1 ≤ x := fun x hx => hS x (Finset.mem_of_mem_erase hx)
    have h_ih := ih n (Nat.lt_succ_self n) S' hS'_pos hS'_card
    have h_sum : ∑ x ∈ S, x = m + ∑ x ∈ S', x := by
      rw [← Finset.add_sum_erase S _ hm]
    rw [h_sum]
    have h_split : (n + 1) * (n + 1 + 1) / 2 = (n + 1) + n * (n + 1) / 2 := by
      have : n + 1 + 1 = n + 2 := rfl
      rw [this]
      exact nat_div_two_succ_succ n
    rw [h_split]
    exact add_le_add hm_ge h_ih

lemma sum_val_succ_ge {k : ℕ} (s : Finset (Fin k)) :
    s.card * (s.card + 1) / 2 ≤ ∑ j ∈ s, (j.val + 1) := by
  let S := s.image (fun j => j.val + 1)
  have h_inj : ∀ j₁ ∈ s, ∀ j₂ ∈ s, j₁.val + 1 = j₂.val + 1 → j₁ = j₂ := by
    intro j₁ _ j₂ _ h
    ext
    omega
  have hS_card : S.card = s.card := Finset.card_image_of_injOn h_inj
  have hS_pos : ∀ x ∈ S, 1 ≤ x := by
    intro x hx
    simp only [Finset.mem_image, S] at hx
    rcases hx with ⟨j, _, rfl⟩
    omega
  have h_bound := sum_pos_finset_ge S hS_pos
  rw [hS_card] at h_bound
  have h_sum : ∑ x ∈ S, x = ∑ j ∈ s, (j.val + 1) := by
    rw [Finset.sum_image h_inj]
  rwa [h_sum] at h_bound

lemma sum_val_succ_ge_real {k : ℕ} (s : Finset (Fin k)) :
    (s.card : ℝ) ^ 2 / 2 ≤ ∑ j ∈ s, ((j.val : ℝ) + 1) := by
  have h := sum_val_succ_ge s
  have h_even : Even (s.card * (s.card + 1)) := Nat.even_mul_succ_self s.card
  have h_div_two : ((s.card * (s.card + 1) / 2 : ℕ) : ℝ) = (s.card : ℝ) * ((s.card : ℝ) + 1) / 2 := by
    have h_eq : 2 * (s.card * (s.card + 1) / 2) = s.card * (s.card + 1) :=
      Nat.two_mul_div_two_of_even h_even
    have h_cast2 : 2 * ((s.card * (s.card + 1) / 2 : ℕ) : ℝ) = (s.card : ℝ) * ((s.card : ℝ) + 1) := by
      have : ((2 * (s.card * (s.card + 1) / 2) : ℕ) : ℝ) = ((s.card * (s.card + 1) : ℕ) : ℝ) := by
        rw [h_eq]
      push_cast at this
      exact this
    linarith
  have h_sq : (s.card : ℝ) ^ 2 / 2 ≤ ((s.card * (s.card + 1) / 2 : ℕ) : ℝ) := by
    rw [h_div_two]
    have : (s.card : ℝ) ^ 2 ≤ (s.card : ℝ) * ((s.card : ℝ) + 1) := by
      have : (s.card : ℝ) * (s.card : ℝ) ≤ (s.card : ℝ) * ((s.card : ℝ) + 1) := by
        nlinarith
      linarith [show (s.card : ℝ) ^ 2 = (s.card : ℝ) * (s.card : ℝ) by ring]
    linarith
  have h_cast : ((s.card * (s.card + 1) / 2 : ℕ) : ℝ) ≤ ∑ j ∈ s, ((j.val : ℝ) + 1) := by
    have h1 : ((s.card * (s.card + 1) / 2 : ℕ) : ℝ) ≤ ((∑ j ∈ s, (j.val + 1) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [Nat.cast_sum] at h1
    have h_congr : (∑ x ∈ s, ((x.val + 1 : ℕ) : ℝ)) = ∑ j ∈ s, ((j.val : ℝ) + 1) := by
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      rfl
    rwa [h_congr] at h1
  exact h_sq.trans h_cast

lemma sum_univ_succ (k : ℕ) :
    ∑ j : Fin k, (j.val + 1) = k * (k + 1) / 2 := by
  induction' k with k ih
  · simp
  · rw [Fin.sum_univ_castSucc]
    have h_cast : (∑ i : Fin k, (i.castSucc.val + 1)) = ∑ i : Fin k, (i.val + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.val_castSucc]
    have h_last : ((Fin.last k).val + 1) = k + 1 := by simp
    rw [h_cast, h_last, ih]
    have : (k + 1) * (k + 1 + 1) / 2 = (k + 1) + k * (k + 1) / 2 := by
      have : k + 1 + 1 = k + 2 := rfl
      rw [this]
      exact nat_div_two_succ_succ k
    rw [this]
    omega

lemma prod_M_pow_eq (k M : ℕ) :
    ∏ j : Fin k, (M : ℝ) ^ (2 * (j.val + 1)) = (M : ℝ) ^ (k * (k + 1)) := by
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.mul_sum, sum_univ_succ]
  have h_even : Even (k * (k + 1)) := Nat.even_mul_succ_self k
  exact Nat.two_mul_div_two_of_even h_even

lemma J_sq_cancel (k ℓ M : ℕ) (hM : 1 ≤ M) :
    (M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) ^ 2 * (M : ℝ) ^ (k * (k + 1)) =
      (jnorm k ℓ M) ^ 2 := by
  have hM_pos : 0 < (M : ℝ) := by positivity
  rw [J_eq_rpow_mul_jnorm k ℓ M hM]
  rw [mul_pow]
  have h_rpow_sq : ((M : ℝ) ^ (2 * (ℓ : ℝ) - (k * (k + 1) / 2 : ℝ))) ^ 2 =
      (M : ℝ) ^ (4 * (ℓ : ℝ) - (k * (k + 1) : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM_pos.le]
    congr 1
    push_cast
    ring
  rw [h_rpow_sq]
  have h_zpow : (M : ℝ) ^ (-(4 * ℓ : ℤ)) = (M : ℝ) ^ (-(4 * (ℓ : ℝ))) := by
    rw [zpow_neg]
    have : (4 * ℓ : ℤ) = ((4 * ℓ : ℕ) : ℤ) := by omega
    rw [this, zpow_natCast, ← Real.rpow_natCast, Real.rpow_neg hM_pos.le]
    congr 1
    push_cast
    rfl
  rw [h_zpow]
  have h_nat_rpow : (M : ℝ) ^ (k * (k + 1)) = (M : ℝ) ^ ((k * (k + 1) : ℕ) : ℝ) :=
    (Real.rpow_natCast (M : ℝ) (k * (k + 1))).symm
  rw [h_nat_rpow]
  push_cast
  have h_reassoc : (M : ℝ) ^ (-(4 * (ℓ : ℝ))) * ((M : ℝ) ^ (4 * (ℓ : ℝ) - ((k : ℝ) * ((k : ℝ) + 1))) * (jnorm k ℓ M) ^ 2) *
      (M : ℝ) ^ ((k : ℝ) * ((k : ℝ) + 1)) =
      ((M : ℝ) ^ (-(4 * (ℓ : ℝ))) * (M : ℝ) ^ (4 * (ℓ : ℝ) - ((k : ℝ) * ((k : ℝ) + 1))) *
        (M : ℝ) ^ ((k : ℝ) * ((k : ℝ) + 1))) * (jnorm k ℓ M) ^ 2 := by ring
  rw [h_reassoc]
  rw [← Real.rpow_add hM_pos, ← Real.rpow_add hM_pos]
  have : -(4 * (ℓ : ℝ)) + (4 * (ℓ : ℝ) - ((k : ℝ) * ((k : ℝ) + 1))) + ((k : ℝ) * ((k : ℝ) + 1)) = 0 := by ring
  rw [this, Real.rpow_zero, one_mul]

/-! ### Part 5: Exponential and Constant Estimates -/

lemma log_le_self' (x : ℝ) (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.add_one_le_exp (Real.log x)
  rw [Real.exp_log hx] at this
  linarith

lemma k_pow_four_k_le (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) ^ (4 * k) : ℝ) ≤ Real.exp (4 * (k : ℝ) ^ 4) := by
  have hk_pos : 0 < (k : ℝ) := by positivity
  have hk_ge1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have h_rpow : ((k : ℝ) ^ (4 * k) : ℝ) = Real.exp (4 * (k : ℝ) * Real.log (k : ℝ)) := by
    rw [← Real.rpow_natCast]
    push_cast
    rw [Real.rpow_def_of_pos hk_pos]
    congr 1
    ring
  rw [h_rpow]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log (k : ℝ) ≤ (k : ℝ) := by
    have := Real.add_one_le_exp (Real.log (k : ℝ))
    rw [Real.exp_log hk_pos] at this
    linarith
  have h_k2_le_k4 : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ 4 := by
    have : 1 ≤ (k : ℝ) ^ 2 := by nlinarith
    calc (k : ℝ) ^ 2 = (k : ℝ) ^ 2 * 1 := by ring
      _ ≤ (k : ℝ) ^ 2 * (k : ℝ) ^ 2 := by
        refine mul_le_mul_of_nonneg_left this (by positivity)
      _ = (k : ℝ) ^ 4 := by ring
  calc 4 * (k : ℝ) * Real.log (k : ℝ)
    _ ≤ 4 * (k : ℝ) * (k : ℝ) := by
      refine mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 4 * (k : ℝ) ^ 2 := by ring
    _ ≤ 4 * (k : ℝ) ^ 4 := by
      linarith

lemma const_pow_k_le (A : ℝ) (hA : 0 < A) (k : ℕ) (hk : 1 ≤ k) :
    A ^ k ≤ Real.exp (|Real.log A| * (k : ℝ) ^ 4) := by
  have hk_ge1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have h_rpow : A ^ k = Real.exp ((k : ℝ) * Real.log A) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hA]
    congr 1
    ring
  rw [h_rpow]
  apply Real.exp_le_exp.mpr
  have h1 : Real.log A ≤ |Real.log A| := le_abs_self _
  have hk2 : 1 ≤ (k : ℝ) ^ 2 := by nlinarith
  have hk3 : 1 ≤ (k : ℝ) ^ 3 := by
    calc 1 = 1 * 1 := by ring
      _ ≤ (k : ℝ) * (k : ℝ) ^ 2 := by
        refine mul_le_mul hk_ge1 hk2 (by norm_num) (by positivity)
      _ = (k : ℝ) ^ 3 := by ring
  have h2 : (k : ℝ) ≤ (k : ℝ) ^ 4 := by
    calc (k : ℝ) = (k : ℝ) * 1 := by ring
      _ ≤ (k : ℝ) * (k : ℝ) ^ 3 := by
        refine mul_le_mul_of_nonneg_left hk3 (by positivity)
      _ = (k : ℝ) ^ 4 := by ring
  calc (k : ℝ) * Real.log A
    _ ≤ (k : ℝ) * |Real.log A| := by
      refine mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (k : ℝ) ^ 4 * |Real.log A| := by
      refine mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
    _ = |Real.log A| * (k : ℝ) ^ 4 := by ring

lemma pow_le_imp_le_rpow (x y : ℝ) (N : ℕ) (hx : 0 ≤ x) (_hy : 0 ≤ y) (hN : 1 ≤ N) (h : x ^ N ≤ y) :
    x ≤ y ^ (1 / (N : ℝ)) := by
  have hN_pos : 0 < (N : ℝ) := by positivity
  have h_x_rpow : x = (x ^ N) ^ (1 / (N : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    have : (N : ℝ) * (1 / (N : ℝ)) = 1 := mul_one_div_cancel hN_pos.ne'
    rw [this, Real.rpow_one]
  rw [h_x_rpow]
  exact Real.rpow_le_rpow (by positivity) h (by positivity)

lemma rpow_split_exp (B : ℝ) (ℓ : ℕ) (_hℓ : 1 ≤ ℓ) :
    (Real.exp (B * (ℓ : ℝ) ^ 2)) ^ (1 / (2 * (ℓ : ℝ) ^ 2)) = Real.exp (B / 2) := by
  have _hℓ_pos : 0 < (ℓ : ℝ) ^ 2 := by positivity
  have _h2 : 0 < 2 * (ℓ : ℝ) ^ 2 := by positivity
  rw [← Real.exp_mul]
  congr 1
  field_simp

lemma rpow_split_M (c : ℝ) (C₀ k ℓ : ℕ) (M : ℕ) (hM : 1 ≤ M) (_hk : 1 ≤ k) (_hC₀ : 1 ≤ C₀) (hℓ : ℓ = C₀ * k ^ 2) :
    ((M : ℝ) ^ (- (c / 2) * (k : ℝ) ^ 2)) ^ (1 / (2 * (ℓ : ℝ) ^ 2)) =
      (M : ℝ) ^ (- (c / (4 * (C₀ : ℝ) ^ 2)) / (k : ℝ) ^ 2) := by
  have hM_pos : 0 < (M : ℝ) := by positivity
  have _hk_pos : 0 < (k : ℝ) := by positivity
  have _hC₀_pos : 0 < (C₀ : ℝ) := by positivity
  have _hℓ_pos : 0 < (ℓ : ℝ) := by
    rw [hℓ]
    positivity
  rw [← Real.rpow_mul hM_pos.le]
  congr 1
  rw [hℓ]
  push_cast
  field_simp
  ring

lemma chooseC₀_exp_bound (C_J c : ℝ) (hCJ : 0 < C_J) (hc : 0 < c) :
    let C₀ : ℕ := Nat.ceil (Real.log (4 * C_J / c)) + 2
    2 * C_J * Real.exp (-(C₀ : ℝ)) ≤ c / 2 := by
  intro C₀
  have h_arg_pos : 0 < 4 * C_J / c := by positivity
  have h_ceil : Real.log (4 * C_J / c) ≤ (Nat.ceil (Real.log (4 * C_J / c)) : ℝ) :=
    Nat.le_ceil _
  have h_C₀_le : Real.log (4 * C_J / c) ≤ (C₀ : ℝ) := by
    dsimp [C₀]
    push_cast
    linarith
  have h_neg : - (C₀ : ℝ) ≤ - Real.log (4 * C_J / c) := by linarith
  have h_exp_neg : Real.exp (- (C₀ : ℝ)) ≤ Real.exp (- Real.log (4 * C_J / c)) :=
    Real.exp_le_exp.mpr h_neg
  rw [← Real.log_inv, Real.exp_log (inv_pos.mpr h_arg_pos)] at h_exp_neg
  have h_inv : (4 * C_J / c)⁻¹ = c / (4 * C_J) := inv_div _ _
  rw [h_inv] at h_exp_neg
  have h_mul : 2 * C_J * Real.exp (- (C₀ : ℝ)) ≤ 2 * C_J * (c / (4 * C_J)) := by
    refine mul_le_mul_of_nonneg_left h_exp_neg (by positivity)
  refine h_mul.trans ?_
  have h_simp : 2 * C_J * (c / (4 * C_J)) = c / 2 := by
    field_simp
    ring
  rw [h_simp]

lemma exp_bound_combine (C_J C_good : ℝ) (C₀ k : ℕ) (_hCJ : 0 ≤ C_J) (hCg : 0 < C_good) (hk : 1 ≤ k) (hC₀ : 1 ≤ C₀) :
    let B := 2 * C_J + |Real.log (C_good * (C₀ : ℝ) ^ 2)| + 4
    let ℓ := C₀ * k ^ 2
    (C_good * (ℓ : ℝ) ^ 2) ^ k * Real.exp (2 * C_J * (ℓ : ℝ) ^ 2) ≤ Real.exp (B * (ℓ : ℝ) ^ 2) := by
  intro B ℓ
  have hk_ge1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hC₀_ge1 : 1 ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
  have hC₀_sq_ge1 : 1 ≤ (C₀ : ℝ) ^ 2 := by nlinarith
  have hℓ_eq : (ℓ : ℝ) = (C₀ : ℝ) * (k : ℝ) ^ 2 := by
    dsimp [ℓ]
    push_cast
    rfl
  have hℓ_sq : (ℓ : ℝ) ^ 2 = (C₀ : ℝ) ^ 2 * (k : ℝ) ^ 4 := by
    rw [hℓ_eq]
    ring
  have h_base_pos : 0 < C_good * (C₀ : ℝ) ^ 2 := by positivity
  have h_pow_pow : ((k : ℝ) ^ 4) ^ k = (k : ℝ) ^ (4 * k) := by
    rw [← pow_mul]
  have h_split_base : (C_good * (ℓ : ℝ) ^ 2) ^ k = (C_good * (C₀ : ℝ) ^ 2) ^ k * (k : ℝ) ^ (4 * k) := by
    rw [hℓ_sq]
    have : C_good * ((C₀ : ℝ) ^ 2 * (k : ℝ) ^ 4) = (C_good * (C₀ : ℝ) ^ 2) * (k : ℝ) ^ 4 := by ring
    rw [this, mul_pow, h_pow_pow]
  have h1 := const_pow_k_le (C_good * (C₀ : ℝ) ^ 2) h_base_pos k hk
  have h2 := k_pow_four_k_le k hk
  have h_prod_le : (C_good * (C₀ : ℝ) ^ 2) ^ k * (k : ℝ) ^ (4 * k) ≤
      Real.exp (|Real.log (C_good * (C₀ : ℝ) ^ 2)| * (k : ℝ) ^ 4) * Real.exp (4 * (k : ℝ) ^ 4) := by
    refine mul_le_mul h1 h2 (by positivity) (by positivity)
  have h_mul_exp : (C_good * (ℓ : ℝ) ^ 2) ^ k * Real.exp (2 * C_J * (ℓ : ℝ) ^ 2) ≤
      (Real.exp (|Real.log (C_good * (C₀ : ℝ) ^ 2)| * (k : ℝ) ^ 4) * Real.exp (4 * (k : ℝ) ^ 4)) *
        Real.exp (2 * C_J * (ℓ : ℝ) ^ 2) := by
    rw [h_split_base]
    refine mul_le_mul_of_nonneg_right h_prod_le (by positivity)
  refine h_mul_exp.trans ?_
  rw [hℓ_sq]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h_reassoc : |Real.log (C_good * (C₀ : ℝ) ^ 2)| * (k : ℝ) ^ 4 + 4 * (k : ℝ) ^ 4 + 2 * C_J * ((C₀ : ℝ) ^ 2 * (k : ℝ) ^ 4) =
      (|Real.log (C_good * (C₀ : ℝ) ^ 2)| + 4 + 2 * C_J * (C₀ : ℝ) ^ 2) * (k : ℝ) ^ 4 := by ring
  rw [h_reassoc]
  have h_B_reassoc : B * ((C₀ : ℝ) ^ 2 * (k : ℝ) ^ 4) =
      (B * (C₀ : ℝ) ^ 2) * (k : ℝ) ^ 4 := by ring
  rw [h_B_reassoc]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  dsimp [B]
  have h_sub : |Real.log (C_good * (C₀ : ℝ) ^ 2)| + 4 ≤
      (|Real.log (C_good * (C₀ : ℝ) ^ 2)| + 4) * (C₀ : ℝ) ^ 2 := by
    have : 0 ≤ |Real.log (C_good * (C₀ : ℝ) ^ 2)| + 4 := by positivity
    calc |Real.log (C_good * (C₀ : ℝ) ^ 2)| + 4
      _ = (|Real.log (C_good * (C₀ : ℝ) ^ 2)| + 4) * 1 := by ring
      _ ≤ (|Real.log (C_good * (C₀ : ℝ) ^ 2)| + 4) * (C₀ : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hC₀_sq_ge1 this
  linarith

lemma prod_coordinate_sums_le (k ℓ M : ℕ) (c₀ C_L : ℝ) (hCL : 0 < C_L)
    (h_bound : ∀ (M ℓ j : ℕ) (c₀ α : ℝ), 2 ≤ M → 1 ≤ ℓ → 1 ≤ j → 0 < c₀ → c₀ ≤ 1 →
      (M : ℝ) ^ (-(2 - c₀) * j) ≤ |α| → |α| ≤ (M : ℝ) ^ (-c₀ * j) →
      (∑ x ∈ Finset.Icc (-(ℓ * M ^ j : ℤ)) (ℓ * M ^ j),
          ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ j : ℤ)) (ℓ * M ^ j), Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖) ≤
        C_L * ℓ ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) * (1 + j * Real.log M))
    (α : Fin k → ℝ)
    (hM : 2 ≤ M) (hℓ : 1 ≤ ℓ) (_hk : 1 ≤ k) (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1)
    (h_good : c₀ * (k : ℝ) ≤ ((Finset.univ.filter fun j : Fin k =>
      (M : ℝ) ^ (-(2 - c₀) * (j.val + 1)) ≤ |α j| ∧
      |α j| ≤ (M : ℝ) ^ (-c₀ * (j.val + 1))).card : ℝ)) :
    let C_good := max (9 : ℝ) (C_L * (1 + 2 / c₀))
    let c := c₀ ^ 3 / 4
    (∏ j : Fin k, ∑ x ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
      ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
        Complex.exp (2 * Real.pi * Complex.I * (α j * (x : ℝ) * (y : ℝ) : ℂ))‖) ≤
    (C_good * (ℓ : ℝ) ^ 2) ^ k * (M : ℝ) ^ (k * (k + 1)) * (M : ℝ) ^ (- c * (k : ℝ) ^ 2) := by
  intro C_good c
  set Good := Finset.univ.filter (fun j : Fin k =>
    (M : ℝ) ^ (-(2 - c₀) * (j.val + 1)) ≤ |α j| ∧
    |α j| ≤ (M : ℝ) ^ (-c₀ * (j.val + 1))) with hGood_def
  have hM1 : 1 ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hM_pos : 0 < (M : ℝ) := by positivity
  have hC_good_ge9 : (9 : ℝ) ≤ C_good := le_max_left _ _
  have hC_good_geCL : C_L * (1 + 2 / c₀) ≤ C_good := le_max_right _ _
  have _hC_good_pos : 0 < C_good := by
    have : 0 < (9 : ℝ) := by norm_num
    linarith
  have h_each : ∀ j : Fin k,
      (∑ x ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
        ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
          Complex.exp (2 * Real.pi * Complex.I * (α j * (x : ℝ) * (y : ℝ) : ℂ))‖) ≤
      C_good * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
        (if j ∈ Good then (M : ℝ) ^ (-(c₀ / 2) * (j.val + 1 : ℝ)) else 1) := by
    intro j
    have hj_pos : 1 ≤ j.val + 1 := by omega
    have hj_cast : (j.val : ℝ) + 1 = ((j.val + 1 : ℕ) : ℝ) := by push_cast; rfl
    by_cases hj : j ∈ Good
    · split_ifs
      rw [Finset.mem_filter] at hj
      rcases hj with ⟨-, hj1, hj2⟩
      rw [hj_cast] at hj1 hj2
      have h_bound_j := h_bound M ℓ (j.val + 1) c₀ (α j) hM hℓ hj_pos hc₀ hc₀' hj1 hj2
      have h_absorb := absorb_log_M M (j.val + 1) c₀ hM hj_pos hc₀
      have h_reassoc1 : C_L * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * (j.val + 1 : ℕ)) * (M : ℝ) ^ (2 * (j.val + 1)) *
          (1 + (j.val + 1 : ℕ) * Real.log (M : ℝ)) =
          C_L * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
            ((M : ℝ) ^ (-c₀ * ((j.val + 1 : ℕ) : ℝ)) * (1 + ((j.val + 1 : ℕ) : ℝ) * Real.log (M : ℝ))) := by
        push_cast
        ring
      have h_mid : (∑ x ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
          ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
            Complex.exp (2 * Real.pi * Complex.I * (α j * (x : ℝ) * (y : ℝ) : ℂ))‖) ≤
          C_L * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
            ((M : ℝ) ^ (-c₀ * ((j.val + 1 : ℕ) : ℝ)) * (1 + ((j.val + 1 : ℕ) : ℝ) * Real.log (M : ℝ))) := by
        rw [← h_reassoc1]
        exact h_bound_j
      refine h_mid.trans ?_
      have h_step2 : C_L * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
            ((M : ℝ) ^ (-c₀ * ((j.val + 1 : ℕ) : ℝ)) * (1 + ((j.val + 1 : ℕ) : ℝ) * Real.log (M : ℝ))) ≤
          C_L * (1 + 2 / c₀) * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
            (M : ℝ) ^ (-(c₀ / 2) * ((j.val + 1 : ℕ) : ℝ)) := by
        calc C_L * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
              ((M : ℝ) ^ (-c₀ * ((j.val + 1 : ℕ) : ℝ)) * (1 + ((j.val + 1 : ℕ) : ℝ) * Real.log (M : ℝ)))
          _ ≤ C_L * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
              ((1 + 2 / c₀) * (M : ℝ) ^ (-(c₀ / 2) * ((j.val + 1 : ℕ) : ℝ))) := by
                refine mul_le_mul_of_nonneg_left h_absorb ?_
                positivity
          _ = C_L * (1 + 2 / c₀) * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
              (M : ℝ) ^ (-(c₀ / 2) * ((j.val + 1 : ℕ) : ℝ)) := by ring
      refine h_step2.trans ?_
      rw [← hj_cast]
      have h_reassoc2 : C_L * (1 + 2 / c₀) * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
          (M : ℝ) ^ (-(c₀ / 2) * ((j.val : ℝ) + 1)) =
          (C_L * (1 + 2 / c₀)) * ((ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
            (M : ℝ) ^ (-(c₀ / 2) * ((j.val : ℝ) + 1))) := by ring
      have h_reassoc3 : C_good * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
          (M : ℝ) ^ (-(c₀ / 2) * ((j.val : ℝ) + 1)) =
          C_good * ((ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
            (M : ℝ) ^ (-(c₀ / 2) * ((j.val : ℝ) + 1))) := by ring
      rw [h_reassoc2, h_reassoc3]
      refine mul_le_mul_of_nonneg_right hC_good_geCL ?_
      positivity
    · split_ifs
      rw [mul_one]
      have h_triv := sum_norm_sum_exp_mul_trivial M ℓ j.val (α j) hM hℓ
      refine h_triv.trans ?_
      have h_nonneg_term : 0 ≤ (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) := by positivity
      have h1 : 9 * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) =
          9 * ((ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1))) := by ring
      have h2 : C_good * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) =
          C_good * ((ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1))) := by ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_right hC_good_ge9 h_nonneg_term
  have h_prod_le : (∏ j : Fin k,
        ∑ x ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
          ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ (j.val + 1) : ℤ)) (ℓ * M ^ (j.val + 1)),
            Complex.exp (2 * Real.pi * Complex.I * (α j * (x : ℝ) * (y : ℝ) : ℂ))‖) ≤
      ∏ j : Fin k, (C_good * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
        (if j ∈ Good then (M : ℝ) ^ (-(c₀ / 2) * (j.val + 1 : ℝ)) else 1)) := by
    apply Finset.prod_le_prod
    · intro j _
      exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    · intro j _
      exact h_each j
  refine h_prod_le.trans ?_
  have h_split_prod : ∏ j : Fin k, (C_good * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * (j.val + 1)) *
        (if j ∈ Good then (M : ℝ) ^ (-(c₀ / 2) * (j.val + 1 : ℝ)) else 1)) =
      (∏ j : Fin k, (C_good * (ℓ : ℝ) ^ 2)) *
      (∏ j : Fin k, (M : ℝ) ^ (2 * (j.val + 1))) *
      (∏ j : Fin k, (if j ∈ Good then (M : ℝ) ^ (-(c₀ / 2) * (j.val + 1 : ℝ)) else 1)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [h_split_prod]
  have h_p1 : ∏ j : Fin k, (C_good * (ℓ : ℝ) ^ 2) = (C_good * (ℓ : ℝ) ^ 2) ^ k := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h_p2 : ∏ j : Fin k, (M : ℝ) ^ (2 * (j.val + 1)) = (M : ℝ) ^ (k * (k + 1)) :=
    prod_M_pow_eq k M
  rw [h_p1, h_p2]
  have h_p3_filter : (∏ j : Fin k, (if j ∈ Good then (M : ℝ) ^ (-(c₀ / 2) * (j.val + 1 : ℝ)) else 1)) =
      ∏ j ∈ Good, (M : ℝ) ^ (-(c₀ / 2) * (j.val + 1 : ℝ)) := by
    rw [← Finset.prod_filter]
    congr 1
    ext x
    simp
  rw [h_p3_filter]
  have h_p3_rpow : (∏ j ∈ Good, (M : ℝ) ^ (-(c₀ / 2) * (j.val + 1 : ℝ))) =
      (M : ℝ) ^ (∑ j ∈ Good, -(c₀ / 2) * (j.val + 1 : ℝ)) := by
    rw [← Real.rpow_sum_of_pos hM_pos]
  rw [h_p3_rpow]
  have h_sum_reassoc : (∑ j ∈ Good, -(c₀ / 2) * (j.val + 1 : ℝ)) =
      -(c₀ / 2) * ∑ j ∈ Good, ((j.val : ℝ) + 1) := by
    rw [← Finset.mul_sum]
  rw [h_sum_reassoc]
  have h_sum_ge := sum_val_succ_ge_real Good
  have h_card_ge : (c₀ * (k : ℝ)) ^ 2 / 2 ≤ (Good.card : ℝ) ^ 2 / 2 := by
    have : 0 ≤ c₀ * (k : ℝ) := by positivity
    have h_sq : (c₀ * (k : ℝ)) ^ 2 ≤ (Good.card : ℝ) ^ 2 := by
      nlinarith
    linarith
  have h_total_sum_ge : (c₀ * (k : ℝ)) ^ 2 / 2 ≤ ∑ j ∈ Good, ((j.val : ℝ) + 1) :=
    h_card_ge.trans h_sum_ge
  have h_exp_le : -(c₀ / 2) * ∑ j ∈ Good, ((j.val : ℝ) + 1) ≤ - c * (k : ℝ) ^ 2 := by
    have : -(c₀ / 2) * ∑ j ∈ Good, ((j.val : ℝ) + 1) ≤ -(c₀ / 2) * ((c₀ * (k : ℝ)) ^ 2 / 2) := by
      have : 0 ≤ c₀ / 2 := by positivity
      nlinarith
    refine this.trans ?_
    dsimp [c]
    have : -(c₀ / 2) * ((c₀ * (k : ℝ)) ^ 2 / 2) = - (c₀ ^ 3 / 4) * (k : ℝ) ^ 2 := by ring
    rw [this]
  have h_rpow_le : (M : ℝ) ^ (-(c₀ / 2) * ∑ j ∈ Good, ((j.val : ℝ) + 1)) ≤ (M : ℝ) ^ (- c * (k : ℝ) ^ 2) :=
    Real.rpow_le_rpow_of_exponent_le hM1 h_exp_le
  exact mul_le_mul_of_nonneg_left h_rpow_le (by positivity)

lemma exp_sq (A : ℝ) : (Real.exp A) ^ 2 = Real.exp (2 * A) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

lemma rpow_sq {M : ℝ} (hM : 0 < M) (A : ℝ) : (M ^ A) ^ 2 = M ^ (2 * A) := by
  rw [pow_two, ← Real.rpow_add hM]
  congr 1
  ring

theorem bilinearEstimate (c₀ : ℝ) (hc₀ : 0 < c₀) (hc₀' : c₀ ≤ 1) : BilinearEstimate c₀ := by
  obtain ⟨C_J, hCJ_pos, hjnorm_le⟩ := jnorm_le
  obtain ⟨C_L, hCL_pos, h_bound⟩ := sum_norm_sum_exp_mul_le
  set c := c₀ ^ 3 / 4 with hc_def
  have hc_pos : 0 < c := by positivity
  set C₀ : ℕ := Nat.ceil (Real.log (4 * C_J / c)) + 2 with hC₀_def
  have hC₀_ge1 : 1 ≤ C₀ := by
    dsimp [C₀]
    omega
  set c₁ := c / (4 * (C₀ : ℝ) ^ 2) with hc₁_def
  have hc₁_pos : 0 < c₁ := by positivity
  set C_good := max (9 : ℝ) (C_L * (1 + 2 / c₀)) with hC_good_def
  have hC_good_pos : 0 < C_good := by
    have : 0 < (9 : ℝ) := by norm_num
    linarith [le_max_left (9 : ℝ) (C_L * (1 + 2 / c₀))]
  set B := 2 * C_J + |Real.log (C_good * (C₀ : ℝ) ^ 2)| + 4 with hB_def
  set C := Real.exp (B / 2) with hC_def
  have hC_pos : 0 < C := by positivity
  refine ⟨c₁, C, hc₁_pos, hC_pos, ?_⟩
  intro k M α hk hM h_good
  have hk_ge1 : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hM_ge1 : 1 ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have hM_pos : 0 < (M : ℝ) := by positivity
  set ℓ := C₀ * k ^ 2 with hℓ_def
  have hℓ_ge1 : 1 ≤ ℓ := by
    dsimp [ℓ]
    have : 1 ≤ k ^ 2 := by nlinarith
    nlinarith
  have h_k2_le_ell : k ^ 2 ≤ ℓ := by
    dsimp [ℓ]
    calc k ^ 2 = 1 * k ^ 2 := by rw [one_mul]
      _ ≤ C₀ * k ^ 2 := by
        refine Nat.mul_le_mul_right (k ^ 2) hC₀_ge1
  have h_coord := prod_coordinate_sums_le k ℓ M c₀ C_L hCL_pos h_bound α hM hℓ_ge1 hk hc₀ hc₀' h_good
  have h_holder := norm_bilinearSum_pow_le k ℓ M hℓ_ge1 (by omega) α
  rw [sum_box_exp_factor] at h_holder
  have h_step1 : ‖bilinearSum k M α‖ ^ (2 * ℓ ^ 2) ≤
      (M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) ^ 2 *
        ((C_good * (ℓ : ℝ) ^ 2) ^ k * (M : ℝ) ^ (k * (k + 1)) * (M : ℝ) ^ (- c * (k : ℝ) ^ 2)) := by
    refine h_holder.trans ?_
    refine mul_le_mul_of_nonneg_left h_coord (by positivity)
  have h_reassoc : (M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) ^ 2 *
        ((C_good * (ℓ : ℝ) ^ 2) ^ k * (M : ℝ) ^ (k * (k + 1)) * (M : ℝ) ^ (- c * (k : ℝ) ^ 2)) =
      (C_good * (ℓ : ℝ) ^ 2) ^ k *
        ((M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) ^ 2 * (M : ℝ) ^ (k * (k + 1))) *
        (M : ℝ) ^ (- c * (k : ℝ) ^ 2) := by ring
  rw [h_reassoc] at h_step1
  rw [J_sq_cancel k ℓ M (by omega)] at h_step1
  have hjnorm_nonneg : 0 ≤ jnorm k ℓ M := by
    dsimp [jnorm]
    positivity
  have hjnorm_bound := hjnorm_le k ℓ M hk h_k2_le_ell (by omega)
  have hjnorm_sq_le : (jnorm k ℓ M) ^ 2 ≤
      (Real.exp (C_J * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ (C_J * (k : ℝ) ^ 2 * Real.exp ((- (ℓ : ℝ)) / (k : ℝ) ^ 2))) ^ 2 := by
    nlinarith
  rw [mul_pow] at hjnorm_sq_le
  rw [exp_sq] at hjnorm_sq_le
  rw [rpow_sq hM_pos] at hjnorm_sq_le
  have h_reassoc_prod : (C_good * (ℓ : ℝ) ^ 2) ^ k * (jnorm k ℓ M) ^ 2 * (M : ℝ) ^ (- c * (k : ℝ) ^ 2) =
      ((C_good * (ℓ : ℝ) ^ 2) ^ k * (jnorm k ℓ M) ^ 2) * (M : ℝ) ^ (- c * (k : ℝ) ^ 2) := by ring
  have h_step2 : (C_good * (ℓ : ℝ) ^ 2) ^ k * (jnorm k ℓ M) ^ 2 * (M : ℝ) ^ (- c * (k : ℝ) ^ 2) ≤
      (C_good * (ℓ : ℝ) ^ 2) ^ k *
        (Real.exp (2 * (C_J * (ℓ : ℝ) ^ 2)) *
          (M : ℝ) ^ (2 * (C_J * (k : ℝ) ^ 2 * Real.exp ((- (ℓ : ℝ)) / (k : ℝ) ^ 2)))) *
        (M : ℝ) ^ (- c * (k : ℝ) ^ 2) := by
    rw [h_reassoc_prod]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left hjnorm_sq_le (by positivity)
  have h_step3 : (C_good * (ℓ : ℝ) ^ 2) ^ k *
        (Real.exp (2 * (C_J * (ℓ : ℝ) ^ 2)) *
          (M : ℝ) ^ (2 * (C_J * (k : ℝ) ^ 2 * Real.exp ((- (ℓ : ℝ)) / (k : ℝ) ^ 2)))) *
        (M : ℝ) ^ (- c * (k : ℝ) ^ 2) =
      ((C_good * (ℓ : ℝ) ^ 2) ^ k * Real.exp (2 * C_J * (ℓ : ℝ) ^ 2)) *
        ((M : ℝ) ^ (2 * (C_J * (k : ℝ) ^ 2 * Real.exp ((- (ℓ : ℝ)) / (k : ℝ) ^ 2))) *
          (M : ℝ) ^ (- c * (k : ℝ) ^ 2)) := by
    have h_exp_assoc : 2 * (C_J * (ℓ : ℝ) ^ 2) = 2 * C_J * (ℓ : ℝ) ^ 2 := by ring
    rw [h_exp_assoc]
    ring
  have h_exp_combine := exp_bound_combine C_J C_good C₀ k hCJ_pos.le hC_good_pos hk hC₀_ge1
  have h_cancel : (- (ℓ : ℝ)) / (k : ℝ) ^ 2 = - (C₀ : ℝ) := by
    dsimp [ℓ]
    push_cast
    have hk_ne : (k : ℝ) ^ 2 ≠ 0 := by positivity
    field_simp
  have h_exp_le : 2 * (C_J * (k : ℝ) ^ 2 * Real.exp ((- (ℓ : ℝ)) / (k : ℝ) ^ 2)) + (- c * (k : ℝ) ^ 2) ≤
      - (c / 2) * (k : ℝ) ^ 2 := by
    rw [h_cancel]
    have h_reassoc_exp : 2 * (C_J * (k : ℝ) ^ 2 * Real.exp (-(C₀ : ℝ))) + (- c * (k : ℝ) ^ 2) =
        (2 * C_J * Real.exp (-(C₀ : ℝ)) - c) * (k : ℝ) ^ 2 := by ring
    rw [h_reassoc_exp]
    have h_bound_exp := chooseC₀_exp_bound C_J c hCJ_pos hc_pos
    have h_diff : 2 * C_J * Real.exp (-(C₀ : ℝ)) - c ≤ - (c / 2) := by linarith
    have : 0 ≤ (k : ℝ) ^ 2 := by positivity
    nlinarith
  have h_rpow_combine : (M : ℝ) ^ (2 * (C_J * (k : ℝ) ^ 2 * Real.exp ((- (ℓ : ℝ)) / (k : ℝ) ^ 2))) *
        (M : ℝ) ^ (- c * (k : ℝ) ^ 2) ≤ (M : ℝ) ^ (- (c / 2) * (k : ℝ) ^ 2) := by
    rw [← Real.rpow_add hM_pos]
    exact Real.rpow_le_rpow_of_exponent_le hM_ge1 h_exp_le
  have h_total_le : ‖bilinearSum k M α‖ ^ (2 * ℓ ^ 2) ≤
      Real.exp (B * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ (- (c / 2) * (k : ℝ) ^ 2) := by
    refine h_step1.trans ?_
    refine h_step2.trans ?_
    rw [h_step3]
    refine mul_le_mul h_exp_combine h_rpow_combine (by positivity) (by positivity)
  have h_N_pos : 1 ≤ 2 * ℓ ^ 2 := by
    have : 1 ≤ ℓ ^ 2 := by nlinarith
    omega
  have h_root := pow_le_imp_le_rpow ‖bilinearSum k M α‖
    (Real.exp (B * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ (- (c / 2) * (k : ℝ) ^ 2))
    (2 * ℓ ^ 2)
    (norm_nonneg _)
    (by positivity)
    h_N_pos
    h_total_le
  have h_N_cast : ((2 * ℓ ^ 2 : ℕ) : ℝ) = 2 * (ℓ : ℝ) ^ 2 := by push_cast; rfl
  rw [h_N_cast] at h_root
  have h_root_split : (Real.exp (B * (ℓ : ℝ) ^ 2) * (M : ℝ) ^ (- (c / 2) * (k : ℝ) ^ 2)) ^ (1 / (2 * (ℓ : ℝ) ^ 2 : ℝ)) =
      (Real.exp (B * (ℓ : ℝ) ^ 2)) ^ (1 / (2 * (ℓ : ℝ) ^ 2 : ℝ)) *
      ((M : ℝ) ^ (- (c / 2) * (k : ℝ) ^ 2)) ^ (1 / (2 * (ℓ : ℝ) ^ 2 : ℝ)) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [h_root_split] at h_root
  have h_exp_root := rpow_split_exp B ℓ hℓ_ge1
  have h_M_root := rpow_split_M c C₀ k ℓ M (by omega) hk hC₀_ge1 rfl
  rw [h_exp_root, h_M_root] at h_root
  have h_sum_eq := bilinearSum_eq k M α
  rw [h_sum_eq]
  exact h_root

end Erdos1201.MR.Vinogradov
