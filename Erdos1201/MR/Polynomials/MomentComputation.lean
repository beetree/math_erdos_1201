import Mathlib
import Erdos1201.MR.Polynomials.DivisorMultiplicity
import Erdos1201.MR.Analysis.MeanValueTheorem
import Erdos1201.MR.Polynomials.PrimePowerCoefficients
import Erdos1201.MR.Analysis.DirichletPolyBasics

open scoped BigOperators

/-!
# Moment Computation for Prime Polynomial Powers and Dirichlet Polynomials

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the mean-square moment computation of Matomäki–Radziwiłł (arXiv:1501.04585v4),
Lemma 13, bounding the mean square of $(Q(1+it))^\ell R(1+it)$ over $t \in [-T, T]$.
Here $Q$ is a Dirichlet polynomial supported on primes in $[Y_1, 2Y_1]$, and $R$ is supported on
$m \in [X/Y_2, 2X/Y_2]$.

The bound uses Montgomery's mean value theorem from `Erdos1201.MR.Analysis.MeanValueTheorem`,
the representation count bound from `Erdos1201.MR.Polynomials.DivisorMultiplicity`, and the
mean-square restricted divisor sum from `Erdos1201.MR.Polynomials.DivisorMultiplicity`.
-/

namespace Erdos1201.MR

/-! ### Part 1: Product bounds and support of representations -/

lemma le_prod_piFinset_of_mem {P : Finset ℕ} (Y₁ : ℕ) (hP : ∀ p ∈ P, Y₁ ≤ p)
    {ℓ : ℕ} {v : Fin ℓ → ℕ} (hv : v ∈ Fintype.piFinset (fun _ : Fin ℓ => P)) :
    Y₁ ^ ℓ ≤ ∏ i, v i := by
  have h_prod : ∏ _i : Fin ℓ, Y₁ ≤ ∏ i : Fin ℓ, v i := by
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro i _hi
    exact hP (v i) (Fintype.mem_piFinset.mp hv i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h_prod
  exact h_prod

lemma prod_piFinset_le_of_mem {P : Finset ℕ} (Y₁ : ℕ) (hP : ∀ p ∈ P, p ≤ 2 * Y₁)
    {ℓ : ℕ} {v : Fin ℓ → ℕ} (hv : v ∈ Fintype.piFinset (fun _ : Fin ℓ => P)) :
    ∏ i, v i ≤ 2 ^ ℓ * Y₁ ^ ℓ := by
  have h_prod : ∏ i : Fin ℓ, v i ≤ ∏ _i : Fin ℓ, (2 * Y₁) := by
    apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    intro i _hi
    exact hP (v i) (Fintype.mem_piFinset.mp hv i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] at h_prod
  exact h_prod

lemma repCount_eq_zero_of_lt {A P : Finset ℕ} {ℓ n Y₁ X Y₂ : ℕ} (hP : ∀ p ∈ P, Y₁ ≤ p)
    (hA : ∀ m ∈ A, X / Y₂ ≤ m) (hn : n < (X / Y₂) * Y₁ ^ ℓ) :
    repCount A P ℓ n = 0 := by
  rw [repCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  rw [Finset.mem_product] at hx
  have h1 : X / Y₂ ≤ x.1 := hA x.1 hx.1
  have h2 : Y₁ ^ ℓ ≤ ∏ i, x.2 i := le_prod_piFinset_of_mem Y₁ hP hx.2
  have hmul : (X / Y₂) * Y₁ ^ ℓ ≤ x.1 * ∏ i, x.2 i := Nat.mul_le_mul h1 h2
  omega

lemma repCount_eq_zero_of_gt {A P : Finset ℕ} {ℓ n Y₁ X Y₂ : ℕ} (hP : ∀ p ∈ P, p ≤ 2 * Y₁)
    (hA : ∀ m ∈ A, m ≤ 2 * X / Y₂) (hn : (2 * X / Y₂) * (2 ^ ℓ * Y₁ ^ ℓ) < n) :
    repCount A P ℓ n = 0 := by
  rw [repCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  rw [Finset.mem_product] at hx
  have h1 : x.1 ≤ 2 * X / Y₂ := hA x.1 hx.1
  have h2 : ∏ i, x.2 i ≤ 2 ^ ℓ * Y₁ ^ ℓ := prod_piFinset_le_of_mem Y₁ hP hx.2
  have hmul : x.1 * ∏ i, x.2 i ≤ (2 * X / Y₂) * (2 ^ ℓ * Y₁ ^ ℓ) := Nat.mul_le_mul h1 h2
  omega

lemma div_two_mul_le_four_mul_div (X Y₂ : ℕ) (hY₂ : 1 ≤ Y₂) (hXY : Y₂ ≤ X) :
    2 * X / Y₂ ≤ 4 * (X / Y₂) := by
  have hq : 1 ≤ X / Y₂ := by
    rw [Nat.one_le_div_iff (by omega)]
    exact hXY
  have hX : X = Y₂ * (X / Y₂) + X % Y₂ := (Nat.div_add_mod X Y₂).symm
  have hmod : X % Y₂ < Y₂ := Nat.mod_lt X (by omega)
  have h2X : 2 * X < Y₂ * (2 * (X / Y₂ + 1)) := by
    calc 2 * X = 2 * (Y₂ * (X / Y₂) + X % Y₂) := by rw [← hX]
    _ < 2 * (Y₂ * (X / Y₂) + Y₂) := by nlinarith
    _ = Y₂ * (2 * (X / Y₂ + 1)) := by ring
  have hdiv : 2 * X / Y₂ < 2 * (X / Y₂ + 1) := Nat.div_lt_of_lt_mul h2X
  omega

lemma inv_cast_div_le (X Y₂ : ℕ) (hY₂ : 1 ≤ Y₂) (hXY : Y₂ ≤ X) :
    (1 : ℝ) / ((X / Y₂ : ℕ) : ℝ) ≤ 2 * (Y₂ : ℝ) / (X : ℝ) := by
  have hq : 1 ≤ X / Y₂ := by
    rw [Nat.one_le_div_iff (by omega)]
    exact hXY
  have hX : X = Y₂ * (X / Y₂) + X % Y₂ := (Nat.div_add_mod X Y₂).symm
  have hmod : X % Y₂ < Y₂ := Nat.mod_lt X (by omega)
  have h_le : X ≤ 2 * Y₂ * (X / Y₂) := by
    calc X = Y₂ * (X / Y₂) + X % Y₂ := hX
    _ ≤ Y₂ * (X / Y₂) + Y₂ := by omega
    _ = Y₂ * (X / Y₂ + 1) := by ring
    _ ≤ Y₂ * (2 * (X / Y₂)) := by
      apply Nat.mul_le_mul_left
      omega
    _ = 2 * Y₂ * (X / Y₂) := by ring
  have h_real_le : (X : ℝ) ≤ 2 * (Y₂ : ℝ) * ((X / Y₂ : ℕ) : ℝ) := by
    have : (X : ℝ) ≤ ((2 * Y₂ * (X / Y₂) : ℕ) : ℝ) := by exact_mod_cast h_le
    push_cast at this
    exact this
  have hX_pos : 0 < (X : ℝ) := by
    have : 1 ≤ X := by omega
    exact Nat.cast_pos.mpr this
  have hq_pos : 0 < ((X / Y₂ : ℕ) : ℝ) := Nat.cast_pos.mpr hq
  rw [div_le_div_iff₀ hq_pos hX_pos]
  calc (1 : ℝ) * (X : ℝ) = (X : ℝ) := by ring
  _ ≤ 2 * (Y₂ : ℝ) * ((X / Y₂ : ℕ) : ℝ) := h_real_le
  _ = 2 * (Y₂ : ℝ) * ((X / Y₂ : ℕ) : ℝ) := rfl

lemma inv_cast_sub_one_le {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / ((n - 1 : ℕ) : ℝ) ≤ 2 / (n : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by
    have : 1 ≤ n := by omega
    exact Nat.cast_pos.mpr this
  have hsub_pos : 0 < ((n - 1 : ℕ) : ℝ) := by
    have : 1 ≤ n - 1 := by omega
    exact Nat.cast_pos.mpr this
  rw [div_le_div_iff₀ hsub_pos hn_pos]
  have h_le : n ≤ 2 * (n - 1) := by omega
  have h_real : (n : ℝ) ≤ 2 * ((n - 1 : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ ((2 * (n - 1) : ℕ) : ℝ) := by exact_mod_cast h_le
    push_cast at this
    exact this
  linarith

/-! ### Part 2: Dyadic summation for restricted divisors -/

lemma sum_Ioc_dyadic_telescope {α : Type*} [AddCommMonoid α] (f : ℕ → α) (Y₀ : ℕ) (K : ℕ) :
    ∑ k ∈ Finset.range K, ∑ n ∈ Finset.Ioc (2 ^ k * Y₀) (2 ^ (k + 1) * Y₀), f n =
      ∑ n ∈ Finset.Ioc Y₀ (2 ^ K * Y₀), f n := by
  induction' K with K ih
  · simp
  · rw [Finset.sum_range_succ, ih]
    have h1 : Y₀ ≤ 2 ^ K * Y₀ := Nat.le_mul_of_pos_left Y₀ (Nat.two_pow_pos K)
    have h2 : 2 ^ K * Y₀ ≤ 2 ^ (K + 1) * Y₀ :=
      Nat.mul_le_mul_right Y₀ (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Finset.sum_Ioc_consecutive f h1 h2]

lemma sum_range_inv_two_pow_le_two (K : ℕ) :
    ∑ k ∈ Finset.range K, (1 / (2 : ℝ) ^ k) ≤ 2 := by
  have h_geom := geom_sum_eq (x := (1 / 2 : ℝ)) (by norm_num) K
  have h_eq : (∑ k ∈ Finset.range K, (1 / (2 : ℝ) ^ k)) =
      ∑ k ∈ Finset.range K, ((1 / 2 : ℝ) ^ k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [one_div_pow]
  rw [h_eq, h_geom]
  have : ((1 / 2 : ℝ) ^ K - 1) / (1 / 2 - 1) = 2 * (1 - (1 / 2 : ℝ) ^ K) := by ring
  rw [this]
  have h_pos : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
  nlinarith

lemma sum_sq_card_div_sq_le (P : Finset ℕ) (Y₁ : ℕ) (hY₁ : 2 ≤ Y₁)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hP : ∀ p ∈ P, Y₁ ≤ p ∧ p ≤ 2 * Y₁)
    (Y : ℕ) (hY : 1 ≤ Y) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), ((restrictedDivisors P n).card : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤
      3 * Real.exp 20 / (Y : ℝ) := by
  have hY_pos : 0 < (Y : ℝ) := Nat.cast_pos.mpr hY
  have hY_sq_pos : 0 < (Y : ℝ) ^ 2 := by positivity
  have h_term_le (n : ℕ) (hn : n ∈ Finset.Ioc Y (2 * Y)) :
      ((restrictedDivisors P n).card : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
      ((restrictedDivisors P n).card : ℝ) ^ 2 / (Y : ℝ) ^ 2 := by
    rw [Finset.mem_Ioc] at hn
    have hn_ge : (Y : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.le
    have h_sq : (Y : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    exact div_le_div_of_nonneg_left (by positivity) hY_sq_pos h_sq
  have h_sum_le := Finset.sum_le_sum h_term_le
  refine h_sum_le.trans ?_
  rw [← Finset.sum_div]
  have h_bound := sum_sq_card_restrictedDivisors_le P Y₁ hY₁ hprime hP Y
  have h1 : (∑ n ∈ Finset.Ioc Y (2 * Y), ((restrictedDivisors P n).card : ℝ) ^ 2) / (Y : ℝ) ^ 2 ≤
      (2 * Real.exp 20 * (Y : ℝ) + Real.exp 20) / (Y : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_right h_bound (by positivity)
  refine h1.trans ?_
  have h2 : Real.exp 20 ≤ Real.exp 20 * (Y : ℝ) := by
    have : 1 ≤ (Y : ℝ) := by exact_mod_cast hY
    nlinarith [Real.exp_pos 20]
  have h3 : (2 * Real.exp 20 * (Y : ℝ) + Real.exp 20) ≤ 3 * Real.exp 20 * (Y : ℝ) := by linarith
  have h4 : (2 * Real.exp 20 * (Y : ℝ) + Real.exp 20) / (Y : ℝ) ^ 2 ≤
      (3 * Real.exp 20 * (Y : ℝ)) / (Y : ℝ) ^ 2 := by
    exact div_le_div_of_nonneg_right h3 (by positivity)
  refine h4.trans_eq ?_
  field_simp

lemma sum_sq_card_restrictedDivisors_dyadic_le (P : Finset ℕ) (Y₁ : ℕ) (hY₁ : 2 ≤ Y₁)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hP : ∀ p ∈ P, Y₁ ≤ p ∧ p ≤ 2 * Y₁)
    (Y₀ : ℕ) (hY₀ : 1 ≤ Y₀) (K : ℕ) :
    (∑ n ∈ Finset.Ioc Y₀ (2 ^ K * Y₀), ((restrictedDivisors P n).card : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤
      6 * Real.exp 20 / (Y₀ : ℝ) := by
  rw [← sum_Ioc_dyadic_telescope (fun n => ((restrictedDivisors P n).card : ℝ) ^ 2 / (n : ℝ) ^ 2) Y₀ K]
  have h_term_k (k : ℕ) (_hk : k ∈ Finset.range K) :
      (∑ n ∈ Finset.Ioc (2 ^ k * Y₀) (2 ^ (k + 1) * Y₀),
        ((restrictedDivisors P n).card : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤
      (3 * Real.exp 20 / (Y₀ : ℝ)) * (1 / (2 : ℝ) ^ k) := by
    have h_two_pow : 2 ^ (k + 1) * Y₀ = 2 * (2 ^ k * Y₀) := by
      rw [pow_succ 2 k]
      ring
    rw [h_two_pow]
    have h_ge : 1 ≤ 2 ^ k * Y₀ := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      have : 1 ≤ 1 * Y₀ := by omega
      nlinarith
    have h_bound := sum_sq_card_div_sq_le P Y₁ hY₁ hprime hP (2 ^ k * Y₀) h_ge
    refine h_bound.trans ?_
    have h_cast : ((2 ^ k * Y₀ : ℕ) : ℝ) = (2 : ℝ) ^ k * (Y₀ : ℝ) := by push_cast; rfl
    rw [h_cast]
    have : (3 * Real.exp 20) / ((2 : ℝ) ^ k * (Y₀ : ℝ)) =
        (3 * Real.exp 20 / (Y₀ : ℝ)) * (1 / (2 : ℝ) ^ k) := by
      ring
    rw [this]
  have h_sum := Finset.sum_le_sum h_term_k
  refine h_sum.trans ?_
  rw [← Finset.mul_sum]
  have h2 := sum_range_inv_two_pow_le_two K
  have h_nonneg : 0 ≤ 3 * Real.exp 20 / (Y₀ : ℝ) := by positivity
  have h_mul := mul_le_mul_of_nonneg_left h2 h_nonneg
  calc (3 * Real.exp 20 / (Y₀ : ℝ)) * ∑ k ∈ Finset.range K, 1 / (2 : ℝ) ^ k
    _ ≤ (3 * Real.exp 20 / (Y₀ : ℝ)) * 2 := h_mul
    _ = 6 * Real.exp 20 / (Y₀ : ℝ) := by ring

/-! ### Part 3: Moment polynomial coefficients and algebraic identity -/

def momentCoeff (c a : ℕ → ℂ) (P A : Finset ℕ) (ℓ n : ℕ) : ℂ :=
  ∑ x ∈ (A ×ˢ Fintype.piFinset (fun _ : Fin ℓ => P)).filter (fun x => x.1 * ∏ i, x.2 i = n),
    a x.1 * ∏ i, c (x.2 i)

lemma norm_momentCoeff_le (c a : ℕ → ℂ) (P A : Finset ℕ) (ℓ n : ℕ)
    (hc : ∀ p, ‖c p‖ ≤ 1) (ha : ∀ m, ‖a m‖ ≤ 1) :
    ‖momentCoeff c a P A ℓ n‖ ≤ (repCount A P ℓ n : ℝ) := by
  unfold momentCoeff repCount
  refine (norm_sum_le _ _).trans ?_
  have h_le : (∑ x ∈ (A ×ˢ Fintype.piFinset fun _ : Fin ℓ => P).filter (fun x => x.1 * ∏ i, x.2 i = n),
      ‖a x.1 * ∏ i, c (x.2 i)‖) ≤
      ∑ x ∈ (A ×ˢ Fintype.piFinset fun _ : Fin ℓ => P).filter (fun x => x.1 * ∏ i, x.2 i = n), 1 := by
    apply Finset.sum_le_sum
    intro x _hx
    rw [norm_mul, norm_prod]
    have h1 : ‖a x.1‖ ≤ 1 := ha (x.1)
    have h2 : ∏ i : Fin ℓ, ‖c (x.2 i)‖ ≤ ∏ i : Fin ℓ, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i _hi; positivity
      · intro i _hi; exact hc (x.2 i)
    simp only [Finset.prod_const_one] at h2
    have h_prod := mul_le_mul h1 h2 (by positivity) (by positivity)
    rwa [mul_one] at h_prod
  refine h_le.trans ?_
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, le_refl]

lemma momentCoeff_eq_zero_of_repCount_eq_zero (c a : ℕ → ℂ) {P A : Finset ℕ} {ℓ n : ℕ}
    (h : repCount A P ℓ n = 0) : momentCoeff c a P A ℓ n = 0 := by
  unfold momentCoeff
  rw [repCount, Finset.card_eq_zero] at h
  rw [h, Finset.sum_empty]

lemma dirichletPoly_pow_eq_mc (c : ℕ → ℂ) (P : Finset ℕ) (ℓ : ℕ) (s : ℂ) :
    (dirichletPoly c P s) ^ ℓ =
      ∑ v ∈ Fintype.piFinset (fun _ : Fin ℓ => P), (∏ i, c (v i)) * ((∏ i, v i : ℕ) : ℂ) ^ (-s) := by
  unfold dirichletPoly
  rw [sum_pow_piFinset]
  apply Finset.sum_congr rfl
  intro v _hv
  rw [Finset.prod_mul_distrib]
  congr 1
  exact (prod_natCast_cpow Finset.univ v (-s))

lemma prod_pos_of_mem_piFinset {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) {ℓ : ℕ}
    {v : Fin ℓ → ℕ} (hv : v ∈ Fintype.piFinset (fun _ : Fin ℓ => P)) : 0 < ∏ i, v i := by
  apply Finset.prod_pos
  intro i _hi
  exact hP (v i) (Fintype.mem_piFinset.mp hv i)

lemma dirichletPoly_pow_mul_eq (c a : ℕ → ℂ) (P A : Finset ℕ) (ℓ : ℕ) (s : ℂ)
    (hP : ∀ p ∈ P, 0 < p) (hA : ∀ m ∈ A, 0 < m) :
    (dirichletPoly c P s) ^ ℓ * dirichletPoly a A s =
      ∑ x ∈ A ×ˢ Fintype.piFinset (fun _ : Fin ℓ => P),
        (a x.1 * ∏ i, c (x.2 i)) * ((x.1 * ∏ i, x.2 i : ℕ) : ℂ) ^ (-s) := by
  rw [mul_comm, dirichletPoly, dirichletPoly_pow_eq_mc]
  rw [Finset.sum_mul_sum]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro v hv
  have hm_pos : 0 < m := hA m hm
  have hv_pos : 0 < ∏ i, v i := prod_pos_of_mem_piFinset hP hv
  rw [natCast_cpow_neg_mul m (∏ i, v i) hm_pos hv_pos s]
  ring

lemma dirichletPoly_pow_mul_eq_dirichletPoly (c a : ℕ → ℂ) (P A : Finset ℕ) (ℓ : ℕ) (s : ℂ)
    (hP : ∀ p ∈ P, 0 < p) (hA : ∀ m ∈ A, 0 < m) (N : ℕ)
    (hsupp : ∀ x ∈ A ×ˢ Fintype.piFinset (fun _ : Fin ℓ => P), x.1 * ∏ i, x.2 i ∈ Finset.Ioc 0 N) :
    (dirichletPoly c P s) ^ ℓ * dirichletPoly a A s =
      dirichletPoly (momentCoeff c a P A ℓ) (Finset.Ioc 0 N) s := by
  rw [dirichletPoly_pow_mul_eq c a P A ℓ s hP hA]
  unfold dirichletPoly
  let S := A ×ˢ Fintype.piFinset (fun _ : Fin ℓ => P)
  let g : (ℕ × (Fin ℓ → ℕ)) → ℕ := fun x => x.1 * ∏ i, x.2 i
  have h_fib := Finset.sum_fiberwise_of_maps_to (g := g) (s := S) (t := Finset.Ioc 0 N) hsupp
    (fun x => (a x.1 * ∏ i, c (x.2 i)) * ((x.1 * ∏ i, x.2 i : ℕ) : ℂ) ^ (-s))
  rw [← h_fib]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold momentCoeff
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_filter] at hx
  have hx_eq : x.1 * ∏ i, x.2 i = n := hx.2
  rw [hx_eq]

lemma sum_momentCoeff_sq_div_sq_le
    (c a : ℕ → ℂ) (P A : Finset ℕ) (ℓ : ℕ) (Y₁ X Y₂ : ℕ)
    (hY₁ : 2 ≤ Y₁) (hY₂ : 1 ≤ Y₂) (hXY : Y₂ ≤ X) (hℓ : 1 ≤ ℓ)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hP : ∀ p ∈ P, Y₁ ≤ p ∧ p ≤ 2 * Y₁)
    (hA : ∀ m ∈ A, X / Y₂ ≤ m ∧ m ≤ 2 * X / Y₂)
    (hc : ∀ p, ‖c p‖ ≤ 1) (ha : ∀ m, ‖a m‖ ≤ 1) :
    (∑ n ∈ Finset.Ioc 0 ((2 * X / Y₂) * (2 ^ ℓ * Y₁ ^ ℓ)),
      ‖momentCoeff c a P A ℓ n‖ ^ 2 / (n : ℝ) ^ 2) ≤
    24 * Real.exp 20 * ((ℓ.factorial : ℝ) ^ 2) * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) := by
  let N := (2 * X / Y₂) * (2 ^ ℓ * Y₁ ^ ℓ)
  let n_min := (X / Y₂) * Y₁ ^ ℓ
  let Y₀ := n_min - 1
  let K := ℓ + 3
  have hq : 1 ≤ X / Y₂ := by
    rw [Nat.one_le_div_iff (by omega)]
    exact hXY
  have hY1_pow : 2 ≤ Y₁ ^ ℓ := by
    have h1 : 2 ≤ 2 ^ ℓ := by
      have := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hℓ
      omega
    have h2 : 2 ^ ℓ ≤ Y₁ ^ ℓ := Nat.pow_le_pow_left hY₁ ℓ
    omega
  have hn_min_ge : 2 ≤ n_min := by
    calc 2 = 1 * 2 := rfl
    _ ≤ (X / Y₂) * Y₁ ^ ℓ := Nat.mul_le_mul hq hY1_pow
  have hY0 : 1 ≤ Y₀ := by omega
  have h_div4 : 2 * X / Y₂ ≤ 4 * (X / Y₂) := div_two_mul_le_four_mul_div X Y₂ hY₂ hXY
  have hN_le1 : N ≤ 4 * (X / Y₂) * (2 ^ ℓ * Y₁ ^ ℓ) := Nat.mul_le_mul_right _ h_div4
  have h_two_Y0 : n_min ≤ 2 * Y₀ := by omega
  have h_pow_succ : 2 ^ K * Y₀ = 2 ^ (ℓ + 2) * (2 * Y₀) := by
    rw [show K = (ℓ + 2) + 1 from rfl, pow_succ]
    ring
  have hN_le_K : N ≤ 2 ^ K * Y₀ := by
    calc N ≤ 4 * (X / Y₂) * (2 ^ ℓ * Y₁ ^ ℓ) := hN_le1
    _ = (4 * 2 ^ ℓ) * ((X / Y₂) * Y₁ ^ ℓ) := by ring
    _ = 2 ^ (ℓ + 2) * n_min := by
      dsimp [n_min]
      have : 4 * 2 ^ ℓ = 2 ^ (ℓ + 2) := by
        rw [show 4 = 2 ^ 2 from rfl, ← pow_add]
        ring
      rw [this]
    _ ≤ 2 ^ (ℓ + 2) * (2 * Y₀) := Nat.mul_le_mul_left _ h_two_Y0
    _ = 2 ^ K * Y₀ := h_pow_succ.symm
  have h_filter_eq : (∑ n ∈ Finset.Ioc 0 N, ‖momentCoeff c a P A ℓ n‖ ^ 2 / (n : ℝ) ^ 2) =
      ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => n_min ≤ n), ‖momentCoeff c a P A ℓ n‖ ^ 2 / (n : ℝ) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 N) (fun n => n_min ≤ n)]
    have h_zero : (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => ¬(n_min ≤ n)),
        ‖momentCoeff c a P A ℓ n‖ ^ 2 / (n : ℝ) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      rw [Finset.mem_filter] at hn
      have hn_lt : n < n_min := by omega
      have h_rep := repCount_eq_zero_of_lt (fun p hp => (hP p hp).1) (fun m hm => (hA m hm).1) hn_lt
      have h_coeff := momentCoeff_eq_zero_of_repCount_eq_zero c a h_rep
      rw [h_coeff, norm_zero, zero_pow (by norm_num), zero_div]
    rw [h_zero, add_zero]
  rw [h_filter_eq]
  have h_sub : (Finset.Ioc 0 N).filter (fun n => n_min ≤ n) ⊆ Finset.Ioc Y₀ (2 ^ K * Y₀) := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    rw [Finset.mem_Ioc]
    refine ⟨by omega, by omega⟩
  have h_term_le (n : ℕ) (hn : n ∈ (Finset.Ioc 0 N).filter (fun n => n_min ≤ n)) :
      ‖momentCoeff c a P A ℓ n‖ ^ 2 / (n : ℝ) ^ 2 ≤
      ((ℓ.factorial : ℝ) ^ 2) * (((restrictedDivisors P n).card : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    have hn_pos : 0 < n := by omega
    have h_rep := repCount_le A P ℓ n (fun p hp => (hprime p hp)) hn_pos
    have h_norm := norm_momentCoeff_le c a P A ℓ n hc ha
    have h_le_fact : ‖momentCoeff c a P A ℓ n‖ ≤ (ℓ.factorial : ℝ) * ((restrictedDivisors P n).card : ℝ) := by
      exact h_norm.trans (by exact_mod_cast h_rep)
    have h_sq : ‖momentCoeff c a P A ℓ n‖ ^ 2 ≤ ((ℓ.factorial : ℝ) * ((restrictedDivisors P n).card : ℝ)) ^ 2 := by
      have : 0 ≤ ‖momentCoeff c a P A ℓ n‖ := norm_nonneg _
      have : 0 ≤ (ℓ.factorial : ℝ) * ((restrictedDivisors P n).card : ℝ) := by positivity
      nlinarith
    rw [mul_pow] at h_sq
    calc ‖momentCoeff c a P A ℓ n‖ ^ 2 / (n : ℝ) ^ 2 ≤
        (((ℓ.factorial : ℝ) ^ 2) * ((restrictedDivisors P n).card : ℝ) ^ 2) / (n : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right h_sq (by positivity)
    _ = ((ℓ.factorial : ℝ) ^ 2) * (((restrictedDivisors P n).card : ℝ) ^ 2 / (n : ℝ) ^ 2) := by ring
  have h_sum_filter_le :
      (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => n_min ≤ n), ‖momentCoeff c a P A ℓ n‖ ^ 2 / (n : ℝ) ^ 2) ≤
      ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => n_min ≤ n),
        ((ℓ.factorial : ℝ) ^ 2) * (((restrictedDivisors P n).card : ℝ) ^ 2 / (n : ℝ) ^ 2) :=
    Finset.sum_le_sum h_term_le
  refine h_sum_filter_le.trans ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun i _ _ => by positivity)).trans ?_
  rw [← Finset.mul_sum]
  have h_dyadic := sum_sq_card_restrictedDivisors_dyadic_le P Y₁ hY₁ hprime hP Y₀ hY0 K
  have h_mul_dyadic : ((ℓ.factorial : ℝ) ^ 2) * ∑ n ∈ Finset.Ioc Y₀ (2 ^ K * Y₀),
        ((restrictedDivisors P n).card : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤
      ((ℓ.factorial : ℝ) ^ 2) * (6 * Real.exp 20 / (Y₀ : ℝ)) := by
    exact mul_le_mul_of_nonneg_left h_dyadic (by positivity)
  refine h_mul_dyadic.trans ?_
  have h_inv_Y0 := inv_cast_sub_one_le (n := n_min) hn_min_ge
  have hn_min_cast : (n_min : ℝ) = ((X / Y₂ : ℕ) : ℝ) * (Y₁ : ℝ) ^ ℓ := by
    dsimp [n_min]
    push_cast
    rfl
  have h_inv_div := inv_cast_div_le X Y₂ hY₂ hXY
  have h_inv_n_min : (1 : ℝ) / (n_min : ℝ) ≤ 2 * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) := by
    rw [hn_min_cast, div_mul_eq_div_mul_one_div]
    have h_nonneg_inv : 0 ≤ 1 / (Y₁ : ℝ) ^ ℓ := by positivity
    have := mul_le_mul_of_nonneg_right h_inv_div h_nonneg_inv
    calc (1 : ℝ) / ((X / Y₂ : ℕ) : ℝ) * (1 / (Y₁ : ℝ) ^ ℓ)
      _ ≤ (2 * (Y₂ : ℝ) / (X : ℝ)) * (1 / (Y₁ : ℝ) ^ ℓ) := this
      _ = 2 * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) := by ring
  have h_step : 2 / (n_min : ℝ) = 2 * (1 / (n_min : ℝ)) := by ring
  have h_inv_Y0_rw : (1 : ℝ) / (Y₀ : ℝ) ≤ 2 * (1 / (n_min : ℝ)) := by
    have : (Y₀ : ℝ) = ((n_min - 1 : ℕ) : ℝ) := rfl
    rw [this]
    exact h_inv_Y0.trans (by rw [h_step])
  have := mul_le_mul_of_nonneg_left h_inv_n_min (by norm_num : (0 : ℝ) ≤ 2)
  have h_inv_Y0_final : (1 : ℝ) / (Y₀ : ℝ) ≤ 4 * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) := by
    calc (1 : ℝ) / (Y₀ : ℝ) ≤ 2 * (1 / (n_min : ℝ)) := h_inv_Y0_rw
    _ ≤ 2 * (2 * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) := this
    _ = 4 * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) := by ring
  have h_div_bound : 6 * Real.exp 20 / (Y₀ : ℝ) ≤
      24 * Real.exp 20 * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) := by
    have h_rw : 6 * Real.exp 20 / (Y₀ : ℝ) = (6 * Real.exp 20) * (1 / (Y₀ : ℝ)) := by ring
    rw [h_rw]
    have := mul_le_mul_of_nonneg_left h_inv_Y0_final (by positivity : 0 ≤ 6 * Real.exp 20)
    calc (6 * Real.exp 20) * (1 / (Y₀ : ℝ))
      _ ≤ (6 * Real.exp 20) * (4 * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) := this
      _ = 24 * Real.exp 20 * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) := by ring
  have := mul_le_mul_of_nonneg_left h_div_bound (by positivity : 0 ≤ ((ℓ.factorial : ℝ) ^ 2))
  calc ((ℓ.factorial : ℝ) ^ 2) * (6 * Real.exp 20 / (Y₀ : ℝ))
    _ ≤ ((ℓ.factorial : ℝ) ^ 2) * (24 * Real.exp 20 * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) := this
    _ = 24 * Real.exp 20 * ((ℓ.factorial : ℝ) ^ 2) * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) := by ring

/-! ### Part 4: Main Moment Computation Theorems -/

lemma integral_norm_sq_poly_pow_eq (c a : ℕ → ℂ) (P A : Finset ℕ) (ℓ N : ℕ)
    (hP_pos : ∀ p ∈ P, 0 < p) (hA_pos : ∀ m ∈ A, 0 < m)
    (hsupp : ∀ x ∈ A ×ˢ Fintype.piFinset (fun _ : Fin ℓ => P), x.1 * ∏ i, x.2 i ∈ Finset.Ioc 0 N) (T : ℝ) :
    (∫ t in (-T)..T, ‖(dirichletPoly c P ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
        dirichletPoly a A ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) =
      ∫ t in (-T)..T, ‖dirichletPoly (momentCoeff c a P A ℓ) (Finset.Ioc 0 N) ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
  have h_eq : (fun t : ℝ => ‖(dirichletPoly c P ((1 : ℂ) + (t : ℝ) * Complex.I)) ^ ℓ *
        dirichletPoly a A ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2) =
      fun t : ℝ => ‖dirichletPoly (momentCoeff c a P A ℓ) (Finset.Ioc 0 N) ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 := by
    ext t
    rw [dirichletPoly_pow_mul_eq_dirichletPoly c a P A ℓ ((1 : ℂ) + (t : ℝ) * Complex.I) hP_pos hA_pos N hsupp]
  rw [h_eq]

/-- General form of Matomäki–Radziwiłł Lemma 13: valid for arbitrary parameters $Y_1, Y_2, X, \ell$. -/
theorem integral_norm_sq_prime_poly_pow_mul_le_general :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y₁ Y₂ X : ℕ) (c a : ℕ → ℂ) (T : ℝ) (ℓ : ℕ),
      2 ≤ Y₁ → 1 ≤ Y₂ → Y₂ ≤ X → 0 ≤ T → 1 ≤ ℓ →
      (∀ p, ‖c p‖ ≤ 1) → (∀ m, ‖a m‖ ≤ 1) →
      ∫ t in (-T)..T, ‖(dirichletPoly c ((Finset.Icc Y₁ (2 * Y₁)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
          dirichletPoly a ((Finset.Ioc 0 (2 * X / Y₂)).filter (fun m => X / Y₂ ≤ m)) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y₁ : ℝ)) * (((ℓ + 1).factorial : ℝ) ^ 2) := by
  let C := 24 * Real.exp 20 * (2 + 6 * Real.pi)
  have hC_pos : 0 < C := by
    dsimp [C]
    have : 0 < Real.pi := Real.pi_pos
    positivity
  use C, hC_pos
  intro Y₁ Y₂ X c a T ℓ hY₁ hY₂ hXY hT hℓ hc ha
  let P := (Finset.Icc Y₁ (2 * Y₁)).filter Nat.Prime
  let A := (Finset.Ioc 0 (2 * X / Y₂)).filter (fun m => X / Y₂ ≤ m)
  let N := (2 * X / Y₂) * (2 ^ ℓ * Y₁ ^ ℓ)
  have hprime : ∀ p ∈ P, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have hP : ∀ p ∈ P, Y₁ ≤ p ∧ p ≤ 2 * Y₁ := by
    intro p hp
    have h := (Finset.mem_filter.mp hp).1
    rw [Finset.mem_Icc] at h
    exact h
  have hA : ∀ m ∈ A, X / Y₂ ≤ m ∧ m ≤ 2 * X / Y₂ := by
    intro m hm
    have h1 := (Finset.mem_filter.mp hm).1
    have h2 := (Finset.mem_filter.mp hm).2
    rw [Finset.mem_Ioc] at h1
    exact ⟨h2, h1.2⟩
  have hP_pos : ∀ p ∈ P, 0 < p := by
    intro p hp
    have := (hP p hp).1
    omega
  have hA_pos : ∀ m ∈ A, 0 < m := by
    intro m hm
    have hq : 1 ≤ X / Y₂ := by
      rw [Nat.one_le_div_iff (by omega)]
      exact hXY
    have := (hA m hm).1
    omega
  have hsupp : ∀ x ∈ A ×ˢ Fintype.piFinset (fun _ : Fin ℓ => P), x.1 * ∏ i, x.2 i ∈ Finset.Ioc 0 N := by
    intro x hx
    rw [Finset.mem_product] at hx
    have hm := hA x.1 hx.1
    have hv := prod_piFinset_le_of_mem Y₁ (fun p hp => (hP p hp).2) hx.2
    have h_prod_pos : 0 < x.1 * ∏ i, x.2 i := by
      have : 0 < x.1 := hA_pos x.1 hx.1
      have : 0 < ∏ i, x.2 i := prod_pos_of_mem_piFinset hP_pos hx.2
      positivity
    have h_prod_le : x.1 * ∏ i, x.2 i ≤ N := Nat.mul_le_mul hm.2 hv
    rw [Finset.mem_Ioc]
    exact ⟨h_prod_pos, h_prod_le⟩
  rw [integral_norm_sq_poly_pow_eq c a P A ℓ N hP_pos hA_pos hsupp T]
  have h_mvt := integral_norm_sq_dirichletPoly_le_mul (momentCoeff c a P A ℓ) N T hT
  refine h_mvt.trans ?_
  have h_sum_coeff := sum_momentCoeff_sq_div_sq_le c a P A ℓ Y₁ X Y₂
    hY₁ hY₂ hXY hℓ hprime hP hA hc ha
  have h_mvt_mul : (2 * T + 6 * Real.pi * (N : ℝ)) *
      ∑ n ∈ Finset.Ioc 0 N, ‖momentCoeff c a P A ℓ n‖ ^ 2 / (n : ℝ) ^ 2 ≤
      (2 * T + 6 * Real.pi * (N : ℝ)) *
        (24 * Real.exp 20 * ((ℓ.factorial : ℝ) ^ 2) * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) := by
    have h_nonneg : 0 ≤ 2 * T + 6 * Real.pi * (N : ℝ) := by
      have : 0 ≤ Real.pi := Real.pi_pos.le
      positivity
    exact mul_le_mul_of_nonneg_left h_sum_coeff h_nonneg
  refine h_mvt_mul.trans ?_
  have hN_cast : (N : ℝ) = ((2 * X / Y₂ : ℕ) : ℝ) * (2 : ℝ) ^ ℓ * (Y₁ : ℝ) ^ ℓ := by
    dsimp [N]
    push_cast
    ring
  have h_div_le : ((2 * X / Y₂ : ℕ) : ℝ) ≤ 2 * (X : ℝ) / (Y₂ : ℝ) := by
    have h := (Nat.cast_div_le : ((2 * X / Y₂ : ℕ) : ℝ) ≤ ((2 * X : ℕ) : ℝ) / (Y₂ : ℝ))
    push_cast at h
    exact h
  have hN_le : (N : ℝ) ≤ 2 * (X : ℝ) / (Y₂ : ℝ) * (2 : ℝ) ^ ℓ * (Y₁ : ℝ) ^ ℓ := by
    rw [hN_cast]
    have h_pos : 0 ≤ (2 : ℝ) ^ ℓ * (Y₁ : ℝ) ^ ℓ := by positivity
    calc ((2 * X / Y₂ : ℕ) : ℝ) * (2 : ℝ) ^ ℓ * (Y₁ : ℝ) ^ ℓ
      _ = ((2 * X / Y₂ : ℕ) : ℝ) * ((2 : ℝ) ^ ℓ * (Y₁ : ℝ) ^ ℓ) := by ring
      _ ≤ (2 * (X : ℝ) / (Y₂ : ℝ)) * ((2 : ℝ) ^ ℓ * (Y₁ : ℝ) ^ ℓ) := mul_le_mul_of_nonneg_right h_div_le h_pos
      _ = 2 * (X : ℝ) / (Y₂ : ℝ) * (2 : ℝ) ^ ℓ * (Y₁ : ℝ) ^ ℓ := by ring
  have hX_pos : 0 < (X : ℝ) := by
    have : 1 ≤ X := by omega
    positivity
  have hY2_pos : 0 < (Y₂ : ℝ) := by
    have : 1 ≤ Y₂ := hY₂
    positivity
  have hY1_pos : 0 < (Y₁ : ℝ) := by
    have : 2 ≤ Y₁ := hY₁
    positivity
  have hY1_pow_pos : 0 < (Y₁ : ℝ) ^ ℓ := by positivity
  have hN_mul : (N : ℝ) * ((Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) ≤ (2 : ℝ) ^ ℓ * (Y₁ : ℝ) := by
    have h_prod_le : (N : ℝ) * ((Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) ≤
        (2 * (X : ℝ) / (Y₂ : ℝ) * (2 : ℝ) ^ ℓ * (Y₁ : ℝ) ^ ℓ) * ((Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) := by
      have : 0 ≤ (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) := by positivity
      exact mul_le_mul_of_nonneg_right hN_le this
    have h_cancel : (2 * (X : ℝ) / (Y₂ : ℝ) * (2 : ℝ) ^ ℓ * (Y₁ : ℝ) ^ ℓ) * ((Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) =
        2 * (2 : ℝ) ^ ℓ := by
      field_simp
      try ring
    have hY1_ge2 : (2 : ℝ) ≤ (Y₁ : ℝ) := by exact_mod_cast hY₁
    have h_le_pow : 2 * (2 : ℝ) ^ ℓ ≤ (2 : ℝ) ^ ℓ * (Y₁ : ℝ) := by
      have : 0 ≤ (2 : ℝ) ^ ℓ := by positivity
      nlinarith
    linarith
  have h_fact_sq_le : ((ℓ.factorial : ℝ) ^ 2) ≤ (((ℓ + 1).factorial : ℝ) ^ 2) := by
    have h_fact_le : (ℓ.factorial : ℝ) ≤ ((ℓ + 1).factorial : ℝ) := by
      have : ℓ.factorial ≤ (ℓ + 1).factorial := Nat.factorial_le (by omega)
      exact_mod_cast this
    have : 0 ≤ (ℓ.factorial : ℝ) := by positivity
    nlinarith
  have h_bracket : (2 * T + 6 * Real.pi * (N : ℝ)) *
      (24 * Real.exp 20 * ((ℓ.factorial : ℝ) ^ 2) * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) =
      (24 * Real.exp 20 * ((ℓ.factorial : ℝ) ^ 2)) *
        (2 * (T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) + 6 * Real.pi * ((N : ℝ) * ((Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)))) := by
    ring
  rw [h_bracket]
  have h_inside : 2 * (T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) + 6 * Real.pi * ((N : ℝ) * ((Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ))) ≤
      (2 + 6 * Real.pi) * (T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y₁ : ℝ)) := by
    have h_term2 : 6 * Real.pi * ((N : ℝ) * ((Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ))) ≤
        6 * Real.pi * ((2 : ℝ) ^ ℓ * (Y₁ : ℝ)) := by
      have : 0 ≤ 6 * Real.pi := by
        have : 0 ≤ Real.pi := Real.pi_pos.le
        positivity
      exact mul_le_mul_of_nonneg_left hN_mul this
    calc 2 * (T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) + 6 * Real.pi * ((N : ℝ) * ((Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)))
      _ ≤ 2 * (T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ)) + 6 * Real.pi * ((2 : ℝ) ^ ℓ * (Y₁ : ℝ)) := by linarith
      _ ≤ (2 + 6 * Real.pi) * (T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y₁ : ℝ)) := by
        have : 0 ≤ T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) := by positivity
        have : 0 ≤ (2 : ℝ) ^ ℓ * (Y₁ : ℝ) := by positivity
        have : 0 ≤ Real.pi := Real.pi_pos.le
        nlinarith
  have h_const_nonneg : 0 ≤ 24 * Real.exp 20 * ((ℓ.factorial : ℝ) ^ 2) := by positivity
  have h_mul_all := mul_le_mul_of_nonneg_left h_inside h_const_nonneg
  refine h_mul_all.trans ?_
  have h_c_eq : (24 * Real.exp 20 * ((ℓ.factorial : ℝ) ^ 2)) *
        ((2 + 6 * Real.pi) * (T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y₁ : ℝ))) =
      C * (T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y₁ : ℝ)) * ((ℓ.factorial : ℝ) ^ 2) := by
    dsimp [C]
    ring
  rw [h_c_eq]
  have h_c_nonneg : 0 ≤ C * (T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y₁ : ℝ)) := by
    dsimp [C]
    positivity
  exact mul_le_mul_of_nonneg_left h_fact_sq_le h_c_nonneg

/-- Matomäki–Radziwiłł Lemma 13 (moment computation) with the paper's support hypothesis $Y_2 \le Y_1^\ell$. -/
theorem integral_norm_sq_prime_poly_pow_mul_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y₁ Y₂ X : ℕ) (c a : ℕ → ℂ) (T : ℝ) (ℓ : ℕ),
      2 ≤ Y₁ → 1 ≤ Y₂ → Y₂ ≤ X → 0 ≤ T → 1 ≤ ℓ → Y₂ ≤ Y₁ ^ ℓ →
      (∀ p, ‖c p‖ ≤ 1) → (∀ m, ‖a m‖ ≤ 1) →
      ∫ t in (-T)..T, ‖(dirichletPoly c ((Finset.Icc Y₁ (2 * Y₁)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
          dirichletPoly a ((Finset.Ioc 0 (2 * X / Y₂)).filter (fun m => X / Y₂ ≤ m)) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (T / X + 2 ^ ℓ * Y₁) * ((ℓ + 1).factorial : ℝ) ^ 2 := by
  obtain ⟨C, hC_pos, hC⟩ := integral_norm_sq_prime_poly_pow_mul_le_general
  use C, hC_pos
  intro Y₁ Y₂ X c a T ℓ hY₁ hY₂ hXY hT hℓ hY2_le hc ha
  have h_gen := hC Y₁ Y₂ X c a T ℓ hY₁ hY₂ hXY hT hℓ hc ha
  refine h_gen.trans ?_
  have hX_pos : 0 < (X : ℝ) := by
    have : 1 ≤ X := by omega
    positivity
  have hY1_pow_pos : 0 < (Y₁ : ℝ) ^ ℓ := by
    have : 2 ≤ Y₁ := hY₁
    positivity
  have h_div_le : (Y₂ : ℝ) / (Y₁ : ℝ) ^ ℓ ≤ 1 := by
    rw [div_le_one₀ hY1_pow_pos]
    exact_mod_cast hY2_le
  have h_t_le : T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) ≤ T / (X : ℝ) := by
    rw [show T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) = (T / (X : ℝ)) * ((Y₂ : ℝ) / (Y₁ : ℝ) ^ ℓ) by ring]
    have : 0 ≤ T / (X : ℝ) := by positivity
    calc (T / (X : ℝ)) * ((Y₂ : ℝ) / (Y₁ : ℝ) ^ ℓ)
      _ ≤ (T / (X : ℝ)) * 1 := mul_le_mul_of_nonneg_left h_div_le this
      _ = T / (X : ℝ) := by ring
  have h_bracket : T * (Y₂ : ℝ) / ((X : ℝ) * (Y₁ : ℝ) ^ ℓ) + (2 : ℝ) ^ ℓ * (Y₁ : ℝ) ≤
      T / (X : ℝ) + (2 : ℝ) ^ ℓ * (Y₁ : ℝ) := by
    linarith
  have h_c_nonneg : 0 ≤ C := hC_pos.le
  have h_fact_nonneg : 0 ≤ ((ℓ + 1).factorial : ℝ) ^ 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_left h_bracket h_c_nonneg
  exact mul_le_mul_of_nonneg_right h1 h_fact_nonneg

end Erdos1201.MR
