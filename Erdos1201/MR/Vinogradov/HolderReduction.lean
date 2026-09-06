import Mathlib
import Erdos1201.MR.Vinogradov.CurveCounts

/-!
# Reduction of Bilinear Sum to Box Linear Sum via Hölder

This module establishes Tao's inequalities (16) and (18) for the Vinogradov
bilinear sum, reducing the bilinear exponential sum to a linear sum over the box.

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

noncomputable section

namespace Erdos1201.MR.Vinogradov

open scoped BigOperators

/-- The bilinear form B(x,y) = ∑_j α_j x_j y_j. -/
def bilinearForm (k : ℕ) (α : Fin k → ℝ) (x y : Fin k → ℤ) : ℝ := ∑ j, α j * x j * y j

/-- The bilinear exponential sum S = (1/M²) ∑_{a,b ≤ M} e(∑ α_j a^j b^j). -/
noncomputable def bilinearSum (k M : ℕ) (α : Fin k → ℝ) : ℂ :=
  (1 / (M : ℂ) ^ 2) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ∑ b ∈ Finset.Icc (1 : ℤ) M,
    Complex.exp (2 * Real.pi * Complex.I * (bilinearForm k α (momentCurve k a) (momentCurve k b)))

/-- Linearity of the bilinear form in the second argument for addition. -/
lemma bilinearForm_add_right (k : ℕ) (α : Fin k → ℝ) (x y₁ y₂ : Fin k → ℤ) :
    bilinearForm k α x (y₁ + y₂) = bilinearForm k α x y₁ + bilinearForm k α x y₂ := by
  dsimp [bilinearForm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- Linearity of the bilinear form in the second argument for subtraction. -/
lemma bilinearForm_sub_right (k : ℕ) (α : Fin k → ℝ) (x y₁ y₂ : Fin k → ℤ) :
    bilinearForm k α x (y₁ - y₂) = bilinearForm k α x y₁ - bilinearForm k α x y₂ := by
  dsimp [bilinearForm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- Linearity of the bilinear form in the first argument for subtraction. -/
lemma bilinearForm_sub_left (k : ℕ) (α : Fin k → ℝ) (x₁ x₂ y : Fin k → ℤ) :
    bilinearForm k α (x₁ - x₂) y = bilinearForm k α x₁ y - bilinearForm k α x₂ y := by
  dsimp [bilinearForm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

/-- Linearity of the bilinear form in the second argument for finite sums. -/
lemma bilinearForm_sum_right {ι : Type*} (s : Finset ι) (k : ℕ) (α : Fin k → ℝ) (x : Fin k → ℤ) (y : ι → Fin k → ℤ) :
    bilinearForm k α x (∑ i ∈ s, y i) = ∑ i ∈ s, bilinearForm k α x (y i) := by
  dsimp [bilinearForm]
  simp_rw [Finset.sum_apply, Int.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Linearity of the bilinear form in the first argument for finite sums. -/
lemma bilinearForm_sum_left {ι : Type*} (s : Finset ι) (k : ℕ) (α : Fin k → ℝ) (x : ι → Fin k → ℤ) (y : Fin k → ℤ) :
    bilinearForm k α (∑ i ∈ s, x i) y = ∑ i ∈ s, bilinearForm k α (x i) y := by
  dsimp [bilinearForm]
  rw [← Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have : (∑ i ∈ s, x i) j = ∑ i ∈ s, (x i) j := Finset.sum_apply j s x
  rw [this, Int.cast_sum, Finset.mul_sum, Finset.sum_mul]

lemma star_exp_two_pi_I (θ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (θ : ℂ))) =
      Complex.exp (-(2 * Real.pi * Complex.I * (θ : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma exp_two_pi_I_sub (θ₁ θ₂ : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (θ₁ : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (θ₂ : ℂ))) =
    Complex.exp (2 * Real.pi * Complex.I * ((θ₁ - θ₂ : ℝ) : ℂ)) := by
  rw [star_exp_two_pi_I]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma exp_sum_bilinear_right (k ℓ : ℕ) (α : Fin k → ℝ) (x : Fin k → ℤ) (p : Fin ℓ → ℤ) :
    (∏ i : Fin ℓ, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α x (momentCurve k (p i)))) =
      Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α x (curveSum k ℓ p)) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, curveSum, bilinearForm_sum_right]
  rw [← Complex.ofReal_sum]

lemma exp_sum_bilinear_left (k ℓ : ℕ) (α : Fin k → ℝ) (p : Fin ℓ → ℤ) (y : Fin k → ℤ) :
    (∏ i : Fin ℓ, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k (p i)) y)) =
      Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ p) y) := by
  rw [← Complex.exp_sum]
  congr 1
  rw [← Finset.mul_sum, curveSum, bilinearForm_sum_left]
  rw [← Complex.ofReal_sum]

lemma curveSum_sub_mem_box (k ℓ M : ℕ) (u v : Fin ℓ → ℤ)
    (hu : u ∈ tuples ℓ M) (hv : v ∈ tuples ℓ M) :
    curveSum k ℓ u - curveSum k ℓ v ∈ box k ℓ M := by
  rw [mem_tuples_iff] at hu hv
  rw [box, Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_Icc, Pi.sub_apply, curveSum_apply, curveSum_apply]
  have h_le : ∀ w : Fin ℓ → ℤ, (∀ i, 1 ≤ w i ∧ w i ≤ (M : ℤ)) →
      0 ≤ ∑ i : Fin ℓ, (w i) ^ (j.val + 1) ∧
      ∑ i : Fin ℓ, (w i) ^ (j.val + 1) ≤ (ℓ : ℤ) * (M : ℤ) ^ (j.val + 1) := by
    intro w hw
    have h_nonneg : ∀ i : Fin ℓ, 0 ≤ (w i) ^ (j.val + 1) := by
      intro i
      have : 0 ≤ w i := by linarith [(hw i).1]
      exact pow_nonneg this (j.val + 1)
    have h_i_le : ∀ i : Fin ℓ, (w i) ^ (j.val + 1) ≤ (M : ℤ) ^ (j.val + 1) := by
      intro i
      have hw0 : 0 ≤ w i := by linarith [(hw i).1]
      exact pow_le_pow_left₀ hw0 (hw i).2 (j.val + 1)
    have h_sum_le : (∑ i : Fin ℓ, (w i) ^ (j.val + 1)) ≤ (ℓ : ℤ) * (M : ℤ) ^ (j.val + 1) := by
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin ℓ)) (fun i => (w i) ^ (j.val + 1)) ((M : ℤ) ^ (j.val + 1))
        (fun i _ => h_i_le i)
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
      exact this
    have h_sum_nonneg : 0 ≤ ∑ i : Fin ℓ, (w i) ^ (j.val + 1) := Finset.sum_nonneg (fun i _ => h_nonneg i)
    exact ⟨h_sum_nonneg, h_sum_le⟩
  obtain ⟨hu0, hu1⟩ := h_le u hu
  obtain ⟨hv0, hv1⟩ := h_le v hv
  constructor
  · linarith
  · linarith

lemma sum_curveSum_sub_le (k ℓ M : ℕ) (f : (Fin k → ℤ) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ u ∈ tuples ℓ M, ∑ v ∈ tuples ℓ M, f (curveSum k ℓ u - curveSum k ℓ v) ≤
      (J k ℓ M : ℝ) * ∑ x ∈ box k ℓ M, f x := by
  have h_maps : Set.MapsTo (fun uv : (Fin ℓ → ℤ) × (Fin ℓ → ℤ) => curveSum k ℓ uv.1 - curveSum k ℓ uv.2)
      ↑((tuples ℓ M) ×ˢ (tuples ℓ M)) ↑(box k ℓ M) := by
    rintro ⟨u, v⟩ huv
    simp only [Finset.mem_coe, Finset.mem_product] at huv
    exact curveSum_sub_mem_box k ℓ M u v huv.1 huv.2
  have h_prod : ∑ u ∈ tuples ℓ M, ∑ v ∈ tuples ℓ M, f (curveSum k ℓ u - curveSum k ℓ v) =
      ∑ uv ∈ (tuples ℓ M) ×ˢ (tuples ℓ M), f (curveSum k ℓ uv.1 - curveSum k ℓ uv.2) := by
    rw [Finset.sum_product]
  rw [h_prod]
  have h_fiber := Finset.sum_fiberwise_of_maps_to h_maps (fun uv => f (curveSum k ℓ uv.1 - curveSum k ℓ uv.2))
  rw [← h_fiber]
  have h_le_each : ∀ x ∈ box k ℓ M,
      ∑ uv ∈ ((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun uv => curveSum k ℓ uv.1 - curveSum k ℓ uv.2 = x),
        f (curveSum k ℓ uv.1 - curveSum k ℓ uv.2) ≤ (J k ℓ M : ℝ) * f x := by
    intro x _
    have h_const : ∀ uv ∈ ((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun uv => curveSum k ℓ uv.1 - curveSum k ℓ uv.2 = x),
        f (curveSum k ℓ uv.1 - curveSum k ℓ uv.2) = f x := by
      intro uv huv
      rw [Finset.mem_filter] at huv
      rw [huv.2]
    rw [Finset.sum_congr rfl h_const]
    rw [Finset.sum_const, nsmul_eq_mul]
    have h_card := card_filter_curveSum_sub_le k ℓ M x
    have h_card_r : (((tuples ℓ M) ×ˢ (tuples ℓ M)).filter (fun uv => curveSum k ℓ uv.1 - curveSum k ℓ uv.2 = x)).card ≤ (J k ℓ M : ℝ) := by
      exact_mod_cast h_card
    nlinarith [hf x]
  have h_sum_le := Finset.sum_le_sum h_le_each
  refine le_trans h_sum_le ?_
  rw [← Finset.mul_sum]

/-- Three-factor Hölder / Cauchy-Schwarz inequality for representation counts. -/
lemma three_factor_holder_le {ι : Type*} (s : Finset ι) (ν F : ι → ℝ)
    (hν : ∀ y ∈ s, 0 ≤ ν y) (hF : ∀ y ∈ s, 0 ≤ F y) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∑ y ∈ s, ν y * F y) ^ (2 * ℓ) ≤
      (∑ y ∈ s, ν y) ^ (2 * ℓ - 2) * (∑ y ∈ s, (ν y) ^ 2) * (∑ y ∈ s, (F y) ^ (2 * ℓ)) := by
  have h_sum_nonneg : 0 ≤ ∑ y ∈ s, ν y := Finset.sum_nonneg hν
  rcases eq_or_lt_of_le h_sum_nonneg with heq | hpos
  · have h_all_zero : ∀ y ∈ s, ν y = 0 := by
      intro y hy
      have h1 := Finset.single_le_sum (fun i hi => hν i hi) hy
      rw [← heq] at h1
      linarith [hν y hy]
    have h_prod_zero : (∑ y ∈ s, ν y * F y) = 0 := by
      have : ∀ y ∈ s, ν y * F y = 0 := fun y hy => by rw [h_all_zero y hy, zero_mul]
      rw [Finset.sum_congr rfl this, Finset.sum_const_zero]
    rw [h_prod_zero]
    have _h2l : 0 < 2 * ℓ := by omega
    rw [zero_pow (by omega)]
    refine mul_nonneg (mul_nonneg (pow_nonneg h_sum_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg fun i _ => pow_nonneg (hF i (by assumption)) _)
  · set S := ∑ y ∈ s, ν y
    have hS_pos : 0 < S := hpos
    set w : ι → ℝ := fun y => ν y / S
    have hw_nonneg : ∀ y ∈ s, 0 ≤ w y := fun y hy => div_nonneg (hν y hy) (le_of_lt hS_pos)
    have hw_sum : ∑ y ∈ s, w y = 1 := by
      dsimp [w]
      rw [← Finset.sum_div, div_self (ne_of_gt hS_pos)]
    have h_mean := Real.pow_arith_mean_le_arith_mean_pow s w F hw_nonneg hw_sum hF ℓ
    have hw_mul : ∀ y ∈ s, w y * F y = (1 / S) * (ν y * F y) := by
      intro y _
      dsimp [w]
      ring
    have hw_pow : ∀ y ∈ s, w y * (F y) ^ ℓ = (1 / S) * (ν y * (F y) ^ ℓ) := by
      intro y _
      dsimp [w]
      ring
    rw [Finset.sum_congr rfl hw_mul, ← Finset.mul_sum] at h_mean
    rw [Finset.sum_congr rfl hw_pow, ← Finset.mul_sum] at h_mean
    rw [mul_pow, one_div_pow] at h_mean
    have h_step1 : (∑ y ∈ s, ν y * F y) ^ ℓ ≤ S ^ (ℓ - 1) * ∑ y ∈ s, ν y * (F y) ^ ℓ := by
      have h_mul_S : S ^ ℓ * ((1 / S ^ ℓ) * (∑ y ∈ s, ν y * F y) ^ ℓ) ≤ S ^ ℓ * ((1 / S) * ∑ y ∈ s, ν y * (F y) ^ ℓ) := by
        gcongr
      have h_lhs : S ^ ℓ * ((1 / S ^ ℓ) * (∑ y ∈ s, ν y * F y) ^ ℓ) = (∑ y ∈ s, ν y * F y) ^ ℓ := by
        rw [← mul_assoc, mul_one_div_cancel (pow_ne_zero ℓ (ne_of_gt hS_pos)), one_mul]
      have h_rhs : S ^ ℓ * ((1 / S) * ∑ y ∈ s, ν y * (F y) ^ ℓ) = S ^ (ℓ - 1) * ∑ y ∈ s, ν y * (F y) ^ ℓ := by
        rw [← mul_assoc]
        have h_pow_eq : S ^ ℓ * (1 / S) = S ^ (ℓ - 1) := by
          rw [mul_one_div]
          have : ℓ = (ℓ - 1) + 1 := by omega
          conv_lhs => rw [this, pow_succ]
          rw [mul_div_cancel_right₀ (S ^ (ℓ - 1)) (ne_of_gt hS_pos)]
        rw [h_pow_eq]
      rwa [h_lhs, h_rhs] at h_mul_S
    have h_sq : ((∑ y ∈ s, ν y * F y) ^ ℓ) ^ 2 ≤ (S ^ (ℓ - 1) * ∑ y ∈ s, ν y * (F y) ^ ℓ) ^ 2 := by
      have h_nonneg_lhs : 0 ≤ (∑ y ∈ s, ν y * F y) ^ ℓ := by
        exact pow_nonneg (Finset.sum_nonneg fun y hy => mul_nonneg (hν y hy) (hF y hy)) ℓ
      nlinarith
    rw [← pow_mul, show ℓ * 2 = 2 * ℓ by omega] at h_sq
    rw [mul_pow, ← pow_mul] at h_sq
    have h_pow_exp : (ℓ - 1) * 2 = 2 * ℓ - 2 := by omega
    rw [h_pow_exp] at h_sq
    have h_cs := Finset.sum_mul_sq_le_sq_mul_sq s ν (fun y => (F y) ^ ℓ)
    have h_pow_sq : ∀ y ∈ s, ((F y) ^ ℓ) ^ 2 = (F y) ^ (2 * ℓ) := by
      intro y _
      rw [← pow_mul, show ℓ * 2 = 2 * ℓ by omega]
    rw [Finset.sum_congr rfl h_pow_sq] at h_cs
    have h_prod_le : S ^ (2 * ℓ - 2) * (∑ y ∈ s, ν y * (F y) ^ ℓ) ^ 2 ≤
        (S ^ (2 * ℓ - 2) * ∑ y ∈ s, (ν y) ^ 2) * ∑ y ∈ s, (F y) ^ (2 * ℓ) := by
      calc
        S ^ (2 * ℓ - 2) * (∑ y ∈ s, ν y * (F y) ^ ℓ) ^ 2
          ≤ S ^ (2 * ℓ - 2) * ((∑ y ∈ s, (ν y) ^ 2) * ∑ y ∈ s, (F y) ^ (2 * ℓ)) := by gcongr
        _ = (S ^ (2 * ℓ - 2) * ∑ y ∈ s, (ν y) ^ 2) * ∑ y ∈ s, (F y) ^ (2 * ℓ) := by ring
    exact le_trans h_sq h_prod_le

/-- Auxiliary phase factor for a complex number. -/
noncomputable def phase (z : ℂ) : ℂ := if z = 0 then 1 else (starRingEnd ℂ) z / (‖z‖ : ℂ)

lemma phase_mul_self (z : ℂ) : phase z * z = (‖z‖ : ℂ) := by
  dsimp [phase]
  split_ifs with hz
  · simp [hz]
  · rw [div_mul_eq_mul_div]
    have h_mul : (starRingEnd ℂ) z * z = (‖z‖ : ℂ) ^ 2 := by
      rw [mul_comm]
      have h1 : z * (starRingEnd ℂ) z = ↑(Complex.normSq z) := Complex.mul_conj z
      rw [h1]
      have h2 : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
      rw [h2]
      push_cast
      rfl
    rw [h_mul, sq]
    have hnz : (‖z‖ : ℂ) ≠ 0 := by simp [hz]
    exact mul_div_cancel_right₀ (‖z‖ : ℂ) hnz

lemma norm_phase_le (z : ℂ) : ‖phase z‖ ≤ 1 := by
  dsimp [phase]
  split_ifs with hz
  · simp
  · rw [norm_div]
    have h_norm_star : ‖(starRingEnd ℂ) z‖ = ‖z‖ := RCLike.norm_conj z
    rw [h_norm_star]
    have h_norm_ofReal : ‖(‖z‖ : ℂ)‖ = ‖z‖ := by
      rw [Complex.norm_def]
      simp only [Complex.normSq_ofReal]
      rw [← sq, Real.sqrt_sq (norm_nonneg z)]
    rw [h_norm_ofReal]
    have hnz : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [div_self hnz]

/-- Expansion of the ℓ-th power of the 1D exponential sum as a linear sum over the box. -/
lemma sum_exp_pow (k ℓ M : ℕ) (a : ℤ) (α : Fin k → ℝ) :
    (∑ b ∈ Finset.Icc (1 : ℤ) M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) (momentCurve k b))) ^ ℓ =
      ∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℂ) * Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) y) := by
  rw [Finset.sum_pow']
  have h_tuples : (Fintype.piFinset fun _ : Fin ℓ => Finset.Icc (1 : ℤ) M) = tuples ℓ M := rfl
  rw [h_tuples]
  have h_prod : ∀ p ∈ tuples ℓ M,
      (∏ i : Fin ℓ, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) (momentCurve k (p i)))) =
        Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) (curveSum k ℓ p)) := by
    intro p _
    exact exp_sum_bilinear_right k ℓ α (momentCurve k a) p
  rw [Finset.sum_congr rfl h_prod]
  have h_maps : Set.MapsTo (curveSum k ℓ) ↑(tuples ℓ M) ↑(box k ℓ M) := by
    intro p hp
    exact curveSum_mem_box k ℓ M p hp
  rw [← Finset.sum_fiberwise_of_maps_to h_maps]
  apply Finset.sum_congr rfl
  intro y _
  have h_const : ∀ p ∈ (tuples ℓ M).filter (fun p => curveSum k ℓ p = y),
      Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) (curveSum k ℓ p)) =
        Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) y) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [hp.2]
  rw [Finset.sum_congr rfl h_const]
  rw [Finset.sum_const, nsmul_eq_mul]
  dsimp [repCount]

/-- Reduction of the bilinear exponential sum to a linear sum over the box (Tao (18)). -/
theorem norm_bilinearSum_pow_le (k ℓ M : ℕ) (hℓ : 1 ≤ ℓ) (hM : 1 ≤ M) (α : Fin k → ℝ) :
    ‖bilinearSum k M α‖ ^ (2 * ℓ ^ 2) ≤
      (M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) ^ 2 *
        ∑ x ∈ box k ℓ M, ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α x y)‖ := by
  have hM_pos : 0 < (M : ℝ) := by positivity
  have hM_c_ne : (M : ℂ) ≠ 0 := by
    have : (M : ℝ) ≠ 0 := ne_of_gt hM_pos
    exact_mod_cast this
  have _hM_c_sq_ne : (M : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hM_c_ne
  set T : ℤ → ℂ := fun a => ∑ b ∈ Finset.Icc (1 : ℤ) M,
    Complex.exp (2 * Real.pi * Complex.I * (bilinearForm k α (momentCurve k a) (momentCurve k b)))
  have h_norm_inv_sq : ‖(1 : ℂ) / (M : ℂ) ^ 2‖ = 1 / (M : ℝ) ^ 2 := by
    rw [norm_div, norm_one, norm_pow]
    have : ‖(M : ℂ)‖ = (M : ℝ) := Complex.norm_natCast M
    rw [this]
  have h_sum_T_le : ‖∑ a ∈ Finset.Icc (1 : ℤ) M, T a‖ ≤ ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖ := norm_sum_le _ _
  have h_bilin_le : ‖bilinearSum k M α‖ ≤ (1 / (M : ℝ) ^ 2) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖ := by
    dsimp [bilinearSum]
    change ‖(1 / (M : ℂ) ^ 2) * ∑ a ∈ Finset.Icc (1 : ℤ) M, T a‖ ≤ _
    rw [norm_mul, h_norm_inv_sq]
    exact mul_le_mul_of_nonneg_left h_sum_T_le (by positivity)
  have h_mean_T : ((1 / (M : ℝ)) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖) ^ ℓ ≤
      (1 / (M : ℝ)) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖ ^ ℓ := by
    set w : ℤ → ℝ := fun _ => 1 / (M : ℝ)
    have hw_nonneg : ∀ a ∈ Finset.Icc (1 : ℤ) M, 0 ≤ w a := fun _ _ => by positivity
    have hw_sum : ∑ a ∈ Finset.Icc (1 : ℤ) M, w a = 1 := by
      dsimp [w]
      rw [Finset.sum_const, card_Icc_one_toNat, nsmul_eq_mul, mul_one_div_cancel (ne_of_gt hM_pos)]
    have h := Real.pow_arith_mean_le_arith_mean_pow (Finset.Icc (1 : ℤ) M) w (fun a => ‖T a‖) hw_nonneg hw_sum (fun a _ => norm_nonneg (T a)) ℓ
    dsimp [w] at h
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h
    exact h
  have h_step1 : ‖bilinearSum k M α‖ ^ ℓ ≤ (M : ℝ) ^ (-((ℓ + 1 : ℤ))) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖ ^ ℓ := by
    have h_le_pow : ‖bilinearSum k M α‖ ^ ℓ ≤ ((1 / (M : ℝ) ^ 2) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖) ^ ℓ := by
      exact pow_le_pow_left₀ (norm_nonneg _) h_bilin_le ℓ
    have h_split : ((1 / (M : ℝ) ^ 2) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖) ^ ℓ =
        (1 / (M : ℝ)) ^ ℓ * ((1 / (M : ℝ)) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖) ^ ℓ := by
      have : (1 / (M : ℝ) ^ 2) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖ =
          (1 / (M : ℝ)) * ((1 / (M : ℝ)) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖) := by
        rw [sq]
        ring
      rw [this, mul_pow]
    rw [h_split] at h_le_pow
    have h_comb : (1 / (M : ℝ)) ^ ℓ * ((1 / (M : ℝ)) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖) ^ ℓ ≤
        (1 / (M : ℝ)) ^ ℓ * ((1 / (M : ℝ)) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖ ^ ℓ) := by
      gcongr
    have h_pow_exp : (1 / (M : ℝ)) ^ ℓ * ((1 / (M : ℝ)) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖ ^ ℓ) =
        (M : ℝ) ^ (-((ℓ + 1 : ℤ))) * ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖ ^ ℓ := by
      rw [← mul_assoc]
      congr 1
      rw [← pow_succ, one_div_pow, zpow_neg]
      have : (ℓ + 1 : ℤ) = ((ℓ + 1 : ℕ) : ℤ) := by push_cast; rfl
      rw [this, zpow_natCast, inv_eq_one_div]
    rw [h_pow_exp] at h_comb
    exact le_trans h_le_pow h_comb
  set c : ℤ → ℂ := fun a => phase (T a ^ ℓ)
  set F : (Fin k → ℤ) → ℝ := fun y => ‖∑ a ∈ Finset.Icc (1 : ℤ) M, c a * Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) y)‖
  have h_step23 : ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖ ^ ℓ ≤ ∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℝ) * F y := by
    have h_eq_c : ∑ a ∈ Finset.Icc (1 : ℤ) M, ((‖T a‖ ^ ℓ : ℝ) : ℂ) = ∑ a ∈ Finset.Icc (1 : ℤ) M, c a * (T a ^ ℓ) := by
      apply Finset.sum_congr rfl
      intro a _
      have h := phase_mul_self (T a ^ ℓ)
      rw [norm_pow] at h
      exact h.symm
    have h_expand : ∑ a ∈ Finset.Icc (1 : ℤ) M, c a * (T a ^ ℓ) =
        ∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℂ) * ∑ a ∈ Finset.Icc (1 : ℤ) M, c a * Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) y) := by
      have h_subst : ∀ a ∈ Finset.Icc (1 : ℤ) M, c a * (T a ^ ℓ) =
          ∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℂ) * (c a * Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) y)) := by
        intro a _
        rw [sum_exp_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      rw [Finset.sum_congr rfl h_subst]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.mul_sum]
    have h_norm_lhs : ‖∑ a ∈ Finset.Icc (1 : ℤ) M, ((‖T a‖ ^ ℓ : ℝ) : ℂ)‖ = ∑ a ∈ Finset.Icc (1 : ℤ) M, ‖T a‖ ^ ℓ := by
      rw [← Complex.ofReal_sum]
      exact Complex.norm_of_nonneg (Finset.sum_nonneg fun _ _ => by positivity)
    have h_norm_rhs : ‖∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℂ) * ∑ a ∈ Finset.Icc (1 : ℤ) M, c a * Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) y)‖ ≤
        ∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℝ) * F y := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro y _
      rw [norm_mul]
      have h_rc : ‖(repCount k ℓ M y : ℂ)‖ = (repCount k ℓ M y : ℝ) := Complex.norm_natCast (repCount k ℓ M y)
      rw [h_rc]
    rw [h_eq_c, h_expand] at h_norm_lhs
    rw [← h_norm_lhs]
    exact h_norm_rhs
  have h_S_le : ‖bilinearSum k M α‖ ^ ℓ ≤ (M : ℝ) ^ (-((ℓ + 1 : ℤ))) * ∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℝ) * F y := by
    refine le_trans h_step1 ?_
    gcongr
  have h_S_2l : (‖bilinearSum k M α‖ ^ ℓ) ^ (2 * ℓ) ≤
      ((M : ℝ) ^ (-((ℓ + 1 : ℤ))) * ∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℝ) * F y) ^ (2 * ℓ) := by
    exact pow_le_pow_left₀ (by positivity) h_S_le (2 * ℓ)
  have h_lhs_exp : (‖bilinearSum k M α‖ ^ ℓ) ^ (2 * ℓ) = ‖bilinearSum k M α‖ ^ (2 * ℓ ^ 2) := by
    rw [← pow_mul]
    congr 1
    ring
  rw [h_lhs_exp] at h_S_2l
  rw [mul_pow] at h_S_2l
  have h_holder := three_factor_holder_le (box k ℓ M) (fun y => (repCount k ℓ M y : ℝ)) F
    (fun _ _ => by positivity) (fun _ _ => norm_nonneg _) ℓ hℓ
  have h_sum_rep : ∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℝ) = (M : ℝ) ^ ℓ := by
    have := sum_repCount k ℓ M
    exact_mod_cast this
  have h_sum_rep_sq : ∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℝ) ^ 2 = (J k ℓ M : ℝ) := by
    have := J_eq_sum_sq_repCount k ℓ M
    exact_mod_cast this.symm
  rw [h_sum_rep, h_sum_rep_sq] at h_holder
  have h_S_2l_bound : ‖bilinearSum k M α‖ ^ (2 * ℓ ^ 2) ≤
      ((M : ℝ) ^ (-((ℓ + 1 : ℤ)))) ^ (2 * ℓ) * (((M : ℝ) ^ ℓ) ^ (2 * ℓ - 2) * (J k ℓ M : ℝ) * ∑ y ∈ box k ℓ M, (F y) ^ (2 * ℓ)) := by
    calc
      ‖bilinearSum k M α‖ ^ (2 * ℓ ^ 2)
        ≤ ((M : ℝ) ^ (-((ℓ + 1 : ℤ)))) ^ (2 * ℓ) * (∑ y ∈ box k ℓ M, (repCount k ℓ M y : ℝ) * F y) ^ (2 * ℓ) := h_S_2l
      _ ≤ ((M : ℝ) ^ (-((ℓ + 1 : ℤ)))) ^ (2 * ℓ) * (((M : ℝ) ^ ℓ) ^ (2 * ℓ - 2) * (J k ℓ M : ℝ) * ∑ y ∈ box k ℓ M, (F y) ^ (2 * ℓ)) := by gcongr
  have h_M_powers : ((M : ℝ) ^ (-((ℓ + 1 : ℤ)))) ^ (2 * ℓ) * (((M : ℝ) ^ ℓ) ^ (2 * ℓ - 2) * (J k ℓ M : ℝ) * ∑ y ∈ box k ℓ M, (F y) ^ (2 * ℓ)) =
      (M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) * ∑ y ∈ box k ℓ M, (F y) ^ (2 * ℓ) := by
    have h_p1 : ((M : ℝ) ^ (-((ℓ + 1 : ℤ)))) ^ (2 * ℓ) = (M : ℝ) ^ (-2 * (ℓ : ℤ) ^ 2 - 2 * (ℓ : ℤ)) := by
      rw [← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    have h_p2 : (((M : ℝ) ^ ℓ) ^ (2 * ℓ - 2)) = (M : ℝ) ^ (2 * (ℓ : ℤ) ^ 2 - 2 * (ℓ : ℤ)) := by
      rw [← pow_mul, ← zpow_natCast]
      congr 1
      have h_sub : ((2 * ℓ - 2 : ℕ) : ℤ) = 2 * (ℓ : ℤ) - 2 := by
        have : 2 ≤ 2 * ℓ := by omega
        exact Nat.cast_sub this
      push_cast
      rw [h_sub]
      ring
    rw [h_p1, h_p2]
    have h_add : (M : ℝ) ^ (-2 * (ℓ : ℤ) ^ 2 - 2 * (ℓ : ℤ)) * ((M : ℝ) ^ (2 * (ℓ : ℤ) ^ 2 - 2 * (ℓ : ℤ)) * (J k ℓ M : ℝ) * ∑ y ∈ box k ℓ M, (F y) ^ (2 * ℓ)) =
        ((M : ℝ) ^ (-2 * (ℓ : ℤ) ^ 2 - 2 * (ℓ : ℤ)) * (M : ℝ) ^ (2 * (ℓ : ℤ) ^ 2 - 2 * (ℓ : ℤ))) * (J k ℓ M : ℝ) * ∑ y ∈ box k ℓ M, (F y) ^ (2 * ℓ) := by ring
    rw [h_add, ← zpow_add₀ (ne_of_gt hM_pos)]
    have : (-2 * (ℓ : ℤ) ^ 2 - 2 * (ℓ : ℤ)) + (2 * (ℓ : ℤ) ^ 2 - 2 * (ℓ : ℤ)) = -(4 * (ℓ : ℤ)) := by ring
    rw [this]
  rw [h_M_powers] at h_S_2l_bound
  set C_tuple : (Fin ℓ → ℤ) → ℂ := fun u => ∏ i : Fin ℓ, c (u i)
  have h_norm_C : ∀ u ∈ tuples ℓ M, ‖C_tuple u‖ ≤ 1 := by
    intro u _
    dsimp [C_tuple]
    rw [norm_prod]
    refine Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => norm_phase_le _)
  have h_F_expand : ∀ y ∈ box k ℓ M, (((F y) ^ (2 * ℓ) : ℝ) : ℂ) =
      ∑ u ∈ tuples ℓ M, ∑ v ∈ tuples ℓ M, C_tuple u * (starRingEnd ℂ) (C_tuple v) *
        Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ u - curveSum k ℓ v) y) := by
    intro y _
    have h_pow_sum : (∑ a ∈ Finset.Icc (1 : ℤ) M, c a * Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (momentCurve k a) y)) ^ ℓ =
        ∑ u ∈ tuples ℓ M, C_tuple u * Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ u) y) := by
      rw [Finset.sum_pow']
      have h_tup : (Fintype.piFinset fun _ : Fin ℓ => Finset.Icc (1 : ℤ) M) = tuples ℓ M := rfl
      rw [h_tup]
      apply Finset.sum_congr rfl
      intro u _
      dsimp [C_tuple]
      rw [Finset.prod_mul_distrib]
      congr 1
      exact exp_sum_bilinear_left k ℓ α u y
    set G := ∑ u ∈ tuples ℓ M, C_tuple u * Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ u) y)
    have h_norm_G : ‖G‖ = F y ^ ℓ := by
      rw [← h_pow_sum, norm_pow]
    have h_sq_G : (((F y) ^ (2 * ℓ) : ℝ) : ℂ) = G * (starRingEnd ℂ) G := by
      have : 2 * ℓ = ℓ * 2 := by omega
      rw [this, pow_mul]
      rw [← h_norm_G]
      have h1 : G * (starRingEnd ℂ) G = ↑(Complex.normSq G) := Complex.mul_conj G
      have h2 : Complex.normSq G = ‖G‖ ^ 2 := Complex.normSq_eq_norm_sq G
      rw [h1, h2]
    rw [h_sq_G]
    dsimp [G]
    rw [map_sum]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [map_mul]
    have h_exp_sub := exp_two_pi_I_sub (bilinearForm k α (curveSum k ℓ u) y) (bilinearForm k α (curveSum k ℓ v) y)
    have h_sub_left := bilinearForm_sub_left k α (curveSum k ℓ u) (curveSum k ℓ v) y
    rw [← h_sub_left] at h_exp_sub
    calc
      (C_tuple u * Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ u) y)) *
        ((starRingEnd ℂ) (C_tuple v) * (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ v) y)))
        = (C_tuple u * (starRingEnd ℂ) (C_tuple v)) *
          (Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ u) y) *
           (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ v) y))) := by ring
      _ = C_tuple u * (starRingEnd ℂ) (C_tuple v) *
          Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ u - curveSum k ℓ v) y) := by rw [h_exp_sub]
  have h_sum_F_sq : ∑ y ∈ box k ℓ M, (F y) ^ (2 * ℓ) ≤
      (J k ℓ M : ℝ) * ∑ x ∈ box k ℓ M, ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α x y)‖ := by
    have h_sum_c : (∑ y ∈ box k ℓ M, (((F y) ^ (2 * ℓ) : ℝ) : ℂ)) =
        ∑ u ∈ tuples ℓ M, ∑ v ∈ tuples ℓ M, C_tuple u * (starRingEnd ℂ) (C_tuple v) *
          ∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ u - curveSum k ℓ v) y) := by
      rw [Finset.sum_congr rfl h_F_expand]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [← Finset.mul_sum]
    have h_norm_lhs : ‖∑ y ∈ box k ℓ M, (((F y) ^ (2 * ℓ) : ℝ) : ℂ)‖ = ∑ y ∈ box k ℓ M, (F y) ^ (2 * ℓ) := by
      rw [← Complex.ofReal_sum]
      exact Complex.norm_of_nonneg (Finset.sum_nonneg fun y _ => pow_nonneg (norm_nonneg _) _)
    have h_norm_le : ‖∑ u ∈ tuples ℓ M, ∑ v ∈ tuples ℓ M, C_tuple u * (starRingEnd ℂ) (C_tuple v) *
          ∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ u - curveSum k ℓ v) y)‖ ≤
        ∑ u ∈ tuples ℓ M, ∑ v ∈ tuples ℓ M, ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ u - curveSum k ℓ v) y)‖ := by
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro u hu
      refine le_trans (norm_sum_le _ _) ?_
      apply Finset.sum_le_sum
      intro v hv
      rw [norm_mul, norm_mul]
      have hCu : ‖C_tuple u‖ ≤ 1 := h_norm_C u hu
      have hCv : ‖(starRingEnd ℂ) (C_tuple v)‖ ≤ 1 := by
        rw [RCLike.norm_conj]
        exact h_norm_C v hv
      have h_prod_le : ‖C_tuple u‖ * ‖(starRingEnd ℂ) (C_tuple v)‖ ≤ 1 := by
        nlinarith [norm_nonneg (C_tuple u), norm_nonneg ((starRingEnd ℂ) (C_tuple v))]
      have _h_nonneg_sum : 0 ≤ ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α (curveSum k ℓ u - curveSum k ℓ v) y)‖ := norm_nonneg _
      nlinarith
    rw [h_sum_c] at h_norm_lhs
    rw [← h_norm_lhs]
    refine le_trans h_norm_le ?_
    exact sum_curveSum_sub_le k ℓ M (fun x => ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α x y)‖) (fun _ => norm_nonneg _)
  have h_final : (M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) * ∑ y ∈ box k ℓ M, (F y) ^ (2 * ℓ) ≤
      (M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) ^ 2 * ∑ x ∈ box k ℓ M, ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α x y)‖ := by
    calc
      (M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) * ∑ y ∈ box k ℓ M, (F y) ^ (2 * ℓ)
        ≤ (M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) * ((J k ℓ M : ℝ) * ∑ x ∈ box k ℓ M, ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α x y)‖) := by gcongr
      _ = (M : ℝ) ^ (-(4 * ℓ : ℤ)) * (J k ℓ M : ℝ) ^ 2 * ∑ x ∈ box k ℓ M, ‖∑ y ∈ box k ℓ M, Complex.exp (2 * Real.pi * Complex.I * bilinearForm k α x y)‖ := by ring
  exact le_trans h_S_2l_bound h_final

end Erdos1201.MR.Vinogradov
