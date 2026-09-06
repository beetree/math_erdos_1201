import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Finset.Sort

open scoped BigOperators

/-!
# Linear and Bilinear Exponential Sums (Tao Lemma 12)

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module proves geometric-series bounds for exponential sums over intervals,
integral-test bounds for distance-to-integer reciprocal sums, and Tao's Lemma 12
bound for coordinate-wise linear-bilinear sums.
-/

namespace Erdos1201.MR.Vinogradov

/-! ### Part 1: Geometric-series exponential sum bounds -/

/-- Auxiliary: sine of distance to nearest integer equals sine of `π * θ` in absolute value. -/
lemma abs_sin_pi_sub_round (θ : ℝ) :
    |Real.sin (Real.pi * (θ - round θ))| = |Real.sin (Real.pi * θ)| := by
  have : Real.pi * (θ - round θ) = Real.pi * θ - (round θ : ℝ) * Real.pi := by ring
  rw [this, Real.sin_sub_int_mul_pi]
  simp

/-- Jordan's inequality applied to the distance to the nearest integer. -/
lemma two_mul_abs_sub_round_le_abs_sin_pi (θ : ℝ) :
    2 * |θ - round θ| ≤ |Real.sin (Real.pi * θ)| := by
  have h_bound : |Real.pi * (θ - round θ)| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have h_round : |θ - round θ| ≤ 1 / 2 := abs_sub_round θ
    nlinarith [Real.pi_pos]
  have hj := Real.mul_abs_le_abs_sin h_bound
  rw [abs_sin_pi_sub_round] at hj
  rw [abs_mul, abs_of_pos Real.pi_pos] at hj
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have : 2 / Real.pi * (Real.pi * |θ - round θ|) = 2 * |θ - round θ| := by
    calc 2 / Real.pi * (Real.pi * |θ - round θ|)
      _ = (2 / Real.pi * Real.pi) * |θ - round θ| := by ring
      _ = 2 * |θ - round θ| := by rw [div_mul_cancel₀ 2 hpi]
  rwa [this] at hj

/-- Exact norm identity for `exp(2π i θ) - 1`. -/
lemma norm_exp_two_pi_I_mul_sub_one (θ : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * θ) - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
  have h_arg : (2 * Real.pi * Complex.I * θ : ℂ) = (2 * Real.pi * θ : ℝ) * Complex.I := by
    push_cast; ring
  rw [h_arg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have h_re_im : (Real.cos (2 * Real.pi * θ) : ℂ) + (Real.sin (2 * Real.pi * θ) : ℝ) * Complex.I - 1 =
      ((Real.cos (2 * Real.pi * θ) - 1 : ℝ) : ℂ) + ((Real.sin (2 * Real.pi * θ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h_re_im, Complex.norm_def, Complex.normSq_add_mul_I]
  have h_id : (Real.cos (2 * Real.pi * θ) - 1) ^ 2 + (Real.sin (2 * Real.pi * θ)) ^ 2 =
      4 * (Real.sin (Real.pi * θ)) ^ 2 := by
    have h_cos : Real.cos (2 * Real.pi * θ) = 1 - 2 * (Real.sin (Real.pi * θ)) ^ 2 := by
      have h1 : Real.cos (2 * (Real.pi * θ)) = 2 * (Real.cos (Real.pi * θ)) ^ 2 - 1 :=
        Real.cos_two_mul (Real.pi * θ)
      have h2 : (Real.sin (Real.pi * θ)) ^ 2 + (Real.cos (Real.pi * θ)) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq (Real.pi * θ)
      have : 2 * Real.pi * θ = 2 * (Real.pi * θ) := by ring
      rw [this, h1]
      linarith
    have h_sin : Real.sin (2 * Real.pi * θ) = 2 * Real.sin (Real.pi * θ) * Real.cos (Real.pi * θ) := by
      have : 2 * Real.pi * θ = 2 * (Real.pi * θ) := by ring
      rw [this, Real.sin_two_mul]
    have h_pyth : (Real.sin (Real.pi * θ)) ^ 2 + (Real.cos (Real.pi * θ)) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq (Real.pi * θ)
    rw [h_cos, h_sin]
    linear_combination 4 * Real.sin (Real.pi * θ) ^ 2 * h_pyth
  rw [h_id]
  have h4 : 4 * Real.sin (Real.pi * θ) ^ 2 = (2 * Real.sin (Real.pi * θ)) ^ 2 := by ring
  rw [h4, Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Reindexing an `Icc (-L) L` sum as a `range (2L + 1)` sum. -/
lemma sum_Icc_exp_eq_sum_range (L : ℕ) (θ : ℝ) :
    (∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))) =
      ∑ i ∈ Finset.range (2 * L + 1),
        Complex.exp (2 * Real.pi * Complex.I * (θ * (-(L : ℤ) + (i : ℤ)))) := by
  let e : ℕ ↪ ℤ := ⟨fun (i : ℕ) => -(L : ℤ) + (i : ℤ), fun a b hab => by
    have h : (a : ℤ) = (b : ℤ) := add_left_cancel hab
    exact Nat.cast_injective h⟩
  have he (i : ℕ) : e i = -(L : ℤ) + (i : ℤ) := rfl
  have : Finset.Icc (-(L : ℤ)) (L : ℤ) = (Finset.range (2 * L + 1)).map e := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, he]
    constructor
    · intro hx
      refine ⟨(x + (L : ℤ)).toNat, ?_, ?_⟩
      · have : 0 ≤ x + (L : ℤ) := by linarith [hx.1]
        have : x + (L : ℤ) < (2 * L + 1 : ℤ) := by linarith [hx.2]
        omega
      · have : 0 ≤ x + (L : ℤ) := by linarith [hx.1]
        have : ((x + (L : ℤ)).toNat : ℤ) = x + (L : ℤ) := Int.toNat_of_nonneg this
        linarith
    · rintro ⟨i, hi, rfl⟩
      constructor
      · linarith
      · have : (i : ℤ) ≤ 2 * (L : ℤ) := by omega
        linarith
  rw [this, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [he]
  push_cast
  ring

/-- Telescoping identity for symmetric exponential sums. -/
lemma mul_sub_one_sum_exp_eq (L : ℕ) (θ : ℝ) :
    (Complex.exp (2 * Real.pi * Complex.I * θ) - 1) *
      (∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))) =
    Complex.exp (2 * Real.pi * Complex.I * (θ * (L + 1 : ℤ))) -
      Complex.exp (2 * Real.pi * Complex.I * (θ * (-(L : ℤ)))) := by
  let f : ℕ → ℂ := fun i => Complex.exp (2 * Real.pi * Complex.I * (θ * (-(L : ℤ) + (i : ℤ))))
  have h_step (i : ℕ) : f (i + 1) - f i =
      (Complex.exp (2 * Real.pi * Complex.I * θ) - 1) * f i := by
    dsimp [f]
    have h_exp_add : Complex.exp (2 * Real.pi * Complex.I * (θ * (-(L : ℤ) + (i + 1 : ℤ)))) =
        Complex.exp (2 * Real.pi * Complex.I * θ) *
        Complex.exp (2 * Real.pi * Complex.I * (θ * (-(L : ℤ) + (i : ℤ)))) := by
      have : (2 * Real.pi * Complex.I * (θ * (-(L : ℤ) + (i + 1 : ℤ)))) =
          (2 * Real.pi * Complex.I * θ) + (2 * Real.pi * Complex.I * (θ * (-(L : ℤ) + (i : ℤ)))) := by
        push_cast; ring
      rw [this, Complex.exp_add]
    rw [h_exp_add]
    ring
  have h_sum := Finset.sum_range_sub f (2 * L + 1)
  have h_rewrite : (∑ i ∈ Finset.range (2 * L + 1), (f (i + 1) - f i)) =
      (Complex.exp (2 * Real.pi * Complex.I * θ) - 1) *
        ∑ i ∈ Finset.range (2 * L + 1), f i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => h_step i
  rw [h_rewrite] at h_sum
  have h_f2L1 : f (2 * L + 1) = Complex.exp (2 * Real.pi * Complex.I * (θ * (L + 1 : ℤ))) := by
    dsimp [f]
    have : (2 * Real.pi * Complex.I * (θ * (-(L : ℤ) + (2 * L + 1 : ℤ)))) =
        (2 * Real.pi * Complex.I * (θ * (L + 1 : ℤ))) := by
      push_cast; ring
    rw [this]
  have h_f0 : f 0 = Complex.exp (2 * Real.pi * Complex.I * (θ * (-(L : ℤ)))) := by
    dsimp [f]
    have : (2 * Real.pi * Complex.I * (θ * (-(L : ℤ) + (0 : ℤ)))) =
        (2 * Real.pi * Complex.I * (θ * (-(L : ℤ)))) := by
      push_cast; ring
    rw [this]
  rw [h_f2L1, h_f0] at h_sum
  have h_eq : (∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))) =
      ∑ i ∈ Finset.range (2 * L + 1), f i :=
    sum_Icc_exp_eq_sum_range L θ
  rw [h_eq, h_sum]

/-- Trivial bound for symmetric exponential sum: `|∑_{|y| ≤ L} e(θ y)| ≤ 2L + 1`. -/
theorem norm_sum_exp_Icc_le_trivial (L : ℕ) (θ : ℝ) :
    ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖ ≤
      2 * L + 1 := by
  have h_card : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  calc ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖
    _ ≤ ∑ y ∈ Finset.Icc (-(L : ℤ)) L, ‖Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖ :=
      norm_sum_le _ _
    _ = ∑ y ∈ Finset.Icc (-(L : ℤ)) L, (1 : ℝ) := by
      refine Finset.sum_congr rfl fun y _ => ?_
      have : (2 * Real.pi * Complex.I * (θ * y) : ℂ) = (2 * Real.pi * (θ * y) : ℝ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    _ = (Finset.Icc (-(L : ℤ)) (L : ℤ)).card := by simp
    _ = 2 * L + 1 := by rw [h_card]; push_cast; rfl

/-- Geometric-series inverse-distance bound when `θ` is not an integer. -/
theorem norm_sum_exp_Icc_le_inv (L : ℕ) (θ : ℝ) (hθ : 0 < |θ - round θ|) :
    ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖ ≤
      1 / (2 * |θ - round θ|) := by
  have h_telescope := mul_sub_one_sum_exp_eq L θ
  have h_norm_eq : ‖(Complex.exp (2 * Real.pi * Complex.I * θ) - 1) *
      (∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y)))‖ =
      ‖Complex.exp (2 * Real.pi * Complex.I * (θ * (L + 1 : ℤ))) -
        Complex.exp (2 * Real.pi * Complex.I * (θ * (-(L : ℤ))))‖ := by
    rw [h_telescope]
  rw [norm_mul] at h_norm_eq
  have h_rhs_le : ‖Complex.exp (2 * Real.pi * Complex.I * (θ * (L + 1 : ℤ))) -
      Complex.exp (2 * Real.pi * Complex.I * (θ * (-(L : ℤ))))‖ ≤ 2 := by
    have h1 : ‖Complex.exp (2 * Real.pi * Complex.I * (θ * (L + 1 : ℤ)))‖ = 1 := by
      have : (2 * Real.pi * Complex.I * (θ * (L + 1 : ℤ)) : ℂ) =
          (2 * Real.pi * (θ * (L + 1 : ℤ)) : ℝ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have h2 : ‖Complex.exp (2 * Real.pi * Complex.I * (θ * (-(L : ℤ))))‖ = 1 := by
      have : (2 * Real.pi * Complex.I * (θ * (-(L : ℤ))) : ℂ) =
          (2 * Real.pi * (θ * (-(L : ℤ))) : ℝ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    have := norm_sub_le (Complex.exp (2 * Real.pi * Complex.I * (θ * (L + 1 : ℤ))))
      (Complex.exp (2 * Real.pi * Complex.I * (θ * (-(L : ℤ)))))
    linarith
  have h_mul_le : ‖Complex.exp (2 * Real.pi * Complex.I * θ) - 1‖ *
      ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖ ≤ 2 := by
    linarith [h_norm_eq, h_rhs_le]
  rw [norm_exp_two_pi_I_mul_sub_one] at h_mul_le
  have h_jordan := two_mul_abs_sub_round_le_abs_sin_pi θ
  have h_lower : 4 * |θ - round θ| ≤ 2 * |Real.sin (Real.pi * θ)| := by linarith
  have h_sum_nonneg : 0 ≤ ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖ := norm_nonneg _
  have h_prod_le : (4 * |θ - round θ|) *
      ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖ ≤ 2 := by
    calc (4 * |θ - round θ|) * ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖
      _ ≤ (2 * |Real.sin (Real.pi * θ)|) * ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖ :=
        mul_le_mul_of_nonneg_right h_lower h_sum_nonneg
      _ ≤ 2 := h_mul_le
  have h4pos : 0 < 4 * |θ - round θ| := by linarith
  have : ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖ ≤
      2 / (4 * |θ - round θ|) := by
    rw [mul_comm] at h_prod_le
    exact (le_div_iff₀ h4pos).mpr h_prod_le
  have h_arith : (2 : ℝ) / (4 * |θ - round θ|) = 1 / (2 * |θ - round θ|) := by
    have : (2 : ℝ) / (4 * |θ - round θ|) = (2 * 1) / (2 * (2 * |θ - round θ|)) := by ring
    rw [this, mul_div_mul_left 1 (2 * |θ - round θ|) two_ne_zero]
  rwa [h_arith] at this

/-- Geometric-series bound: |∑_{|y| ≤ L} e(θ y)| ≤ min(2L+1, 1/(2‖θ‖)) where ‖θ‖ is the distance to the nearest integer. -/
theorem norm_sum_exp_Icc_le (L : ℕ) (θ : ℝ) (hθ : 0 < |θ - round θ|) :
    ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * y))‖ ≤
      min (2 * L + 1 : ℝ) (1 / (2 * |θ - round θ|)) :=
  le_min (norm_sum_exp_Icc_le_trivial L θ) (norm_sum_exp_Icc_le_inv L θ hθ)

/-! ### Part 2: Integral-test bound for distance-to-integer reciprocal sums -/

/-- Distance to nearest integer summand avoiding division by zero. -/
noncomputable def invDistTerm (L : ℝ) (θ : ℝ) : ℝ :=
  if θ = round θ then L else min L (1 / (2 * |θ - round θ|))

lemma card_filter_lt_le_sub (c : ℝ) (S : Finset ℤ) (x : ℤ) (hx : x ∈ S)
    (hc : ∀ y ∈ S, c < (y : ℝ)) :
    ((S.filter (· < x)).card : ℝ) ≤ (x : ℝ) - c := by
  have h_nonneg : 0 ≤ x - (⌊c⌋ + 1) := by
    have : c < (x : ℝ) := hc x hx
    have : ⌊c⌋ < x := Int.floor_lt.mpr this
    omega
  have h_sub : S.filter (· < x) ⊆ Finset.Ico (⌊c⌋ + 1) x := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_Ico] at hy ⊢
    refine ⟨?_, hy.2⟩
    have : c < (y : ℝ) := hc y hy.1
    have : ⌊c⌋ < y := Int.floor_lt.mpr this
    omega
  have h_card := Finset.card_le_card h_sub
  rw [Int.card_Ico] at h_card
  have h_eq : ((x - (⌊c⌋ + 1)).toNat : ℤ) = x - (⌊c⌋ + 1) := Int.toNat_of_nonneg h_nonneg
  have h_le : ((S.filter (· < x)).card : ℤ) ≤ x - (⌊c⌋ + 1) := by
    have : ((S.filter (· < x)).card : ℤ) ≤ ((x - (⌊c⌋ + 1)).toNat : ℤ) := by
      exact_mod_cast h_card
    rwa [h_eq] at this
  have h_fl : c < (⌊c⌋ : ℝ) + 1 := Int.lt_floor_add_one c
  have h_cast : ((S.filter (· < x)).card : ℝ) ≤ (x : ℝ) - (⌊c⌋ + 1 : ℝ) := by
    exact_mod_cast h_le
  linarith

lemma sum_inv_sub_le_sum_harmonic (c α : ℝ) (hα : 0 < α) (S : Finset ℤ)
    (hc : ∀ y ∈ S, c < (y : ℝ)) (L : ℝ) (hL : 0 ≤ L) :
    ∑ x ∈ S, min L (1 / (2 * α * ((x : ℝ) - c))) ≤
      L + (1 / (2 * α)) * ∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j := by
  by_cases hS : S = ∅
  · simp only [hS, Finset.sum_empty, Finset.card_empty]
    have : Finset.Icc (1 : ℕ) 0 = ∅ := rfl
    rw [this, Finset.sum_empty, mul_zero, add_zero]
    exact hL
  have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
  let m₀ := S.min' hS_nonempty
  have hm₀ : m₀ ∈ S := Finset.min'_mem S hS_nonempty
  have h_split : S = insert m₀ (S.erase m₀) := (Finset.insert_erase hm₀).symm
  have h_sum_split : (∑ x ∈ S, min L (1 / (2 * α * ((x : ℝ) - c)))) =
      min L (1 / (2 * α * ((m₀ : ℝ) - c))) +
        ∑ x ∈ S.erase m₀, min L (1 / (2 * α * ((x : ℝ) - c))) := by
    conv_lhs => rw [h_split]
    rw [Finset.sum_insert (Finset.notMem_erase m₀ S)]
  rw [h_sum_split]
  have h_m0_le : min L (1 / (2 * α * ((m₀ : ℝ) - c))) ≤ L := min_le_left _ _
  have h_rest : ∑ x ∈ S.erase m₀, min L (1 / (2 * α * ((x : ℝ) - c))) ≤
      (1 / (2 * α)) * ∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j := by
    let g : ℤ → ℕ := fun x => (S.filter (· < x)).card
    have hg_inj : ∀ x ∈ S.erase m₀, ∀ y ∈ S.erase m₀, g x = g y → x = y := by
      intro x hx y hy h_eq
      simp only [Finset.mem_erase] at hx hy
      rcases lt_trichotomy x y with hlt | heq | hgt
      · have h_ss : S.filter (· < x) ⊂ S.filter (· < y) := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨fun z hz => ?_, fun heq_set => ?_⟩
          · simp only [Finset.mem_filter] at hz ⊢
            exact ⟨hz.1, hz.2.trans hlt⟩
          · have : x ∈ S.filter (· < y) := by
              simp only [Finset.mem_filter]
              exact ⟨hx.2, hlt⟩
            rw [← heq_set] at this
            simp at this
        have := Finset.card_lt_card h_ss
        dsimp [g] at h_eq
        linarith
      · exact heq
      · have h_ss : S.filter (· < y) ⊂ S.filter (· < x) := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨fun z hz => ?_, fun heq_set => ?_⟩
          · simp only [Finset.mem_filter] at hz ⊢
            exact ⟨hz.1, hz.2.trans hgt⟩
          · have : y ∈ S.filter (· < x) := by
              simp only [Finset.mem_filter]
              exact ⟨hy.2, hgt⟩
            rw [← heq_set] at this
            simp at this
        have := Finset.card_lt_card h_ss
        dsimp [g] at h_eq
        linarith
    have hg_range : ∀ x ∈ S.erase m₀, g x ∈ Finset.Icc (1 : ℕ) S.card := by
      intro x hx
      simp only [Finset.mem_erase] at hx
      dsimp [g]
      rw [Finset.mem_Icc]
      constructor
      · have hm0_lt : m₀ < x := by
          have h_le := Finset.min'_le S x hx.2
          rcases h_le.lt_or_eq with h1 | h2
          · exact h1
          · exact False.elim (hx.1 h2.symm)
        have : m₀ ∈ S.filter (· < x) := by
          simp only [Finset.mem_filter]
          exact ⟨hm₀, hm0_lt⟩
        have := Finset.card_pos.mpr ⟨m₀, this⟩
        omega
      · exact (Finset.card_le_card (Finset.filter_subset (· < x) S)).trans le_rfl
    have h_term : ∀ x ∈ S.erase m₀, min L (1 / (2 * α * ((x : ℝ) - c))) ≤
        (1 / (2 * α)) * (1 / (g x : ℝ)) := by
      intro x hx
      have hxS : x ∈ S := (Finset.mem_erase.mp hx).2
      have h_card_le := card_filter_lt_le_sub c S x hxS hc
      have h_gx_pos : 0 < (g x : ℝ) := by
        have : 1 ≤ g x := (Finset.mem_Icc.mp (hg_range x hx)).1
        exact Nat.cast_pos.mpr this
      have h_denom_pos : 0 < (x : ℝ) - c := by
        have := hc x hxS
        linarith
      calc min L (1 / (2 * α * ((x : ℝ) - c)))
        _ ≤ 1 / (2 * α * ((x : ℝ) - c)) := min_le_right _ _
        _ = (1 / (2 * α)) * (1 / ((x : ℝ) - c)) := by
          have : 2 * α * ((x : ℝ) - c) = (2 * α) * ((x : ℝ) - c) := by ring
          rw [this, one_div_mul_one_div]
        _ ≤ (1 / (2 * α)) * (1 / (g x : ℝ)) := by
          have h2a : 0 < 1 / (2 * α) := by positivity
          apply mul_le_mul_of_nonneg_left _ h2a.le
          apply one_div_le_one_div_of_le h_gx_pos h_card_le
    calc ∑ x ∈ S.erase m₀, min L (1 / (2 * α * ((x : ℝ) - c)))
      _ ≤ ∑ x ∈ S.erase m₀, (1 / (2 * α)) * (1 / (g x : ℝ)) :=
        Finset.sum_le_sum h_term
      _ = (1 / (2 * α)) * ∑ x ∈ S.erase m₀, (1 / (g x : ℝ)) := by
        rw [← Finset.mul_sum]
      _ ≤ (1 / (2 * α)) * ∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j := by
        have h2a : 0 ≤ 1 / (2 * α) := by positivity
        apply mul_le_mul_of_nonneg_left _ h2a
        have h_sub : (S.erase m₀).image g ⊆ Finset.Icc (1 : ℕ) S.card := by
          intro y hy
          simp only [Finset.mem_image] at hy
          rcases hy with ⟨x, hx, rfl⟩
          exact hg_range x hx
        have h_img : ∑ j ∈ (S.erase m₀).image g, (1 : ℝ) / j ≤
            ∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
          intro j _ _
          positivity
        have h_inj_sum : (∑ x ∈ S.erase m₀, (1 : ℝ) / (g x : ℝ)) =
            ∑ j ∈ (S.erase m₀).image g, (1 : ℝ) / j := by
          rw [Finset.sum_image hg_inj]
        rwa [h_inj_sum]
  linarith

lemma sum_inv_sub_left_le_sum_harmonic (c α : ℝ) (hα : 0 < α) (S : Finset ℤ)
    (hc : ∀ y ∈ S, (y : ℝ) < c) (L : ℝ) (hL : 0 ≤ L) :
    ∑ x ∈ S, min L (1 / (2 * α * (c - (x : ℝ)))) ≤
      L + (1 / (2 * α)) * ∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j := by
  let negEmb : ℤ ↪ ℤ := ⟨fun z => -z, neg_injective⟩
  have hc' : ∀ y ∈ S.map negEmb, -c < (y : ℝ) := by
    intro y hy
    simp only [Finset.mem_map, negEmb] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have := hc z hz
    dsimp; push_cast; linarith
  have h_bound := sum_inv_sub_le_sum_harmonic (-c) α hα (S.map negEmb) hc' L hL
  have h_eq : (∑ x ∈ S, min L (1 / (2 * α * (c - (x : ℝ))))) =
      ∑ z ∈ S.map negEmb, min L (1 / (2 * α * ((z : ℝ) - (-c)))) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun x _ => ?_
    dsimp [negEmb]
    have : c - (x : ℝ) = (↑(-x) : ℝ) - -c := by push_cast; ring
    rw [this]
  rw [Finset.card_map] at h_bound
  rwa [h_eq]

lemma card_filter_cast_eq_le_one (c : ℝ) (S : Finset ℤ) :
    (S.filter (fun (x : ℤ) => (x : ℝ) = c)).card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro x hx y hy
  simp only [Finset.mem_filter] at hx hy
  have : (x : ℝ) = (y : ℝ) := by linarith [hx.2, hy.2]
  exact_mod_cast this

lemma sum_harmonic_le_sum_harmonic {m n : ℕ} (hmn : m ≤ n) :
    ∑ j ∈ Finset.Icc (1 : ℕ) m, (1 : ℝ) / j ≤ ∑ j ∈ Finset.Icc (1 : ℕ) n, (1 : ℝ) / j := by
  have h_sub : Finset.Icc (1 : ℕ) m ⊆ Finset.Icc (1 : ℕ) n := by
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    exact ⟨hx.1, hx.2.trans hmn⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg h_sub
  intro j _ _
  positivity

lemma sum_harmonic_le_one_add_log (n : ℕ) :
    ∑ j ∈ Finset.Icc (1 : ℕ) n, (1 : ℝ) / j ≤ 1 + Real.log n := by
  by_cases hn : n = 0
  · subst hn
    have : Finset.Icc (1 : ℕ) 0 = ∅ := rfl
    rw [this, Finset.sum_empty]
    simp
  have h_eq : (∑ j ∈ Finset.Icc (1 : ℕ) n, (1 : ℝ) / j) = (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    refine Finset.sum_congr rfl fun j _ => by simp [div_eq_inv_mul]
  rw [h_eq]
  exact harmonic_le_one_add_log n

lemma card_round_image_Icc_le (X : ℕ) (α : ℝ) :
    (((Finset.Icc (-(X : ℤ)) X).image (fun (x : ℤ) => round (α * (x : ℝ)))).card : ℝ) ≤
      2 * X * |α| + 3 := by
  let S := Finset.Icc (-(X : ℤ)) X
  let N := S.image (fun (x : ℤ) => round (α * (x : ℝ)))
  let a := ⌊-(X : ℝ) * |α| - 1/2⌋
  let b := ⌊(X : ℝ) * |α| + 1/2⌋
  have h_sub : N ⊆ Finset.Icc a b := by
    intro n hn
    simp only [Finset.mem_image, N] at hn
    rcases hn with ⟨x, hx, rfl⟩
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_Icc]
    have h_abs_x : |(x : ℝ)| ≤ (X : ℝ) := by
      rw [abs_le]
      constructor
      · exact_mod_cast hx.1
      · exact_mod_cast hx.2
    have h_abs_ax : |α * (x : ℝ)| ≤ (X : ℝ) * |α| := by
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right h_abs_x (abs_nonneg α)
    have h_round : |(round (α * (x : ℝ)) : ℝ) - α * (x : ℝ)| ≤ 1 / 2 := by
      have := abs_sub_round (α * (x : ℝ))
      rwa [abs_sub_comm]
    have h_upper : (round (α * (x : ℝ)) : ℝ) ≤ (X : ℝ) * |α| + 1 / 2 := by
      have : (round (α * (x : ℝ)) : ℝ) = (round (α * (x : ℝ)) - α * (x : ℝ)) + α * (x : ℝ) := by ring
      rw [this]
      linarith [(le_abs_self _).trans h_abs_ax, (le_abs_self _).trans h_round]
    have h_lower : -(X : ℝ) * |α| - 1 / 2 ≤ (round (α * (x : ℝ)) : ℝ) := by
      have : (round (α * (x : ℝ)) : ℝ) = (round (α * (x : ℝ)) - α * (x : ℝ)) + α * (x : ℝ) := by ring
      rw [this]
      have : -((X : ℝ) * |α|) ≤ α * (x : ℝ) := by
        have := neg_abs_le (α * (x : ℝ))
        linarith
      have : -(1 / 2 : ℝ) ≤ (round (α * (x : ℝ)) - α * (x : ℝ)) := by
        have := neg_abs_le (round (α * (x : ℝ)) - α * (x : ℝ))
        linarith
      linarith
    constructor
    · exact Int.floor_le_iff.mpr (by linarith)
    · exact Int.le_floor.mpr h_upper
  have h_card := Finset.card_le_card h_sub
  rw [Int.card_Icc] at h_card
  have h_nonneg : 0 ≤ b + 1 - a := by
    have h_b : 0 ≤ (X : ℝ) * |α| + 1/2 := by positivity
    have h_a : -(X : ℝ) * |α| - 1/2 ≤ 1/2 := by linarith [h_b]
    have : a ≤ b := by
      dsimp [a, b]
      apply Int.floor_le_floor
      linarith
    omega
  have h_toNat : ((b + 1 - a).toNat : ℝ) = (b + 1 - a : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg h_nonneg
  have h1 : (b : ℝ) ≤ (X : ℝ) * |α| + 1/2 := Int.floor_le _
  have h2 : -(X : ℝ) * |α| - 1/2 - 1 < (a : ℝ) := Int.sub_one_lt_floor _
  have h_bound : (N.card : ℝ) ≤ (b + 1 - a : ℝ) := by
    calc (N.card : ℝ) ≤ ((b + 1 - a).toNat : ℝ) := by exact_mod_cast h_card
      _ = (b + 1 - a : ℤ) := h_toNat
      _ = (b + 1 - a : ℝ) := by push_cast; rfl
  linarith

lemma card_filter_round_pos_alpha_le (X : ℕ) (α : ℝ) (hα : 0 < α) (n : ℤ) :
    (((Finset.Icc (-(X : ℤ)) X).filter (fun (x : ℤ) => round (α * (x : ℝ)) = n)).card : ℝ) ≤
      1 / α + 2 := by
  let S := (Finset.Icc (-(X : ℤ)) X).filter (fun (x : ℤ) => round (α * (x : ℝ)) = n)
  let a := ⌊((n : ℝ) - 1/2) / α⌋
  let b := ⌊((n : ℝ) + 1/2) / α⌋
  have h_sub : S ⊆ Finset.Icc a b := by
    intro x hx
    simp only [Finset.mem_filter, S] at hx
    have h_round : |(round (α * (x : ℝ)) : ℝ) - α * (x : ℝ)| ≤ 1 / 2 := by
      have := abs_sub_round (α * (x : ℝ))
      rwa [abs_sub_comm]
    have h_eq : (round (α * (x : ℝ)) : ℝ) = n := by exact_mod_cast hx.2
    rw [h_eq] at h_round
    rw [abs_le] at h_round
    rw [Finset.mem_Icc]
    constructor
    · apply Int.floor_le_iff.mpr
      have : (n : ℝ) - 1/2 ≤ (x : ℝ) * α := by
        rw [mul_comm]
        linarith [h_round.1]
      have : ((n : ℝ) - 1/2) / α ≤ (x : ℝ) := (div_le_iff₀ hα).mpr this
      linarith
    · apply Int.le_floor.mpr
      have : (x : ℝ) * α ≤ (n : ℝ) + 1/2 := by
        rw [mul_comm]
        linarith [h_round.2]
      exact (le_div_iff₀ hα).mpr this
  have h_card := Finset.card_le_card h_sub
  rw [Int.card_Icc] at h_card
  have h_nonneg : 0 ≤ b + 1 - a := by
    have : a ≤ b := by
      dsimp [a, b]
      apply Int.floor_le_floor
      have : (n : ℝ) - 1/2 ≤ (n : ℝ) + 1/2 := by linarith
      exact div_le_div_of_nonneg_right this hα.le
    omega
  have h_toNat : ((b + 1 - a).toNat : ℝ) = (b + 1 - a : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg h_nonneg
  have h1 : (b : ℝ) ≤ ((n : ℝ) + 1/2) / α := Int.floor_le _
  have h2 : ((n : ℝ) - 1/2) / α - 1 < (a : ℝ) := Int.sub_one_lt_floor _
  have h_bound : (S.card : ℝ) ≤ (b + 1 - a : ℝ) := by
    calc (S.card : ℝ) ≤ ((b + 1 - a).toNat : ℝ) := by exact_mod_cast h_card
      _ = (b + 1 - a : ℤ) := h_toNat
      _ = (b + 1 - a : ℝ) := by push_cast; rfl
  have : ((n : ℝ) + 1/2) / α - (((n : ℝ) - 1/2) / α - 1) + 1 = 1 / α + 2 := by
    have : ((n : ℝ) + 1/2) / α - ((n : ℝ) - 1/2) / α = 1 / α := by
      rw [← sub_div]
      ring_nf
    linarith
  linarith

lemma card_filter_round_neg_alpha_le (X : ℕ) (α : ℝ) (hα : α < 0) (n : ℤ) :
    (((Finset.Icc (-(X : ℤ)) X).filter (fun (x : ℤ) => round (α * (x : ℝ)) = n)).card : ℝ) ≤
      1 / |α| + 2 := by
  let S := (Finset.Icc (-(X : ℤ)) X).filter (fun (x : ℤ) => round (α * (x : ℝ)) = n)
  let a := ⌊((n : ℝ) + 1/2) / α⌋
  let b := ⌊((n : ℝ) - 1/2) / α⌋
  have h_sub : S ⊆ Finset.Icc a b := by
    intro x hx
    simp only [Finset.mem_filter, S] at hx
    have h_round : |(round (α * (x : ℝ)) : ℝ) - α * (x : ℝ)| ≤ 1 / 2 := by
      have := abs_sub_round (α * (x : ℝ))
      rwa [abs_sub_comm]
    have h_eq : (round (α * (x : ℝ)) : ℝ) = n := by exact_mod_cast hx.2
    rw [h_eq] at h_round
    rw [abs_le] at h_round
    rw [Finset.mem_Icc]
    constructor
    · apply Int.floor_le_iff.mpr
      have : (x : ℝ) * α ≤ (n : ℝ) + 1/2 := by
        rw [mul_comm]
        linarith [h_round.2]
      have : ((n : ℝ) + 1/2) / α ≤ (x : ℝ) := (div_le_iff_of_neg hα).mpr this
      linarith
    · apply Int.le_floor.mpr
      have : (n : ℝ) - 1/2 ≤ (x : ℝ) * α := by
        rw [mul_comm]
        linarith [h_round.1]
      exact (le_div_iff_of_neg hα).mpr this
  have h_card := Finset.card_le_card h_sub
  rw [Int.card_Icc] at h_card
  have h_nonneg : 0 ≤ b + 1 - a := by
    have : a ≤ b := by
      dsimp [a, b]
      apply Int.floor_le_floor
      have : ((n : ℝ) + 1/2) / α ≤ ((n : ℝ) - 1/2) / α := by
        have : ((n : ℝ) - 1/2) / α - ((n : ℝ) + 1/2) / α = - (1 / α) := by
          rw [← sub_div]
          ring_nf
        have : 0 < - (1 / α) := by
          have : 1 / α < 0 := one_div_neg.mpr hα
          linarith
        linarith
      exact this
    omega
  have h_toNat : ((b + 1 - a).toNat : ℝ) = (b + 1 - a : ℤ) := by
    exact_mod_cast Int.toNat_of_nonneg h_nonneg
  have h1 : (b : ℝ) ≤ ((n : ℝ) - 1/2) / α := Int.floor_le _
  have h2 : ((n : ℝ) + 1/2) / α - 1 < (a : ℝ) := Int.sub_one_lt_floor _
  have h_bound : (S.card : ℝ) ≤ (b + 1 - a : ℝ) := by
    calc (S.card : ℝ) ≤ ((b + 1 - a).toNat : ℝ) := by exact_mod_cast h_card
      _ = (b + 1 - a : ℤ) := h_toNat
      _ = (b + 1 - a : ℝ) := by push_cast; rfl
  have : ((n : ℝ) - 1/2) / α - (((n : ℝ) + 1/2) / α - 1) + 1 = - (1 / α) + 2 := by
    have : ((n : ℝ) - 1/2) / α - ((n : ℝ) + 1/2) / α = - (1 / α) := by
      rw [← sub_div]
      ring_nf
    linarith
  have h_abs : |α| = -α := abs_of_neg hα
  have : 1 / |α| = - (1 / α) := by
    rw [h_abs]
    ring
  linarith

lemma card_filter_round_le (X : ℕ) (α : ℝ) (hα : 0 < |α|) (n : ℤ) :
    (((Finset.Icc (-(X : ℤ)) X).filter (fun (x : ℤ) => round (α * (x : ℝ)) = n)).card : ℝ) ≤
      1 / |α| + 2 := by
  rcases lt_or_gt_of_ne (abs_pos.mp hα) with hneg | hpos
  · exact card_filter_round_neg_alpha_le X α hneg n
  · have := card_filter_round_pos_alpha_le X α hpos n
    rwa [abs_of_pos hpos]



lemma sum_inv_dist_split_le (c α : ℝ) (hα : 0 < α) (S : Finset ℤ) (L : ℝ) (hL : 0 ≤ L) :
    ∑ x ∈ S, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|))) ≤
      3 * L + (1 / α) * ∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j := by
  let S_eq := S.filter (fun (x : ℤ) => (x : ℝ) = c)
  let S_lt := S.filter (fun (x : ℤ) => (x : ℝ) < c)
  let S_gt := S.filter (fun (x : ℤ) => c < (x : ℝ))
  have h_split1 : S = S_eq ∪ S.filter (fun (x : ℤ) => (x : ℝ) ≠ c) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, S_eq]
    tauto
  have h_disj1 : Disjoint S_eq (S.filter (fun (x : ℤ) => (x : ℝ) ≠ c)) := by
    simp only [Finset.disjoint_filter, S_eq]
    intro _ _ h1 h2
    exact h2 h1
  have h_split2 : S.filter (fun (x : ℤ) => (x : ℝ) ≠ c) = S_lt ∪ S_gt := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, S_lt, S_gt]
    constructor
    · rintro ⟨hx, hne⟩
      rcases lt_or_gt_of_ne hne with h1 | h2
      · left; exact ⟨hx, h1⟩
      · right; exact ⟨hx, h2⟩
    · rintro (⟨hx, hlt⟩ | ⟨hx, hgt⟩)
      · exact ⟨hx, hlt.ne⟩
      · exact ⟨hx, hgt.ne'⟩
  have h_disj2 : Disjoint S_lt S_gt := by
    simp only [Finset.disjoint_filter, S_lt, S_gt]
    intro _ _ h1 h2
    linarith
  have h_sum_split : (∑ x ∈ S, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|)))) =
      (∑ x ∈ S_eq, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|)))) +
      (∑ x ∈ S_lt, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|)))) +
      (∑ x ∈ S_gt, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|)))) := by
    nth_rw 1 [h_split1]
    rw [Finset.sum_union h_disj1, h_split2, Finset.sum_union h_disj2]
    ring
  have h_eq_sum : ∑ x ∈ S_eq, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|))) ≤ L := by
    have : (∑ x ∈ S_eq, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|)))) =
        ∑ x ∈ S_eq, L := by
      refine Finset.sum_congr rfl fun x hx => by
        simp only [Finset.mem_filter, S_eq] at hx
        simp [hx.2]
    rw [this, Finset.sum_const, nsmul_eq_mul]
    have h_card := card_filter_cast_eq_le_one c S
    have : (S_eq.card : ℝ) ≤ 1 := by exact_mod_cast h_card
    nlinarith
  have h_lt_sum : ∑ x ∈ S_lt, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|))) ≤
      L + (1 / (2 * α)) * ∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j := by
    have h_rw : (∑ x ∈ S_lt, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|)))) =
        ∑ x ∈ S_lt, min L (1 / (2 * α * (c - (x : ℝ)))) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_filter, S_lt] at hx
      have : (x : ℝ) ≠ c := hx.2.ne
      simp only [this, ite_false]
      have : |(x : ℝ) - c| = c - (x : ℝ) := by
        rw [abs_sub_comm, abs_of_pos]
        linarith [hx.2]
      rw [this]
    rw [h_rw]
    have h_bound := sum_inv_sub_left_le_sum_harmonic c α hα S_lt (fun y hy => (Finset.mem_filter.mp hy).2) L hL
    have h_card_le : S_lt.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h_harm := sum_harmonic_le_sum_harmonic h_card_le
    have : 0 ≤ 1 / (2 * α) := by positivity
    linarith [mul_le_mul_of_nonneg_left h_harm this]
  have h_gt_sum : ∑ x ∈ S_gt, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|))) ≤
      L + (1 / (2 * α)) * ∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j := by
    have h_rw : (∑ x ∈ S_gt, (if (x : ℝ) = c then L else min L (1 / (2 * α * |(x : ℝ) - c|)))) =
        ∑ x ∈ S_gt, min L (1 / (2 * α * ((x : ℝ) - c))) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [Finset.mem_filter, S_gt] at hx
      have : (x : ℝ) ≠ c := hx.2.ne'
      simp only [this, ite_false]
      have : |(x : ℝ) - c| = (x : ℝ) - c := abs_of_pos (by linarith [hx.2])
      rw [this]
    rw [h_rw]
    have h_bound := sum_inv_sub_le_sum_harmonic c α hα S_gt (fun y hy => (Finset.mem_filter.mp hy).2) L hL
    have h_card_le : S_gt.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h_harm := sum_harmonic_le_sum_harmonic h_card_le
    have : 0 ≤ 1 / (2 * α) := by positivity
    linarith [mul_le_mul_of_nonneg_left h_harm this]
  have h_coeff : (1 / (2 * α)) + (1 / (2 * α)) = 1 / α := by
    have : (2 : ℝ) * α ≠ 0 := by positivity
    field_simp
    ring
  have h_harm_coeff : (1 / (2 * α)) * (∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j) +
      (1 / (2 * α)) * (∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j) =
      (1 / α) * (∑ j ∈ Finset.Icc (1 : ℕ) S.card, (1 : ℝ) / j) := by
    rw [← add_mul, h_coeff]
  rw [h_sum_split]
  linarith [h_eq_sum, h_lt_sum, h_gt_sum, h_harm_coeff]

lemma harmonic_fiber_bound (K : ℕ) (α : ℝ) (hα_pos : 0 < |α|) (hα_le : |α| ≤ 1)
    (hK : (K : ℝ) ≤ 1 / |α| + 2) :
    ∑ j ∈ Finset.Icc (1 : ℕ) K, (1 : ℝ) / j ≤ 3 * (1 + Real.log (1 / |α|)) := by
  have h_harm := sum_harmonic_le_one_add_log K
  have h_inv_ge1 : 1 ≤ 1 / |α| := by
    rw [one_le_div₀ hα_pos]
    exact hα_le
  have hK_le : (K : ℝ) ≤ 3 * (1 / |α|) := by linarith
  have h_log_nonneg : 0 ≤ Real.log (1 / |α|) := Real.log_nonneg h_inv_ge1
  by_cases hK0 : K = 0
  · subst hK0
    simp only [Finset.Icc_eq_empty_of_lt (by decide : 0 < 1), Finset.sum_empty]
    linarith
  · have hK_pos : 0 < (K : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hK0)
    have h_log_K : Real.log (K : ℝ) ≤ Real.log (3 * (1 / |α|)) :=
      Real.log_le_log hK_pos hK_le
    have h_log_mul : Real.log (3 * (1 / |α|)) = Real.log 3 + Real.log (1 / |α|) :=
      Real.log_mul (by norm_num) (by positivity)
    have h_log3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    linarith

lemma summand_fiber_congr (n : ℤ) (α : ℝ) (hα_ne : α ≠ 0) (L : ℝ) (x : ℤ)
    (hx : round (α * (x : ℝ)) = n) :
    (if α * (x : ℝ) = round (α * (x : ℝ)) then L else min L (1 / (2 * |α * (x : ℝ) - round (α * (x : ℝ))|))) =
    (if (x : ℝ) = (n : ℝ) / α then L else min L (1 / (2 * |α| * |(x : ℝ) - (n : ℝ) / α|))) := by
  have h_round_eq : (round (α * (x : ℝ)) : ℝ) = (n : ℝ) := by exact_mod_cast hx
  have h_eq_iff : (α * (x : ℝ) = round (α * (x : ℝ))) ↔ ((x : ℝ) = (n : ℝ) / α) := by
    rw [h_round_eq]
    constructor
    · intro h
      calc (x : ℝ) = (α * (x : ℝ)) / α := (mul_div_cancel_left₀ (x : ℝ) hα_ne).symm
        _ = (n : ℝ) / α := by rw [h]
    · intro h
      rw [h, mul_div_cancel₀ (n : ℝ) hα_ne]
  have h_dist_eq : |α * (x : ℝ) - round (α * (x : ℝ))| = |α| * |(x : ℝ) - (n : ℝ) / α| := by
    rw [h_round_eq]
    have : α * (x : ℝ) - (n : ℝ) = α * ((x : ℝ) - (n : ℝ) / α) := by
      rw [mul_sub, mul_div_cancel₀ (n : ℝ) hα_ne]
    rw [this, abs_mul]
  have : (α * (x : ℝ) = round (α * (x : ℝ))) ↔ ((x : ℝ) = (n : ℝ) / α) := h_eq_iff
  simp only [this]
  split_ifs
  · rfl
  · rw [h_dist_eq, mul_assoc]

lemma sum_fiber_le (X L : ℕ) (α : ℝ) (hα_pos : 0 < |α|) (hα_le : |α| ≤ 1) (n : ℤ) :
    let S := Finset.Icc (-(X : ℤ)) X
    let S_n := S.filter (fun (x : ℤ) => round (α * (x : ℝ)) = n)
    ∑ x ∈ S_n, (if α * (x : ℝ) = round (α * (x : ℝ)) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * (x : ℝ) - round (α * (x : ℝ))|))) ≤
      3 * ((L : ℝ) + 1 / |α|) * (1 + Real.log (1 / |α|)) := by
  intro S S_n
  have hα_ne : α ≠ 0 := by
    intro h0
    subst h0
    simp at hα_pos
  have h_congr : (∑ x ∈ S_n, (if α * (x : ℝ) = round (α * (x : ℝ)) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * (x : ℝ) - round (α * (x : ℝ))|)))) =
      ∑ x ∈ S_n, (if (x : ℝ) = (n : ℝ) / α then (L : ℝ) else min (L : ℝ) (1 / (2 * |α| * |(x : ℝ) - (n : ℝ) / α|))) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_filter, S_n] at hx
    exact summand_fiber_congr n α hα_ne (L : ℝ) x hx.2
  rw [h_congr]
  have h_split := sum_inv_dist_split_le ((n : ℝ) / α) |α| hα_pos S_n (L : ℝ) (Nat.cast_nonneg L)
  have h_harm := harmonic_fiber_bound S_n.card α hα_pos hα_le (card_filter_round_le X α hα_pos n)
  have h_inv_pos : 0 < 1 / |α| := by positivity
  have h_harm_mul : (1 / |α|) * ∑ j ∈ Finset.Icc (1 : ℕ) S_n.card, (1 : ℝ) / j ≤
      (1 / |α|) * (3 * (1 + Real.log (1 / |α|))) :=
    mul_le_mul_of_nonneg_left h_harm h_inv_pos.le
  have h_log_nonneg : 0 ≤ Real.log (1 / |α|) := by
    have : 1 ≤ 1 / |α| := by
      rw [one_le_div₀ hα_pos]
      exact hα_le
    exact Real.log_nonneg this
  have hL_nonneg : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  nlinarith

/-- Explicit constant 9 bound for distance-to-integer reciprocal sums. -/
theorem sum_min_inv_dist_le_nine (X L : ℕ) (α : ℝ) (hα_pos : 0 < |α|) (hα_le : |α| ≤ 1) :
    (∑ x ∈ Finset.Icc (-(X : ℤ)) X, (if α * x = round (α * x) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * x - round (α * x)|)))) ≤
      9 * (1 + (X : ℝ) * |α|) * ((L : ℝ) + 1 / |α|) * (1 + Real.log (1 / |α|)) := by
  let S := Finset.Icc (-(X : ℤ)) X
  let N := S.image (fun (x : ℤ) => round (α * (x : ℝ)))
  have h_fiber : (∑ x ∈ S, (if α * (x : ℝ) = round (α * (x : ℝ)) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * (x : ℝ) - round (α * (x : ℝ))|)))) =
      ∑ n ∈ N, ∑ x ∈ S.filter (fun (x : ℤ) => round (α * (x : ℝ)) = n),
        (if α * (x : ℝ) = round (α * (x : ℝ)) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * (x : ℝ) - round (α * (x : ℝ))|))) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun (x : ℤ) => round (α * (x : ℝ)))]
    intro x hx
    exact Finset.mem_image_of_mem _ hx
  rw [h_fiber]
  have h_sum_le : (∑ n ∈ N, ∑ x ∈ S.filter (fun (x : ℤ) => round (α * (x : ℝ)) = n),
        (if α * (x : ℝ) = round (α * (x : ℝ)) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * (x : ℝ) - round (α * (x : ℝ))|)))) ≤
      ∑ n ∈ N, 3 * ((L : ℝ) + 1 / |α|) * (1 + Real.log (1 / |α|)) := by
    refine Finset.sum_le_sum fun n _ => ?_
    exact sum_fiber_le X L α hα_pos hα_le n
  have h_const : (∑ n ∈ N, 3 * ((L : ℝ) + 1 / |α|) * (1 + Real.log (1 / |α|))) =
      (N.card : ℝ) * (3 * ((L : ℝ) + 1 / |α|) * (1 + Real.log (1 / |α|))) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h_card_N := card_round_image_Icc_le X α
  have h_card_le : (N.card : ℝ) ≤ 3 * (1 + (X : ℝ) * |α|) := by
    have : 0 ≤ (X : ℝ) * |α| := mul_nonneg (Nat.cast_nonneg X) (abs_nonneg α)
    linarith [h_card_N]
  have h_term_nonneg : 0 ≤ 3 * ((L : ℝ) + 1 / |α|) * (1 + Real.log (1 / |α|)) := by
    have : 0 ≤ 1 / |α| := by positivity
    have : 0 ≤ Real.log (1 / |α|) := by
      have : 1 ≤ 1 / |α| := by
        rw [one_le_div₀ hα_pos]
        exact hα_le
      exact Real.log_nonneg this
    have : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
    positivity
  have h_mul_le := mul_le_mul_of_nonneg_right h_card_le h_term_nonneg
  have h_alg : (3 * (1 + (X : ℝ) * |α|)) * (3 * ((L : ℝ) + 1 / |α|) * (1 + Real.log (1 / |α|))) =
      9 * (1 + (X : ℝ) * |α|) * ((L : ℝ) + 1 / |α|) * (1 + Real.log (1 / |α|)) := by ring
  linarith [h_sum_le, h_const, h_mul_le, h_alg]

/-- Part 2: Integral-test bound for distance-to-integer reciprocal sums. -/
theorem sum_min_inv_dist_le : ∃ C : ℝ, 0 < C ∧ ∀ (X L : ℕ) (α : ℝ), 0 < |α| → |α| ≤ 1 →
    (∑ x ∈ Finset.Icc (-(X : ℤ)) X, (if α * x = round (α * x) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * x - round (α * x)|)))) ≤
      C * (1 + X * |α|) * (L + 1 / |α|) * (1 + Real.log (1 / |α|)) :=
  ⟨9, by norm_num, sum_min_inv_dist_le_nine⟩

/-- Variant of `sum_min_inv_dist_le` with the standard `min` summand. -/
theorem sum_min_inv_dist_le' : ∃ C : ℝ, 0 < C ∧ ∀ (X L : ℕ) (α : ℝ), 0 < |α| → |α| ≤ 1 →
    (∑ x ∈ Finset.Icc (-(X : ℤ)) X, min (L : ℝ) (1 / (2 * |α * x - round (α * x)|))) ≤
      C * (1 + X * |α|) * (L + 1 / |α|) * (1 + Real.log (1 / |α|)) := by
  rcases sum_min_inv_dist_le with ⟨C, hC_pos, hC⟩
  refine ⟨C, hC_pos, fun X L α hα_pos hα_le => ?_⟩
  have h_le : (∑ x ∈ Finset.Icc (-(X : ℤ)) X, min (L : ℝ) (1 / (2 * |α * x - round (α * x)|))) ≤
      ∑ x ∈ Finset.Icc (-(X : ℤ)) X, (if α * x = round (α * x) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * x - round (α * x)|))) := by
    refine Finset.sum_le_sum fun x _ => ?_
    split_ifs with h
    · exact min_le_left _ _
    · rfl
  exact h_le.trans (hC X L α hα_pos hα_le)

/-! ### Part 3: Bilinear exponential sums (Tao Lemma 12) -/

lemma norm_inner_sum_exp_mul_le (L : ℕ) (hL : 1 ≤ L) (α : ℝ) (x : ℤ) :
    ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖ ≤
      3 * (if α * (x : ℝ) = round (α * (x : ℝ)) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * (x : ℝ) - round (α * (x : ℝ))|))) := by
  let θ := α * (x : ℝ)
  have h_rw : (∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (α * x * y))) =
      ∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (θ * (y : ℤ))) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 2
    dsimp [θ]
    push_cast
    ring
  rw [h_rw]

  split_ifs with hθ
  · have h_triv := norm_sum_exp_Icc_le_trivial L θ
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  · have h_pos : 0 < |θ - round θ| := by
      have : θ - round θ ≠ 0 := sub_ne_zero.mpr hθ
      exact abs_pos.mpr this
    have h_bound := norm_sum_exp_Icc_le L θ h_pos
    have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    have h_2L1 : (2 * (L : ℝ) + 1) ≤ 3 * (L : ℝ) := by linarith
    have h_min1 : min (2 * (L : ℝ) + 1) (1 / (2 * |θ - round θ|)) ≤
        3 * min (L : ℝ) (1 / (2 * |θ - round θ|)) := by
      rw [mul_min_of_nonneg _ _ (by norm_num)]
      apply le_min
      · exact (min_le_left _ _).trans h_2L1
      · have : 0 ≤ 1 / (2 * |θ - round θ|) := by positivity
        linarith [min_le_right (2 * (L : ℝ) + 1) (1 / (2 * |θ - round θ|))]
    exact h_bound.trans h_min1

lemma alpha_bounds_of_pow_bounds (M ℓ j : ℕ) (c₀ α : ℝ) (hM : 2 ≤ M) (_hℓ : 1 ≤ ℓ) (_hj : 1 ≤ j)
    (_hc0_pos : 0 < c₀) (_hc0_le1 : c₀ ≤ 1)
    (hα_low : (M : ℝ) ^ (-(2 - c₀) * j) ≤ |α|)
    (hα_high : |α| ≤ (M : ℝ) ^ (-c₀ * j)) :
    0 < |α| ∧ |α| ≤ 1 := by
  have hM_pos : 0 < (M : ℝ) := by positivity
  have h1 : 0 < (M : ℝ) ^ (-(2 - c₀) * j) := by positivity
  have h_low : 0 < |α| := h1.trans_le hα_low
  have h2 : (M : ℝ) ^ (-c₀ * j) ≤ 1 := by
    have : -c₀ * (j : ℝ) ≤ 0 := by
      have : 0 ≤ c₀ * (j : ℝ) := by positivity
      linarith
    have hM1 : 1 ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
    calc (M : ℝ) ^ (-c₀ * j)
      _ ≤ (M : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 this
      _ = 1 := Real.rpow_zero _
  exact ⟨h_low, hα_high.trans h2⟩

lemma log_inv_alpha_le (M j : ℕ) (c₀ α : ℝ) (hM : 2 ≤ M) (_hj : 1 ≤ j)
    (_hc0_pos : 0 < c₀) (_hc0_le1 : c₀ ≤ 1)
    (hα_low : (M : ℝ) ^ (-(2 - c₀) * j) ≤ |α|) :
    1 + Real.log (1 / |α|) ≤ 2 * (1 + (j : ℝ) * Real.log (M : ℝ)) := by
  have hM_pos : 0 < (M : ℝ) := by positivity
  have h1 : 0 < (M : ℝ) ^ (-(2 - c₀) * j) := by positivity
  have h_low : 0 < |α| := h1.trans_le hα_low
  have h_inv : 1 / |α| ≤ ((M : ℝ) ^ (-(2 - c₀) * j))⁻¹ := by
    rw [one_div]
    exact inv_le_inv₀ h_low h1 |>.mpr hα_low
  have h_inv_rpow : ((M : ℝ) ^ (-(2 - c₀) * j))⁻¹ = (M : ℝ) ^ ((2 - c₀) * (j : ℝ)) := by
    rw [← Real.rpow_neg hM_pos.le]
    ring_nf
  rw [h_inv_rpow] at h_inv
  have h_exp_le : (2 - c₀) * (j : ℝ) ≤ 2 * (j : ℝ) := by
    have : 0 ≤ (j : ℝ) := by positivity
    nlinarith
  have hM1 : 1 ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
  have h_rpow_le : (M : ℝ) ^ ((2 - c₀) * (j : ℝ)) ≤ (M : ℝ) ^ (2 * (j : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hM1 h_exp_le
  have h_inv_le : 1 / |α| ≤ (M : ℝ) ^ (2 * (j : ℝ)) := h_inv.trans h_rpow_le
  have h_log_le : Real.log (1 / |α|) ≤ Real.log ((M : ℝ) ^ (2 * (j : ℝ))) :=
    Real.log_le_log (by positivity) h_inv_le
  have h_log_rpow : Real.log ((M : ℝ) ^ (2 * (j : ℝ))) = 2 * (j : ℝ) * Real.log (M : ℝ) :=
    Real.log_rpow hM_pos (2 * (j : ℝ))
  rw [h_log_rpow] at h_log_le
  have h_logM_pos : 0 < Real.log (M : ℝ) := by
    rw [Real.log_pos_iff hM_pos.le]
    exact_mod_cast (by omega : 1 < M)
  nlinarith

lemma prod_inv_alpha_le (M ℓ j : ℕ) (c₀ α : ℝ) (hM : 2 ≤ M) (_hℓ : 1 ≤ ℓ) (_hj : 1 ≤ j)
    (_hc0_pos : 0 < c₀) (_hc0_le1 : c₀ ≤ 1)
    (hα_low : (M : ℝ) ^ (-(2 - c₀) * j) ≤ |α|)
    (hα_high : |α| ≤ (M : ℝ) ^ (-c₀ * j)) :
    let X := (ℓ : ℝ) * (M : ℝ) ^ j
    let L := (ℓ : ℝ) * (M : ℝ) ^ j
    (1 + X * |α|) * (L + 1 / |α|) ≤
      4 * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) := by
  intro X L
  have hM_pos : 0 < (M : ℝ) := by positivity
  have h1 : 0 < (M : ℝ) ^ (-(2 - c₀) * j) := by positivity
  have h_low : 0 < |α| := h1.trans_le hα_low
  have h_inv : 1 / |α| ≤ ((M : ℝ) ^ (-(2 - c₀) * j))⁻¹ := by
    rw [one_div]
    exact inv_le_inv₀ h_low h1 |>.mpr hα_low
  have h_inv_rpow : ((M : ℝ) ^ (-(2 - c₀) * j))⁻¹ = (M : ℝ) ^ ((2 - c₀) * (j : ℝ)) := by
    rw [← Real.rpow_neg hM_pos.le]
    ring_nf
  rw [h_inv_rpow] at h_inv
  have h_rpow_split : (M : ℝ) ^ ((2 - c₀) * (j : ℝ)) = (M : ℝ) ^ (-c₀ * (j : ℝ)) * (M : ℝ) ^ (2 * (j : ℝ)) := by
    have : (2 - c₀) * (j : ℝ) = -c₀ * (j : ℝ) + 2 * (j : ℝ) := by ring
    rw [this, Real.rpow_add hM_pos]
  rw [h_rpow_split] at h_inv
  have h_rpow_nat : (M : ℝ) ^ (2 * (j : ℝ)) = (M : ℝ) ^ (2 * j) := by
    rw [← Real.rpow_natCast]
    push_cast
    ring_nf
  rw [h_rpow_nat] at h_inv
  have h_inv_bound : 1 / |α| ≤ (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) := by
    calc 1 / |α| ≤ (M : ℝ) ^ (-c₀ * (j : ℝ)) * (M : ℝ) ^ (2 * j) := h_inv
      _ ≤ (ℓ : ℝ) ^ 2 * ((M : ℝ) ^ (-c₀ * (j : ℝ)) * (M : ℝ) ^ (2 * j)) := by
        have : 1 ≤ (ℓ : ℝ) ^ 2 := by
          have : 1 ≤ (ℓ : ℝ) := by exact_mod_cast _hℓ
          nlinarith
        have : 0 ≤ (M : ℝ) ^ (-c₀ * (j : ℝ)) * (M : ℝ) ^ (2 * j) := by positivity
        nlinarith
      _ = (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) := by ring
  have h_XL : X * L * |α| ≤ (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) := by
    have h_XL_eq : X * L = (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * j) := by
      dsimp [X, L]
      have : ((M : ℝ) ^ j) * ((M : ℝ) ^ j) = (M : ℝ) ^ (2 * j) := by
        rw [← pow_add]
        ring_nf
      calc (ℓ : ℝ) * (M : ℝ) ^ j * ((ℓ : ℝ) * (M : ℝ) ^ j)
        _ = (ℓ : ℝ) ^ 2 * (((M : ℝ) ^ j) * ((M : ℝ) ^ j)) := by ring
        _ = (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * j) := by rw [this]
    rw [h_XL_eq]
    have h_mul : (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * j) * |α| ≤ (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * j) * (M : ℝ) ^ (-c₀ * j) := by
      have : 0 ≤ (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * j) := by positivity
      exact mul_le_mul_of_nonneg_left hα_high this
    calc (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * j) * |α|
      _ ≤ (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (2 * j) * (M : ℝ) ^ (-c₀ * j) := h_mul
      _ = (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) := by ring
  have h_cross : L + X ≤ 2 * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) := by
    dsimp [X, L]
    have h_sum : (ℓ : ℝ) * (M : ℝ) ^ j + (ℓ : ℝ) * (M : ℝ) ^ j = 2 * (ℓ : ℝ) * (M : ℝ) ^ j := by ring
    rw [h_sum]
    have h_exp : (j : ℝ) ≤ -c₀ * (j : ℝ) + 2 * (j : ℝ) := by
      have : c₀ * (j : ℝ) ≤ (j : ℝ) := by
        have : 0 ≤ (j : ℝ) := by positivity
        nlinarith
      linarith
    have hM1 : 1 ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
    have h_rpow_le : (M : ℝ) ^ (j : ℝ) ≤ (M : ℝ) ^ (-c₀ * (j : ℝ) + 2 * (j : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hM1 h_exp
    rw [Real.rpow_add hM_pos] at h_rpow_le
    rw [Real.rpow_natCast] at h_rpow_le
    rw [h_rpow_nat] at h_rpow_le
    have h_2ell : 2 * (ℓ : ℝ) ≤ 2 * (ℓ : ℝ) ^ 2 := by
      have : 1 ≤ (ℓ : ℝ) := by exact_mod_cast _hℓ
      nlinarith
    have : 0 ≤ (M : ℝ) ^ (-c₀ * (j : ℝ)) * (M : ℝ) ^ (2 * j) := by positivity
    nlinarith
  have h_cancel : X * |α| * (1 / |α|) = X := by
    rw [mul_assoc, mul_one_div_cancel h_low.ne', mul_one]
  have h_expand : (1 + X * |α|) * (L + 1 / |α|) = L + 1 / |α| + X * L * |α| + X := by
    calc (1 + X * |α|) * (L + 1 / |α|)
      _ = L + 1 / |α| + (X * |α| * L + X * |α| * (1 / |α|)) := by ring
      _ = L + 1 / |α| + (X * |α| * L + X) := by rw [h_cancel]
      _ = L + 1 / |α| + X * L * |α| + X := by ring
  rw [h_expand]
  linarith [h_inv_bound, h_XL, h_cross]

/-- Part 3: Lemma 12 conclusion for one coordinate. -/
theorem sum_norm_sum_exp_mul_le : ∃ C : ℝ, 0 < C ∧ ∀ (M ℓ j : ℕ) (c₀ α : ℝ), 2 ≤ M → 1 ≤ ℓ → 1 ≤ j → 0 < c₀ → c₀ ≤ 1 →
    (M : ℝ) ^ (-(2 - c₀) * j) ≤ |α| → |α| ≤ (M : ℝ) ^ (-c₀ * j) →
    (∑ x ∈ Finset.Icc (-(ℓ * M ^ j : ℤ)) (ℓ * M ^ j),
        ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ j : ℤ)) (ℓ * M ^ j), Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖) ≤
      C * ℓ ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) * (1 + j * Real.log M) := by
  use 216
  refine ⟨by norm_num, fun M ℓ j c₀ α hM hℓ hj hc0_pos hc0_le1 hα_low hα_high => ?_⟩
  let L := ℓ * M ^ j
  have hL_pos : 1 ≤ L := by
    have : 1 ≤ M ^ j := one_le_pow₀ (by omega)
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hα_bounds := alpha_bounds_of_pow_bounds M ℓ j c₀ α hM hℓ hj hc0_pos hc0_le1 hα_low hα_high
  have h_inner : (∑ x ∈ Finset.Icc (-(L : ℤ)) L,
        ‖∑ y ∈ Finset.Icc (-(L : ℤ)) L, Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖) ≤
      3 * ∑ x ∈ Finset.Icc (-(L : ℤ)) L,
        (if α * (x : ℝ) = round (α * (x : ℝ)) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * (x : ℝ) - round (α * (x : ℝ))|))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => norm_inner_sum_exp_mul_le L hL_pos α x
  have h_part2 := sum_min_inv_dist_le_nine L L α hα_bounds.1 hα_bounds.2
  have h_prod := prod_inv_alpha_le M ℓ j c₀ α hM hℓ hj hc0_pos hc0_le1 hα_low hα_high
  have h_log := log_inv_alpha_le M j c₀ α hM hj hc0_pos hc0_le1 hα_low
  have hL_cast : (L : ℝ) = (ℓ : ℝ) * (M : ℝ) ^ j := by
    dsimp [L]
    push_cast
    rfl
  have h_step_part2 : (∑ x ∈ Finset.Icc (-(L : ℤ)) L,
        if α * (x : ℝ) = round (α * (x : ℝ)) then (L : ℝ)
        else min (L : ℝ) (1 / (2 * |α * (x : ℝ) - round (α * (x : ℝ))|))) ≤
      9 * (1 + (ℓ : ℝ) * (M : ℝ) ^ j * |α|) * ((ℓ : ℝ) * (M : ℝ) ^ j + 1 / |α|) * (1 + Real.log (1 / |α|)) := by
    rw [← hL_cast]
    exact h_part2
  have h_prod_nonneg : 0 ≤ 4 * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) := by positivity
  have h_step2 : 0 ≤ 1 + Real.log (1 / |α|) := by
    have : 1 ≤ 1 / |α| := by
      rw [one_le_div₀ hα_bounds.1]
      exact hα_bounds.2
    have := Real.log_nonneg this
    linarith
  have h_mul_both : (1 + (ℓ : ℝ) * (M : ℝ) ^ j * |α|) * ((ℓ : ℝ) * (M : ℝ) ^ j + 1 / |α|) * (1 + Real.log (1 / |α|)) ≤
      (4 * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j)) * (2 * (1 + (j : ℝ) * Real.log (M : ℝ))) :=
    mul_le_mul h_prod h_log h_step2 h_prod_nonneg
  have h_alg : 3 * (9 * (1 + (ℓ : ℝ) * (M : ℝ) ^ j * |α|) * ((ℓ : ℝ) * (M : ℝ) ^ j + 1 / |α|) * (1 + Real.log (1 / |α|))) ≤
      216 * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) * (1 + (j : ℝ) * Real.log (M : ℝ)) := by
    calc 3 * (9 * (1 + (ℓ : ℝ) * (M : ℝ) ^ j * |α|) * ((ℓ : ℝ) * (M : ℝ) ^ j + 1 / |α|) * (1 + Real.log (1 / |α|)))
      _ = 27 * ((1 + (ℓ : ℝ) * (M : ℝ) ^ j * |α|) * ((ℓ : ℝ) * (M : ℝ) ^ j + 1 / |α|) * (1 + Real.log (1 / |α|))) := by ring
      _ ≤ 27 * ((4 * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j)) * (2 * (1 + (j : ℝ) * Real.log (M : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left h_mul_both (by norm_num)
      _ = 216 * (ℓ : ℝ) ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) * (1 + (j : ℝ) * Real.log (M : ℝ)) := by ring
  calc (∑ x ∈ Finset.Icc (-(ℓ * M ^ j : ℤ)) (ℓ * M ^ j),
        ‖∑ y ∈ Finset.Icc (-(ℓ * M ^ j : ℤ)) (ℓ * M ^ j), Complex.exp (2 * Real.pi * Complex.I * (α * x * y))‖)
    _ ≤ 3 * ∑ x ∈ Finset.Icc (-(L : ℤ)) L,
          (if α * (x : ℝ) = round (α * (x : ℝ)) then (L : ℝ) else min (L : ℝ) (1 / (2 * |α * (x : ℝ) - round (α * (x : ℝ))|))) := h_inner
    _ ≤ 3 * (9 * (1 + (ℓ : ℝ) * (M : ℝ) ^ j * |α|) * ((ℓ : ℝ) * (M : ℝ) ^ j + 1 / |α|) * (1 + Real.log (1 / |α|))) :=
      mul_le_mul_of_nonneg_left h_step_part2 (by norm_num)
    _ ≤ 216 * ℓ ^ 2 * (M : ℝ) ^ (-c₀ * j) * (M : ℝ) ^ (2 * j) * (1 + j * Real.log M) := h_alg

end Erdos1201.MR.Vinogradov











