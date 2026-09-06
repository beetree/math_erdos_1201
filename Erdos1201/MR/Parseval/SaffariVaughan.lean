import Mathlib

/-!
# Saffari–Vaughan Averaging for Window Sums

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This file formalizes the Saffari–Vaughan averaging step from the proof of
Matomäki–Radziwiłł Lemma 14: an additive window sum is controlled by an average
of multiplicative window sums.

## Main Definitions and Results

* `Erdos1201.MR.windowSum`: The sum of coefficients `a n` over integers `n` with `x < n ≤ y`.
* `Erdos1201.MR.norm_sq_windowSum_le`: The Saffari–Vaughan bound controlling `‖windowSum a x (x + h)‖ ^ 2`
  by two integral averages over scaled multiplicative windows.
-/

open MeasureTheory

namespace Erdos1201.MR

/-- Sum of `a n` over the integers n with x < n ≤ y (real endpoints). -/
noncomputable def windowSum (a : ℕ → ℂ) (x y : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun (n : ℕ) => x < n), a n

/-- Measurability of `windowSum a x y` as a function of the upper endpoint `y`. -/
lemma measurable_windowSum (a : ℕ → ℂ) (x : ℝ) :
    Measurable (fun y => windowSum a x y) := by
  have h : (fun y => windowSum a x y) =
      (fun k => ∑ n ∈ (Finset.Ioc 0 k).filter (fun (n : ℕ) => x < n), a n) ∘ Nat.floor := rfl
  rw [h]
  exact (measurable_of_countable _).comp Nat.measurable_floor

/-- Uniform bound on `‖windowSum a x y‖` for `y ≤ B`. -/
lemma norm_windowSum_le (a : ℕ → ℂ) (x y B : ℝ) (hy : y ≤ B) :
    ‖windowSum a x y‖ ≤ ∑ n ∈ Finset.Ioc 0 ⌊B⌋₊, ‖a n‖ := by
  dsimp [windowSum]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => norm_nonneg _)
  intro n hn
  rw [Finset.mem_filter] at hn
  rw [Finset.mem_Ioc] at hn ⊢
  refine ⟨hn.1.1, ?_⟩
  exact hn.1.2.trans (Nat.floor_le_floor hy)

/-- Any bounded measurable complex function on a compact interval is interval-integrable. -/
lemma intervalIntegrable_of_bounded_complex {a b : ℝ}
    {g : ℝ → ℂ} (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Set.uIoc a b, ‖g x‖ ≤ C) :
    IntervalIntegrable g volume a b := by
  have hconst : IntervalIntegrable (fun _ : ℝ => C) volume a b := intervalIntegrable_const
  refine IntervalIntegrable.mono_fun hconst hg.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  apply Filter.Eventually.of_forall
  intro x hx
  simp only [Real.norm_of_nonneg hC0]
  exact hC x hx

/-- Any bounded measurable real function on a compact interval is interval-integrable. -/
lemma intervalIntegrable_of_bounded_real {a b : ℝ}
    {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x ∈ Set.uIoc a b, ‖g x‖ ≤ C) :
    IntervalIntegrable g volume a b := by
  have hconst : IntervalIntegrable (fun _ : ℝ => C) volume a b := intervalIntegrable_const
  refine IntervalIntegrable.mono_fun hconst hg.aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_uIoc).mpr ?_
  apply Filter.Eventually.of_forall
  intro x hx
  simp only [Real.norm_of_nonneg hC0]
  exact hC x hx

/-- Interval integrability of `w ↦ windowSum a y (x + w)` on `[h, 3h]`. -/
lemma intervalIntegrable_windowSum_add (a : ℕ → ℂ) (y x h : ℝ) (hh : 0 ≤ h) :
    IntervalIntegrable (fun w => windowSum a y (x + w)) volume h (3 * h) := by
  have hmeas : Measurable (fun w => windowSum a y (x + w)) :=
    (measurable_windowSum a y).comp (continuous_const_add x).measurable
  set B := x + 3 * h
  set C := ∑ n ∈ Finset.Ioc 0 ⌊B⌋₊, ‖a n‖
  have hC0 : 0 ≤ C := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  refine intervalIntegrable_of_bounded_complex hmeas hC0 ?_
  intro w hw
  rw [Set.uIoc_of_le (by linarith : h ≤ 3 * h)] at hw
  refine norm_windowSum_le a y (x + w) B ?_
  linarith [hw.2]

/-- Interval integrability of `w ↦ ‖windowSum a y (x + w)‖ ^ 2` on `[h, 3h]`. -/
lemma intervalIntegrable_norm_sq_windowSum_add (a : ℕ → ℂ) (y x h : ℝ) (hh : 0 ≤ h) :
    IntervalIntegrable (fun w => ‖windowSum a y (x + w)‖ ^ 2) volume h (3 * h) := by
  have hmeas : Measurable (fun w => ‖windowSum a y (x + w)‖ ^ 2) := by
    have h1 : Measurable (fun w => windowSum a y (x + w)) :=
      (measurable_windowSum a y).comp (continuous_const_add x).measurable
    exact (continuous_norm.measurable.comp h1).pow_const 2
  set B := x + 3 * h
  set C := (∑ n ∈ Finset.Ioc 0 ⌊B⌋₊, ‖a n‖) ^ 2
  have hC0 : 0 ≤ C := sq_nonneg _
  refine intervalIntegrable_of_bounded_real hmeas hC0 ?_
  intro w hw
  rw [Set.uIoc_of_le (by linarith : h ≤ 3 * h)] at hw
  have hwB : x + w ≤ B := by linarith [hw.2]
  have hle := norm_windowSum_le a y (x + w) B hwB
  have hsq := sq_le_sq' (by linarith [norm_nonneg (windowSum a y (x + w))]) hle
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hsq

/-- Interval integrability of `u ↦ ‖windowSum a x (x * (1 + u))‖ ^ 2` on `[h / x, 3 * h / x]`. -/
lemma intervalIntegrable_norm_sq_windowSum_scaled (a : ℕ → ℂ) (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    IntervalIntegrable (fun u => ‖windowSum a x (x * (1 + u))‖ ^ 2) volume (h / x) (3 * h / x) := by
  have hmeas : Measurable (fun u => ‖windowSum a x (x * (1 + u))‖ ^ 2) := by
    have hcont : Continuous (fun u : ℝ => x * (1 + u)) :=
      continuous_const.mul (continuous_const.add continuous_id)
    have h1 : Measurable (fun u => windowSum a x (x * (1 + u))) :=
      (measurable_windowSum a x).comp hcont.measurable
    exact (continuous_norm.measurable.comp h1).pow_const 2
  set B := x + 3 * h
  set C := (∑ n ∈ Finset.Ioc 0 ⌊B⌋₊, ‖a n‖) ^ 2
  have hC0 : 0 ≤ C := sq_nonneg _
  have hle : h / x ≤ 3 * h / x := div_le_div_of_nonneg_right (by linarith) (by linarith)
  refine intervalIntegrable_of_bounded_real hmeas hC0 ?_
  intro u hu
  rw [Set.uIoc_of_le hle] at hu
  have huB : x * (1 + u) ≤ B := by
    calc
      x * (1 + u) = x + x * u := by ring
      _ ≤ x + x * (3 * h / x) := by
        have : x * u ≤ x * (3 * h / x) := mul_le_mul_of_nonneg_left hu.2 (by linarith)
        linarith
      _ = B := by
        dsimp [B]
        have hx_ne : x ≠ 0 := ne_of_gt hx
        rw [mul_div_cancel₀ (3 * h) hx_ne]
  have hnorm_le := norm_windowSum_le a x (x * (1 + u)) B huB
  have hsq := sq_le_sq' (by linarith [norm_nonneg (windowSum a x (x * (1 + u)))]) hnorm_le
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hsq

/-- Pointwise splitting identity for `windowSum`: for `h ≤ w`,
`windowSum a x (x + h) = windowSum a x (x + w) - windowSum a (x + h) (x + w)`. -/
lemma windowSum_add_split (a : ℕ → ℂ) (x h w : ℝ) (hx : 0 < x) (hh : 0 < h) (hw : h ≤ w) :
    windowSum a x (x + h) = windowSum a x (x + w) - windowSum a (x + h) (x + w) := by
  dsimp [windowSum]
  rw [eq_sub_iff_add_eq]
  rw [← Finset.sum_union]
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro (⟨⟨h0n, hn_le⟩, hxn⟩ | ⟨⟨h0n, hn_le⟩, hxhn⟩)
      · refine ⟨⟨h0n, ?_⟩, hxn⟩
        have h1 : (n : ℝ) ≤ x + h := (Nat.le_floor_iff (by linarith)).mp hn_le
        have h2 : (n : ℝ) ≤ x + w := by linarith
        exact (Nat.le_floor_iff (by linarith)).mpr h2
      · refine ⟨⟨h0n, hn_le⟩, by linarith⟩
    · rintro ⟨⟨h0n, hn_le⟩, hxn⟩
      by_cases hnh : (n : ℝ) ≤ x + h
      · left
        refine ⟨⟨h0n, (Nat.le_floor_iff (by linarith)).mpr hnh⟩, hxn⟩
      · right
        have hnh' : x + h < (n : ℝ) := lt_of_not_ge hnh
        refine ⟨⟨h0n, hn_le⟩, hnh'⟩
  · rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn1 hn2
    have h1 : (n : ℝ) ≤ x + h := (Nat.le_floor_iff (by linarith)).mp hn1.1.2
    have h2 : x + h < (n : ℝ) := hn2.2
    linarith

/-- Cauchy–Schwarz inequality for interval integrals:
`(∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2`. -/
lemma sq_integral_le_integral_sq (a b : ℝ) (hab : a ≤ b) (g : ℝ → ℝ)
    (hg : IntervalIntegrable g volume a b) (hg2 : IntervalIntegrable (fun x => g x ^ 2) volume a b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  by_cases h : a = b
  · subst h
    simp
  have hab_lt : a < b := lt_of_le_of_ne hab h
  have hba_pos : 0 < b - a := sub_pos.mpr hab_lt
  set I := ∫ x in a..b, g x
  set c := I / (b - a)
  have h_pointwise : ∀ x, 2 * c * g x - c ^ 2 ≤ g x ^ 2 := by
    intro x
    have : 0 ≤ (g x - c) ^ 2 := sq_nonneg _
    linarith
  have h_int_lin : IntervalIntegrable (fun x => 2 * c * g x - c ^ 2) volume a b := by
    apply IntervalIntegrable.sub
    · exact hg.const_mul (2 * c)
    · exact intervalIntegrable_const
  have h_mono := intervalIntegral.integral_mono hab h_int_lin hg2 h_pointwise
  rw [intervalIntegral.integral_sub (hg.const_mul (2 * c)) intervalIntegrable_const] at h_mono
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h_mono
  simp only [smul_eq_mul] at h_mono
  have h_alg : 2 * c * I - (b - a) * c ^ 2 = I ^ 2 / (b - a) := by
    dsimp [c]
    have : b - a ≠ 0 := ne_of_gt hba_pos
    field_simp
    ring
  rw [h_alg] at h_mono
  rw [mul_comm]
  exact (div_le_iff₀ hba_pos).mp h_mono

/-- First substitution identity: substitution `w = x * u` converts the interval integral
over `w ∈ [h, 3 * h]` into an integral over `u ∈ [h / x, 3 * h / x]`. -/
lemma integral_subst_first (a : ℕ → ℂ) (x h : ℝ) (hx : 0 < x) :
    (x / h) * ∫ u in (h / x)..(3 * h / x), ‖windowSum a x (x * (1 + u))‖ ^ 2 =
    (1 / h) * ∫ w in h..(3 * h), ‖windowSum a x (x + w)‖ ^ 2 := by
  have hx_ne : x ≠ 0 := ne_of_gt hx
  set f := fun w => ‖windowSum a x (x + w)‖ ^ 2
  have h_comp : (fun u => ‖windowSum a x (x * (1 + u))‖ ^ 2) = (fun u => f (x * u)) := by
    ext u
    dsimp [f]
    congr 2
    congr 1
    calc
      x * (1 + u) = x * 1 + x * u := mul_add x 1 u
      _ = x + x * u := by rw [mul_one]
  rw [h_comp]
  have h_int := intervalIntegral.integral_comp_mul_left f hx_ne (a := h / x) (b := 3 * h / x)
  simp only [smul_eq_mul] at h_int
  have h1 : x * (h / x) = h := mul_div_cancel₀ h hx_ne
  have h2 : x * (3 * h / x) = 3 * h := mul_div_cancel₀ (3 * h) hx_ne
  rw [h1, h2] at h_int
  rw [h_int]
  set I := ∫ w in h..(3 * h), f w
  calc
    (x / h) * (x⁻¹ * I) = ((x / h) * x⁻¹) * I := by rw [mul_assoc]
    _ = (1 / h) * I := by
      congr 1
      rw [div_mul_eq_mul_div, mul_comm, inv_mul_cancel₀ hx_ne]

/-- Second substitution identity: substitution `w = h + (x + h) * u` converts the interval integral
over `w ∈ [h, 3 * h]` into an integral over `u ∈ [0, 2 * h / (x + h)]`. -/
lemma integral_subst_second (a : ℕ → ℂ) (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    ((x + h) / h) * ∫ u in (0 : ℝ)..(2 * h / (x + h)), ‖windowSum a (x + h) ((x + h) * (1 + u))‖ ^ 2 =
    (1 / h) * ∫ w in h..(3 * h), ‖windowSum a (x + h) (x + w)‖ ^ 2 := by
  have hxh_pos : 0 < x + h := add_pos hx hh
  have hxh_ne : x + h ≠ 0 := ne_of_gt hxh_pos
  set f := fun w => ‖windowSum a (x + h) (x + w)‖ ^ 2
  have h_comp : (fun u => ‖windowSum a (x + h) ((x + h) * (1 + u))‖ ^ 2) =
      (fun u => f ((x + h) * u + h)) := by
    ext u
    dsimp [f]
    congr 2
    congr 1
    calc
      (x + h) * (1 + u) = (x + h) * 1 + (x + h) * u := mul_add (x + h) 1 u
      _ = x + h + (x + h) * u := by rw [mul_one]
      _ = x + ((x + h) * u + h) := by ring
  rw [h_comp]
  set g := fun v => f (v + h)
  have h_mul := intervalIntegral.integral_comp_mul_left g hxh_ne (a := 0) (b := 2 * h / (x + h))
  simp only [smul_eq_mul] at h_mul
  rw [mul_zero, mul_div_cancel₀ (2 * h) hxh_ne] at h_mul
  have h_comp2 : (fun u => f ((x + h) * u + h)) = (fun u => g ((x + h) * u)) := rfl
  rw [h_comp2, h_mul]
  have h_shift := intervalIntegral.integral_comp_add_right f h (a := 0) (b := 2 * h)
  have h0h : 0 + h = h := zero_add h
  have h2h : 2 * h + h = 3 * h := by ring
  rw [h0h, h2h] at h_shift
  rw [← h_shift]
  set I := ∫ (x_1 : ℝ) in 0..2 * h, f (x_1 + h)
  calc
    ((x + h) / h) * ((x + h)⁻¹ * I) = (((x + h) / h) * (x + h)⁻¹) * I := by rw [mul_assoc]
    _ = (1 / h) * I := by
      congr 1
      rw [div_mul_eq_mul_div, mul_comm, inv_mul_cancel₀ hxh_ne]

/-- Quadratic inequality `(A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2`. -/
lemma sq_add_le_two_mul_sq_add_sq (A B : ℝ) : (A + B) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
  have : 0 ≤ (A - B) ^ 2 := sq_nonneg _
  linarith

/-- **Saffari–Vaughan Averaging Step (Matomäki–Radziwiłł Lemma 14)**:
An additive window sum is controlled by an average of multiplicative window sums. -/
theorem norm_sq_windowSum_le (a : ℕ → ℂ) (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    ‖windowSum a x (x + h)‖ ^ 2 ≤
      (x / h) * ∫ u in (h / x)..(3 * h / x), ‖windowSum a x (x * (1 + u))‖ ^ 2 +
      ((x + h) / h) * ∫ u in (0 : ℝ)..(2 * h / (x + h)), ‖windowSum a (x + h) ((x + h) * (1 + u))‖ ^ 2 := by
  have h_le_3h : h ≤ 3 * h := by linarith
  have h2h_pos : 0 < 2 * h := by linarith
  have h2h_ne : (2 * h : ℝ) ≠ 0 := ne_of_gt h2h_pos
  set S := windowSum a x (x + h)
  set F := fun w => windowSum a x (x + w)
  set G := fun w => windowSum a (x + h) (x + w)
  have hF_int : IntervalIntegrable F volume h (3 * h) :=
    intervalIntegrable_windowSum_add a x x h (by linarith)
  have hG_int : IntervalIntegrable G volume h (3 * h) :=
    intervalIntegrable_windowSum_add a (x + h) x h (by linarith)
  have hF2_int : IntervalIntegrable (fun w => ‖F w‖ ^ 2) volume h (3 * h) :=
    intervalIntegrable_norm_sq_windowSum_add a x x h (by linarith)
  have hG2_int : IntervalIntegrable (fun w => ‖G w‖ ^ 2) volume h (3 * h) :=
    intervalIntegrable_norm_sq_windowSum_add a (x + h) x h (by linarith)
  have h_eq_on : Set.EqOn (fun _ => S) (fun w => F w - G w) (Set.uIcc h (3 * h)) := by
    intro w hw
    rw [Set.uIcc_of_le h_le_3h] at hw
    exact windowSum_add_split a x h w hx hh hw.1
  have h_int_eq : ∫ w in h..(3 * h), S = ∫ w in h..(3 * h), (F w - G w) :=
    intervalIntegral.integral_congr (μ := volume) h_eq_on
  have h_lhs : ∫ w in h..(3 * h), S = (2 * h) • S := by
    have := intervalIntegral.integral_const (a := h) (b := 3 * h) S
    rw [this]
    congr 1
    ring
  have h_rhs : ∫ w in h..(3 * h), (F w - G w) = (∫ w in h..(3 * h), F w) - (∫ w in h..(3 * h), G w) :=
    intervalIntegral.integral_sub hF_int hG_int
  rw [h_lhs, h_rhs] at h_int_eq
  set IF := ∫ w in h..(3 * h), F w
  set IG := ∫ w in h..(3 * h), G w
  have h_smul : (2 * h) • S = IF - IG := h_int_eq
  have h_norm_smul : ‖(2 * h) • S‖ = ‖IF - IG‖ := by rw [h_smul]
  rw [norm_smul, Real.norm_of_nonneg (by linarith)] at h_norm_smul
  have h_norm_S : ‖S‖ = (2 * h)⁻¹ * ‖IF - IG‖ := by
    calc
      ‖S‖ = (2 * h)⁻¹ * ((2 * h) * ‖S‖) := by rw [inv_mul_cancel_left₀ h2h_ne]
      _ = (2 * h)⁻¹ * ‖IF - IG‖ := by rw [h_norm_smul]
  have h_norm_sq_S : ‖S‖ ^ 2 = (2 * h)⁻¹ ^ 2 * ‖IF - IG‖ ^ 2 := by
    rw [h_norm_S, mul_pow]
  have h_diff_le : ‖IF - IG‖ ≤ ‖IF‖ + ‖IG‖ := norm_sub_le IF IG
  have h_diff_sq_le : ‖IF - IG‖ ^ 2 ≤ 2 * ‖IF‖ ^ 2 + 2 * ‖IG‖ ^ 2 := by
    have h1 : ‖IF - IG‖ ^ 2 ≤ (‖IF‖ + ‖IG‖) ^ 2 := by
      refine sq_le_sq' ?_ h_diff_le
      linarith [norm_nonneg (IF - IG)]
    exact h1.trans (sq_add_le_two_mul_sq_add_sq ‖IF‖ ‖IG‖)
  have h_norm_sq_le : ‖S‖ ^ 2 ≤ (2 * h)⁻¹ ^ 2 * (2 * ‖IF‖ ^ 2 + 2 * ‖IG‖ ^ 2) := by
    rw [h_norm_sq_S]
    exact mul_le_mul_of_nonneg_left h_diff_sq_le (sq_nonneg _)
  have h_split_sq : (2 * h)⁻¹ ^ 2 * (2 * ‖IF‖ ^ 2 + 2 * ‖IG‖ ^ 2) =
      (1 / (2 * h ^ 2)) * ‖IF‖ ^ 2 + (1 / (2 * h ^ 2)) * ‖IG‖ ^ 2 := by
    have : (2 * h)⁻¹ ^ 2 = 1 / (4 * h ^ 2) := by
      field_simp
      ring
    rw [this]
    ring
  rw [h_split_sq] at h_norm_sq_le
  -- Now bound ‖IF‖ ^ 2 and ‖IG‖ ^ 2:
  have h_norm_IF : ‖IF‖ ≤ ∫ w in h..(3 * h), ‖F w‖ :=
    intervalIntegral.norm_integral_le_integral_norm h_le_3h
  have h_norm_sq_IF : ‖IF‖ ^ 2 ≤ (∫ w in h..(3 * h), ‖F w‖) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg IF]) h_norm_IF
  have h_cs_IF := sq_integral_le_integral_sq h (3 * h) h_le_3h (fun w => ‖F w‖) hF_int.norm hF2_int
  have h3h_sub_h : 3 * h - h = 2 * h := by ring
  rw [h3h_sub_h] at h_cs_IF
  have h_bound_IF : ‖IF‖ ^ 2 ≤ (2 * h) * ∫ w in h..(3 * h), ‖F w‖ ^ 2 :=
    h_norm_sq_IF.trans h_cs_IF
  -- Same for IG:
  have h_norm_IG : ‖IG‖ ≤ ∫ w in h..(3 * h), ‖G w‖ :=
    intervalIntegral.norm_integral_le_integral_norm h_le_3h
  have h_norm_sq_IG : ‖IG‖ ^ 2 ≤ (∫ w in h..(3 * h), ‖G w‖) ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg IG]) h_norm_IG
  have h_cs_IG := sq_integral_le_integral_sq h (3 * h) h_le_3h (fun w => ‖G w‖) hG_int.norm hG2_int
  rw [h3h_sub_h] at h_cs_IG
  have h_bound_IG : ‖IG‖ ^ 2 ≤ (2 * h) * ∫ w in h..(3 * h), ‖G w‖ ^ 2 :=
    h_norm_sq_IG.trans h_cs_IG
  have h_coeff_pos : 0 ≤ 1 / (2 * h ^ 2) := by positivity
  have h_term1_le : (1 / (2 * h ^ 2)) * ‖IF‖ ^ 2 ≤ ((1 / h) * ∫ w in h..(3 * h), ‖F w‖ ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left h_bound_IF h_coeff_pos
    have halg : (1 / (2 * h ^ 2)) * ((2 * h) * ∫ w in h..(3 * h), ‖F w‖ ^ 2) =
        (1 / h) * ∫ w in h..(3 * h), ‖F w‖ ^ 2 := by
      field_simp
    rwa [halg] at h1
  have h_term2_le : (1 / (2 * h ^ 2)) * ‖IG‖ ^ 2 ≤ ((1 / h) * ∫ w in h..(3 * h), ‖G w‖ ^ 2) := by
    have h2 := mul_le_mul_of_nonneg_left h_bound_IG h_coeff_pos
    have halg : (1 / (2 * h ^ 2)) * ((2 * h) * ∫ w in h..(3 * h), ‖G w‖ ^ 2) =
        (1 / h) * ∫ w in h..(3 * h), ‖G w‖ ^ 2 := by
      field_simp
    rwa [halg] at h2
  have h_mid_le : ‖S‖ ^ 2 ≤ ((1 / h) * ∫ w in h..(3 * h), ‖F w‖ ^ 2) +
                             ((1 / h) * ∫ w in h..(3 * h), ‖G w‖ ^ 2) :=
    h_norm_sq_le.trans (add_le_add h_term1_le h_term2_le)
  dsimp [F, G] at h_mid_le
  rw [← integral_subst_first a x h hx] at h_mid_le
  rw [← integral_subst_second a x h hx hh] at h_mid_le
  set term2 := ((x + h) / h) * ∫ u in (0 : ℝ)..(2 * h / (x + h)), ‖windowSum a (x + h) ((x + h) * (1 + u))‖ ^ 2
  have h_term2_nonneg : 0 ≤ term2 := by
    dsimp [term2]
    refine mul_nonneg (by positivity) ?_
    refine intervalIntegral.integral_nonneg (by positivity) ?_
    intro u _
    exact sq_nonneg _
  have h_u_int : IntervalIntegrable (fun u => ‖windowSum a x (x * (1 + u))‖ ^ 2) volume (h / x) (3 * h / x) :=
    intervalIntegrable_norm_sq_windowSum_scaled a x h hx hh
  have h_add_int := intervalIntegral.integral_add h_u_int (intervalIntegrable_const (c := term2))
  have h_const_int : ∫ (u : ℝ) in h / x..3 * h / x, term2 = (2 * h / x) * term2 := by
    have := intervalIntegral.integral_const (a := h / x) (b := 3 * h / x) term2
    rw [this]
    simp only [smul_eq_mul]
    congr 1
    ring
  have h_expand : (x / h) * ∫ u in (h / x)..(3 * h / x), (‖windowSum a x (x * (1 + u))‖ ^ 2 + term2) =
      (x / h) * (∫ u in (h / x)..(3 * h / x), ‖windowSum a x (x * (1 + u))‖ ^ 2) + 2 * term2 := by
    rw [h_add_int, mul_add, h_const_int]
    congr 1
    calc
      (x / h) * ((2 * h / x) * term2) = ((x / h) * (2 * h / x)) * term2 := by rw [mul_assoc]
      _ = 2 * term2 := by
        congr 1
        field_simp
  have h_le_double : ((x / h) * ∫ u in (h / x)..(3 * h / x), ‖windowSum a x (x * (1 + u))‖ ^ 2) + term2 ≤
      ((x / h) * ∫ u in (h / x)..(3 * h / x), ‖windowSum a x (x * (1 + u))‖ ^ 2) + 2 * term2 := by
    linarith
  rw [← h_expand] at h_le_double
  exact h_mid_le.trans h_le_double

end Erdos1201.MR
