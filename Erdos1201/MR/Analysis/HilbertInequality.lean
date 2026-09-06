import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Erdos1201.Vendor.NumberTheory.BoundedPrimeGaps.BombieriVinogradov.Analytic.CosecantHilbert

open Filter Metric
open scoped Topology BigOperators

/-!
# Montgomery--Vaughan Generalized Hilbert Inequality on the Real Line

This file formalizes the real-line generalized Hilbert inequality from
Montgomery--Vaughan (1974), Theorem 1, eq. (1.1).

The inequality bounds the bilinear form
`∑ r, ∑ s ≠ r, u r * conj(u s) / (x r - x s)`
by `Real.pi * δ⁻¹ * ∑ r, ‖u r‖ ^ 2` for any finite family of real numbers `x r`
that are `δ`-separated (`|x r - x s| ≥ δ` for `r ≠ s`).

The proof proceeds by applying the Montgomery--Vaughan cosecant Hilbert inequality
(`BoundedGaps.Maynard.norm_cosecantBilinearForm_le`) to scaled points `ε * x r`.
For sufficiently small `ε > 0`, the points are `(ε * δ)`-separated on the circle
`UnitAddCircle`, where circle distance coincides with Euclidean distance.
Multiplying by `Real.pi * ε` and taking the limit as `ε → 0⁺` yields the real-line
Hilbert inequality via `le_of_tendsto`.

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

namespace Erdos1201.MR

/-- The standard limit `(sin t) / t → 1` as `t → 0` in punctured neighborhoods. -/
lemma tendsto_sin_div_zero : Tendsto (fun t : ℝ => Real.sin t / t) (𝓝[≠] 0) (𝓝 1) := by
  have h := Real.hasDerivAt_sin 0
  rw [Real.cos_zero] at h
  have h2 := h.tendsto_slope_zero
  simp only [sub_zero, Real.sin_zero, zero_add] at h2
  have h3 : (fun t : ℝ => t⁻¹ • Real.sin t) = (fun t : ℝ => Real.sin t / t) := by
    ext t
    simp [div_eq_inv_mul]
  rwa [h3] at h2

/-- As `ε → 0⁺`, `(π ε) / sin (π ε y) → y⁻¹` for any nonzero real `y`. -/
lemma tendsto_pi_mul_div_sin {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun ε : ℝ => (Real.pi * ε) * (Real.sin (Real.pi * (ε * y)))⁻¹) (𝓝[>] 0) (𝓝 y⁻¹) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpiy : Real.pi * y ≠ 0 := mul_ne_zero hpi hy
  have h_t : Tendsto (fun ε : ℝ => (Real.pi * y) * ε) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Continuous (fun ε : ℝ => (Real.pi * y) * ε) := continuous_id.const_mul _
      have ht := hcont.tendsto (0 : ℝ)
      simp only [mul_zero] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact mul_ne_zero hpiy hε.ne'
  have h_inv : Tendsto (fun t : ℝ => (Real.sin t / t)⁻¹) (𝓝[≠] 0) (𝓝 (1⁻¹ : ℝ)) :=
    tendsto_sin_div_zero.inv₀ one_ne_zero
  rw [inv_one] at h_inv
  have h_comp := h_inv.comp h_t
  have h_mul := Tendsto.const_mul y⁻¹ h_comp
  rw [mul_one] at h_mul
  refine h_mul.congr' ?_
  refine Filter.Eventually.of_forall fun ε => ?_
  dsimp
  rw [inv_div, div_eq_mul_inv]
  have h_eq : (Real.pi * y) * ε = Real.pi * (ε * y) := by ring
  rw [h_eq]
  calc
    y⁻¹ * (Real.pi * (ε * y) * (Real.sin (Real.pi * (ε * y)))⁻¹) =
        (y⁻¹ * y) * (Real.pi * ε * (Real.sin (Real.pi * (ε * y)))⁻¹) := by ring
    _ = 1 * (Real.pi * ε * (Real.sin (Real.pi * (ε * y)))⁻¹) := by rw [inv_mul_cancel₀ hy]
    _ = Real.pi * ε * (Real.sin (Real.pi * (ε * y)))⁻¹ := by rw [one_mul]

/-- Each term in the scaled cosecant bilinear form converges to the corresponding
term in the real Hilbert form. -/
lemma tendsto_term (c : ℂ) {y : ℝ} (hy : y ≠ 0) :
    Tendsto (fun ε : ℝ => c * (((Real.pi * ε * (Real.sin (Real.pi * (ε * y)))⁻¹ : ℝ) : ℂ)))
      (𝓝[>] 0) (𝓝 (c / ((y : ℝ) : ℂ))) := by
  have ht_real := tendsto_pi_mul_div_sin hy
  have ht_c : Tendsto (fun ε : ℝ => ((Real.pi * ε * (Real.sin (Real.pi * (ε * y)))⁻¹ : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((y⁻¹ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp ht_real
  have ht_mul := Tendsto.const_mul c ht_c
  have hdiv : c * ((y⁻¹ : ℝ) : ℂ) = c / ((y : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, div_eq_mul_inv]
  rwa [hdiv] at ht_mul

/-- The distance between two points in a finite family is bounded by the diameter of the range. -/
lemma abs_sub_le_range_diam {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) (r s : ι) :
    |x r - x s| ≤
      Finset.univ.sup' Finset.univ_nonempty x - Finset.univ.inf' Finset.univ_nonempty x := by
  have hr_le : x r ≤ Finset.univ.sup' Finset.univ_nonempty x :=
    Finset.le_sup' x (Finset.mem_univ r)
  have hs_ge : Finset.univ.inf' Finset.univ_nonempty x ≤ x s :=
    Finset.inf'_le x (Finset.mem_univ s)
  have hs_le : x s ≤ Finset.univ.sup' Finset.univ_nonempty x :=
    Finset.le_sup' x (Finset.mem_univ s)
  have hr_ge : Finset.univ.inf' Finset.univ_nonempty x ≤ x r :=
    Finset.inf'_le x (Finset.mem_univ r)
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- Circle distance on `UnitAddCircle` equals the Euclidean distance when the difference
is at most `1 / 2`. -/
lemma dist_coe_unitAddCircle {a b : ℝ} (h : |a - b| ≤ 1 / 2) :
    dist (a : UnitAddCircle) (b : UnitAddCircle) = |a - b| := by
  rw [dist_eq_norm]
  have hcoe : (a : UnitAddCircle) - (b : UnitAddCircle) = ((a - b : ℝ) : UnitAddCircle) := rfl
  rw [hcoe]
  have hiff := @AddCircle.norm_coe_eq_abs_iff (1 : ℝ) (a - b) (by norm_num)
  rw [hiff.mpr]
  simpa using h

/-- Scaled points `ε * x r` are `(ε * δ)`-separated on `UnitAddCircle` for small `ε > 0`. -/
lemma separated_scaled {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) {δ : ℝ} (_hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |x r - x s|)
    {ε : ℝ} (hε_pos : 0 < ε)
    (hε_lt : ε < (2 * (Finset.univ.sup' Finset.univ_nonempty x - Finset.univ.inf' Finset.univ_nonempty x + 1))⁻¹) :
    ∀ r s, r ≠ s → (ε * δ) ≤ dist ((ε * x r : ℝ) : UnitAddCircle) ((ε * x s : ℝ) : UnitAddCircle) := by
  intro r s hrs
  let D := Finset.univ.sup' Finset.univ_nonempty x - Finset.univ.inf' Finset.univ_nonempty x
  have hD : 0 ≤ D := by
    obtain ⟨i₀⟩ : Nonempty ι := inferInstance
    have := abs_sub_le_range_diam x i₀ i₀
    simp only [sub_self, abs_zero] at this
    exact this
  have hM_pos : 0 < D + 1 := by linarith
  have h_le_D : |x r - x s| ≤ D := abs_sub_le_range_diam x r s
  have h_scaled_le : |ε * x r - ε * x s| ≤ 1 / 2 := by
    rw [← mul_sub, abs_mul, abs_of_pos hε_pos]
    have h_prod : ε * |x r - x s| ≤ ε * D := mul_le_mul_of_nonneg_left h_le_D hε_pos.le
    have h_prod2 : ε * D < 1 / 2 := by
      calc
        ε * D ≤ ε * (D + 1) := mul_le_mul_of_nonneg_left (by linarith) hε_pos.le
        _ < (2 * (D + 1))⁻¹ * (D + 1) := mul_lt_mul_of_pos_right hε_lt hM_pos
        _ = 1 / 2 := by
          field_simp [ne_of_gt hM_pos]
    linarith
  rw [dist_coe_unitAddCircle h_scaled_le]
  rw [← mul_sub, abs_mul, abs_of_pos hε_pos]
  exact mul_le_mul_of_nonneg_left (hsep r s hrs) hε_pos.le

/-- The open interval `(0, c)` is a neighborhood of `0` in `𝓝[>] 0` for `c > 0`. -/
lemma mem_nhdsGT_Ioo {c : ℝ} (hc : 0 < c) : Set.Ioo 0 c ∈ 𝓝[>] (0 : ℝ) := by
  have h1 : Set.Iio c ∈ 𝓝 (0 : ℝ) := Iio_mem_nhds hc
  have h2 := inter_mem_nhdsWithin (Set.Ioi 0) h1
  rwa [Set.Ioi_inter_Iio] at h2

/-- Multiplying the cosecant bilinear form by `π * ε` scales each term. -/
lemma mul_cosecantBilinearForm_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (u : ι → ℂ) (ε : ℝ) :
    ((Real.pi * ε : ℝ) : ℂ) * BoundedGaps.Maynard.cosecantBilinearForm (fun r => ε * x r) u =
      ∑ r, ∑ s ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u s) *
          (((Real.pi * ε * (Real.sin (Real.pi * (ε * (x r - x s))))⁻¹ : ℝ) : ℂ)) := by
  dsimp [BoundedGaps.Maynard.cosecantBilinearForm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have h_arg : ε * x r - ε * x s = ε * (x r - x s) := by ring
  rw [h_arg]
  push_cast
  ring

/-- The factor `(π ε) * (ε δ)⁻¹` simplifies to `π * δ⁻¹`. -/
lemma scaled_bound_eq {δ ε : ℝ} (S : ℝ) (hε : 0 < ε) :
    (Real.pi * ε) * ((ε * δ)⁻¹ * S) = Real.pi * δ⁻¹ * S := by
  have hε_ne : ε ≠ 0 := hε.ne'
  rw [mul_inv]
  calc
    (Real.pi * ε) * (ε⁻¹ * δ⁻¹ * S) = (ε * ε⁻¹) * (Real.pi * δ⁻¹ * S) := by ring
    _ = 1 * (Real.pi * δ⁻¹ * S) := by rw [mul_inv_cancel₀ hε_ne]
    _ = Real.pi * δ⁻¹ * S := by ring

/-- The norm of `((π ε : ℝ) : ℂ)` is `π * ε` for `ε > 0`. -/
lemma norm_pi_mul_coe (ε : ℝ) (hε : 0 < ε) :
    ‖((Real.pi * ε : ℝ) : ℂ)‖ = Real.pi * ε := by
  rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg Real.pi_pos.le hε.le)]

/-- Generalized Hilbert inequality on the real line (Montgomery--Vaughan 1974, Theorem 1, eq. (1.1)).
For any finite collection of real numbers `x r` separated by at least `δ > 0`,
`‖∑ r, ∑ s ≠ r, u r * conj(u s) / (x r - x s)‖ ≤ π * δ⁻¹ * ∑ r, ‖u r‖²`. -/
theorem norm_hilbert_form_le {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ r s, r ≠ s → δ ≤ |x r - x s|) (u : ι → ℂ) :
    ‖∑ r, ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) / ((x r - x s : ℝ) : ℂ)‖ ≤
      Real.pi * δ⁻¹ * ∑ r, ‖u r‖ ^ 2 := by
  by_cases hι : Nonempty ι
  · have : Nonempty ι := hι
    let D := Finset.univ.sup' Finset.univ_nonempty x - Finset.univ.inf' Finset.univ_nonempty x
    have hD : 0 ≤ D := by
      obtain ⟨i₀⟩ : Nonempty ι := inferInstance
      have := abs_sub_le_range_diam x i₀ i₀
      simp only [sub_self, abs_zero] at this
      exact this
    have hc_pos : 0 < (2 * (D + 1))⁻¹ := by
      have : 0 < 2 * (D + 1) := by linarith
      exact inv_pos.mpr this
    have h_tend : Tendsto (fun ε : ℝ => ∑ r, ∑ s ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u s) *
          (((Real.pi * ε * (Real.sin (Real.pi * (ε * (x r - x s))))⁻¹ : ℝ) : ℂ)))
        (𝓝[>] 0)
        (𝓝 (∑ r, ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) / ((x r - x s : ℝ) : ℂ))) := by
      apply tendsto_finsetSum
      intro r hr
      apply tendsto_finsetSum
      intro s hs
      have hrs : r ≠ s := (Finset.ne_of_mem_erase hs).symm
      have hsep_rs : δ ≤ |x r - x s| := hsep r s hrs
      have hy : x r - x s ≠ 0 := by
        intro h
        rw [h, abs_zero] at hsep_rs
        linarith
      exact tendsto_term (u r * (starRingEnd ℂ) (u s)) hy
    have h_norm_tend := continuous_norm.continuousAt.tendsto.comp h_tend
    change Tendsto (fun ε : ℝ => ‖∑ r, ∑ s ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u s) *
          (((Real.pi * ε * (Real.sin (Real.pi * (ε * (x r - x s))))⁻¹ : ℝ) : ℂ))‖)
        (𝓝[>] 0)
        (𝓝 ‖∑ r, ∑ s ∈ Finset.univ.erase r, u r * (starRingEnd ℂ) (u s) / ((x r - x s : ℝ) : ℂ)‖) at h_norm_tend
    have h_congr : (fun ε : ℝ => ‖∑ r, ∑ s ∈ Finset.univ.erase r,
        u r * (starRingEnd ℂ) (u s) *
          (((Real.pi * ε * (Real.sin (Real.pi * (ε * (x r - x s))))⁻¹ : ℝ) : ℂ))‖) =
        (fun ε : ℝ => ‖((Real.pi * ε : ℝ) : ℂ) * BoundedGaps.Maynard.cosecantBilinearForm (fun r => ε * x r) u‖) := by
      ext ε
      rw [← mul_cosecantBilinearForm_eq]
    rw [h_congr] at h_norm_tend
    refine le_of_tendsto h_norm_tend ?_
    refine Filter.eventually_of_mem (mem_nhdsGT_Ioo hc_pos) fun ε hε => ?_
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < (2 * (D + 1))⁻¹ := hε.2
    have hsep_scaled := separated_scaled x hδ hsep hε_pos hε_lt
    have hεδ_pos : 0 < ε * δ := mul_pos hε_pos hδ
    have h_bound := BoundedGaps.Maynard.norm_cosecantBilinearForm_le (fun r => ε * x r) hεδ_pos hsep_scaled u
    calc
      ‖((Real.pi * ε : ℝ) : ℂ) * BoundedGaps.Maynard.cosecantBilinearForm (fun r => ε * x r) u‖ =
          ‖((Real.pi * ε : ℝ) : ℂ)‖ * ‖BoundedGaps.Maynard.cosecantBilinearForm (fun r => ε * x r) u‖ :=
        norm_mul _ _
      _ = (Real.pi * ε) * ‖BoundedGaps.Maynard.cosecantBilinearForm (fun r => ε * x r) u‖ := by
        rw [norm_pi_mul_coe ε hε_pos]
      _ ≤ (Real.pi * ε) * ((ε * δ)⁻¹ * ∑ r, ‖u r‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h_bound (mul_nonneg Real.pi_pos.le hε_pos.le)
      _ = Real.pi * δ⁻¹ * ∑ r, ‖u r‖ ^ 2 :=
        scaled_bound_eq (∑ r, ‖u r‖ ^ 2) hε_pos
  · have : IsEmpty ι := not_nonempty_iff.mp hι
    simp [Finset.univ_eq_empty]

end Erdos1201.MR
