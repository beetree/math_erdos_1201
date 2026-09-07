/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gemini

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Erdos1201.Vendor.NumberTheory.PNT.MediumPNT
import Erdos1201.MR.Twisted.TwistedChebyshev
import Erdos1201.MR.Twisted.TwistedContour

/-!
# Bounds for the Twisted Smoothed Chebyshev Function and Contours

This module establishes bounds on the contour integral pieces `J₁` through `J₉`
arising in the twisted contour decompositions `twistedChebyshevPull1` and
`twistedChebyshevPull2` from `Erdos1201.MR.Twisted.TwistedContour`.
-/

namespace Erdos1201.MR

open Complex Real MeasureTheory Set Filter Function

/-- Integrability of `t⁻²` on the lower tail `(-∞, -T]`. -/
lemma integrable_inv_sq_Iic {T : ℝ} (hT : 0 < T) :
    Integrable (fun (t : ℝ) => (t^2)⁻¹) (volume.restrict (Iic (-T))) := by
  have D3 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT |>.comp_neg
  simp only [rpow_neg_ofNat, Int.reduceNeg, zpow_neg, neg_Ioi] at D3
  have D4 := (integrableOn_Iic_iff_integrableOn_Iio' (by
    refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
    simp only [ne_eq, measure_singleton,
      EReal.coe_ennreal_zero, EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
  unfold IntegrableOn at D4
  have eq_fun : (fun (x : ℝ) => ((-x)^2)⁻¹) = fun x => (x^2)⁻¹ := by
    funext x; simp only [even_two, Even.neg_pow]
  exact eq_fun ▸ D4

/-- Integrability of `t⁻²` on the upper tail `[T, ∞)`. -/
lemma integrable_inv_sq_Ici {T : ℝ} (hT : 0 < T) :
    Integrable (fun (t : ℝ) => (t^2)⁻¹) (volume.restrict (Ici T)) := by
  have D3 := integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hT
  have D4 := (integrableOn_Ici_iff_integrableOn_Ioi' (by
    refine EReal.coe_ennreal_ne_coe_ennreal_iff.mp ?_
    simp only [ne_eq, measure_singleton,
      EReal.coe_ennreal_zero, EReal.coe_ennreal_top, EReal.zero_ne_top, not_false_eq_true])).mpr D3
  unfold IntegrableOn at D4
  have eq_fun : (fun (x : ℝ) => x ^ (-2 : ℝ)) = fun x => (x^2)⁻¹ := by
    funext x; simp [zpow_ofNat]
  exact eq_fun ▸ D4

/-- Norm squared of a shifted complex number `σ + (t - u) * I`. -/
lemma norm_sq_shift (σ t u : ℝ) :
    ‖(σ : ℂ) + t * I - u * I‖^2 = σ^2 + (t - u)^2 := by
  have : (σ : ℂ) + t * I - u * I = (σ : ℂ) + ((t - u : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, Complex.sq_norm, normSq_add_mul_I]

/-- Quadratic lower bound for `(t - u)^2` on `t ≤ -T` when `2 * |u| + 3 ≤ T`. -/
lemma sq_sub_ge_quarter_sq_of_le_neg {t u T : ℝ} (ht : t ≤ -T) (hT : 2 * |u| + 3 ≤ T) :
    t^2 / 4 ≤ (t - u)^2 := by
  have hu : |u| ≤ -t / 2 := by
    calc |u| ≤ T / 2 := by linarith [abs_nonneg u]
    _ ≤ -t / 2 := by linarith
  have h1 : -t / 2 ≤ -t + u := by
    have := neg_abs_le u
    linarith
  have h2 : 0 ≤ -t / 2 := by linarith [abs_nonneg u]
  have h3 : (-t / 2)^2 ≤ (-t + u)^2 := by nlinarith
  have h4 : (-t / 2)^2 = t^2 / 4 := by ring
  have h5 : (-t + u)^2 = (t - u)^2 := by ring
  linarith

/-- Quadratic lower bound for `(t - u)^2` on `t ≥ T` when `2 * |u| + 3 ≤ T`. -/
lemma sq_sub_ge_quarter_sq_of_ge {t u T : ℝ} (ht : T ≤ t) (hT : 2 * |u| + 3 ≤ T) :
    t^2 / 4 ≤ (t - u)^2 := by
  have hu : |u| ≤ t / 2 := by
    calc |u| ≤ T / 2 := by linarith [abs_nonneg u]
    _ ≤ t / 2 := by linarith
  have h1 : t / 2 ≤ t - u := by
    have := le_abs_self u
    linarith
  have h2 : 0 ≤ t / 2 := by linarith [abs_nonneg u]
  have h3 : (t / 2)^2 ≤ (t - u)^2 := by nlinarith
  have h4 : (t / 2)^2 = t^2 / 4 := by ring
  linarith

/-- Upper bound on the inverse norm squared by `4 * t⁻²` on the lower tail `t ≤ -T`. -/
lemma inv_norm_sq_shift_le_four_div_sq {σ t u T : ℝ} (ht : t ≤ -T) (hT : 2 * |u| + 3 ≤ T) :
    (‖(σ : ℂ) + t * I - u * I‖^2)⁻¹ ≤ 4 * (t^2)⁻¹ := by
  have ht_ne : t ≠ 0 := by
    have : T > 0 := by linarith [abs_nonneg u]
    linarith
  have h_sq : t^2 / 4 ≤ (t - u)^2 := sq_sub_ge_quarter_sq_of_le_neg ht hT
  have h_norm : ‖(σ : ℂ) + t * I - u * I‖^2 = σ^2 + (t - u)^2 := norm_sq_shift σ t u
  have h_denom : t^2 / 4 ≤ ‖(σ : ℂ) + t * I - u * I‖^2 := by
    rw [h_norm]
    have : 0 ≤ σ^2 := sq_nonneg σ
    linarith
  have h_pos : 0 < t^2 / 4 := by positivity
  have h_inv := (inv_le_inv₀ (by linarith) h_pos).mpr h_denom
  have h_inv4 : (t^2 / 4)⁻¹ = 4 * (t^2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
  rwa [h_inv4] at h_inv

/-- Upper bound on the inverse norm squared by `4 * t⁻²` on the upper tail `T ≤ t`. -/
lemma inv_norm_sq_shift_le_four_div_sq_of_ge {σ t u T : ℝ} (ht : T ≤ t) (hT : 2 * |u| + 3 ≤ T) :
    (‖(σ : ℂ) + t * I - u * I‖^2)⁻¹ ≤ 4 * (t^2)⁻¹ := by
  have ht_ne : t ≠ 0 := by
    have : T > 0 := by linarith [abs_nonneg u]
    linarith
  have h_sq : t^2 / 4 ≤ (t - u)^2 := sq_sub_ge_quarter_sq_of_ge ht hT
  have h_norm : ‖(σ : ℂ) + t * I - u * I‖^2 = σ^2 + (t - u)^2 := norm_sq_shift σ t u
  have h_denom : t^2 / 4 ≤ ‖(σ : ℂ) + t * I - u * I‖^2 := by
    rw [h_norm]
    have : 0 ≤ σ^2 := sq_nonneg σ
    linarith
  have h_pos : 0 < t^2 / 4 := by positivity
  have h_inv := (inv_le_inv₀ (by linarith) h_pos).mpr h_denom
  have h_inv4 : (t^2 / 4)⁻¹ = 4 * (t^2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
  rwa [h_inv4] at h_inv

/-- Evaluation of the integral of `t⁻²` on `(-∞, -T]`. -/
lemma integral_inv_sq_Iic_eq {T : ℝ} (hT : 0 < T) :
    ∫ (t : ℝ) in Iic (-T), (t^2)⁻¹ = T⁻¹ := by
  rw [← integral_comp_neg_Ioi]
  have : (fun x : ℝ => ((-x)^2)⁻¹) = (fun x : ℝ => x ^ (-2 : ℝ)) := by
    ext x; simp [zpow_ofNat]
  rw [this]
  rw [integral_Ioi_rpow_of_lt (by norm_num) hT]
  ring_nf
  rw [rpow_neg_one]

/-- Evaluation of the integral of `t⁻²` on `[T, ∞)`. -/
lemma integral_inv_sq_Ici_eq {T : ℝ} (hT : 0 < T) :
    ∫ (t : ℝ) in Ici T, (t^2)⁻¹ = T⁻¹ := by
  have : (fun x : ℝ => (x^2)⁻¹) = (fun x : ℝ => x ^ (-2 : ℝ)) := by
    ext x; simp [zpow_ofNat]
  rw [this, integral_Ici_eq_integral_Ioi]
  rw [integral_Ioi_rpow_of_lt (by norm_num) hT]
  ring_nf
  rw [rpow_neg_one]

/-- Norm of a shifted complex power `X ^ (s - u * I)` equals `X ^ s.re`. -/
lemma norm_cpow_shift {X : ℝ} (hX : 0 < X) (s : ℂ) (u : ℝ) :
    ‖(X : ℂ) ^ (s - u * Complex.I)‖ = X ^ s.re := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, re_sub_u_I]

/-- Complex cast identity for `1 + 1/log X`. -/
lemma pts_re_cast (X : ℝ) :
    ((1 + (Real.log X)⁻¹ : ℝ) : ℂ) = 1 + (↑(Real.log X))⁻¹ := by
  push_cast; ring

/-- Bound on the lower vertical tail contour integral `J₁`. -/
theorem J1Bound (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (_νnonneg : ∀ x > 0, 0 ≤ ν x)
    (_mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1)
      (u : ℝ) (T : ℝ) (_ : 3 < T) (_ : 2 * |u| + 3 ≤ T),
      ‖J₁ ν ε X T u‖ ≤ C * X * Real.log X / (ε * T) := by
  obtain ⟨M, M_pos, M_bounds⟩ := MellinOfSmooth1b diffν suppν
  have G0 : ∃ K > 0, ∀ (t σ : ℝ), 1 < σ → σ < 2 → ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ K * (σ - 1)⁻¹ := by
    obtain ⟨K', K'_pos, K'_bounds⟩ := triv_bound_zeta
    use 2 * (K' + 1), by positivity
    intro t σ cond cond2
    have T0 : 0 < K' + 1 := by positivity
    have T1 : 1 ≤ (σ - 1)⁻¹ := by
      have U : σ - 1 ≤ 1 := by linarith
      have U1 := (inv_le_inv₀ (by positivity) (by exact sub_pos.mpr cond)).mpr U
      simp_all only [one_div, inv_one]
    have U := calc
      ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ =
        ‖-deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ := by
          rw [← norm_neg, mul_comm, neg_div']
      _ ≤ (σ - 1)⁻¹ + K' := K'_bounds σ t cond
      _ ≤ (σ - 1)⁻¹ + (K' + 1) := by linarith
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) := by nlinarith
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) * (σ - 1)⁻¹ := by nlinarith
      _ = 2 * (K' + 1) * (σ - 1)⁻¹ := by ring
    exact U
  obtain ⟨K, K_pos, K_bounds⟩ := G0
  let C := |π|⁻¹ * 2⁻¹ * (4 * rexp 1 * K * M)
  have C_pos : 0 < C := by positivity
  refine ⟨C, C_pos, fun X X_gt ε ε_pos ε_lt_one u T T_gt hTu => ?_⟩
  let pts_re : ℝ := 1 + (Real.log X)⁻¹
  have log_pos : 0 < Real.log X := Real.log_pos (by linarith)
  have pts_re_gt : 1 < pts_re := by
    dsimp [pts_re]
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith
  have pts_re_pos : 0 < pts_re := by linarith
  have pts_re_lt : pts_re < 2 := by
    dsimp [pts_re]
    have : 1 < Real.log 3 := logt_gt_one (le_refl 3)
    have : (Real.log X)⁻¹ < 1 := by
      have : 1 < Real.log X := by
        calc 1 < Real.log 3 := by exact logt_gt_one (le_refl 3)
        _ < Real.log X := Real.log_lt_log (by norm_num) X_gt
      exact inv_lt_one_of_one_lt₀ this
    linarith
  have inve : (pts_re - 1)⁻¹ = Real.log X := by
    dsimp [pts_re]; ring_nf; rw [inv_inv]
  have K_bnd (t : ℝ) : ‖deriv riemannZeta (pts_re + t * I) / riemannZeta (pts_re + t * I)‖ ≤ K * Real.log X := by
    rw [← inve]
    exact K_bounds t pts_re pts_re_gt pts_re_lt
  have M_bnd (t : ℝ) : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((pts_re : ℂ) + t * I - u * I)‖ ≤
      M * (ε * ‖(pts_re : ℂ) + t * I - u * I‖^2)⁻¹ := by
    have hs1 : (pts_re : ℂ) + t * I - u * I = (pts_re : ℂ) + ((t - u : ℝ) : ℂ) * I := by push_cast; ring
    have h_re : ((pts_re : ℂ) + t * I - u * I).re = pts_re := by
      rw [hs1]; simp
    have h_re1 : pts_re ≤ ((pts_re : ℂ) + t * I - u * I).re := by rw [h_re]
    have h_re2 : ((pts_re : ℂ) + t * I - u * I).re ≤ 2 := by rw [h_re]; exact pts_re_lt.le
    exact M_bounds pts_re pts_re_pos ((pts_re : ℂ) + t * I - u * I) h_re1 h_re2 ε ε_pos ε_lt_one
  have X_bnd (t : ℝ) : ‖(X : ℂ) ^ ((pts_re : ℂ) + t * I - u * I)‖ = rexp 1 * X := by
    rw [norm_cpow_shift (by linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
    dsimp [pts_re]
    have : X ^ (1 + (Real.log X)⁻¹) = X * X ^ (Real.log X)⁻¹ :=
      rpow_one_add' (by linarith) (ne_of_gt pts_re_pos)
    rw [this, rpow_inv_log (by linarith) (ne_of_gt (by linarith))]
    ring
  have f_bnd (t : ℝ) (ht : t ≤ -T) :
      ‖twistedIntegrand ν ε X u (pts_re + t * I)‖ ≤
        (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹ := by
    unfold twistedIntegrand
    have h_zeta : ‖(-deriv riemannZeta (pts_re + t * I)) / riemannZeta (pts_re + t * I)‖ ≤ K * Real.log X := by
      rw [neg_div, norm_neg]
      exact K_bnd t
    have h_mellin_le : M * (ε * ‖(pts_re : ℂ) + t * I - u * I‖^2)⁻¹ ≤
        4 * M * ε⁻¹ * (t^2)⁻¹ := by
      have := inv_norm_sq_shift_le_four_div_sq ht hTu (σ := pts_re)
      have : (ε * ‖(pts_re : ℂ) + t * I - u * I‖^2)⁻¹ = ε⁻¹ * (‖(pts_re : ℂ) + t * I - u * I‖^2)⁻¹ := mul_inv _ _
      rw [this]
      have : 0 ≤ M * ε⁻¹ := by positivity
      nlinarith
    have h_mel : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((pts_re : ℂ) + t * I - u * I)‖ ≤ 4 * M * ε⁻¹ * (t^2)⁻¹ :=
      le_trans (M_bnd t) h_mellin_le
    have h_xcpow : ‖(X : ℂ) ^ ((pts_re : ℂ) + t * I - u * I)‖ ≤ rexp 1 * X := le_of_eq (X_bnd t)
    have h_step1 := norm_mul_le_of_le h_mel h_xcpow
    have h_step2 := norm_mul_le_of_le h_zeta h_step1
    calc ‖(-deriv riemannZeta (pts_re + t * I)) / riemannZeta (pts_re + t * I) *
            mellin (fun x => (Smooth1 ν ε x : ℂ)) ((pts_re : ℂ) + t * I - u * I) *
            (X : ℂ) ^ ((pts_re : ℂ) + t * I - u * I)‖ =
          ‖(-deriv riemannZeta (pts_re + t * I)) / riemannZeta (pts_re + t * I) *
            (mellin (fun x => (Smooth1 ν ε x : ℂ)) ((pts_re : ℂ) + t * I - u * I) *
            (X : ℂ) ^ ((pts_re : ℂ) + t * I - u * I))‖ := by ring_nf
      _ ≤ (K * Real.log X) * (4 * M * ε⁻¹ * (t^2)⁻¹ * (rexp 1 * X)) := h_step2
      _ = (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹ := by ring
  have int_bnd : ‖∫ t in Iic (-T), twistedIntegrand ν ε X u (pts_re + t * I)‖ ≤
      (4 * rexp 1 * K * M) * X * Real.log X / (ε * T) := by
    have h_mono : ‖∫ t in Iic (-T), twistedIntegrand ν ε X u (pts_re + t * I)‖ ≤
        ∫ t in Iic (-T), ‖twistedIntegrand ν ε X u (pts_re + t * I)‖ :=
      norm_integral_le_integral_norm _
    have h_nonneg : 0 ≤ᵐ[volume.restrict (Iic (-T))] (fun t => ‖twistedIntegrand ν ε X u (pts_re + t * I)‖) := by
      filter_upwards with t; exact norm_nonneg _
    have h_sq_int : Integrable (fun t : ℝ => (t^2)⁻¹) (volume.restrict (Iic (-T))) :=
      integrable_inv_sq_Iic (by linarith)
    have h_bound_int : Integrable (fun t : ℝ => (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹) (volume.restrict (Iic (-T))) :=
      h_sq_int.const_mul ((4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹)
    have h_le_ae : (fun t => ‖twistedIntegrand ν ε X u (pts_re + t * I)‖) ≤ᵐ[volume.restrict (Iic (-T))]
        (fun t => (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹) := by
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      exact f_bnd t ht
    have h_le : (∫ t in Iic (-T), ‖twistedIntegrand ν ε X u (pts_re + t * I)‖) ≤
        ∫ t in Iic (-T), (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹ :=
      integral_mono_of_nonneg h_nonneg h_bound_int h_le_ae
    have h_calc : (∫ t in Iic (-T), (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹) =
        (4 * rexp 1 * K * M) * X * Real.log X / (ε * T) := by
      rw [integral_const_mul, integral_inv_sq_Iic_eq (by linarith)]
      ring
    rw [h_calc] at h_le
    exact le_trans h_mono h_le
  unfold J₁
  rw [Complex.norm_mul (1 / (2 * π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  have h_pts : (pts_re : ℂ) = 1 + (↑(Real.log X))⁻¹ := pts_re_cast X
  rw [← h_pts]
  have Z4 := mul_le_mul_of_nonneg_left int_bnd Z2
  have h_eq : |π|⁻¹ * 2⁻¹ * ((4 * rexp 1 * K * M) * X * Real.log X / (ε * T)) =
      C * X * Real.log X / (ε * T) := by
    dsimp [C]; ring
  rw [h_eq] at Z4
  exact Z4

/-- Bound on the upper vertical tail contour integral `J₉`. -/
theorem J9Bound (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (_νnonneg : ∀ x > 0, 0 ≤ ν x)
    (_mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1)
      (u : ℝ) (T : ℝ) (_ : 3 < T) (_ : 2 * |u| + 3 ≤ T),
      ‖J₉ ν ε X T u‖ ≤ C * X * Real.log X / (ε * T) := by
  obtain ⟨M, M_pos, M_bounds⟩ := MellinOfSmooth1b diffν suppν
  have G0 : ∃ K > 0, ∀ (t σ : ℝ), 1 < σ → σ < 2 → ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ K * (σ - 1)⁻¹ := by
    obtain ⟨K', K'_pos, K'_bounds⟩ := triv_bound_zeta
    use 2 * (K' + 1), by positivity
    intro t σ cond cond2
    have T0 : 0 < K' + 1 := by positivity
    have T1 : 1 ≤ (σ - 1)⁻¹ := by
      have U : σ - 1 ≤ 1 := by linarith
      have U1 := (inv_le_inv₀ (by positivity) (by exact sub_pos.mpr cond)).mpr U
      simp_all only [one_div, inv_one]
    have U := calc
      ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ =
        ‖-deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ := by
          rw [← norm_neg, mul_comm, neg_div']
      _ ≤ (σ - 1)⁻¹ + K' := K'_bounds σ t cond
      _ ≤ (σ - 1)⁻¹ + (K' + 1) := by linarith
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) := by nlinarith
      _ ≤ (K' + 1) * (σ - 1)⁻¹ + (K' + 1) * (σ - 1)⁻¹ := by nlinarith
      _ = 2 * (K' + 1) * (σ - 1)⁻¹ := by ring
    exact U
  obtain ⟨K, K_pos, K_bounds⟩ := G0
  let C := |π|⁻¹ * 2⁻¹ * (4 * rexp 1 * K * M)
  have C_pos : 0 < C := by positivity
  refine ⟨C, C_pos, fun X X_gt ε ε_pos ε_lt_one u T T_gt hTu => ?_⟩
  let pts_re : ℝ := 1 + (Real.log X)⁻¹
  have log_pos : 0 < Real.log X := Real.log_pos (by linarith)
  have pts_re_gt : 1 < pts_re := by
    dsimp [pts_re]
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith
  have pts_re_pos : 0 < pts_re := by linarith
  have pts_re_lt : pts_re < 2 := by
    dsimp [pts_re]
    have : 1 < Real.log 3 := logt_gt_one (le_refl 3)
    have : (Real.log X)⁻¹ < 1 := by
      have : 1 < Real.log X := by
        calc 1 < Real.log 3 := by exact logt_gt_one (le_refl 3)
        _ < Real.log X := Real.log_lt_log (by norm_num) X_gt
      exact inv_lt_one_of_one_lt₀ this
    linarith
  have inve : (pts_re - 1)⁻¹ = Real.log X := by
    dsimp [pts_re]; ring_nf; rw [inv_inv]
  have K_bnd (t : ℝ) : ‖deriv riemannZeta (pts_re + t * I) / riemannZeta (pts_re + t * I)‖ ≤ K * Real.log X := by
    rw [← inve]
    exact K_bounds t pts_re pts_re_gt pts_re_lt
  have M_bnd (t : ℝ) : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((pts_re : ℂ) + t * I - u * I)‖ ≤
      M * (ε * ‖(pts_re : ℂ) + t * I - u * I‖^2)⁻¹ := by
    have hs1 : (pts_re : ℂ) + t * I - u * I = (pts_re : ℂ) + ((t - u : ℝ) : ℂ) * I := by push_cast; ring
    have h_re : ((pts_re : ℂ) + t * I - u * I).re = pts_re := by
      rw [hs1]; simp
    have h_re1 : pts_re ≤ ((pts_re : ℂ) + t * I - u * I).re := by rw [h_re]
    have h_re2 : ((pts_re : ℂ) + t * I - u * I).re ≤ 2 := by rw [h_re]; exact pts_re_lt.le
    exact M_bounds pts_re pts_re_pos ((pts_re : ℂ) + t * I - u * I) h_re1 h_re2 ε ε_pos ε_lt_one
  have X_bnd (t : ℝ) : ‖(X : ℂ) ^ ((pts_re : ℂ) + t * I - u * I)‖ = rexp 1 * X := by
    rw [norm_cpow_shift (by linarith)]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero]
    dsimp [pts_re]
    have : X ^ (1 + (Real.log X)⁻¹) = X * X ^ (Real.log X)⁻¹ :=
      rpow_one_add' (by linarith) (ne_of_gt pts_re_pos)
    rw [this, rpow_inv_log (by linarith) (ne_of_gt (by linarith))]
    ring
  have f_bnd (t : ℝ) (ht : T ≤ t) :
      ‖twistedIntegrand ν ε X u (pts_re + t * I)‖ ≤
        (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹ := by
    unfold twistedIntegrand
    have h_zeta : ‖(-deriv riemannZeta (pts_re + t * I)) / riemannZeta (pts_re + t * I)‖ ≤ K * Real.log X := by
      rw [neg_div, norm_neg]
      exact K_bnd t
    have h_mellin_le : M * (ε * ‖(pts_re : ℂ) + t * I - u * I‖^2)⁻¹ ≤
        4 * M * ε⁻¹ * (t^2)⁻¹ := by
      have := inv_norm_sq_shift_le_four_div_sq_of_ge ht hTu (σ := pts_re)
      have : (ε * ‖(pts_re : ℂ) + t * I - u * I‖^2)⁻¹ = ε⁻¹ * (‖(pts_re : ℂ) + t * I - u * I‖^2)⁻¹ := mul_inv _ _
      rw [this]
      have : 0 ≤ M * ε⁻¹ := by positivity
      nlinarith
    have h_mel : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((pts_re : ℂ) + t * I - u * I)‖ ≤ 4 * M * ε⁻¹ * (t^2)⁻¹ :=
      le_trans (M_bnd t) h_mellin_le
    have h_xcpow : ‖(X : ℂ) ^ ((pts_re : ℂ) + t * I - u * I)‖ ≤ rexp 1 * X := le_of_eq (X_bnd t)
    have h_step1 := norm_mul_le_of_le h_mel h_xcpow
    have h_step2 := norm_mul_le_of_le h_zeta h_step1
    calc ‖(-deriv riemannZeta (pts_re + t * I)) / riemannZeta (pts_re + t * I) *
            mellin (fun x => (Smooth1 ν ε x : ℂ)) ((pts_re : ℂ) + t * I - u * I) *
            (X : ℂ) ^ ((pts_re : ℂ) + t * I - u * I)‖ =
          ‖(-deriv riemannZeta (pts_re + t * I)) / riemannZeta (pts_re + t * I) *
            (mellin (fun x => (Smooth1 ν ε x : ℂ)) ((pts_re : ℂ) + t * I - u * I) *
            (X : ℂ) ^ ((pts_re : ℂ) + t * I - u * I))‖ := by ring_nf
      _ ≤ (K * Real.log X) * (4 * M * ε⁻¹ * (t^2)⁻¹ * (rexp 1 * X)) := h_step2
      _ = (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹ := by ring
  have int_bnd : ‖∫ t in Ici T, twistedIntegrand ν ε X u (pts_re + t * I)‖ ≤
      (4 * rexp 1 * K * M) * X * Real.log X / (ε * T) := by
    have h_mono : ‖∫ t in Ici T, twistedIntegrand ν ε X u (pts_re + t * I)‖ ≤
        ∫ t in Ici T, ‖twistedIntegrand ν ε X u (pts_re + t * I)‖ :=
      norm_integral_le_integral_norm _
    have h_nonneg : 0 ≤ᵐ[volume.restrict (Ici T)] (fun t => ‖twistedIntegrand ν ε X u (pts_re + t * I)‖) := by
      filter_upwards with t; exact norm_nonneg _
    have h_sq_int : Integrable (fun t : ℝ => (t^2)⁻¹) (volume.restrict (Ici T)) :=
      integrable_inv_sq_Ici (by linarith)
    have h_bound_int : Integrable (fun t : ℝ => (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹) (volume.restrict (Ici T)) :=
      h_sq_int.const_mul ((4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹)
    have h_le_ae : (fun t => ‖twistedIntegrand ν ε X u (pts_re + t * I)‖) ≤ᵐ[volume.restrict (Ici T)]
        (fun t => (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      exact f_bnd t ht
    have h_le : (∫ t in Ici T, ‖twistedIntegrand ν ε X u (pts_re + t * I)‖) ≤
        ∫ t in Ici T, (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹ :=
      integral_mono_of_nonneg h_nonneg h_bound_int h_le_ae
    have h_calc : (∫ t in Ici T, (4 * rexp 1 * K * M) * X * Real.log X * ε⁻¹ * (t^2)⁻¹) =
        (4 * rexp 1 * K * M) * X * Real.log X / (ε * T) := by
      rw [integral_const_mul, integral_inv_sq_Ici_eq (by linarith)]
      ring
    rw [h_calc] at h_le
    exact le_trans h_mono h_le
  unfold J₉
  rw [Complex.norm_mul (1 / (2 * π * I)) _]
  simp only [one_div, mul_inv_rev, inv_I, neg_mul, norm_neg, Complex.norm_mul, norm_I, norm_inv,
    norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul, ofReal_inv, ge_iff_le]
  have Z2 : 0 ≤ |π|⁻¹ * 2⁻¹ := by positivity
  have h_pts : (pts_re : ℂ) = 1 + (↑(Real.log X))⁻¹ := pts_re_cast X
  rw [← h_pts]
  have Z4 := mul_le_mul_of_nonneg_left int_bnd Z2
  have h_eq : |π|⁻¹ * 2⁻¹ * ((4 * rexp 1 * K * M) * X * Real.log X / (ε * T)) =
      C * X * Real.log X / (ε * T) := by
    dsimp [C]; ring
  rw [h_eq] at Z4
  exact Z4

/-- Algebraic decomposition of the contour difference into nine terms. -/
lemma contour_algebra_decomp (ν : ℝ → ℝ) (ε X T σ₁ σ₂ u : ℝ) (main : ℂ)
    (h_sum : twistedChebyshev ν ε X u = twistedSum ν ε X u)
    (h_pull1 : twistedChebyshev ν ε X u =
      J₁ ν ε X T u - J₂ ν ε T X σ₁ u + J₃₇ ν ε T X σ₁ u + J₈ ν ε T X σ₁ u + J₉ ν ε X T u + main)
    (h_pull2 : J₃₇ ν ε T X σ₁ u =
      J₃ ν ε T X σ₁ u - J₄ ν ε X σ₁ σ₂ u + J₅ ν ε X σ₂ u + J₆ ν ε X σ₁ σ₂ u + J₇ ν ε T X σ₁ u) :
    twistedSum ν ε X u - main =
      J₁ ν ε X T u - J₂ ν ε T X σ₁ u + J₃ ν ε T X σ₁ u - J₄ ν ε X σ₁ σ₂ u +
      J₅ ν ε X σ₂ u + J₆ ν ε X σ₁ σ₂ u + J₇ ν ε T X σ₁ u + J₈ ν ε T X σ₁ u + J₉ ν ε X T u := by
  rw [← h_sum, h_pull1, h_pull2]
  ring

/-- Triangle inequality splitting of the nine-term contour difference. -/
lemma norm_nine_decomp {S M J₁ J₂ J₃ J₄ J₅ J₆ J₇ J₈ J₉ : ℂ}
    (h : S - M = J₁ - J₂ + J₃ - J₄ + J₅ + J₆ + J₇ + J₈ + J₉) :
    ‖S - M‖ ≤ ‖J₁‖ + ‖J₂‖ + ‖J₃‖ + ‖J₄‖ + ‖J₅‖ + ‖J₆‖ + ‖J₇‖ + ‖J₈‖ + ‖J₉‖ := by
  rw [h]
  have h1 : ‖J₁ - J₂ + J₃ - J₄ + J₅ + J₆ + J₇ + J₈ + J₉‖ ≤
      ‖J₁ - J₂ + J₃ - J₄ + J₅ + J₆ + J₇ + J₈‖ + ‖J₉‖ := norm_add_le _ _
  have h2 : ‖J₁ - J₂ + J₃ - J₄ + J₅ + J₆ + J₇ + J₈‖ ≤
      ‖J₁ - J₂ + J₃ - J₄ + J₅ + J₆ + J₇‖ + ‖J₈‖ := norm_add_le _ _
  have h3 : ‖J₁ - J₂ + J₃ - J₄ + J₅ + J₆ + J₇‖ ≤
      ‖J₁ - J₂ + J₃ - J₄ + J₅ + J₆‖ + ‖J₇‖ := norm_add_le _ _
  have h4 : ‖J₁ - J₂ + J₃ - J₄ + J₅ + J₆‖ ≤
      ‖J₁ - J₂ + J₃ - J₄ + J₅‖ + ‖J₆‖ := norm_add_le _ _
  have h5 : ‖J₁ - J₂ + J₃ - J₄ + J₅‖ ≤
      ‖J₁ - J₂ + J₃ - J₄‖ + ‖J₅‖ := norm_add_le _ _
  have h6 : ‖J₁ - J₂ + J₃ - J₄‖ ≤
      ‖J₁ - J₂ + J₃‖ + ‖J₄‖ := by
    have : J₁ - J₂ + J₃ - J₄ = (J₁ - J₂ + J₃) + -J₄ := by ring
    rw [this]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_neg]
  have h7 : ‖J₁ - J₂ + J₃‖ ≤
      ‖J₁ - J₂‖ + ‖J₃‖ := norm_add_le _ _
  have h8 : ‖J₁ - J₂‖ ≤
      ‖J₁‖ + ‖J₂‖ := by
    have : J₁ - J₂ = J₁ + -J₂ := by ring
    rw [this]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_neg]
  linarith

/-- Linear combination bound combining the nine individual contour estimates. -/
lemma sum_nine_bounds_le {A B C C₁ C₂ C₃ C₄ C₅ C₆ C₇ C₈ C₉ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂) (_hC₃ : 0 ≤ C₃) (_hC₄ : 0 ≤ C₄)
    (_hC₅ : 0 ≤ C₅) (_hC₆ : 0 ≤ C₆) (_hC₇ : 0 ≤ C₇) (_hC₈ : 0 ≤ C₈) (_hC₉ : 0 ≤ C₉)
    {n1 n2 n3 n4 n5 n6 n7 n8 n9 : ℝ}
    (h1 : n1 ≤ C₁ * A) (h2 : n2 ≤ C₂ * A)
    (h3 : n3 ≤ C₃ * B) (h4 : n4 ≤ C₄ * B)
    (h5 : n5 ≤ C₅ * C)
    (h6 : n6 ≤ C₆ * B) (h7 : n7 ≤ C₇ * B)
    (h8 : n8 ≤ C₈ * A) (h9 : n9 ≤ C₉ * A) :
    n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 ≤
      (C₁ + C₂ + C₈ + C₉ + C₃ + C₄ + C₆ + C₇ + C₅) * (A + B + C) := by
  have : n1 + n2 + n3 + n4 + n5 + n6 + n7 + n8 + n9 ≤
      (C₁ + C₂ + C₈ + C₉) * A + (C₃ + C₄ + C₆ + C₇) * B + C₅ * C := by linarith
  refine le_trans this ?_
  have h_bound : (C₁ + C₂ + C₈ + C₉) * A + (C₃ + C₄ + C₆ + C₇) * B + C₅ * C ≤
      (C₁ + C₂ + C₈ + C₉ + C₃ + C₄ + C₆ + C₇ + C₅) * A +
      (C₁ + C₂ + C₈ + C₉ + C₃ + C₄ + C₆ + C₇ + C₅) * B +
      (C₁ + C₂ + C₈ + C₉ + C₃ + C₄ + C₆ + C₇ + C₅) * C := by
    have h1' : (C₁ + C₂ + C₈ + C₉) ≤ (C₁ + C₂ + C₈ + C₉ + C₃ + C₄ + C₆ + C₇ + C₅) := by linarith
    have h2' : (C₃ + C₄ + C₆ + C₇) ≤ (C₁ + C₂ + C₈ + C₉ + C₃ + C₄ + C₆ + C₇ + C₅) := by linarith
    have h3' : C₅ ≤ (C₁ + C₂ + C₈ + C₉ + C₃ + C₄ + C₆ + C₇ + C₅) := by linarith
    nlinarith
  refine le_trans h_bound ?_
  ring_nf; rfl

/-- Holomorphy of `ζ'/ζ` on `[σ₂, 2] × [-3, 3] \ {1}` from `LogDerivZetaHolcSmallT`. -/
lemma holo_zeta_of_smallT :
    ∃ (σ₂ : ℝ) (_ : 0 < σ₂) (_ : σ₂ < 1),
      DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
        (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1}) := by
  obtain ⟨σ₂', σ₂'_lt_one, holo2'⟩ := LogDerivZetaHolcSmallT
  let σ₂ : ℝ := max σ₂' (1 / 2)
  have σ₂_pos : 0 < σ₂ := by
    dsimp [σ₂]
    have : (0 : ℝ) < 1 / 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  have σ₂_lt_one : σ₂ < 1 := by
    dsimp [σ₂]
    rw [max_lt_iff]
    exact ⟨σ₂'_lt_one, by norm_num⟩
  refine ⟨σ₂, σ₂_pos, σ₂_lt_one, ?_⟩
  have h_mono : Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1} ⊆
      uIcc σ₂' 2 ×ℂ uIcc (-3) 3 \ {1} := by
    intro s hs
    simp only [Set.mem_sdiff, mem_reProdIm, mem_Icc, mem_singleton_iff] at hs ⊢
    refine ⟨⟨?_, ?_⟩, hs.2⟩
    · rw [uIcc_of_le (by linarith)]
      have : σ₂' ≤ σ₂ := le_max_left σ₂' (1 / 2)
      exact ⟨le_trans this hs.1.1.1, hs.1.1.2⟩
    · rw [uIcc_of_le (by norm_num)]
      exact hs.1.2
  exact holo2'.mono h_mono

/-- Holomorphy of the twisted integrand `twistedIntegrand` on `[σ₂, 2] × [-3, 3] \ {1}`. -/
lemma holoOn2_of_LogDerivZeta {ν : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε) (ε_lt_one : ε < 1)
    {X : ℝ} (X_gt : 3 < X) (u : ℝ) {σ₂ : ℝ} (hσ₂_pos : 0 < σ₂)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1) (diffν : ContDiff ℝ 1 ν)
    (h_holo_zeta : DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1})) :
    DifferentiableOn ℂ (twistedIntegrand ν ε X u) (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1}) := by
  unfold twistedIntegrand
  have h_zeta : DifferentiableOn ℂ (fun s => (-deriv riemannZeta s) / riemannZeta s)
      (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1}) := by
    have : (fun s => (-deriv riemannZeta s) / riemannZeta s) = -(fun s => deriv riemannZeta s / riemannZeta s) := by
      ext s; simp only [Pi.neg_apply, neg_div]
    rw [this]
    exact h_holo_zeta.neg
  have h_mel : DifferentiableOn ℂ (fun s => mellin (fun x => (Smooth1 ν ε x : ℂ)) (s - u * Complex.I))
      (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1}) := by
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply mellin_shift_diffAt ν ε_pos ε_lt_one suppν νnonneg mass_one diffν u
    have hs_re : s.re ∈ Set.Icc σ₂ 2 := (mem_reProdIm.mp hs.1).1
    linarith [hs_re.1]
  have h_cpow : DifferentiableOn ℂ (fun s => (X : ℂ) ^ (s - u * Complex.I))
      (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1}) := by
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    exact cpow_shift_diffAt X u X_gt s
  exact (h_zeta.mul h_mel).mul h_cpow

/-- Evaluation of `‖1 / (2 * π * I)‖ = |π|⁻¹ * 2⁻¹`. -/
lemma norm_one_div_two_pi_I : ‖(1 / (2 * π * I) : ℂ)‖ = |π|⁻¹ * 2⁻¹ := by
  have : (1 / (2 * π * I) : ℂ) = (2 * π * I)⁻¹ := one_div (2 * π * I)
  rw [this, norm_inv, norm_mul, norm_mul, norm_I, mul_one, norm_real, norm_eq_abs,
    Complex.norm_ofNat]
  ring

lemma re_sub_three_I (σ : ℝ) : ((σ : ℂ) - 3 * I).re = σ := by
  have : (σ : ℂ) - 3 * I = (σ : ℂ) + ((-3 : ℝ) : ℂ) * I := by push_cast; ring
  rw [this]; simp

lemma im_sub_three_I (σ : ℝ) : ((σ : ℂ) - 3 * I).im = -3 := by
  have : (σ : ℂ) - 3 * I = (σ : ℂ) + ((-3 : ℝ) : ℂ) * I := by push_cast; ring
  rw [this]; simp

lemma re_add_three_I (σ : ℝ) : ((σ : ℂ) + 3 * I).re = σ := by
  have : (σ : ℂ) + 3 * I = (σ : ℂ) + ((3 : ℝ) : ℂ) * I := by push_cast; ring
  rw [this]; simp

lemma im_add_three_I (σ : ℝ) : ((σ : ℂ) + 3 * I).im = 3 := by
  have : (σ : ℂ) + 3 * I = (σ : ℂ) + ((3 : ℝ) : ℂ) * I := by push_cast; ring
  rw [this]; simp

lemma re_add_t_I (σ t : ℝ) : ((σ : ℂ) + t * I).re = σ := by
  have : (σ : ℂ) + t * I = (σ : ℂ) + (t : ℂ) * I := by ring
  rw [this]; simp

lemma im_add_t_I (σ t : ℝ) : ((σ : ℂ) + t * I).im = t := by
  have : (σ : ℂ) + t * I = (σ : ℂ) + (t : ℂ) * I := by ring
  rw [this]; simp

lemma re_sub_T_I (σ T : ℝ) : ((σ : ℂ) - T * I).re = σ := by
  have : (σ : ℂ) - T * I = (σ : ℂ) + ((-T : ℝ) : ℂ) * I := by push_cast; ring
  rw [this]; simp

lemma re_add_T_I (σ T : ℝ) : ((σ : ℂ) + T * I).re = σ := by
  have : (σ : ℂ) + T * I = (σ : ℂ) + (T : ℂ) * I := by ring
  rw [this]; simp

/-- Bound on the lower horizontal cross-segment contour integral `J₂`. -/
theorem J2Bound (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    (θ φ : ℝ → ℝ) (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ φ |t|) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1)
      (u : ℝ) (T : ℝ) (_ : 3 < T) (_ : 2 * |u| + 3 ≤ T) (_ : φ T ≤ T),
      ‖J₂ ν ε T X (1 - θ T) u‖ ≤ C * X * Real.log X / (ε * T) := by
  obtain ⟨M, M_pos, M_bounds⟩ := MellinOfSmooth1b diffν suppν
  let C := |π|⁻¹ * 2⁻¹ * (8 * rexp 1 * M)
  have C_pos : 0 < C := by positivity
  refine ⟨C, C_pos, fun X X_gt ε ε_pos ε_lt_one u T T_gt hTu hphi => ?_⟩
  let σ₁ := 1 - θ T
  let pts_re : ℝ := 1 + (Real.log X)⁻¹
  have hT_le : 3 ≤ T := T_gt.le
  have hθT := hθ T hT_le
  have σ₁_pos : 0 < σ₁ := by
    dsimp [σ₁]; linarith [hθT.2]
  have σ₁_ge_half : 1 / 2 ≤ σ₁ := by
    dsimp [σ₁]; linarith [hθT.2]
  have log_pos : 0 < Real.log X := Real.log_pos (by linarith)
  have pts_re_gt : 1 < pts_re := by
    dsimp [pts_re]
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith
  have pts_re_lt : pts_re ≤ 2 := by
    dsimp [pts_re]
    have : 1 < Real.log 3 := logt_gt_one (le_refl 3)
    have : (Real.log X)⁻¹ < 1 := by
      have : 1 < Real.log X := by
        calc 1 < Real.log 3 := logt_gt_one (le_refl 3)
        _ < Real.log X := Real.log_lt_log (by norm_num) X_gt
      exact inv_lt_one_of_one_lt₀ this
    linarith
  have σ₁_le_pts : σ₁ ≤ pts_re := by
    dsimp [σ₁, pts_re]
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith [hθT.1]
  have f_bnd (σ : ℝ) (hσ : σ ∈ uIoc σ₁ pts_re) :
      ‖twistedIntegrand ν ε X u (σ - T * I)‖ ≤ (4 * rexp 1 * M) * X * Real.log X / (ε * T) := by
    rw [uIoc_of_le σ₁_le_pts, mem_Ioc] at hσ
    have hσ_ge_half : 1 / 2 ≤ σ := le_trans σ₁_ge_half hσ.1.le
    have hσ_le_two : σ ≤ 2 := le_trans hσ.2 pts_re_lt
    have h_zeta : ‖(-deriv riemannZeta (σ - T * I)) / riemannZeta (σ - T * I)‖ ≤ φ T := by
      rw [neg_div, norm_neg]
      have : (σ : ℂ) - T * I = (σ : ℂ) + (-T : ℝ) * I := by push_cast; ring
      rw [this]
      have h_abs : |-T| = T := by rw [abs_neg, abs_of_pos (by linarith)]
      have h1 : 3 ≤ |-T| := by rw [h_abs]; exact hT_le
      have h2 : 1 - θ |-T| ≤ σ := by rw [h_abs]; exact le_trans (le_refl _) hσ.1.le
      have h_bnd := hζ σ (-T) h1 h2 hσ_le_two
      rwa [h_abs] at h_bnd
    have h_mel_le : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ : ℂ) - T * I - u * I)‖ ≤
        4 * M / (ε * T^2) := by
      have hs : ((σ : ℂ) - T * I - u * I).re = σ := by
        have : (σ : ℂ) - T * I - u * I = (σ : ℂ) + ((-T - u : ℝ) : ℂ) * I := by push_cast; ring
        rw [this]; simp
      have h_half_pos : (0 : ℝ) < 1 / 2 := by norm_num
      have h_mel := M_bounds (1 / 2) h_half_pos ((σ : ℂ) - T * I - u * I)
        (by rw [hs]; exact hσ_ge_half) (by rw [hs]; exact hσ_le_two) ε ε_pos ε_lt_one
      have h_norm_sq : T^2 / 4 ≤ ‖(σ : ℂ) - T * I - u * I‖^2 := by
        have : (σ : ℂ) - T * I - u * I = (σ : ℂ) + (-T : ℝ) * I - u * I := by push_cast; ring
        rw [this, norm_sq_shift]
        have h_t : -T ≤ -T := le_refl _
        have h_sq := sq_sub_ge_quarter_sq_of_le_neg h_t hTu
        have : (-T)^2 / 4 = T^2 / 4 := by ring
        rw [this] at h_sq
        have : 0 ≤ σ^2 := sq_nonneg σ
        linarith
      have h_inv : (‖(σ : ℂ) - T * I - u * I‖^2)⁻¹ ≤ 4 * (T^2)⁻¹ := by
        have hT_pos : 0 < T^2 / 4 := by positivity
        have h := (inv_le_inv₀ (by linarith) hT_pos).mpr h_norm_sq
        have : (T^2 / 4)⁻¹ = 4 * (T^2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
        rwa [this] at h
      have h_calc : M * (ε * ‖(σ : ℂ) - T * I - u * I‖^2)⁻¹ ≤ 4 * M / (ε * T^2) := by
        have : (ε * ‖(σ : ℂ) - T * I - u * I‖^2)⁻¹ = ε⁻¹ * (‖(σ : ℂ) - T * I - u * I‖^2)⁻¹ := mul_inv _ _
        rw [this]
        have : 4 * M / (ε * T^2) = (M * ε⁻¹) * (4 * (T^2)⁻¹) := by ring
        rw [this]
        have : 0 ≤ M * ε⁻¹ := by positivity
        nlinarith
      exact le_trans h_mel h_calc
    have h_xcpow : ‖(X : ℂ) ^ ((σ : ℂ) - T * I - u * I)‖ ≤ rexp 1 * X := by
      rw [norm_cpow_shift (by linarith)]
      rw [re_sub_T_I σ T]
      have h_mono : X ^ σ ≤ X ^ pts_re := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.2
      have h_pts_eq : X ^ pts_re = rexp 1 * X := by
        dsimp [pts_re]
        have : X ^ (1 + (Real.log X)⁻¹) = X * X ^ (Real.log X)⁻¹ :=
          rpow_one_add' (by linarith) (ne_of_gt (by linarith))
        rw [this, rpow_inv_log (by linarith) (ne_of_gt (by linarith))]
        ring
      rw [h_pts_eq] at h_mono
      exact h_mono
    have h_int_eq : ‖twistedIntegrand ν ε X u (σ - T * I)‖ =
        ‖(-deriv riemannZeta (σ - T * I)) / riemannZeta (σ - T * I)‖ *
        ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ : ℂ) - T * I - u * I)‖ *
        ‖(X : ℂ) ^ ((σ : ℂ) - T * I - u * I)‖ := by
      dsimp [twistedIntegrand]
      rw [norm_mul, norm_mul]
    rw [h_int_eq]
    have h_zeta_nonneg : 0 ≤ φ T := le_trans (norm_nonneg _) h_zeta
    have h_mel_nonneg : 0 ≤ 4 * M / (ε * T^2) := by positivity
    have h12 := mul_le_mul h_zeta h_mel_le (norm_nonneg _) h_zeta_nonneg
    have h12_nonneg : 0 ≤ φ T * (4 * M / (ε * T^2)) := mul_nonneg h_zeta_nonneg h_mel_nonneg
    have h123 := mul_le_mul h12 h_xcpow (norm_nonneg _) h12_nonneg
    refine le_trans h123 ?_
    have h_step1 : φ T * (4 * M / (ε * T^2)) * (rexp 1 * X) = 4 * rexp 1 * M * X * (φ T / T) / (ε * T) := by
      ring
    rw [h_step1]
    have h_phi_div : φ T / T ≤ 1 := by
      rw [div_le_one₀ (by linarith)]
      exact hphi
    have h_one_le_log : 1 ≤ Real.log X := by
      have : 1 < Real.log 3 := logt_gt_one (le_refl 3)
      have : Real.log 3 < Real.log X := Real.log_lt_log (by norm_num) X_gt
      linarith
    have h_phi_le_log : φ T / T ≤ Real.log X := le_trans h_phi_div h_one_le_log
    have h_mult : 4 * rexp 1 * M * X * (φ T / T) ≤ 4 * rexp 1 * M * X * Real.log X := by
      have : 0 ≤ 4 * rexp 1 * M * X := by positivity
      nlinarith
    exact div_le_div_of_nonneg_right h_mult (by positivity)
  have int_bnd : ‖∫ σ in σ₁..pts_re, twistedIntegrand ν ε X u (σ - T * I)‖ ≤
      (8 * rexp 1 * M) * X * Real.log X / (ε * T) := by
    have h_norm_int := intervalIntegral.norm_integral_le_of_norm_le_const f_bnd
    refine le_trans h_norm_int ?_
    have h_len : |pts_re - σ₁| ≤ 2 := by
      rw [abs_of_nonneg (by linarith)]
      dsimp [pts_re, σ₁]
      have : (Real.log X)⁻¹ < 1 := by
        have : 1 < Real.log X := by
          calc 1 < Real.log 3 := logt_gt_one (le_refl 3)
          _ < Real.log X := Real.log_lt_log (by norm_num) X_gt
        exact inv_lt_one_of_one_lt₀ this
      linarith [hθT.1]
    have : ((4 * rexp 1 * M) * X * Real.log X / (ε * T)) * |pts_re - σ₁| ≤
        ((4 * rexp 1 * M) * X * Real.log X / (ε * T)) * 2 := by
      have : 0 ≤ (4 * rexp 1 * M) * X * Real.log X / (ε * T) := by positivity
      nlinarith
    refine le_trans this ?_
    ring_nf; rfl
  unfold J₂
  rw [norm_mul, norm_one_div_two_pi_I]
  have Z4 := mul_le_mul_of_nonneg_left int_bnd (by positivity : 0 ≤ |π|⁻¹ * 2⁻¹)
  have h_eq : |π|⁻¹ * 2⁻¹ * ((8 * rexp 1 * M) * X * Real.log X / (ε * T)) =
      C * X * Real.log X / (ε * T) := by
    dsimp [C]; ring
  rw [h_eq] at Z4
  exact Z4

/-- Bound on the upper horizontal cross-segment contour integral `J₈`. -/
theorem J8Bound (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    (θ φ : ℝ → ℝ) (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ φ |t|) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1)
      (u : ℝ) (T : ℝ) (_ : 3 < T) (_ : 2 * |u| + 3 ≤ T) (_ : φ T ≤ T),
      ‖J₈ ν ε T X (1 - θ T) u‖ ≤ C * X * Real.log X / (ε * T) := by
  obtain ⟨M, M_pos, M_bounds⟩ := MellinOfSmooth1b diffν suppν
  let C := |π|⁻¹ * 2⁻¹ * (8 * rexp 1 * M)
  have C_pos : 0 < C := by positivity
  refine ⟨C, C_pos, fun X X_gt ε ε_pos ε_lt_one u T T_gt hTu hphi => ?_⟩
  let σ₁ := 1 - θ T
  let pts_re : ℝ := 1 + (Real.log X)⁻¹
  have hT_le : 3 ≤ T := T_gt.le
  have hθT := hθ T hT_le
  have σ₁_pos : 0 < σ₁ := by
    dsimp [σ₁]; linarith [hθT.2]
  have σ₁_ge_half : 1 / 2 ≤ σ₁ := by
    dsimp [σ₁]; linarith [hθT.2]
  have log_pos : 0 < Real.log X := Real.log_pos (by linarith)
  have pts_re_gt : 1 < pts_re := by
    dsimp [pts_re]
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith
  have pts_re_lt : pts_re ≤ 2 := by
    dsimp [pts_re]
    have : 1 < Real.log 3 := logt_gt_one (le_refl 3)
    have : (Real.log X)⁻¹ < 1 := by
      have : 1 < Real.log X := by
        calc 1 < Real.log 3 := logt_gt_one (le_refl 3)
        _ < Real.log X := Real.log_lt_log (by norm_num) X_gt
      exact inv_lt_one_of_one_lt₀ this
    linarith
  have σ₁_le_pts : σ₁ ≤ pts_re := by
    dsimp [σ₁, pts_re]
    have : 0 < (Real.log X)⁻¹ := by positivity
    linarith [hθT.1]
  have f_bnd (σ : ℝ) (hσ : σ ∈ uIoc σ₁ pts_re) :
      ‖twistedIntegrand ν ε X u (σ + T * I)‖ ≤ (4 * rexp 1 * M) * X * Real.log X / (ε * T) := by
    rw [uIoc_of_le σ₁_le_pts, mem_Ioc] at hσ
    have hσ_ge_half : 1 / 2 ≤ σ := le_trans σ₁_ge_half hσ.1.le
    have hσ_le_two : σ ≤ 2 := le_trans hσ.2 pts_re_lt
    have h_zeta : ‖(-deriv riemannZeta (σ + T * I)) / riemannZeta (σ + T * I)‖ ≤ φ T := by
      rw [neg_div, norm_neg]
      have h_abs : |T| = T := abs_of_pos (by linarith)
      have h1 : 3 ≤ |T| := by rw [h_abs]; exact hT_le
      have h2 : 1 - θ |T| ≤ σ := by rw [h_abs]; exact le_trans (le_refl _) hσ.1.le
      have h_bnd := hζ σ T h1 h2 hσ_le_two
      rwa [h_abs] at h_bnd
    have h_mel_le : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + T * I - u * I)‖ ≤
        4 * M / (ε * T^2) := by
      have hs : ((σ : ℂ) + T * I - u * I).re = σ := by
        have : (σ : ℂ) + T * I - u * I = (σ : ℂ) + ((T - u : ℝ) : ℂ) * I := by push_cast; ring
        rw [this]; simp
      have h_half_pos : (0 : ℝ) < 1 / 2 := by norm_num
      have h_mel := M_bounds (1 / 2) h_half_pos ((σ : ℂ) + T * I - u * I)
        (by rw [hs]; exact hσ_ge_half) (by rw [hs]; exact hσ_le_two) ε ε_pos ε_lt_one
      have h_norm_sq : T^2 / 4 ≤ ‖(σ : ℂ) + T * I - u * I‖^2 := by
        have : (σ : ℂ) + T * I - u * I = (σ : ℂ) + (T : ℝ) * I - u * I := by ring
        rw [this, norm_sq_shift]
        have h_t : T ≤ T := le_refl _
        have h_sq := sq_sub_ge_quarter_sq_of_ge h_t hTu
        have : 0 ≤ σ^2 := sq_nonneg σ
        linarith
      have h_inv : (‖(σ : ℂ) + T * I - u * I‖^2)⁻¹ ≤ 4 * (T^2)⁻¹ := by
        have hT_pos : 0 < T^2 / 4 := by positivity
        have h := (inv_le_inv₀ (by linarith) hT_pos).mpr h_norm_sq
        have : (T^2 / 4)⁻¹ = 4 * (T^2)⁻¹ := by rw [inv_div, div_eq_mul_inv]
        rwa [this] at h
      have h_calc : M * (ε * ‖(σ : ℂ) + T * I - u * I‖^2)⁻¹ ≤ 4 * M / (ε * T^2) := by
        have : (ε * ‖(σ : ℂ) + T * I - u * I‖^2)⁻¹ = ε⁻¹ * (‖(σ : ℂ) + T * I - u * I‖^2)⁻¹ := mul_inv _ _
        rw [this]
        have : 4 * M / (ε * T^2) = (M * ε⁻¹) * (4 * (T^2)⁻¹) := by ring
        rw [this]
        have : 0 ≤ M * ε⁻¹ := by positivity
        nlinarith
      exact le_trans h_mel h_calc
    have h_xcpow : ‖(X : ℂ) ^ ((σ : ℂ) + T * I - u * I)‖ ≤ rexp 1 * X := by
      rw [norm_cpow_shift (by linarith)]
      rw [re_add_T_I σ T]
      have h_mono : X ^ σ ≤ X ^ pts_re := Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.2
      have h_pts_eq : X ^ pts_re = rexp 1 * X := by
        dsimp [pts_re]
        have : X ^ (1 + (Real.log X)⁻¹) = X * X ^ (Real.log X)⁻¹ :=
          rpow_one_add' (by linarith) (ne_of_gt (by linarith))
        rw [this, rpow_inv_log (by linarith) (ne_of_gt (by linarith))]
        ring
      rw [h_pts_eq] at h_mono
      exact h_mono
    have h_int_eq : ‖twistedIntegrand ν ε X u (σ + T * I)‖ =
        ‖(-deriv riemannZeta (σ + T * I)) / riemannZeta (σ + T * I)‖ *
        ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + T * I - u * I)‖ *
        ‖(X : ℂ) ^ ((σ : ℂ) + T * I - u * I)‖ := by
      dsimp [twistedIntegrand]
      rw [norm_mul, norm_mul]
    rw [h_int_eq]
    have h_zeta_nonneg : 0 ≤ φ T := le_trans (norm_nonneg _) h_zeta
    have h_mel_nonneg : 0 ≤ 4 * M / (ε * T^2) := by positivity
    have h12 := mul_le_mul h_zeta h_mel_le (norm_nonneg _) h_zeta_nonneg
    have h12_nonneg : 0 ≤ φ T * (4 * M / (ε * T^2)) := mul_nonneg h_zeta_nonneg h_mel_nonneg
    have h123 := mul_le_mul h12 h_xcpow (norm_nonneg _) h12_nonneg
    refine le_trans h123 ?_
    have h_step1 : φ T * (4 * M / (ε * T^2)) * (rexp 1 * X) = 4 * rexp 1 * M * X * (φ T / T) / (ε * T) := by
      ring
    rw [h_step1]
    have h_phi_div : φ T / T ≤ 1 := by
      rw [div_le_one₀ (by linarith)]
      exact hphi
    have h_one_le_log : 1 ≤ Real.log X := by
      have : 1 < Real.log 3 := logt_gt_one (le_refl 3)
      have : Real.log 3 < Real.log X := Real.log_lt_log (by norm_num) X_gt
      linarith
    have h_phi_le_log : φ T / T ≤ Real.log X := le_trans h_phi_div h_one_le_log
    have h_mult : 4 * rexp 1 * M * X * (φ T / T) ≤ 4 * rexp 1 * M * X * Real.log X := by
      have : 0 ≤ 4 * rexp 1 * M * X := by positivity
      nlinarith
    exact div_le_div_of_nonneg_right h_mult (by positivity)
  have int_bnd : ‖∫ σ in σ₁..pts_re, twistedIntegrand ν ε X u (σ + T * I)‖ ≤
      (8 * rexp 1 * M) * X * Real.log X / (ε * T) := by
    have h_norm_int := intervalIntegral.norm_integral_le_of_norm_le_const f_bnd
    refine le_trans h_norm_int ?_
    have h_len : |pts_re - σ₁| ≤ 2 := by
      rw [abs_of_nonneg (by linarith)]
      dsimp [pts_re, σ₁]
      have : (Real.log X)⁻¹ < 1 := by
        have : 1 < Real.log X := by
          calc 1 < Real.log 3 := logt_gt_one (le_refl 3)
          _ < Real.log X := Real.log_lt_log (by norm_num) X_gt
        exact inv_lt_one_of_one_lt₀ this
      linarith [hθT.1]
    have : ((4 * rexp 1 * M) * X * Real.log X / (ε * T)) * |pts_re - σ₁| ≤
        ((4 * rexp 1 * M) * X * Real.log X / (ε * T)) * 2 := by
      have : 0 ≤ (4 * rexp 1 * M) * X * Real.log X / (ε * T) := by positivity
      nlinarith
    refine le_trans this ?_
    ring_nf; rfl
  unfold J₈
  rw [norm_mul, norm_one_div_two_pi_I]
  have Z4 := mul_le_mul_of_nonneg_left int_bnd (by positivity : 0 ≤ |π|⁻¹ * 2⁻¹)
  have h_eq : |π|⁻¹ * 2⁻¹ * ((8 * rexp 1 * M) * X * Real.log X / (ε * T)) =
      C * X * Real.log X / (ε * T) := by
    dsimp [C]; ring
  rw [h_eq] at Z4
  exact Z4

lemma hasDerivAt_arctan_scaled (u : ℝ) (x : ℝ) :
    HasDerivAt (fun t => 2 * arctan (2 * (t - u))) (4 / (1 + 4 * (x - u)^2)) x := by
  have h1 : HasDerivAt (fun t => 2 * (t - u)) 2 x := by
    have : (fun t => 2 * (t - u)) = fun t => 2 * t - 2 * u := by ext t; ring
    rw [this]
    have h : HasDerivAt (fun t => 2 * t) 2 x := by
      simpa using (hasDerivAt_id' x).const_mul 2
    exact h.sub_const (2 * u)
  have h2 := (hasDerivAt_arctan (2 * (x - u))).comp x h1
  have h3 : HasDerivAt (fun t => 2 * arctan (2 * (t - u))) (2 * (1 / (1 + (2 * (x - u)) ^ 2) * 2)) x :=
    h2.const_mul 2
  have heq : 2 * (1 / (1 + (2 * (x - u)) ^ 2) * 2) = 4 / (1 + 4 * (x - u)^2) := by
    have : (2 * (x - u))^2 = 4 * (x - u)^2 := by ring
    rw [this]
    ring
  rwa [heq] at h3

lemma integral_arctan_scaled_eq (u a b : ℝ) :
    ∫ t in a..b, (4 / (1 + 4 * (t - u)^2)) = 2 * arctan (2 * (b - u)) - 2 * arctan (2 * (a - u)) := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun t => 2 * arctan (2 * (t - u))) (4 / (1 + 4 * (x - u)^2)) x :=
    fun x _ => hasDerivAt_arctan_scaled u x
  have hcont : Continuous (fun x => 4 / (1 + 4 * (x - u)^2)) := by
    apply continuous_const.div
    · apply continuous_const.add
      apply continuous_const.mul
      exact (continuous_id'.sub continuous_const).pow 2
    · intro x
      have : 0 ≤ 4 * (x - u)^2 := by positivity
      linarith
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable a b)

lemma integral_arctan_scaled_le (u a b : ℝ) :
    ∫ t in a..b, (4 / (1 + 4 * (t - u)^2)) ≤ 2 * π := by
  rw [integral_arctan_scaled_eq]
  have h1 : arctan (2 * (b - u)) < π / 2 := arctan_lt_pi_div_two _
  have h2 : -(π / 2) < arctan (2 * (a - u)) := neg_pi_div_two_lt_arctan _
  linarith

lemma integral_norm_le_example (u a b C : ℝ) (hab : a ≤ b) (hC : 0 ≤ C)
    (f : ℝ → ℂ) (hf : ∀ t ∈ Ioc a b, ‖f t‖ ≤ C * (4 / (1 + 4 * (t - u)^2))) :
    ‖∫ t in a..b, f t‖ ≤ C * (2 * π) := by
  have hcont : Continuous (fun x => C * (4 / (1 + 4 * (x - u)^2))) := by
    apply continuous_const.mul
    apply continuous_const.div
    · apply continuous_const.add
      apply continuous_const.mul
      exact (continuous_id'.sub continuous_const).pow 2
    · intro x
      have : 0 ≤ 4 * (x - u)^2 := by positivity
      linarith
  have h_int : IntervalIntegrable (fun x => C * (4 / (1 + 4 * (x - u)^2))) volume a b :=
    hcont.intervalIntegrable a b
  have h_ae : ∀ᵐ t, t ∈ Set.Ioc a b → ‖f t‖ ≤ C * (4 / (1 + 4 * (t - u)^2)) :=
    Filter.Eventually.of_forall hf
  have h_bound := intervalIntegral.norm_integral_le_of_norm_le hab h_ae h_int
  refine le_trans h_bound ?_
  rw [intervalIntegral.integral_const_mul]
  have h_int_le := integral_arctan_scaled_le u a b
  have : C * ∫ t in a..b, 4 / (1 + 4 * (t - u) ^ 2) ≤ C * (2 * π) :=
    mul_le_mul_of_nonneg_left h_int_le hC
  exact this

/-- Bound on the lower vertical contour integral `J₃`. -/
theorem J3Bound (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    (θ φ : ℝ → ℝ) (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2) (hθanti : AntitoneOn θ (Set.Ici 3))
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t) (hφmono : MonotoneOn φ (Set.Ici 3))
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ φ |t|) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1)
      (u : ℝ) (T : ℝ) (_ : 3 < T),
      ‖J₃ ν ε T X (1 - θ T) u‖ ≤ C * X ^ (1 - θ T) * φ T / ε := by
  obtain ⟨M, M_pos, M_bounds⟩ := MellinOfSmooth1b diffν suppν
  let C := |π|⁻¹ * 2⁻¹ * (2 * π * M)
  have C_pos : 0 < C := by positivity
  refine ⟨C, C_pos, fun X X_gt ε ε_pos ε_lt_one u T T_gt => ?_⟩
  let σ₁ := 1 - θ T
  have hT_le : 3 ≤ T := T_gt.le
  have hθT := hθ T hT_le
  have σ₁_pos : 0 < σ₁ := by dsimp [σ₁]; linarith [hθT.2]
  have σ₁_ge_half : 1 / 2 ≤ σ₁ := by dsimp [σ₁]; linarith [hθT.2]
  have σ₁_le_two : σ₁ ≤ 2 := by dsimp [σ₁]; linarith [hθT.1]
  have hab : -T ≤ -3 := by linarith
  have f_bnd (t : ℝ) (ht : t ∈ Ioc (-T) (-3)) :
      ‖twistedIntegrand ν ε X u (σ₁ + t * I)‖ ≤
      (M * X ^ σ₁ * φ T * ε⁻¹) * (4 / (1 + 4 * (t - u)^2)) := by
    have ht_abs : 3 ≤ |t| ∧ |t| ≤ T := by
      constructor
      · rw [abs_of_neg (by linarith [ht.2])]
        linarith [ht.2]
      · rw [abs_of_neg (by linarith [ht.2])]
        linarith [ht.1]
    have h_zeta : ‖(-deriv riemannZeta (σ₁ + t * I)) / riemannZeta (σ₁ + t * I)‖ ≤ φ T := by
      rw [neg_div, norm_neg]
      have h1 : 3 ≤ |t| := ht_abs.left
      have h_th : θ T ≤ θ |t| := hθanti ht_abs.left hT_le ht_abs.right
      have h2 : 1 - θ |t| ≤ σ₁ := by dsimp [σ₁]; linarith
      have h_bnd := hζ σ₁ t h1 h2 σ₁_le_two
      have h_phi : φ |t| ≤ φ T := hφmono ht_abs.left hT_le ht_abs.right
      exact le_trans h_bnd h_phi
    have h_mel_le : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ₁ : ℂ) + t * I - u * I)‖ ≤
        M * ε⁻¹ * (4 / (1 + 4 * (t - u)^2)) := by
      have hs : ((σ₁ : ℂ) + t * I - u * I).re = σ₁ := by
        have : (σ₁ : ℂ) + t * I - u * I = (σ₁ : ℂ) + ((t - u : ℝ) : ℂ) * I := by push_cast; ring
        rw [this]; simp
      have h_mel := M_bounds (1 / 2) (by norm_num) ((σ₁ : ℂ) + t * I - u * I)
        (by rw [hs]; exact σ₁_ge_half) (by rw [hs]; exact σ₁_le_two) ε ε_pos ε_lt_one
      have h_norm_sq : ‖(σ₁ : ℂ) + t * I - u * I‖^2 = σ₁^2 + (t - u)^2 := norm_sq_shift σ₁ t u
      have h_norm_ge : 1 / 4 + (t - u)^2 ≤ ‖(σ₁ : ℂ) + t * I - u * I‖^2 := by
        rw [h_norm_sq]
        have : (1 / 2)^2 ≤ σ₁^2 := by nlinarith [σ₁_ge_half]
        linarith
      have h_inv : (‖(σ₁ : ℂ) + t * I - u * I‖^2)⁻¹ ≤ 4 / (1 + 4 * (t - u)^2) := by
        have h_pos : 0 < 1 / 4 + (t - u)^2 := by
          have : 0 ≤ (t - u)^2 := sq_nonneg _
          linarith
        have h := (inv_le_inv₀ (by linarith) h_pos).mpr h_norm_ge
        have h_alg : (1 / 4 + (t - u)^2)⁻¹ = 4 / (1 + 4 * (t - u)^2) := by
          have : 1 / 4 + (t - u)^2 = (1 + 4 * (t - u)^2) / 4 := by ring
          rw [this, inv_div]
        rwa [h_alg] at h
      have h_calc : M * (ε * ‖(σ₁ : ℂ) + t * I - u * I‖^2)⁻¹ ≤ M * ε⁻¹ * (4 / (1 + 4 * (t - u)^2)) := by
        have : (ε * ‖(σ₁ : ℂ) + t * I - u * I‖^2)⁻¹ = ε⁻¹ * (‖(σ₁ : ℂ) + t * I - u * I‖^2)⁻¹ := mul_inv _ _
        rw [this]
        have : 0 ≤ M * ε⁻¹ := by positivity
        nlinarith
      exact le_trans h_mel h_calc
    have h_xcpow : ‖(X : ℂ) ^ ((σ₁ : ℂ) + t * I - u * I)‖ = X ^ σ₁ := by
      rw [norm_cpow_shift (by linarith)]
      have : ((σ₁ : ℂ) + t * I).re = σ₁ := re_add_t_I σ₁ t
      rw [this]
    have h_int_eq : ‖twistedIntegrand ν ε X u (σ₁ + t * I)‖ =
        ‖(-deriv riemannZeta (σ₁ + t * I)) / riemannZeta (σ₁ + t * I)‖ *
        ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ₁ : ℂ) + t * I - u * I)‖ *
        ‖(X : ℂ) ^ ((σ₁ : ℂ) + t * I - u * I)‖ := by
      dsimp [twistedIntegrand]
      rw [norm_mul, norm_mul]
    rw [h_int_eq]
    have h_zeta_nonneg : 0 ≤ φ T := by linarith [hφ T hT_le]
    have h_mel_nonneg : 0 ≤ M * ε⁻¹ * (4 / (1 + 4 * (t - u)^2)) := by positivity
    have h12 := mul_le_mul h_zeta h_mel_le (norm_nonneg _) h_zeta_nonneg
    have h12_nonneg : 0 ≤ φ T * (M * ε⁻¹ * (4 / (1 + 4 * (t - u)^2))) := mul_nonneg h_zeta_nonneg h_mel_nonneg
    have h123 := mul_le_mul h12 (le_of_eq h_xcpow) (norm_nonneg _) h12_nonneg
    refine le_trans h123 (le_of_eq ?_)
    ring
  have hC_nonneg : 0 ≤ (M * X ^ σ₁ * φ T * ε⁻¹) := by
    have : 0 ≤ φ T := by linarith [hφ T hT_le]
    positivity
  have int_bnd : ‖∫ t in (-T)..(-3), twistedIntegrand ν ε X u (σ₁ + t * I)‖ ≤
      (M * X ^ σ₁ * φ T * ε⁻¹) * (2 * π) := by
    apply integral_norm_le_example u (-T) (-3) (M * X ^ σ₁ * φ T * ε⁻¹) hab hC_nonneg
    exact f_bnd
  unfold J₃
  rw [norm_mul, norm_mul, norm_I, one_mul, norm_one_div_two_pi_I]
  have Z4 := mul_le_mul_of_nonneg_left int_bnd (by positivity : 0 ≤ |π|⁻¹ * 2⁻¹)
  have h_eq : |π|⁻¹ * 2⁻¹ * ((M * X ^ σ₁ * φ T * ε⁻¹) * (2 * π)) =
      C * X ^ (1 - θ T) * φ T / ε := by
    dsimp [C, σ₁]; ring
  rw [h_eq] at Z4
  exact Z4

/-- Bound on the upper vertical contour integral `J₇`. -/
theorem J7Bound (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    (θ φ : ℝ → ℝ) (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2) (hθanti : AntitoneOn θ (Set.Ici 3))
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t) (hφmono : MonotoneOn φ (Set.Ici 3))
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ φ |t|) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1)
      (u : ℝ) (T : ℝ) (_ : 3 < T),
      ‖J₇ ν ε T X (1 - θ T) u‖ ≤ C * X ^ (1 - θ T) * φ T / ε := by
  obtain ⟨M, M_pos, M_bounds⟩ := MellinOfSmooth1b diffν suppν
  let C := |π|⁻¹ * 2⁻¹ * (2 * π * M)
  have C_pos : 0 < C := by positivity
  refine ⟨C, C_pos, fun X X_gt ε ε_pos ε_lt_one u T T_gt => ?_⟩
  let σ₁ := 1 - θ T
  have hT_le : 3 ≤ T := T_gt.le
  have hθT := hθ T hT_le
  have σ₁_pos : 0 < σ₁ := by dsimp [σ₁]; linarith [hθT.2]
  have σ₁_ge_half : 1 / 2 ≤ σ₁ := by dsimp [σ₁]; linarith [hθT.2]
  have σ₁_le_two : σ₁ ≤ 2 := by dsimp [σ₁]; linarith [hθT.1]
  have hab : 3 ≤ T := hT_le
  have f_bnd (t : ℝ) (ht : t ∈ Ioc 3 T) :
      ‖twistedIntegrand ν ε X u (σ₁ + t * I)‖ ≤
      (M * X ^ σ₁ * φ T * ε⁻¹) * (4 / (1 + 4 * (t - u)^2)) := by
    have ht_abs : 3 ≤ |t| ∧ |t| ≤ T := by
      constructor
      · rw [abs_of_pos (by linarith [ht.1])]
        linarith [ht.1]
      · rw [abs_of_pos (by linarith [ht.1])]
        linarith [ht.2]
    have h_zeta : ‖(-deriv riemannZeta (σ₁ + t * I)) / riemannZeta (σ₁ + t * I)‖ ≤ φ T := by
      rw [neg_div, norm_neg]
      have h1 : 3 ≤ |t| := ht_abs.left
      have h_th : θ T ≤ θ |t| := hθanti ht_abs.left hT_le ht_abs.right
      have h2 : 1 - θ |t| ≤ σ₁ := by dsimp [σ₁]; linarith
      have h_bnd := hζ σ₁ t h1 h2 σ₁_le_two
      have h_phi : φ |t| ≤ φ T := hφmono ht_abs.left hT_le ht_abs.right
      exact le_trans h_bnd h_phi
    have h_mel_le : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ₁ : ℂ) + t * I - u * I)‖ ≤
        M * ε⁻¹ * (4 / (1 + 4 * (t - u)^2)) := by
      have hs : ((σ₁ : ℂ) + t * I - u * I).re = σ₁ := by
        have : (σ₁ : ℂ) + t * I - u * I = (σ₁ : ℂ) + ((t - u : ℝ) : ℂ) * I := by push_cast; ring
        rw [this]; simp
      have h_mel := M_bounds (1 / 2) (by norm_num) ((σ₁ : ℂ) + t * I - u * I)
        (by rw [hs]; exact σ₁_ge_half) (by rw [hs]; exact σ₁_le_two) ε ε_pos ε_lt_one
      have h_norm_sq : ‖(σ₁ : ℂ) + t * I - u * I‖^2 = σ₁^2 + (t - u)^2 := norm_sq_shift σ₁ t u
      have h_norm_ge : 1 / 4 + (t - u)^2 ≤ ‖(σ₁ : ℂ) + t * I - u * I‖^2 := by
        rw [h_norm_sq]
        have : (1 / 2)^2 ≤ σ₁^2 := by nlinarith [σ₁_ge_half]
        linarith
      have h_inv : (‖(σ₁ : ℂ) + t * I - u * I‖^2)⁻¹ ≤ 4 / (1 + 4 * (t - u)^2) := by
        have h_pos : 0 < 1 / 4 + (t - u)^2 := by
          have : 0 ≤ (t - u)^2 := sq_nonneg _
          linarith
        have h := (inv_le_inv₀ (by linarith) h_pos).mpr h_norm_ge
        have h_alg : (1 / 4 + (t - u)^2)⁻¹ = 4 / (1 + 4 * (t - u)^2) := by
          have : 1 / 4 + (t - u)^2 = (1 + 4 * (t - u)^2) / 4 := by ring
          rw [this, inv_div]
        rwa [h_alg] at h
      have h_calc : M * (ε * ‖(σ₁ : ℂ) + t * I - u * I‖^2)⁻¹ ≤ M * ε⁻¹ * (4 / (1 + 4 * (t - u)^2)) := by
        have : (ε * ‖(σ₁ : ℂ) + t * I - u * I‖^2)⁻¹ = ε⁻¹ * (‖(σ₁ : ℂ) + t * I - u * I‖^2)⁻¹ := mul_inv _ _
        rw [this]
        have : 0 ≤ M * ε⁻¹ := by positivity
        nlinarith
      exact le_trans h_mel h_calc
    have h_xcpow : ‖(X : ℂ) ^ ((σ₁ : ℂ) + t * I - u * I)‖ = X ^ σ₁ := by
      rw [norm_cpow_shift (by linarith)]
      have : ((σ₁ : ℂ) + t * I).re = σ₁ := re_add_t_I σ₁ t
      rw [this]
    have h_int_eq : ‖twistedIntegrand ν ε X u (σ₁ + t * I)‖ =
        ‖(-deriv riemannZeta (σ₁ + t * I)) / riemannZeta (σ₁ + t * I)‖ *
        ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ₁ : ℂ) + t * I - u * I)‖ *
        ‖(X : ℂ) ^ ((σ₁ : ℂ) + t * I - u * I)‖ := by
      dsimp [twistedIntegrand]
      rw [norm_mul, norm_mul]
    rw [h_int_eq]
    have h_zeta_nonneg : 0 ≤ φ T := by linarith [hφ T hT_le]
    have h_mel_nonneg : 0 ≤ M * ε⁻¹ * (4 / (1 + 4 * (t - u)^2)) := by positivity
    have h12 := mul_le_mul h_zeta h_mel_le (norm_nonneg _) h_zeta_nonneg
    have h12_nonneg : 0 ≤ φ T * (M * ε⁻¹ * (4 / (1 + 4 * (t - u)^2))) := mul_nonneg h_zeta_nonneg h_mel_nonneg
    have h123 := mul_le_mul h12 (le_of_eq h_xcpow) (norm_nonneg _) h12_nonneg
    refine le_trans h123 (le_of_eq ?_)
    ring
  have hC_nonneg : 0 ≤ (M * X ^ σ₁ * φ T * ε⁻¹) := by
    have : 0 ≤ φ T := by linarith [hφ T hT_le]
    positivity
  have int_bnd : ‖∫ t in 3..T, twistedIntegrand ν ε X u (σ₁ + t * I)‖ ≤
      (M * X ^ σ₁ * φ T * ε⁻¹) * (2 * π) := by
    apply integral_norm_le_example u 3 T (M * X ^ σ₁ * φ T * ε⁻¹) hab hC_nonneg
    exact f_bnd
  unfold J₇
  rw [norm_mul, norm_mul, norm_I, one_mul, norm_one_div_two_pi_I]
  have Z4 := mul_le_mul_of_nonneg_left int_bnd (by positivity : 0 ≤ |π|⁻¹ * 2⁻¹)
  have h_eq : |π|⁻¹ * 2⁻¹ * ((M * X ^ σ₁ * φ T * ε⁻¹) * (2 * π)) =
      C * X ^ (1 - θ T) * φ T / ε := by
    dsimp [C, σ₁]; ring
  rw [h_eq] at Z4
  exact Z4

/-- Bound on `deriv riemannZeta / riemannZeta` on the three segments of the compact box boundary. -/
theorem zeta_bound_on_box_boundary {σ₂ : ℝ} (hσ₂_pos : 0 < σ₂) (hσ₂_lt : σ₂ < 1)
    (h_holo : DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1})) :
    ∃ (B : ℝ) (_ : 0 < B),
      (∀ σ ∈ Set.Icc σ₂ 1, ‖deriv riemannZeta (σ - 3 * I) / riemannZeta (σ - 3 * I)‖ ≤ B) ∧
      (∀ σ ∈ Set.Icc σ₂ 1, ‖deriv riemannZeta (σ + 3 * I) / riemannZeta (σ + 3 * I)‖ ≤ B) ∧
      (∀ t ∈ Set.Icc (-3 : ℝ) 3, ‖deriv riemannZeta (σ₂ + t * I) / riemannZeta (σ₂ + t * I)‖ ≤ B) := by
  let K₄ : Set ℂ := Set.Icc σ₂ 1 ×ℂ {-3}
  have hK₄_compact : IsCompact K₄ := isCompact_Icc.reProdIm isCompact_singleton
  have hK₄_sub : K₄ ⊆ Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1} := by
    intro z hz
    simp only [K₄, mem_reProdIm, mem_Icc, mem_singleton_iff, Set.mem_sdiff] at hz ⊢
    refine ⟨⟨⟨hz.1.1, by linarith [hz.1.2]⟩, ⟨by linarith [hz.2], by linarith [hz.2]⟩⟩, ?_⟩
    intro hz1; have := congr_arg Complex.im hz1
    simp only [hz.2, one_im] at this; norm_num at this
  have h_cont₄ : ContinuousOn (fun s => deriv riemannZeta s / riemannZeta s) K₄ :=
    (h_holo.mono hK₄_sub).continuousOn
  obtain ⟨B₄, hB₄⟩ := IsCompact.exists_bound_of_continuousOn hK₄_compact h_cont₄

  let K₆ : Set ℂ := Set.Icc σ₂ 1 ×ℂ {3}
  have hK₆_compact : IsCompact K₆ := isCompact_Icc.reProdIm isCompact_singleton
  have hK₆_sub : K₆ ⊆ Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1} := by
    intro z hz
    simp only [K₆, mem_reProdIm, mem_Icc, mem_singleton_iff, Set.mem_sdiff] at hz ⊢
    refine ⟨⟨⟨hz.1.1, by linarith [hz.1.2]⟩, ⟨by linarith [hz.2], by linarith [hz.2]⟩⟩, ?_⟩
    intro hz1; have := congr_arg Complex.im hz1
    simp only [hz.2, one_im] at this; norm_num at this
  have h_cont₆ : ContinuousOn (fun s => deriv riemannZeta s / riemannZeta s) K₆ :=
    (h_holo.mono hK₆_sub).continuousOn
  obtain ⟨B₆, hB₆⟩ := IsCompact.exists_bound_of_continuousOn hK₆_compact h_cont₆

  let K₅ : Set ℂ := {σ₂} ×ℂ Set.Icc (-3) 3
  have hK₅_compact : IsCompact K₅ := isCompact_singleton.reProdIm isCompact_Icc
  have hK₅_sub : K₅ ⊆ Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1} := by
    intro z hz
    simp only [K₅, mem_reProdIm, mem_Icc, mem_singleton_iff, Set.mem_sdiff] at hz ⊢
    refine ⟨⟨⟨by rw [hz.1], by rw [hz.1]; linarith⟩, hz.2⟩, ?_⟩
    intro hz1; have := congr_arg Complex.re hz1
    simp only [hz.1, one_re] at this; linarith
  have h_cont₅ : ContinuousOn (fun s => deriv riemannZeta s / riemannZeta s) K₅ :=
    (h_holo.mono hK₅_sub).continuousOn
  obtain ⟨B₅, hB₅⟩ := IsCompact.exists_bound_of_continuousOn hK₅_compact h_cont₅

  let B := |B₄| + |B₆| + |B₅| + 1
  have B_pos : 0 < B := by positivity
  refine ⟨B, B_pos, ?_, ?_, ?_⟩
  · intro σ hσ
    have hz : (σ : ℂ) - 3 * I ∈ K₄ := by
      simp only [K₄, mem_reProdIm, mem_singleton_iff, re_sub_three_I, im_sub_three_I,
        hσ, and_true]
    have := hB₄ (σ - 3 * I) hz
    linarith [le_abs_self B₄, abs_nonneg B₆, abs_nonneg B₅]
  · intro σ hσ
    have hz : (σ : ℂ) + 3 * I ∈ K₆ := by
      simp only [K₆, mem_reProdIm, mem_singleton_iff, re_add_three_I, im_add_three_I,
        hσ, and_true]
    have := hB₆ (σ + 3 * I) hz
    linarith [le_abs_self B₆, abs_nonneg B₄, abs_nonneg B₅]
  · intro t ht
    have hz : (σ₂ : ℂ) + t * I ∈ K₅ := by
      simp only [K₅, mem_reProdIm, mem_singleton_iff, re_add_t_I, im_add_t_I,
        ht, and_true]
    have := hB₅ (σ₂ + t * I) hz
    linarith [le_abs_self B₅, abs_nonneg B₄, abs_nonneg B₆]

/-- Bound on the lower horizontal connecting contour integral `J₄`. -/
theorem J4Bound (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    {σ₂ : ℝ} (hσ₂_pos : 0 < σ₂) (hσ₂_lt : σ₂ < 1)
    (h_holo : DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1})) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1)
      (u : ℝ) (T : ℝ) (_ : 3 < T) (θ : ℝ → ℝ) (_ : 0 < θ T) (_ : θ T ≤ 1 / 2)
      (_ : σ₂ < 1 - θ T) (φ : ℝ → ℝ) (_ : 1 ≤ φ T),
      ‖J₄ ν ε X (1 - θ T) σ₂ u‖ ≤ C * X ^ (1 - θ T) * φ T / ε := by
  obtain ⟨M, M_pos, M_bounds⟩ := MellinOfSmooth1b diffν suppν
  obtain ⟨B, B_pos, hB₄, _, _⟩ := zeta_bound_on_box_boundary hσ₂_pos hσ₂_lt h_holo
  let C := |π|⁻¹ * 2⁻¹ * (B * M * (σ₂^2)⁻¹ * 2)
  have C_pos : 0 < C := by positivity
  refine ⟨C, C_pos, fun X X_gt ε ε_pos ε_lt_one u T T_gt θ _hθT _hθT_le hσ₂_lt_σ₁ φ hφ => ?_⟩
  let σ₁ := 1 - θ T
  have σ₁_lt_one : σ₁ < 1 := by dsimp [σ₁]; linarith
  have σ₁_pos : 0 < σ₁ := by dsimp [σ₁]; linarith
  have f_bnd (σ : ℝ) (hσ : σ ∈ uIoc σ₂ σ₁) :
      ‖twistedIntegrand ν ε X u (σ - 3 * I)‖ ≤ (B * M * (σ₂^2)⁻¹) * X ^ σ₁ * ε⁻¹ := by
    rw [uIoc_of_le hσ₂_lt_σ₁.le, mem_Ioc] at hσ
    have hσ_in_Icc : σ ∈ Icc σ₂ 1 := ⟨hσ.1.le, le_trans hσ.2 σ₁_lt_one.le⟩
    have h_zeta : ‖(-deriv riemannZeta (σ - 3 * I)) / riemannZeta (σ - 3 * I)‖ ≤ B := by
      rw [neg_div, norm_neg]
      exact hB₄ σ hσ_in_Icc
    have h_mel_le : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ : ℂ) - 3 * I - u * I)‖ ≤
        M * ε⁻¹ * (σ₂^2)⁻¹ := by
      have hs : ((σ : ℂ) - 3 * I - u * I).re = σ := by
        have : (σ : ℂ) - 3 * I - u * I = (σ : ℂ) + ((-3 - u : ℝ) : ℂ) * I := by push_cast; ring
        rw [this]; simp
      have h_mel := M_bounds σ₂ hσ₂_pos ((σ : ℂ) - 3 * I - u * I)
        (by rw [hs]; exact hσ.1.le) (by rw [hs]; linarith [hσ_in_Icc.2]) ε ε_pos ε_lt_one
      have h_norm_sq : σ₂^2 ≤ ‖(σ : ℂ) - 3 * I - u * I‖^2 := by
        have : (σ : ℂ) - 3 * I - u * I = (σ : ℂ) + (-3 : ℝ) * I - u * I := by push_cast; ring
        rw [this, norm_sq_shift]
        have : 0 ≤ (-3 - u)^2 := sq_nonneg _
        have : σ₂^2 ≤ σ^2 := by nlinarith [hσ.1.le]
        linarith
      have h_inv : (‖(σ : ℂ) - 3 * I - u * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ := by
        have h_pos : 0 < σ₂^2 := by positivity
        exact (inv_le_inv₀ (by linarith) h_pos).mpr h_norm_sq
      have h_calc : M * (ε * ‖(σ : ℂ) - 3 * I - u * I‖^2)⁻¹ ≤ M * ε⁻¹ * (σ₂^2)⁻¹ := by
        have : (ε * ‖(σ : ℂ) - 3 * I - u * I‖^2)⁻¹ = ε⁻¹ * (‖(σ : ℂ) - 3 * I - u * I‖^2)⁻¹ := mul_inv _ _
        rw [this]
        have : 0 ≤ M * ε⁻¹ := by positivity
        nlinarith
      exact le_trans h_mel h_calc
    have h_xcpow : ‖(X : ℂ) ^ ((σ : ℂ) - 3 * I - u * I)‖ ≤ X ^ σ₁ := by
      rw [norm_cpow_shift (by linarith)]
      have : ((σ : ℂ) - 3 * I).re = σ := re_sub_three_I σ
      rw [this]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.2
    have h_int_eq : ‖twistedIntegrand ν ε X u (σ - 3 * I)‖ =
        ‖(-deriv riemannZeta (σ - 3 * I)) / riemannZeta (σ - 3 * I)‖ *
        ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ : ℂ) - 3 * I - u * I)‖ *
        ‖(X : ℂ) ^ ((σ : ℂ) - 3 * I - u * I)‖ := by
      dsimp [twistedIntegrand]
      rw [norm_mul, norm_mul]
    rw [h_int_eq]
    have h_zeta_nonneg : 0 ≤ B := B_pos.le
    have h_mel_nonneg : 0 ≤ M * ε⁻¹ * (σ₂^2)⁻¹ := by positivity
    have h12 := mul_le_mul h_zeta h_mel_le (norm_nonneg _) h_zeta_nonneg
    have h12_nonneg : 0 ≤ B * (M * ε⁻¹ * (σ₂^2)⁻¹) := mul_nonneg h_zeta_nonneg h_mel_nonneg
    have h123 := mul_le_mul h12 h_xcpow (norm_nonneg _) h12_nonneg
    refine le_trans h123 (le_of_eq ?_)
    ring
  have int_bnd : ‖∫ σ in σ₂..σ₁, twistedIntegrand ν ε X u (σ - 3 * I)‖ ≤
      (B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε := by
    have h_norm_int := intervalIntegral.norm_integral_le_of_norm_le_const f_bnd
    refine le_trans h_norm_int ?_
    have h_len : |σ₁ - σ₂| ≤ 2 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have : ((B * M * (σ₂^2)⁻¹) * X ^ σ₁ * ε⁻¹) * |σ₁ - σ₂| ≤ ((B * M * (σ₂^2)⁻¹) * X ^ σ₁ * ε⁻¹) * 2 := by
      have : 0 ≤ (B * M * (σ₂^2)⁻¹) * X ^ σ₁ * ε⁻¹ := by positivity
      nlinarith
    refine le_trans this ?_
    ring_nf; rfl
  unfold J₄
  rw [norm_mul, norm_one_div_two_pi_I]
  have Z4 := mul_le_mul_of_nonneg_left int_bnd (by positivity : 0 ≤ |π|⁻¹ * 2⁻¹)
  have h_phi_le : (B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε ≤ (B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ * φ T / ε := by
    have h_step : ((B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε) * 1 ≤ ((B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε) * φ T :=
      mul_le_mul_of_nonneg_left hφ (by positivity)
    have h_eq1 : ((B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε) * 1 = (B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε := by ring
    have h_eq2 : ((B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε) * φ T = (B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ * φ T / ε := by ring
    linarith
  have Z5 := le_trans Z4 (mul_le_mul_of_nonneg_left h_phi_le (by positivity))
  have h_eq : |π|⁻¹ * 2⁻¹ * ((B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ * φ T / ε) =
      C * X ^ (1 - θ T) * φ T / ε := by
    dsimp [C, σ₁]; ring
  rw [h_eq] at Z5
  exact Z5

/-- Bound on the upper horizontal connecting contour integral `J₆`. -/
theorem J6Bound (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    {σ₂ : ℝ} (hσ₂_pos : 0 < σ₂) (hσ₂_lt : σ₂ < 1)
    (h_holo : DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1})) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1)
      (u : ℝ) (T : ℝ) (_ : 3 < T) (θ : ℝ → ℝ) (_ : 0 < θ T) (_ : θ T ≤ 1 / 2)
      (_ : σ₂ < 1 - θ T) (φ : ℝ → ℝ) (_ : 1 ≤ φ T),
      ‖J₆ ν ε X (1 - θ T) σ₂ u‖ ≤ C * X ^ (1 - θ T) * φ T / ε := by
  obtain ⟨M, M_pos, M_bounds⟩ := MellinOfSmooth1b diffν suppν
  obtain ⟨B, B_pos, _, hB₆, _⟩ := zeta_bound_on_box_boundary hσ₂_pos hσ₂_lt h_holo
  let C := |π|⁻¹ * 2⁻¹ * (B * M * (σ₂^2)⁻¹ * 2)
  have C_pos : 0 < C := by positivity
  refine ⟨C, C_pos, fun X X_gt ε ε_pos ε_lt_one u T T_gt θ _hθT _hθT_le hσ₂_lt_σ₁ φ hφ => ?_⟩
  let σ₁ := 1 - θ T
  have σ₁_lt_one : σ₁ < 1 := by dsimp [σ₁]; linarith
  have σ₁_pos : 0 < σ₁ := by dsimp [σ₁]; linarith
  have f_bnd (σ : ℝ) (hσ : σ ∈ uIoc σ₂ σ₁) :
      ‖twistedIntegrand ν ε X u (σ + 3 * I)‖ ≤ (B * M * (σ₂^2)⁻¹) * X ^ σ₁ * ε⁻¹ := by
    rw [uIoc_of_le hσ₂_lt_σ₁.le, mem_Ioc] at hσ
    have hσ_in_Icc : σ ∈ Icc σ₂ 1 := ⟨hσ.1.le, le_trans hσ.2 σ₁_lt_one.le⟩
    have h_zeta : ‖(-deriv riemannZeta (σ + 3 * I)) / riemannZeta (σ + 3 * I)‖ ≤ B := by
      rw [neg_div, norm_neg]
      exact hB₆ σ hσ_in_Icc
    have h_mel_le : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + 3 * I - u * I)‖ ≤
        M * ε⁻¹ * (σ₂^2)⁻¹ := by
      have hs : ((σ : ℂ) + 3 * I - u * I).re = σ := by
        have : (σ : ℂ) + 3 * I - u * I = (σ : ℂ) + ((3 - u : ℝ) : ℂ) * I := by push_cast; ring
        rw [this]; simp
      have h_mel := M_bounds σ₂ hσ₂_pos ((σ : ℂ) + 3 * I - u * I)
        (by rw [hs]; exact hσ.1.le) (by rw [hs]; linarith [hσ_in_Icc.2]) ε ε_pos ε_lt_one
      have h_norm_sq : σ₂^2 ≤ ‖(σ : ℂ) + 3 * I - u * I‖^2 := by
        have : (σ : ℂ) + 3 * I - u * I = (σ : ℂ) + (3 : ℝ) * I - u * I := by push_cast; ring
        rw [this, norm_sq_shift]
        have : 0 ≤ (3 - u)^2 := sq_nonneg _
        have : σ₂^2 ≤ σ^2 := by nlinarith [hσ.1.le]
        linarith
      have h_inv : (‖(σ : ℂ) + 3 * I - u * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ := by
        have h_pos : 0 < σ₂^2 := by positivity
        exact (inv_le_inv₀ (by linarith) h_pos).mpr h_norm_sq
      have h_calc : M * (ε * ‖(σ : ℂ) + 3 * I - u * I‖^2)⁻¹ ≤ M * ε⁻¹ * (σ₂^2)⁻¹ := by
        have : (ε * ‖(σ : ℂ) + 3 * I - u * I‖^2)⁻¹ = ε⁻¹ * (‖(σ : ℂ) + 3 * I - u * I‖^2)⁻¹ := mul_inv _ _
        rw [this]
        have : 0 ≤ M * ε⁻¹ := by positivity
        nlinarith
      exact le_trans h_mel h_calc
    have h_xcpow : ‖(X : ℂ) ^ ((σ : ℂ) + 3 * I - u * I)‖ ≤ X ^ σ₁ := by
      rw [norm_cpow_shift (by linarith)]
      have : ((σ : ℂ) + 3 * I).re = σ := re_add_three_I σ
      rw [this]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) hσ.2
    have h_int_eq : ‖twistedIntegrand ν ε X u (σ + 3 * I)‖ =
        ‖(-deriv riemannZeta (σ + 3 * I)) / riemannZeta (σ + 3 * I)‖ *
        ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ : ℂ) + 3 * I - u * I)‖ *
        ‖(X : ℂ) ^ ((σ : ℂ) + 3 * I - u * I)‖ := by
      dsimp [twistedIntegrand]
      rw [norm_mul, norm_mul]
    rw [h_int_eq]
    have h_zeta_nonneg : 0 ≤ B := B_pos.le
    have h_mel_nonneg : 0 ≤ M * ε⁻¹ * (σ₂^2)⁻¹ := by positivity
    have h12 := mul_le_mul h_zeta h_mel_le (norm_nonneg _) h_zeta_nonneg
    have h12_nonneg : 0 ≤ B * (M * ε⁻¹ * (σ₂^2)⁻¹) := mul_nonneg h_zeta_nonneg h_mel_nonneg
    have h123 := mul_le_mul h12 h_xcpow (norm_nonneg _) h12_nonneg
    refine le_trans h123 (le_of_eq ?_)
    ring
  have int_bnd : ‖∫ σ in σ₂..σ₁, twistedIntegrand ν ε X u (σ + 3 * I)‖ ≤
      (B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε := by
    have h_norm_int := intervalIntegral.norm_integral_le_of_norm_le_const f_bnd
    refine le_trans h_norm_int ?_
    have h_len : |σ₁ - σ₂| ≤ 2 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have : ((B * M * (σ₂^2)⁻¹) * X ^ σ₁ * ε⁻¹) * |σ₁ - σ₂| ≤ ((B * M * (σ₂^2)⁻¹) * X ^ σ₁ * ε⁻¹) * 2 := by
      have : 0 ≤ (B * M * (σ₂^2)⁻¹) * X ^ σ₁ * ε⁻¹ := by positivity
      nlinarith
    refine le_trans this ?_
    ring_nf; rfl
  unfold J₆
  rw [norm_mul, norm_one_div_two_pi_I]
  have Z4 := mul_le_mul_of_nonneg_left int_bnd (by positivity : 0 ≤ |π|⁻¹ * 2⁻¹)
  have h_phi_le : (B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε ≤ (B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ * φ T / ε := by
    have h_step : ((B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε) * 1 ≤ ((B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε) * φ T :=
      mul_le_mul_of_nonneg_left hφ (by positivity)
    have h_eq1 : ((B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε) * 1 = (B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε := by ring
    have h_eq2 : ((B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ / ε) * φ T = (B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ * φ T / ε := by ring
    linarith
  have Z5 := le_trans Z4 (mul_le_mul_of_nonneg_left h_phi_le (by positivity))
  have h_eq : |π|⁻¹ * 2⁻¹ * ((B * M * (σ₂^2)⁻¹ * 2) * X ^ σ₁ * φ T / ε) =
      C * X ^ (1 - θ T) * φ T / ε := by
    dsimp [C, σ₁]; ring
  rw [h_eq] at Z5
  exact Z5

/-- Bound on the central vertical contour integral `J₅`. -/
theorem J5Bound (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2)
    {σ₂ : ℝ} (hσ₂_pos : 0 < σ₂) (hσ₂_lt : σ₂ < 1)
    (h_holo : DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      (Set.Icc σ₂ 2 ×ℂ Set.Icc (-3) 3 \ {1})) :
    ∃ (C : ℝ) (_ : 0 < C), ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1)
      (u : ℝ),
      ‖J₅ ν ε X σ₂ u‖ ≤ C * X ^ σ₂ / ε := by
  obtain ⟨M, M_pos, M_bounds⟩ := MellinOfSmooth1b diffν suppν
  obtain ⟨B, B_pos, _, _, hB₅⟩ := zeta_bound_on_box_boundary hσ₂_pos hσ₂_lt h_holo
  let C := |π|⁻¹ * 2⁻¹ * (B * M * (σ₂^2)⁻¹ * 6)
  have C_pos : 0 < C := by positivity
  refine ⟨C, C_pos, fun X X_gt ε ε_pos ε_lt_one u => ?_⟩
  have f_bnd (t : ℝ) (ht : t ∈ uIoc (-3 : ℝ) 3) :
      ‖twistedIntegrand ν ε X u (σ₂ + t * I)‖ ≤ (B * M * (σ₂^2)⁻¹) * X ^ σ₂ * ε⁻¹ := by
    rw [uIoc_of_le (by norm_num : (-3 : ℝ) ≤ 3), mem_Ioc] at ht
    have ht_in_Icc : t ∈ Icc (-3 : ℝ) 3 := ⟨ht.1.le, ht.2⟩
    have h_zeta : ‖(-deriv riemannZeta (σ₂ + t * I)) / riemannZeta (σ₂ + t * I)‖ ≤ B := by
      rw [neg_div, norm_neg]
      exact hB₅ t ht_in_Icc
    have h_mel_le : ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ₂ : ℂ) + t * I - u * I)‖ ≤
        M * ε⁻¹ * (σ₂^2)⁻¹ := by
      have hs : ((σ₂ : ℂ) + t * I - u * I).re = σ₂ := by
        have : (σ₂ : ℂ) + t * I - u * I = (σ₂ : ℂ) + ((t - u : ℝ) : ℂ) * I := by push_cast; ring
        rw [this]; simp
      have h_mel := M_bounds σ₂ hσ₂_pos ((σ₂ : ℂ) + t * I - u * I)
        (by rw [hs]) (by rw [hs]; linarith) ε ε_pos ε_lt_one
      have h_norm_sq : σ₂^2 ≤ ‖(σ₂ : ℂ) + t * I - u * I‖^2 := by
        rw [norm_sq_shift]
        have : 0 ≤ (t - u)^2 := sq_nonneg _
        linarith
      have h_inv : (‖(σ₂ : ℂ) + t * I - u * I‖^2)⁻¹ ≤ (σ₂^2)⁻¹ := by
        have h_pos : 0 < σ₂^2 := by positivity
        exact (inv_le_inv₀ (by linarith) h_pos).mpr h_norm_sq
      have h_calc : M * (ε * ‖(σ₂ : ℂ) + t * I - u * I‖^2)⁻¹ ≤ M * ε⁻¹ * (σ₂^2)⁻¹ := by
        have : (ε * ‖(σ₂ : ℂ) + t * I - u * I‖^2)⁻¹ = ε⁻¹ * (‖(σ₂ : ℂ) + t * I - u * I‖^2)⁻¹ := mul_inv _ _
        rw [this]
        have : 0 ≤ M * ε⁻¹ := by positivity
        nlinarith
      exact le_trans h_mel h_calc
    have h_xcpow : ‖(X : ℂ) ^ ((σ₂ : ℂ) + t * I - u * I)‖ = X ^ σ₂ := by
      rw [norm_cpow_shift (by linarith)]
      have : ((σ₂ : ℂ) + t * I).re = σ₂ := re_add_t_I σ₂ t
      rw [this]
    have h_int_eq : ‖twistedIntegrand ν ε X u (σ₂ + t * I)‖ =
        ‖(-deriv riemannZeta (σ₂ + t * I)) / riemannZeta (σ₂ + t * I)‖ *
        ‖mellin (fun x => (Smooth1 ν ε x : ℂ)) ((σ₂ : ℂ) + t * I - u * I)‖ *
        ‖(X : ℂ) ^ ((σ₂ : ℂ) + t * I - u * I)‖ := by
      dsimp [twistedIntegrand]
      rw [norm_mul, norm_mul]
    rw [h_int_eq]
    have h_zeta_nonneg : 0 ≤ B := B_pos.le
    have h_mel_nonneg : 0 ≤ M * ε⁻¹ * (σ₂^2)⁻¹ := by positivity
    have h12 := mul_le_mul h_zeta h_mel_le (norm_nonneg _) h_zeta_nonneg
    have h12_nonneg : 0 ≤ B * (M * ε⁻¹ * (σ₂^2)⁻¹) := mul_nonneg h_zeta_nonneg h_mel_nonneg
    have h123 := mul_le_mul h12 (le_of_eq h_xcpow) (norm_nonneg _) h12_nonneg
    refine le_trans h123 (le_of_eq ?_)
    ring
  have int_bnd : ‖∫ t in (-3 : ℝ)..3, twistedIntegrand ν ε X u (σ₂ + t * I)‖ ≤
      (B * M * (σ₂^2)⁻¹ * 6) * X ^ σ₂ / ε := by
    have h_norm_int := intervalIntegral.norm_integral_le_of_norm_le_const f_bnd
    refine le_trans h_norm_int ?_
    have h_len : |(3 : ℝ) - (-3)| = 6 := by norm_num
    rw [h_len]
    have : ((B * M * (σ₂^2)⁻¹) * X ^ σ₂ * ε⁻¹) * 6 = (B * M * (σ₂^2)⁻¹ * 6) * X ^ σ₂ / ε := by ring
    rw [this]
  unfold J₅
  rw [norm_mul, norm_mul, norm_I, one_mul, norm_one_div_two_pi_I]
  have Z4 := mul_le_mul_of_nonneg_left int_bnd (by positivity : 0 ≤ |π|⁻¹ * 2⁻¹)
  have h_eq : |π|⁻¹ * 2⁻¹ * ((B * M * (σ₂^2)⁻¹ * 6) * X ^ σ₂ / ε) =
      C * X ^ σ₂ / ε := by
    dsimp [C]; ring
  rw [h_eq] at Z4
  exact Z4

/-- Main theorem: bound on the difference between the twisted smoothed sum and the main term. -/
theorem twistedSum_sub_main_le (ν : ℝ → ℝ) (diffν : ContDiff ℝ 1 ν)
    (suppν : Function.support ν ⊆ Set.Icc (1 / 2) 2) (νnonneg : ∀ x > 0, 0 ≤ ν x)
    (mass_one : ∫ x in Set.Ioi 0, ν x / x = 1)
    (θ φ : ℝ → ℝ) (hθ : ∀ t, 3 ≤ t → 0 < θ t ∧ θ t ≤ 1 / 2) (hθanti : AntitoneOn θ (Set.Ici 3))
    (hφ : ∀ t, 3 ≤ t → 1 ≤ φ t) (hφmono : MonotoneOn φ (Set.Ici 3))
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - θ |t| ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ φ |t|)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s)
      ((Set.Icc (1 - θ T) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ (θ₀ : ℝ) (_ : 0 < θ₀) (σ₂ : ℝ) (_ : 0 < σ₂) (_ : σ₂ < 1) (C : ℝ) (_ : 0 < C),
      ∀ (X : ℝ) (_ : 3 < X) (ε : ℝ) (_ : 0 < ε) (_ : ε < 1) (u : ℝ) (T : ℝ)
        (_ : 3 < T) (_ : 2 * |u| + 3 ≤ T) (_ : φ T ≤ T) (_ : θ T ≤ θ₀),
      ‖twistedSum ν ε X u - mellin (fun x => (Smooth1 ν ε x : ℂ)) (1 - u * Complex.I) *
        (X : ℂ) ^ ((1 : ℂ) - u * Complex.I)‖ ≤
        C * (X * Real.log X / (ε * T) + X ^ (1 - θ T) * φ T / ε + X ^ σ₂ / ε) := by
  obtain ⟨σ₂, σ₂_pos, σ₂_lt_one, h_holo_zeta⟩ := holo_zeta_of_smallT
  let θ₀ := (1 - σ₂) / 2
  have θ₀_pos : 0 < θ₀ := by
    dsimp [θ₀]; linarith
  obtain ⟨C₁, C₁_pos, hJ1⟩ := J1Bound ν diffν suppν νnonneg mass_one
  obtain ⟨C₂, C₂_pos, hJ2⟩ := J2Bound ν diffν suppν θ φ hθ hζ
  obtain ⟨C₃, C₃_pos, hJ3⟩ := J3Bound ν diffν suppν θ φ hθ hθanti hφ hφmono hζ
  obtain ⟨C₄, C₄_pos, hJ4⟩ := J4Bound ν diffν suppν σ₂_pos σ₂_lt_one h_holo_zeta
  obtain ⟨C₅, C₅_pos, hJ5⟩ := J5Bound ν diffν suppν σ₂_pos σ₂_lt_one h_holo_zeta
  obtain ⟨C₆, C₆_pos, hJ6⟩ := J6Bound ν diffν suppν σ₂_pos σ₂_lt_one h_holo_zeta
  obtain ⟨C₇, C₇_pos, hJ7⟩ := J7Bound ν diffν suppν θ φ hθ hθanti hφ hφmono hζ
  obtain ⟨C₈, C₈_pos, hJ8⟩ := J8Bound ν diffν suppν θ φ hθ hζ
  obtain ⟨C₉, C₉_pos, hJ9⟩ := J9Bound ν diffν suppν νnonneg mass_one
  let C := C₁ + C₂ + C₈ + C₉ + C₃ + C₄ + C₆ + C₇ + C₅
  have C_pos : 0 < C := by positivity
  refine ⟨θ₀, θ₀_pos, σ₂, σ₂_pos, σ₂_lt_one, C, C_pos, ?_⟩
  intro X X_gt ε ε_pos ε_lt_one u T T_gt hTu hphi htheta
  let σ₁ := 1 - θ T
  have hT_le : 3 ≤ T := T_gt.le
  have hθT := hθ T hT_le
  have σ₁_lt_one : σ₁ < 1 := by dsimp [σ₁]; linarith [hθT.1]
  have σ₁_pos : 0 < σ₁ := by dsimp [σ₁]; linarith [hθT.2]
  have σ₂_lt_σ₁ : σ₂ < σ₁ := by
    dsimp [σ₁, θ₀] at htheta ⊢
    linarith
  have h_holoT := hholo T hT_le
  have h_holo2 := holoOn2_of_LogDerivZeta ε_pos ε_lt_one X_gt u σ₂_pos suppν νnonneg mass_one diffν h_holo_zeta
  have h_sum := twistedChebyshev_eq_twistedSum ν diffν νnonneg suppν mass_one X_gt ε_pos ε_lt_one u
  have h_pull1 := twistedChebyshevPull1 ν ε_pos ε_lt_one X X_gt (by linarith) σ₁_pos σ₁_lt_one h_holoT suppν νnonneg mass_one diffν u
  have h_pull2 := twistedChebyshevPull2 ν ε_pos ε_lt_one X X_gt T_gt σ₂_pos σ₁_lt_one σ₂_lt_σ₁ h_holoT u h_holo2 suppν νnonneg mass_one diffν
  let main := mellin (fun x => (Smooth1 ν ε x : ℂ)) (1 - u * Complex.I) * (X : ℂ) ^ ((1 : ℂ) - u * Complex.I)
  have h_alg := contour_algebra_decomp ν ε X T σ₁ σ₂ u main h_sum h_pull1 h_pull2
  have h_norm := norm_nine_decomp h_alg
  let A := X * Real.log X / (ε * T)
  let B := X ^ (1 - θ T) * φ T / ε
  let K := X ^ σ₂ / ε
  have hA : 0 ≤ A := by
    dsimp [A]
    have : 0 ≤ Real.log X := (Real.log_pos (by linarith)).le
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    have : 0 ≤ φ T := (hφ T hT_le).trans' (by norm_num)
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]; positivity
  have h1 := hJ1 X X_gt ε ε_pos ε_lt_one u T T_gt hTu
  have h2 := hJ2 X X_gt ε ε_pos ε_lt_one u T T_gt hTu hphi
  have h3 := hJ3 X X_gt ε ε_pos ε_lt_one u T T_gt
  have h4 := hJ4 X X_gt ε ε_pos ε_lt_one u T T_gt θ hθT.1 hθT.2 σ₂_lt_σ₁ φ (hφ T hT_le)
  have h5 := hJ5 X X_gt ε ε_pos ε_lt_one u
  have h6 := hJ6 X X_gt ε ε_pos ε_lt_one u T T_gt θ hθT.1 hθT.2 σ₂_lt_σ₁ φ (hφ T hT_le)
  have h7 := hJ7 X X_gt ε ε_pos ε_lt_one u T T_gt
  have h8 := hJ8 X X_gt ε ε_pos ε_lt_one u T T_gt hTu hphi
  have h9 := hJ9 X X_gt ε ε_pos ε_lt_one u T T_gt hTu
  have h1' : ‖J₁ ν ε X T u‖ ≤ C₁ * A := by
    refine le_trans h1 (le_of_eq ?_)
    dsimp [A]; ring
  have h2' : ‖J₂ ν ε T X (1 - θ T) u‖ ≤ C₂ * A := by
    refine le_trans h2 (le_of_eq ?_)
    dsimp [A]; ring
  have h3' : ‖J₃ ν ε T X (1 - θ T) u‖ ≤ C₃ * B := by
    refine le_trans h3 (le_of_eq ?_)
    dsimp [B]; ring
  have h4' : ‖J₄ ν ε X (1 - θ T) σ₂ u‖ ≤ C₄ * B := by
    refine le_trans h4 (le_of_eq ?_)
    dsimp [B]; ring
  have h5' : ‖J₅ ν ε X σ₂ u‖ ≤ C₅ * K := by
    refine le_trans h5 (le_of_eq ?_)
    dsimp [K]; ring
  have h6' : ‖J₆ ν ε X (1 - θ T) σ₂ u‖ ≤ C₆ * B := by
    refine le_trans h6 (le_of_eq ?_)
    dsimp [B]; ring
  have h7' : ‖J₇ ν ε T X (1 - θ T) u‖ ≤ C₇ * B := by
    refine le_trans h7 (le_of_eq ?_)
    dsimp [B]; ring
  have h8' : ‖J₈ ν ε T X (1 - θ T) u‖ ≤ C₈ * A := by
    refine le_trans h8 (le_of_eq ?_)
    dsimp [A]; ring
  have h9' : ‖J₉ ν ε X T u‖ ≤ C₉ * A := by
    refine le_trans h9 (le_of_eq ?_)
    dsimp [A]; ring
  have h_comb := sum_nine_bounds_le (C₁ := C₁) (C₂ := C₂) (C₃ := C₃) (C₄ := C₄) (C₅ := C₅)
    (C₆ := C₆) (C₇ := C₇) (C₈ := C₈) (C₉ := C₉)
    hA hB hK (by positivity) (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    h1' h2' h3' h4' h5' h6' h7' h8' h9'
  exact le_trans h_norm h_comb

end Erdos1201.MR

