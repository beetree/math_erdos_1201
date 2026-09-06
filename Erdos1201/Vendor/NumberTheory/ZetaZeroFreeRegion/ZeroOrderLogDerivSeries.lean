module

public import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.ZeroSetExplicitBounds
public import Erdos1201.Vendor.NumberTheory.PNT.MediumPNT
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Dirichlet

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
Bounds the real part of `-logDerivZeta` at points `1 + δ + it` by splitting off the
zero-order term at a candidate zero `ρ` from the finite sum over `ZetaZerosNearPoint`
(`Finset.sum_erase_add`, `lem_Z1splitge*`, `Z1bound`, `Z0boundRe`) and then expresses `-logDerivZeta`
away from the pole at `1` as the von Mangoldt Dirichlet series (`neg_logDeriv_zeta_eq_vonMangoldt_sum`,
`zeta1zetaseries*`), establishing the termwise and real-part summability facts
(`vonMangoldt_LSeriesSummable`, `LSeriesSummable_to_summable`, `ReZconverges1`) needed downstream.
-/

public section

namespace ZetaZeroFreeRegion

open Complex Topology Filter Interval Set Asymptotics ZetaFunctionEstimates AnalyticZeroCounting

lemma lem_Z2bound :
  ∃ C > 1,
     ∀ t : ℝ, 2 < |t| →
      ∀ δ, 0 < δ ∧ δ < 1 →
        (-(logDerivZeta ((1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I))).re
          ≤ C * Real.log (abs t + 2) := by
  -- Start from the explicit bound with log(|2t| + 2)
  obtain ⟨C₁, hC₁_pos, hbound₁⟩ := lem_explicit2Real2

  -- Show a concrete log comparison: log(|2t|+2) ≤ 2*log(|t|+2) for |t| > 3
  have h_log_comp :
      ∀ t : ℝ, 2 < |t| → Real.log (abs (2 * t) + 2) ≤ 2 * Real.log (abs t + 2) := by
    intro t ht
    have h_pos_2t : 0 < abs (2 * t) + 2 := by linarith [abs_nonneg (2 * t)]
    have h_pos_t : 0 < abs t + 2 := by linarith [abs_nonneg t]
    have h_2t_eq : abs (2 * t) = 2 * abs t := by
      rw [abs_mul, abs_two]

    -- For |t| > 3, we have |2t| + 2 = 2|t| + 2 ≤ 4|t| ≤ 4(|t| + 2) when |t| ≥ 2
    have h_bound : abs (2 * t) + 2 ≤ 4 * (abs t + 2) := by
      rw [h_2t_eq]
      -- 2|t| + 2 ≤ 4(|t| + 2) = 4|t| + 8
      linarith [abs_nonneg t]

    have h_4_pos : (0 : ℝ) < 4 := by norm_num
    have h_log_bound : Real.log (abs (2 * t) + 2) ≤ Real.log (4 * (abs t + 2)) :=
      Real.log_le_log h_pos_2t h_bound

    have h_log_mul_eq : Real.log (4 * (abs t + 2)) = Real.log 4 + Real.log (abs t + 2) := by
      exact Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt h_pos_t)

    -- Now use that log(4) ≤ log(|t| + 2) since |t| > 3 implies |t| + 2 > 5 > 4
    have h_4_le : (4 : ℝ) ≤ abs t + 2 := by linarith [ht]
    have h_log_4 : Real.log 4 ≤ Real.log (abs t + 2) :=
      Real.log_le_log (by norm_num) h_4_le

    calc Real.log (abs (2 * t) + 2)
      ≤ Real.log (4 * (abs t + 2)) := h_log_bound
      _ = Real.log 4 + Real.log (abs t + 2) := h_log_mul_eq
      _ ≤ Real.log (abs t + 2) + Real.log (abs t + 2) := by linarith [h_log_4]
      _ = 2 * Real.log (abs t + 2) := by ring

  -- Get positivity from C₁ > 1
  have hC₁_nonneg : 0 ≤ C₁ := le_of_lt (lt_trans zero_lt_one hC₁_pos)

  -- Use C = 2 * C₁
  refine ⟨2 * C₁, ?_, ?_⟩
  · -- Show 2 * C₁ > 1
    linarith [hC₁_pos]
  · -- Main bound
    intro t ht δ hδ
    let s := (1 : ℂ) + (δ : ℝ) + (2 * (t : ℝ)) * Complex.I

    -- From lem_explicit2Real2
    have h1 : (-(logDerivZeta s)).re ≤ C₁ * Real.log (abs (2 * t) + 2) := hbound₁ t ht δ hδ

    -- Apply log comparison
    have h3 : Real.log (abs (2 * t) + 2) ≤ 2 * Real.log (abs t + 2) := h_log_comp t ht

    -- Combine everything
    calc (-(logDerivZeta s)).re
      ≤ C₁ * Real.log (abs (2 * t) + 2) := h1
      _ ≤ C₁ * (2 * Real.log (abs t + 2)) := mul_le_mul_of_nonneg_left h3 hC₁_nonneg
      _ = (2 * C₁) * Real.log (abs t + 2) := by ring





lemma re_ofReal_div_ge_one (a : ℝ) (z : ℂ) (ha : 1 ≤ a) (hz : 0 ≤ (1 / z).re) : ((a : ℂ) / z).re ≥ (1 / z).re := by
  have hrepr : ((a : ℂ) / z).re = a * (1 / z).re := by
    simp [div_eq_mul_inv, Complex.mul_re]
  have hmul : (1 : ℝ) * (1 / z).re ≤ a * (1 / z).re :=
    mul_le_mul_of_nonneg_right ha hz
  calc
    ((a : ℂ) / z).re = a * (1 / z).re := hrepr
    _ ≥ 1 * (1 / z).re := by exact hmul
    _ = (1 / z).re := by simp [one_mul]

lemma riemannZeta_not_eventually_zero_of_ne_one {s : ℂ} (hs : s ≠ 1) :
  ¬ (∀ᶠ z in nhds s, riemannZeta z = 0) := by
  intro hEvZero
  -- Define H(s) = (s - 1) * ζ(s) with the removable singularity at s = 1 filled by H(1) = 1
  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1
  -- H is entire (complex-differentiable everywhere)
  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    · -- at z = 1: removable singularity
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      · -- differentiable on punctured neighborhood of 1
        -- Show eventual differentiability at points t ≠ 1 near 1
        filter_upwards [self_mem_nhdsWithin] with t ht
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta t := by
          -- zeta is differentiable away from 1
          exact differentiableAt_riemannZeta ht
        have hdiff := h1.mul h2
        -- congruence with the updated function away from 1
        apply hdiff.congr_of_eventuallyEq
        filter_upwards [eventually_ne_nhds ht] with u hu
        simp [H, Function.update_of_ne hu]
      · -- continuity at 1 from the known limit
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    · -- at z ≠ 1: equality with (z-1)ζ(z)
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := by
        exact differentiableAt_riemannZeta hz
      have hdiff := h1.mul h2
      -- congruence with H away from the updated point
      apply hdiff.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with u hu
      simp [H, Function.update_of_ne hu]
  -- Hence H is analytic on a neighborhood of every point of the whole space
  have hH_analytic : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff
  -- The zero function is analytic everywhere
  have h0_analytic : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ := by
    intro z _; simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
  -- From eventual vanishing of ζ near s and s ≠ 1, we get eventual vanishing of H near s
  have hEv_ne1 : ∀ᶠ z in nhds s, z ≠ 1 := eventually_ne_nhds hs
  have hEv_H0 : ∀ᶠ z in nhds s, H z = 0 := by
    filter_upwards [hEvZero, hEv_ne1] with z hz_zero hz_ne1
    -- On z ≠ 1, H z = (z - 1) * ζ z = 0
    have : H z = (z - 1) * riemannZeta z := by simp [H, Function.update_of_ne hz_ne1]
    simp [this, hz_zero]
  -- Identity theorem on the connected set univ: H coincides with 0 everywhere
  have hEqOn : Set.EqOn H (fun _ : ℂ => (0 : ℂ)) Set.univ := by
    -- univ is preconnected
    have hU : IsPreconnected (Set.univ : Set ℂ) := by simpa using isPreconnected_univ
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hH_analytic h0_analytic hU (by simp) hEv_H0
  have hHeq : H = fun _ : ℂ => (0 : ℂ) := by
    funext z; simpa using hEqOn (by simp : z ∈ (Set.univ : Set ℂ))
  -- Evaluate at 2 to get a contradiction
  have h2ne1 : (2 : ℂ) ≠ 1 := by norm_num
  have hH2 : H (2 : ℂ) = (2 - 1) * riemannZeta (2 : ℂ) := by
    simp [H, Function.update_of_ne h2ne1]
  have hzeta2_ne : riemannZeta (2 : ℂ) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by simp)
  have hprod_zero' : 0 = (2 - 1) * riemannZeta (2 : ℂ) := by
    simpa [hHeq] using hH2
  have hprod_zero : (2 - 1) * riemannZeta (2 : ℂ) = 0 := hprod_zero'.symm
  have hnonzero : (2 - 1) * riemannZeta (2 : ℂ) ≠ 0 := by
    have hcoeff : (2 : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr h2ne1
    exact mul_ne_zero hcoeff hzeta2_ne
  exact hnonzero hprod_zero

lemma analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero {f : ℂ → ℂ} {z0 : ℂ}
  (hf : AnalyticAt ℂ f z0) (hzero : f z0 = 0)
  (hnot : ¬ (∀ᶠ z in nhds z0, f z = 0)) :
  1 ≤ (analyticOrderAt f z0).toNat := by
  classical
  -- The analytic order is nonzero since f z0 = 0
  have hne0 : analyticOrderAt f z0 ≠ 0 := by
    intro h0
    have hzne : f z0 ≠ 0 := (AnalyticAt.analyticOrderAt_eq_zero hf).1 h0
    exact hzne hzero
  -- The analytic order is not top since f is not eventually zero near z0
  have hneTop : analyticOrderAt f z0 ≠ ⊤ := by
    intro htop
    have hall : (∀ᶠ z in nhds z0, f z = 0) := (analyticOrderAt_eq_top).1 htop
    exact hnot hall
  -- Hence it is a finite natural number n
  rcases ENat.ne_top_iff_exists.mp hneTop with ⟨n, hn⟩
  -- Moreover, it is not zero
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hne0
    -- rewrite analyticOrderAt in terms of n
    rw [← hn, hn0]
    exact Nat.cast_zero
  -- Therefore 1 ≤ n
  have hposn : 1 ≤ n := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_ne_zero)
  -- Conclude for toNat; rewrite using hn
  rw [← hn, ENat.toNat_natCast]
  exact hposn

lemma lem_Z1splitge (delta : ℝ) (hdelta_pos : delta > 0) (hdelta : delta < 1) (rho : ℂ)
  (h_rho_in_zeroZ : rho ∈ zeroZ) (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)) (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) ≥
(1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re := by
  classical
  -- Split off the rho term
  have hsplit :
      Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
        (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
          (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) =
      (((analyticOrderAt riemannZeta rho).toNat : ℂ) /
        (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re +
      Finset.sum ((Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho)
        (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
          (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) := by
    have hmem : rho ∈ Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im) := by
      simpa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using h_rho_in_Zt
    simpa only [add_comm] using
      (Finset.sum_erase_add
        (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
        (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
          (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re)
        hmem).symm
  -- Rewrite the sum using the split
  rw [hsplit]
  -- Show the first term ≥ (1/(...)).re
  have h_rho_ne_one : rho ≠ (1 : ℂ) := by
    intro h
    have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
    exact hz1_ne (by simpa [zeroZ, h] using h_rho_in_zeroZ)
  have hAnal : AnalyticAt ℂ riemannZeta rho := analyticOn_riemannZeta rho h_rho_ne_one
  have hNotEv : ¬ (∀ᶠ z in nhds rho, riemannZeta z = 0) :=
    riemannZeta_not_eventually_zero_of_ne_one h_rho_ne_one
  have horder_nat : 1 ≤ (analyticOrderAt riemannZeta rho).toNat :=
    analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero
      hAnal (by simpa [zeroZ] using h_rho_in_zeroZ) hNotEv
  have ha_real : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta rho).toNat : ℝ) := by exact_mod_cast horder_nat
  have hz_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re :=
    lem_Re1deltatge0 delta hdelta_pos rho.im rho h_rho_in_Zt
  have hfirst :
      (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho)).re
        ≤ (((((analyticOrderAt riemannZeta rho).toNat : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho))).re := by
    -- use re_ofReal_div_ge_one
    simpa [ge_iff_le] using
      (re_ofReal_div_ge_one ((analyticOrderAt riemannZeta rho).toNat : ℝ)
        ((((1 : ℂ) + delta + rho.im * Complex.I) - rho)) ha_real hz_nonneg)
  -- Next, show the remaining sum is ≥ 0
  have hsum_nonneg :
      0 ≤ Finset.sum
        ((Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im)).erase rho)
        (fun rho1 : ℂ =>
          (((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re) := by
    apply Finset.sum_nonneg
    intro rho1 hmem
    rcases Finset.mem_erase.mp hmem with ⟨_, hmemS⟩
    -- membership in the original set
    have hZt : rho1 ∈ ZetaZerosNearPoint rho.im := by
      simpa [Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite rho.im)] using hmemS
    -- Show rho1 ≠ 1
    have hne1 : rho1 ≠ (1 : ℂ) := by
      intro h
      have hz1_ne : riemannZeta (1 : ℂ) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
      have hzero1 : riemannZeta rho1 = 0 := hZt.1
      exact hz1_ne (by simpa [h] using hzero1)
    -- Order at rho1 is ≥ 1
    have hAnal1 : AnalyticAt ℂ riemannZeta rho1 := analyticOn_riemannZeta rho1 hne1
    have hNotEv1 : ¬ (∀ᶠ z in nhds rho1, riemannZeta z = 0) :=
      riemannZeta_not_eventually_zero_of_ne_one hne1
    have hzero1 : riemannZeta rho1 = 0 := hZt.1
    have horder1 : 1 ≤ (analyticOrderAt riemannZeta rho1).toNat :=
      analyticOrderAt_pos_toNat_of_zero_of_analytic_not_eventually_zero hAnal1 hzero1 hNotEv1
    have ha1_real : (1 : ℝ) ≤ ((analyticOrderAt riemannZeta rho1).toNat : ℝ) := by exact_mod_cast horder1
    -- (1/(...)).re ≥ 0
    have hz1_nonneg : 0 ≤ (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re :=
      lem_Re1deltatge0 delta hdelta_pos rho.im rho1 hZt
    -- Lower bound: (1/z).re ≤ ((a:ℂ)/z).re
    have hge :
        (1 / (((1 : ℂ) + delta + rho.im * Complex.I) - rho1)).re ≤
          (((((analyticOrderAt riemannZeta rho1).toNat : ℝ) : ℂ) /
            (((1 : ℂ) + delta + rho.im * Complex.I) - rho1))).re := by
      simpa [ge_iff_le] using
        (re_ofReal_div_ge_one ((analyticOrderAt riemannZeta rho1).toNat : ℝ)
          ((((1 : ℂ) + delta + rho.im * Complex.I) - rho1)) ha1_real hz1_nonneg)
    -- Thus the target real part is ≥ 0 by transitivity
    exact le_trans hz1_nonneg hge
  -- Combine the two bounds
  have h := add_le_add hfirst hsum_nonneg
  -- simplify right-hand side
  simpa using h


lemma lem_1deltatrho0 (delta : ℝ) (_hdelta : delta > 0) (rho : ℂ) (_h_rho_in_zeroZ : rho ∈ zeroZ) :
((1 : ℂ) + delta + rho.im * Complex.I - rho) = ((1 : ℝ) + delta - rho.re) := by
  -- The key insight: rho = rho.re + rho.im * Complex.I
  -- So: (1 + delta + rho.im * I) - rho = (1 + delta + rho.im * I) - (rho.re + rho.im * I)
  --     = 1 + delta + rho.im * I - rho.re - rho.im * I
  --     = 1 + delta - rho.re
  calc (1 : ℂ) + delta + rho.im * Complex.I - rho
    = (1 : ℂ) + delta + rho.im * Complex.I - (rho.re + rho.im * Complex.I) := by rw [Complex.re_add_im]
  _ = (1 : ℂ) + delta - rho.re := by ring
  _ = ((1 : ℝ) + delta - rho.re : ℂ) := by norm_cast

lemma lem_1delsigReal (delta : ℝ) (hdelta_pos : delta > 0) (hdelta : delta < 1) (rho : ℂ) (h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta + rho.im * Complex.I - rho)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
  rw [lem_1deltatrho0 delta hdelta_pos rho h_rho_in_zeroZ]
  -- After applying lem_1deltatrho0, we have:
  -- (1 / (↑1 + ↑delta - ↑rho.re)).re = 1 / (1 + delta - rho.re)

  -- The key is to rewrite (↑1 + ↑delta - ↑rho.re) as ↑(1 + delta - rho.re)
  rw [← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_one]
  -- Now we have (1 / ↑(1 + delta - rho.re)).re = 1 / (1 + delta - rho.re)

  -- Apply Complex.div_ofReal_re
  rw [Complex.div_ofReal_re]
  -- This gives us (1 : ℂ).re / (1 + delta - rho.re) = 1 / (1 + delta - rho.re)
  rw [Complex.ofReal_re]



lemma lem_re_inv_one_plus_delta_minus_rho_real (delta : ℝ) (hdelta : delta > 0)  (rho : ℂ) (h_rho_in_zeroZ : rho ∈ zeroZ) :
(1 / ((1 : ℂ) + delta + rho.im * Complex.I - rho)).re = 1 / ((1 : ℝ) + delta - rho.re) := by
  -- Apply lem_1deltatrho0 to simplify the denominator
  rw [lem_1deltatrho0 delta hdelta rho h_rho_in_zeroZ]
  -- Rewrite the real cast so Complex.div_ofReal_re applies
  rw [← Complex.ofReal_add, ← Complex.ofReal_sub, ← Complex.ofReal_one]
  rw [Complex.div_ofReal_re, Complex.ofReal_re]

lemma lem_Z1splitge2 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (rho : ℂ)
  (h_rho_in_zeroZ : rho ∈ zeroZ) (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint rho.im) :
    Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite rho.im))
      (fun rho1 : ℂ => (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / ((1 : ℂ) + delta + rho.im * Complex.I - rho1)).re) ≥
1 / ((1 : ℝ) + delta - rho.re) := by
  -- Apply lem_Z1splitge to get the first inequality
  have h1 := lem_Z1splitge delta hdelta hdelta_lt_1 rho h_rho_in_zeroZ h_rho_in_Zt
  -- Apply lem_re_inv_one_plus_delta_minus_rho_real to rewrite the right-hand side
  have h2 := lem_re_inv_one_plus_delta_minus_rho_real delta hdelta rho h_rho_in_zeroZ
  -- Combine the results
  rw [← h2]
  exact h1

lemma lem_Z1splitge3 (delta : ℝ) (hdelta : delta > 0) (hdelta_lt_1 : delta < 1) (sigma t : ℝ) (rho : ℂ)
  (h_rho_eq : rho = sigma + t * Complex.I) (h_rho_in_zeroZ : rho ∈ zeroZ)
  (h_rho_in_Zt : rho ∈ ZetaZerosNearPoint t) :
(Finset.sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t)) (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (((1 : ℂ) + delta + t * Complex.I) - rho1)) ).re ≥ 1 / ((1 : ℝ) + delta - sigma) := by
  -- Convert the real part of the sum to the sum of real parts
  rw [Complex.re_sum]

  -- Extract rho.im = t and rho.re = sigma from h_rho_eq
  have h_rho_im : rho.im = t := by
    rw [h_rho_eq]
    simp [Complex.add_im, Complex.mul_im, Complex.I_im]
  have h_rho_re : rho.re = sigma := by
    rw [h_rho_eq]
    simp [Complex.add_re, Complex.mul_re, Complex.I_re]

  -- Since rho.im = t, we have rho ∈ ZetaZerosNearPoint rho.im
  have h_rho_in_Zt' : rho ∈ ZetaZerosNearPoint rho.im := by
    rw [h_rho_im]
    exact h_rho_in_Zt

  -- Apply lem_Z1splitge2
  have h_bound := lem_Z1splitge2 delta hdelta hdelta_lt_1 rho h_rho_in_zeroZ h_rho_in_Zt'

  -- Since rho.im = t and rho.re = sigma, we can convert the bound
  convert h_bound using 1
  -- Show the sums are equal by substituting rho.im = t
  simp_rw [← h_rho_im]
  -- Show the bounds are equal by substituting rho.re = sigma
  rw [h_rho_re]


lemma Z1bound :
  ∃ C > 1,
    ∀ (delta : ℝ), (0 < delta ∧ delta < 1) →
      ∀ t : ℝ, 2 < |t| →
        ∀ s : ℂ, s ∈ zeroZ ∧ s.im = t →
          (-(logDerivZeta ((1 : ℂ) + delta + t * Complex.I))).re
            ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
  classical
  -- Start from the explicit real-part bound
  obtain ⟨C0, hC0gt1, hExp⟩ := lem_explicit1RealReal
  -- Choose a global constant C ≥ C0 and large enough to absorb a fixed constant 3
  have hlog5pos : 0 < Real.log 4 := Real.log_pos (by norm_num : (1 : ℝ) < 4)
  let C : ℝ := max (C0 + 3 / Real.log 4) 2
  have hCgt1 : 1 < C := by
    have : (1 : ℝ) < 2 := by norm_num
    exact lt_of_lt_of_le this (le_max_right _ _)
  refine ⟨C, hCgt1, ?_⟩
  intro delta hdelta t ht s hs
  -- Abbreviations
  set sp : ℂ := (1 : ℂ) + delta + t * Complex.I
  set S : Finset ℂ := Set.Finite.toFinset (ZetaZerosNearPoint_finite t)
  set Sre : ℝ :=
    Finset.sum S
      (fun rho1 : ℂ =>
        (((analyticOrderAt riemannZeta rho1).toNat : ℂ) / (sp - rho1)).re)
  -- From explicit bound: |(logDerivZeta sp).re - Sre| ≤ C0 * log(|t|+2)
  have h_bound : abs ((logDerivZeta sp).re - Sre)
        ≤ C0 * Real.log (abs t + 2) := by
    simpa [sp, S, Sre] using hExp t ht delta hdelta
  -- Isolate - (logDerivZeta sp).re using Sre and the triangle inequality
  have h_left : -(C0 * Real.log (abs t + 2)) ≤ (logDerivZeta sp).re - Sre :=
    (abs_le.mp h_bound).1
  have h_neg : -((logDerivZeta sp).re - Sre) ≤ C0 * Real.log (abs t + 2) := by
    simpa using neg_le_neg h_left
  have h_isol : - (logDerivZeta sp).re ≤ C0 * Real.log (abs t + 2) - Sre := by
    have := sub_le_sub_right h_neg Sre
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Show Sre ≥ 0 using nonnegativity termwise
  have hS_nonneg : 0 ≤ Sre := by
    apply Finset.sum_nonneg
    intro rho1 hmem
    have hZt : rho1 ∈ ZetaZerosNearPoint t := by
      simpa [S, Set.Finite.mem_toFinset (ZetaZerosNearPoint_finite t)] using hmem
    -- Each term's real part is ≥ 0
    simpa [sp] using
      (lem_Re1deltatge0m delta hdelta.1 t hdelta.2 rho1 hZt)
  -- Basic bound with Sre dropped
  have h_basic : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) := by
    have h_drop : C0 * Real.log (abs t + 2) - Sre ≤ C0 * Real.log (abs t + 2) :=
      sub_le_self _ hS_nonneg
    exact le_trans h_isol h_drop
  -- Split on whether s ∈ ZetaZerosNearPoint t
  by_cases hmem : s ∈ ZetaZerosNearPoint t
  · -- Case 1: s ∈ Z_t; use the strong lower bound Sre ≥ 1/(1+δ-σ)
    set sigma : ℝ := s.re
    have h_rho_eq : s = (sigma : ℂ) + t * Complex.I := by
      have : s = s.re + s.im * Complex.I := by simp [Complex.re_add_im]
      simpa [sigma, hs.2] using this
    -- Real-part of the complex sum equals Sre
    have hsum_rew := Complex.re_sum (Set.Finite.toFinset (ZetaZerosNearPoint_finite t))
      (fun rho1 : ℂ => ((analyticOrderAt riemannZeta rho1).toNat : ℂ) /
        (((1 : ℂ) + delta + t * Complex.I) - rho1))
    have h_sum_ge' :=
      lem_Z1splitge3 delta hdelta.1 hdelta.2 sigma t s h_rho_eq hs.1 hmem
    have h_sum_ge : Sre ≥ 1 / ((1 : ℝ) + delta - sigma) := by
      simpa [sp, S, Sre, hsum_rew] using h_sum_ge'
    -- Chain inequalities: -(logDerivZeta sp).re ≤ C0*log - Sre ≤ C0*log - 1/(...)
    have h1 : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) := by
      have : (1 / ((1 : ℝ) + delta - sigma)) ≤ Sre := h_sum_ge
      have := sub_le_sub_left this (C0 * Real.log (abs t + 2))
      exact le_trans h_isol (by simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this)
    -- Enlarge C0 to C on the logarithmic term
    have hCge : C0 ≤ C :=
      le_trans (by
        have : 0 ≤ 3 / Real.log 4 := le_of_lt (div_pos (by norm_num) hlog5pos)
        have := add_le_add_left this C0
        simpa using this) (le_max_left _ _)
    -- log(|t|+2) ≥ 0 since |t| > 3
    have hY_nonneg : 0 ≤ Real.log (abs t + 2) := by
      have h2le : (2 : ℝ) ≤ abs t + 2 := by
        have h0 : 0 ≤ |t| := abs_nonneg t
        simp [add_comm]
      exact le_of_lt (Real.log_pos (lt_of_lt_of_le (by norm_num) h2le))
    have h_enlarge : C0 * Real.log (abs t + 2) ≤ C * Real.log (abs t + 2) :=
      mul_le_mul_of_nonneg_right hCge hY_nonneg
    have h2 : C0 * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) ≤
              C * Real.log (abs t + 2) - (1 / ((1 : ℝ) + delta - sigma)) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (sub_le_sub_right h_enlarge (1 / ((1 : ℝ) + delta - sigma)))
    have := le_trans h1 h2
    simpa [sp, sigma, Complex.neg_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using this
  · -- Case 2: s ∉ Z_t. Use geometry to bound 1/(1+δ - s.re) ≤ 3 and then absorb the constant.
    -- s is a zero with imaginary part t, so the distance condition must fail
    have h_notle : ¬ ‖s - ((3/2 : ℂ) + t * Complex.I)‖ ≤ (5/6 : ℝ) := by
      intro hle
      exact hmem ⟨hs.1, hle⟩
    have hdist_gt : (5/6 : ℝ) < ‖s - ((3/2 : ℂ) + t * Complex.I)‖ := not_le.mp h_notle
    -- Compute the distance as a real absolute value: the difference has zero imaginary part
    have h_re : (s - ((3/2 : ℂ) + t * Complex.I)).re = s.re - (3/2 : ℝ) := by
      simp [Complex.sub_re, Complex.add_re]
    have h_im : (s - ((3/2 : ℂ) + t * Complex.I)).im = 0 := by
      have : (s - ((3/2 : ℂ) + t * Complex.I)).im = s.im - t := by
        simp [Complex.sub_im, Complex.add_im]
      simp [hs.2]
    have h_eq : s - ((3/2 : ℂ) + t * Complex.I) = (((s.re - (3/2 : ℝ)) : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [h_re]
      · simp [h_im]
    have hdist_real : ‖s - ((3/2 : ℂ) + t * Complex.I)‖ = |s.re - (3/2 : ℝ)| := by
      simpa [h_eq, Real.norm_eq_abs] using Complex.norm_real (s.re - (3/2 : ℝ))
    have habs_gt : (5/6 : ℝ) < |s.re - (3/2 : ℝ)| := by simpa [hdist_real] using hdist_gt
    -- Zeta zero implies s.re ≤ 1
    have h0 : riemannZeta (s.re + s.im * Complex.I) = 0 := by
      simpa [zeroZ, Complex.re_add_im] using hs.1
    have hs_le1 : s.re ≤ 1 := le_of_not_gt fun hgt =>
      (riemannZeta_ne_zero_of_one_le_re (s := s.re + s.im * Complex.I)
        (by simpa using hgt.le)) h0
    -- Thus s.re - 3/2 ≤ 0, so |s.re - 3/2| = 3/2 - s.re
    have h_nonpos : s.re - (3/2 : ℝ) ≤ 0 := by linarith [hs_le1]
    have h_abs_eq : |s.re - (3/2 : ℝ)| = (3/2 : ℝ) - s.re := by
      have : |s.re - (3/2 : ℝ)| = -(s.re - (3/2 : ℝ)) := abs_of_nonpos h_nonpos
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h_gt' : (5/6 : ℝ) < (3/2 : ℝ) - s.re := by simpa [h_abs_eq] using habs_gt
    have hs_le_23 : s.re ≤ (2/3 : ℝ) := by linarith [h_gt']
    -- Hence denominator is bounded below by 1/3, giving 1/(...) ≤ 3
    have hden_ge : (1/3 : ℝ) ≤ 1 + delta - s.re := by
      have : (1/3 : ℝ) ≤ 1 - s.re := by linarith [hs_le_23]
      have : 1 - s.re ≤ 1 + delta - s.re := by linarith [hdelta.1]
      exact le_trans ‹(1/3 : ℝ) ≤ 1 - s.re› this
    have hone_div_le3 : 1 / (1 + delta - s.re) ≤ (3 : ℝ) := by
      have : 1 / (1 + delta - s.re) ≤ 1 / (1/3 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1/3) hden_ge
      simpa [one_div] using this
    have hneg_ge : - (3 : ℝ) ≤ - (1 / (1 + delta - s.re)) := by
      simpa using (neg_le_neg hone_div_le3)
    -- Compare logs to absorb the constant 3
    have hlog_ge : Real.log 4 ≤ Real.log (abs t + 2) := by
      have : (4 : ℝ) < abs t + 2 := by linarith [ht]
      exact Real.log_le_log (by norm_num) (le_of_lt this)
    have hC_ge_add : C ≥ C0 + 3 / Real.log 4 := by exact le_max_left _ _
    have hCminus : C - C0 ≥ 3 / Real.log 4 := by linarith
    have hY_nonneg : 0 ≤ Real.log (abs t + 2) := by
      have h2le : (2 : ℝ) ≤ abs t + 2 := by
        have h0 : 0 ≤ |t| := abs_nonneg t
        simp [add_comm]
      exact le_of_lt (Real.log_pos (lt_of_lt_of_le (by norm_num) h2le))
    have hmul1 : (3 / Real.log 4) * Real.log 4 ≤ (3 / Real.log 4) * Real.log (abs t + 2) := by
      have hk_nonneg : 0 ≤ 3 / Real.log 4 := le_of_lt (div_pos (by norm_num) hlog5pos)
      exact mul_le_mul_of_nonneg_left hlog_ge hk_nonneg
    have hmul2 : (3 / Real.log 4) * Real.log (abs t + 2) ≤ (C - C0) * Real.log (abs t + 2) := by
      exact mul_le_mul_of_nonneg_right hCminus hY_nonneg
    have hmul_ge3 : (3 : ℝ) ≤ (C - C0) * Real.log (abs t + 2) := by
      have hne5 : Real.log 4 ≠ 0 := ne_of_gt hlog5pos
      have hcalc : (3 / Real.log 4) * Real.log 4 = 3 := by
        simp [div_eq_mul_inv, hne5]
      have : (3 / Real.log 4) * Real.log 4 ≤ (C - C0) * Real.log (abs t + 2) :=
        le_trans hmul1 hmul2
      simpa [hcalc] using this
    -- Now C * log ≥ C0 * log + 3
    have hCmul' : C0 * Real.log (abs t + 2) + 3 ≤ C * Real.log (abs t + 2) := by
      have : C0 * Real.log (abs t + 2) + 3 ≤ C0 * Real.log (abs t + 2) + (C - C0) * Real.log (abs t + 2) := by
        linarith [hmul_ge3]
      have hcalc : C * Real.log (abs t + 2) =
          C0 * Real.log (abs t + 2) + (C - C0) * Real.log (abs t + 2) := by
        ring
      simpa [hcalc, add_comm, add_left_comm, add_assoc] using this
    -- Combine: from basic bound and the constant absorption and -1/(...) ≥ -3
    have : (-(logDerivZeta sp)).re ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
      have h1 : (-(logDerivZeta sp)).re ≤ C0 * Real.log (abs t + 2) := h_basic
      have h2 : C0 * Real.log (abs t + 2) ≤ C * Real.log (abs t + 2) - 3 := by
        linarith [hCmul']
      have h3 : C * Real.log (abs t + 2) - 3 ≤ - (1 / (1 + delta - s.re)) + C * Real.log (abs t + 2) := by
        have := add_le_add_right hneg_ge (C * Real.log (abs t + 2))
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
      exact le_trans h1 (le_trans h2 h3)
    simpa [sp, Complex.neg_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this


lemma Z0boundRe :
Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) (fun (delta : ℝ) => (- (logDerivZeta ((1 : ℂ) + delta))).re - (1 / delta)) (fun _ => (1 : ℝ)) := by
  -- From Z0bound, we have the complex version
  have h := Z0bound

  -- Show that our function equals the real part of the function in Z0bound
  have h_eq : (fun (delta : ℝ) => (- (logDerivZeta ((1 : ℂ) + delta))).re - (1 / delta)) =
              (fun (delta : ℝ) => (-logDerivZeta ((1 : ℂ) + delta) - (1 / (delta : ℂ))).re) := by
    ext delta
    rw [Complex.sub_re, Complex.neg_re]
    -- Show that (1 / (delta : ℂ)).re = 1 / delta
    have : (1 / (delta : ℂ)).re = 1 / delta := by
      rw [Complex.div_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im]
      simp [Complex.normSq_ofReal]
    rw [this]

  rw [h_eq]

  -- Now apply the general principle: if f =O[l] g, then f.re =O[l] ‖g‖
  -- Since |z.re| ≤ |z| for any complex z
  rw [Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c
  filter_upwards [hc] with delta h_delta
  have : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
  rw [this] at h_delta
  have : ‖(1 : ℝ)‖ = (1 : ℝ) := by simp
  rw [this]
  exact le_trans (Complex.abs_re_le_norm _) h_delta









lemma absorb_pos_constant_into_log {L A c : ℝ} (hL : 1 ≤ L) (hc : 0 ≤ c) : A * L + c ≤ (A + c) * L := by
  -- Since 1 ≤ L and c ≥ 0, we have c ≤ L * c
  have hc_le : c ≤ L * c := by
    have h := mul_le_mul_of_nonneg_right hL hc
    simpa [one_mul] using h
  -- Add A * L to both sides and rewrite
  have h0 : A * L + c ≤ A * L + L * c := by
    linarith [hc_le]
  calc
    A * L + c ≤ A * L + L * c := h0
    _ = A * L + c * L := by simp [mul_comm]
    _ = (A + c) * L := by simp [right_distrib]


lemma neg_logDeriv_zeta_eq_vonMangoldt_sum (s : ℂ) (hs : 1 < s.re) : -(deriv riemannZeta s / riemannZeta s) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
  -- Reuse the Dirichlet-series identification already proved in MediumPNT, modulo
  -- `a / n ^ s` vs `a * n ^ (-s)`.
  rw [← neg_div, LogDerivativeDirichlet s hs]
  exact tsum_congr fun n => by rw [div_eq_mul_inv, Complex.cpow_neg]

lemma zeta1zetaseries {s : ℂ} (hs : 1 < s.re) :
-logDerivZeta s = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold logDerivZeta
  -- Goal: -(deriv riemannZeta s / riemannZeta s) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-s)
  exact neg_logDeriv_zeta_eq_vonMangoldt_sum s hs

lemma complex_re_of_real_add_imag (x y : ℝ) : (x + y * I).re = x := by
  simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]

lemma zeta1zetaseriesxy (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I)) := by
  apply zeta1zetaseries
  rw [complex_re_of_real_add_imag]
  exact hx

lemma Zconverges1 (x y : ℝ) (hx : 1 < x) : riemannZeta (x + y * I) ≠ 0 := by
  apply riemannZeta_ne_zero_of_one_lt_re
  simpa [Complex.add_re, Complex.mul_re] using hx

lemma summable_of_support_singleton {α : Type*} [SeminormedAddCommGroup α] (f : ℕ → α) (n₀ : ℕ) (h : ∀ n : ℕ, n ≠ n₀ → f n = 0) : Summable f := by
  -- Show that f has finite support, so it's summable
  have h_finite_support : Set.Finite (Function.support f) := by
    -- The support is contained in {n₀}
    have h_subset : Function.support f ⊆ {n₀} := by
      intro n hn
      -- hn : n ∈ Function.support f means f n ≠ 0
      -- We need to show n ∈ {n₀}, i.e., n = n₀
      by_contra h_ne
      -- If n ≠ n₀, then by hypothesis h, f n = 0
      have h_zero : f n = 0 := h n h_ne
      -- But this contradicts f n ≠ 0
      simp [Function.mem_support] at hn
      exact hn h_zero
    -- Since support ⊆ {n₀} and {n₀} is finite, support is finite
    exact Set.Finite.subset (Set.finite_singleton n₀) h_subset

  -- Use the fact that functions with finite support are summable
  exact summable_of_hasFiniteSupport h_finite_support

lemma summable_of_summable_add_sub {α : Type*} [SeminormedAddCommGroup α] (f g h : ℕ → α) (h_eq : f = g + h) (hf : Summable f) (hh : Summable h) : Summable g := by
  -- Since f = g + h, we have g = f - h
  -- To show this, we use that if a = b + c in an additive group, then b = a - c

  -- First, show that g = f - h
  have g_eq_f_sub_h : g = f - h := by
    -- Use that f = g + h implies g = f - h
    rw [← sub_eq_iff_eq_add] at h_eq
    exact h_eq.symm

  -- Now rewrite the goal using this equality
  rw [g_eq_f_sub_h]

  -- Use that the difference of summable functions is summable
  -- This follows from f - h = f + (-h) and Summable.add
  exact hf.sub hh

lemma LSeriesSummable_to_summable (f : ℕ → ℂ) (s : ℂ) (h : LSeriesSummable f s) : Summable (fun n => f n * (n : ℂ) ^ (-s)) := by
  -- LSeriesSummable f s means Summable (LSeries.term f s)
  have h_term_summable : Summable (LSeries.term f s) := h

  -- For n ≠ 0, the two functions are equal
  have h_eq_nonzero : ∀ n : ℕ, n ≠ 0 → LSeries.term f s n = f n * (n : ℂ) ^ (-s) := by
    intro n hn
    rw [LSeries.term_of_ne_zero hn]
    rw [div_eq_mul_inv, Complex.cpow_neg]

  -- The difference function is summable (it's non-zero at most at n = 0)
  let diff := fun n => LSeries.term f s n - f n * (n : ℂ) ^ (-s)

  have h_diff_support : ∀ n : ℕ, n ≠ 0 → diff n = 0 := by
    intro n hn
    simp only [diff]
    rw [h_eq_nonzero n hn]
    simp

  have h_diff_summable : Summable diff := by
    -- The support of diff is contained in {0}
    apply summable_of_support_singleton diff 0 h_diff_support

  -- Since LSeries.term f s = (target function) + diff, and both LSeries.term and diff are summable,
  -- the target function is summable
  have h_rw : LSeries.term f s = (fun n => f n * (n : ℂ) ^ (-s)) + diff := by
    ext n
    simp only [diff, Pi.add_apply]
    ring

  -- Use the fact that if f = g + h and both f and h are summable, then g is summable
  exact summable_of_summable_add_sub (LSeries.term f s) (fun n => f n * (n : ℂ) ^ (-s)) diff h_rw h_term_summable h_diff_summable

lemma ReZconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) := by
  -- Apply Lemma Zconverge1 (ensures zeta function is non-zero, so logDerivZeta is well-defined)
  have h_nonzero : riemannZeta (x + y * I) ≠ 0 := Zconverges1 x y hx

  -- Use the fact that the von Mangoldt L-series is summable for Re(s) > 1
  have h_re_gt_one : 1 < (x + y * I).re := by
    rw [complex_re_of_real_add_imag]
    exact hx

  -- The von Mangoldt L-series is summable
  have h_L_summable : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt h_re_gt_one

  -- Convert L-series summability to summability of our terms
  have h_summable : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    LSeriesSummable_to_summable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) h_L_summable

  -- If a complex function is summable, then its real part is summable
  have h_hasSum : HasSum (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))) :=
    h_summable.hasSum

  -- Use Complex.hasSum_re to get HasSum for real parts
  have h_hasSum_re : HasSum (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re) (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x + y * I))).re :=
    Complex.hasSum_re h_hasSum

  -- Convert HasSum to Summable
  exact h_hasSum_re.summable

end ZetaZeroFreeRegion
