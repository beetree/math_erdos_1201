module

public import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.JensenZeroCountingDistanceBounds

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
Refines the log-derivative bound for `ζ'/ζ` on the strip `1 - δ_t ≤ Re(s) ≤ 3/2`,
`Im(s) = t`, into an explicit `C * (log |t|)^2` estimate with a uniform width
parameter `A`, then transports the "no zero close to the strip" argument to
show the small ball `Y_t(δ_t)` around `1 - δ_t + it` is empty, i.e. contains
no zeros of `ζ`, and that `Y_t(δ)` is always finite.
-/

public section

namespace ZetaZeroFreeRegion

open Complex Topology Filter Interval Set Asymptotics ZetaFunctionEstimates AnalyticZeroCounting

lemma lem_sumKdeltatlogt :
  ∃ C_3 > 1, ∀ (t : ℝ) (ht : |t| > 3),
  let c := (3/2 : ℂ) + I * t;
  ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
      (C_3 / (deltaz_t t)) * Real.log |t| := by
  -- Extract C_2 from lem_sum_m_rho_zeta
  obtain ⟨C_2, hC_2_pos, hC_2_bound⟩ := lem_sum_m_rho_zeta

  -- Use C_3 = C_2
  use C_2

  constructor
  · -- Prove C_3 > 1, which follows from C_2 > 1
    exact hC_2_pos

  · -- Main proof
    intro t ht c hfin z hz

    -- Apply lem_sumK1abs to get the first bound
    have h1 := lem_sumK1abs t ht z hfin hz

    -- Apply lem_sum_m_rho_zeta to get the second bound
    have h2 := hC_2_bound t ht hfin

    -- Get positivity of deltaz_t t
    have ht2 : |t| > 2 := by linarith [ht]
    have h_delta_pos : 0 < deltaz_t t := (lem_delta19.2 t ht2).1

    -- Show that |t| ≥ 1 for log nonnegative
    have h_t_ge_one : (1 : ℝ) ≤ |t| := by linarith [ht]

    -- Combine the bounds
    calc
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖)
        ≤ (1 / (2 * deltaz_t t)) * (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) := h1
      _ ≤ (1 / (2 * deltaz_t t)) * (C_2 * Real.log |t|) := by
          apply mul_le_mul_of_nonneg_left h2
          apply div_nonneg (by norm_num)
          apply mul_nonneg (by norm_num) (le_of_lt h_delta_pos)
      _ = (C_2 / (2 * deltaz_t t)) * Real.log |t| := by ring
      _ ≤ (C_2 / deltaz_t t) * Real.log |t| := by
          apply mul_le_mul_of_nonneg_right _ (Real.log_nonneg h_t_ge_one)
          -- Show C_2 / (2 * deltaz_t t) ≤ C_2 / deltaz_t t
          apply div_le_div_of_nonneg_left (le_of_lt (lt_trans zero_lt_one hC_2_pos))
          · exact h_delta_pos
          · -- Show deltaz_t t ≤ 2 * deltaz_t t
            calc deltaz_t t
              = 1 * deltaz_t t := by rw [one_mul]
            _ ≤ 2 * deltaz_t t := by
              apply mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt h_delta_pos)

lemma lem_sumKlogt2 :
  ∃ C_4 > 1, ∀ (t : ℝ) (ht : |t| > 3),
  let c := (3/2 : ℂ) + I * t
  ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
      C_4 * Real.log |t|^2 := by
  -- Apply lem_sumKdeltatlogt to get C_3
  obtain ⟨C_3, hC_3_gt, hC_3⟩ := lem_sumKdeltatlogt

  -- Define C_4 large enough to absorb constant factors
  use max (100 * C_3 / zerofree_constant) 2

  constructor
  · exact lt_max_of_lt_right (by norm_num : (2 : ℝ) > 1)

  · intro t ht c hfin z hz
    -- Apply the bound from lem_sumKdeltatlogt
    have h_bound := hC_3 t ht hfin z hz

    -- Essential positivity conditions
    have h_t_pos : 0 < |t| := by linarith [ht, abs_nonneg t]
    have h_log_t_pos : 0 < Real.log |t| := Real.log_pos (by linarith [ht] : (1 : ℝ) < |t|)
    have hC_3_pos : 0 < C_3 := lt_trans zero_lt_one hC_3_gt
    have h_zerofree_pos : 0 < zerofree_constant := zerofree_constant_pos

    -- Key bound: log(|t| + 2) ≤ 2 * log|t| for |t| > 3
    have h_log_bound : Real.log (|t| + 2) ≤ 2 * Real.log |t| := by
      have h_ineq : |t| + 2 ≤ 2 * |t| := by linarith [ht]
      have h_log_ineq := Real.log_le_log (by linarith [abs_nonneg t] : 0 < |t| + 2) h_ineq
      rw [Real.log_mul (by norm_num) (ne_of_gt h_t_pos)] at h_log_ineq
      have h_log2_bound : Real.log 2 ≤ Real.log |t| :=
        Real.log_le_log (by norm_num) (by linarith [ht] : (2 : ℝ) ≤ |t|)
      linarith [h_log_ineq]

    -- Use the definition of deltaz_t to bound the key ratio
    have h_deltaz_eq : deltaz_t t = (zerofree_constant / 20) / Real.log (|t| + 2) := by
      simp [deltaz_t, deltaz, Complex.mul_I_im]

    -- The key insight: bound C_3 / deltaz_t t * log|t| using the definition and log bound
    have h_main_bound : C_3 / deltaz_t t * Real.log |t| ≤
                        40 * C_3 / zerofree_constant * (Real.log |t|)^2 := by
      -- Substitute deltaz_t definition
      rw [h_deltaz_eq]

      -- Use basic division properties to rewrite
      have h_div_rewrite : C_3 / ((zerofree_constant / 20) / Real.log (|t| + 2)) =
                          C_3 * Real.log (|t| + 2) * 20 / zerofree_constant := by
        field_simp [ne_of_gt h_zerofree_pos, ne_of_gt (Real.log_pos (by linarith [abs_nonneg t] : (1 : ℝ) < |t| + 2))]

      rw [h_div_rewrite]
      -- Now bound using the logarithm inequality
      have h_pos_factor : 0 ≤ C_3 * 20 / zerofree_constant :=
        div_nonneg (mul_nonneg (le_of_lt hC_3_pos) (by norm_num)) (le_of_lt h_zerofree_pos)

      calc C_3 * Real.log (|t| + 2) * 20 / zerofree_constant * Real.log |t|
          = C_3 * 20 / zerofree_constant * Real.log (|t| + 2) * Real.log |t| := by ring
      _ ≤ C_3 * 20 / zerofree_constant * (2 * Real.log |t|) * Real.log |t| := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h_log_bound h_pos_factor)
                (le_of_lt h_log_t_pos)
      _ = 40 * C_3 / zerofree_constant * (Real.log |t|)^2 := by simp [pow_two]; ring

    -- Final bound using C_4 definition
    calc (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖)
        ≤ C_3 / deltaz_t t * Real.log |t| := h_bound
    _ ≤ 40 * C_3 / zerofree_constant * (Real.log |t|)^2 := h_main_bound
    _ ≤ max (100 * C_3 / zerofree_constant) 2 * (Real.log |t|)^2 := by
        have h_factor_bound : 40 * C_3 / zerofree_constant ≤ max (100 * C_3 / zerofree_constant) 2 := by
          have h_coeff_ineq : 40 * C_3 ≤ 100 * C_3 := by
            -- Use mul_le_mul_of_nonneg_right: if a ≤ b and 0 ≤ c, then a * c ≤ b * c
            have h_coeff : (40 : ℝ) ≤ 100 := by norm_num
            exact mul_le_mul_of_nonneg_right h_coeff (le_of_lt hC_3_pos)
          have h_div_ineq : 40 * C_3 / zerofree_constant ≤ 100 * C_3 / zerofree_constant := by
            -- Apply division monotonicity
            exact div_le_div_of_nonneg_right h_coeff_ineq (le_of_lt h_zerofree_pos)
          exact le_trans h_div_ineq (le_max_left _ _)
        exact mul_le_mul_of_nonneg_right h_factor_bound (sq_nonneg _)


lemma lem_logDerivZetalogt0 :
  ∃ C > 1,
  ∀ (t : ℝ) (ht : |t| > 3),
    ∀ s : ℂ, (1 - deltaz_t t) ≤ s.re ∧ s.re ≤ 3/2 ∧ s.im = t →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ C * Real.log |t|^2 := by
  -- Apply the two main lemmas as stated in the informal proof
  obtain ⟨C_1, hC_1_gt, hC_1⟩ := lem_Zeta_Triangle_ZFR
  obtain ⟨C_4, hC_4_gt, hC_4⟩ := lem_sumKlogt2

  -- Set C = C_1 + C_4
  use C_1 + C_4

  constructor
  · -- Prove C > 1
    linarith [hC_1_gt, hC_4_gt]

  · -- Main proof
    intro t ht s hs

    -- Define the center and get finiteness
    let c := (3/2 : ℂ) + I * t
    have hfin := lem_finiteKzeta t ht

    -- Apply lem_Zeta_Triangle_ZFR
    have h_triangle := hC_1 t ht hfin s hs

    -- Apply lem_triangle_ZFR to bound the sum norm
    have h_triangle_ineq := lem_triangle_ZFR t ht s hfin hs

    -- Apply lem_sumKlogt2 to bound the sum
    have h_sum_bound := hC_4 t ht hfin s hs

    -- Show that log |t| ≤ (log |t|)^2 for |t| > 3
    have h_log_sq_ge : Real.log |t| ≤ Real.log |t|^2 := by
      have h_log_ge_one : (1 : ℝ) ≤ Real.log |t| := by
        -- Since |t| > 3 > e, we have log |t| > log e = 1
        have h_t_gt_e : Real.exp 1 < |t| := by
          have h_e_bound : Real.exp 1 < 3 := by
            -- Use the fact that e < 3 from lem_three_gt_e
            simpa using lem_three_gt_e
          linarith [ht]
        -- Apply log monotonicity: exp 1 ≤ |t| implies 1 ≤ log |t|
        have h_t_pos : 0 < |t| := by linarith [ht, abs_nonneg t]
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (le_of_lt h_t_gt_e)
      have h_log_pos : 0 < Real.log |t| := Real.log_pos (by linarith [ht] : (1 : ℝ) < |t|)
      rw [pow_two]
      exact le_mul_of_one_le_right (le_of_lt h_log_pos) h_log_ge_one

    -- Combine the bounds
    calc ‖deriv riemannZeta s / riemannZeta s‖
        ≤ ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (s - ρ))‖ + C_1 * Real.log |t| := h_triangle
      _ ≤ (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖s - ρ‖) + C_1 * Real.log |t| := by
          linarith [h_triangle_ineq]
      _ ≤ C_4 * Real.log |t|^2 + C_1 * Real.log |t| := by
          linarith [h_sum_bound]
      _ ≤ C_4 * Real.log |t|^2 + C_1 * Real.log |t|^2 := by
          -- Use the fact that log |t| ≤ (log |t|)^2
          have h_c1_nonneg : 0 ≤ C_1 := le_of_lt (lt_trans zero_lt_one hC_1_gt)
          linarith [mul_le_mul_of_nonneg_left h_log_sq_ge h_c1_nonneg]
      _ = (C_4 + C_1) * Real.log |t|^2 := by ring
      _ = (C_1 + C_4) * Real.log |t|^2 := by ring


-- Let t∈ℝ. If z∈ D̄_{2δ_t}(1-δ_t+it) then Re(z) > 1-4δ_t

-- For t∈ℝ with |t|>3 and z∈ D̄_{2δ_t}(1-δ_t+it), we have Re(z) ≥ 1 - 6δ(z)

lemma helper_absIm_le_add_smallball (t : ℝ) (z : ℂ)
  (hz : z ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t)) :
  |z.im| ≤ |t| + 2 * deltaz_t t := by
  -- From membership in the closed ball, we get a bound on the norm of the difference
  have hnorm : ‖z - (1 - deltaz_t t + t * Complex.I)‖ ≤ 2 * deltaz_t t := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  -- The imaginary part of the difference is bounded by its norm
  have h_im_diff : |(z - (1 - deltaz_t t + t * Complex.I)).im| ≤ 2 * deltaz_t t :=
    le_trans (Complex.abs_im_le_norm _) hnorm
  -- Compute the imaginary part of the center
  have center_im : (1 - deltaz_t t + t * Complex.I).im = t := by
    simp [Complex.add_im, Complex.mul_im]
  -- Rewrite the imaginary part of the difference
  have diff_im : (z - (1 - deltaz_t t + t * Complex.I)).im = z.im - t := by
    simp [Complex.sub_im, center_im]
  -- Thus |z.im - t| ≤ 2 δ_t
  have h_im_sub : |z.im - t| ≤ 2 * deltaz_t t := by
    simpa [diff_im] using h_im_diff
  -- Triangle inequality: |z.im| ≤ |z.im - t| + |t|
  have tri : |z.im| ≤ |z.im - t| + |t| := by
    simpa [sub_eq_add_neg] using (abs_add_le (z.im - t) t)
  -- Combine the bounds
  have : |z.im - t| + |t| ≤ 2 * deltaz_t t + |t| := by linarith [h_im_sub]
  have hfinal : |z.im| ≤ 2 * deltaz_t t + |t| := le_trans tri this
  simpa [add_comm] using hfinal


lemma helper_one_div_log_le_two_div_smallball (t : ℝ) (ht : |t| > 3) (z : ℂ)
  (hz : z ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t)) :
  (1 : ℝ) / Real.log (|t| + 2) ≤ 2 / Real.log (|z.im| + 2) := by
  -- Positivity of the logs
  have ht_pos1 : 1 < |t| + 2 := by linarith [abs_nonneg t]
  have hz_pos1 : 1 < |z.im| + 2 := by linarith [abs_nonneg z.im]
  have log_t_pos : 0 < Real.log (|t| + 2) := Real.log_pos ht_pos1
  have log_z_pos : 0 < Real.log (|z.im| + 2) := Real.log_pos hz_pos1
  -- From membership in the closed ball, bound the imaginary part
  have h_norm : ‖z - (1 - deltaz_t t + t * Complex.I)‖ ≤ 2 * deltaz_t t := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  have center_im : (1 - deltaz_t t + t * Complex.I).im = t := by
    simp [Complex.add_im, Complex.mul_I_im]
  have diff_im : (z - (1 - deltaz_t t + t * Complex.I)).im = z.im - t := by
    simp [Complex.sub_im, center_im]
  have h1 : |z.im - t| ≤ ‖z - (1 - deltaz_t t + t * Complex.I)‖ := by
    simpa [diff_im] using Complex.abs_im_le_norm (z - (1 - deltaz_t t + t * Complex.I))
  have h2 : |z.im - t| ≤ 2 * deltaz_t t := h1.trans h_norm
  have hz_im_le : |z.im| ≤ |z.im - t| + |t| := by
    -- |z.im| = |(z.im - t) + t| ≤ |z.im - t| + |t|
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using abs_add_le (z.im - t) t
  have hz_im_le2 : |z.im| ≤ 2 * deltaz_t t + |t| := by linarith [hz_im_le, h2]
  have hz_add2_le1 : |z.im| + 2 ≤ (2 * deltaz_t t + |t|) + 2 := by linarith [hz_im_le2]
  -- Use deltaz_t t < 1 to compare with 2 * (|t| + 2)
  have hdelta_lt_one : deltaz_t t < 1 := by
    have hlt19 : deltaz_t t < 1 / 9 :=
      ((lem_delta19).2 t (by linarith : |t| > 2)).2
    exact lt_trans hlt19 (by norm_num)
  have h2delta_le_two : 2 * deltaz_t t ≤ 2 := by
    have hle : deltaz_t t ≤ 1 := le_of_lt hdelta_lt_one
    have := mul_le_mul_of_nonneg_left hle (by norm_num : (0 : ℝ) ≤ 2)
    simpa using this
  have htwo_le : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have h2delta_le_tplus2 : 2 * deltaz_t t ≤ |t| + 2 := le_trans h2delta_le_two htwo_le
  have step_mid : (2 * deltaz_t t + |t|) + 2 ≤ ((|t| + 2) + |t|) + 2 := by
    have := add_le_add_right (add_le_add_right h2delta_le_tplus2 |t|) 2
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hz_plus2_le : |z.im| + 2 ≤ (|t| + 2) + |t| + 2 := le_trans hz_add2_le1 step_mid
  have hz_im_bound_final : |z.im| + 2 ≤ 2 * (|t| + 2) := by
    -- (|t| + 2) + |t| + 2 = 2*|t| + 4 = 2*(|t|+2)
    simpa [two_mul, add_comm, add_left_comm, add_assoc] using hz_plus2_le
  -- Logarithmic inequality
  have hxpos : 0 < |z.im| + 2 := by linarith [abs_nonneg z.im]
  have hlog_step : Real.log (|z.im| + 2) ≤ Real.log (2 * (|t| + 2)) :=
    Real.log_le_log hxpos hz_im_bound_final
  have hlog_mul : Real.log (2 * (|t| + 2)) = Real.log 2 + Real.log (|t| + 2) := by
    have hneet : (|t| + 2) ≠ 0 := ne_of_gt (lt_trans (by norm_num) ht_pos1)
    simpa using Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hneet
  have hlog2_le_logt : Real.log 2 ≤ Real.log (|t| + 2) := by
    have h2lt : 0 < (2 : ℝ) := by norm_num
    have h2le : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
    exact Real.log_le_log h2lt h2le
  have hlog_le_two : Real.log (|z.im| + 2) ≤ 2 * Real.log (|t| + 2) := by
    have : Real.log (|z.im| + 2) ≤ Real.log 2 + Real.log (|t| + 2) := by
      simpa [hlog_mul] using hlog_step
    have : Real.log (|z.im| + 2) ≤ Real.log (|t| + 2) + Real.log (|t| + 2) := by
      linarith [this, hlog2_le_logt]
    simpa [two_mul] using this
  -- Clear denominators via div_le_div_iff₀
  have h' : 1 * Real.log (|z.im| + 2) ≤ 2 * Real.log (|t| + 2) := by
    simpa [one_mul] using hlog_le_two
  simpa [one_mul] using (div_le_div_iff₀ log_t_pos log_z_pos).mpr h'

lemma helper_deltaz_t_le_two_deltaz_smallball (t : ℝ) (ht : |t| > 3) (z : ℂ)
  (hz : z ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t)) :
  deltaz_t t ≤ 2 * deltaz z := by
  -- Use the key helper lemma to get the reciprocal inequality
  have h_recip := helper_one_div_log_le_two_div_smallball t ht z hz

  -- Multiply both sides by the positive constant (zerofree_constant / 20)
  have hpos_const : 0 ≤ zerofree_constant / 20 := by
    have hpos : 0 < zerofree_constant := zerofree_constant_pos
    have h20 : 0 < (20 : ℝ) := by norm_num
    exact div_nonneg (le_of_lt hpos) (le_of_lt h20)

  have h_mul := mul_le_mul_of_nonneg_left h_recip hpos_const

  calc
    deltaz_t t
        = (zerofree_constant / 20) / Real.log (|t| + 2) := by
              simp [deltaz_t, deltaz, Complex.mul_I_im]
    _ = (zerofree_constant / 20) * (1 / Real.log (|t| + 2)) := by
              simp [div_eq_mul_inv]
    _ ≤ (zerofree_constant / 20) * (2 / Real.log (|z.im| + 2)) := by
              simpa [one_div, div_eq_mul_inv] using h_mul
    _ = 2 * ((zerofree_constant / 20) * (1 / Real.log (|z.im| + 2))) := by
              ring
    _ = 2 * deltaz z := by
              simp [deltaz, div_eq_mul_inv]

lemma lem_DRez6dz :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t),
    z.re ≥ 1 - 6 * deltaz z := by
  intro t ht z hz
  -- From membership in the closed ball: ‖z - (1 - δ_t + t*I)‖ ≤ 2 δ_t
  have h_ball : ‖z - (1 - deltaz_t t + t * Complex.I)‖ ≤ 2 * deltaz_t t := by
    simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
  -- Real part of the difference is bounded by the norm
  have h_re_absle : |(z - (1 - deltaz_t t + t * Complex.I)).re| ≤ 2 * deltaz_t t :=
    (Complex.abs_re_le_norm _).trans h_ball
  have h_re_absle' : |z.re - (1 - deltaz_t t)| ≤ 2 * deltaz_t t := by
    simpa [Complex.sub_re] using h_re_absle
  -- Hence z.re - (1 - δ_t) ≥ -2 δ_t
  have h_lower : z.re - (1 - deltaz_t t) ≥ -(2 * deltaz_t t) := by
    have := (abs_le).1 h_re_absle'
    exact this.1
  -- Therefore z.re ≥ 1 - 3 δ_t
  have h3 : z.re ≥ 1 - 3 * deltaz_t t := by
    linarith
  -- From helper: δ_t ≤ 2 δ(z)
  have h_dt_le : deltaz_t t ≤ 2 * deltaz z :=
    helper_deltaz_t_le_two_deltaz_smallball t ht z hz
  -- Multiply by 3 to get 3 δ_t ≤ 6 δ(z)
  have h_mult : 3 * deltaz_t t ≤ 6 * deltaz z := by
    have h := mul_le_mul_of_nonneg_left h_dt_le (by norm_num : (0 : ℝ) ≤ 3)
    calc
      3 * deltaz_t t ≤ 3 * (2 * deltaz z) := h
      _ = 6 * deltaz z := by ring
  -- Thus 1 - 3 δ_t ≥ 1 - 6 δ(z)
  have h_final : 1 - 3 * deltaz_t t ≥ 1 - 6 * deltaz z := by
    linarith [h_mult]
  -- Combine the inequalities: 1 - 6 δ(z) ≤ 1 - 3 δ_t ≤ z.re
  exact le_trans h_final h3


-- For t∈ℝ with |t|>3 we have Y_t(δ_t) ⊂ D̄_{2δ_t}(1-δ_t+it)

theorem lem_rhoYzero (t : ℝ) (δ : ℝ) (ρ_1 : ℂ) (h_rho_1_in_Yt : ρ_1 ∈ Yt t δ) :
    riemannZeta ρ_1 = 0 := by
  -- Unfold the definition of Yt
  unfold Yt at h_rho_1_in_Yt
  -- h_rho_1_in_Yt : riemannZeta ρ_1 = 0 ∧ norm (ρ_1 - (1 - δ + t * Complex.I)) ≤ 2 * δ
  exact h_rho_1_in_Yt.1

theorem lem_zRe2 (t : ℝ) (δ : ℝ) (z : ℂ)
    (h_le : ‖(z - (1 - δ + t * Complex.I))‖ ≤ 2 * δ) :
    |(z - (1 - δ + t * Complex.I)).re| ≤ 2 * δ := by
  have h1 : |(z - (1 - δ + t * Complex.I)).re| ≤ ‖(z - (1 - δ + t * Complex.I))‖ :=
    Complex.abs_re_le_norm (z - (1 - δ + t * Complex.I))
  exact le_trans h1 h_le

theorem lem_Rezit (t : ℝ) (δ : ℝ) (z : ℂ) :
    (z - (1 - δ + t * Complex.I)).re = z.re - (1 - δ) := by
  rw [Complex.sub_re]
  -- Goal: (1 - δ + t * Complex.I).re = 1 - δ
  rw [Complex.add_re]
  -- Goal: (1 - δ).re + (t * Complex.I).re = 1 - δ
  rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  -- Goal: 1 - δ + (t * Complex.I).re = 1 - δ
  rw [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
  -- Goal: 1 - δ + (t * 0 - 0 * 1) = 1 - δ
  simp

theorem lem_zRe3 (t : ℝ) (δ : ℝ) (z : ℂ)
    (h_le : ‖(z - (1 - δ + t * Complex.I))‖ ≤ 2 * δ) :
    |z.re - (1 - δ)| ≤ 2 * δ := by
  -- Control the real part by the absolute value
  have h1 : |(z - (1 - δ + t * Complex.I)).re| ≤ 2 * δ :=
    lem_zRe2 t δ z h_le
  -- Rewrite the real part explicitly
  have hRe : (z - (1 - δ + t * Complex.I)).re = z.re - (1 - δ) :=
    lem_Rezit t δ z
  simpa [hRe] using h1

/--
Let $\delta >0$ and $z\in \C$. If $|\Re(z)-(1-\delta)| \le \delta/2$ then $\Re(z) \ge 1-\frac{3}{2}\delta$
-/
theorem lem_absrez1d2 (δ : ℝ) (z : ℂ)
    (h_le : |z.re - (1 - δ)| ≤ 2 * δ) :
    z.re ≥ 1 - 3 * δ := by
  -- From |a| ≤ b we get a ≥ -b for real a
  have hneg : z.re - (1 - δ) ≥ - (2 * δ) :=
    (abs_le.mp h_le).1
  -- Rearrange to obtain the desired lower bound
  have : z.re ≥ 1 - δ - 2 * δ := by linarith
  -- 1 - δ - 2 * δ >= 1 - (3/2) * δ
  convert this using 1
  ring
theorem lem_absrez1d3 (δ : ℝ) (z : ℂ) (hδ : δ > 0)
    (h_le : |z.re - (1 - δ)| ≤ 2 * δ) :
    z.re > 1 - 4 * δ := by
  have h1 : z.re ≥ 1 - 3 * δ := lem_absrez1d2 δ z h_le
  linarith [h1, hδ]



lemma lem_zIm2 (t : ℝ) (δ : ℝ) (z : ℂ)
    (h_le : ‖(z - (1 - δ + t * Complex.I))‖ ≤ 2 * δ) :
    |(z - (1 - δ + t * Complex.I)).im| ≤ 2 * δ := by
  have : |(z - (1 - δ + t * Complex.I)).im| ≤ ‖(z - (1 - δ + t * Complex.I))‖ :=
    Complex.abs_im_le_norm (z - (1 - δ + t * Complex.I))
  exact le_trans this h_le

lemma lem_zIm3 (t : ℝ) (δ : ℝ) (z : ℂ)
    (h_le : ‖(z - (1 - δ + t * Complex.I))‖ ≤ 2 * δ) :
    |z.im - t| ≤ 2 * δ := by
  have h1 : |(z - (1 - δ + t * Complex.I)).im| ≤ 2 * δ :=
    lem_zIm2 t δ z h_le
  have him : (z - (1 - δ + t * Complex.I)).im = z.im - t := by
    simpa [Complex.add_im, Complex.mul_im] using
      Complex.sub_im z (1 - δ + t * Complex.I)
  simpa [him] using h1


lemma log_add_lt_log_add_div {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
  Real.log (x + y) < Real.log x + y / x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have hxy_pos : 0 < x + y := add_pos hx hy
  have hxy_ne : x + y ≠ 0 := ne_of_gt hxy_pos
  have hy_div_pos : 0 < y / x := div_pos hy hx
  have hdiv_eq : (x + y) / x = 1 + y / x := by
    have : (x + y) / x = x / x + y / x := by simp [add_div]
    simpa [div_self hxne] using this
  have hgt1 : 1 < (x + y) / x := by
    have : 1 < 1 + y / x := by linarith [hy_div_pos]
    simpa [hdiv_eq] using this
  have hposu : 0 < (x + y) / x := lt_trans zero_lt_one hgt1
  have hne1 : (x + y) / x ≠ 1 := ne_of_gt hgt1
  have hloglt : Real.log ((x + y) / x) < (x + y) / x - 1 :=
    Real.log_lt_sub_one_of_pos hposu hne1
  have hrhs : (x + y) / x - 1 = y / x := by
    have : (1 + y / x) - 1 = y / x := by
      simp
    simp [hdiv_eq]
  have hldiv : Real.log ((x + y) / x) = Real.log (x + y) - Real.log x :=
    Real.log_div hxy_ne hxne
  have hcore : Real.log (x + y) - Real.log x < y / x := by
    simpa [hldiv, hrhs] using hloglt
  have := add_lt_add_right hcore (Real.log x)
  simpa [sub_add_cancel, add_comm, add_left_comm, add_assoc] using this

lemma abs_le_add_of_abs_sub_le' {a b ε : ℝ} (h : |a - b| ≤ ε) :
  |a| ≤ |b| + ε := by
  calc
    |a| = |b + (a - b)| := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    _ ≤ |b| + |a - b| := by
      simpa [sub_eq_add_neg] using abs_add_le b (a - b)
    _ ≤ |b| + ε := by
      linarith [h]





lemma abs_lower_bound_sub (x y : ℝ) : |x| ≥ |y| - |x - y| := by
  -- From |y - x| ≤ |y - x|, apply the helper inequality
  have h' : |y| ≤ |x| + |y - x| := by
    have htriv : |y - x| ≤ |y - x| := le_rfl
    simpa [sub_eq_add_neg] using
      (abs_le_add_of_abs_sub_le' (a := y) (b := x) (ε := |y - x|) htriv)
  -- Rewrite |y - x| as |x - y|
  have h1 : |y| ≤ |x| + |x - y| := by simpa [abs_sub_comm] using h'
  -- Rearrange to get the desired bound
  simpa [ge_iff_le] using (sub_le_iff_le_add).2 h1


lemma lem_Kzetaempty :
  ∀ t : ℝ, |t| > 3 →
    Yt t (deltaz_t t) = ∅ := by
  intro t ht
  -- Use the fact that a set is empty iff no element belongs to it
  rw [Set.eq_empty_iff_forall_notMem]
  intro ρ_1 h_mem
  -- ρ_1 ∈ Yt t (deltaz_t t)
  -- By lem_rhoYzero, we have riemannZeta ρ_1 = 0
  have h_zero : riemannZeta ρ_1 = 0 := lem_rhoYzero t (deltaz_t t) ρ_1 h_mem

  -- From membership in Yt, extract the norm condition
  have h_norm : ‖ρ_1 - (1 - deltaz_t t + t * Complex.I)‖ ≤ 2 * deltaz_t t := by
    exact h_mem.2

  -- Bound the imaginary part: |ρ_1.im - t| ≤ 2 * deltaz_t t
  have h_im_bound : |ρ_1.im - t| ≤ 2 * deltaz_t t := by
    exact lem_zIm3 t (deltaz_t t) ρ_1 h_norm

  -- Since |t| > 3, we can show |ρ_1.im| > 2
  have h_delta_small : deltaz_t t < 1/9 := by
    have h_bounds := lem_delta19
    exact (h_bounds.2 t (by linarith [ht])).2

  have h_im_large : 2 < |ρ_1.im| := by
    -- Use triangle inequality: ||ρ_1.im| - |t|| ≤ |ρ_1.im - t|
    have h_tri : |ρ_1.im| ≥ |t| - |ρ_1.im - t| := by
      exact abs_lower_bound_sub ρ_1.im t
    have h_bound : |ρ_1.im| ≥ |t| - 2 * deltaz_t t := by
      exact ge_trans h_tri (by gcongr)
    have h_small_delta : 2 * deltaz_t t < 2/9 := by
      linarith [h_delta_small]
    have h_final : |t| - 2 * deltaz_t t > 3 - 2/9 := by
      linarith [ht, h_small_delta]
    have h_gt_2 : 3 - 2/9 > 2 := by norm_num
    linarith [h_bound, h_final, h_gt_2]

  -- Get bound on real part from being in the ball
  have h_in_ball : ρ_1 ∈ Metric.closedBall (1 - deltaz_t t + t * Complex.I) (2 * deltaz_t t) := by
    apply Metric.mem_closedBall.mpr
    rwa [Complex.dist_eq]

  have h_re_bound : ρ_1.re ≥ 1 - 6 * deltaz ρ_1 := by
    exact lem_DRez6dz t ht ρ_1 h_in_ball

  -- Apply zero-free region lemma to get contradiction
  have h_delta_pos : 0 < deltaz ρ_1 := by
    have h_bounds := lem_delta19
    exact (h_bounds.1 ρ_1 (by linarith [h_im_large])).1

  have h_re_strict : ρ_1.re > 1 - 9 * deltaz ρ_1 := by
    linarith [h_re_bound, h_delta_pos]

  have h_nonzero : riemannZeta ρ_1 ≠ 0 := by
    exact lem_ZFRdelta ρ_1 h_im_large h_re_strict

  -- This contradicts h_zero
  exact h_nonzero h_zero

lemma Yt_subset_closedBall (t : ℝ) (δ : ℝ) :
    Yt t δ ⊆ Metric.closedBall (1 - δ + t * Complex.I) (2 * δ) := by
  -- Show subset by taking an arbitrary element
  intro ρ_1 hρ_1
  -- hρ_1 tells us ρ_1 is in Yt t δ
  -- Unfold the definition of Yt
  unfold Yt at hρ_1
  -- Extract the second condition: |ρ_1 - (1 - δ + t * Complex.I)| ≤ 2 * δ
  obtain ⟨_, h_abs⟩ := hρ_1
  -- Show membership in closed ball
  rw [Metric.mem_closedBall]
  -- The distance in ℂ is given by Complex.abs
  rw [Complex.dist_eq]
  -- This is exactly our condition
  exact h_abs

lemma Yt_finite (t : ℝ) (δ : ℝ) : (Yt t δ).Finite := by
  -- Yt t δ is a subset of the closed ball
  have h_subset := Yt_subset_closedBall t δ

  -- The closed ball is compact
  let K := Metric.closedBall (1 - δ + t * Complex.I) (2 * δ)
  have h_compact : IsCompact K := ProperSpace.isCompact_closedBall (1 - δ + t * Complex.I) (2 * δ)

  -- The zeros of riemannZeta in this compact set are finite
  have h_zeros_finite := riemannZeta_zeros_finite_of_compact K h_compact

  -- Show that Yt t δ is a subset of {z ∈ K | riemannZeta z = 0}
  have h_sub : Yt t δ ⊆ {z ∈ K | riemannZeta z = 0} := by
    intro ρ hρ
    -- hρ tells us ρ ∈ Yt t δ
    -- From the definition of Yt, we get riemannZeta ρ = 0 and ρ is in the closed ball
    constructor
    · -- ρ is in K (the closed ball)
      exact h_subset hρ
    · -- riemannZeta ρ = 0
      unfold Yt at hρ
      exact hρ.1

  -- A subset of a finite set is finite
  exact Set.Finite.subset h_zeros_finite h_sub

end ZetaZeroFreeRegion
