module

public import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.ZeroFreeRegionExistence

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
Distance and multiplicity bounds for zeros of `riemannZeta` inside the small
disks `D̄(3/2+it, 5/6)` used in the zero-free region argument: relating
`Im(z)` on the disk to `|t|`, bounding `δ_t` against `δ(z)`, bounding
`|z-ρ|` from below and `Re(ρ)` from above for zeros `ρ`, and (via a
disk-shift Jensen's-formula argument) bounding the number of zeros
(with multiplicity) of `riemannZeta` in `D̄(3/2+it, 5/6)` by `C_2 log|t|`.
-/

public section

namespace ZetaZeroFreeRegion

open Complex Topology Filter Interval Set Asymptotics ZetaFunctionEstimates AnalyticZeroCounting

lemma lem_DImt2d :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    |z.im| ≤ |t| + 5/6 := by
  intro t ht z hz
  -- z is in the closed ball, so ‖z - (3/2 + t * Complex.I)‖ ≤ 5/6
  rw [Metric.mem_closedBall] at hz
  -- The center has imaginary part t
  have center_im : (3/2 + t * Complex.I).im = t := by simp [Complex.add_im, Complex.one_im, Complex.mul_im]
  -- So (z - center).im = z.im - t
  have diff_im : (z - (3/2 + t * Complex.I)).im = z.im - t := by
    rw [Complex.sub_im, center_im]
  -- We know |z.im - t| ≤ ‖z - center‖
  have h1 : |z.im - t| ≤ ‖z - (3/2 + t * Complex.I)‖ := by
    rw [← diff_im]
    exact Complex.abs_im_le_norm _
  -- Combining with the ball constraint
  have h2 : |z.im - t| ≤ 5/6 := by
    rw [Complex.dist_eq] at hz
    exact le_trans h1 hz
  -- Use triangle inequality: since z.im = (z.im - t) + t, we have |z.im| ≤ |z.im - t| + |t|
  have h3 : |z.im| ≤ |z.im - t| + |t| := by
    conv_lhs => rw [show z.im = (z.im - t) + t by ring]
    exact abs_add_le (z.im - t) t
  linarith

-- For t∈ℝ with |t|>3 and z∈ D̄_{2δ_t}(1-δ_t+it), we have |Im(z)|+2 ≤ (|t|+2)²
lemma lem_DIMt2 :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    |z.im| + 2 ≤ (|t| + 2)^3 := by
  intro t ht z hz
  -- From the previous lemma, |z.im| ≤ |t| + 5/6
  have h1' := lem_DImt2d t ht z hz
  -- Add 2 to both sides and simplify
  have h1a : |z.im| + 2 ≤ |t| + 17/6 := by
    linarith [h1']
  -- Bound |t| + 17/6 by |t| + 3
  have h17le3 : |t| + 17/6 ≤ |t| + 3 := by
    have : (17 : ℝ) / 6 ≤ 3 := by norm_num
    linarith
  -- Show |t| + 3 ≤ (|t| + 2)^3 by expanding and using nonnegativity
  have h_nonneg_poly : 0 ≤ |t|^3 + 6 * |t|^2 + 11 * |t| + 5 := by
    have h0 : 0 ≤ |t|^3 := by exact pow_nonneg (abs_nonneg _) 3
    have h1 : 0 ≤ 6 * |t|^2 := by
      have : 0 ≤ (6 : ℝ) := by norm_num
      exact mul_nonneg this (sq_nonneg _)
    have h2 : 0 ≤ 11 * |t| := by
      have : 0 ≤ (11 : ℝ) := by norm_num
      exact mul_nonneg this (abs_nonneg _)
    have h3 : 0 ≤ (5 : ℝ) := by norm_num
    exact add_nonneg (add_nonneg (add_nonneg h0 h1) h2) h3
  have h_add : |t| + 3 ≤ (|t| + 3) + (|t|^3 + 6 * |t|^2 + 11 * |t| + 5) := by
    simpa using (le_add_of_nonneg_right (a := |t| + 3) h_nonneg_poly)
  have h_expand : (|t| + 2)^3 = (|t| + 3) + (|t|^3 + 6 * |t|^2 + 11 * |t| + 5) := by
    ring
  have h3 : |t| + 3 ≤ (|t| + 2)^3 := by
    simpa [h_expand] using h_add
  -- Chain the inequalities
  exact le_trans (le_trans h1a h17le3) h3

-- For t∈ℝ with |t|>3 and z∈ D̄_{2δ_t}(1-δ_t+it), we have log(|Im(z)|+2) ≤ 2log(|t|+2)
lemma lem_DlogImlog :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    Real.log (|z.im| + 2) ≤ 3 * Real.log (|t| + 2) := by
  intro t ht z hz
  -- From lem_DIMt2 we have the key inequality on the arguments of the logs
  have h1 : |z.im| + 2 ≤ (|t| + 2)^3 := lem_DIMt2 t ht z hz
  -- Positivity of the left argument of log
  have h2 : 0 < |z.im| + 2 := by
    have : 0 ≤ |z.im| := abs_nonneg _
    linarith
  -- Monotonicity of log
  have hlog := Real.log_le_log h2 h1
  -- Rewrite the RHS using log_pow
  simpa [Real.log_pow] using hlog

-- For t∈ℝ with |t|>3 and z∈ D̄_{2δ_t}(1-δ_t+it), we have 1/log(|t|+2) ≤ 2/log(|Im(z)|+2)
lemma lem_D1logtlog :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    (1 : ℝ) / Real.log (|t| + 2) ≤ 3 / Real.log (|z.im| + 2) := by
  intro t ht z hz
  have h1 := lem_DlogImlog t ht z hz
  -- We need log(|t| + 2) > 0 and log(|z.im| + 2) > 0
  have ht_pos : |t| + 2 > 1 := by linarith [abs_nonneg t]
  have hz_pos : |z.im| + 2 > 1 := by linarith [abs_nonneg z.im]
  have log_t_pos : Real.log (|t| + 2) > 0 := Real.log_pos ht_pos
  have log_z_pos : Real.log (|z.im| + 2) > 0 := Real.log_pos hz_pos
  -- From h1: log(|z.im| + 2) ≤ 2 * log(|t| + 2)
  -- We want: 1/log(|t| + 2) ≤ 2/log(|z.im| + 2)
  -- Cross multiply: 1 * log(|z.im| + 2) ≤ 2 * log(|t| + 2)
  rw [div_le_div_iff₀ log_t_pos log_z_pos]
  simp only [one_mul]
  exact h1

-- For t∈ℝ with |t|>3 and z∈ D̄_{2δ_t}(1-δ_t+it), we have δ_t ≤ 2δ(z)
lemma lem_Ddt2dz :
  ∀ t : ℝ, |t| > 3 → ∀ z ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6),
    deltaz_t t ≤ 3 * deltaz z := by
  intro t ht z hz
  have h := lem_D1logtlog t ht z hz
  have hpos : 0 ≤ zerofree_constant / 20 := by
    have ha : 0 < zerofree_constant := zerofree_constant_pos
    have h9 : 0 < (20 : ℝ) := by norm_num
    exact div_nonneg (le_of_lt ha) (le_of_lt h9)
  have h2 := mul_le_mul_of_nonneg_left h hpos
  calc
    deltaz_t t
        = (zerofree_constant / 20) / Real.log (|t| + 2) := by
            simp [deltaz_t, deltaz, Complex.mul_I_im]
    _ = (zerofree_constant / 20) * (1 / Real.log (|t| + 2)) := by simp [div_eq_mul_inv]
    _ ≤ (zerofree_constant / 20) * (3 / Real.log (|z.im| + 2)) := h2
    _ = 3 * ((zerofree_constant / 20) * (1 / Real.log (|z.im| + 2))) := by
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    _ = 3 * deltaz z := by simp [deltaz, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma lem_deltarhotodeltat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → deltaz ρ ≥ (1/3) * deltaz_t t := by
  intro c hρK
  rcases hρK with ⟨hball, _hzero⟩
  have hball' : ρ ∈ Metric.closedBall ((3/2 : ℂ) + t * Complex.I) (5/6) := by
    simpa [c, mul_comm] using hball
  have hmain : deltaz_t t ≤ 3 * deltaz ρ := lem_Ddt2dz t ht ρ hball'
  have hthird_nonneg : 0 ≤ (1/3 : ℝ) := by norm_num
  have h_mul : (1/3 : ℝ) * deltaz_t t ≤ (1/3 : ℝ) * (3 * deltaz ρ) :=
    mul_le_mul_of_nonneg_left hmain hthird_nonneg
  have h_simplify : (1/3 : ℝ) * (3 * deltaz ρ) = deltaz ρ := by
    ring
  have : (1/3 : ℝ) * deltaz_t t ≤ deltaz ρ := by
    simpa [h_simplify] using h_mul
  simpa [mul_comm] using this

-- lem_Rerhotodeltat: For ρ∈ K_ζ(5/6;c) we have Re(ρ) ≤ 1 - 3δ_t
lemma lem_Rerhotodeltat (t : ℝ) (ht : |t| > 3) (ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) → ρ.re ≤ 1 - 3 * deltaz_t t := by
  intros c h_rho_in
  -- Apply lem_Rerhotodeltarho to get Re(ρ) ≤ 1 - 9 * δ(ρ)
  have h1 : ρ.re ≤ 1 - 9 * deltaz ρ :=
    lem_Rerhotodeltarho (ρ := ρ) t ht (by simpa [c, mul_comm] using h_rho_in)
  -- Apply lem_deltarhotodeltat to get δ(ρ) ≥ (1/3) * δ_t
  have h2 : deltaz ρ ≥ (1/3) * deltaz_t t := lem_deltarhotodeltat t ht ρ h_rho_in
  -- From h2, we get 9 * δ(ρ) ≥ 9 * (1/3) * δ_t = 3 * δ_t
  have h3 : 9 * deltaz ρ ≥ 3 * deltaz_t t := by
    calc
      9 * deltaz ρ
          ≥ 9 * ((1/3) * deltaz_t t) := by
                exact mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ℝ) ≤ 9)
      _ = 9 * (1/3) * deltaz_t t := by ring
      _ = 3 * deltaz_t t := by norm_num
  -- Therefore 1 - 9 * δ(ρ) ≤ 1 - 3 * δ_t
  have h4 : 1 - 9 * deltaz ρ ≤ 1 - 3 * deltaz_t t := by
    linarith [h3]
  -- By transitivity: Re(ρ) ≤ 1 - 9 * δ(ρ) ≤ 1 - 3 * δ_t
  exact le_trans h1 h4

-- lem_RezRerho: Re(z) - Re(ρ) ≥ 2δ_t
lemma lem_RezRerho (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    z.re - ρ.re ≥ 2 * deltaz_t t := by
  intro c h_rho_mem h_z
  -- Use lem_Rerhotodeltat to get upper bound on ρ.re
  have h_rho_bound := lem_Rerhotodeltat t ht ρ h_rho_mem
  -- Extract lower bound on z.re from hypothesis
  have h_z_lower := h_z.1
  -- Calculate: z.re - ρ.re ≥ (1 - deltaz_t t) - (1 - 3 * deltaz_t t) = 2 * deltaz_t t
  linarith [h_z_lower, h_rho_bound]

-- lem_abszrhodelta: |z-ρ| ≥ 2δ_t
lemma lem_abszrhodelta (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖z - ρ‖ ≥ 2 * deltaz_t t := by
  intro c h_rho_in_K h_z_conditions
  -- Use lem_RezRerho to get z.re - ρ.re ≥ 2 * deltaz_t t
  have h1 : z.re - ρ.re ≥ 2 * deltaz_t t := (lem_RezRerho t ht z ρ) h_rho_in_K h_z_conditions
  -- Use Complex.re_le_norm to get ‖z - ρ‖ ≥ z.re - ρ.re
  have h2 : ‖z - ρ‖ ≥ z.re - ρ.re := by
    simpa only [Complex.sub_re] using (Complex.re_le_norm (z - ρ))
  -- Combine by transitivity: 2 * deltaz_t t ≤ z.re - ρ.re ≤ ‖z - ρ‖
  exact le_trans h1 h2

-- lem_abszrhodeltanot0: |z-ρ| > 0

-- lem_1abszrho: 1/|z-ρ| ≤ 1/(2δ_t)
lemma lem_1abszrho (t : ℝ) (ht : |t| > 3) (z ρ : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) →
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    1 / ‖z - ρ‖ ≤ 1 / (2 * deltaz_t t) := by
  intro c hρ hz
  -- Apply one_div_le_one_div_of_le with the needed conditions
  apply one_div_le_one_div_of_le
  -- First need to prove 0 < 2 * deltaz_t t
  · have h_delta_pos : 0 < deltaz_t t := by
      have h_delta19 := lem_delta19
      exact (h_delta19.2 t (by linarith [ht] : |t| > 2)).1
    linarith [h_delta_pos]
  -- Second need to prove 2 * deltaz_t t ≤ ‖z - ρ‖
  · exact lem_abszrhodelta t ht z ρ hρ hz


lemma lem_finiteKzeta (t : ℝ) (ht : |t| > 3) :
    let c := (3/2 : ℂ) + I * t
    (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite := by
  intro c
  have hK : IsCompact (Metric.closedBall c (5 / (6 : ℝ))) :=
    ProperSpace.isCompact_closedBall c (5 / (6 : ℝ))
  simpa [zerosetKfRc] using
    (riemannZeta_zeros_finite_of_compact (Metric.closedBall c (5 / (6 : ℝ))) hK)

lemma lem_triangle_ZFR (t : ℝ) (ht : |t| > 3) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ ≤
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) := by
  -- Introduce variables correctly: c (center), hfin (finiteness proof), hz_cond (conditions on z)
  intros c hfin hz_cond

  -- Apply triangle inequality: ||∑ f_i|| ≤ ∑ ||f_i||
  apply le_trans (norm_sum_le _ _)

  -- Show each term satisfies the bound: ||m_ρ / (z-ρ)|| ≤ m_ρ / ||z-ρ||
  apply Finset.sum_le_sum
  intro ρ hρ

  -- Apply norm_div
  rw [norm_div]

  -- The norm of a natural number cast to ℂ equals the real cast
  rw [Complex.norm_natCast]

-- lem_Zeta_Triangle_ZFR: Triangle inequality bound for zeta'/zeta
lemma lem_Zeta_Triangle_ZFR :
    ∃ C_1 : ℝ, C_1 > 1 ∧
    ∀ t : ℝ, |t| > 3 →
      let c := (3/2 : ℂ) + I * t
      ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∀ z : ℂ, 1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
        ‖deriv riemannZeta z / riemannZeta z‖ ≤
        ‖(∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖ +
        C_1 * Real.log |t| := by
  obtain ⟨C1, hC1, hbound⟩ := lem_Zeta_Expansion_ZFR
  refine ⟨C1, hC1, ?_⟩
  intro t ht c hfin z hz
  -- Let S denote the finite sum over zeros
  let S := (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))
  have hbound1 := hbound t ht hfin z hz
  have htri : ‖deriv riemannZeta z / riemannZeta z‖ ≤ ‖(deriv riemannZeta z / riemannZeta z) - S‖ + ‖S‖ := by
    have hn := norm_add_le ((deriv riemannZeta z / riemannZeta z) - S) S
    have hrewrite : (deriv riemannZeta z / riemannZeta z) - S + S = (deriv riemannZeta z / riemannZeta z) := by
      simp [sub_eq_add_neg]
    simpa [S, hrewrite] using hn
  have : ‖deriv riemannZeta z / riemannZeta z‖ ≤ C1 * Real.log |t| + ‖S‖ := by
    linarith [htri, hbound1]
  simpa [S, add_comm] using this

-- lem_sumK1abs: Sum bound
lemma lem_sumK1abs (t : ℝ) (ht : |t| > 3) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
    1 - deltaz_t t ≤ z.re ∧ z.re ≤ 3/2 ∧ z.im = t →
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖) ≤
    (1 / (2 * deltaz_t t)) * (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ)) := by
  intro c hfin hzcond
  -- Pointwise bound using lem_1abszrho
  have hptwise : ∀ ρ ∈ hfin.toFinset,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖z - ρ‖ ≤
      (1 / (2 * deltaz_t t)) * ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
    intro ρ hρmem
    have hρ_in : ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta) :=
      (Set.Finite.mem_toFinset (hs := hfin)).1 hρmem
    have hbase : 1 / ‖z - ρ‖ ≤ 1 / (2 * deltaz_t t) :=
      lem_1abszrho t ht z ρ hρ_in hzcond
    have hnonneg : 0 ≤ ((analyticOrderAt riemannZeta ρ).toNat : ℝ) := by
      exact_mod_cast (Nat.zero_le ((analyticOrderAt riemannZeta ρ).toNat))
    have := mul_le_mul_of_nonneg_left hbase hnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hsum := Finset.sum_le_sum hptwise
  -- Rewrite the right-hand side sum as a constant times the sum
  have hrw :=
    (Finset.mul_sum (s := hfin.toFinset)
      (f := fun ρ => ((analyticOrderAt riemannZeta ρ).toNat : ℝ))
      (a := (1 / (2 * deltaz_t t))))
  have hsum2 := hsum
  -- Use the rewriting equality in the desired direction
  rw [← hrw] at hsum2
  -- Finish
  simpa [div_eq_mul_inv] using hsum2

lemma helper_analyticOnNhd_shift_div (f : ℂ → ℂ) (c : ℂ)
    (h : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ f z)
    (hc : f c ≠ 0) :
    AnalyticOnNhd ℂ (fun z => f (z + c) / f c) (Metric.closedBall (0 : ℂ) 1) := by
  -- Unfold the definition of AnalyticOnNhd on a set: pointwise AnalyticAt on the set
  intro z hz
  -- From hz : z ∈ closedBall 0 1, we get ‖z‖ ≤ 1
  have hz_norm : ‖z‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  -- Hence z + c belongs to the translated ball: dist (z + c) c ≤ 1
  have hz_addc_mem : z + c ∈ Metric.closedBall c 1 := by
    -- Show dist (z + c) c ≤ 1 from ‖z‖ ≤ 1
    have : dist (z + c) c ≤ 1 := by
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz_norm
    simpa [Metric.mem_closedBall] using this
  -- f is analytic at z + c by the hypothesis h
  have h_f_at : AnalyticAt ℂ f (z + c) := h (z + c) hz_addc_mem
  -- The translation z ↦ z + c is analytic at z
  have h_addc : AnalyticAt ℂ (fun w => w + c) z := by
    have h1 : AnalyticAt ℂ (id + fun _ : ℂ => c) z := analyticAt_id.add analyticAt_const
    have heq : (id + fun _ : ℂ => c) = fun w : ℂ => w + c := by funext w; simp
    rwa [heq] at h1
  -- Therefore, the composition z ↦ f (z + c) is analytic at z
  have h_comp : AnalyticAt ℂ (fun w => f (w + c)) z :=
    (AnalyticAt.fun_comp h_f_at h_addc)
  -- Multiplication by the constant (1 / f c) is analytic; hence division by f c is analytic
  have h_mul_const : AnalyticAt ℂ (fun w => (1 / f c) * f (w + c)) z :=
    (analyticAt_const.mul h_comp)
  -- Rewrite to the desired form
  simpa [div_eq_mul_inv, mul_comm] using h_mul_const

lemma helper_finite_zeros_shift (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ)
    (hc : f c ≠ 0)
    (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1))
    (hfin : (zerosetKfRc r c f).Finite) :
    (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)).Finite :=
by
  classical
  let g : ℂ → ℂ := fun z => f (z + c) / f c
  have hEq :
      zerosetKfRc r (0 : ℂ) g = (fun ρ : ℂ => ρ - c) '' zerosetKfRc r c f := by
    apply Set.Subset.antisymm
    · intro x hx
      -- x ∈ closedBall 0 r and g x = 0
      have hx_ball : dist x (0 : ℂ) ≤ r := by
        simpa [Metric.mem_closedBall] using hx.1
      -- hence x + c ∈ closedBall c r
      have hx_ball' : dist (x + c) c ≤ r := by
        simpa [Complex.dist_eq, add_sub_cancel] using hx_ball
      -- and f (x + c) = 0 from g x = 0 and hc
      have hx_zero : f (x + c) = 0 := by
        rcases (div_eq_zero_iff).mp (by simpa [g] using hx.2) with hnum | hden
        · exact hnum
        · exact (hc hden).elim
      refine ⟨x + c, ?_, ?_⟩
      · exact ⟨by simpa [Metric.mem_closedBall] using hx_ball', hx_zero⟩
      · simp
    · intro x hx
      rcases hx with ⟨ρ, hρ, rfl⟩
      -- ρ ∈ closedBall c r and f ρ = 0
      have hρ_ball : dist ρ c ≤ r := by
        simpa [Metric.mem_closedBall] using hρ.1
      refine ⟨?_, ?_⟩
      · -- membership in closedBall 0 r
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hρ_ball
      · -- g (ρ - c) = 0
        have : f ρ = 0 := hρ.2
        simp [g, sub_add_cancel, this]
  -- The target set equals an image of a finite set, hence finite
  have himage : ((fun ρ : ℂ => ρ - c) '' zerosetKfRc r c f).Finite :=
    hfin.image (fun ρ : ℂ => ρ - c)
  simpa [g, hEq] using himage

lemma helper_bound_shifted (B R : ℝ) (hB : 1 < B) (hRpos : 0 < R) (hRlt1 : R < 1)
    (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
    (h_bound : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖(fun w => f (w + c) / f c) z‖ ≤ B / ‖f c‖ :=
by
  intro z hz
  -- From z ∈ closedBall 0 R, we get ‖z‖ ≤ R
  have hz_norm : ‖z‖ ≤ R := by
    have hz' : dist z (0 : ℂ) ≤ R := by simpa [Metric.mem_closedBall] using hz
    simpa [Complex.dist_eq] using hz'
  -- Hence z + c ∈ closedBall c R
  have hz_ballc : z + c ∈ Metric.closedBall c R := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, add_sub_cancel] using hz_norm
  -- Apply the bound on f over the translated ball
  have hfb : ‖f (z + c)‖ ≤ B := h_bound (z + c) hz_ballc
  -- Since f c ≠ 0, its norm is positive
  have hpos : 0 < ‖f c‖ := (norm_pos_iff).2 hc
  -- Divide the inequality by ‖f c‖
  have hdiv : ‖f (z + c)‖ / ‖f c‖ ≤ B / ‖f c‖ := (div_le_div_iff_of_pos_right hpos).2 hfb
  -- Rewrite the left-hand side using norm_div
  have hnorm_eq : ‖(fun w => f (w + c) / f c) z‖ = ‖f (z + c)‖ / ‖f c‖ := by
    change ‖f (z + c) / f c‖ = ‖f (z + c)‖ / ‖f c‖
    simp
  simpa [hnorm_eq] using hdiv

lemma helper_g_zero_eq_one (f : ℂ → ℂ) (c : ℂ) (hc : f c ≠ 0) :
  (fun z => f (z + c) / f c) 0 = 1 := by
  simp [hc]

lemma helper_zerosetKfR_eq_center0 (r : ℝ) (hr : r > 0) (f : ℂ → ℂ) :
  zerosetKfR r hr f = zerosetKfRc r (0 : ℂ) f := by
  ext ρ; simp [zerosetKfR, zerosetKfRc]

lemma helper_one_le_Bdivfc2 (B R : ℝ) (hB : 1 < B) (hRpos : 0 < R) (hRlt1 : R < 1)
  (f : ℂ → ℂ) (c : ℂ) (hc : f c ≠ 0)
  (h_bound : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B) :
  1 ≤ B / ‖f c‖ :=
by
  have hc_in : c ∈ Metric.closedBall c R := by
    have h0le : (0 : ℝ) ≤ R := le_of_lt hRpos
    simpa [Metric.mem_closedBall, dist_self] using h0le
  have hfc_le : ‖f c‖ ≤ B := h_bound c hc_in
  have hfc_pos : 0 < ‖f c‖ := (norm_pos_iff.mpr hc)
  have hdiv := (div_le_div_iff_of_pos_right (c := ‖f c‖) hfc_pos).mpr hfc_le
  simpa [div_self (ne_of_gt hfc_pos)] using hdiv


lemma helper_apply_jensen_to_g
  (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_ne : g 0 ≠ 0)
  (hg0_one : g 0 = 1)
  (hfin_g : (zerosetKfR R1 (by linarith) g).Finite)
  (hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B) :
  (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) ≤ Real.log B / Real.log (R / R1) := by
  classical
  -- For each zero σ, obtain local factorization data
  have h_exists : ∀ σ ∈ zerosetKfR R1 (by linarith) g,
      ∃ hσ : ℂ → ℂ, AnalyticAt ℂ hσ σ ∧ hσ σ ≠ 0 ∧
        ∀ᶠ z in nhds σ, g z = (z - σ) ^ (analyticOrderAt g σ).toNat * hσ z := by
    intro σ hσ
    exact lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR_lt_1 g h_g_analytic hg0_ne σ hσ
  -- Define a choice of local factors h_σ(σ)
  let h_σ : ℂ → (ℂ → ℂ) :=
    fun σ => dite (σ ∈ zerosetKfR R1 (by linarith) g)
      (fun h => Classical.choose (h_exists σ h))
      (fun _ => fun _ => (1 : ℂ))
  -- Prove the specification for h_σ on zeros
  have h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) g,
      AnalyticAt ℂ (h_σ σ) σ ∧ (h_σ σ) σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, g z = (z - σ) ^ (analyticOrderAt g σ).toNat * (h_σ σ) z := by
    intro σ hσin
    have hx := h_exists σ hσin
    dsimp [h_σ]
    -- Use the chosen witness at σ
    simpa [hσin] using (Classical.choose_spec hx)
  -- Apply the Jensen-type bound lemma
  have hbound :=
    lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1
      g h_g_analytic hg0_ne hg0_one hfin_g (h_σ := h_σ) hg_le_B h_σ_spec
  -- Rewrite to the desired division form
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hbound

lemma helper_sum_f_equals_sum_g
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1))
  (hfin : (zerosetKfRc r c f).Finite) :
  (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
  =
  (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
      ((analyticOrderAt (fun z => f (z + c) / f c) ρ').toNat : ℝ)) :=
by
  classical
  -- Notation
  let S : Finset ℂ := hfin.toFinset
  let φ : ℂ → ℂ := fun ρ => ρ - c
  let g' : ℂ → ℂ := fun z => f (z + c) / f c

  -- Relate the RHS indexing Finset to the image of S under φ
  have himg : (φ '' zerosetKfRc r c f).Finite := hfin.image φ
  have h_img_toFinset : ((hfin.image φ).toFinset) = S.image φ := by
    simpa [S] using (Set.Finite.toFinset_image (s := (zerosetKfRc r c f)) (f := φ)
      (hs := hfin) (h := himg))

  -- First, change the summand using equality of analytic orders at corresponding points
  have h_orders_match :
      (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ)) =
      (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := by
    apply Finset.sum_congr rfl
    intro ρ hρS
    -- ρ is in the zero set of f within the ball centered at c of radius r
    have hρ_mem : ρ ∈ zerosetKfRc r c f :=
      (Set.Finite.mem_toFinset (hs := hfin)).1 hρS
    have hρ_ball : ρ ∈ Metric.closedBall c r := hρ_mem.1
    have hρ_fzero : f ρ = 0 := hρ_mem.2
    -- Show that ρ' = ρ - c is in the zero set for g' centered at 0
    have hρ'_ball : (φ ρ) ∈ Metric.closedBall (0 : ℂ) r := by
      -- dist ρ c ≤ r
      have hdist_le : dist ρ c ≤ r := by
        simpa [Metric.mem_closedBall] using hρ_ball
      -- translate the inequality to the origin
      have : dist (φ ρ) 0 ≤ r := by
        simpa [φ, dist_eq_norm] using (by simpa [dist_eq_norm] using hdist_le)
      simpa [Metric.mem_closedBall] using this
    have hρ'_gzero : g' (φ ρ) = 0 := by
      simp [g', φ, hc, hρ_fzero, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hρ'_mem : (φ ρ) ∈ zerosetKfRc r (0 : ℂ) g' := ⟨hρ'_ball, hρ'_gzero⟩
    -- Apply fc_m_order to equate multiplicities
    have h_m_eq := fc_m_order r hr c f hc h_analytic (ρ' := φ ρ) hρ'_mem
    -- (φ ρ) + c = ρ
    have h_m_eq' : analyticOrderAt g' (φ ρ) = analyticOrderAt f ρ := by
      simpa [g', φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_m_eq
    -- Pass to toNat and cast to ℝ
    have h_toNat : (analyticOrderAt g' (φ ρ)).toNat = (analyticOrderAt f ρ).toNat := by
      simpa using congrArg ENat.toNat h_m_eq'
    simp [h_toNat]

  -- Next, rewrite the sum over the image using Finset.sum_image
  have h_inj : Function.Injective φ := by
    intro x y hxy
    -- add c to both sides to cancel the subtraction
    have := congrArg (fun z => z + c) hxy
    simpa [φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

  have h_sum_image :
      (∑ ρ' ∈ S.image φ, ((analyticOrderAt g' ρ').toNat : ℝ)) =
      (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := by
    refine Finset.sum_image ?h
    intro x hx y hy hxy
    -- need x = y from φ x = φ y
    exact h_inj hxy

  -- Put everything together
  calc
    (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
        = (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ)) := by rfl
    _ = (∑ ρ ∈ S, ((analyticOrderAt g' (φ ρ)).toNat : ℝ)) := h_orders_match
    _ = (∑ ρ' ∈ S.image φ, ((analyticOrderAt g' ρ').toNat : ℝ)) := h_sum_image.symm
    _ = (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
            ((analyticOrderAt (fun z => f (z + c) / f c) ρ').toNat : ℝ)) := by
          -- rewrite the index and the function names
          simp [S, φ, g', h_img_toFinset]

lemma helper_zero_set_shift_eq
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1)) :
  zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)
  = (fun ρ => ρ - c) '' (zerosetKfRc r c f) := by
  simpa using fc_zeros r hr c f hc h_analytic

lemma helper_fin_zero_g_is_image
  (r : ℝ) (hr : r > 0) (c : ℂ) (f : ℂ → ℂ) (hc : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (Metric.closedBall c 1))
  (hfin : (zerosetKfRc r c f).Finite) :
  (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)).Finite :=
by
  classical
  have hset : zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)
      = (fun ρ => ρ - c) '' (zerosetKfRc r c f) :=
    by simpa using fc_zeros r hr c f hc h_analytic
  have hfin_img : ((fun ρ => ρ - c) '' (zerosetKfRc r c f)).Finite := hfin.image _
  simpa [hset] using hfin_img

lemma helper_AnalyticOnNhd_to_pointwise {S : Set ℂ} {f : ℂ → ℂ}
  (h : AnalyticOnNhd ℂ f S) : ∀ z ∈ S, AnalyticAt ℂ f z := by
  intro z hz
  exact h z hz

lemma jensen_sum_bound_strict
  (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_ne : g 0 ≠ 0)
  (hg0_one : g 0 = 1)
  (hfin_g : (zerosetKfR R1 (by linarith) g).Finite)
  (hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B) :
  (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) ≤
    Real.log B / Real.log (R / R1) := by
  exact helper_apply_jensen_to_g B R R1 hB hR1_pos hR1_lt_R hR_lt_1 g
    h_g_analytic hg0_ne hg0_one hfin_g hg_le_B

lemma no_zero_of_bound_one_and_center_one
  (R : ℝ) (hR_lt_1 : R < 1)
  (g : ℂ → ℂ)
  (h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z)
  (hg0_one : g 0 = 1)
  (hg_le_one : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ 1) :
  ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 := by
  intro z hz
  by_cases hRpos : 0 < R
  ·
    -- differentiability inside the open ball
    have hdiff : DifferentiableOn ℂ g (Metric.ball (0 : ℂ) R) := by
      intro x hx
      have hxlt : ‖x‖ < R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hx
      have hxle1 : ‖x‖ ≤ 1 := le_trans (le_of_lt hxlt) (le_of_lt hR_lt_1)
      have hx_in1 : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hxle1
      exact ((h_g_analytic x hx_in1).differentiableAt).differentiableWithinAt
    -- continuity on the closed ball of radius R
    have hcont : ContinuousOn g (Metric.closedBall (0 : ℂ) R) := by
      intro x hx
      have hxleR : ‖x‖ ≤ R := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hx
      have hxle1 : ‖x‖ ≤ 1 := le_trans hxleR (le_of_lt hR_lt_1)
      have hx_in1 : x ∈ Metric.closedBall (0 : ℂ) 1 := by
        simpa [Metric.mem_closedBall, Complex.dist_eq] using hxle1
      exact (h_g_analytic x hx_in1).continuousAt.continuousWithinAt
    have hdcc : DiffContOnCl ℂ g (Metric.ball (0 : ℂ) R) :=
      DiffContOnCl.mk_ball hdiff hcont
    -- maximum of the modulus at 0 on the open ball of radius R
    have hIsMax : IsMaxOn (fun z => ‖g z‖) (Metric.ball (0 : ℂ) R) 0 := by
      intro y hy
      have hynormlt : ‖y‖ < R := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hy
      have hyle : ‖y‖ ≤ R := le_of_lt hynormlt
      have hgy : ‖g y‖ ≤ 1 := hg_le_one y hyle
      simpa [hg0_one] using hgy
    -- apply maximum modulus principle on the closed ball
    have hEqOn :=
      Complex.eqOn_closedBall_of_isMaxOn_norm (z := (0 : ℂ)) (r := R) hdcc hIsMax
    have hz_eq : g z = (fun _ => g 0) z := hEqOn hz
    have hz_eq1 : g z = g 0 := by simpa using hz_eq
    have gz_one : g z = 1 := by simpa [hg0_one] using hz_eq1
    simp [gz_one]
  ·
    -- If R ≤ 0, then any z in closedBall(0,R) must be 0, hence g z = 1 ≠ 0
    have hRle : R ≤ 0 := le_of_not_gt hRpos
    have hz_le : ‖z‖ ≤ R := by
      simpa [Metric.mem_closedBall, Complex.dist_eq] using hz
    have hz_norm_eq : ‖z‖ = 0 :=
      le_antisymm (le_trans hz_le hRle) (norm_nonneg z)
    have hz_zero : z = 0 := by
      simpa [norm_eq_zero] using hz_norm_eq
    simp [hz_zero, hg0_one]

lemma helper_sum_over_equal_finite_sets_orders
  {S T : Set ℂ} (g : ℂ → ℂ)
  (hS : S.Finite) (hT : T.Finite) (hST : S = T) :
  (∑ x ∈ hS.toFinset, ((analyticOrderAt g x).toNat : ℝ))
  = (∑ x ∈ hT.toFinset, ((analyticOrderAt g x).toNat : ℝ)) := by
  classical
  have hF : hS.toFinset = hT.toFinset := by
    ext x
    simp [Set.Finite.mem_toFinset, hST]
  simp [hF]


lemma helper_bound_on_ball_to_norm_imp
  {R : ℝ} {g : ℂ → ℂ} {M : ℝ}
  (hg : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ M) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ M := by
  intro z hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R := by
    have : dist z (0 : ℂ) ≤ R := by
      simpa [dist_eq_norm] using hz
    simpa [Metric.mem_closedBall] using this
  exact hg z hz'

lemma helper_pointwise_to_AnalyticOnNhd {S : Set ℂ} {f : ℂ → ℂ}
  (h : ∀ z ∈ S, AnalyticAt ℂ f z) : AnalyticOnNhd ℂ f S := h

lemma lem_sum_m_rho_bound_c (B R R1 : ℝ) (hB : 1 < B)
  (hR1_pos : 0 < R1)
  (hR1_lt_R : R1 < R)
  (hR_lt_1 : R < 1)
  (f : ℂ → ℂ)
  (c : ℂ)
  (h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ f z)
  (h_f_nonzero_at_zero : f c ≠ 0)
  (hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖f z‖ ≤ B)
  (hfin : (zerosetKfRc R1 c f).Finite) :
      ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
  classical
  -- Define the shifted function g(z) = f(z+c)/f(c)
  let g : ℂ → ℂ := fun z => f (z + c) / f c

  -- g is analytic on the unit closed ball centered at 0
  have h_g_analyticOn : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) :=
    helper_analyticOnNhd_shift_div f c h_f_analytic h_f_nonzero_at_zero
  have h_g_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ g z :=
    helper_AnalyticOnNhd_to_pointwise h_g_analyticOn

  -- g(0) = 1 and hence g(0) ≠ 0
  have hg0_one : g 0 = 1 := helper_g_zero_eq_one f c h_f_nonzero_at_zero
  have hg0_ne : g 0 ≠ 0 := by simp [hg0_one]

  -- Finiteness of zeros of g in radius R1 and set equalities
  have hAnal_f : AnalyticOnNhd ℂ f (Metric.closedBall c 1) :=
    helper_pointwise_to_AnalyticOnNhd h_f_analytic
  have hfin_g0 : (zerosetKfRc R1 (0 : ℂ) g).Finite :=
    helper_fin_zero_g_is_image R1 hR1_pos c f h_f_nonzero_at_zero hAnal_f hfin
  have hZR_eq : zerosetKfR R1 hR1_pos g = zerosetKfRc R1 (0 : ℂ) g :=
    helper_zerosetKfR_eq_center0 R1 hR1_pos g
  have hfin_g : (zerosetKfR R1 (by exact hR1_pos) g).Finite := by
    simpa [hZR_eq] using hfin_g0

  -- Bound on g on the closed ball of radius R
  have h_bound_shift : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖g z‖ ≤ B / ‖f c‖ :=
    helper_bound_shifted B R hB (by exact lt_trans hR1_pos hR1_lt_R) hR_lt_1 c f
      h_f_nonzero_at_zero (fun z hz => hf_le_B z <| by simpa using hz)
  have hg_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ B / ‖f c‖ :=
    helper_bound_on_ball_to_norm_imp (R := R) (g := g) (M := B / ‖f c‖) h_bound_shift

  -- Show 1 ≤ B / ‖f c‖ to split into cases
  have hfc_le : ‖f c‖ ≤ B := by
    have : c ∈ Metric.closedBall c R := by
      have hRpos' : 0 ≤ R := le_of_lt (lt_trans hR1_pos hR1_lt_R)
      have : dist c c ≤ R := by simpa [dist_self] using hRpos'
      simpa [Metric.mem_closedBall] using this
    exact hf_le_B c this
  have hfc_pos : 0 < ‖f c‖ := (norm_pos_iff).2 h_f_nonzero_at_zero
  have hBdiv_ge_one : 1 ≤ B / ‖f c‖ := by
    have hdiv := (div_le_div_iff_of_pos_right hfc_pos).mpr hfc_le
    simpa [div_self (ne_of_gt hfc_pos)] using hdiv

  -- Equality between sums over zeros of f and zeros of g (shifted)
  have hsum_fg_eq :
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
        = (∑ ρ' ∈ ((hfin.image (fun ρ => ρ - c)).toFinset),
            ((analyticOrderAt g ρ').toNat : ℝ)) :=
    helper_sum_f_equals_sum_g (r := R1) (hr := hR1_pos) (c := c)
      (f := f) (hc := h_f_nonzero_at_zero) (h_analytic := hAnal_f) (hfin := hfin)

  -- Equality of sets for g-zeros and the image of f-zeros
  have hST_g_img : zerosetKfR R1 hR1_pos g
      = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) := by
    have h1 : zerosetKfR R1 hR1_pos g = zerosetKfRc R1 (0 : ℂ) g :=
      helper_zerosetKfR_eq_center0 R1 hR1_pos g
    have h2 : zerosetKfRc R1 (0 : ℂ) g
        = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) :=
      helper_zero_set_shift_eq R1 hR1_pos c f h_f_nonzero_at_zero hAnal_f
    simpa [h1] using h2

  -- Now split into cases depending on whether B/‖f c‖ > 1 or = 1
  rcases lt_or_eq_of_le hBdiv_ge_one with hBdiv_gt_one | hBdiv_eq_one
  · -- Strict case: apply Jensen bound to g with B' = B / ‖f c‖
    have hsum_g_bound :=
      jensen_sum_bound_strict (B := B / ‖f c‖) (R := R) (R1 := R1)
        (hB := hBdiv_gt_one)
        (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
        (g := g) (h_g_analytic := h_g_analytic) (hg0_ne := hg0_ne)
        (hg0_one := hg0_one) (hfin_g := hfin_g) (hg_le_B := hg_le_B)
    -- Replace the indexing finite set using equality of sets S = image set
    have hsum_g_reindex :
        (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          = (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) :=
      helper_sum_over_equal_finite_sets_orders (g := g)
        (S := zerosetKfR R1 hR1_pos g)
        (T := (fun ρ => ρ - c) '' (zerosetKfRc R1 c f))
        (hS := hfin_g) (hT := hfin.image (fun ρ => ρ - c)) (hST := hST_g_img)
    -- Combine bounds and equalities to obtain the desired inequality
    have :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
      simpa [hsum_g_reindex] using hsum_g_bound
    -- Replace g-sum by f-sum using hsum_fg_eq
    simpa [hsum_fg_eq] using this
  · -- Equality case: B / ‖f c‖ = 1; show no zeros for g inside radius R, hence sum = 0
    have hBdiv_eq_one' : B / ‖f c‖ = 1 := by
      simpa [eq_comm] using hBdiv_eq_one
    have hg_le_one : ∀ z : ℂ, ‖z‖ ≤ R → ‖g z‖ ≤ 1 := by
      intro z hz
      have := hg_le_B z hz
      simpa [hBdiv_eq_one'] using this
    have g_nonzero_on_ball : ∀ z ∈ Metric.closedBall (0 : ℂ) R, g z ≠ 0 :=
      no_zero_of_bound_one_and_center_one R hR_lt_1 g h_g_analytic hg0_one hg_le_one
    -- zeroset within radius R1 is empty; hence the finite sum is zero
    have hS_empty : zerosetKfR R1 hR1_pos g = (∅ : Set ℂ) := by
      ext z; constructor
      · intro hz
        rcases hz with ⟨hzball, hzzero⟩
        have hzR1 : ‖z‖ ≤ R1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
        have hzR : ‖z‖ ≤ R := le_trans hzR1 (le_of_lt hR1_lt_R)
        have hzR' : z ∈ Metric.closedBall (0 : ℂ) R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using hzR
        exact (g_nonzero_on_ball z hzR') hzzero
      · intro hzfalse
        cases hzfalse
    have hsum_g_zero :
        (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) = 0 := by
      have h :=
        helper_sum_over_equal_finite_sets_orders (g := g)
          (S := zerosetKfR R1 hR1_pos g) (T := (∅ : Set ℂ))
          (hS := hfin_g) (hT := Set.finite_empty) (hST := hS_empty)
      simpa using h
    -- Transport zero sum to the image-of-f sum via equality of finite sets S = image set
    have hsum_reindex :=
      helper_sum_over_equal_finite_sets_orders (g := g)
        (S := zerosetKfR R1 hR1_pos g)
        (T := (fun ρ => ρ - c) '' (zerosetKfRc R1 c f))
        (hS := hfin_g) (hT := hfin.image (fun ρ => ρ - c)) (hST := hST_g_img)
    have hsum_img_eq :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ))
          = (∑ ρ ∈ hfin_g.toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) := by
      simpa using hsum_reindex.symm
    have hsum_img_zero :
        (∑ ρ ∈ (hfin.image (fun ρ => ρ - c)).toFinset, ((analyticOrderAt g ρ).toNat : ℝ)) = 0 := by
      simp [hsum_img_eq, hsum_g_zero]
    -- Hence the sum over f is zero via hsum_fg_eq
    have hsum_f_zero :
        (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) = 0 := by
      simpa [hsum_img_zero] using hsum_fg_eq
    -- Right-hand side equals zero since log(1) = 0
    have hRHS_zero : Real.log (B / ‖f c‖) / Real.log (R / R1) = 0 := by
      simp [hBdiv_eq_one']
    -- Conclude the desired inequality
    have :
        (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt f ρ).toNat : ℝ))
          ≤ Real.log (B / ‖f c‖) / Real.log (R / R1) := by
      simp [hsum_f_zero, hRHS_zero]
    exact this

lemma lem_sum_m_rho_zeta :
    ∃ C_2 > 1, ∀ (t : ℝ) (ht : |t| > 3),
    let c := (3/2 : ℂ) + I * t;
    ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) ≤ C_2 * Real.log |t| := by
  classical
  -- Constants from auxiliary bounds
  obtain ⟨b, hb_gt1, hb_bound⟩ := zeta32upper
  obtain ⟨a, ha_pos, ha_bound⟩ := zeta_low_332
  -- Radii
  let R1 : ℝ := 5 / 6
  let R : ℝ := 8 / 9
  let logRatio : ℝ := Real.log (R / R1)
  -- Define constant from b and a
  let u : ℝ := Real.log (b / a)
  let C2 : ℝ := max 2 ((1 + |u|) / logRatio)
  have hC2_gt_one : 1 < C2 := by
    have htwo_lt : (1 : ℝ) < 2 := by norm_num
    have hle : (2 : ℝ) ≤ C2 := by
      have := le_max_left (2 : ℝ) ((1 + |u|) / logRatio)
      simp [C2]
    exact lt_of_lt_of_le htwo_lt hle
  refine ⟨C2, hC2_gt_one, ?_⟩
  intro t ht c hfin
  -- Numeric facts about radii
  have hR1_pos : 0 < R1 := by dsimp [R1]; norm_num
  have hR1_lt_R : R1 < R := by dsimp [R1, R]; norm_num
  have hR_lt_1 : R < 1 := by dsimp [R]; norm_num
  have hR_le_one : R ≤ (1 : ℝ) := by dsimp [R]; norm_num
  -- Analyticity on closedBall c 1: ζ is analytic off {1}, and the ball avoids 1 for |t|>1
  have ht1 : |t| > 1 := lt_trans (by norm_num) ht
  have h_f_analytic : ∀ z ∈ Metric.closedBall c 1, AnalyticAt ℂ riemannZeta z := by
    intro z hz
    have hz_ne_one : z ≠ (1 : ℂ) := (D1cinTt_pre t ht1) z (by simpa [c] using hz)
    have hz_mem : z ∈ ({1} : Set ℂ)ᶜ := by simpa using hz_ne_one
    exact analyticOn_riemannZeta z hz_mem
  -- Nonzero at center
  have h_nonzero : riemannZeta c ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_lt_re
    norm_num [c, Complex.add_re, Complex.I_mul_re]
  -- Upper bound on |ζ| on closedBall c R with B = b * |t|
  have ht2 : |t| > 2 := by linarith
  have h_upper_on_ball1 : ∀ z ∈ Metric.closedBall c 1, ‖riemannZeta z‖ < b * |t| := by
    have h := hb_bound t ht2
    intro z hz; simpa [c] using h z (by simpa [c] using hz)
  have hf_le_B : ∀ z ∈ Metric.closedBall c R, ‖riemannZeta z‖ ≤ b * |t| := by
    intro z hz
    have hz1 : z ∈ Metric.closedBall c 1 :=
      (Metric.closedBall_subset_closedBall hR_le_one) hz
    exact le_of_lt (h_upper_on_ball1 z hz1)
  -- Show B = b * |t| > 1
  have hb_pos : 0 < b := lt_trans (by norm_num) hb_gt1
  have htabove1 : (1 : ℝ) ≤ |t| := le_of_lt ht1
  have hb_le_B : b ≤ b * |t| := by
    have := mul_le_mul_of_nonneg_left htabove1 (le_of_lt hb_pos)
    simpa [one_mul] using this
  have hBpos : 1 < b * |t| := lt_of_lt_of_le hb_gt1 hb_le_B
  -- Apply the Jensen-type bound centered at c, with R1=5/6, R=8/9
  have h_sum_bound :=
    lem_sum_m_rho_bound_c (B := b * |t|) (R := R) (R1 := R1)
      (hB := hBpos)
      (hR1_pos := hR1_pos)
      (hR1_lt_R := hR1_lt_R)
      (hR_lt_1 := hR_lt_1)
      (f := riemannZeta) (c := c)
      (h_f_analytic := h_f_analytic)
      (h_f_nonzero_at_zero := h_nonzero)
      (hf_le_B := hf_le_B)
      (hfin := hfin)
  -- Positivity of logRatio
  have hlogRatio_pos : 0 < logRatio := by
    have : 1 < R / R1 := by dsimp [R, R1]; norm_num
    exact Real.log_pos this
  -- Lower bound for |ζ c|
  have h_zeta_ge_a : a ≤ ‖riemannZeta c‖ := by
    simpa [c, mul_comm] using ha_bound t
  -- Now convert RHS to a multiple of log |t|
  -- First, bound the log of the quotient using a ≤ ‖ζ c‖
  have ht_abs_pos : 0 < |t| := lt_trans (by norm_num) ht
  have hζ_norm_pos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr h_nonzero
  have hb_ne : (b : ℝ) ≠ 0 := ne_of_gt hb_pos
  have ht_abs_ne : (|t| : ℝ) ≠ 0 := ne_of_gt ht_abs_pos
  have ha_ne : a ≠ 0 := ne_of_gt ha_pos
  have hlog_split1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        = (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖ := by
    have : Real.log (b * |t|) = Real.log b + Real.log |t| :=
      Real.log_mul hb_ne ht_abs_ne
    have :
        Real.log ((b * |t|) / ‖riemannZeta c‖)
          = Real.log (b * |t|) - Real.log ‖riemannZeta c‖ :=
      Real.log_div (by exact mul_ne_zero hb_ne ht_abs_ne) (ne_of_gt hζ_norm_pos)
    simp [this, Real.log_mul hb_ne ht_abs_ne]
  have hlog_div_eq : Real.log (b / a) = Real.log b - Real.log a :=
    Real.log_div hb_ne ha_ne
  have hlog_a_le : Real.log a ≤ Real.log ‖riemannZeta c‖ :=
    Real.log_le_log (by exact ha_pos) (by exact h_zeta_ge_a)
  have hneg : -(Real.log ‖riemannZeta c‖) ≤ -Real.log a := by
    simpa using (neg_le_neg hlog_a_le)
  have hRHS_le_const :
      Real.log ((b * |t|) / ‖riemannZeta c‖)
        ≤ Real.log |t| + Real.log (b / a) := by
    -- Rewrite LHS and RHS and use hneg
    have :
        (Real.log b + Real.log |t|) - Real.log ‖riemannZeta c‖
          ≤ (Real.log b + Real.log |t|) - Real.log a := by
      linarith [hneg]
    simpa [hlog_split1, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, hlog_div_eq]
      using this
  -- Divide by positive logRatio
  have hRHS1 :
      Real.log ((b * |t|) / ‖riemannZeta c‖) / logRatio
        ≤ (Real.log |t| + Real.log (b / a)) / logRatio := by
    exact div_le_div_of_nonneg_right hRHS_le_const (le_of_lt hlogRatio_pos)
  -- Bound additive constant by |u|
  have hlogt_ge_one : (1 : ℝ) ≤ Real.log |t| := by
    -- log |t| ≥ log 3 ≥ 1
    have h3le : (3 : ℝ) ≤ |t| := le_of_lt ht
    have hlog3_le : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) h3le
    have h_exp_le : Real.exp (1 : ℝ) ≤ 3 := le_of_lt lem_three_gt_e
    have hlog3_ge_one : (1 : ℝ) ≤ Real.log 3 :=
      (Real.le_log_iff_exp_le (by norm_num : 0 < (3 : ℝ))).mpr h_exp_le
    exact le_trans hlog3_ge_one hlog3_le
  have hadd_le : Real.log |t| + Real.log (b / a) ≤ (1 + |u|) * Real.log |t| := by
    have haux1 : Real.log (b / a) ≤ |u| := by simpa [u] using le_abs_self (Real.log (b / a))
    have haux2 : |u| ≤ |u| * Real.log |t| := by
      have hnonneg : 0 ≤ |u| := abs_nonneg _
      have h1le : (1 : ℝ) ≤ Real.log |t| := hlogt_ge_one
      simpa [one_mul] using (mul_le_mul_of_nonneg_left h1le hnonneg)
    calc
      Real.log |t| + Real.log (b / a)
          ≤ Real.log |t| + |u| := by linarith [haux1]
      _ ≤ Real.log |t| + (|u| * Real.log |t|) := by linarith [haux2]
      _ = (1 + |u|) * Real.log |t| := by ring
  have hRHS2 :
      (Real.log |t| + Real.log (b / a)) / logRatio
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := div_le_div_of_nonneg_right hadd_le (le_of_lt hlogRatio_pos)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hfinal :
      (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℝ))
        ≤ ((1 + |u|) / logRatio) * Real.log |t| := by
    have := le_trans h_sum_bound hRHS1
    exact le_trans this hRHS2
  -- Compare with C2 * log |t|
  have hC2_ge : ((1 + |u|) / logRatio) ≤ C2 := by
    have := le_max_right (2 : ℝ) ((1 + |u|) / logRatio)
    simp [C2]
  have hlogt_nonneg : 0 ≤ Real.log |t| := le_trans (by norm_num) hlogt_ge_one
  have hscale := mul_le_mul_of_nonneg_right hC2_ge hlogt_nonneg
  exact le_trans hfinal hscale

end ZetaZeroFreeRegion
