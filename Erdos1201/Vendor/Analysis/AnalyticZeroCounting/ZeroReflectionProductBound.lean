module

public import Erdos1201.Vendor.Analysis.AnalyticZeroCounting.FiniteZeroSetQuotient

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open DiskAnalyticBounds

/-!
The finite "reflected-zero" product `Bf` — `Cf` (the deflated quotient from
`FiniteZeroSetQuotient`) times a finite product of factors
`(R - ρ̄z/R)^{m_ρ}` reflecting each zero `ρ` through the circle of radius `R`
— is analytic on the whole closed disk of radius `R` (the reflection factor
patches the poles `Cf` would otherwise have at the zeros), has modulus equal
to `‖f‖` on the boundary circle, and hence (by the maximum-modulus
principle) is bounded on the disk by whatever bounds `f` there. Concludes
with the resulting bound on `‖Bf(0)‖` as a product of `R/‖ρ‖` factors.
-/

public section

namespace AnalyticZeroCounting

@[expose] noncomputable def Bf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) : ℂ :=
  Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z *
  ∏ ρ ∈ h_finite_zeros.toFinset,
    ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat

lemma lem_BfCf
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z * (∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) /
    (∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat) := by
  -- Since z ∉ zerosetKfR R1, we know z is not in the zero set
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2

  -- Unfold Bf definition
  unfold Bf

  -- Unfold Cf definition and use the else branch since z ∉ zerosetKfR R1
  unfold Cf
  simp [hz_not_in]

  -- Now we have: (f z / ∏ ρ, (z - ρ)^m) * ∏ ρ, Blaschke_factor = goal
  -- Use div_mul_eq_mul_div: (a / b) * c = (a * c) / b
  exact div_mul_eq_mul_div _ _ _

lemma lem_Bf_div
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    (∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) /
    (∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat) =
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat /
       (z - ρ) ^ (analyticOrderAt f ρ).toNat) := by
  rw [Finset.prod_div_distrib]

lemma lem_Bf_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z * ∏ ρ ∈ h_finite_zeros.toFinset,
      (((R : ℂ) - star ρ * z / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat := by
  -- Start with lem_BfCf to get the initial form
  rw [lem_BfCf h_finite_zeros h_σ z hz]
  -- Use mul_div_assoc to rearrange f z * (A / B) = f z * A / B
  rw [mul_div_assoc]
  -- Work on the division part using congr
  congr 1
  -- Apply lem_Bf_div with explicit parameters
  rw [@lem_Bf_div R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros z hz]
  -- Turn each ratio's numerator/denominator powers into a power of the ratio
  simp only [div_pow]


lemma lem_frho_zero_contra
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) : f ρ ≠ 0 → ρ ∉ zerosetKfR R1 (by linarith) f := by
  intro h_f_rho_ne_zero h_rho_in_KfR1
  -- From membership in zerosetKfR, we get f ρ = 0
  have h_f_rho_zero : f ρ = 0 := h_rho_in_KfR1.2
  -- This contradicts the assumption that f ρ ≠ 0
  exact h_f_rho_ne_zero h_f_rho_zero

lemma lem_f_is_nonzero (f : ℂ → ℂ) : f 0 ≠ 0 → f ≠ 0 := by
  intro h_f_zero_ne_zero h_f_eq_zero
  -- If f = 0, then f 0 = 0
  have h_f_at_zero_eq_zero : f 0 = 0 := by
    rw [h_f_eq_zero]
    simp
  -- This contradicts f 0 ≠ 0
  exact h_f_zero_ne_zero h_f_at_zero_eq_zero


theorem lem_rho_in_disk_R1
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    norm ρ ≤ R1 := by
  -- By definition of zerosetKfR, ρ is in the closed ball of radius R1
  have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
  -- In a closed ball, the distance from center is at most the radius
  rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
  simp only [sub_zero] at h_in_ball
  exact h_in_ball


theorem lem_zero_not_in_Kf (R R1 : ℝ)
  (hR1_pos : 0 < R1)
  (hR1_lt_R : R1 < R)
  (f : ℂ → ℂ)
  (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z) :
    f 0 ≠ 0 → 0 ∉ zerosetKfR R1 (by linarith) f := by
  intro h_f_zero_ne_zero h_zero_in_KfR1
  -- From membership in zerosetKfR, we get f 0 = 0
  have h_f_zero_eq_zero : f 0 = 0 := h_zero_in_KfR1.2
  -- This contradicts the assumption that f 0 ≠ 0
  exact h_f_zero_ne_zero h_f_zero_eq_zero


lemma lem_rho_ne_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f, ρ ≠ 0 := by
  intro ρ h_ρ_in_zeros h_ρ_eq_zero
  -- If ρ = 0, then ρ ∈ zerosetKfR implies 0 ∈ zerosetKfR
  rw [h_ρ_eq_zero] at h_ρ_in_zeros
  -- But this contradicts lem_zero_not_in_Kf
  have h_zero_not_in : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  exact h_zero_not_in h_ρ_in_zeros


theorem lem_mod_rho_pos
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ (ρ : ℂ), ρ ∈ zerosetKfR R1 (by linarith) f → norm ρ > 0 := by
  intro ρ h_ρ_in_zeros
  -- First show that ρ ≠ 0
  have h_ρ_ne_zero : ρ ≠ 0 :=
    lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
  -- Now use the lemma that norm is positive for nonzero elements
  exact norm_pos_iff.mpr h_ρ_ne_zero


theorem lem_rho_in_disk_R1_repeat (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    norm ρ ≤ R1 :=
  lem_rho_in_disk_R1 R R1 hR1_pos hR1_lt_R f ρ h_rho_in_KfR1


lemma lem_inv_mod_rho_ge_inv_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    1 / norm ρ ≥ 1 / R1 := by
  -- From membership in zerosetKfR, we know |ρ| ≤ R1
  have h_abs_ρ_le_R1 : norm ρ ≤ R1 :=
    lem_rho_in_disk_R1 R R1 hR1_pos hR1_lt_R f ρ h_rho_in_KfR1
  -- We need |ρ| > 0 to apply the inverse monotonicity lemma
  have h_abs_ρ_pos : norm ρ > 0 :=
    lem_mod_rho_pos R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
  -- We need R1 > 0
  have h_R1_pos : R1 > 0 := by
    linarith
  -- Apply inverse monotonicity: if 0 < |ρ| ≤ R1, then 1/R1 ≤ 1/|ρ|
  exact one_div_le_one_div_of_le h_abs_ρ_pos h_abs_ρ_le_R1


theorem lem_R_div_mod_rho_ge_R_div_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ R / R1 := by
  -- Get the inverse inequality: 1/|ρ| ≥ 1/R1
  have h_inv_ineq : 1 / norm ρ ≥ 1 / R1 :=
    lem_inv_mod_rho_ge_inv_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
  -- Since multiplication by R > 0 preserves inequality direction
  -- R * (1/|ρ|) ≥ R * (1/R1) becomes R/|ρ| ≥ R/R1
  have h_R_div_abs_ρ_eq : R * (1 / norm ρ) = R / norm ρ := by ring
  have h_R_div_R1_eq : R * (1 / R1) = R / R1 := by ring
  rw [← h_R_div_abs_ρ_eq, ← h_R_div_R1_eq]
  exact mul_le_mul_of_nonneg_left h_inv_ineq (by linarith)

theorem lem_R_div_mod_rho_ge_R_over_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ (R/R1 : ℝ) := by
  -- First show R / |ρ| ≥ R / R1
  have h_ineq1 : R / norm ρ ≥ R / R1 :=
    lem_R_div_mod_rho_ge_R_div_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
  -- Then show R / R1 = 3/2
  linarith


lemma lem_mod_Bf_is_prod_mod (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ)
    (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat‖ := by
  -- Use definition of Bf: Bf z = Cf z * ∏ ρ, ((R - star ρ * z / R)^{m_ρ})
  unfold Bf
  rw [norm_mul]
  -- Use norm_prod to distribute norm over the product
  rw [norm_prod]
  -- When z ∉ zerosetKfR R1, we have Cf z = f z / ∏ ρ, (z - ρ)^{m_ρ} by definition
  have hCf : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp only [hz, ↓reduceDIte]
  rw [hCf, norm_div]
  -- Apply norm_prod to the denominator
  rw [norm_prod]
  -- Rearrange: (‖f z‖ / ∏‖(z-ρ)^{m_ρ}‖) * ∏‖(R - star ρ * z / R)^{m_ρ}‖
  rw [div_mul_eq_mul_div]
  -- Use properties of products to combine: ‖f z‖ * (∏‖(R - star ρ * z / R)^{m_ρ}‖ / ∏‖(z-ρ)^{m_ρ}‖)
  rw [mul_div_assoc]
  -- Use Finset.prod_div_distrib: ∏(a/b) = (∏a)/(∏b)
  rw [← Finset.prod_div_distrib]
  congr 2
  ext ρ
  -- Show ‖a^n‖ / ‖b^n‖ = ‖(a/b)^n‖
  rw [← norm_div, ← div_pow]
  congr 2
  -- Show star ρ * z = z * star ρ by commutativity
  ring


lemma lem_mod_Bf_prod_mod (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
  (z : ℂ)
  (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
  -- Apply lem_mod_Bf_is_prod_mod to get the first form (use hz that z ∉ zeroset)
  have h1 := lem_mod_Bf_is_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  rw [h1]
  -- Now use norm_pow to transform each term in the product
  congr 2
  ext ρ
  rw [norm_pow]

lemma lem_mod_Bf_at_0 (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖((R : ℂ) / (-ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
  -- Apply the general result at z = 0 (0 is not in the zero set by lem_zero_not_in_Kf)
  have hz0 : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec 0 hz0]
  -- Now simplify: when z = 0, we have ((R - 0 * star ρ / R) / (0 - ρ)) = R / (-ρ)
  congr 2
  ext ρ
  congr 1
  simp only [zero_mul, zero_div, sub_zero, zero_sub]

lemma lem_mod_neg (w : ℂ) : ‖-w‖ = ‖w‖ := by
  simp

lemma lem_mod_div_and_neg (R : ℝ) (hR_pos : 0 < R) (ρ : ℂ) (h_rho_ne_zero : ρ ≠ 0) :
  ‖(R : ℂ) / (-ρ)‖ = R / ‖ρ‖ := by
  -- Use division formula for abs, abs of real, and abs of neg
  have hdiv := norm_div (R : ℂ) (-ρ)
  have hnorm_real : ‖(R : ℂ)‖ = |R| := by simp
  calc
    ‖(R : ℂ) / (-ρ)‖ = ‖(R : ℂ)‖ / ‖-ρ‖ := hdiv
    _ = ‖(R : ℂ)‖ / ‖ρ‖ := by simp [norm_neg]
    _ = |R| / ‖ρ‖ := by simp [hnorm_real]
    _ = R / ‖ρ‖ := by simp [abs_of_pos hR_pos]


theorem lem_mod_Bf_at_0_eval  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
  -- Start with lem_mod_Bf_at_0
  rw [lem_mod_Bf_at_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec]
  -- Now we need to show the products are equal
  congr 1
  -- Use Finset.prod_congr to show the products are equal
  apply Finset.prod_congr rfl
  intro ρ hρ
  -- We need to show ‖((R : ℂ) / (-ρ))‖ ^ (analyticOrderAt f ρ).toNat = (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat
  -- This follows from lem_mod_div_and_neg if ρ ≠ 0
  have h_ρ_ne_zero : ρ ≠ 0 := by
    -- ρ is in h_finite_zeros.toFinset, so it's in zerosetKfR
    have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
      exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
    exact lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
  -- Apply lem_mod_div_and_neg to rewrite the norm
  rw [lem_mod_div_and_neg R (by linarith) ρ h_ρ_ne_zero]


lemma lem_mod_of_pos_real (x : ℝ) (hx : 0 < x) : abs x = x := by
  exact abs_of_pos hx


theorem lem_mod_Bf_at_0_as_ratio  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
  exact lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec

lemma lem_prod_ineq {ι : Type*} (K : Finset ι) (a b : ι → ℝ)
    (h_nonneg : ∀ ρ ∈ K, 0 ≤ a ρ) (h_le : ∀ ρ ∈ K, a ρ ≤ b ρ) :
    ∏ ρ ∈ K, a ρ ≤ ∏ ρ ∈ K, b ρ := by
  exact Finset.prod_le_prod h_nonneg h_le


lemma lem_power_ineq (n : ℕ) (c : ℝ) (hc : c > 1) (hn : n ≥ 1) : c ≤ c ^ n := by
  rcases n with _ | n
  · -- n = 0, contradiction with hn : n ≥ 1
    omega
  · -- n = n + 1, so c ≤ c^(n+1)
    have h_c_ge_1 : 1 ≤ c := le_of_lt hc
    rw [pow_succ]
    -- c ≤ c * c^n since c ≥ 1 and c^n ≥ 1
    have h_c_pow_n_ge_1 : 1 ≤ c ^ n := by exact one_le_pow₀ h_c_ge_1
    calc c = c * 1 := (mul_one c).symm
    _ ≤ c * c ^ n := mul_le_mul_of_nonneg_left h_c_pow_n_ge_1 (le_of_lt (lt_trans zero_lt_one hc))
    _ = c ^ n * c := mul_comm (c) (c ^ n)


lemma lem_power_ineq_1 (n : ℕ) (c : ℝ) (hc : 1 ≤ c) (hn : 1 ≤ n) : 1 ≤ c ^ n := by
  exact one_le_pow₀ hc


lemma lem_prod_power_ineq {ι : Type*} (K : Finset ι) (c : ι → ℝ) (n : ι → ℕ)
    (h_c_ge_1 : ∀ ρ ∈ K, 1 ≤ c ρ)
    (h_n_ge_1 : ∀ ρ ∈ K, 1 ≤ n ρ) :
    ∏ ρ ∈ K, (c ρ) ^ (n ρ) ≥ 1 := by
  classical
  induction K using Finset.induction with
  | empty => simp
  | insert i s h_not_in ih =>
    rw [Finset.prod_insert h_not_in]
    have h_pow_ge_1 : 1 ≤ c i ^ n i :=
      one_le_pow₀ (h_c_ge_1 i (Finset.mem_insert_self i s))
    have h_prod_ge_1 : 1 ≤ ∏ ρ ∈ s, (c ρ) ^ (n ρ) := by
      apply ih
      · intro ρ hρ; exact h_c_ge_1 ρ (Finset.mem_insert_of_mem hρ)
      · intro ρ hρ; exact h_n_ge_1 ρ (Finset.mem_insert_of_mem hρ)
    exact one_le_mul_of_one_le_of_one_le h_pow_ge_1 h_prod_ge_1


theorem lem_prod_1 {ι : Type*} {M : Type*} [CommMonoid M] (K : Finset ι) : ∏ _ρ ∈ K, (1 : M) = 1 := by
  exact Finset.prod_const_one


lemma lem_prod_power_ineq1 {ι : Type*} (K : Finset ι) (c : ι → ℝ) (n : ι → ℕ)
    (h_c_ge_1 : ∀ ρ ∈ K, 1 ≤ c ρ) (h_n_ge_1 : ∀ ρ ∈ K, 1 ≤ n ρ) :
    ∏ ρ ∈ K, (c ρ) ^ (n ρ) ≥ 1 := by
  exact lem_prod_power_ineq K c n h_c_ge_1 h_n_ge_1


lemma lem_mod_lower_bound_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (hR_lt_1 : R < 1) :  -- ADD THIS
    ∏ ρ ∈ h_finite_zeros.toFinset,
      (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat ≥ 1 := by
  classical
  set K := h_finite_zeros.toFinset

  have h_base_ge_1 : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have h :=
    lem_prod_ineq K (fun _ : ℂ => (1 : ℝ))
      (fun ρ : ℂ => (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
      (by intro ρ hρ; norm_num)
      (by
        intro ρ hρ
        simpa using (one_le_pow₀ (by linarith [h_base_ge_1])))
  simpa [K] using h

theorem lem_mod_Bf_at_0_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≥ 1 := by
  -- First derive f 0 ≠ 0 from f 0 = 1
  have R_over_R1_nonneg : 1 < R / R1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have R_over_R1_nonneg : 0 ≤ R / R1 := by linarith
  have h_f_nonzero_at_zero : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
  -- Use lem_mod_Bf_at_0_as_ratio to express ‖Bf ... 0‖ as a product
  rw [lem_mod_Bf_at_0_as_ratio R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros]
  -- Since f 0 = 1, we have ‖f 0‖ = 1
  rw [hf0_eq_one, norm_one, one_mul]
  -- Show that the product ∏ (R / ‖ρ‖)^n ≥ ∏ (3/2)^n
  have h_prod_ge : ∏ ρ ∈ h_finite_zeros.toFinset, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat ≥
                   ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat := by
    apply Finset.prod_le_prod
    -- Show (3/2)^n ≥ 0
    · intro ρ hρ
      apply pow_nonneg
      apply R_over_R1_nonneg
    -- Show (R / ‖ρ‖)^n ≥ (3/2)^n for each ρ
    · intro ρ hρ
      have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
        exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
      -- We have R / norm ρ ≥ 3/2, and ‖ρ‖ = norm ρ
      have h_ratio_ge : R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
        -- norm is defined as ‖z‖, so they are equal
        have h_norm_abs_eq : ‖ρ‖ = norm ρ := by rfl
        rw [h_norm_abs_eq]
        exact lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros

      -- Use power monotonicity: if a ≥ b > 0, then a^n ≥ b^n
      have h_3_2_pos : (1 : ℝ) < (R/R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
      have h_3_2_pos : (0 : ℝ) < (R/R1 : ℝ) := by linarith
      have h_ratio_pos : (0 : ℝ) ≤ R / ‖ρ‖ := by
        linarith [h_ratio_ge]
      exact pow_le_pow_left₀ R_over_R1_nonneg h_ratio_ge (analyticOrderAt f ρ).toNat
  -- Use lem_mod_lower_bound_1: the (3/2)^n product is ≥ 1
  have h_3_2_prod_ge_1 : ∏ ρ ∈ h_finite_zeros.toFinset, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat ≥ 1 :=
    lem_mod_lower_bound_1 R R1 hR1_pos hR1_lt_R f h_f_analytic hf0_eq_one h_finite_zeros hR_lt_1
  -- Combine: 1 ≤ (3/2)^n product ≤ (R/‖ρ‖)^n product
  exact le_trans h_3_2_prod_ge_1 h_prod_ge
  assumption

lemma lem_linear_factor_analytic (R : ℝ) (hR_pos : 0 < R) (ρ : ℂ) (z : ℂ) :
  AnalyticAt ℂ (fun w => (R : ℂ) - star ρ * w / (R : ℂ)) z := by
  -- The function is (R : ℂ) - star ρ * w / (R : ℂ)
  -- This is an affine function: constant - (constant / constant) * w
  -- We can rewrite as: (R : ℂ) - (star ρ / (R : ℂ)) * w

  -- First show that (R : ℂ) is analytic (constant function)
  have h_const : AnalyticAt ℂ (fun _ => (R : ℂ)) z := analyticAt_const

  -- Show that w ↦ w is analytic (identity function)
  have h_id : AnalyticAt ℂ (fun w => w) z := analyticAt_id

  -- Show that star ρ / (R : ℂ) is a nonzero constant since R > 0
  have h_const_coeff : AnalyticAt ℂ (fun _ => star ρ / (R : ℂ)) z := analyticAt_const

  -- Show that the multiplication (star ρ / (R : ℂ)) * w is analytic
  have h_mul : AnalyticAt ℂ (fun w => star ρ / (R : ℂ) * w) z :=
    AnalyticAt.fun_mul h_const_coeff h_id

  -- Show that the subtraction is analytic
  have h_sub : AnalyticAt ℂ (fun w => (R : ℂ) - star ρ / (R : ℂ) * w) z :=
    AnalyticAt.fun_sub h_const h_mul

  -- The original function equals this by algebra
  convert h_sub using 1
  ext w
  ring

lemma lem_pow_analyticAt {g : ℂ → ℂ} (n : ℕ) (w : ℂ) :
  AnalyticAt ℂ g w → AnalyticAt ℂ (fun z => (g z) ^ n) w := by
  intro hg
  exact AnalyticAt.fun_pow hg n

lemma lem_finset_prod_analyticAt {α : Type*} {S : Finset α} {g : α → ℂ → ℂ} (w : ℂ) :
  (∀ a ∈ S, AnalyticAt ℂ (g a) w) → AnalyticAt ℂ (fun z => ∏ a ∈ S, g a z) w := by
  intro h
  classical
  induction S using Finset.induction with
  | empty =>
    -- Base case: empty finset, product is 1 (constant function)
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | insert a s ha ih =>
    -- Inductive step: insert element a into finset s
    simp only [Finset.prod_insert ha]
    -- Product becomes g a z * (∏ b ∈ s, g b z)
    apply AnalyticAt.fun_mul
    · -- g a is analytic at w
      apply h
      exact Finset.mem_insert_self a s
    · -- Product over s is analytic at w by inductive hypothesis
      apply ih
      intro b hb
      apply h
      exact Finset.mem_insert_of_mem hb

lemma analyticOrderAt_top_iff_eventually_zero (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) :
  analyticOrderAt f z = ⊤ ↔ ∀ᶠ w in nhds z, f w = 0 := by
  simp [analyticOrderAt, hf]

lemma isPreconnected_closedBall (x : ℂ) (r : ℝ) : IsPreconnected (Metric.closedBall x r) := by
  -- Closed balls are convex
  have h_convex : Convex ℝ (Metric.closedBall x r) := convex_closedBall _ _
  -- Convex sets are preconnected
  exact h_convex.isPreconnected

lemma Set.infinite_Icc_of_lt {a b : ℝ} (h : a < b) : (Set.Icc a b).Infinite := by
  -- Proof by contradiction
  intro h_finite
  -- The open interval (a,b) is a subset of [a,b]
  have h_subset : Set.Ioo a b ⊆ Set.Icc a b := Set.Ioo_subset_Icc_self
  -- If [a,b] is finite, then (a,b) is finite as a subset
  have h_Ioo_finite : (Set.Ioo a b).Finite := h_finite.subset h_subset
  -- But (a,b) is infinite for a < b
  have h_Ioo_infinite : (Set.Ioo a b).Infinite := Set.Ioo_infinite h
  -- This is a contradiction
  exact h_Ioo_infinite h_Ioo_finite

lemma infinite_closedBall_of_pos (x : ℂ) (r : ℝ) (hr : 0 < r) : (Metric.closedBall x r).Infinite := by
  -- We'll show the closed ball contains an infinite line segment
  -- Consider the horizontal line segment from x in the real direction
  let f : ℝ → ℂ := fun t => x + t

  -- Show that f maps [0, r/2] into the closed ball
  have h_maps_to : Set.MapsTo f (Set.Icc 0 (r/2)) (Metric.closedBall x r) := by
    intro t ht
    rw [Metric.mem_closedBall]
    -- Need to show: dist (f t) x ≤ r
    have h_eq : f t = x + t := rfl
    rw [h_eq, Complex.dist_eq, add_sub_cancel_left]
    -- Now need to show: ‖(t : ℂ)‖ ≤ r
    have h_norm : ‖(t : ℂ)‖ = |t| := by
      exact Complex.norm_real t
    rw [h_norm, abs_of_nonneg ht.1]
    exact le_trans ht.2 (le_of_lt (half_lt_self hr))

  -- f is injective on [0, r/2]
  have h_inj : Set.InjOn f (Set.Icc 0 (r/2)) := by
    intro s hs t ht h_eq
    have : x + s = x + t := h_eq
    have : (s : ℂ) = (t : ℂ) := add_left_cancel this
    exact Complex.ofReal_inj.mp this

  -- The interval [0, r/2] is infinite
  have h_infinite_interval : (Set.Icc (0:ℝ) (r/2)).Infinite :=
    Set.infinite_Icc_of_lt (half_pos hr)

  -- Therefore the image f '' [0, r/2] is infinite
  have h_infinite_image : (f '' Set.Icc 0 (r/2)).Infinite :=
    Set.Infinite.image h_inj h_infinite_interval

  -- The image is contained in the closed ball
  have h_subset : f '' Set.Icc 0 (r/2) ⊆ Metric.closedBall x r :=
    Set.MapsTo.image_subset h_maps_to

  -- Use contradiction: if the closed ball were finite, its subset would be finite
  intro h_finite
  exact h_infinite_image (h_finite.subset h_subset)

lemma analyticOrderAt_ne_top_of_finite_zeros_in_ball (f : ℂ → ℂ) (R : ℝ) (hR_pos : 0 < R)
    (hf_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) R, AnalyticAt ℂ f z)
    (ρ : ℂ) (hρ_zero : f ρ = 0) (hρ_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R)
    (h_finite_zeros : {z ∈ Metric.closedBall (0 : ℂ) R | f z = 0}.Finite) :
    analyticOrderAt f ρ ≠ ⊤ := by
  -- Proof by contradiction
  by_contra htop
  -- From order = ⊤ we get that f is eventually zero near ρ
  have h_eventually_zero : ∀ᶠ z in nhds ρ, f z = 0 := by
    rw [← analyticOrderAt_top_iff_eventually_zero f ρ (hf_analytic ρ hρ_in_ball)]
    exact htop
  -- f is analytic on a neighborhood of the closed ball
  have hf_on_ball : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R) := by
    intro z
    exact hf_analytic z
  -- The closed ball is preconnected
  have h_preconn : IsPreconnected (Metric.closedBall (0 : ℂ) R) :=
    isPreconnected_closedBall (0 : ℂ) R
  -- By identity principle, f = 0 on the closed ball
  have h_eqOn_zero : Set.EqOn f 0 (Metric.closedBall (0 : ℂ) R) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf_on_ball h_preconn hρ_in_ball h_eventually_zero
  -- Hence every point in the closed ball is a zero
  have h_all_zeros : ∀ z ∈ Metric.closedBall (0 : ℂ) R, f z = 0 := by
    intro z hz
    have := h_eqOn_zero hz
    simpa [Pi.zero_apply] using this
  -- This means the zero set equals the entire closed ball
  have h_zero_set_eq : {z ∈ Metric.closedBall (0 : ℂ) R | f z = 0} = Metric.closedBall (0 : ℂ) R := by
    ext z
    constructor
    · intro hz; exact hz.1
    · intro hz; exact ⟨hz, h_all_zeros z hz⟩
  -- But the closed ball is infinite (for R > 0), contradicting finite zeros
  have h_ball_infinite : (Metric.closedBall (0 : ℂ) R).Infinite :=
    infinite_closedBall_of_pos (0 : ℂ) R hR_pos
  -- This contradicts the finite zeros assumption
  rw [h_zero_set_eq] at h_finite_zeros
  exact h_ball_infinite h_finite_zeros

theorem lem_Bf_is_analytic (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) := by
  -- By definition of AnalyticOnNhd
  intro z hz

  -- First show the finite Blaschke product factor is analytic at z
  have h_blaschke_linear : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => (R : ℂ) - star ρ * w / (R : ℂ)) z := by
    intro ρ hρ
    -- rewrite as constant + constant * w
    have h_eq : (fun w : ℂ => (R : ℂ) - star ρ * w / (R : ℂ)) =
                (fun w : ℂ => (R : ℂ) + (-(star ρ) / (R : ℂ)) * w) := by
      funext w
      field_simp
      ring
    rw [h_eq]
    exact AnalyticAt.fun_add analyticAt_const (AnalyticAt.fun_mul analyticAt_const analyticAt_id)

  have h_powers : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    exact (h_blaschke_linear ρ hρ).fun_pow _

  have h_product : AnalyticAt ℂ (fun w => ∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
    -- use the reusable lemma for finset products of analytic functions
    apply lem_finset_prod_analyticAt z
    intro ρ hρ
    apply h_powers
    exact hρ
  -- Now handle two cases: z is in the finite zero set or not
  by_cases hz_in : z ∈ zerosetKfR R1 (by linarith) f
  · -- z is a zero: use the local factor specification to get analyticity of Cf at σ
    have h_cf_at_sigma := @lem_Cf_analytic_at_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in
    -- Multiply analytic functions to get analyticity of Bf = Cf * product
    exact AnalyticAt.fun_mul h_cf_at_sigma h_product

  · -- z is not a zero: Cf is analytic off the zero set
    have hz_in_compl : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f := by
      constructor
      · exact hz
      · exact hz_in
    have h_cf_off := @lem_Cf_analytic_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in_compl
    exact AnalyticAt.fun_mul h_cf_off h_product

lemma complex_mul_star_eq_norm_sq (z : ℂ) : z * star z = (‖z‖ ^ 2 : ℂ) := by
  -- Use the fact that star = conj for complex numbers
  rw [Complex.star_def]
  -- Now use Complex.mul_conj': z * conj z = ‖z‖ ^ 2
  exact Complex.mul_conj' z

lemma lem_mod_Bf_eq_mod_f_on_boundary (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ = ‖f z‖ := by
  intro z hz
  -- Use the factorization from lem_mod_Bf_prod_mod; first show z ∉ zerosetKfR
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := by
    intro h_in
    -- h_in says z ∈ closedBall (0, R1), so ‖z‖ ≤ R1
    have h_norm_le_R1 : ‖z‖ ≤ R1 := by simpa [sub_zero] using (h_in.1 : z ∈ Metric.closedBall (0 : ℂ) R1)
    -- hz gives ‖z‖ = R, and R1 < R, contradiction
    have h_norm_eq_R : ‖z‖ = R := by simpa using hz
    linarith [h_norm_le_R1, h_norm_eq_R, hR1_lt_R]
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_not_in]

  -- Show each Blaschke factor has norm 1 when |z| = R
  have h_each_factor_one : ∀ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ = 1 := by
    intro ρ hρ

    -- First, we need z ≠ ρ (if z = ρ, we get a contradiction since |z| = R > R1 but ρ ∈ ball(0, R1))
    have z_ne_rho : z ≠ ρ := by
      intro h_eq
      have rho_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
      have rho_bound : ‖ρ‖ ≤ R1 := by
        have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := rho_in_zeros.1
        rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
        simpa using h_in_ball
      have R1_lt_R : R1 < R := by linarith
      rw [← h_eq, hz] at rho_bound
      linarith [R1_lt_R]

    -- Now prove the Blaschke factor has norm 1
    rw [Complex.norm_div]

    -- Use z * star z = ‖z‖² = R² when |z| = R
    have z_conj_eq : z * star z = (R ^ 2 : ℂ) := by
      rw [complex_mul_star_eq_norm_sq z, hz, pow_two]

    -- Rewrite numerator: R - z * star ρ / R = (R² - z * star ρ) / R
    have num_rewrite : (R : ℂ) - z * star ρ / (R : ℂ) = ((R : ℂ)^2 - z * star ρ) / (R : ℂ) := by
      field_simp [ne_of_gt hR1_pos]

    rw [num_rewrite, Complex.norm_div]

    -- Key step: R² - z * star ρ = z * star(z - ρ) using z * star z = R²
    have factor_eq : (R : ℂ)^2 - z * star ρ = z * star (z - ρ) := by
      rw [← z_conj_eq, star_sub]
      ring

    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    field_simp
    have hnorm_cast : ‖(↑‖z‖ : ℂ)‖ = ‖z‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
    have hz_ne : ‖z‖ ≠ 0 := by
      rw [hz]; linarith [hR1_pos, hR1_lt_R]
    have hzρ_ne : ‖z - ρ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z_ne_rho)
    rw [hnorm_cast, mul_comm ‖z - ρ‖ ‖z‖]
    exact div_self (mul_ne_zero hz_ne hzρ_ne)


  -- Apply this to show the product equals 1
  have h_prod_one : ∏ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat = 1 := by
    -- Each factor equals 1, and 1^n = 1
    rw [← Finset.prod_congr rfl (fun ρ hρ => by rw [h_each_factor_one ρ hρ, one_pow])]
    rw [Finset.prod_const_one]

  rw [h_prod_one, mul_one]


lemma lem_Bf_bounded_on_boundary (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  -- proof body needs updating to use hR_lt_1
  intro z hz
  have hz_le : ‖z‖ ≤ R := le_of_eq hz
  have h_eq :=
    lem_mod_Bf_eq_mod_f_on_boundary R R1 (by linarith) hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  simpa [h_eq] using hf_le_B z hz_le

lemma norm_eq_radius_of_mem_sphere (w : ℂ) (R : ℝ) (hw : w ∈ Metric.sphere (0 : ℂ) R) : ‖w‖ = R := by
  have hdist : dist w (0 : ℂ) = R := by simpa [Metric.sphere] using hw
  simpa [Complex.dist_eq, sub_zero] using hdist

lemma mem_closedBall_of_norm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  have : dist z (0 : ℂ) ≤ R := by simpa [Complex.dist_eq, sub_zero] using hz
  simpa [Metric.closedBall] using this

lemma closure_ball_eq_closedBall_center (R : ℝ) (hR : 0 < R) :
  closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := by
  simpa using (closure_ball (x := (0 : ℂ)) (r := R) (ne_of_gt hR))

lemma lem_max_mod_principle_for_Bf (B R : ℝ) (hB : 1 < B) (hR_pos : 0 < R)
    (fB : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ fB (Metric.closedBall (0 : ℂ) R))
  (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R → ‖fB z‖ ≤ B) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖fB z‖ ≤ B := by
  intro z hz
  -- Prepare nonnegativity of B
  have hB0 : 0 ≤ B := le_of_lt (lt_trans zero_lt_one hB)
  -- Convert analytic assumption to the form required by Hard MMP
  have h_an_on_closure : AnalyticOn ℂ fB (closure (Metric.ball (0 : ℂ) R)) := by
    simpa [closure_ball_eq_closedBall_center R hR_pos] using h_analytic.analyticOn
  -- Apply Hard maximum modulus principle on the closed ball of radius R
  have h_le :=
    lem_HardMMP R B hR_pos hB0 fB h_an_on_closure (by
      intro z hzR; exact h_bd_boundary z hzR)
  -- It remains to see that z belongs to the closure of the open ball of radius R
  have hz_cl : z ∈ closure (Metric.ball (0 : ℂ) R) := by
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_of_norm_le hz
    simpa [closure_ball_eq_closedBall_center R hR_pos] using hz_closed
  exact h_le z hz_cl


lemma lem_Bf_bounded_in_disk_from_boundary (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  have hA := lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec
  exact lem_max_mod_principle_for_Bf B R hB (by linarith)
    (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) hA h_bd_boundary


lemma lem_Bf_bounded_in_disk_from_f (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  intro z hz
  have h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B :=
    lem_Bf_bounded_on_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  exact (lem_Bf_bounded_in_disk_from_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec h_bd_boundary) z hz


lemma lem_Bf_at_0_le_M (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≤ B := by
  have h :=
    lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  have h0 : ‖(0 : ℂ)‖ ≤ R := by simpa using (le_of_lt (by linarith))
  simpa using h 0 h0


lemma lem_combine_bounds_on_Bf0 (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hBf0 : ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat : ℝ) ≤ B := by
  classical
  -- Abbreviate the finite set of zeros
  set K := h_finite_zeros.toFinset
  -- Evaluate ‖Bf(0)‖ in terms of the product over zeros
  have hf0_ne0 : f 0 ≠ 0 := by simp [hf0_eq_one]
  have hf0_norm : ‖f 0‖ = 1 := by simp [hf0_eq_one]
  have h_eval0 :=
    lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic hf0_ne0 h_finite_zeros h_σ h_σ_spec
  have h_eval_prod :
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖
        = ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
    rw [h_eval0, hf0_norm, one_mul]
  -- For each zero ρ ∈ K, we have R/‖ρ‖ ≥ 3/2
  have h_base_ge : ∀ ρ ∈ K, R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
    intro ρ hρK
    have hρ_in : ρ ∈ zerosetKfR R1 (by linarith) f := by simpa [K] using hρK
    simpa using
      (lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic hf0_ne0 ρ hρ_in)
  -- Compare products termwise and combine
  have R_over_R1_nonneg : 0 ≤ R/R1 := by
    have : 0 ≤ R := by linarith
    apply div_nonneg (by assumption) (le_of_lt hR1_pos)
  have h_prod_le :
      ∏ ρ ∈ K, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat
        ≤ ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
    refine lem_prod_ineq K
      (fun ρ => (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
      (fun ρ => (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat)
      ?h_nonneg ?h_le
    · intro ρ hρK; exact pow_nonneg (R_over_R1_nonneg) _
    · intro ρ hρK
      exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ R / R1) (h_base_ge ρ hρK) _
  have h_prod_le_B :
      ∏ ρ ∈ K, (R / R1: ℝ) ^ (analyticOrderAt f ρ).toNat ≤ B := by
    have h_right : ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat =
        ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ := by
      simp [h_eval_prod]
    exact le_trans h_prod_le (by simpa [h_right] using hBf0)
  -- Convert the product of powers to a single power with exponent the sum of exponents
  have h_prod_pow_sum :
      (∏ ρ ∈ K, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
        = (R/R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderAt f ρ).toNat) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum K (fun ρ => (analyticOrderAt f ρ).toNat) (R/R1 : ℝ))
  -- Now we have a bound on (3/2)^(sum m_ρ) with a natural-number exponent
  have h_natPow : (R / R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderAt f ρ).toNat) ≤ B := by
    simpa [h_prod_pow_sum] using h_prod_le_B
  -- Let S be that natural sum of multiplicities
  set S : ℕ := ∑ ρ ∈ K, (analyticOrderAt f ρ).toNat
  have h_natPowS : (R / R1 : ℝ) ^ S ≤ B := by simpa [S] using h_natPow
  -- Convert to real exponent using Real.rpow_natCast
  have h_rpowS : (R / R1 : ℝ) ^ (S : ℝ) ≤ B := by
    -- rewrite the left-hand side using rpow_natCast
    simpa [(Real.rpow_natCast (R / R1 : ℝ) S)] using h_natPowS
  -- Finally, rewrite S back as the sum over K and K as the toFinset
  have h_cast_sum : (S : ℝ)
      = (∑ ρ ∈ K, ((analyticOrderAt f ρ).toNat : ℝ)) := by
    simp [S]
  -- Conclude by rewriting the exponent
  have : (R / R1 : ℝ) ^ (∑ ρ ∈ K, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ B := by
    simpa [h_cast_sum] using h_rpowS
  simpa [K] using this

end AnalyticZeroCounting
