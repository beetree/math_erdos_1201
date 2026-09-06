module

public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Erdos1201.Vendor.Analysis.DiskAnalyticBounds.BorelCaratheodoryI

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
The Cauchy integral formula for the derivative on a disk (as a circle
integral and its real-parameter form), the resulting `‖f'‖` bound, and
Borel–Carathéodory II: the derivative-strength Borel–Carathéodory bound
`‖f'(z)‖ ≤ 16MR²/(R−r)³`.
-/

public section

namespace DiskAnalyticBounds

def I := Complex.I

lemma cauchy_formula_deriv {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r_int), (w - z)⁻¹ ^ 2 • f w := by
  -- Extract the witness from hf_domain
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain

  -- Show z is in the ball of radius r_int
  have hz_in_ball : z ∈ Metric.ball (0 : ℂ) r_int := by
    apply Metric.mem_ball.mpr
    have h1 : ‖z - 0‖ ≤ r_z := by
      have := Metric.mem_closedBall.mp hz
      rwa [dist_eq_norm] at this
    simp only [sub_zero] at h1
    have h2 : ‖z‖ < r_int := lt_of_le_of_lt h1 h_r_z_lt_r_int
    rwa [dist_eq_norm, sub_zero]

  -- Use U = ball 0 R_analytic as our open set
  set U := Metric.ball (0 : ℂ) R_analytic

  -- Show closedBall 0 r_int ⊆ U
  have hc_subset : Metric.closedBall (0 : ℂ) r_int ⊆ U := by
    apply Metric.closedBall_subset_ball
    exact h_r_int_lt_R_analytic

  -- Show f is differentiable on U
  have hf_on_U : DifferentiableOn ℂ f U := by
    -- Since Metric.ball 0 R_analytic ⊆ Metric.closedBall 0 R_analytic ⊆ U'
    -- and f is differentiable on U', it's also differentiable on the smaller set U
    apply DifferentiableOn.mono hf_diff_U'
    calc U = Metric.ball 0 R_analytic := rfl
         _ ⊆ Metric.closedBall 0 R_analytic := Metric.ball_subset_closedBall
         _ ⊆ U' := h_subset

  -- Apply the Cauchy integral formula for derivatives
  have cauchy_eq := Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
    Metric.isOpen_ball hc_subset hf_on_U hz_in_ball

  -- Convert to our desired form
  rw [← cauchy_eq]

  -- The coefficients are equal and the integrands are equal
  congr 2
  · -- (2 * π * I)⁻¹ = 1 / (2 * Real.pi * I)
    simp only [one_div]
    -- Complex.I = I by definition
    rfl
  · -- ((w - z) ^ 2)⁻¹ • f w = (w - z)⁻¹ ^ 2 • f w
    ext w
    rw [← inv_pow]

lemma lem_dw_dt {r_int : ℝ} (t : ℝ) :
deriv (fun t' => r_int * Complex.exp (I * t')) t = I * r_int * Complex.exp (I * t) := by
  -- Apply constant multiplication rule
  rw [deriv_const_mul]
  -- Apply chain rule for complex exponential
  rw [deriv_cexp]
  -- Apply constant multiplication for I * t'
  rw [deriv_const_mul]
  -- Now we have: r_int * (Complex.exp (I * t) * (I * deriv (fun y => y) t))
  -- We need to show this equals I * r_int * Complex.exp (I * t)
  -- First, convert deriv (fun y => y) t to 1
  convert_to r_int * (Complex.exp (I * t) * (I * 1)) = I * r_int * Complex.exp (I * t)
  · -- Show that deriv (fun y => y) t = 1
    rw [← deriv_id]
    congr
  -- Now simplify the arithmetic
  ring
  -- Prove differentiability conditions (in reverse order as they appear in the goal)
  · exact differentiableAt_id
  · exact (differentiableAt_const I).mul differentiableAt_id
  · exact DifferentiableAt.cexp ((differentiableAt_const I).mul differentiableAt_id)

lemma circleMap_zero_eq_exp (r : ℝ) (t : ℝ) : circleMap 0 r t = r * Complex.exp (I * t) := by
  rw [circleMap_zero]
  unfold I
  rw [mul_comm (t : ℂ) Complex.I]

lemma lem_dw_dt_real {r_int : ℝ} (t : ℝ) :
deriv (fun (t' : ℝ) => r_int * Complex.exp (I * t')) t = I * r_int * Complex.exp (I * t) := by
  -- Apply constant multiplication rule
  rw [deriv_const_mul]
  -- Apply chain rule for complex exponential
  rw [deriv_cexp]
  -- Apply constant multiplication rule for I * t'
  rw [deriv_const_mul]
  -- Complex.ofReal is definitionally the coercion of Complex.ofRealCLM (Mathlib), whose
  -- derivative is given by `ContinuousLinearMap.deriv`.
  rw [show Complex.ofReal = ⇑Complex.ofRealCLM from rfl, ContinuousLinearMap.deriv]
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one]
  -- Simplify: r_int * (Complex.exp (I * t) * (I * 1)) = I * r_int * Complex.exp (I * t)
  ring
  -- Prove differentiability conditions (in reverse order as they appear), via Mathlib's
  -- `Complex.differentiable_ofReal`.
  · exact Complex.differentiable_ofReal.differentiableAt
  · exact (differentiableAt_const I).mul Complex.differentiable_ofReal.differentiableAt
  · exact DifferentiableAt.cexp ((differentiableAt_const I).mul Complex.differentiable_ofReal.differentiableAt)

lemma deriv_circleMap_zero (r : ℝ) (t : ℝ) : deriv (circleMap 0 r) t = I * r * Complex.exp (I * t) := by
  rw [deriv_circleMap, circleMap_zero_eq_exp]
  unfold I
  ring

lemma lem_CIF_deriv_param {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi * I)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(I * r_int * Complex.exp (I * t) * ((r_int * Complex.exp (I * t)) - z)⁻¹ ^ 2) * f (r_int * Complex.exp (I * t))) := by
  -- Apply cauchy_formula_deriv to get the circle integral form
  rw [cauchy_formula_deriv hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  -- Convert circle integral to parametric integral using circleIntegral_def_Icc
  rw [circleIntegral_def_Icc]

  -- Convert scalar multiplication to regular multiplication
  rw [smul_eq_mul]

  -- Substitute circleMap and its derivative
  simp only [circleMap_zero_eq_exp, deriv_circleMap_zero]

  -- Now we need to match the form: the integrand should be
  -- (I * r_int * Complex.exp (I * t)) • ((r_int * Complex.exp (I * t) - z)⁻¹ ^ 2 • f (r_int * Complex.exp (I * t)))
  -- which equals our target form
  congr 2
  ext t
  simp only [smul_eq_mul]
  ring

lemma mul_comm_div_cancel (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) : a * b / (b * a) = 1 := by
  -- Use commutativity to rewrite b * a as a * b
  rw [mul_comm b a]
  -- Now we have a * b / (a * b) = 1
  -- Use div_self with the fact that a * b ≠ 0
  apply div_self
  -- Show a * b ≠ 0
  exact mul_ne_zero ha hb

lemma complex_coeff_I_cancel : (1 : ℂ) / (2 * Real.pi * I) * I = 1 / (2 * Real.pi) := by
  field_simp [Complex.I_ne_zero, Real.pi_pos.ne']
  exact div_self Complex.I_ne_zero

lemma factor_I_from_integrand (f : ℂ → ℂ) (r_int : ℝ) (z : ℂ) :
  ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I * ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
  I * ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) := by
  -- Rewrite the left-hand side to separate I from the rest of the integrand
  -- The key insight is that I * (expression) = I • (expression) in ℂ
  have h : ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I * ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
           ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), I • (↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t))) := by
    congr 1
    ext t
    rw [smul_eq_mul]
    ring
  rw [h]
  -- Apply linearity of integration to factor out the scalar I
  rw [MeasureTheory.integral_smul]
  -- Convert scalar multiplication back to regular multiplication
  rw [smul_eq_mul]

lemma integrand_transform_div (f : ℂ → ℂ) (r_int : ℝ) (z : ℂ) (t : ℝ) :
  ↑r_int * Complex.exp (I * ↑t) * (↑r_int * Complex.exp (I * ↑t) - z)⁻¹ ^ 2 * f (↑r_int * Complex.exp (I * ↑t)) =
  ↑r_int * Complex.exp (I * ↑t) * f (↑r_int * Complex.exp (I * ↑t)) / (↑r_int * Complex.exp (I * ↑t) - z) ^ 2 := by
  -- Use inv_pow to transform (w - z)⁻¹ ^ 2 to ((w - z) ^ 2)⁻¹
  rw [inv_pow]
  -- Use div_eq_mul_inv in reverse to transform multiplication by inverse to division
  rw [← div_eq_mul_inv]
  -- Now we need to rearrange the multiplication
  ring

lemma lem_CIF_deriv_simplified {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    deriv f z = (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
  -- Apply lem_CIF_deriv_param
  rw [lem_CIF_deriv_param hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

  -- Factor out I from the integrand using linearity
  rw [factor_I_from_integrand f r_int z]

  -- Rearrange to cancel I factors: (1 / (2 * Real.pi * I)) * I = 1 / (2 * Real.pi)
  rw [← mul_assoc, complex_coeff_I_cancel]

  -- Transform the integrand from multiplicative inverse to division form
  congr 2
  funext t
  rw [integrand_transform_div f r_int z t]

lemma lem_modulus_of_f_prime0 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) = norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
(r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
  -- Apply the simplified Cauchy integral formula for derivatives
  rw [lem_CIF_deriv_simplified hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]

lemma one_div_two_pi_pos : (1 : ℝ) / (2 * Real.pi) > 0 := by positivity

lemma abs_ofReal_mul_complex (c : ℝ) (z : ℂ) (hc : c ≥ 0) : norm (↑c * z) = c * norm z := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]

lemma complex_abs_mul (a b : ℂ) : norm (a * b) = norm a * norm b :=
  Complex.norm_mul a b

lemma complex_abs_ofReal_nonneg (r : ℝ) (hr : r ≥ 0) : norm (↑r : ℂ) = r := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

lemma abs_one_div_two_pi_complex : norm (1 / (2 * ↑Real.pi : ℂ)) = 1 / (2 * Real.pi) := by
  rw [show (1 / (2 * ↑Real.pi) : ℂ) = ↑(1 / (2 * Real.pi) : ℝ) by push_cast; ring]
  exact complex_abs_ofReal_nonneg _ (by positivity)

lemma lem_integral_modulus_inequality {r_int : ℝ} {z : ℂ} {f : ℂ → ℂ} :
norm ((1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), (r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
  rw [complex_abs_mul, abs_one_div_two_pi_complex]
  exact mul_le_mul_of_nonneg_left (MeasureTheory.norm_integral_le_integral_norm _) one_div_two_pi_pos.le

lemma lem_modulus_of_f_prime {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm (deriv f z) ≤ (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) := by
  -- Apply lem_modulus_of_f_prime0 to get the equality form
  rw [lem_modulus_of_f_prime0 hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
  -- Apply lem_integral_modulus_inequality to get the desired inequality
  exact lem_integral_modulus_inequality

lemma lem_modulus_of_integrand_product2 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic) :
    norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) =
norm (f (r_int * Complex.exp (I * t))) * norm (r_int * Complex.exp (I * t)) := by
  -- Since norm is the norm, use the multiplicative property of norms
  rw [norm_mul]

lemma lem_modeit (t : ℝ) : norm (Complex.exp (I * t)) = Real.exp (Complex.re (I * t)) := by
  -- This is a direct application of the general theorem
  exact Complex.norm_exp (I * t)

lemma lem_Reit0 (t : ℝ) : Complex.re (I * t) = 0 := by
  simp [I, Complex.mul_re]

lemma lem_eReite0 (t : ℝ) : Real.exp (Complex.re (I * t)) = Real.exp 0 := by
  -- Apply Lemma lem_Reit0 to show Complex.re (I * t) = 0
  rw [lem_Reit0]

lemma lem_eReit1 (t : ℝ) : Real.exp (Complex.re (I * t)) = 1 := by
  -- Apply lem_eReite0 to rewrite Real.exp (Complex.re (I * t)) = Real.exp 0
  rw [lem_eReite0]
  -- Apply Real.exp_zero to show Real.exp 0 = 1
  rw [Real.exp_zero]

lemma lem_modulus_of_e_it_is_one (t : ℝ) : norm (Complex.exp (I * t)) = 1 := by
  rw [mul_comm (I : ℂ) (t : ℂ)]
  exact Complex.norm_exp_ofReal_mul_I t

lemma lem_modulus_of_ae_it {a t : ℝ} (ha : 0 < a) : norm (a * Complex.exp (I * t)) = a := by
  -- avoid fragile `change` on coerced terms; rewrite directly
  rw [norm_mul, lem_modulus_of_e_it_is_one, mul_one, Complex.norm_real]
  exact abs_of_pos ha

lemma lem_modulus_of_integrand_product3 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic) :
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) = r_int * norm (f (r_int * Complex.exp (I * t))) := by
  -- Use lem_modulus_of_integrand_product2 to split the absolute value
  rw [lem_modulus_of_integrand_product2 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]
  -- Use lem_modulus_of_ae_it to simplify norm (r_int * Complex.exp (I * t))
  have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
  rw [lem_modulus_of_ae_it h_r_int_pos]
  -- Now we have norm (f (...)) * r_int = r_int * norm (f (...))
  ring

lemma lem_reverse_triangle2 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic) :
norm (r_int * Complex.exp (I * t)) - norm z ≤ norm (r_int * Complex.exp (I * t) - z) := by
  -- Apply lem_reverse_triangle with w = r_int * Complex.exp (I * t)
  exact norm_sub_norm_le (r_int * Complex.exp (I * t)) z

lemma lem_reverse_triangle3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic) :
r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z) := by
  -- First establish that |r_int * e^{it}| = r_int
  have h_mod : norm (r_int * Complex.exp (I * t)) = r_int := by
    have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
    exact lem_modulus_of_ae_it h_r_int_pos
  -- Apply the reverse triangle inequality from lem_reverse_triangle
  have h_triangle := norm_sub_norm_le (r_int * Complex.exp (I * t)) z
  -- Substitute h_mod into h_triangle
  rw [h_mod] at h_triangle
  exact h_triangle

lemma lem_zrr1 {R_analytic r_z r_int : ℝ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
0 < r_int - norm z := by
  -- From membership in closed ball, get bound on norm
  have h1 : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
  -- For complex numbers, dist z 0 = ‖z‖
  have h2 : dist z 0 = ‖z‖ := by
    rw [dist_eq_norm, sub_zero]
  -- So ‖z‖ ≤ r_z
  have h3 : ‖z‖ ≤ r_z := by rwa [← h2]
  -- For complex numbers, norm z = ‖z‖
  have h4 : norm z = ‖z‖ := rfl
  -- So norm z ≤ r_z
  have h5 : norm z ≤ r_z := by rwa [h4]
  -- Combined with r_z < r_int, we get norm z < r_int
  have h6 : norm z < r_int := lt_of_le_of_lt h5 h_r_z_lt_r_int
  -- Therefore 0 < r_int - norm z
  linarith

lemma lem_zrr2 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
r_int - r_z ≤ norm (r_int * Complex.exp (I * t) - z) := by
  -- From membership in closed ball, get bound on norm z
  have h1 : norm z ≤ r_z := by
    have h_dist : dist z 0 ≤ r_z := Metric.mem_closedBall.mp hz
    rw [dist_eq_norm, sub_zero] at h_dist
    exact h_dist
  -- Since norm z ≤ r_z, we have r_int - r_z ≤ r_int - norm z
  have h2 : r_int - r_z ≤ r_int - norm z := by linarith [h1]
  -- Apply lem_reverse_triangle3 to get r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z)
  have h3 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
  -- Combine using transitivity
  exact le_trans h2 h3

lemma lem_rr11 {r r' : ℝ} (h_r_pos : 0 < r) (h_r_lt_r_prime : r < r') : r' - r > 0 := by
  linarith

lemma lem_rr12 {r r' : ℝ} (h_r_pos : 0 < r) (h_r_lt_r_prime : r < r') :
(r' - r) ^ 2 > 0 := by
  -- Use lem_rr11 to show r' - r > 0
  have h_diff_pos : r' - r > 0 := lem_rr11 h_r_pos h_r_lt_r_prime
  -- Apply sq_pos_of_pos to conclude (r' - r)^2 > 0
  exact sq_pos_of_pos h_diff_pos

lemma lem_zrr3 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int - r_z) ^ 2 ≤ norm (r_int * Complex.exp (I * t) - z) ^ 2 := by
  -- Use lem_zrr2 to get the inequality without squares
  have h_ineq := @lem_zrr2 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Show both sides are nonnegative
  have h_nonneg_left : 0 ≤ r_int - r_z := by linarith [h_r_z_lt_r_int]
  have h_nonneg_right : 0 ≤ norm (r_int * Complex.exp (I * t) - z) := norm_nonneg _
  -- Apply mul_self_le_mul_self to square both sides
  have h_sq := mul_self_le_mul_self h_nonneg_left h_ineq
  -- Convert from a * a to a ^ 2
  rw [pow_two, pow_two]
  exact h_sq

lemma lem_zrr4 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm ((r_int * Complex.exp (I * t) - z) ^ 2) = (norm (r_int * Complex.exp (I * t) - z)) ^ 2 := by
  exact Complex.norm_pow (r_int * Complex.exp (I * t) - z) 2

lemma lem_reverse_triangle4 {R_analytic r_z r_int : ℝ} {t : ℝ} {z : ℂ}
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
0 < norm (r_int * Complex.exp (I * t) - z) := by
  -- Apply lem_zrr1 to get 0 < r_int - norm z
  have h1 := lem_zrr1 h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Apply lem_reverse_triangle3 to get r_int - norm z ≤ norm (r_int * Complex.exp (I * t) - z)
  have h2 := @lem_reverse_triangle3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic
  -- Combine using transitivity
  exact lt_of_lt_of_le h1 h2

lemma lem_wposneq0 (w : ℂ) : norm w > 0 → w ≠ 0 := by
  intro h
  -- Use contrapositive: if w = 0, then norm w = 0
  by_contra h_eq_zero
  -- If w = 0, then norm w = 0
  have h_abs_zero : norm w = 0 := by
    rw [h_eq_zero]
    simp
  -- But this contradicts h : norm w > 0
  rw [h_abs_zero] at h
  exact lt_irrefl 0 h

lemma lem_reverse_triangle5 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
r_int * Complex.exp (I * t) - z ≠ 0 := by
  -- Apply lem_reverse_triangle4 to get 0 < norm (r_int * Complex.exp (I * t) - z)
  have h_pos := @lem_reverse_triangle4 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Apply lem_wposneq0 to conclude the complex number is not zero
  exact lem_wposneq0 (r_int * Complex.exp (I * t) - z) h_pos

lemma lem_reverse_triangle6 {R_analytic r_z r_int : ℝ} (t : ℝ)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
(r_int * Complex.exp (I * t) - z) ^ 2 ≠ 0 := by
  -- Apply lem_reverse_triangle5 as suggested in the informal proof
  have h_ne_zero := lem_reverse_triangle5 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Apply pow_ne_zero (which is the Mathlib version of mul_self_ne_zero for powers)
  exact pow_ne_zero 2 h_ne_zero

lemma lem_modulus_of_integrand_product {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
norm (f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
  rw [norm_div, Complex.norm_pow]

lemma lem_modulus_of_product {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
(r_int * norm (f (r_int * Complex.exp (I * t)))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2 := by
  -- First apply lem_modulus_of_integrand_product to split the absolute value of the quotient
  rw [lem_modulus_of_integrand_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
  -- Then apply lem_modulus_of_integrand_product3 to simplify the numerator
  rw [lem_modulus_of_integrand_product3 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]

lemma lem_modulus_of_product2 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
(r_int * norm (f (r_int * Complex.exp (I * t)))) / ((norm (r_int * Complex.exp (I * t) - z)) ^ 2) := by
  -- Apply lem_modulus_of_integrand_product to split the division
  rw [lem_modulus_of_integrand_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
  -- Apply lem_modulus_of_integrand_product3 to simplify the numerator
  rw [lem_modulus_of_integrand_product3 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic]

lemma lem_modulus_of_product3 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 R_analytic))
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    (r_int * norm (f (r_int * Complex.exp (I * t)))) / ((norm (r_int * Complex.exp (I * t) - z)) ^ 2) ≤
(r_int * norm (f (r_int * Complex.exp (I * t)))) / ((r_int - r_z) ^ 2) := by
  -- We need to show that (r_int - r_z)^2 ≤ (norm (r_int * Complex.exp (I * t) - z))^2
  -- This comes from lem_zrr3
  have h_ineq := @lem_zrr3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  -- Show the numerator is nonnegative
  have h_numer_nonneg : 0 ≤ r_int * norm (f (r_int * Complex.exp (I * t))) := by
    apply mul_nonneg
    · linarith [h_r_z_pos, h_r_z_lt_r_int]
    · exact norm_nonneg _

  -- Show the denominators are positive
  have h_denom1_pos : 0 < (norm (r_int * Complex.exp (I * t) - z)) ^ 2 := by
    apply pow_pos
    exact lem_reverse_triangle4 h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  have h_denom2_pos : 0 < (r_int - r_z) ^ 2 := by
    exact lem_rr12 h_r_z_pos h_r_z_lt_r_int

  -- Apply division monotonicity
  exact div_le_div_of_nonneg_left h_numer_nonneg h_denom2_pos h_ineq

lemma lem_modulus_of_product4 {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} (t : ℝ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤
(r_int * norm (f (r_int * Complex.exp (I * t)))) / ((r_int - r_z) ^ 2) := by
  -- First rewrite using lem_modulus_of_product
  rw [lem_modulus_of_product t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz]
  -- Now we have: (r_int * norm (f (r_int * Complex.exp (I * t)))) / norm ((r_int * Complex.exp (I * t)) - z) ^ 2
  -- We need to show this ≤ (r_int * norm (f (r_int * Complex.exp (I * t)))) / ((r_int - r_z) ^ 2)

  -- Use lem_zrr3 to get the key inequality: (r_int - r_z) ^ 2 ≤ norm (r_int * Complex.exp (I * t) - z) ^ 2
  have h_ineq := @lem_zrr3 R_analytic r_z r_int t z h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  -- Apply division monotonicity - when denominator increases, fraction decreases
  apply div_le_div_of_nonneg_left
  · -- Numerator is nonnegative
    apply mul_nonneg
    · linarith [h_r_z_pos, h_r_z_lt_r_int]
    · exact norm_nonneg _
  · -- Denominator (r_int - r_z)^2 is positive
    apply pow_pos
    linarith [h_r_z_lt_r_int]
  · -- The key inequality: (r_int - r_z)^2 ≤ Complex.abs(...) ^ 2
    exact h_ineq



lemma lem_bound_on_f_at_r_prime {M R_analytic r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (hr_int_pos : 0 < r_int)
    (hr_int_lt_R_analytic : r_int < R_analytic)
    (f : ℂ → ℂ)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ z ∈ Metric.closedBall 0 R_analytic, (f z).re ≤ M)
    (t : ℝ) :
norm (f (r_int * Complex.exp (I * t))) ≤ (2 * r_int * M) / (R_analytic - r_int) := by
  obtain ⟨U, hU_open, h_subset, hf_diff_U⟩ := hf_domain
  set z₀ := r_int * Complex.exp (I * t) with hz₀_def
  have hz₀_norm : ‖z₀‖ = r_int := lem_modulus_of_ae_it hr_int_pos
  have hz₀_mem : z₀ ∈ Metric.ball (0 : ℂ) R_analytic := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, hz₀_norm]
    exact hr_int_lt_R_analytic
  have hf_ball : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R_analytic) :=
    hf_diff_U.mono (Metric.ball_subset_closedBall.trans h_subset)
  have hmaps : Set.MapsTo f (Metric.ball (0 : ℂ) R_analytic) {w | w.re ≤ M} :=
    fun w hw => hRe_f_le_M w (Metric.ball_subset_closedBall hw)
  have h := Complex.borelCaratheodory_zero hM_pos hf_ball hmaps hR_analytic_pos hz₀_mem hf0
  rw [hz₀_norm] at h
  have heq : 2 * M * r_int / (R_analytic - r_int) = 2 * r_int * M / (R_analytic - r_int) := by ring
  rwa [heq] at h

lemma lem_bound_on_integrand_modulus {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z)
    (t : ℝ) :
norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
  -- Apply lem_modulus_of_product4 to get intermediate bound
  have h1 := lem_modulus_of_product4 t hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz
  -- Apply lem_bound_on_f_at_r_prime to bound |f(r_int * e^{it})|
  have h2 := lem_bound_on_f_at_r_prime hM_pos hR_analytic_pos (lt_trans h_r_z_pos h_r_z_lt_r_int) h_r_int_lt_R_analytic f hf_domain hf0 hRe_f_le_M t

  -- Now we need to combine these bounds properly
  have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
  have h_denom_nonneg : 0 ≤ (r_int - r_z) ^ 2 := by
    apply sq_nonneg

  -- Multiply both sides of h2 by r_int and divide by (r_int - r_z)^2
  have h3 : (r_int * norm (f (r_int * Complex.exp (I * t)))) / (r_int - r_z) ^ 2 ≤
            (r_int * (2 * r_int * M / (R_analytic - r_int))) / (r_int - r_z) ^ 2 := by
    apply div_le_div_of_nonneg_right _ h_denom_nonneg
    apply mul_le_mul_of_nonneg_left h2
    linarith [h_r_int_pos]

  -- Simplify the right-hand side
  have h4 : (r_int * (2 * r_int * M / (R_analytic - r_int))) / (r_int - r_z) ^ 2 =
            (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
    have h_R_sub_r_pos : 0 < R_analytic - r_int := by linarith [h_r_int_lt_R_analytic]
    have h_r_sub_r_pos : 0 < r_int - r_z := by linarith [h_r_z_lt_r_int]
    field_simp [ne_of_gt h_R_sub_r_pos, ne_of_gt (pow_pos h_r_sub_r_pos 2)]

  -- Apply transitivity
  rw [h4] at h3
  exact le_trans h1 h3

lemma lem_integral_inequality_aux {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in a..b, g t ≤ ∫ t in a..b, C :=
  intervalIntegral.integral_mono_on hab h_integrable intervalIntegrable_const h_bound

lemma lem_integral_inequality {g : ℝ → ℝ} {C a b : ℝ} (hab : a ≤ b)
    (h_integrable : IntervalIntegrable g MeasureTheory.volume a b)
    (h_bound : ∀ t ∈ Set.Icc a b, g t ≤ C) :
∫ t in Set.Icc a b, g t ≤ ∫ t in Set.Icc a b, C := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab, ← intervalIntegral.integral_of_le hab]
  exact lem_integral_inequality_aux hab h_integrable h_bound

lemma continuous_real_parameterization (r : ℝ) : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := by
  fun_prop

lemma continuous_f_parameterized {f : ℂ → ℂ} {R r : ℝ}     (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
 (hr_pos : 0 < r) (hr_lt_R : r < R) : Continuous (fun t : ℝ => f (r * Complex.exp (I * t))) := by
  -- f is continuous on the closed ball since it's differentiable there
  obtain ⟨U', hU'_open, h_subset, hf_diff_U'⟩ := hf_domain
  have hf_cont : ContinuousOn f (Metric.closedBall 0 R) := by
    -- First restrict differentiability from U' to the closed ball
    have hf_on_closed : DifferentiableOn ℂ f (Metric.closedBall 0 R) :=
      hf_diff_U'.mono h_subset
    -- Then use the fact that differentiable implies continuous
    exact DifferentiableOn.continuousOn hf_on_closed

  -- The parameterization is continuous
  have hparam_cont : Continuous (fun t : ℝ => r * Complex.exp (I * t)) := continuous_real_parameterization r

  -- Show that the parameterization maps into the closed ball
  have hparam_range : ∀ t : ℝ, r * Complex.exp (I * t) ∈ Metric.closedBall 0 R := by
    intro t
    rw [Metric.mem_closedBall, dist_zero_right]
    -- Convert norm to norm and use lem_modulus_of_ae_it
    change norm (r * Complex.exp (I * t)) ≤ R
    rw [lem_modulus_of_ae_it hr_pos]
    exact le_of_lt hr_lt_R

  -- Apply composition: f continuous on closed ball, parameterization continuous and maps into closed ball
  -- Use ContinuousOn.comp to get continuity on Set.univ
  have hcomp_on : ContinuousOn (fun t : ℝ => f (r * Complex.exp (I * t))) Set.univ := by
    apply ContinuousOn.comp hf_cont (Continuous.continuousOn hparam_cont)
    intro t _
    exact hparam_range t

  -- Convert ContinuousOn Set.univ to Continuous using the equivalence
  rwa [continuousOn_univ] at hcomp_on

lemma continuous_denominator_parameterized (r : ℝ) (z : ℂ) : Continuous (fun t : ℝ => (r * Complex.exp (I * t) - z) ^ 2) := by
  fun_prop

lemma interval_integrable_cauchy_integrand {f : ℂ → ℂ} {R_analytic r_z r_int : ℝ} {z : ℂ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hz : z ∈ Metric.closedBall 0 r_z) :
IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
  -- The integrand is continuous, so it's interval integrable
  apply Continuous.intervalIntegrable

  -- Show continuity of the integrand
  apply Continuous.comp continuous_norm

  -- Show the quotient is continuous (denominator never zero by lem_reverse_triangle6)
  apply Continuous.div₀

  -- Show numerator is continuous: t ↦ r_int * exp(I*t) * f(r_int * exp(I*t))
  · apply Continuous.mul
    -- First part: t ↦ r_int * exp(I*t) is continuous
    · exact continuous_real_parameterization r_int
    -- Second part: t ↦ f(r_int * exp(I*t)) is continuous
    · have h_r_int_pos : 0 < r_int := lt_trans h_r_z_pos h_r_z_lt_r_int
      exact continuous_f_parameterized hf_domain h_r_int_pos h_r_int_lt_R_analytic

  -- Show denominator is continuous: t ↦ (r_int * exp(I*t) - z)^2
  · exact continuous_denominator_parameterized r_int z

  -- Show denominator is never zero (key insight from informal proof)
  · intro t
    exact lem_reverse_triangle6 t h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

lemma integral_const_over_interval (C : ℝ) :
∫ t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul]

lemma lem_f_prime_bound_by_integral_of_constant {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
  -- Apply lem_modulus_of_f_prime as stated in the informal proof
  have h1 := lem_modulus_of_f_prime hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  -- Apply lem_bound_on_integrand_modulus as stated in the informal proof
  -- with g(t) = |f(r'e^{it}) r'e^{it} / (r'e^{it} - z)^2| and C = 2(r')^2M/((R-r')(r'-r)^2)
  set C := (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2)

  have h_bound : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ C := by
    intro t ht
    exact lem_bound_on_integrand_modulus hM_pos hR_analytic_pos h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hf_domain hf0 hRe_f_le_M hz t

  -- The integrand in h1 and h_bound are the same up to commutativity of multiplication
  have h_eq : ∀ t, norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) =
    norm ((f (r_int * Complex.exp (I * t)) * (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) := by
    intro t
    congr 2
    ring

  -- Convert the bound to apply to the integrand in h1
  have h_bound_h1 : ∀ t ∈ Set.Icc 0 (2 * Real.pi),
    norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2) ≤ C := by
    intro t ht
    rw [h_eq]
    exact h_bound t ht

  -- Apply lem_integral_inequality as stated in the informal proof
  have h_integrable : IntervalIntegrable (fun t => norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) MeasureTheory.volume 0 (2 * Real.pi) := by
    -- Use the added lemma for integrability
    exact interval_integrable_cauchy_integrand hf_domain h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hz

  have h2 := lem_integral_inequality ?_ h_integrable h_bound_h1

  -- The integral of constant C over [0, 2π] equals 2π * C
  have h_const_integral : ∫ t in Set.Icc 0 (2 * Real.pi), C = (2 * Real.pi) * C := by
    -- Use the added lemma for integration of constants
    exact integral_const_over_interval C

  -- Apply the chain of inequalities
  rw [h_const_integral] at h2

  have h3 : (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi),
    norm ((r_int * Complex.exp (I * t) * f (r_int * Complex.exp (I * t))) / ((r_int * Complex.exp (I * t)) - z) ^ 2)) ≤
    (1 / (2 * Real.pi)) * (2 * Real.pi * C) := by
    apply mul_le_mul_of_nonneg_left h2
    apply div_nonneg
    · norm_num
    · linarith [Real.pi_pos]

  -- Simplify (1/(2π)) * (2π * C) = C
  have h4 : (1 / (2 * Real.pi)) * (2 * Real.pi * C) = C := by
    have h_pi_ne_zero : (2 : ℝ) * Real.pi ≠ 0 := ne_of_gt (by linarith [Real.pi_pos])
    field_simp [h_pi_ne_zero]

  rw [h4] at h3
  exact le_trans h1 h3
  simp [Real.pi_nonneg]

lemma lem_integral_of_1 : ∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), (1 : ℝ) = 2 * Real.pi := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by positivity),
      intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

lemma lem_integral_2 : (1 / (2 * Real.pi)) * (∫ (t : ℝ) in Set.Icc 0 (2 * Real.pi), (1 : ℝ)) = 1 := by
  -- Apply lem_integral_of_1 to rewrite the integral
  rw [lem_integral_of_1]
  -- Now we have (1 / (2 * Real.pi)) * (2 * Real.pi) = 1
  -- Use field_simp to handle the division and multiplication
  field_simp

lemma lem_f_prime_bound {f : ℂ → ℂ} {M R_analytic r_z r_int : ℝ}
    (hM_pos : 0 < M)
    (hR_analytic_pos : 0 < R_analytic)
    (h_r_z_pos : 0 < r_z)
    (h_r_z_lt_r_int : r_z < r_int)
    (h_r_int_lt_R_analytic : r_int < R_analytic)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R_analytic ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R_analytic, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r_z) :
norm (deriv f z) ≤ (2 * r_int ^ 2 * M) / ((R_analytic - r_int) * (r_int - r_z) ^ 2) := by
  -- Use the lemma that has the same statement
  exact lem_f_prime_bound_by_integral_of_constant hM_pos hR_analytic_pos h_r_z_pos h_r_z_lt_r_int h_r_int_lt_R_analytic hf_domain hf0 hRe_f_le_M hz

lemma lem_r_prime_gt_r {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
r < (r + R) / 2 := by
  linarith

lemma lem_r_prime_lt_R {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(r + R) / 2 < R :=
  add_div_two_lt_right.mpr h_r_lt_R

lemma lem_r_prime_is_intermediate {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
r < (r + R) / 2 ∧ (r + R) / 2 < R :=
  ⟨left_lt_add_div_two.mpr h_r_lt_R, lem_r_prime_lt_R h_r_pos h_r_lt_R⟩

lemma lem_calc_R_minus_r_prime {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
R - ((r + R) / 2) = (R - r) / 2 := by
  field_simp
  ring

lemma lem_calc_r_prime_minus_r {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
((r + R) / 2) - r = (R - r) / 2 := by
  -- Multiply through by 2 to clear denominators
  field_simp
  -- Now we need to prove: r + R - 2 * r = R - r
  -- Simplify: r + R - 2*r = R - r
  ring

lemma lem_calc_denominator_specific {r R : ℝ}
    (h_r_pos : 0 < r)
    (h_r_lt_R : r < R) :
(R - ((r + R) / 2)) * (((r + R) / 2) - r) ^ 2 = ((R - r) ^ 3) / 8 := by
  -- Use lem_calc_R_minus_r_prime to rewrite the first term
  rw [lem_calc_R_minus_r_prime h_r_pos h_r_lt_R]
  -- Show that ((r + R) / 2) - r = (R - r) / 2
  have h_calc : ((r + R) / 2) - r = (R - r) / 2 := by
    field_simp
    ring
  -- Rewrite using this identity
  rw [h_calc]
  -- Now we have (R - r) / 2 * ((R - r) / 2) ^ 2 = ((R - r) ^ 3) / 8
  -- Simplify: (R - r) / 2 * (R - r)^2 / 4 = (R - r)^3 / 8
  ring

lemma lem_calc_numerator_specific {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
2 * (((r + R) / 2) ^ 2) * M = ((R + r) ^ 2 * M) / 2 := by
  -- Use ring to handle the algebraic manipulation
  ring

lemma lem_frac_simplify {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (((R + r) ^ 2 * M) / 2) / (((R - r) ^ 3) / 8) := by
  -- Unfold the definition of r_prime
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl]
  -- Apply the numerator lemma
  have h_num := lem_calc_numerator_specific hM_pos hr_pos hr_lt_R
  -- Apply the denominator lemma
  have h_denom := lem_calc_denominator_specific hr_pos hr_lt_R
  -- Rewrite using both lemmas
  rw [← h_num, ← h_denom]

lemma lem_frac_simplify2 {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
((R + r) ^ 2 * M / 2) / ((R - r) ^ 3 / 8) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by
  -- This is a division of fractions: (a/b) / (c/d) = (a/b) * (d/c) = ad/bc
  -- We have ((R + r)^2 * M / 2) / ((R - r)^3 / 8) = ((R + r)^2 * M / 2) * (8 / (R - r)^3)
  -- = (8 * (R + r)^2 * M) / (2 * (R - r)^3) = (4 * (R + r)^2 * M) / ((R - r)^3)

  -- First, we need to show that the denominators are nonzero
  have h_two_ne_zero : (2 : ℝ) ≠ 0 := by norm_num
  have h_eight_ne_zero : (8 : ℝ) ≠ 0 := by norm_num
  have h_R_minus_r_ne_zero : R - r ≠ 0 := by linarith [hr_lt_R]
  have h_R_minus_r_pow_ne_zero : (R - r) ^ 3 ≠ 0 := by
    apply pow_ne_zero
    exact h_R_minus_r_ne_zero

  -- Use field_simp to clear denominators and then ring to simplify
  field_simp [h_two_ne_zero, h_eight_ne_zero, h_R_minus_r_pow_ne_zero]
  ring

lemma lem_frac_simplify3 {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) = (4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) := by
  -- Unfold the let definition
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl]
  -- Apply lem_frac_simplify to get the intermediate form
  have h1 := lem_frac_simplify hM_pos hr_pos hr_lt_R
  -- Apply lem_frac_simplify2 to complete the transformation
  have h2 := lem_frac_simplify2 hM_pos hr_pos hr_lt_R
  -- Combine the two steps
  rw [h1, h2]

lemma lem_ineq_R_plus_r_lt_2R {r R : ℝ} (h_r_lt_R : r < R) :
R + r < 2 * R := by
  -- Rewrite 2 * R as R + R
  rw [two_mul]
  -- Now we want to show R + r < R + R, which follows from r < R
  linarith [h_r_lt_R]

lemma lem_R_plus_r_is_positive {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
0 < R + r := by
  -- Since r < R and r > 0, we have R > 0
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
  -- Both R > 0 and r > 0, so R + r > 0
  exact add_pos hR_pos hr_pos

lemma lem_2R_is_positive {R : ℝ} (hR_pos : 0 < R) : 0 < 2 * R := by
  apply mul_pos
  · norm_num
  · exact hR_pos

lemma lem_square_inequality_strict {a b : ℝ}
    (h_a_pos : 0 < a)
    (h_a_lt_b : a < b) :
a ^ 2 < b ^ 2 := by
  have h_b_nonneg : 0 ≤ b := (lt_trans h_a_pos h_a_lt_b).le
  simpa [pow_two] using (mul_self_lt_mul_self_iff h_a_pos.le h_b_nonneg).mp h_a_lt_b

lemma lem_ineq_R_plus_r_sq_lt_2R_sq {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(R + r) ^ 2 < (2 * R) ^ 2 := by
  -- Let a = R + r and b = 2 * R as suggested in the informal proof
  let a := R + r
  let b := 2 * R

  -- From lem_R_plus_r_is_positive: a > 0
  have ha_pos : 0 < a := lem_R_plus_r_is_positive hr_pos hr_lt_R

  -- From lem_2R_is_positive: b > 0 (need to establish that R > 0 first)
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
  have hb_pos : 0 < b := by
    unfold b
    exact lem_2R_is_positive hR_pos

  -- From lem_ineq_R_plus_r_lt_2R: a < b
  have hab : a < b := by
    unfold a b
    exact lem_ineq_R_plus_r_lt_2R hr_lt_R

  -- Apply lem_square_inequality_strict
  have : a ^ 2 < b ^ 2 := lem_square_inequality_strict ha_pos hab

  -- Convert back to original terms
  unfold a b at this
  exact this

lemma lem_2R_sq_is_4R_sq {R : ℝ} (hR_pos : 0 < R) : (2 * R) ^ 2 = 4 * R ^ 2 := by
  -- Use ring to simplify the algebraic expression
  ring

lemma lem_ineq_R_plus_r_sq {r R : ℝ}
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(R + r) ^ 2 < 4 * R ^ 2 := by
  -- Get R + r < 2 * R
  have h1 := lem_ineq_R_plus_r_lt_2R hr_lt_R
  -- Get 0 < R + r
  have h2 := lem_R_plus_r_is_positive hr_pos hr_lt_R
  -- Apply lem_square_inequality_strict to get (R + r)^2 < (2 * R)^2
  have h3 := lem_square_inequality_strict h2 h1
  -- Use lem_2R_sq_is_4R_sq to rewrite (2 * R)^2 = 4 * R^2
  have hR_pos : 0 < R := lt_trans hr_pos hr_lt_R
  have h4 := lem_2R_sq_is_4R_sq hR_pos
  rw [h4] at h3
  exact h3

lemma lem_ineq_R_plus_r_sqM {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
4 * (R + r) ^ 2 * M < 16 * R ^ 2 * M := by
  -- Apply lem_ineq_R_plus_r_sq to get (R + r) ^ 2 < 4 * R ^ 2
  have h_ineq := lem_ineq_R_plus_r_sq hr_pos hr_lt_R
  -- Show that 4 * M > 0
  have h_4M_pos : 0 < 4 * M := by
    apply mul_pos
    · norm_num
    · exact hM_pos
  -- Multiply both sides by 4 * M
  have h_mult := mul_lt_mul_of_pos_right h_ineq h_4M_pos
  -- Rearrange to get the desired form
  nlinarith [h_mult]

lemma lem_simplify_final_bound {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
(4 * (R + r) ^ 2 * M) / ((R - r) ^ 3) < (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
  -- Apply lem_ineq_R_plus_r_sqM to get the numerator inequality
  have h_num_ineq := lem_ineq_R_plus_r_sqM hM_pos hr_pos hr_lt_R
  -- Show that (R - r)^3 > 0
  have h_denom_pos : 0 < (R - r) ^ 3 := by
    apply pow_pos
    linarith [hr_lt_R]
  -- Apply division monotonicity
  exact div_lt_div_of_pos_right h_num_ineq h_denom_pos

lemma lem_bound_after_substitution {M r R : ℝ}
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R) :
    let r_prime := (r + R) / 2
(2 * (r_prime ^ 2) * M) / ((R - r_prime) * (r_prime - r) ^ 2) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
  -- Unfold the let binding
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl]
  -- Apply lem_frac_simplify3 to rewrite the left side
  have h1 := lem_frac_simplify3 hM_pos hr_pos hr_lt_R
  -- Unfold the let in h1 as well
  simp only [show (r + R) / 2 = (r + R) / 2 from rfl] at h1
  rw [h1]
  -- Apply lem_simplify_final_bound to get strict inequality
  have h2 := lem_simplify_final_bound hM_pos hr_pos hr_lt_R
  -- Since < implies ≤, we're done
  exact le_of_lt h2

theorem borel_caratheodory_II {f : ℂ → ℂ} {R M r : ℝ}
    (hR_pos : 0 < R)
    (hM_pos : 0 < M)
    (hr_pos : 0 < r)
    (hr_lt_R : r < R)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
    (hf0 : f 0 = 0)
    (hRe_f_le_M : ∀ w ∈ Metric.closedBall 0 R, (f w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r) :
norm (deriv f z) ≤ (16 * M * R ^ 2) / ((R - r) ^ 3) := by
  -- Set r' = (r + R) / 2 as suggested in the informal proof
  set r_prime := (r + R) / 2

  -- Show that r < r' < R using lem_r_prime_is_intermediate
  have h_intermediate := lem_r_prime_is_intermediate hr_pos hr_lt_R
  have h_r_lt_r_prime := h_intermediate.1
  have h_r_prime_lt_R := h_intermediate.2

  -- Apply lem_f_prime_bound with r_int = r_prime
  have h_bound := lem_f_prime_bound hM_pos hR_pos hr_pos h_r_lt_r_prime h_r_prime_lt_R hf_domain hf0 hRe_f_le_M hz

  -- Apply lem_bound_after_substitution to get the final bound
  have h_final := lem_bound_after_substitution hM_pos hr_pos hr_lt_R

  -- Combine the bounds using transitivity
  have h_combined : norm (deriv f z) ≤ (16 * R ^ 2 * M) / ((R - r) ^ 3) := by
    exact le_trans h_bound h_final

  -- Rearrange to match the target form: (16 * M * R ^ 2) / ((R - r) ^ 3)
  convert h_combined using 1
  ring

end DiskAnalyticBounds
