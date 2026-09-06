module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Erdos1201.Vendor.Analysis.DiskAnalyticBounds.NormAlgebraAndMaximumModulus

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
Borel–Carathéodory I: if `f` is analytic on a closed disk of radius `R`,
`f 0 = 0`, and `Re f ≤ M` throughout, then `‖f‖ ≤ (2r/(R-r))·M` on the smaller
closed disk of radius `r < R`. Built from the norm algebra and
maximum-modulus infrastructure of `NormAlgebraAndMaximumModulus`.
-/

public section

namespace DiskAnalyticBounds

lemma lem_denominator_nonzero (R M : ℝ) (hR : R > 0) (hM : M > 0)
  (f : ℂ → ℂ) (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
  (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → (2 * M - f z) ≠ 0 := by
  intro z hz
  -- Apply lem_real_part_lower_bound4 with w = f z
  apply lem_real_part_lower_bound4 (f z) M hM
  -- Show that Complex.re (f z) ≤ M
  exact h_re_bound z hz

lemma lem_f_vs_2M_minus_f (R M : ℝ) (hR : R > 0) (hM : M > 0)
  (f : ℂ → ℂ) (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
  (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → norm (f z) / norm (2 * M - f z) ≤ 1 := by
  intro z hz
  -- Apply lem_nonnegative_product9 with w = f(z)
  apply lem_nonnegative_product9 M (f z) hM
  -- Show that Complex.re (f z) ≤ M
  exact h_re_bound z hz

lemma lem_removable_singularity (R : ℝ) (hR : R > 0) (f : ℂ → ℂ)
  (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R))) (h_zero : f 0 = 0) :
AnalyticOn ℂ (fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z) (closure (Metric.ball (0 : ℂ) R)) := by
  -- First convert the domain to Metric.closedBall form for lem_ordernatcast2
  rw [closure_ball (0 : ℂ) (ne_of_gt hR)] at h_analytic ⊢

  -- Define the target function g
  let g : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z

  -- Use the helper lemma lem_analAtOnOn to combine analyticity at 0 and on punctured disk
  apply lem_analAtOnOn hR g

  · -- First goal: AnalyticAt ℂ g 0
    -- This follows directly from lem_ordernatcast2
    exact lem_ordernatcast2 hR f h_zero h_analytic

  · -- Second goal: AnalyticOn ℂ g {z : ℂ | ‖z‖ ≤ R ∧ z ≠ 0}
    -- For z ≠ 0, g z = f z / z, which is analytic since f is analytic and z ≠ 0
    -- We can use lem_fzzTanal which shows exactly this
    have f_on_closedball : AnalyticOn ℂ f (Metric.closedBall 0 R) := h_analytic
    have quotient_analytic : AnalyticOn ℂ (fun z ↦ f z / z) {z : ℂ | ‖z‖ ≤ R ∧ z ≠ 0} :=
      lem_fzzTanal hR f f_on_closedball

    -- Show that g equals f z / z on the punctured disk
    apply AnalyticOn.congr quotient_analytic
    intro z hz
    -- Since z ≠ 0, the if-then-else evaluates to the else branch
    simp [g, ite_eq_right hz.2]

noncomputable def f_M (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M) :
ℂ → ℂ := fun z ↦ (if z = 0 then (fderiv ℂ f 0) 1 else f z / z) / (2 * M - f z)

lemma lem_g_analytic (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M) :
AnalyticOn ℂ (f_M R M hR hM f h_analytic h_zero h_re_bound) (closure (Metric.ball (0 : ℂ) R)) := by
  -- Define h₁(z) = f(z)/z with removable singularity at 0
  let h₁ : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z
  -- Define h₂(z) = 2*M - f(z)
  let h₂ : ℂ → ℂ := fun z ↦ 2 * M - f z

  -- Show that f_M = h₁ / h₂
  have h_eq : f_M R M hR hM f h_analytic h_zero h_re_bound = fun z ↦ h₁ z / h₂ z := by
    ext z
    unfold f_M h₁ h₂
    simp

  -- Rewrite the goal using this equality
  rw [h_eq]

  -- Apply AnalyticOn.div directly
  apply AnalyticOn.div

  -- Show h₁ is analytic using lem_removable_singularity
  · exact lem_removable_singularity R hR f h_analytic h_zero

  -- Show h₂ is analytic (constant minus analytic function)
  · have h₂_analytic : AnalyticOn ℂ h₂ (closure (Metric.ball (0 : ℂ) R)) := by
      unfold h₂
      apply AnalyticOn.sub
      · exact analyticOn_const
      · exact h_analytic
    exact h₂_analytic

  -- Show h₂ is non-zero using lem_denominator_nonzero
  · intro z hz
    unfold h₂
    exact lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz

lemma lem_g_on_boundaryz (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_in_closure : z ∈ closure (Metric.ball (0 : ℂ) R)) (hz_nonzero : z ≠ 0) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
norm (f z / z) / norm (2 * M - f z) := by
  -- Use the definition of f_M
  unfold f_M
  -- Since z ≠ 0, the if-then-else simplifies to the else branch
  simp only [ite_eq_right hz_nonzero]
  -- Now we need to show norm ((f z / z) / (2 * M - f z)) = norm (f z / z) / norm (2 * M - f z)
  -- We need to show that 2 * M - f z ≠ 0 for norm_div (unconditional, but the shape needs it in scope)
  have h_nonzero : (2 * M - f z) ≠ 0 := lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz_in_closure
  exact norm_div (f z / z) (2 * M - f z)

lemma lem_g_on_boundary (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_on_boundary : norm z = R) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
(norm (f z) / R) / norm (2 * M - f z) := by
  -- First show that z ≠ 0 since |z| = R > 0
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz_on_boundary
    simp at hz_on_boundary
    linarith [hz_on_boundary, hR]

  -- Show that z ∈ the closure of the metric ball since |z| = R
  have hz_in_closure : z ∈ closure (Metric.ball (0 : ℂ) R) := by
    rw [closure_ball (0 : ℂ) (ne_of_gt hR)]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    convert le_of_eq hz_on_boundary

  -- Apply lem_g_on_boundaryz to get the first form
  have h1 : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    norm (f z / z) / norm (2 * M - f z) :=
    lem_g_on_boundaryz R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure hz_nonzero

  -- Apply norm_div to transform f z / z
  have h2 : norm (f z / z) = norm (f z) / R := by
    rw [norm_div, hz_on_boundary]

  -- Combine the results
  rw [h1, h2]

lemma lem_f_vs_2M_minus_fR (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_in_closure : z ∈ closure (Metric.ball (0 : ℂ) R)) :
(norm (f z) / R) / norm (2 * M - f z) ≤ 1 / R := by
  -- Apply lem_f_vs_2M_minus_f to get the bound
  have h1 : norm (f z) / norm (2 * M - f z) ≤ 1 :=
    lem_f_vs_2M_minus_f R M hR hM f h_analytic h_re_bound z hz_in_closure

  -- Rewrite the left side using division associativity
  -- (a / b) / c = a / (b * c)
  rw [div_div]
  -- Goal is now: norm (f z) / (R * norm (2 * M - f z)) ≤ 1 / R

  -- Use commutativity to rewrite R * norm (2 * M - f z) as norm (2 * M - f z) * R
  rw [mul_comm R]
  -- Goal is now: norm (f z) / (norm (2 * M - f z) * R) ≤ 1 / R

  -- Rewrite a / (b * c) as (a / b) / c
  rw [← div_div]
  -- Goal is now: (norm (f z) / norm (2 * M - f z)) / R ≤ 1 / R

  -- Apply division monotonicity: if a ≤ b and c > 0, then a / c ≤ b / c
  exact div_le_div_of_nonneg_right h1 (le_of_lt hR)

lemma lem_g_boundary_bound0 (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (z : ℂ) (hz_on_boundary : norm z = R) :
norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R := by
  -- First, show that z is in the closure of the metric ball since |z| = R
  have hz_in_closure : z ∈ closure (Metric.ball (0 : ℂ) R) := by
    rw [closure_ball (0 : ℂ) (ne_of_gt hR)]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    convert le_of_eq hz_on_boundary

  -- Apply lem_g_on_boundary to rewrite the left side
  rw [lem_g_on_boundary R M hR hM f h_analytic h_zero h_re_bound z hz_on_boundary]

  -- Apply lem_f_vs_2M_minus_fR to get the bound
  exact lem_f_vs_2M_minus_fR R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure

lemma lem_g_interior_bound (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M) :
∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R := by
  -- Show that 1/R ≥ 0
  have hB : (1 / R : ℝ) ≥ 0 := div_nonneg zero_le_one (le_of_lt hR)
  -- f_M is analytic on the closure of the metric ball
  have h_g_analytic : AnalyticOn ℂ (f_M R M hR hM f h_analytic h_zero h_re_bound) (closure (Metric.ball (0 : ℂ) R)) :=
    lem_g_analytic R M hR hM f h_analytic h_zero h_re_bound
  -- Apply the Maximum Modulus Principle (lem_MMP) in the mpr direction
  apply (lem_MMP R (1 / R) hR hB (f_M R M hR hM f h_analytic h_zero h_re_bound) h_g_analytic).mpr
  -- Show boundary condition: for z with |z| = R, |f_M(z)| ≤ 1/R
  intro z hz_boundary
  exact lem_g_boundary_bound0 R M hR hM f h_analytic h_zero h_re_bound z hz_boundary

lemma lem_g_at_r (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
  norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
(norm (f z) / r) / norm (2 * M - f z) := by
  -- First show that z ≠ 0 since |z| = r > 0
  have hz_nonzero : z ≠ 0 := by
    intro h_eq
    rw [h_eq] at hz_on_boundary
    simp at hz_on_boundary
    linarith [hz_on_boundary, hr_pos]

  -- Show that z is in the closure of the metric ball since |z| = r < R
  have hz_in_closure : z ∈ closure (Metric.ball (0 : ℂ) R) := by
    rw [closure_ball (0 : ℂ) (ne_of_gt hR)]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  -- Apply lem_g_on_boundaryz to get the first form
  have h1 : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    norm (f z / z) / norm (2 * M - f z) :=
    lem_g_on_boundaryz R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure hz_nonzero

  -- Apply norm_div to transform f z / z with w = f z
  have h2 : norm (f z / z) = norm (f z) / r := by
    rw [norm_div, hz_on_boundary]

  -- Combine the results
  rw [h1, h2]

lemma lem_g_at_rR (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
(norm (f z) / r) / norm (2 * M - f z) ≤ 1 / R := by
  -- Show that z is in the closure of the metric ball since |z| = r < R
  have hz_in_closure : z ∈ closure (Metric.ball (0 : ℂ) R) := by
    rw [closure_ball (0 : ℂ) (ne_of_gt hR)]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  -- Apply lem_g_interior_bound to get the bound on f_M
  have h_bound : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) ≤ 1 / R :=
    lem_g_interior_bound R M hR hM f h_analytic h_zero h_re_bound z hz_in_closure

  -- Apply lem_g_at_r to rewrite f_M in terms of f
  have h_eq : norm (f_M R M hR hM f h_analytic h_zero h_re_bound z) =
    (norm (f z) / r) / norm (2 * M - f z) :=
    lem_g_at_r R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  -- Combine the results
  rw [← h_eq]
  exact h_bound

lemma lem_fracs (a b r R : ℝ) (ha : a > 0) (hb : b > 0) (hr : r > 0) (hR : R > 0)
(h_le : (a / r) / b ≤ 1 / R) : R * a ≤ r * b := by
  rw [div_div, div_le_div_iff₀ (mul_pos hr hb) hR, one_mul] at h_le
  linarith

lemma lem_nonneg_product_with_real_abs (r M : ℝ) (hr : r > 0) (hM : M > 0) : 0 ≤ r * (2 * |M|) := by
  positivity

lemma lem_f_bound_rearranged (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
R * norm (f z) ≤ r * norm (2 * M - f z) := by
  -- Show that z is in the closure of the metric ball
  have hz_in_closure : z ∈ closure (Metric.ball (0 : ℂ) R) := by
    rw [closure_ball (0 : ℂ) (ne_of_gt hR)]
    rw [Metric.mem_closedBall]
    rw [Complex.dist_eq]
    simp
    linarith [hz_on_boundary, hr_lt_R]

  -- Apply lem_g_at_rR to get the key inequality (as mentioned in informal proof)
  have h_ineq : (norm (f z) / r) / norm (2 * M - f z) ≤ 1 / R :=
    lem_g_at_rR R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  -- Show that 2 * M - f z ≠ 0, so norm (2 * M - f z) > 0
  have h_denom_nonzero : (2 * M - f z) ≠ 0 :=
    lem_denominator_nonzero R M hR hM f h_analytic h_re_bound z hz_in_closure

  have h_denom_pos : norm (2 * M - f z) > 0 :=
    lem_abspos (2 * M - f z) h_denom_nonzero

  -- Case analysis on whether f z = 0
  by_cases h_case : f z = 0
  · -- Case: f z = 0, then R * 0 ≤ r * norm (2 * M - f z)
    rw [h_case]
    simp [AbsoluteValue.map_zero, mul_zero]
    exact lem_nonneg_product_with_real_abs r M hr_pos hM
  · -- Case: f z ≠ 0, so norm (f z) > 0
    have h_num_pos : norm (f z) > 0 :=
      lem_abspos (f z) h_case

    -- Apply lem_fracs with a = norm (f z), b = norm (2 * M - f z)
    -- This is exactly what the informal proof says to do
    exact lem_fracs (norm (f z)) (norm (2 * M - f z)) r R
           h_num_pos h_denom_pos hr_pos hR h_ineq

lemma lem_final_bound_on_circle0 (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ) (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
  -- Apply lem_f_bound_rearranged to get the inequality R * |f(z)| ≤ r * |2*M - f(z)|
  have h_ineq : R * norm (f z) ≤ r * norm (2 * M - f z) :=
    lem_f_bound_rearranged R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

  -- Apply lem_rtriangle7 with F = f(z)
  have h_bound : norm (f z) ≤ (2 * M * r) / (R - r) :=
    lem_rtriangle7 r R M (f z) hr_pos hr_lt_R hM h_ineq

  -- Rearrange (2 * M * r) / (R - r) to (2 * r / (R - r)) * M
  have h_rearrange : (2 * M * r) / (R - r) = (2 * r / (R - r)) * M := by
    field_simp

  -- Apply the rearrangement
  rw [← h_rearrange]
  exact h_bound

lemma lem_final_bound_on_circle (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ) (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_on_boundary : norm z = r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
  exact lem_final_bound_on_circle0 R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_on_boundary

lemma lem_BCI (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R)
    (z : ℂ) (hz_in_ball : norm z ≤ r) :
norm (f z) ≤ (2 * r / (R - r)) * M := by
  have hz_lt_R : ‖z‖ < R := lt_of_le_of_lt hz_in_ball hr_lt_R
  have hz_mem : z ∈ Metric.ball (0 : ℂ) R := by
    simpa [Metric.mem_ball, dist_eq_norm] using hz_lt_R
  have hsub : Metric.ball (0 : ℂ) R ⊆ closure (Metric.ball (0 : ℂ) R) := subset_closure
  have hf_diff : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R) :=
    (h_analytic.mono hsub).differentiableOn
  have hf_maps : Set.MapsTo f (Metric.ball (0 : ℂ) R) {w : ℂ | w.re ≤ M} :=
    fun w hw => h_re_bound w (hsub hw)
  have hb := Complex.borelCaratheodory_zero hM hf_diff hf_maps hR hz_mem h_zero
  have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have h_denom_r_pos : 0 < R - r := by linarith
  have h_denom_z_pos : 0 < R - ‖z‖ := by linarith
  have h_mono : 2 * M * ‖z‖ / (R - ‖z‖) ≤ 2 * r / (R - r) * M := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ h_denom_z_pos h_denom_r_pos]
    nlinarith [mul_le_mul_of_nonneg_left hz_in_ball (mul_pos hM hR).le]
  linarith [hb, h_mono]

theorem thm_BorelCaratheodoryI (R M : ℝ) (hR : R > 0) (hM : M > 0)
    (f : ℂ → ℂ)
    (h_analytic : AnalyticOn ℂ f (closure (Metric.ball (0 : ℂ) R)))
    (h_zero : f 0 = 0)
    (h_re_bound : ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → Complex.re (f z) ≤ M)
    (r : ℝ) (hr_pos : r > 0) (hr_lt_R : r < R) :
sSup ((norm ∘ f) '' (closure (Metric.ball (0 : ℂ) r))) ≤ (2 * r / (R - r)) * M := by
  -- Apply Real.sSup_le - we need to show every element is bounded and the bound is nonnegative
  apply Real.sSup_le
  · -- Show that every element x in the image of the closed metric ball satisfies the desired bound
    intro x hx
    -- hx says that x comes from the closure of the metric ball of radius r.
    obtain ⟨z, hz_in_closure, hx_eq⟩ := hx
    rw [← hx_eq]
    -- Now we need to show norm (f z) ≤ (2 * r / (R - r)) * M
    -- First, convert closure membership to |z| ≤ r
    have hz_bound : norm z ≤ r := by
      rw [closure_ball (0 : ℂ) (ne_of_gt hr_pos)] at hz_in_closure
      rw [Metric.mem_closedBall] at hz_in_closure
      rw [Complex.dist_eq] at hz_in_closure
      simp at hz_in_closure
      exact hz_in_closure
    -- Apply lem_BCI
    exact lem_BCI R M hR hM f h_analytic h_zero h_re_bound r hr_pos hr_lt_R z hz_bound
  · -- Show that (2 * r / (R - r)) * M ≥ 0
    have : (0:ℝ) < R - r := by linarith
    positivity



end DiskAnalyticBounds
