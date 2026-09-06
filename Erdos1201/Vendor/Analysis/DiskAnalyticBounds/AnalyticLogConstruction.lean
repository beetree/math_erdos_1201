module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Erdos1201.Vendor.Analysis.DiskAnalyticBounds.RectangleContourDerivativeBound

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Filter Topology

/-!
Existence of an analytic logarithm/branch: given `B` analytic and zero-free
on a closed disk, constructs `J` analytic on a smaller closed disk with
`J 0 = 0`, `J' = B'/B`, and `log‖B(z)‖ - log‖B(0)‖ = Re(J(z))` — i.e. `J` is
a branch of `log B` on the disk. Built on the primitive-construction
machinery of `RectangleContourConstruction`/`RectangleContourDerivativeBound`.
-/

public section

namespace DiskAnalyticBounds

/-- Lemma: There exists J analyticOnNhd with J(0) = 0 and J'(z) = B'(z)/B(z). -/
lemma I_is_antiderivative
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J : ℂ → ℂ, AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) ∧
      J 0 = 0 ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z := by
  classical
  -- L := B'/B is analytic on closedBall R'
  have hB_on_R' : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R') :=
    hB.mono (Metric.closedBall_subset_closedBall hR'_lt_R.le)
  have hderiv_on_R' : AnalyticOnNhd ℂ (deriv B) (Metric.closedBall (0 : ℂ) R') :=
    AnalyticOnNhd.deriv hB_on_R'
  let L : ℂ → ℂ := fun z => deriv B z / B z
  have hL_on_R' : AnalyticOnNhd ℂ L (Metric.closedBall (0 : ℂ) R') := by
    simpa [L] using AnalyticOnNhd.div hderiv_on_R' hB_on_R' hB_ne_zero
  -- Choose R_mid with r1 < R_mid < R'
  let δ : ℝ := (R' - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R' - r1 := sub_pos.mpr hr1_lt_R'
    simpa [δ] using half_pos this
  let R_mid : ℝ := r1 + δ
  have hR_mid_pos : 0 < R_mid := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R_mid] using this
  have hr1_lt_R_mid : r1 < R_mid := by
    have : 0 < δ := hδ_pos
    simpa [R_mid] using (lt_add_of_pos_right r1 this)
  have hR_mid_lt_R' : R_mid < R' := by
    have hδlt : δ < R' - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R'))
    have : r1 + δ < r1 + (R' - r1) := by linarith [hδlt]
    simpa [R_mid, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Define J as the primitive of L on radius R_mid with outer radius R'
  let J : ℂ → ℂ :=
    If_ext (r1 := R_mid) (R := R') (R0 := R) hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one L hL_on_R'
  -- If_is_differentiable_on gives differentiability on closedBall R_mid and
  -- the within-derivative there equals L
  have hIf :=
    (If_is_differentiable_on (r1 := R_mid) (R := R') (R0 := R)
      hR_mid_pos hR_mid_lt_R' hR'_lt_R hR_lt_one (f := L) hL_on_R')
  have hDiffOn_mid : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) R_mid) := by
    simpa [J] using hIf.1
  -- Differentiable on the open ball R_mid by restriction
  have hDiffOn_ball_R_mid : DifferentiableOn ℂ J (Metric.ball (0 : ℂ) R_mid) :=
    hDiffOn_mid.mono Metric.ball_subset_closedBall
  -- 1) J is analytic on a neighborhood of every point of closedBall r1
  have hJ_analyticOnNhd : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1) := by
    intro z hz
    -- z is strictly inside radius R_mid since ‖z‖ ≤ r1 < R_mid
    have hz_le : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
    -- Differentiability on the open ball of radius R_mid yields AnalyticAt at z
    exact (DifferentiableOn.analyticAt (s := Metric.ball (0 : ℂ) R_mid)
      (f := J) hDiffOn_ball_R_mid (Metric.isOpen_ball.mem_nhds hz_ball))
  -- 2) J(0) = 0
  have h0_in_mid : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R_mid := by
    simpa [Metric.mem_closedBall, dist_self] using (le_of_lt hR_mid_pos)
  have hJ0 : J 0 = 0 := by
    simp [J, If_ext, If_taxicab, h0_in_mid]
  -- 3) For each z in closedBall r1, deriv J z = L z = B'/B
  have hderiv_eq : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = L z := by
    intro z hz
    -- z is strictly inside radius R_mid
    have hz_le : dist z (0 : ℂ) ≤ r1 := by simpa [Metric.mem_closedBall] using hz
    have hz_lt : dist z (0 : ℂ) < R_mid := lt_of_le_of_lt hz_le hr1_lt_R_mid
    have hz_ball : z ∈ Metric.ball (0 : ℂ) R_mid := by simpa [Metric.mem_ball] using hz_lt
    have hz_cb_mid : z ∈ Metric.closedBall (0 : ℂ) R_mid := Metric.ball_subset_closedBall hz_ball
    -- closedBall R_mid is a neighborhood of z since it contains an open ball around z
    have h_cb_nhds : Metric.closedBall (0 : ℂ) R_mid ∈ 𝓝 z :=
      Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz_ball) Metric.ball_subset_closedBall
    -- We have: derivWithin J (closedBall R_mid) z = L z from If_is_differentiable_on
    have hDW_eq_L : derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z = L z := by
      simpa [J] using hIf.2 z hz_cb_mid
    -- From differentiability within on closedBall R_mid, get a HasDerivWithinAt with derivative L z
    have hHasWithin : HasDerivWithinAt J (derivWithin J (Metric.closedBall (0 : ℂ) R_mid) z)
        (Metric.closedBall (0 : ℂ) R_mid) z :=
      (hDiffOn_mid z hz_cb_mid).hasDerivWithinAt
    have hHasWithinL : HasDerivWithinAt J (L z) (Metric.closedBall (0 : ℂ) R_mid) z := by
      simpa [hDW_eq_L]
        using hHasWithin
    -- Since closedBall R_mid is a neighborhood of z, upgrade to HasDerivAt
    have hHasDerivAt : HasDerivAt J (L z) z :=
      HasDerivWithinAt.hasDerivAt hHasWithinL h_cb_nhds
    -- Conclude the equality of derivatives
    simpa using hHasDerivAt.deriv
  -- Package the result
  refine ⟨J, hJ_analyticOnNhd, hJ0, ?_⟩
  intro z hz
  simpa [L] using hderiv_eq z hz

/-- Definition: H(z) := exp(J(z))/B(z) where J is from I_is_antiderivative. -/
noncomputable def H_auxiliary
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    (J : ℂ → ℂ) : ℂ → ℂ :=
  fun z => Complex.exp (J z) / B z

/-- Lemma: H(0) = 1/B(0). -/
lemma H_at_zero
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 = 1 / B 0 := by
  simp [H_auxiliary, hJ_zero]

/-- Lemma: J'(z)B(z) = B'(z). -/
lemma log_deriv_id
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z = deriv B z := by
  intro z hz
  -- z ∈ closedBall 0 r1 implies z ∈ closedBall 0 R
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR'_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR'_le
    simpa using hzR''
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hJd := hJ_deriv z hz
  have hmult := congrArg (fun t => t * B z) hJd
  have hR2 : (deriv B z / B z) * B z = deriv B z * B z / B z := by
    simpa using (div_mul_eq_mul_div (deriv B z) (B z) (B z))
  have hmult' : deriv J z * B z = deriv B z * B z / B z := by
    simpa [hR2] using hmult
  have hdiv' : deriv B z * B z / B z = deriv B z := by
    field_simp [hBnz]
  calc
    deriv J z * B z = deriv B z * B z / B z := hmult'
    _ = deriv B z := by simpa using hdiv'

/-- Lemma: J'(z)B(z) - B'(z) = 0. -/
lemma log_deriv_identity
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z * B z - deriv B z = 0 := by
  intro z hz
  have h_eq := log_deriv_id hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  rw [h_eq]
  simp

/-- Lemma: Derivative of H(z) using quotient rule. -/
lemma H_derivative_quotient_rule
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z =
      (deriv (fun w => Complex.exp (J w)) z * B z - deriv B z * Complex.exp (J z)) / (B z)^2 := by
  intro z hz
  -- z belongs to the larger closed ball
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR_le
    simpa using hzR''
  -- differentiability and nonvanishing of denominator
  have hB_nz : B z ≠ 0 := hB_ne_zero z hzR
  have hB' : AnalyticOnNhd ℂ B (Metric.closedBall 0 R') :=
    hB.mono (Metric.closedBall_subset_closedBall hR'_lt_R.le)
  have hB_diff : DifferentiableAt ℂ B z := (hB' z hzR).differentiableAt
  have hJ_diff : DifferentiableAt ℂ J z := (hJ z hz).differentiableAt
  have hF_diff : DifferentiableAt ℂ (fun w => Complex.exp (J w)) z := hJ_diff.cexp
  -- apply the quotient rule for derivatives
  have h := deriv_div (hc := hF_diff) (hd := hB_diff) (hx := hB_nz)
  rw [show ((fun w => Complex.exp (J w)) / B) = (fun z => Complex.exp (J z) / B z) from rfl] at h
  unfold H_auxiliary
  simpa [mul_comm] using h

lemma H_derivative_calc
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z =
      (deriv J z * B z - deriv B z) * Complex.exp (J z) / (B z)^2 := by
  intro z hz
  -- Get the quotient rule result
  have hquot := H_derivative_quotient_rule hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- Get the chain rule result for exp(J(z))
  have hchain : deriv (fun w => Complex.exp (J w)) z = deriv J z * Complex.exp (J z) := by
    have hJ_diff : DifferentiableAt ℂ J z := (hJ z hz).differentiableAt
    have hJ_has : HasDerivAt J (deriv J z) z := hJ_diff.hasDerivAt
    have hcomp := (Complex.hasDerivAt_exp (J z)).comp z hJ_has
    have hd := hcomp.deriv
    rw [show (Complex.exp ∘ J) = (fun w => Complex.exp (J w)) from rfl] at hd
    rwa [mul_comm] at hd
  -- Substitute chain rule into quotient rule
  rw [hquot, hchain]
  -- Now we have: (deriv J z * Complex.exp (J z) * B z - deriv B z * Complex.exp (J z)) / (B z)^2
  -- Factor out Complex.exp (J z)
  have h1 : deriv J z * Complex.exp (J z) * B z - deriv B z * Complex.exp (J z) =
           Complex.exp (J z) * (deriv J z * B z - deriv B z) := by ring
  rw [h1]
  -- Rearrange: Complex.exp (J z) * (deriv J z * B z - deriv B z) / (B z)^2 =
  --           (deriv J z * B z - deriv B z) * Complex.exp (J z) / (B z)^2
  ring

lemma H_derivative_is_zero
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 := by
  intro z hz
  have hcalc :=
    H_derivative_calc hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  have hident :=
    log_deriv_identity hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  simpa [hident] using hcalc

lemma H_auxiliary_differentiableOn_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1)) :
    DifferentiableOn ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) :=
by
  -- closedBall r1 is a subset of closedBall R
  have hsubset : Metric.closedBall (0 : ℂ) r1 ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    have hz' : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hle : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    have : dist z (0 : ℂ) ≤ R := le_trans hz' hle
    simpa [Metric.mem_closedBall] using this
  -- differentiability of J and B on the closed ball
  have hJ_diff : DifferentiableOn ℂ J (Metric.closedBall (0 : ℂ) r1) :=
    hJ.differentiableOn
  have hB_diff_r1 : DifferentiableOn ℂ B (Metric.closedBall (0 : ℂ) r1) :=
    (hB.differentiableOn).mono hsubset
  -- differentiability of exp on ℂ and composition with J
  have hExp_diff : DifferentiableOn ℂ Complex.exp (Set.univ : Set ℂ) :=
    (Complex.differentiable_exp.differentiableOn)
  have hExp_comp : DifferentiableOn ℂ (fun z => Complex.exp (J z)) (Metric.closedBall (0 : ℂ) r1) := by
    refine hExp_diff.comp hJ_diff ?_
    intro x hx; simp
  -- B is nonvanishing on the smaller closed ball
  have hB_ne_zero_r1 : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z ≠ 0 := by
    intro z hz; exact hB_ne_zero z (by
    have x : Metric.closedBall 0 r1 ⊆ Metric.closedBall 0 R' := Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_R')
    simp [x]
    simp at hz
    linarith
    )
  -- quotient rule for differentiability on sets
  have hdiv := hExp_comp.div hB_diff_r1 hB_ne_zero_r1
  rw [show ((fun z => Complex.exp (J z)) / B) = (fun z => Complex.exp (J z) / B z) from rfl] at hdiv
  -- unfold definition of H_auxiliary
  unfold H_auxiliary
  exact hdiv

lemma hasDerivAt_H_auxiliary_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      HasDerivAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) 0 z := by
  intro z hz
  -- z ∈ closedBall r1 implies z ∈ closedBall R
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := by
      simpa [Metric.mem_closedBall] using hz
    have hR_le : r1 ≤ R' := le_of_lt (hr1_lt_R')
    have hzR'' : dist z (0 : ℂ) ≤ R' := le_trans hzR' hR_le
    simpa [Metric.mem_closedBall] using hzR''
  have hBnz : B z ≠ 0 := hB_ne_zero z (hzR)
  -- Differentiability at z of exp ∘ J and of B
  have hJ_anal : AnalyticAt ℂ J z := hJ z hz
  have hExp_diff_at_Jz : DifferentiableAt ℂ Complex.exp (J z) :=
    Complex.differentiableAt_exp
  have hc_diff : DifferentiableAt ℂ (fun w => Complex.exp (J w)) z :=
    hExp_diff_at_Jz.comp z hJ_anal.differentiableAt

  have hB' : AnalyticOnNhd ℂ B (Metric.closedBall 0 R') :=
    hB.mono (Metric.closedBall_subset_closedBall hR'_lt_R.le)
  have hd_diff : DifferentiableAt ℂ B z := (hB' z hzR).differentiableAt
  -- DifferentiableAt for H and then HasDerivAt with deriv coefficient
  have hH_diff : DifferentiableAt ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z := by
    have hthis := hc_diff.div hd_diff hBnz
    rw [show ((fun w => Complex.exp (J w)) / B) = (fun z => Complex.exp (J z) / B z) from rfl] at hthis
    unfold H_auxiliary
    exact hthis
  have hH_has : HasDerivAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z) z :=
    hH_diff.hasDerivAt
  have hderiv0 : deriv (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) z = 0 :=
    H_derivative_is_zero hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  simpa [hderiv0] using hH_has

lemma H_auxiliary_fderivWithin_zero_on_closedBall
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 :=
by
  intro z hz
  -- classical derivative at z is zero, hence within derivative exists with value 0
  have hHasAt :=
    hasDerivAt_H_auxiliary_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero
      hJ hJ_zero hJ_deriv z hz
  have hHasWithin :
      HasDerivWithinAt (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J) 0
        (Metric.closedBall (0 : ℂ) r1) z :=
    hHasAt.hasDerivWithinAt
  -- compute the scalar derivative within equals 0 (with/without uniqueness)
  classical
  have hderivWithin0 :
      derivWithin (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) z = 0 := by
    by_cases hUDc : UniqueDiffWithinAt ℂ (Metric.closedBall (0 : ℂ) r1) z
    · simpa using hHasWithin.derivWithin hUDc
    · simpa using
        (derivWithin_zero_of_not_uniqueDiffWithinAt
          (𝕜 := ℂ)
          (f := H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
          (s := Metric.closedBall (0 : ℂ) r1) (x := z) hUDc)
  -- conclude on the Fréchet derivative within
  have h₁ : fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) z =
      ContinuousLinearMap.toSpanSingleton ℂ
        (derivWithin (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
          (Metric.closedBall (0 : ℂ) r1) z) :=
    (toSpanSingleton_derivWithin (𝕜 := ℂ)
      (f := H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (s := Metric.closedBall (0 : ℂ) r1) (x := z)).symm
  rw [h₁, hderivWithin0, ContinuousLinearMap.toSpanSingleton_zero]

/-- Lemma: H is constant on the closed ball. -/
lemma H_is_constant
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z =
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J 0 := by
  intro z hz
  have hs : Convex ℝ (Metric.closedBall (0 : ℂ) r1) := by
    simpa using (convex_closedBall (0 : ℂ) r1)
  have hdiff : DifferentiableOn ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
      (Metric.closedBall (0 : ℂ) r1) :=
    H_auxiliary_differentiableOn_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ
  have hfderiv0 : ∀ x ∈ Metric.closedBall (0 : ℂ) r1,
      fderivWithin ℂ (H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J)
        (Metric.closedBall (0 : ℂ) r1) x = 0 :=
    H_auxiliary_fderivWithin_zero_on_closedBall hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv
  exact hs.is_const_of_fderivWithin_eq_zero hdiff hfderiv0 hz
    (Metric.mem_closedBall_self hr1_pos.le)

lemma H_is_one
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      H_auxiliary hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero J z = 1 / B 0 := by
  intro z hz
  have hconst := H_is_constant hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  have h0 := H_at_zero hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv
  simpa [h0] using hconst

/-- Lemma: B(z) = B(0) * exp(J(z)). -/
lemma analytic_log_exists
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1, B z = B 0 * Complex.exp (J z) := by
  intro z hz
  -- Use H_is_one to get that H(z) = 1 / B(0)
  have hH_const := H_is_one hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- Unfold the definition of H_auxiliary
  unfold H_auxiliary at hH_const
  -- Now we have: exp(J z) / B z = 1 / B 0
  have hzR : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hzR' : dist z (0 : ℂ) ≤ r1 := hz
    have hR_le : r1 ≤ R := le_of_lt (lt_trans hr1_lt_R' hR'_lt_R)
    exact le_trans hzR' (by linarith)
  have hBnz : B z ≠ 0 := hB_ne_zero z hzR
  have hR_pos : 0 < R := lt_trans (lt_trans hr1_pos hr1_lt_R') hR'_lt_R
  have hB0nz : B 0 ≠ 0 := hB_ne_zero 0 (by
    simp [Metric.closedBall, dist_zero_right]
    exact le_of_lt (by linarith))
  -- From exp(J z) / B z = 1 / B 0, cross multiply
  have heq : Complex.exp (J z) * B 0 = B z := by
    field_simp [hBnz, hB0nz] at hH_const
    exact hH_const
  -- Use commutativity to get the desired form
  rw [← heq, mul_comm]

/-- Lemma: |B(z)| = |B(0)| * |exp(J(z))|. -/
lemma modulus_of_B_product_form
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * norm (Complex.exp (J z)) := by
  intro z hz
  have hBform := analytic_log_exists hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- B z = B 0 * exp (J z)
  simpa [norm_mul] using (congrArg norm hBform)

/-- Lemma: |B(z)| = |B(0)| * exp(Re(J(z))). -/
lemma modulus_of_exp_log
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      norm (B z) = norm (B 0) * Real.exp (Complex.re (J z)) := by
  intro z hz
  rw [modulus_of_B_product_form hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz]
  rw [Complex.norm_exp (J z)]

/-- Lemma: log|B(z)| = log|B(0)| + log(exp(Re(J(z)))). -/
lemma log_modulus_as_sum
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) =
      Real.log (norm (B 0)) + Real.log (Real.exp (Complex.re (J z))) := by
  intro z hz
  -- Get the equation |B(z)| = |B(0)| * exp(Re(J(z)))
  have h_eq := modulus_of_exp_log hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- Apply logarithm and use log(a * b) = log(a) + log(b)
  rw [h_eq, Real.log_mul]
  · -- Show norm (B 0) ≠ 0
    -- Since norm z = ‖z‖, we need ‖B 0‖ ≠ 0, which is equivalent to B 0 ≠ 0
    simp [norm_ne_zero_iff]
    apply hB_ne_zero
    -- Show 0 ∈ Metric.closedBall (0 : ℂ) R
    rw [Metric.mem_closedBall, dist_self]
    linarith
  · -- Show Real.exp (Complex.re (J z)) ≠ 0
    exact Real.exp_ne_zero _

/-- Lemma: log|B(z)| - log|B(0)| = Re(J(z)). -/
lemma real_log_of_modulus_difference
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0)
    {J : ℂ → ℂ}
    (hJ : AnalyticOnNhd ℂ J (Metric.closedBall (0 : ℂ) r1))
    (hJ_zero : J 0 = 0)
    (hJ_deriv : ∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J z = deriv B z / B z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J z) := by
  intro z hz
  -- Use the lemma log_modulus_as_sum
  have h_sum := log_modulus_as_sum hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ_zero hJ_deriv z hz
  -- Rearrange to get the difference
  rw [h_sum]
  -- Simplify Real.log (Real.exp (Complex.re (J z))) = Complex.re (J z)
  rw [Real.log_exp]
  ring

theorem log_of_analytic
    {r1 R' R : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R' : r1 < R') (hR'_lt_R : R' < R) (hR_lt_one : R < 1)
    {B : ℂ → ℂ}
    (hB : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R))
    (hB_ne_zero : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0) :
    ∃ J_B : ℂ → ℂ,
      AnalyticOnNhd ℂ J_B (Metric.closedBall (0 : ℂ) r1) ∧
      J_B 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1, deriv J_B z = deriv B z / B z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) r1,
        Real.log (norm (B z)) - Real.log (norm (B 0)) = Complex.re (J_B z)) := by
  have hB_ne_zero_R' : ∀ z ∈ Metric.closedBall (0 : ℂ) R', B z ≠ 0 := hB_ne_zero
  obtain ⟨J_B, hJ, hJ0, hJderiv⟩ :=
    I_is_antiderivative hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero_R'
  refine ⟨J_B, hJ, hJ0, hJderiv, ?_⟩
  intro z hz
  simpa using
    (real_log_of_modulus_difference hr1_pos hr1_lt_R' hR'_lt_R hR_lt_one hB hB_ne_zero hJ hJ0 hJderiv z hz)

end DiskAnalyticBounds
