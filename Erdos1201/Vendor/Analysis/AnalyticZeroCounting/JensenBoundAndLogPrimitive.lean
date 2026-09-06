module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Erdos1201.Vendor.Analysis.AnalyticZeroCounting.ZeroReflectionProductBound

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open DiskAnalyticBounds

/-!
Jensen's inequality for the zero-counting sum (multiplicative and
logarithmic forms, plus the resulting bound on the number of zeros), then
the construction of `Lf`, an analytic logarithm of `Bf` on a smaller disk
(via `DiskAnalyticBounds.log_of_analytic`), with `Lf 0 = 0` and its
derivative bounded via Borel–Carathéodory II. Finishes with the elementary
`logDeriv` algebra (product/quotient/power/constant rules) needed to expand
`logDeriv Bf` in the next module.
-/

public section

namespace AnalyticZeroCounting

lemma lem_jensen_inequality_form (B R R1 : ℝ) (hB : 1 < B)
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
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat : ℝ) ≤ B := by
  -- Derive f 0 ≠ 0 from f 0 = 1
  have hf0_ne0 : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
  -- Bound Bf at 0 using the maximum modulus arguments
  have hBf0 :=
    lem_Bf_at_0_le_M B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic hf0_ne0 h_finite_zeros h_σ h_σ_spec hf_le_B
  -- Convert that bound into the desired product bound
  let K := h_finite_zeros.toFinset
  have hres := lem_combine_bounds_on_Bf0 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hBf0
  -- Align coercions and finish (adjust numerical coercions if necessary)
  simpa using hres


lemma lem_log_mono_inc {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy

lemma lem_three_gt_e : (3 : ℝ) > Real.exp 1 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : (2.7182818286 : ℝ) < 3 := by norm_num
  exact lt_trans h1 h2  -- This is a numerical fact: e ≈ 2.718 < 3


lemma lem_jensen_log_form (B R R1 : ℝ) (hB : 1 < B)
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
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) * Real.log (R / R1) ≤ Real.log B := by
  -- Let S denote the sum of the multiplicities
  set S : ℝ := ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)
  -- From the Jensen-type inequality
  have hpow_le : (R / R1 : ℝ) ^ S ≤ B := by
    simpa [S] using
      (lem_jensen_inequality_form B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hf_le_B)
  -- Base positivity
  have hbase_pos : 1 < (R / R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have hbase_pos' : 0 < (R / R1 : ℝ) := by
    have : 0 < R := by linarith
    linarith
  -- Positivity of the left-hand side to apply log monotonicity
  have hxpos : 0 < (R / R1 : ℝ) ^ S := by
    simpa [S] using Real.rpow_pos_of_pos hbase_pos' S
  -- Apply monotonicity of log
  have hlog_le : Real.log ((R / R1 : ℝ) ^ S) ≤ Real.log B :=
    lem_log_mono_inc hxpos hpow_le
  -- Rewrite log of a power
  have hlog_rpow : Real.log ((R / R1 : ℝ) ^ S) = S * Real.log (R / R1) := by
    simpa using (Real.log_rpow hbase_pos' S)
  -- Conclude
  simpa [S, hlog_rpow] using hlog_le


lemma lem_sum_ineq {ι : Type*} (K : Finset ι) (a b : ι → ℝ)
  (h_le : ∀ i ∈ K, a i ≤ b i) :
  Finset.sum K a ≤ Finset.sum K b := by
  classical
  exact Finset.sum_le_sum (by intro i hi; exact h_le i hi)


lemma nat_one_le_cast_real (n : ℕ) : 1 ≤ n → (1 : ℝ) ≤ (n : ℝ) := by
  intro h
  rw [← Nat.cast_one]
  exact Nat.cast_le.mpr h


lemma lem_frho_zero' (R R1 : ℝ)
    (hR_pos : 0 < R1)
    (hR1 : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    f ρ = 0 := h_rho_in_KfR1.2

lemma lem_sum_m_rho_1 (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
     (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (hR_lt_1 : R < 1) :
    (h_finite_zeros.toFinset.card : ℝ) ≤ ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) := by
  -- Apply lem_sum_ineq as mentioned in the informal proof, with a_ρ = 1 and b_ρ = m_ρ
  -- First convert card to sum of 1's
  have h_card_as_sum : (h_finite_zeros.toFinset.card : ℝ) = ∑ ρ ∈ h_finite_zeros.toFinset, (1 : ℝ) := by
    simp [Finset.sum_const, smul_eq_mul]
  rw [h_card_as_sum]
  -- Now apply lem_sum_ineq
  apply lem_sum_ineq h_finite_zeros.toFinset (fun _ => (1 : ℝ)) (fun ρ => ((analyticOrderAt f ρ).toNat : ℝ))
  -- Show 1 ≤ m_ρ for each zero ρ (following the approach from lem_m_rho_ge_1)
  intro ρ hρ
  -- Get that ρ is a zero
  have hρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f :=
    (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
  have h_f_rho_zero : f ρ = 0 :=
    lem_frho_zero' R R1 (by linarith) hR1_lt_R f h_f_analytic ρ hρ_in_zeros
  -- f is analytic at ρ
  have h_f_analytic_at_rho : AnalyticAt ℂ f ρ := by
    apply h_f_analytic
    have h_R1_lt_1 : R1 < 1 := by linarith [hR_lt_1]
    exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) hρ_in_zeros.1
  -- The order is finite (following lem_m_rho_is_nat approach)
  have h_order_finite : analyticOrderAt f ρ ≠ ⊤ := by
    have h_R1_pos : 0 < R1 := by linarith [hR1_pos]
    apply analyticOrderAt_ne_top_of_finite_zeros_in_ball f R1 h_R1_pos
    · intro z hz
      apply h_f_analytic
      have h_R1_lt_1 : R1 < 1 := by linarith [hR_lt_1]
      exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) hz
    · exact h_f_rho_zero
    · exact hρ_in_zeros.1
    · exact h_finite_zeros
  -- Use analyticOrderAt_ge_one_of_zero: order ≥ 1 for zeros
  have h_order_ge_one : analyticOrderAt f ρ ≥ 1 :=
    analyticOrderAt_ge_one_of_zero f ρ h_f_analytic_at_rho h_f_rho_zero h_order_finite
  -- Convert to natural number bound
  have h_toNat_ge_one : 1 ≤ (analyticOrderAt f ρ).toNat := by
    have h_pos : 0 < analyticOrderAt f ρ := lt_of_lt_of_le zero_lt_one h_order_ge_one
    exact ENat.toNat_pos h_pos.ne' h_order_finite
  -- Convert to real
  exact nat_one_le_cast_real _ h_toNat_ge_one



lemma lem_sum_m_rho_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ (1/Real.log (R/R1)) * Real.log B := by
  have h_div_log : (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) * Real.log (R/R1) ≤ Real.log B := by
    apply lem_jensen_log_form B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hf_le_B
  have log_pos' : R/R1 > 1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have log_pos : Real.log (R/R1) > 0 := by exact Real.log_pos log_pos'
  calc
    ∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderAt f ρ).toNat
    _ = 1 / Real.log (R / R1) * (Real.log (R / R1) * (∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderAt f ρ).toNat)) := by
      field_simp [ne_of_gt log_pos]
    _ ≤ 1 / Real.log (R / R1) * Real.log B := by
      have hc : 0 ≤ 1 / Real.log (R / R1) := le_of_lt (div_pos one_pos log_pos)
      exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact h_div_log) hc

lemma lem_sum_1_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    (h_finite_zeros.toFinset.card : ℝ) ≤ (1/Real.log (R/R1)) * Real.log B := by
  have h1 :=
    lem_sum_m_rho_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_finite_zeros hR_lt_1
  have h2 :=
    lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ hf_le_B h_σ_spec
  exact le_trans h1 h2


variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 hR1_pos f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 hR1_pos f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)

-- Helper to get f 0 ≠ 0 from f 0 = 1
lemma f_zero_ne_zero (h_f_zero : f 0 = 1) : f 0 ≠ 0 := by
  rw [h_f_zero]; simp


lemma Bf_is_analytic_on_disk
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) :=
    let hspec := h_σ_spec
    lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
      h_finite_zeros h_σ hspec

lemma lem_Bf_eq_prod_Cf
    (R R1 : ℝ)
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
    ∀ z, Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) *
      (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z) := by
  intro z
  unfold Bf
  ring

lemma lem_num_prod_never_zero_all
    (R R1 : ℝ)
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
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1,
      (∏ ρ ∈ h_finite_zeros.toFinset,
        ((R : ℂ) - star ρ * z / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
  intro z hz
  apply Finset.prod_ne_zero_iff.mpr
  intro ρ hρ
  apply pow_ne_zero

  -- Following the informal proof: extract bounds |ρ| ≤ R1, |z| ≤ R1
  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    rwa [Set.Finite.mem_toFinset h_finite_zeros] at hρ
  have hρ_bound : ‖ρ‖ ≤ R1 := by
    rw [zerosetKfR] at hρ_mem; simp at hρ_mem; exact hρ_mem.1
  have hz_bound : ‖z‖ ≤ R1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hz; exact hz

  -- Get R > 0
  have hR_pos : (0 : ℝ) < R := lt_trans hR1_pos hR1_lt_R

  -- Key step: show R - R1²/R > 0 as stated in informal proof
  have key_positive : (0 : ℝ) < R - R1 * R1 / R := by
    -- Since R1 < R, we have R1² < R² so R1²/R < R
    have h1 : R1 * R1 < R * R := by
      apply mul_self_lt_mul_self (le_of_lt hR1_pos) hR1_lt_R
    have h2 : R1 * R1 / R < R := by
      rw [div_lt_iff₀ hR_pos]
      exact h1
    linarith [h2]

  -- Show factor is nonzero by proving positive norm
  suffices h : (0 : ℝ) < ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ by
    exact norm_pos_iff.mp h

  -- Use reverse triangle inequality: |a - b| ≥ |a| - |b|
  have triangle_ineq : ‖(R : ℂ) - star ρ * z / (R : ℂ)‖ ≥ ‖(R : ℂ)‖ - ‖star ρ * z / (R : ℂ)‖ :=
    norm_sub_norm_le _ _

  -- Simplify ‖(R : ℂ)‖ = R
  have R_norm_eq : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_of_nonneg (le_of_lt hR_pos)]

  -- Bound the product term: ‖star ρ * z / (R : ℂ)‖ ≤ R1 * R1 / R
  have product_bound : ‖star ρ * z / (R : ℂ)‖ ≤ R1 * R1 / R := by
    rw [norm_div, norm_mul, norm_star, R_norm_eq]
    -- We need to show ‖ρ‖ * ‖z‖ / R ≤ R1 * R1 / R
    -- This is equivalent to ‖ρ‖ * ‖z‖ ≤ R1 * R1
    have mult_bound : ‖ρ‖ * ‖z‖ ≤ R1 * R1 := by
      exact mul_le_mul hρ_bound hz_bound (norm_nonneg _) (le_of_lt hR1_pos)
    -- Use the fact that division preserves inequality for positive denominators
    have : ‖ρ‖ * ‖z‖ / R ≤ R1 * R1 / R := by
      exact div_le_div_of_nonneg_right mult_bound (le_of_lt hR_pos)
    exact this

  -- Combine the bounds: ‖factor‖ ≥ R - R1²/R > 0
  rw [R_norm_eq] at triangle_ineq
  linarith [triangle_ineq, product_bound, key_positive]

lemma Bf_never_zero
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1, Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z ≠ 0 := by
  intro z hz
  -- Use the factorization of Bf as product of numerator and Cf
  rw [lem_Bf_eq_prod_Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec]
  -- Show the product is nonzero by showing each factor is nonzero
  apply mul_ne_zero
  · -- First factor: the product over zeros (numerator part) using lem:bl_num_nonzero
    exact lem_num_prod_never_zero_all R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec z hz
  · -- Second factor: Cf never zero using lem:C_never_zero
    exact lem_Cf_never_zero h_finite_zeros h_σ h_σ_spec z hz

lemma Bf0_not_zero
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0 ≠ 0 := by
  apply Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  simp [Metric.mem_closedBall, dist_zero_right, le_of_lt hR1_pos]

@[expose] noncomputable def Lf : ℂ → ℂ :=
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  Classical.choose (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
)


lemma Lf_is_analytic
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec)
                     (Metric.closedBall (0 : ℂ) r) := by
  unfold Lf
  exact (Classical.choose_spec (log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
    )
  )).1

lemma Lf_at_0_is_0
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec 0 = 0 := by
  unfold Lf
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  let log_exists := log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro z hz
      have h_num_ne_zero : B_f z ≠ 0 :=
        Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz
      assumption
    )
  exact (Classical.choose_spec log_exists).2.1


lemma lem_BCII {L : ℂ → ℂ} {r M r₁ : ℝ}
    (hr_pos : 0 < r)
    (hM_pos : 0 < M)
    (hr₁_pos : 0 < r₁)
    (hr₁_lt_r : r₁  < r)
    (hL_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ DifferentiableOn ℂ L U)
    (hL0 : L 0 = 0)
    (hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ M)
    {z : ℂ} (hz : z ∈ Metric.closedBall 0 r₁) :
norm (deriv L z) ≤ (16 * M * r ^ 2) / ((r - r₁) ^ 3) := by
  apply borel_caratheodory_II hr_pos hM_pos hr₁_pos hr₁_lt_r hL_domain hL0 hre_L_le_M hz


lemma re_Lf_as_diff_of_log_mods
    (r R R1 : ℝ)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      Complex.re (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z) =
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) -
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)) := by
  intro z hz
  -- Use the three lemmas mentioned in informal proof: def:Lf, lem:log_of_analytic, lem:real_log_of_modulus_difference
  let B_f := Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ
  have h_Bf_analytic : AnalyticOnNhd ℂ B_f (Metric.closedBall (0 : ℂ) R) :=
    Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  have h_Bf_ne_zero : ∀ w ∈ Metric.closedBall (0 : ℂ) R1, B_f w ≠ 0 := by
    intro w hw
    exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw

  -- Apply lem:log_of_analytic
  have h_log_exists := log_of_analytic hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 h_Bf_analytic h_Bf_ne_zero
  have h_choose_spec := Classical.choose_spec h_log_exists

  -- Use def:Lf: Lf is defined as Classical.choose h_log_exists
  have h_Lf_def : Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec = Classical.choose h_log_exists := by
    unfold Lf
    simp only [B_f]

  -- Apply lem:real_log_of_modulus_difference
  rw [h_Lf_def]
  exact (h_choose_spec.2.2.2 z hz).symm

lemma log_Bf_le_log_B
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_Bf_pos : ∀ z, norm z ≤ R1 →
                0 < norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z))
    (h_Bf_bound : ∀ z, norm z ≤ R1 →
                  norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) ≤ Real.log B := by
  intro z hz
  apply Real.log_le_log
  · exact h_Bf_pos z hz
  · exact h_Bf_bound z hz


lemma log_Bf_le_log_B2
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_Bf_bound : ∀ z, ‖z‖ ≤ R →
                  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z, ‖z‖ ≤ R1 →
      Real.log (‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z‖) ≤ Real.log B := by
  -- Use log_Bf_le_log_B directly
  apply log_Bf_le_log_B B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  · -- Prove h_Bf_pos: ∀ z, ‖z‖ ≤ R1 → 0 < ‖Bf ... z‖
    intro z hz
    have hz_mem : z ∈ Metric.closedBall (0 : ℂ) R1 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hz
    have hBf_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz_mem
    exact norm_pos_iff.mpr hBf_ne_zero
  · -- Prove h_Bf_bound: ∀ z, ‖z‖ ≤ R1 → ‖Bf ... z‖ ≤ B
    intro z hz
    have hz_le_R : ‖z‖ ≤ R := by linarith [hz, hR1_lt_R]
    exact h_Bf_bound z hz_le_R

lemma log_Bf_le_log_B3
    (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ R1 →
      Real.log (norm (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z)) ≤ Real.log B := by
  -- Apply log_Bf_le_log_B2, which needs a bound on Bf on the disk of radius R
  apply log_Bf_le_log_B2 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  -- Get this bound using lem_Bf_bounded_in_disk_from_f
  apply lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ h_σ_spec
  -- Apply the hypothesis h_f_bound (norm = ‖·‖ definitionally)
  exact h_f_bound

lemma log_Bf0_ge_0
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    0 ≤ Real.log (‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0‖) := by
  -- Apply log monotonicity with x = 1 and y = |Bf(...,0)|
  have h_pos : 0 < (1 : ℝ) := by norm_num
  have h_Bf_ge_1 : 1 ≤ ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0‖ :=
    lem_mod_Bf_at_0_ge_1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_f_zero h_finite_zeros h_σ h_σ_spec
  have h_log_mono := lem_log_mono_inc h_pos h_Bf_ge_1
  rw [Real.log_one] at h_log_mono
  exact h_log_mono

lemma re_Lf_le_log_B
    (B r R R1 : ℝ)
    (hB : 1 < B)
    (hr_pos : 0 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ r →
      Complex.re (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z) ≤ Real.log B := by
  intro z hz
  -- Use re_Lf_as_diff_of_log_mods to rewrite the real part as a difference of logarithms
  rw [re_Lf_as_diff_of_log_mods r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z]
  · -- Apply log_Bf_le_log_B3 and log_Bf0_ge_0
    -- derive the required bound ‖z‖ ≤ R1 from ‖z‖ ≤ r and r < R1
    have hz_apply_BC_to_Lfle_R1 : ‖z‖ ≤ R1 := by linarith [hz, hr_lt_R1]
    have h1 := log_Bf_le_log_B3 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec h_f_bound z hz_apply_BC_to_Lfle_R1
    have h2 := log_Bf0_ge_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
    linarith
  · -- Show z is in the closed ball of radius r
    exact Metric.mem_closedBall.mpr (by simpa [dist_zero_right] using hz)

lemma analyticOnNhd_closedBall_exists_open_differentiableOn {L : ℂ → ℂ} {r : ℝ}
  (h : AnalyticOnNhd ℂ L (Metric.closedBall (0 : ℂ) r)) :
  ∃ U, IsOpen U ∧ Metric.closedBall (0 : ℂ) r ⊆ U ∧ DifferentiableOn ℂ L U := by
  classical
  -- Index the closed ball
  let I := {x : ℂ // x ∈ Metric.closedBall (0 : ℂ) r}
  -- For each point in the closed ball, obtain an open neighborhood where L is analytic
  have hI : ∀ i : I, ∃ (W : Set ℂ), IsOpen W ∧ (i : ℂ) ∈ W ∧ AnalyticOn ℂ L W := by
    intro i
    have hAt : AnalyticAt ℂ L (i : ℂ) := h i i.property
    -- From analyticity at a point, get a neighborhood where L is analytic
    have hWithin : AnalyticWithinAt ℂ L (Set.univ) (i : ℂ) := by
      simpa using (hAt.analyticWithinAt : AnalyticWithinAt ℂ L Set.univ (i : ℂ))
    rcases (AnalyticWithinAt.exists_mem_nhdsWithin_analyticOn hWithin) with ⟨U₀, hU₀nhds, hU₀analytic⟩
    have hU₀nhds' : U₀ ∈ nhds (i : ℂ) := by simpa [nhdsWithin_univ] using hU₀nhds
    rcases _root_.mem_nhds_iff.mp hU₀nhds' with ⟨W, hWsub, hWopen, hiW⟩
    refine ⟨W, hWopen, hiW, hU₀analytic.mono ?_⟩
    exact hWsub
  choose V hVopen hiV hVanalytic using hI
  -- Define U as the union of these neighborhoods
  let U : Set ℂ := ⋃ i : I, V i
  have hUopen : IsOpen U := by
    simpa [U] using isOpen_iUnion (fun i => hVopen i)
  -- The closed ball is covered by U
  have hsub : Metric.closedBall (0 : ℂ) r ⊆ U := by
    intro x hx
    refine Set.mem_iUnion.mpr ?_
    refine ⟨⟨x, hx⟩, ?_⟩
    simpa using hiV ⟨x, hx⟩
  -- L is differentiable on U since it is differentiable on each V i
  have hdiffOn : DifferentiableOn ℂ L U := by
    intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
    have hdi : DifferentiableOn ℂ L (V i) := (hVanalytic i).differentiableOn
    have hdiAt : DifferentiableAt ℂ L y := hdi.differentiableAt ((hVopen i).mem_nhds hyi)
    exact hdiAt.differentiableWithinAt
  exact ⟨U, hUopen, hsub, hdiffOn⟩

lemma log_pos_of_one_lt {B : ℝ} (hB : 1 < B) : 0 < Real.log B := by
  simpa using Real.log_pos hB

lemma apply_BC_to_Lf
    (B r1 r R R1 : ℝ)
    (hB : 1 < B)
    (hr1_pos : 0 < r1)
    (hr1_lt_r : r1 < r)
    (hr_lt_R1 : r < R1)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bound : ∀ z, norm z ≤ R → norm (f z) ≤ B) :
    ∀ z, norm z ≤ r1 →
      norm (deriv (Lf (lt_trans hr1_pos hr1_lt_r : 0 < r) hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z) ≤
      (16 * Real.log B * r^2) / (r - r1)^3 := by
  classical
  intro z hz
  -- derive 0 < r from 0 < r1 and r1 < r
  have hr_pos : 0 < r := lt_trans hr1_pos hr1_lt_r
  -- instantiate L := Lf ... with the derived positivity proof
  let L := Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
  -- L is analytic on a neighborhood of the closed ball of radius r
  have h_analytic_nhd :=
    Lf_is_analytic r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  -- Build an open set U containing the closed ball where L is differentiable
  let U : Set ℂ :=
    { y | ∃ x ∈ Metric.closedBall (0 : ℂ) r, ∃ s : ℝ, 0 < s ∧ y ∈ Metric.ball x s ∧
        AnalyticOnNhd ℂ L (Metric.ball x s) }
  have hU_open : IsOpen U := by
    refine isOpen_iff_mem_nhds.mpr ?_
    intro y hy
    rcases hy with ⟨x, hxCB, s, hs_pos, hyin, hAnaBall⟩
    have hnhds : Metric.ball x s ∈ nhds y := (Metric.isOpen_ball.mem_nhds hyin)
    exact Filter.mem_of_superset hnhds (by intro z hz; exact ⟨x, hxCB, s, hs_pos, hz, hAnaBall⟩)
  have hCB_subset : Metric.closedBall (0 : ℂ) r ⊆ U := by
    intro x hx
    have hAt : AnalyticAt ℂ L x := h_analytic_nhd x hx
    rcases AnalyticAt.exists_ball_analyticOnNhd hAt with ⟨s, hs_pos, hAnaBall⟩
    have hx_in_ball : x ∈ Metric.ball x s := by
      simpa [Metric.mem_ball, dist_self] using hs_pos
    exact ⟨x, hx, s, hs_pos, hx_in_ball, hAnaBall⟩
  have hDiffU : DifferentiableOn ℂ L U := by
    intro y hy
    rcases hy with ⟨x, hxCB, s, hs_pos, hy_in, hAnaBall⟩
    -- From AnalyticOnNhd on the ball, get AnalyticAt at y
    have hAt : AnalyticAt ℂ L y := hAnaBall y hy_in
    exact (AnalyticAt.differentiableAt hAt).differentiableWithinAt
  -- Package domain data
  have hL_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 r ⊆ U ∧ DifferentiableOn ℂ L U :=
    ⟨U, hU_open, hCB_subset, hDiffU⟩
  -- L(0) = 0
  have hL0 : L 0 = 0 := by
    simpa [L] using (Lf_at_0_is_0 r R R1 hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
  -- Re L ≤ log B on the closed ball of radius r
  have hre_L_le_M : ∀ w ∈ Metric.closedBall 0 r, (L w).re ≤ Real.log B := by
    intro w hw
    have hw' : norm w ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    exact re_Lf_le_log_B B r R R1 hB hr_pos hr_lt_R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec h_f_bound w hw'
  -- z ∈ closedBall 0 r1
  have hz' : z ∈ Metric.closedBall 0 r1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  -- Apply Borel–Carathéodory II
  have hBC :=
    lem_BCII hr_pos (Real.log_pos hB) hr1_pos hr1_lt_r hL_domain hL0 hre_L_le_M hz'
  -- conclude
  simpa [L] using hBC


lemma analyticOnNhd_Bf_closedBall (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z):
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) :=
  Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec

lemma helper_Bf_analytic_on_disk (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z):
    ∀ z ∈ Metric.closedBall (0 : ℂ) R, AnalyticAt ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) z := by
  intro z hz
  have h_analytic_on := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
  exact h_analytic_on z hz

-- Lemma 5: 1Bneq0
lemma oneBneq0 (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z):
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0 ≠ 0 ∧
    (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ ≠ 0 := by
  have h0mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using le_of_lt hR1_pos
  have hB0ne :
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0 ≠ 0 := by
    have h := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec

    exact h 0 h0mem
  refine And.intro hB0ne ?_
  exact inv_ne_zero hB0ne

-- Lemma 6: Lf_deriv_is_logBf_deriv
lemma Lf_deriv_is_logBf_deriv (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                           Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) z =
      logDeriv (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) z := by
  intro z _
  -- Rewrite the division as multiplication by inverse
  have h_eq : (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w /
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0) =
              (fun w ↦ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ *
                       Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w) := by
    ext w
    rw [div_eq_mul_inv]
    ring
  rw [h_eq]
  -- Show that Bf ... 0 ≠ 0 using Bf_never_zero
  have h0_in_ball : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R1 := by
    simp [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt hR1_pos
  have h_Bf0_ne_zero := Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec 0 h0_in_ball
  -- Show that the inverse is non-zero
  have h_inv_ne_zero : (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ 0)⁻¹ ≠ 0 :=
    inv_ne_zero h_Bf0_ne_zero
  -- Apply logDeriv_const_mul
  exact logDeriv_const_mul z _ h_inv_ne_zero

-- Lemma 7: Lfderiv_is_logderivBf

lemma logDeriv_div_const {a : ℂ} {g : ℂ → ℂ} (ha : a ≠ 0) : ∀ z, logDeriv (fun w ↦ g w / a) z = logDeriv g z := by
  intro z
  have hfun : (fun w ↦ g w / a) = (fun w ↦ a⁻¹ * g w) := by
    funext w
    simp [div_eq_mul_inv, mul_comm]
  simpa [hfun] using (logDeriv_const_mul z a⁻¹ (inv_ne_zero ha))

-- Continuing with the remaining lemmas...

-- Lemma 12: z_minus_rho_diff_nonzero
lemma z_minus_rho_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    z - ρ ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ w - ρ) z := by
  intro ρ hρ z hz
  have hz_pair := (Set.mem_sdiff z).1 hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_pair.1
  have hz_notK : z ∉ zerosetKfR R1 (by linarith) f := hz_pair.2
  -- Show z ≠ ρ hence z - ρ ≠ 0
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz_notK (by simpa [h_eq] using hρ)
  have h_nonzero : z - ρ ≠ 0 := sub_ne_zero.mpr hz_ne_rho
  -- Differentiability of w ↦ w - ρ at z
  have hdiff : DifferentiableAt ℂ (fun w => w) z := differentiableAt_fun_id
  have hdiff_sub : DifferentiableAt ℂ (fun w => w - ρ) z := hdiff.sub_const ρ
  exact ⟨h_nonzero, hdiff_sub⟩

-- Lemma 13: blaschke_num_diff_nonzero
lemma blaschke_num_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R,
    R - (star ρ) * z / R ≠ 0 ∧ DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := by
  intro ρ hρ z hz
  constructor
  · intro hzero
    have hRne : (R : ℂ) ≠ 0 := by
      simpa using (Complex.ofReal_ne_zero.mpr (ne_of_gt (hR1_pos.trans hR1_lt_R)))
    -- From the equation R - conj(ρ) * z / R = 0, deduce conj(ρ) * z = R^2
    have heq : (R : ℂ) = (star ρ) * z / (R : ℂ) := sub_eq_zero.mp hzero
    have hmul := congrArg (fun t : ℂ => t * (R : ℂ)) heq
    have heq_mul : (R : ℂ) * (R : ℂ) = (star ρ) * z := by
      -- simplify the right-hand side
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hRne] using hmul
    -- Take norms and simplify
    have hnorm_eq : ‖(R : ℂ)‖ * ‖(R : ℂ)‖ = ‖ρ‖ * ‖z‖ := by
      simpa [Complex.norm_mul, Complex.norm_conj] using congrArg (fun t : ℂ => ‖t‖) heq_mul
    -- Bounds: ‖z‖ ≤ R and ‖ρ‖ ≤ R1
    have hz_norm_le : ‖z‖ ≤ R := by
      have hz' : dist z (0 : ℂ) ≤ R := (Metric.mem_closedBall.mp hz)
      simpa [dist_eq_norm] using hz'
    have hrho_norm_le : ‖ρ‖ ≤ R1 := by
      rcases hρ with ⟨hρ_ball, _hρ_zero⟩
      have : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_ball)
      simpa [dist_eq_norm] using this
    have hz_nonneg : 0 ≤ ‖z‖ := by simp
    have hR1_nonneg : 0 ≤ R1 := le_of_lt hR1_pos
    have hle : ‖ρ‖ * ‖z‖ ≤ R1 * R := by
      have h1 : ‖ρ‖ * ‖z‖ ≤ R1 * ‖z‖ := mul_le_mul_of_nonneg_right hrho_norm_le hz_nonneg
      have h2 : R1 * ‖z‖ ≤ R1 * R := mul_le_mul_of_nonneg_left hz_norm_le hR1_nonneg
      exact le_trans h1 h2
    -- Evaluate ‖(R : ℂ)‖ as R (since R > 0)
    have hnorm_R : ‖(R : ℂ)‖ = R := by
      have h1 : ‖(R : ℂ)‖ = |R| := by simp
      simp [h1, abs_of_pos (hR1_pos.trans hR1_lt_R)]
    -- Rewrite the equality using hnorm_R
    have : R * R = ‖ρ‖ * ‖z‖ := by simpa [hnorm_R] using hnorm_eq
    have hle' : R * R ≤ R1 * R := by simpa [this] using hle
    -- But R1 * R < R * R since R > 0, hence RHS < LHS, contradiction
    have hposR : 0 < R := hR1_pos.trans hR1_lt_R
    have hposRR : 0 < R * R := by nlinarith [hposR]
    have hlt : R1 * R < R * R := by
      exact mul_lt_mul_of_pos_right hR1_lt_R hposR
    exact (lt_irrefl _ (lt_of_le_of_lt hle' hlt))
  · -- Differentiability: linear function
    have h_const : DifferentiableAt ℂ (fun _ : ℂ => (R : ℂ)) z := by
      simp
    have h_id : DifferentiableAt ℂ (fun w : ℂ => w) z := by
      simp
    have h_mul : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w) z := by
      simpa using h_id.const_mul (star ρ)
    have h_div : DifferentiableAt ℂ (fun w : ℂ => (star ρ) * w / (R : ℂ)) z := by
      simpa [div_eq_mul_inv] using h_mul.mul_const ((R : ℂ)⁻¹)
    simpa using h_const.sub h_div

-- Lemma 14: blaschke_frac_diff_nonzero
lemma blaschke_frac_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (R - (star ρ) * z / R) / (z - ρ) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro ρ hρ z hz
  -- Denominator: nonvanishing and differentiable
  have hden := z_minus_rho_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz
  have hden_ne : z - ρ ≠ 0 := hden.1
  have hden_diff : DifferentiableAt ℂ (fun w ↦ w - ρ) z := hden.2
  -- Extract membership in the smaller closed ball
  have hz_in_small : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_small : z ∈ Metric.closedBall (0 : ℂ) R1 := hz_in_small.1
  -- Show z ∈ closedBall 0 1 to use the numerator lemma
  have hz_dist_le_small : dist z (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hz_small
  have hRle : R ≤ 1 := le_of_lt hR_lt_1
  have hR1_le_R : R1 ≤ R := le_of_lt hR1_lt_R
  have hR1_le_1 : R1 ≤ 1 := le_trans hR1_le_R hRle
  have hz_ball1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have hz_le1 : dist z (0 : ℂ) ≤ 1 := le_trans hz_dist_le_small hR1_le_1
    simpa [Metric.mem_closedBall] using hz_le1
  -- Numerator: nonvanishing and differentiable
  have hz_ballR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : dist z (0 : ℂ) ≤ R := le_trans hz_dist_le_small (le_of_lt hR1_lt_R)
    simpa [Metric.mem_closedBall] using hz_le_R
  have hnum := blaschke_num_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ z hz_ballR
  have hnum_ne : R - (star ρ) * z / R ≠ 0 := hnum.1
  have hnum_diff : DifferentiableAt ℂ (fun w ↦ R - (star ρ) * w / R) z := hnum.2
  -- Conclude
  refine And.intro ?_ ?_
  · intro h
    have h' : (R - (star ρ) * z / R) * (z - ρ)⁻¹ = 0 := by
      simpa [div_eq_mul_inv] using h
    rcases mul_eq_zero.mp h' with hnum0 | hinv0
    · exact hnum_ne hnum0
    · exact hden_ne (inv_eq_zero.mp hinv0)
  · exact hnum_diff.div hden_diff hden_ne

-- Lemma 15: blaschke_pow_diff_nonzero
lemma blaschke_pow_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro ρ hρ z hz
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ z hz
  rcases hfrac with ⟨hne, hdiff⟩
  constructor
  · exact pow_ne_zero _ hne
  · simpa using hdiff.fun_pow ((analyticOrderAt f ρ).toNat)

-- Lemma 16: blaschke_prod_diff_nonzero
lemma blaschke_prod_diff_nonzero {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    (∏ ρ ∈ h_finite_zeros.toFinset, ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat) ≠ 0 ∧
    DifferentiableAt ℂ (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                        ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  classical
  constructor
  · -- non-vanishing of the product
    have hne_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.1
    exact (Finset.prod_ne_zero_iff).2 hne_each
  · -- differentiability of the product
    have hdiff_each : ∀ ρ ∈ h_finite_zeros.toFinset,
        DifferentiableAt ℂ
          (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
      intro ρ hρ
      have hρ' : ρ ∈ zerosetKfR R1 (by linarith) f :=
        (h_finite_zeros.mem_toFinset).1 hρ
      have hpair :=
        blaschke_pow_diff_nonzero (R := R) (R1 := R1) (f := f)
          hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ' z hz
      exact hpair.2
    -- Use DifferentiableAt.finsetProd and identify the function
    have hdiff :=
      (DifferentiableAt.finsetProd (u := h_finite_zeros.toFinset)
        (f := fun ρ => fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        (x := z) hdiff_each)
    have hfun_eq :
        (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)
        =
        (∏ ρ ∈ h_finite_zeros.toFinset,
            (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat)) := by
      funext w
      simp [Finset.prod_apply]
    exact hfun_eq.symm ▸ hdiff

-- Lemma 17: f_diff_nonzero_outside_Kf
lemma f_diff_nonzero_outside_Kf {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith ) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    f z ≠ 0 ∧ DifferentiableAt ℂ f z := by
  intro z hz
  -- unpack membership in the set difference
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R1 ∧
      z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 := hz'.1
  have hz_notin : z ∉ zerosetKfR R1 (by linarith) f := hz'.2
  -- show f z ≠ 0
  have hz_nonzero : f z ≠ 0 := by
    intro hfz
    exact hz_notin ⟨hz_in_R1, hfz⟩
  -- show differentiable at z using analyticity on closedBall 1
  have hR1_lt_1 : R1 < 1 := by linarith
  have hsubset1 :
      Metric.closedBall (0 : ℂ) R1 ⊆ Metric.ball (0 : ℂ) 1 :=
    Metric.closedBall_subset_ball hR1_lt_1
  have hz_in_ball1 : z ∈ Metric.ball (0 : ℂ) 1 := hsubset1 hz_in_R1
  have hz_in_1 : z ∈ Metric.closedBall (0 : ℂ) 1 :=
    Metric.ball_subset_closedBall hz_in_ball1
  have hAna : AnalyticAt ℂ f z := h_f_analytic z hz_in_1
  have hDiff : DifferentiableAt ℂ f z := hAna.differentiableAt
  exact ⟨hz_nonzero, hDiff⟩

-- Lemma 18: Bf_diff_nonzero_outside_Kf
lemma Bf_diff_nonzero_outside_Kf
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ z ≠ 0 ∧
    DifferentiableAt ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) z := by
  intro z hz
  -- Extract membership from set difference
  rw [Set.mem_sdiff] at hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R1 := hz.1

  constructor
  · -- Bf z ≠ 0: Apply Bf_never_zero directly
    exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec z hz_ball

  · -- DifferentiableAt: Use Bf_is_analytic_on_disk
    -- Since R1 < R, we have closedBall R1 ⊆ closedBall R
    have hz_R : z ∈ Metric.closedBall (0 : ℂ) R :=
      Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_R) hz_ball
    -- Get AnalyticOnNhd from the lemma
    have h_analytic_on := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec
    -- Apply to get AnalyticAt at z
    have h_analytic_at := h_analytic_on z hz_R
    -- Convert AnalyticAt to DifferentiableAt
    exact h_analytic_at.differentiableAt

/-- `deriv Lf` agrees with `logDeriv Bf` on the closed ball of radius `r`.
Split out of `Lf_deriv_step1`'s proof (upstream keeps it inline) so the
`unfold Lf` needed to reach `log_of_analytic`'s internal witness stays
inside this module: `Lf`'s `noncomputable def` embeds tactic-proof
subterms (e.g. `hB_ne_zero`'s proof) that the module system compiles as
file-private auxiliary constants even when `Lf` itself is `@[expose]`d, so
a cross-module `unfold Lf` cannot see them. -/
lemma Lf_deriv_eq_logDeriv_Bf :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r,
      deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z := by
  intro z hz_in_r
  let B_f : ℂ → ℂ :=
    fun w => Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
  let log_exists := log_of_analytic
    (r1 := r) (R' := R1) (R := R)
    hr_pos hr_lt_R1 hR1_lt_R hR_lt_1
    (B := B_f)
    (hB := Bf_is_analytic_on_disk R R1 hR1_pos hR1_lt_R hR_lt_1
              f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec)
    (hB_ne_zero := by
      intro w hw
      exact Bf_never_zero R R1 hR1_pos hR1_lt_R hR_lt_1
        f h_f_analytic h_f_zero h_finite_zeros h_σ h_σ_spec w hw)
  have hderiv_all : ∀ w ∈ Metric.closedBall (0 : ℂ) r,
      deriv (Classical.choose log_exists) w = deriv B_f w / B_f w :=
    (Classical.choose_spec log_exists).2.2.1
  have hderiv_Lf :
      deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos
                  h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
        = deriv B_f z / B_f z := by
    unfold Lf
    simpa using hderiv_all z hz_in_r
  have h_as_log : deriv B_f z / B_f z = logDeriv B_f z :=
    (logDeriv_apply B_f z).symm
  simpa [B_f] using hderiv_Lf.trans h_as_log

end AnalyticZeroCounting
