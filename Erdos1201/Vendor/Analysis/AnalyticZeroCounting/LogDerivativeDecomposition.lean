module

public import Erdos1201.Vendor.Analysis.AnalyticZeroCounting.JensenBoundAndLogPrimitive

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open DiskAnalyticBounds

/-!
The headline log-derivative decomposition theorem: expands `logDeriv Bf` as
`logDeriv f` plus the logarithmic derivative of the finite reflected-zero
product, then differentiates `Lf` termwise to get an explicit pole
expansion `f'/f - Σ mρ/(z-ρ) + Σ mρ/(z - R²/ρ̄)` for `deriv Lf`. Combines the
Borel–Carathéodory bound on `Lf'` (from `JensenBoundAndLogPrimitive`) with a
direct norm bound on the reflected-pole tail sum to conclude the final
inequality `‖f'/f - Σ mρ/(z-ρ)‖ ≤ (BC term + reflection term) · log B`.
-/

public section

namespace AnalyticZeroCounting

variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 hR1_pos f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 hR1_pos f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)

-- Lemma 20: logDeriv_Bf_is_sum

lemma nhds_avoids_finset {z : ℂ} (K : Finset ℂ) (hz : z ∉ (K : Set ℂ)) : ∀ᶠ w in nhds z, ∀ ρ ∈ K, w ≠ ρ := by
  classical
  -- Define the open set avoiding all points of K
  let U : Set ℂ := ⋂ ρ ∈ K, {w : ℂ | w ≠ ρ}
  -- Each set {w | w ≠ ρ} is open, being the complement of a singleton
  have hopen_each : ∀ ρ ∈ K, IsOpen ({w : ℂ | w ≠ ρ} : Set ℂ) := by
    intro ρ hρ
    have hopen : IsOpen ((({ρ} : Set ℂ)ᶜ : Set ℂ)) := isOpen_compl_singleton
    have hEq : ((({ρ} : Set ℂ)ᶜ : Set ℂ)) = {w : ℂ | w ≠ ρ} := by
      ext w; simp
    simpa [hEq]
      using hopen
  -- Hence the finite intersection is open
  have hopenU : IsOpen U :=
    isOpen_biInter_finset (s := K) (f := fun ρ : ℂ => ({w : ℂ | w ≠ ρ} : Set ℂ)) hopen_each
  -- z belongs to U because z ≠ ρ for all ρ ∈ K (since z ∉ K)
  have hzU : z ∈ U := by
    have hznot : ∀ ρ ∈ K, z ≠ ρ := by
      intro ρ hρ h
      exact hz (by simpa [h] using hρ)
    simpa [U] using hznot
  -- Therefore U is a neighborhood of z
  have hU_mem : U ∈ nhds z := hopenU.mem_nhds hzU
  -- Any point in U is different from all points of K
  refine Filter.eventually_of_mem hU_mem ?_
  intro w hw ρ hρ
  have hw_all := Set.mem_iInter₂.mp hw
  have : w ∈ ({w : ℂ | w ≠ ρ} : Set ℂ) := hw_all ρ hρ
  simpa using this

lemma Cf_eventually_eq_f_div_prod {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    (fun w ↦ Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (by simp [h_f_zero]) h_finite_zeros h_σ w)
      =ᶠ[nhds z]
    (fun w ↦ f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) := by
  classical
  rcases hz with ⟨hz_ball, hz_notin⟩
  -- Let S be the finite zero set
  set S : Set ℂ := zerosetKfR R1 (by linarith) f
  have hS_fin : S.Finite := h_finite_zeros
  have hU_open : IsOpen Sᶜ := hS_fin.isClosed.isOpen_compl
  have hz_memU : z ∈ Sᶜ := by simpa [S] using hz_notin
  have hU_mem : Sᶜ ∈ nhds z := hU_open.mem_nhds hz_memU
  refine Filter.eventually_of_mem hU_mem ?_
  intro w hw
  have hw_notin : w ∉ S := by
    -- w ∈ Sᶜ
    simpa [Set.mem_compl] using hw
  -- Simplify Cf on Sᶜ
  simp [S, Cf, hw_notin]

lemma prod_num_mul_inv_den_eq_prod_ratio
  (K : Finset ℂ) (N D : ℂ → ℂ) (m : ℂ → ℕ) :
  (∏ ρ ∈ K, (N ρ) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ) ^ (m ρ))⁻¹
  = ∏ ρ ∈ K, ((N ρ / D ρ) ^ (m ρ)) := by
  classical
  -- rewrite inverse of product as product of inverses
  have hinv : (∏ ρ ∈ K, (D ρ) ^ (m ρ))⁻¹ = ∏ ρ ∈ K, ((D ρ) ^ (m ρ))⁻¹ := by
    simp
  calc
    (∏ ρ ∈ K, (N ρ) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ) ^ (m ρ)) * (∏ ρ ∈ K, ((D ρ) ^ (m ρ))⁻¹) := by
          simp
    _ = ∏ ρ ∈ K, ((N ρ) ^ (m ρ) * ((D ρ) ^ (m ρ))⁻¹) := by
          simpa using (Finset.prod_mul_distrib (s := K)
                        (f := fun ρ => (N ρ) ^ (m ρ))
                        (g := fun ρ => ((D ρ) ^ (m ρ))⁻¹)).symm
    _ = ∏ ρ ∈ K, ((N ρ / D ρ) ^ (m ρ)) := by
          apply Finset.prod_congr rfl
          intro ρ hρ
          -- manipulate per factor
          calc
            (N ρ) ^ (m ρ) * ((D ρ) ^ (m ρ))⁻¹
                = (N ρ) ^ (m ρ) * ((D ρ)⁻¹) ^ (m ρ) := by
                  simp
            _ = ((N ρ) * (D ρ)⁻¹) ^ (m ρ) := by
                  simp [mul_pow]
            _ = (N ρ / D ρ) ^ (m ρ) := by
                  simp [div_eq_mul_inv]

lemma prod_num_mul_inv_den_eq_prod_ratio_fun
  (K : Finset ℂ) (N D : ℂ → ℂ → ℂ) (m : ℂ → ℕ) :
  (fun w ↦ (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹)
  = (fun w ↦ ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ))) := by
  funext w
  classical
  have h_inv :
      (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹ = ∏ ρ ∈ K, ((D ρ w) ^ (m ρ))⁻¹ := by
    simp
  calc
    (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, ((D ρ w) ^ (m ρ))⁻¹) := by
          rw [h_inv]
    _   = ∏ ρ ∈ K, ((N ρ w) ^ (m ρ)) * ((D ρ w) ^ (m ρ))⁻¹ := by
          simpa using
            (Finset.prod_mul_distrib
              (s := K)
              (f := fun ρ => (N ρ w) ^ (m ρ))
              (g := fun ρ => ((D ρ w) ^ (m ρ))⁻¹)).symm
    _   = ∏ ρ ∈ K, (N ρ w / D ρ w) ^ (m ρ) := by
          refine Finset.prod_congr rfl ?_
          intro ρ hρ
          have hpow :
            (N ρ w / D ρ w) ^ (m ρ)
              = ((N ρ w) ^ (m ρ)) * ((D ρ w) ^ (m ρ))⁻¹ := by
            simp [div_eq_mul_inv, mul_pow, inv_pow]
          simp [hpow]

lemma div_mul_eq_mul_mul_inv_fun {α} (f A B : α → ℂ) :
  (fun w => (f w / A w) * B w) = (fun w => f w * (B w * (A w)⁻¹)) := by
  funext w
  simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

lemma prod_num_mul_inv_den_eq_prod_ratio_fun_mem
  (K : Finset ℂ) (N D : ℂ → ℂ → ℂ) (m : ℂ → ℕ) :
  (fun w ↦ (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹)
  = (fun w ↦ ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ))) := by
  funext w
  classical
  calc
    (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) * (∏ ρ ∈ K, (D ρ w) ^ (m ρ))⁻¹
        = (∏ ρ ∈ K, (N ρ w) ^ (m ρ)) / (∏ ρ ∈ K, (D ρ w) ^ (m ρ)) := by
          simp [div_eq_mul_inv]
    _ = ∏ ρ ∈ K, ((N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ)) := by
          simp
    _ = ∏ ρ ∈ K, ((N ρ w / D ρ w) ^ (m ρ)) := by
          refine Finset.prod_congr rfl ?_
          intro ρ hρ
          have hpow_div :
              (N ρ w / D ρ w) ^ (m ρ)
                = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
            calc
              (N ρ w / D ρ w) ^ (m ρ)
                  = (N ρ w * (D ρ w)⁻¹) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
              _ = (N ρ w) ^ (m ρ) * ((D ρ w)⁻¹) ^ (m ρ) := by
                        simpa using (mul_pow (N ρ w) ((D ρ w)⁻¹) (m ρ))
              _ = (N ρ w) ^ (m ρ) * ((D ρ w) ^ (m ρ))⁻¹ := by
                        simp
              _ = (N ρ w) ^ (m ρ) / (D ρ w) ^ (m ρ) := by
                        simp [div_eq_mul_inv]
          simpa using hpow_div.symm

lemma logDeriv_Bf_is_sum :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \
          zerosetKfR R1 (by linarith) f,
    logDeriv (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ) z =
    logDeriv f z +
      logDeriv
        (fun w ↦
          ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  classical
  intro z hz
  -- Abbreviations
  set K : Finset ℂ := h_finite_zeros.toFinset
  -- Define denominator and numerator products and the ratio product
  let A : ℂ → ℂ := fun w => ∏ ρ ∈ K, (w - ρ) ^ (analyticOrderAt f ρ).toNat
  let BN : ℂ → ℂ := fun w => ∏ ρ ∈ K, (R - (star ρ) * w / R) ^ (analyticOrderAt f ρ).toNat
  let RatProd : ℂ → ℂ :=
    fun w => ∏ ρ ∈ K, ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat
  -- Establish: Bf is eventually equal to f times the product of ratios near z
  set S : Set ℂ := zerosetKfR R1 (by linarith) f
  have hS_fin : S.Finite := h_finite_zeros
  have hU_open : IsOpen Sᶜ := hS_fin.isClosed.isOpen_compl
  have hz_notin : z ∉ S := by
    rcases hz with ⟨_, hnotin⟩; exact hnotin
  have hzU : z ∈ Sᶜ := by simpa [Set.mem_compl] using hz_notin
  have hU_mem : Sᶜ ∈ nhds z := hU_open.mem_nhds hzU
  have h_ev :
      (fun w ↦ Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w)
        =ᶠ[nhds z]
      (fun w ↦ f w * RatProd w) := by
    refine Filter.eventually_of_mem hU_mem ?_
    intro w hwU
    have hw_notin : w ∉ S := by simpa [Set.mem_compl] using hwU
    -- Rewrite Bf and Cf at points away from the zero set
    have hBf_w :
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w * BN w := by
      simp [Bf, BN, K]
    have hCf_w :
        Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = f w / A w := by
      simp [Cf, S, A, K, hw_notin]
    -- Use functional identities to simplify to f * RatProd
    have h_eq1 := div_mul_eq_mul_mul_inv_fun (f := f) (A := A) (B := BN)
    have h_eq1_w : (f w / A w) * BN w = f w * (BN w * (A w)⁻¹) := by
      simpa using congrArg (fun g : (ℂ → ℂ) => g w) h_eq1
    have h_eq2 :=
      prod_num_mul_inv_den_eq_prod_ratio_fun_mem
        (K := K)
        (N := fun ρ w ↦ (R - (star ρ) * w / R))
        (D := fun ρ w ↦ (w - ρ))
        (m := fun ρ ↦ (analyticOrderAt f ρ).toNat)
    have h_eq2_w : BN w * (A w)⁻¹ = RatProd w := by
      simpa [BN, A, RatProd] using congrArg (fun g : (ℂ → ℂ) => g w) h_eq2
    -- Chain the equalities
    calc
      Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero) h_finite_zeros h_σ w
          = (f w / A w) * BN w := by simpa [hCf_w] using hBf_w
      _ = f w * (BN w * (A w)⁻¹) := h_eq1_w
      _ = f w * RatProd w := by simp [h_eq2_w]
  -- Transfer equality to logDeriv at z
  have hlog_congr := (logDeriv_congr_nhds h_ev).self_of_nhds
  -- Apply product rule to the RHS
  have hf' := f_diff_nonzero_outside_Kf (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  obtain ⟨hf_ne, hf_diff⟩ := hf'
  have hg' := blaschke_prod_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  obtain ⟨hg_ne, hg_diff⟩ := hg'
  have hsum := logDeriv_mul (f := f) (g := RatProd) z hf_ne hg_ne hf_diff hg_diff
  simpa [RatProd, K] using hlog_congr.trans hsum

theorem ball_containment {r R1 : ℝ} (_hr_pos : 0 < r) (hr_lt_R1 : r < R1) (z : ℂ) (hz : z ∈ Metric.closedBall 0 r) : z ∈ Metric.closedBall 0 R1 := by
  simp at *
  exact le_trans hz (le_of_lt hr_lt_R1)

theorem in_r_minus_kf {R1 r : ℝ} {f : ℂ → ℂ}
  (hr_pos : 0 < r)
  (hr_lt_R1 : r < R1)
  (z : ℂ)
  (hz : z ∈ Metric.closedBall 0 r \ zerosetKfR R1 (by linarith) f) :
   z ∈ Metric.closedBall 0 R1 \ zerosetKfR R1 (by linarith) f := by
  obtain ⟨h1, h2⟩ := hz
  have : z ∈ Metric.closedBall 0 R1 := by
    apply ball_containment hr_pos hr_lt_R1 z h1
  constructor <;> assumption

-- Lemma 22: Lf_deriv_step1
lemma Lf_deriv_step1 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
                                ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  -- Extract closedBall membership
  have hz' : z ∈ Metric.closedBall (0 : ℂ) r ∧ z ∉ zerosetKfR R1 (by linarith) f := by
    simpa [Set.mem_sdiff] using hz
  have hz_ball : z ∈ Metric.closedBall (0 : ℂ) r := hz'.1
  -- From Lfderiv_is_logderivBf
  have hLf :=
  --
    (Lf_deriv_is_logBf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec
      z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)).symm
  -- Expand logDeriv of Bf into sum
  have hsum :
      logDeriv (fun w ↦
        Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
          h_finite_zeros h_σ w) z =
      logDeriv f z +
        logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
            ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    have h :=
      (logDeriv_Bf_is_sum (R := R) (R1 := R1) (r := r) (f := f) (h_σ := h_σ)
        hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros) z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
    simpa using h
  -- Turn logDeriv f into deriv f / f using differentiability and nonvanishing
  obtain ⟨hf_ne, hfdiff⟩ :=
    f_diff_nonzero_outside_Kf (R := R) (R1 := R1) (f := f)
      hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have hfrac : logDeriv f z = deriv f z / f z := logDeriv_apply f z
  -- Combine
  -- First, identify deriv Lf with the logarithmic derivative of Bf at z
  -- (proved in JensenBoundAndLogPrimitive, where `unfold Lf` can still see
  -- Lf's file-private internal witnesses; see that lemma's docstring)
  have hLf_eq_logDerivBf :=
    Lf_deriv_eq_logDeriv_Bf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz_ball
  -- Chain the identities: deriv Lf = logDeriv Bf = logDeriv f + logDeriv(prod),
  -- then rewrite logDeriv f as deriv f / f.
  calc
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z
        = logDeriv (fun w ↦
            Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic (f_zero_ne_zero h_f_zero)
              h_finite_zeros h_σ w) z := hLf_eq_logDerivBf
    _ = logDeriv f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := hsum
    _ = deriv f z / f z +
          logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
            simp [hfrac]

-- Lemma 23: logDeriv_prod_is_sum
lemma logDeriv_prod_is_sum {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, logDeriv (fun w ↦
              ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
  intro z hz
  have hdiff : ∀ ρ ∈ h_finite_zeros.toFinset,
      DifferentiableAt ℂ (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.2
  have hne : ∀ ρ ∈ h_finite_zeros.toFinset,
      ((R - (star ρ) * z / R) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat ≠ 0 := by
    intro ρ hρ
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f :=
      (h_finite_zeros.mem_toFinset).mp hρ
    have h := blaschke_pow_diff_nonzero (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρmem z hz
    exact h.1
  simpa using logDeriv_fun_prod hne hdiff

-- Lemma 24: logDeriv_power_is_mul
lemma logDeriv_power_is_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    (analyticOrderAt f ρ).toNat * logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz ρ hρFin
  have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    simpa using (h_finite_zeros.mem_toFinset.mp hρFin)
  have hfrac :=
    blaschke_frac_diff_nonzero (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρmem z hz
  rcases hfrac with ⟨_hneq, hdiff⟩
  simpa using logDeriv_fun_pow hdiff (analyticOrderAt f ρ).toNat

-- Lemma 25: logDeriv_prod_is_sum_mul
lemma logDeriv_prod_is_sum_mul {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    logDeriv (fun w ↦ ∏ ρ ∈ h_finite_zeros.toFinset,
             ((R - (star ρ) * w / R) / (w - ρ)) ^ (analyticOrderAt f ρ).toNat) z =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have hsum :=
    logDeriv_prod_is_sum (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz
  refine hsum.trans ?_
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  exact
    logDeriv_power_is_mul (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ

-- Lemma 26: Lf_deriv_step2
lemma Lf_deriv_step2 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                                       logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z := by
  intro z hz
  classical
  have h1 :=
    Lf_deriv_step1 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  have hsum :=
    logDeriv_prod_is_sum_mul (R:=R) (R1:=R1) (f:=f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)
  have h2 := congrArg (fun t => deriv f z / f z + t) hsum
  exact h1.trans h2

-- Lemma 27: logDeriv_Blaschke_is_diff
lemma logDeriv_Blaschke_is_diff {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ∀ ρ ∈ h_finite_zeros.toFinset,
    logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
    logDeriv (fun w ↦ R - (star ρ) * w / R) z - logDeriv (fun w ↦ w - ρ) z := by
  intro z hz ρ hρ
  have hρ_set : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (Set.Finite.mem_toFinset (hs := h_finite_zeros) (a := ρ)).mp hρ
  rcases hz with ⟨hz_in, hz_notin⟩
  have hden := z_minus_rho_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z ⟨hz_in, hz_notin⟩
  rcases hden with ⟨hden_nz, hden_diff⟩
  have hz_le : ‖z‖ ≤ R1 := by
    simpa [Metric.closedBall, dist_eq_norm] using hz_in
  have hle1 : R1 < 1 := by linarith [hR1_lt_R, hR_lt_1]
  have hz_in1 : z ∈ Metric.closedBall (0 : ℂ) 1 := by
    have : ‖z‖ ≤ 1 := le_of_lt (hz_le.trans_lt hle1)
    simpa [Metric.closedBall, dist_eq_norm] using this
  have hz_inR : z ∈ Metric.closedBall (0 : ℂ) R := by
    have hz_le_R : ‖z‖ ≤ R := by
      calc ‖z‖ ≤ R1 := hz_le
      _ ≤  R := le_of_lt hR1_lt_R
    simpa [Metric.closedBall, dist_eq_norm] using hz_le_R
  have hnum := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros
      ρ hρ_set z hz_inR
  rcases hnum with ⟨hnum_nz, hnum_diff⟩
  exact logDeriv_div z hnum_nz hden_nz hnum_diff hden_diff

-- Lemma 28: logDeriv_linear
lemma logDeriv_linear {a b : ℂ} {z : ℂ} (ha : a ≠ 0) (hz : z ≠ -b/a) :
    logDeriv (fun w ↦ a * w + b) z = a / (a * z + b) := by
  -- derivative of w ↦ a * w is a
  have h_id : HasDerivAt (fun w : ℂ => w) (1 : ℂ) z := hasDerivAt_id _
  have h_mul' : HasDerivAt (fun w : ℂ => a * w) a z := by
    simpa [one_mul] using (h_id.const_mul a)
  have h_deriv_mul : deriv (fun w : ℂ => a * w) z = a := h_mul'.deriv
  -- unfold logDeriv and compute
  simp [logDeriv, h_deriv_mul]

-- Lemma 29: logDeriv_denominator
lemma logDeriv_denominator {ρ : ℂ} {z : ℂ} (hz : z ≠ ρ) :
    logDeriv (fun w ↦ w - ρ) z = 1 / (z - ρ) := by
  have h :=
    logDeriv_linear (a := (1 : ℂ)) (b := -ρ) (z := z)
      (ha := by simp)
      (hz := by simpa using hz)
  simpa [one_mul, sub_eq_add_neg] using h

-- Lemma 30: logDeriv_numerator_pre
lemma logDeriv_numerator_pre {R : ℝ} {ρ : ℂ} {z : ℂ} :
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = -(star ρ) / R / (R - (star ρ) * z / R) := by
  classical
  -- Put the function in the linear form b + a * w
  let a : ℂ := -(star ρ) / (R : ℂ)
  let b : ℂ := (R : ℂ)
  have hlin : (fun w : ℂ ↦ (R : ℂ) - (star ρ) * w / (R : ℂ)) = (fun w : ℂ ↦ b + a * w) := by
    funext w
    -- rewrite as b + a*w
    simp [a, b, sub_eq_add_neg, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
          add_comm, add_left_comm, add_assoc]
  -- Compute the derivative of b + a * w
  have hderiv_add : deriv (fun w : ℂ => b + a * w) z =
      deriv (fun _ : ℂ => b) z + deriv (fun y : ℂ => a * y) z := by
    simp
  have hderiv_ab : deriv (fun w : ℂ => b + a * w) z = a := by
    simp [deriv_const, deriv_const_mul, mul_comm]
  -- Now compute the logarithmic derivative and rewrite back
  simp [hlin, logDeriv, hderiv_ab, a, b, sub_eq_add_neg, div_eq_mul_inv,
         mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

lemma star_ne_zero_of_ne_zero {ρ : ℂ} (hρ : ρ ≠ 0) : star ρ ≠ 0 := by
  -- Use that conjugation preserves (and reflects) zero over ℂ
  -- This is true in any star semiring: star x = 0 ↔ x = 0
  -- We use the forward direction: if star ρ = 0 then ρ = 0, contradicting hρ
  intro h
  -- apply the equivalence star_eq_zero.mp
  have : ρ = 0 := (star_eq_zero).1 h
  exact hρ this

lemma field_identity_general {K : Type*} [Field K] {a b c : K} (ha : a ≠ 0) (hb : b ≠ 0) (hden : a - c*b/a ≠ 0) : (-(b/a)) / (a - c*b/a) = (1 : K) / (c - a^2/b) := by
  -- Multiply numerator and denominator by -a/b
  have hmul : (-(a / b) : K) ≠ 0 := by
    have hdiv_ne : a / b ≠ 0 := div_ne_zero ha hb
    exact neg_ne_zero.mpr hdiv_ne
  have hnum : (-(b/a) * (-(a/b))) = (1 : K) := by
    calc
      (-(b/a) * (-(a/b))) = (b/a) * (a/b) := by simp [neg_mul_neg]
      _ = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have hOne : (b/a) * (a/b) = (1 : K) := by
    calc
      (b/a) * (a/b) = (b * a⁻¹) * (a * b⁻¹) := by simp [div_eq_mul_inv]
      _ = b * (a⁻¹ * (a * b⁻¹)) := by simp [mul_assoc]
      _ = b * ((a⁻¹ * a) * b⁻¹) := by simp [mul_assoc]
      _ = b * (1 * b⁻¹) := by simp [ha]
      _ = b * b⁻¹ := by simp
      _ = 1 := by simp [hb]
  have haab : a * (a / b) = a^2 / b := by
    simp [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hcbab : (c * b / a) * (a / b) = c := by
    calc
      (c * b / a) * (a / b) = (c * (b / a)) * (a / b) := by simp [div_eq_mul_inv, mul_assoc]
      _ = c * ((b / a) * (a / b)) := by simp [mul_assoc]
      _ = c * 1 := by simp [hOne]
      _ = c := by simp
  have hdenom : ((a - c*b/a) * (-(a/b))) = c - a^2 / b := by
    calc
      ((a - c*b/a) * (-(a/b))) = -((a - c*b/a) * (a / b)) := by simp [mul_neg]
      _ = -(a * (a / b) - (c * b / a) * (a / b)) := by simp [sub_mul]
      _ = (c * b / a) * (a / b) - a * (a / b) := by simp [neg_sub]
      _ = c - a^2 / b := by simp [hcbab, haab]
  calc
    (-(b/a)) / (a - c*b/a)
        = (-(b/a) * (-(a/b))) / ((a - c*b/a) * (-(a/b))) := by
          simpa using
            (mul_div_mul_right (a := (-(b / a))) (b := (a - c * b / a)) (c := (-(a / b))) hmul).symm
    _ = 1 / ((a - c*b/a) * (-(a/b))) := by simp [hnum]
    _ = 1 / (c - a^2/b) := by simp [hdenom]

lemma complex_identity_from_field {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hρ : ρ ≠ 0) (hden : (R:ℂ) - (star ρ) * z / R ≠ 0) : (-(star ρ) / (R:ℂ)) / ((R:ℂ) - (star ρ) * z / R) = (1 : ℂ) / (z - (R:ℂ)^2 / (star ρ)) := by
  have ha : (R : ℂ) ≠ 0 := by simpa using (Complex.ofReal_ne_zero.mpr hR)
  have hb : star ρ ≠ 0 := star_ne_zero_of_ne_zero hρ
  have hden' : (R : ℂ) - z * (star ρ) / (R : ℂ) ≠ 0 := by
    simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hden
  have h := field_identity_general (K := ℂ) (a := (R : ℂ)) (b := star ρ) (c := z) ha hb hden'
  simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using h

lemma logDeriv_numerator_rearranged {R : ℝ} {ρ z : ℂ} (hR : R ≠ 0) (hrho : ρ ≠ 0) (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0) : -(star ρ) / R / ((R : ℂ) - (star ρ) * z / R) = 1 / (z - (R : ℂ)^2 / (star ρ)) := by
  simpa using (complex_identity_from_field (R:=R) (ρ:=ρ) (z:=z) (hR:=hR) (hρ:=hrho) (hden:=h_denom_ne_zero))

-- Lemma 32: logDeriv_numerator
lemma logDeriv_numerator {R : ℝ} {ρ : ℂ} {z : ℂ}
    (hR : R ≠ 0)
    (hrho : ρ ≠ 0)
    (h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0):
    logDeriv (fun w ↦ R - (star ρ) * w / R) z = 1 / (z - R^2 / (star ρ)) := by
  rw [logDeriv_numerator_pre, logDeriv_numerator_rearranged]
  <;> assumption

-- Lemma 33: logDeriv_Blaschke_is_diff_frac
lemma logDeriv_Blaschke_is_diff_frac {R R1 : ℝ} {f : ℂ → ℂ}
     (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1) (h_f_zero : f 0 = 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ ρ ∈ h_finite_zeros.toFinset,
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f , logDeriv (fun w ↦ (R - (star ρ) * w / R) / (w - ρ)) z =
         1 / (z - R^2 / (star ρ)) - 1 / (z - ρ) := by
  intro ρ hρ z hz
  -- Apply the division rule for logDeriv using logDeriv_Blaschke_is_diff
  have h_div := logDeriv_Blaschke_is_diff (R := R) (R1 := R1) (f := f) hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz ρ hρ
  -- Evaluate logDeriv(R - (star ρ) * w / R) using logDeriv_numerator
  have hρ_mem : ρ ∈ zerosetKfR R1 (by linarith) f := by
    exact (h_finite_zeros.mem_toFinset).mp hρ
  have hρ_ne_zero : ρ ≠ 0 := by
    intro h_eq
    -- ρ = 0 would mean f(0) = 0, but h_f_zero says f(0) = 1
    have : f 0 = 0 := by simpa [h_eq] using hρ_mem.2
    exact (zero_ne_one : (0 : ℂ) ≠ 1) (this.symm.trans h_f_zero)
  have hR_ne_zero : R ≠ 0 := ne_of_gt (hR1_pos.trans hR1_lt_R)
  have h_denom_ne_zero : (R : ℂ) - (star ρ) * z / R ≠ 0 := by
    -- This follows from blaschke_num_diff_nonzero
    have hz_ball : z ∈ Metric.closedBall (0 : ℂ) R := by
      have hle : R1 < R := hR1_lt_R
      apply Metric.closedBall_subset_closedBall (le_of_lt hle)
      exact hz.1
    have h := blaschke_num_diff_nonzero hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros ρ hρ_mem z hz_ball
    exact h.1
  have h_num := logDeriv_numerator hR_ne_zero hρ_ne_zero h_denom_ne_zero
  -- Evaluate logDeriv(z - ρ) using logDeriv_denominator
  have hz_ne_rho : z ≠ ρ := by
    intro h_eq
    exact hz.2 (by simpa [h_eq] using hρ_mem)
  have h_den := logDeriv_denominator hz_ne_rho
  -- Substitute the results back
  rw [h_div, h_num, h_den]

-- Lemma 34: Lf_deriv_step3
lemma Lf_deriv_step3 :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z + ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat * (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) := by
  intro z hz
  -- Assuming Lf_deriv_step2 is also corrected to remove B
  rw [Lf_deriv_step2 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
  congr 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  congr 1
  exact logDeriv_Blaschke_is_diff_frac hR1_pos hR1_lt_R hR_lt_1 h_f_zero h_f_analytic h_finite_zeros ρ hρ z (in_r_minus_kf hr_pos hr_lt_R1 _ hz)

-- Lemma 35: sum_of_diff
lemma sum_of_diff {K : Finset ℂ} {a b : ℂ → ℂ} :
    ∑ ρ ∈ K, (a ρ - b ρ) = ∑ ρ ∈ K, a ρ - ∑ ρ ∈ K, b ρ := by
  simp [Finset.sum_sub_distrib]

-- Lemma 36: sum_rearranged
lemma sum_rearranged {R R1 : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat *
                                    (1 / (z - R^2 / (star ρ)) - 1 / (z - ρ)) =
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) := by
  intro z hz
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext ρ
  rw [mul_sub, mul_one_div, mul_one_div]

-- Lemma 37: Lf_deriv_final_formula
lemma Lf_deriv_final_formula :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z =
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) +
                      ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
  -- Apply Lf_deriv_step3 with the corrected, simpler signature
  rw [Lf_deriv_step3 hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz]
  -- Apply sum_rearranged with a simpler signature
  rw [sum_rearranged hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz]
  -- Rearrange terms
  ring

-- Lemma 38: rearrange_Lf_deriv
lemma rearrange_Lf_deriv :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
    deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ) =
    deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z -
    ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)) := by
  intro z hz
  -- The call to Lf_deriv_final_formula is now simpler as it no longer needs hB
  have h_final := Lf_deriv_final_formula hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz
  rw [h_final]
  ring

-- Lemma 39: triangle_ineq_sum
lemma triangle_ineq_sum {w₁ w₂ : ℂ} :
    ‖w₁ - w₂‖ ≤ ‖w₁‖ + ‖w₂‖ := by
  have h : w₁ - w₂ = w₁ + (-w₂) := sub_eq_add_neg w₁ w₂
  rw [h]
  have h₁ : ‖w₁ + (-w₂)‖ ≤ ‖w₁‖ + ‖-w₂‖ := norm_add_le w₁ (-w₂)
  have h₂ : ‖-w₂‖ = ‖w₂‖ := norm_neg w₂
  rw [h₂] at h₁; exact h₁

-- Lemma 40: target_inequality_setup
lemma target_inequality_setup :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f,
  ‖deriv f z / f z - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
  ‖deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z‖ +
  ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ := by
  intro z hz
  -- The call to rearrange_Lf_deriv is now corrected and simplified.
  -- The `hB` argument that caused the error has been removed.
  have hrearr := rearrange_Lf_deriv hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz

  -- The rest of the proof is a direct application of the triangle inequality.
  -- We want to show ‖A‖ ≤ ‖B‖ + ‖C‖, where hrearr gives A = B - C.
  rw [hrearr]
  exact norm_sub_le _ _
-- Additional helper lemmas needed for the bounds

-- Additional bound lemmas

lemma conj_norm_eq_norm (z : ℂ) : ‖star z‖ = ‖z‖ := by
  simp [Complex.star_def]

lemma norm_div_eq (a b : ℂ) (hb : b ≠ 0) : ‖a / b‖ = ‖a‖ / ‖b‖ := by
  calc
    ‖a / b‖ = ‖a * b⁻¹‖ := by simp [div_eq_mul_inv]
    _ = ‖a‖ * ‖b⁻¹‖ := norm_mul _ _
    _ = ‖a‖ * ‖b‖⁻¹ := by simp [norm_inv]
    _ = ‖a‖ / ‖b‖ := by simp [div_eq_mul_inv]

lemma norm_Rsq_div_conj (R : ℝ) (ρ : ℂ) (hρ : ρ ≠ 0) : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ := by
  have hb : star ρ ≠ 0 := by
    intro h
    have h' := congrArg star h
    -- star (star ρ) = 0, hence ρ = 0
    have : ρ = 0 := by simpa [star_star] using h'
    exact hρ this
  have hnormR : ‖(R^2 : ℂ)‖ = (R^2 : ℝ) := by
    have h := (RCLike.norm_ofReal (K:=ℂ) (R^2))
    simp [abs_of_nonneg (sq_nonneg R)]
  calc
    ‖((R^2 : ℂ) / (star ρ))‖
        = ‖(R^2 : ℂ)‖ / ‖star ρ‖ := norm_div_eq _ _ hb
    _ = (R^2 : ℝ) / ‖ρ‖ := by
      simp [hnormR, conj_norm_eq_norm]

lemma zerosetKfR_subset_closedBall {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ} :
  zerosetKfR R1 hR1 f ⊆ Metric.closedBall (0 : ℂ) R1 := by
  intro ρ hρ
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  exact hmem.left

lemma mem_zerosetKfR_ne_zero_of_f0_eq_one {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ}
  (hf0 : f 0 = 1) {ρ : ℂ} (hρ : ρ ∈ zerosetKfR R1 hR1 f) : ρ ≠ 0 := by
  intro hρ0
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 ∧ f ρ = 0 := by
    simpa [zerosetKfR] using hρ
  have hzero : f 0 = 0 := by simpa [hρ0] using hmem.right
  have h10 : (1 : ℂ) ≠ 0 := one_ne_zero
  exact h10 (by simp [hf0] at hzero)

lemma norm_sub_ge_norm_sub (x y : ℂ) : ‖x - y‖ ≥ ‖y‖ - ‖x‖ := by
  have htri : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
    simpa [sub_eq_add_neg, add_comm] using norm_add_le (y - x) x
  have h' : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := (sub_le_iff_le_add).mpr htri
  have hsymm : ‖y - x‖ = ‖x - y‖ := by
    simpa [sub_eq_add_neg, add_comm] using (norm_neg (x - y))
  simpa [hsymm] using h'


lemma mem_zerosetKfR_norm_le {R1 : ℝ} (hR1 : 0 < R1) {f : ℂ → ℂ} {ρ : ℂ}
  (hρ : ρ ∈ zerosetKfR R1 hR1 f) : ‖ρ‖ ≤ R1 := by
  have hmem : ρ ∈ Metric.closedBall (0 : ℂ) R1 :=
    (zerosetKfR_subset_closedBall (R1 := R1) hR1 (f := f)) hρ
  have hdist : dist ρ (0 : ℂ) ≤ R1 := by
    simpa [Metric.mem_closedBall] using hmem
  simpa [dist_eq_norm, sub_zero] using hdist

lemma lem_sum_bound_step2 {R R1: ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
      (∑ ρ ∈ h_finite_zeros.toFinset,
          ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ (1/(R^2/R1 - R1)) *
          (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) := by
  classical
  intro z hz
  rcases hz with ⟨hzball, _hznotin⟩
  have hz_norm : ‖z‖ ≤ R1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hzball
  -- Define the index finset
  set S := h_finite_zeros.toFinset
  have hS_spec : ∀ {ρ : ℂ}, ρ ∈ S → ρ ∈ zerosetKfR R1 (by linarith) f := by
    intro ρ hρ
    have hiff := (Set.Finite.mem_toFinset (hs := h_finite_zeros) : ρ ∈ S ↔ ρ ∈ zerosetKfR R1 (by linarith) f)
    exact (Iff.mp hiff) hρ
  -- Termwise bound and then sum
  have hsum_le :
      (∑ ρ ∈ S, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - (R^2 : ℂ) / (star ρ)‖)
        ≤ ∑ ρ ∈ S, (1/(R^2/R1 - R1)) * ((analyticOrderAt f ρ).toNat : ℝ) := by
    refine Finset.sum_le_sum ?termwise
    intro ρ hρS
    have hρmem : ρ ∈ zerosetKfR R1 (by linarith) f := hS_spec hρS
    have hρ_ne : ρ ≠ 0 :=
      mem_zerosetKfR_ne_zero_of_f0_eq_one (R1 := R1) (hR1 := by linarith)
        (f := f) h_f_zero hρmem
    have hρ_norm : ‖ρ‖ ≤ R1 := mem_zerosetKfR_norm_le (R1 := R1)
      (hR1 := by linarith) (f := f) hρmem
    have hpt : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1/(R^2/R1 - R1) := by
      -- Use triangle inequality and norms
      have h_Rsq_norm : ‖((R^2 : ℂ) / (star ρ))‖ = (R^2 : ℝ) / ‖ρ‖ :=
        norm_Rsq_div_conj R ρ hρ_ne
      have h_lower_bound : ‖z - (R^2 : ℂ) / (star ρ)‖ ≥ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ :=
        norm_sub_ge_norm_sub z ((R^2 : ℂ) / (star ρ))
      -- Since ‖ρ‖ ≤ R1 and ‖ρ‖ > 0, we have ‖((R^2 : ℂ) / (star ρ))‖ ≥ R^2/R1
      have hρ_pos : 0 < ‖ρ‖ := by
        simpa [norm_pos_iff] using hρ_ne
      have h_Rsq_bound : R^2/R1 ≤ ‖((R^2 : ℂ) / (star ρ))‖ := by
        rw [h_Rsq_norm]
        exact div_le_div_of_nonneg_left (sq_nonneg R) hρ_pos hρ_norm
      have h_combined : R^2/R1 - R1 ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        calc R^2/R1 - R1
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - R1 := by linarith [h_Rsq_bound]
        _ ≤ ‖((R^2 : ℂ) / (star ρ))‖ - ‖z‖ := by linarith [hz_norm]
        _ ≤ ‖z - (R^2 : ℂ) / (star ρ)‖ := h_lower_bound
      have h_pos_denom : 0 < R^2/R1 - R1 := by
        have h_R_pos : 0 < R := by linarith [hR1_pos, hR1_lt_R]
        have h_Rsq_pos : 0 < R^2 := sq_pos_of_pos h_R_pos
        calc R^2/R1 - R1
        _ = (R^2 - R1*R1)/R1 := by field_simp
        _ = (R - R1)*(R + R1)/R1 := by ring
        _ > 0 := by
          apply div_pos
          · apply mul_pos
            · linarith [hR1_lt_R]
            · linarith [hR1_pos, hR1_lt_R]
          · exact hR1_pos
      have h_pos_norm : 0 < ‖z - (R^2 : ℂ) / (star ρ)‖ := by
        apply lt_of_lt_of_le h_pos_denom h_combined
      -- Use the basic inequality: if 0 < a ≤ b then 1/b ≤ 1/a
      have h_reciprocal : 1 / ‖z - (R^2 : ℂ) / (star ρ)‖ ≤ 1 / (R^2/R1 - R1) := by
        apply div_le_div_of_nonneg_left
        · norm_num
        · exact h_pos_denom
        · exact h_combined
      exact h_reciprocal
    have hmnonneg : 0 ≤ ((analyticOrderAt f ρ).toNat : ℝ) := by
      exact_mod_cast (Nat.zero_le (analyticOrderAt f ρ).toNat)
    have hmul := mul_le_mul_of_nonneg_left hpt hmnonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  -- pull out the constant on the RHS sum
  rw [← Finset.mul_sum] at hsum_le
  exact hsum_le

-- 1/((R^2/R_1 - R_1) log(R/R_1))

lemma sq_div_sub_pos (a b : ℝ) (ha_pos : 0 < a) (hab : a < b) : 0 < b^2/a - a := by
  -- Convert the inequality to a < b^2/a
  rw [sub_pos]
  -- Use lt_div_iff₀ to convert a < b^2/a to a * a < b^2
  rw [lt_div_iff₀ ha_pos]
  -- Rewrite a * a as a^2
  rw [← pow_two]
  -- Now we need a^2 < b^2, which follows from a < b for positive numbers
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  apply pow_lt_pow_left₀ hab ha_nonneg
  norm_num --lem_square_inequality_strict ha_pos hab

lemma final_sum_bound {R R1 B : ℝ} {f : ℂ → ℂ}
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (hB : 1 < B)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f,
    ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ ≤
    1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
  intro z hz
  -- Step 1: Use triangle inequality (norm_sum_le)
  have h_norm_bound := norm_sum_le h_finite_zeros.toFinset (fun ρ => (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ)))

  -- Step 2: Simplify norm of each term
  have h_sum_eq : ∑ ρ ∈ h_finite_zeros.toFinset, ‖(analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ =
    ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - R^2 / (star ρ)‖ := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [norm_div, Complex.norm_natCast]

  -- Step 3: Apply lem_sum_bound_step2 (first lemma from informal proof)
  have h_step2 := lem_sum_bound_step2 hR1_pos hR1_lt_R hR_lt_1 h_f_analytic h_f_zero h_finite_zeros z hz

  -- Step 4: Apply lem_sum_m_rho_bound
  have h_f_nonzero : f 0 ≠ 0 := by rw [h_f_zero]; norm_num
  have h_f_bounded_alt : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B := by
    intro w hw
    exact h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw))
  -- Build a uniform existence statement for all σ
  have h_exists : ∀ σ : ℂ, ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g σ ∧ g σ ≠ 0 ∧
      (σ ∈ zerosetKfR R1 (by linarith) f →
        ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * g z) := by
    intro σ
    by_cases hσ : σ ∈ zerosetKfR R1 (by linarith) f
    · -- σ is a zero: use lem_analytic_zero_factor
      have hex := lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero σ hσ
      obtain ⟨g, hg_at, hg_ne, h_eq⟩ := hex
      exact ⟨g, hg_at, hg_ne, fun _ => h_eq⟩
    · -- σ is not a zero: use constant function 1
      refine ⟨fun _ => 1, ?_, ?_, ?_⟩
      · exact analyticAt_const
      · norm_num
      · intro h_contra
        contradiction
  -- Use classical choice to extract the function
  let h_σ : ℂ → (ℂ → ℂ) := fun σ => Classical.choose (h_exists σ)
  have h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z := by
    intro σ hσ
    have spec := Classical.choose_spec (h_exists σ)
    exact ⟨spec.1, spec.2.1, spec.2.2 hσ⟩
  have h_sum_bound := lem_sum_m_rho_bound B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero h_f_zero h_finite_zeros h_σ h_f_bounded_alt h_σ_spec

  -- Step 5: Establish needed positivity properties
  have h_pos : 0 < R^2/R1 - R1 := sq_div_sub_pos R1 R hR1_pos hR1_lt_R
  have h_ratio_gt_one : 1 < R/R1 := by
    rw [one_lt_div_iff]
    left
    exact ⟨hR1_pos, hR1_lt_R⟩
  have h_log_pos : 0 < Real.log (R/R1) := Real.log_pos h_ratio_gt_one

  calc ‖∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖
    ≤ ∑ ρ ∈ h_finite_zeros.toFinset, ‖(analyticOrderAt f ρ).toNat / (z - R^2 / (star ρ))‖ := h_norm_bound
    _ = ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ) / ‖z - R^2 / (star ρ)‖ := h_sum_eq
    _ ≤ (1/(R^2/R1 - R1)) * (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) := h_step2
    _ ≤ (1/(R^2/R1 - R1)) * ((1/Real.log (R/R1)) * Real.log B) := by
              apply mul_le_mul_of_nonneg_left h_sum_bound (div_nonneg zero_le_one (le_of_lt h_pos))
    _ = 1/((R^2/R1 - R1) * Real.log (R/R1)) * Real.log B := by
      field_simp [ne_of_gt h_pos, ne_of_gt h_log_pos]

-- Now, we can fix the `final_inequality` lemma.
lemma final_inequality
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic :
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ_spec :
      ∀ σ ∈ zerosetKfR R1 (by linarith) f,
        AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
        ∀ᶠ z in nhds σ,
          f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 (by linarith) f,

        ‖(deriv f z / f z
          - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ))‖
      ≤
      16 * r^2 / ((r - r1)^3) * Real.log B
        + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
  intro z hz

  -- Establish missing positive hypotheses from the parameter constraints
  have hr_pos : 0 < r := by linarith [hr1pos, hr1_lt_r]
  have hR1_pos : 0 < R1 := by linarith [hr_pos, hr_lt_R1]

  -- Lift z from r1-ball to r-ball (needed for target_inequality_setup)
  have hz_in_r : z ∈ Metric.closedBall (0 : ℂ) r \ zerosetKfR R1 (by linarith) f := by
    constructor
    · apply Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_r)
      exact hz.1
    · exact hz.2

  -- Apply target_inequality_setup (from informal proof)
  have hineq :=
    target_inequality_setup hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec z hz_in_r

  -- Lift z from r1-ball to R1-ball (needed for final_sum_bound)
  have hz_in_R1 : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f := by
    constructor
    · apply Metric.closedBall_subset_closedBall
      exact le_of_lt (lt_trans hr1_lt_r hr_lt_R1)
      exact hz.1
    · exact hz.2

  -- Apply final_sum_bound (from informal proof)
  have hsum :=
    final_sum_bound hR1_pos hR1_lt_R hR_lt_1 hB h_f_analytic h_f_zero h_finite_zeros h_f_bounded z hz_in_R1

  -- Apply apply_BC_to_Lf (from informal proof)
  have hz_le_r1 : ‖z‖ ≤ r1 := by simpa [Metric.mem_closedBall, dist_eq_norm] using hz.1

  -- Convert ‖z‖ ≤ r1 to norm z ≤ r1 (they are definitionally equal)
  have hz_abs : ‖z‖ ≤ r1 := hz_le_r1

  have h_BC := apply_BC_to_Lf
    (B := B) (r1 := r1) (r := r) (R := R) (R1 := R1)
    (hB := hB) (hr1_pos := hr1pos) (hr1_lt_r := hr1_lt_r) (hr_lt_R1 := hr_lt_R1)
    (hR1_pos := hR1_pos) (hR1_lt_R := hR1_lt_R) (hR_lt_1 := hR_lt_1)
    (f := f) (h_f_analytic := h_f_analytic) (h_f_zero := h_f_zero)
    (h_finite_zeros := h_finite_zeros) (h_σ := h_σ) (h_σ_spec := h_σ_spec)
    (h_f_bound := fun w hw => h_f_bounded w (Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hw)))
    z hz_abs

  -- Convert norm to norm and rearrange the bound
  have hLf : ‖deriv (Lf hr_pos hr_lt_R1 hR1_lt_R hR_lt_1 hR1_pos h_f_analytic h_f_zero h_finite_zeros h_σ_spec) z‖ ≤
             16 * r^2 / ((r - r1)^3) * Real.log B := by
    -- h_BC gives: norm (...) ≤ (16 * Real.log B * r^2) / (r - r1)^3
    -- We need: ‖...‖ ≤ 16 * r^2 / ((r - r1)^3) * Real.log B
    -- norm and ‖·‖ are definitionally equal
    convert h_BC using 1
    -- Rearrange: (16 * Real.log B * r^2) / (r - r1)^3 = 16 * r^2 / ((r - r1)^3) * Real.log B
    ring

  exact le_trans hineq (add_le_add hLf hsum)


-- Lemma 43: final_ineq1
lemma final_ineq1
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_zero : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_f_bounded : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖f z‖ ≤ B) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1 \ zerosetKfR R1 (by linarith) f,
    ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset,
                 (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
    (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log B := by
  intro z hz
  -- Get the bound with separate terms from final_inequality
  have h_bound : ‖(deriv f z / f z) - ∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat / (z - ρ)‖ ≤
      16 * r^2 / ((r - r1)^3) * Real.log B + 1 / ((R^2 / R1 - R1) * Real.log (R / R1)) * Real.log B := by
    apply final_inequality <;> assumption
  -- Factor out Real.log B using right distributivity: a * c + b * c = (a + b) * c
  rw [← add_mul] at h_bound
  exact h_bound

end AnalyticZeroCounting
