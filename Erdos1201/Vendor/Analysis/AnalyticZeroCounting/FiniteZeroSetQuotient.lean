module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.Normed.Module.Connected
public import Erdos1201.Vendor.Analysis.DiskAnalyticBounds.AnalyticLogConstruction

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open DiskAnalyticBounds

/-!
Zero-counting apparatus for an analytic function on the unit disk: the
finite zero set of `f` inside a closed sub-disk of radius `R`, the identity
theorem argument showing that a nonzero `f` can only have finitely many
zeros there, multiplicity facts (`analyticOrderAt` is finite and `≥ 1` at
each zero), and the "deflated" quotient `Cf` obtained by dividing `f` by
the product of `(z - ρ)^{m_ρ}` over its zero set (locally patched across
each zero via a nonvanishing analytic factor so the quotient stays
analytic there).
-/

public section

namespace AnalyticZeroCounting

lemma DRinD1 (R : ℝ) (hR : 0 < R) (hR' : R < 1) :
    Metric.closedBall (0 : ℂ) R ⊆ Metric.ball (0 : ℂ) 1 := by
  exact Metric.closedBall_subset_ball hR'
@[expose] def zerosetKfR (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0}
lemma lemKinDR (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ Metric.closedBall (0 : ℂ) R := by
  intro ρ hρ
  -- hρ : ρ ∈ zerosetKfR R hR f
  -- By definition of zerosetKfR, this means ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0
  rw [zerosetKfR] at hρ
  -- Now hρ : ρ ∈ {ρ : ℂ | ρ ∈ Metric.closedBall (0 : ℂ) R ∧ f ρ = 0}
  exact hρ.1
lemma lemKRinK1 (R : ℝ) (hR : 0 < R) (hR' : R < 1) (f : ℂ → ℂ) :
    zerosetKfR R hR f ⊆ {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} := by
  intro ρ hρ
  simp only [zerosetKfR, Set.mem_ofPred_eq] at hρ ⊢
  constructor
  · exact DRinD1 R hR hR' hρ.1
  · exact hρ.2

lemma lem_bolzano_weierstrass {D : Set ℂ} (hD : IsCompact D) {Z : Set ℂ} (hZ_inf : Z.Infinite) (hZ_sub_D : Z ⊆ D) :
    ∃ ρ₀ ∈ D, AccPt ρ₀ (Filter.principal Z) :=
  Set.Infinite.exists_accPt_of_subset_isCompact hZ_inf hD hZ_sub_D
lemma lem_zeros_have_limit_point (R : ℝ) (hR : 0 < R) (f : ℂ → ℂ) (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f)) := by
  apply lem_bolzano_weierstrass
  · -- Show IsCompact (Metric.closedBall (0 : ℂ) R)
    exact Metric.isCompact_of_isClosed_isBounded Metric.isClosed_closedBall Metric.isBounded_closedBall
  · exact h_Kf_inf
  · exact lemKinDR R hR f

open Filter Metric Set Bornology Function

lemma lem_identity_theorem (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  -- The open ball is a subset of the closed ball
  have h_subset : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1 := Metric.ball_subset_closedBall
  -- So f is analytic on a neighborhood of the open ball
  have hf_open : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := AnalyticOnNhd.mono hf h_subset
  -- The open ball is preconnected (since it's connected)
  have h_conn : IsConnected (Metric.ball (0 : ℂ) 1) := isConnected_ball (by norm_num : (0 : ℝ) < 1)
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) := h_conn.isPreconnected
  -- Convert accumulation point to closure membership
  have h_zeros_subset : {ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0} ⊆ {z | f z = 0} := by
    intro z hz
    exact hz.2
  -- From AccPt over the smaller set, get AccPt over the zero set using filter monotonicity
  have h_acc_zero : AccPt ρ₀ (Filter.principal ({z | f z = 0})) := by
    exact AccPt.mono h_acc (principal_mono.2 h_zeros_subset)
  -- AccPt principal is equivalent to ClusterPt on the punctured set; then use closure equivalence
  have h_closure : ρ₀ ∈ closure ({z | f z = 0} \ {ρ₀}) := by
    -- accPt_principal_iff_clusterPt : AccPt x (𝓟 C) ↔ ClusterPt x (𝓟 (C \ {x}))
    have h_cluster : ClusterPt ρ₀ (Filter.principal ({z | f z = 0} \ {ρ₀})) :=
      (accPt_principal_iff_clusterPt).mp h_acc_zero
    exact (mem_closure_iff_clusterPt).2 h_cluster
  -- Apply the identity theorem
  exact AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure hf_open h_preconn hρ₀_in_D1 h_closure
lemma lem_identity_theoremR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (ρ₀ : ℂ) (hρ₀_in_DR : ρ₀ ∈ Metric.closedBall (0 : ℂ) R)
    (h_acc : AccPt ρ₀ (Filter.principal ({ρ : ℂ | ρ ∈ Metric.ball (0 : ℂ) 1 ∧ f ρ = 0}))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have hρ₀_in_D1 : ρ₀ ∈ Metric.ball (0 : ℂ) 1 := DRinD1 R hR hR' hρ₀_in_DR
  exact lem_identity_theorem f hf ρ₀ hρ₀_in_D1 h_acc
lemma lem_identity_theoremKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_rho0 : ∃ ρ₀ ∈ Metric.closedBall (0 : ℂ) R, AccPt ρ₀ (Filter.principal (zerosetKfR R hR f))) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  -- Extract the existence of ρ₀
  obtain ⟨ρ₀, hρ₀_in_R, h_acc⟩ := h_exists_rho0
  -- Apply lem_identity_theoremR
  apply lem_identity_theoremR R hR hR' f hf ρ₀ hρ₀_in_R
  -- Convert the accumulation point using monotonicity and lemKRinK1
  exact AccPt.mono h_acc (principal_mono.2 (lemKRinK1 R hR hR' f))
lemma lem_identity_infiniteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_Kf_inf : Set.Infinite (zerosetKfR R hR f)) :
    EqOn f 0 (Metric.ball (0 : ℂ) 1) := by
  have h_exists_rho0 := lem_zeros_have_limit_point R hR f h_Kf_inf
  exact lem_identity_theoremKR R hR hR' f hf h_exists_rho0
lemma lem_Contra_finiteKR (R : ℝ) (hR : 0 < R) (hR' : R < 1)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (h_exists_nonzero : ∃ z ∈ Metric.ball (0 : ℂ) 1, f z ≠ 0) :
    Set.Finite (zerosetKfR R hR f) := by
  -- Use contrapositive of lem_identity_infiniteKR
  by_contra h_not_finite
  -- h_not_finite: ¬Set.Finite (zerosetKfR R hR f)
  -- This is equivalent to Set.Infinite (zerosetKfR R hR f) by definition
  have h_Kf_inf : Set.Infinite (zerosetKfR R hR f) := h_not_finite
  -- Apply lem_identity_infiniteKR
  have h_eq_zero := lem_identity_infiniteKR R hR hR' f hf h_Kf_inf
  -- h_eq_zero : EqOn f 0 (Metric.ball (0 : ℂ) 1)
  -- But we have h_exists_nonzero which contradicts this
  obtain ⟨z, hz_in_ball, hz_nonzero⟩ := h_exists_nonzero
  have h_f_z_zero : f z = 0 := h_eq_zero hz_in_ball
  exact hz_nonzero h_f_z_zero

open Classical

lemma lem_frho_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    f ρ = 0 := h_rho_in_KfR1.2

lemma lem_m_rho_is_nat (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≠ ⊤ := by
  intro ρ h_rho_in_KfR1
  -- ρ lies in the closed ball of radius R1
  have hρ_closed_R1 : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
  -- R1 < R and R < 1 implies R1 < 1
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
  -- Hence ρ ∈ ball 0 1
  have hρ_ball1 : ρ ∈ Metric.ball (0 : ℂ) 1 := by
    have hdist_le : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_closed_R1)
    have hdist_lt : dist ρ (0 : ℂ) < 1 := by linarith
    simpa [Metric.mem_ball] using hdist_lt
  -- f is analytic at ρ
  have hf_at_ρ : AnalyticAt ℂ f ρ := by
    -- ρ ∈ closedBall 0 1 since R1 < 1
    have hsubset : Metric.closedBall (0 : ℂ) R1 ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)
    have hρ_closed1 : ρ ∈ Metric.closedBall (0 : ℂ) 1 := hsubset hρ_closed_R1
    exact h_f_analytic ρ hρ_closed1
  -- Suppose, for contradiction, that the order is ⊤
  by_contra htop
  -- From order = ⊤ we get that f is eventually zero near ρ
  have h_eventually_zero : ∀ᶠ z in nhds ρ, f z = 0 := by
    have h_equiv : (analyticOrderAt f ρ = ⊤ ↔ ∀ᶠ z in nhds ρ, f z = 0) := by
      simp [analyticOrderAt, hf_at_ρ]
    exact h_equiv.mp (by simpa using htop)
  -- f is analytic on a neighborhood of the unit ball
  have hf_on_ball : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      (Metric.ball_subset_closedBall : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1) hz
    exact h_f_analytic z hz'
  -- The unit ball is preconnected
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) :=
    (isConnected_ball (by exact (zero_lt_one : (0 : ℝ) < 1))).isPreconnected
  -- By identity principle, f = 0 on the unit ball
  have h_eqOn_zero : Set.EqOn f 0 (Metric.ball (0 : ℂ) 1) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf_on_ball h_preconn hρ_ball1
      h_eventually_zero
  -- Hence f 0 = 0, contradiction
  have h0_in_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball]
  have : f 0 = 0 := by
    have h := h_eqOn_zero h0_in_ball
    simpa [Pi.zero_apply] using h
  exact h_f_nonzero_at_zero this

lemma analyticOrderAt_ge_one_of_zero (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) (hz : f z = 0) (hfinite : analyticOrderAt f z ≠ ⊤) : analyticOrderAt f z ≥ 1 := by
  -- Show that analyticOrderAt f z ≠ 0 using the characterization
  have h_order_ne_zero : analyticOrderAt f z ≠ 0 := by
    intro h_order_zero
    -- If the order is 0, then f z ≠ 0 by the characterization
    have h_f_ne_zero : f z ≠ 0 := by
      rw [← AnalyticAt.analyticOrderAt_eq_zero hf]
      exact h_order_zero
    -- This contradicts hz : f z = 0
    exact h_f_ne_zero hz
  -- Since analyticOrderAt f z is finite (≠ ⊤) and ≠ 0, it must be ≥ 1
  exact Order.one_le_iff_ne_zero.mpr h_order_ne_zero


lemma lem_m_rho_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≥ 1 := by
  intro ρ h_rho_in_KfR1
  -- Use lem_frho_zero as mentioned in informal proof
  have h_f_rho_zero : f ρ = 0 := lem_frho_zero R R1 hR1_pos hR1_lt_R f h_f_analytic ρ h_rho_in_KfR1
  -- Use lem_m_rho_is_nat as mentioned in informal proof
  have h_order_finite : analyticOrderAt f ρ ≠ ⊤ := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 ρ h_rho_in_KfR1
  -- f is analytic at ρ
  have h_f_analytic_at_rho : AnalyticAt ℂ f ρ := by
    apply h_f_analytic
    -- With R < 1 and R1 < R, we have R1 < 1
    have h_R1_lt_1 : R1 < 1 := by linarith
    have h_rho_in_R1 : ρ ∈ Metric.closedBall 0 R1 := h_rho_in_KfR1.1
    exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) h_rho_in_R1
  -- Apply the helper lemma (combining results from both mentioned lemmas)
  exact analyticOrderAt_ge_one_of_zero f ρ h_f_analytic_at_rho h_f_rho_zero h_order_finite

/-! ### The quotient `Cf` (no core wrapper) -/

/-- The “deflated” quotient: divide `f` by the product of `(z-ρ)^{m_ρ}`, and at a zero `z=σ`
    use the local factor function `h_σ σ` in the numerator (so the expression extends analytically). -/
@[expose] noncomputable def Cf
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))  -- for each σ in the zero set, a local factor function
    (z : ℂ) : ℂ :=
  if hz : z ∈ zerosetKfR R1 (by linarith) f then
    h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase z), (z - ρ) ^ (analyticOrderAt f ρ).toNat
  else
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat


lemma lem_denomAnalAt (S : Finset ℂ) (n : ℂ → ℕ)
    (hn_pos : ∀ s ∈ S, 0 < n s) (w : ℂ) (hw : w ∉ S) :
    AnalyticAt ℂ (fun z => ∏ s ∈ S, (z - s) ^ (n s)) w ∧
    (∏ s ∈ S, (w - s) ^ (n s)) ≠ 0 := by
  constructor
  · -- First part: AnalyticAt
    -- Use Finset.analyticAt_fun_prod
    let f : ℂ → ℂ → ℂ := fun s z => (z - s) ^ (n s)
    have h_each_analytic : ∀ s ∈ S, AnalyticAt ℂ (f s) w := by
      intro s hs
      simp only [f]
      -- Need to show AnalyticAt ℂ (fun z => (z - s) ^ (n s)) w
      have h_sub : AnalyticAt ℂ (fun z => z - s) w := by
        exact AnalyticAt.sub analyticAt_id analyticAt_const
      -- Apply pow with the natural number n s
      exact h_sub.pow (n s)
    have h_prod := Finset.analyticAt_fun_prod S h_each_analytic
    exact h_prod
  · -- Second part: nonzero product
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    apply pow_ne_zero
    -- Need w - s ≠ 0
    intro h_eq
    -- Use sub_eq_zero: a - b = 0 ↔ a = b
    have h_w_eq_s : w = s := by
      rwa [← sub_eq_zero]
    -- This contradicts hw : w ∉ S since s ∈ S
    rw [h_w_eq_s] at hw
    exact hw hs

lemma lem_ratioAnalAt (w : ℂ) (R R1 : ℝ) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h w)
    (S : Finset ℂ) (hS : ↑S ⊆ Metric.closedBall (0 : ℂ) R1) (n : ℂ → ℕ)
    (hn_pos : ∀ s ∈ S, 0 < n s)
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1 \ ↑S) :
    AnalyticAt ℂ (fun z => h z / ∏ s ∈ S, (z - s) ^ (n s)) w := by
  classical
  -- Denominator is analytic at w and nonzero at w
  have hden := lem_denomAnalAt (S := S) (n := n)
      (hn_pos := hn_pos) (w := w)
      (hw := by simpa using hw.2)
  -- Apply the division rule for analytic functions
  exact AnalyticAt.div hh hden.1 hden.2

lemma lem_analytic_zero_factor (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ) (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∃ h_σ : ℂ → ℂ, AnalyticAt ℂ h_σ σ ∧ h_σ σ ≠ 0 ∧
    ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ z := by
  classical
  -- f is analytic at σ
  have hσ_closed_R1 : σ ∈ Metric.closedBall (0 : ℂ) R1 := hσ.1
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
  have hσ_closed1 : σ ∈ Metric.closedBall (0 : ℂ) 1 :=
    (Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)) hσ_closed_R1
  have hfσ : AnalyticAt ℂ f σ := h_f_analytic σ hσ_closed1
  -- the order at σ is finite
  have h_order_finite : analyticOrderAt f σ ≠ ⊤ :=
    lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 σ hσ
  -- use the characterization of finite order to get the factorization
  rcases (hfσ.analyticOrderAt_ne_top).mp h_order_finite with ⟨g, hgσ, hgσ_ne, h_eq⟩
  -- turn scalar multiplication into multiplication on ℂ and rewrite the exponent
  have h_eq' : ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * g z := by
    refine h_eq.mono ?_
    intro z hz
    simpa [smul_eq_mul, analyticOrderNatAt] using hz
  exact ⟨g, hgσ, hgσ_ne, h_eq'⟩

/-! ### Cf lemmas (renamed to use `Cf` directly) -/

lemma lem_Cf_analytic_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) z := by

  -- Apply lem_ratioAnalAt to get analyticity of the ratio function
  have h_ratio_analytic : AnalyticAt ℂ (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) z := by
    apply lem_ratioAnalAt z R R1 hR1_lt_R hR_lt_1 f

    -- f is analytic at z
    · apply h_f_analytic
      exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1

    -- The finite zero set is contained in closedBall 0 R1
    · intro ρ hρ
      have h_mem : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
      exact h_mem.1

    -- All orders are positive
    · intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hs
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros

      rcases h_cases : analyticOrderAt f s with _ | n
      · -- Case: order is ∞
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      · -- Case: order is finite n ≥ 1
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp [h_cases]
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1)

    -- z is in closedBall 0 1 but not in the zero set
    · constructor
      · exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1
      · -- Show z ∉ ↑h_finite_zeros.toFinset
        intro h_z_in_finset
        have h_z_in_zeros : z ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp h_z_in_finset
        exact hz.2 h_z_in_zeros

  -- Show that the ratio function equals Cf in a neighborhood of z
  have h_eventually_eq : (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds z]
    (fun w => Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w) := by
    -- Since the zero set is finite, its complement is open
    have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2
    have h_open : IsOpen (Set.compl (zerosetKfR R1 (by linarith) f)) := h_finite_zeros.isClosed.isOpen_compl
    apply Filter.eventually_of_mem (h_open.mem_nhds hz_not_in)
    intro w hw_not_in_compl
    -- Convert from membership in complement to non-membership
    have hw_not_in_zeros : w ∉ zerosetKfR R1 (by linarith) f := hw_not_in_compl
    -- Since w ∉ zerosetKfR R1, Cf w uses the else branch
    show f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat =
         Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w
    -- Apply the definition of Cf using dif_neg for dependent if-then-else
    rw [Cf, dite_eq_right hw_not_in_zeros]

  -- Transfer analyticity
  exact h_ratio_analytic.congr h_eventually_eq

lemma lem_Cf_at_sigma_onK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z = σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  refine Filter.Eventually.of_forall ?_
  intro z hz
  subst hz
  simp [Cf, hσ]


lemma lem_Cf_at_sigma_offK0
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z /
      ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  -- Get the factorization from h_σ_spec
  obtain ⟨h_σ_analytic, h_σ_ne_zero, h_f_eq⟩ := h_σ_spec σ hσ

  -- h_σ σ is continuous at σ and nonzero there, so it's eventually nonzero
  have h_σ_eventually_nonzero : ∀ᶠ z in nhds σ, h_σ σ z ≠ 0 := by
    have h_cont : ContinuousAt (h_σ σ) σ := h_σ_analytic.continuousAt
    exact h_cont.eventually_ne h_σ_ne_zero

  -- For z ≠ σ near σ, f z ≠ 0 due to the factorization
  have h_f_eventually_nonzero : ∀ᶠ z in nhds σ, z ≠ σ → f z ≠ 0 := by
    filter_upwards [h_f_eq, h_σ_eventually_nonzero] with z h_fz_eq h_σz_nonzero
    intro hz_ne
    rw [h_fz_eq]
    apply mul_ne_zero
    · apply pow_ne_zero
      exact sub_ne_zero.mpr hz_ne
    · exact h_σz_nonzero

  -- Therefore, z ≠ σ near σ implies z ∉ zerosetKfR
  have h_eventually_not_in_zeroset : ∀ᶠ z in nhds σ, z ≠ σ → z ∉ zerosetKfR R1 (by linarith) f := by
    filter_upwards [h_f_eventually_nonzero] with z h_fz_nonzero
    intro hz_ne hz_in_zeroset
    exact h_fz_nonzero hz_ne hz_in_zeroset.2

  -- Combine everything
  filter_upwards [h_f_eq, h_eventually_not_in_zeroset] with z h_fz_eq h_not_in_zeroset
  intro hz_ne
  -- Since z ≠ σ, we have z ∉ zerosetKfR, so Cf uses the else branch
  have hz_not_in_K : z ∉ zerosetKfR R1 (by linarith) f := h_not_in_zeroset hz_ne
  -- Unfold Cf using the else branch and substitute f z
  unfold Cf
  simp [hz_not_in_K, h_fz_eq]

lemma lem_prod_no_sigma1
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) (z : ℂ) :
    ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat =
    (z - σ) ^ (analyticOrderAt f σ).toNat *
    ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  classical
  have hmem : σ ∈ h_finite_zeros.toFinset :=
    (Set.Finite.mem_toFinset (hs := h_finite_zeros)).2 hσ
  simpa using
    (Finset.mul_prod_erase (s := h_finite_zeros.toFinset)
      (f := fun ρ => (z - ρ) ^ (analyticOrderAt f ρ).toNat) (a := σ) hmem).symm

lemma lem_prod_no_sigma2
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) (z : ℂ)
    (hz : z ∉ zerosetKfR R1 (by linarith) f) :
    (z - σ) ^ (analyticOrderAt f σ).toNat /
    ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat =
    1 / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  -- Use lem_prod_no_sigma1 to factorize the denominator
  have h_factor := @lem_prod_no_sigma1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ z
  rw [h_factor]

  -- Now we have (z - σ)^n / ((z - σ)^n * ∏ ρ ∈ erase σ, (z - ρ)^m_ρ)
  -- Convert a / (a * b) to (a / a) / b using div_mul_eq_div_div
  rw [div_mul_eq_div_div]

  -- Show (z - σ)^n ≠ 0
  have h_nonzero : (z - σ) ^ (analyticOrderAt f σ).toNat ≠ 0 := by
    apply pow_ne_zero
    intro h_eq
    -- If z - σ = 0, then z = σ, contradicting hz
    have h_z_eq_sigma : z = σ := sub_eq_zero.mp h_eq
    rw [h_z_eq_sigma] at hz
    exact hz hσ

  -- Use div_self to get (z - σ)^n / (z - σ)^n = 1
  rw [div_self h_nonzero, one_div]

lemma lem_Cf_at_sigma_offK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  -- Get the form from lem_Cf_at_sigma_offK0
  have h_cf_form := @lem_Cf_at_sigma_offK0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  filter_upwards [h_cf_form] with z h_cf_z
  intro hz_ne_sigma
  -- Apply the form from lem_Cf_at_sigma_offK0
  rw [h_cf_z hz_ne_sigma]
  -- Use product decomposition lem_prod_no_sigma1
  have h_prod_decomp := @lem_prod_no_sigma1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ z
  -- Substitute the full product with the decomposed form in the denominator
  rw [h_prod_decomp]
  -- Now apply mul_div_mul_left directly to cancel (z - σ)^m terms
  apply mul_div_mul_left
  -- Show (z - σ)^m ≠ 0
  apply pow_ne_zero
  exact sub_ne_zero.mpr hz_ne_sigma

lemma lem_Cf_at_sigma
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ,
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  -- Get the eventually statements for both cases
  have h_on := @lem_Cf_at_sigma_onK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
  have h_off := @lem_Cf_at_sigma_offK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
  -- Combine them using filter_upwards
  filter_upwards [h_on, h_off] with z hz_on hz_off
  by_cases h : z = σ
  · -- Case z = σ: use h_on, but need to convert h_σ z z to h_σ σ z
    have eq_result := hz_on h
    -- When z = σ, we have h_σ z z = h_σ σ σ and h_σ σ z = h_σ σ σ
    rw [h] at eq_result ⊢
    exact eq_result
  · -- Case z ≠ σ: directly use h_off
    exact hz_off h

lemma lem_h_ratio_anal
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f)
    (g : ℂ → ℂ) (hg_analytic : AnalyticAt ℂ g σ) :
    AnalyticAt ℂ
      (fun z => g z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (z - ρ) ^ (analyticOrderAt f ρ).toNat) σ := by
  -- Use lem_denomAnalAt to show the denominator is analytic and nonzero at σ
  have hden := lem_denomAnalAt (S := h_finite_zeros.toFinset.erase σ)
    (n := fun ρ => (analyticOrderAt f ρ).toNat)
    (hn_pos := by
      intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := by
        have h_mem_erase : s ∈ h_finite_zeros.toFinset.erase σ := hs
        have h_mem_orig : s ∈ h_finite_zeros.toFinset := Finset.mem_of_mem_erase h_mem_erase
        exact h_finite_zeros.mem_toFinset.mp h_mem_orig
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      rcases h_cases : analyticOrderAt f s with _ | n
      · -- Case: order is ∞
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      · -- Case: order is finite n ≥ 1
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp [h_cases]
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1))
    (w := σ)
    (hw := by
      simp [Finset.mem_erase])
  -- Apply the division rule for analytic functions
  exact AnalyticAt.div hg_analytic hden.1 hden.2

lemma lem_Cf_analytic_at_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) σ := by
  -- Get the eventual equality from lem_Cf_at_sigma with all explicit arguments
  have h_eventually_eq := @lem_Cf_at_sigma R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  -- Get analyticity of the ratio function from lem_h_ratio_anal
  obtain ⟨h_σ_analytic, _, _⟩ := h_σ_spec σ hσ
  have h_ratio_analytic := @lem_h_ratio_anal R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ (h_σ σ) h_σ_analytic

  -- Reverse the direction of the eventual equality
  have h_rev_eq : (fun z => h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds σ]
                  (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) := by
    filter_upwards [h_eventually_eq] with z h_z
    exact h_z.symm

  -- Use AnalyticAt.congr to transfer analyticity
  exact AnalyticAt.congr h_ratio_analytic h_rev_eq


lemma lem_f_nonzero_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {h_f_nonzero_at_zero : f 0 ≠ 0}
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    f z ≠ 0 := by
  exact fun h => hz.2 ⟨hz.1, h⟩

lemma lem_Cf_nonzero_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z ≠ 0 := by
  -- Since z ∉ zerosetKfR R1, Cf uses the else branch
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2

  -- Unfold Cf definition using the else branch
  have h_cf_eq : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp [hz_not_in]

  rw [h_cf_eq]

  -- Apply div_ne_zero: need numerator ≠ 0 and denominator ≠ 0
  apply div_ne_zero

  -- Numerator: f z ≠ 0 by lem_f_nonzero_off_K with explicit parameters
  · apply @lem_f_nonzero_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero z hz

  -- Denominator: product is nonzero
  · apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    -- Need (z - ρ) ^ (analyticOrderAt f ρ).toNat ≠ 0
    apply pow_ne_zero
    -- Need z - ρ ≠ 0, i.e., z ≠ ρ
    intro h_eq
    -- From h_eq : z - ρ = 0, we get z = ρ using sub_eq_zero
    have hz_eq_rho : z = ρ := by
      rwa [sub_eq_zero] at h_eq
    -- But ρ ∈ zerosetKfR R1 (from hρ) and z ∉ zerosetKfR R1 (from hz_not_in)
    have hρ_in : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
    rw [hz_eq_rho] at hz_not_in
    exact hz_not_in hρ_in

lemma lem_Cf_nonzero_on_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ σ ≠ 0 := by
  have hnum : h_σ σ σ ≠ 0 := (h_σ_spec σ hσ).2.1
  have hden :
      (∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (σ - ρ) ^ (analyticOrderAt f ρ).toNat) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro ρ hρmem
    have hρ_ne_σ : ρ ≠ σ := (Finset.mem_erase.mp hρmem).1
    have hσ_ne_ρ : σ ≠ ρ := hρ_ne_σ.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hσ_ne_ρ)
  have :
      h_σ σ σ /
          ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
            (σ - ρ) ^ (analyticOrderAt f ρ).toNat ≠
        0 := by
    exact div_ne_zero hnum hden
  simpa [Cf, hσ] using this

lemma lem_Cf_never_zero
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R1) :
    Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z ≠ 0 := by
  -- Split into cases: either z is in the zero set or not
  by_cases h : z ∈ zerosetKfR R1 (by linarith) f
  · -- Case: z ∈ zerosetKfR R1 (by linarith) f
    exact lem_Cf_nonzero_on_K h_finite_zeros h_σ h_σ_spec z h
  · -- Case: z ∉ zerosetKfR R1 (by linarith) f
    have hz_diff : z ∈ Metric.closedBall (0 : ℂ) R1 \ zerosetKfR R1 (by linarith) f := ⟨hz, h⟩
    exact lem_Cf_nonzero_off_K h_finite_zeros h_σ h_σ_spec z hz_diff

lemma factor_nonzero_outside_domain (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
    (ρ : ℂ) (hρ_bound : ‖ρ‖ ≤ R1) (hρ_ne_zero : ρ ≠ 0) (z : ℂ) (hz_in_R1 : ‖z‖ ≤ R1) :
    (R : ℂ) - star ρ * z / (R : ℂ) ≠ 0 := by
  -- Proof by contradiction
  intro h_eq_zero
  have hR_pos : 0 < R := by linarith

  -- From the equation being zero, we get star ρ * z = R²
  have h_mul_eq_R_sq : star ρ * z = (R : ℂ) ^ 2 := by
    have hR_ne_zero : (R : ℂ) ≠ 0 := by
      rw [Ne, ← norm_eq_zero]
      simp [Complex.norm_of_nonneg (le_of_lt hR_pos)]
      linarith
    -- From h_eq_zero: (R : ℂ) - star ρ * z / (R : ℂ) = 0
    -- Rearrange to: (R : ℂ) = star ρ * z / (R : ℂ)
    -- Multiply by (R : ℂ): (R : ℂ)² = star ρ * z
    rw [sub_eq_zero] at h_eq_zero
    rw [eq_div_iff_mul_eq hR_ne_zero] at h_eq_zero
    rw [← pow_two] at h_eq_zero
    exact h_eq_zero.symm

  -- Taking norms of both sides: ‖star ρ * z‖ = ‖(R : ℂ) ^ 2‖
  have h_norm_eq : ‖ρ‖ * ‖z‖ = R ^ 2 := by
    have h_left : ‖star ρ * z‖ = ‖ρ‖ * ‖z‖ := by
      rw [norm_mul, norm_star]
    have h_right : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
      rw [Complex.norm_pow, Complex.norm_of_nonneg (le_of_lt hR_pos)]
    rw [← h_left, h_mul_eq_R_sq, h_right]

  -- Since ‖ρ‖ ≤ R1 and ‖z‖ ≤ R1, we have R² = ‖ρ‖ * ‖z‖ ≤ R1 * R1 = R1²
  have h_R_sq_le : R ^ 2 ≤ R1 ^ 2 := by
    calc R ^ 2
      = ‖ρ‖ * ‖z‖ := h_norm_eq.symm
      _ ≤ R1 * ‖z‖ := mul_le_mul_of_nonneg_right hρ_bound (norm_nonneg z)
      _ ≤ R1 * R1 := mul_le_mul_of_nonneg_left hz_in_R1 (le_of_lt hR1_pos)
      _ = R1 ^ 2 := by rw [← pow_two]

  -- This gives R ≤ R1
  have h_R_le_R1 : R ≤ R1 := by
    exact le_of_pow_le_pow_left₀ (by norm_num) (le_of_lt hR1_pos) h_R_sq_le

  -- This contradicts the hypothesis R1 < R
  linarith

lemma linear_pow_analytic (a b : ℂ) (n : ℕ) (z : ℂ) :
    AnalyticAt ℂ (fun w => (a - b * w) ^ n) z := by
  -- The function w ↦ a - b * w is linear, hence analytic
  have h_linear : AnalyticAt ℂ (fun w => a - b * w) z := by
    -- a is constant, hence analytic
    have h_const : AnalyticAt ℂ (fun _ => a) z := analyticAt_const
    -- b * w is analytic (scalar multiplication of identity)
    have h_mul : AnalyticAt ℂ (fun w => b * w) z := by
      have h_id : AnalyticAt ℂ (fun w => w) z := analyticAt_id
      exact AnalyticAt.fun_mul analyticAt_const h_id
    -- subtraction of analytic functions is analytic
    exact h_const.sub h_mul
  -- Powers of analytic functions are analytic
  exact h_linear.fun_pow n



end AnalyticZeroCounting
