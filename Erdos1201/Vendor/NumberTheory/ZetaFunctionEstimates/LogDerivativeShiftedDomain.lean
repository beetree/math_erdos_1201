module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Erdos1201.Vendor.NumberTheory.ZetaFunctionEstimates.ZetaAnalyticContinuation

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
The log-derivative of `riemannZeta`, analyticity of `riemannZeta` away from
`1`, and the shifted-domain machinery needed to apply `AnalyticZeroCounting`'s
`final_ineq1` to a disk centered at `c = 3/2 + it` (`fc_analytic_normalized`,
`fc_log_deriv`, `fc_bound`, `fc_zeros`, `fc_m_order`, `DminusK`): the
normalized shift `g(w) = f(w+c)/f(c)` translates a general disk-centered
zero-counting/log-derivative bound (`AnalyticZeroCounting.final_ineq1`) into
`final_ineq2`, the version centered at `c` used for the concrete estimates
on `riemannZeta` at `c = 3/2 + it`.
-/

public section

namespace ZetaFunctionEstimates

open Real Set Filter Topology MeasureTheory Complex Metric AnalyticZeroCounting

@[expose] noncomputable def logDerivZeta (s : ℂ) : ℂ := deriv riemannZeta s / riemannZeta s

@[expose] def zerosetKfRc (R : ℝ) (c : ℂ) (f : ℂ → ℂ) : Set ℂ :=
  {ρ : ℂ | ρ ∈ Metric.closedBall c R ∧ f ρ = 0}

lemma zetadiffAtnot1 : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ riemannZeta s :=
  fun _ => differentiableAt_riemannZeta



lemma DiffAtOn {T : Set ℂ} {g : ℂ → ℂ} :
    (∀ s ∈ T, DifferentiableAt ℂ g s) → DifferentiableOn ℂ g T := by
  intro h s hs
  exact (h s hs).differentiableWithinAt

lemma DiffOnanalOnNhd {T : Set ℂ} (hT : IsOpen T) {g : ℂ → ℂ} :
    DifferentiableOn ℂ g T → AnalyticOnNhd ℂ g T := by
  intro hdiff
  exact hdiff.analyticOnNhd hT

lemma DiffAtallanalOnNhd {T : Set ℂ} (hT : IsOpen T) {g : ℂ → ℂ} :
    (∀ s ∈ T, DifferentiableAt ℂ g s) → AnalyticOnNhd ℂ g T := by
  intro hdiff
  apply DiffOnanalOnNhd hT
  exact DiffAtOn hdiff

lemma zetaanalOnnot1 : AnalyticOnNhd ℂ riemannZeta {s : ℂ | s ≠ 1} := by
  apply DiffAtallanalOnNhd
  · apply isOpen_compl_singleton
  · exact zetadiffAtnot1

lemma I_mul_ofReal_im (t : ℝ) : (I * ↑t).im = t := by
  have h1 : (I * (↑t : ℂ)).im = (↑t : ℂ).re := Complex.I_mul_im (↑t : ℂ)
  rw [h1]
  simp [Complex.ofReal_re]

lemma complex_im_sub_I_mul (a : ℂ) (t : ℝ) : (a - I * t).im = a.im - t := by
  rw [Complex.sub_im]
  rw [I_mul_ofReal_im]

lemma D1cinTt_pre (t : ℝ) (ht : |t| > 1) :
    ∀ s ∈ closedBall (3/2 + I * t : ℂ) 1, s ≠ 1 := by
  intro s hs
  by_contra h
  rw [h] at hs
  rw [mem_closedBall] at hs
  rw [Complex.dist_eq] at hs
  have h1 : (1 : ℂ) - (3/2 + I * t) = -1/2 - I * t := by ring
  rw [h1] at hs
  have h2 : (-1/2 - I * t : ℂ).im = -t := by
    have : (-1/2 - I * t : ℂ) = (-1/2 : ℂ) - I * t := by ring
    rw [this]
    rw [complex_im_sub_I_mul]
    simp [Complex.ofReal_im]
  have h3 : ‖(-1/2 - I * t : ℂ)‖ ≥ |(-1/2 - I * t : ℂ).im| := Complex.abs_im_le_norm _
  rw [h2] at h3
  rw [abs_neg] at h3
  have h4 : ‖(-1/2 - I * t : ℂ)‖ > 1 := lt_of_lt_of_le ht h3
  linarith [h4, hs]

lemma D1cinTt (t : ℝ) (ht : |t| > 1) :
    closedBall (3/2 + I * t : ℂ) 1 ⊆ {s : ℂ | s ≠ 1} := by
  exact fun s hs => D1cinTt_pre t ht s hs

lemma zetaanalOnD1c (t : ℝ) (ht : |t| > 1) :
    AnalyticOnNhd ℂ riemannZeta (closedBall (3/2 + I * t : ℂ) 1) := by
  apply zetaanalOnnot1.mono
  exact D1cinTt t ht


lemma sigmageq1 (s : ℂ) (hs : s.re > 1) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

lemma Complex_I_mul_ofReal_re (r : ℝ) : (I * (r : ℂ)).re = 0 := by
  have h : (I * (r : ℂ)).re = -(r : ℂ).im := Complex.I_mul_re (r : ℂ)
  rw [h]
  simp

lemma re_real_add_I_mul_gt (a b : ℝ) (h : a > 1) : (a + I * b).re > 1 := by
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  rw [Complex_I_mul_ofReal_re]
  simp
  exact h

lemma fc_analytic_normalized (c : ℂ) (f : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0) :
    (AnalyticOnNhd ℂ (fun z => f (z + c) / f c) (closedBall (0 : ℂ) 1)) ∧ (fun z => f (z + c) / f c) 0 = 1 := by
  constructor
  · apply AnalyticOnNhd.div
    · apply AnalyticOnNhd.comp h_analytic
      · intro z _
        exact analyticAt_id.add analyticAt_const
      · intro z hz
        rw [mem_closedBall] at hz ⊢
        rw [Complex.dist_eq] at hz ⊢
        convert hz using 1
        ring_nf
    · exact analyticOnNhd_const
    · intro z _
      exact h_nonzero
  · simp
    exact h_nonzero

lemma deriv_normalized_nohd (c : ℂ) (f : ℂ → ℂ) (z : ℂ) (h_nonzero : f c ≠ 0) :
  deriv (fun w => f (w + c) / f c) z = (deriv f (z + c)) / f c := by
  rw [deriv_div_const]
  rw [deriv_comp_add_const]

lemma frac_cancel_const {x y c : ℂ} (hc : c ≠ 0) (hy : y ≠ 0) : (x / c) / (y / c) = x / y := by
  field_simp [hc, hy]


lemma fc_bound (B : ℝ) (hB : B > 1) (R : ℝ) (hRpos : 0 < R) (hR : R < 1) (c : ℂ) (f : ℂ → ℂ) (h_nonzero : f c ≠ 0)
    (h_bound : ∀ z ∈ closedBall c R, ‖f z‖ ≤ B) :
    ∀ z ∈ closedBall (0 : ℂ) R, ‖(fun w => f (w + c) / f c) z‖ ≤ B / ‖f c‖ := by
  intro z hz
  have hz' : ‖z‖ ≤ R := by
    simpa [mem_closedBall, Complex.dist_eq] using hz
  have hz_plus : z + c ∈ closedBall c R := by
    have : ‖(z + c) - c‖ ≤ R := by simpa [add_sub_cancel] using hz'
    simpa [mem_closedBall, Complex.dist_eq] using this
  have hfb : ‖f (z + c)‖ ≤ B := h_bound (z + c) hz_plus
  have hnorm : ‖f (z + c) / f c‖ = ‖f (z + c)‖ / ‖f c‖ := by
    simp [div_eq_mul_inv, norm_mul, norm_inv]
  have : ‖f (z + c)‖ / ‖f c‖ ≤ B / ‖f c‖ :=
    div_le_div_of_nonneg_right hfb (norm_nonneg _)
  simpa [hnorm] using this

lemma fc_zeros (r : ℝ) (h : r > 0) (c : ℂ) (f : ℂ → ℂ) (h_nonzero : f c ≠ 0)
  (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) :
    (zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)) = (fun ρ => ρ - c) '' (zerosetKfRc r c f) := by
  ext ρ'; constructor
  · intro hmem
    rcases hmem with ⟨hball, hzero⟩
    have hprod : f (ρ' + c) * (f c)⁻¹ = 0 := by simpa [div_eq_mul_inv] using hzero
    have hnum0 : f (ρ' + c) = 0 := by
      rcases mul_eq_zero.mp hprod with hnum | hinv
      · exact hnum
      · have : (f c)⁻¹ ≠ 0 := inv_ne_zero h_nonzero
        exact (this hinv).elim
    refine ⟨ρ' + c, ?_, ?_⟩
    · have hdist0 : dist ρ' (0 : ℂ) ≤ r := by simpa [mem_closedBall] using hball
      have hdist1 : dist (ρ' + c) c ≤ r := by
        simpa [Complex.dist_eq, add_sub_cancel] using hdist0
      have hmem_ball : ρ' + c ∈ closedBall c r := by
        simpa [mem_closedBall] using hdist1
      exact And.intro hmem_ball hnum0
    · simp
  · intro him
    rcases him with ⟨y, hy_mem, hy_eq⟩
    subst hy_eq
    rcases hy_mem with ⟨hy_ball, hy_zero⟩
    refine And.intro ?_ ?_
    · have hdist : dist y c ≤ r := by simpa [mem_closedBall] using hy_ball
      have hdist0 : dist (y - c) (0 : ℂ) ≤ r := by
        simpa [Complex.dist_eq, sub_zero] using hdist
      simpa [mem_closedBall] using hdist0
    · simp [sub_add_cancel, hy_zero]

lemma analyticOrderAt_const_mul_eq (f : ℂ → ℂ) (a z0 : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun z => a * f z) z0 = analyticOrderAt f z0 := by
  classical
  by_cases hf : AnalyticAt ℂ f z0
  · have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
      simpa using (analyticAt_const (x := z0) (v := a))
    have hconst_order_zero : analyticOrderAt (fun _ : ℂ => a) z0 = 0 := by
      refine (AnalyticAt.analyticOrderAt_eq_natCast (f := fun _ : ℂ => a) (z₀ := z0) hconst).mpr ?_
      refine ⟨(fun _ : ℂ => a), (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) z0), ?_, ?_⟩
      · simpa using ha
      · exact Filter.Eventually.of_forall (fun _ => by simp)
    have hmul := analyticOrderAt_mul (f := fun _ : ℂ => a) (g := f) hconst hf
    have hpi : ((fun _ : ℂ => a) * f) = fun z => a * f z := by
      funext z; simp [Pi.mul_apply]
    rw [hpi] at hmul
    simpa [hconst_order_zero, zero_add] using hmul
  · have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
      simpa using (analyticAt_const (x := z0) (v := a))
    have hconst_ne : (fun _ : ℂ => a) z0 ≠ 0 := by simpa using ha
    have hiff := (analyticAt_iff_analytic_fun_mul (f := fun _ : ℂ => a) (g := f) (z := z0) hconst hconst_ne)
    have hmul : ¬ AnalyticAt ℂ (fun z => a * f z) z0 := by
      intro h
      have : AnalyticAt ℂ f z0 := (hiff.mpr (by simpa using h))
      exact hf this
    simp [analyticOrderAt, hf, hmul]







lemma analyticOrderAt_mul_const_eq (f : ℂ → ℂ) (a z0 : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun z => f z * a) z0 = analyticOrderAt f z0 := by
  classical
  have hcomm : (fun z => f z * a) = (fun z => a * f z) := by
    funext z; simp [mul_comm]
  have hrew : analyticOrderAt (fun z => f z * a) z0 =
      analyticOrderAt (fun z => a * f z) z0 := by
    simp [hcomm]
  by_cases hf : AnalyticAt ℂ f z0
  · have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) z0)
    have hadd : analyticOrderAt (fun z => a * f z) z0
        = analyticOrderAt (fun _ : ℂ => a) z0 + analyticOrderAt f z0 := by
      have hm := analyticOrderAt_mul hconst hf
      have hpi : ((fun _ : ℂ => a) * f) = fun z => a * f z := by
        funext z; simp [Pi.mul_apply]
      rwa [hpi] at hm
    have hconst_zero : analyticOrderAt (fun _ : ℂ => a) z0 = 0 := by
      have hiff := (AnalyticAt.analyticOrderAt_eq_zero hconst)
      have hval : (fun _ : ℂ => a) z0 ≠ 0 := by simpa using ha
      exact hiff.mpr hval
    calc
      analyticOrderAt (fun z => f z * a) z0
          = analyticOrderAt (fun z => a * f z) z0 := hrew
      _ = analyticOrderAt (fun _ : ℂ => a) z0 + analyticOrderAt f z0 := hadd
      _ = 0 + analyticOrderAt f z0 := by simp [hconst_zero]
      _ = analyticOrderAt f z0 := by simp
  · have hnot : ¬ AnalyticAt ℂ (fun z => a * f z) z0 := by
      intro hmul
      have hconst : AnalyticAt ℂ (fun _ : ℂ => a) z0 := by
        simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => a) z0)
      have hval : (fun _ : ℂ => a) z0 ≠ 0 := by simpa using ha
      have hiff := (analyticAt_iff_analytic_fun_smul (h₁f := hconst) (h₂f := hval)
                        (g := f) (z := z0))
      have hsmul : AnalyticAt ℂ (fun z => (fun _ : ℂ => a) z • f z) z0 := by
        simpa [smul_eq_mul] using hmul
      have : AnalyticAt ℂ f z0 := hiff.mpr hsmul
      exact hf this
    calc
      analyticOrderAt (fun z => f z * a) z0
          = analyticOrderAt (fun z => a * f z) z0 := hrew
      _ = 0 := by simp [analyticOrderAt, hnot]
      _ = analyticOrderAt f z0 := by simp [analyticOrderAt, hf]

lemma fc_m_order (r : ℝ) (h : r > 0) (c : ℂ) (f : ℂ → ℂ) (h_nonzero : f c ≠ 0)
    (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1))
    {ρ' : ℂ} (hρ' : ρ' ∈ zerosetKfRc r (0 : ℂ) (fun z => f (z + c) / f c)) :
    analyticOrderAt (fun z => f (z + c) / f c) ρ' = analyticOrderAt f (ρ' + c) := by
  classical
  set g0 : ℂ → ℂ := fun z => f (z + c) with hg0
  have hconst : analyticOrderAt (fun z => g0 z * (1 / f c)) ρ' = analyticOrderAt g0 ρ' := by
    have hne : (1 / f c) ≠ 0 := one_div_ne_zero h_nonzero
    simpa using (analyticOrderAt_mul_const_eq (f := g0) (a := (1 / f c)) (z0 := ρ') hne)
  have hconst_rewrite : analyticOrderAt (fun z => f (z + c) / f c) ρ'
        = analyticOrderAt (fun z => g0 z * (1 / f c)) ρ' := by
    have : (fun z => f (z + c) / f c) = (fun z => g0 z * (1 / f c)) := by
      funext z; simp [g0, hg0, div_eq_mul_inv, mul_comm]
    simp [this]
  have htrans : analyticOrderAt g0 ρ' = analyticOrderAt f (ρ' + c) := by
    by_cases hfA : AnalyticAt ℂ f (ρ' + c)
    · have h_add : AnalyticAt ℂ (fun z : ℂ => z + c) ρ' :=
        AnalyticAt.add analyticAt_id analyticAt_const
      have hgA : AnalyticAt ℂ g0 ρ' := by
        have hcomp : AnalyticAt ℂ f ((fun z : ℂ => z + c) ρ') := by simpa using hfA
        have := AnalyticAt.comp (g := f) (f := fun z : ℂ => z + c) (x := ρ') hcomp h_add
        simpa [g0, hg0, Function.comp_def] using this
      by_cases hgez : (∀ᶠ z in nhds ρ', g0 z = 0)
      · have hT_sub_cont : ContinuousAt (fun w : ℂ => w - c) (ρ' + c) :=
          ContinuousAt.sub continuousAt_id continuousAt_const
        have hT_sub : Tendsto (fun w : ℂ => w - c) (nhds (ρ' + c)) (nhds ρ') := by
          simpa using (hT_sub_cont.tendsto)
        have hEfw : ∀ᶠ w in nhds (ρ' + c), f w = 0 := by
          have : ∀ᶠ w in nhds (ρ' + c), g0 (w - c) = 0 := hT_sub.eventually hgez
          simpa [g0, hg0, sub_add_cancel] using this
        have hg_top : analyticOrderAt g0 ρ' = ⊤ :=
          (analyticOrderAt_eq_top (f := g0) (z₀ := ρ')).2 hgez
        have hf_top : analyticOrderAt f (ρ' + c) = ⊤ :=
          (analyticOrderAt_eq_top (f := f) (z₀ := ρ' + c)).2 hEfw
        simp [hg_top, hf_top]
      · have h_exists := (AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff hgA).mpr hgez
        rcases h_exists with ⟨n, φ, hφA, hφ_ne, hevent⟩
        have hT_sub_cont : ContinuousAt (fun w : ℂ => w - c) (ρ' + c) :=
          ContinuousAt.sub continuousAt_id continuousAt_const
        have hT_sub : Tendsto (fun w : ℂ => w - c) (nhds (ρ' + c)) (nhds ρ') := by
          simpa using (hT_sub_cont.tendsto)
        have hevent_w : ∀ᶠ w in nhds (ρ' + c), f w
              = (w - (ρ' + c)) ^ n * ((fun w => φ (w - c)) w) := by
          have : ∀ᶠ w in nhds (ρ' + c), g0 (w - c)
                    = ((w - c) - ρ') ^ n * φ (w - c) :=
            hT_sub.eventually hevent
          refine this.mono ?_
          intro w hw
          have hsubsimp : (w - c) - ρ' = w - (ρ' + c) := by ring
          simpa [g0, hg0, hsubsimp] using hw
        have hψA : AnalyticAt ℂ (fun w => φ (w - c)) (ρ' + c) := by
          have h_subA : AnalyticAt ℂ (fun w : ℂ => w - c) (ρ' + c) :=
            AnalyticAt.sub analyticAt_id analyticAt_const
          have hφA_at : AnalyticAt ℂ φ ((fun w : ℂ => w - c) (ρ' + c)) := by simpa using hφA
          have := AnalyticAt.comp (g := φ) (f := fun w => w - c) (x := (ρ' + c)) hφA_at h_subA
          simpa [Function.comp_def] using this
        have hψ_ne : (fun w => φ (w - c)) (ρ' + c) ≠ 0 := by
          simpa using hφ_ne
        have hg_eq_n : analyticOrderAt g0 ρ' = n := by
          exact (AnalyticAt.analyticOrderAt_eq_natCast (f := g0) (z₀ := ρ') hgA).mpr
            ⟨φ, hφA, hφ_ne, hevent⟩
        have hf_eq_n : analyticOrderAt f (ρ' + c) = n := by
          exact (AnalyticAt.analyticOrderAt_eq_natCast (f := f) (z₀ := ρ' + c) hfA).mpr
            ⟨(fun w => φ (w - c)), hψA, hψ_ne, hevent_w⟩
        simp [hg_eq_n, hf_eq_n]
    · have hg_not : ¬ AnalyticAt ℂ g0 ρ' := by
        intro hgA
        have h_subA : AnalyticAt ℂ (fun w : ℂ => w - c) (ρ' + c) :=
          AnalyticAt.sub analyticAt_id analyticAt_const
        have hgA_at : AnalyticAt ℂ g0 ((ρ' + c) - c) := by simpa using hgA
        have hcomp := (AnalyticAt.comp (g := g0) (f := fun w => w - c)
                          (x := (ρ' + c)) hgA_at h_subA)
        have : AnalyticAt ℂ (fun w : ℂ => g0 (w - c)) (ρ' + c) := by simpa [Function.comp_def] using hcomp
        have : AnalyticAt ℂ f (ρ' + c) := by
          simpa [g0, hg0, sub_add_cancel] using this
        exact hfA this
      simp [analyticOrderAt, hfA, hg_not]
  calc
    analyticOrderAt (fun z => f (z + c) / f c) ρ'
        = analyticOrderAt (fun z => g0 z * (1 / f c)) ρ' := hconst_rewrite
    _ = analyticOrderAt g0 ρ' := hconst
    _ = analyticOrderAt f (ρ' + c) := htrans

lemma DminusK (r1 : ℝ) (R1 : ℝ) (hr1 : r1 > 0) (hR1 : R1 > 0) (c : ℂ) (f : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0) :
    ∀ z : ℂ, z ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun w => f (w + c) / f c) ↔
             z + c ∈ closedBall c r1 \ zerosetKfRc R1 c f := by
  intro z
  constructor
  · intro ⟨hz_ball, hz_not_zero⟩
    constructor
    · have hdist : dist z (0 : ℂ) ≤ r1 := by simpa [mem_closedBall] using hz_ball
      have hdist_c : dist (z + c) c ≤ r1 := by
        simpa [Complex.dist_eq, add_sub_cancel] using hdist
      simpa [mem_closedBall] using hdist_c
    · intro h_contra
      apply hz_not_zero
      rcases h_contra with ⟨hz_c_ball, hz_c_zero⟩
      constructor
      · have hdist_c : dist (z + c) c ≤ R1 := by simpa [mem_closedBall] using hz_c_ball
        have hdist_0 : dist z (0 : ℂ) ≤ R1 := by
          simpa [Complex.dist_eq, add_sub_cancel] using hdist_c
        simpa [mem_closedBall] using hdist_0
      · have : f (z + c) = 0 := hz_c_zero
        simp [this, zero_div]
  · intro ⟨hz_c_ball, hz_c_not_zero⟩
    constructor
    · have hdist_c : dist (z + c) c ≤ r1 := by simpa [mem_closedBall] using hz_c_ball
      have hdist_0 : dist z (0 : ℂ) ≤ r1 := by
        simpa [Complex.dist_eq, add_sub_cancel] using hdist_c
      simpa [mem_closedBall] using hdist_0
    · intro h_contra
      apply hz_c_not_zero
      rcases h_contra with ⟨hz_ball, hz_zero⟩
      constructor
      · have hdist_0 : dist z (0 : ℂ) ≤ R1 := by simpa [mem_closedBall] using hz_ball
        have hdist_c : dist (z + c) c ≤ R1 := by
          simpa [Complex.dist_eq, add_sub_cancel] using hdist_0
        simpa [mem_closedBall] using hdist_c
      · have h_div_zero : f (z + c) / f c = 0 := hz_zero
        have h_mul_zero : f (z + c) * (f c)⁻¹ = 0 := by simpa [div_eq_mul_inv] using h_div_zero
        rcases mul_eq_zero.mp h_mul_zero with h_num | h_inv
        · exact h_num
        · have : (f c)⁻¹ ≠ 0 := inv_ne_zero h_nonzero
          exact (this h_inv).elim

lemma shifted_zeros_correspondence (R1 : ℝ) (hR1 : R1 > 0) (c z : ℂ)
    (f : ℂ → ℂ) (h_nonzero : f c ≠ 0) (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1))
    (hfin_orig : (zerosetKfRc R1 c f).Finite)
    (hfin_shift : (zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c)).Finite) :
    ∑ ρ ∈ hfin_orig.toFinset, ((analyticOrderAt f ρ).toNat : ℂ) / (z - ρ) =
    ∑ ρ' ∈ hfin_shift.toFinset, ((analyticOrderAt (fun u => f (u + c) / f c) ρ').toNat : ℂ) / ((z - c) - ρ') := by
  have h_bij : (zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c)) = (fun ρ => ρ - c) '' (zerosetKfRc R1 c f) :=
    fc_zeros R1 hR1 c f h_nonzero h_analytic
  apply Finset.sum_bij (fun ρ _ => ρ - c)
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset] at hρ ⊢
    rw [h_bij]
    use ρ, hρ
  · intro ρ₁ hρ₁ ρ₂ hρ₂ h_eq
    have : ρ₁ = ρ₁ - c + c := by ring
    rw [this, h_eq]
    ring
  · intro ρ' hρ'
    simp only [Set.Finite.mem_toFinset] at hρ'
    rw [h_bij] at hρ'
    obtain ⟨ρ, hρ_mem, hρ_eq⟩ := hρ'
    use ρ
    simp only [Set.Finite.mem_toFinset]
    exact ⟨hρ_mem, hρ_eq⟩
  · intro ρ hρ
    simp only [Set.Finite.mem_toFinset] at hρ
    have h_shift_mem : ρ - c ∈ zerosetKfRc R1 (0 : ℂ) (fun u => f (u + c) / f c) := by
      rw [h_bij]
      use ρ, hρ
    have h_order := fc_m_order R1 hR1 c f h_nonzero h_analytic h_shift_mem
    have h_add : (ρ - c) + c = ρ := by ring
    rw [h_add] at h_order
    rw [← h_order]
    ring

lemma final_ineq2
    (B : ℝ) (hB : 1 < B) (r1 r R R1 : ℝ) (hr1pos : 0 < r1) (hr1_lt_r : r1 < r) (hr_lt_R1 : r < R1)
    (hR1_lt_R : R1 < R) (hR : R < 1)
    (c : ℂ) (f : ℂ → ℂ) (h_analytic : AnalyticOnNhd ℂ f (closedBall c 1)) (h_nonzero : f c ≠ 0)
    (h_bound : ∀ z ∈ closedBall c R, ‖f z‖ < B)
    (hfin : (zerosetKfRc R1 (0 : ℂ) (fun z => f (z + c) / f c)).Finite) :
    ∀ z ∈ closedBall (0 : ℂ) r1 \ zerosetKfRc R1 (0 : ℂ) (fun z => f (z + c) / f c),
    ‖(deriv (fun z => f (z + c) / f c) z / (f (z + c) / f c)) - ∑ ρ ∈ hfin.toFinset,
      ((analyticOrderAt (fun w => f (w + c) / f c) ρ).toNat : ℂ) / (z - ρ)‖ ≤ (16 * r^2 / ((r - r1)^3) +
    1 / ((R^2 / R1 - R1) * Real.log (R / R1))) * Real.log (B / ‖f c‖) := by
  intro z hz
  let g : ℂ → ℂ := fun w => f (w + c) / f c
  have hR_pos : 0 < R := by linarith [hr1pos, hr1_lt_r, hr_lt_R1, hR1_lt_R]
  have hR1_pos : 0 < R1 := by linarith [hr1pos, hr1_lt_r, hr_lt_R1]
  have h_norm_pos : 0 < ‖f c‖ := norm_pos_iff.mpr h_nonzero
  have h_fc_bound_at_c : ‖f c‖ < B := by
    apply h_bound
    rw [mem_closedBall, dist_self]
    exact le_of_lt hR_pos
  have h_B_div_gt_one : 1 < B / ‖f c‖ := by
    rw [one_lt_div h_norm_pos]
    exact h_fc_bound_at_c
  have h_g_analytic : ∀ w ∈ closedBall (0 : ℂ) 1, AnalyticAt ℂ g w :=
    (fc_analytic_normalized c f h_analytic h_nonzero).1
  have h_g_zero : g 0 = 1 :=
    (fc_analytic_normalized c f h_analytic h_nonzero).2
  have h_g_bound : ∀ w ∈ closedBall (0 : ℂ) R, ‖g w‖ ≤ B / ‖f c‖ := by
    apply fc_bound B hB R hR_pos hR c f h_nonzero
    intro w hw
    exact le_of_lt (h_bound w hw)
  have h_zeroset_equiv : zerosetKfRc R1 (0 : ℂ) g = zerosetKfR R1 hR1_pos g := by
    ext ρ
    simp only [zerosetKfRc, zerosetKfR, mem_ofPred_eq, mem_closedBall, Complex.dist_eq, sub_zero]
  have h_g_finite : (zerosetKfR R1 hR1_pos g).Finite := by
    rwa [← h_zeroset_equiv]
  have h_σ_exists : ∃ h_σ : ℂ → (ℂ → ℂ), ∀ σ ∈ zerosetKfR R1 hR1_pos g,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ w in nhds σ, g w = (w - σ) ^ (analyticOrderAt g σ).toNat * h_σ σ w := by
    classical
    let h_σ : ℂ → (ℂ → ℂ) := fun σ =>
      if hσ : σ ∈ zerosetKfR R1 hR1_pos g
      then Classical.choose (lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR g h_g_analytic
           (by simp [g]; exact h_nonzero) σ hσ)
      else fun _ => 0
    use h_σ
    intro σ hσ
    simp only [h_σ, dite_eq_left hσ]
    exact Classical.choose_spec (lem_analytic_zero_factor R R1 hR1_pos hR1_lt_R hR g h_g_analytic
           (by simp [g]; exact h_nonzero) σ hσ)
  obtain ⟨h_σ, h_σ_spec⟩ := h_σ_exists
  have := final_ineq1 (B / ‖f c‖) h_B_div_gt_one r1 r R R1 hr1pos hr1_lt_r hr_lt_R1 hR1_lt_R hR
    g h_g_analytic h_g_zero h_g_finite h_σ_spec h_g_bound z
  have hz_domain : z ∈ closedBall (0 : ℂ) r1 \ zerosetKfR R1 hR1_pos g := by
    rw [h_zeroset_equiv] at hz
    exact hz
  exact this hz_domain

end ZetaFunctionEstimates
