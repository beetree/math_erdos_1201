module

public import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.LogDerivZetaStripRefinement
import Erdos1201.Vendor.NumberTheory.BoundedPrimeGaps.BombieriVinogradov.Analytic.RiemannZetaZeroFree

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
This is the capstone module of the zero-free-region development: it assembles the earlier
center/edge bounds on `ζ'/ζ` into a single uniform bound valid on `|t| > 3` and
`σ ≥ 1 - A / log(|t|+2)` (`thm_final_result`), restates it as a genuine zero-free region for
`riemannZeta` (`ZetaZeroFree_p`), and repackages the uniform bound with an `Ici`-style hypothesis
(`LogDerivZetaBndUnif2`). `ZetaZeroFree_p` is consumed by a sibling module in this family.
-/

public section

namespace ZetaZeroFreeRegion

open Complex Topology Filter Interval Set Asymptotics Function Real ZetaFunctionEstimates AnalyticZeroCounting

lemma lem_norm_logDeriv_le_tsum (s : ℂ) (hs : 1 < s.re) :
  ‖deriv riemannZeta s / riemannZeta s‖ ≤ ∑' n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s)‖ := by
  classical
  -- Define f(n) = Λ(n) as complex-valued coefficients
  let f : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
  -- Summability of the L-series terms on Re s > 1
  have hsum_term : Summable (fun n : ℕ => LSeries.term f s n) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) hs
  -- Hence the sum of norms is summable as well in ℂ (finite-dimensional over ℝ)
  have hsum_norm : Summable (fun n : ℕ => ‖LSeries.term f s n‖) :=
    (summable_norm_iff).mpr hsum_term
  -- Identification of the L-series with the negative logarithmic derivative
  have hEq : (∑' n : ℕ, LSeries.term f s n) = - deriv riemannZeta s / riemannZeta s :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := s) hs
  -- Pointwise identification of the norm of the L-series term with the explicit quotient
  have hpoint : (fun n : ℕ => ‖LSeries.term f s n‖)
                = (fun n : ℕ => ‖f n / ((n : ℂ) ^ s)‖) := by
    funext n
    by_cases h0 : n = 0
    · -- At n = 0, both sides are 0
      subst h0
      -- Use that Λ(0) = 0 since it is a ZeroHom
      have hf0r : ArithmeticFunction.vonMangoldt 0 = 0 := by
        simp
      have hf0 : f 0 = 0 := by simp [f, hf0r]
      simp [LSeries.term, f, hf0]
    · -- For n ≠ 0, the term is exactly f n / (n^s)
      simp [LSeries.term, f, h0]
  -- Apply the inequality ‖tsum f‖ ≤ ∑ ‖f‖ and rewrite
  calc
    ‖deriv riemannZeta s / riemannZeta s‖
        = ‖- deriv riemannZeta s / riemannZeta s‖ := by simp [norm_neg]
    _ = ‖∑' n : ℕ, LSeries.term f s n‖ := by simp [hEq]
    _ ≤ ∑' n : ℕ, ‖LSeries.term f s n‖ :=
          norm_tsum_le_tsum_norm (f := fun n : ℕ => LSeries.term f s n) hsum_norm
    _ = ∑' n : ℕ, ‖f n / ((n : ℂ) ^ s)‖ := by simp [hpoint]
    _ = ∑' n : ℕ, ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / ((n : ℂ) ^ s)‖ := rfl

lemma lem_tsum_norm_vonMangoldt_depends_on_Re_cast (s : ℂ) (σ : ℝ)
  (hσ : σ = s.re) (hs : 1 < s.re) :
  (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
    = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
  -- s.re ≠ 0 and σ ≠ 0
  have hre_ne_zero : s.re ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs)
  have hσ_ne_zero : σ ≠ 0 := by
    have : 0 < σ := by simpa [hσ] using (lt_trans zero_lt_one hs)
    exact ne_of_gt this
  -- Show equality of the summands for each n, then conclude by congrArg on tsum
  have hterm : (fun n : ℕ => ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
      = (fun n : ℕ => ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    funext n
    -- Denominator norms depend only on real part of exponent
    have hden_s : ‖(n : ℂ) ^ s‖ = (n : ℝ) ^ s.re :=
      Complex.norm_natCast_cpow_of_re_ne_zero n hre_ne_zero
    have hden_σ : ‖(n : ℂ) ^ (σ : ℂ)‖ = (n : ℝ) ^ (σ : ℂ).re :=
      Complex.norm_natCast_cpow_of_re_ne_zero n (by simpa [Complex.ofReal_re] using hσ_ne_zero)
    calc
      ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖
          = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ / ‖(n : ℂ) ^ s‖ := by simp [norm_div]
      _ = |ArithmeticFunction.vonMangoldt n| / ((n : ℝ) ^ s.re) := by
            simp [hden_s, Complex.norm_real]
      _ = |ArithmeticFunction.vonMangoldt n| / ((n : ℝ) ^ σ) := by simp [hσ]
      _ = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))‖ / ‖(n : ℂ) ^ (σ : ℂ)‖ := by
            simp [hden_σ, Complex.ofReal_re, Complex.norm_real]
      _ = ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖ := by simp [norm_div]
  simpa using congrArg (fun f : ℕ → ℝ => ∑' n, f n) hterm

lemma helper_norm_neg_logDeriv_eq_tsum_norm (σ : ℝ) (hσ : 1 < σ) :
  ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ =
    (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖) := by
  -- The named real-σ equality already on this file's import graph
  -- (VonMangoldtSeriesPositivityBounds), rewritten from `|∑ Λn·n^{-σ}|` to
  -- `∑ ‖Λn/n^σ‖` using nonnegativity of each term.
  have hkey := norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt σ hσ
  have hterm : ∀ n : ℕ,
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖
        = (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) := by
    intro n
    by_cases h0 : n = 0
    · simp [h0]
    · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
      have hcp : (n : ℂ) ^ (-(σ : ℂ)) = Complex.ofReal ((n : ℝ) ^ (-σ)) := by
        simpa using (Complex.ofReal_cpow (x := (n : ℝ)) (Nat.cast_nonneg n) (-σ)).symm
      have hval : (ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))
          = Complex.ofReal ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ)) := by
        rw [div_eq_mul_inv, ← Complex.cpow_neg, hcp]
        simp [Complex.ofReal_mul]
      rw [hval]
      simp [Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) (-σ))]
  have hsum_eq : (∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) / ((n : ℂ) ^ (σ : ℂ))‖)
      = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) :=
    tsum_congr hterm
  have hsum_nonneg : 0 ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-σ) :=
    tsum_nonneg (vonMangoldt_rpow_nonneg σ)
  rw [hsum_eq, ← abs_of_nonneg hsum_nonneg, ← hkey]
  simp [logDerivZeta, neg_div]

theorem lem_zetacenterbd :
  ∀ t : ℝ,
    ∀ σ : ℝ,
      σ ≥ 3/2 →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤
      ‖deriv riemannZeta σ / riemannZeta σ‖ := by
  intro t σ hσge
  -- Set s = σ + it
  set s : ℂ := Complex.mk σ t
  -- Since σ ≥ 3/2 > 1, we have 1 < s.re and 1 < σ
  have hs : 1 < s.re := by
    have : (1 : ℝ) < (3 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hσge
  have hσgt1 : 1 < σ := by
    have : (1 : ℝ) < (3 / 2 : ℝ) := by norm_num
    exact lt_of_lt_of_le this hσge
  -- First bound by sum of norms of the L-series terms at s
  have h_le_sum := lem_norm_logDeriv_le_tsum s hs
  have h1 : ‖deriv riemannZeta s / riemannZeta s‖ ≤
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖) := by
    simpa [norm_div, Complex.norm_real] using h_le_sum
  -- The sum of norms depends only on the real part of s, i.e., equals the sum at σ ∈ ℝ
  have h_dep :
      (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ s)‖)
        = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) := by
    -- here s.re = σ
    have hre : σ = s.re := by simp [s]
    simpa using (lem_tsum_norm_vonMangoldt_depends_on_Re_cast s σ hre hs)
  have h_dep_ratio :
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖)
        = (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖) := by
    simpa [norm_div, Complex.norm_real] using h_dep
  -- At real σ, the sum of norms equals the norm of -ζ'/ζ(σ)
  have h_sum_eq_norm :
      ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖
        = (∑' n : ℕ, ‖(((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) / ((n : ℂ) ^ (σ : ℂ))‖) :=
    helper_norm_neg_logDeriv_eq_tsum_norm σ hσgt1
  have h_sum_eq_norm_ratio :
      (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖)
        = ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    simpa [norm_div, Complex.norm_real] using h_sum_eq_norm.symm
  -- Chain the inequalities/equalities
  have h_main : ‖deriv riemannZeta s / riemannZeta s‖ ≤ ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := by
    calc
      ‖deriv riemannZeta s / riemannZeta s‖
          ≤ (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ s‖) := h1
      _ = (∑' n : ℕ, |ArithmeticFunction.vonMangoldt n| / ‖(n : ℂ) ^ (σ : ℂ)‖) := h_dep_ratio
      _ = ‖- deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ := h_sum_eq_norm_ratio
  -- Finally, remove the minus sign and rewrite s = σ + it
  simpa [s, norm_neg] using h_main

lemma lem_logDerivZetalogt32 :
  ∃ C : ℝ, C > 1 ∧
  ∀ t : ℝ, |t| > 3 →
    ∀ σ : ℝ,
      σ ≥ 3/2 →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤ C := by
  -- Obtain the constant from the real-axis bound near 1
  obtain ⟨C0, hC0_gt1, hC0_bound⟩ := Z0bound_const
  -- Choose a convenient constant C = C0 + 2
  refine ⟨C0 + 2, by linarith, ?_⟩
  intro t ht σ hσ
  -- Reduce to the real axis using the center bound
  have h_center := lem_zetacenterbd t σ hσ
  -- Set δ = σ - 1 (> 0 and ≥ 1/2)
  set δ : ℝ := σ - 1
  have hδ_pos : 0 < δ := by linarith [hσ]
  have hδ_ge_half : (1 / 2 : ℝ) ≤ δ := by linarith [hσ]
  -- Apply the constant bound near 1 on the real axis
  have hZ0 := hC0_bound δ hδ_pos
  -- Triangle inequality to bound ‖-logDerivZeta (1+δ)‖ by the sum of the two terms
  have h_tri : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤
      ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ + ‖(1 / (δ : ℂ))‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (norm_add_le (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) (1 / (δ : ℂ)))
  -- Bound ‖1/(δ : ℂ)‖ ≤ 2 using δ ≥ 1/2
  have h_norm_div_le_two : ‖(1 / (δ : ℂ))‖ ≤ 2 := by
    -- compute ‖1 / (δ:ℂ)‖ = 1 / ‖(δ:ℂ)‖ and ‖(δ:ℂ)‖ = |δ|
    have hnorm_div : ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      simp
    have hnorm_ofReal : ‖(δ : ℂ)‖ = |δ| := by
      simp
    -- From δ ≥ 1/2 > 0, get 1 / |δ| ≤ 2
    have h_abs_ge : (1 / 2 : ℝ) ≤ |δ| := by
      have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
      simpa [abs_of_nonneg hδ_nonneg] using hδ_ge_half
    have hhalfpos : (0 : ℝ) < 1 / 2 := by norm_num
    have hone_div_abs_le_two : 1 / |δ| ≤ 2 := by
      simpa using (one_div_le_one_div_of_le hhalfpos h_abs_ge)
    -- Conclude the bound on the complex norm
    have : 1 / ‖(δ : ℂ)‖ ≤ 2 := by simpa [hnorm_ofReal] using hone_div_abs_le_two
    -- rewrite ‖1/(δ:ℂ)‖ via hnorm_div
    have hnorm_div' : ‖(1 / (δ : ℂ))‖ = 1 / ‖(δ : ℂ)‖ := by
      simp [norm_one]
    simpa [hnorm_div'] using this
  -- Combine: first use the triangle inequality, then the Z0 bound, then the bound on ‖1/δ‖
  have h_real_axis_bound : ‖logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 := by
    have h1 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + ‖(1 / (δ : ℂ))‖ := by
      linarith [h_tri, hZ0]
    have h2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C0 + 2 := by
      linarith [h1, h_norm_div_le_two]
    simpa [norm_neg] using h2
  -- Rewrite ((1:ℂ)+δ) as σ
  have hσ_real : (1 : ℝ) + δ = σ := by
    simp [δ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hσ_eq : (1 : ℂ) + δ = (σ : ℂ) := by
    have : ((1 + δ : ℝ) : ℂ) = (σ : ℂ) := by simpa using congrArg Complex.ofReal hσ_real
    simpa [Complex.ofReal_add] using this
  have hR_bound : ‖deriv riemannZeta σ / riemannZeta σ‖ ≤ C0 + 2 := by
    -- logDerivZeta equals deriv ζ / ζ by definition
    simpa [logDerivZeta, hσ_eq] using h_real_axis_bound
  -- Conclude using the center bound
  exact le_trans h_center hR_bound

theorem thm_final_result :
  ∃ A : ℝ, A > 0 ∧ A < 1 ∧
  ∃ C : ℝ, C > 1 ∧
  ∀ t : ℝ, |t| > 3 →
    ∀ σ : ℝ,
      σ ≥ 1 - A / Real.log (abs t + 2) →
      ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖ ≤ C * (Real.log (abs t)) ^ 2 := by
  -- Apply lem_logDerivZetalogt2 and lem_logDerivZetalogt32 as suggested by informal proof
  obtain ⟨C₀, hC₀_pos, hC₀⟩ := lem_logDerivZetalogt0
  obtain ⟨C₃₂, hC₃₂_pos, hC₃₂⟩ := lem_logDerivZetalogt32

  -- Use A = zerofree_constant / 20 (this matches deltaz_t definition)
  use zerofree_constant / 20

  constructor
  · -- Prove A > 0
    apply div_pos zerofree_constant_pos
    norm_num

  constructor
  · -- Prove A < 1
    rw [div_lt_one (by norm_num : (0 : ℝ) < 20)]
    -- Need to show zerofree_constant < 20
    have h1 : zerofree_constant < 1 := zerofree_constant_lt_one
    linarith

  -- Use C = max C₀ C₃₂
  use max C₀ C₃₂

  constructor
  · -- Prove C > 1
    exact lt_max_of_lt_left hC₀_pos

  · -- Main bound
    intro t ht σ hσ

    -- Key insight: A / Real.log (abs t + 2) = deltaz_t t when A = zerofree_constant / 20
    have h_eq : zerofree_constant / 20 / Real.log (abs t + 2) = deltaz_t t := by
      unfold deltaz_t deltaz
      simp [Complex.mul_I_im]

    -- So the condition becomes σ ≥ 1 - deltaz_t t
    have hσ' : σ ≥ 1 - deltaz_t t := by
      rw [← h_eq]
      exact hσ

    by_cases h : σ ≥ 3/2
    · -- Case σ ≥ 3/2: use lem_logDerivZetalogt32
      have bound := hC₃₂ t ht σ h
      have hC_le : C₃₂ ≤ max C₀ C₃₂ := le_max_right _ _
      -- Need to show C₃₂ ≤ C₃₂ * (Real.log (abs t))^2
      have hlog_ge_one : 1 ≤ Real.log (abs t) := by
        have h_ge : Real.exp 1 ≤ abs t := by
          -- Since |t| > 3 and e < 3, we have e < |t|
          have he_lt_3 : Real.exp 1 < 3 := lem_three_gt_e  -- Use the existing lemma
          linarith [ht, abs_nonneg t]
        exact (Real.le_log_iff_exp_le (by linarith [abs_nonneg t])).2 h_ge
      have h_one_le_sq : 1 ≤ (Real.log (abs t)) ^ 2 := by
        have h_sq : (Real.log (abs t)) ^ 2 = Real.log (abs t) * Real.log (abs t) := by
          rw [pow_two]
        rw [h_sq]
        have h_mul : 1 * 1 ≤ Real.log (abs t) * Real.log (abs t) :=
          mul_self_le_mul_self (zero_le_one) hlog_ge_one
        simpa using h_mul
      have h_pos : 0 < C₃₂ := lt_trans zero_lt_one hC₃₂_pos
      calc ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖
        ≤ C₃₂ := bound
        _ = C₃₂ * 1 := by rw [mul_one]
        _ ≤ C₃₂ * (Real.log (abs t)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left h_one_le_sq (le_of_lt h_pos)
        _ ≤ max C₀ C₃₂ * (Real.log (abs t)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hC_le (sq_nonneg _)

    · -- Case σ < 3/2: use lem_logDerivZetalogt0
      push Not at h
      have h_conditions : 1 - deltaz_t t ≤ σ ∧ σ ≤ 3/2 ∧ t = t := by
        exact ⟨hσ', le_of_lt h, rfl⟩
      have bound := hC₀ t ht ⟨σ, t⟩ h_conditions
      have hC_le : C₀ ≤ max C₀ C₃₂ := le_max_left _ _
      calc ‖deriv riemannZeta (Complex.mk σ t) / riemannZeta (Complex.mk σ t)‖
        ≤ C₀ * Real.log |t| ^ 2 := bound
        _ ≤ max C₀ C₃₂ * Real.log |t| ^ 2 := by
          apply mul_le_mul_of_nonneg_right hC_le (sq_nonneg _)

lemma ZetaZeroFree_p :
    ∃ (A : ℝ) (_ : A ∈ Set.Ioc 0 (1 / 2)),
    ∀ (σ : ℝ)
    (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Set.Ico (1 - A / Real.log |t| ^ 1) 1),
    riemannZeta (σ + t * Complex.I) ≠ 0 := by
  -- Global zero location bound: zeros lie to the left of 1 - c / log(|Im|+2).
  -- Reuse the shared corpus quantitative zero-free region for `riemannZeta`
  -- (`BoundedGaps.Maynard.exists_nat_riemannZeta_zero_re_lt`) instead of
  -- re-deriving it from the local `zerofree` development.
  obtain ⟨M, hM2, hMbound⟩ := BoundedGaps.Maynard.exists_nat_riemannZeta_zero_re_lt
  set c : ℝ := 1 / (M : ℝ) ^ 2 with hcdef
  have hMR : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
  have hMpos : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le (by norm_num) hMR
  have hc_pos : 0 < c := by positivity
  have hbound : ∀ s : ℂ, riemannZeta s = 0 → s.re < 1 - c / Real.log (|s.im| + 2) := by
    intro s hs
    have hraw := hMbound s hs
    have heq : c / Real.log (|s.im| + 2) = 1 / ((M : ℝ) ^ 2 * Real.log (|s.im| + 2)) := by
      rw [hcdef, div_div]
    rwa [heq]
  -- Choose a universal constant A small enough
  let A0 : ℝ := min (1 / 2 : ℝ) (c / 2)
  let A : ℝ := min A0 ((1 / 4 : ℝ) * Real.log 3)
  have hA_pos : 0 < A := by
    have h1 : 0 < (1 / 2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc_pos this
    have hA0pos : 0 < A0 := lt_min_iff.mpr ⟨h1, h2⟩
    have hlog3pos : 0 < Real.log (3 : ℝ) :=
      (Real.log_pos_iff (by norm_num : (0 : ℝ) ≤ 3)).2 (by norm_num)
    have h3 : 0 < (1 / 4 : ℝ) * Real.log 3 := by
      exact mul_pos (by norm_num) hlog3pos
    exact lt_min_iff.mpr ⟨hA0pos, h3⟩
  have hA_le_half : A ≤ 1/2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_left _ _)
  have hA_le_c2 : A ≤ c / 2 := by
    have : A ≤ A0 := min_le_left _ _
    exact this.trans (min_le_right _ _)
  have hA_le_log3quarter : A ≤ (1 / 4 : ℝ) * Real.log 3 := min_le_right _ _
  refine ⟨A, ?_, ?_⟩
  · exact ⟨hA_pos, hA_le_half⟩
  · intro σ t htgt3 hσI hzero
    -- Notation for logs
    set L := Real.log |t| with hLdef
    set Lp := Real.log (|t| + 2) with hLpdef
    have hpos_abs : 0 ≤ |t| := abs_nonneg t
    have hLpos : 0 < L := (Real.log_pos_iff hpos_abs).2 (lt_trans (by norm_num) htgt3)
    have hLp_pos_arg : 0 < |t| + 2 := by linarith
    have hLp_pos : 0 < Lp := (Real.log_pos_iff (le_of_lt hLp_pos_arg)).2 (by linarith)
    -- From |t| > 3, we have log 3 ≤ L
    have hlog3_le_L : Real.log 3 ≤ L := by
      have h3pos : 0 < (3 : ℝ) := by norm_num
      have : (3 : ℝ) ≤ |t| := le_of_lt htgt3
      simpa [hLdef] using Real.log_le_log h3pos this
    -- Hence ((1/4) log 3)/L ≤ 1/4
    have hquarter_ratio_le : ((1 / 4 : ℝ) * Real.log 3) / L ≤ (1 / 4 : ℝ) := by
      have h := div_le_div_of_nonneg_right hlog3_le_L (le_of_lt hLpos)
      have h' := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1/4)
      have hne : L ≠ 0 := ne_of_gt hLpos
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hne] using h'
    -- Therefore A/L ≤ 1/4
    have hA_over_le_quarter : A / L ≤ (1 / 4 : ℝ) := by
      have := div_le_div_of_nonneg_right hA_le_log3quarter (le_of_lt hLpos)
      exact this.trans hquarter_ratio_le
    -- Deduce σ ≥ 3/4 > 0 and σ < 1
    have hlow : 1 - A / L ≤ σ := by simpa [hLdef, pow_one] using hσI.1
    have hσ_ge_34 : (3 / 4 : ℝ) ≤ σ := by
      have : (3 / 4 : ℝ) ≤ 1 - A / L := by linarith
      exact this.trans hlow
    have hσ_pos : 0 < σ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < (3/4 : ℝ)) hσ_ge_34
    have hσ_lt_one : σ < 1 := hσI.2
    -- Show Lp < 2L
    have hlog_lt : Lp < 2 * L := by
      have h1 : 0 < |t| - 2 := by linarith
      have h2 : 0 < |t| + 1 := by linarith
      have hprod_pos : 0 < (|t| - 2) * (|t| + 1) := mul_pos h1 h2
      have hpoly : |t| * |t| - (|t| + 2) = (|t| - 2) * (|t| + 1) := by ring
      have hlt : |t| + 2 < |t| * |t| := by
        calc
          |t| + 2 < |t| + 2 + (|t| - 2) * (|t| + 1) := by linarith [hprod_pos]
          _ = |t| * |t| := by rw [← hpoly]; ring
      have hposb : 0 < |t| + 2 := by linarith
      have hlog_lt' : Real.log (|t| + 2) < Real.log (|t| * |t|) := Real.log_lt_log hposb hlt
      have hlogmul : Real.log (|t| ^ 2) = 2 * Real.log |t| := Real.log_pow |t| 2
      calc
        Lp = Real.log (|t| + 2) := by simp [hLpdef]
        _ < Real.log (|t| * |t|) := hlog_lt'
        _ = Real.log (|t| ^ 2) := by simp [pow_two]
        _ = 2 * Real.log |t| := by simp
        _ = 2 * L := by simp [hLdef]
    -- Then 1/(2L) < 1/Lp, hence (c/2)/L < c/Lp
    have h_inv_comp : 1 / (2 * L) < 1 / Lp := one_div_lt_one_div_of_lt hLp_pos hlog_lt
    have hstep2 : (c / 2) / L < c / Lp := by
      have hcpos' : 0 < c := hc_pos
      have : c * (1 / (2 * L)) < c * (1 / Lp) := mul_lt_mul_of_pos_left h_inv_comp hcpos'
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
    -- From A ≤ c/2, we have A/L ≤ (c/2)/L
    have hstep1 : A / L ≤ (c / 2) / L := by
      have := div_le_div_of_nonneg_right hA_le_c2 (le_of_lt hLpos)
      simpa [div_eq_mul_inv] using this
    have hstrict_div : A / L < c / Lp := lt_of_le_of_lt hstep1 hstep2
    -- Hence σ > 1 - c/Lp by the interval's lower bound
    have hσ_gt : 1 - c / Lp < σ := by
      have hneg' : - (c / Lp) < - (A / L) := by simpa [neg_div] using neg_lt_neg hstrict_div
      have : 1 - c / Lp < 1 - A / L := by linarith [hneg']
      exact this.trans_le hlow
    -- Contradiction with the zero location bound reused from the shared corpus module.
    let s : ℂ := Complex.mk σ t
    have hs_zero : riemannZeta s = 0 := by simpa [s, Complex.mk_eq_add_mul_I] using hzero
    have hbound_applied : s.re < 1 - c / Real.log (|s.im| + 2) := hbound s hs_zero
    have hlt : σ < 1 - c / Lp := by simpa [s, hLpdef] using hbound_applied
    linarith [hσ_gt, hlt]

lemma LogDerivZetaBndUnif2 :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 1)), ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      C * Real.log |t| ^ 2 := by
  classical
  obtain ⟨c, hc, hc2, K, hK, hfinal⟩ := thm_final_result
  -- Choose constants
  let A : ℝ := min (1/2 : ℝ) (c / 2)
  have hApos : 0 < A := by
    have h1 : 0 < (1/2 : ℝ) := by norm_num
    have h2 : 0 < c / 2 := by
      have : 0 < (2 : ℝ) := by norm_num
      exact div_pos hc this
    exact (lt_min_iff).2 ⟨h1, h2⟩
  have hAle : A ≤ (1/2 : ℝ) := min_le_left _ _
  have hA_in : A ∈ Ioc 0 (1/2) := ⟨hApos, hAle⟩
  let C : ℝ := K
  have hCpos : 0 < C := by
    have hKpos : 0 < K := lt_trans (by norm_num : (0 : ℝ) < 1) hK
    exact hKpos
  refine ⟨A, hA_in, C, hCpos, ?_⟩
  intro σ t htgt3 hσI
  -- Notation for logs
  let x := |t|
  have hxpos : 0 ≤ x := abs_nonneg t
  have hxgt3 : 3 < x := htgt3
  let L := Real.log x
  let L' := Real.log (x + 2)
  have hLpos : 0 < L := (Real.log_pos_iff hxpos).2 (lt_trans (by norm_num) hxgt3)
  have hL'pos : 0 < L' :=
    (Real.log_pos_iff (by linarith : 0 ≤ x + 2)).2 (by linarith [hxpos, hxgt3])
  -- From the Ici-bound we have σ ≥ 1 - A / L
  have hσ_ge : 1 - A / L ≤ σ := by simpa [pow_one, L, x] using hσI
  -- Show L' < 2L
  have hprod_pos : 0 < (x - 2) * (x + 1) := by
    have hxgt2 : (2 : ℝ) < x := lt_trans (by norm_num) hxgt3
    exact mul_pos (sub_pos.mpr hxgt2) (add_pos_of_nonneg_of_pos hxpos (by norm_num))
  have hdiff_pos : 0 < x ^ 2 - (x + 2) := by
    have hpoly : x ^ 2 - (x + 2) = (x - 2) * (x + 1) := by ring
    simpa [hpoly] using hprod_pos
  have hlt_sq : x + 2 < x ^ 2 := by linarith
  have hlog_lt : L' < Real.log (x ^ 2) :=
    Real.log_lt_log (by linarith : 0 < x + 2) hlt_sq
  have hlog_pow : Real.log (x ^ 2) = 2 * L := by
    simp [L]
  have hL'_lt_2L : L' < 2 * L := by simpa [L', hlog_pow]
    using hlog_lt
  -- Build strict inequality A/L < c/L'
  have hA_le_c2 : A ≤ c / 2 := min_le_right _ _
  have hstep0 : A / L ≤ (c / 2) / L :=
    div_le_div_of_nonneg_right hA_le_c2 (le_of_lt hLpos)
  have hrecip : 1 / (2 * L) < 1 / L' :=
    one_div_lt_one_div_of_lt hL'pos hL'_lt_2L
  have hmul : c * (1 / (2 * L)) < c * (1 / L') :=
    mul_lt_mul_of_pos_left hrecip hc
  have hstep2 : (c / 2) / L < c / L' := by
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hmul
  have hineq : A / L < c / L' := lt_of_le_of_lt hstep0 hstep2
  have hσ_gt : σ > 1 - c / L' := by
    have : 1 - c / L' < 1 - A / L := by linarith [hineq]
    exact lt_of_lt_of_le this hσ_ge
  -- Apply the global bound from thm_final_result
  have hmain' : ‖(deriv riemannZeta) (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤
      K * (Real.log |t|) ^ 2 := by
    have h_eq : σ + t * Complex.I = Complex.mk σ t := by
      rw [Complex.mk_eq_add_mul_I]
    rw [h_eq]
    have hσ_ge_required : σ ≥ 1 - c / Real.log (abs t + 2) := by
      have h_abs_eq : abs t = |t| := by simp
      rw [h_abs_eq]
      exact le_of_lt hσ_gt
    exact hfinal t htgt3 σ hσ_ge_required
  -- The bound is already what we need since C = K
  simpa [C, L, x] using hmain'

end ZetaZeroFreeRegion
