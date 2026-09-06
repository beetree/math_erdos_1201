module

public import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.VonMangoldtSeriesPositivityBounds

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
Establishes the classical de la Vallée Poussin zero-free region for `riemannZeta`:
combining the `3+4cos+cos2` trigonometric positivity of the von Mangoldt Dirichlet
series (`Z341pos`) with the explicit bound `lem341tsC` yields a constant `c > 0`
such that every zero `s` with `|Im s| > 2` satisfies `Re s ≤ 1 - c / log(|Im s|+2)`
(`zerofree`). This is then repackaged as an explicit distance-from-the-line-`Re=1`
function `deltaz` and used to show `ζ` has no zeros with `Re z > 1 - 9·δ(z)`
(`lem_ZFRdelta`), together with finiteness of zero sets in compact regions
(via `riemannZeta_zeros_finite_of_compact`, resting on the simple pole at `1` and
isolation of zeros) and geometric placement lemmas locating zero-free rectangles
around the critical strip (`lem_ZFRinD`, `lem_ZFRnotK`, `lem_Zeta_Expansion_ZFR`).
-/

public section

namespace ZetaZeroFreeRegion

open Complex Topology Filter Interval Set Asymptotics ZetaFunctionEstimates AnalyticZeroCounting


lemma lem_341series2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
     4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
     (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re)
    =
    ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  rw [Z341series t delta hdelta]
  exact lem341series t delta hdelta

lemma lem_Lambda_pos_trig_sum (n : ℕ) (delta : ℝ) (t : ℝ) (hn : n ≥ 1) (hdelta : delta > 0) :
    0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply mul_nonneg
  · -- Show ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + delta)) ≥ 0
    apply lem_realnx n (1 + delta) hn
    -- Show 1 + delta ≥ 1
    linarith [hdelta]
  · -- Show 3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ)) ≥ 0
    exact DiskAnalyticBounds.lem_postriglogn n hn t


lemma lem_seriespos (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    0 ≤ ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  apply tsum_nonneg
  intro n
  by_cases h : n = 0
  · -- Case n = 0: von Mangoldt function is 0, so the term is 0
    simp [h, ArithmeticFunction.vonMangoldt_apply]
  · -- Case n ≠ 0: apply lem_Lambda_pos_trig_sum
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact lem_Lambda_pos_trig_sum n delta t hn hdelta

lemma Z341pos (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    0 ≤ 3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
        4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
        (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re := by
  rw [lem_341series2 t delta hdelta]
  exact lem_seriespos t delta hdelta



lemma pos_delta_from_C_L {C L : ℝ} (hC : 0 < C) (hL : 0 < L) : 0 < 1 / (2 * C * L) := by
  have hCL : 0 < C * L := mul_pos hC hL
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hpos : 0 < 2 * C * L := by
    have : 0 < 2 * (C * L) := mul_pos h2 hCL
    simpa [mul_assoc] using this
  exact one_div_pos.mpr hpos


lemma two_C_log_pos {C t : ℝ} (hC : 0 < C) : 0 < 2 * C * Real.log (|t| + 2) := by
  have hL : 0 < Real.log (|t| + 2) := Real.log_pos (by nlinarith [abs_nonneg t])
  have h2 : 0 < (2 : ℝ) := by norm_num
  have hCL : 0 < C * Real.log (|t| + 2) := mul_pos hC hL
  have : 0 < 2 * (C * Real.log (|t| + 2)) := mul_pos h2 hCL
  simpa [mul_comm, mul_left_comm, mul_assoc] using this


lemma mul_one_div_mul_right {A b : ℝ} (hA : A ≠ 0) : A * (1 / (A * b)) = 1 / b := by
  calc
    A * (1 / (A * b)) = A * ((A * b)⁻¹) := by simp [one_div]
    _ = A / (A * b) := by simp [div_eq_mul_inv]
    _ = A / A / b := by
      simpa using (div_mul_eq_div_div (a := A) (b := A) (c := b))
    _ = 1 / b := by
      have : A / A = (1 : ℝ) := by simp [hA]
      simp [this]



lemma rhs_eval_of_inv (C L δ : ℝ) (h : 1 / δ = 2 * C * L) : 3 / δ + C * L = 7 * C * L := by
  calc
    3 / δ + C * L
        = 3 * (1 / δ) + C * L := by simp [div_eq_mul_inv, one_div]
    _   = 3 * (2 * C * L) + C * L := by simp [h]
    _   = 6 * C * L + C * L := by ring
    _   = 7 * C * L := by ring

lemma lem341tsC :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
    4 / (1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2))) ≤ 7 * C * Real.log (abs s.im + 2) := by
  -- Get the constant C from Z341bounds_const
  obtain ⟨C, hCpos, hbound⟩ := Z341bounds_const
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTim

  -- Define L = log(|s.im| + 2) and δ = 1/(2CL)
  let L : ℝ := Real.log (|s.im| + 2)
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by nlinarith [abs_nonneg s.im])
  let δ : ℝ := 1 / (2 * C * L)

  -- Show δ > 0
  have hCpos_weak : 0 < C := lt_trans zero_lt_one hCpos
  have hδpos : 0 < δ := pos_delta_from_C_L hCpos_weak hLpos

  -- Show δ < 1: need 1 < 2*C*L
  have hδlt : δ < 1 := by
    -- Since |s.im| > 3, we have L > log(5) > 1
    have hL_gt_1 : 1 < L := by
      have h5_lt : 4 < |s.im| + 2 := by linarith [hTim]
      have hL_gt_log5 : Real.log 4 < L := Real.log_lt_log (by norm_num) h5_lt
      have hlog5_gt_1 : 1 < Real.log 4 := by
        have h5_gt_e : Real.exp 1 < 4 := by
          have h3_gt_e := lem_three_gt_e
          linarith [h3_gt_e]
        rw [← Real.log_exp 1]
        exact Real.log_lt_log (Real.exp_pos 1) h5_gt_e
      linarith [hlog5_gt_1, hL_gt_log5]
    -- Now 2*C*L > 2*1*1 = 2 > 1 since C > 1 and L > 1
    have h2CL_gt_1 : 1 < 2 * C * L := by
      -- Since C > 1 and L > 1, we have C*L > 1*1 = 1, so 2*C*L > 2*1 = 2 > 1
      have hCL_gt_1 : 1 < C * L := by
        calc C * L
          > 1 * L := by exact mul_lt_mul_of_pos_right hCpos hLpos
          _ = L := by simp
          _ > 1 := hL_gt_1
      have h2_pos : (0 : ℝ) < 2 := by norm_num
      calc 2 * C * L
        = 2 * (C * L) := by ring
        _ > 2 * 1 := by exact mul_lt_mul_of_pos_left hCL_gt_1 h2_pos
        _ = 2 := by simp
        _ > 1 := by norm_num
    -- Therefore δ = 1/(2*C*L) < 1
    simp only [δ]
    rw [div_lt_one_iff]
    left
    exact ⟨two_C_log_pos hCpos_weak, h2CL_gt_1⟩

  -- Apply Z341bounds_const
  have hmem : (s.re + s.im * Complex.I) ∈ zeroZ := by
    simpa [Complex.re_add_im] using hs.1
  have hupper := hbound δ hδpos hδlt (s.im) hTim (s.re) hmem

  -- Apply Z341pos for non-negativity
  have hpos := Z341pos (s.im) δ hδpos

  -- Combine: 0 ≤ LHS ≤ RHS, so rearranging gives the desired inequality
  have hRHS_nonneg : 0 ≤ 3 / δ - 4 / (1 + δ - s.re) + C * L := le_trans hpos hupper
  have hineq1 : 4 / (1 + δ - s.re) ≤ 3 / δ + C * L := by linarith [hRHS_nonneg]

  -- Rewrite denominator: 1 + δ - s.re = 1 - s.re + δ
  have hineq2 : 4 / (1 - s.re + δ) ≤ 3 / δ + C * L := by
    convert hineq1 using 2
    ring

  -- Substitute δ = 1/(2CL) and use rhs_eval_of_inv
  have hinv : 1 / δ = 2 * C * L := by
    simp only [δ, one_div, inv_inv]

  have hrhs_eval : 3 / δ + C * L = 7 * C * L := rhs_eval_of_inv C L δ hinv

  have hfinal : 4 / (1 - s.re + δ) ≤ 7 * C * L := by
    rw [← hrhs_eval]
    exact hineq2

  -- The goal is exactly what we have with L and δ substituted
  convert hfinal


lemma div_le_to_le_mul (x y z : ℝ) (hy : 0 < y) (h : x / y ≤ z) : x ≤ z * y := by
  rwa [div_le_iff₀ hy] at h

lemma le_mul_to_le_div (x y z : ℝ) (hy : 0 < y) (h : x ≤ z * y) : x / y ≤ z := by
  rw [div_le_iff₀ hy]
  exact h

lemma reciprocal_div_inequality (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : 4 / a ≤ b) : a ≥ 4 / b := by
  -- From 4/a ≤ b, multiply both sides by a > 0 to get 4 ≤ b * a
  have h1 : 4 ≤ b * a := div_le_to_le_mul 4 a b ha h
  -- Use commutativity to get 4 ≤ a * b
  have h2 : 4 ≤ a * b := by
    rwa [mul_comm] at h1
  -- From 4 ≤ a * b, divide both sides by b > 0 to get 4/b ≤ a
  have h3 : 4 / b ≤ a := le_mul_to_le_div 4 b a hb h2
  -- This is exactly what we want to prove (a ≥ 4/b is the same as 4/b ≤ a)
  exact h3


lemma lem341tsC2 :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
          1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2)) ≥ 4 / (7 * C * Real.log (abs s.im + 2)) := by
  -- Obtain the constant and bound from lem341tsC
  rcases lem341tsC with ⟨C, hCpos, hT⟩
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTs
  -- Define a and b to apply reciprocal_div_inequality
  set a := 1 - s.re + 1 / (2 * C * Real.log (abs s.im + 2)) with ha
  set b := 7 * C * Real.log (abs s.im + 2) with hb
  have hineq : 4 / a ≤ b := by
    simpa [ha, hb] using hT s hs hTs
  -- Show b &gt; 0
  have h_abs_nonneg : 0 ≤ |s.im| := abs_nonneg _
  have h_two_le : (2 : ℝ) ≤ |s.im| + 2 := by
    linarith [h_abs_nonneg]
  have h_one_lt : (1 : ℝ) < |s.im| + 2 := lt_of_lt_of_le one_lt_two h_two_le
  have hx0 : 0 ≤ |s.im| + 2 := by linarith [h_abs_nonneg]
  have hlogpos : 0 < Real.log (|s.im| + 2) := (Real.log_pos_iff hx0).2 h_one_lt
  have h7pos : 0 < (7 : ℝ) := by exact_mod_cast (by decide : (0 : ℕ) < 7)
  have hbpos : 0 < b := by
    have h7Cpos : 0 < 7 * C := by linarith
    exact mul_pos h7Cpos hlogpos
  -- Show a &gt; 0
  rcases hs with ⟨_, hRepos, hRelt⟩
  have h1 : 0 < 1 - s.re := sub_pos.mpr hRelt
  have h2pos : 0 < (2 : ℝ) := lt_trans zero_lt_one one_lt_two
  have h2Cpos : 0 < (2 : ℝ) * C := by linarith
  have hdenpos : 0 < 2 * C * Real.log (|s.im| + 2) := mul_pos h2Cpos hlogpos
  have hinvpos : 0 < 1 / (2 * C * Real.log (|s.im| + 2)) := one_div_pos.mpr hdenpos
  have hapos : 0 < a := by
    have := add_pos h1 hinvpos
    simpa [ha] using this
  -- Apply reciprocal_div_inequality to flip the inequality
  have hres := reciprocal_div_inequality a b hapos hbpos hineq
  simpa [ha, hb] using hres

lemma simplify_4_7_2 (C L : ℝ) : 4 / (7 * C * L) - 1 / (2 * C * L) = 1 / (14 * C * L) := by
  -- Regroup the products in the denominators
  have h1 : (4 : ℝ) / (7 * (C * L)) = (4 : ℝ) / (7 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (4 : ℝ)) (b := (7 : ℝ)) (c := C * L))
  have h2 : (1 : ℝ) / (2 * (C * L)) = (1 : ℝ) / (2 : ℝ) / (C * L) := by
    simpa using (div_mul_eq_div_div (a := (1 : ℝ)) (b := (2 : ℝ)) (c := C * L))
  -- Compute the scalar difference (4/7 - 1/2) = 1/14
  have h3' : ((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹ = (14 : ℝ)⁻¹ := by
    have h3 : ((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ)) = (1 : ℝ) / (14 : ℝ) := by
      norm_num
    simpa [one_div] using h3
  calc
    4 / (7 * C * L) - 1 / (2 * C * L)
        = (4 : ℝ) / (7 * (C * L)) - (1 : ℝ) / (2 * (C * L)) := by
          simp [mul_assoc]
    _ = (4 : ℝ) / (7 : ℝ) / (C * L) - (1 : ℝ) / (2 : ℝ) / (C * L) := by
          simp [h1, h2]
    _ = (((4 : ℝ) / (7 : ℝ)) - ((1 : ℝ) / (2 : ℝ))) / (C * L) := by
          simpa using (sub_div (a := ((4 : ℝ) / (7 : ℝ))) (b := ((1 : ℝ) / (2 : ℝ))) (c := C * L)).symm
    _ = (((4 : ℝ) / (7 : ℝ)) - (2 : ℝ)⁻¹) / (C * L) := by
          simp [one_div]
    _ = (14 : ℝ)⁻¹ / (C * L) := by
          simp [h3']
    _ = 1 / (14 * (C * L)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc, one_div] using
            (div_mul_eq_div_div (a := (1 : ℝ)) (b := (14 : ℝ)) (c := C * L)).symm
    _ = 1 / (14 * C * L) := by simp [mul_assoc]

lemma fraction_diff_lower_bound (C L a : ℝ) : 4 / (7 * C * L) ≤ a + 1 / (2 * C * L) → 1 / (14 * C * L) ≤ a := by
  intro h
  have h' : 4 / (7 * C * L) - 1 / (2 * C * L) ≤ a := (sub_le_iff_le_add).mpr h
  have hdiff : 1 / (14 * C * L) = 4 / (7 * C * L) - 1 / (2 * C * L) := by
    symm
    exact simplify_4_7_2 C L
  calc
    1 / (14 * C * L)
        = 4 / (7 * C * L) - 1 / (2 * C * L) := hdiff
    _ ≤ a := h'

lemma lem341tsC3 :
    ∃ C > 1, ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| →
    1 - s.re ≥ 1 / (14 * C * Real.log (abs s.im + 2)) := by
  obtain ⟨C, hCpos, hT⟩ := lem341tsC2
  refine ⟨C, hCpos, ?_⟩
  intro s hs hTle
  have h := hT s hs hTle
  -- Convert the inequality to the form required by fraction_diff_lower_bound
  have h' : 4 / (7 * C * Real.log (abs s.im + 2)) ≤
      (1 - s.re) + 1 / (2 * C * Real.log (abs s.im + 2)) := by
    simpa [ge_iff_le, add_comm, add_left_comm, add_assoc] using h
  -- Apply the algebraic rearrangement lemma
  have h'' := fraction_diff_lower_bound C (Real.log (abs s.im + 2)) (1 - s.re) h'
  -- Conclude
  simpa [ge_iff_le, mul_comm, mul_left_comm, mul_assoc] using h''



lemma zerofree :
    ∃ c, c > 0 ∧ c < 1 ∧ ∀ s : ℂ,
        (s ∈ zeroZ ∧ 0 < s.re ∧ s.re < 1) →
          2 < |s.im| → s.re ≤ 1 - c / (Real.log (abs s.im + 2)) := by
  -- Obtain the inequality from lem341tsC3
  rcases lem341tsC3 with ⟨C0, hC0pos, hT⟩
  -- Define the final constant C := 1 / (14 * C0)
  set C : ℝ := 1 / (14 * C0) with hCdef
  -- Show C > 0
  have h14pos : 0 < (14 : ℝ) := by norm_num
  have hC0pos' : 0 < C0 := lt_trans zero_lt_one hC0pos
  have hCpos : 0 < C := by
    have hdenpos : 0 < 14 * C0 := mul_pos h14pos hC0pos'
    exact one_div_pos.mpr hdenpos
  -- Show C < 1: Since C0 > 1, we have 14 * C0 > 14 > 1, so C = 1/(14*C0) < 1
  have hClt1 : C < 1 := by
    have h14C0_pos : 0 < 14 * C0 := mul_pos h14pos hC0pos'
    have h14C0_gt_1 : 1 < 14 * C0 := by
      have h14_gt_1 : (1 : ℝ) < 14 := by norm_num
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ < 14 * 1 := by exact mul_lt_mul_of_pos_right h14_gt_1 zero_lt_one
        _ < 14 * C0 := by exact mul_lt_mul_of_pos_left hC0pos h14pos
    rw [hCdef]
    rw [div_lt_one_iff]
    left
    exact ⟨h14C0_pos, h14C0_gt_1⟩
  -- Provide constants and prove the desired bound
  refine ⟨C, hCpos, hClt1, ?_⟩
  intro s hs hTle
  -- Let L denote the logarithm term
  set L := Real.log (abs s.im + 2) with hLdef
  -- From lem341tsC3 we have: 1 / (14 * C0 * L) ≤ 1 - s.re
  have hb0 := hT s hs hTle
  -- Rewrite the bound to match C / L on the left
  have hb' : C / L ≤ 1 - s.re := by
    simpa [hLdef, hCdef, one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hb0
  -- Rearranging gives the desired inequality
  have : s.re ≤ 1 - C / L := by linarith
  simpa [hLdef] using this


/--
For $t\in\R$ and $\delta >0$, define
$\mathcal{Y}_t(\delta) = \{\rho_1\in\C : \zeta(\rho_1) = 0 \,\text{and} \, |\rho_1-(1-\delta+it)|\le \delta/2\}.$
-/
@[expose] def Yt (t : ℝ) (δ : ℝ) : Set ℂ :=
  { ρ_1 : ℂ | riemannZeta ρ_1 = 0 ∧ ‖ρ_1 - (1 - δ + t * Complex.I)‖ ≤ 2 * δ }

-- The constant a from the zerofree lemma
@[expose] noncomputable def zerofree_constant : ℝ := Classical.choose zerofree

lemma zerofree_constant_pos : 0 < zerofree_constant :=
  (Classical.choose_spec zerofree).1

lemma zerofree_constant_lt_one : zerofree_constant < 1 :=
  (Classical.choose_spec zerofree).2.1

@[expose] noncomputable def deltaz (z : ℂ) : ℝ := (zerofree_constant / 20) / Real.log (|z.im| + 2)

@[expose] noncomputable def deltaz_t (t : ℝ) : ℝ := deltaz (t * Complex.I)

-- For z∈ℂ we have 0<δ(z)<1/9. For t∈ℝ we have 0<δ_t<1/9.
lemma lem_delta19 :
  (∀ z : ℂ, |z.im| > 2 → (0 < deltaz z ∧ deltaz z < 1/9)) ∧
  (∀ t : ℝ, |t| > 2 → (0 < deltaz_t t ∧ deltaz_t t < 1/9)) := by
  -- First, prove the result for complex z
  have h_complex : ∀ z : ℂ, |z.im| > 2 → (0 < deltaz z ∧ deltaz z < 1/9) := by
    intro z hz
    constructor
    · -- Show 0 < deltaz z
      have h_num_pos : 0 < zerofree_constant / 20 := by
        exact div_pos zerofree_constant_pos (by norm_num)
      have h_den_pos : 0 < Real.log (|z.im| + 2) := by
        have h_gt_one : (1 : ℝ) < |z.im| + 2 := by
          have h_nonneg : (0 : ℝ) ≤ |z.im| := abs_nonneg _
          linarith [hz]
        exact Real.log_pos h_gt_one
      unfold deltaz
      exact div_pos h_num_pos h_den_pos
    · -- Show deltaz z < 1/9
      -- First establish the key bounds
      have h_den_ge_half : (1/2 : ℝ) ≤ Real.log (|z.im| + 2) := by
        -- log(|z.im| + 2) ≥ log(2) ≥ 1/2
        have h_den_ge_log2 : Real.log 2 ≤ Real.log (|z.im| + 2) := by
          have h_pos : 0 < |z.im| + 2 := by linarith [abs_nonneg (z.im)]
          have h_le : (2 : ℝ) ≤ |z.im| + 2 := by linarith [abs_nonneg (z.im)]
          exact Real.log_le_log (by norm_num) h_le
        -- Show log 2 ≥ 1/2 using exp(1/2) ≤ 2
        have h_log2_ge_half : (1/2 : ℝ) ≤ Real.log 2 := by
          have h_exp_half_le_two : Real.exp (1/2) ≤ 2 := by
            -- exp(1/2)^2 = exp(1) < 3 < 4 = 2^2, so exp(1/2) < 2
            have h_exp_one_lt_three : Real.exp 1 < 3 := lem_three_gt_e
            have h_exp_sq : (Real.exp (1/2))^2 = Real.exp 1 := by
              rw [pow_two, ← Real.exp_add]; norm_num
            have h_exp_sq_lt_four : (Real.exp (1/2))^2 < 4 := by
              rw [h_exp_sq]; linarith [h_exp_one_lt_three]
            -- Use sq_lt_sq to get exp(1/2) < 2
            have h_exp_pos : 0 ≤ Real.exp (1/2) := le_of_lt (Real.exp_pos _)
            have h_two_pos : 0 ≤ (2 : ℝ) := by norm_num
            have h_four_eq : (2 : ℝ)^2 = 4 := by norm_num
            rw [← h_four_eq] at h_exp_sq_lt_four
            have h_lt_abs := (sq_lt_sq).mp h_exp_sq_lt_four
            rw [abs_of_nonneg h_exp_pos, abs_of_nonneg h_two_pos] at h_lt_abs
            exact le_of_lt h_lt_abs
          exact (Real.le_log_iff_exp_le (by norm_num : 0 < (2 : ℝ))).mpr h_exp_half_le_two
        exact le_trans h_log2_ge_half h_den_ge_log2
      -- Now get the bound on the reciprocal
      have h_inv_le_two : 1 / Real.log (|z.im| + 2) ≤ 2 := by
        have h_pos_half : 0 < (1/2 : ℝ) := by norm_num
        have h_ineq := one_div_le_one_div_of_le h_pos_half h_den_ge_half
        have h_eq : (1 : ℝ) / (1 / 2) = 2 := by norm_num
        linarith [h_ineq, h_eq]
      -- Now bound deltaz z
      have h_bound : deltaz z ≤ zerofree_constant / 10 := by
        have h_num_nonneg : 0 ≤ zerofree_constant / 20 := by
          exact le_of_lt (div_pos zerofree_constant_pos (by norm_num))
        have h_mul_ineq : (zerofree_constant / 20) * (1 / Real.log (|z.im| + 2)) ≤ (zerofree_constant / 20) * 2 :=
          mul_le_mul_of_nonneg_left h_inv_le_two h_num_nonneg
        have h_lhs_eq : deltaz z = (zerofree_constant / 20) * (1 / Real.log (|z.im| + 2)) := by
          unfold deltaz; ring
        have h_rhs_eq : (zerofree_constant / 20) * 2 = zerofree_constant / 10 := by ring
        rw [h_lhs_eq, ← h_rhs_eq]
        exact h_mul_ineq
      -- Final bound: zerofree_constant / 10 < 1/10 < 1/9
      have h_lt_tenth : zerofree_constant / 10 < 1 / 10 := by
        exact div_lt_div_of_pos_right zerofree_constant_lt_one (by norm_num)
      have h_tenth_lt_ninth : (1 : ℝ) / 10 < 1 / 9 := by norm_num
      exact lt_trans (lt_of_le_of_lt h_bound h_lt_tenth) h_tenth_lt_ninth

  -- Now construct the main result
  constructor
  · exact h_complex
  · -- For real t
    intro t ht
    -- Use deltaz_t t = deltaz (t * Complex.I) and |(t * Complex.I).im| = |t|
    have h_eq : deltaz_t t = deltaz (t * Complex.I) := rfl
    rw [h_eq]
    have h_im_eq : |(t * Complex.I).im| = |t| := by simp [Complex.mul_I_im]
    rw [← h_im_eq] at ht
    exact h_complex (t * Complex.I) ht

lemma riemannZeta_no_zeros_accumulate_at_one :
  ∀ Z : Set ℂ, (∀ z ∈ Z, riemannZeta z = 0) → ¬AccPt 1 (Filter.principal Z) := by
  intro Z hZ
  -- Prove by contradiction
  by_contra h_acc

  -- The key fact from the informal proof: riemannZeta has a simple pole at 1 with residue 1
  -- This means (s - 1) * riemannZeta s → 1 as s → 1 (s ≠ 1)
  have h_residue := riemannZeta_residue_one

  -- From the residue formula, for ε = 1/2, there exists δ > 0 such that
  -- for all s with s ≠ 1 and dist(s, 1) < δ, we have dist((s - 1) * riemannZeta s, 1) < 1/2
  rw [Metric.tendsto_nhdsWithin_nhds] at h_residue
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := h_residue (1/2) (by norm_num : (0 : ℝ) < 1/2)

  -- AccPt 1 (principal Z) means 1 is an accumulation point of Z
  -- By accPt_iff_nhds, for every neighborhood U of 1, there exists y ∈ U ∩ Z with y ≠ 1
  rw [accPt_iff_nhds] at h_acc

  -- Apply this to the ball of radius δ around 1
  obtain ⟨y, ⟨hy_ball, hy_Z⟩, hy_ne⟩ := h_acc (Metric.ball 1 δ) (Metric.ball_mem_nhds 1 hδ_pos)

  -- y is a zero of riemannZeta
  have hy_zero : riemannZeta y = 0 := hZ y hy_Z

  -- y is in the complement of {1}, i.e., y ≠ 1
  have hy_in_compl : y ∈ ({1} : Set ℂ)ᶜ := by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact hy_ne

  have hy_dist : dist y 1 < δ := hy_ball

  -- Apply the residue bound
  have h_bound := hδ_bound hy_in_compl hy_dist

  -- We have dist((y - 1) * riemannZeta y, 1) < 1/2
  -- But riemannZeta y = 0, so (y - 1) * riemannZeta y = 0
  -- Thus dist(0, 1) < 1/2
  rw [hy_zero, mul_zero] at h_bound

  -- Now dist(0, 1) in ℂ equals |0 - 1| = |-1| = |1| = 1
  have h_dist_eq : dist (0 : ℂ) (1 : ℂ) = 1 := by
    rw [Complex.dist_eq]
    norm_num

  rw [h_dist_eq] at h_bound
  -- This gives 1 < 1/2, which is a contradiction
  norm_num at h_bound

lemma eventually_eq_zero_implies_frequently_eq_zero_punctured (f : ℂ → ℂ) (z₀ : ℂ) :
  (∀ᶠ z in nhds z₀, f z = 0) → (∃ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0) := by
  intro h_eventually
  -- Following the informal proof:
  -- If f is eventually zero in a neighborhood of z₀, there exists an open set U
  -- containing z₀ where f is zero. Since U is open and contains z₀, it must contain
  -- infinitely many points different from z₀. All these points satisfy f(z) = 0
  -- and are in the punctured neighborhood, so f is frequently zero there.

  -- The punctured neighborhood is NeBot (non-trivial) for complex numbers
  -- Using the standard notation 𝓝[≠] for punctured neighborhoods
  have h_nebot : Filter.NeBot (nhdsWithin z₀ {z₀}ᶜ) := by
    -- Complex numbers form a normed field, so punctured neighborhoods are NeBot
    exact NormedField.nhdsNE_neBot z₀

  -- Since nhdsWithin z₀ {z₀}ᶜ ≤ nhds z₀, if f is eventually zero in nhds z₀,
  -- it's also eventually zero in nhdsWithin z₀ {z₀}ᶜ
  have h_eventually_punctured : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, f z = 0 := by
    -- Use the fact that nhdsWithin is smaller than nhds
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds h_eventually

  -- In a NeBot filter, if something is eventually true, it's frequently true
  exact h_eventually_punctured.frequently

lemma riemannZeta_zeros_finite_of_compact (K : Set ℂ) (hK : IsCompact K) :
    {z ∈ K | riemannZeta z = 0}.Finite := by
  -- The proof follows from the fact that zeros of meromorphic functions are isolated
  -- and isolated points in a compact set must be finite

  -- Suppose for contradiction that the set of zeros is infinite
  by_contra h_not_finite
  push Not at h_not_finite

  -- Let Z be the set of zeros in K
  let Z := {z ∈ K | riemannZeta z = 0}

  -- Since Z is infinite and contained in the compact set K,
  -- by the Bolzano-Weierstrass theorem, Z has an accumulation point in K
  have hZ_inf : Z.Infinite := h_not_finite
  have hZ_sub : Z ⊆ K := fun z hz => hz.1

  -- Apply Bolzano-Weierstrass to get an accumulation point
  obtain ⟨z₀, hz₀_K, hz₀_acc⟩ := lem_bolzano_weierstrass hK hZ_inf hZ_sub

  -- Case 1: If z₀ = 1
  by_cases h_eq_one : z₀ = 1
  · -- z₀ = 1, use riemannZeta_no_zeros_accumulate_at_one directly
    subst h_eq_one
    -- The set Z consists of zeros of riemannZeta
    have hZ_zeros : ∀ z ∈ Z, riemannZeta z = 0 := fun z hz => hz.2
    -- This contradicts riemannZeta_no_zeros_accumulate_at_one
    exact riemannZeta_no_zeros_accumulate_at_one Z hZ_zeros hz₀_acc

  · -- z₀ ≠ 1, use analyticity argument
    -- The Riemann zeta function is analytic at z₀ (since z₀ ≠ 1)
    have h_analytic : AnalyticAt ℂ riemannZeta z₀ :=
      zetaanalOnnot1 z₀ h_eq_one

    -- Apply the principle of isolated zeros
    obtain h_ev_zero | h_ev_ne := h_analytic.eventually_eq_zero_or_eventually_ne_zero

    · -- Case: riemannZeta is eventually zero in a neighborhood of z₀
      -- This would make it identically zero on the connected set {s : ℂ | s ≠ 1}

      -- Convert eventually to frequently in punctured neighborhood
      have h_freq := eventually_eq_zero_implies_frequently_eq_zero_punctured riemannZeta z₀ h_ev_zero

      have h_rank : 1 < Module.rank ℝ ℂ := by
        rw [Complex.rank_real_complex]
        norm_num
      have hpre : IsPreconnected ({s : ℂ | s ≠ 1} : Set ℂ) := by
        rw [show ({s : ℂ | s ≠ 1} : Set ℂ) = ({1} : Set ℂ)ᶜ by ext x; simp]
        exact (isConnected_compl_singleton_of_one_lt_rank h_rank (1 : ℂ)).isPreconnected
      -- Apply the identity theorem on the preconnected set {s : ℂ | s ≠ 1}
      have h_eq_on_zero := zetaanalOnnot1.eqOn_zero_of_preconnected_of_frequently_eq_zero
        hpre h_eq_one h_freq

      -- This says riemannZeta is zero on {s : ℂ | s ≠ 1}
      -- But riemannZeta(0) = -1/2 ≠ 0
      have : riemannZeta 0 = 0 := h_eq_on_zero (by simp : (0 : ℂ) ∈ {s | s ≠ 1})
      rw [riemannZeta_zero] at this
      norm_num at this

    · -- Case: riemannZeta is eventually non-zero in punctured neighborhoods
      -- But z₀ is an accumulation point of Z, so there are zeros arbitrarily close
      -- This contradicts the isolation property

      -- AccPt means the punctured neighborhood filter intersected with principal Z is NeBot
      unfold AccPt at hz₀_acc

      -- From eventually ne zero, we get eventually not in Z in punctured neighborhoods
      have h_ev_not_Z : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ, z ∉ Z := by
        apply Filter.Eventually.mono h_ev_ne
        intro z hz hz_in_Z
        exact hz hz_in_Z.2

      -- This means in the intersection filter, we eventually have False
      have h_ev_false : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z, False := by
        rw [Filter.eventually_inf_principal]
        exact h_ev_not_Z

      -- By eventually_false_iff_eq_bot, this filter equals ⊥
      have h_eq_bot : nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z = ⊥ :=
        Filter.eventually_false_iff_eq_bot.mp h_ev_false

      -- But hz₀_acc says this filter is NeBot
      -- NeBot means the filter is not equal to ⊥
      have h_ne_bot : nhdsWithin z₀ {z₀}ᶜ ⊓ Filter.principal Z ≠ ⊥ := hz₀_acc.ne

      -- This is a contradiction
      exact h_ne_bot h_eq_bot

-- For z∈ℂ, if Re(z) > 1 - 9δ(z) then ζ(z)≠0
lemma lem_ZFRdelta :
  ∀ z : ℂ, 2 < |z.im| → z.re > 1 - 9 * deltaz z → riemannZeta z ≠ 0 := by
  intro z him hre
  by_cases h1 : 1 ≤ z.re
  · -- In the half-plane Re z ≥ 1, ζ ≠ 0
    simpa using riemannZeta_ne_zero_of_one_le_re h1
  -- Now assume Re z < 1
  have hzlt1 : z.re < 1 := lt_of_not_ge h1
  -- From |Im z| > 2, get 0 < δ(z) and δ(z) < 1/9
  have hgt : |z.im| > 2 := by simpa using him
  have hδ := (lem_delta19).1 z hgt
  rcases hδ with ⟨hδ_pos, hδ_lt_19⟩
  -- Then 9 * δ(z) < 1, so 0 < 1 - 9 * δ(z) < z.re, hence 0 < z.re
  have h9δ_lt1 : 9 * deltaz z < 1 := by
    have h := mul_lt_mul_of_pos_left hδ_lt_19 (by norm_num : 0 < (9 : ℝ))
    have h9 : (9 : ℝ) * (1 / 9) = 1 := by norm_num
    simpa [h9] using h
  have hzre_pos : 0 < z.re := by
    have : 0 < 1 - 9 * deltaz z := sub_pos.mpr h9δ_lt1
    exact lt_trans this hre
  -- Suppose for contradiction that ζ z = 0
  by_contra hzero
  have hzmem : z ∈ zeroZ := by simpa [zeroZ] using hzero
  -- Apply the zero-free region inequality with the chosen constant
  have hprop := (Classical.choose_spec zerofree).2.2
  have hbound : z.re ≤ 1 - zerofree_constant / Real.log (|z.im| + 2) :=
    hprop z ⟨hzmem, hzre_pos, hzlt1⟩ him
  -- Let L = log(|Im z| + 2) and note L > 0
  set L : ℝ := Real.log (|z.im| + 2) with hLdef
  have hLpos : 0 < L := by
    have hone_lt : (1 : ℝ) < |z.im| + 2 := by
      have : (0 : ℝ) ≤ |z.im| := abs_nonneg _
      linarith
    have := Real.log_pos hone_lt
    simpa [hLdef] using this
  -- Compare 1 - c/L and 1 - 9 * δ(z)
  have hb_le_a' : ((9 : ℝ) / 20) * (zerofree_constant / L) ≤ zerofree_constant / L := by
    have hcoef_le1 : ((9 : ℝ) / 20) ≤ 1 := by norm_num
    have ha_nonneg : 0 ≤ zerofree_constant / L := le_of_lt (div_pos zerofree_constant_pos hLpos)
    have := mul_le_mul_of_nonneg_right hcoef_le1 ha_nonneg
    simpa [one_mul] using this
  have h9d_eq : 9 * deltaz z = ((9 : ℝ) / 20) * (zerofree_constant / L) := by
    simp [deltaz, hLdef, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hdelta_le : 9 * deltaz z ≤ zerofree_constant / L := by
    simpa [h9d_eq] using hb_le_a'
  have h_le_rhs : 1 - zerofree_constant / L ≤ 1 - 9 * deltaz z := by
    linarith [hdelta_le]
  -- Combine to contradict hre
  have hle : z.re ≤ 1 - 9 * deltaz z := le_trans hbound h_le_rhs
  have hcontr : z.re < z.re := lt_of_le_of_lt hle hre
  exact (lt_irrefl (z.re)) hcontr

-- lem_ZFRinD: For t∈ℝ with |t|>3, c=3/2+it and z=σ+it with 1-δ_t ≤ σ ≤ 3/2, we have z∈ D̄_{2/3}(c)


lemma complex_sub_ofReal_I_real_eq_ofReal (z : ℂ) (a t : ℝ) (him : z.im = t) :
  z - ((a : ℂ) + Complex.I * t) = ((z.re - a) : ℂ) := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im]
  · simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_mul_im, him]

lemma lem_ZFRinD (t : ℝ) (ht : |t| > 2) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
    z ∈ Metric.closedBall c (2/3) := by
  intro c h
  rcases h with ⟨h_low, hrest⟩
  rcases hrest with ⟨h_high, him⟩
  have hsub : z - c = ((z.re - (3/2)) : ℂ) := by
    simpa [c] using complex_sub_ofReal_I_real_eq_ofReal z (3/2) t him
  have h1 : dist z c = ‖((z.re - (3/2)) : ℂ)‖ := by
    simp [dist_eq_norm, hsub]
  have h2 : ‖((z.re - (3/2)) : ℂ)‖ = ‖z.re - (3/2)‖ := by
    simpa using (Complex.norm_real (z.re - (3/2)))
  have hdist_abs : dist z c = |z.re - (3/2)| := by
    have h4 : dist z c = ‖z.re - (3/2)‖ := h1.trans h2
    simpa [Real.norm_eq_abs] using h4
  have hnonpos : z.re - (3/2) ≤ 0 := sub_nonpos_of_le h_high
  have habs : |z.re - (3/2)| = 3/2 - z.re := by
    have := abs_of_nonpos hnonpos
    simpa [neg_sub] using this
  have hdist_eq : dist z c = 3/2 - z.re := hdist_abs.trans habs
  have h_le : dist z c ≤ 1/2 + deltaz_t t := by
    calc
      dist z c = 3/2 - z.re := hdist_eq
      _ ≤ 3/2 - (1 - deltaz_t t) := by linarith
      _ = 1/2 + deltaz_t t := by ring
  have hδlt : deltaz_t t < 1/9 := (lem_delta19.2 t ht).2
  have h12δ_lt : (1/2 : ℝ) + deltaz_t t < (1/2 : ℝ) + 1/9 := by
    have := add_lt_add_right hδlt (1/2 : ℝ)
    simpa [add_comm, add_left_comm, add_assoc] using this
  have h123_lt : (1/2 : ℝ) + 1/9 < (2/3 : ℝ) := by norm_num
  have h_lt : (1/2 : ℝ) + deltaz_t t < (2/3 : ℝ) := lt_trans h12δ_lt h123_lt
  have hdist_le : dist z c ≤ 2/3 := le_trans h_le (le_of_lt h_lt)
  exact (Metric.mem_closedBall).2 hdist_le

-- lem_ZFRnotK: For t∈ℝ with |t|>3, c=3/2+it and z=σ+it with 1-δ_t ≤ σ ≤ 3/2, we have z∉ K_ζ(5/6;c)
lemma lem_ZFRnotK (t : ℝ) (ht : |t| > 2) (z : ℂ) :
    let c := (3/2 : ℂ) + I * t
    1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
    z ∉ zerosetKfRc (5/6) c riemannZeta := by
  intro c h

  -- Extract the conjunction components
  obtain ⟨h_ge, h_le, h_im⟩ := h

  -- Key relationship: when z.im = t, we have deltaz z = deltaz_t t
  have h_delta_eq : deltaz z = deltaz_t t := by
    rw [deltaz_t, deltaz]
    -- Need to show the denominators are equal
    congr 1
    congr 1
    -- Show |z.im| = |(t * Complex.I).im|
    rw [h_im]
    -- Now show |t| = |(t * Complex.I).im|
    -- Since (t * Complex.I).im = t, this is |t| = |t|
    simp only [Complex.mul_I_im, Complex.ofReal_re]

  -- Convert the deltaz_t bound to a deltaz bound
  have h_ge_delta : 1 - deltaz z ≤ Complex.re z := by
    rwa [← h_delta_eq] at h_ge

  -- Get positivity of deltaz z from lem_delta19
  have h_im_gt : |z.im| > 2 := by
    rw [h_im]
    exact ht

  have h_delta_pos : 0 < deltaz z := by
    exact (lem_delta19.1 z h_im_gt).1

  -- Since deltaz z > 0, we have deltaz z < 9 * deltaz z
  have h_delta_lt_9delta : deltaz z < 9 * deltaz z := by
    linarith [h_delta_pos]

  -- Therefore Complex.re z > 1 - 9 * deltaz z
  have h_strict : Complex.re z > 1 - 9 * deltaz z := by
    linarith [h_ge_delta, h_delta_lt_9delta]

  -- Apply the zero-free region lemma
  have h_zeta_ne_zero : riemannZeta z ≠ 0 :=
    lem_ZFRdelta z h_im_gt h_strict

  -- Now prove z ∉ zerosetKfRc (5/6) c riemannZeta by contradiction
  intro h_mem
  -- By definition, z ∈ zerosetKfRc should imply riemannZeta z = 0
  have h_zero : riemannZeta z = 0 := h_mem.2
  -- This contradicts h_zeta_ne_zero
  exact h_zeta_ne_zero h_zero

-- lem_Zeta_Expansion_ZFR: Zeta expansion in the zero-free region
lemma lem_Zeta_Expansion_ZFR :
    ∃ C_1 : ℝ, C_1 > 1 ∧
    ∀ t : ℝ, |t| > 3 →
      let c := (3/2 : ℂ) + I * t;
      ∀ (hfin : (zerosetKfRc (5 / (6 : ℝ)) c riemannZeta).Finite),
      ∀ z : ℂ, 1 - deltaz_t t ≤ Complex.re z ∧ Complex.re z ≤ 3/2 ∧ Complex.im z = t →
        ‖(deriv riemannZeta z / riemannZeta z) -
          (∑ ρ ∈ hfin.toFinset, ((analyticOrderAt riemannZeta ρ).toNat : ℂ) / (z - ρ))‖
        ≤ C_1 * Real.log |t| := by
  obtain ⟨C, hC_gt_one, hC_expansion⟩ :=
    Zeta1_Zeta_Expansion (2/3) (3/4)
    (by norm_num : (0 : ℝ) < 2/3)
    (by norm_num : (2/3 : ℝ) < 3/4)
    (by norm_num : (3/4 : ℝ) < 5/6)
  let C_1 := C * (1 / ((3/4 : ℝ) - 2/3)^3 + 1)
  have hC_1_gt_1 : C_1 > 1 := by
    have h_coeff : (1 : ℝ) / ((3/4 : ℝ) - 2/3)^3 + 1 > 1 := by
      have h_pos : ((3/4 : ℝ) - 2/3)^3 > 0 := by norm_num
      have h_div_pos : (1 : ℝ) / ((3/4 : ℝ) - 2/3)^3 > 0 := div_pos one_pos h_pos
      linarith
    have h_ge_1 : (1 : ℝ) ≤ C := le_of_lt hC_gt_one
    exact one_lt_mul_of_le_of_lt h_ge_1 h_coeff
  refine ⟨C_1, hC_1_gt_1, ?_⟩
  intro t ht c hfin z hz
  have ht2 : |t| > 2 := by linarith
  have hz_in_ball : z ∈ Metric.closedBall c (2/3) := by
    simpa [c] using (lem_ZFRinD t ht2 z hz)
  have hz_not_in_K : z ∉ zerosetKfRc (5/6) c riemannZeta := by
    simpa [c] using (lem_ZFRnotK t ht2 z hz)
  have hz_in_diff : z ∈ Metric.closedBall c (2/3) \ zerosetKfRc (5/6) c riemannZeta :=
    ⟨hz_in_ball, hz_not_in_K⟩
  have h_expansion := hC_expansion t ht hfin z hz_in_diff
  rw [show logDerivZeta z = deriv riemannZeta z / riemannZeta z from rfl] at h_expansion
  exact h_expansion

-- lem_Rerhotodeltarho: For ρ∈ K_ζ(5/6;c) we have Re(ρ) ≤ 1 - 9δ(ρ)
lemma lem_Rerhotodeltarho {ρ : ℂ} :
  ∀ t : ℝ, |t| > 3 → ρ ∈ (zerosetKfRc (5 / (6 : ℝ)) (3/2+ t* Complex.I) riemannZeta) → ρ.re ≤ 1 - 9 * deltaz ρ := by
  intro t ht h_mem
  -- From ρ ∈ zerosetKfRc, we get riemannZeta ρ = 0
  have h_zero : riemannZeta ρ = 0 := h_mem.2

  -- ρ is in a closed ball of radius 5/6 around 3/2 + t*I
  have h_ball : ρ ∈ Metric.closedBall (3/2 + t * Complex.I) (5/6) := h_mem.1

  -- This means dist(ρ, 3/2 + t*I) ≤ 5/6
  have h_dist : dist ρ (3/2 + t * Complex.I) ≤ 5/6 := by
    rwa [Metric.mem_closedBall] at h_ball

  -- We need |ρ.im| > 2 to apply lem_ZFRdelta
  have h_im : 2 < |ρ.im| := by
    -- The imaginary part of ρ is close to t, so |ρ.im - t| ≤ 5/6
    have h_im_bound : |ρ.im - t| ≤ 5/6 := by
      -- |ρ.im - t| ≤ ||ρ - (3/2 + t*I)||
      have h_le_norm : |ρ.im - t| ≤ ‖ρ - (3/2 + t * Complex.I)‖ := by
        have : |(ρ - (3/2 + t * Complex.I)).im| ≤ ‖ρ - (3/2 + t * Complex.I)‖ :=
          Complex.abs_im_le_norm _
        have h_im_eq : (ρ - (3/2 + t * Complex.I)).im = ρ.im - t := by
          simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im]
        rwa [← h_im_eq]
      rw [← Complex.dist_eq] at h_le_norm
      linarith [h_le_norm, h_dist]

    -- Apply triangle inequality: |t| - |ρ.im| ≤ |t - ρ.im| = |ρ.im - t|
    have triangle := abs_sub_abs_le_abs_sub t ρ.im
    -- This gives |t| - |ρ.im| ≤ |t - ρ.im|
    -- Rewrite |t - ρ.im| = |ρ.im - t|
    have eq_comm : |t - ρ.im| = |ρ.im - t| := abs_sub_comm t ρ.im
    rw [eq_comm] at triangle
    -- Now triangle : |t| - |ρ.im| ≤ |ρ.im - t|
    -- Rearrange to get |ρ.im| ≥ |t| - |ρ.im - t|
    have h_ge : |ρ.im| ≥ |t| - |ρ.im - t| := by linarith [triangle]

    -- Since |t| > 3 and |ρ.im - t| ≤ 5/6, we get |ρ.im| ≥ 3 - 5/6 = 13/6 > 2
    have : |ρ.im| ≥ |t| - 5/6 := by linarith [h_ge, h_im_bound]
    have : |ρ.im| > 3 - 5/6 := by linarith [ht]
    have h_calc : (3 : ℝ) - 5/6 = 13/6 := by norm_num
    have h_gt2 : (13 : ℝ)/6 > 2 := by norm_num
    rw [h_calc] at *
    linarith [h_gt2]

  -- Apply contrapositive of lem_ZFRdelta
  -- lem_ZFRdelta: 2 < |z.im| → z.re > 1 - 9 * deltaz z → riemannZeta z ≠ 0
  -- contrapositive: riemannZeta z = 0 → ¬(z.re > 1 - 9 * deltaz z)
  have h_not_gt : ¬(ρ.re > 1 - 9 * deltaz ρ) := by
    intro h_gt
    have h_ne_zero := lem_ZFRdelta ρ h_im h_gt
    exact h_ne_zero h_zero

  exact le_of_not_gt h_not_gt

end ZetaZeroFreeRegion
