module

public import Erdos1201.Vendor.NumberTheory.ZetaZeroFreeRegion.ZeroOrderLogDerivSeries
public import Erdos1201.Vendor.Analysis.DiskAnalyticBounds.NormAlgebraAndMaximumModulus
public import Erdos1201.Vendor.Analysis.AnalyticZeroCounting.JensenBoundAndLogPrimitive

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
Von Mangoldt Dirichlet series for `-ζ'/ζ`: the real/imaginary-part identities
turning `-logDerivZeta (x + yI)` into `∑ Λ(n) n^{-x} cos(y log n)`, positivity
and comparison bounds for these series, a uniform bound on the residue term
`-ζ'/ζ(1+δ) - 1/δ` (small `δ`, a compact middle range, and large `δ` via the
Dirichlet series at `x = 2`), and the "3-4-1" combination
`3(-ζ'/ζ)(1+δ) + 4(-ζ'/ζ)(1+δ+it) + (-ζ'/ζ)(1+δ+2it)` rewritten as a
nonnegative-coefficient Dirichlet series and bounded near a hypothetical zero.
-/

public section

namespace ZetaZeroFreeRegion

open Complex Topology Filter Interval Set Asymptotics ZetaFunctionEstimates AnalyticZeroCounting

lemma lem_nxy (n : ℕ) (hn : n ≥ 1) (x y : ℝ) :
    Complex.cpow (n : ℂ) (-(x + y * I)) = Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
  -- Rewrite -(x + y * I) as (-x) + (-(y * I))
  have h : -(x + y * I) = (-x : ℂ) + (-(y * I)) := by ring
  rw [h]
  -- Apply Complex.cpow_add with α = (-x : ℂ) and β = -(y * I)
  exact Complex.cpow_add (-x : ℂ) (-(y * I)) (by
    rw [Nat.cast_ne_zero, ← Nat.one_le_iff_ne_zero]
    exact hn)

lemma lem_zeta1zetaseriesxy2 (x y : ℝ) (hx : 1 < x) :
    -logDerivZeta (x + y * I) = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℂ) * (Complex.cpow (n : ℂ) ((-x) : ℂ)) * (Complex.cpow (n : ℂ) (-(y * I))) := by
  -- Apply zeta1zetaseriesxy
  rw [zeta1zetaseriesxy x y hx]
  -- Transform the sum by rewriting each term
  congr 1
  ext n
  -- Convert ^ to cpow
  rw [← Complex.cpow_eq_pow]
  -- For n ≥ 1, apply lem_nxy; for n = 0, both sides are 0
  by_cases h : n = 0
  · -- Case n = 0: both terms are 0
    simp [h]
  · -- Case n ≠ 0: can apply lem_nxy
    have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [lem_nxy n hn x y]
    -- Rearrange multiplication: (a * b) * c = a * (b * c)
    ring

lemma LSeriesSummable_to_explicit_summable (x y : ℝ) (_hx : 1 < x) : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) → Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))) := by
  intro h_summable

  -- vonMangoldt(0) = 0, so we can use LSeries.term_def₀
  have h_vm_zero : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
    simp [ArithmeticFunction.vonMangoldt_apply]

  -- Show the functions are pointwise equal
  have h_eq : ∀ n : ℕ, LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) n =
    (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) := by
    intro n
    -- Use LSeries.term_def₀ since vonMangoldt(0) = 0
    rw [LSeries.term_def₀ h_vm_zero]
    -- Now we have vonMangoldt(n) * (n : ℂ) ^ (-(x + y * I))
    -- Convert from ^ to cpow using Complex.cpow_eq_pow
    rw [← Complex.cpow_eq_pow]
    -- Now we have vonMangoldt(n) * cpow (n : ℂ) (-(x + y * I))
    -- For n ≥ 1, use lem_nxy to split the exponent
    by_cases hn : n = 0
    · -- Case n = 0: both sides are 0
      simp [hn, h_vm_zero]
    · -- Case n ≠ 0: use lem_nxy to split
      have hn_ge : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
      rw [lem_nxy n hn_ge x y]
      ring

  -- LSeriesSummable means summability of the terms
  have h_term_summable : Summable (fun n => LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (x + y * I) n) := by
    exact h_summable

  -- Use the pointwise equality to transfer summability
  convert h_term_summable using 1
  ext n
  exact (h_eq n).symm

lemma Zseriesconverges1 (x y : ℝ) (hx : 1 < x) :
Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))) := by
  -- Use Zconverge1 to ensure riemannZeta doesn't vanish
  have h_zeta_ne_zero := Zconverges1 x y hx

  -- Use lem_zeta1zetaseriesxy2 to get the series representation
  have h_series := lem_zeta1zetaseriesxy2 x y hx

  -- The series is exactly the von Mangoldt L-series at s = x + y * I
  -- Apply the von Mangoldt L-series summability result
  have h_re : 1 < (x + y * I).re := by
    rw [complex_re_of_real_add_imag]
    exact hx

  have h_summable := ArithmeticFunction.LSeriesSummable_vonMangoldt h_re

  -- Convert from LSeriesSummable to explicit Summable form
  exact LSeriesSummable_to_explicit_summable x y hx h_summable


lemma lem_realnx (n : ℕ) (x : ℝ) (_hn : n ≥ 1) (_hx : x ≥ 1) :
    ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x) ≥ 0 := by
  apply mul_nonneg
  · -- Show ArithmeticFunction.vonMangoldt n ≥ 0
    exact ArithmeticFunction.vonMangoldt_nonneg
  · -- Show (n : ℝ) ^ (-x) ≥ 0
    apply Real.rpow_nonneg
    -- Show 0 ≤ (n : ℝ)
    exact Nat.cast_nonneg n


lemma lem_sumRealZ (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re := by
  -- Apply lem_zeta1zetaseriesxy2 and then take real part
  rw [lem_zeta1zetaseriesxy2 x y hx]
  -- Apply Complex.re_tsum to move .re inside the sum
  exact Complex.re_tsum (Zseriesconverges1 x y hx)

lemma RealLambdaxy (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (_hx : 1 < x) :
    ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I))).re =
((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
  -- Let b = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x)
  let b := ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-x)

  -- The key step: show that (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) = (b : ℂ)
  have h1 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) = (b : ℂ) := by
    -- Use Complex.ofReal_cpow
    have h_real_pow : Complex.cpow (n : ℂ) ((-x) : ℂ) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
      simpa using (Complex.ofReal_cpow (x := (n : ℝ)) (Nat.cast_nonneg n) (-x)).symm

    rw [h_real_pow]
    rw [← Complex.ofReal_mul]

  -- Use associativity: a * b * c = (a * b) * c
  have h2 : (ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ) * Complex.cpow (n : ℂ) (-(y * I)) =
           ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) ((-x) : ℂ)) * Complex.cpow (n : ℂ) (-(y * I)) := by
    rw [mul_assoc]

  rw [h2, h1]

  -- Now apply Complex.re_ofReal_mul with b (real) and Complex.cpow (n : ℂ) (-(y * I))
  exact Complex.re_ofReal_mul b (Complex.cpow (n : ℂ) (-(y * I)))

lemma ReZseriesRen (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) * (Complex.cpow (n : ℂ) (-(y * I))).re := by
  rw [lem_sumRealZ x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    exact RealLambdaxy n x y hn hx

lemma Rezeta1zetaseries (x y : ℝ) (hx : 1 < x) :
    (-logDerivZeta (x + y * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
  rw [ReZseriesRen x y hx]
  congr 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    rw [← DiskAnalyticBounds.lem_eacosalog3 n hn y]
    -- Need to show (Complex.cpow (n : ℂ) (-(y * I))).re = ((n : ℂ) ^ (-y * Complex.I)).re
    congr 1
    -- Show Complex.cpow (n : ℂ) (-(y * I)) = (n : ℂ) ^ (-y * Complex.I)
    rw [Complex.cpow_eq_pow]
    -- Show -(y * I) = -y * Complex.I
    simp [I]

lemma complex_vonMangoldt_real_part_eq (n : ℕ) (x y : ℝ) (hn : n ≥ 1) (hx : 1 < x) :
((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
(ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
  -- Step 1: Use lem_nxy to split the complex power
  rw [lem_nxy n hn x y]

  -- Step 2: Rearrange to match RealLambdaxy format
  rw [← mul_assoc]

  -- Step 3: Use RealLambdaxy to connect the product form to real terms
  rw [RealLambdaxy n x y hn hx]

  -- Step 4: Convert Complex.cpow to ^ and handle I vs Complex.I for lem_eacosalog3
  -- First, convert Complex.cpow to ^
  have h_cpow : (Complex.cpow (n : ℂ) (-(y * I))).re = ((n : ℂ) ^ (-(y * I))).re := by
    rw [Complex.cpow_eq_pow]

  -- Second, convert I to Complex.I
  have h_I : -(y * I) = -y * Complex.I := by
    simp [I]

  -- Apply both conversions
  rw [h_cpow, h_I]

  -- Now apply lem_eacosalog3 to rewrite the imaginary power part
  rw [DiskAnalyticBounds.lem_eacosalog3 n hn y]

lemma Rezetaseries_convergence (x y : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) := by
  -- Apply ReZconverges1 to get summability of the complex series real part
  have h1 : Summable (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) :=
    ReZconverges1 x y hx

  -- Show pointwise equality between the complex series and our target series
  have h2 : ∀ n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re =
                      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ)) := by
    intro n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      exact complex_vonMangoldt_real_part_eq n x y hn hx

  -- Apply the pointwise equality to transfer summability
  have h3 : (fun n => ((ArithmeticFunction.vonMangoldt n : ℂ) * Complex.cpow (n : ℂ) (-(x + y * I))).re) =
            (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (y * Real.log (n : ℝ))) :=
    funext h2
  rwa [← h3]

lemma Rezetaseries2t (x t : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (2 * t * Real.log (n : ℝ))) := by
  -- Apply Rezetaseries_convergence with y = 2 * t
  exact Rezetaseries_convergence x (2 * t) hx

lemma Rezetaseries0 (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
  -- Apply Rezetaseries_convergence with y = 0
  have h1 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) * Real.cos (0 * Real.log (n : ℝ))) :=
    Rezetaseries_convergence x 0 hx
  -- Use lem_cost0 to show cos(0 * log n) = 1
  convert h1 using 1
  ext n
  by_cases h : n = 0
  · simp [h]
  · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
    simp

lemma uniform_bound_Z0_complex : ∃ δ0 > 0, ∃ C0 ≥ 0, ∀ δ : ℝ, 0 < δ → δ < δ0 → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 := by
  -- Define the function appearing in Z0bound
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))
  -- Start from the big-O statement near 0+
  have hO := Z0bound
  -- Unpack the big-O into an eventual bound with some constant c
  rcases (Asymptotics.isBigO_iff).1 hO with ⟨c, hc⟩
  have h_event : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c := by
    -- simplify ‖(1 : ℂ)‖ = 1
    have : ∀ᶠ δ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)), ‖f δ‖ ≤ c * ‖(1 : ℂ)‖ := hc
    refine this.mono ?_
    intro δ hδ
    have : ‖(1 : ℂ)‖ = (1 : ℝ) := by simp
    simpa [this] using hδ
  -- Turn the eventual statement into existence of a concrete set S in the filter
  rcases (Filter.eventually_iff_exists_mem).1 h_event with ⟨S, hS_in, hS_bound⟩
  -- Since S ∈ nhdsWithin 0 (0, ∞), it contains an interval (0, δ0]
  rcases (mem_nhdsGT_iff_exists_Ioc_subset).1 hS_in with ⟨δ0, hδ0pos, hIoc_sub_S⟩
  -- Choose C0 = max c 0 to ensure nonnegativity and preserve the bound
  refine ⟨δ0, hδ0pos, max c 0, le_max_right _ _, ?_⟩
  intro δ hδpos hδlt
  -- δ belongs to (0, δ0] ⊆ S
  have hδ_in_S : δ ∈ S := hIoc_sub_S ⟨hδpos, le_of_lt hδlt⟩
  -- Hence we have the bound on the norm
  have hnorm_le_c : ‖f δ‖ ≤ c := hS_bound δ hδ_in_S
  -- Strengthen to a nonnegative constant C0 = max c 0
  exact le_trans hnorm_le_c (le_max_left _ _)


lemma vonMangoldt_rpow_nonneg (x : ℝ) : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x) := by
  intro n
  have h1 : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : 0 ≤ (n : ℝ) ^ (-x) := by
    exact Real.rpow_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n) _
  simpa using mul_nonneg h1 h2


lemma norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt (x : ℝ) (hx : 1 < x) :
  ‖-logDerivZeta (x : ℂ)‖ = |∑' n, ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x))| := by
  -- Dirichlet series identity for −ζ'/ζ on Re s > 1
  have hx' : 1 < (x : ℂ).re := by simpa using hx
  have hseries := zeta1zetaseries (s := (x : ℂ)) hx'
  -- Identify each complex term as the complexification of the corresponding real term
  let g : ℕ → ℝ := fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
  have hterm : ∀ n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)) = (g n : ℂ) := by
    intro n
    by_cases h : n = 0
    · -- both sides are zero since vonMangoldt 0 = 0
      have hv0C : (ArithmeticFunction.vonMangoldt 0 : ℂ) = 0 := by
        simp [ArithmeticFunction.vonMangoldt_apply]
      have hv0R : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
        simp [ArithmeticFunction.vonMangoldt_apply]
      simp [g, h, hv0C, hv0R]
    · -- n ≥ 1: use the cpow-neg-real identification
      have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h
      have hcp : (n : ℂ) ^ (-(x : ℂ)) = Complex.ofReal ((n : ℝ) ^ (-x)) := by
        simpa using (Complex.ofReal_cpow (x := (n : ℝ)) (Nat.cast_nonneg n) (-x)).symm
      -- rewrite using ofReal multiplicativity
      have : (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ))
              = Complex.ofReal (ArithmeticFunction.vonMangoldt n) * Complex.ofReal ((n : ℝ) ^ (-x)) := by
        simp [hcp]
      simpa [g, Complex.ofReal_mul] using this
  -- Rewrite the series using the pointwise identification
  have hsum_eq : (∑' n, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = ∑' n, (g n : ℂ) := by
    -- use function extensionality under tsum
    have hfun : (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-(x : ℂ)))
                = (fun n => (g n : ℂ)) := funext hterm
    simp [hfun]
  -- Sum of complexifications equals complexification of the real sum
  have hsum_ofReal : (∑' n, (g n : ℂ)) = Complex.ofReal (∑' n, g n) := by
    simpa using (Complex.ofReal_tsum g).symm
  -- Conclude that −ζ'/ζ(x) is real, equal to the complexification of the real Dirichlet series
  have hval : -logDerivZeta (x : ℂ) = Complex.ofReal (∑' n, g n) := by
    -- from the Dirichlet series identity
    simpa [hsum_eq, hsum_ofReal] using hseries
  -- Take norms; for a real number seen in ℂ, the norm is the absolute value
  calc
    ‖-logDerivZeta (x : ℂ)‖ = ‖Complex.ofReal (∑' n, g n)‖ := by simp [hval]
    _ = |∑' n, g n| := by
      exact (RCLike.norm_ofReal (K := ℂ) (∑' n, g n))

lemma bounded_on_compact_interval (a b : ℝ) (h0 : 0 < a) (_hle : a ≤ b) : ∃ Cmid ≥ 0, ∀ δ : ℝ, a ≤ δ → δ ≤ b → ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid := by
  -- Work on the compact set s = [a,b]
  let s : Set ℝ := Set.Icc a b
  let f : ℝ → ℂ := fun δ => -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))

  -- Define H by filling in the removable singularity at s = 1 for (s-1) * ζ(s).
  let H : ℂ → ℂ := Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1

  -- H is complex-differentiable everywhere (entire); proof adapted from Z0bound.
  have hH_diff : Differentiable ℂ H := by
    intro z
    rcases eq_or_ne z 1 with rfl | hz
    · -- differentiable at 1 via removable singularity
      refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
      · -- differentiable on punctured nhds around 1 of (u-1)*ζ(u)
        filter_upwards [self_mem_nhdsWithin] with t ht
        have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) t := by
          have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) t :=
            (differentiableAt_id.sub_const 1)
          have h2 : DifferentiableAt ℂ riemannZeta t :=
            (differentiableAt_riemannZeta ht)
          exact h1.mul h2
        apply DifferentiableAt.congr_of_eventuallyEq hdiff
        filter_upwards [eventually_ne_nhds ht] with u hu using by
          simp [H, Function.update_of_ne hu]
      · -- continuity of H at 1 from riemannZeta_residue_one
        simpa [H, continuousAt_update_same] using riemannZeta_residue_one
    · -- z ≠ 1: H agrees with (z-1)ζ(z), hence differentiable
      have hdiff : DifferentiableAt ℂ (fun u : ℂ => (u - 1) * riemannZeta u) z := by
        have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
        have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz)
        exact h1.mul h2
      apply DifferentiableAt.congr_of_eventuallyEq hdiff
      filter_upwards [eventually_ne_nhds hz] with u hu using by
        simp [H, Function.update_of_ne hu]

  -- Define the analytic function G(s) = -(H'(s))/H(s).
  let G : ℂ → ℂ := fun z => - (deriv H z) / H z

  -- For δ > 0, relate f(δ) with G(1+δ)
  have h_eq_on_pos : ∀ ⦃δ : ℝ⦄, 0 < δ →
      (-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))) = G ((1 : ℂ) + δ) := by
    intro δ hδ
    -- Abbreviations
    let z : ℂ := (1 : ℂ) + δ
    have hz_ne_one : z ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ : ℝ) = 1 := by
        simpa [z, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ = 0 := by linarith
      exact (ne_of_gt hδ) this
    have hzeta_ne : riemannZeta z ≠ 0 := by
      have : 1 < z.re := by simpa [z, Complex.add_re, Complex.ofReal_re] using by linarith
      exact riemannZeta_ne_zero_of_one_le_re (le_of_lt this)

    have h_id_deriv : deriv (fun u : ℂ => u - 1) z = 1 := by
      exact ((hasDerivAt_id z).sub_const 1).deriv
    have h_log_id : logDeriv (fun u : ℂ => u - 1) z = 1 / (z - 1) := by
      simp [logDeriv_apply, h_id_deriv]
    have hz1 : z - 1 ≠ 0 := by simpa using sub_ne_zero.mpr hz_ne_one
    have hζ : riemannZeta z ≠ 0 := hzeta_ne

    have h_deriv_mul : deriv (fun u : ℂ => (u - 1) * riemannZeta u) z
          = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      have hmul := h1.mul h2
      have heq : (fun u : ℂ => (u - 1) * riemannZeta u) = (riemannZeta * fun u : ℂ => u - 1) := by
        funext u; simp [Pi.mul_apply, mul_comm]
      rw [heq]
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using hmul.deriv

    have h_prodLog :
        logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z =
          logDeriv (fun u : ℂ => u - 1) z + logDerivZeta z := by
      have h1 : DifferentiableAt ℂ (fun u : ℂ => u - 1) z := (differentiableAt_id.sub_const 1)
      have h2 : DifferentiableAt ℂ riemannZeta z := (differentiableAt_riemannZeta hz_ne_one)
      have hfnz : (fun u : ℂ => u - 1) z ≠ 0 := by simpa using hz1
      have hgnz : riemannZeta z ≠ 0 := hζ
      have heqPi : (fun u : ℂ => (u - 1) * riemannZeta u)
          = ((fun u : ℂ => u - 1) * riemannZeta) := by
        funext u; simp [Pi.mul_apply]
      rw [heqPi]
      simpa [logDerivZeta, logDeriv_apply] using
        (logDeriv_mul (x := z) (f := fun u : ℂ => u - 1) (g := riemannZeta) hfnz hgnz h1 h2)

    have h_step : -logDerivZeta z - (1 / (z - 1))
        = - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z := by
      have : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
            = 1 / (z - 1) + logDerivZeta z := by
        simpa [h_log_id, add_comm] using h_prodLog
      have hneg : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z
                 = - (1 / (z - 1) + logDerivZeta z) := by
        simpa using congrArg Neg.neg this
      simpa [sub_eq_add_neg, add_comm] using hneg.symm

    have h_H_eq : H z = (z - 1) * riemannZeta z := by
      simp [H, Function.update_of_ne hz_ne_one]

    have h_eq_event : (fun u : ℂ => H u) =ᶠ[nhds z] (fun u : ℂ => (u - 1) * riemannZeta u) := by
      filter_upwards [eventually_ne_nhds hz_ne_one] with u hu
      simp [H, Function.update_of_ne hu]

    have h_hasDeriv_prod :
        HasDerivAt (fun u : ℂ => (u - 1) * riemannZeta u)
          (riemannZeta z + (z - 1) * deriv riemannZeta z) z := by
      have h1 : HasDerivAt (fun u : ℂ => u - 1) 1 z := (hasDerivAt_id z).sub_const 1
      have h2 : HasDerivAt riemannZeta (deriv riemannZeta z) z :=
        (differentiableAt_riemannZeta hz_ne_one).hasDerivAt
      have hmul := h1.mul h2
      have heq : (fun u : ℂ => (u - 1) * riemannZeta u) = (riemannZeta * fun u : ℂ => u - 1) := by
        funext u; simp [Pi.mul_apply, mul_comm]
      rw [heq]
      simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using hmul

    have h_hasDeriv_H :
        HasDerivAt H (riemannZeta z + (z - 1) * deriv riemannZeta z) z :=
      h_hasDeriv_prod.congr_of_eventuallyEq h_eq_event

    have h_dH : deriv H z = riemannZeta z + (z - 1) * deriv riemannZeta z := by
      simpa using h_hasDeriv_H.deriv

    have h_log_to_G : - logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = G z := by
      have h' : logDeriv (fun u : ℂ => (u - 1) * riemannZeta u) z = (deriv H z) / H z := by
        simp [logDeriv_apply, h_H_eq, h_dH, h_deriv_mul]
      have hneg' := congrArg (fun w => -w) h'
      simpa [G, neg_div] using hneg'

    have : -logDerivZeta z - (1 / (z - 1)) = G z := by
      simpa using h_step.trans h_log_to_G

    -- Substitute z = 1 + δ and 1/(z-1) = 1/δ
    simpa [z] using this

  -- Define the δ-parameterized function F(δ) := G(1 + δ).
  let F : ℝ → ℂ := fun δ => G ((1 : ℂ) + δ)

  -- H (and hence deriv H) is analytic on a neighborhood of every point; thus G is analytic at points where H ≠ 0.
  have hH_analytic_univ : AnalyticOnNhd ℂ H Set.univ :=
    (Complex.analyticOnNhd_univ_iff_differentiable).2 hH_diff

  -- Show F is continuous on [a,b]
  have hF_contOn : ContinuousOn F s := by
    intro δ0 hδ0
    -- Consider s0 = 1 + δ0
    let s0 : ℂ := (1 : ℂ) + δ0
    have hδ0pos : 0 < δ0 := lt_of_lt_of_le h0 hδ0.1
    have hs0_ne_one : s0 ≠ (1 : ℂ) := by
      intro h
      have hre : (1 + δ0 : ℝ) = 1 := by
        simpa [s0, Complex.add_re, Complex.ofReal_re] using congrArg Complex.re h
      have : δ0 = 0 := by linarith
      exact (ne_of_gt hδ0pos) this
    have hs0_re_gt_one : 1 < s0.re := by
      simpa [s0, Complex.add_re, Complex.ofReal_re] using by linarith
    have hζ_ne : riemannZeta s0 ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (le_of_lt hs0_re_gt_one)
    have hHs0_eq : H s0 = (s0 - 1) * riemannZeta s0 := by
      simp [H, Function.update_of_ne hs0_ne_one]
    have hHs0_ne : H s0 ≠ 0 := by
      have hs0m1_ne : s0 - 1 ≠ 0 := sub_ne_zero.mpr hs0_ne_one
      have : (s0 - 1) * riemannZeta s0 ≠ 0 := mul_ne_zero hs0m1_ne hζ_ne
      simpa [hHs0_eq] using this
    -- G is analytic (hence continuous) at s0 since H is analytic and H(s0) ≠ 0.
    have hH_an_at_s0 : AnalyticAt ℂ H s0 := hH_analytic_univ s0 (by simp)
    have hH'_an_at_s0 : AnalyticAt ℂ (fun z => deriv H z) s0 := hH_an_at_s0.deriv
    have hG_an_at_s0 : AnalyticAt ℂ (fun z => G z) s0 := by
      have h_div : AnalyticAt ℂ (fun z => (deriv H z) / H z) s0 :=
        hH'_an_at_s0.div hH_an_at_s0 (by simpa using hHs0_ne)
      have h_neg : AnalyticAt ℂ (fun z => -((deriv H z) / H z)) s0 := h_div.neg
      simpa [G, div_eq_mul_inv, mul_left_comm, mul_comm, mul_assoc] using h_neg
    have hG_cont_s0 : ContinuousAt (fun z : ℂ => G z) s0 := hG_an_at_s0.continuousAt
    -- affine map δ ↦ 1 + δ is continuous at δ0
    let affine : ℝ → ℂ := fun δ => (1 : ℂ) + (δ : ℂ)
    have h_affine_at : ContinuousAt affine δ0 :=
      (continuousAt_const).add Complex.continuous_ofReal.continuousAt
    -- Compose and restrict
    have hy : affine δ0 = s0 := by simp [affine, s0]
    have hG_at : ContinuousAt (fun z : ℂ => G z) (affine δ0) := by simpa [hy] using hG_cont_s0
    have h_comp_at : ContinuousAt (fun δ : ℝ => G (affine δ)) δ0 := hG_at.comp h_affine_at
    simpa [F, s, affine] using h_comp_at.continuousWithinAt

  -- On [a,b], for δ ≥ a > 0, f δ = F δ by h_eq_on_pos
  have h_eq_on_s : ∀ ⦃δ : ℝ⦄, δ ∈ s → f δ = F δ := by
    intro δ hδ
    have hδpos : 0 < δ := lt_of_lt_of_le h0 hδ.1
    simpa [f, F] using h_eq_on_pos hδpos

  -- By compactness, the norm of a continuous function on [a,b] is bounded above.
  have hK : IsCompact s := isCompact_Icc
  have hNorm_contOn : ContinuousOn (fun δ => ‖F δ‖) s := hF_contOn.norm
  have hBdd : BddAbove ((fun δ => ‖F δ‖) '' s) := IsCompact.bddAbove_image hK hNorm_contOn
  rcases hBdd with ⟨C, hC⟩

  -- Choose a nonnegative bound constant
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro δ hδa hδb
  -- Reduce goal to a statement about F using the equality on s
  change ‖f δ‖ ≤ max C 0
  have hδmem : δ ∈ s := ⟨hδa, hδb⟩
  have himg : (fun δ => ‖F δ‖) δ ∈ (fun δ => ‖F δ‖) '' s := ⟨δ, hδmem, rfl⟩
  have hbound : ‖F δ‖ ≤ C := hC himg
  have hbound' : ‖F δ‖ ≤ max C 0 := le_trans hbound (le_max_left _ _)
  -- use f = F on s to rewrite the norm
  have hfδ_eq : f δ = F δ := h_eq_on_s hδmem
  calc
    ‖f δ‖ = ‖F δ‖ := by simp [hfδ_eq]
    _ ≤ max C 0 := hbound'

lemma norm_one_div_coe_real_le_one_of_one_le {δ : ℝ} (h : 1 ≤ δ) : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := by
  -- Use norm_div to simplify the left-hand side
  have hδpos : 0 < δ := lt_of_lt_of_le zero_lt_one h
  calc
    ‖(1 : ℂ) / (δ : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(δ : ℂ)‖ := by
      exact norm_div (1 : ℂ) (δ : ℂ)
    _ = 1 / ‖(δ : ℂ)‖ := by simp
    _ = 1 / |δ| := by simp
    _ = 1 / δ := by simp [abs_of_nonneg (le_of_lt hδpos)]
    _ ≤ 1 := by
      -- From monotonicity of one_div on (0, ∞), with 1 ≤ δ
      simpa using (one_div_le_one_div_of_le (ha := (zero_lt_one)) (h := h))

/-- There exists a constant `C > 0` such that for all `δ > 0`,
`‖ -logDerivZeta (1 + δ) - 1/δ ‖ ≤ C`.  -/
lemma Z0bound_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ‖ -logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C := by
  -- Small-delta uniform bound from big-O near 0+
  rcases uniform_bound_Z0_complex with ⟨δ0, hδ0pos, C0, hC0nonneg, hsmall⟩
  -- Middle interval [a,1]
  let a : ℝ := min δ0 1
  have ha_pos : 0 < a := lt_min_iff.2 ⟨hδ0pos, zero_lt_one⟩
  have ha_le_one : a ≤ 1 := min_le_right _ _
  rcases bounded_on_compact_interval a 1 ha_pos ha_le_one with ⟨Cmid, hCmid_nonneg, hmid⟩
  -- Large-delta constant via Dirichlet series at x = 2
  let C2 : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))
  have hC2_nonneg : 0 ≤ C2 := by
    have hnn : ∀ n, 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) :=
      vonMangoldt_rpow_nonneg 2
    exact tsum_nonneg hnn
  -- Final constant: strictly greater than 1 and dominates all partial constants
  let C : ℝ := 2 + C0 + Cmid + C2
  have hCgt1 : 1 < C := by
    have : 2 ≤ 2 + C0 + Cmid + C2 := by linarith [hC0nonneg, hCmid_nonneg, hC2_nonneg]
    linarith
  refine ⟨C, hCgt1, ?_⟩
  intro δ hδpos
  by_cases hlt : δ < δ0
  · -- Small δ: use hsmall and enlarge to C
    have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C0 :=
      hsmall δ hδpos hlt
    -- C ≥ C0
    have hC0_le_C : C0 ≤ C := by linarith
    exact le_trans hbound hC0_le_C
  · -- δ ≥ δ0
    have hge : δ0 ≤ δ := le_of_not_gt hlt
    rcases le_total δ 1 with hδle1 | hδge1
    · -- Middle interval: a ≤ δ ≤ 1
      have ha_le_δ : a ≤ δ := le_trans (min_le_left δ0 1) hge
      have hbound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ Cmid :=
        hmid δ ha_le_δ hδle1
      -- C ≥ Cmid
      have hCmid_le_C : Cmid ≤ C := by linarith
      exact le_trans hbound hCmid_le_C
    · -- Large δ: bound ‖-ζ'/ζ(1+δ)‖ by C2 and add 1/δ ≤ 1
      -- Set x = 1 + δ
      let x : ℝ := 1 + δ
      have hx1 : 1 < x := by
        have : 0 < δ := hδpos
        have : 1 < 1 + δ := lt_add_of_pos_right 1 this
        exact this
      -- equality for norm via Dirichlet series (at real x)
      have h_norm_eq_abs_real : ‖-logDerivZeta (x : ℂ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| :=
        norm_negLogDerivZeta_real_eq_abs_tsum_vonMangoldt x hx1
      -- Identify (1:ℂ)+δ with (x : ℂ)
      have eqArg : ((1 : ℂ) + δ) = (x : ℂ) := by simp [x]
      -- Convert the equality to our argument
      have h_norm_eq_abs : ‖-logDerivZeta ((1 : ℂ) + δ)‖
            = |∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)| := by
        simpa [eqArg] using h_norm_eq_abs_real
      -- Define the real sum S
      let S : ℝ := ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
      have hsum_nonneg : 0 ≤ S := by
        change 0 ≤ ∑' n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
        exact tsum_nonneg (vonMangoldt_rpow_nonneg x)
      -- From equality with |S| and nonnegativity, bound the norm by S
      have h_norm_le_sum : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ S := by
        have : ‖-logDerivZeta ((1 : ℂ) + δ)‖ = |S| := h_norm_eq_abs
        have : |S| = S := abs_of_nonneg hsum_nonneg
        exact le_of_eq (h_norm_eq_abs.trans this)
      -- Compare S with C2 using termwise monotonicity from x ≥ 2
      have hx_ge_two : 2 ≤ x := by
        -- since δ ≥ 1 in this branch
        have : 1 ≤ δ := hδge1
        have : 2 ≤ 1 + δ := by linarith
        exact this
      -- Show pointwise inequality for the summands
      have h_le_2 : ∀ n, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)
                          ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ)) := by
        intro n
        by_cases h0 : n = 0
        · simp [h0]
        · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
          have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hrpow : (n : ℝ) ^ (-x) ≤ (n : ℝ) ^ (-(2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hn' (neg_le_neg hx_ge_two)
          have hΛ_nonneg : 0 ≤ (ArithmeticFunction.vonMangoldt n : ℝ) :=
            ArithmeticFunction.vonMangoldt_nonneg
          exact mul_le_mul_of_nonneg_left hrpow hΛ_nonneg
      -- Summability of both series
      have h_summ_x : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-x)) := by
        exact Rezetaseries0 x hx1
      have h_summ_2 : Summable (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(2 : ℝ))) :=
        Rezetaseries0 2 (by norm_num)
      have hsum_le : S ≤ C2 := by
        -- use the general tsum comparison lemma
        exact Summable.tsum_le_tsum h_le_2 h_summ_x h_summ_2
      -- Combine to bound the norm by C2
      have h_norm_le_C2 : ‖-logDerivZeta ((1 : ℂ) + δ)‖ ≤ C2 :=
        le_trans h_norm_le_sum hsum_le
      -- Now bound the target by triangle inequality and 1/δ ≤ 1
      have h_one_div_le : ‖(1 : ℂ) / (δ : ℂ)‖ ≤ 1 := norm_one_div_coe_real_le_one_of_one_le hδge1
      have htriangle : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖
                        ≤ ‖-logDerivZeta ((1 : ℂ) + δ)‖ + ‖(1 : ℂ) / (δ : ℂ)‖ :=
        norm_sub_le _ _
      have hlarge_bound : ‖-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))‖ ≤ C2 + 1 := by
        refine le_trans htriangle ?_
        exact add_le_add h_norm_le_C2 h_one_div_le
      -- Enlarge to C
      have hC2_le_C : C2 + 1 ≤ C := by linarith
      exact le_trans hlarge_bound hC2_le_C

/-- There exists a constant `C > 0` such that for all `δ > 0`,
`Re(-logDerivZeta (1 + δ) - 1/δ) ≤ C`. -/
lemma Z0boundRe_const :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ((-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))).re) ≤ C := by
  -- Use Z0bound_const to get a bound on the norm
  rcases Z0bound_const with ⟨C, hCpos, hC⟩
  use C
  constructor
  · exact hCpos
  · intro δ hδ
    -- Apply the bound and use that real part ≤ norm
    have h_bound := hC δ hδ
    exact le_trans (Complex.re_le_norm _) h_bound

/-- There exists a constant `C > 0` such that for all `δ > 0`,
`Re(-logDerivZeta (1 + δ)) + Re(- 1/δ) ≤ C`. -/
lemma Z0boundRe_const2 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    ((-logDerivZeta ((1 : ℂ) + δ)).re + (-(1 / (δ : ℂ))).re) ≤ C := by
  -- Use Z0boundRe_const and Complex.sub_re
  rcases Z0boundRe_const with ⟨C, hC_pos, hC⟩
  use C, hC_pos
  intro δ hδ
  have h_sub_re : ((-logDerivZeta ((1 : ℂ) + δ) - (1 / (δ : ℂ))).re) =
    ((-logDerivZeta ((1 : ℂ) + δ)).re + (-(1 / (δ : ℂ))).re) := by
    rw [Complex.sub_re]
    rfl
  rw [← h_sub_re]
  exact hC δ hδ

/-- There exists a constant `C > 0` such that for all `δ > 0`,
`Re(-logDerivZeta (1 + δ)) - 1/δ ≤ C`. -/
lemma Z0boundRe_const3 :
  ∃ C > 1, ∀ (δ : ℝ) (_hδ : δ > 0),
    (-logDerivZeta ((1 : ℂ) + δ)).re - (1 / δ) ≤ C := by
  -- Use Z0boundRe_const2 which gives us the bound with complex division
  rcases Z0boundRe_const2 with ⟨C, hCpos, hC⟩
  use C, hCpos
  intro δ hδ
  -- Apply Z0boundRe_const2
  have h := hC δ hδ
  -- Key insight: (-(1 / (δ : ℂ))).re = -(1 / δ) since 1/δ is real
  have h_re_eq : (-(1 / (δ : ℂ))).re = -(1 / δ) := by
    rw [Complex.neg_re, Complex.div_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im]
    simp [Complex.normSq_ofReal]
  -- Rewrite the bound using this equality
  rwa [h_re_eq] at h

lemma Z341bounds_const :
  ∃ C > 1, ∀ (δ : ℝ) (hδ : δ > 0) (hδ1 : δ < 1), ∀ t : ℝ, 2 < |t| → ∀ σ : ℝ,
    (σ + t * Complex.I) ∈ zeroZ →
      3 * (-logDerivZeta ((1 : ℂ) + δ)).re
    + 4 * (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re
    +     (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re
    ≤ 3 / δ - 4 / (1 + δ - σ) + C * Real.log (|t| + 2) := by
  -- Apply the three lemmas mentioned in informal proof: Z0boundRe_const3, Z1bound, Z2bound
  rcases Z0boundRe_const3 with ⟨C0, hC0pos, hZ0⟩
  rcases Z1bound with ⟨C1, hC1pos, hZ1⟩
  rcases lem_Z2bound with ⟨C2, hC2pos, hZ2⟩

  -- Choose final constant
  let C := 3 * C0 + 4 * C1 + C2

  have hC_gt_one : 1 < C := by
    have h1 : 1 < C0 := hC0pos
    have h2 : 3 < 3 * C0 := by linarith [mul_lt_mul_of_pos_left h1 (by norm_num : (0 : ℝ) < 3)]
    have h3 : 0 < 4 * C1 := mul_pos (by norm_num) (lt_trans zero_lt_one hC1pos)
    have h4 : 0 < C2 := lt_trans zero_lt_one hC2pos
    linarith [h2, h3, h4]

  use C
  constructor
  · exact hC_gt_one
  · intro δ hδpos hδ1 t ht σ hσ

    -- Apply the bounds from the referenced lemmas directly
    have hZ0_bound : (-logDerivZeta ((1 : ℂ) + δ)).re ≤ C0 + (1 / δ) := by
      have := hZ0 δ hδpos
      linarith

    have hZ1_bound : (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re ≤ -(1 / (1 + δ - σ)) + C1 * Real.log (|t| + 2) := by
      let s := σ + t * Complex.I
      have hs_mem : s ∈ zeroZ := hσ
      have hs_im : s.im = t := by simp [s]
      have hs_re : s.re = σ := by simp [s]
      have hδ_cond : 0 < δ ∧ δ < 1 := ⟨hδpos, hδ1⟩
      have := hZ1 δ hδ_cond t ht s ⟨hs_mem, hs_im⟩
      rw [hs_re] at this
      exact this

    have hZ2_bound : (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re ≤ C2 * Real.log (|t| + 2) := by
      have hδ_cond : 0 < δ ∧ δ < 1 := ⟨hδpos, hδ1⟩
      exact hZ2 t ht δ hδ_cond

    -- Show log(|t| + 2) ≥ 1 for constant absorption
    have hlog_ge_one : 1 ≤ Real.log (|t| + 2) := by
      have h1 : 2 < |t| := ht
      have h2 : Real.exp 1 < 3 := lem_three_gt_e
      have he_lt_t2 : Real.exp 1 < |t| + 2 := by linarith
      have ht2_pos : 0 < |t| + 2 := by linarith [abs_nonneg t]
      exact Real.le_log_iff_exp_le ht2_pos |>.mpr (le_of_lt he_lt_t2)

    -- Apply the bounds and combine step by step
    calc
      3 * (-logDerivZeta ((1 : ℂ) + δ)).re + 4 * (-logDerivZeta ((1 : ℂ) + δ + t * Complex.I)).re + (-logDerivZeta ((1 : ℂ) + δ + (2 * t) * Complex.I)).re
        ≤ 3 * (C0 + (1 / δ)) + 4 * (-(1 / (1 + δ - σ)) + C1 * Real.log (|t| + 2)) + C2 * Real.log (|t| + 2) := by
          exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hZ0_bound (by norm_num)) (mul_le_mul_of_nonneg_left hZ1_bound (by norm_num))) hZ2_bound
      _ = 3 * C0 + 3 / δ - 4 / (1 + δ - σ) + (4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + 3 * C0 + (4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + ((4 * C1 + C2) * Real.log (|t| + 2) + 3 * C0) := by ring
      _ ≤ 3 / δ - 4 / (1 + δ - σ) + (4 * C1 + C2 + 3 * C0) * Real.log (|t| + 2) := by
        -- Apply absorb_pos_constant_into_log with the right order of terms
        have hC0_pos : 0 < C0 := lt_trans zero_lt_one hC0pos
        have hC0_nonneg : 0 ≤ 3 * C0 := mul_nonneg (by norm_num) (le_of_lt hC0_pos)
        have h_absorb := absorb_pos_constant_into_log (L := Real.log (|t| + 2)) (A := 4 * C1 + C2) (c := 3 * C0) hlog_ge_one hC0_nonneg
        -- h_absorb : (4 * C1 + C2) * Real.log (|t| + 2) + 3 * C0 ≤ (4 * C1 + C2 + 3 * C0) * Real.log (|t| + 2)
        linarith [h_absorb]
      _ = 3 / δ - 4 / (1 + δ - σ) + (3 * C0 + 4 * C1 + C2) * Real.log (|t| + 2) := by ring
      _ = 3 / δ - 4 / (1 + δ - σ) + C * Real.log (|t| + 2) := by ring


def ZeroAt (σ t : ℝ) : Prop :=
  (σ + t * I) ∈ zeroZ


/-- Filter on `δ`: approach 0⁺. -/
def Fδ : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)


lemma Rezeta1zetaseries1 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + t * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) := by
  -- Apply Rezeta1zetaseries with x = 1 + delta and y = t
  have h1 : 1 < 1 + delta := by linarith [hdelta]
  convert Rezeta1zetaseries (1 + delta) t h1
  -- Show that the complex expressions are equal
  simp [Complex.ofReal_add]

lemma Rezeta1zetaseries2 (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)) := by
  -- Apply Rezeta1zetaseries with x = 1 + delta and y = 2 * t
  have h1 : 1 < 1 + delta := by linarith [hdelta]
  -- Rewrite the left side to match the pattern exactly, ensuring real arithmetic
  have h2 : (1 : ℂ) + delta + (2 * t) * I = (1 + delta : ℝ) + ((2 * t) : ℝ) * I := by
    simp [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
  rw [h2]
  exact Rezeta1zetaseries (1 + delta) (2 * t) h1

lemma Rezeta1zetaseries0 (delta : ℝ) (hdelta : delta > 0) :
    (-logDerivZeta ((1 : ℂ) + delta)).re = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
  -- Start with Rezeta1zetaseries1 with t = 0
  have h_series : (-logDerivZeta ((1 : ℂ) + delta + 0 * I)).re =
                  ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) :=
    Rezeta1zetaseries1 0 delta hdelta

  -- Simplify the LHS: (1 : ℂ) + delta + 0 * I = (1 : ℂ) + delta
  have h_lhs : (-logDerivZeta ((1 : ℂ) + delta + 0 * I)).re = (-logDerivZeta ((1 : ℂ) + delta)).re := by
    congr 2
    simp

  -- Simplify the RHS using lem_cost0: cos(0 * log n) = 1
  have h_rhs : ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (0 * Real.log (n : ℝ)) =
               ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) := by
    congr 1
    funext n
    by_cases h : n = 0
    · simp [h]
    · have hn : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr h
      simp

  -- Combine the results
  rw [← h_lhs, h_series, h_rhs]

lemma Z341series (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * (-logDerivZeta ((1 : ℂ) + delta)).re +
     4 * (-logDerivZeta ((1 : ℂ) + delta + t * I)).re +
     (-logDerivZeta ((1 : ℂ) + delta + (2 * t) * I)).re)
    =
    (3 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) +
     4 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) +
     ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) := by
  rw [Rezeta1zetaseries0 delta hdelta, Rezeta1zetaseries1 t delta hdelta, Rezeta1zetaseries2 t delta hdelta]

lemma lem341seriesConv (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    Summable (fun n : ℕ =>
      3 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) +
      4 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)) +
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) := by
  -- First establish that 1 < 1 + delta
  have h1 : 1 < 1 + delta := by linarith [hdelta]

  -- Apply the three convergence results from the context
  have h2 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta))) :=
    Rezetaseries0 (1 + delta) h1

  have h3 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) :=
    Rezetaseries_convergence (1 + delta) t h1

  have h4 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) :=
    Rezetaseries2t (1 + delta) t h1

  -- Use scalar multiplication to get summability of the scaled terms
  have h5 : Summable (fun n : ℕ => 3 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)))) :=
    Summable.mul_left 3 h2

  have h6 : Summable (fun n : ℕ => 4 * ((ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)))) :=
    Summable.mul_left 4 h3

  -- Rewrite the scalar multiplications
  have h5' : Summable (fun n : ℕ => 3 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta))) := by
    convert h5 using 1
    ext n
    ring

  have h6' : Summable (fun n : ℕ => 4 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) := by
    convert h6 using 1
    ext n
    ring

  -- Use summability of sums
  have h7 : Summable (fun n : ℕ =>
    3 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) +
    4 * (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) :=
    h5'.add h6'

  -- Finally add the third term
  exact h7.add h4

lemma lem341series (t : ℝ) (delta : ℝ) (hdelta : delta > 0) :
    (3 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)))
    + (4 * ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ)))
    + (∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ)))
    = ∑' (n : ℕ), (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * (3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ))) := by
  -- First establish that 1 < 1 + delta
  have h1 : 1 < 1 + delta := by linarith [hdelta]

  -- Apply the convergence results from the context
  have h2 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta))) :=
    Rezetaseries0 (1 + delta) h1

  have h3 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (t * Real.log (n : ℝ))) :=
    Rezetaseries_convergence (1 + delta) t h1

  have h4 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + delta)) * Real.cos (2 * t * Real.log (n : ℝ))) :=
    Rezetaseries2t (1 + delta) t h1

  -- Use scalar multiplication properties of tsum (in reverse direction)
  rw [← Summable.tsum_mul_left 3 h2]
  rw [← Summable.tsum_mul_left 4 h3]

  -- Use additivity of tsum
  rw [← Summable.tsum_add (Summable.mul_left 3 h2) (Summable.mul_left 4 h3)]
  rw [← Summable.tsum_add]

  -- Factor out common terms
  congr 1
  ext n
  ring

  -- Apply the final summability result
  · exact Summable.add (Summable.mul_left 3 h2) (Summable.mul_left 4 h3)
  · exact h4

end ZetaZeroFreeRegion
