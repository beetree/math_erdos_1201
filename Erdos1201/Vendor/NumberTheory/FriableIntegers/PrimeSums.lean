module

public import Erdos1201.Vendor.NumberTheory.FriableIntegers.ArithmeticBandGeometry
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.Scale
public import Erdos1201.Vendor.NumberTheory.PrimeReciprocal
public import Erdos1201.Vendor.NumberTheory.SievedSetSquaredGaps.RoughPrimeSum
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-!
# Prime sums on the concrete moving band

This file derives the finite prime-sum estimates needed in the prime-power transfer bound from
Mathlib's Chebyshev bound.  No prime-sum estimate is introduced as a contract.
-/

open scoped BigOperators Nat.Prime
open Filter Topology

namespace FriableIntegers.PrimeSums

open ArithmeticModel Scale

/-- The complete set of primes at most `Y`, written in the same interval form as
`Chebyshev.theta`. -/
def primesUpTo (Y : ℕ) : Finset ℕ :=
  (Finset.Icc 0 Y).filter Nat.Prime

/-- `primesUpTo` is monotone in the upper endpoint. -/
theorem primesUpTo_mono {A Y : ℕ} (hAY : A ≤ Y) :
    primesUpTo A ⊆ primesUpTo Y :=
  Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hAY)

/-- The moving prime band is the standard difference of prime prefixes. -/
theorem primeBand_eq_primesLE_sdiff (n W : ℕ) :
    primeBand n W = Nat.primesLE (yNat n) \ Nat.primesLE W := by
  ext p
  simp only [mem_primeBand, Finset.mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨hp, hWp, hpY⟩
    exact ⟨⟨hpY, hp⟩, fun hpW ↦ (Nat.not_le_of_gt hWp) hpW.1⟩
  · rintro ⟨⟨hpY, hp⟩, hpW⟩
    refine ⟨hp, ?_, hpY⟩
    by_contra hWp
    exact hpW ⟨Nat.le_of_not_gt hWp, hp⟩

noncomputable def completeLogReciprocalSum (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y, Real.log (p : ℝ) / (p : ℝ)

noncomputable def completeReciprocalSum (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y, 1 / (p : ℝ)

/-- `completeReciprocalSum` written over Mathlib's `Nat.primesLE`, matching
the `primeHarmonic` prefix used in the Meissel--Mertens development. -/
theorem completeReciprocalSum_eq_sum_primesLE (Y : ℕ) :
    completeReciprocalSum Y = ∑ p ∈ Nat.primesLE Y, (p : ℝ)⁻¹ := by
  rw [completeReciprocalSum,
    (by unfold primesUpTo; exact (Nat.primesLE_eq_filter_Icc_zero Y).symm :
      primesUpTo Y = Nat.primesLE Y)]
  exact Finset.sum_congr rfl fun p _ => one_div (p : ℝ)

/-- The reciprocal-prime sum over a numerical interval `(A,Y]`, expressed as
the subtraction of two `completeReciprocalSum` prefixes. -/
theorem primesUpTo_sdiff_reciprocalSum_eq_sub {A Y : ℕ} (hAY : A ≤ Y) :
    (∑ p ∈ primesUpTo Y \ primesUpTo A, 1 / (p : ℝ)) =
      completeReciprocalSum Y - completeReciprocalSum A := by
  have hsum := Finset.sum_sdiff (primesUpTo_mono hAY) (f := fun p : ℕ => 1 / (p : ℝ))
  unfold completeReciprocalSum
  exact (eq_sub_iff_add_eq).2 hsum

noncomputable def bandLogReciprocalSum (n W : ℕ) : ℝ :=
  ∑ p ∈ primeBand n W, Real.log (p : ℝ) / (p : ℝ)

noncomputable def bandReciprocalSum (n W : ℕ) : ℝ :=
  ∑ p ∈ primeBand n W, 1 / (p : ℝ)

/-- The friable moving-band sum agrees with the shared reciprocal-prime block. -/
theorem bandReciprocalSum_eq_primeReciprocalBlock (n W : ℕ) :
    bandReciprocalSum n W = Research.primeReciprocalBlock W (yNat n) := by
  simp only [bandReciprocalSum, Research.primeReciprocalBlock,
    primeBand_eq_primesLE_sdiff]

noncomputable def bandReciprocalSquareSum (n W : ℕ) : ℝ :=
  ∑ p ∈ primeBand n W, 1 / (p : ℝ) ^ 2

/-- The finite prime-band subtype sum agrees with the corresponding sum over
`primeBand`, for any real-valued function of the prime.  This is the single
Finset identification behind every `BandPrime`/`primeBand` sum rewrite. -/
theorem sum_bandPrime_eq (n W : ℕ) (f : ℕ → ℝ) :
    (∑ p : ArithmeticBandGeometry.BandPrime n W, f p.1) =
      ∑ p ∈ primeBand n W, f p :=
  (Finset.sum_subtype (primeBand n W) (fun _p ↦ Iff.rfl) f).symm

theorem sum_bandPrime_inv_eq (n W : ℕ) :
    (∑ p : ArithmeticBandGeometry.BandPrime n W, 1 / (p.1 : ℝ)) =
      bandReciprocalSum n W :=
  sum_bandPrime_eq n W (fun p ↦ 1 / (p : ℝ))

theorem sum_bandPrime_inv_sq_eq (n W : ℕ) :
    (∑ p : ArithmeticBandGeometry.BandPrime n W, 1 / (p.1 : ℝ) ^ 2) =
      bandReciprocalSquareSum n W :=
  sum_bandPrime_eq n W (fun p ↦ 1 / (p : ℝ) ^ 2)

/-- The weighted first moment of the concrete logarithmic prime coordinates. -/
noncomputable def bandTReciprocalSum (n W : ℕ) : ℝ :=
  ∑ p ∈ primeBand n W, tPrime n p / (p : ℝ)

noncomputable def primeLogCoeff (k : ℕ) : ℝ :=
  if k.Prime then Real.log (k : ℝ) else 0

theorem sum_primeLogCoeff_Icc (x : ℝ) :
    (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, primeLogCoeff k) = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  rw [Finset.sum_filter]
  rfl

theorem primeBand_subset_primesUpTo (n W : ℕ) :
    primeBand n W ⊆ primesUpTo (yNat n) := by
  intro p hp
  have h := mem_primeBand.mp hp
  simp [primesUpTo, h.1, h.2.2]

/-- The square-reciprocal tail needed in every `IJ/JJ` row contraction. -/
theorem bandReciprocalSquareSum_le (n W : ℕ) (hW : 1 ≤ W) :
    bandReciprocalSquareSum n W ≤ 1 / (W : ℝ) := by
  exact finset_sum_one_div_sq_le (primeBand n W) W (yNat n) (by omega)
    (fun p hp => cutoff_lt_of_mem_primeBand hp)
    (fun p hp => le_yNat_of_mem_primeBand hp)

/-- Abel summation for the logarithmically weighted prime harmonic sum.
This is exported so the moving-cell transfer can subtract two endpoints
without introducing an unproved Mertens-type input. -/
theorem completeLogReciprocalSum_eq (Y : ℕ) (hY : 2 ≤ Y) :
    completeLogReciprocalSum Y =
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) +
        ∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2 := by
  let c : ℕ → ℝ := primeLogCoeff
  have hc0 : c 0 = 0 := by simp [c, primeLogCoeff]
  have hc1 : c 1 = 0 := by simp [c, primeLogCoeff]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) Y,
      DifferentiableAt ℝ (fun x : ℝ => x⁻¹) t := by
    intro t ht
    exact differentiableAt_inv (by linarith [ht.1])
  have hint : MeasureTheory.IntegrableOn
      (deriv (fun x : ℝ => x⁻¹)) (Set.Icc (2 : ℝ) Y) := by
    rw [show deriv (fun x : ℝ => x⁻¹) = fun x => -(x ^ 2)⁻¹ by
      funext x
      exact deriv_inv]
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have ht20 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht0
    exact ContinuousAt.continuousWithinAt (((continuousAt_id.pow 2).inv₀ ht20).neg)
  have habel := sum_mul_eq_sub_integral_mul₁ (f := fun x : ℝ => x⁻¹)
    c hc0 hc1 (Y : ℝ) hdiff hint
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast hY)] at habel
  rw [show (⌊(Y : ℝ)⌋₊ : ℕ) = Y by simp] at habel
  have hcumY : (∑ k ∈ Finset.Icc 0 Y, c k) = Chebyshev.theta (Y : ℝ) := by
    simpa [c] using sum_primeLogCoeff_Icc (Y : ℝ)
  have hcum : ∀ t : ℝ,
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = Chebyshev.theta t := by
    intro t
    simpa [c] using sum_primeLogCoeff_Icc t
  rw [hcumY] at habel
  simp_rw [hcum] at habel
  simp_rw [deriv_inv] at habel
  have hlhs :
      (∑ k ∈ Finset.Icc 0 Y, (k : ℝ)⁻¹ * c k) =
        completeLogReciprocalSum Y := by
    simp [completeLogReciprocalSum, primesUpTo, c, primeLogCoeff,
      Finset.sum_filter, div_eq_mul_inv, mul_comm]
  rw [hlhs] at habel
  have hInt :
      (∫ x in (2 : ℝ)..Y, -(x ^ 2)⁻¹ * Chebyshev.theta x) =
        -(∫ x in (2 : ℝ)..Y, Chebyshev.theta x / x ^ 2) := by
    calc
      (∫ x in (2 : ℝ)..Y, -(x ^ 2)⁻¹ * Chebyshev.theta x) =
          ∫ x in (2 : ℝ)..Y, -(Chebyshev.theta x / x ^ 2) := by
            apply intervalIntegral.integral_congr
            intro x hx
            simp only [div_eq_mul_inv]
            ring
      _ = -(∫ x in (2 : ℝ)..Y, Chebyshev.theta x / x ^ 2) :=
        intervalIntegral.integral_neg
  rw [hInt] at habel
  calc
    completeLogReciprocalSum Y =
        (Y : ℝ)⁻¹ * Chebyshev.theta (Y : ℝ) +
          ∫ x in (2 : ℝ)..Y, Chebyshev.theta x / x ^ 2 := by
      linarith
    _ = Chebyshev.theta (Y : ℝ) / (Y : ℝ) +
        ∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2 := by
      rw [div_eq_mul_inv]
      ring

theorem deriv_inv_mul_log {x : ℝ} (hx : x ≠ 0)
    (hlog : Real.log x ≠ 0) :
    deriv (fun z : ℝ => (z * Real.log z)⁻¹) x =
      -(Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) := by
  have hmul : HasDerivAt (fun z : ℝ => z * Real.log z)
      (Real.log x + x * x⁻¹) x := by
    convert (hasDerivAt_id x).mul (Real.hasDerivAt_log hx) using 1 <;> try rfl
    all_goals simp only [id_eq]
    all_goals field_simp [hx]
  have hinv : HasDerivAt (fun z : ℝ => (z * Real.log z)⁻¹)
      (-(Real.log x + x * x⁻¹) / (x * Real.log x) ^ 2) x :=
    hmul.inv (mul_ne_zero hx hlog)
  rw [hinv.deriv]
  field_simp [hx, hlog]

/-- Abel summation formula for the prime harmonic sum.  This is exported for
the moving-band quadrature: subtracting the formula at two endpoints makes
the Mertens constant disappear. -/
theorem completeReciprocalSum_eq (Y : ℕ) (hY : 2 ≤ Y) :
    completeReciprocalSum Y =
      Chebyshev.theta (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) +
        ∫ t in (2 : ℝ)..Y,
          Chebyshev.theta t * (Real.log t + 1) /
            (t ^ 2 * Real.log t ^ 2) := by
  let c : ℕ → ℝ := primeLogCoeff
  have hc0 : c 0 = 0 := by simp [c, primeLogCoeff]
  have hc1 : c 1 = 0 := by simp [c, primeLogCoeff]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) Y,
      DifferentiableAt ℝ (fun x : ℝ => (x * Real.log x)⁻¹) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    exact (((differentiableAt_id.mul (Real.differentiableAt_log ht0))).inv
      (mul_ne_zero ht0 hlog0))
  have hint : MeasureTheory.IntegrableOn
      (deriv (fun x : ℝ => (x * Real.log x)⁻¹)) (Set.Icc (2 : ℝ) Y) := by
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    have hcont : ContinuousWithinAt
        (fun u : ℝ => -(Real.log u + 1) / (u ^ 2 * Real.log u ^ 2))
        (Set.Icc (2 : ℝ) Y) t :=
      ContinuousAt.continuousWithinAt
        (((Real.continuousAt_log ht0).add continuousAt_const).neg.div
          ((continuousAt_id.pow 2).mul ((Real.continuousAt_log ht0).pow 2))
          (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hlog0)))
    refine hcont.congr (fun (u : ℝ) hu => ?_) ?_
    · exact deriv_inv_mul_log
        (by linarith [hu.1])
        (Real.log_ne_zero_of_pos_of_ne_one
          (by linarith [hu.1]) (by linarith [hu.1]))
    · exact deriv_inv_mul_log ht0 hlog0
  have habel := sum_mul_eq_sub_integral_mul₁
    (f := fun x : ℝ => (x * Real.log x)⁻¹)
    c hc0 hc1 (Y : ℝ) hdiff hint
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast hY)] at habel
  rw [show (⌊(Y : ℝ)⌋₊ : ℕ) = Y by simp] at habel
  have hcumY : (∑ k ∈ Finset.Icc 0 Y, c k) = Chebyshev.theta (Y : ℝ) := by
    simpa [c] using sum_primeLogCoeff_Icc (Y : ℝ)
  have hcum : ∀ t : ℝ,
      (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = Chebyshev.theta t := by
    intro t
    simpa [c] using sum_primeLogCoeff_Icc t
  rw [hcumY] at habel
  simp_rw [hcum] at habel
  have hlhs :
      (∑ k ∈ Finset.Icc 0 Y, ((k : ℝ) * Real.log (k : ℝ))⁻¹ * c k) =
        completeReciprocalSum Y := by
    rw [completeReciprocalSum, primesUpTo, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hprime : k.Prime
    · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hprime.ne_zero
      have hlog0 : Real.log (k : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one
          (by exact_mod_cast hprime.pos) (by exact_mod_cast hprime.ne_one)
      simp only [c, primeLogCoeff, hprime, ite_true]
      field_simp
    · simp [c, primeLogCoeff, hprime]
  rw [hlhs] at habel
  have hInt :
      (∫ x in (2 : ℝ)..Y,
        deriv (fun z : ℝ => (z * Real.log z)⁻¹) x * Chebyshev.theta x) =
        -(∫ x in (2 : ℝ)..Y,
          Chebyshev.theta x * (Real.log x + 1) /
            (x ^ 2 * Real.log x ^ 2)) := by
    calc
      (∫ x in (2 : ℝ)..Y,
        deriv (fun z : ℝ => (z * Real.log z)⁻¹) x * Chebyshev.theta x) =
          ∫ x in (2 : ℝ)..Y,
            -(Chebyshev.theta x * (Real.log x + 1) /
              (x ^ 2 * Real.log x ^ 2)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le (by exact_mod_cast hY)] at hx
        have hx0 : x ≠ 0 := by linarith [hx.1]
        have hlog0 : Real.log x ≠ 0 :=
          Real.log_ne_zero_of_pos_of_ne_one
            (by linarith [hx.1]) (by linarith [hx.1])
        change deriv (fun z : ℝ => (z * Real.log z)⁻¹) x * Chebyshev.theta x = _
        rw [deriv_inv_mul_log hx0 hlog0]
        ring
      _ = -(∫ x in (2 : ℝ)..Y,
          Chebyshev.theta x * (Real.log x + 1) /
            (x ^ 2 * Real.log x ^ 2)) := intervalIntegral.integral_neg
  rw [hInt] at habel
  have hY0 : (Y : ℝ) ≠ 0 := by positivity
  have hlogY0 : Real.log (Y : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity) (by exact_mod_cast (show Y ≠ 1 by omega))
  calc
    completeReciprocalSum Y =
        (((Y : ℝ) * Real.log (Y : ℝ))⁻¹ * Chebyshev.theta (Y : ℝ)) +
          ∫ x in (2 : ℝ)..Y,
            Chebyshev.theta x * (Real.log x + 1) /
              (x ^ 2 * Real.log x ^ 2) := by
      linarith
    _ = Chebyshev.theta (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) +
        ∫ t in (2 : ℝ)..Y,
          Chebyshev.theta t * (Real.log t + 1) /
            (t ^ 2 * Real.log t ^ 2) := by
      field_simp

/-- Local integrability of the first Abel kernel. -/
theorem intervalIntegrable_theta_div_sq {Y : ℝ} (hY : 2 ≤ Y) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / t ^ 2)
      MeasureTheory.volume 2 Y := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hY]
  conv =>
    arg 1
    ext t
    rw [Chebyshev.theta, div_eq_mul_inv, mul_comm, Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) ?_
  apply ContinuousOn.integrableOn_Icc
  intro t ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  exact ContinuousAt.continuousWithinAt ((continuousAt_id.pow 2).inv₀ (pow_ne_zero 2 ht0))

/-- Local integrability of the Abel-summation integrand. -/
theorem intervalIntegrable_mertensIntegrand {Y : ℝ} (hY : 2 ≤ Y) :
    IntervalIntegrable
      (fun t : ℝ => Chebyshev.theta t * (Real.log t + 1) /
        (t ^ 2 * Real.log t ^ 2)) MeasureTheory.volume 2 Y := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hY]
  have hg : MeasureTheory.IntegrableOn
      (fun t : ℝ =>
        ((Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) * Chebyshev.theta t)
      (Set.Icc (2 : ℝ) Y) := by
    conv =>
      arg 1
      ext t
      rw [Chebyshev.theta, Finset.sum_filter]
    refine integrableOn_mul_sum_Icc _ (by norm_num) ?_
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog0 : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith [ht.1]) (by linarith [ht.1])
    exact (((Real.continuousAt_log ht0).add continuousAt_const).div
        ((continuousAt_id.pow 2).mul ((Real.continuousAt_log ht0).pow 2))
        (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hlog0))).continuousWithinAt
  exact hg.congr_fun (by
    intro t ht
    ring) measurableSet_Icc

theorem integral_one_div_mul_log {Y : ℝ} (hY : 2 ≤ Y) :
    (∫ t in (2 : ℝ)..Y, 1 / (t * Real.log t)) =
      Real.log (Real.log Y) - Real.log (Real.log 2) := by
  have h := integral_inv_div_log (show (1 : ℝ) < 2 by norm_num) (show (1 : ℝ) < Y by linarith)
  simpa [div_eq_mul_inv, mul_inv, mul_comm] using h

/-- An explicit Mertens-type upper bound, obtained from the global Chebyshev
bound by Abel summation.  It is sufficient for every harmonic loss in
the prime-power transfer bound and does not invoke the prime number theorem as an assumption. -/
theorem completeReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    completeReciprocalSum Y ≤
      2 * Real.log 4 + 3 * Real.log 4 *
        (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
  rw [completeReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlogYhalf : (1 / 2 : ℝ) ≤ Real.log (Y : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (Y : ℝ) :=
      Real.log_le_log (by norm_num) hYR
    nlinarith [Real.log_two_gt_d9]
  have hlogY0 : 0 < Real.log (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hboundary :
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
        2 * Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) ≤
          (Real.log 4 * (Y : ℝ)) /
            ((Y : ℝ) * Real.log (Y : ℝ)) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ 2 * Real.log 4 := by
        field_simp [hY0.ne', hlogY0.ne']
        nlinarith
  have hint :
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
        3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
    calc
      (∫ t in (2 : ℝ)..Y,
        Chebyshev.theta t * (Real.log t + 1) /
          (t ^ 2 * Real.log t ^ 2)) ≤
          ∫ t in (2 : ℝ)..Y,
            3 * Real.log 4 * (1 / (t * Real.log t)) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_mertensIntegrand hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          have hlog0 : Real.log t ≠ 0 :=
            Real.log_ne_zero_of_pos_of_ne_one
              (by linarith [ht.1]) (by linarith [ht.1])
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul
              (continuousAt_const.div
                (continuousAt_id.mul (Real.continuousAt_log ht0))
                (mul_ne_zero ht0 hlog0)))
        · intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          have hloghalf : (1 / 2 : ℝ) ≤ Real.log t := by
            have hmono : Real.log 2 ≤ Real.log t :=
              Real.log_le_log (by norm_num) ht.1
            nlinarith [Real.log_two_gt_d9]
          calc
            Chebyshev.theta t * (Real.log t + 1) /
                (t ^ 2 * Real.log t ^ 2) ≤
                (Real.log 4 * t) * (Real.log t + 1) /
                  (t ^ 2 * Real.log t ^ 2) := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (le_of_lt ht0)
            _ ≤ 3 * Real.log 4 * (1 / (t * Real.log t)) := by
              field_simp [ht0.ne', (show Real.log t ≠ 0 by linarith)]
              nlinarith
      _ = 3 * Real.log 4 *
          (Real.log (Real.log (Y : ℝ)) - Real.log (Real.log 2)) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_mul_log hYR]
  linarith

/-- A global Chebyshev bound for the logarithmically weighted reciprocal
prime sum.  The deliberately simple constant is uniform in the endpoint. -/
theorem completeLogReciprocalSum_le (Y : ℕ) (hY : 2 ≤ Y) :
    completeLogReciprocalSum Y ≤ Real.log 4 * (1 + Real.log (Y : ℝ)) := by
  rw [completeLogReciprocalSum_eq Y hY]
  have hYR : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hY0 : (0 : ℝ) < (Y : ℝ) := by linarith
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have htheta : Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤ Real.log 4 := by
    calc
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) ≤
          (Real.log 4 * (Y : ℝ)) / (Y : ℝ) := by
        gcongr
        exact Chebyshev.theta_le_log4_mul_x (by positivity)
      _ = Real.log 4 := by field_simp
  have hint :
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
        Real.log 4 * Real.log (Y : ℝ) := by
    calc
      (∫ t in (2 : ℝ)..Y, Chebyshev.theta t / t ^ 2) ≤
          ∫ t in (2 : ℝ)..Y, Real.log 4 * (1 / t) := by
        refine intervalIntegral.integral_mono_on hYR
          (intervalIntegrable_theta_div_sq hYR) ?_ ?_
        · apply ContinuousOn.intervalIntegrable
          intro t ht
          rw [Set.uIcc_of_le hYR] at ht
          have ht0 : t ≠ 0 := by linarith [ht.1]
          exact ContinuousAt.continuousWithinAt
            (continuousAt_const.mul (continuousAt_const.div continuousAt_id ht0))
        · intro t ht
          calc
            Chebyshev.theta t / t ^ 2 ≤ (Real.log 4 * t) / t ^ 2 := by
              gcongr
              exact Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])
            _ = Real.log 4 * (1 / t) := by
              have ht0 : t ≠ 0 := by linarith [ht.1]
              field_simp
      _ = Real.log 4 * Real.log ((Y : ℝ) / 2) := by
        rw [intervalIntegral.integral_const_mul,
          integral_one_div_of_pos (by norm_num) hY0]
      _ ≤ Real.log 4 * Real.log (Y : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hlog4
        apply Real.log_le_log (div_pos hY0 (by norm_num))
        linarith
  nlinarith

theorem bandLogReciprocalSum_le_complete (n W : ℕ) :
    bandLogReciprocalSum n W ≤ completeLogReciprocalSum (yNat n) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeBand_subset_primesUpTo n W)
  intro p hp hnot
  have hp' : p ≤ yNat n ∧ p.Prime := by
    simpa [primesUpTo] using hp
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp'.2.one_le)) (by positivity)

theorem bandReciprocalSum_le_complete (n W : ℕ) :
    bandReciprocalSum n W ≤ completeReciprocalSum (yNat n) := by
  rw [bandReciprocalSum_eq_primeReciprocalBlock]
  unfold Research.primeReciprocalBlock
  rw [← primeBand_eq_primesLE_sdiff]
  apply Finset.sum_le_sum_of_subset_of_nonneg (primeBand_subset_primesUpTo n W)
  intro p hp hnot
  positivity

/-- The unweighted prime harmonic mass has precisely the `O(log L)` loss
allowed in the prime-power transfer bound.  The constant is explicit and independent of `W` and of
every later tilt box. -/
theorem eventually_bandReciprocalSum_le_logL (W : ℕ) :
    ∀ᶠ n in atTop,
      bandReciprocalSum n W ≤ 12 * Real.log (L n) := by
  have hyTop : Tendsto (fun n : ℕ => y n) atTop atTop := tendsto_y_atTop
  have hLTop : Tendsto L atTop atTop := by
    convert Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop using 1 ;
      ext n ; simp [L]
  have hlogLTop : Tendsto (fun n : ℕ => Real.log (L n)) atTop atTop :=
    Real.tendsto_log_atTop.comp hLTop
  have hlog4nonneg : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4upper : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog2pos : (0 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hinvLog2 : (Real.log 2)⁻¹ ≤ 2 := by
    rw [← one_div, one_div_le hlog2pos (by norm_num)]
    nlinarith [Real.log_two_gt_d9]
  have hloglog2 : (-1 : ℝ) ≤ Real.log (Real.log 2) := by
    calc
      (-1 : ℝ) ≤ 1 - (Real.log 2)⁻¹ := by linarith
      _ ≤ Real.log (Real.log 2) := Real.one_sub_inv_le_log_of_pos hlog2pos
  filter_upwards [eventually_gt_atTop 0,
    hyTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually (eventually_ge_atTop (1 : ℝ)),
    hlogLTop.eventually (eventually_ge_atTop (5 : ℝ))] with n hn hyn hLn hlogLn
  have hyNat : 2 ≤ yNat n := Nat.le_floor hyn
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hlogNatPos : 0 < Real.log (yNat n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < yNat n by omega))
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hn))
  have hlogNatLeY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hlogNatLeL : Real.log (yNat n : ℝ) ≤ L n := by
    calc
      Real.log (yNat n : ℝ) ≤ Real.log (y n) := hlogNatLeY
      _ = (2 / 9 : ℝ) * L n := log_y hn
      _ ≤ L n := by nlinarith
  have hloglogNatLeL :
      Real.log (Real.log (yNat n : ℝ)) ≤ Real.log (L n) :=
    Real.log_le_log hlogNatPos hlogNatLeL
  have hraw :
      bandReciprocalSum n W ≤
        2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := by
    calc
      bandReciprocalSum n W ≤ completeReciprocalSum (yNat n) :=
        bandReciprocalSum_le_complete n W
      _ ≤ 2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (Real.log (yNat n : ℝ)) - Real.log (Real.log 2)) :=
        completeReciprocalSum_le (yNat n) hyNat
      _ ≤ 2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := by
        gcongr
  calc
    bandReciprocalSum n W ≤
        2 * Real.log 4 + 3 * Real.log 4 *
          (Real.log (L n) - Real.log (Real.log 2)) := hraw
    _ = Real.log 4 *
        (2 + 3 * Real.log (L n) - 3 * Real.log (Real.log 2)) := by ring
    _ ≤ Real.log 4 * (5 + 3 * Real.log (L n)) := by
      apply mul_le_mul_of_nonneg_left _ hlog4nonneg
      nlinarith
    _ ≤ 3 * (5 + 3 * Real.log (L n)) := by
      apply mul_le_mul_of_nonneg_right hlog4upper
      nlinarith
    _ ≤ 12 * Real.log (L n) := by nlinarith

theorem bandTReciprocalSum_eq (n W : ℕ) :
    bandTReciprocalSum n W =
      bandLogReciprocalSum n W / Real.log (y n) := by
  rw [bandTReciprocalSum, bandLogReciprocalSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [tPrime]
  ring

/-- The `t_p/p` mass of the moving prime band is uniformly bounded.  This is
the first-moment estimate used in the weighted covariance-row contraction. -/
theorem eventually_bandTReciprocalSum_le (W : ℕ) :
    ∀ᶠ n in atTop, bandTReciprocalSum n W ≤ 2 * Real.log 4 := by
  have hyTop : Tendsto (fun n : ℕ => y n) atTop atTop := tendsto_y_atTop
  have hLTop : Tendsto L atTop atTop := by
    convert Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop using 1 ;
      ext n ; simp [L]
  filter_upwards [eventually_gt_atTop 0,
    hyTop.eventually (eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually (eventually_ge_atTop (9 / 2 : ℝ))] with n hn hyn hLn
  have hyNat : 2 ≤ yNat n := by
    exact Nat.le_floor hyn
  have hlogy : 1 ≤ Real.log (y n) := by
    rw [log_y hn]
    nlinarith
  have hlogy0 : 0 < Real.log (y n) := lt_of_lt_of_le (by norm_num) hlogy
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) := by positivity
  have hyFloor : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (le_of_lt (y_pos hn))
  have hlogFloor : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatPos hyFloor
  have hnum :
      Real.log 4 * (1 + Real.log (yNat n : ℝ)) ≤
        Real.log 4 * (2 * Real.log (y n)) := by
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by norm_num))
    nlinarith
  calc
    bandTReciprocalSum n W =
        bandLogReciprocalSum n W / Real.log (y n) := bandTReciprocalSum_eq n W
    _ ≤ completeLogReciprocalSum (yNat n) / Real.log (y n) := by
      exact div_le_div_of_nonneg_right (bandLogReciprocalSum_le_complete n W)
        (le_of_lt hlogy0)
    _ ≤ (Real.log 4 * (1 + Real.log (yNat n : ℝ))) /
          Real.log (y n) := by
      exact div_le_div_of_nonneg_right (completeLogReciprocalSum_le (yNat n) hyNat)
        (le_of_lt hlogy0)
    _ ≤ (Real.log 4 * (2 * Real.log (y n))) / Real.log (y n) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hlogy0)
    _ = 2 * Real.log 4 := by field_simp

end FriableIntegers.PrimeSums
