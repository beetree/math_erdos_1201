module

public import Erdos1201.Vendor.NumberTheory.FriableIntegers.DickmanBasic
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.StructuredCells
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.Scale
public import Erdos1201.Vendor.NumberTheory.PNT.MediumPNT
public import Mathlib.NumberTheory.Harmonic.Bounds

public import Erdos1201.Vendor.NumberTheory.FriableIntegers.FriableAsymptoticPart1
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.FriableAsymptoticPart2
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.FriableAsymptoticPart3

@[expose] public section

/-!
# Friable counts on the main friable-integer estimate scale — part 4

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's concrete finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.

Closed-top Dickman integral, reverse step, and the uniform finite de Bruijn estimate.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace FriableIntegers.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale



/-- The Dickman integral remains valid when the upper endpoint lies on the
birth face `u = 1`; differentiability is only needed in the open interval. -/
theorem integral_dickmanContinuousWeight_closed_top (X z y : ℝ)
    (hz : 1 < z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc z y,
      1 ≤ Real.log X / Real.log t ∧
        Real.log X / Real.log t ≤ 6) :
    (∫ t in z..y, dickmanContinuousWeight X t) =
      dickmanAntiderivative X y - dickmanAntiderivative X z := by
  have hcontW : ContinuousOn
      (dickmanContinuousWeight X) (Set.Icc z y) :=
    (continuousOn_dickmanContinuousWeight X).mono (fun t ht => by
      rw [Set.mem_Ioi]
      exact hz.trans_le ht.1)
  have hint : IntervalIntegrable (dickmanContinuousWeight X)
      MeasureTheory.volume z y := by
    rw [← Set.uIcc_of_le hzy.le] at hcontW
    exact hcontW.intervalIntegrable
  have hcontA : ContinuousOn
      (dickmanAntiderivative X) (Set.Icc z y) := by
    intro t ht
    have ht1 : 1 < t := hz.trans_le ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlogne : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    have hqcont : ContinuousAt (fun s : ℝ => Real.log X / Real.log s) t :=
      continuousAt_const.div (Real.continuousAt_log ht0) hlogne
    exact (continuousAt_const.mul
      (continuous_rho.continuousAt.comp hqcont)).continuousWithinAt
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hzy.le hcontA
  · intro t ht
    have htI : t ∈ Set.Icc z y := ⟨ht.1.le, ht.2.le⟩
    have hqt6 := (hq t htI).2
    have hlogt : 0 < Real.log t := Real.log_pos (hz.trans ht.1)
    have hlogy : 0 < Real.log y := Real.log_pos (hz.trans hzy)
    have hlogty : Real.log t < Real.log y :=
      Real.strictMonoOn_log (show t ∈ Set.Ioi 0 by
        exact hz.trans ht.1 |>.trans' (by norm_num))
        (show y ∈ Set.Ioi 0 by exact hz.trans hzy |>.trans' (by norm_num)) ht.2
    have hqy1 := (hq y ⟨hzy.le, le_rfl⟩).1
    have hlogX : 0 < Real.log X := by
      have h := (le_div_iff₀ hlogy).mp hqy1
      linarith
    have hqstrict : 1 < Real.log X / Real.log t := by
      have hdiv : Real.log X / Real.log y < Real.log X / Real.log t := by
        exact (div_lt_div_iff_of_pos_left hlogX hlogy hlogt).2 hlogty
      exact hqy1.trans_lt hdiv
    exact hasDerivAt_dickmanAntiderivative X t (hz.trans ht.1)
      hqstrict hqt6
  · exact hint

/-- Prime-sum approximation with the upper endpoint allowed on `u = 1`. -/
theorem dickmanPrimeSum_pnt_bound_closed_top (X : ℕ) (hX : 1 ≤ X)
    {C : ℝ} (hC : 0 ≤ C) {X₀ z y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / (Real.log (T : ℝ)) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6) :
    |(∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
        dickmanPrimeSummand X p) -
      (dickmanAntiderivative (X : ℝ) (y : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ))| ≤
      500 * C * (X : ℝ) / Real.log (z : ℝ) +
        2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ) := by
  have hpnt := dickmanWeight_pnt_bound X hX hC hbound hX₀z hz hzy hq
  rw [primeThetaWeightedInterval_dickman,
    integerAbelMain_eq_sum_Ioc (dickmanThetaWeight X) hzy] at hpnt
  have hriemann := dickmanWeight_sum_integral_bound X hX hz hzy.le hq
  have hintegral := integral_dickmanContinuousWeight_closed_top
    (X : ℝ) (z : ℝ) (y : ℝ)
    (by exact_mod_cast (show 1 < z by omega))
    (by exact_mod_cast hzy) hq
  rw [hintegral] at hriemann
  calc
    _ = |((∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          dickmanPrimeSummand X p) -
          ∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) +
        ((∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ)))| := by ring_nf
    _ ≤ |(∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
          dickmanPrimeSummand X p) -
          ∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m| +
        |(∑ m ∈ Finset.Ioc z y, dickmanThetaWeight X m) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ))| := abs_add_le _ _
    _ ≤ _ := add_le_add hpnt hriemann

/-- Reverse (complement) method-of-steps inequality.  It starts from an upper
cutoff and solves the exact recursion for the lower cutoff. -/
theorem friableCount_reverse_step_pnt_bound (X : ℕ) (hX : 1 ≤ X)
    {C E₁ : ℝ} (hC : 0 ≤ C) {X₀ z y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / (Real.log (T : ℝ)) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzy : z < y)
    (hq : ∀ t ∈ Set.Icc (z : ℝ) (y : ℝ),
      1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6)
    (e : ℕ → ℝ)
    (htop : |(friableCount X y : ℝ) -
        dickmanAntiderivative (X : ℝ) (y : ℝ)| ≤ E₁)
    (hquot : ∀ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow,
      |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| ≤ e p) :
    |(friableCount X z : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ)| ≤
      E₁ + (∑ p ∈ (y + 1).primesBelow \ (z + 1).primesBelow, e p) +
        (500 * C * (X : ℝ) / Real.log (z : ℝ) +
          2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ)) := by
  let P := (y + 1).primesBelow \ (z + 1).primesBelow
  have hrecNat := friableCount_prime_interval X (Nat.succ_le_iff.mp hX) hzy.le
  have hrec : (friableCount X y : ℝ) = (friableCount X z : ℝ) +
      ∑ p ∈ P, (friableCount (X / p) p : ℝ) := by
    exact_mod_cast hrecNat
  have hsum :
      |(∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
          ∑ p ∈ P, dickmanPrimeSummand X p| ≤
        ∑ p ∈ P, e p := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ p ∈ P,
          |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ P, e p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hquot p (by simpa [P] using hp)
  have hprime := dickmanPrimeSum_pnt_bound_closed_top
    X hX hC hbound hX₀z hz hzy hq
  change |(∑ p ∈ P, dickmanPrimeSummand X p) -
      (dickmanAntiderivative (X : ℝ) (y : ℝ) -
        dickmanAntiderivative (X : ℝ) (z : ℝ))| ≤ _ at hprime
  have hrearrange : (friableCount X z : ℝ) =
      (friableCount X y : ℝ) -
        ∑ p ∈ P, (friableCount (X / p) p : ℝ) := by linarith
  rw [hrearrange]
  calc
    _ = |((friableCount X y : ℝ) -
          dickmanAntiderivative (X : ℝ) (y : ℝ)) -
        ((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
          ∑ p ∈ P, dickmanPrimeSummand X p) -
        ((∑ p ∈ P, dickmanPrimeSummand X p) -
          (dickmanAntiderivative (X : ℝ) (y : ℝ) -
            dickmanAntiderivative (X : ℝ) (z : ℝ)))| := by ring_nf
    _ ≤ |(friableCount X y : ℝ) -
          dickmanAntiderivative (X : ℝ) (y : ℝ)| +
        (|(∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
            ∑ p ∈ P, dickmanPrimeSummand X p| +
          |(∑ p ∈ P, dickmanPrimeSummand X p) -
            (dickmanAntiderivative (X : ℝ) (y : ℝ) -
              dickmanAntiderivative (X : ℝ) (z : ℝ))|) := by
      calc
        _ = |((friableCount X y : ℝ) -
              dickmanAntiderivative (X : ℝ) (y : ℝ)) +
            (-((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
              ∑ p ∈ P, dickmanPrimeSummand X p) +
            -((∑ p ∈ P, dickmanPrimeSummand X p) -
              (dickmanAntiderivative (X : ℝ) (y : ℝ) -
                dickmanAntiderivative (X : ℝ) (z : ℝ))))| := by ring_nf
        _ ≤ |(friableCount X y : ℝ) -
              dickmanAntiderivative (X : ℝ) (y : ℝ)| +
            |-((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
                ∑ p ∈ P, dickmanPrimeSummand X p) +
              -((∑ p ∈ P, dickmanPrimeSummand X p) -
                (dickmanAntiderivative (X : ℝ) (y : ℝ) -
                  dickmanAntiderivative (X : ℝ) (z : ℝ)))| := abs_add_le _ _
        _ ≤ |(friableCount X y : ℝ) -
              dickmanAntiderivative (X : ℝ) (y : ℝ)| +
            (|-((∑ p ∈ P, (friableCount (X / p) p : ℝ)) -
                ∑ p ∈ P, dickmanPrimeSummand X p)| +
              |-((∑ p ∈ P, dickmanPrimeSummand X p) -
                (dickmanAntiderivative (X : ℝ) (y : ℝ) -
                  dickmanAntiderivative (X : ℝ) (z : ℝ)))|) :=
          add_le_add le_rfl (abs_add_le _ _)
        _ = _ := by simp only [abs_neg]
    _ ≤ E₁ + ((∑ p ∈ P, e p) +
        (500 * C * (X : ℝ) / Real.log (z : ℝ) +
          2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (z : ℝ))) := by
      exact add_le_add htop (add_le_add hsum hprime)
    _ = _ := by
      dsimp [P]
      ring

theorem friableCount_top_exact {X : ℕ} (hX : 2 ≤ X) :
    (friableCount X X : ℝ) = dickmanAntiderivative (X : ℝ) (X : ℝ) := by
  have hlog : Real.log (X : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by positivity)
      (by exact_mod_cast (show X ≠ 1 by omega))
  rw [friableCount_eq_self le_rfl, dickmanAntiderivative,
    div_self hlog, rho_one]
  ring

/-- Elementary Chebyshev cardinality majorant: if every element of a finite
set of primes has `log`-value at least `L` and value at most `U`, the set's
cardinality is at most `(log 4) · U / L`. This is the shared skeleton behind
every elementary Chebyshev interval-cardinality bound in the corpus: fix a
finite set of primes, get a lower bound on `∑ log p` from a pointwise floor
`L`, get an upper bound from `θ(U) ≤ (log 4) · U`, divide. -/
theorem card_primes_le_log4_mul_div_of_forall_log_ge
    {S : Finset ℕ} (hSprime : ∀ p ∈ S, p.Prime)
    {L : ℝ} (hL : 0 < L) (hSL : ∀ p ∈ S, L ≤ Real.log p)
    {U : ℕ} (hSU : ∀ p ∈ S, p ≤ U) :
    (S.card : ℝ) ≤ Real.log 4 * (U : ℝ) / L := by
  have hlower : (S.card : ℝ) * L ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ S, L := by simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ p ∈ S, Real.log (p : ℝ) := Finset.sum_le_sum hSL
  have hupper : (∑ p ∈ S, Real.log (p : ℝ)) ≤ Real.log 4 * (U : ℝ) := by
    calc
      _ ≤ ∑ p ∈ (U + 1).primesBelow, Real.log (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesBelow.2 ⟨Nat.lt_succ_of_le (hSU p hp), hSprime p hp⟩
        · intro p hp hnot
          exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le)
      _ = primeLogSumUpTo U := rfl
      _ = Chebyshev.theta (U : ℝ) := primeLogSumUpTo_eq_theta U
      _ ≤ Real.log 4 * (U : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (by positivity)
  apply (le_div_iff₀ hL).2
  exact hlower.trans hupper

/-- The number of primes in `(z,Y]` has the elementary Chebyshev bound at
the exact scale needed to sum the uniform floor error. -/
theorem primeInterval_card_le (z Y : ℕ) (hz : 2 ≤ z) :
    (((Y + 1).primesBelow \ (z + 1).primesBelow).card : ℝ) ≤
      Real.log 4 * (Y : ℝ) / Real.log (z : ℝ) := by
  apply card_primes_le_log4_mul_div_of_forall_log_ge
  · exact fun p hp => Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  · exact Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  · intro p hp
    have hpout := (Finset.mem_sdiff.mp hp).2
    have hpz : z < p := by
      by_contra hnot
      apply hpout
      rw [Nat.mem_primesBelow]
      exact ⟨by omega,
        Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1⟩
    exact Real.log_le_log (by positivity) (by exact_mod_cast hpz.le)
  · intro p hp
    have hmem := (Finset.mem_sdiff.mp hp).1
    rw [Nat.mem_primesBelow] at hmem
    exact Nat.lt_succ_iff.mp hmem.1

/-- The endpoint Riemann error is eventually at most one copy of the natural
`X / log y` error scale, uniformly for `X ≤ y^5`. -/
theorem exists_dickmanRiemann_remainder_threshold :
    ∃ Y₀ : ℕ, ∀ {y X : ℕ}, Y₀ ≤ y → 2 ≤ y → 1 ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) ≤
        (X : ℝ) / Real.log (y : ℝ) := by
  have hlogdivReal : Filter.Tendsto
      (fun x : ℝ => Real.log x / x) Filter.atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogdiv : Filter.Tendsto
      (fun y : ℕ => Real.log (y : ℝ) / (y : ℝ))
      Filter.atTop (nhds 0) := by
    convert hlogdivReal.comp (tendsto_natCast_atTop_atTop (R := ℝ)) using 1 ; rfl
  have hlogsqdivReal : Filter.Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (1 : ℝ))
      Filter.atTop (nhds 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have hlogsqdiv : Filter.Tendsto
      (fun y : ℕ => Real.log (y : ℝ) ^ 2 / (y : ℝ))
      Filter.atTop (nhds 0) := by
    convert hlogsqdivReal.comp (tendsto_natCast_atTop_atTop (R := ℝ)) using 1 ;
      ext y ; simp [Real.rpow_one]
  have htotal : Filter.Tendsto
      (fun y : ℕ =>
        12 * (Real.log (y : ℝ) / (y : ℝ)) +
          80 * (Real.log (y : ℝ) ^ 2 / (y : ℝ)))
      Filter.atTop (nhds 0) := by
    have h12 : Filter.Tendsto (fun _ : ℕ => (12 : ℝ))
        Filter.atTop (nhds 12) := tendsto_const_nhds
    have h80 : Filter.Tendsto (fun _ : ℕ => (80 : ℝ))
        Filter.atTop (nhds 80) := tendsto_const_nhds
    convert (h12.mul hlogdiv).add (h80.mul hlogsqdiv) using 1
    norm_num
  have hevent : ∀ᶠ y : ℕ in Filter.atTop,
      12 * (Real.log (y : ℝ) / (y : ℝ)) +
          80 * (Real.log (y : ℝ) ^ 2 / (y : ℝ)) ≤ 1 := by
    have hlt := htotal.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hlt] with y hy
    exact hy.le
  obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨Y₀, ?_⟩
  intro y X hY₀y hy2 hX hlogX
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hypos : (0 : ℝ) < (y : ℝ) := by positivity
  have hXpos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hscaled :
      2 * (6 + 8 * Real.log (X : ℝ)) * Real.log (y : ℝ) /
          (y : ℝ) ≤ 1 := by
    have hinside : 6 + 8 * Real.log (X : ℝ) ≤
        6 + 40 * Real.log (y : ℝ) := by linarith
    calc
      _ = (2 * Real.log (y : ℝ) / (y : ℝ)) *
          (6 + 8 * Real.log (X : ℝ)) := by ring
      _ ≤ (2 * Real.log (y : ℝ) / (y : ℝ)) *
          (6 + 40 * Real.log (y : ℝ)) :=
        mul_le_mul_of_nonneg_left hinside (by positivity)
      _ = 2 * (6 + 40 * Real.log (y : ℝ)) * Real.log (y : ℝ) /
          (y : ℝ) := by ring
      _ = 12 * (Real.log (y : ℝ) / (y : ℝ)) +
          80 * (Real.log (y : ℝ) ^ 2 / (y : ℝ)) := by ring
      _ ≤ 1 := hY₀ y hY₀y
  apply (le_div_iff₀ hlogy).2
  calc
    (2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ)) *
        Real.log (y : ℝ) =
      (X : ℝ) *
        (2 * (6 + 8 * Real.log (X : ℝ)) * Real.log (y : ℝ) /
          (y : ℝ)) := by ring
    _ ≤ (X : ℝ) * 1 := mul_le_mul_of_nonneg_left hscaled hXpos.le
    _ = (X : ℝ) := by ring

/-- Uniform finite de Bruijn estimate on the complete four-mark coordinate
range.  This is a closed theorem: the PNT, contraction, and endpoint
thresholds are all chosen internally. -/
theorem exists_uniform_friableCount_dickman_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → y ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(friableCount X y : ℝ) - (X : ℝ) * rho (dickmanU X y)| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨C, hCpos, X₀, hbound⟩ :=
    exists_primeLogSumUpTo_error_bound (3 : ℝ)
  obtain ⟨Zc, hcontract⟩ := exists_primeInvLogSum_contraction_threshold
  obtain ⟨Zr, hriemann⟩ := exists_dickmanRiemann_remainder_threshold
  let K : ℝ := 10 * (500 * C + 3 * Real.log 4 + 1)
  let Y₀ : ℕ := max 2 (max X₀ (max Zc Zr))
  have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, Y₀, ?_⟩
  intro X
  induction X using Nat.strong_induction_on with
  | h X ih =>
      intro y hY₀y hyX hlogXy
      have hy2 : 2 ≤ y := (le_max_left 2 (max X₀ (max Zc Zr))).trans hY₀y
      have hypos : 0 < y := by omega
      have hX2 : 2 ≤ X := hy2.trans hyX
      have hXpos : 0 < X := by omega
      have hlogy : 0 < Real.log (y : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < y by omega))
      by_cases hyXeq : y = X
      · subst y
        rw [friableCount_top_exact hX2]
        simp only [dickmanAntiderivative, dickmanU, sub_self, abs_zero]
        positivity
      · have hyXlt : y < X := lt_of_le_of_ne hyX hyXeq
        let P := (X + 1).primesBelow \ (y + 1).primesBelow
        let e : ℕ → ℝ := fun p =>
          K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) + 3
        have hX₀y : X₀ ≤ y :=
          (le_max_left X₀ (max Zc Zr)).trans
            ((le_max_right 2 (max X₀ (max Zc Zr))).trans hY₀y)
        have hZcy : Zc ≤ y :=
          (le_max_left Zc Zr).trans
            ((le_max_right X₀ (max Zc Zr)).trans
              ((le_max_right 2 (max X₀ (max Zc Zr))).trans hY₀y))
        have hZry : Zr ≤ y :=
          (le_max_right Zc Zr).trans
            ((le_max_right X₀ (max Zc Zr)).trans
              ((le_max_right 2 (max X₀ (max Zc Zr))).trans hY₀y))
        have hq : ∀ t ∈ Set.Icc (y : ℝ) (X : ℝ),
            1 ≤ logRatio (X : ℝ) t ∧ logRatio (X : ℝ) t ≤ 6 := by
          intro t ht
          have ht1 : 1 < t :=
            (by exact_mod_cast (show 1 < y by omega) : (1 : ℝ) < y).trans_le ht.1
          have hlogt : 0 < Real.log t := Real.log_pos ht1
          have hlogtX : Real.log t ≤ Real.log (X : ℝ) := by
            apply Real.log_le_log (by linarith)
            exact ht.2
          have hlogyt : Real.log (y : ℝ) ≤ Real.log t := by
            apply Real.log_le_log (by positivity)
            exact ht.1
          constructor
          · dsimp [logRatio]
            apply (le_div_iff₀ hlogt).2
            simpa using hlogtX
          · dsimp [logRatio]
            apply (div_le_iff₀ hlogt).2
            linarith
        have hquot : ∀ p ∈ P,
            |(friableCount (X / p) p : ℝ) - dickmanPrimeSummand X p| ≤ e p := by
          intro p hpP
          have hpcomplete : p ∈ (X + 1).primesBelow \ (y + 1).primesBelow := by
            simpa [P] using hpP
          have hpprime : p.Prime :=
            Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hpcomplete).1
          have hpX : p ≤ X := by
            have := (Nat.lt_of_mem_primesBelow
              (Finset.mem_sdiff.mp hpcomplete).1)
            omega
          have hyp : y < p := by
            have hpout := (Finset.mem_sdiff.mp hpcomplete).2
            by_contra hnot
            apply hpout
            rw [Nat.mem_primesBelow]
            exact ⟨by omega, hpprime⟩
          have hp2 : 2 ≤ p := hpprime.two_le
          have hlogp : 0 < Real.log (p : ℝ) :=
            Real.log_pos (by exact_mod_cast hpprime.one_lt)
          have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hyp.le)
          have hq5 : Real.log (X : ℝ) / Real.log (p : ℝ) ≤ 5 := by
            apply (div_le_iff₀ hlogp).2
            linarith
          have hfloor := dickmanPrimeSummand_floor_stability X p hp2 hpX hq5
          have hApos : 1 ≤ X / p :=
            (Nat.le_div_iff_mul_le hpprime.pos).2 (by simpa using hpX)
          have hcount :
              |(friableCount (X / p) p : ℝ) -
                ((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p)| ≤
                K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) := by
            by_cases hpA : p ≤ X / p
            · have hAX : X / p < X := Nat.div_lt_self hXpos hpprime.one_lt
              have hlogAX : Real.log ((X / p : ℕ) : ℝ) ≤
                  Real.log (X : ℝ) := by
                apply Real.log_le_log (by exact_mod_cast hApos)
                exact_mod_cast Nat.div_le_self X p
              have hlogA5 : Real.log ((X / p : ℕ) : ℝ) ≤
                  5 * Real.log (p : ℝ) := by
                have := (div_le_iff₀ hlogp).mp hq5
                exact hlogAX.trans this
              exact ih (X / p) hAX (y := p)
                (hY₀y.trans hyp.le) hpA hlogA5
            · have hAp : X / p ≤ p := le_of_not_ge hpA
              rw [friableCount_eq_dickman_initial hApos hpprime.one_lt hAp,
                sub_self, abs_zero]
              positivity
          calc
            _ ≤ |(friableCount (X / p) p : ℝ) -
                  ((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p)| +
                |((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p) -
                  dickmanPrimeSummand X p| := by
              exact abs_sub_le _ _ _
            _ ≤ K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ) + 3 :=
              add_le_add hcount hfloor
            _ = e p := rfl
        have htop : |(friableCount X X : ℝ) -
            dickmanAntiderivative (X : ℝ) (X : ℝ)| ≤ 0 := by
          rw [friableCount_top_exact hX2, sub_self, abs_zero]
        have hreverse := friableCount_reverse_step_pnt_bound
          X hXpos hCpos.le hbound hX₀y hy2 hyXlt hq e htop
          (fun p hp => hquot p (by simpa [P] using hp))
        have hsumA : (∑ p ∈ P,
              K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ)) ≤
            K * (X : ℝ) * primeInvLogSum y X := by
          rw [primeInvLogSum]
          calc
            _ ≤ ∑ p ∈ P,
                K * (X : ℝ) *
                  (1 / ((p : ℝ) * Real.log (p : ℝ))) := by
              apply Finset.sum_le_sum
              intro p hpP
              have hpcomplete : p ∈ (X + 1).primesBelow \ (y + 1).primesBelow := by
                simpa [P] using hpP
              have hpprime : p.Prime :=
                Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hpcomplete).1
              have hlogp : 0 < Real.log (p : ℝ) :=
                Real.log_pos (by exact_mod_cast hpprime.one_lt)
              have hcast : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / (p : ℝ) :=
                Nat.cast_div_le
              calc
                _ ≤ K * ((X : ℝ) / (p : ℝ)) / Real.log (p : ℝ) := by
                  gcongr
                _ = K * (X : ℝ) *
                    (1 / ((p : ℝ) * Real.log (p : ℝ))) := by field_simp
            _ = K * (X : ℝ) *
                (∑ p ∈ P, 1 / ((p : ℝ) * Real.log (p : ℝ))) := by
              rw [Finset.mul_sum]
            _ = _ := by congr 2
        have hcontractYX : primeInvLogSum y X ≤
            9 / (10 * Real.log (y : ℝ)) :=
          hcontract hZcy hyXlt hlogXy
        have hsumAcontract : (∑ p ∈ P,
              K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ)) ≤
            (9 / 10 * K) * (X : ℝ) / Real.log (y : ℝ) := by
          calc
            _ ≤ K * (X : ℝ) * primeInvLogSum y X := hsumA
            _ ≤ K * (X : ℝ) * (9 / (10 * Real.log (y : ℝ))) := by
              gcongr
            _ = (9 / 10 * K) * (X : ℝ) /
                Real.log (y : ℝ) := by ring
        have hcard := primeInterval_card_le y X hy2
        have hsume : (∑ p ∈ P, e p) ≤
            (9 / 10 * K + 3 * Real.log 4) * (X : ℝ) /
              Real.log (y : ℝ) := by
          calc
            _ = (∑ p ∈ P,
                K * ((X / p : ℕ) : ℝ) / Real.log (p : ℝ)) +
                3 * (P.card : ℝ) := by
              simp only [e, Finset.sum_add_distrib, Finset.sum_const,
                nsmul_eq_mul]
              ring
            _ ≤ (9 / 10 * K) * (X : ℝ) / Real.log (y : ℝ) +
                3 * (Real.log 4 * (X : ℝ) / Real.log (y : ℝ)) :=
              add_le_add hsumAcontract (mul_le_mul_of_nonneg_left
                (by simpa [P] using hcard) (by norm_num))
            _ = (9 / 10 * K + 3 * Real.log 4) * (X : ℝ) /
                Real.log (y : ℝ) := by ring
        have hR := hriemann hZry hy2 hXpos hlogXy
        have hreverse' :
            |(friableCount X y : ℝ) -
                dickmanAntiderivative (X : ℝ) (y : ℝ)| ≤
              (9 / 10 * K + 3 * Real.log 4 + 500 * C + 1) *
                (X : ℝ) / Real.log (y : ℝ) := by
          calc
            _ ≤ 0 + (∑ p ∈ P, e p) +
                (500 * C * (X : ℝ) / Real.log (y : ℝ) +
                  2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) /
                    (y : ℝ)) := by simpa [P] using hreverse
            _ ≤ (∑ p ∈ P, e p) +
                (500 * C * (X : ℝ) / Real.log (y : ℝ) +
                  (X : ℝ) / Real.log (y : ℝ)) := by
              simpa only [zero_add] using
                add_le_add le_rfl (add_le_add le_rfl hR)
            _ ≤ (9 / 10 * K + 3 * Real.log 4) * (X : ℝ) /
                  Real.log (y : ℝ) +
                (500 * C * (X : ℝ) / Real.log (y : ℝ) +
                  (X : ℝ) / Real.log (y : ℝ)) :=
              add_le_add hsume le_rfl
            _ = (9 / 10 * K + 3 * Real.log 4 + 500 * C + 1) *
                (X : ℝ) / Real.log (y : ℝ) := by ring
        have hcoeff : 9 / 10 * K + 3 * Real.log 4 + 500 * C + 1 = K := by
          dsimp [K]
          ring
        rw [hcoeff] at hreverse'
        simpa only [dickmanAntiderivative, dickmanU] using hreverse'


/-- The integral cutoff `floor(n^(2/9))` retains enough logarithmic size
for the complete four-mark coordinate range. -/
theorem eventually_one_fifth_L_le_log_yNat :
    ∀ᶠ n : ℕ in Filter.atTop,
      (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := tendsto_y_atTop
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    convert Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop using 1 ;
      ext n ; simp [L]
  filter_upwards [Filter.eventually_gt_atTop 0,
    hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
    hLTop.eventually
      (Filter.eventually_ge_atTop (45 * Real.log 2))] with n hn hyn hLn
  have hypos : 0 < y n := y_pos hn
  have hyNatLower : y n / 2 ≤ (yNat n : ℝ) := by
    have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hyNatPos : (0 : ℝ) < (yNat n : ℝ) :=
    (div_pos hypos (by norm_num)).trans_le hyNatLower
  have hlogLower : Real.log (y n / 2) ≤ Real.log (yNat n : ℝ) :=
    Real.log_le_log (div_pos hypos (by norm_num)) hyNatLower
  have hlogDiv : Real.log (y n / 2) = Real.log (y n) - Real.log 2 := by
    rw [Real.log_div hypos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
  calc
    (1 / 5 : ℝ) * L n ≤ Real.log (y n / 2) := by
      rw [hlogDiv, log_y hn]
      linarith
    _ ≤ Real.log (yNat n : ℝ) := hlogLower

/-- Uniform Dickman estimate with the exact initial face included. -/
theorem exists_uniform_friableCount_dickman_bound_all_faces :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → 0 < X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |(friableCount X y : ℝ) - (X : ℝ) * rho (dickmanU X y)| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₁, hmain⟩ :=
    exists_uniform_friableCount_dickman_bound
  refine ⟨K, hK, max 2 Y₁, ?_⟩
  intro X y hy hX hlog
  have hy2 : 2 ≤ y := (le_max_left 2 Y₁).trans hy
  have hY₁y : Y₁ ≤ y := (le_max_right 2 Y₁).trans hy
  by_cases hyX : y ≤ X
  · exact hmain hY₁y hyX hlog
  · have hXy : X ≤ y := le_of_not_ge hyX
    rw [friableCount_eq_dickman_initial hX (by omega) hXy,
      sub_self, abs_zero]
    positivity



end FriableIntegers.FriableAsymptotic
