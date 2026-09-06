module

public import Erdos1201.Vendor.NumberTheory.FriableIntegers.DickmanBasic
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.StructuredCells
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.Scale
public import Erdos1201.Vendor.NumberTheory.PNT.MediumPNT
public import Mathlib.NumberTheory.Harmonic.Bounds

public import Erdos1201.Vendor.NumberTheory.FriableIntegers.FriableAsymptoticPart1
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.FriableAsymptoticPart2

@[expose] public section

/-!
# Friable counts on the main friable-integer estimate scale — part 3

This file develops the arithmetic side of the uniform Dickman estimate from
Mathlib's concrete finite set `Nat.smoothNumbersUpTo`.  In particular, the
statements below are exact finite identities: no asymptotic count is exposed
as a hypothesis or a contract.

Our second parameter `y` is inclusive: `friableCount X y` counts positive
integers at most `X` all of whose prime factors are at most `y`.  Thus the
underlying Mathlib smoothness threshold is `y + 1`.

Uniform floor stability for the recursive Dickman kernel and prime-inverse-log contraction.
-/

open scoped BigOperators
open Filter Topology Asymptotics

namespace FriableIntegers.FriableAsymptotic

open ArithmeticModel DickmanBasic Scale

/-! ## Uniform floor stability for the recursive Dickman kernel -/

/-- Replacing a positive real quotient by its integer floor perturbs the
Dickman main term by an absolute constant, uniformly on the compact range
used by the four-mark induction. -/
theorem rho_floor_kernel_stability (A : ℕ) {r p : ℝ}
    (hA : 1 ≤ A) (hAr : (A : ℝ) ≤ r) (hrA : r < (A : ℝ) + 1)
    (hp : (2 : ℝ) ≤ p) (hb4 : Real.log r / Real.log p ≤ 4) :
    |(A : ℝ) * rho (Real.log (A : ℝ) / Real.log p) -
        r * rho (Real.log r / Real.log p)| ≤ 3 := by
  let a : ℝ := Real.log (A : ℝ) / Real.log p
  let b : ℝ := Real.log r / Real.log p
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hA)
  have hrpos : 0 < r := hApos.trans_le hAr
  have hppos : 0 < p := by linarith
  have hlogppos : 0 < Real.log p := Real.log_pos (by linarith)
  have hlogp_half : (1 / 2 : ℝ) ≤ Real.log p := by
    have hmono : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) hp
    nlinarith [Real.log_two_gt_d9]
  have hlogAr : Real.log (A : ℝ) ≤ Real.log r :=
    Real.log_le_log hApos hAr
  have hab : a ≤ b := by
    dsimp [a, b]
    exact div_le_div_of_nonneg_right hlogAr hlogppos.le
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hA)) hlogppos.le
  have hb0 : 0 ≤ b := ha0.trans hab
  have hb5 : b ≤ 5 := by dsimp [b]; linarith
  have hrhoa0 : 0 ≤ rho a :=
    (rho_pos_on_zero_five ha0 (hab.trans hb5)).le
  have hrhob0 : 0 ≤ rho b := (rho_pos_on_zero_five hb0 hb5).le
  have hrhob1 : rho b ≤ 1 := rho_le_one_of_le_five hb5
  have hrho : |rho a - rho b| ≤ b - a := by
    rw [abs_sub_comm]
    exact rho_lipschitz_of_le_five hab hb5
  have hlogquot : Real.log r - Real.log (A : ℝ) ≤
      r / (A : ℝ) - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos hrpos hApos)
    rw [Real.log_div hrpos.ne' hApos.ne'] at h
    exact h
  have hscaled : (A : ℝ) *
      (Real.log r - Real.log (A : ℝ)) ≤ r - (A : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hlogquot hApos.le
    calc
      (A : ℝ) * (Real.log r - Real.log (A : ℝ)) ≤
          (A : ℝ) * (r / (A : ℝ) - 1) := h
      _ = r - (A : ℝ) := by field_simp
  have hAdiff : (A : ℝ) * (b - a) ≤ 2 := by
    have hdiv := div_le_div_of_nonneg_right hscaled hlogppos.le
    have hfirst : (A : ℝ) * (b - a) ≤
        (r - (A : ℝ)) / Real.log p := by
      dsimp [a, b]
      convert hdiv using 1 <;> try rfl
      all_goals field_simp [hlogppos.ne']
    have hsecond : (r - (A : ℝ)) / Real.log p ≤ 2 := by
      apply (div_le_iff₀ hlogppos).2
      nlinarith
    exact hfirst.trans hsecond
  have hgap0 : 0 ≤ r - (A : ℝ) := sub_nonneg.mpr hAr
  have hgap1 : r - (A : ℝ) ≤ 1 := by linarith
  calc
    _ = |(A : ℝ) * (rho a - rho b) +
          ((A : ℝ) - r) * rho b| := by dsimp [a, b]; congr 1; ring
    _ ≤ |(A : ℝ) * (rho a - rho b)| +
          |((A : ℝ) - r) * rho b| := abs_add_le _ _
    _ = (A : ℝ) * |rho a - rho b| +
          (r - (A : ℝ)) * rho b := by
      rw [abs_mul, abs_mul, abs_of_nonneg hApos.le,
        abs_of_nonpos (sub_nonpos.mpr hAr), abs_of_nonneg hrhob0]
      ring
    _ ≤ (A : ℝ) * (b - a) +
          (r - (A : ℝ)) * 1 := by gcongr
    _ ≤ 2 + 1 := add_le_add hAdiff (by simpa using hgap1)
    _ = 3 := by norm_num

/-- The integer quotient in the exact largest-prime recurrence and its real
Dickman model differ by at most three. -/
theorem dickmanPrimeSummand_floor_stability (X p : ℕ)
    (hp2 : 2 ≤ p) (hpX : p ≤ X)
    (hq5 : Real.log (X : ℝ) / Real.log (p : ℝ) ≤ 5) :
    |((X / p : ℕ) : ℝ) * rho (dickmanU (X / p) p) -
        dickmanPrimeSummand X p| ≤ 3 := by
  have hp0 : 0 < p := by omega
  have hX0 : 0 < X := hp0.trans_le hpX
  have hA : 1 ≤ X / p := by
    apply (Nat.le_div_iff_mul_le hp0).2
    simpa using hpX
  have hAr : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / (p : ℝ) :=
    Nat.cast_div_le
  have hupperNat : X < (X / p + 1) * p :=
    (Nat.div_lt_iff_lt_mul hp0).mp (Nat.lt_succ_self (X / p))
  have hrA : (X : ℝ) / (p : ℝ) < ((X / p : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ (by exact_mod_cast hp0 : (0 : ℝ) < p)).2
    exact_mod_cast hupperNat
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hlogdiv :
      Real.log ((X : ℝ) / (p : ℝ)) =
        Real.log (X : ℝ) - Real.log (p : ℝ) := by
    rw [Real.log_div (by exact_mod_cast hX0.ne' : (X : ℝ) ≠ 0)
      (by exact_mod_cast hp0.ne' : (p : ℝ) ≠ 0)]
  have hb4 : Real.log ((X : ℝ) / (p : ℝ)) /
      Real.log (p : ℝ) ≤ 4 := by
    rw [hlogdiv]
    apply (div_le_iff₀ hlogp).2
    have hq := (div_le_iff₀ hlogp).mp hq5
    linarith
  have hcoord : Real.log ((X : ℝ) / (p : ℝ)) /
      Real.log (p : ℝ) =
        Real.log (X : ℝ) / Real.log (p : ℝ) - 1 := by
    rw [hlogdiv]
    field_simp
  have hstab := rho_floor_kernel_stability (X / p) hA hAr hrA
    (by exact_mod_cast hp2) hb4
  rw [hcoord] at hstab
  simpa only [dickmanU, dickmanPrimeSummand] using hstab


/-- Chebyshev test weight whose prime mass is `1 / (p log p)`. -/
noncomputable def invLogThetaWeight (m : ℕ) : ℝ :=
  1 / ((m : ℝ) * Real.log (m : ℝ) ^ 2)

noncomputable def invLogContinuousWeight (t : ℝ) : ℝ :=
  1 / (t * Real.log t ^ 2)

noncomputable def invLogAntiderivative (t : ℝ) : ℝ :=
  -(1 / Real.log t)

theorem invLogContinuousWeight_nat (m : ℕ) :
    invLogContinuousWeight (m : ℝ) = invLogThetaWeight m := rfl

theorem hasDerivAt_invLogContinuousWeight {t : ℝ} (ht : t ≠ 0)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt invLogContinuousWeight
      (-(Real.log t + 2) / (t ^ 2 * Real.log t ^ 3)) t := by
  unfold invLogContinuousWeight
  have hlogsq : HasDerivAt (fun s : ℝ => Real.log s ^ 2)
      (2 * Real.log t / t) t := by
    convert (Real.hasDerivAt_log ht).pow 2 using 1 <;> try rfl
    all_goals ring
  have hden : HasDerivAt (fun s : ℝ => s * Real.log s ^ 2)
      (Real.log t ^ 2 + 2 * Real.log t) t := by
    convert (hasDerivAt_id t).mul hlogsq using 1 <;> try rfl
    all_goals simp only [id_eq]
    all_goals field_simp [ht]
  have hden0 : t * Real.log t ^ 2 ≠ 0 :=
    mul_ne_zero ht (pow_ne_zero 2 hlog)
  have hraw := (hasDerivAt_const t (1 : ℝ)).div hden hden0
  convert hraw using 1 <;> try rfl
  all_goals field_simp [ht, hlog]
  all_goals ring

theorem invLog_deriv_bound {k : ℕ} (hk : 2 ≤ k) {t : ℝ}
    (ht : (k : ℝ) ≤ t) :
    |-(Real.log t + 2) / (t ^ 2 * Real.log t ^ 3)| ≤
      20 / (k : ℝ) ^ 2 := by
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have ht2 : (2 : ℝ) ≤ t := hkR.trans ht
  have htpos : 0 < t := by linarith
  have hkpos : (0 : ℝ) < (k : ℝ) := by positivity
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log t := by
    have hmono : Real.log 2 ≤ Real.log t :=
      Real.log_le_log (by norm_num) ht2
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log t := by linarith
  have hpoly : (Real.log t + 2) / Real.log t ^ 3 ≤ 20 := by
    apply (div_le_iff₀ (pow_pos hlogpos 3)).2
    have hfac : 0 ≤ (2 * Real.log t - 1) *
        (10 * Real.log t ^ 2 + 5 * Real.log t + 2) := by
      apply mul_nonneg
      · linarith
      · nlinarith [sq_nonneg (Real.log t)]
    nlinarith
  rw [abs_div, abs_neg, abs_mul,
    abs_of_nonneg (sq_nonneg t), abs_of_pos (pow_pos hlogpos 3),
    abs_of_nonneg (by linarith : 0 ≤ Real.log t + 2)]
  calc
    (Real.log t + 2) / (t ^ 2 * Real.log t ^ 3) =
        ((Real.log t + 2) / Real.log t ^ 3) / t ^ 2 := by field_simp
    _ ≤ 20 / t ^ 2 := div_le_div_of_nonneg_right hpoly (sq_nonneg t)
    _ ≤ 20 / (k : ℝ) ^ 2 := by gcongr

theorem invLogWeight_cell_oscillation {k : ℕ} (hk : 2 ≤ k)
    {s t : ℝ} (hs : s ∈ Set.Icc (k : ℝ) (k + 1 : ℕ))
    (ht : t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
    |invLogContinuousWeight s - invLogContinuousWeight t| ≤
      (20 / (k : ℝ) ^ 2) * |s - t| := by
  have hdiff (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      DifferentiableAt ℝ invLogContinuousWeight u := by
    have hu2 : (2 : ℝ) ≤ u := (by exact_mod_cast hk : (2 : ℝ) ≤ k).trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (hasDerivAt_invLogContinuousWeight hu0 hlogu).differentiableAt
  have hbound (u : ℝ) (hu : u ∈ Set.Icc (k : ℝ) (k + 1 : ℕ)) :
      ‖deriv invLogContinuousWeight u‖ ≤ 20 / (k : ℝ) ^ 2 := by
    have hu2 : (2 : ℝ) ≤ u := (by exact_mod_cast hk : (2 : ℝ) ≤ k).trans hu.1
    have hu0 : u ≠ 0 := by linarith
    have hlogu : Real.log u ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    rw [(hasDerivAt_invLogContinuousWeight hu0 hlogu).deriv,
      Real.norm_eq_abs]
    exact invLog_deriv_bound hk hu.1
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (convex_Icc (k : ℝ) (k + 1 : ℕ)) ht hs

theorem invLogThetaWeight_abs_le {m : ℕ} (hm : 2 ≤ m) :
    |invLogThetaWeight m| ≤ 4 / (m : ℝ) := by
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log (m : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (m : ℝ) := by
      apply Real.log_le_log
      · norm_num
      · exact_mod_cast hm
    nlinarith [Real.log_two_gt_d9]
  have hmpos : (0 : ℝ) < m := by positivity
  have hlogpos : 0 < Real.log (m : ℝ) := by linarith
  rw [invLogThetaWeight, abs_div, abs_one, abs_mul,
    abs_of_pos hmpos, abs_pow, abs_of_pos hlogpos]
  apply (div_le_div_iff₀ (mul_pos hmpos (sq_pos_of_pos hlogpos)) hmpos).2
  nlinarith [sq_nonneg (Real.log (m : ℝ) - 1 / 2)]

theorem invLogWeight_pnt_bound {C : ℝ} (hC : 0 ≤ C)
    {X₀ z Y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzY : z < Y)
    (hlogz : 1 ≤ Real.log (z : ℝ))
    (hlogY : Real.log (Y : ℝ) ≤ 5 * Real.log (z : ℝ)) :
    |primeThetaWeightedInterval invLogThetaWeight z Y -
        integerAbelMain invLogThetaWeight z Y| ≤
      128 * C / Real.log (z : ℝ) ^ 2 := by
  have hlogzpos : 0 < Real.log (z : ℝ) := lt_of_lt_of_le (by norm_num) hlogz
  have hlogzY : Real.log (z : ℝ) ≤ Real.log (Y : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hzY.le
  have hgeneric := primeThetaWeightedInterval_pnt_bound
    invLogThetaWeight (A := (3 : ℝ)) hbound hX₀z hzY
  simp only [Real.rpow_ofNat] at hgeneric
  have htermY : |invLogThetaWeight Y| *
      (C * ((Y : ℝ) / Real.log (Y : ℝ) ^ (3 : ℕ))) ≤
      4 * C / Real.log (z : ℝ) ^ 2 := by
    have hY0 : (Y : ℝ) ≠ 0 := by
      exact_mod_cast (show Y ≠ 0 by omega)
    calc
      _ ≤ (4 / (Y : ℝ)) *
          (C * ((Y : ℝ) / Real.log (Y : ℝ) ^ 3)) := by
        gcongr
        exact invLogThetaWeight_abs_le (hz.trans hzY.le)
      _ = 4 * C / Real.log (Y : ℝ) ^ 3 := by field_simp [hY0]
      _ ≤ 4 * C / Real.log (z : ℝ) ^ 3 := by gcongr
      _ ≤ 4 * C / Real.log (z : ℝ) ^ 2 := by
        have hfac : 0 ≤ 4 * C := by positivity
        apply div_le_div_of_nonneg_left hfac (pow_pos hlogzpos 2)
        nlinarith [mul_le_mul_of_nonneg_left hlogz hlogzpos.le]
  have htermZ : |invLogThetaWeight (z + 1)| *
      (C * ((z : ℝ) / Real.log (z : ℝ) ^ (3 : ℕ))) ≤
      4 * C / Real.log (z : ℝ) ^ 2 := by
    have hf := invLogThetaWeight_abs_le (m := z + 1) (by omega)
    have hf' : |invLogThetaWeight (z + 1)| ≤ 4 / (z : ℝ) :=
      hf.trans (by gcongr; omega)
    calc
      _ ≤ (4 / (z : ℝ)) *
          (C * ((z : ℝ) / Real.log (z : ℝ) ^ 3)) := by gcongr
      _ = 4 * C / Real.log (z : ℝ) ^ 3 := by field_simp
      _ ≤ 4 * C / Real.log (z : ℝ) ^ 2 := by
        have hfac : 0 ≤ 4 * C := by positivity
        apply div_le_div_of_nonneg_left hfac (pow_pos hlogzpos 2)
        nlinarith [mul_le_mul_of_nonneg_left hlogz hlogzpos.le]
  have hvar : (∑ m ∈ Finset.Ioc z (Y - 1),
      |invLogThetaWeight (m + 1) - invLogThetaWeight m| *
        (C * ((m : ℝ) / Real.log (m : ℝ) ^ (3 : ℕ)))) ≤
      120 * C / Real.log (z : ℝ) ^ 2 := by
    have hpoint : ∀ m ∈ Finset.Ioc z (Y - 1),
        |invLogThetaWeight (m + 1) - invLogThetaWeight m| *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3)) ≤
          (20 * C / Real.log (z : ℝ) ^ 3) * (1 / (m : ℝ)) := by
      intro m hm
      rw [Finset.mem_Ioc] at hm
      have hm2 : 2 ≤ m := hz.trans hm.1.le
      have hdiff : |invLogThetaWeight (m + 1) -
          invLogThetaWeight m| ≤ 20 / (m : ℝ) ^ 2 := by
        rw [← invLogContinuousWeight_nat,
          ← invLogContinuousWeight_nat]
        have hs : ((m + 1 : ℕ) : ℝ) ∈ Set.Icc (m : ℝ) (m + 1 : ℕ) := by
          constructor <;> norm_num
        have ht : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + 1 : ℕ) := by
          constructor <;> norm_num
        simpa using invLogWeight_cell_oscillation hm2 hs ht
      have hlogzm : Real.log (z : ℝ) ≤ Real.log (m : ℝ) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast hm.1.le
      have hlogmpos : 0 < Real.log (m : ℝ) := hlogzpos.trans_le hlogzm
      calc
        _ ≤ (20 / (m : ℝ) ^ 2) *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3)) := by gcongr
        _ = (20 * C / Real.log (m : ℝ) ^ 3) * (1 / (m : ℝ)) := by
          field_simp
        _ ≤ (20 * C / Real.log (z : ℝ) ^ 3) * (1 / (m : ℝ)) := by
          gcongr
    have hsum : (∑ m ∈ Finset.Ioc z (Y - 1),
        |invLogThetaWeight (m + 1) - invLogThetaWeight m| *
          (C * ((m : ℝ) / Real.log (m : ℝ) ^ 3))) ≤
        (20 * C / Real.log (z : ℝ) ^ 3) *
          (∑ m ∈ Finset.Ioc z (Y - 1), 1 / (m : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun m hm => hpoint m hm
    have hhar : (∑ m ∈ Finset.Ioc z (Y - 1), 1 / (m : ℝ)) ≤
        6 * Real.log (z : ℝ) := by
      calc
        _ ≤ 1 + Real.log (Y : ℝ) := by
          exact (harmonic_Ioc_le (z := z) (y := Y - 1)).trans (by
            have hlogsub : Real.log ((Y - 1 : ℕ) : ℝ) ≤
                Real.log (Y : ℝ) := by
              apply Real.log_le_log
              · exact_mod_cast (show 0 < Y - 1 by omega)
              · exact_mod_cast (Nat.sub_le Y 1)
            linarith)
        _ ≤ 6 * Real.log (z : ℝ) := by linarith
    calc
      _ ≤ (20 * C / Real.log (z : ℝ) ^ 3) *
          (∑ m ∈ Finset.Ioc z (Y - 1), 1 / (m : ℝ)) := hsum
      _ ≤ (20 * C / Real.log (z : ℝ) ^ 3) *
          (6 * Real.log (z : ℝ)) := by gcongr
      _ = 120 * C / Real.log (z : ℝ) ^ 2 := by field_simp; ring
  calc
    _ ≤ |invLogThetaWeight Y| *
          (C * ((Y : ℝ) / Real.log (Y : ℝ) ^ (3 : ℕ))) +
        |invLogThetaWeight (z + 1)| *
          (C * ((z : ℝ) / Real.log (z : ℝ) ^ (3 : ℕ))) +
        ∑ m ∈ Finset.Ioc z (Y - 1),
          |invLogThetaWeight (m + 1) - invLogThetaWeight m| *
            (C * ((m : ℝ) / Real.log (m : ℝ) ^ (3 : ℕ))) := hgeneric
    _ ≤ 4 * C / Real.log (z : ℝ) ^ 2 +
        4 * C / Real.log (z : ℝ) ^ 2 +
        120 * C / Real.log (z : ℝ) ^ 2 := by
      exact add_le_add (add_le_add htermY htermZ) hvar
    _ = 128 * C / Real.log (z : ℝ) ^ 2 := by ring

theorem hasDerivAt_invLogAntiderivative {t : ℝ} (ht : t ≠ 0)
    (hlog : Real.log t ≠ 0) :
    HasDerivAt invLogAntiderivative
      (invLogContinuousWeight t) t := by
  unfold invLogAntiderivative invLogContinuousWeight
  have hraw := (hasDerivAt_const t (1 : ℝ)).div
    (Real.hasDerivAt_log ht) hlog
  convert hraw.neg using 1 <;> try rfl
  all_goals ring

theorem integral_invLogContinuousWeight {z Y : ℕ}
    (hz : 2 ≤ z) (hzY : z ≤ Y) :
    (∫ t in (z : ℝ)..(Y : ℝ), invLogContinuousWeight t) =
      1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ) := by
  have hcont : ContinuousOn invLogAntiderivative
      (Set.Icc (z : ℝ) (Y : ℝ)) := by
    intro t htI
    have ht2 : (2 : ℝ) ≤ t := (by exact_mod_cast hz : (2 : ℝ) ≤ z).trans htI.1
    have ht0 : t ≠ 0 := by linarith
    have hlogt : Real.log t ≠ 0 :=
      Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
    exact (hasDerivAt_invLogAntiderivative ht0 hlogt).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable invLogContinuousWeight
      MeasureTheory.volume (z : ℝ) (Y : ℝ) := by
    have hcontW : ContinuousOn invLogContinuousWeight
        (Set.Icc (z : ℝ) (Y : ℝ)) := by
      intro t htI
      have ht2 : (2 : ℝ) ≤ t := (by exact_mod_cast hz : (2 : ℝ) ≤ z).trans htI.1
      have ht0 : t ≠ 0 := by linarith
      have hlogt : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
      exact (hasDerivAt_invLogContinuousWeight ht0 hlogt).continuousAt.continuousWithinAt
    rw [← Set.uIcc_of_le (by exact_mod_cast hzY)] at hcontW
    exact hcontW.intervalIntegrable
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := invLogAntiderivative) (f' := invLogContinuousWeight)
    (by exact_mod_cast hzY) hcont
    (fun t htI => by
      have ht2 : (2 : ℝ) < t := (by exact_mod_cast hz : (2 : ℝ) ≤ z).trans_lt htI.1
      exact hasDerivAt_invLogAntiderivative (by linarith)
        (Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)))
    hint
  rw [hfund]
  simp only [invLogAntiderivative]
  ring

theorem invLogWeight_sum_integral_bound {z Y : ℕ}
    (hz : 2 ≤ z) (hzY : z ≤ Y) :
    |(∑ m ∈ Finset.Ioc z Y, invLogThetaWeight m) -
        ∫ t in (z : ℝ)..(Y : ℝ), invLogContinuousWeight t| ≤
      40 / (z : ℝ) := by
  have hint : ∀ k ∈ Set.Ico z Y,
      IntervalIntegrable invLogContinuousWeight MeasureTheory.volume
        (k : ℝ) (k + 1 : ℕ) := by
    intro k hk
    rw [Set.mem_Ico] at hk
    have hk2 : 2 ≤ k := hz.trans hk.1
    have hcont : ContinuousOn invLogContinuousWeight
        (Set.Icc (k : ℝ) (k + 1 : ℕ)) := by
      intro t htI
      have ht2 : (2 : ℝ) ≤ t := (by exact_mod_cast hk2 : (2 : ℝ) ≤ k).trans htI.1
      have ht0 : t ≠ 0 := by linarith
      have hlogt : Real.log t ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
      exact (hasDerivAt_invLogContinuousWeight ht0 hlogt).continuousAt.continuousWithinAt
    rw [← Set.uIcc_of_le (by norm_num : (k : ℝ) ≤ (k + 1 : ℕ))] at hcont
    exact hcont.intervalIntegrable
  have hosc : ∀ k ∈ Finset.Ico z Y,
      ∀ t ∈ Set.Icc (k : ℝ) (k + 1 : ℕ),
        |invLogContinuousWeight ((k : ℝ) + 1) -
          invLogContinuousWeight t| ≤ 20 / (k : ℝ) ^ 2 := by
    intro k hk t htI
    rw [Finset.mem_Ico] at hk
    have hk2 : 2 ≤ k := hz.trans hk.1
    have hs : ((k + 1 : ℕ) : ℝ) ∈ Set.Icc (k : ℝ) (k + 1 : ℕ) := by
      constructor <;> norm_num
    have h := invLogWeight_cell_oscillation hk2 hs htI
    simp only [Nat.cast_add, Nat.cast_one] at h
    apply h.trans
    have htI' : (k : ℝ) ≤ t ∧ t ≤ (k : ℝ) + 1 := by
      exact ⟨htI.1, by simpa only [Nat.cast_add, Nat.cast_one] using htI.2⟩
    have hdist0 : 0 ≤ (k : ℝ) + 1 - t := by linarith [htI'.2]
    rw [abs_of_nonneg hdist0]
    have hdist1 : (k : ℝ) + 1 - t ≤ 1 := by linarith [htI'.1]
    calc
      _ ≤ (20 / (k : ℝ) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left hdist1
          (div_nonneg (by norm_num) (sq_nonneg (k : ℝ)))
      _ = 20 / (k : ℝ) ^ 2 := by ring
  have hR := sum_integral_error_bound invLogContinuousWeight
    (fun k => 20 / (k : ℝ) ^ 2) hzY hint hosc
  simp only [invLogContinuousWeight_nat] at hR
  calc
    _ ≤ ∑ k ∈ Finset.Ico z Y, 20 / (k : ℝ) ^ 2 := hR
    _ = 20 * ∑ k ∈ Finset.Ico z Y, 1 / (k : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ 20 * (2 / (z : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ico_inv_sq_le (show 1 ≤ z by omega)) (by norm_num)
    _ = 40 / (z : ℝ) := by ring

noncomputable def primeInvLogSum (z Y : ℕ) : ℝ :=
  ∑ p ∈ (Y + 1).primesBelow \ (z + 1).primesBelow,
    1 / ((p : ℝ) * Real.log (p : ℝ))

theorem primeThetaWeightedInterval_invLog (z Y : ℕ) :
    primeThetaWeightedInterval invLogThetaWeight z Y =
      primeInvLogSum z Y := by
  rw [primeThetaWeightedInterval, primeInvLogSum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime :=
    Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hlog : Real.log (p : ℝ) ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast hpprime.pos) (by exact_mod_cast hpprime.ne_one)
  rw [invLogThetaWeight]
  field_simp [hlog]

theorem primeInvLogSum_contraction_of_bound {C : ℝ} (hC : 0 ≤ C)
    {X₀ z Y : ℕ}
    (hbound : ∀ T, X₀ ≤ T →
      |primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ (3 : ℝ)))
    (hX₀z : X₀ ≤ z) (hz : 2 ≤ z) (hzY : z < Y)
    (hlogz : 1 ≤ Real.log (z : ℝ))
    (hlogY : Real.log (Y : ℝ) ≤ 5 * Real.log (z : ℝ))
    (hsmall : 128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ) ≤
      1 / (10 * Real.log (z : ℝ))) :
    primeInvLogSum z Y ≤ 9 / (10 * Real.log (z : ℝ)) := by
  have hlogzpos : 0 < Real.log (z : ℝ) := lt_of_lt_of_le (by norm_num) hlogz
  have hlogzY : Real.log (z : ℝ) ≤ Real.log (Y : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hzY.le
  have hlogYpos : 0 < Real.log (Y : ℝ) := hlogzpos.trans_le hlogzY
  have hpnt := invLogWeight_pnt_bound hC hbound hX₀z hz hzY hlogz hlogY
  rw [primeThetaWeightedInterval_invLog,
    integerAbelMain_eq_sum_Ioc invLogThetaWeight hzY] at hpnt
  have hriemann := invLogWeight_sum_integral_bound hz hzY.le
  rw [integral_invLogContinuousWeight hz hzY.le] at hriemann
  have htotal : |primeInvLogSum z Y -
      (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ))| ≤
      128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ) := by
    calc
      _ = |(primeInvLogSum z Y -
            ∑ m ∈ Finset.Ioc z Y, invLogThetaWeight m) +
          ((∑ m ∈ Finset.Ioc z Y, invLogThetaWeight m) -
            (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ)))| := by ring_nf
      _ ≤ |primeInvLogSum z Y -
            ∑ m ∈ Finset.Ioc z Y, invLogThetaWeight m| +
          |(∑ m ∈ Finset.Ioc z Y, invLogThetaWeight m) -
            (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ))| :=
        abs_add_le _ _
      _ ≤ _ := add_le_add hpnt hriemann
  have hmain : 1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ) ≤
      4 / (5 * Real.log (z : ℝ)) := by
    have hfrac : (1 / 5 : ℝ) ≤
        Real.log (z : ℝ) / Real.log (Y : ℝ) := by
      apply (le_div_iff₀ hlogYpos).2
      linarith
    calc
      1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ) =
          (1 - Real.log (z : ℝ) / Real.log (Y : ℝ)) /
            Real.log (z : ℝ) := by field_simp
      _ ≤ (4 / 5 : ℝ) / Real.log (z : ℝ) := by
        exact div_le_div_of_nonneg_right (by linarith) hlogzpos.le
      _ = 4 / (5 * Real.log (z : ℝ)) := by ring
  have hupper : primeInvLogSum z Y ≤
      (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ)) +
        (128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ)) := by
    have hsigned := (le_abs_self (primeInvLogSum z Y -
      (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ)))).trans htotal
    linarith
  calc
    primeInvLogSum z Y ≤
        (1 / Real.log (z : ℝ) - 1 / Real.log (Y : ℝ)) +
          (128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ)) := hupper
    _ ≤ 4 / (5 * Real.log (z : ℝ)) +
          1 / (10 * Real.log (z : ℝ)) := add_le_add hmain hsmall
    _ = 9 / (10 * Real.log (z : ℝ)) := by ring

/-- The contraction estimate has an absolute lower threshold; all analytic
hypotheses are discharged from the medium-strength prime number theorem. -/
theorem exists_primeInvLogSum_contraction_threshold :
    ∃ Z₀ : ℕ, ∀ {z Y : ℕ}, Z₀ ≤ z → z < Y →
      Real.log (Y : ℝ) ≤ 5 * Real.log (z : ℝ) →
      primeInvLogSum z Y ≤ 9 / (10 * Real.log (z : ℝ)) := by
  obtain ⟨C, hCpos, X₀, hbound⟩ :=
    exists_primeLogSumUpTo_error_bound (3 : ℝ)
  have hlogTop : Filter.Tendsto (fun z : ℕ => Real.log (z : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvlog : Filter.Tendsto
      (fun z : ℕ => (Real.log (z : ℝ))⁻¹)
      Filter.atTop (nhds 0) := hlogTop.inv_tendsto_atTop
  have hlogdiv : Filter.Tendsto
      (fun z : ℕ => Real.log (z : ℝ) / (z : ℝ))
      Filter.atTop (nhds 0) := by
    convert Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ)) using 1 ; rfl
  have hsmallT : Filter.Tendsto
      (fun z : ℕ =>
        128 * C * (Real.log (z : ℝ))⁻¹ +
          40 * (Real.log (z : ℝ) / (z : ℝ)))
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul hinvlog).add
      (tendsto_const_nhds.mul hlogdiv) using 1
    norm_num
  have hsmallEvent : ∀ᶠ z : ℕ in Filter.atTop,
      128 * C * (Real.log (z : ℝ))⁻¹ +
          40 * (Real.log (z : ℝ) / (z : ℝ)) ≤ 1 / 10 := by
    have hlt := hsmallT.eventually
      (Iio_mem_nhds (show (0 : ℝ) < 1 / 10 by norm_num))
    filter_upwards [hlt] with z hz
    exact hz.le
  have hlogEvent : ∀ᶠ z : ℕ in Filter.atTop,
      1 ≤ Real.log (z : ℝ) :=
    hlogTop.eventually (Filter.eventually_ge_atTop 1)
  have hall : ∀ᶠ z : ℕ in Filter.atTop,
      X₀ ≤ z ∧ 2 ≤ z ∧ 1 ≤ Real.log (z : ℝ) ∧
        128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ) ≤
          1 / (10 * Real.log (z : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop (max X₀ 2),
      hlogEvent, hsmallEvent] with z hzbase hlogz hscaled
    have hX₀z : X₀ ≤ z := (le_max_left X₀ 2).trans hzbase
    have hz2 : 2 ≤ z := (le_max_right X₀ 2).trans hzbase
    have hlogpos : 0 < Real.log (z : ℝ) :=
      lt_of_lt_of_le (by norm_num) hlogz
    have hmul :
        (128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ)) *
            Real.log (z : ℝ) ≤ 1 / 10 := by
      calc
        _ = 128 * C * (Real.log (z : ℝ))⁻¹ +
            40 * (Real.log (z : ℝ) / (z : ℝ)) := by
              field_simp [hlogpos.ne']
        _ ≤ 1 / 10 := hscaled
    have hsmall :
        128 * C / Real.log (z : ℝ) ^ 2 + 40 / (z : ℝ) ≤
          (1 / 10) / Real.log (z : ℝ) :=
      (le_div_iff₀ hlogpos).2 hmul
    refine ⟨hX₀z, hz2, hlogz, ?_⟩
    convert hsmall using 1
    ring
  obtain ⟨Z₀, hZ₀⟩ := Filter.eventually_atTop.mp hall
  refine ⟨Z₀, ?_⟩
  intro z Y hz hzY hlogY
  obtain ⟨hX₀z, hz2, hlogz, hsmall⟩ := hZ₀ z hz
  exact primeInvLogSum_contraction_of_bound hCpos.le hbound
    hX₀z hz2 hzY hlogz hlogY hsmall

end FriableIntegers.FriableAsymptotic
