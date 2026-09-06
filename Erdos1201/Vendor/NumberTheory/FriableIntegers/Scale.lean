module

public import Erdos1201.Vendor.NumberTheory.FriableIntegers.ArithmeticModel
public import Erdos1201.Vendor.NumberTheory.FriableIntegers.Definitions

@[expose] public section

/-!
# Exact scale identities

This file records the elementary identities behind the fixed choice
`y = n^(2/9)` used throughout the marked and smooth bridge.  Keeping them as
equalities avoids repeatedly treating `U = 9/2` and the four-mark cofactor
margin as informal arithmetic simplifications.
-/

open Filter Topology

namespace FriableIntegers.Scale

open ArithmeticModel

/-- The logarithmic scale `L = log n`. -/
noncomputable def L (n : ℕ) : ℝ :=
  Real.log (n : ℝ)

/-- The smooth-number parameter before it is simplified to `9/2`. -/
noncomputable def U (n : ℕ) : ℝ :=
  L n / Real.log (y n)


theorem L_pos {n : ℕ} (hn : 1 < n) : 0 < L n := by
  exact Real.log_pos (by exact_mod_cast hn)

theorem y_pos {n : ℕ} (hn : 0 < n) : 0 < y n := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

/-- `log y = (2/9) log n`, with no asymptotic error. -/
theorem log_y {n : ℕ} (hn : 0 < n) :
    Real.log (y n) = (2 / 9 : ℝ) * L n := by
  simpa [y, L] using
    (Real.log_rpow (by exact_mod_cast hn : (0 : ℝ) < n) (2 / 9 : ℝ))


/-- Four marked prime factors use precisely the exponent `8/9`. -/
theorem y_pow_four (n : ℕ) :
    y n ^ 4 = (n : ℝ) ^ (8 / 9 : ℝ) := by
  calc
    y n ^ 4 = ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 4 := rfl
    _ = (n : ℝ) ^ ((2 / 9 : ℝ) * (4 : ℕ)) :=
      (Real.rpow_mul_natCast (Nat.cast_nonneg n) (2 / 9 : ℝ) 4).symm
    _ = (n : ℝ) ^ (8 / 9 : ℝ) := by norm_num

/-- Three marked prime factors use precisely the exponent `2/3`. -/
theorem y_pow_three (n : ℕ) :
    y n ^ 3 = (n : ℝ) ^ (2 / 3 : ℝ) := by
  calc
    y n ^ 3 = ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 3 := rfl
    _ = (n : ℝ) ^ ((2 / 9 : ℝ) * (3 : ℕ)) :=
      (Real.rpow_mul_natCast (Nat.cast_nonneg n) (2 / 9 : ℝ) 3).symm
    _ = (n : ℝ) ^ (2 / 3 : ℝ) := by norm_num

theorem y_pow_two (n : ℕ) :
    y n ^ 2 = (n : ℝ) ^ (4 / 9 : ℝ) := by
  calc
    y n ^ 2 = ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 2 := rfl
    _ = (n : ℝ) ^ ((2 / 9 : ℝ) * (2 : ℕ)) :=
      (Real.rpow_mul_natCast (Nat.cast_nonneg n) (2 / 9 : ℝ) 2).symm
    _ = (n : ℝ) ^ (4 / 9 : ℝ) := by norm_num

/-- The floored scale never exceeds `√n`: `⌊y n⌋² ≤ n` for `n ≥ 1`. -/
theorem yNat_mul_self_le_self {n : ℕ} (hn : 1 ≤ n) : yNat n * yNat n ≤ n := by
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
  have hyFloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
  have hyFloorNonneg : (0 : ℝ) ≤ yNat n := by positivity
  have hsq : (yNat n : ℝ) ^ 2 ≤ y n ^ 2 :=
    (sq_le_sq₀ hyFloorNonneg hyNonneg).2 hyFloor
  have hpow : (n : ℝ) ^ (4 / 9 : ℝ) ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hnOne
        (by norm_num : (4 / 9 : ℝ) ≤ 1)
  rw [y_pow_two] at hsq
  have hcast : ((yNat n * yNat n : ℕ) : ℝ) ≤ (n : ℝ) := by
    push_cast
    simpa only [pow_two] using hsq.trans hpow
  exact_mod_cast hcast

/-- The smallest cofactor after four marks is exactly `n^(1/9)`. -/
theorem cofactor_four {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / y n ^ 4 = (n : ℝ) ^ (1 / 9 : ℝ) := by
  rw [y_pow_four]
  calc
    (n : ℝ) / (n : ℝ) ^ (8 / 9 : ℝ) =
        (n : ℝ) ^ ((1 : ℝ) - 8 / 9) := by
          rw [Real.rpow_sub (by exact_mod_cast hn), Real.rpow_one]
    _ = (n : ℝ) ^ (1 / 9 : ℝ) := by norm_num


/-- The accumulated two-mark endpoint scale used in the row estimates. -/
noncomputable def endpointRatio (n : ℕ) : ℝ :=
  y n ^ 2 * L n ^ 2 / (n : ℝ)

theorem endpointRatio_eq {n : ℕ} (hn : 0 < n) :
    endpointRatio n = L n ^ 2 / (n : ℝ) ^ (5 / 9 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      (n : ℝ) ^ (4 / 9 : ℝ) * (n : ℝ) ^ (5 / 9 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  rw [endpointRatio, y_pow_two]
  field_simp [(Real.rpow_pos_of_pos hnR (5 / 9 : ℝ)).ne', hnR.ne']
  nlinarith

/-- In particular, all `y^2 L^2 / n` endpoint errors vanish. -/
theorem tendsto_endpointRatio_zero :
    Tendsto endpointRatio atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (5 / 9 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 5 / 9)).tendsto_div_nhds_zero
  have hnat : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (5 / 9 : ℝ))
      atTop (𝓝 0) := by
    apply (hreal.comp tendsto_natCast_atTop_atTop).congr'
    exact Eventually.of_forall fun _ ↦ by
      simp only [Function.comp_apply, Real.rpow_two]
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa [L] using (endpointRatio_eq hn).symm

/-- The squared smooth cutoff `⌊y⌋²` is eventually bounded by the exact
`secondOrderScale / L` scale, obtained by squaring the vanishing
`endpointRatio` limit. -/
theorem eventually_yNat_sq_le_secondOrderScale_div_L :
    ∀ᶠ n : ℕ in atTop,
      (yNat n : ℝ) ^ 2 <= secondOrderScale n / L n := by
  have hratio := tendsto_endpointRatio_zero.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hratio, eventually_ge_atTop 2]
      with n hratioN hn
  have hnPos : 0 < n := by omega
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnPos
  have hL : 0 < L n := L_pos hn
  have hyNonneg : 0 <= y n := (y_pos hnPos).le
  have hyFloor : (yNat n : ℝ) <= y n :=
    Nat.floor_le hyNonneg
  have hySq : (yNat n : ℝ) ^ 2 <= y n ^ 2 :=
    (sq_le_sq₀ (Nat.cast_nonneg _) hyNonneg).2 hyFloor
  have hratioNat :
      (yNat n : ℝ) ^ 2 * L n ^ 2 / (n : ℝ) <= 1 := by
    calc
      (yNat n : ℝ) ^ 2 * L n ^ 2 / (n : ℝ) <=
          y n ^ 2 * L n ^ 2 / (n : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hySq (sq_nonneg _)) hnReal.le
      _ = endpointRatio n := by rfl
      _ <= 1 := hratioN.le
  have hySqScale :
      (yNat n : ℝ) ^ 2 <= (n : ℝ) / L n ^ 2 := by
    apply (le_div_iff₀ (pow_pos hL 2)).2
    have hcross := (div_le_iff₀ hnReal).1 hratioNat
    simpa only [one_mul] using hcross
  have htarget :
      (n : ℝ) / L n ^ 2 = secondOrderScale n / L n := by
    change (n : ℝ) / Real.log (n : ℝ) ^ 2 =
      ((n : ℝ) / Real.log (n : ℝ)) / Real.log (n : ℝ)
    ring
  exact hySqScale.trans_eq htarget

/-- A product-log rate together with eventual nonnegativity implies ordinary
convergence to zero. -/
theorem tendsto_zero_of_eventually_nonneg_mul_logL_zero
    (epsilon : ℕ → ℝ)
    (hepsilon : ∀ᶠ n : ℕ in atTop, 0 ≤ epsilon n)
    (hrate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0)) :
    Tendsto epsilon atTop (nhds 0) := by
  have hLTop : Tendsto L atTop atTop := by
    convert Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop using 1
    ext n
    rfl
  have hlogOne : ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log (L n) :=
    (Real.tendsto_log_atTop.comp hLTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hupper : ∀ᶠ n : ℕ in atTop,
      epsilon n ≤ epsilon n * Real.log (L n) := by
    filter_upwards [hepsilon, hlogOne] with n hn hlog
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hn
  exact squeeze_zero' hepsilon hupper hrate

end FriableIntegers.Scale
