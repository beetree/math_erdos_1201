/-
Copyright (c) 2026 Antigravity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/
import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Ranges
import Erdos1201.MR.Setup
import Erdos1201.MR.Decomposition.Lemma12Assembly
import Erdos1201.MR.Decomposition.Lemma12
import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.MR.Analysis.MeanValueTheorem
import Erdos1201.MR.Analysis.WellSpaced
import Erdos1201.MR.Parseval.WindowEnergy
import Erdos1201.MR.Prop1.Split
import Erdos1201.MR.Prop1.UsetCard
import Erdos1201.MR.Prop1.UsetSmall
import Erdos1201.MR.Prop1.UsetLarge
import Erdos1201.MR.Sieve.RangeSieveUpperHR
import Erdos1201.MR.Polynomials.PrimePolyMoments

open MeasureTheory intervalIntegral
open scoped BigOperators Real Topology
open Classical Filter

namespace Erdos1201.MR

/-!
# Assembly of the Exceptional Set Uset Bounds (Proposition 1, Section 8.3)

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the assembly of the exceptional set ($U$-part) bound of Proposition 1:
1. Uniform upper bound on the integral of $\|F_u\|^2$ over $Uset$ via Montgomery's mean value theorem;
2. Application of Matomäki–Radziwiłł Lemma 12 (`integral_norm_sq_F_le_sum_QR`) to $U = Uset$;
3. Halberstam–Richert sieve upper bound on the unsifted fraction on dyadic intervals;
4. Pointwise regularity, continuity, measurability, and boundedness of the product Dirichlet polynomial $\|Q_v R_v\|^2$;
5. Well-spaced reduction (`exists_wellSpaced_of_integral`) converting the integral of $\|Q_v R_v\|^2$ over $Uset$ to sums over well-spaced point sets;
6. Splitting of well-spaced sums into small-prime and large-prime regimes via `sum_small_prime_poly_mul_le` and `sum_large_prime_poly_mul_le`;
7. Cardinality bounds for the small-prime component on $Uset$ via `card_wellSpaced_subset_Uset_le`;
8. The bridge theorem `RangeSystem.integral_Uset_le_unsifted_bridge` assembling all bounds.
-/

/-- Inclusion of the exceptional set `Uset` into the symmetric interval `[-T, T]`. -/
lemma Uset_subset_Icc_neg {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T) :
    S.Uset hJ β X T₀ T ⊆ Set.Icc (-T) T := by
  intro t ht
  have ht_Icc := ht.1
  have hT_nonneg : 0 ≤ T := hT0.trans hT
  refine ⟨by linarith [ht_Icc.1, hT0, hT], ht_Icc.2⟩

/-- Uniform mean value theorem bound for `Fu` on `Uset` via Montgomery's theorem. -/
lemma integral_Uset_norm_sq_Fu_le_uniform {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hX : 1 ≤ X) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T) :
    ∫ t in S.Uset hJ β X T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (36 * Real.pi + 2) * (T / (X : ℝ) + 1) := by
  have hT_nonneg : 0 ≤ T := hT0.trans hT
  have h_sub := Uset_subset_Icc_neg S hJ β X T₀ T hT0 hT
  have h_meas := S.measurableSet_Uset hJ β X T₀ T
  have h_pos_n : ∀ n ∈ Finset.Ioc X (2 * X), 0 < n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    omega
  have h_set_le := setIntegral_norm_sq_dirichletPoly_le (fX β X) (Finset.Ioc X (2 * X))
    h_pos_n T hT_nonneg (S.Uset hJ β X T₀ T) h_meas h_sub
  have h_coeff_le : ∀ n, ‖fX β X n‖ ≤ 1 := norm_fX_le_one β X
  have h_F_le := integral_norm_sq_F_le_mul (fX β X) h_coeff_le X hX T hT_nonneg
  unfold Fu
  exact h_set_le.trans h_F_le

/-- Multiplicativity of `fX β X (p * m) = fX β X m * fX β X p` when `p ∈ primeRange P Q`
and `Q ≤ X^β` and `¬ p ∣ m`. -/
lemma factor_fX_coeff_primeRange (β : ℝ) (X : ℕ) (P Q : ℕ) (hQX : (Q : ℝ) ≤ (X : ℝ) ^ β)
    {p m : ℕ} (hp : p ∈ primeRange P Q) (hpm : ¬ p ∣ m) :
    fX β X (p * m) = fX β X m * fX β X p := by
  have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp_le_Q : p ≤ Q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  have hp_le_X : (p : ℝ) ≤ (X : ℝ) ^ β := by
    have : (p : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hp_le_Q
    linarith
  have hm_pos : 0 < m := by
    by_contra hm
    have : m = 0 := by omega
    subst this
    exact hpm (dvd_zero p)
  have hfX_pm : fX β X (p * m) = fX β X m := fX_mul_of_prime_le β X p m hp_prime hm_pos hp_le_X
  have hfX_p : fX β X p = 1 := fX_prime_eq_one β X p hp_prime hp_le_X
  rw [hfX_pm, hfX_p, mul_one]

/-- Equivalence between filtering by `primeRange P Q` and filtering by primes in `[P, Q]`. -/
lemma filter_primeRange_eq_primes (X P Q : ℕ) :
    (Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n) =
    (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n) := by
  apply Finset.filter_congr
  intro n _
  constructor
  · intro h p hp hP hpQ
    have hp_mem : p ∈ primeRange P Q := by
      unfold primeRange
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hP, hpQ⟩, hp⟩
    exact h p hp_mem
  · intro h p hp
    unfold primeRange at hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    exact h p hp.2 hp.1.1 hp.1.2

/-- Halberstam–Richert upper sieve bound on the unsifted fraction for primes in `[P, Q]`. -/
lemma card_unsifted_div_X_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X P Q : ℕ), 2 ≤ P → P ≤ Q → 2 ≤ X → Q ≤ X →
      (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / (X : ℝ) ≤
        C * Real.log P / Real.log Q := by
  obtain ⟨C, hC_pos, h_hr⟩ := card_no_prime_factor_in_Icc_le_hr'
  use C
  refine ⟨hC_pos, ?_⟩
  intro X P Q hP hPQ hX hQX
  have h_eq : (Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n) =
      (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n) :=
    filter_primeRange_eq_primes X P Q
  rw [h_eq]
  have h_card := h_hr X P Q hP hPQ hX hQX
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have h_div := div_le_div_of_nonneg_right h_card hX_pos.le
  refine h_div.trans ?_
  have : C * (X : ℝ) * Real.log (P : ℝ) / Real.log (Q : ℝ) / (X : ℝ) =
      C * Real.log (P : ℝ) / Real.log (Q : ℝ) := by
    calc C * (X : ℝ) * Real.log (P : ℝ) / Real.log (Q : ℝ) / (X : ℝ)
      _ = (C * Real.log (P : ℝ) / Real.log (Q : ℝ)) * (X : ℝ) / (X : ℝ) := by ring
      _ = (C * Real.log (P : ℝ) / Real.log (Q : ℝ)) * ((X : ℝ) / (X : ℝ)) := by ring
      _ = (C * Real.log (P : ℝ) / Real.log (Q : ℝ)) * 1 := by rw [div_self (ne_of_gt hX_pos)]
      _ = C * Real.log (P : ℝ) / Real.log (Q : ℝ) := by ring
  rw [this]

/-- Application of Matomäki–Radziwiłł Lemma 12 to the exceptional set `Uset`. -/
theorem integral_Uset_norm_sq_Fu_le_sum_QR :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
      (β : ℝ) (X : ℕ) (T₀ T : ℝ) (P Q : ℕ) (H : ℝ),
      1 ≤ X → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ X → (P : ℝ) ^ 4 ≤ X → 1 ≤ H → 0 ≤ T₀ → T₀ ≤ T →
      (Q : ℝ) ≤ (X : ℝ) ^ β →
      let U := S.Uset hJ β X T₀ T
      ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
            ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
                dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
        C * (T / X + 1) * (1 / H + 1 / P + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := by
  obtain ⟨C_L12, hC_L12_pos, hL12⟩ := integral_norm_sq_F_le_sum_QR
  use C_L12
  refine ⟨hC_L12_pos, ?_⟩
  intro J η S hJ β X T₀ T P Q H hX hP hPQ hQX hP4 hH hT0 hT hQX_beta U
  have hT_nonneg : 0 ≤ T := hT0.trans hT
  have hU_meas : MeasurableSet U := S.measurableSet_Uset hJ β X T₀ T
  have hU_sub : U ⊆ Set.Icc (-T) T := Uset_subset_Icc_neg S hJ β X T₀ T hT0 hT
  have ha : ∀ n, ‖fX β X n‖ ≤ 1 := norm_fX_le_one β X
  have hb : ∀ m, ‖fX β X m‖ ≤ 1 := norm_fX_le_one β X
  have hc : ∀ p, ‖fX β X p‖ ≤ 1 := norm_fX_le_one β X
  have hfactor : ∀ p m, p ∈ primeRange P Q → ¬ p ∣ m → fX β X (p * m) = fX β X m * fX β X p :=
    fun p m hp hpm => factor_fX_coeff_primeRange β X P Q hQX_beta hp hpm
  exact hL12 X P Q H (fX β X) (fX β X) (fX β X) T U hX hP hPQ hQX hP4 hH hT_nonneg hU_meas hU_sub ha hb hc hfactor

/-- Application of Matomäki–Radziwiłł Lemma 12 to `Uset` combined with the Halberstam–Richert sieve bound. -/
lemma integral_Uset_norm_sq_Fu_le_sum_QR_sieve :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
      (β : ℝ) (X : ℕ) (T₀ T : ℝ) (P Q : ℕ) (H : ℝ),
      2 ≤ X → 2 ≤ P → P ≤ Q → Q ≤ X → (P : ℝ) ^ 4 ≤ X → 1 ≤ H → 0 ≤ T₀ → T₀ ≤ T →
      (Q : ℝ) ≤ (X : ℝ) ^ β →
      let U := S.Uset hJ β X T₀ T
      ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
            ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
                dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
        C * (T / X + 1) * (1 / H + 1 / P + Real.log P / Real.log Q) := by
  obtain ⟨C_L12, hC_L12_pos, hL12⟩ := integral_Uset_norm_sq_Fu_le_sum_QR
  obtain ⟨C_HR, hC_HR_pos, hHR⟩ := card_unsifted_div_X_le
  let C := C_L12 * max 1 C_HR
  have hC_pos : 0 < C := mul_pos hC_L12_pos (lt_of_lt_of_le zero_lt_one (le_max_left 1 C_HR))
  refine ⟨C, hC_pos, ?_⟩
  intro J η S hJ β X T₀ T P Q H hX hP hPQ hQX hP4 hH hT0 hT hQX_beta U
  have hX1 : 1 ≤ X := by omega
  have hQX_r : (Q : ℝ) ≤ X := by exact_mod_cast hQX
  have h_l12 := hL12 S hJ β X T₀ T P Q H hX1 hP hPQ hQX_r hP4 hH hT0 hT hQX_beta
  have h_hr := hHR X P Q hP hPQ hX hQX
  have h_sum_le : 1 / H + 1 / (P : ℝ) + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / (X : ℝ) ≤
      (max 1 C_HR) * (1 / H + 1 / (P : ℝ) + Real.log (P : ℝ) / Real.log (Q : ℝ)) := by
    have h1 : 1 / H + 1 / (P : ℝ) ≤ (max 1 C_HR) * (1 / H + 1 / (P : ℝ)) := by
      have : 1 ≤ max 1 C_HR := le_max_left 1 C_HR
      have h_nonneg : 0 ≤ 1 / H + 1 / (P : ℝ) := by positivity
      calc 1 / H + 1 / (P : ℝ) = 1 * (1 / H + 1 / (P : ℝ)) := by ring
        _ ≤ (max 1 C_HR) * (1 / H + 1 / (P : ℝ)) := mul_le_mul_of_nonneg_right this h_nonneg
    have h2 : (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / (X : ℝ) ≤
        (max 1 C_HR) * (Real.log (P : ℝ) / Real.log (Q : ℝ)) := by
      have : C_HR ≤ max 1 C_HR := le_max_right 1 C_HR
      have hlog_nonneg : 0 ≤ Real.log (P : ℝ) / Real.log (Q : ℝ) := by
        have : 1 < (P : ℝ) := by exact_mod_cast (show 1 < P by omega)
        have : 1 < (Q : ℝ) := by exact_mod_cast (show 1 < Q by omega)
        positivity
      refine h_hr.trans ?_
      calc C_HR * Real.log (P : ℝ) / Real.log (Q : ℝ) = C_HR * (Real.log (P : ℝ) / Real.log (Q : ℝ)) := by ring
        _ ≤ (max 1 C_HR) * (Real.log (P : ℝ) / Real.log (Q : ℝ)) := mul_le_mul_of_nonneg_right this hlog_nonneg
    calc 1 / H + 1 / (P : ℝ) + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / (X : ℝ)
      _ ≤ (max 1 C_HR) * (1 / H + 1 / (P : ℝ)) + (max 1 C_HR) * (Real.log (P : ℝ) / Real.log (Q : ℝ)) := by linarith
      _ = (max 1 C_HR) * (1 / H + 1 / (P : ℝ) + Real.log (P : ℝ) / Real.log (Q : ℝ)) := by ring
  have hC_ge_L12 : C_L12 ≤ C := by
    have : 1 ≤ max 1 C_HR := le_max_left 1 C_HR
    calc C_L12 = C_L12 * 1 := by ring
      _ ≤ C_L12 * max 1 C_HR := mul_le_mul_of_nonneg_left this hC_L12_pos.le
  have hTX_nonneg : 0 ≤ T / (X : ℝ) + 1 := by
    have : 0 ≤ T / (X : ℝ) := div_nonneg (hT0.trans hT) (by positivity)
    linarith
  have h_term2_le : C_L12 * (T / X + 1) * (1 / H + 1 / P + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) ≤
      C * (T / X + 1) * (1 / H + 1 / P + Real.log P / Real.log Q) := by
    calc C_L12 * (T / X + 1) * (1 / H + 1 / P + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X)
      _ = (C_L12 * (T / X + 1)) * (1 / H + 1 / P + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := by ring
      _ ≤ (C_L12 * (T / X + 1)) * ((max 1 C_HR) * (1 / H + 1 / P + Real.log P / Real.log Q)) :=
        mul_le_mul_of_nonneg_left h_sum_le (by positivity)
      _ = (C_L12 * max 1 C_HR) * (T / X + 1) * (1 / H + 1 / P + Real.log P / Real.log Q) := by ring
      _ = C * (T / X + 1) * (1 / H + 1 / P + Real.log P / Real.log Q) := rfl
  have h_term1_le : C_L12 * (H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
        ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      C * (H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
        ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) := by
    have h_prod_nonneg : 0 ≤ (H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
        ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) := by
      have hH_pos : 0 ≤ H := by linarith
      have hlogQ : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q by omega))
      have hsum_nonneg : 0 ≤ ∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
          ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
              dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
        apply Finset.sum_nonneg
        intro v _
        exact setIntegral_nonneg (S.measurableSet_Uset hJ β X T₀ T) (fun t _ => sq_nonneg _)
      positivity
    calc C_L12 * (H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
          ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
              dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2)
      _ = C_L12 * ((H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
          ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
              dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2)) := by ring
      _ ≤ C * ((H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
          ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
              dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right hC_ge_L12 h_prod_nonneg
      _ = C * (H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
          ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
              dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) := by ring
  linarith [h_l12, h_term1_le, h_term2_le]

/-- Strictly positive support for `shortPrimeRange`. -/
lemma pos_of_mem_shortPrimeRange {P Q : ℕ} {H : ℝ} {v p : ℕ} (hp : p ∈ shortPrimeRange P Q H v) :
    0 < p := by
  rw [mem_shortPrimeRange] at hp
  exact hp.1.1.pos

/-- Strictly positive support for `cofactorRange`. -/
lemma pos_of_mem_cofactorRange {X : ℕ} {H : ℝ} {v m : ℕ} (hm : m ∈ cofactorRange X H v) :
    0 < m := by
  unfold cofactorRange at hm
  rw [Finset.mem_filter, Finset.mem_Ioc] at hm
  exact hm.1.1

/-- Continuity of the short prime Dirichlet polynomial. -/
lemma continuous_shortPrime_poly (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) :
    Continuous (fun t : ℝ => dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)) :=
  continuous_dirichletPoly_one_line (fX β X) (shortPrimeRange P Q H v) (fun _ => pos_of_mem_shortPrimeRange)

/-- Continuity of the cofactor Dirichlet polynomial. -/
lemma continuous_cofactor_poly (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) :
    Continuous (fun t : ℝ => dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1))
      (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)) :=
  continuous_dirichletPoly_one_line _ (cofactorRange X H v) (fun _ => pos_of_mem_cofactorRange)

/-- Continuity of the product polynomial `Q_v * R_v`. -/
lemma continuous_QR_v (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) :
    Continuous (fun t : ℝ => dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
      dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)) :=
  (continuous_shortPrime_poly β X P Q H v).mul (continuous_cofactor_poly β X P Q H v)

/-- Measurability of `‖Q_v * R_v‖²`. -/
lemma measurable_norm_sq_QR_v (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) :
    Measurable (fun t : ℝ => ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
      dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) :=
  ((continuous_QR_v β X P Q H v).norm.pow 2).measurable

/-- Pointwise boundedness of `‖Q_v * R_v‖²` on ℝ. -/
lemma bounded_norm_sq_QR_v (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) :
    ∃ B : ℝ, ∀ t : ℝ, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
      dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤ B := by
  let BQ := ∑ p ∈ shortPrimeRange P Q H v, ‖fX β X p‖ / (p : ℝ)
  let BR := ∑ m ∈ cofactorRange X H v, ‖fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ / (m : ℝ)
  use (BQ * BR) ^ 2
  intro t
  rw [norm_mul, mul_pow]
  have hQ := norm_dirichletPoly_le (fX β X) (shortPrimeRange P Q H v) (fun _ => pos_of_mem_shortPrimeRange) t
  have hR := norm_dirichletPoly_le (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) (fun _ => pos_of_mem_cofactorRange) t
  have hQ_sq : ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤ BQ ^ 2 := by
    have : 0 ≤ ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ := norm_nonneg _
    nlinarith
  have hR_sq : ‖dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤ BR ^ 2 := by
    have : 0 ≤ ‖dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ := norm_nonneg _
    nlinarith
  calc ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
        ‖dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2
    _ ≤ BQ ^ 2 * BR ^ 2 := mul_le_mul hQ_sq hR_sq (sq_nonneg _) (sq_nonneg _)
    _ = (BQ * BR) ^ 2 := by ring

/-- Subsets of well-spaced finsets are well-spaced. -/
lemma wellSpaced_subset {S S' : Finset ℝ} (hS : WellSpaced S) (hsub : S' ⊆ S) :
    WellSpaced S' :=
  fun s hs t ht hne => hS s (hsub hs) t (hsub ht) hne

/-- Splitting a sum over a finset by a decidable predicate. -/
lemma sum_split_filter (𝒯 : Finset ℝ) (p : ℝ → Prop) [DecidablePred p] (f : ℝ → ℝ) :
    (∑ t ∈ 𝒯, f t) = (∑ t ∈ 𝒯.filter p, f t) + (∑ t ∈ 𝒯.filter (fun t => ¬ p t), f t) := by
  rw [Finset.sum_filter_add_sum_filter_not]

/-- Well-spaced reduction for the integral of `‖Q_v * R_v‖²` over `Uset`. -/
lemma exists_wellSpaced_integral_QR_v_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (T₀ T : ℝ) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T)
    (ε : ℝ) (hε : 0 < ε) :
    let U := S.Uset hJ β X T₀ T
    let F_v := fun t : ℝ => ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
      dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2
    ∃ S₁ S₂ : Finset ℝ, WellSpaced S₁ ∧ WellSpaced S₂ ∧ (↑S₁ ⊆ U) ∧ (↑S₂ ⊆ U) ∧
      ∫ t in U, F_v t ≤ (∑ t ∈ S₁, F_v t) + (∑ t ∈ S₂, F_v t) + ε := by
  intro U F_v
  have hT_nonneg : 0 ≤ T := hT0.trans hT
  have hU_meas : MeasurableSet U := S.measurableSet_Uset hJ β X T₀ T
  have hU_sub : U ⊆ Set.Icc (-T) T := Uset_subset_Icc_neg S hJ β X T₀ T hT0 hT
  have hF_nonneg : ∀ t, 0 ≤ F_v t := fun t => sq_nonneg _
  have hF_meas : Measurable F_v := measurable_norm_sq_QR_v β X P Q H v
  have hF_bdd : ∃ B, ∀ t, F_v t ≤ B := bounded_norm_sq_QR_v β X P Q H v
  obtain ⟨S₁, S₂, hS₁, hS₂, hS₁U, hS₂U, _, _, h_int⟩ :=
    exists_wellSpaced_of_integral F_v U T hT_nonneg hU_meas hU_sub hF_nonneg hF_meas hF_bdd ε hε
  exact ⟨S₁, S₂, hS₁, hS₂, hS₁U, hS₂U, h_int⟩

/-- Simultaneous small/large prime bounds on the filtered components of a well-spaced set. -/
theorem sum_QR_v_wellSpaced_le (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ C_S C_L c : ℝ, 0 < C_S ∧ 0 < C_L ∧ 0 < c ∧
      ∀ (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (T τ Z ε : ℝ) (𝒯 : Finset ℝ),
        3 / 4 ≤ β → β < 1 → 16 ≤ X → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ (X : ℝ) ^ β → 2 ≤ H → H ≤ Real.sqrt P →
        v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊ →
        3 ≤ T → T ≤ X → 1 ≤ τ → 0 ≤ ε → WellSpaced 𝒯 → (∀ t ∈ 𝒯, τ ≤ |t| ∧ |t| ≤ T) →
        (Q : ℝ) < Z → 4 ≤ Z → Z ≤ Real.sqrt X → Real.log X ≤ (Real.log (Z - 1)) ^ (5 / 4 : ℝ) →
        let 𝒯_S : Finset ℝ := 𝒯.filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)
        let 𝒯_L : Finset ℝ := 𝒯.filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))
        (∑ t ∈ 𝒯_S, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
          C_S * ε ^ 2 * Real.log T * (1 + 𝒯_S.card * Real.sqrt T * Real.exp (v / H) / X) ∧
        (∑ t ∈ 𝒯_L, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
          C_L * ((Real.log X + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
                + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
            (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
            ((H / (v : ℝ)) * (1 + 𝒯_L.card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2)) := by
  obtain ⟨C_S, hC_S_pos, h_small⟩ := sum_small_prime_poly_mul_le
  obtain ⟨c, C_L, hc_pos, hC_L_pos, h_large⟩ := sum_large_prime_poly_mul_le c₀ K hc₀ hK hζ hholo
  refine ⟨C_S, C_L, c, hC_S_pos, hC_L_pos, hc_pos, ?_⟩
  intro β X P Q H v T τ Z ε 𝒯 hβ hβ1 hX hP hPQ hQX hH hHP hv hT hTX hτ hε h𝒯 ht_bounds hQZ hZ hZX hlogX 𝒯_S 𝒯_L
  have hX1 : 1 ≤ X := by omega
  have hH1 : 1 ≤ H := by linarith
  have hT2 : 2 ≤ T := by linarith
  have h𝒯_S_sub : 𝒯_S ⊆ 𝒯 := Finset.filter_subset _ _
  have h𝒯_L_sub : 𝒯_L ⊆ 𝒯 := Finset.filter_subset _ _
  have h𝒯_S_well : WellSpaced 𝒯_S := wellSpaced_subset h𝒯 h𝒯_S_sub
  have h𝒯_L_well : WellSpaced 𝒯_L := wellSpaced_subset h𝒯 h𝒯_L_sub
  have ht_S_le : ∀ t ∈ 𝒯_S, |t| ≤ T := fun t ht => (ht_bounds t (h𝒯_S_sub ht)).2
  have ht_L_bounds : ∀ t ∈ 𝒯_L, τ ≤ |t| ∧ |t| ≤ T := fun t ht => ht_bounds t (h𝒯_L_sub ht)
  have hb : ∀ m, ‖fX β X m‖ ≤ 1 := norm_fX_le_one β X
  have hc : ∀ p, ‖fX β X p‖ ≤ 1 := norm_fX_le_one β X
  have hQ_S : ∀ t ∈ 𝒯_S, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ≤ ε := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  constructor
  · exact h_small X P Q H v (fX β X) (fX β X) T ε 𝒯_S hX1 hH1 hT2 hε h𝒯_S_well ht_S_le hb hc hQ_S
  · exact h_large β X P Q H v T τ Z 𝒯_L hβ hβ1 hX hP hPQ hQX hH hHP hv hT hTX hτ h𝒯_L_well ht_L_bounds hQZ hZ hZX hlogX

/-- Combined upper bound on the well-spaced sum of `‖Q_v * R_v‖²`. -/
theorem sum_QR_v_wellSpaced_total_le (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ C_S C_L c : ℝ, 0 < C_S ∧ 0 < C_L ∧ 0 < c ∧
      ∀ (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (T τ Z ε : ℝ) (𝒯 : Finset ℝ),
        3 / 4 ≤ β → β < 1 → 16 ≤ X → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ (X : ℝ) ^ β → 2 ≤ H → H ≤ Real.sqrt P →
        v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊ →
        3 ≤ T → T ≤ X → 1 ≤ τ → 0 ≤ ε → WellSpaced 𝒯 → (∀ t ∈ 𝒯, τ ≤ |t| ∧ |t| ≤ T) →
        (Q : ℝ) < Z → 4 ≤ Z → Z ≤ Real.sqrt X → Real.log X ≤ (Real.log (Z - 1)) ^ (5 / 4 : ℝ) →
        let 𝒯_S : Finset ℝ := 𝒯.filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)
        let 𝒯_L : Finset ℝ := 𝒯.filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))
        (∑ t ∈ 𝒯, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
          C_S * ε ^ 2 * Real.log T * (1 + 𝒯_S.card * Real.sqrt T * Real.exp (v / H) / X) +
          C_L * ((Real.log X + 2) * (1 / (τ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
                + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
            (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
            ((H / (v : ℝ)) * (1 + 𝒯_L.card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2)) := by
  obtain ⟨C_S, C_L, c, hC_S_pos, hC_L_pos, hc_pos, h_QR⟩ := sum_QR_v_wellSpaced_le c₀ K hc₀ hK hζ hholo
  refine ⟨C_S, C_L, c, hC_S_pos, hC_L_pos, hc_pos, ?_⟩
  intro β X P Q H v T τ Z ε 𝒯 hβ hβ1 hX hP hPQ hQX hH hHP hv hT hTX hτ hε h𝒯 ht_bounds hQZ hZ hZX hlogX 𝒯_S 𝒯_L
  have h_both := h_QR β X P Q H v T τ Z ε 𝒯 hβ hβ1 hX hP hPQ hQX hH hHP hv hT hTX hτ hε h𝒯 ht_bounds hQZ hZ hZX hlogX
  have h_split := sum_split_filter 𝒯 (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)
    (fun t => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) *
        dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2)
  rw [h_split]
  linarith [h_both.1, h_both.2]

/-- The exceptional set card bound on the small prime component `𝒯_S`. -/
lemma card_wellSpaced_subset_Uset_small_le {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) (𝒯 : Finset ℝ)
      (P Q : ℕ) (H : ℝ) (v : ℕ) (ε : ℝ),
      16 ≤ X → 1 ≤ T₀ → T₀ ≤ T → T ≤ X → WellSpaced 𝒯 → (↑𝒯 ⊆ S.Uset hJ β X T₀ T) →
      (∀ j, 2 ≤ S.Hj hJ j) → (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) →
      (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) →
      let 𝒯_S : Finset ℝ := 𝒯.filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)
      (𝒯_S.card : ℝ) ≤ C * (S.Hj hJ ⟨J - 1, by omega⟩ * Real.log (S.Q ⟨J - 1, by omega⟩) + 2) *
        T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X := by
  obtain ⟨C_c, hC_c_pos, h_card⟩ := RangeSystem.card_wellSpaced_subset_Uset_le hη0 hη
  refine ⟨C_c, hC_c_pos, ?_⟩
  intro J S hJ β X T₀ T 𝒯 P Q H v ε hX hT0 hT hTX h𝒯 h𝒯_sub hH hQ hP 𝒯_S
  have h𝒯_S_sub : 𝒯_S ⊆ 𝒯 := Finset.filter_subset _ _
  have h𝒯_S_well : WellSpaced 𝒯_S := wellSpaced_subset h𝒯 h𝒯_S_sub
  have h𝒯_S_in_U : ↑𝒯_S ⊆ S.Uset hJ β X T₀ T := by
    intro t ht
    have : t ∈ 𝒯 := h𝒯_S_sub (Finset.mem_coe.mp ht)
    exact h𝒯_sub (Finset.mem_coe.mpr this)
  exact h_card J S hJ β X T₀ T 𝒯_S hX hT0 hT hTX h𝒯_S_well h𝒯_S_in_U hH hQ hP

/-- Reduction of the integral of `‖Q_v * R_v‖²` over `Uset` to well-spaced small/large prime sums. -/
theorem integral_QR_v_le_wellSpaced_sum (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ C_S C_L c : ℝ, 0 < C_S ∧ 0 < C_L ∧ 0 < c ∧
      ∀ {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
        (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (T T₀ Z ε ε₀ : ℝ),
        3 / 4 ≤ β → β < 1 → 16 ≤ X → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ (X : ℝ) ^ β → 2 ≤ H → H ≤ Real.sqrt P →
        v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊ →
        3 ≤ T → T ≤ X → 1 ≤ T₀ → T₀ ≤ T → 0 ≤ ε → 0 < ε₀ →
        (Q : ℝ) < Z → 4 ≤ Z → Z ≤ Real.sqrt X → Real.log X ≤ (Real.log (Z - 1)) ^ (5 / 4 : ℝ) →
        let U := S.Uset hJ β X T₀ T
        ∃ S₁ S₂ : Finset ℝ, WellSpaced S₁ ∧ WellSpaced S₂ ∧ (↑S₁ ⊆ U) ∧ (↑S₂ ⊆ U) ∧
          let S₁_S : Finset ℝ := S₁.filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)
          let S₁_L : Finset ℝ := S₁.filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))
          let S₂_S : Finset ℝ := S₂.filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)
          let S₂_L : Finset ℝ := S₂.filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))
          ∫ t in U, ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I) *
              dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
            (C_S * ε ^ 2 * Real.log T * (1 + S₁_S.card * Real.sqrt T * Real.exp (v / H) / X) +
             C_L * ((Real.log X + 2) * (1 / (T₀ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
                   + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
               (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
               ((H / (v : ℝ)) * (1 + S₁_L.card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2))) +
            (C_S * ε ^ 2 * Real.log T * (1 + S₂_S.card * Real.sqrt T * Real.exp (v / H) / X) +
             C_L * ((Real.log X + 2) * (1 / (T₀ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
                   + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
               (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
               ((H / (v : ℝ)) * (1 + S₂_L.card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2))) + ε₀ := by
  obtain ⟨C_S, C_L, c, hC_S_pos, hC_L_pos, hc_pos, h_tot⟩ := sum_QR_v_wellSpaced_total_le c₀ K hc₀ hK hζ hholo
  refine ⟨C_S, C_L, c, hC_S_pos, hC_L_pos, hc_pos, ?_⟩
  intro J η S hJ β X P Q H v T T₀ Z ε ε₀ hβ hβ1 hX hP hPQ hQX hH hHP hv hT hTX hT0 hT0T hε hε0 hQZ hZ hZX hlogX U
  have hT0_nonneg : 0 ≤ T₀ := by linarith
  obtain ⟨S₁, S₂, hS₁, hS₂, hS₁U, hS₂U, h_int⟩ :=
    exists_wellSpaced_integral_QR_v_le S hJ β X P Q H v T₀ T hT0_nonneg hT0T ε₀ hε0
  refine ⟨S₁, S₂, hS₁, hS₂, hS₁U, hS₂U, ?_⟩
  intro S₁_S S₁_L S₂_S S₂_L
  have ht_bounds (𝒯 : Finset ℝ) (h𝒯U : ↑𝒯 ⊆ U) : ∀ t ∈ 𝒯, T₀ ≤ |t| ∧ |t| ≤ T := by
    intro t ht
    have ht_in : t ∈ U := h𝒯U (Finset.mem_coe.mpr ht)
    have ht_Icc := ht_in.1
    have : 0 ≤ t := by linarith [hT0, ht_Icc.1]
    rw [abs_of_nonneg this]
    exact ⟨ht_Icc.1, ht_Icc.2⟩
  have h_bound1 := h_tot β X P Q H v T T₀ Z ε S₁ hβ hβ1 hX hP hPQ hQX hH hHP hv hT hTX hT0 hε hS₁ (ht_bounds S₁ hS₁U) hQZ hZ hZX hlogX
  have h_bound2 := h_tot β X P Q H v T T₀ Z ε S₂ hβ hβ1 hX hP hPQ hQX hH hHP hv hT hTX hT0 hε hS₂ (ht_bounds S₂ hS₂U) hQZ hZ hZX hlogX
  dsimp only [Qpoly, S₁_S, S₁_L, S₂_S, S₂_L] at *
  linarith [h_int, h_bound1, h_bound2]

/-- Bridge theorem: assembly of Matomäki–Radziwiłł Lemma 12 on the exceptional set `Uset`
combined with the Halberstam–Richert sieve bound. -/
theorem RangeSystem.integral_Uset_le_unsifted_bridge :
    ∃ C : ℝ, 0 < C ∧ ∀ {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
      (β : ℝ) (X : ℕ) (T₀ T : ℝ) (P Q : ℕ) (H : ℝ),
      2 ≤ X → 2 ≤ P → P ≤ Q → Q ≤ X → (P : ℝ) ^ 4 ≤ X → 1 ≤ H → 0 ≤ T₀ → T₀ ≤ T →
      (Q : ℝ) ≤ (X : ℝ) ^ β →
      let U := S.Uset hJ β X T₀ T
      ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
            ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
                dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
        C * (T / X + 1) * (1 / H + 1 / P + Real.log P / Real.log Q) :=
  integral_Uset_norm_sq_Fu_le_sum_QR_sieve

/-- The exceptional set card bound on the large prime component `𝒯_L` via level J-1. -/
lemma card_wellSpaced_subset_Uset_large_le {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) (𝒯 : Finset ℝ)
      (P Q : ℕ) (H : ℝ) (v : ℕ) (ε : ℝ),
      16 ≤ X → 1 ≤ T₀ → T₀ ≤ T → T ≤ X → WellSpaced 𝒯 → (↑𝒯 ⊆ S.Uset hJ β X T₀ T) →
      (∀ j, 2 ≤ S.Hj hJ j) → (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) →
      (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) →
      let 𝒯_L : Finset ℝ := 𝒯.filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))
      (𝒯_L.card : ℝ) ≤ C * (S.Hj hJ ⟨J - 1, by omega⟩ * Real.log (S.Q ⟨J - 1, by omega⟩) + 2) *
        T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log X)) * Real.log X := by
  obtain ⟨C_c, hC_c_pos, h_card⟩ := RangeSystem.card_wellSpaced_subset_Uset_le hη0 hη
  refine ⟨C_c, hC_c_pos, ?_⟩
  intro J S hJ β X T₀ T 𝒯 P Q H v ε hX hT0 hT hTX h𝒯 h𝒯_sub hH hQ hP 𝒯_L
  have h𝒯_L_sub : 𝒯_L ⊆ 𝒯 := Finset.filter_subset _ _
  have h𝒯_L_well : WellSpaced 𝒯_L := wellSpaced_subset h𝒯 h𝒯_L_sub
  have h𝒯_L_in_U : ↑𝒯_L ⊆ S.Uset hJ β X T₀ T := by
    intro t ht
    have : t ∈ 𝒯 := h𝒯_L_sub (Finset.mem_coe.mp ht)
    exact h𝒯_sub (Finset.mem_coe.mpr this)
  exact h_card J S hJ β X T₀ T 𝒯_L hX hT0 hT hTX h𝒯_L_well h𝒯_L_in_U hH hQ hP

/-- Lemma 8 bound on the large-prime well-spaced set `𝒯_L` for any dyadic scale `P₀`. -/
lemma card_TL_le_raw (C₈ : ℝ)
    (hlem8 : ∀ (P : ℕ) (a : ℕ → ℂ) (T V : ℝ) (S : Finset ℝ),
      2 ≤ P → 1 ≤ T → 1 ≤ V → (∀ p, ‖a p‖ ≤ 1) → WellSpaced S → (∀ t ∈ S, |t| ≤ T) →
      (∀ t ∈ S, V⁻¹ ≤ ‖dirichletPoly a ((Finset.Ioc P (2 * P)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I)‖) →
      (S.card : ℝ) ≤ C₈ * T ^ (2 * Real.log V / Real.log P) * V ^ 2 *
        Real.exp (2 * (Real.log T / Real.log P) * Real.log (Real.log T + 2)) * 5 ^ ⌈Real.log T / Real.log P⌉₊ * (⌈Real.log T / Real.log P⌉₊).factorial)
    (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (T ε : ℝ) (𝒯 : Finset ℝ)
    (hH : 2 ≤ H) (hT : 1 ≤ T) (hε_pos : 0 < ε) (hε_le1 : ε ≤ 1) (hws : WellSpaced 𝒯) (ht_le : ∀ t ∈ 𝒯, |t| ≤ T)
    (P₀ : ℕ) (hP₀_5 : 5 ≤ P₀) (hP₀_lt : (P₀ : ℝ) < Real.exp ((v : ℝ) / H)) (hP₀_ge : Real.exp ((v : ℝ) / H) ≤ (P₀ : ℝ) + 1) :
    let 𝒯_L : Finset ℝ := 𝒯.filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))
    (𝒯_L.card : ℝ) ≤ C₈ * T ^ (2 * Real.log (1 / ε) / Real.log P₀) * (1 / ε) ^ 2 *
      Real.exp (2 * (Real.log T / Real.log P₀) * Real.log (Real.log T + 2)) * 5 ^ ⌈Real.log T / Real.log P₀⌉₊ * (⌈Real.log T / Real.log P₀⌉₊).factorial := by
  intro 𝒯_L
  let V := 1 / ε
  have hV1 : 1 ≤ V := by
    dsimp [V]
    rw [one_div]
    exact (one_le_inv₀ hε_pos).mpr hε_le1
  have hP₀_2 : 2 ≤ P₀ := by omega
  have hws_L : WellSpaced 𝒯_L := WellSpaced.filter hws _
  have ht_L_le : ∀ t ∈ 𝒯_L, |t| ≤ T := fun t ht => ht_le t (Finset.mem_filter.mp ht).1
  let a_coeff : ℕ → ℂ := fun p => if p ∈ shortPrimeRange P Q H v then fX β X p else 0
  have ha_le : ∀ p, ‖a_coeff p‖ ≤ 1 := by
    intro p
    dsimp [a_coeff]
    split_ifs
    · exact norm_fX_le_one β X p
    · simp
  have hsub : shortPrimeRange P Q H v ⊆ (Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime :=
    shortPrimeRange_subset_Ioc_prime P Q H v hH P₀ hP₀_lt hP₀_ge hP₀_5
  have hV_le : ∀ t ∈ 𝒯_L, V⁻¹ ≤ ‖dirichletPoly a_coeff ((Finset.Ioc P₀ (2 * P₀)).filter Nat.Prime) ((1 : ℂ) + t * Complex.I)‖ := by
    intro t ht
    rw [Finset.mem_filter] at ht
    have ht_not := ht.2
    have ht_gt : ε < ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ := lt_of_not_ge ht_not
    have h_poly := dirichletPoly_eq_Qpoly β X P Q H v P₀ hsub ((1 : ℂ) + t * Complex.I)
    rw [h_poly]
    dsimp [V]
    rw [one_div, inv_inv]
    exact ht_gt.le
  exact hlem8 P₀ a_coeff T V 𝒯_L hP₀_2 hT hV1 ha_le hws_L ht_L_le hV_le

/-- Packaged Lemma 8 bound on the large-prime well-spaced set `𝒯_L` with existential constant `C > 0`. -/
lemma card_TL_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (X P Q : ℕ) (H : ℝ) (v : ℕ) (T ε : ℝ) (𝒯 : Finset ℝ),
      2 ≤ H → 1 ≤ T → 0 < ε → ε ≤ 1 → WellSpaced 𝒯 → (∀ t ∈ 𝒯, |t| ≤ T) →
      ∀ (P₀ : ℕ), 5 ≤ P₀ → (P₀ : ℝ) < Real.exp ((v : ℝ) / H) → Real.exp ((v : ℝ) / H) ≤ (P₀ : ℝ) + 1 →
      let 𝒯_L : Finset ℝ := 𝒯.filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))
      (𝒯_L.card : ℝ) ≤ C * T ^ (2 * Real.log (1 / ε) / Real.log P₀) * (1 / ε) ^ 2 *
        Real.exp (2 * (Real.log T / Real.log P₀) * Real.log (Real.log T + 2)) * 5 ^ ⌈Real.log T / Real.log P₀⌉₊ * (⌈Real.log T / Real.log P₀⌉₊).factorial := by
  obtain ⟨C₈, hC₈_pos, hlem8⟩ := card_wellSpaced_large_prime_poly_le
  refine ⟨C₈, hC₈_pos, ?_⟩
  intro β X P Q H v T ε 𝒯 hH hT hε_pos hε_le1 hws ht_le P₀ hP₀_5 hP₀_lt hP₀_ge
  exact card_TL_le_raw C₈ hlem8 β X P Q H v T ε 𝒯 hH hT hε_pos hε_le1 hws ht_le P₀ hP₀_5 hP₀_lt hP₀_ge

/-- Master bridge theorem: assembly of Lemma 12 on `Uset` with the sieve bound and the
small/large well-spaced point decomposition across all frequencies `v`. -/
theorem integral_Uset_norm_sq_Fu_le_wellSpaced_bridge (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1})) :
    ∃ C_B C_S C_L c : ℝ, 0 < C_B ∧ 0 < C_S ∧ 0 < C_L ∧ 0 < c ∧
      ∀ {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
        (β : ℝ) (X P Q : ℕ) (H : ℝ) (T T₀ Z ε ε₀ : ℝ),
        3 / 4 ≤ β → β < 1 → 16 ≤ X → 2 ≤ P → P ≤ Q → Q ≤ X → (P : ℝ) ^ 4 ≤ X → (Q : ℝ) ≤ (X : ℝ) ^ β →
        2 ≤ H → H ≤ Real.sqrt P →
        3 ≤ T → T ≤ X → 1 ≤ T₀ → T₀ ≤ T → 0 ≤ ε → 0 < ε₀ →
        (Q : ℝ) < Z → 4 ≤ Z → Z ≤ Real.sqrt X → Real.log X ≤ (Real.log (Z - 1)) ^ (5 / 4 : ℝ) →
        let U := S.Uset hJ β X T₀ T
        ∃ (f_S₁ f_S₂ : ℕ → Finset ℝ),
          (∀ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
            WellSpaced (f_S₁ v) ∧ WellSpaced (f_S₂ v) ∧ (↑(f_S₁ v) ⊆ U) ∧ (↑(f_S₂ v) ⊆ U)) ∧
          ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
            C_B * (H * Real.log Q) * (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
              ((C_S * ε ^ 2 * Real.log T * (1 + ((f_S₁ v).filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)).card * Real.sqrt T * Real.exp (v / H) / X) +
               C_L * ((Real.log X + 2) * (1 / (T₀ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
                     + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
                 (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
                 ((H / (v : ℝ)) * (1 + ((f_S₁ v).filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))).card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2))) +
              (C_S * ε ^ 2 * Real.log T * (1 + ((f_S₂ v).filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)).card * Real.sqrt T * Real.exp (v / H) / X) +
               C_L * ((Real.log X + 2) * (1 / (T₀ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
                     + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
                 (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
                 ((H / (v : ℝ)) * (1 + ((f_S₂ v).filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))).card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2))) + ε₀)) +
            C_B * (T / X + 1) * (1 / H + 1 / P + Real.log P / Real.log Q) := by
  obtain ⟨C_B, hC_B_pos, h_bridge⟩ := RangeSystem.integral_Uset_le_unsifted_bridge
  obtain ⟨C_S, C_L, c, hC_S_pos, hC_L_pos, hc_pos, h_QR⟩ := integral_QR_v_le_wellSpaced_sum c₀ K hc₀ hK hζ hholo
  refine ⟨C_B, C_S, C_L, c, hC_B_pos, hC_S_pos, hC_L_pos, hc_pos, ?_⟩
  intro J η S hJ β X P Q H T T₀ Z ε ε₀ hβ hβ1 hX hP hPQ hQX hP4 hQXβ hH hHP hT hTX hT0 hT0T hε hε0 hQZ hZ hZX hlogX U
  have hT0_nonneg : 0 ≤ T₀ := by linarith
  have hX_ge2 : 2 ≤ X := by omega
  have hH_ge1 : 1 ≤ H := by linarith
  have h_br := h_bridge S hJ β X T₀ T P Q H hX_ge2 hP hPQ hQX hP4 hH_ge1 hT0_nonneg hT0T hQXβ
  set I_v := Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊
  have h_each_all (v : ℕ) :
      ∃ S₁ S₂ : Finset ℝ,
        (v ∈ I_v → WellSpaced S₁ ∧ WellSpaced S₂ ∧ (↑S₁ ⊆ U) ∧ (↑S₂ ⊆ U) ∧
          ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
              dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
            ((C_S * ε ^ 2 * Real.log T * (1 + (S₁.filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)).card * Real.sqrt T * Real.exp (v / H) / X) +
             C_L * ((Real.log X + 2) * (1 / (T₀ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
                   + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
               (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
               ((H / (v : ℝ)) * (1 + (S₁.filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))).card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2))) +
            (C_S * ε ^ 2 * Real.log T * (1 + (S₂.filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)).card * Real.sqrt T * Real.exp (v / H) / X) +
             C_L * ((Real.log X + 2) * (1 / (T₀ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
                   + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
               (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
               ((H / (v : ℝ)) * (1 + (S₂.filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))).card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2))) + ε₀)) := by
    by_cases hv : v ∈ I_v
    · obtain ⟨S₁, S₂, hS₁, hS₂, hS₁U, hS₂U, h_le⟩ := h_QR S hJ β X P Q H v T T₀ Z ε ε₀ hβ hβ1 hX hP hPQ hQXβ hH hHP hv hT hTX hT0 hT0T hε hε0 hQZ hZ hZX hlogX
      refine ⟨S₁, S₂, fun _ => ⟨hS₁, hS₂, hS₁U, hS₂U, h_le⟩⟩
    · refine ⟨∅, ∅, fun h => False.elim (hv h)⟩
  choose f_S₁ f_S₂ h_prop using h_each_all
  refine ⟨f_S₁, f_S₂, ?_, ?_⟩
  · intro v hv
    have h := h_prop v hv
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  · have h_sum_le :
        (∑ v ∈ I_v, ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        ∑ v ∈ I_v,
          ((C_S * ε ^ 2 * Real.log T * (1 + ((f_S₁ v).filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)).card * Real.sqrt T * Real.exp (v / H) / X) +
           C_L * ((Real.log X + 2) * (1 / (T₀ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
                 + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
             (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
             ((H / (v : ℝ)) * (1 + ((f_S₁ v).filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))).card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2))) +
          (C_S * ε ^ 2 * Real.log T * (1 + ((f_S₂ v).filter (fun (t : ℝ) => ‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε)).card * Real.sqrt T * Real.exp (v / H) / X) +
           C_L * ((Real.log X + 2) * (1 / (T₀ * Real.log (Z - 1)) + Real.exp (-c * (Real.log (Z - 1)) ^ (1 / 16 : ℝ))) + 1 / Z
                 + Real.exp (-(Real.log X) / (4 * Real.log Z)) * (Real.log Z) ^ (6 : ℝ)) ^ 2 *
             (1 / (H * Real.log P) + (1 + Real.log P) ^ 3 / Real.sqrt P) *
             ((H / (v : ℝ)) * (1 + ((f_S₂ v).filter (fun (t : ℝ) => ¬ (‖Qpoly β X P Q H v ((1 : ℂ) + t * Complex.I)‖ ≤ ε))).card * Real.exp (-c * Real.log P / (Real.log (P * T)) ^ (3 / 4 : ℝ)) * (Real.log (P * T)) ^ 2))) + ε₀) :=
      Finset.sum_le_sum (fun v hv => (h_prop v hv).2.2.2.2)
    have h_pre_nonneg : 0 ≤ C_B * (H * Real.log Q) := by
      have hH_pos : 0 < H := by linarith
      have hQ_pos : 0 < (Q : ℝ) := by
        have : 2 ≤ Q := hP.trans hPQ
        exact Nat.cast_pos.mpr (by omega)
      have hlogQ_nonneg : 0 ≤ Real.log (Q : ℝ) := by
        have : 1 ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
        exact Real.log_nonneg this
      positivity
    have h_mul_le := mul_le_mul_of_nonneg_left h_sum_le h_pre_nonneg
    linarith [h_br, h_mul_le]

/-- Small-X uniform scaling: for any threshold `X₀ ≥ 16`, Montgomery's theorem yields
an upper bound by `C₀ * (T/X + 1) * (log X)^{-1/400}` on `16 ≤ X ≤ X₀`. -/
lemma integral_Uset_norm_sq_Fu_le_bounded_X (X₀ : ℕ) (_hX₀ : 16 ≤ X₀) {J : ℕ} {η : ℝ}
    (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ)
    (hX : 16 ≤ X) (hXX₀ : X ≤ X₀) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T) :
    let C₀ := (36 * Real.pi + 2) * (Real.log (X₀ : ℝ)) ^ (1 / 400 : ℝ)
    ∫ t in S.Uset hJ β X T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      C₀ * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  intro C₀
  have hX_ge1 : 1 ≤ X := by omega
  have h_uni := integral_Uset_norm_sq_Fu_le_uniform S hJ β X T₀ T hX_ge1 hT0 hT
  have h16 : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXX₀_r : (X : ℝ) ≤ (X₀ : ℝ) := by exact_mod_cast hXX₀
  have hlog16 : 0 < Real.log 16 := by
    have := log_sixteen_gt_exp_one
    positivity
  have hlogX_pos : 0 < Real.log (X : ℝ) := by
    have : Real.log 16 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) h16
    linarith
  have hlogX_le : Real.log (X : ℝ) ≤ Real.log (X₀ : ℝ) :=
    Real.log_le_log (by linarith) hXX₀_r
  have h_rpow_le : (Real.log (X : ℝ)) ^ (1 / 400 : ℝ) ≤ (Real.log (X₀ : ℝ)) ^ (1 / 400 : ℝ) :=
    Real.rpow_le_rpow hlogX_pos.le hlogX_le (by norm_num)
  have h_rpow_pos : 0 < (Real.log (X : ℝ)) ^ (1 / 400 : ℝ) :=
    Real.rpow_pos_of_pos hlogX_pos _
  have h_one_le : 1 ≤ (Real.log (X₀ : ℝ)) ^ (1 / 400 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
    rw [Real.rpow_neg hlogX_pos.le, ← div_eq_mul_inv]
    exact (one_le_div₀ h_rpow_pos).mpr h_rpow_le
  have h_TX_nonneg : 0 ≤ T / (X : ℝ) + 1 := by
    have : 0 ≤ T / (X : ℝ) := div_nonneg (hT0.trans hT) (by positivity)
    linarith
  have h_const_nonneg : 0 ≤ (36 * Real.pi + 2) * (T / (X : ℝ) + 1) := by
    have : 0 ≤ Real.pi := Real.pi_pos.le
    positivity
  have h_scale : (36 * Real.pi + 2) * (T / (X : ℝ) + 1) ≤
      (36 * Real.pi + 2) * (T / (X : ℝ) + 1) *
        ((Real.log (X₀ : ℝ)) ^ (1 / 400 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) := by
    calc (36 * Real.pi + 2) * (T / (X : ℝ) + 1)
      _ = (36 * Real.pi + 2) * (T / (X : ℝ) + 1) * 1 := by ring
      _ ≤ (36 * Real.pi + 2) * (T / (X : ℝ) + 1) *
          ((Real.log (X₀ : ℝ)) ^ (1 / 400 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) :=
        mul_le_mul_of_nonneg_left h_one_le h_const_nonneg
  have h_reorder : (36 * Real.pi + 2) * (T / (X : ℝ) + 1) *
        ((Real.log (X₀ : ℝ)) ^ (1 / 400 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) =
      C₀ * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
    dsimp [C₀]
    ring
  rw [h_reorder] at h_scale
  exact h_uni.trans h_scale

/-- Lower bound on `log X > 1` for `X ≥ 16`. -/
lemma log_X_gt_one {X : ℕ} (hX : 16 ≤ X) : 1 < Real.log (X : ℝ) := by
  have h16 : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlog16 := log_sixteen_gt_exp_one
  have he1 : 1 < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have : 1 < Real.log 16 := he1.trans hlog16
  have h_le : Real.log 16 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) h16
  exact this.trans_le h_le

/-- Counterexample: with the parameter choices $a = 1/200$, $P_U = \lceil\exp((\log X)^{1-a})\rceil_+$,
and $Z = \exp((\log X)^{19/20})$ suggested in the asymptotic hint, $Z < P_U$ holds strictly
for all $X \ge 16$, because $1 - a = 199/200 = 0.995 > 0.95 = 19/20$. -/
theorem PU_gt_Z_of_prompt_params {X : ℕ} (hX : 16 ≤ X) :
    let a : ℝ := 1 / 200
    let P_U : ℕ := ⌈Real.exp ((Real.log (X : ℝ)) ^ (1 - a))⌉₊
    let Z : ℝ := Real.exp ((Real.log (X : ℝ)) ^ (19 / 20 : ℝ))
    Z < (P_U : ℝ) := by
  intro a P_U Z
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have ha_exp : (19 / 20 : ℝ) < 1 - a := by
    dsimp [a]
    norm_num
  have h_rpow_lt : (Real.log (X : ℝ)) ^ (19 / 20 : ℝ) < (Real.log (X : ℝ)) ^ (1 - a) :=
    Real.rpow_lt_rpow_of_exponent_lt hlogX ha_exp
  have h_exp_lt : Z < Real.exp ((Real.log (X : ℝ)) ^ (1 - a)) := by
    dsimp [Z]
    exact Real.exp_lt_exp.mpr h_rpow_lt
  have h_ceil : Real.exp ((Real.log (X : ℝ)) ^ (1 - a)) ≤ (P_U : ℝ) := Nat.le_ceil _
  exact h_exp_lt.trans_le h_ceil

/-- Exact impossibility theorem: no $X \ge 16$ can ever satisfy $P_U \le Q < Z$ with the
prompt's suggested parameters, proving that `exists_X₀_side_conditions` as stated is mathematically false. -/
theorem not_PU_le_Q_and_Q_lt_Z {X : ℕ} (hX : 16 ≤ X) (Q : ℝ) :
    let a : ℝ := 1 / 200
    let P_U : ℕ := ⌈Real.exp ((Real.log (X : ℝ)) ^ (1 - a))⌉₊
    let Z : ℝ := Real.exp ((Real.log (X : ℝ)) ^ (19 / 20 : ℝ))
    ¬ ((P_U : ℝ) ≤ Q ∧ Q < Z) := by
  intro a P_U Z ⟨hPQ, hQZ⟩
  have hPZ : (P_U : ℝ) < Z := hPQ.trans_lt hQZ
  have hZP : Z < (P_U : ℝ) := PU_gt_Z_of_prompt_params hX
  linarith

/-- The corrected parameter exponents $17/20 < 43/50 < 19/20$ strictly satisfy
the required ordering $(\log X)^{17/20} < (\log X)^{43/50} < (\log X)^{19/20}$ for all $X \ge 16$. -/
theorem corrected_params_ordering {X : ℕ} (hX : 16 ≤ X) :
    (Real.log (X : ℝ)) ^ (17 / 20 : ℝ) < (Real.log (X : ℝ)) ^ (43 / 50 : ℝ) ∧
    (Real.log (X : ℝ)) ^ (43 / 50 : ℝ) < (Real.log (X : ℝ)) ^ (19 / 20 : ℝ) := by
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have h1 : (17 / 20 : ℝ) < 43 / 50 := by norm_num
  have h2 : (43 / 50 : ℝ) < 19 / 20 := by norm_num
  exact ⟨Real.rpow_lt_rpow_of_exponent_lt hlogX h1, Real.rpow_lt_rpow_of_exponent_lt hlogX h2⟩

/-! ### Corrected Parameters and Side Conditions for $X \ge X_0$ -/

/-- Corrected small exponent parameter $a = 1/200$. -/
noncomputable def a_param : ℝ := 1 / 200

/-- Lower prime scale $P_U(X) = \lceil\exp((\log X)^{1-a})\rceil_+$. -/
noncomputable def P_U (X : ℕ) : ℕ := ⌈Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param))⌉₊

/-- Upper prime scale $Q_U(X) = \lfloor\exp((\log X)^{1-a/2})\rfloor_+$. -/
noncomputable def Q_U (X : ℕ) : ℕ := ⌊Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))⌋₊

/-- Frequency parameter $H_U(X) = (\log X)^a$. -/
noncomputable def H_U (X : ℕ) : ℝ := (Real.log (X : ℝ)) ^ a_param

/-- Zero-free region cutoff parameter $Z(X) = \exp(2 (\log X)^{1-a/2})$. -/
noncomputable def Z_param (X : ℕ) : ℝ := Real.exp (2 * (Real.log (X : ℝ)) ^ (1 - a_param / 2))

/-- Dirichlet polynomial smallness threshold $\varepsilon(X) = (\log X)^{-100}$. -/
noncomputable def eps_param (X : ℕ) : ℝ := (Real.log (X : ℝ)) ^ (-100 : ℝ)

/-- Well-spaced discretization parameter $\varepsilon_0(X) = 1/X$. -/
noncomputable def eps0_param (X : ℕ) : ℝ := 1 / (X : ℝ)

lemma a_param_pos : 0 < a_param := by dsimp [a_param]; norm_num
lemma a_param_lt_one : a_param < 1 := by dsimp [a_param]; norm_num
lemma one_sub_a_param_pos : 0 < 1 - a_param := by dsimp [a_param]; norm_num
lemma one_sub_a_half_pos : 0 < 1 - a_param / 2 := by dsimp [a_param]; norm_num
lemma one_sub_a_lt_one_sub_a_half : 1 - a_param < 1 - a_param / 2 := by dsimp [a_param]; norm_num
lemma one_sub_a_half_lt_one : 1 - a_param / 2 < 1 := by dsimp [a_param]; norm_num

/-- Under the corrected parameters, $Q_U < Z$ holds unconditionally for all $X \ge 16$. -/
theorem QU_lt_Z_corrected {X : ℕ} (hX : 16 ≤ X) : (Q_U X : ℝ) < Z_param X := by
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hrpow_pos : 0 < (Real.log (X : ℝ)) ^ (1 - a_param / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hlt : (Real.log (X : ℝ)) ^ (1 - a_param / 2) < 2 * (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by linarith
  have hexp : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) < Z_param X := by
    dsimp [Z_param]
    exact Real.exp_lt_exp.mpr hlt
  have hfloor : (Q_U X : ℝ) ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) := Nat.floor_le (by positivity)
  exact hfloor.trans_lt hexp

/-- $2 \le P_U(X)$ holds unconditionally for all $X \ge 16$. -/
theorem two_le_P_U {X : ℕ} (hX : 16 ≤ X) : 2 ≤ P_U X := by
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have h_rpow : (1 : ℝ) < (Real.log (X : ℝ)) ^ (1 - a_param) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (1 - a_param) := (Real.one_rpow _).symm
      _ < (Real.log (X : ℝ)) ^ (1 - a_param) := Real.rpow_lt_rpow zero_le_one hlogX one_sub_a_param_pos
  have hexp : Real.exp 1 < Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := Real.exp_lt_exp.mpr h_rpow
  have he : 2 < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2 : 2 < Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := he.trans hexp
  have hceil : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) ≤ (P_U X : ℝ) := Nat.le_ceil _
  have h_le : (2 : ℝ) ≤ (P_U X : ℝ) := (h2.trans_le hceil).le
  exact_mod_cast h_le

/-- $4 \le Z(X)$ holds unconditionally for all $X \ge 16$. -/
theorem four_le_Z {X : ℕ} (hX : 16 ≤ X) : 4 ≤ Z_param X := by
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have h_rpow : (1 : ℝ) < (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (1 - a_param / 2) := (Real.one_rpow _).symm
      _ < (Real.log (X : ℝ)) ^ (1 - a_param / 2) := Real.rpow_lt_rpow zero_le_one hlogX one_sub_a_half_pos
  have h2 : 2 < 2 * (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by linarith
  have hexp : Real.exp 2 < Z_param X := by
    dsimp [Z_param]
    exact Real.exp_lt_exp.mpr h2
  have he1 : 2 < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have he2 : 4 < Real.exp 2 := by
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ < Real.exp 1 * Real.exp 1 := mul_lt_mul he1 he1.le (by norm_num) (by positivity)
      _ = Real.exp (1 + 1) := (Real.exp_add 1 1).symm
      _ = Real.exp 2 := by norm_num
  linarith [he2.trans hexp]

/-- $\varepsilon(X) \ge 0$ for all $X \ge 16$. -/
theorem eps_param_nonneg {X : ℕ} (hX : 16 ≤ X) : 0 ≤ eps_param X := by
  have hlogX : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  dsimp [eps_param]
  positivity

/-- $\varepsilon_0(X) > 0$ for all $X \ge 16$. -/
theorem eps0_param_pos {X : ℕ} (hX : 16 ≤ X) : 0 < eps0_param X := by
  dsimp [eps0_param]
  have : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  positivity

/-- Limit of $\log X \to \infty$ along natural numbers. -/
lemma tendsto_log_natCast_atTop : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- Limit of $(\log X)^b \to \infty$ for any positive exponent $b > 0$. -/
lemma tendsto_log_rpow_atTop {b : ℝ} (hb : 0 < b) :
    Tendsto (fun X : ℕ => (Real.log (X : ℝ)) ^ b) atTop atTop :=
  (tendsto_rpow_atTop hb).comp tendsto_log_natCast_atTop

/-- $(\log X)^{1/15} \ge 3$ holds eventually. -/
theorem eventually_three_le_log_rpow_fifteen :
    ∀ᶠ X : ℕ in atTop, 3 ≤ (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) :=
  (tendsto_log_rpow_atTop (by norm_num : 0 < (1 / 15 : ℝ))).eventually_ge_atTop 3

/-- $\log \log X \ge 2$ holds eventually. -/
theorem eventually_two_le_log_log :
    ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log (Real.log (X : ℝ)) :=
  (Real.tendsto_log_atTop.comp tendsto_log_natCast_atTop).eventually_ge_atTop 2

/-- $2 \le H_U(X)$ holds eventually. -/
theorem eventually_two_le_H_U :
    ∀ᶠ X : ℕ in atTop, 2 ≤ H_U X :=
  (tendsto_log_rpow_atTop a_param_pos).eventually_ge_atTop 2

/-- $Z(X) \le \sqrt{X}$ holds whenever $4 \le (\log X)^{a/2}$. -/
theorem Z_le_sqrt_of_four_le_rpow {X : ℕ} (hX : 16 ≤ X)
    (h4 : 4 ≤ (Real.log (X : ℝ)) ^ (a_param / 2)) :
    Z_param X ≤ Real.sqrt (X : ℝ) := by
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have h_add : (1 - a_param / 2) + a_param / 2 = 1 := by ring
  have h_mul : (Real.log (X : ℝ)) ^ (1 - a_param / 2) * (Real.log (X : ℝ)) ^ (a_param / 2) = Real.log (X : ℝ) := by
    rw [← Real.rpow_add hpos, h_add, Real.rpow_one]
  have h_le : 4 * (Real.log (X : ℝ)) ^ (1 - a_param / 2) ≤ Real.log (X : ℝ) := by
    calc 4 * (Real.log (X : ℝ)) ^ (1 - a_param / 2)
      _ = (Real.log (X : ℝ)) ^ (1 - a_param / 2) * 4 := by ring
      _ ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) * (Real.log (X : ℝ)) ^ (a_param / 2) :=
        mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hpos.le _)
      _ = Real.log (X : ℝ) := h_mul
  have h_exp_le : 2 * (Real.log (X : ℝ)) ^ (1 - a_param / 2) ≤ (1 / 2 : ℝ) * Real.log (X : ℝ) := by linarith
  have hexp : Z_param X ≤ Real.exp ((1 / 2 : ℝ) * Real.log (X : ℝ)) := by
    dsimp [Z_param]
    exact Real.exp_le_exp.mpr h_exp_le
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hsqrt : Real.exp ((1 / 2 : ℝ) * Real.log (X : ℝ)) = Real.sqrt (X : ℝ) := by
    rw [mul_comm, ← Real.rpow_def_of_pos hX_pos, Real.sqrt_eq_rpow]
  rw [hsqrt] at hexp
  exact hexp

/-- $Z(X) \le \sqrt{X}$ holds eventually. -/
theorem eventually_Z_le_sqrt : ∀ᶠ X : ℕ in atTop, Z_param X ≤ Real.sqrt (X : ℝ) := by
  have ha_pos : 0 < a_param / 2 := by dsimp [a_param]; norm_num
  have h4 := (tendsto_log_rpow_atTop ha_pos).eventually_ge_atTop 4
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h4] with X hX h4X
  exact Z_le_sqrt_of_four_le_rpow hX h4X

/-- $P_U(X)^4 \le X$ holds eventually. -/
theorem eventually_P_U_pow_four_le :
    ∀ᶠ X : ℕ in atTop, (P_U X : ℝ) ^ 4 ≤ (X : ℝ) := by
  have ha_pos : 0 < a_param := by dsimp [a_param]; norm_num
  have h_rpow_neg : Tendsto (fun X : ℕ => (Real.log (X : ℝ)) ^ (-a_param)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ha_pos).comp tendsto_log_natCast_atTop
  have h_four_mul : Tendsto (fun X : ℕ => 4 * (Real.log (X : ℝ)) ^ (-a_param)) atTop (𝓝 0) := by
    have := h_rpow_neg.const_mul 4
    simpa using this
  have h_log_inv : Tendsto (fun X : ℕ => Real.log 16 / Real.log (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_natCast_atTop
  have h_sum : Tendsto (fun X : ℕ => Real.log 16 / Real.log (X : ℝ) + 4 * (Real.log (X : ℝ)) ^ (-a_param)) atTop (𝓝 0) := by
    have := h_log_inv.add h_four_mul
    simpa using this
  have h_eventually_lt_one := (Tendsto.eventually_lt_const (show (0 : ℝ) < 1 by norm_num) h_sum)
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_eventually_lt_one] with X hX h_lt
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have h_mul_le : Real.log 16 + 4 * (Real.log (X : ℝ)) ^ (1 - a_param) ≤ Real.log (X : ℝ) := by
    have h_factor : 4 * (Real.log (X : ℝ)) ^ (1 - a_param) = (4 * (Real.log (X : ℝ)) ^ (-a_param)) * Real.log (X : ℝ) := by
      have h_add : -a_param + 1 = 1 - a_param := by ring
      calc 4 * (Real.log (X : ℝ)) ^ (1 - a_param) = 4 * ((Real.log (X : ℝ)) ^ (-a_param + 1)) := by rw [h_add]
        _ = 4 * ((Real.log (X : ℝ)) ^ (-a_param) * (Real.log (X : ℝ)) ^ (1 : ℝ)) := by rw [Real.rpow_add hpos]
        _ = 4 * ((Real.log (X : ℝ)) ^ (-a_param) * Real.log (X : ℝ)) := by rw [Real.rpow_one]
        _ = (4 * (Real.log (X : ℝ)) ^ (-a_param)) * Real.log (X : ℝ) := by ring
    have h_div : Real.log 16 = (Real.log 16 / Real.log (X : ℝ)) * Real.log (X : ℝ) := by
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)]
    calc Real.log 16 + 4 * (Real.log (X : ℝ)) ^ (1 - a_param)
      _ = (Real.log 16 / Real.log (X : ℝ)) * Real.log (X : ℝ) + (4 * (Real.log (X : ℝ)) ^ (-a_param)) * Real.log (X : ℝ) := by rw [← h_div, ← h_factor]
      _ = (Real.log 16 / Real.log (X : ℝ) + 4 * (Real.log (X : ℝ)) ^ (-a_param)) * Real.log (X : ℝ) := by ring
      _ ≤ 1 * Real.log (X : ℝ) := mul_le_mul_of_nonneg_right h_lt.le hpos.le
      _ = Real.log (X : ℝ) := by ring
  have h_exp_le : Real.exp (Real.log 16 + 4 * (Real.log (X : ℝ)) ^ (1 - a_param)) ≤ Real.exp (Real.log (X : ℝ)) :=
    Real.exp_le_exp.mpr h_mul_le
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  rw [Real.exp_log hX_pos, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16)] at h_exp_le
  have hP_le : (P_U X : ℝ) ≤ 2 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := by
    dsimp [P_U]
    have hceil : (⌈Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param))⌉₊ : ℝ) < Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have he : 1 ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := by
      have : 0 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := by positivity
      exact Real.one_le_exp this
    linarith
  have hP_nonneg : 0 ≤ (P_U X : ℝ) := Nat.cast_nonneg _
  have hP4 : (P_U X : ℝ) ^ 4 ≤ (2 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param))) ^ 4 :=
    pow_le_pow_left₀ hP_nonneg hP_le 4
  have h_pow_eq : (2 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param))) ^ 4 =
      16 * Real.exp (4 * (Real.log (X : ℝ)) ^ (1 - a_param)) := by
    have : (2 : ℝ) ^ 4 = 16 := by norm_num
    have h_exp_pow : (Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param))) ^ 4 = Real.exp (4 * (Real.log (X : ℝ)) ^ (1 - a_param)) := by
      rw [← Real.exp_nat_mul]
      push_cast
      ring_nf
    rw [mul_pow, this, h_exp_pow]
  rw [h_pow_eq] at hP4
  exact hP4.trans h_exp_le

/-- $Q_U(X) \le X^{3/4}$ holds eventually. -/
theorem eventually_Q_U_le_X_pow_three_quarters :
    ∀ᶠ X : ℕ in atTop, (Q_U X : ℝ) ≤ (X : ℝ) ^ (3 / 4 : ℝ) := by
  have ha_pos : 0 < a_param / 2 := by dsimp [a_param]; norm_num
  have h_rpow_neg : Tendsto (fun X : ℕ => (Real.log (X : ℝ)) ^ (- (a_param / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ha_pos).comp tendsto_log_natCast_atTop
  have h_lt : ∀ᶠ X : ℕ in atTop, (Real.log (X : ℝ)) ^ (- (a_param / 2)) < 3 / 4 :=
    Tendsto.eventually_lt_const (show (0 : ℝ) < 3 / 4 by norm_num) h_rpow_neg
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_lt] with X hX h_lt_34
  have hpos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have h_add : - (a_param / 2) + 1 = 1 - a_param / 2 := by ring
  have h_exp_le : (Real.log (X : ℝ)) ^ (1 - a_param / 2) ≤ (3 / 4 : ℝ) * Real.log (X : ℝ) := by
    calc (Real.log (X : ℝ)) ^ (1 - a_param / 2)
      _ = (Real.log (X : ℝ)) ^ (- (a_param / 2) + 1) := by rw [h_add]
      _ = (Real.log (X : ℝ)) ^ (- (a_param / 2)) * (Real.log (X : ℝ)) ^ (1 : ℝ) := by rw [Real.rpow_add hpos]
      _ = (Real.log (X : ℝ)) ^ (- (a_param / 2)) * Real.log (X : ℝ) := by rw [Real.rpow_one]
      _ ≤ (3 / 4 : ℝ) * Real.log (X : ℝ) := mul_le_mul_of_nonneg_right h_lt_34.le hpos.le
  have hexp_le : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) ≤ Real.exp ((3 / 4 : ℝ) * Real.log (X : ℝ)) :=
    Real.exp_le_exp.mpr h_exp_le
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have h_rpow_eq : Real.exp ((3 / 4 : ℝ) * Real.log (X : ℝ)) = (X : ℝ) ^ (3 / 4 : ℝ) := by
    rw [mul_comm, ← Real.rpow_def_of_pos hX_pos]
  rw [h_rpow_eq] at hexp_le
  dsimp [Q_U]
  have hfloor : (⌊Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))⌋₊ : ℝ) ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) :=
    Nat.floor_le (by positivity)
  exact hfloor.trans hexp_le

/-- $P_U(X) \le Q_U(X)$ holds eventually. -/
theorem eventually_P_U_le_Q_U :
    ∀ᶠ X : ℕ in atTop, P_U X ≤ Q_U X := by
  have ha_pos : 0 < a_param / 2 := by dsimp [a_param]; norm_num
  have h1_sub : 0 < 1 - a_param / 2 := by dsimp [a_param]; norm_num
  have h_rpow_neg : Tendsto (fun X : ℕ => (Real.log (X : ℝ)) ^ (- (a_param / 2))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ha_pos).comp tendsto_log_natCast_atTop
  have h_lt_half : ∀ᶠ X : ℕ in atTop, (Real.log (X : ℝ)) ^ (- (a_param / 2)) ≤ 1 / 2 :=
    (Tendsto.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num) h_rpow_neg)
  have h_ge_four : ∀ᶠ X : ℕ in atTop, 4 ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) :=
    (tendsto_log_rpow_atTop h1_sub).eventually_ge_atTop 4
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_lt_half, h_ge_four] with X hX h_half h_four
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have h_sub_pos : 1 / 2 ≤ 1 - (Real.log (X : ℝ)) ^ (- (a_param / 2)) := by linarith
  have h_split : (Real.log (X : ℝ)) ^ (1 - a_param) = (Real.log (X : ℝ)) ^ (1 - a_param / 2) * (Real.log (X : ℝ)) ^ (- (a_param / 2)) := by
    have h_add : (1 - a_param / 2) + (- (a_param / 2)) = 1 - a_param := by ring
    rw [← Real.rpow_add hpos, h_add]
  have h_diff : 2 ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) - (Real.log (X : ℝ)) ^ (1 - a_param) := by
    calc (2 : ℝ) = 4 * (1 / 2 : ℝ) := by norm_num
      _ ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) * (1 - (Real.log (X : ℝ)) ^ (- (a_param / 2))) :=
        mul_le_mul h_four h_sub_pos (by norm_num) (by positivity)
      _ = (Real.log (X : ℝ)) ^ (1 - a_param / 2) - (Real.log (X : ℝ)) ^ (1 - a_param / 2) * (Real.log (X : ℝ)) ^ (- (a_param / 2)) := by ring
      _ = (Real.log (X : ℝ)) ^ (1 - a_param / 2) - (Real.log (X : ℝ)) ^ (1 - a_param) := by rw [h_split]
  have h_exp_add : (Real.log (X : ℝ)) ^ (1 - a_param) + 2 ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by linarith
  have h_exp_le : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param) + 2) ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) :=
    Real.exp_le_exp.mpr h_exp_add
  rw [Real.exp_add] at h_exp_le
  have he1 : 2 < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have he2 : 4 < Real.exp 2 := by
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ < Real.exp 1 * Real.exp 1 := mul_lt_mul he1 he1.le (by norm_num) (by positivity)
      _ = Real.exp (1 + 1) := (Real.exp_add 1 1).symm
      _ = Real.exp 2 := by norm_num
  have h_exp1_pos : 0 < Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := Real.exp_pos _
  have h_two_le : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) + 2 ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) := by
    calc Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) + 2
      _ ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) + 3 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := by
        have : 1 ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := by
          have : 0 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := by positivity
          exact Real.one_le_exp this
        linarith
      _ = 4 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := by ring
      _ ≤ Real.exp 2 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) :=
        mul_le_mul_of_nonneg_right he2.le h_exp1_pos.le
      _ = Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) * Real.exp 2 := by ring
      _ ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) := h_exp_le
  have hP_ceil : (P_U X : ℝ) < Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hQ_floor : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) - 1 < (Q_U X : ℝ) :=
    Nat.sub_one_lt_floor _
  have h_strict : (P_U X : ℝ) < (Q_U X : ℝ) := by linarith
  exact_mod_cast h_strict.le

/-- $H_U(X) \le \sqrt{P_U(X)}$ holds eventually. -/
theorem eventually_H_U_le_sqrt_P_U :
    ∀ᶠ X : ℕ in atTop, H_U X ≤ Real.sqrt (P_U X : ℝ) := by
  have h_exp_neg : 0 < 1 - 2 * a_param := by dsimp [a_param]; norm_num
  have h_rpow_neg : Tendsto (fun X : ℕ => (Real.log (X : ℝ)) ^ (- (1 - 2 * a_param))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop h_exp_neg).comp tendsto_log_natCast_atTop
  have h_lt_half : ∀ᶠ X : ℕ in atTop, (Real.log (X : ℝ)) ^ (- (1 - 2 * a_param)) ≤ 1 / 2 :=
    (Tendsto.eventually_le_const (show (0 : ℝ) < 1 / 2 by norm_num) h_rpow_neg)
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_lt_half] with X hX h_half
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have h_split : a_param = (- (1 - 2 * a_param)) + (1 - a_param) := by ring
  have h_HU_le : H_U X ≤ (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param) := by
    dsimp [H_U]
    calc (Real.log (X : ℝ)) ^ a_param
      _ = (Real.log (X : ℝ)) ^ ((- (1 - 2 * a_param)) + (1 - a_param)) := by nth_rw 1 [h_split]
      _ = (Real.log (X : ℝ)) ^ (- (1 - 2 * a_param)) * (Real.log (X : ℝ)) ^ (1 - a_param) := by rw [Real.rpow_add hpos]
      _ ≤ (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param) :=
        mul_le_mul_of_nonneg_right h_half (by positivity)
  have h_y_le_exp : (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param) ≤
      Real.exp ((1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param)) := by
    have := Real.add_one_le_exp ((1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param))
    linarith
  have h_exp_eq : Real.exp ((1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param)) =
      Real.sqrt (Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param))) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul, mul_comm]
  have h_ceil : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) ≤ (P_U X : ℝ) :=
    Nat.le_ceil _
  have h_sqrt_le : Real.sqrt (Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param))) ≤ Real.sqrt (P_U X : ℝ) :=
    Real.sqrt_le_sqrt h_ceil
  rw [h_exp_eq] at h_y_le_exp
  exact h_HU_le.trans (h_y_le_exp.trans h_sqrt_le)

/-- $\sqrt{z} \le z - 1$ for all $z \ge 4$. -/
lemma sqrt_le_sub_one_of_four_le {z : ℝ} (hz : 4 ≤ z) : Real.sqrt z ≤ z - 1 := by
  have h2 : 2 ≤ Real.sqrt z := by
    have : Real.sqrt 4 ≤ Real.sqrt z := Real.sqrt_le_sqrt hz
    norm_num at this
    exact this
  have : Real.sqrt z * 2 ≤ Real.sqrt z * Real.sqrt z :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [Real.mul_self_sqrt (by linarith)] at this
  linarith

/-- $\log X \le (\log(Z(X) - 1))^{5/4}$ holds eventually. -/
theorem eventually_log_X_le_log_Z_sub_one_rpow :
    ∀ᶠ X : ℕ in atTop, Real.log (X : ℝ) ≤ (Real.log (Z_param X - 1)) ^ (5 / 4 : ℝ) := by
  have h_exp_pos : 0 < (5 / 4 : ℝ) * (1 - a_param / 2) - 1 := by dsimp [a_param]; norm_num
  have h_rpow_ge_one : ∀ᶠ X : ℕ in atTop, 1 ≤ (Real.log (X : ℝ)) ^ ((5 / 4 : ℝ) * (1 - a_param / 2) - 1) :=
    (tendsto_log_rpow_atTop h_exp_pos).eventually_ge_atTop 1
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_rpow_ge_one] with X hX h_ge1
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have hZ_ge_4 : 4 ≤ Z_param X := four_le_Z hX
  have hsqrt_Z_le : Real.sqrt (Z_param X) ≤ Z_param X - 1 := sqrt_le_sub_one_of_four_le hZ_ge_4
  have hsqrt_Z_pos : 0 < Real.sqrt (Z_param X) := by
    have : (0 : ℝ) < 4 := by norm_num
    have : 0 < Z_param X := this.trans_le hZ_ge_4
    positivity
  have hlog_sqrt : Real.log (Real.sqrt (Z_param X)) ≤ Real.log (Z_param X - 1) :=
    Real.log_le_log hsqrt_Z_pos hsqrt_Z_le
  have hlog_Z_eq : Real.log (Real.sqrt (Z_param X)) = (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by
    rw [Real.sqrt_eq_rpow]
    have hZ_pos : 0 < Z_param X := by linarith
    rw [Real.log_rpow hZ_pos]
    dsimp [Z_param]
    rw [Real.log_exp]
    ring
  rw [hlog_Z_eq] at hlog_sqrt
  have hlog_sqrt_pos : 0 < (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by positivity
  have h_54_pos : 0 < (5 / 4 : ℝ) := by norm_num
  have h_pow_le : ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) ^ (5 / 4 : ℝ) ≤ (Real.log (Z_param X - 1)) ^ (5 / 4 : ℝ) :=
    Real.rpow_le_rpow hlog_sqrt_pos.le hlog_sqrt h_54_pos.le
  have h_rpow_mul : ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) ^ (5 / 4 : ℝ) =
      (Real.log (X : ℝ)) ^ ((1 - a_param / 2) * (5 / 4 : ℝ)) := by
    rw [← Real.rpow_mul hpos.le]
  have h_split : (1 - a_param / 2) * (5 / 4 : ℝ) = 1 + ((5 / 4 : ℝ) * (1 - a_param / 2) - 1) := by ring
  have h_logX_le : Real.log (X : ℝ) ≤ (Real.log (X : ℝ)) ^ ((1 - a_param / 2) * (5 / 4 : ℝ)) := by
    calc Real.log (X : ℝ) = Real.log (X : ℝ) * 1 := by ring
      _ ≤ Real.log (X : ℝ) * (Real.log (X : ℝ)) ^ ((5 / 4 : ℝ) * (1 - a_param / 2) - 1) :=
        mul_le_mul_of_nonneg_left h_ge1 hpos.le
      _ = (Real.log (X : ℝ)) ^ (1 : ℝ) * (Real.log (X : ℝ)) ^ ((5 / 4 : ℝ) * (1 - a_param / 2) - 1) := by rw [Real.rpow_one]
      _ = (Real.log (X : ℝ)) ^ (1 + ((5 / 4 : ℝ) * (1 - a_param / 2) - 1)) := (Real.rpow_add hpos _ _).symm
      _ = (Real.log (X : ℝ)) ^ ((1 - a_param / 2) * (5 / 4 : ℝ)) := by rw [← h_split]
  calc Real.log (X : ℝ)
    _ ≤ (Real.log (X : ℝ)) ^ ((1 - a_param / 2) * (5 / 4 : ℝ)) := h_logX_le
    _ = ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) ^ (5 / 4 : ℝ) := h_rpow_mul.symm
    _ ≤ (Real.log (Z_param X - 1)) ^ (5 / 4 : ℝ) := h_pow_le

/-- When $Q_U(X) \le X^{3/4}$ and $3/4 \le \beta < 1$, both $Q_U \le X^\beta$ and $Q_U \le X$ hold. -/
lemma Q_U_le_X_pow_beta {X : ℕ} (hX : 16 ≤ X) (β : ℝ) (hβ : 3 / 4 ≤ β) (hβ1 : β < 1)
    (hQ : (Q_U X : ℝ) ≤ (X : ℝ) ^ (3 / 4 : ℝ)) :
    (Q_U X : ℝ) ≤ (X : ℝ) ^ β ∧ Q_U X ≤ X := by
  have hX_pos : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have h_rpow_le : (X : ℝ) ^ (3 / 4 : ℝ) ≤ (X : ℝ) ^ β :=
    Real.rpow_le_rpow_of_exponent_le hX_pos hβ
  have h_QX_beta : (Q_U X : ℝ) ≤ (X : ℝ) ^ β := hQ.trans h_rpow_le
  have h_rpow_le_one : (X : ℝ) ^ β ≤ (X : ℝ) ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX_pos hβ1.le
  rw [Real.rpow_one] at h_rpow_le_one
  have h_QX : (Q_U X : ℝ) ≤ (X : ℝ) := h_QX_beta.trans h_rpow_le_one
  have h_QX_nat : Q_U X ≤ X := by exact_mod_cast h_QX
  exact ⟨h_QX_beta, h_QX_nat⟩

/-- All 14 side conditions for Proposition 1 exceptional set assembly hold eventually as $X \to \infty$. -/
theorem eventually_all_side_conditions :
    ∀ᶠ X : ℕ in atTop,
      16 ≤ X ∧ 2 ≤ P_U X ∧ P_U X ≤ Q_U X ∧ (Q_U X : ℝ) ≤ (X : ℝ) ^ (3 / 4 : ℝ) ∧
      (P_U X : ℝ) ^ 4 ≤ (X : ℝ) ∧ 2 ≤ H_U X ∧ H_U X ≤ Real.sqrt (P_U X : ℝ) ∧
      (Q_U X : ℝ) < Z_param X ∧ 4 ≤ Z_param X ∧ Z_param X ≤ Real.sqrt (X : ℝ) ∧
      Real.log (X : ℝ) ≤ (Real.log (Z_param X - 1)) ^ (5 / 4 : ℝ) ∧
      3 ≤ (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) ∧ 2 ≤ Real.log (Real.log (X : ℝ)) := by
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, eventually_P_U_le_Q_U, eventually_Q_U_le_X_pow_three_quarters,
    eventually_P_U_pow_four_le, eventually_two_le_H_U, eventually_H_U_le_sqrt_P_U,
    eventually_Z_le_sqrt, eventually_log_X_le_log_Z_sub_one_rpow,
    eventually_three_le_log_rpow_fifteen, eventually_two_le_log_log]
    with X hX hPQ hQX hP4 h2H hHP hZX hlogZ h3 h2
  refine ⟨hX, two_le_P_U hX, hPQ, hQX, hP4, h2H, hHP, QU_lt_Z_corrected hX, four_le_Z hX, hZX, hlogZ, h3, h2⟩

/-- Master existential threshold $X_0 \ge 16$: for all $X \ge X_0$, all side conditions hold. -/
theorem exists_X0_all_side_conditions :
    ∃ X₀ : ℕ, 16 ≤ X₀ ∧ ∀ X, X₀ ≤ X →
      16 ≤ X ∧ 2 ≤ P_U X ∧ P_U X ≤ Q_U X ∧ (Q_U X : ℝ) ≤ (X : ℝ) ^ (3 / 4 : ℝ) ∧
      (P_U X : ℝ) ^ 4 ≤ (X : ℝ) ∧ 2 ≤ H_U X ∧ H_U X ≤ Real.sqrt (P_U X : ℝ) ∧
      (Q_U X : ℝ) < Z_param X ∧ 4 ≤ Z_param X ∧ Z_param X ≤ Real.sqrt (X : ℝ) ∧
      Real.log (X : ℝ) ≤ (Real.log (Z_param X - 1)) ^ (5 / 4 : ℝ) ∧
      3 ≤ (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) ∧ 2 ≤ Real.log (Real.log (X : ℝ)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_all_side_conditions
  use max N 16
  refine ⟨le_max_right N 16, ?_⟩
  intro X hX
  have hNX : N ≤ X := (le_max_left N 16).trans hX
  exact hN X hNX

/-! ### Bookkeeping Estimates with Corrected Parameters -/

/-- Bookkeeping (i): Pointwise exponential bound $e^{v/H_U} \le e Q_U$ for $v \in I_U$. -/
lemma exp_v_div_H_le_exp_mul_Q_U {X : ℕ} {v : ℕ}
    (hH : 1 ≤ H_U X) (hv : v ≤ ⌈H_U X * Real.log (Q_U X : ℝ)⌉₊)
    (hQ_pos : 0 < (Q_U X : ℝ)) :
    Real.exp ((v : ℝ) / H_U X) ≤ Real.exp 1 * (Q_U X : ℝ) := by
  have hH_pos : 0 < H_U X := by linarith
  have hv_r : (v : ℝ) ≤ H_U X * Real.log (Q_U X : ℝ) + 1 := by
    have h_ceil : (⌈H_U X * Real.log (Q_U X : ℝ)⌉₊ : ℝ) < H_U X * Real.log (Q_U X : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have : (v : ℝ) ≤ (⌈H_U X * Real.log (Q_U X : ℝ)⌉₊ : ℝ) := by exact_mod_cast hv
    linarith
  have h_div : (v : ℝ) / H_U X ≤ Real.log (Q_U X : ℝ) + 1 / H_U X := by
    have : (v : ℝ) / H_U X ≤ (H_U X * Real.log (Q_U X : ℝ) + 1) / H_U X :=
      div_le_div_of_nonneg_right hv_r hH_pos.le
    have h_rw : (H_U X * Real.log (Q_U X : ℝ) + 1) / H_U X = Real.log (Q_U X : ℝ) + 1 / H_U X := by
      rw [add_div, mul_div_cancel_left₀ _ (ne_of_gt hH_pos)]
    linarith
  have h_inv : 1 / H_U X ≤ 1 := by
    calc 1 / H_U X ≤ 1 / 1 := one_div_le_one_div_of_le zero_lt_one hH
      _ = 1 := by norm_num
  have h_le_log : (v : ℝ) / H_U X ≤ Real.log (Q_U X : ℝ) + 1 := by linarith
  have hexp := Real.exp_le_exp.mpr h_le_log
  rw [Real.exp_add, Real.exp_log hQ_pos] at hexp
  linarith

/-- Bookkeeping (iii): Frequency ratio bound $H_U / v \le 2 / \log P_U$ for $v \ge \lfloor H_U \log P_U \rfloor$. -/
lemma H_div_v_le_two_div_log_P {H logP : ℝ} {v : ℕ}
    (hH_pos : 0 < H) (hlogP_pos : 0 < logP)
    (h_two_le : 2 ≤ H * logP) (hv : ⌊H * logP⌋₊ ≤ v) :
    H / (v : ℝ) ≤ 2 / logP := by
  have hv_r : (⌊H * logP⌋₊ : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
  have h_sub_one : H * logP - 1 ≤ (⌊H * logP⌋₊ : ℝ) := (Nat.sub_one_lt_floor _).le
  have hv_ge : H * logP - 1 ≤ (v : ℝ) := h_sub_one.trans hv_r
  have h_half : (1 / 2 : ℝ) * (H * logP) ≤ H * logP - 1 := by linarith
  have hv_ge_half : (1 / 2 : ℝ) * (H * logP) ≤ (v : ℝ) := h_half.trans hv_ge
  have hv_pos : 0 < (v : ℝ) := by
    have : 0 < (1 / 2 : ℝ) * (H * logP) := by positivity
    linarith
  have h_inv : 1 / (v : ℝ) ≤ 1 / ((1 / 2 : ℝ) * (H * logP)) :=
    one_div_le_one_div_of_le (by positivity) hv_ge_half
  have h_cancel : H * (1 / ((1 / 2 : ℝ) * (H * logP))) = 2 / logP := by
    calc H * (1 / ((1 / 2 : ℝ) * (H * logP)))
      _ = H * (2 / (H * logP)) := by ring
      _ = (H * 2) / (H * logP) := by ring
      _ = (2 * H) / (logP * H) := by ring
      _ = 2 / logP := mul_div_mul_right 2 logP (ne_of_gt hH_pos)
  calc H / (v : ℝ) = H * (1 / (v : ℝ)) := by ring
    _ ≤ H * (1 / ((1 / 2 : ℝ) * (H * logP))) := mul_le_mul_of_nonneg_left h_inv hH_pos.le
    _ = 2 / logP := h_cancel

/-- Bookkeeping (iv): Exponent comparison showing the dominant large-prime exponent
$2a - 1/8 = -23/200$ strictly beats the target rate $-1/400$. -/
lemma exponent_comparison :
    2 * a_param - 1 / 8 < - (1 / 400 : ℝ) := by
  dsimp [a_param]
  norm_num

/-- Bookkeeping (ii): Exponent comparison for the cofactor integral error $\mathcal{R}$ showing
$a/2 - 1/15 = -77/1200 < -1/16 = -75/1200$. -/
lemma R_exponent_comparison :
    a_param / 2 - 1 / 15 < - (1 / 16 : ℝ) := by
  dsimp [a_param]
  norm_num

/-- For all $X \ge 16$, if $r_1 \le r_2$, then $(\log X)^{r_1} \le (\log X)^{r_2}$. -/
lemma rpow_log_le_rpow_log_of_le {X : ℕ} (hX : 16 ≤ X) {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    (Real.log (X : ℝ)) ^ r₁ ≤ (Real.log (X : ℝ)) ^ r₂ := by
  have hlogX : 1 ≤ Real.log (X : ℝ) := (log_X_gt_one hX).le
  exact Real.rpow_le_rpow_of_exponent_le hlogX hr

/-- Subdominant power beats dominant power:
if $r_1 < r_2$ and $d > 0$, then $B (\log X)^{r_1} - d (\log X)^{r_2} \le -(d/2) (\log X)^{r_2}$ eventually. -/
lemma eventually_rpow_sub_rpow_le (r₁ r₂ B d : ℝ) (hr : r₁ < r₂) (hd : 0 < d) :
    ∀ᶠ X : ℕ in atTop, B * (Real.log (X : ℝ)) ^ r₁ - d * (Real.log (X : ℝ)) ^ r₂ ≤
      - (d / 2) * (Real.log (X : ℝ)) ^ r₂ := by
  have h_diff_pos : 0 < r₂ - r₁ := by linarith
  have h_tendsto : Tendsto (fun X : ℕ => (Real.log (X : ℝ)) ^ (r₁ - r₂)) atTop (𝓝 0) := by
    have h_neg : (fun X : ℕ => (Real.log (X : ℝ)) ^ (r₁ - r₂)) = (fun X : ℕ => (Real.log (X : ℝ)) ^ (- (r₂ - r₁))) := by
      ext X
      congr 1
      ring
    rw [h_neg]
    exact (tendsto_rpow_neg_atTop h_diff_pos).comp tendsto_log_natCast_atTop
  have hd2_pos : 0 < d / 2 := by linarith
  have h_mul_tendsto : Tendsto (fun X : ℕ => B * (Real.log (X : ℝ)) ^ (r₁ - r₂)) atTop (𝓝 0) := by
    have := h_tendsto.const_mul B
    simpa using this
  have h_le : ∀ᶠ X : ℕ in atTop, B * (Real.log (X : ℝ)) ^ (r₁ - r₂) ≤ d / 2 :=
    Tendsto.eventually_le_const hd2_pos h_mul_tendsto
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_le] with X hX h_B
  have hlogX : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have h_r2_pos : 0 < (Real.log (X : ℝ)) ^ r₂ := Real.rpow_pos_of_pos hlogX _
  have h_split : r₁ = (r₁ - r₂) + r₂ := by ring
  have h_factor : B * (Real.log (X : ℝ)) ^ r₁ = (B * (Real.log (X : ℝ)) ^ (r₁ - r₂)) * (Real.log (X : ℝ)) ^ r₂ := by
    calc B * (Real.log (X : ℝ)) ^ r₁
      _ = B * (Real.log (X : ℝ)) ^ ((r₁ - r₂) + r₂) := by nth_rw 1 [h_split]
      _ = B * ((Real.log (X : ℝ)) ^ (r₁ - r₂) * (Real.log (X : ℝ)) ^ r₂) := by rw [Real.rpow_add hlogX]
      _ = (B * (Real.log (X : ℝ)) ^ (r₁ - r₂)) * (Real.log (X : ℝ)) ^ r₂ := by ring
  rw [h_factor]
  calc (B * (Real.log (X : ℝ)) ^ (r₁ - r₂)) * (Real.log (X : ℝ)) ^ r₂ - d * (Real.log (X : ℝ)) ^ r₂
    _ = (B * (Real.log (X : ℝ)) ^ (r₁ - r₂) - d) * (Real.log (X : ℝ)) ^ r₂ := by ring
    _ ≤ (d / 2 - d) * (Real.log (X : ℝ)) ^ r₂ := mul_le_mul_of_nonneg_right (by linarith) h_r2_pos.le
    _ = - (d / 2) * (Real.log (X : ℝ)) ^ r₂ := by ring

/-- Exponential of subdominant minus dominant power is $\le 1$ eventually. -/
lemma eventually_exp_rpow_sub_rpow_le_one (r₁ r₂ B d : ℝ) (hr : r₁ < r₂) (hd : 0 < d) (_hr2 : 0 < r₂) :
    ∀ᶠ X : ℕ in atTop, Real.exp (B * (Real.log (X : ℝ)) ^ r₁ - d * (Real.log (X : ℝ)) ^ r₂) ≤ 1 := by
  have h_sub := eventually_rpow_sub_rpow_le r₁ r₂ B d hr hd
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_sub] with X hX h_le
  have hlogX : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have h_neg_le : - (d / 2) * (Real.log (X : ℝ)) ^ r₂ ≤ 0 := by
    have : 0 ≤ d / 2 := by linarith
    nlinarith [Real.rpow_nonneg hlogX.le r₂]
  have h_exp_le : B * (Real.log (X : ℝ)) ^ r₁ - d * (Real.log (X : ℝ)) ^ r₂ ≤ 0 := h_le.trans h_neg_le
  exact Real.exp_le_one_iff.mpr h_exp_le

/-- Product with constant $A > 0$: $A \exp(B (\log X)^{r_1} - d (\log X)^{r_2}) \le 1$ eventually. -/
lemma eventually_mul_exp_rpow_sub_rpow_le_one (A : ℝ) (hA : 0 < A) (r₁ r₂ B d : ℝ)
    (hr1 : 0 ≤ r₁) (hr : r₁ < r₂) (hd : 0 < d) (hr2 : 0 < r₂) :
    ∀ᶠ X : ℕ in atTop, A * Real.exp (B * (Real.log (X : ℝ)) ^ r₁ - d * (Real.log (X : ℝ)) ^ r₂) ≤ 1 := by
  let B' := B + |Real.log A|
  have h_sub := eventually_exp_rpow_sub_rpow_le_one r₁ r₂ B' d hr hd hr2
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_sub] with X hX h_le
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hlogX_r1 : 1 ≤ (Real.log (X : ℝ)) ^ r₁ := by
    calc (1 : ℝ) = (1 : ℝ) ^ r₁ := (Real.one_rpow _).symm
      _ ≤ (Real.log (X : ℝ)) ^ r₁ := Real.rpow_le_rpow zero_le_one hlogX.le hr1
  have h_logA : Real.log A ≤ |Real.log A| * (Real.log (X : ℝ)) ^ r₁ := by
    calc Real.log A ≤ |Real.log A| := le_abs_self _
      _ = |Real.log A| * 1 := by ring
      _ ≤ |Real.log A| * (Real.log (X : ℝ)) ^ r₁ := mul_le_mul_of_nonneg_left hlogX_r1 (abs_nonneg _)
  have h_exp_add : Real.log A + (B * (Real.log (X : ℝ)) ^ r₁ - d * (Real.log (X : ℝ)) ^ r₂) ≤
      B' * (Real.log (X : ℝ)) ^ r₁ - d * (Real.log (X : ℝ)) ^ r₂ := by
    dsimp [B']
    linarith
  have hexp : Real.exp (Real.log A + (B * (Real.log (X : ℝ)) ^ r₁ - d * (Real.log (X : ℝ)) ^ r₂)) ≤
      Real.exp (B' * (Real.log (X : ℝ)) ^ r₁ - d * (Real.log (X : ℝ)) ^ r₂) :=
    Real.exp_le_exp.mpr h_exp_add
  rw [Real.exp_add, Real.exp_log hA] at hexp
  exact hexp.trans h_le

/-- Log-log subdominance: $\log \log X \le c (\log X)^r$ eventually for any $r, c > 0$. -/
lemma eventually_log_log_le_rpow {r : ℝ} (hr : 0 < r) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, Real.log (Real.log (X : ℝ)) ≤ c * (Real.log (X : ℝ)) ^ r := by
  have h_bound := (_root_.isLittleO_log_rpow_atTop hr).bound hc
  have h_comp := tendsto_log_natCast_atTop.eventually h_bound
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_comp] with X hX hx
  have hlogX : 1 ≤ Real.log (X : ℝ) := (log_X_gt_one hX).le
  have hloglogX_nonneg : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg hlogX
  rw [Real.norm_eq_abs, abs_of_nonneg hloglogX_nonneg] at hx
  have hrpow_nonneg : 0 ≤ (Real.log (X : ℝ)) ^ r := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_eq_abs, abs_of_nonneg hrpow_nonneg] at hx
  exact hx

/-- Monomial in $\log X$ is eventually bounded by an exponential:
for any $C > 0, p \in \mathbb{R}, d > 0, r > 0$, $C (\log X)^p \le \exp(d (\log X)^r)$ eventually. -/
lemma eventually_mul_rpow_log_le_exp_rpow (C : ℝ) (hC : 0 < C) (p d r : ℝ) (hd : 0 < d) (hr : 0 < r) :
    ∀ᶠ X : ℕ in atTop, C * (Real.log (X : ℝ)) ^ p ≤ Real.exp (d * (Real.log (X : ℝ)) ^ r) := by
  have hd2 : 0 < d / 2 := by linarith
  have h_const : ∀ᶠ X : ℕ in atTop, Real.log C ≤ (d / 2) * (Real.log (X : ℝ)) ^ r := by
    have h_rpow := tendsto_log_rpow_atTop hr
    have h_inf := Filter.Tendsto.const_mul_atTop hd2 h_rpow
    exact h_inf.eventually_ge_atTop (Real.log C)
  have hc_pos : 0 < (d / 2) / (|p| + 1) := by positivity
  have h_loglog := eventually_log_log_le_rpow hr ((d / 2) / (|p| + 1)) hc_pos
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_const, h_loglog] with X hX h_C h_ll
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have h_p_le : p * Real.log (Real.log (X : ℝ)) ≤ (d / 2) * (Real.log (X : ℝ)) ^ r := by
    have h_abs_p : p ≤ |p| + 1 := by
      have := le_abs_self p
      linarith
    have hloglog_nonneg : 0 ≤ Real.log (Real.log (X : ℝ)) := Real.log_nonneg hlogX.le
    have h_mul_p : p * Real.log (Real.log (X : ℝ)) ≤ (|p| + 1) * Real.log (Real.log (X : ℝ)) :=
      mul_le_mul_of_nonneg_right h_abs_p hloglog_nonneg
    have h_mul_ll : (|p| + 1) * Real.log (Real.log (X : ℝ)) ≤ (|p| + 1) * (((d / 2) / (|p| + 1)) * (Real.log (X : ℝ)) ^ r) :=
      mul_le_mul_of_nonneg_left h_ll (by positivity)
    have h_cancel : (|p| + 1) * (((d / 2) / (|p| + 1)) * (Real.log (X : ℝ)) ^ r) = (d / 2) * (Real.log (X : ℝ)) ^ r := by
      have : (|p| + 1) ≠ 0 := by positivity
      calc (|p| + 1) * (((d / 2) / (|p| + 1)) * (Real.log (X : ℝ)) ^ r)
        _ = ((|p| + 1) * ((d / 2) / (|p| + 1))) * (Real.log (X : ℝ)) ^ r := by ring
        _ = (d / 2) * (Real.log (X : ℝ)) ^ r := by rw [mul_div_cancel₀ _ this]
    linarith
  have h_sum : Real.log C + p * Real.log (Real.log (X : ℝ)) ≤ d * (Real.log (X : ℝ)) ^ r := by
    linarith
  have hexp := Real.exp_le_exp.mpr h_sum
  rw [Real.exp_add, Real.exp_log hC] at hexp
  have h_rpow_eq : Real.exp (p * Real.log (Real.log (X : ℝ))) = (Real.log (X : ℝ)) ^ p := by
    rw [mul_comm, ← Real.rpow_def_of_pos hpos]
  rw [h_rpow_eq] at hexp
  exact hexp

/-- $1 / H_U(X) \le (\log X)^{-1/400}$ for all $X \ge 16$. -/
lemma one_div_H_U_le {X : ℕ} (hX : 16 ≤ X) :
    1 / H_U X ≤ (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  dsimp [H_U, a_param]
  have hlogX : 1 ≤ Real.log (X : ℝ) := (log_X_gt_one hX).le
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  rw [one_div, ← Real.rpow_neg hpos.le]
  exact Real.rpow_le_rpow_of_exponent_le hlogX (by norm_num)

/-- $1 / P_U(X) \le (\log X)^{-1/400}$ for all $X \ge 16$. -/
lemma one_div_P_U_le {X : ℕ} (hX : 16 ≤ X) :
    1 / (P_U X : ℝ) ≤ (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  have hlogX : 1 ≤ Real.log (X : ℝ) := (log_X_gt_one hX).le
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have h_rpow_le : (Real.log (X : ℝ)) ^ (1 / 400 : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 - a_param) :=
    Real.rpow_le_rpow_of_exponent_le hlogX (by dsimp [a_param]; norm_num)
  have h_exp_ge : (Real.log (X : ℝ)) ^ (1 - a_param) ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := by
    have h_nonneg : 0 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := by positivity
    have := Real.add_one_le_exp ((Real.log (X : ℝ)) ^ (1 - a_param))
    linarith
  have h_ceil : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) ≤ (P_U X : ℝ) := Nat.le_ceil _
  have hP_ge : (Real.log (X : ℝ)) ^ (1 / 400 : ℝ) ≤ (P_U X : ℝ) :=
    h_rpow_le.trans (h_exp_ge.trans h_ceil)
  have h_rpow_pos : 0 < (Real.log (X : ℝ)) ^ (1 / 400 : ℝ) := Real.rpow_pos_of_pos hpos _
  have h_inv := one_div_le_one_div_of_le h_rpow_pos hP_ge
  rw [Real.rpow_neg hpos.le, ← one_div]
  exact h_inv

/-- $\log(P_U X) / \log(Q_U X) \le 4 (\log X)^{-1/400}$ eventually. -/
lemma eventually_log_P_U_div_log_Q_U_le :
    ∀ᶠ X : ℕ in atTop, Real.log (P_U X : ℝ) / Real.log (Q_U X : ℝ) ≤
      4 * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  have ha_pos : 0 < a_param / 2 := by dsimp [a_param]; norm_num
  have h_rpow_ge : ∀ᶠ X : ℕ in atTop, 2 ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) :=
    (tendsto_log_rpow_atTop (by dsimp [a_param]; norm_num)).eventually_ge_atTop 2
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_rpow_ge] with X hX h_ge2
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have hP_ceil : (P_U X : ℝ) < Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have he1 : 1 ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := by
    have : 0 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := by positivity
    exact Real.one_le_exp this
  have hP_le : (P_U X : ℝ) ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param) + 1) := by
    calc (P_U X : ℝ) ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) + 1 := hP_ceil.le
      _ ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) * Real.exp 1 := by
        have : 2 < Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
        nlinarith
      _ = Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param) + 1) := (Real.exp_add _ _).symm
  have hP_pos : 0 < (P_U X : ℝ) := by
    have : 2 ≤ P_U X := two_le_P_U hX
    exact Nat.cast_pos.mpr (by omega)
  have hlogP_le : Real.log (P_U X : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 - a_param) + 1 := by
    rw [← Real.log_exp ((Real.log (X : ℝ)) ^ (1 - a_param) + 1)]
    exact Real.log_le_log hP_pos hP_le
  have h1_le_rpow : 1 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (1 - a_param) := (Real.one_rpow _).symm
      _ ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := Real.rpow_le_rpow zero_le_one hlogX.le one_sub_a_param_pos.le
  have hlogP_le2 : Real.log (P_U X : ℝ) ≤ 2 * (Real.log (X : ℝ)) ^ (1 - a_param) := by linarith
  have hQ_floor : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) - 1 ≤ (Q_U X : ℝ) :=
    (Nat.sub_one_lt_floor _).le
  have he2 : Real.exp 1 ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2) - 1) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hQ_ge : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2) - 1) ≤ (Q_U X : ℝ) := by
    have h_exp_sub : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2) - 1) ≤
        Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) - 1 := by
      have : 1 ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) - 1 := by linarith
      have h_add := Real.add_one_le_exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2) - 1)
      have h_exp1 : 2 < Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      have : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) =
          Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2) - 1 + 1) := by ring_nf
      rw [this, Real.exp_add]
      nlinarith
    exact h_exp_sub.trans hQ_floor
  have hQ_pos : 0 < (Q_U X : ℝ) := by
    have : 0 < Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2) - 1) := Real.exp_pos _
    exact this.trans_le hQ_ge
  have hlogQ_ge : (Real.log (X : ℝ)) ^ (1 - a_param / 2) - 1 ≤ Real.log (Q_U X : ℝ) := by
    rw [← Real.log_exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2) - 1)]
    exact Real.log_le_log (Real.exp_pos _) hQ_ge
  have hlogQ_ge_half : (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param / 2) ≤ Real.log (Q_U X : ℝ) := by
    have : (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param / 2) ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) - 1 := by
      linarith
    exact this.trans hlogQ_ge
  have hlogQ_pos : 0 < Real.log (Q_U X : ℝ) := by
    have : 0 < (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by positivity
    exact this.trans_le hlogQ_ge_half
  have h_half_pos : 0 < (1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by positivity
  have h_div_le1 : Real.log (P_U X : ℝ) / Real.log (Q_U X : ℝ) ≤
      (2 * (Real.log (X : ℝ)) ^ (1 - a_param)) / Real.log (Q_U X : ℝ) :=
    div_le_div_of_nonneg_right hlogP_le2 hlogQ_pos.le
  have h_div_le2 : (2 * (Real.log (X : ℝ)) ^ (1 - a_param)) / Real.log (Q_U X : ℝ) ≤
      (2 * (Real.log (X : ℝ)) ^ (1 - a_param)) / ((1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param / 2)) :=
    div_le_div_of_nonneg_left (by positivity) h_half_pos hlogQ_ge_half
  have h_div_le := h_div_le1.trans h_div_le2
  have h_rpow_sub : (Real.log (X : ℝ)) ^ (1 - a_param) / (Real.log (X : ℝ)) ^ (1 - a_param / 2) =
      (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
    rw [← Real.rpow_sub hpos]
    congr 1
    dsimp [a_param]
    ring
  have h_calc : (2 * (Real.log (X : ℝ)) ^ (1 - a_param)) / ((1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param / 2)) =
      4 * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
    calc (2 * (Real.log (X : ℝ)) ^ (1 - a_param)) / ((1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param / 2))
      _ = (2 / (1 / 2 : ℝ)) * ((Real.log (X : ℝ)) ^ (1 - a_param) / (Real.log (X : ℝ)) ^ (1 - a_param / 2)) := by ring
      _ = 4 * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by rw [h_rpow_sub]; norm_num
  rw [h_calc] at h_div_le
  exact h_div_le

/-- Sieve error bound: $1/H_U + 1/P_U + \log P_U / \log Q_U \le 6 (\log X)^{-1/400}$ eventually. -/
lemma eventually_sieve_error_le :
    ∀ᶠ X : ℕ in atTop, 1 / H_U X + 1 / (P_U X : ℝ) + Real.log (P_U X : ℝ) / Real.log (Q_U X : ℝ) ≤
      6 * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, eventually_log_P_U_div_log_Q_U_le] with X hX h_log_ratio
  have hH := one_div_H_U_le hX
  have hP := one_div_P_U_le hX
  linarith

/-- $\log(Z(X) - 1) \ge (\log X)^{1 - a/2}$ for all $X \ge 16$. -/
lemma log_Z_sub_one_ge {X : ℕ} (hX : 16 ≤ X) :
    (Real.log (X : ℝ)) ^ (1 - a_param / 2) ≤ Real.log (Z_param X - 1) := by
  have hZ_ge_4 : 4 ≤ Z_param X := four_le_Z hX
  have hsqrt_Z_le : Real.sqrt (Z_param X) ≤ Z_param X - 1 := sqrt_le_sub_one_of_four_le hZ_ge_4
  have hsqrt_Z_pos : 0 < Real.sqrt (Z_param X) := by
    have : (0 : ℝ) < 4 := by norm_num
    have : 0 < Z_param X := this.trans_le hZ_ge_4
    positivity
  have hlog_sqrt : Real.log (Real.sqrt (Z_param X)) ≤ Real.log (Z_param X - 1) :=
    Real.log_le_log hsqrt_Z_pos hsqrt_Z_le
  have hlog_Z_eq : Real.log (Real.sqrt (Z_param X)) = (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by
    rw [Real.sqrt_eq_rpow]
    have hZ_pos : 0 < Z_param X := by linarith
    rw [Real.log_rpow hZ_pos]
    dsimp [Z_param]
    rw [Real.log_exp]
    ring
  rw [← hlog_Z_eq]
  exact hlog_sqrt

/-- The density error $(1 + \log P_U)^3 / \sqrt{P_U}$ is bounded by $1 / (H_U \log P_U)$ eventually. -/
lemma eventually_P_U_density_bound :
    ∀ᶠ X : ℕ in atTop, (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ) ≤
      1 / (H_U X * Real.log (P_U X : ℝ)) := by
  have hd : (0 : ℝ) < 1 / 2 := by norm_num
  have hr : (0 : ℝ) < 1 - a_param := one_sub_a_param_pos
  have h_mul := eventually_mul_rpow_log_le_exp_rpow 54 (by norm_num) (4 - 3 * a_param) (1 / 2) (1 - a_param) hd hr
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  have h_rpow_ge : ∀ᶠ X : ℕ in atTop, 2 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) :=
    (tendsto_log_rpow_atTop one_sub_a_param_pos).eventually_ge_atTop 2
  filter_upwards [h16, h_rpow_ge, h_mul] with X hX h_ge2 h_exp_le
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have hP_pos : 0 < (P_U X : ℝ) := by
    have : 2 ≤ P_U X := two_le_P_U hX
    exact Nat.cast_pos.mpr (by omega)
  have hP_ceil : (P_U X : ℝ) < Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) + 1 :=
    Nat.ceil_lt_add_one (Real.exp_pos _).le
  have he1 : 1 ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) := by
    have : 0 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := by positivity
    exact Real.one_le_exp this
  have hP_le : (P_U X : ℝ) ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param) + 1) := by
    calc (P_U X : ℝ) ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) + 1 := hP_ceil.le
      _ ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) * Real.exp 1 := by
        have : 2 < Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
        nlinarith
      _ = Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param) + 1) := (Real.exp_add _ _).symm
  have hlogP_le : Real.log (P_U X : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 - a_param) + 1 := by
    rw [← Real.log_exp ((Real.log (X : ℝ)) ^ (1 - a_param) + 1)]
    exact Real.log_le_log hP_pos hP_le
  have hlogP_le2 : Real.log (P_U X : ℝ) ≤ 2 * (Real.log (X : ℝ)) ^ (1 - a_param) := by
    have : 1 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (1 - a_param) := (Real.one_rpow _).symm
        _ ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := Real.rpow_le_rpow zero_le_one hlogX.le one_sub_a_param_pos.le
    linarith
  have h1_add_logP_le : 1 + Real.log (P_U X : ℝ) ≤ 3 * (Real.log (X : ℝ)) ^ (1 - a_param) := by
    have : 1 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (1 - a_param) := (Real.one_rpow _).symm
        _ ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := Real.rpow_le_rpow zero_le_one hlogX.le one_sub_a_param_pos.le
    linarith
  have hP_ge : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) ≤ (P_U X : ℝ) := Nat.le_ceil _
  have hsqrtP_ge : Real.exp ((1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param)) ≤ Real.sqrt (P_U X : ℝ) := by
    have h_exp_eq : Real.exp ((1 / 2 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param)) =
        Real.sqrt (Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param))) := by
      rw [Real.sqrt_eq_rpow, ← Real.exp_mul, mul_comm]
    rw [h_exp_eq]
    exact Real.sqrt_le_sqrt hP_ge
  have hlogP_pos : 0 < Real.log (P_U X : ℝ) := by
    have : 2 ≤ P_U X := two_le_P_U hX
    have : (1 : ℝ) < (P_U X : ℝ) := by exact_mod_cast (by omega : 1 < P_U X)
    exact Real.log_pos this
  have hH_pos : 0 < H_U X := by
    dsimp [H_U]
    exact Real.rpow_pos_of_pos hpos _
  have hsqrtP_pos : 0 < Real.sqrt (P_U X : ℝ) := Real.sqrt_pos.mpr hP_pos
  have h_prod_le : H_U X * Real.log (P_U X : ℝ) * (1 + Real.log (P_U X : ℝ)) ^ 3 ≤
      54 * (Real.log (X : ℝ)) ^ (4 - 3 * a_param) := by
    dsimp [H_U]
    have h1 : (1 + Real.log (P_U X : ℝ)) ^ 3 ≤ (3 * (Real.log (X : ℝ)) ^ (1 - a_param)) ^ 3 := by
      apply pow_le_pow_left₀ (by positivity) h1_add_logP_le
    have h2 : (3 * (Real.log (X : ℝ)) ^ (1 - a_param)) ^ 3 = 27 * ((Real.log (X : ℝ)) ^ (1 - a_param)) ^ 3 := by ring
    rw [h2] at h1
    have h3 : ((Real.log (X : ℝ)) ^ (1 - a_param)) ^ 3 = (Real.log (X : ℝ)) ^ (3 * (1 - a_param)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
      congr 1
      ring
    rw [h3] at h1
    calc (Real.log (X : ℝ)) ^ a_param * Real.log (P_U X : ℝ) * (1 + Real.log (P_U X : ℝ)) ^ 3
      _ ≤ (Real.log (X : ℝ)) ^ a_param * (2 * (Real.log (X : ℝ)) ^ (1 - a_param)) * (27 * (Real.log (X : ℝ)) ^ (3 * (1 - a_param))) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left hlogP_le2 (by positivity)
        · exact h1
        · positivity
        · positivity
      _ = 54 * ((Real.log (X : ℝ)) ^ a_param * (Real.log (X : ℝ)) ^ (1 - a_param) * (Real.log (X : ℝ)) ^ (3 * (1 - a_param))) := by ring
      _ = 54 * (Real.log (X : ℝ)) ^ (4 - 3 * a_param) := by
        congr 1
        rw [← Real.rpow_add hpos, ← Real.rpow_add hpos]
        congr 1
        ring
  have h_main_le : H_U X * Real.log (P_U X : ℝ) * (1 + Real.log (P_U X : ℝ)) ^ 3 ≤ Real.sqrt (P_U X : ℝ) :=
    h_prod_le.trans (h_exp_le.trans hsqrtP_ge)
  have h_prod_comm : (1 + Real.log (P_U X : ℝ)) ^ 3 * (H_U X * Real.log (P_U X : ℝ)) ≤ Real.sqrt (P_U X : ℝ) := by
    calc (1 + Real.log (P_U X : ℝ)) ^ 3 * (H_U X * Real.log (P_U X : ℝ))
      _ = H_U X * Real.log (P_U X : ℝ) * (1 + Real.log (P_U X : ℝ)) ^ 3 := by ring
      _ ≤ Real.sqrt (P_U X : ℝ) := h_main_le
  have h_div1 : (1 + Real.log (P_U X : ℝ)) ^ 3 ≤ Real.sqrt (P_U X : ℝ) / (H_U X * Real.log (P_U X : ℝ)) :=
    (le_div_iff₀ (mul_pos hH_pos hlogP_pos)).mpr h_prod_comm
  have h_div2 : (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ) ≤ 1 / (H_U X * Real.log (P_U X : ℝ)) := by
    rw [div_le_iff₀ hsqrtP_pos]
    rw [div_eq_mul_one_div] at h_div1
    linarith
  exact h_div2

/-- The cofactor integral error $\mathcal{R}$ is bounded by $(\log X)^{-1/16}$ eventually. -/
lemma eventually_R_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ T₀ : ℝ, (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) ≤ T₀ →
      ((Real.log (X : ℝ) + 2) * (1 / (T₀ * Real.log (Z_param X - 1)) + Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ))) +
       1 / Z_param X +
       Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log (Z_param X))) * (Real.log (Z_param X)) ^ (6 : ℝ)) ≤
        (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by
  have h_delta : (0 : ℝ) < - (1 / 16 : ℝ) - (a_param / 2 - 1 / 15) := by
    dsimp [a_param]; norm_num
  have h_term1_ev : ∀ᶠ X : ℕ in atTop, 8 ≤ (Real.log (X : ℝ)) ^ (- (1 / 16 : ℝ) - (a_param / 2 - 1 / 15)) :=
    (tendsto_log_rpow_atTop h_delta).eventually_ge_atTop 8
  have hr2_pos : (0 : ℝ) < (1 - a_param / 2) / 16 := by dsimp [a_param]; norm_num
  have h_term2_ev := eventually_mul_rpow_log_le_exp_rpow 8 (by norm_num) (1 + 1 / 16) c ((1 - a_param / 2) / 16) hc hr2_pos
  have hr3_pos : (0 : ℝ) < 1 - a_param / 2 := by dsimp [a_param]; norm_num
  have h_term3_ev := eventually_mul_rpow_log_le_exp_rpow 4 (by norm_num) (1 / 16) 2 (1 - a_param / 2) (by norm_num) hr3_pos
  have hr4_pos : (0 : ℝ) < a_param / 2 := by dsimp [a_param]; norm_num
  have h_term4_ev := eventually_mul_rpow_log_le_exp_rpow 256 (by norm_num) (6 * (1 - a_param / 2) + 1 / 16) (1 / 8) (a_param / 2) (by norm_num) hr4_pos
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  have h_log_ge2 : ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log (X : ℝ) :=
    tendsto_log_natCast_atTop.eventually_ge_atTop 2
  filter_upwards [h16, h_log_ge2, h_term1_ev, h_term2_ev, h_term3_ev, h_term4_ev] with X hX hlog_ge2 ht1 ht2 ht3 ht4 T₀ hT0
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have hlogX_ge1 : 1 ≤ Real.log (X : ℝ) := by linarith
  have hlogX_add2 : Real.log (X : ℝ) + 2 ≤ 2 * Real.log (X : ℝ) := by linarith
  have hZ_ge_4 : 4 ≤ Z_param X := four_le_Z hX
  have hZ_pos : 0 < Z_param X := by linarith
  have hlogZ_eq : Real.log (Z_param X) = 2 * (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by
    dsimp [Z_param]
    rw [Real.log_exp]
  have hlog_Z_sub1 : (Real.log (X : ℝ)) ^ (1 - a_param / 2) ≤ Real.log (Z_param X - 1) := log_Z_sub_one_ge hX
  have hlog_Z_sub1_pos : 0 < Real.log (Z_param X - 1) := by
    have : 0 < (Real.log (X : ℝ)) ^ (1 - a_param / 2) := Real.rpow_pos_of_pos hpos _
    exact this.trans_le hlog_Z_sub1
  have hT0_pos : 0 < T₀ := by
    have : 0 < (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) := Real.rpow_pos_of_pos hpos _
    exact this.trans_le hT0
  -- Term 1
  have h_t1_main : (Real.log (X : ℝ) + 2) / (T₀ * Real.log (Z_param X - 1)) ≤
      (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by
    have h_denom_ge : (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param / 2) ≤
        T₀ * Real.log (Z_param X - 1) := mul_le_mul hT0 hlog_Z_sub1 (by positivity) hT0_pos.le
    have h_denom_eq : (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param / 2) =
        (Real.log (X : ℝ)) ^ (1 / 15 + (1 - a_param / 2)) := by rw [Real.rpow_add hpos]
    rw [h_denom_eq] at h_denom_ge
    have h_denom_pos : 0 < (Real.log (X : ℝ)) ^ (1 / 15 + (1 - a_param / 2)) := Real.rpow_pos_of_pos hpos _
    have h_div_le : (Real.log (X : ℝ) + 2) / (T₀ * Real.log (Z_param X - 1)) ≤
        (2 * Real.log (X : ℝ)) / (Real.log (X : ℝ)) ^ (1 / 15 + (1 - a_param / 2)) :=
      div_le_div₀ (by positivity) hlogX_add2 h_denom_pos h_denom_ge
    have h_div_eq : (2 * Real.log (X : ℝ)) / (Real.log (X : ℝ)) ^ (1 / 15 + (1 - a_param / 2)) =
        2 * (Real.log (X : ℝ)) ^ (a_param / 2 - 1 / 15) := by
      have h1 : Real.log (X : ℝ) = (Real.log (X : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      nth_rw 1 [h1]
      rw [mul_div_assoc, ← Real.rpow_sub hpos]
      congr 1
      ring_nf
    rw [h_div_eq] at h_div_le
    have h_exp_step : 2 * (Real.log (X : ℝ)) ^ (a_param / 2 - 1 / 15) ≤
        (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by
      have h_rpow_split : (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) =
          (Real.log (X : ℝ)) ^ (- (1 / 16 : ℝ) - (a_param / 2 - 1 / 15)) * (Real.log (X : ℝ)) ^ (a_param / 2 - 1 / 15) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
      rw [h_rpow_split]
      have : 2 ≤ (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (- (1 / 16 : ℝ) - (a_param / 2 - 1 / 15)) := by
        linarith
      nlinarith [Real.rpow_pos_of_pos hpos (a_param / 2 - 1 / 15)]
    exact h_div_le.trans h_exp_step
  -- Term 2
  have h_t2_main : (Real.log (X : ℝ) + 2) * Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ)) ≤
      (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by
    have h_rpow_sub1 : ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) ^ (1 / 16 : ℝ) ≤
        (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hlog_Z_sub1 (by norm_num)
    have h_rpow_mul : ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) ^ (1 / 16 : ℝ) =
        (Real.log (X : ℝ)) ^ ((1 - a_param / 2) / 16) := by
      rw [← Real.rpow_mul hpos.le]
      congr 1
      ring
    rw [h_rpow_mul] at h_rpow_sub1
    have h_exp_le : Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ)) ≤
        Real.exp (-c * (Real.log (X : ℝ)) ^ ((1 - a_param / 2) / 16)) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have h_comb_le : (Real.log (X : ℝ) + 2) * Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ)) ≤
        (2 * Real.log (X : ℝ)) * Real.exp (-c * (Real.log (X : ℝ)) ^ ((1 - a_param / 2) / 16)) :=
      mul_le_mul hlogX_add2 h_exp_le (by positivity) (by positivity)
    have ht2_div : Real.exp (-c * (Real.log (X : ℝ)) ^ ((1 - a_param / 2) / 16)) ≤
        (1 / 8 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 + 1 / 16 : ℝ)) := by
      have h_inv : 1 / Real.exp (c * (Real.log (X : ℝ)) ^ ((1 - a_param / 2) / 16)) ≤
          1 / (8 * (Real.log (X : ℝ)) ^ (1 + 1 / 16 : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) ht2
      rw [one_div, ← Real.exp_neg] at h_inv
      have h_rw : 1 / (8 * (Real.log (X : ℝ)) ^ (1 + 1 / 16 : ℝ)) =
          (1 / 8 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 + 1 / 16 : ℝ)) := by
        rw [one_div, mul_inv, ← one_div, ← Real.rpow_neg hpos.le]
      rw [h_rw] at h_inv
      rw [← neg_mul] at h_inv
      exact h_inv
    have h_mul_le : (2 * Real.log (X : ℝ)) * Real.exp (-c * (Real.log (X : ℝ)) ^ ((1 - a_param / 2) / 16)) ≤
        (2 * Real.log (X : ℝ)) * ((1 / 8 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 + 1 / 16 : ℝ))) :=
      mul_le_mul_of_nonneg_left ht2_div (by positivity)
    have h_calc : (2 * Real.log (X : ℝ)) * ((1 / 8 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 + 1 / 16 : ℝ))) =
        (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by
      have h1 : Real.log (X : ℝ) = (Real.log (X : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
      nth_rw 1 [h1]
      calc (2 * (Real.log (X : ℝ)) ^ (1 : ℝ)) * ((1 / 8 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 + 1 / 16 : ℝ)))
        _ = (2 * (1 / 8 : ℝ)) * ((Real.log (X : ℝ)) ^ (1 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 + 1 / 16 : ℝ))) := by ring_nf
        _ = (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (1 + -(1 + 1 / 16 : ℝ)) := by rw [Real.rpow_add hpos]; norm_num
        _ = (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by congr 2; norm_num
    rw [h_calc] at h_mul_le
    exact h_comb_le.trans h_mul_le
  -- Term 3
  have h_t3_main : 1 / Z_param X ≤ (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by
    dsimp [Z_param]
    have h_inv : 1 / Real.exp (2 * (Real.log (X : ℝ)) ^ (1 - a_param / 2)) ≤
        1 / (4 * (Real.log (X : ℝ)) ^ (1 / 16 : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) ht3
    have h_rw : 1 / (4 * (Real.log (X : ℝ)) ^ (1 / 16 : ℝ)) =
        (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by
      rw [one_div, mul_inv, ← one_div, ← Real.rpow_neg hpos.le]
    exact h_inv.trans_eq h_rw
  -- Term 4
  have h_t4_main : Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log (Z_param X))) * (Real.log (Z_param X)) ^ (6 : ℝ) ≤
      (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by
    have h_exp_arg : -(Real.log (X : ℝ)) / (4 * Real.log (Z_param X)) = - (1 / 8 : ℝ) * (Real.log (X : ℝ)) ^ (a_param / 2) := by
      rw [hlogZ_eq]
      have h1 : -(Real.log (X : ℝ)) / (4 * (2 * (Real.log (X : ℝ)) ^ (1 - a_param / 2))) =
          (- (1 / 8 : ℝ)) * ((Real.log (X : ℝ)) / (Real.log (X : ℝ)) ^ (1 - a_param / 2)) := by ring_nf
      rw [h1]
      have h2 : Real.log (X : ℝ) / (Real.log (X : ℝ)) ^ (1 - a_param / 2) = (Real.log (X : ℝ)) ^ (a_param / 2) := by
        have h_one : Real.log (X : ℝ) = (Real.log (X : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
        nth_rw 1 [h_one]
        rw [← Real.rpow_sub hpos]
        congr 1
        dsimp [a_param]
        norm_num
      rw [h2]
    rw [h_exp_arg]
    have h_logZ_pow : (Real.log (Z_param X)) ^ (6 : ℝ) = 64 * (Real.log (X : ℝ)) ^ (6 * (1 - a_param / 2)) := by
      rw [hlogZ_eq]
      have : (2 * (Real.log (X : ℝ)) ^ (1 - a_param / 2)) ^ (6 : ℝ) =
          (2 : ℝ) ^ (6 : ℝ) * ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) ^ (6 : ℝ) :=
        Real.mul_rpow (by norm_num) (by positivity)
      rw [this]
      have h26 : (2 : ℝ) ^ (6 : ℝ) = 64 := by norm_num
      rw [h26, ← Real.rpow_mul hpos.le]
      congr 1
      rw [mul_comm]
    rw [h_logZ_pow]
    have ht4_div : Real.exp (- (1 / 8 : ℝ) * (Real.log (X : ℝ)) ^ (a_param / 2)) ≤
        (1 / 256 : ℝ) * (Real.log (X : ℝ)) ^ (-(6 * (1 - a_param / 2) + 1 / 16 : ℝ)) := by
      have h_inv : 1 / Real.exp ((1 / 8 : ℝ) * (Real.log (X : ℝ)) ^ (a_param / 2)) ≤
          1 / (256 * (Real.log (X : ℝ)) ^ (6 * (1 - a_param / 2) + 1 / 16 : ℝ)) :=
        one_div_le_one_div_of_le (by positivity) ht4
      rw [one_div, ← Real.exp_neg] at h_inv
      have h_rw : 1 / (256 * (Real.log (X : ℝ)) ^ (6 * (1 - a_param / 2) + 1 / 16 : ℝ)) =
          (1 / 256 : ℝ) * (Real.log (X : ℝ)) ^ (-(6 * (1 - a_param / 2) + 1 / 16 : ℝ)) := by
        rw [one_div, mul_inv, ← one_div, ← Real.rpow_neg hpos.le]
      rw [h_rw] at h_inv
      rw [← neg_mul] at h_inv
      exact h_inv
    have h_mul_le : Real.exp (- (1 / 8 : ℝ) * (Real.log (X : ℝ)) ^ (a_param / 2)) * (64 * (Real.log (X : ℝ)) ^ (6 * (1 - a_param / 2))) ≤
        ((1 / 256 : ℝ) * (Real.log (X : ℝ)) ^ (-(6 * (1 - a_param / 2) + 1 / 16 : ℝ))) *
        (64 * (Real.log (X : ℝ)) ^ (6 * (1 - a_param / 2))) :=
      mul_le_mul_of_nonneg_right ht4_div (by positivity)
    have h_calc : ((1 / 256 : ℝ) * (Real.log (X : ℝ)) ^ (-(6 * (1 - a_param / 2) + 1 / 16 : ℝ))) *
        (64 * (Real.log (X : ℝ)) ^ (6 * (1 - a_param / 2))) =
        (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by
      calc ((1 / 256 : ℝ) * (Real.log (X : ℝ)) ^ (-(6 * (1 - a_param / 2) + 1 / 16 : ℝ))) *
          (64 * (Real.log (X : ℝ)) ^ (6 * (1 - a_param / 2)))
        _ = ((1 / 256 : ℝ) * 64) * ((Real.log (X : ℝ)) ^ (-(6 * (1 - a_param / 2) + 1 / 16 : ℝ)) *
            (Real.log (X : ℝ)) ^ (6 * (1 - a_param / 2))) := by ring_nf
        _ = (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(6 * (1 - a_param / 2) + 1 / 16 : ℝ) + 6 * (1 - a_param / 2)) := by
          rw [Real.rpow_add hpos]; norm_num
        _ = (1 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ)) := by congr 2; dsimp [a_param]; norm_num
    rw [h_calc] at h_mul_le
    exact h_mul_le
  -- Combine all 4 terms
  have h_add_expand : (Real.log (X : ℝ) + 2) * (1 / (T₀ * Real.log (Z_param X - 1)) + Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ))) =
      (Real.log (X : ℝ) + 2) / (T₀ * Real.log (Z_param X - 1)) +
      (Real.log (X : ℝ) + 2) * Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ)) := by
    rw [mul_add, mul_one_div]
  rw [h_add_expand]
  linarith

/-- The squared cofactor integral error $\mathcal{R}^2$ is bounded by $(\log X)^{-1/8}$ eventually. -/
lemma eventually_R_sq_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ T₀ : ℝ, (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) ≤ T₀ →
      ((Real.log (X : ℝ) + 2) * (1 / (T₀ * Real.log (Z_param X - 1)) + Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ))) +
       1 / Z_param X +
       Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log (Z_param X))) * (Real.log (Z_param X)) ^ (6 : ℝ)) ^ 2 ≤
        (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) := by
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, eventually_R_le c hc] with X hX hR T₀ hT0
  have hR_le := hR T₀ hT0
  have hpos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have hT0_pos : 0 < T₀ := by
    have : 0 < (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) := Real.rpow_pos_of_pos hpos _
    exact this.trans_le hT0
  have hlog_Z_sub1_pos : 0 < Real.log (Z_param X - 1) := by
    have : 0 < (Real.log (X : ℝ)) ^ (1 - a_param / 2) := Real.rpow_pos_of_pos hpos _
    exact this.trans_le (log_Z_sub_one_ge hX)
  have hZ_pos : 0 < Z_param X := by linarith [four_le_Z hX]
  have hlogZ_nonneg : 0 ≤ Real.log (Z_param X) := Real.log_nonneg (by linarith [four_le_Z hX])
  have hR_nonneg : 0 ≤ ((Real.log (X : ℝ) + 2) * (1 / (T₀ * Real.log (Z_param X - 1)) + Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ))) +
       1 / Z_param X +
       Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log (Z_param X))) * (Real.log (Z_param X)) ^ (6 : ℝ)) := by
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · refine mul_nonneg (by linarith) (add_nonneg ?_ (Real.exp_pos _).le)
      exact one_div_nonneg.mpr (mul_nonneg hT0_pos.le hlog_Z_sub1_pos.le)
    · exact one_div_nonneg.mpr hZ_pos.le
    · exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hlogZ_nonneg _)
  have h_sq := pow_le_pow_left₀ hR_nonneg hR_le 2
  have h_rpow_sq : ((Real.log (X : ℝ)) ^ (-(1 / 16 : ℝ))) ^ 2 = (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    norm_num
  rwa [h_rpow_sq] at h_sq

/-- Combined bound on the reciprocal frequency log and density term:
$1 / (H_U \log P_U) + (1 + \log P_U)^3 / \sqrt{P_U} \le 2 / (H_U \log P_U)$ eventually. -/
lemma eventually_sum_inv_H_logP_and_density_le :
    ∀ᶠ X : ℕ in atTop,
      1 / (H_U X * Real.log (P_U X : ℝ)) + (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ) ≤
        2 / (H_U X * Real.log (P_U X : ℝ)) := by
  filter_upwards [eventually_P_U_density_bound] with X h
  have : 1 / (H_U X * Real.log (P_U X : ℝ)) + 1 / (H_U X * Real.log (P_U X : ℝ)) =
      2 / (H_U X * Real.log (P_U X : ℝ)) := by ring
  linarith

/-- General cardinality bound for integer intervals: $|[a, b]| \le b + 1$. -/
lemma card_Icc_le_top_add_one (a b : ℕ) : (Finset.card (Finset.Icc a b) : ℝ) ≤ (b : ℝ) + 1 := by
  by_cases hab : a ≤ b
  · rw [Nat.card_Icc]
    have h_le : b + 1 - a ≤ b + 1 := Nat.sub_le (b + 1) a
    have h_cast : ((b + 1 - a : ℕ) : ℝ) ≤ ((b + 1 : ℕ) : ℝ) := Nat.cast_le.mpr h_le
    push_cast at h_cast
    exact h_cast
  · have : Finset.Icc a b = ∅ := Finset.Icc_eq_empty_of_lt (not_le.mp hab)
    rw [this, Finset.card_empty]
    simp only [Nat.cast_zero]
    have : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
    linarith

/-- Cardinality of the frequency index set $I_U$: $|I_U| \le 2 H_U \log Q_U$ eventually. -/
lemma eventually_card_IU_le :
    ∀ᶠ X : ℕ in atTop,
      let I_U := Finset.Icc ⌊H_U X * Real.log (P_U X : ℝ)⌋₊ ⌈H_U X * Real.log (Q_U X : ℝ)⌉₊
      (I_U.card : ℝ) ≤ 2 * (H_U X * Real.log (Q_U X : ℝ)) := by
  have h_sides := eventually_all_side_conditions
  have h_HU4 : ∀ᶠ X : ℕ in atTop, 4 ≤ H_U X :=
    (tendsto_log_rpow_atTop a_param_pos).eventually_ge_atTop 4
  filter_upwards [h_sides, h_HU4] with X hX hH4
  intro I_U
  have hP2 : 2 ≤ P_U X := hX.2.1
  have hPQ : P_U X ≤ Q_U X := hX.2.2.1
  have hQ2 : 2 ≤ Q_U X := hP2.trans hPQ
  have hQ_r : (2 : ℝ) ≤ (Q_U X : ℝ) := by exact_mod_cast hQ2
  have hlogQ_ge : (1 / 2 : ℝ) ≤ Real.log (Q_U X : ℝ) := by
    have : Real.log 2 ≤ Real.log (Q_U X : ℝ) := Real.log_le_log (by norm_num) hQ_r
    have : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    linarith
  have hpos : 0 ≤ H_U X * Real.log (Q_U X : ℝ) := by
    have : 0 ≤ H_U X := by linarith
    have : 0 ≤ Real.log (Q_U X : ℝ) := by linarith
    positivity
  have h_card := card_Icc_le_top_add_one ⌊H_U X * Real.log (P_U X : ℝ)⌋₊ ⌈H_U X * Real.log (Q_U X : ℝ)⌉₊
  have h_ceil : (⌈H_U X * Real.log (Q_U X : ℝ)⌉₊ : ℝ) < H_U X * Real.log (Q_U X : ℝ) + 1 :=
    Nat.ceil_lt_add_one hpos
  have h_two_le : 2 ≤ H_U X * Real.log (Q_U X : ℝ) := by
    calc (2 : ℝ)
      _ = 4 * (1 / 2 : ℝ) := by norm_num
      _ ≤ H_U X * Real.log (Q_U X : ℝ) := mul_le_mul hH4 hlogQ_ge (by norm_num) (by linarith)
  linarith

/-- Upper bound on $\log Q_U(X) \le (\log X)^{1 - a/2}$. -/
lemma log_Q_U_le {X : ℕ} (hX : 16 ≤ X) :
    Real.log (Q_U X : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by
  have hQ_le : (Q_U X : ℝ) ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) := Nat.floor_le (Real.exp_pos _).le
  have hpos : 0 ≤ Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have h_exp_ge1 : 1 ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) := by
    have : 0 ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by positivity
    exact Real.one_le_exp this
  have h_floor_ge1 : 1 ≤ ⌊Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))⌋₊ := Nat.le_floor (by exact_mod_cast h_exp_ge1)
  have hQ_pos : 0 < (Q_U X : ℝ) := by
    dsimp [Q_U]
    exact Nat.cast_pos.mpr (by omega)
  rw [← Real.log_exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))]
  exact Real.log_le_log hQ_pos hQ_le

/-- Lower bound on $\log P_U(X) \ge (\log X)^{1 - a}$. -/
lemma log_P_U_ge {X : ℕ} (_hX : 16 ≤ X) :
    (Real.log (X : ℝ)) ^ (1 - a_param) ≤ Real.log (P_U X : ℝ) := by
  have hP_ge : Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param)) ≤ (P_U X : ℝ) := Nat.le_ceil _
  rw [← Real.log_exp ((Real.log (X : ℝ)) ^ (1 - a_param))]
  exact Real.log_le_log (Real.exp_pos _) hP_ge

/-- Part 1 power bound: $(H_U \log Q_U)^2 (\log X)^{-199} \le (\log X)^{-1/400}$ eventually. -/
lemma eventually_part1_le :
    ∀ᶠ X : ℕ in atTop,
      (H_U X * Real.log (Q_U X : ℝ)) ^ 2 * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) ≤
        (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  have h_exp : a_param - 197 < - (1 / 400 : ℝ) := by
    dsimp [a_param]; norm_num
  have h_rpow := (tendsto_log_rpow_atTop (show 0 < - (1 / 400 : ℝ) - (a_param - 197) by dsimp [a_param]; norm_num)).eventually_ge_atTop 1
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_rpow] with X hX h_pow
  have hpos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have hH : H_U X = (Real.log (X : ℝ)) ^ a_param := rfl
  have hlogQ : Real.log (Q_U X : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) := log_Q_U_le hX
  have hH_nonneg : 0 ≤ (Real.log (X : ℝ)) ^ a_param := by positivity
  have h_prod : H_U X * Real.log (Q_U X : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 + a_param / 2) := by
    rw [hH]
    have h_mul := mul_le_mul_of_nonneg_left hlogQ hH_nonneg
    have h_add : (Real.log (X : ℝ)) ^ a_param * (Real.log (X : ℝ)) ^ (1 - a_param / 2) =
        (Real.log (X : ℝ)) ^ (1 + a_param / 2) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    rwa [h_add] at h_mul
  have h_prod_nonneg : 0 ≤ H_U X * Real.log (Q_U X : ℝ) := by
    dsimp [H_U]
    have h_exp_ge1 : 1 ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) := by
      have : 0 ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by positivity
      exact Real.one_le_exp this
    have h_floor_ge1 : 1 ≤ ⌊Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))⌋₊ := Nat.le_floor (by exact_mod_cast h_exp_ge1)
    have hQ_ge1 : 1 ≤ (Q_U X : ℝ) := by
      dsimp [Q_U]
      exact_mod_cast h_floor_ge1
    have : 0 ≤ Real.log (Q_U X : ℝ) := Real.log_nonneg hQ_ge1
    positivity
  have h_prod_sq : (H_U X * Real.log (Q_U X : ℝ)) ^ 2 ≤ ((Real.log (X : ℝ)) ^ (1 + a_param / 2)) ^ 2 :=
    pow_le_pow_left₀ h_prod_nonneg h_prod 2
  have h_sq_simp : ((Real.log (X : ℝ)) ^ (1 + a_param / 2)) ^ 2 = (Real.log (X : ℝ)) ^ (2 + a_param) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  rw [h_sq_simp] at h_prod_sq
  have h_total : (H_U X * Real.log (Q_U X : ℝ)) ^ 2 * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) ≤
      (Real.log (X : ℝ)) ^ (2 + a_param) * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) :=
    mul_le_mul_of_nonneg_right h_prod_sq (by positivity)
  have h_add_total : (Real.log (X : ℝ)) ^ (2 + a_param) * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) =
      (Real.log (X : ℝ)) ^ (a_param - 197) := by
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  rw [h_add_total] at h_total
  have h_le_fin : (Real.log (X : ℝ)) ^ (a_param - 197) ≤ (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
    rpow_log_le_rpow_log_of_le hX h_exp.le
  exact h_total.trans h_le_fin

/-- Part 2 power bound: $(\log X)^{-1/8} H_U (\log Q_U / \log P_U)^2 \le (\log X)^{-1/400}$ eventually. -/
lemma eventually_part2_le :
    ∀ᶠ X : ℕ in atTop,
      (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H_U X * (Real.log (Q_U X : ℝ) / Real.log (P_U X : ℝ)) ^ 2 ≤
        (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16] with X hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have hH : H_U X = (Real.log (X : ℝ)) ^ a_param := rfl
  have hlogQ : Real.log (Q_U X : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) := log_Q_U_le hX
  have hlogP : (Real.log (X : ℝ)) ^ (1 - a_param) ≤ Real.log (P_U X : ℝ) := log_P_U_ge hX
  have hlogP_pos : 0 < Real.log (P_U X : ℝ) := by
    have : 0 < (Real.log (X : ℝ)) ^ (1 - a_param) := by positivity
    exact this.trans_le hlogP
  have h_exp_ge1 : 1 ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) := by
    have : 0 ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by positivity
    exact Real.one_le_exp this
  have h_floor_ge1 : 1 ≤ ⌊Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))⌋₊ := Nat.le_floor (by exact_mod_cast h_exp_ge1)
  have hQ_ge1 : 1 ≤ (Q_U X : ℝ) := by
    dsimp [Q_U]
    exact_mod_cast h_floor_ge1
  have hlogQ_nonneg : 0 ≤ Real.log (Q_U X : ℝ) := Real.log_nonneg hQ_ge1
  have h_div_le : Real.log (Q_U X : ℝ) / Real.log (P_U X : ℝ) ≤ (Real.log (X : ℝ)) ^ (a_param / 2) := by
    rw [div_le_iff₀ hlogP_pos]
    have h_prod : (Real.log (X : ℝ)) ^ (a_param / 2) * (Real.log (X : ℝ)) ^ (1 - a_param) =
        (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    calc Real.log (Q_U X : ℝ)
      _ ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) := hlogQ
      _ = (Real.log (X : ℝ)) ^ (a_param / 2) * (Real.log (X : ℝ)) ^ (1 - a_param) := h_prod.symm
      _ ≤ (Real.log (X : ℝ)) ^ (a_param / 2) * Real.log (P_U X : ℝ) :=
        mul_le_mul_of_nonneg_left hlogP (by positivity)
  have h_div_sq : (Real.log (Q_U X : ℝ) / Real.log (P_U X : ℝ)) ^ 2 ≤ ((Real.log (X : ℝ)) ^ (a_param / 2)) ^ 2 := by
    have h_div_nonneg : 0 ≤ Real.log (Q_U X : ℝ) / Real.log (P_U X : ℝ) := div_nonneg hlogQ_nonneg hlogP_pos.le
    exact pow_le_pow_left₀ h_div_nonneg h_div_le 2
  have h_rpow_sq : ((Real.log (X : ℝ)) ^ (a_param / 2)) ^ 2 = (Real.log (X : ℝ)) ^ a_param := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  rw [h_rpow_sq] at h_div_sq
  have h_mul1 : H_U X * (Real.log (Q_U X : ℝ) / Real.log (P_U X : ℝ)) ^ 2 ≤ (Real.log (X : ℝ)) ^ (2 * a_param) := by
    rw [hH]
    have h_mul := mul_le_mul_of_nonneg_left h_div_sq (show 0 ≤ (Real.log (X : ℝ)) ^ a_param by positivity)
    have h_add : (Real.log (X : ℝ)) ^ a_param * (Real.log (X : ℝ)) ^ a_param = (Real.log (X : ℝ)) ^ (2 * a_param) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    rwa [h_add] at h_mul
  have h_mul2 : (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H_U X * (Real.log (Q_U X : ℝ) / Real.log (P_U X : ℝ)) ^ 2 ≤
      (Real.log (X : ℝ)) ^ (2 * a_param - 1 / 8) := by
    calc (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H_U X * (Real.log (Q_U X : ℝ) / Real.log (P_U X : ℝ)) ^ 2
      _ = (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * (H_U X * (Real.log (Q_U X : ℝ) / Real.log (P_U X : ℝ)) ^ 2) := by ring
      _ ≤ (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * (Real.log (X : ℝ)) ^ (2 * a_param) :=
        mul_le_mul_of_nonneg_left h_mul1 (by positivity)
      _ = (Real.log (X : ℝ)) ^ (2 * a_param - 1 / 8) := by
        rw [← Real.rpow_add hpos]
        congr 1
        ring
  have h_fin : (Real.log (X : ℝ)) ^ (2 * a_param - 1 / 8) ≤ (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
    rpow_log_le_rpow_log_of_le hX exponent_comparison.le
  exact h_mul2.trans h_fin

/-- Part 3 power bound: $(H_U \log Q_U)^2 / X \le (\log X)^{-1/400}$ eventually. -/
lemma eventually_part3_le :
    ∀ᶠ X : ℕ in atTop,
      (H_U X * Real.log (Q_U X : ℝ)) ^ 2 / (X : ℝ) ≤
        (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  have h_ev := eventually_mul_rpow_log_le_exp_rpow 1 (by norm_num) (2 + a_param + 1 / 400) 1 1 (by norm_num) (by norm_num)
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_ev] with X hX h_exp
  have hpos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have h_exp_rw : Real.exp (1 * (Real.log (X : ℝ)) ^ (1 : ℝ)) = (X : ℝ) := by
    rw [Real.rpow_one, one_mul, Real.exp_log hX_pos]
  rw [one_mul, h_exp_rw] at h_exp
  have hH : H_U X = (Real.log (X : ℝ)) ^ a_param := rfl
  have hlogQ : Real.log (Q_U X : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) := log_Q_U_le hX
  have hH_nonneg : 0 ≤ (Real.log (X : ℝ)) ^ a_param := by positivity
  have h_prod : H_U X * Real.log (Q_U X : ℝ) ≤ (Real.log (X : ℝ)) ^ (1 + a_param / 2) := by
    rw [hH]
    have h_mul := mul_le_mul_of_nonneg_left hlogQ hH_nonneg
    have h_add : (Real.log (X : ℝ)) ^ a_param * (Real.log (X : ℝ)) ^ (1 - a_param / 2) =
        (Real.log (X : ℝ)) ^ (1 + a_param / 2) := by
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    rwa [h_add] at h_mul
  have h_prod_nonneg : 0 ≤ H_U X * Real.log (Q_U X : ℝ) := by
    dsimp [H_U]
    have h_exp_ge1 : 1 ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) := by
      have : 0 ≤ (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by positivity
      exact Real.one_le_exp this
    have h_floor_ge1 : 1 ≤ ⌊Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))⌋₊ := Nat.le_floor (by exact_mod_cast h_exp_ge1)
    have hQ_ge1 : 1 ≤ (Q_U X : ℝ) := by
      dsimp [Q_U]
      exact_mod_cast h_floor_ge1
    have : 0 ≤ Real.log (Q_U X : ℝ) := Real.log_nonneg hQ_ge1
    positivity
  have h_prod_sq : (H_U X * Real.log (Q_U X : ℝ)) ^ 2 ≤ ((Real.log (X : ℝ)) ^ (1 + a_param / 2)) ^ 2 :=
    pow_le_pow_left₀ h_prod_nonneg h_prod 2
  have h_sq_simp : ((Real.log (X : ℝ)) ^ (1 + a_param / 2)) ^ 2 = (Real.log (X : ℝ)) ^ (2 + a_param) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  rw [h_sq_simp] at h_prod_sq
  have h_split : (Real.log (X : ℝ)) ^ (2 + a_param + 1 / 400) =
      (Real.log (X : ℝ)) ^ (2 + a_param) * (Real.log (X : ℝ)) ^ (1 / 400 : ℝ) := by
    rw [← Real.rpow_add hpos]
  rw [h_split] at h_exp
  have h_div : (Real.log (X : ℝ)) ^ (2 + a_param) ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ (1 / 400 : ℝ) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hpos _)).mpr h_exp
  have h_div_X : (Real.log (X : ℝ)) ^ (2 + a_param) / (X : ℝ) ≤ 1 / (Real.log (X : ℝ)) ^ (1 / 400 : ℝ) := by
    rw [div_le_iff₀ hX_pos]
    rw [div_eq_mul_one_div] at h_div
    linarith
  have h_inv : 1 / (Real.log (X : ℝ)) ^ (1 / 400 : ℝ) = (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
    rw [one_div, ← Real.rpow_neg hpos.le]
  rw [h_inv] at h_div_X
  have h_chain : (H_U X * Real.log (Q_U X : ℝ)) ^ 2 / (X : ℝ) ≤ (Real.log (X : ℝ)) ^ (2 + a_param) / (X : ℝ) :=
    div_le_div_of_nonneg_right h_prod_sq hX_pos.le
  exact h_chain.trans h_div_X

/-- Algebraic reduction for the bridge sum bound. -/
lemma bridge_sum_bound
    (C_B C_S C_L : ℝ) (hCB : 0 ≤ C_B) (hCS : 0 ≤ C_S) (hCL : 0 ≤ C_L)
    (X : ℕ) (_hX : 16 ≤ X)
    (H logQ logP : ℝ) (hH : 0 < H) (hlogQ : 0 ≤ logQ) (hlogP : 0 < logP)
    (card_I : ℝ) (hcard_I : card_I ≤ 2 * (H * logQ)) (_hcard_nonneg : 0 ≤ card_I)
    (sum_val : ℝ)
    (M : ℝ)
    (hM_eq : M = 4 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) +
      16 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H * logP ^ 2) + 1 / (X : ℝ))
    (hM_nonneg : 0 ≤ M)
    (hsum_val : sum_val ≤ card_I * M)
    (hp1 : (H * logQ) ^ 2 * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) ≤ (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)))
    (hp2 : (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H * (logQ / logP) ^ 2 ≤ (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)))
    (hp3 : (H * logQ) ^ 2 / (X : ℝ) ≤ (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) :
    C_B * (H * logQ) * sum_val ≤
      (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  have hHlogQ_nonneg : 0 ≤ H * logQ := mul_nonneg hH.le hlogQ
  have h_pre_nonneg : 0 ≤ C_B * (H * logQ) := mul_nonneg hCB hHlogQ_nonneg
  have h_sum_step : sum_val ≤ 2 * (H * logQ) * M := by
    calc sum_val ≤ card_I * M := hsum_val
      _ ≤ 2 * (H * logQ) * M := mul_le_mul_of_nonneg_right hcard_I hM_nonneg
  have h_mul_step : C_B * (H * logQ) * sum_val ≤ C_B * (H * logQ) * (2 * (H * logQ) * M) :=
    mul_le_mul_of_nonneg_left h_sum_step h_pre_nonneg
  have h_algebra : C_B * (H * logQ) * (2 * (H * logQ) * M) =
      8 * C_B * C_S * ((H * logQ) ^ 2 * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
      32 * C_B * C_L * ((Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H * (logQ / logP) ^ 2) +
      2 * C_B * ((H * logQ) ^ 2 / (X : ℝ)) := by
    rw [hM_eq]
    have hH_ne : H ≠ 0 := hH.ne'
    have hlogP_ne : logP ≠ 0 := hlogP.ne'
    have h1 : C_B * (H * logQ) * (2 * (H * logQ) * (16 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H * logP ^ 2))) =
        32 * C_B * C_L * ((Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H * (logQ / logP) ^ 2) := by
      calc C_B * (H * logQ) * (2 * (H * logQ) * (16 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H * logP ^ 2)))
        _ = (C_B * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ))) * (32 * ((H * logQ) * (H * logQ) / (H * logP ^ 2))) := by ring
        _ = (C_B * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ))) * (32 * (H * (logQ / logP) ^ 2)) := by
          congr 1
          have : (H * logQ) * (H * logQ) / (H * logP ^ 2) = H * (logQ / logP) ^ 2 := by
            field_simp
          rw [this]
        _ = 32 * C_B * C_L * ((Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H * (logQ / logP) ^ 2) := by ring
    calc C_B * (H * logQ) * (2 * (H * logQ) * (4 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) +
          16 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H * logP ^ 2) + 1 / (X : ℝ)))
      _ = C_B * (H * logQ) * (2 * (H * logQ) * (4 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)))) +
          C_B * (H * logQ) * (2 * (H * logQ) * (16 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H * logP ^ 2))) +
          C_B * (H * logQ) * (2 * (H * logQ) * (1 / (X : ℝ))) := by ring
      _ = 8 * C_B * C_S * ((H * logQ) ^ 2 * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
          32 * C_B * C_L * ((Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H * (logQ / logP) ^ 2) +
          2 * C_B * ((H * logQ) ^ 2 / (X : ℝ)) := by
        rw [h1]
        ring
  rw [h_algebra] at h_mul_step
  have h_bound1 : 8 * C_B * C_S * ((H * logQ) ^ 2 * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) ≤
      8 * C_B * C_S * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
    mul_le_mul_of_nonneg_left hp1 (by positivity)
  have h_bound2 : 32 * C_B * C_L * ((Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H * (logQ / logP) ^ 2) ≤
      32 * C_B * C_L * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
    mul_le_mul_of_nonneg_left hp2 (by positivity)
  have h_bound3 : 2 * C_B * ((H * logQ) ^ 2 / (X : ℝ)) ≤
      2 * C_B * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
    mul_le_mul_of_nonneg_left hp3 (by positivity)
  have h_combine : 8 * C_B * C_S * ((H * logQ) ^ 2 * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
      32 * C_B * C_L * ((Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H * (logQ / logP) ^ 2) +
      2 * C_B * ((H * logQ) ^ 2 / (X : ℝ)) ≤
      (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
    calc 8 * C_B * C_S * ((H * logQ) ^ 2 * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
          32 * C_B * C_L * ((Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * H * (logQ / logP) ^ 2) +
          2 * C_B * ((H * logQ) ^ 2 / (X : ℝ))
      _ ≤ 8 * C_B * C_S * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) +
          32 * C_B * C_L * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) +
          2 * C_B * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by linarith [h_bound1, h_bound2, h_bound3]
      _ = (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by ring
  exact h_mul_step.trans h_combine

/-- Core decay bound for the small prime cardinality factor. -/
lemma eventually_S_bound_core (C_c : ℝ) (hCc : 0 < C_c) {η : ℝ} (hη0 : 0 < η) :
    ∀ᶠ X : ℕ in atTop,
      (3 * Real.exp 1 * C_c) * Real.exp (2 * (Real.log (X : ℝ)) ^ (1 - a_param / 2) - η * (Real.log (X : ℝ))) ≤ 1 := by
  have hA : 0 < 3 * Real.exp 1 * C_c := by positivity
  have hr1 : 0 ≤ 1 - a_param / 2 := one_sub_a_half_pos.le
  have hr : 1 - a_param / 2 < 1 := one_sub_a_half_lt_one
  have hr2 : 0 < (1 : ℝ) := by norm_num
  have h := eventually_mul_exp_rpow_sub_rpow_le_one (3 * Real.exp 1 * C_c) hA (1 - a_param / 2) 1 2 η hr1 hr hη0 hr2
  filter_upwards [h] with X hX
  have h_rpow1 : (Real.log (X : ℝ)) ^ (1 : ℝ) = Real.log (X : ℝ) := Real.rpow_one (Real.log (X : ℝ))
  rwa [h_rpow1] at hX

/-- Exponent comparison for the large prime cardinality factor: $2a < 1/4 - a$. -/
lemma L_exponent_comparison : 2 * a_param < 1 / 4 - a_param := by
  dsimp [a_param]
  norm_num

/-- Core decay bound for the large prime cardinality factor. -/
lemma eventually_L_bound_core (C : ℝ) (hC : 0 < C) (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      C * Real.exp (1000 * (Real.log (X : ℝ)) ^ (2 * a_param) - (c / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param)) ≤ 1 := by
  have hr1 : 0 ≤ 2 * a_param := by dsimp [a_param]; norm_num
  have hr : 2 * a_param < 1 / 4 - a_param := L_exponent_comparison
  have hd : 0 < c / 2 := by linarith
  have hr2 : 0 < 1 / 4 - a_param := by dsimp [a_param]; norm_num
  exact eventually_mul_exp_rpow_sub_rpow_le_one C hC (2 * a_param) (1 / 4 - a_param) 1000 (c / 2) hr1 hr hd hr2

/-- Master threshold reduction: derives the final unconditional theorem from the eventual bridge bound. -/
theorem RangeSystem.integral_Uset_le_unsifted_of_eventually {_c₀ _K : ℝ} {η : ℝ}
    (h_ev : ∃ C_large : ℝ, 0 < C_large ∧
      ∀ᶠ X : ℕ in atTop, ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (T₀ T : ℝ),
        3 / 4 ≤ β → β < 1 → 16 ≤ X → (Real.log X) ^ (1 / 15 : ℝ) ≤ T₀ → T₀ ≤ T → T ≤ X →
        (∀ j, 2 ≤ S.Hj hJ j) → (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) →
        (∀ j, S.Hj hJ j ≤ Real.sqrt (S.P j)) →
        (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) →
        ∫ t in S.Uset hJ β X T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
          C_large * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ),
      3 / 4 ≤ β → β < 1 → 16 ≤ X → (Real.log X) ^ (1 / 15 : ℝ) ≤ T₀ → T₀ ≤ T → T ≤ X →
      (∀ j, 2 ≤ S.Hj hJ j) → (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) →
      (∀ j, S.Hj hJ j ≤ Real.sqrt (S.P j)) →
      (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) →
      ∫ t in S.Uset hJ β X T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  obtain ⟨C_large, hClarge_pos, h_ev_prop⟩ := h_ev
  obtain ⟨X₁, hX₁⟩ := Filter.eventually_atTop.mp h_ev_prop
  let X₀ := max 16 X₁
  have hX₀_ge16 : 16 ≤ X₀ := le_max_left 16 X₁
  have hX₀_geX₁ : X₁ ≤ X₀ := le_max_right 16 X₁
  let C₀ := (36 * Real.pi + 2) * (Real.log (X₀ : ℝ)) ^ (1 / 400 : ℝ)
  have hC₀_pos : 0 < C₀ := by
    dsimp [C₀]
    have : 0 < 36 * Real.pi + 2 := by positivity
    have : 0 < Real.log (X₀ : ℝ) := by
      have : (16 : ℝ) ≤ (X₀ : ℝ) := by exact_mod_cast hX₀_ge16
      have : 0 < Real.log 16 := by
        have := log_sixteen_gt_exp_one
        positivity
      have : Real.log 16 ≤ Real.log (X₀ : ℝ) := Real.log_le_log (by norm_num) (by linarith)
      linarith
    positivity
  let C := max C₀ C_large + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro J S hJ β X T₀ T hβ hβ1 hX hT0 hT0T hTX hH hQ hP hP_last
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have hT0_nonneg : 0 ≤ T₀ := by
    have : 0 < (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) := Real.rpow_pos_of_pos hlogX_pos _
    linarith
  have hT_nonneg : 0 ≤ T := by linarith
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have h_nonneg : 0 ≤ (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
    have : 0 ≤ T / (X : ℝ) + 1 := by positivity
    have : 0 ≤ (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by positivity
    positivity
  by_cases hX_le : X ≤ X₀
  · have h_bound := integral_Uset_norm_sq_Fu_le_bounded_X X₀ hX₀_ge16 S hJ β X T₀ T hX hX_le hT0_nonneg hT0T
    have hC₀_le_C : C₀ ≤ C := by
      dsimp [C]
      linarith [le_max_left C₀ C_large]
    calc ∫ t in S.Uset hJ β X T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2
      _ ≤ C₀ * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := h_bound
      _ = C₀ * ((T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) := by ring
      _ ≤ C * ((T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) :=
        mul_le_mul_of_nonneg_right hC₀_le_C h_nonneg
      _ = C * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by ring
  · have hX_gt : X₀ < X := not_le.mp hX_le
    have hX_ge_X₁ : X₁ ≤ X := hX₀_geX₁.trans hX_gt.le
    have h_large := hX₁ X hX_ge_X₁ J S hJ β T₀ T hβ hβ1 hX hT0 hT0T hTX hH hQ hP hP_last
    have hClarge_le_C : C_large ≤ C := by
      dsimp [C]
      linarith [le_max_right C₀ C_large]
    calc ∫ t in S.Uset hJ β X T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2
      _ ≤ C_large * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := h_large
      _ = C_large * ((T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) := by ring
      _ ≤ C * ((T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) :=
        mul_le_mul_of_nonneg_right hClarge_le_C h_nonneg
      _ = C * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by ring


lemma eventually_S_exponent_le :
    ∀ᶠ X : ℕ in atTop,
      3 * Real.sqrt (Real.log (X : ℝ)) + Real.log (Real.log (X : ℝ)) ≤
        (Real.log (X : ℝ)) ^ (1 - a_param / 2) := by
  have hr1 : (1 / 2 : ℝ) < 1 - a_param / 2 := by
    dsimp [a_param]; norm_num
  have hr2 : 0 < 1 - a_param / 2 := by
    dsimp [a_param]; norm_num
  have h_rpow := eventually_rpow_sub_rpow_le (1 / 2) (1 - a_param / 2) 3 1 hr1 zero_lt_one
  have h_loglog := eventually_log_log_le_rpow hr2 (1 / 2) (by norm_num)
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_rpow, h_loglog] with X hX hr hll
  have hsqrt : Real.sqrt (Real.log (X : ℝ)) = (Real.log (X : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.sqrt_eq_rpow (Real.log (X : ℝ))
  rw [hsqrt]
  linarith

lemma eventually_S_card_factor {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∀ᶠ X : ℕ in atTop, ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (T₀ T : ℝ) (𝒯 : Finset ℝ)
      (v : ℕ),
      3 / 4 ≤ β → β < 1 → 16 ≤ X → (Real.log X) ^ (1 / 15 : ℝ) ≤ T₀ → T₀ ≤ T → T ≤ X →
      (∀ j, 2 ≤ S.Hj hJ j) → (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) →
      (∀ j, S.Hj hJ j ≤ Real.sqrt (S.P j)) →
      (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) →
      WellSpaced 𝒯 → (↑𝒯 ⊆ S.Uset hJ β X T₀ T) →
      v ∈ Finset.Icc ⌊H_U X * Real.log (P_U X : ℝ)⌋₊ ⌈H_U X * Real.log (Q_U X : ℝ)⌉₊ →
      let 𝒯_S : Finset ℝ := 𝒯.filter (fun (t : ℝ) => ‖Qpoly β X (P_U X) (Q_U X) (H_U X) v ((1 : ℂ) + t * Complex.I)‖ ≤ eps_param X)
      (𝒯_S.card : ℝ) * Real.sqrt T * Real.exp ((v : ℝ) / H_U X) / (X : ℝ) ≤ 1 := by
  obtain ⟨C_c, hCc_pos, hcard⟩ := card_wellSpaced_subset_Uset_small_le hη0 hη
  have hS_core := eventually_S_bound_core C_c hCc_pos hη0
  have hS_exp := eventually_S_exponent_le
  have h_sides := eventually_all_side_conditions
  filter_upwards [hS_core, hS_exp, h_sides] with X hS_core_X hS_exp_X h_sides_X
  intro J S hJ β T₀ T 𝒯 v hβ hβ1 hX hT0 hT0T hTX hH hQ hP hP_last hws h𝒯_sub hv 𝒯_S
  have hpos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hT0_ge1 : 1 ≤ T₀ := by
    have h3 := h_sides_X.2.2.2.2.2.2.2.2.2.2.2.1
    linarith
  have hT_pos : 0 < T := by linarith
  have h_TS_le := hcard J S hJ β X T₀ T 𝒯 (P_U X) (Q_U X) (H_U X) v (eps_param X)
    hX hT0_ge1 hT0T hTX hws h𝒯_sub hH hQ hP_last
  change (𝒯_S.card : ℝ) ≤ _ at h_TS_le
  set j : Fin J := ⟨J - 1, by omega⟩
  have hP_le_Q : (S.P j : ℝ) ≤ (S.Q j : ℝ) := by exact_mod_cast S.P_le_Q j
  have hQ_le : (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) := hQ j
  have h_sqrt_log_nonneg : 0 ≤ Real.sqrt (Real.log (X : ℝ)) := Real.sqrt_nonneg _
  have h_exp_ge1 : 1 ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) := Real.one_le_exp h_sqrt_log_nonneg
  have hH_le : S.Hj hJ j ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) := by
    have h1 : S.Hj hJ j ≤ Real.sqrt (S.P j) := hP j
    have h2 : Real.sqrt (S.P j) ≤ Real.sqrt (S.Q j) := Real.sqrt_le_sqrt hP_le_Q
    have h3 : Real.sqrt (S.Q j) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      calc (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) := hQ_le
        _ ≤ (Real.exp (Real.sqrt (Real.log (X : ℝ)))) ^ 2 := by
          nlinarith
    exact h1.trans (h2.trans h3)
  have h_logQ_le : Real.log (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) := by
    have hQ_pos : 0 < (S.Q j : ℝ) := by
      have : 2 ≤ S.Q j := (S.two_le_P j).trans (S.P_le_Q j)
      exact Nat.cast_pos.mpr (by omega)
    have hlog : Real.log (S.Q j : ℝ) ≤ Real.sqrt (Real.log (X : ℝ)) := by
      rw [← Real.log_exp (Real.sqrt (Real.log (X : ℝ)))]
      exact Real.log_le_log hQ_pos hQ_le
    have h_le_exp : Real.sqrt (Real.log (X : ℝ)) ≤ Real.exp (Real.sqrt (Real.log (X : ℝ))) := by
      have := Real.add_one_le_exp (Real.sqrt (Real.log (X : ℝ)))
      linarith
    exact hlog.trans h_le_exp
  have h_logQ_nonneg : 0 ≤ Real.log (S.Q j : ℝ) := by
    have h1 : 1 ≤ S.Q j := by
      have h2 : 2 ≤ S.Q j := (S.two_le_P j).trans (S.P_le_Q j)
      omega
    exact Real.log_nonneg (by exact_mod_cast h1)
  have h_bracket_le : S.Hj hJ j * Real.log (S.Q j : ℝ) + 2 ≤ 3 * Real.exp (2 * Real.sqrt (Real.log (X : ℝ))) := by
    have h_mul : S.Hj hJ j * Real.log (S.Q j : ℝ) ≤
        Real.exp (Real.sqrt (Real.log (X : ℝ))) * Real.exp (Real.sqrt (Real.log (X : ℝ))) :=
      mul_le_mul hH_le h_logQ_le h_logQ_nonneg (by positivity)
    rw [← Real.exp_add] at h_mul
    have : Real.sqrt (Real.log (X : ℝ)) + Real.sqrt (Real.log (X : ℝ)) = 2 * Real.sqrt (Real.log (X : ℝ)) := by ring
    rw [this] at h_mul
    have h_two_le_exp : (2 : ℝ) ≤ 2 * Real.exp (2 * Real.sqrt (Real.log (X : ℝ))) := by
      have : 1 ≤ Real.exp (2 * Real.sqrt (Real.log (X : ℝ))) := Real.one_le_exp (by positivity)
      linarith
    linarith
  have h_part_le : (S.Hj hJ j * Real.log (S.Q j : ℝ) + 2) * Real.exp (Real.sqrt (Real.log (X : ℝ))) * Real.log (X : ℝ) ≤
      3 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) := by
    have h1 : (S.Hj hJ j * Real.log (S.Q j : ℝ) + 2) * Real.exp (Real.sqrt (Real.log (X : ℝ))) ≤
        3 * Real.exp (3 * Real.sqrt (Real.log (X : ℝ))) := by
      calc (S.Hj hJ j * Real.log (S.Q j : ℝ) + 2) * Real.exp (Real.sqrt (Real.log (X : ℝ)))
        _ ≤ (3 * Real.exp (2 * Real.sqrt (Real.log (X : ℝ)))) * Real.exp (Real.sqrt (Real.log (X : ℝ))) :=
          mul_le_mul_of_nonneg_right h_bracket_le (Real.exp_pos _).le
        _ = 3 * (Real.exp (2 * Real.sqrt (Real.log (X : ℝ))) * Real.exp (Real.sqrt (Real.log (X : ℝ)))) := by ring
        _ = 3 * Real.exp (3 * Real.sqrt (Real.log (X : ℝ))) := by
          rw [← Real.exp_add]; congr 2; ring
    have h2 : (S.Hj hJ j * Real.log (S.Q j : ℝ) + 2) * Real.exp (Real.sqrt (Real.log (X : ℝ))) * Real.log (X : ℝ) ≤
        3 * Real.exp (3 * Real.sqrt (Real.log (X : ℝ)) + Real.log (Real.log (X : ℝ))) := by
      calc (S.Hj hJ j * Real.log (S.Q j : ℝ) + 2) * Real.exp (Real.sqrt (Real.log (X : ℝ))) * Real.log (X : ℝ)
        _ ≤ (3 * Real.exp (3 * Real.sqrt (Real.log (X : ℝ)))) * Real.log (X : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hpos.le
        _ = 3 * (Real.exp (3 * Real.sqrt (Real.log (X : ℝ))) * Real.exp (Real.log (Real.log (X : ℝ)))) := by
          rw [Real.exp_log hpos]
          ring
        _ = 3 * Real.exp (3 * Real.sqrt (Real.log (X : ℝ)) + Real.log (Real.log (X : ℝ))) := by
          rw [← Real.exp_add]
    have h3 : 3 * Real.exp (3 * Real.sqrt (Real.log (X : ℝ)) + Real.log (Real.log (X : ℝ))) ≤
        3 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hS_exp_X) (by norm_num)
    exact h2.trans h3
  have h_card_bound : (𝒯_S.card : ℝ) ≤
      C_c * (3 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))) * T ^ (1 / 2 - η) := by
    calc (𝒯_S.card : ℝ)
      _ ≤ C_c * (S.Hj hJ j * Real.log (S.Q j : ℝ) + 2) * T ^ (1 / 2 - η) * Real.exp (Real.sqrt (Real.log (X : ℝ))) * Real.log (X : ℝ) := h_TS_le
      _ = C_c * ((S.Hj hJ j * Real.log (S.Q j : ℝ) + 2) * Real.exp (Real.sqrt (Real.log (X : ℝ))) * Real.log (X : ℝ)) * T ^ (1 / 2 - η) := by ring
      _ ≤ C_c * (3 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))) * T ^ (1 / 2 - η) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left h_part_le hCc_pos.le
  have h_sqrt_T : Real.sqrt T = T ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow T
  have h_T_pow : T ^ (1 / 2 - η) * Real.sqrt T = T ^ (1 - η) := by
    rw [h_sqrt_T, ← Real.rpow_add hT_pos]
    congr 1
    ring
  have h1_sub_η : 0 ≤ 1 - η := by linarith
  have h_T_le_X : T ^ (1 - η) ≤ (X : ℝ) ^ (1 - η) :=
    Real.rpow_le_rpow (by linarith) hTX h1_sub_η
  have h_X_div : (X : ℝ) ^ (1 - η) / (X : ℝ) = Real.exp (-η * Real.log (X : ℝ)) := by
    have h_sub : (X : ℝ) ^ (1 - η) / (X : ℝ) = (X : ℝ) ^ (-η) := by
      have h1 : (X : ℝ) = (X : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      nth_rw 2 [h1]
      rw [← Real.rpow_sub hX_pos]
      congr 1
      ring
    rw [h_sub, Real.rpow_def_of_pos hX_pos, mul_comm]
  have h_T_div_X : T ^ (1 / 2 - η) * Real.sqrt T / (X : ℝ) ≤ Real.exp (-η * Real.log (X : ℝ)) := by
    rw [h_T_pow]
    have : T ^ (1 - η) / (X : ℝ) ≤ (X : ℝ) ^ (1 - η) / (X : ℝ) :=
      div_le_div_of_nonneg_right h_T_le_X hX_pos.le
    rwa [h_X_div] at this
  have hv_le : v ≤ ⌈H_U X * Real.log (Q_U X : ℝ)⌉₊ := (Finset.mem_Icc.mp hv).2
  have h_exp_v : Real.exp ((v : ℝ) / H_U X) ≤ Real.exp 1 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) := by
    have hH1 : 1 ≤ H_U X := by
      have := h_sides_X.2.2.2.2.2.1
      linarith
    have hQ_pos : 0 < (Q_U X : ℝ) := by
      have : 2 ≤ Q_U X := by
        have := h_sides_X.2.1
        have := h_sides_X.2.2.1
        omega
      exact Nat.cast_pos.mpr (by omega)
    have h_ev := exp_v_div_H_le_exp_mul_Q_U hH1 hv_le hQ_pos
    have hQ_floor : (Q_U X : ℝ) ≤ Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) :=
      Nat.floor_le (Real.exp_pos _).le
    have h_mul := mul_le_mul_of_nonneg_left hQ_floor (Real.exp_pos 1).le
    exact h_ev.trans h_mul
  calc (𝒯_S.card : ℝ) * Real.sqrt T * Real.exp ((v : ℝ) / H_U X) / (X : ℝ)
    _ = (𝒯_S.card : ℝ) * (Real.sqrt T / (X : ℝ)) * Real.exp ((v : ℝ) / H_U X) := by ring
    _ ≤ (C_c * (3 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))) * T ^ (1 / 2 - η)) *
        (Real.sqrt T / (X : ℝ)) * (Real.exp 1 * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right h_card_bound (by positivity)) h_exp_v (by positivity) (by positivity)
    _ = (3 * Real.exp 1 * C_c) * (T ^ (1 / 2 - η) * Real.sqrt T / (X : ℝ)) *
        (Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))) := by ring
    _ ≤ (3 * Real.exp 1 * C_c) * Real.exp (-η * Real.log (X : ℝ)) *
        (Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) * Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2))) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      refine mul_le_mul_of_nonneg_left h_T_div_X (by positivity)
    _ = (3 * Real.exp 1 * C_c) * (Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) *
        Real.exp ((Real.log (X : ℝ)) ^ (1 - a_param / 2)) * Real.exp (-η * Real.log (X : ℝ))) := by ring
    _ = (3 * Real.exp 1 * C_c) * Real.exp (2 * (Real.log (X : ℝ)) ^ (1 - a_param / 2) - η * Real.log (X : ℝ)) := by
      congr 1
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ 1 := hS_core_X

lemma eventually_L_decay_exponent (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop,
      Real.log 4 + 2 * Real.log (Real.log (X : ℝ)) ≤
        c * (2 ^ (-(3 / 4 : ℝ)) - 1 / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param) := by
  have hd : 0 < c * (2 ^ (-(3 / 4 : ℝ)) - 1 / 2) := by
    have h2 : (1 / 2 : ℝ) < 2 ^ (-(3 / 4 : ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← one_div]
      have hlt : (3 / 4 : ℝ) < 1 := by norm_num
      have hpow : (2 : ℝ) ^ (3 / 4 : ℝ) < 2 ^ (1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
      rw [Real.rpow_one] at hpow
      have hpos : 0 < (2 : ℝ) ^ (3 / 4 : ℝ) := by positivity
      exact one_div_lt_one_div_of_lt hpos hpow
    positivity
  have hr : 0 < 1 / 4 - a_param := by
    dsimp [a_param]; norm_num
  have h_const : ∀ᶠ X : ℕ in atTop, Real.log 4 ≤ (c * (2 ^ (-(3 / 4 : ℝ)) - 1 / 2) / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param) := by
    have h_rpow := tendsto_log_rpow_atTop hr
    have h_inf := Filter.Tendsto.const_mul_atTop (by linarith : 0 < c * (2 ^ (-(3 / 4 : ℝ)) - 1 / 2) / 2) h_rpow
    exact h_inf.eventually_ge_atTop (Real.log 4)
  have h_ll := eventually_log_log_le_rpow hr ((c * (2 ^ (-(3 / 4 : ℝ)) - 1 / 2) / 2) / 2) (by positivity)
  filter_upwards [h_const, h_ll] with X h1 h2
  linarith

lemma eventually_L_decay_factor_le (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ T : ℝ, 1 ≤ T → T ≤ (X : ℝ) →
      Real.exp (-c * Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ)) *
        (Real.log ((P_U X : ℝ) * T)) ^ 2 ≤
      Real.exp (-(c / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param)) := by
  have h_sides := eventually_all_side_conditions
  have h_exp := eventually_L_decay_exponent c hc
  filter_upwards [h_sides, h_exp] with X h_sides_X h_exp_X T hT1 hTX
  have hX : 16 ≤ X := h_sides_X.1
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hP_pos : 0 < (P_U X : ℝ) := by
    have : 2 ≤ P_U X := h_sides_X.2.1
    exact Nat.cast_pos.mpr (by omega)
  have hP_le_X : (P_U X : ℝ) ≤ (X : ℝ) := by
    have hPQ : P_U X ≤ Q_U X := h_sides_X.2.2.1
    have hQX : (Q_U X : ℝ) ≤ (X : ℝ) ^ (3 / 4 : ℝ) := h_sides_X.2.2.2.1
    have hX_ge1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
    have h34_le1 : (3 / 4 : ℝ) ≤ 1 := by norm_num
    have hQX_X : (Q_U X : ℝ) ≤ (X : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le hX_ge1 h34_le1
      rw [Real.rpow_one] at this
      exact hQX.trans this
    have : (P_U X : ℝ) ≤ (Q_U X : ℝ) := by exact_mod_cast hPQ
    exact this.trans hQX_X
  have hPT_le : (P_U X : ℝ) * T ≤ (X : ℝ) ^ 2 := by
    calc (P_U X : ℝ) * T ≤ (X : ℝ) * (X : ℝ) := mul_le_mul hP_le_X hTX (by linarith) hX_pos.le
      _ = (X : ℝ) ^ 2 := by ring
  have hPT_ge2 : (2 : ℝ) ≤ (P_U X : ℝ) * T := by
    have hP2 : (2 : ℝ) ≤ (P_U X : ℝ) := by exact_mod_cast h_sides_X.2.1
    calc (2 : ℝ) = 2 * 1 := by norm_num
      _ ≤ (P_U X : ℝ) * T := mul_le_mul hP2 hT1 zero_le_one (by positivity)
  have hPT_pos : 0 < (P_U X : ℝ) * T := by linarith
  have hlogPT_pos : 0 < Real.log ((P_U X : ℝ) * T) := by
    have : Real.log 2 ≤ Real.log ((P_U X : ℝ) * T) := Real.log_le_log (by norm_num) hPT_ge2
    have hlog2 := Real.log_two_gt_d9
    linarith
  have hlogPT_le : Real.log ((P_U X : ℝ) * T) ≤ 2 * Real.log (X : ℝ) := by
    have hlog_X2 : Real.log ((X : ℝ) ^ 2) = 2 * Real.log (X : ℝ) := by
      rw [← Real.rpow_two, Real.log_rpow hX_pos]
    rw [← hlog_X2]
    exact Real.log_le_log hPT_pos hPT_le
  have h34_pos : 0 < (3 / 4 : ℝ) := by norm_num
  have hlogPT_34_le : (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ) ≤ (2 * Real.log (X : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow hlogPT_pos.le hlogPT_le h34_pos.le
  have h_mul_rpow : (2 * Real.log (X : ℝ)) ^ (3 / 4 : ℝ) = (2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.mul_rpow (by norm_num) hpos.le
  rw [h_mul_rpow] at hlogPT_34_le
  have hlogP_ge : (Real.log (X : ℝ)) ^ (1 - a_param) ≤ Real.log (P_U X : ℝ) := log_P_U_ge hX
  have h_frac_ge : (Real.log (X : ℝ)) ^ (1 - a_param) / ((2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (3 / 4 : ℝ)) ≤
      Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ) := by
    have h1 := div_le_div_of_nonneg_left (show 0 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) by positivity)
      (by positivity) hlogPT_34_le
    have h2 := div_le_div_of_nonneg_right hlogP_ge (show 0 ≤ (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ) by positivity)
    exact h1.trans h2
  have h_div_split : (Real.log (X : ℝ)) ^ (1 - a_param) / ((2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (3 / 4 : ℝ)) =
      (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param) := by
    have h1 : (Real.log (X : ℝ)) ^ (1 - a_param) / (Real.log (X : ℝ)) ^ (3 / 4 : ℝ) =
        (Real.log (X : ℝ)) ^ (1 / 4 - a_param) := by
      rw [← Real.rpow_sub hpos]
      congr 1
      ring
    have h2 : 1 / (2 : ℝ) ^ (3 / 4 : ℝ) = (2 : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), one_div]
    calc (Real.log (X : ℝ)) ^ (1 - a_param) / ((2 : ℝ) ^ (3 / 4 : ℝ) * (Real.log (X : ℝ)) ^ (3 / 4 : ℝ))
      _ = (1 / (2 : ℝ) ^ (3 / 4 : ℝ)) * ((Real.log (X : ℝ)) ^ (1 - a_param) / (Real.log (X : ℝ)) ^ (3 / 4 : ℝ)) := by ring
      _ = (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param) := by rw [h2, h1]
  rw [h_div_split] at h_frac_ge
  have h_neg_mul : -c * (Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ)) ≤
      -c * ((2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param)) := by
    have : 0 ≤ c := hc.le
    nlinarith
  have h_rw_neg : -c * ((2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param)) =
      -c * (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param) := by ring
  rw [h_rw_neg] at h_neg_mul
  have h_sq_le : (Real.log ((P_U X : ℝ) * T)) ^ 2 ≤ 4 * (Real.log (X : ℝ)) ^ 2 := by
    have : 0 ≤ Real.log ((P_U X : ℝ) * T) := hlogPT_pos.le
    have h := pow_le_pow_left₀ this hlogPT_le 2
    have : (2 * Real.log (X : ℝ)) ^ 2 = 4 * (Real.log (X : ℝ)) ^ 2 := by ring
    rwa [this] at h
  have h_sq_exp : 4 * (Real.log (X : ℝ)) ^ 2 = Real.exp (Real.log 4 + 2 * Real.log (Real.log (X : ℝ))) := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    have hlog2 : Real.exp (2 * Real.log (Real.log (X : ℝ))) = (Real.log (X : ℝ)) ^ 2 := by
      rw [mul_comm, ← Real.rpow_natCast, ← Real.rpow_def_of_pos hpos]
      norm_num
    rw [hlog2]
  have h_sq_le_exp : (Real.log ((P_U X : ℝ) * T)) ^ 2 ≤ Real.exp (Real.log 4 + 2 * Real.log (Real.log (X : ℝ))) := by
    rw [← h_sq_exp]
    exact h_sq_le
  have h_comb : -c * (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param) +
      (Real.log 4 + 2 * Real.log (Real.log (X : ℝ))) ≤
      -(c / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param) := by
    have h_rearr : -c * (2 : ℝ) ^ (-(3 / 4 : ℝ)) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param) +
        c * (2 ^ (-(3 / 4 : ℝ)) - 1 / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param) =
        -(c / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param) := by ring
    linarith [h_exp_X]
  have h_exp_le : Real.exp (-c * (Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ))) *
      Real.exp (Real.log 4 + 2 * Real.log (Real.log (X : ℝ))) ≤
      Real.exp (-(c / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have h_mul_div : -c * Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ) =
      -c * (Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ)) := by ring
  rw [h_mul_div]
  calc Real.exp (-c * (Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ))) *
        (Real.log ((P_U X : ℝ) * T)) ^ 2
    _ ≤ Real.exp (-c * (Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ))) *
        Real.exp (Real.log 4 + 2 * Real.log (Real.log (X : ℝ))) :=
      mul_le_mul_of_nonneg_left h_sq_le_exp (Real.exp_pos _).le
    _ ≤ Real.exp (-(c / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param)) := h_exp_le

lemma exp_sub_one_ge_exp_half {y : ℝ} (hy : 3 ≤ y) :
    Real.exp (y / 2) ≤ Real.exp y - 1 := by
  have hy2 : (1.5 : ℝ) ≤ y / 2 := by linarith
  have he15 : (2.5 : ℝ) ≤ Real.exp (y / 2) := by
    have : y / 2 + 1 ≤ Real.exp (y / 2) := Real.add_one_le_exp (y / 2)
    linarith
  have he_sub : (1 : ℝ) ≤ Real.exp (y / 2) - 1 := by linarith
  have h_prod : (1 : ℝ) ≤ Real.exp (y / 2) * (Real.exp (y / 2) - 1) := by
    nlinarith
  have h_exp_sq : Real.exp (y / 2) * Real.exp (y / 2) = Real.exp y := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h_expand : Real.exp (y / 2) * (Real.exp (y / 2) - 1) = Real.exp y - Real.exp (y / 2) := by
    calc Real.exp (y / 2) * (Real.exp (y / 2) - 1)
      _ = Real.exp (y / 2) * Real.exp (y / 2) - Real.exp (y / 2) := by ring
      _ = Real.exp y - Real.exp (y / 2) := by rw [h_exp_sq]
  rw [h_expand] at h_prod
  linarith

lemma P0_properties {X : ℕ} (hX : 16 ≤ X) {v : ℕ}
    (hv : ⌊H_U X * Real.log (P_U X : ℝ)⌋₊ ≤ v)
    (h_HU_ge1 : 1 ≤ H_U X)
    (hlogP_ge : 4 ≤ (Real.log (X : ℝ)) ^ (1 - a_param)) :
    let P₀ := ⌈Real.exp ((v : ℝ) / H_U X)⌉₊ - 1
    5 ≤ P₀ ∧ (P₀ : ℝ) < Real.exp ((v : ℝ) / H_U X) ∧ Real.exp ((v : ℝ) / H_U X) ≤ (P₀ : ℝ) + 1 := by
  intro P₀
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have hH_pos : 0 < H_U X := by linarith
  have h_logPU : (Real.log (X : ℝ)) ^ (1 - a_param) ≤ Real.log (P_U X : ℝ) := log_P_U_ge hX
  have h4_logP : 4 ≤ Real.log (P_U X : ℝ) := hlogP_ge.trans h_logPU
  have hv_r : (v : ℝ) ≥ H_U X * Real.log (P_U X : ℝ) - 1 := by
    have : (⌊H_U X * Real.log (P_U X : ℝ)⌋₊ : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
    have h_floor : H_U X * Real.log (P_U X : ℝ) - 1 ≤ (⌊H_U X * Real.log (P_U X : ℝ)⌋₊ : ℝ) :=
      (Nat.sub_one_lt_floor _).le
    exact h_floor.trans this
  have h_div_ge : (v : ℝ) / H_U X ≥ Real.log (P_U X : ℝ) - 1 / H_U X := by
    have : (H_U X * Real.log (P_U X : ℝ) - 1) / H_U X ≤ (v : ℝ) / H_U X :=
      div_le_div_of_nonneg_right hv_r hH_pos.le
    have h_rw : (H_U X * Real.log (P_U X : ℝ) - 1) / H_U X = Real.log (P_U X : ℝ) - 1 / H_U X := by
      rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hH_pos)]
    rwa [h_rw] at this
  have h_inv_le : 1 / H_U X ≤ 1 := by
    calc 1 / H_U X ≤ 1 / 1 := one_div_le_one_div_of_le zero_lt_one h_HU_ge1
      _ = 1 := by norm_num
  have h_vH_ge3 : 3 ≤ (v : ℝ) / H_U X := by linarith
  have h_exp_ge : Real.exp 2 ≤ Real.exp ((v : ℝ) / H_U X) := Real.exp_le_exp.mpr (by linarith)
  have he2 : 7 ≤ Real.exp 2 := by
    have he1 : (2.7 : ℝ) < Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have : (7 : ℝ) ≤ (2.7 : ℝ) ^ 2 := by norm_num
    have : (2.7 : ℝ) ^ 2 < (Real.exp 1) ^ 2 := pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
    rw [← Real.exp_nat_mul] at this
    push_cast at this
    linarith
  have h_exp_ge7 : 7 ≤ Real.exp ((v : ℝ) / H_U X) := he2.trans h_exp_ge
  have h_ceil_ge : 7 ≤ ⌈Real.exp ((v : ℝ) / H_U X)⌉₊ := by
    exact_mod_cast (h_exp_ge7.trans (Nat.le_ceil _))
  have hP0_ge : 5 ≤ P₀ := by
    dsimp [P₀]
    omega
  have h_ceil_pos : 1 ≤ ⌈Real.exp ((v : ℝ) / H_U X)⌉₊ := by omega
  have hP0_cast : (P₀ : ℝ) = (⌈Real.exp ((v : ℝ) / H_U X)⌉₊ : ℝ) - 1 := by
    dsimp [P₀]
    rw [Nat.cast_sub h_ceil_pos]
    simp
  have h_lt : (P₀ : ℝ) < Real.exp ((v : ℝ) / H_U X) := by
    rw [hP0_cast]
    have h_ceil_lt := Nat.ceil_lt_add_one (Real.exp_pos ((v : ℝ) / H_U X)).le
    linarith
  have h_le : Real.exp ((v : ℝ) / H_U X) ≤ (P₀ : ℝ) + 1 := by
    rw [hP0_cast]
    have := Nat.le_ceil (Real.exp ((v : ℝ) / H_U X))
    linarith
  exact ⟨hP0_ge, h_lt, h_le⟩

lemma log_P0_ge_third {X : ℕ} (hX : 16 ≤ X) {v : ℕ}
    (hv : ⌊H_U X * Real.log (P_U X : ℝ)⌋₊ ≤ v)
    (h_HU_ge1 : 1 ≤ H_U X)
    (hlogP_ge : 4 ≤ (Real.log (X : ℝ)) ^ (1 - a_param)) :
    let P₀ := ⌈Real.exp ((v : ℝ) / H_U X)⌉₊ - 1
    (1 / 3 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param) ≤ Real.log (P₀ : ℝ) := by
  intro P₀
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have hH_pos : 0 < H_U X := by linarith
  have h_logPU : (Real.log (X : ℝ)) ^ (1 - a_param) ≤ Real.log (P_U X : ℝ) := log_P_U_ge hX
  have h4_logP : 4 ≤ Real.log (P_U X : ℝ) := hlogP_ge.trans h_logPU
  have hv_r : (v : ℝ) ≥ H_U X * Real.log (P_U X : ℝ) - 1 := by
    have : (⌊H_U X * Real.log (P_U X : ℝ)⌋₊ : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv
    have h_floor : H_U X * Real.log (P_U X : ℝ) - 1 ≤ (⌊H_U X * Real.log (P_U X : ℝ)⌋₊ : ℝ) :=
      (Nat.sub_one_lt_floor _).le
    exact h_floor.trans this
  have h_div_ge : (v : ℝ) / H_U X ≥ Real.log (P_U X : ℝ) - 1 / H_U X := by
    have : (H_U X * Real.log (P_U X : ℝ) - 1) / H_U X ≤ (v : ℝ) / H_U X :=
      div_le_div_of_nonneg_right hv_r hH_pos.le
    have h_rw : (H_U X * Real.log (P_U X : ℝ) - 1) / H_U X = Real.log (P_U X : ℝ) - 1 / H_U X := by
      rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt hH_pos)]
    rwa [h_rw] at this
  have h_inv_le : 1 / H_U X ≤ 1 := by
    calc 1 / H_U X ≤ 1 / 1 := one_div_le_one_div_of_le zero_lt_one h_HU_ge1
      _ = 1 := by norm_num
  have h_vH_ge3 : 3 ≤ (v : ℝ) / H_U X := by linarith
  have h_third_ge : (1 / 3 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param) ≤ (1 / 2 : ℝ) * ((v : ℝ) / H_U X) := by
    calc (1 / 3 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param)
      _ ≤ (1 / 3 : ℝ) * Real.log (P_U X : ℝ) := mul_le_mul_of_nonneg_left h_logPU (by norm_num)
      _ ≤ (1 / 2 : ℝ) * (Real.log (P_U X : ℝ) - 1) := by linarith
      _ ≤ (1 / 2 : ℝ) * ((v : ℝ) / H_U X) := by linarith
  have h_exp_half_le : Real.exp (((v : ℝ) / H_U X) / 2) ≤ Real.exp ((v : ℝ) / H_U X) - 1 :=
    exp_sub_one_ge_exp_half h_vH_ge3
  have h_sub_le_P0 : Real.exp ((v : ℝ) / H_U X) - 1 ≤ (P₀ : ℝ) := by
    dsimp [P₀]
    have h_ceil := Nat.le_ceil (Real.exp ((v : ℝ) / H_U X))
    have h_ceil_pos : 1 ≤ ⌈Real.exp ((v : ℝ) / H_U X)⌉₊ := by
      have : 7 ≤ Real.exp 2 := by
        have he1 : (2.7 : ℝ) < Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
        have : (7 : ℝ) ≤ (2.7 : ℝ) ^ 2 := by norm_num
        have : (2.7 : ℝ) ^ 2 < (Real.exp 1) ^ 2 := pow_lt_pow_left₀ he1 (by norm_num) (by norm_num)
        rw [← Real.exp_nat_mul] at this
        push_cast at this
        linarith
      have : 7 ≤ Real.exp ((v : ℝ) / H_U X) := by
        have : Real.exp 2 ≤ Real.exp ((v : ℝ) / H_U X) := Real.exp_le_exp.mpr (by linarith)
        linarith
      have : (7 : ℝ) ≤ (⌈Real.exp ((v : ℝ) / H_U X)⌉₊ : ℝ) := this.trans (Nat.le_ceil _)
      have : 7 ≤ ⌈Real.exp ((v : ℝ) / H_U X)⌉₊ := by exact_mod_cast this
      omega
    rw [Nat.cast_sub h_ceil_pos]
    simp
    linarith
  have h_exp_half_le_P0 : Real.exp (((v : ℝ) / H_U X) / 2) ≤ (P₀ : ℝ) :=
    h_exp_half_le.trans h_sub_le_P0
  have h_P0_pos : 0 < (P₀ : ℝ) := by
    have : 0 < Real.exp (((v : ℝ) / H_U X) / 2) := Real.exp_pos _
    exact this.trans_le h_exp_half_le_P0
  have h_log_le := Real.log_le_log (Real.exp_pos _) h_exp_half_le_P0
  rw [Real.log_exp] at h_log_le
  have : (1 / 2 : ℝ) * ((v : ℝ) / H_U X) = ((v : ℝ) / H_U X) / 2 := by ring
  rw [← this] at h_log_le
  exact h_third_ge.trans h_log_le

lemma eventually_L_exponent_comparison :
    ∀ᶠ X : ℕ in atTop,
      850 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) ≤
        1000 * (Real.log (X : ℝ)) ^ (2 * a_param) := by
  have ha_pos : 0 < a_param := a_param_pos
  have h_const_pos : 0 < (1000 / 850 : ℝ) := by norm_num
  have h_ll := eventually_log_log_le_rpow ha_pos (1000 / 850) h_const_pos
  have h16 : ∀ᶠ X : ℕ in atTop, 16 ≤ X := eventually_ge_atTop 16
  filter_upwards [h16, h_ll] with X hX hll
  have hpos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have h_mul : 850 * Real.log (Real.log (X : ℝ)) ≤ 1000 * (Real.log (X : ℝ)) ^ a_param := by
    calc 850 * Real.log (Real.log (X : ℝ))
      _ ≤ 850 * ((1000 / 850 : ℝ) * (Real.log (X : ℝ)) ^ a_param) :=
        mul_le_mul_of_nonneg_left hll (by norm_num)
      _ = 1000 * (Real.log (X : ℝ)) ^ a_param := by ring
  have h_rpow_nonneg : 0 ≤ (Real.log (X : ℝ)) ^ a_param := by positivity
  calc 850 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))
    _ = (Real.log (X : ℝ)) ^ a_param * (850 * Real.log (Real.log (X : ℝ))) := by ring
    _ ≤ (Real.log (X : ℝ)) ^ a_param * (1000 * (Real.log (X : ℝ)) ^ a_param) :=
      mul_le_mul_of_nonneg_left h_mul h_rpow_nonneg
    _ = 1000 * ((Real.log (X : ℝ)) ^ a_param * (Real.log (X : ℝ)) ^ a_param) := by ring
    _ = 1000 * (Real.log (X : ℝ)) ^ (2 * a_param) := by
      rw [← Real.rpow_add hpos]
      congr 2
      ring


lemma five_pow_mul_factorial_le (k : ℕ) :
    (5 : ℝ) ^ k * (k.factorial : ℝ) ≤ Real.exp ((k : ℝ) * Real.log (5 * (k : ℝ) + 1)) := by
  by_cases hk : k = 0
  · subst hk
    simp
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    have hk_rpos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk_pos
    have hfact : (k.factorial : ℝ) ≤ (k : ℝ) ^ k := by
      exact_mod_cast Nat.factorial_le_pow k
    have h5k : (5 : ℝ) ^ k * (k : ℝ) ^ k = (5 * (k : ℝ)) ^ k := by
      rw [← mul_pow]
    have h_prod : (5 : ℝ) ^ k * (k.factorial : ℝ) ≤ (5 * (k : ℝ)) ^ k := by
      rw [← h5k]
      exact mul_le_mul_of_nonneg_left hfact (by positivity)
    have h_base : 5 * (k : ℝ) ≤ 5 * (k : ℝ) + 1 := by linarith
    have h_pow_le : (5 * (k : ℝ)) ^ k ≤ (5 * (k : ℝ) + 1) ^ k := by
      refine pow_le_pow_left₀ (by positivity) h_base k
    have h_pos_base : 0 < 5 * (k : ℝ) + 1 := by positivity
    have h_exp_rw : (5 * (k : ℝ) + 1) ^ k = Real.exp ((k : ℝ) * Real.log (5 * (k : ℝ) + 1)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos h_pos_base, mul_comm]
    rw [h_exp_rw] at h_pow_le
    exact h_prod.trans h_pow_le

lemma eventually_L_helpers :
    ∀ᶠ X : ℕ in atTop,
      4 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) ∧
      1 ≤ (Real.log (X : ℝ)) ^ a_param ∧
      Real.log 21 + a_param * Real.log (Real.log (X : ℝ)) ≤ 4 * Real.log (Real.log (X : ℝ)) := by
  have h1 : ∀ᶠ X : ℕ in atTop, 4 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) :=
    (tendsto_log_rpow_atTop (by dsimp [a_param]; norm_num)).eventually_ge_atTop 4
  have h2 : ∀ᶠ X : ℕ in atTop, 1 ≤ (Real.log (X : ℝ)) ^ a_param :=
    (tendsto_log_rpow_atTop a_param_pos).eventually_ge_atTop 1
  have h3 : ∀ᶠ X : ℕ in atTop, Real.log 21 + a_param * Real.log (Real.log (X : ℝ)) ≤ 4 * Real.log (Real.log (X : ℝ)) := by
    have h_coeff : 0 < 4 - a_param := by dsimp [a_param]; norm_num
    have h_tendsto : Tendsto (fun X : ℕ => Real.log (Real.log (X : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_log_natCast_atTop
    have h_ll := h_tendsto.eventually_ge_atTop (Real.log 21 / (4 - a_param))
    filter_upwards [h_ll] with X hX
    rw [div_le_iff₀ h_coeff] at hX
    linarith [hX]
  filter_upwards [h1, h2, h3] with X h1X h2X h3X
  exact ⟨h1X, h2X, h3X⟩

lemma log_add_two_le_two_log {y : ℝ} (hy : 2 ≤ y) : Real.log (y + 2) ≤ 2 * Real.log y := by
  have hy_pos : 0 < y := by linarith
  have h_quad : y + 2 ≤ y ^ 2 := by
    have : 0 ≤ (y - 2) * (y + 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have h_pos2 : 0 < y + 2 := by linarith
  have h_log_le := Real.log_le_log h_pos2 h_quad
  have h_log_sq : Real.log (y ^ 2) = 2 * Real.log y := by
    rw [← Real.rpow_two, Real.log_rpow hy_pos]
  rwa [h_log_sq] at h_log_le

lemma inv_eps_param_eq {X : ℕ} (hX : 16 ≤ X) : 1 / eps_param X = (Real.log (X : ℝ)) ^ (100 : ℝ) := by
  dsimp [eps_param]
  rw [Real.rpow_neg (by linarith [log_X_gt_one hX] : 0 ≤ Real.log (X : ℝ)), one_div, inv_inv]

lemma log_inv_eps_param {X : ℕ} (hX : 16 ≤ X) :
    Real.log (1 / eps_param X) = 100 * Real.log (Real.log (X : ℝ)) := by
  rw [inv_eps_param_eq hX]
  have hpos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  exact Real.log_rpow hpos 100

lemma inv_eps_param_sq_eq {X : ℕ} (hX : 16 ≤ X) :
    (1 / eps_param X) ^ 2 = Real.exp (200 * Real.log (Real.log (X : ℝ))) := by
  rw [inv_eps_param_eq hX]
  have hpos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have h_sq : ((Real.log (X : ℝ)) ^ (100 : ℝ)) ^ 2 = (Real.log (X : ℝ)) ^ (200 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    norm_num
  rw [h_sq, Real.rpow_def_of_pos hpos]
  congr 1
  ring

lemma eventually_L_card_factor (c : ℝ) (hc : 0 < c) :
    ∀ᶠ X : ℕ in atTop, ∀ (β : ℝ) (T : ℝ) (𝒯 : Finset ℝ) (v : ℕ),
      1 ≤ T → T ≤ (X : ℝ) → WellSpaced 𝒯 → (∀ t ∈ 𝒯, |t| ≤ T) →
      v ∈ Finset.Icc ⌊H_U X * Real.log (P_U X : ℝ)⌋₊ ⌈H_U X * Real.log (Q_U X : ℝ)⌉₊ →
      let 𝒯_L : Finset ℝ := 𝒯.filter (fun (t : ℝ) => ¬ (‖Qpoly β X (P_U X) (Q_U X) (H_U X) v ((1 : ℂ) + t * Complex.I)‖ ≤ eps_param X))
      (𝒯_L.card : ℝ) * Real.exp (-c * Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ)) *
        (Real.log ((P_U X : ℝ) * T)) ^ 2 ≤ 1 := by
  obtain ⟨C₈, hC₈_pos, hcard_TL⟩ := card_TL_le
  have h_core := eventually_L_bound_core C₈ hC₈_pos c hc
  have h_decay := eventually_L_decay_factor_le c hc
  have h_comp := eventually_L_exponent_comparison
  have h_help := eventually_L_helpers
  have h_sides := eventually_all_side_conditions
  filter_upwards [h_core, h_decay, h_comp, h_help, h_sides] with X h_core_X h_decay_X h_comp_X h_help_X h_sides_X
  intro β T 𝒯 v hT1 hTX hws ht_le hv 𝒯_L
  have hX : 16 ≤ X := h_sides_X.1
  have hlogX : 1 < Real.log (X : ℝ) := log_X_gt_one hX
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  have hll_pos : 0 < Real.log (Real.log (X : ℝ)) := Real.log_pos hlogX
  have hH_ge2 : 2 ≤ H_U X := by
    have := h_sides_X.2.2.2.2.1
    linarith
  have hH_ge1 : 1 ≤ H_U X := by linarith
  have hε_pos : 0 < eps_param X := Real.rpow_pos_of_pos hpos (-100)
  have hε_le1 : eps_param X ≤ 1 := by
    dsimp [eps_param]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hv_mem := Finset.mem_Icc.mp hv
  have hv_floor : ⌊H_U X * Real.log (P_U X : ℝ)⌋₊ ≤ v := hv_mem.1
  have h_logP_ge : 4 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := h_help_X.1
  set P₀ := ⌈Real.exp ((v : ℝ) / H_U X)⌉₊ - 1
  have hP0_props := P0_properties hX hv_floor hH_ge1 h_logP_ge
  have hP0_5 : 5 ≤ P₀ := hP0_props.1
  have hP0_lt : (P₀ : ℝ) < Real.exp ((v : ℝ) / H_U X) := hP0_props.2.1
  have hP0_ge : Real.exp ((v : ℝ) / H_U X) ≤ (P₀ : ℝ) + 1 := hP0_props.2.2
  have hP0_pos : 0 < (P₀ : ℝ) := by
    have : 0 < (5 : ℝ) := by norm_num
    exact this.trans_le (by exact_mod_cast hP0_5)
  have hlogP0_pos : 0 < Real.log (P₀ : ℝ) := by
    have : (1 : ℝ) < 5 := by norm_num
    have : (1 : ℝ) < (P₀ : ℝ) := this.trans_le (by exact_mod_cast hP0_5)
    exact Real.log_pos this
  have h_TL_bound := hcard_TL β X (P_U X) (Q_U X) (H_U X) v T (eps_param X) 𝒯
    hH_ge2 hT1 hε_pos hε_le1 hws ht_le P₀ hP0_5 hP0_lt hP0_ge
  change (𝒯_L.card : ℝ) ≤ _ at h_TL_bound
  have h_logP0_third := log_P0_ge_third hX hv_floor hH_ge1 h_logP_ge
  have h_logT_nonneg : 0 ≤ Real.log T := Real.log_nonneg hT1
  have h_logT_le_logX : Real.log T ≤ Real.log (X : ℝ) := by
    have hT_pos : 0 < T := by linarith
    exact Real.log_le_log hT_pos hTX
  have h_y_le : Real.log T / Real.log (P₀ : ℝ) ≤ 3 * (Real.log (X : ℝ)) ^ a_param := by
    have h1 : Real.log T / Real.log (P₀ : ℝ) ≤ Real.log (X : ℝ) / Real.log (P₀ : ℝ) :=
      div_le_div_of_nonneg_right h_logT_le_logX hlogP0_pos.le
    have h2 : Real.log (X : ℝ) / Real.log (P₀ : ℝ) ≤ Real.log (X : ℝ) / ((1 / 3 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param)) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) h_logP0_third
    have h3 : Real.log (X : ℝ) / ((1 / 3 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param)) =
        3 * (Real.log (X : ℝ)) ^ a_param := by
      have hr : Real.log (X : ℝ) / (Real.log (X : ℝ)) ^ (1 - a_param) = (Real.log (X : ℝ)) ^ a_param := by
        have h_pow1 : Real.log (X : ℝ) = (Real.log (X : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
        nth_rw 1 [h_pow1]
        rw [← Real.rpow_sub hpos]
        congr 1
        ring
      calc Real.log (X : ℝ) / ((1 / 3 : ℝ) * (Real.log (X : ℝ)) ^ (1 - a_param))
        _ = (1 / (1 / 3 : ℝ)) * (Real.log (X : ℝ) / (Real.log (X : ℝ)) ^ (1 - a_param)) := by ring
        _ = 3 * (Real.log (X : ℝ)) ^ a_param := by
          rw [hr]
          norm_num
    exact (h1.trans h2).trans_eq h3
  have h_y_nonneg : 0 ≤ Real.log T / Real.log (P₀ : ℝ) := div_nonneg h_logT_nonneg hlogP0_pos.le
  have h_fact1 : T ^ (2 * Real.log (1 / eps_param X) / Real.log (P₀ : ℝ)) ≤
      Real.exp (600 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))) := by
    have hT_pos : 0 < T := by linarith
    rw [Real.rpow_def_of_pos hT_pos, log_inv_eps_param hX]
    have h_prod : Real.log T * (2 * (100 * Real.log (Real.log (X : ℝ))) / Real.log (P₀ : ℝ)) =
        200 * Real.log (Real.log (X : ℝ)) * (Real.log T / Real.log (P₀ : ℝ)) := by ring
    rw [h_prod]
    have h_le : 200 * Real.log (Real.log (X : ℝ)) * (Real.log T / Real.log (P₀ : ℝ)) ≤
        600 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by
      calc 200 * Real.log (Real.log (X : ℝ)) * (Real.log T / Real.log (P₀ : ℝ))
        _ ≤ 200 * Real.log (Real.log (X : ℝ)) * (3 * (Real.log (X : ℝ)) ^ a_param) :=
          mul_le_mul_of_nonneg_left h_y_le (by positivity)
        _ = 600 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by ring
    exact Real.exp_le_exp.mpr h_le
  have h_fact2 : (1 / eps_param X) ^ 2 ≤
      Real.exp (200 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))) := by
    rw [inv_eps_param_sq_eq hX]
    have h_le : 200 * Real.log (Real.log (X : ℝ)) ≤
        200 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by
      have h1 : 1 ≤ (Real.log (X : ℝ)) ^ a_param := h_help_X.2.1
      calc 200 * Real.log (Real.log (X : ℝ))
        _ = 200 * 1 * Real.log (Real.log (X : ℝ)) := by ring
        _ ≤ 200 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hll_pos.le
          linarith
    exact Real.exp_le_exp.mpr h_le
  have h_fact3 : Real.exp (2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2)) ≤
      Real.exp (12 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))) := by
    have hlogX_ge2 : 2 ≤ Real.log (X : ℝ) := by
      have : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
      have h16 : (2 : ℝ) ≤ Real.log 16 := by
        have := log_sixteen_gt_exp_one
        have := Real.exp_one_gt_d9
        linarith
      have : Real.log 16 ≤ Real.log (X : ℝ) := Real.log_le_log (by norm_num) this
      linarith
    have h_logT2_le : Real.log (Real.log T + 2) ≤ 2 * Real.log (Real.log (X : ℝ)) := by
      have h1 : Real.log T + 2 ≤ Real.log (X : ℝ) + 2 := by linarith
      have h2 : Real.log (Real.log T + 2) ≤ Real.log (Real.log (X : ℝ) + 2) := by
        refine Real.log_le_log (by linarith [h_logT_nonneg]) h1
      have h3 := log_add_two_le_two_log hlogX_ge2
      exact h2.trans h3
    have h_exp_le : 2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2) ≤
        12 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by
      have h_two_y : 2 * (Real.log T / Real.log (P₀ : ℝ)) ≤ 2 * (3 * (Real.log (X : ℝ)) ^ a_param) := by
        linarith [h_y_le]
      have h_logT2_nonneg : 0 ≤ Real.log (Real.log T + 2) :=
        Real.log_nonneg (by linarith [h_logT_nonneg] : (1 : ℝ) ≤ Real.log T + 2)
      calc 2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2)
        _ ≤ 2 * (3 * (Real.log (X : ℝ)) ^ a_param) * (2 * Real.log (Real.log (X : ℝ))) :=
          mul_le_mul h_two_y h_logT2_le h_logT2_nonneg (by positivity)
        _ = 12 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by ring
    exact Real.exp_le_exp.mpr h_exp_le
  set k := ⌈Real.log T / Real.log (P₀ : ℝ)⌉₊
  have h_fact4 : (5 : ℝ) ^ k * (k.factorial : ℝ) ≤
      Real.exp (16 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))) := by
    have h_five := five_pow_mul_factorial_le k
    have hk_lt : (k : ℝ) < Real.log T / Real.log (P₀ : ℝ) + 1 := Nat.ceil_lt_add_one h_y_nonneg
    have hk_le : (k : ℝ) ≤ 4 * (Real.log (X : ℝ)) ^ a_param := by
      have h1 : (Real.log T / Real.log (P₀ : ℝ)) + 1 ≤ 3 * (Real.log (X : ℝ)) ^ a_param + 1 := by linarith
      have h2 : 3 * (Real.log (X : ℝ)) ^ a_param + 1 ≤ 4 * (Real.log (X : ℝ)) ^ a_param := by
        have := h_help_X.2.1
        linarith
      linarith
    have h_5k1_le : 5 * (k : ℝ) + 1 ≤ 21 * (Real.log (X : ℝ)) ^ a_param := by
      have := h_help_X.2.1
      linarith
    have h_5k1_pos : 0 < 5 * (k : ℝ) + 1 := by positivity
    have h_log_5k1 : Real.log (5 * (k : ℝ) + 1) ≤ 4 * Real.log (Real.log (X : ℝ)) := by
      have h1 : Real.log (5 * (k : ℝ) + 1) ≤ Real.log (21 * (Real.log (X : ℝ)) ^ a_param) :=
        Real.log_le_log h_5k1_pos h_5k1_le
      have h2 : Real.log (21 * (Real.log (X : ℝ)) ^ a_param) =
          Real.log 21 + a_param * Real.log (Real.log (X : ℝ)) := by
        rw [Real.log_mul (by norm_num) (by positivity)]
        congr 1
        exact Real.log_rpow hpos a_param
      rw [h2] at h1
      exact h1.trans h_help_X.2.2
    have h_exp_le : (k : ℝ) * Real.log (5 * (k : ℝ) + 1) ≤
        16 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by
      calc (k : ℝ) * Real.log (5 * (k : ℝ) + 1)
        _ ≤ (4 * (Real.log (X : ℝ)) ^ a_param) * (4 * Real.log (Real.log (X : ℝ))) := by
          refine mul_le_mul hk_le h_log_5k1 ?_ (by positivity)
          have : (1 : ℝ) ≤ 5 * (k : ℝ) + 1 := by linarith
          exact Real.log_nonneg this
        _ = 16 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by ring
    exact h_five.trans (Real.exp_le_exp.mpr h_exp_le)
  have h_prod4_le : T ^ (2 * Real.log (1 / eps_param X) / Real.log (P₀ : ℝ)) * (1 / eps_param X) ^ 2 *
      Real.exp (2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2)) *
      (5 ^ k * (k.factorial : ℝ)) ≤
      Real.exp (1000 * (Real.log (X : ℝ)) ^ (2 * a_param)) := by
    have h1 : T ^ (2 * Real.log (1 / eps_param X) / Real.log (P₀ : ℝ)) * (1 / eps_param X) ^ 2 ≤
        Real.exp (800 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))) := by
      have h := mul_le_mul h_fact1 h_fact2 (by positivity) (Real.exp_pos _).le
      rw [← Real.exp_add] at h
      have h_add : 600 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) +
          200 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) =
          800 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by ring
      rwa [h_add] at h
    have h2 : T ^ (2 * Real.log (1 / eps_param X) / Real.log (P₀ : ℝ)) * (1 / eps_param X) ^ 2 *
        Real.exp (2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2)) ≤
        Real.exp (812 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))) := by
      have h := mul_le_mul h1 h_fact3 (Real.exp_pos _).le (Real.exp_pos _).le
      rw [← Real.exp_add] at h
      have h_add : 800 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) +
          12 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) =
          812 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by ring
      rwa [h_add] at h
    have h3 : T ^ (2 * Real.log (1 / eps_param X) / Real.log (P₀ : ℝ)) * (1 / eps_param X) ^ 2 *
        Real.exp (2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2)) *
        (5 ^ k * (k.factorial : ℝ)) ≤
        Real.exp (828 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))) := by
      have h := mul_le_mul h2 h_fact4 (by positivity) (Real.exp_pos _).le
      rw [← Real.exp_add] at h
      have h_add : 812 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) +
          16 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) =
          828 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by ring
      rwa [h_add] at h
    have h4 : Real.exp (828 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))) ≤
        Real.exp (850 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))) := by
      refine Real.exp_le_exp.mpr ?_
      have : 0 ≤ (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ)) := by positivity
      nlinarith
    have h5 : Real.exp (850 * (Real.log (X : ℝ)) ^ a_param * Real.log (Real.log (X : ℝ))) ≤
        Real.exp (1000 * (Real.log (X : ℝ)) ^ (2 * a_param)) :=
      Real.exp_le_exp.mpr h_comp_X
    exact h3.trans (h4.trans h5)
  have h_TL_card_le : (𝒯_L.card : ℝ) ≤ C₈ * Real.exp (1000 * (Real.log (X : ℝ)) ^ (2 * a_param)) := by
    calc (𝒯_L.card : ℝ)
      _ ≤ C₈ * T ^ (2 * Real.log (1 / eps_param X) / Real.log (P₀ : ℝ)) * (1 / eps_param X) ^ 2 *
          Real.exp (2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2)) * 5 ^ k * (k.factorial : ℝ) := h_TL_bound
      _ = C₈ * (T ^ (2 * Real.log (1 / eps_param X) / Real.log (P₀ : ℝ)) * (1 / eps_param X) ^ 2 *
          Real.exp (2 * (Real.log T / Real.log (P₀ : ℝ)) * Real.log (Real.log T + 2)) * (5 ^ k * (k.factorial : ℝ))) := by ring
      _ ≤ C₈ * Real.exp (1000 * (Real.log (X : ℝ)) ^ (2 * a_param)) :=
        mul_le_mul_of_nonneg_left h_prod4_le hC₈_pos.le
  have h_decay_le := h_decay_X T hT1 hTX
  calc (𝒯_L.card : ℝ) * Real.exp (-c * Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ)) *
        (Real.log ((P_U X : ℝ) * T)) ^ 2
    _ = (𝒯_L.card : ℝ) * (Real.exp (-c * Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ)) *
        (Real.log ((P_U X : ℝ) * T)) ^ 2) := by ring
    _ ≤ (C₈ * Real.exp (1000 * (Real.log (X : ℝ)) ^ (2 * a_param))) *
        Real.exp (-(c / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param)) := by
      refine mul_le_mul h_TL_card_le h_decay_le (by positivity) (by positivity)
    _ = C₈ * (Real.exp (1000 * (Real.log (X : ℝ)) ^ (2 * a_param)) *
        Real.exp (-(c / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param))) := by ring
    _ = C₈ * Real.exp (1000 * (Real.log (X : ℝ)) ^ (2 * a_param) - (c / 2) * (Real.log (X : ℝ)) ^ (1 / 4 - a_param)) := by
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ 1 := h_core_X

lemma eps_param_sq_mul_logT_le {X : ℕ} (hX : 16 ≤ X) {T : ℝ} (hT : 0 < T) (hTX : T ≤ (X : ℝ)) :
    eps_param X ^ 2 * Real.log T ≤ (Real.log (X : ℝ)) ^ (-(199 : ℝ)) := by
  have hpos : 0 < Real.log (X : ℝ) := by linarith [log_X_gt_one hX]
  have h_logT_le : Real.log T ≤ Real.log (X : ℝ) := Real.log_le_log hT hTX
  have h_eps_sq : eps_param X ^ 2 = (Real.log (X : ℝ)) ^ (-(200 : ℝ)) := by
    dsimp [eps_param]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    norm_num
  rw [h_eps_sq]
  have h_mul : (Real.log (X : ℝ)) ^ (-(200 : ℝ)) * Real.log T ≤
      (Real.log (X : ℝ)) ^ (-(200 : ℝ)) * Real.log (X : ℝ) :=
    mul_le_mul_of_nonneg_left h_logT_le (by positivity)
  have h_exp : (Real.log (X : ℝ)) ^ (-(200 : ℝ)) * Real.log (X : ℝ) =
      (Real.log (X : ℝ)) ^ (-(199 : ℝ)) := by
    have h1 : Real.log (X : ℝ) = (Real.log (X : ℝ)) ^ (1 : ℝ) := (Real.rpow_one _).symm
    nth_rw 2 [h1]
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  exact h_mul.trans_eq h_exp

lemma sum_le_card_mul (s : Finset ℕ) (f : ℕ → ℝ) (M : ℝ) (h : ∀ x ∈ s, f x ≤ M) :
    (∑ x ∈ s, f x) ≤ (s.card : ℝ) * M := by
  have h_le := Finset.sum_le_card_nsmul s f M h
  rwa [nsmul_eq_mul] at h_le

lemma eventually_bridge_bound (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1}))
    {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∃ C_large : ℝ, 0 < C_large ∧
      ∀ᶠ X : ℕ in atTop, ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (T₀ T : ℝ),
        3 / 4 ≤ β → β < 1 → 16 ≤ X → (Real.log X) ^ (1 / 15 : ℝ) ≤ T₀ → T₀ ≤ T → T ≤ X →
        (∀ j, 2 ≤ S.Hj hJ j) → (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) →
        (∀ j, S.Hj hJ j ≤ Real.sqrt (S.P j)) →
        (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) →
        ∫ t in S.Uset hJ β X T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
          C_large * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
  obtain ⟨C_B, C_S, C_L, c, hCB_pos, hCS_pos, hCL_pos, hc_pos, h_bridge⟩ :=
    integral_Uset_norm_sq_Fu_le_wellSpaced_bridge c₀ K hc₀ hK hζ hholo
  let C_large := 8 * C_B * C_S + 32 * C_B * C_L + 8 * C_B + 1
  have hClarge_pos : 0 < C_large := by positivity
  refine ⟨C_large, hClarge_pos, ?_⟩
  have h_sides := eventually_all_side_conditions
  have h_R_sq := eventually_R_sq_le c hc_pos
  have h_sum_inv := eventually_sum_inv_H_logP_and_density_le
  have h_card_IU := eventually_card_IU_le
  have h_sieve := eventually_sieve_error_le
  have hp1 := eventually_part1_le
  have hp2 := eventually_part2_le
  have hp3 := eventually_part3_le
  have h_S_card := eventually_S_card_factor hη0 hη
  have h_L_card := eventually_L_card_factor c hc_pos
  filter_upwards [h_sides, h_R_sq, h_sum_inv, h_card_IU, h_sieve, hp1, hp2, hp3, h_S_card, h_L_card] with
    X h_sides_X h_R_sq_X h_sum_inv_X h_card_IU_X h_sieve_X hp1_X hp2_X hp3_X h_S_card_X h_L_card_X
  intro J S hJ β T₀ T hβ hβ1 hX hT0 hT0T hTX hH hQ hP hP_last
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hP2 : 2 ≤ P_U X := h_sides_X.2.1
  have hPQ : P_U X ≤ Q_U X := h_sides_X.2.2.1
  have hQ_le_rpow : (Q_U X : ℝ) ≤ (X : ℝ) ^ (3 / 4 : ℝ) := h_sides_X.2.2.2.1
  have hQX : Q_U X ≤ X := by
    have h1 : (Q_U X : ℝ) ≤ (X : ℝ) := by
      have : (X : ℝ) ^ (3 / 4 : ℝ) ≤ (X : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ X)) (by norm_num)
      rw [Real.rpow_one] at this
      exact hQ_le_rpow.trans this
    exact_mod_cast h1
  have hP4 : (P_U X : ℝ) ^ 4 ≤ (X : ℝ) := h_sides_X.2.2.2.2.1
  have hQβ : (Q_U X : ℝ) ≤ (X : ℝ) ^ β := by
    have : (X : ℝ) ^ (3 / 4 : ℝ) ≤ (X : ℝ) ^ β :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ X)) hβ
    exact hQ_le_rpow.trans this
  have hH2 : 2 ≤ H_U X := h_sides_X.2.2.2.2.2.1
  have hHP : H_U X ≤ Real.sqrt (P_U X : ℝ) := h_sides_X.2.2.2.2.2.2.1
  have hQZ : (Q_U X : ℝ) < Z_param X := h_sides_X.2.2.2.2.2.2.2.1
  have hZ4 : 4 ≤ Z_param X := h_sides_X.2.2.2.2.2.2.2.2.1
  have hZX : Z_param X ≤ Real.sqrt (X : ℝ) := h_sides_X.2.2.2.2.2.2.2.2.2.1
  have hlogXZ : Real.log (X : ℝ) ≤ (Real.log (Z_param X - 1)) ^ (5 / 4 : ℝ) := h_sides_X.2.2.2.2.2.2.2.2.2.2.1
  have h3_le_T0 : 3 ≤ (Real.log (X : ℝ)) ^ (1 / 15 : ℝ) := h_sides_X.2.2.2.2.2.2.2.2.2.2.2.1
  have h3T0 : 3 ≤ T₀ := h3_le_T0.trans hT0
  have h3T : 3 ≤ T := h3T0.trans hT0T
  have h1T0 : 1 ≤ T₀ := by linarith
  have h1T : 1 ≤ T := by linarith
  have hε_nonneg : 0 ≤ eps_param X := Real.rpow_nonneg (by linarith [log_X_gt_one hX]) _
  have hε0_pos : 0 < 1 / (X : ℝ) := by positivity
  have h_logP_pos : 0 < Real.log (P_U X : ℝ) := by
    have : (1 : ℝ) < (P_U X : ℝ) := by exact_mod_cast (by omega : 1 < P_U X)
    exact Real.log_pos this
  have h_logQ_nonneg : 0 ≤ Real.log (Q_U X : ℝ) := by
    have : (1 : ℝ) ≤ (Q_U X : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q_U X)
    exact Real.log_nonneg this
  have h_HU_pos : 0 < H_U X := by linarith
  have h_two_le_HlogP : 2 ≤ H_U X * Real.log (P_U X : ℝ) := by
    have h2 : 1 ≤ Real.log (P_U X : ℝ) := by
      have h_logPU : (Real.log (X : ℝ)) ^ (1 - a_param) ≤ Real.log (P_U X : ℝ) := log_P_U_ge hX
      have h1 : (1 : ℝ) ≤ Real.log (X : ℝ) := (log_X_gt_one hX).le
      have h2 : (0 : ℝ) ≤ 1 - a_param := by dsimp [a_param]; norm_num
      have h_rpow_ge1 : 1 ≤ (Real.log (X : ℝ)) ^ (1 - a_param) := Real.one_le_rpow h1 h2
      exact h_rpow_ge1.trans h_logPU
    nlinarith [hH2, h2]
  have h_bridge_res := h_bridge S hJ β X (P_U X) (Q_U X) (H_U X) T T₀ (Z_param X) (eps_param X) (1 / (X : ℝ))
    hβ hβ1 hX hP2 hPQ hQX hP4 hQβ hH2 hHP h3T hTX h1T0 hT0T hε_nonneg hε0_pos hQZ hZ4 hZX hlogXZ
  set U := S.Uset hJ β X T₀ T
  obtain ⟨f_S₁, f_S₂, h_ws_sub, h_int_bound⟩ := h_bridge_res
  set I_U := Finset.Icc ⌊H_U X * Real.log (P_U X : ℝ)⌋₊ ⌈H_U X * Real.log (Q_U X : ℝ)⌉₊
  let factor_S (f : ℕ → Finset ℝ) (v : ℕ) : ℝ :=
    1 + ((f v).filter (fun (t : ℝ) => ‖Qpoly β X (P_U X) (Q_U X) (H_U X) v ((1 : ℂ) + t * Complex.I)‖ ≤ eps_param X)).card *
      Real.sqrt T * Real.exp (v / H_U X) / X
  let factor_L (f : ℕ → Finset ℝ) (v : ℕ) : ℝ :=
    1 + ((f v).filter (fun (t : ℝ) => ¬ (‖Qpoly β X (P_U X) (Q_U X) (H_U X) v ((1 : ℂ) + t * Complex.I)‖ ≤ eps_param X))).card *
      Real.exp (-c * Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P_U X : ℝ) * T)) ^ 2
  let term_S (f : ℕ → Finset ℝ) (v : ℕ) : ℝ :=
    C_S * eps_param X ^ 2 * Real.log T * factor_S f v
  let term_L (f : ℕ → Finset ℝ) (v : ℕ) : ℝ :=
    C_L * ((Real.log (X : ℝ) + 2) * (1 / (T₀ * Real.log (Z_param X - 1)) + Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ))) + 1 / Z_param X
          + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log (Z_param X))) * (Real.log (Z_param X)) ^ (6 : ℝ)) ^ 2 *
      (1 / (H_U X * Real.log (P_U X : ℝ)) + (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ)) *
      ((H_U X / (v : ℝ)) * factor_L f v)
  let term_v (v : ℕ) : ℝ :=
    ((term_S f_S₁ v + term_L f_S₁ v) + (term_S f_S₂ v + term_L f_S₂ v) + 1 / (X : ℝ))
  change ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
    C_B * (H_U X * Real.log (Q_U X : ℝ)) * (∑ v ∈ I_U, term_v v) +
    C_B * (T / (X : ℝ) + 1) * (1 / H_U X + 1 / (P_U X : ℝ) + Real.log (P_U X : ℝ) / Real.log (Q_U X : ℝ)) at h_int_bound
  have hU_sub_Icc : U ⊆ Set.Icc (-T) T := Uset_subset_Icc_neg S hJ β X T₀ T (zero_le_one.trans h1T0) hT0T
  have h_t_le : ∀ (f : Finset ℝ), (↑f ⊆ U) → ∀ t ∈ f, |t| ≤ T := by
    intro f hf t ht
    have : t ∈ U := hf (Finset.mem_coe.mpr ht)
    have := hU_sub_Icc this
    exact abs_le.mpr ⟨this.1, this.2⟩
  have hR_sq_le := h_R_sq_X T₀ hT0
  have h_sum_inv_le := h_sum_inv_X
  have h_logX_nonneg : 0 ≤ Real.log (X : ℝ) := zero_le_one.trans (log_X_gt_one hX).le
  have hT_pos : 0 < T := zero_lt_one.trans_le h1T
  have h_eps_logT := eps_param_sq_mul_logT_le hX hT_pos hTX
  have h_bound_S_nonneg : 0 ≤ C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) :=
    mul_nonneg hCS_pos.le (Real.rpow_nonneg h_logX_nonneg _)
  have h_rpow_L_nonneg : 0 ≤ (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_nonneg h_logX_nonneg _
  have hCL_R : C_L * ((Real.log (X : ℝ) + 2) * (1 / (T₀ * Real.log (Z_param X - 1)) + Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ))) + 1 / Z_param X
          + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log (Z_param X))) * (Real.log (Z_param X)) ^ (6 : ℝ)) ^ 2 ≤
      C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) :=
    mul_le_mul_of_nonneg_left hR_sq_le hCL_pos.le
  have hCL_R_nonneg : 0 ≤ C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) :=
    mul_nonneg hCL_pos.le h_rpow_L_nonneg
  have h_two_div_nonneg : 0 ≤ 2 / Real.log (P_U X : ℝ) := div_nonneg (by norm_num) h_logP_pos.le
  have h_mid_bound_nonneg : 0 ≤ 2 / (H_U X * Real.log (P_U X : ℝ)) :=
    div_nonneg (by norm_num) (mul_nonneg h_HU_pos.le h_logP_pos.le)
  have h_term_S1 : ∀ v ∈ I_U, term_S f_S₁ v ≤ 2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) := by
    intro v hv
    have h_ws1 := (h_ws_sub v hv).1
    have h_sub1 := (h_ws_sub v hv).2.2.1
    have h_S1 := h_S_card_X J S hJ β T₀ T (f_S₁ v) v hβ hβ1 hX hT0 hT0T hTX hH hQ hP hP_last h_ws1 h_sub1 hv
    have h_bracket : factor_S f_S₁ v ≤ 2 := by
      calc factor_S f_S₁ v ≤ (1 : ℝ) + 1 := add_le_add le_rfl h_S1
      _ = 2 := by norm_num
    have h_pre : C_S * eps_param X ^ 2 * Real.log T ≤ C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h_eps_logT hCS_pos.le
    have h_bracket_nonneg : 0 ≤ factor_S f_S₁ v := by
      have : 0 ≤ ((f_S₁ v).filter (fun (t : ℝ) => ‖Qpoly β X (P_U X) (Q_U X) (H_U X) v ((1 : ℂ) + t * Complex.I)‖ ≤ eps_param X)).card *
          Real.sqrt T * Real.exp (v / H_U X) / X := by
        refine div_nonneg ?_ (Nat.cast_nonneg _)
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
      exact add_nonneg zero_le_one this
    calc term_S f_S₁ v
      _ = C_S * eps_param X ^ 2 * Real.log T * factor_S f_S₁ v := rfl
      _ ≤ (C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) * 2 :=
        mul_le_mul h_pre h_bracket h_bracket_nonneg h_bound_S_nonneg
      _ = 2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) := by ring
  have h_term_S2 : ∀ v ∈ I_U, term_S f_S₂ v ≤ 2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) := by
    intro v hv
    have h_ws2 := (h_ws_sub v hv).2.1
    have h_sub2 := (h_ws_sub v hv).2.2.2
    have h_S2 := h_S_card_X J S hJ β T₀ T (f_S₂ v) v hβ hβ1 hX hT0 hT0T hTX hH hQ hP hP_last h_ws2 h_sub2 hv
    have h_bracket : factor_S f_S₂ v ≤ 2 := by
      calc factor_S f_S₂ v ≤ (1 : ℝ) + 1 := add_le_add le_rfl h_S2
      _ = 2 := by norm_num
    have h_pre : C_S * eps_param X ^ 2 * Real.log T ≤ C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h_eps_logT hCS_pos.le
    have h_bracket_nonneg : 0 ≤ factor_S f_S₂ v := by
      have : 0 ≤ ((f_S₂ v).filter (fun (t : ℝ) => ‖Qpoly β X (P_U X) (Q_U X) (H_U X) v ((1 : ℂ) + t * Complex.I)‖ ≤ eps_param X)).card *
          Real.sqrt T * Real.exp (v / H_U X) / X := by
        refine div_nonneg ?_ (Nat.cast_nonneg _)
        exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) (Real.exp_pos _).le
      exact add_nonneg zero_le_one this
    calc term_S f_S₂ v
      _ = C_S * eps_param X ^ 2 * Real.log T * factor_S f_S₂ v := rfl
      _ ≤ (C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) * 2 :=
        mul_le_mul h_pre h_bracket h_bracket_nonneg h_bound_S_nonneg
      _ = 2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) := by ring
  have h_term_L1 : ∀ v ∈ I_U, term_L f_S₁ v ≤
      8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2) := by
    intro v hv
    have h_ws1 := (h_ws_sub v hv).1
    have h_sub1 := (h_ws_sub v hv).2.2.1
    have ht_le1 := h_t_le (f_S₁ v) h_sub1
    have h_L1 := h_L_card_X β T (f_S₁ v) v h1T hTX h_ws1 ht_le1 hv
    have hv_floor : ⌊H_U X * Real.log (P_U X : ℝ)⌋₊ ≤ v := (Finset.mem_Icc.mp hv).1
    have h_two_div := H_div_v_le_two_div_log_P h_HU_pos h_logP_pos h_two_le_HlogP hv_floor
    have h_bracket_L : factor_L f_S₁ v ≤ 2 := by
      calc factor_L f_S₁ v ≤ (1 : ℝ) + 1 := add_le_add le_rfl h_L1
      _ = 2 := by norm_num
    have h_bracket_L_nonneg : 0 ≤ factor_L f_S₁ v := by
      have : 0 ≤ ((f_S₁ v).filter (fun (t : ℝ) => ¬ (‖Qpoly β X (P_U X) (Q_U X) (H_U X) v ((1 : ℂ) + t * Complex.I)‖ ≤ eps_param X))).card *
          Real.exp (-c * Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P_U X : ℝ) * T)) ^ 2 :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
      exact add_nonneg zero_le_one this
    have h_v_term : (H_U X / (v : ℝ)) * factor_L f_S₁ v ≤ 4 / Real.log (P_U X : ℝ) := by
      calc (H_U X / (v : ℝ)) * factor_L f_S₁ v
        _ ≤ (2 / Real.log (P_U X : ℝ)) * 2 :=
          mul_le_mul h_two_div h_bracket_L h_bracket_L_nonneg h_two_div_nonneg
        _ = 4 / Real.log (P_U X : ℝ) := by ring
    have h_v_term_nonneg : 0 ≤ (H_U X / (v : ℝ)) * factor_L f_S₁ v :=
      mul_nonneg (div_nonneg h_HU_pos.le (Nat.cast_nonneg _)) h_bracket_L_nonneg
    have h_mid : (1 / (H_U X * Real.log (P_U X : ℝ)) + (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ)) *
        ((H_U X / (v : ℝ)) * factor_L f_S₁ v) ≤
        8 / (H_U X * (Real.log (P_U X : ℝ)) ^ 2) := by
      calc _ ≤ (2 / (H_U X * Real.log (P_U X : ℝ))) * (4 / Real.log (P_U X : ℝ)) :=
            mul_le_mul h_sum_inv_le h_v_term h_v_term_nonneg h_mid_bound_nonneg
        _ = 8 / (H_U X * (Real.log (P_U X : ℝ)) ^ 2) := by ring
    have h_mid_nonneg : 0 ≤ (1 / (H_U X * Real.log (P_U X : ℝ)) + (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ)) *
        ((H_U X / (v : ℝ)) * factor_L f_S₁ v) := by
      have : 0 ≤ 1 / (H_U X * Real.log (P_U X : ℝ)) + (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ) := by
        refine add_nonneg (div_nonneg (by norm_num) (mul_nonneg h_HU_pos.le h_logP_pos.le)) ?_
        refine div_nonneg ?_ (Real.sqrt_nonneg _)
        exact pow_nonneg (add_nonneg zero_le_one h_logP_pos.le) _
      exact mul_nonneg this h_v_term_nonneg
    calc term_L f_S₁ v
      _ = C_L * ((Real.log (X : ℝ) + 2) * (1 / (T₀ * Real.log (Z_param X - 1)) + Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ))) + 1 / Z_param X
          + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log (Z_param X))) * (Real.log (Z_param X)) ^ (6 : ℝ)) ^ 2 *
        ((1 / (H_U X * Real.log (P_U X : ℝ)) + (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ)) *
          ((H_U X / (v : ℝ)) * factor_L f_S₁ v)) := by ring
      _ ≤ C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * (8 / (H_U X * (Real.log (P_U X : ℝ)) ^ 2)) :=
        mul_le_mul hCL_R h_mid h_mid_nonneg hCL_R_nonneg
      _ = 8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2) := by ring
  have h_term_L2 : ∀ v ∈ I_U, term_L f_S₂ v ≤
      8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2) := by
    intro v hv
    have h_ws2 := (h_ws_sub v hv).2.1
    have h_sub2 := (h_ws_sub v hv).2.2.2
    have ht_le2 := h_t_le (f_S₂ v) h_sub2
    have h_L2 := h_L_card_X β T (f_S₂ v) v h1T hTX h_ws2 ht_le2 hv
    have hv_floor : ⌊H_U X * Real.log (P_U X : ℝ)⌋₊ ≤ v := (Finset.mem_Icc.mp hv).1
    have h_two_div := H_div_v_le_two_div_log_P h_HU_pos h_logP_pos h_two_le_HlogP hv_floor
    have h_bracket_L : factor_L f_S₂ v ≤ 2 := by
      calc factor_L f_S₂ v ≤ (1 : ℝ) + 1 := add_le_add le_rfl h_L2
      _ = 2 := by norm_num
    have h_bracket_L_nonneg : 0 ≤ factor_L f_S₂ v := by
      have : 0 ≤ ((f_S₂ v).filter (fun (t : ℝ) => ¬ (‖Qpoly β X (P_U X) (Q_U X) (H_U X) v ((1 : ℂ) + t * Complex.I)‖ ≤ eps_param X))).card *
          Real.exp (-c * Real.log (P_U X : ℝ) / (Real.log ((P_U X : ℝ) * T)) ^ (3 / 4 : ℝ)) * (Real.log ((P_U X : ℝ) * T)) ^ 2 :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) (sq_nonneg _)
      exact add_nonneg zero_le_one this
    have h_v_term : (H_U X / (v : ℝ)) * factor_L f_S₂ v ≤ 4 / Real.log (P_U X : ℝ) := by
      calc (H_U X / (v : ℝ)) * factor_L f_S₂ v
        _ ≤ (2 / Real.log (P_U X : ℝ)) * 2 :=
          mul_le_mul h_two_div h_bracket_L h_bracket_L_nonneg h_two_div_nonneg
        _ = 4 / Real.log (P_U X : ℝ) := by ring
    have h_v_term_nonneg : 0 ≤ (H_U X / (v : ℝ)) * factor_L f_S₂ v :=
      mul_nonneg (div_nonneg h_HU_pos.le (Nat.cast_nonneg _)) h_bracket_L_nonneg
    have h_mid : (1 / (H_U X * Real.log (P_U X : ℝ)) + (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ)) *
        ((H_U X / (v : ℝ)) * factor_L f_S₂ v) ≤
        8 / (H_U X * (Real.log (P_U X : ℝ)) ^ 2) := by
      calc _ ≤ (2 / (H_U X * Real.log (P_U X : ℝ))) * (4 / Real.log (P_U X : ℝ)) :=
            mul_le_mul h_sum_inv_le h_v_term h_v_term_nonneg h_mid_bound_nonneg
        _ = 8 / (H_U X * (Real.log (P_U X : ℝ)) ^ 2) := by ring
    have h_mid_nonneg : 0 ≤ (1 / (H_U X * Real.log (P_U X : ℝ)) + (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ)) *
        ((H_U X / (v : ℝ)) * factor_L f_S₂ v) := by
      have : 0 ≤ 1 / (H_U X * Real.log (P_U X : ℝ)) + (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ) := by
        refine add_nonneg (div_nonneg (by norm_num) (mul_nonneg h_HU_pos.le h_logP_pos.le)) ?_
        refine div_nonneg ?_ (Real.sqrt_nonneg _)
        exact pow_nonneg (add_nonneg zero_le_one h_logP_pos.le) _
      exact mul_nonneg this h_v_term_nonneg
    calc term_L f_S₂ v
      _ = C_L * ((Real.log (X : ℝ) + 2) * (1 / (T₀ * Real.log (Z_param X - 1)) + Real.exp (-c * (Real.log (Z_param X - 1)) ^ (1 / 16 : ℝ))) + 1 / Z_param X
          + Real.exp (-(Real.log (X : ℝ)) / (4 * Real.log (Z_param X))) * (Real.log (Z_param X)) ^ (6 : ℝ)) ^ 2 *
        ((1 / (H_U X * Real.log (P_U X : ℝ)) + (1 + Real.log (P_U X : ℝ)) ^ 3 / Real.sqrt (P_U X : ℝ)) *
          ((H_U X / (v : ℝ)) * factor_L f_S₂ v)) := by ring
      _ ≤ C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) * (8 / (H_U X * (Real.log (P_U X : ℝ)) ^ 2)) :=
        mul_le_mul hCL_R h_mid h_mid_nonneg hCL_R_nonneg
      _ = 8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2) := by ring
  set M := 4 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) +
    16 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2) + 1 / (X : ℝ)
  have hM_nonneg : 0 ≤ M := by positivity
  have h_sum_le : (∑ v ∈ I_U, term_v v) ≤ (I_U.card : ℝ) * M := by
    refine sum_le_card_mul I_U term_v M ?_
    intro v hv
    dsimp [term_v, M]
    have hS1 := h_term_S1 v hv
    have hS2 := h_term_S2 v hv
    have hL1 := h_term_L1 v hv
    have hL2 := h_term_L2 v hv
    have h_pair1 : term_S f_S₁ v + term_L f_S₁ v ≤
        (2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
        (8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2)) :=
      add_le_add hS1 hL1
    have h_pair2 : term_S f_S₂ v + term_L f_S₂ v ≤
        (2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
        (8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2)) :=
      add_le_add hS2 hL2
    have h_sum4 : (term_S f_S₁ v + term_L f_S₁ v) + (term_S f_S₂ v + term_L f_S₂ v) ≤
        ((2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
         (8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2))) +
        ((2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
         (8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2))) :=
      add_le_add h_pair1 h_pair2
    have h_sum : (term_S f_S₁ v + term_L f_S₁ v) + (term_S f_S₂ v + term_L f_S₂ v) + 1 / (X : ℝ) ≤
        (((2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
          (8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2))) +
         ((2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
          (8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2)))) +
        1 / (X : ℝ) :=
      add_le_add h_sum4 le_rfl
    have h_alg : (((2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
          (8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2))) +
         ((2 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ))) +
          (8 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2)))) +
        1 / (X : ℝ) =
        4 * C_S * (Real.log (X : ℝ)) ^ (-(199 : ℝ)) +
        16 * C_L * (Real.log (X : ℝ)) ^ (-(1 / 8 : ℝ)) / (H_U X * (Real.log (P_U X : ℝ)) ^ 2) + 1 / (X : ℝ) := by ring
    exact h_sum.trans_eq h_alg
  have h_bridge_sum := bridge_sum_bound C_B C_S C_L hCB_pos.le hCS_pos.le hCL_pos.le X hX
    (H_U X) (Real.log (Q_U X : ℝ)) (Real.log (P_U X : ℝ))
    h_HU_pos h_logQ_nonneg h_logP_pos
    (I_U.card : ℝ) h_card_IU_X (Nat.cast_nonneg _)
    (∑ v ∈ I_U, term_v v) M rfl hM_nonneg h_sum_le
    hp1_X hp2_X hp3_X
  have h_one_le_factor : 1 ≤ T / (X : ℝ) + 1 := by
    have hT_nonneg : 0 ≤ T := h3T.trans' (by norm_num)
    have : 0 ≤ T / (X : ℝ) := div_nonneg hT_nonneg hX_pos.le
    exact le_add_of_nonneg_left this
  have h_sieve_bound : C_B * (T / (X : ℝ) + 1) * (1 / H_U X + 1 / (P_U X : ℝ) + Real.log (P_U X : ℝ) / Real.log (Q_U X : ℝ)) ≤
      6 * C_B * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
    have h_factor_nonneg : 0 ≤ C_B * (T / (X : ℝ) + 1) :=
      mul_nonneg hCB_pos.le (zero_le_one.trans h_one_le_factor)
    calc C_B * (T / (X : ℝ) + 1) * (1 / H_U X + 1 / (P_U X : ℝ) + Real.log (P_U X : ℝ) / Real.log (Q_U X : ℝ))
      _ ≤ C_B * (T / (X : ℝ) + 1) * (6 * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) :=
        mul_le_mul_of_nonneg_left h_sieve_X h_factor_nonneg
      _ = 6 * C_B * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by ring
  have h_first_part_le : (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) ≤
      (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
    have h_nonneg_C : 0 ≤ 8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B := by
      have : 0 ≤ 8 * C_B * C_S := by positivity
      have : 0 ≤ 32 * C_B * C_L := by positivity
      have : 0 ≤ 2 * C_B := by positivity
      positivity
    have h_rpow_nonneg : 0 ≤ (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
      Real.rpow_nonneg h_logX_nonneg _
    calc (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))
      _ = (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * 1 * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by ring
      _ ≤ (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
        refine mul_le_mul_of_nonneg_right ?_ h_rpow_nonneg
        exact mul_le_mul_of_nonneg_left h_one_le_factor h_nonneg_C
  have h_step1 : ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) +
      6 * C_B * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
    calc ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2
      _ ≤ C_B * (H_U X * Real.log (Q_U X : ℝ)) * (∑ v ∈ I_U, term_v v) +
          C_B * (T / (X : ℝ) + 1) * (1 / H_U X + 1 / (P_U X : ℝ) + Real.log (P_U X : ℝ) / Real.log (Q_U X : ℝ)) := h_int_bound
      _ ≤ (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) +
          6 * C_B * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
        add_le_add h_bridge_sum h_sieve_bound
  calc ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2
    _ ≤ (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) +
        6 * C_B * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := h_step1
    _ ≤ (8 * C_B * C_S + 32 * C_B * C_L + 2 * C_B) * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) +
        6 * C_B * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
      add_le_add h_first_part_le le_rfl
    _ = (8 * C_B * C_S + 32 * C_B * C_L + 8 * C_B) * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by ring
    _ ≤ C_large * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by
      have : 8 * C_B * C_S + 32 * C_B * C_L + 8 * C_B ≤ C_large := by
        dsimp [C_large]
        exact le_add_of_nonneg_right zero_le_one
      have h_rpow_pos : 0 ≤ (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
        Real.rpow_nonneg h_logX_nonneg _
      have h_prod_nonneg : 0 ≤ (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
        mul_nonneg (zero_le_one.trans h_one_le_factor) h_rpow_pos
      calc (8 * C_B * C_S + 32 * C_B * C_L + 8 * C_B) * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))
        _ = (8 * C_B * C_S + 32 * C_B * C_L + 8 * C_B) * ((T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) := by ring
        _ ≤ C_large * ((T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ))) :=
          mul_le_mul_of_nonneg_right this h_prod_nonneg
        _ = C_large * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) := by ring

theorem RangeSystem.integral_Uset_le_unsifted (c₀ K : ℝ) (hc₀ : 0 < c₀) (hK : 1 ≤ K)
    (hζ : ∀ (σ t : ℝ), 3 ≤ |t| → 1 - c₀ / (Real.log |t|) ^ (3 / 4 : ℝ) ≤ σ → σ ≤ 2 → ‖deriv riemannZeta (σ + t * Complex.I) / riemannZeta (σ + t * Complex.I)‖ ≤ K * (Real.log |t|) ^ 2)
    (hholo : ∀ T, 3 ≤ T → DifferentiableOn ℂ (fun s => deriv riemannZeta s / riemannZeta s) ((Set.Icc (1 - c₀ / (Real.log T) ^ (3 / 4 : ℝ)) 2 ×ℂ Set.Icc (-T) T) \ {1}))
    {η : ℝ} (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ),
      3 / 4 ≤ β → β < 1 → 16 ≤ X → (Real.log X) ^ (1 / 15 : ℝ) ≤ T₀ → T₀ ≤ T → T ≤ X →
      (∀ j, 2 ≤ S.Hj hJ j) → (∀ j, (S.Q j : ℝ) ≤ Real.exp (Real.sqrt (Real.log X))) →
      (∀ j, S.Hj hJ j ≤ Real.sqrt (S.P j)) →
      (Real.log X) ^ (20 / η) ≤ (S.P ⟨J - 1, by omega⟩ : ℝ) →
      ∫ t in S.Uset hJ β X T₀ T, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (T / (X : ℝ) + 1) * (Real.log (X : ℝ)) ^ (-(1 / 400 : ℝ)) :=
  @RangeSystem.integral_Uset_le_unsifted_of_eventually c₀ K η (eventually_bridge_bound c₀ K hc₀ hK hζ hholo hη0 hη)


end Erdos1201.MR


