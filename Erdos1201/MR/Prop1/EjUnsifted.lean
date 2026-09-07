import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Ranges
import Erdos1201.MR.Setup
import Erdos1201.MR.Decomposition.Lemma12Assembly
import Erdos1201.MR.Decomposition.Lemma12
import Erdos1201.MR.Prop1.Ej
import Erdos1201.MR.Polynomials.MomentComputation
import Erdos1201.MR.Analysis.MeanValueTheorem
import Erdos1201.MR.Prop1.MomentBridge
import Mathlib.Analysis.SpecialFunctions.Stirling

open MeasureTheory intervalIntegral
open scoped BigOperators Real

/-!
# Matomäki–Radziwiłł Proposition 1: Level Set Ej Unsifted Bound

This module establishes bounds for the integral over $T_j = \text{Tset } j$
of the unsifted Dirichlet polynomial $|F_u(\beta, X, 1 + it)|^2$ for $j \ge 1$
($j \ge 2$ in 1-based indexing), corresponding to Section 8.2 of Matomäki–Radziwiłł (arXiv:1501.04585v4).

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

namespace Erdos1201.MR

/-- Multiplicativity of `fX β X` on primes in `primeRange P Q` when coprime to cofactor `m`. -/

lemma factor_fX_coeff (β : ℝ) (X : ℕ) (P Q : ℕ) (hQX : (Q : ℝ) ≤ (X : ℝ) ^ β)
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

lemma one_div_Hj_eq {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (j : Fin J) :
    1 / S.Hj hJ j =
      (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (((j.val + 1 : ℕ) : ℝ) ^ 2 * (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η)) := by
  unfold RangeSystem.Hj
  rw [one_div, inv_div]

lemma one_div_Pj_le_one_div_Hj {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (j : Fin J)
    (hP : 2 ≤ S.P j) (hH1 : 1 ≤ S.Hj hJ j) (hHP : S.Hj hJ j ≤ Real.sqrt (S.P j)) :
    1 / (S.P j : ℝ) ≤ 1 / S.Hj hJ j := by
  have hP_pos : 0 < (S.P j : ℝ) := by positivity
  have hH_pos : 0 < S.Hj hJ j := by linarith
  have hP1 : 1 ≤ (S.P j : ℝ) := by exact_mod_cast (by omega : 1 ≤ S.P j)
  have hsqrt : Real.sqrt (S.P j : ℝ) ≤ (S.P j : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc (S.P j : ℝ) = (S.P j : ℝ) * 1 := by ring
      _ ≤ (S.P j : ℝ) * (S.P j : ℝ) := mul_le_mul_of_nonneg_left hP1 (by positivity)
      _ = (S.P j : ℝ) ^ 2 := by ring
  have h2 : S.Hj hJ j ≤ (S.P j : ℝ) := hHP.trans hsqrt
  exact one_div_le_one_div_of_le hH_pos h2

theorem integral_Tset_norm_sq_Fu_le_uniform {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) (hX : 1 ≤ X) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T) :
    ∫ t in S.Tset hJ β X T₀ T j, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (36 * Real.pi + 2) * (T / (X : ℝ) + 1) := by
  have hT_nonneg : 0 ≤ T := hT0.trans hT
  have h_sub := S.Tset_subset_Icc_neg hJ β X T₀ T j hT0 hT
  have h_meas := S.measurableSet_Tset hJ β X T₀ T j
  have h_pos_n : ∀ n ∈ Finset.Ioc X (2 * X), 0 < n := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    omega
  have h_set_le := setIntegral_norm_sq_dirichletPoly_le (fX β X) (Finset.Ioc X (2 * X))
    h_pos_n T hT_nonneg (S.Tset hJ β X T₀ T j) h_meas h_sub
  have h_coeff_le : ∀ n, ‖fX β X n‖ ≤ 1 := norm_fX_le_one β X
  have h_F_le := integral_norm_sq_F_le_mul (fX β X) h_coeff_le X hX T hT_nonneg
  unfold Fu
  exact h_set_le.trans h_F_le

theorem integral_norm_sq_Fu_le_sum_QR :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
      (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J),
      3 / 4 ≤ β → β < 1 → 2 ≤ X → 0 ≤ T₀ → T₀ ≤ T →
      (∀ k, (S.Q k : ℝ) ≤ (X : ℝ) ^ β) → (S.Q j : ℝ) ^ 4 ≤ X → 1 ≤ S.Hj hJ j →
      let P := S.P j
      let Q := S.Q j
      let H := S.Hj hJ j
      let U := S.Tset hJ β X T₀ T j
      ∫ t in U, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (H * Real.log Q) * (∑ v ∈ S.Ij hJ j,
            ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
                dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
        C * (T / X + 1) * (1 / H + 1 / (P : ℝ) + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := by
  obtain ⟨C_L12, hC_L12_pos, hL12⟩ := integral_norm_sq_F_le_sum_QR
  use C_L12, hC_L12_pos
  intro J η S hJ β X T₀ T j hβ hβ1 hX hT0 hT hQX_all hQ4 hH1
  let P := S.P j
  let Q := S.Q j
  let H := S.Hj hJ j
  let U := S.Tset hJ β X T₀ T j
  have hX1 : 1 ≤ X := by omega
  have hP2 : 2 ≤ P := S.two_le_P j
  have hPQ : P ≤ Q := S.P_le_Q j
  have hQX : (Q : ℝ) ≤ X := by
    have hQ_ge2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hP2.trans hPQ
    have h1 : (1 : ℝ) ≤ (Q : ℝ) := by linarith
    have hQ2 : (1 : ℝ) ≤ (Q : ℝ) * (Q : ℝ) := by nlinarith
    have hQ3 : (1 : ℝ) ≤ (Q : ℝ) * ((Q : ℝ) * (Q : ℝ)) := by nlinarith
    have h4 : (Q : ℝ) ^ 4 = (Q : ℝ) * ((Q : ℝ) * ((Q : ℝ) * (Q : ℝ))) := by ring
    have h_le : (Q : ℝ) ≤ (Q : ℝ) ^ 4 := by
      rw [h4]
      nlinarith
    exact h_le.trans hQ4
  have hP4 : (P : ℝ) ^ 4 ≤ X := by
    have hPQ_r : (P : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hPQ
    have : (P : ℝ) ^ 4 ≤ (Q : ℝ) ^ 4 := by
      have : 0 ≤ (P : ℝ) := by positivity
      gcongr
    exact this.trans hQ4
  have hT_pos : 0 ≤ T := hT0.trans hT
  have hU_meas : MeasurableSet U := S.measurableSet_Tset hJ β X T₀ T j
  have hU_sub : U ⊆ Set.Icc (-T) T := S.Tset_subset_Icc_neg hJ β X T₀ T j hT0 hT
  let a := fX β X
  let b := fX β X
  let c := fX β X
  have ha : ∀ n, ‖a n‖ ≤ 1 := fun n => norm_fX_le_one β X n
  have hb : ∀ m, ‖b m‖ ≤ 1 := fun m => norm_fX_le_one β X m
  have hc : ∀ p, ‖c p‖ ≤ 1 := fun p => norm_fX_le_one β X p
  have hfactor : ∀ p m, p ∈ primeRange P Q → ¬ p ∣ m → a (p * m) = b m * c p :=
    fun p m hp hpm => factor_fX_coeff β X P Q (hQX_all j) hp hpm
  have h_l12 := hL12 X P Q H a b c T U hX1 hP2 hPQ hQX hP4 hH1 hT_pos hU_meas hU_sub ha hb hc hfactor
  exact h_l12

/-- For r ∈ I_i, the set of heights in T_j where Q_{r, H_i} is large (paper Section 8.2). -/
def RangeSystem.Tset_r {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j i : Fin J) (r : ℕ) : Set ℝ :=
  S.Tset hJ β X T₀ T j ∩ {t | Real.exp (-(alpha η (i.val + 1)) * r / S.Hj hJ i) <
    ‖Qpoly β X (S.P i) (S.Q i) (S.Hj hJ i) r ((1 : ℂ) + t * Complex.I)‖}

lemma RangeSystem.measurableSet_Tset_r {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j i : Fin J) (r : ℕ) :
    MeasurableSet (S.Tset_r hJ β X T₀ T j i r) := by
  unfold Tset_r
  refine (S.measurableSet_Tset hJ β X T₀ T j).inter ?_
  exact measurableSet_lt measurable_const (measurable_norm_Qpoly β X (S.P i) (S.Q i) (S.Hj hJ i) r)

lemma RangeSystem.Tset_subset_biUnion_r {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j i : Fin J) (hij : i < j) :
    S.Tset hJ β X T₀ T j ⊆ ⋃ r ∈ S.Ij hJ i, S.Tset_r hJ β X T₀ T j i r := by
  intro t ht
  obtain ⟨r, hr, hQr⟩ := S.Tset_exists_violating_r hJ β X T₀ T j i hij ht
  rw [Set.mem_iUnion]
  use r
  rw [Set.mem_iUnion]
  use hr
  exact ⟨ht, hQr⟩

lemma RangeSystem.norm_sq_QR_v_le_on_Tset_r {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j i : Fin J) (v : ℕ) (hv : v ∈ S.Ij hJ j)
    (r : ℕ) (_hr : r ∈ S.Ij hJ i) (ℓ : ℕ) (t : ℝ) (ht : t ∈ S.Tset_r hJ β X T₀ T j i r) :
    let P := S.P j
    let Q := S.Q j
    let H := S.Hj hJ j
    let Pi := S.P i
    let Qi := S.Q i
    let Hi := S.Hj hJ i
    let c := fX β X
    let b_omega := fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
    ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
        dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
        ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
          dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
  intro P Q H Pi Qi Hi c b_omega
  have ht_Tset := ht.1
  have ht_large := ht.2
  rw [norm_mul, mul_pow]
  have ht_good := S.Tset_good hJ β X T₀ T j ht_Tset v hv
  change ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ≤
    Real.exp (-(alpha η (j.val + 1)) * v / H) at ht_good
  have hQ_sq : ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H) := by
    have h1 : ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        (Real.exp (-(alpha η (j.val + 1)) * v / H)) ^ 2 := by
      nlinarith [norm_nonneg (dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I))]
    have h2 : (Real.exp (-(alpha η (j.val + 1)) * v / H)) ^ 2 = Real.exp (-2 * (alpha η (j.val + 1)) * v / H) := by
      rw [← Real.exp_nat_mul]
      ring_nf
    rwa [h2] at h1
  change Real.exp (-(alpha η (i.val + 1)) * r / Hi) <
    ‖dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)‖ at ht_large
  have h_inv_Qi : 1 ≤ Real.exp ((alpha η (i.val + 1)) * r / Hi) *
      ‖dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)‖ := by
    have h_exp_mul : Real.exp ((alpha η (i.val + 1)) * r / Hi) * Real.exp (-(alpha η (i.val + 1)) * r / Hi) = 1 := by
      rw [← Real.exp_add]
      have : (alpha η (i.val + 1)) * r / Hi + (-(alpha η (i.val + 1)) * r / Hi) = 0 := by ring
      rw [this, Real.exp_zero]
    have h_lt := mul_le_mul_of_nonneg_left (le_of_lt ht_large) (Real.exp_pos ((alpha η (i.val + 1)) * r / Hi)).le
    rw [h_exp_mul] at h_lt
    exact h_lt
  have h_inv_pow : 1 ≤ (Real.exp ((alpha η (i.val + 1)) * r / Hi) *
      ‖dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)‖) ^ (2 * ℓ) := by
    have : 1 = (1 : ℝ) ^ (2 * ℓ) := (one_pow (2 * ℓ)).symm
    rw [this]
    exact pow_le_pow_left₀ (by norm_num) h_inv_Qi (2 * ℓ)
  have h_pow_split : (Real.exp ((alpha η (i.val + 1)) * r / Hi) *
      ‖dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)‖) ^ (2 * ℓ) =
      Real.exp (2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
        ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ‖ ^ 2 := by
    rw [mul_pow, ← Real.exp_nat_mul, norm_pow]
    congr 1
    · congr 1
      push_cast
      ring
    · rw [← pow_mul, mul_comm ℓ 2]
  rw [h_pow_split] at h_inv_pow
  have h_exp_add : Real.exp (-2 * (alpha η (j.val + 1)) * v / H) *
      Real.exp (2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) =
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) := by
    rw [← Real.exp_add]
  have h_R_le : ‖dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (Real.exp (2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
        ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ‖ ^ 2) *
        ‖dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    calc ‖dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2
      _ = 1 * ‖dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by ring
      _ ≤ (Real.exp (2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
        ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ‖ ^ 2) *
        ‖dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h_inv_pow (sq_nonneg _)
  have h_prod_mul : ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
      dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 =
      ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ‖ ^ 2 *
        ‖dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    rw [norm_mul, mul_pow]
  calc ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
        ‖dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2
    _ ≤ Real.exp (-2 * (alpha η (j.val + 1)) * v / H) *
          ‖dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hQ_sq (sq_nonneg _)
    _ ≤ Real.exp (-2 * (alpha η (j.val + 1)) * v / H) *
          ((Real.exp (2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
            ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ‖ ^ 2) *
            ‖dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h_R_le (Real.exp_pos _).le
    _ = (Real.exp (-2 * (alpha η (j.val + 1)) * v / H) *
          Real.exp (2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi)) *
          (‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ‖ ^ 2 *
            ‖dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) := by ring
    _ = Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
          ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
            dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
      rw [h_exp_add, ← h_prod_mul]


lemma RangeSystem.integral_norm_sq_QR_v_le_on_Tset_r {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T)
    (j i : Fin J) (v : ℕ) (hv : v ∈ S.Ij hJ j)
    (r : ℕ) (hr : r ∈ S.Ij hJ i) (ℓ : ℕ) :
    let P := S.P j
    let Q := S.Q j
    let H := S.Hj hJ j
    let Pi := S.P i
    let Qi := S.Q i
    let Hi := S.Hj hJ i
    let c := fX β X
    let b_omega := fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
    let U_r := S.Tset_r hJ β X T₀ T j i r
    ∫ t in U_r, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
        dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
        ∫ t in U_r, ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
          dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
  intro P Q H Pi Qi Hi c b_omega U_r
  have hU_meas : MeasurableSet U_r := S.measurableSet_Tset_r hJ β X T₀ T j i r
  have hU_sub : U_r ⊆ Set.Icc (-T) T := by
    intro t ht
    have ht_T := ht.1
    exact S.Tset_subset_Icc_neg hJ β X T₀ T j hT0 hT ht_T
  let Qv (t : ℝ) := dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)
  let Rv (t : ℝ) := dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)
  let Qir (t : ℝ) := dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)
  have hCont_Qv : Continuous (fun t => ‖Qv t‖ ^ 2) := by
    apply Continuous.pow; apply Continuous.norm; apply continuous_dirichletPoly_l12
    intro n hn
    unfold shortPrimeRange primeRange at hn
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    have := hn.1.2.two_le
    omega
  have hCont_Rv : Continuous (fun t => ‖Rv t‖ ^ 2) := by
    apply Continuous.pow; apply Continuous.norm; apply continuous_dirichletPoly_l12
    intro n hn
    unfold cofactorRange at hn
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  have hCont_QR : Continuous (fun t => ‖Qv t * Rv t‖ ^ 2) := by
    have : (fun t => ‖Qv t * Rv t‖ ^ 2) = fun t => ‖Qv t‖ ^ 2 * ‖Rv t‖ ^ 2 := by
      ext t; rw [norm_mul, mul_pow]
    rw [this]
    exact hCont_Qv.mul hCont_Rv
  have hCont_Qir : Continuous (fun t => ‖Qir t ^ ℓ * Rv t‖ ^ 2) := by
    have : (fun t => ‖Qir t ^ ℓ * Rv t‖ ^ 2) = fun t => (‖Qir t‖ ^ 2) ^ ℓ * ‖Rv t‖ ^ 2 := by
      ext t; rw [norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm ℓ 2, pow_mul]
    rw [this]
    have h1 : Continuous (fun t => ‖Qir t‖ ^ 2) := by
      apply Continuous.pow; apply Continuous.norm; apply continuous_dirichletPoly_l12
      intro n hn
      unfold shortPrimeRange primeRange at hn
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
      have := hn.1.2.two_le
      omega
    exact (h1.pow ℓ).mul hCont_Rv
  have hInt_QR : IntegrableOn (fun t => ‖Qv t * Rv t‖ ^ 2) U_r :=
    hCont_QR.integrableOn_Icc.mono_set hU_sub
  have hInt_Qir_R : IntegrableOn (fun t => ‖Qir t ^ ℓ * Rv t‖ ^ 2) U_r :=
    hCont_Qir.integrableOn_Icc.mono_set hU_sub
  have hInt_rhs : IntegrableOn (fun t => Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
      ‖Qir t ^ ℓ * Rv t‖ ^ 2) U_r := hInt_Qir_R.const_mul _
  have h_pt : ∀ t ∈ U_r, ‖Qv t * Rv t‖ ^ 2 ≤
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
        ‖Qir t ^ ℓ * Rv t‖ ^ 2 := fun t ht =>
    S.norm_sq_QR_v_le_on_Tset_r hJ β X T₀ T j i v hv r hr ℓ t ht
  have h_le := setIntegral_mono_on hInt_QR hInt_rhs hU_meas h_pt
  rw [MeasureTheory.integral_const_mul] at h_le
  exact h_le



lemma RangeSystem.integral_norm_sq_Qir_pow_R_le_interval {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T)
    (j i : Fin J) (v : ℕ) (r : ℕ) (ℓ : ℕ) :
    let P := S.P j
    let Q := S.Q j
    let H := S.Hj hJ j
    let Pi := S.P i
    let Qi := S.Q i
    let Hi := S.Hj hJ i
    let c := fX β X
    let b_omega := fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
    let U_r := S.Tset_r hJ β X T₀ T j i r
    ∫ t in U_r, ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
        dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      ∫ t in (-T)..T, ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
        dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
  intro P Q H Pi Qi Hi c b_omega U_r
  have hU_sub : U_r ⊆ Set.Icc (-T) T := by
    intro t ht
    have ht_T := ht.1
    exact S.Tset_subset_Icc_neg hJ β X T₀ T j hT0 hT ht_T
  let Qir (t : ℝ) := dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)
  let Rv (t : ℝ) := dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)
  let f (t : ℝ) := ‖Qir t ^ ℓ * Rv t‖ ^ 2
  have hCont_Rv : Continuous (fun t => ‖Rv t‖ ^ 2) := by
    apply Continuous.pow; apply Continuous.norm; apply continuous_dirichletPoly_l12
    intro n hn
    unfold cofactorRange at hn
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  have hCont_Qir : Continuous f := by
    dsimp [f]
    have : (fun t => ‖Qir t ^ ℓ * Rv t‖ ^ 2) = fun t => (‖Qir t‖ ^ 2) ^ ℓ * ‖Rv t‖ ^ 2 := by
      ext t; rw [norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm ℓ 2, pow_mul]
    rw [this]
    have h1 : Continuous (fun t => ‖Qir t‖ ^ 2) := by
      apply Continuous.pow; apply Continuous.norm; apply continuous_dirichletPoly_l12
      intro n hn
      unfold shortPrimeRange primeRange at hn
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
      have := hn.1.2.two_le
      omega
    exact (h1.pow ℓ).mul hCont_Rv
  have hf : ∀ t, 0 ≤ f t := fun _ => sq_nonneg _
  have hint : IntegrableOn f (Set.Icc (-T) T) := hCont_Qir.integrableOn_Icc
  have h_le : ∫ t in U_r, f t ≤ ∫ t in Set.Icc (-T) T, f t :=
    setIntegral_mono_set hint.integrable (ae_of_all _ hf) hU_sub.eventuallyLE
  have h_neg_le : -T ≤ T := by linarith [hT0, hT]
  have h_interval : ∫ t in (-T)..T, f t = ∫ t in Set.Ioc (-T) T, f t :=
    integral_of_le h_neg_le
  have h_int_eq : ∫ t in Set.Icc (-T) T, f t = ∫ t in Set.Ioc (-T) T, f t := by
    rw [← integral_Icc_eq_integral_Ioc]
  change ∫ t in U_r, f t ≤ ∫ t in (-T)..T, f t
  linarith



lemma RangeSystem.sum_Ij_exp_le_card_mul {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (j : Fin J) (hH : 0 < S.Hj hJ j) (hα : 0 ≤ alpha η (j.val + 1)) :
    (∑ v ∈ S.Ij hJ j, Real.exp (-2 * (alpha η (j.val + 1)) * (v : ℝ) / S.Hj hJ j)) ≤
      ((S.Ij hJ j).card : ℝ) * Real.exp (-2 * (alpha η (j.val + 1)) * (⌊S.Hj hJ j * Real.log (S.P j)⌋₊ : ℝ) / S.Hj hJ j) := by
  let a := ⌊S.Hj hJ j * Real.log (S.P j)⌋₊
  have h_term : ∀ v ∈ S.Ij hJ j, Real.exp (-2 * (alpha η (j.val + 1)) * (v : ℝ) / S.Hj hJ j) ≤
      Real.exp (-2 * (alpha η (j.val + 1)) * (a : ℝ) / S.Hj hJ j) := by
    intro v hv
    unfold Ij at hv
    rw [Finset.mem_Icc] at hv
    have hva : (a : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv.1
    have h_coeff_nonneg : 0 ≤ 2 * (alpha η (j.val + 1)) / S.Hj hJ j := by positivity
    have h_mul := mul_le_mul_of_nonneg_left hva h_coeff_nonneg
    have h_neg : - (2 * (alpha η (j.val + 1)) / S.Hj hJ j * (v : ℝ)) ≤
        - (2 * (alpha η (j.val + 1)) / S.Hj hJ j * (a : ℝ)) := by linarith
    have h1 : -2 * (alpha η (j.val + 1)) * (v : ℝ) / S.Hj hJ j =
        - (2 * (alpha η (j.val + 1)) / S.Hj hJ j * (v : ℝ)) := by ring
    have h2 : -2 * (alpha η (j.val + 1)) * (a : ℝ) / S.Hj hJ j =
        - (2 * (alpha η (j.val + 1)) / S.Hj hJ j * (a : ℝ)) := by ring
    rw [h1, h2]
    exact Real.exp_le_exp.mpr h_neg
  have h_sum := Finset.sum_le_sum h_term
  simp only [Finset.sum_const, nsmul_eq_mul] at h_sum
  exact h_sum



lemma RangeSystem.integral_norm_sq_QR_v_le_interval {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T)
    (j i : Fin J) (v : ℕ) (hv : v ∈ S.Ij hJ j)
    (r : ℕ) (hr : r ∈ S.Ij hJ i) (ℓ : ℕ) :
    let P := S.P j
    let Q := S.Q j
    let H := S.Hj hJ j
    let Pi := S.P i
    let Qi := S.Q i
    let Hi := S.Hj hJ i
    let c := fX β X
    let b_omega := fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
    let U_r := S.Tset_r hJ β X T₀ T j i r
    ∫ t in U_r, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
        dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
        ∫ t in (-T)..T, ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
          dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
  intro P Q H Pi Qi Hi c b_omega U_r
  have h1 := S.integral_norm_sq_QR_v_le_on_Tset_r hJ β X T₀ T hT0 hT j i v hv r hr ℓ
  have h2 := S.integral_norm_sq_Qir_pow_R_le_interval hJ β X T₀ T hT0 hT j i v r ℓ
  have h_exp_nonneg : 0 ≤ Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) :=
    (Real.exp_pos _).le
  have h_mul := mul_le_mul_of_nonneg_left h2 h_exp_nonneg
  exact h1.trans h_mul

theorem integral_norm_sq_QR_v_le_uniform_Fu :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
      (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j : Fin J) (v : ℕ),
      1 ≤ X → 0 ≤ T₀ → T₀ ≤ T → 1 ≤ S.Hj hJ j → v ∈ S.Ij hJ j →
      let P := S.P j
      let Q := S.Q j
      let H := S.Hj hJ j
      let U := S.Tset hJ β X T₀ T j
      ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        Real.exp (-2 * (alpha η (j.val + 1)) * v / H) * (C * (T / ((X : ℝ) / Q) + 1)) := by
  obtain ⟨C, hC_pos, hC⟩ := integral_norm_sq_QR_v_le_uniform
  use C, hC_pos
  intro J η S hJ β X T₀ T j v hX hT0 hT hH hv
  exact hC J S hJ β X T₀ T j (fX β X) v hX hT0 hT hH (norm_fX_le_one β X) hv

lemma RangeSystem.sum_integral_norm_sq_QR_v_le_Fu {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hX : 1 ≤ X) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T)
    (j : Fin J) (hH : 1 ≤ S.Hj hJ j) :
    let P := S.P j
    let Q := S.Q j
    let H := S.Hj hJ j
    let U := S.Tset hJ β X T₀ T j
    (∑ v ∈ S.Ij hJ j,
      ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      (∑ v ∈ S.Ij hJ j, Real.exp (-2 * (alpha η (j.val + 1)) * v / H)) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) :=
  S.sum_integral_norm_sq_QR_v_le hJ β X T₀ T hX hT0 hT j hH (fX β X) (norm_fX_le_one β X)

/-- Indicator pointwise inequality for covering sets. -/
lemma indicator_le_sum_indicator {α : Type*} (s : Set α) {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (A : ι → Set α)
    (h_sub : s ⊆ ⋃ i ∈ I, A i) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) (x : α) :
    s.indicator f x ≤ ∑ i ∈ I, (A i).indicator f x := by
  by_cases hx : x ∈ s
  · have hx_mem := h_sub hx
    rw [Set.mem_iUnion] at hx_mem
    rcases hx_mem with ⟨i, hi⟩
    rw [Set.mem_iUnion] at hi
    rcases hi with ⟨hiI, hxA⟩
    rw [Set.indicator_of_mem hx]
    have h_term : f x = (A i).indicator f x := (Set.indicator_of_mem hxA f).symm
    rw [h_term]
    have h_rest_nonneg : 0 ≤ ∑ j ∈ I.erase i, (A j).indicator f x := by
      apply Finset.sum_nonneg
      intro j _
      exact Set.indicator_nonneg (fun y _ => hf y) x
    calc (A i).indicator f x
      _ ≤ (A i).indicator f x + ∑ j ∈ I.erase i, (A j).indicator f x := le_add_of_nonneg_right h_rest_nonneg
      _ = ∑ j ∈ I, (A j).indicator f x := Finset.add_sum_erase I (fun j => (A j).indicator f x) hiI
  · rw [Set.indicator_of_notMem hx]
    apply Finset.sum_nonneg
    intro i _
    exact Set.indicator_nonneg (fun y _ => hf y) x

/-- Finite union bound for integrals of non-negative functions on covered sets. -/
lemma setIntegral_le_sum_setIntegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Set α) {ι : Type*} [DecidableEq ι] (I : Finset ι) (A : ι → Set α)
    (h_sub : s ⊆ ⋃ i ∈ I, A i) (hs : MeasurableSet s) (hA : ∀ i ∈ I, MeasurableSet (A i))
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hint_s : IntegrableOn f s μ) (hint_A : ∀ i ∈ I, IntegrableOn f (A i) μ) :
    ∫ x in s, f x ∂μ ≤ ∑ i ∈ I, ∫ x in A i, f x ∂μ := by
  rw [← MeasureTheory.integral_indicator hs]
  have h_sum_int : (∑ i ∈ I, ∫ x in A i, f x ∂μ) = ∫ x, (∑ i ∈ I, (A i).indicator f x) ∂μ := by
    rw [integral_finsetSum I (fun i hi => (hint_A i hi).integrable_indicator (hA i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [MeasureTheory.integral_indicator (hA i hi)]
  have h_pt : ∀ x, s.indicator f x ≤ ∑ i ∈ I, (A i).indicator f x :=
    indicator_le_sum_indicator s I A h_sub f hf
  have h_int1 : Integrable (s.indicator f) μ := hint_s.integrable_indicator hs
  have h_int2 : Integrable (fun x => ∑ i ∈ I, (A i).indicator f x) μ := by
    apply integrable_finsetSum
    intro i hi
    exact (hint_A i hi).integrable_indicator (hA i hi)
  exact (integral_mono h_int1 h_int2 h_pt).trans (le_of_eq h_sum_int.symm)

/-- Step 2: On T_j, the integral of |Q_v R_v|^2 is bounded by the sum of integrals over T_{j,r}. -/
lemma RangeSystem.integral_norm_sq_QR_v_le_sum_r {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T)
    (j i : Fin J) (hij : i < j) (v : ℕ) :
    let P := S.P j
    let Q := S.Q j
    let H := S.Hj hJ j
    let c := fX β X
    let b_omega := fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
    let U := S.Tset hJ β X T₀ T j
    let U_r (r : ℕ) := S.Tset_r hJ β X T₀ T j i r
    let f (t : ℝ) := ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
        dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2
    ∫ t in U, f t ≤ ∑ r ∈ S.Ij hJ i, ∫ t in U_r r, f t := by
  intro P Q H c b_omega U U_r f
  have h_sub : U ⊆ ⋃ r ∈ S.Ij hJ i, U_r r := S.Tset_subset_biUnion_r hJ β X T₀ T j i hij
  have hs : MeasurableSet U := S.measurableSet_Tset hJ β X T₀ T j
  have hA : ∀ r ∈ S.Ij hJ i, MeasurableSet (U_r r) := fun r _ => S.measurableSet_Tset_r hJ β X T₀ T j i r
  have hf : ∀ t, 0 ≤ f t := fun _ => sq_nonneg _
  let Qv (t : ℝ) := dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)
  let Rv (t : ℝ) := dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)
  have hCont_Qv : Continuous (fun t => ‖Qv t‖ ^ 2) := by
    apply Continuous.pow; apply Continuous.norm; apply continuous_dirichletPoly_l12
    intro n hn
    unfold shortPrimeRange primeRange at hn
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    have := hn.1.2.two_le
    omega
  have hCont_Rv : Continuous (fun t => ‖Rv t‖ ^ 2) := by
    apply Continuous.pow; apply Continuous.norm; apply continuous_dirichletPoly_l12
    intro n hn
    unfold cofactorRange at hn
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  have hCont_f : Continuous f := by
    dsimp [f]
    have : (fun t => ‖Qv t * Rv t‖ ^ 2) = fun t => ‖Qv t‖ ^ 2 * ‖Rv t‖ ^ 2 := by
      ext t; rw [norm_mul, mul_pow]
    rw [this]
    exact hCont_Qv.mul hCont_Rv
  have hU_sub : U ⊆ Set.Icc (-T) T := S.Tset_subset_Icc_neg hJ β X T₀ T j hT0 hT
  have hint_s : IntegrableOn f U := hCont_f.integrableOn_Icc.mono_set hU_sub
  have hint_A : ∀ r ∈ S.Ij hJ i, IntegrableOn f (U_r r) := by
    intro r _
    have hUr_sub : U_r r ⊆ Set.Icc (-T) T := by
      intro t ht
      exact hU_sub ht.1
    exact hCont_f.integrableOn_Icc.mono_set hUr_sub
  exact setIntegral_le_sum_setIntegral U (S.Ij hJ i) U_r h_sub hs hA f hf hint_s hint_A

/-- Steps 2 and 3: Reduction of the bilinear integral on T_j to lengthened moments over [-T, T]. -/
lemma RangeSystem.integral_norm_sq_QR_v_le_sum_interval {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T)
    (j i : Fin J) (hij : i < j) (v : ℕ) (hv : v ∈ S.Ij hJ j) (ℓ : ℕ → ℕ) :
    let P := S.P j
    let Q := S.Q j
    let H := S.Hj hJ j
    let Pi := S.P i
    let Qi := S.Q i
    let Hi := S.Hj hJ i
    let c := fX β X
    let b_omega := fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
    let U := S.Tset hJ β X T₀ T j
    ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
        dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      ∑ r ∈ S.Ij hJ i,
        Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ℓ r : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
          ∫ t in (-T)..T, ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ (ℓ r) *
            dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
  intro P Q H Pi Qi Hi c b_omega U
  have h_split := S.integral_norm_sq_QR_v_le_sum_r hJ β X T₀ T hT0 hT j i hij v
  refine h_split.trans ?_
  apply Finset.sum_le_sum
  intro r hr
  exact S.integral_norm_sq_QR_v_le_interval hJ β X T₀ T hT0 hT j i v hv r hr (ℓ r)

/-- Monotonicity of Hj in the level index j. -/
lemma Hj_le_Hj_of_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (i j : Fin J) (hij : i ≤ j) : S.Hj hJ i ≤ S.Hj hJ j := by
  unfold RangeSystem.Hj
  have hi_le_j : i.val + 1 ≤ j.val + 1 := by omega
  have hi_cast : ((i.val + 1 : ℕ) : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by exact_mod_cast hi_le_j
  have hsq : ((i.val + 1 : ℕ) : ℝ) ^ 2 ≤ ((j.val + 1 : ℕ) : ℝ) ^ 2 := by
    have : 0 ≤ ((i.val + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hP0 : 0 ≤ (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) := by positivity
  have hQ0 : 0 ≤ (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) := by positivity
  have hnum : ((i.val + 1 : ℕ) : ℝ) ^ 2 * (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) ≤
      ((j.val + 1 : ℕ) : ℝ) ^ 2 * (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) :=
    mul_le_mul_of_nonneg_right hsq hP0
  exact div_le_div_of_nonneg_right hnum hQ0

/-- Lower bound 3/2 ≤ r / H_i for r ∈ I_i when log P_i ≥ 2 and H_i ≥ 2. -/
lemma three_halves_le_r_div_Hi {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (i : Fin J) (r : ℕ) (hr : r ∈ S.Ij hJ i)
    (hHi : 2 ≤ S.Hj hJ i) (hPi : 2 ≤ Real.log (S.P i)) :
    3 / 2 ≤ (r : ℝ) / S.Hj hJ i := by
  unfold RangeSystem.Ij at hr
  rw [Finset.mem_Icc] at hr
  have hr1 : ⌊S.Hj hJ i * Real.log (S.P i)⌋₊ ≤ r := hr.1
  have hr_cast : (⌊S.Hj hJ i * Real.log (S.P i)⌋₊ : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hH_pos : 0 < S.Hj hJ i := by linarith
  have hfloor : S.Hj hJ i * Real.log (S.P i) - 1 ≤ (⌊S.Hj hJ i * Real.log (S.P i)⌋₊ : ℝ) :=
    (Nat.sub_one_lt_floor (S.Hj hJ i * Real.log (S.P i))).le
  have h_sub_le : S.Hj hJ i * Real.log (S.P i) - 1 ≤ (r : ℝ) := hfloor.trans hr_cast
  have h_div : (S.Hj hJ i * Real.log (S.P i) - 1) / S.Hj hJ i ≤ (r : ℝ) / S.Hj hJ i :=
    div_le_div_of_nonneg_right h_sub_le (le_of_lt hH_pos)
  have h_split : (S.Hj hJ i * Real.log (S.P i) - 1) / S.Hj hJ i =
      Real.log (S.P i) - 1 / S.Hj hJ i := by
    rw [sub_div, mul_div_cancel_left₀ _ hH_pos.ne']
  rw [h_split] at h_div
  have h_inv : 1 / S.Hj hJ i ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hHi
  have h_bound : 3 / 2 ≤ Real.log (S.P i) - 1 / S.Hj hJ i := by linarith
  exact h_bound.trans h_div

/-- Lower bound 3/2 ≤ v / H_j for v ∈ I_j when log P_j ≥ 2 and H_j ≥ 2. -/
lemma three_halves_le_v_div_Hj {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (j : Fin J) (v : ℕ) (hv : v ∈ S.Ij hJ j)
    (hHj : 2 ≤ S.Hj hJ j) (hPj : 2 ≤ Real.log (S.P j)) :
    3 / 2 ≤ (v : ℝ) / S.Hj hJ j :=
  three_halves_le_r_div_Hi S hJ j v hv hHj hPj

/-- The lengthening power parameter $\ell := \lceil (v/H_j) / (r/H_i) \rceil$. -/
noncomputable def ell (v r : ℕ) (H Hi : ℝ) : ℕ := ⌈((v : ℝ) / H) / ((r : ℝ) / Hi)⌉₊

/-- Positivity: 1 ≤ ℓ. -/
lemma one_le_ell {v r : ℕ} {H Hi : ℝ}
    (hv : 0 < (v : ℝ) / H) (hr : 0 < (r : ℝ) / Hi) :
    1 ≤ ell v r H Hi := by
  unfold ell
  have h_ratio_pos : 0 < ((v : ℝ) / H) / ((r : ℝ) / Hi) := div_pos hv hr
  exact Nat.one_le_ceil_iff.mpr h_ratio_pos

/-- Ceiling lower bound: v/H ≤ ℓ * (r/Hi). -/
lemma v_div_H_le_ell_mul {v r : ℕ} {H Hi : ℝ} (hr : 0 < (r : ℝ) / Hi) :
    (v : ℝ) / H ≤ ((ell v r H Hi : ℕ) : ℝ) * ((r : ℝ) / Hi) := by
  unfold ell
  have h_ceil := Nat.le_ceil (((v : ℝ) / H) / ((r : ℝ) / Hi))
  have h_mul := mul_le_mul_of_nonneg_right h_ceil (le_of_lt hr)
  rw [div_mul_cancel₀ _ hr.ne'] at h_mul
  exact h_mul

/-- Ceiling upper bound: ℓ ≤ (v/H)/(r/Hi) + 1. -/
lemma ell_le_add_one {v r : ℕ} {H Hi : ℝ} (hr : 0 < (r : ℝ) / Hi) (hv : 0 ≤ (v : ℝ) / H) :
    ((ell v r H Hi : ℕ) : ℝ) ≤ ((v : ℝ) / H) / ((r : ℝ) / Hi) + 1 := by
  unfold ell
  have h_nonneg : 0 ≤ ((v : ℝ) / H) / ((r : ℝ) / Hi) := div_nonneg hv (le_of_lt hr)
  exact (Nat.ceil_lt_add_one h_nonneg).le

/-- Linear algebra split for the lengthened exponent. -/
lemma exponent_split_le (α_i α_j v r H Hi : ℝ) (ℓ : ℕ)
    (hα_i : 0 ≤ α_i) (hr_pos : 0 < r / Hi)
    (_hℓ_mul : v / H ≤ (ℓ : ℝ) * (r / Hi))
    (hℓ_le : (ℓ : ℝ) ≤ (v / H) / (r / Hi) + 1) :
    -2 * α_j * v / H + 2 * (ℓ : ℝ) * α_i * r / Hi ≤
      2 * (α_i - α_j) * (v / H) + 2 * α_i * (r / Hi) := by
  have h_diff : (ℓ : ℝ) * (r / Hi) - v / H ≤ r / Hi := by
    have h1 : (ℓ : ℝ) * (r / Hi) ≤ ((v / H) / (r / Hi) + 1) * (r / Hi) :=
      mul_le_mul_of_nonneg_right hℓ_le (le_of_lt hr_pos)
    have h2 : ((v / H) / (r / Hi) + 1) * (r / Hi) = v / H + r / Hi := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hr_pos.ne']
    linarith
  have h_alg : -2 * α_j * v / H + 2 * (ℓ : ℝ) * α_i * r / Hi =
      2 * (α_i - α_j) * (v / H) + 2 * α_i * ((ℓ : ℝ) * (r / Hi) - v / H) := by ring
  rw [h_alg]
  have h_mul := mul_le_mul_of_nonneg_left h_diff (by linarith : 0 ≤ 2 * α_i)
  linarith

/-- Bound on the positive term: exp(2 α_i r/Hi) ≤ exp(1/4) √Q_i. -/
lemma exp_two_alpha_i_r_div_Hi_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (hη0 : 0 < η) (hη : η < 1 / 6) (i : Fin J) (r : ℕ) (hr : r ∈ S.Ij hJ i) (hHi : 2 ≤ S.Hj hJ i) :
    Real.exp (2 * (alpha η (i.val + 1)) * ((r : ℝ) / S.Hj hJ i)) ≤
      Real.exp (1 / 4 : ℝ) * Real.sqrt (S.Q i) := by
  have hHi_pos : 0 < S.Hj hJ i := by linarith
  have hQi_pos : (0 : ℝ) < S.Q i := by
    have := (S.two_le_P i).trans (S.P_le_Q i)
    exact Nat.cast_pos.mpr (by linarith)
  have hQi_ge1 : (1 : ℝ) ≤ S.Q i := by
    have := (S.two_le_P i).trans (S.P_le_Q i)
    exact_mod_cast (by omega : 1 ≤ S.Q i)
  have hlogQi_nonneg : 0 ≤ Real.log (S.Q i) := Real.log_nonneg hQi_ge1
  unfold RangeSystem.Ij at hr
  rw [Finset.mem_Icc] at hr
  have hr2 : r ≤ ⌈S.Hj hJ i * Real.log (S.Q i)⌉₊ := hr.2
  have hr_cast : (r : ℝ) ≤ (⌈S.Hj hJ i * Real.log (S.Q i)⌉₊ : ℝ) := by exact_mod_cast hr2
  have hceil : (⌈S.Hj hJ i * Real.log (S.Q i)⌉₊ : ℝ) ≤ S.Hj hJ i * Real.log (S.Q i) + 1 := by
    have hprod_nonneg : 0 ≤ S.Hj hJ i * Real.log (S.Q i) := mul_nonneg (by linarith) hlogQi_nonneg
    exact (Nat.ceil_lt_add_one hprod_nonneg).le
  have hr_le : (r : ℝ) ≤ S.Hj hJ i * Real.log (S.Q i) + 1 := hr_cast.trans hceil
  have hr_div : (r : ℝ) / S.Hj hJ i ≤ Real.log (S.Q i) + 1 / S.Hj hJ i := by
    have h1 : (r : ℝ) / S.Hj hJ i ≤ (S.Hj hJ i * Real.log (S.Q i) + 1) / S.Hj hJ i :=
      div_le_div_of_nonneg_right hr_le (le_of_lt hHi_pos)
    rw [add_div, mul_div_cancel_left₀ _ hHi_pos.ne'] at h1
    exact h1
  have h_inv : 1 / S.Hj hJ i ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hHi
  have hr_bound : (r : ℝ) / S.Hj hJ i ≤ Real.log (S.Q i) + 1 / 2 := by linarith
  have hα_le : alpha η (i.val + 1) ≤ 1 / 4 := by
    have := alpha_le η hη0 (i.val + 1)
    linarith
  have hα_pos : 0 ≤ alpha η (i.val + 1) :=
    alpha_pos η hη0 hη (i.val + 1) (by omega) |>.le
  have h2α_le : 2 * alpha η (i.val + 1) ≤ 1 / 2 := by linarith
  have hr_nonneg : 0 ≤ (r : ℝ) / S.Hj hJ i := by positivity
  have h_prod : 2 * (alpha η (i.val + 1)) * ((r : ℝ) / S.Hj hJ i) ≤
      (1 / 2) * (Real.log (S.Q i) + 1 / 2) := by
    nlinarith
  have h_exp := Real.exp_le_exp.mpr h_prod
  have h_exp_split : Real.exp ((1 / 2) * (Real.log (S.Q i) + 1 / 2)) =
      Real.exp (1 / 4 : ℝ) * Real.exp ((1 / 2) * Real.log (S.Q i)) := by
    have : (1 / 2 : ℝ) * (Real.log (S.Q i) + 1 / 2) = (1 / 4 : ℝ) + (1 / 2) * Real.log (S.Q i) := by ring
    rw [this, Real.exp_add]
  have h_sqrt : Real.exp ((1 / 2) * Real.log (S.Q i)) = Real.sqrt (S.Q i) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hQi_pos]
    ring_nf
  rw [h_exp_split, h_sqrt] at h_exp
  exact h_exp

/-- Condition (3) decay: exp(2 (α_i - α_j) v / H_j) ≤ exp(1/48) Q_i^{-8}. -/
lemma exp_two_alpha_sub_v_div_Hj_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (hη0 : 0 < η) (hη : η < 1 / 6) (j i : Fin J) (hij : i.val + 1 = j.val)
    (v : ℕ) (hv : v ∈ S.Ij hJ j) (hHj : 2 ≤ S.Hj hJ j) (_hPj : 2 ≤ Real.log (S.P j)) :
    Real.exp (2 * (alpha η (i.val + 1) - alpha η (j.val + 1)) * ((v : ℝ) / S.Hj hJ j)) ≤
      Real.exp (1 / 48 : ℝ) * (S.Q i : ℝ) ^ (-8 : ℝ) := by
  have hj_pos : 0 < ((j.val + 1 : ℕ) : ℝ) := by
    have : 1 ≤ j.val + 1 := by omega
    exact Nat.cast_pos.mpr this
  have hj2_pos : 0 < ((j.val + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hHj_pos : 0 < S.Hj hJ j := by linarith
  have hQi_pos : (0 : ℝ) < S.Q i := by
    have := (S.two_le_P i).trans (S.P_le_Q i)
    exact Nat.cast_pos.mpr (by linarith)
  have h_alpha := alpha_sub_succ_le hη0 hij
  have h2alpha : 2 * (alpha η (i.val + 1) - alpha η (j.val + 1)) ≤ - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) := by
    calc 2 * (alpha η (i.val + 1) - alpha η (j.val + 1))
      _ ≤ 2 * (- (η / (2 * ((j.val + 1 : ℕ) : ℝ) ^ 2))) := mul_le_mul_of_nonneg_left h_alpha (by norm_num)
      _ = - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) := by ring
  unfold RangeSystem.Ij at hv
  rw [Finset.mem_Icc] at hv
  have hv1 : ⌊S.Hj hJ j * Real.log (S.P j)⌋₊ ≤ v := hv.1
  have hv_cast : (⌊S.Hj hJ j * Real.log (S.P j)⌋₊ : ℝ) ≤ (v : ℝ) := by exact_mod_cast hv1
  have hfloor : S.Hj hJ j * Real.log (S.P j) - 1 ≤ (⌊S.Hj hJ j * Real.log (S.P j)⌋₊ : ℝ) :=
    (Nat.sub_one_lt_floor (S.Hj hJ j * Real.log (S.P j))).le
  have hv_le : S.Hj hJ j * Real.log (S.P j) - 1 ≤ (v : ℝ) := hfloor.trans hv_cast
  have hv_div : Real.log (S.P j) - 1 / S.Hj hJ j ≤ (v : ℝ) / S.Hj hJ j := by
    have h1 : (S.Hj hJ j * Real.log (S.P j) - 1) / S.Hj hJ j ≤ (v : ℝ) / S.Hj hJ j :=
      div_le_div_of_nonneg_right hv_le (le_of_lt hHj_pos)
    have h2 : (S.Hj hJ j * Real.log (S.P j) - 1) / S.Hj hJ j = Real.log (S.P j) - 1 / S.Hj hJ j := by
      rw [sub_div, mul_div_cancel_left₀ _ hHj_pos.ne']
    rwa [h2] at h1
  have h_inv : 1 / S.Hj hJ j ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hHj
  have hv_bound : Real.log (S.P j) - 1 / 2 ≤ (v : ℝ) / S.Hj hJ j := by linarith
  have h_eta_neg : - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) ≤ 0 := by
    have : 0 ≤ η / ((j.val + 1 : ℕ) : ℝ) ^ 2 := by positivity
    linarith
  have h_exp_arg : 2 * (alpha η (i.val + 1) - alpha η (j.val + 1)) * ((v : ℝ) / S.Hj hJ j) ≤
      - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * (Real.log (S.P j) - 1 / 2) := by
    have h1 : 2 * (alpha η (i.val + 1) - alpha η (j.val + 1)) * ((v : ℝ) / S.Hj hJ j) ≤
        - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * ((v : ℝ) / S.Hj hJ j) :=
      mul_le_mul_of_nonneg_right h2alpha (by positivity)
    have h2 : - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * ((v : ℝ) / S.Hj hJ j) ≤
        - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * (Real.log (S.P j) - 1 / 2) := by
      nlinarith
    exact h1.trans h2
  have hcond3 := S.cond3 j i hij
  have h_log_j_nonneg : 0 ≤ 16 * Real.log ((j.val + 1 : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j.val + 1)
    exact mul_nonneg (by norm_num) (Real.log_nonneg this)
  have h_Pj_bound : (8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i) ≤ Real.log (S.P j) := by
    linarith [hcond3, h_log_j_nonneg]
  have h_eta_factor : (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * ((8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i)) =
      8 * Real.log (S.Q i) := by
    calc (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * ((8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i))
      _ = (η / ((j.val + 1 : ℕ) : ℝ) ^ 2 * (8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η)) * Real.log (S.Q i) := by ring
      _ = 8 * Real.log (S.Q i) := by
        have h_cancel : η / ((j.val + 1 : ℕ) : ℝ) ^ 2 * (8 * ((j.val + 1 : ℕ) : ℝ) ^ 2 / η) = 8 := by
          field_simp
        rw [h_cancel]
  have h_neg_mul : - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * Real.log (S.P j) ≤ - 8 * Real.log (S.Q i) := by
    have : 0 < η / ((j.val + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have h1 := mul_le_mul_of_nonneg_left h_Pj_bound this.le
    rw [h_eta_factor] at h1
    linarith
  have hj_ge2 : (2 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) := by
    have : 2 ≤ j.val + 1 := by omega
    exact_mod_cast this
  have hj_sq_ge4 : (4 : ℝ) ≤ ((j.val + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have h_eta_half : (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * (1 / 2) ≤ 1 / 48 := by
    calc (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * (1 / 2)
      _ ≤ ((1 / 6) / 4) * (1 / 2) := by
        have h1 : η / ((j.val + 1 : ℕ) : ℝ) ^ 2 ≤ (1 / 6) / 4 := by
          have h2 : 0 < ((j.val + 1 : ℕ) : ℝ) ^ 2 := by positivity
          calc η / ((j.val + 1 : ℕ) : ℝ) ^ 2
            _ ≤ (1 / 6) / ((j.val + 1 : ℕ) : ℝ) ^ 2 := div_le_div_of_nonneg_right hη.le h2.le
            _ ≤ (1 / 6) / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hj_sq_ge4
        exact mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ = 1 / 48 := by norm_num
  have h_total : - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * (Real.log (S.P j) - 1 / 2) ≤
      - 8 * Real.log (S.Q i) + 1 / 48 := by
    have : - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * (Real.log (S.P j) - 1 / 2) =
        - (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * Real.log (S.P j) + (η / ((j.val + 1 : ℕ) : ℝ) ^ 2) * (1 / 2) := by ring
    rw [this]
    linarith
  have h_bound_final := h_exp_arg.trans h_total
  have h_exp := Real.exp_le_exp.mpr h_bound_final
  have h_exp_split : Real.exp (- 8 * Real.log (S.Q i) + 1 / 48) =
      Real.exp (1 / 48 : ℝ) * (S.Q i : ℝ) ^ (-8 : ℝ) := by
    rw [add_comm, Real.exp_add, Real.rpow_def_of_pos hQi_pos]
    congr 1
    congr 1
    ring
  rw [h_exp_split] at h_exp
  exact h_exp

/-- Net exponential prefactor decay from lengthening: exp(-2 α_j v/H + 2 ℓ α_i r/Hi) ≤ exp(1/48 + 1/4) Q_i^{-15/2}. -/
lemma exp_lengthening_product_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (hη0 : 0 < η) (hη : η < 1 / 6) (j i : Fin J) (hij : i.val + 1 = j.val)
    (v r : ℕ) (hv : v ∈ S.Ij hJ j) (hr : r ∈ S.Ij hJ i)
    (hHj : 2 ≤ S.Hj hJ j) (hHi : 2 ≤ S.Hj hJ i)
    (hPj : 2 ≤ Real.log (S.P j)) (hPi : 2 ≤ Real.log (S.P i)) :
    let H := S.Hj hJ j
    let Hi := S.Hj hJ i
    let ℓ := ell v r H Hi
    Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * (ℓ : ℝ) * (alpha η (i.val + 1)) * r / Hi) ≤
      Real.exp (1 / 48 + 1 / 4 : ℝ) * (S.Q i : ℝ) ^ (- (15 / 2 : ℝ)) := by
  intro H Hi ℓ
  have hHi_pos : 0 < Hi := by linarith
  have hHj_pos : 0 < H := by linarith
  have hr_pos : 0 < (r : ℝ) / Hi := by
    have := three_halves_le_r_div_Hi S hJ i r hr hHi hPi
    linarith
  have hv_pos : 0 ≤ (v : ℝ) / H := by positivity
  have hα_pos : 0 ≤ alpha η (i.val + 1) :=
    alpha_pos η hη0 hη (i.val + 1) (by omega) |>.le
  have hℓ_ge := v_div_H_le_ell_mul hr_pos (v := v) (H := H)
  have hℓ_le := ell_le_add_one hr_pos hv_pos (v := v) (H := H)
  have h_split := exponent_split_le (alpha η (i.val + 1)) (alpha η (j.val + 1))
    v r H Hi ℓ hα_pos hr_pos hℓ_ge hℓ_le
  have h_exp := Real.exp_le_exp.mpr h_split
  have h_exp_add : Real.exp (2 * (alpha η (i.val + 1) - alpha η (j.val + 1)) * (v / H) + 2 * alpha η (i.val + 1) * (r / Hi)) =
      Real.exp (2 * (alpha η (i.val + 1) - alpha η (j.val + 1)) * (v / H)) *
        Real.exp (2 * alpha η (i.val + 1) * (r / Hi)) := Real.exp_add _ _
  rw [h_exp_add] at h_exp
  have h_term1 : Real.exp (2 * (alpha η (i.val + 1) - alpha η (j.val + 1)) * (v / H)) ≤
      Real.exp (1 / 48 : ℝ) * (S.Q i : ℝ) ^ (-8 : ℝ) :=
    exp_two_alpha_sub_v_div_Hj_le S hJ hη0 hη j i hij v hv hHj hPj
  have h_term2 : Real.exp (2 * (alpha η (i.val + 1)) * (r / Hi)) ≤
      Real.exp (1 / 4 : ℝ) * Real.sqrt (S.Q i) :=
    exp_two_alpha_i_r_div_Hi_le S hJ hη0 hη i r hr hHi
  have h_prod := mul_le_mul h_term1 h_term2 (by positivity) (by positivity)
  have hQi_pos : (0 : ℝ) < S.Q i := by
    have := (S.two_le_P i).trans (S.P_le_Q i)
    exact Nat.cast_pos.mpr (by linarith)
  have h_sqrt : Real.sqrt (S.Q i) = (S.Q i : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow (S.Q i)
  have h_pow : (S.Q i : ℝ) ^ (-8 : ℝ) * (S.Q i : ℝ) ^ (1 / 2 : ℝ) =
      (S.Q i : ℝ) ^ (- (15 / 2 : ℝ)) := by
    rw [← Real.rpow_add hQi_pos]
    congr 1
    ring
  have h_alg : (Real.exp (1 / 48 : ℝ) * (S.Q i : ℝ) ^ (-8 : ℝ)) * (Real.exp (1 / 4 : ℝ) * Real.sqrt (S.Q i)) =
      Real.exp (1 / 48 + 1 / 4 : ℝ) * (S.Q i : ℝ) ^ (- (15 / 2 : ℝ)) := by
    calc (Real.exp (1 / 48 : ℝ) * (S.Q i : ℝ) ^ (-8 : ℝ)) * (Real.exp (1 / 4 : ℝ) * Real.sqrt (S.Q i))
      _ = (Real.exp (1 / 48 : ℝ) * Real.exp (1 / 4 : ℝ)) * ((S.Q i : ℝ) ^ (-8 : ℝ) * Real.sqrt (S.Q i)) := by ring
      _ = Real.exp (1 / 48 + 1 / 4 : ℝ) * ((S.Q i : ℝ) ^ (-8 : ℝ) * (S.Q i : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [← Real.exp_add, h_sqrt]
      _ = Real.exp (1 / 48 + 1 / 4 : ℝ) * (S.Q i : ℝ) ^ (- (15 / 2 : ℝ)) := by rw [h_pow]
  rw [h_alg] at h_prod
  exact h_exp.trans h_prod

/-- Sum over r ∈ I_i of the exponential lengthening prefactor. -/
lemma RangeSystem.sum_exp_lengthening_product_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (hη0 : 0 < η) (hη : η < 1 / 6) (j i : Fin J) (hij : i.val + 1 = j.val)
    (v : ℕ) (hv : v ∈ S.Ij hJ j)
    (hHj : 2 ≤ S.Hj hJ j) (hHi : 2 ≤ S.Hj hJ i)
    (hPj : 2 ≤ Real.log (S.P j)) (hPi : 2 ≤ Real.log (S.P i)) :
    let H := S.Hj hJ j
    let Hi := S.Hj hJ i
    (∑ r ∈ S.Ij hJ i, Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ell v r H Hi : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi)) ≤
      ((S.Ij hJ i).card : ℝ) * (Real.exp (1 / 48 + 1 / 4 : ℝ) * (S.Q i : ℝ) ^ (- (15 / 2 : ℝ))) := by
  intro H Hi
  have h_term : ∀ r ∈ S.Ij hJ i,
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ell v r H Hi : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) ≤
        Real.exp (1 / 48 + 1 / 4 : ℝ) * (S.Q i : ℝ) ^ (- (15 / 2 : ℝ)) :=
    fun r hr => exp_lengthening_product_le S hJ hη0 hη j i hij v r hv hr hHj hHi hPj hPi
  have h_sum := Finset.sum_le_sum h_term
  simp only [Finset.sum_const, nsmul_eq_mul] at h_sum
  exact h_sum

open Real Stirling

/-- Stirling sequence is bounded by e/√2 for all n ≥ 1. -/
theorem stirlingSeq_le_one (n : ℕ) (hn : 1 ≤ n) :
    stirlingSeq n ≤ exp 1 / √2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h_anti : (Real.log ∘ stirlingSeq ∘ Nat.succ) m ≤ (Real.log ∘ stirlingSeq ∘ Nat.succ) 0 :=
    log_stirlingSeq'_antitone (Nat.zero_le m)
  dsimp [Function.comp] at h_anti
  rw [stirlingSeq_one] at h_anti
  have hpos : 0 < stirlingSeq (m + 1) := by
    calc 0 < √π := by positivity
    _ ≤ stirlingSeq (m + 1) := sqrt_pi_le_stirlingSeq (by omega)
  have h_exp := Real.exp_le_exp.mpr h_anti
  rw [Real.exp_log hpos] at h_exp
  have he2_pos : 0 < exp 1 / √2 := by positivity
  rw [Real.exp_log he2_pos] at h_exp
  exact h_exp

/-- Global Stirling upper bound: n! ≤ e √n (n/e)^n for all n ≥ 1. -/
theorem factorial_le_stirling (n : ℕ) (hn : 1 ≤ n) :
    (n.factorial : ℝ) ≤ exp 1 * √(n : ℝ) * ((n : ℝ) / exp 1) ^ n := by
  have h_seq := stirlingSeq_le_one n hn
  unfold stirlingSeq at h_seq
  have h_denom_pos : 0 < √(2 * (n : ℝ)) * ((n : ℝ) / exp 1) ^ n := by
    have h1 : 0 < √(2 * (n : ℝ)) := by
      have : 0 < 2 * (n : ℝ) := by positivity
      exact Real.sqrt_pos.mpr this
    have h2 : 0 < ((n : ℝ) / exp 1) ^ n := by positivity
    exact mul_pos h1 h2
  rw [div_le_iff₀ h_denom_pos] at h_seq
  have h_sqrt : √(2 * (n : ℝ)) = √2 * √(n : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
  rw [h_sqrt] at h_seq
  calc (n.factorial : ℝ) ≤ (exp 1 / √2) * (√2 * √(n : ℝ) * ((n : ℝ) / exp 1) ^ n) := h_seq
  _ = exp 1 * √(n : ℝ) * ((n : ℝ) / exp 1) ^ n := by
    have h2 : √2 ≠ 0 := by positivity
    field_simp

/-- Cofactor range exponential bound: exp(v / H_j) + 1 ≤ X. -/
lemma exp_v_div_H_add_one_le_X {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (X : ℕ) (j : Fin J) (v : ℕ) (hv : v ∈ S.Ij hJ j)
    (hH : 2 ≤ S.Hj hJ j) (hQ4 : (S.Q j : ℝ) ^ 4 ≤ X) :
    Real.exp ((v : ℝ) / S.Hj hJ j) + 1 ≤ (X : ℝ) := by
  have hH_pos : 0 < S.Hj hJ j := by linarith
  have hQ_ge2 : 2 ≤ S.Q j := (S.two_le_P j).trans (S.P_le_Q j)
  have hQ_pos : 0 < (S.Q j : ℝ) := by exact_mod_cast (by omega : 0 < S.Q j)
  have hQ_ge2_r : (2 : ℝ) ≤ S.Q j := by exact_mod_cast hQ_ge2
  have hlogQ_nonneg : 0 ≤ Real.log (S.Q j) := Real.log_nonneg (by linarith)
  unfold RangeSystem.Ij at hv
  rw [Finset.mem_Icc] at hv
  have hv2 : v ≤ ⌈S.Hj hJ j * Real.log (S.Q j)⌉₊ := hv.2
  have hv_cast : (v : ℝ) ≤ (⌈S.Hj hJ j * Real.log (S.Q j)⌉₊ : ℝ) := by exact_mod_cast hv2
  have hceil : (⌈S.Hj hJ j * Real.log (S.Q j)⌉₊ : ℝ) ≤ S.Hj hJ j * Real.log (S.Q j) + 1 := by
    have hprod_nonneg : 0 ≤ S.Hj hJ j * Real.log (S.Q j) := mul_nonneg (by linarith) hlogQ_nonneg
    exact (Nat.ceil_lt_add_one hprod_nonneg).le
  have hv_le : (v : ℝ) ≤ S.Hj hJ j * Real.log (S.Q j) + 1 := hv_cast.trans hceil
  have hv_div : (v : ℝ) / S.Hj hJ j ≤ Real.log (S.Q j) + 1 / S.Hj hJ j := by
    have h1 : (v : ℝ) / S.Hj hJ j ≤ (S.Hj hJ j * Real.log (S.Q j) + 1) / S.Hj hJ j :=
      div_le_div_of_nonneg_right hv_le (le_of_lt hH_pos)
    rw [add_div, mul_div_cancel_left₀ _ hH_pos.ne'] at h1
    exact h1
  have h_inv : 1 / S.Hj hJ j ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hH
  have hv_bound : (v : ℝ) / S.Hj hJ j ≤ Real.log (S.Q j) + 1 / 2 := by linarith
  have h_exp := Real.exp_le_exp.mpr hv_bound
  have h_exp_split : Real.exp (Real.log (S.Q j) + 1 / 2) = (S.Q j : ℝ) * Real.exp (1 / 2 : ℝ) := by
    rw [Real.exp_add, Real.exp_log hQ_pos]
  rw [h_exp_split] at h_exp
  have he_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h1 := Real.exp_le_exp.mpr this
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h1
    exact h1
  have h_exp_le_2Q : Real.exp ((v : ℝ) / S.Hj hJ j) ≤ 2 * (S.Q j : ℝ) := by
    calc Real.exp ((v : ℝ) / S.Hj hJ j)
      _ ≤ (S.Q j : ℝ) * Real.exp (1 / 2 : ℝ) := h_exp
      _ ≤ (S.Q j : ℝ) * 2 := mul_le_mul_of_nonneg_left he_half hQ_pos.le
      _ = 2 * (S.Q j : ℝ) := by ring
  have h_2Q_add_1 : 2 * (S.Q j : ℝ) + 1 ≤ (S.Q j : ℝ) ^ 4 := by
    have hQ2 : 4 ≤ (S.Q j : ℝ) ^ 2 := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (S.Q j : ℝ) ^ 2 := by nlinarith
    have hQ3 : 8 ≤ (S.Q j : ℝ) ^ 3 := by
      calc (8 : ℝ) = 2 * 4 := by norm_num
      _ ≤ (S.Q j : ℝ) * (S.Q j : ℝ) ^ 2 := mul_le_mul hQ_ge2_r hQ2 (by norm_num) (by positivity)
      _ = (S.Q j : ℝ) ^ 3 := by ring
    calc 2 * (S.Q j : ℝ) + 1
      _ ≤ 2 * (S.Q j : ℝ) + (S.Q j : ℝ) := by linarith
      _ = 3 * (S.Q j : ℝ) := by ring
      _ ≤ (S.Q j : ℝ) ^ 3 * (S.Q j : ℝ) := by
        have : 3 ≤ (S.Q j : ℝ) ^ 3 := by linarith
        nlinarith
      _ = (S.Q j : ℝ) ^ 4 := by ring
  linarith

/-- Short prime range exponential bound: exp(r / H_i) ≤ 2 Q_i. -/
lemma exp_r_div_Hi_le_two_mul_Qi {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (i : Fin J) (r : ℕ) (hr : r ∈ S.Ij hJ i)
    (hHi : 2 ≤ S.Hj hJ i) :
    Real.exp ((r : ℝ) / S.Hj hJ i) ≤ 2 * (S.Q i : ℝ) := by
  have hHi_pos : 0 < S.Hj hJ i := by linarith
  have hQ_pos : 0 < (S.Q i : ℝ) := by
    have := (S.two_le_P i).trans (S.P_le_Q i)
    exact Nat.cast_pos.mpr (by linarith)
  have hlogQ_nonneg : 0 ≤ Real.log (S.Q i) := by
    have : 1 ≤ (S.Q i : ℝ) := by
      have := (S.two_le_P i).trans (S.P_le_Q i)
      exact_mod_cast (by omega : 1 ≤ S.Q i)
    exact Real.log_nonneg this
  unfold RangeSystem.Ij at hr
  rw [Finset.mem_Icc] at hr
  have hr2 : r ≤ ⌈S.Hj hJ i * Real.log (S.Q i)⌉₊ := hr.2
  have hr_cast : (r : ℝ) ≤ (⌈S.Hj hJ i * Real.log (S.Q i)⌉₊ : ℝ) := by exact_mod_cast hr2
  have hceil : (⌈S.Hj hJ i * Real.log (S.Q i)⌉₊ : ℝ) ≤ S.Hj hJ i * Real.log (S.Q i) + 1 := by
    have hprod_nonneg : 0 ≤ S.Hj hJ i * Real.log (S.Q i) := mul_nonneg (by linarith) hlogQ_nonneg
    exact (Nat.ceil_lt_add_one hprod_nonneg).le
  have hr_le : (r : ℝ) ≤ S.Hj hJ i * Real.log (S.Q i) + 1 := hr_cast.trans hceil
  have hr_div : (r : ℝ) / S.Hj hJ i ≤ Real.log (S.Q i) + 1 / S.Hj hJ i := by
    have h1 : (r : ℝ) / S.Hj hJ i ≤ (S.Hj hJ i * Real.log (S.Q i) + 1) / S.Hj hJ i :=
      div_le_div_of_nonneg_right hr_le (le_of_lt hHi_pos)
    rw [add_div, mul_div_cancel_left₀ _ hHi_pos.ne'] at h1
    exact h1
  have h_inv : 1 / S.Hj hJ i ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hHi
  have hr_bound : (r : ℝ) / S.Hj hJ i ≤ Real.log (S.Q i) + 1 / 2 := by linarith
  have h_exp := Real.exp_le_exp.mpr hr_bound
  have h_exp_split : Real.exp (Real.log (S.Q i) + 1 / 2) = (S.Q i : ℝ) * Real.exp (1 / 2 : ℝ) := by
    rw [Real.exp_add, Real.exp_log hQ_pos]
  rw [h_exp_split] at h_exp
  have he_half : Real.exp (1 / 2 : ℝ) ≤ 2 := by
    have : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h1 := Real.exp_le_exp.mpr this
    rw [Real.exp_log (by norm_num : (0:ℝ) < 2)] at h1
    exact h1
  calc Real.exp ((r : ℝ) / S.Hj hJ i)
    _ ≤ (S.Q i : ℝ) * Real.exp (1 / 2 : ℝ) := h_exp
    _ ≤ (S.Q i : ℝ) * 2 := mul_le_mul_of_nonneg_left he_half hQ_pos.le
    _ = 2 * (S.Q i : ℝ) := by ring

/-- Application of MomentBridge to the cofactor and short-prime Dirichlet polynomials. -/
lemma integral_norm_sq_Qir_pow_Rv_le_interval :
    ∃ C_B : ℝ, 0 < C_B ∧ ∀ (J : ℕ) {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
      (β : ℝ) (X : ℕ) (T₀ T : ℝ) (_hX : 2 ≤ X) (_hT0 : 0 ≤ T₀) (_hT : T₀ ≤ T)
      (j i : Fin J) (v : ℕ) (_hv : v ∈ S.Ij hJ j)
      (r : ℕ) (_hr : r ∈ S.Ij hJ i)
      (_hHj : 2 ≤ S.Hj hJ j) (_hHi : 2 ≤ S.Hj hJ i)
      (_hPj : 2 ≤ Real.log (S.P j)) (_hPi : 2 ≤ Real.log (S.P i))
      (_hQ4 : (S.Q j : ℝ) ^ 4 ≤ X),
      let P := S.P j
      let Q := S.Q j
      let H := S.Hj hJ j
      let Pi := S.P i
      let Qi := S.Q i
      let Hi := S.Hj hJ i
      let c := fX β X
      let b_omega := fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
      let ℓ := ell v r H Hi
      ∫ t in (-T)..T, ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ ℓ *
          dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C_B * (T / (X : ℝ) + Real.exp ((r : ℝ) / Hi)) * (8 : ℝ) ^ ℓ * (((ℓ + 1).factorial : ℝ)) ^ 2 := by
  obtain ⟨C, hC_pos, hC⟩ := integral_norm_sq_shortPrimePoly_pow_mul_cofactor_le
  refine ⟨C, hC_pos, ?_⟩
  intro J η S hJ β X T₀ T hX hT0 hT j i v hv r hr hHj hHi _hPj hPi hQ4 P Q H Pi Qi Hi c b_omega ℓ
  have hX1 : 1 ≤ X := by omega
  have hH1 : 1 ≤ H := by linarith
  have hHi2 : 2 ≤ Hi := hHi
  have hr_pos : 0 < (r : ℝ) / Hi := by
    have := three_halves_le_r_div_Hi S hJ i r hr hHi hPi
    linarith
  have hv_pos : 0 < (v : ℝ) / H := by
    have := three_halves_le_v_div_Hj S hJ j v hv hHj (by linarith)
    linarith
  have hℓ1 : 1 ≤ ℓ := one_le_ell hv_pos hr_pos
  have hT_nonneg : 0 ≤ T := hT0.trans hT
  have hrHi : 1 ≤ (r : ℝ) / Hi := by
    have := three_halves_le_r_div_Hi S hJ i r hr hHi hPi
    linarith
  have hvH_mul : (v : ℝ) / H ≤ (ℓ : ℝ) * ((r : ℝ) / Hi) := v_div_H_le_ell_mul hr_pos
  have hexp_X : Real.exp ((v : ℝ) / H) + 1 ≤ (X : ℝ) :=
    exp_v_div_H_add_one_le_X S hJ X j v hv hHj hQ4
  have hc : ∀ p, ‖c p‖ ≤ 1 := norm_fX_le_one β X
  have ha : ∀ m, ‖b_omega m‖ ≤ 1 := fun m => norm_b_div_omega_le_one (fX β X) (norm_fX_le_one β X) P Q m
  exact hC X P Q Pi Qi H Hi v r ℓ c b_omega T hX1 hH1 hHi2 hℓ1 hT_nonneg hrHi hvH_mul hexp_X hc ha

/-- Bilinear moment on T_j bounded by the bridge sum over r ∈ I_i. -/
lemma RangeSystem.integral_norm_sq_QR_v_le_sum_bridge :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
      (β : ℝ) (X : ℕ) (T₀ T : ℝ) (_hX : 2 ≤ X) (_hT0 : 0 ≤ T₀) (_hT : T₀ ≤ T)
      (j i : Fin J) (_hij : i < j) (v : ℕ) (_hv : v ∈ S.Ij hJ j)
      (_hHj : 2 ≤ S.Hj hJ j) (_hHi : 2 ≤ S.Hj hJ i)
      (_hPj : 2 ≤ Real.log (S.P j)) (_hPi : 2 ≤ Real.log (S.P i))
      (_hQ4 : (S.Q j : ℝ) ^ 4 ≤ X),
      let P := S.P j
      let Q := S.Q j
      let H := S.Hj hJ j
      let Qi := S.Q i
      let Hi := S.Hj hJ i
      let c := fX β X
      let b_omega := fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
      let U := S.Tset hJ β X T₀ T j
      ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (T / (X : ℝ) + 1) * (Qi : ℝ) *
          ∑ r ∈ S.Ij hJ i,
            Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ell v r H Hi : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
              ((8 : ℝ) ^ (ell v r H Hi) * (((ell v r H Hi + 1).factorial : ℝ)) ^ 2) := by
  obtain ⟨C_B, hC_B_pos, hC_B⟩ := integral_norm_sq_Qir_pow_Rv_le_interval
  refine ⟨2 * C_B, by positivity, ?_⟩
  intro J η S hJ β X T₀ T hX hT0 hT j i hij v hv hHj hHi _hPj hPi hQ4 P Q H Qi Hi c b_omega U
  let Pi := S.P i
  let ℓ := fun r => ell v r H Hi
  have h_sum_int := S.integral_norm_sq_QR_v_le_sum_interval hJ β X T₀ T hT0 hT j i hij v hv ℓ
  dsimp only [P, Q, H, Pi, Qi, Hi, c, b_omega, U] at h_sum_int ⊢
  refine h_sum_int.trans ?_
  have hQi_ge2 : 2 ≤ S.Q i := (S.two_le_P i).trans (S.P_le_Q i)
  have _hQi_pos : 0 < (S.Q i : ℝ) := by exact_mod_cast (by omega : 0 < S.Q i)
  have _hQi_ge2_r : (2 : ℝ) ≤ S.Q i := by exact_mod_cast hQi_ge2
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hT_nonneg : 0 ≤ T := hT0.trans hT
  have hTX_nonneg : 0 ≤ T / (X : ℝ) := div_nonneg hT_nonneg hX_pos.le
  have h_term_le : ∀ r ∈ S.Ij hJ i,
      Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ℓ r : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
        ∫ t in (-T)..T, ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ (ℓ r) *
          dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (2 * C_B * (T / (X : ℝ) + 1) * (Qi : ℝ)) *
        (Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ℓ r : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
          ((8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2)) := by
    intro r hr
    have h_int := hC_B J S hJ β X T₀ T hX hT0 hT j i v hv r hr hHj hHi _hPj hPi hQ4
    dsimp only [ℓ]
    have hexp_r := exp_r_div_Hi_le_two_mul_Qi S hJ i r hr hHi
    have h_brack : T / (X : ℝ) + Real.exp ((r : ℝ) / Hi) ≤ 2 * (T / (X : ℝ) + 1) * (Qi : ℝ) := by
      calc T / (X : ℝ) + Real.exp ((r : ℝ) / Hi)
        _ ≤ T / (X : ℝ) + 2 * (Qi : ℝ) := by linarith [hexp_r]
        _ ≤ 2 * (Qi : ℝ) * (T / (X : ℝ)) + 2 * (Qi : ℝ) := by
          have : 1 ≤ 2 * (Qi : ℝ) := by linarith
          have : 1 * (T / (X : ℝ)) ≤ 2 * (Qi : ℝ) * (T / (X : ℝ)) :=
            mul_le_mul_of_nonneg_right this hTX_nonneg
          linarith
        _ = 2 * (T / (X : ℝ) + 1) * (Qi : ℝ) := by ring
    have h_prod : C_B * (T / (X : ℝ) + Real.exp ((r : ℝ) / Hi)) * (8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2 ≤
        (2 * C_B * (T / (X : ℝ) + 1) * (Qi : ℝ)) * ((8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2) := by
      have h_fact_pos : 0 ≤ (8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2 := by positivity
      calc C_B * (T / (X : ℝ) + Real.exp ((r : ℝ) / Hi)) * (8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2
        _ = (C_B * (T / (X : ℝ) + Real.exp ((r : ℝ) / Hi))) * ((8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2) := by ring
        _ ≤ (C_B * (2 * (T / (X : ℝ) + 1) * (Qi : ℝ))) * ((8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ h_fact_pos
          exact mul_le_mul_of_nonneg_left h_brack hC_B_pos.le
        _ = (2 * C_B * (T / (X : ℝ) + 1) * (Qi : ℝ)) * ((8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2) := by ring
    have hexp_nonneg : 0 ≤ Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ℓ r : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) :=
      (Real.exp_pos _).le
    calc Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ℓ r : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
          ∫ t in (-T)..T, ‖(dirichletPoly c (shortPrimeRange Pi Qi Hi r) ((1 : ℂ) + t * Complex.I)) ^ (ℓ r) *
            dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2
      _ ≤ Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ℓ r : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
            (C_B * (T / (X : ℝ) + Real.exp ((r : ℝ) / Hi)) * (8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_left h_int hexp_nonneg
      _ ≤ Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ℓ r : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
            ((2 * C_B * (T / (X : ℝ) + 1) * (Qi : ℝ)) * ((8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2)) :=
        mul_le_mul_of_nonneg_left h_prod hexp_nonneg
      _ = (2 * C_B * (T / (X : ℝ) + 1) * (Qi : ℝ)) *
            (Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ℓ r : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
              ((8 : ℝ) ^ (ℓ r) * (((ℓ r + 1).factorial : ℝ)) ^ 2)) := by ring
  have h_sum_le := Finset.sum_le_sum h_term_le
  rw [← Finset.mul_sum] at h_sum_le
  exact h_sum_le

/-- Sum over v ∈ I_j of bilinear moments on T_j bounded by the double bridge sum. -/
lemma RangeSystem.sum_integral_norm_sq_QR_v_le_bridge :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
      (β : ℝ) (X : ℕ) (T₀ T : ℝ) (_hX : 2 ≤ X) (_hT0 : 0 ≤ T₀) (_hT : T₀ ≤ T)
      (j i : Fin J) (_hij : i < j)
      (_hHj : 2 ≤ S.Hj hJ j) (_hHi : 2 ≤ S.Hj hJ i)
      (_hPj : 2 ≤ Real.log (S.P j)) (_hPi : 2 ≤ Real.log (S.P i))
      (_hQ4 : (S.Q j : ℝ) ^ 4 ≤ X),
      let P := S.P j
      let Q := S.Q j
      let H := S.Hj hJ j
      let Qi := S.Q i
      let Hi := S.Hj hJ i
      let c := fX β X
      let b_omega := fun m => fX β X m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
      let U := S.Tset hJ β X T₀ T j
      (∑ v ∈ S.Ij hJ j,
        ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C * (T / (X : ℝ) + 1) * (Qi : ℝ) *
          ∑ v ∈ S.Ij hJ j, ∑ r ∈ S.Ij hJ i,
            Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ell v r H Hi : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
              ((8 : ℝ) ^ (ell v r H Hi) * (((ell v r H Hi + 1).factorial : ℝ)) ^ 2) := by
  obtain ⟨C, hC_pos, hC⟩ := RangeSystem.integral_norm_sq_QR_v_le_sum_bridge
  refine ⟨C, hC_pos, ?_⟩
  intro J η S hJ β X T₀ T hX hT0 hT j i hij hHj hHi hPj hPi hQ4 P Q H Qi Hi c b_omega U
  have h_term : ∀ v ∈ S.Ij hJ j,
      (∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C * (T / (X : ℝ) + 1) * (Qi : ℝ) *
          ∑ r ∈ S.Ij hJ i,
            Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ell v r H Hi : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
              ((8 : ℝ) ^ (ell v r H Hi) * (((ell v r H Hi + 1).factorial : ℝ)) ^ 2) :=
    fun v hv => hC J S hJ β X T₀ T hX hT0 hT j i hij v hv hHj hHi hPj hPi hQ4
  have h_sum := Finset.sum_le_sum h_term
  rw [← Finset.mul_sum] at h_sum
  exact h_sum

/-- Assembly theorem: unsifted moment on T_j bounded by the bridge double sum and error terms. -/
theorem RangeSystem.integral_Tset_succ_le_unsifted_bridge {η : ℝ} (_hη0 : 0 < η) (_hη : η < 1 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J : ℕ) (S : RangeSystem J η) (hJ : 0 < J) (β : ℝ) (X : ℕ) (T₀ T : ℝ) (j i : Fin J),
      i < j → 3 / 4 ≤ β → β < 1 → 2 ≤ X → 0 ≤ T₀ → T₀ ≤ T →
      (∀ k, (S.Q k : ℝ) ≤ (X : ℝ) ^ β) → (2 ≤ S.Hj hJ j ∧ S.Hj hJ j ≤ Real.sqrt (S.P j)) → (2 ≤ S.Hj hJ i) →
      (2 ≤ Real.log (S.P j)) → (2 ≤ Real.log (S.P i)) → (S.Q j : ℝ) ^ 4 ≤ X →
      let H := S.Hj hJ j
      let Hi := S.Hj hJ i
      ∫ t in S.Tset hJ β X T₀ T j, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (T / (X : ℝ) + 1) * (
          (H * Real.log (S.Q j)) * (S.Q i : ℝ) * (∑ v ∈ S.Ij hJ j, ∑ r ∈ S.Ij hJ i,
            Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ell v r H Hi : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
              ((8 : ℝ) ^ (ell v r H Hi) * (((ell v r H Hi + 1).factorial : ℝ)) ^ 2))
          + (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (((j.val + 1 : ℕ) : ℝ) ^ 2 * (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η))
          + 1 / (S.P j : ℝ)
          + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange (S.P j) (S.Q j), ¬ p ∣ n)).card : ℝ) / X) := by
  obtain ⟨C_L12, hC_L12_pos, hL12⟩ := integral_norm_sq_Fu_le_sum_QR
  obtain ⟨C_br, hC_br_pos, h_br⟩ := RangeSystem.sum_integral_norm_sq_QR_v_le_bridge
  let C := max (C_L12 * C_br) C_L12 + 1
  have hC_pos : 0 < C := by
    have : 0 < max (C_L12 * C_br) C_L12 := lt_of_lt_of_le hC_L12_pos (le_max_right _ _)
    linarith
  refine ⟨C, hC_pos, ?_⟩
  intro J S hJ β X T₀ T j i hij hβ hβ1 hX hT0 hT hQX hHj hHi hPj hPi hQ4 H Hi
  have hH1 : 1 ≤ S.Hj hJ j := by linarith [hHj.1]
  have h_l12 := hL12 J S hJ β X T₀ T j hβ hβ1 hX hT0 hT hQX hQ4 hH1
  have h_bridge := h_br J S hJ β X T₀ T hX hT0 hT j i hij hHj.1 hHi hPj hPi hQ4
  dsimp only at h_l12 ⊢
  have h_1divH : 1 / S.Hj hJ j =
      (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (((j.val + 1 : ℕ) : ℝ) ^ 2 * (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η)) :=
    one_div_Hj_eq S hJ j
  rw [h_1divH] at h_l12
  have _hTX_nonneg : 0 ≤ T / (X : ℝ) + 1 := by
    have : 0 ≤ T / (X : ℝ) := div_nonneg (hT0.trans hT) (by positivity)
    linarith
  have _hH_logQ_nonneg : 0 ≤ H * Real.log (S.Q j) := by
    have : 0 ≤ H := by linarith [hHj.1]
    have _hQ_ge2 : 2 ≤ S.Q j := (S.two_le_P j).trans (S.P_le_Q j)
    have : 0 ≤ Real.log (S.Q j) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ S.Q j))
    positivity
  have hC_ge_L12 : C_L12 ≤ C := by
    calc C_L12 ≤ max (C_L12 * C_br) C_L12 := le_max_right _ _
    _ ≤ C := by linarith
  have hC_ge_prod : C_L12 * C_br ≤ C := by
    calc C_L12 * C_br ≤ max (C_L12 * C_br) C_L12 := le_max_left _ _
    _ ≤ C := by linarith
  let MainSum := ∑ v ∈ S.Ij hJ j, ∑ r ∈ S.Ij hJ i,
    Real.exp (-2 * (alpha η (j.val + 1)) * v / H + 2 * ((ell v r H Hi : ℕ) : ℝ) * (alpha η (i.val + 1)) * r / Hi) *
      ((8 : ℝ) ^ (ell v r H Hi) * (((ell v r H Hi + 1).factorial : ℝ)) ^ 2)
  have h_main_prod : C_L12 * (H * Real.log (S.Q j)) *
      (C_br * (T / (X : ℝ) + 1) * (S.Q i : ℝ) * MainSum) ≤
      C * (T / (X : ℝ) + 1) * ((H * Real.log (S.Q j)) * (S.Q i : ℝ) * MainSum) := by
    have h_nonneg : 0 ≤ (T / (X : ℝ) + 1) * ((H * Real.log (S.Q j)) * (S.Q i : ℝ) * MainSum) := by
      have : 0 ≤ (S.Q i : ℝ) := by exact_mod_cast (by omega : 0 ≤ S.Q i)
      have : 0 ≤ MainSum := by
        apply Finset.sum_nonneg; intro v _
        apply Finset.sum_nonneg; intro r _
        positivity
      positivity
    calc C_L12 * (H * Real.log (S.Q j)) * (C_br * (T / (X : ℝ) + 1) * (S.Q i : ℝ) * MainSum)
      _ = (C_L12 * C_br) * ((T / (X : ℝ) + 1) * ((H * Real.log (S.Q j)) * (S.Q i : ℝ) * MainSum)) := by ring
      _ ≤ C * ((T / (X : ℝ) + 1) * ((H * Real.log (S.Q j)) * (S.Q i : ℝ) * MainSum)) :=
        mul_le_mul_of_nonneg_right hC_ge_prod h_nonneg
      _ = C * (T / (X : ℝ) + 1) * ((H * Real.log (S.Q j)) * (S.Q i : ℝ) * MainSum) := by ring
  have h_step1 : C_L12 * (H * Real.log (S.Q j)) *
      (∑ v ∈ S.Ij hJ j,
        ∫ t in S.Tset hJ β X T₀ T j,
          ‖dirichletPoly (fX β X) (shortPrimeRange (S.P j) (S.Q j) H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange (S.P j) (S.Q j)) m : ℂ) + 1))
              (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      C * (T / (X : ℝ) + 1) * ((H * Real.log (S.Q j)) * (S.Q i : ℝ) * MainSum) := by
    have h_mul_le : C_L12 * (H * Real.log (S.Q j)) *
        (∑ v ∈ S.Ij hJ j,
          ∫ t in S.Tset hJ β X T₀ T j,
            ‖dirichletPoly (fX β X) (shortPrimeRange (S.P j) (S.Q j) H v) ((1 : ℂ) + t * Complex.I) *
              dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange (S.P j) (S.Q j)) m : ℂ) + 1))
                (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
        C_L12 * (H * Real.log (S.Q j)) * (C_br * (T / (X : ℝ) + 1) * (S.Q i : ℝ) * MainSum) := by
      refine mul_le_mul_of_nonneg_left h_bridge ?_
      positivity
    exact h_mul_le.trans h_main_prod
  let Err := (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (((j.val + 1 : ℕ) : ℝ) ^ 2 * (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η)) +
    1 / (S.P j : ℝ) + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange (S.P j) (S.Q j), ¬ p ∣ n)).card : ℝ) / X
  have h_step2 : C_L12 * (T / (X : ℝ) + 1) * Err ≤ C * (T / (X : ℝ) + 1) * Err := by
    have h_nonneg : 0 ≤ (T / (X : ℝ) + 1) * Err := by
      have : 0 ≤ Err := by
        have _hP0 : 0 ≤ (S.P ⟨0, hJ⟩ : ℝ) := by exact_mod_cast (by omega : 0 ≤ S.P ⟨0, hJ⟩)
        have _hQ0 : 0 ≤ (S.Q ⟨0, hJ⟩ : ℝ) := by exact_mod_cast (by omega : 0 ≤ S.Q ⟨0, hJ⟩)
        have : 0 ≤ (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) := by positivity
        have : 0 ≤ (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η) := by positivity
        have : 0 ≤ 1 / (S.P j : ℝ) := by positivity
        have : 0 ≤ (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange (S.P j) (S.Q j), ¬ p ∣ n)).card : ℝ) / X := by positivity
        positivity
      positivity
    calc C_L12 * (T / (X : ℝ) + 1) * Err
      _ = C_L12 * ((T / (X : ℝ) + 1) * Err) := by ring
      _ ≤ C * ((T / (X : ℝ) + 1) * Err) := mul_le_mul_of_nonneg_right hC_ge_L12 h_nonneg
      _ = C * (T / (X : ℝ) + 1) * Err := by ring
  calc ∫ t in S.Tset hJ β X T₀ T j, ‖Fu β X ((1 : ℂ) + t * Complex.I)‖ ^ 2
    _ ≤ C_L12 * (H * Real.log (S.Q j)) *
          (∑ v ∈ S.Ij hJ j,
            ∫ t in S.Tset hJ β X T₀ T j,
              ‖dirichletPoly (fX β X) (shortPrimeRange (S.P j) (S.Q j) H v) ((1 : ℂ) + t * Complex.I) *
                dirichletPoly (fun m => fX β X m / ((omegaIn (primeRange (S.P j) (S.Q j)) m : ℂ) + 1))
                  (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
        C_L12 * (T / (X : ℝ) + 1) * Err := h_l12
    _ ≤ C * (T / (X : ℝ) + 1) * ((H * Real.log (S.Q j)) * (S.Q i : ℝ) * MainSum) +
        C * (T / (X : ℝ) + 1) * Err := add_le_add h_step1 h_step2
    _ = C * (T / (X : ℝ) + 1) * ((H * Real.log (S.Q j)) * (S.Q i : ℝ) * MainSum +
        (Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (((j.val + 1 : ℕ) : ℝ) ^ 2 * (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η)) +
        1 / (S.P j : ℝ) +
        (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange (S.P j) (S.Q j), ¬ p ∣ n)).card : ℝ) / X) := by
      dsimp [Err]
      ring

end Erdos1201.MR

