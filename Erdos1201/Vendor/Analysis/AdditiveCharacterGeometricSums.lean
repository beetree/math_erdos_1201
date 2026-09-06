module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Sum
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-
Elementary additive-character kernel identities and the Schur row-sum form of
the finite additive large-sieve estimate. Source provenance is recorded in the
campaign report.
-/

@[expose] public section

namespace AdditiveCharacterGeometricSums

open scoped BigOperators
open Real Complex

/-- Distance to the nearest integer. -/
noncomputable def nearestIntegerDistance (x : ℝ) : ℝ := |x - round x|

/-- The standard additive character `exp(2π i θ)`. -/
noncomputable def additiveCharacter (θ : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * θ)

lemma nearestIntegerDistance_nonneg (x : ℝ) : 0 ≤ nearestIntegerDistance x :=
  abs_nonneg _

lemma nearestIntegerDistance_le_half (x : ℝ) : nearestIntegerDistance x ≤ 1 / 2 :=
  by simpa only [nearestIntegerDistance] using (abs_sub_round x)

/-- A Jordan-type lower bound for the sine of a real number. -/
lemma two_mul_nearestIntegerDistance_le_abs_sin (α : ℝ) :
    2 * nearestIntegerDistance α ≤ |Real.sin (Real.pi * α)| := by
  set β := α - round α with hβ
  have hβ_range : β ∈ Set.Icc (-1 / 2) (1 / 2) := by
    constructor <;> linarith [abs_le.mp (abs_sub_round α)]
  have hβ_abs : nearestIntegerDistance α = abs β := by
    simp [nearestIntegerDistance, hβ]
  have h_sin : abs (Real.sin (Real.pi * α)) = abs (Real.sin (Real.pi * β)) := by
    rw [mul_sub, Real.sin_sub]
    norm_num [mul_comm Real.pi, Real.sin_add, Real.cos_add]
  have h_sin_nonneg : ∀ β : ℝ, 0 ≤ β ∧ β ≤ 1 / 2 →
      2 * β ≤ abs (Real.sin (Real.pi * β)) := by
    intro β hβ
    rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))]
    exact le_trans (by ring_nf; norm_num [Real.pi_pos.ne'])
      (Real.mul_le_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))
  cases abs_cases β <;> simp_all +decide
  · simpa only [abs_of_nonneg (sub_nonneg.mpr ‹_›)] using
      h_sin_nonneg _ (sub_nonneg.mpr ‹_›) (by norm_num at *; linarith)
  · convert h_sin_nonneg (-(α - round α)) (by linarith) (by linarith) using 1 <;> ring_nf
    rw [← abs_neg, ← Real.sin_neg]
    ring_nf

/-- A finite additive-character geometric-sum bound away from integral phases. -/
lemma norm_sum_additiveCharacter_le (M N : ℕ) (α : ℝ)
    (h : nearestIntegerDistance α ≠ 0) :
    ‖(∑ n ∈ Finset.Ico M (M + N), additiveCharacter (n * α))‖ ≤
      1 / (2 * nearestIntegerDistance α) := by
  have h_geo_series : ∑ n ∈ Finset.Ico M (M + N), additiveCharacter (n * α) =
      (additiveCharacter ((M + N) * α) - additiveCharacter (M * α)) /
        (additiveCharacter α - 1) := by
    rw [eq_div_iff]
    · convert Finset.sum_range_sub (fun n => additiveCharacter ((M + n) * α)) N using 1 <;>
        norm_num [add_mul, Finset.sum_Ico_eq_sum_range]
      simp +decide [← add_assoc, Finset.sum_mul _ _ _, additiveCharacter]
      rw [← Finset.sum_sub_distrib]
      congr
      ext
      ring_nf
      norm_num [← Complex.exp_add]
      ring_nf
    · contrapose! h
      simp_all +decide [sub_eq_iff_eq_add]
      have h_alpha_int : ∃ k : ℤ, α = k := by
        rw [additiveCharacter, Complex.exp_eq_one_iff] at h
        obtain ⟨k, hk⟩ := h
        exact ⟨k, by norm_num [Complex.ext_iff] at hk; nlinarith [Real.pi_pos]⟩
      unfold nearestIntegerDistance
      rcases h_alpha_int with ⟨k, hk⟩
      rw [hk]
      simp
  have h_abs : ‖additiveCharacter ((M + N) * α) - additiveCharacter (M * α)‖ ≤ 2 := by
    calc
      ‖additiveCharacter ((M + N) * α) - additiveCharacter (M * α)‖
          ≤ ‖additiveCharacter ((M + N) * α)‖ + ‖additiveCharacter (M * α)‖ :=
        norm_sub_le _ _
      _ = 2 := by norm_num [additiveCharacter, Complex.norm_exp]
  have h_abs_z_minus_one : ‖additiveCharacter α - 1‖ ≥ 4 * nearestIntegerDistance α := by
    have h_abs_z_minus_one : ‖additiveCharacter α - 1‖ =
        2 * |Real.sin (Real.pi * α)| := by
      unfold additiveCharacter
      norm_num [Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im]
      ring_nf
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num <;> ring_nf <;>
        norm_num [Real.sin_sq, Real.cos_sq] <;> ring_nf
      nlinarith [Real.cos_sq' (Real.pi * α * 2)]
    linarith [two_mul_nearestIntegerDistance_le_abs_sin α]
  rw [h_geo_series, norm_div]
  rw [div_le_div_iff₀] <;>
    nlinarith [show 0 < nearestIntegerDistance α from
      lt_of_le_of_ne (nearestIntegerDistance_nonneg α) h.symm]

lemma additiveCharacter_add (x y : ℝ) :
    additiveCharacter x * additiveCharacter y = additiveCharacter (x + y) := by
  unfold additiveCharacter
  rw [← Complex.exp_add]
  ring_nf
  push_cast
  ring_nf

lemma conj_additiveCharacter (x : ℝ) :
    (starRingEnd ℂ) (additiveCharacter x) = additiveCharacter (-x) := by
  unfold additiveCharacter
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  push_cast
  ring

lemma norm_additiveCharacter (x : ℝ) : ‖additiveCharacter x‖ = 1 := by
  unfold additiveCharacter
  rw [Complex.norm_exp]
  norm_num

/-- The finite additive-character kernel. -/
noncomputable def additiveCharacterKernel (M N : ℕ) (a : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico M (M + N), additiveCharacter (n * a)

lemma additiveCharacterKernel_zero (M N : ℕ) : additiveCharacterKernel M N 0 = (N : ℂ) := by
  unfold additiveCharacterKernel
  simp [additiveCharacter, Nat.card_Ico]

lemma norm_additiveCharacterKernel_le (M N : ℕ) (a : ℝ)
    (h : nearestIntegerDistance a ≠ 0) :
    ‖additiveCharacterKernel M N a‖ ≤ 1 / (2 * nearestIntegerDistance a) :=
  norm_sum_additiveCharacter_le M N a h

lemma norm_additiveCharacterKernel_neg (M N : ℕ) (a : ℝ) :
    ‖additiveCharacterKernel M N (-a)‖ = ‖additiveCharacterKernel M N a‖ := by
  unfold additiveCharacterKernel
  rw [← norm_star]
  congr 1
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [star_def, conj_additiveCharacter]
  congr 1
  ring


/-- The Schur row-sum form of the finite additive large-sieve estimate. -/
theorem additiveLargeSieve_rowbound (M N R : ℕ) (θ : Fin R → ℝ) (c : Fin R → ℂ) (Δ : ℝ)
    (hΔ : ∀ r, ∑ s, ‖additiveCharacterKernel M N (θ r - θ s)‖ ≤ Δ) :
    (∑ n ∈ Finset.Ico M (M + N), ‖∑ r, c r * additiveCharacter (n * θ r)‖ ^ 2)
      ≤ Δ * ∑ r, ‖c r‖ ^ 2 := by
  have h_fubini : ∑ n ∈ Finset.Ico M (M + N), ‖∑ r, c r * additiveCharacter (n * θ r)‖ ^ 2 =
      (∑ r, ∑ s, c r * (starRingEnd ℂ (c s)) *
        (additiveCharacterKernel M N (θ r - θ s))).re := by
    have h_fubini : ∑ n ∈ Finset.Ico M (M + N), ‖∑ r, c r * additiveCharacter (n * θ r)‖ ^ 2 =
        (∑ n ∈ Finset.Ico M (M + N), (∑ r, c r * additiveCharacter (n * θ r)) *
          (∑ s, (starRingEnd ℂ (c s)) * additiveCharacter (-n * θ s))).re := by
      have h_fubini : ∀ n ∈ Finset.Ico M (M + N),
          ‖∑ r, c r * additiveCharacter (n * θ r)‖ ^ 2 =
            (∑ r, c r * additiveCharacter (n * θ r)) *
              (∑ s, (starRingEnd ℂ (c s)) * additiveCharacter (-n * θ s)) := by
        intro n hn
        have h_sum_rearrange : ‖∑ r : Fin R, c r * additiveCharacter (n * θ r)‖ ^ 2 =
            (∑ r : Fin R, c r * additiveCharacter (n * θ r)) *
              starRingEnd ℂ (∑ r : Fin R, c r * additiveCharacter (n * θ r)) := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
        convert h_sum_rearrange using 2
        simp +decide [additiveCharacter, Complex.ext_iff, Complex.exp_re, Complex.exp_im]
      rw [← Finset.sum_congr rfl h_fubini]
      norm_cast
    convert h_fubini using 3
    simp +decide [Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm]
    ring_nf
    rw [Finset.sum_comm, Finset.sum_congr rfl]
    rw [Finset.sum_comm]
    simp +decide [additiveCharacterKernel, Finset.mul_sum _ _ _, mul_assoc, mul_comm,
      additiveCharacter_add]
    exact fun _ => Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => by ring_nf)
  have h_amgm : ∀ r s, ‖c r‖ * ‖c s‖ ≤ (‖c r‖ ^ 2 + ‖c s‖ ^ 2) / 2 := by
    exact fun r s => by linarith only [sq_nonneg (‖c r‖ - ‖c s‖)]
  have h_bound : (∑ r, ∑ s, c r * (starRingEnd ℂ (c s)) *
      additiveCharacterKernel M N (θ r - θ s)).re ≤
      ∑ r, ∑ s, (‖c r‖ ^ 2 + ‖c s‖ ^ 2) / 2 *
        ‖additiveCharacterKernel M N (θ r - θ s)‖ := by
    refine' le_trans _ (Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_right (h_amgm r s) (norm_nonneg _))
    exact (Complex.re_le_norm _).trans (by
      calc
        ‖∑ r, ∑ s, c r * (starRingEnd ℂ (c s)) *
            additiveCharacterKernel M N (θ r - θ s)‖
          ≤ ∑ r, ‖∑ s, c r * (starRingEnd ℂ (c s)) *
            additiveCharacterKernel M N (θ r - θ s)‖ := norm_sum_le _ _
        _ ≤ ∑ r, ∑ s, ‖c r * (starRingEnd ℂ (c s)) *
            additiveCharacterKernel M N (θ r - θ s)‖ :=
          Finset.sum_le_sum fun r _ => norm_sum_le _ _
        _ = ∑ r, ∑ s, ‖c r‖ * ‖c s‖ *
            ‖additiveCharacterKernel M N (θ r - θ s)‖ := by simp)
  have h_sum_bound : ∑ r, ∑ s, (‖c r‖ ^ 2 + ‖c s‖ ^ 2) / 2 *
      ‖additiveCharacterKernel M N (θ r - θ s)‖ ≤
      ∑ r, ‖c r‖ ^ 2 * (∑ s, ‖additiveCharacterKernel M N (θ r - θ s)‖) := by
    norm_num [Finset.sum_add_distrib, add_mul, Finset.mul_sum _ _ _, div_mul_eq_mul_div]
    norm_num [Finset.sum_add_distrib, ← Finset.sum_div _ _, norm_additiveCharacterKernel_neg]
    rw [← Finset.sum_comm]
    ring_nf
    norm_num
    rw [show (∑ x : Fin R, ∑ x_1 : Fin R,
        ‖c x_1‖ ^ 2 * ‖additiveCharacterKernel M N (θ x - θ x_1)‖) =
        ∑ x : Fin R, ∑ x_1 : Fin R,
          ‖c x_1‖ ^ 2 * ‖additiveCharacterKernel M N (θ x_1 - θ x)‖ from
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by
        rw [← norm_additiveCharacterKernel_neg]
        ring_nf]
    linarith
  exact h_fubini.symm ▸ h_bound.trans (h_sum_bound.trans (by
    rw [Finset.mul_sum _ _ _]
    exact Finset.sum_le_sum fun i _ => by
      nlinarith only [hΔ i, show 0 ≤ ‖c i‖ ^ 2 by positivity]))

/-- The spacing form of the finite additive large-sieve estimate. -/
theorem additiveLargeSieve_spacing (M N R : ℕ) (θ : Fin R → ℝ) (c : Fin R → ℂ)
    (Δ : ℝ)
    (hΔ : ∀ r, (N : ℝ) + ∑ s ∈ Finset.univ.erase r,
      1 / (2 * nearestIntegerDistance (θ r - θ s)) ≤ Δ)
    (hsp : ∀ r s, r ≠ s → nearestIntegerDistance (θ r - θ s) ≠ 0) :
    (∑ n ∈ Finset.Ico M (M + N), ‖∑ r, c r * additiveCharacter (n * θ r)‖ ^ 2)
      ≤ Δ * ∑ r, ‖c r‖ ^ 2 := by
  convert additiveLargeSieve_rowbound M N R θ c Δ _ using 2
  intro r
  refine' le_trans _ (hΔ r)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ r), add_comm]
  exact add_le_add (by simp +decide [additiveCharacterKernel_zero])
    (Finset.sum_le_sum fun s hs => norm_additiveCharacterKernel_le M N _ <|
      hsp _ _ (Finset.mem_erase.mp hs).1.symm)

lemma nearestIntegerDistance_neg (a : ℝ) :
    nearestIntegerDistance (-a) = nearestIntegerDistance a := by
  unfold nearestIntegerDistance
  rw [abs_sub_round_eq_min, abs_sub_round_eq_min]
  by_cases h : Int.fract a = 0
  · rw [Int.fract_neg_eq_zero.mpr h, h]
  · rw [Int.fract_neg h, min_comm]
    ring_nf

end AdditiveCharacterGeometricSums
