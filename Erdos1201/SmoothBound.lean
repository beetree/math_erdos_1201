import Erdos1201.AnalyticInputs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Smooth Number Upper Bound

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This file formalizes the deduction of `SmoothUpperInput` from a Mertens-type
prime-sum lower bound.
-/

open Finset Filter
open scoped Nat.Prime BigOperators Topology Filter

namespace Erdos1201

/-- Primes in the window `(⌊X^γ⌋₊, X]`. -/
noncomputable def primeRange (γ : ℝ) (X : ℕ) : Finset ℕ :=
  (Ioc ⌊(X : ℝ) ^ γ⌋₊ X).filter Nat.Prime

/-- Multiples of `p` in `(X, 2X]` count exactly `(2X)/p - X/p`. -/
theorem card_Ioc_filter_dvd {X p : ℕ} :
    ((Ioc X (2 * X)).filter (fun x => p ∣ x)).card = (2 * X) / p - X / p := by
  have h_union : Ioc 0 (2 * X) = Ioc 0 X ∪ Ioc X (2 * X) := by
    rw [Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
  have h_disj : Disjoint ((Ioc 0 X).filter (fun x => p ∣ x)) ((Ioc X (2 * X)).filter (fun x => p ∣ x)) := by
    rw [disjoint_left]
    intro x h1 h2
    simp only [mem_filter, mem_Ioc] at h1 h2
    omega
  have h_filt : (Ioc 0 (2 * X)).filter (fun x => p ∣ x) =
      ((Ioc 0 X).filter (fun x => p ∣ x)) ∪ ((Ioc X (2 * X)).filter (fun x => p ∣ x)) := by
    rw [h_union, filter_union]
  have h_card := card_union_of_disjoint h_disj
  rw [← h_filt, Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at h_card
  omega

/-- The number of multiples in `(X, 2X]` is at most one more than in `[X, 2X)`. -/
theorem card_Ico_filter_dvd_ge {X p : ℕ} :
    ((Ioc X (2 * X)).filter (fun x => p ∣ x)).card ≤
      ((Ico X (2 * X)).filter (fun x => p ∣ x)).card + 1 := by
  have hsub : (Ioc X (2 * X)).filter (fun x => p ∣ x) ⊆
      insert (2 * X) ((Ico X (2 * X)).filter (fun x => p ∣ x)) := by
    intro x hx
    simp only [mem_filter, mem_Ioc, mem_insert, mem_Ico] at hx ⊢
    rcases hx with ⟨⟨hX, h2X⟩, hp⟩
    by_cases h : x = 2 * X
    · left; exact h
    · right; exact ⟨⟨le_of_lt hX, lt_of_le_of_ne h2X h⟩, hp⟩
  have hcard := card_le_card hsub
  have hcard2 := card_insert_le (2 * X) ((Ico X (2 * X)).filter (fun x => p ∣ x))
  omega

/-- Real lower bound for the difference of integer divisions: `(2X)/p - X/p ≥ X/p - 1`. -/
theorem nat_div_sub_div_ge (X : ℕ) {p : ℕ} (hp : 0 < p) :
    ((X : ℝ) / p) - 1 ≤ (((2 * X / p : ℕ) : ℝ) - ((X / p : ℕ) : ℝ)) := by
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have h1 : 2 * X < (2 * X / p + 1) * p := by
    have h := Nat.div_add_mod (2 * X) p
    have hmod := Nat.mod_lt (2 * X) hp
    rw [add_mul, one_mul, mul_comm (2 * X / p) p]
    omega
  have h2 : (X / p) * p ≤ X := Nat.div_mul_le_self X p
  have h1_real : (2 * X : ℝ) < (((2 * X / p : ℕ) : ℝ) + 1) * (p : ℝ) := by
    have : (2 * X : ℝ) < (((2 * X / p + 1 : ℕ) : ℝ) * (p : ℝ)) := by exact_mod_cast h1
    push_cast at this
    exact this
  have h2_real : ((X / p : ℕ) : ℝ) * (p : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast h2
  have h3 : (2 * X : ℝ) / (p : ℝ) - 1 ≤ ((2 * X / p : ℕ) : ℝ) := by
    rw [div_sub_one (ne_of_gt hp_pos), div_le_iff₀ hp_pos]
    linarith
  have h4 : ((X / p : ℕ) : ℝ) ≤ (X : ℝ) / (p : ℝ) := by
    rw [le_div_iff₀ hp_pos]
    linarith
  have h5 : (2 * X : ℝ) / (p : ℝ) = 2 * ((X : ℝ) / (p : ℝ)) := by
    ring
  linarith

/-- Multiples of `p` in `[X, 2X)` number at least `X/p - 2`. -/
theorem card_Ico_filter_dvd_lower_bound (X : ℕ) {p : ℕ} (hp : 0 < p) :
    (X : ℝ) / p - 2 ≤ (((Ico X (2 * X)).filter (fun x => p ∣ x)).card : ℝ) := by
  have h1 := card_Ico_filter_dvd_ge (X := X) (p := p)
  have h2 := card_Ioc_filter_dvd (X := X) (p := p)
  have h3 := nat_div_sub_div_ge X hp
  have hsub : (((2 * X / p - X / p : ℕ) : ℝ)) = ((2 * X / p : ℕ) : ℝ) - ((X / p : ℕ) : ℝ) :=
    Nat.cast_sub (Nat.div_le_div_right (by omega))
  have h_card_real : (((Ioc X (2 * X)).filter (fun x => p ∣ x)).card : ℝ) ≤
      (((Ico X (2 * X)).filter (fun x => p ∣ x)).card : ℝ) + 1 := by
    exact_mod_cast h1
  rw [h2, hsub] at h_card_real
  linarith

/-- A positive integer with a prime factor in `primeRange γ X` is not `X^β`-smooth if `β ≤ γ`. -/
theorem not_smooth_of_mem_primeRange {X : ℕ} (hX : 1 ≤ X) {β γ : ℝ} (hβγ : β ≤ γ)
    {p : ℕ} (hp : p ∈ primeRange γ X) {n : ℕ} (hdiv : p ∣ n) :
    ¬ Smooth ((X : ℝ) ^ β) n := by
  intro hs
  have hp_prime : p.Prime := (mem_filter.mp hp).2
  have hp_ioc : p ∈ Ioc ⌊(X : ℝ) ^ γ⌋₊ X := (mem_filter.mp hp).1
  have hp_gt_floor : ⌊(X : ℝ) ^ γ⌋₊ < p := (mem_Ioc.mp hp_ioc).1
  have hX_pos : 0 ≤ (X : ℝ) := by positivity
  have h_rpow_pos : 0 ≤ (X : ℝ) ^ γ := Real.rpow_nonneg hX_pos γ
  have hp_gt : (X : ℝ) ^ γ < (p : ℝ) := (Nat.floor_lt h_rpow_pos).mp hp_gt_floor
  have hp_le : (p : ℝ) ≤ (X : ℝ) ^ β := hs.2 p hp_prime hdiv
  have h_exp : (X : ℝ) ^ β ≤ (X : ℝ) ^ γ := by
    have : 1 ≤ (X : ℝ) := by exact_mod_cast hX
    exact Real.rpow_le_rpow_of_exponent_le this hβγ
  linarith

/-- For `X ≥ 4` and `γ ≥ 3/4`, the product of any two primes in `primeRange γ X` exceeds `2X`. -/
theorem prime_mul_gt_two_mul {X : ℕ} (hX : 4 ≤ X) {γ : ℝ} (hγ : 3/4 ≤ γ)
    {p q : ℕ} (hp : p ∈ primeRange γ X) (hq : q ∈ primeRange γ X) :
    2 * (X : ℝ) < (p * q : ℝ) := by
  have hX_ge4 : (4 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hX_pos : 0 < (X : ℝ) := by linarith
  have hX_ge1 : 1 ≤ (X : ℝ) := by linarith
  have hp_ioc := (mem_filter.mp hp).1
  have hq_ioc := (mem_filter.mp hq).1
  have hp_gt_floor := (mem_Ioc.mp hp_ioc).1
  have hq_gt_floor := (mem_Ioc.mp hq_ioc).1
  have h_rpow_pos : 0 ≤ (X : ℝ) ^ γ := Real.rpow_nonneg (by linarith) γ
  have hp_gt : (X : ℝ) ^ γ < (p : ℝ) := (Nat.floor_lt h_rpow_pos).mp hp_gt_floor
  have hq_gt : (X : ℝ) ^ γ < (q : ℝ) := (Nat.floor_lt h_rpow_pos).mp hq_gt_floor
  have hpq_gt : (X : ℝ) ^ γ * (X : ℝ) ^ γ < (p : ℝ) * (q : ℝ) := by nlinarith
  have h_add : (X : ℝ) ^ γ * (X : ℝ) ^ γ = (X : ℝ) ^ (γ + γ) := by
    rw [← Real.rpow_add hX_pos]
  have h_two_gamma : 3/2 ≤ γ + γ := by linarith
  have h_rpow_ge : (X : ℝ) ^ (3/2 : ℝ) ≤ (X : ℝ) ^ (γ + γ) :=
    Real.rpow_le_rpow_of_exponent_le hX_ge1 h_two_gamma
  have h_split : (X : ℝ) ^ (3/2 : ℝ) = (X : ℝ) * (X : ℝ) ^ (1/2 : ℝ) := by
    have : (3/2 : ℝ) = 1 + 1/2 := by norm_num
    rw [this, Real.rpow_add hX_pos, Real.rpow_one]
  have h_sqrt : (2 : ℝ) ≤ (X : ℝ) ^ (1/2 : ℝ) := by
    have h4 : (4 : ℝ) ^ (1/2 : ℝ) ≤ (X : ℝ) ^ (1/2 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hX_ge4 (by norm_num)
    have h4_val : (4 : ℝ) ^ (1/2 : ℝ) = 2 := by
      rw [← Real.sqrt_eq_rpow]
      norm_num
    linarith
  have h_2X_le : 2 * (X : ℝ) ≤ (X : ℝ) ^ (3/2 : ℝ) := by
    rw [h_split]
    nlinarith
  linarith

/-- For `X ≥ 4`, `γ ≥ 3/4` and `n ∈ [X, 2X)`, at most one prime in `primeRange γ X` divides `n`. -/
theorem card_filter_primeRange_dvd_le_one {X : ℕ} (hX : 4 ≤ X) {γ : ℝ} (hγ : 3/4 ≤ γ)
    {n : ℕ} (hn : n ∈ Ico X (2 * X)) :
    ((primeRange γ X).filter (fun p => p ∣ n)).card ≤ 1 := by
  by_contra! h
  rcases Finset.one_lt_card_iff.mp h with ⟨p, q, hp, hq, hpq⟩
  simp only [mem_filter] at hp hq
  have hp_prime : p.Prime := (mem_filter.mp hp.1).2
  have hq_prime : q.Prime := (mem_filter.mp hq.1).2
  have hcoprime : Nat.Coprime p q := (Nat.coprime_primes hp_prime hq_prime).mpr hpq
  have hmul_dvd : p * q ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcoprime hp.2 hq.2
  have hn_pos : 0 < n := by
    have := (mem_Ico.mp hn).1
    omega
  have hpq_le_n : p * q ≤ n := Nat.le_of_dvd hn_pos hmul_dvd
  have hn_lt : n < 2 * X := (mem_Ico.mp hn).2
  have h_prod_lt : (p * q : ℝ) < 2 * (X : ℝ) := by
    have : (p * q : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpq_le_n
    have : (n : ℝ) < (2 * X : ℝ) := by exact_mod_cast hn_lt
    linarith
  have h_prod_gt := prime_mul_gt_two_mul hX hγ hp.1 hq.1
  linarith

/-- The sum of divisibility indicators over a set of primes equals the cardinality of divisors. -/
theorem sum_indicator_dvd_eq_card (s : Finset ℕ) (n : ℕ) :
    (∑ p ∈ s, (if p ∣ n then (1 : ℝ) else 0)) = ((s.filter (fun p => p ∣ n)).card : ℝ) := by
  rw [← sum_filter]
  simp

/-- Pointwise inequality bounding the smooth indicator by `1 - ∑ (p ∣ n)`. -/
theorem smoothIndicator_le_one_sub_sum_div {X : ℕ} {β γ : ℝ} {n : ℕ}
    (h_card : ((primeRange γ X).filter (fun p => p ∣ n)).card ≤ 1)
    (h_not_smooth : ∀ p ∈ primeRange γ X, p ∣ n → ¬ Smooth ((X : ℝ) ^ β) n) :
    smoothIndicator ((X : ℝ) ^ β) n ≤ 1 - ∑ p ∈ primeRange γ X, (if p ∣ n then (1 : ℝ) else 0) := by
  rw [sum_indicator_dvd_eq_card]
  by_cases hs : Smooth ((X : ℝ) ^ β) n
  · have : (primeRange γ X).filter (fun p => p ∣ n) = ∅ := by
      rw [filter_eq_empty_iff]
      intro p hp hp_dvd
      exact h_not_smooth p hp hp_dvd hs
    rw [this, card_empty, Nat.cast_zero]
    simp [smoothIndicator, hs]
  · simp only [smoothIndicator, hs, ↓reduceIte]
    have : ((primeRange γ X).filter (fun p => p ∣ n)).card = 0 ∨
           ((primeRange γ X).filter (fun p => p ∣ n)).card = 1 := by omega
    rcases this with h0 | h1
    · rw [h0]
      norm_num
    · rw [h1]
      norm_num

/-- Sum of constant 1 over `Ico X (2 * X)` is `X`. -/
theorem sum_const_ico (X : ℕ) : (∑ _n ∈ Ico X (2 * X), (1 : ℝ)) = (X : ℝ) := by
  simp only [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  congr 1
  omega

/-- Swapping summation of prime divisibility indicators over `n ∈ Ico X (2 * X)`. -/
theorem sum_indicator_dvd_swap (s : Finset ℕ) (X : ℕ) :
    (∑ n ∈ Ico X (2 * X), ∑ p ∈ s, (if p ∣ n then (1 : ℝ) else 0)) =
    ∑ p ∈ s, (((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) := by
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  rw [← sum_filter]
  simp

/-- Lower bound for the sum over primes of the number of multiples in `Ico X (2 * X)`. -/
theorem sum_dvd_card_lower_bound (γ : ℝ) (X : ℕ)
    (h_bound : ∀ p ∈ primeRange γ X, (X : ℝ) / p - 2 ≤ (((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ)) :
    (X : ℝ) * (∑ p ∈ primeRange γ X, (1 : ℝ) / p) - 2 * ((primeRange γ X).card : ℝ) ≤
      ∑ p ∈ primeRange γ X, (((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) := by
  have hsum : (∑ p ∈ primeRange γ X, ((X : ℝ) / p - 2)) ≤
      ∑ p ∈ primeRange γ X, (((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) :=
    sum_le_sum h_bound
  have heq : (∑ p ∈ primeRange γ X, ((X : ℝ) / p - 2)) =
      (X : ℝ) * (∑ p ∈ primeRange γ X, (1 : ℝ) / p) - 2 * ((primeRange γ X).card : ℝ) := by
    rw [sum_sub_distrib]
    have h_div : (∑ p ∈ primeRange γ X, (X : ℝ) / p) = (X : ℝ) * (∑ p ∈ primeRange γ X, (1 : ℝ) / p) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    have h_const : (∑ _p ∈ primeRange γ X, (2 : ℝ)) = 2 * ((primeRange γ X).card : ℝ) := by
      simp only [sum_const, nsmul_eq_mul]
      ring
    rw [h_div, h_const]
  linarith

/-- Block mean bound deduced from a sum bound over `Ico X (2 * X)`. -/
theorem blockMean_le_formula {X : ℕ} (hX : 0 < X) {β : ℝ} {S_p : ℝ} {card_P : ℝ}
    (h_sum : (∑ n ∈ Ico X (2 * X), smoothIndicator ((X : ℝ) ^ β) n) ≤
      (X : ℝ) * (1 - S_p) + 2 * card_P) :
    blockMean (smoothIndicator ((X : ℝ) ^ β)) X ≤ 1 - S_p + 2 * (card_P / (X : ℝ)) := by
  rw [blockMean]
  have hX_pos : 0 < (X : ℝ) := Nat.cast_pos.mpr hX
  have : (∑ n ∈ Ico X (2 * X), smoothIndicator ((X : ℝ) ^ β) n) / (X : ℝ) ≤
      ((X : ℝ) * (1 - S_p) + 2 * card_P) / (X : ℝ) :=
    div_le_div_of_nonneg_right h_sum (le_of_lt hX_pos)
  have h_alg : ((X : ℝ) * (1 - S_p) + 2 * card_P) / (X : ℝ) = 1 - S_p + 2 * (card_P / (X : ℝ)) := by
    calc
      ((X : ℝ) * (1 - S_p) + 2 * card_P) / (X : ℝ) =
        ((X : ℝ) * (1 - S_p)) / (X : ℝ) + (2 * card_P) / (X : ℝ) := add_div _ _ _
      _ = (1 - S_p) + 2 * (card_P / (X : ℝ)) := by
        rw [mul_div_cancel_left₀ (1 - S_p) (ne_of_gt hX_pos)]
        ring
  linarith

/-- The primes in `primeRange γ X` are a subset of all primes up to `X`. -/
theorem primeRange_subset_primesLE (γ : ℝ) (X : ℕ) :
    primeRange γ X ⊆ Nat.primesLE X := by
  intro p hp
  simp only [primeRange, mem_filter, mem_Ioc] at hp
  rw [Nat.mem_primesLE]
  exact ⟨hp.1.2, hp.2⟩

/-- The cardinality of `primeRange γ X` is at most the prime-counting function `π X`. -/
theorem card_primeRange_le_primeCounting (γ : ℝ) (X : ℕ) :
    (primeRange γ X).card ≤ Nat.primeCounting X := by
  have h := card_le_card (primeRange_subset_primesLE γ X)
  rw [Nat.primesLE_card_eq_primeCounting] at h
  exact h

/-- By Chebyshev's bound, `π(X) / X` is eventually bounded by any positive constant. -/
theorem eventually_primeCounting_div_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, (Nat.primeCounting X : ℝ) / (X : ℝ) ≤ ε := by
  have h_cheb_real := Chebyshev.eventually_primeCounting_le (by norm_num : 0 < (1 : ℝ))
  have h_cheb_nat := tendsto_natCast_atTop_atTop.eventually h_cheb_real
  have h_log_tendsto : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_div_tendsto : Tendsto (fun X : ℕ => (Real.log 4 + 1) / Real.log (X : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop h_log_tendsto
  have h_div_le := Tendsto.eventually_le_const hε h_div_tendsto
  have h_X_ge1 : ∀ᶠ X : ℕ in atTop, 1 ≤ X := eventually_ge_atTop 1
  filter_upwards [h_cheb_nat, h_div_le, h_X_ge1] with X h_cheb h_div hX1
  simp only [Nat.floor_natCast] at h_cheb
  have hX_pos : 0 < (X : ℝ) := by
    have : 1 ≤ (X : ℝ) := by exact_mod_cast hX1
    linarith
  have h_div_X : (Nat.primeCounting X : ℝ) / (X : ℝ) ≤ (Real.log 4 + 1) / Real.log (X : ℝ) := by
    have h_rw : ((Real.log 4 + 1) * (X : ℝ) / Real.log (X : ℝ)) / (X : ℝ) =
        (Real.log 4 + 1) / Real.log (X : ℝ) := by
      rw [mul_div_right_comm, mul_div_cancel_right₀ _ (ne_of_gt hX_pos)]
    rw [← h_rw]
    exact div_le_div_of_nonneg_right h_cheb (le_of_lt hX_pos)
  exact h_div_X.trans h_div

/-- Deduction of `SmoothUpperInput` from a Mertens-type prime sum lower bound. -/
theorem smoothUpperInput_of_primeSums
    (hprimes : ∀ γ : ℝ, 0 < γ → γ < 1 → ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in Filter.atTop,
      c ≤ ∑ p ∈ (Finset.Ioc ⌊(X : ℝ) ^ γ⌋₊ X).filter Nat.Prime, (1 : ℝ) / p) :
    SmoothUpperInput := by
  intro β hβ_pos hβ_lt1
  set γ : ℝ := max β (3/4) with hγ_def
  have hγ_pos : 0 < γ := by
    have : 0 < (3/4 : ℝ) := by norm_num
    exact lt_of_lt_of_le this (le_max_right β (3/4))
  have hγ_lt1 : γ < 1 := max_lt hβ_lt1 (by norm_num)
  have hβγ : β ≤ γ := le_max_left β (3/4)
  have hγ_ge : 3/4 ≤ γ := le_max_right β (3/4)
  rcases hprimes γ hγ_pos hγ_lt1 with ⟨c0, hc0_pos, h_primes_ev⟩
  have hε_pos : 0 < c0 / 4 := by linarith
  have h_pi_ev := eventually_primeCounting_div_le hε_pos
  have h_X4_ev : ∀ᶠ X : ℕ in atTop, 4 ≤ X := eventually_ge_atTop 4
  refine ⟨1 - c0 / 2, by linarith, ?_⟩
  filter_upwards [h_primes_ev, h_pi_ev, h_X4_ev] with X h_sum_primes h_pi hX4
  have hX_pos : 0 < X := by omega
  have h_sum_bound : (∑ n ∈ Ico X (2 * X), smoothIndicator ((X : ℝ) ^ β) n) ≤
      (X : ℝ) * (1 - (∑ p ∈ primeRange γ X, (1 : ℝ) / p)) + 2 * ((primeRange γ X).card : ℝ) := by
    have h_ptwise : ∀ n ∈ Ico X (2 * X),
        smoothIndicator ((X : ℝ) ^ β) n ≤ 1 - ∑ p ∈ primeRange γ X, (if p ∣ n then (1 : ℝ) else 0) := by
      intro n hn
      have h1 := card_filter_primeRange_dvd_le_one hX4 hγ_ge hn
      have h2 : ∀ p ∈ primeRange γ X, p ∣ n → ¬ Smooth ((X : ℝ) ^ β) n := by
        intro p hp hp_dvd
        exact not_smooth_of_mem_primeRange (by omega) hβγ hp hp_dvd
      exact smoothIndicator_le_one_sub_sum_div h1 h2
    have h_sum_le := sum_le_sum h_ptwise
    rw [sum_sub_distrib, sum_const_ico X, sum_indicator_dvd_swap] at h_sum_le
    have h_lower : (X : ℝ) * (∑ p ∈ primeRange γ X, (1 : ℝ) / p) - 2 * ((primeRange γ X).card : ℝ) ≤
        ∑ p ∈ primeRange γ X, (((Ico X (2 * X)).filter (fun n => p ∣ n)).card : ℝ) := by
      apply sum_dvd_card_lower_bound
      intro p hp
      have hp_prime : p.Prime := (mem_filter.mp hp).2
      exact card_Ico_filter_dvd_lower_bound X hp_prime.pos
    linarith
  have h_bm := blockMean_le_formula hX_pos h_sum_bound
  have h_card_le : ((primeRange γ X).card : ℝ) ≤ (Nat.primeCounting X : ℝ) := by
    exact_mod_cast card_primeRange_le_primeCounting γ X
  have hX_real_pos : 0 < (X : ℝ) := Nat.cast_pos.mpr hX_pos
  have h_card_div : ((primeRange γ X).card : ℝ) / (X : ℝ) ≤ (Nat.primeCounting X : ℝ) / (X : ℝ) :=
    div_le_div_of_nonneg_right h_card_le (le_of_lt hX_real_pos)
  have h_P_primes : (∑ p ∈ primeRange γ X, (1 : ℝ) / p) =
      ∑ p ∈ (Ioc ⌊(X : ℝ) ^ γ⌋₊ X).filter Nat.Prime, (1 : ℝ) / p := rfl
  rw [h_P_primes] at h_bm
  linarith

end Erdos1201
