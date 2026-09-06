import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Prime
import Mathlib.NumberTheory.Divisors
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Multiplicity of Restricted Divisors and Representation Counts

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

These lemmas establish elementary multiplicity bounds behind Matomäki–Radziwiłł Lemma 13:
1. `repCount_le`: The representation count `repCount A P ℓ n` of `n` as `m * p₁ * ⋯ * p_ℓ`
   with `m ∈ A` and `p_i ∈ P` is bounded by `ℓ! * (restrictedDivisors P n).card`.
2. `sum_sq_card_restrictedDivisors_le`: The sum of squares
   `∑ n ∈ (Y, 2Y], ((restrictedDivisors P n).card : ℝ)^2`
   is bounded by `2 * Real.exp 20 * Y + Real.exp 20`.
-/

open Finset

namespace Erdos1201.MR

/-- Divisors of `n` all of whose prime factors lie in the finset `P`. -/
def restrictedDivisors (P : Finset ℕ) (n : ℕ) : Finset ℕ :=
  n.divisors.filter (fun r => ∀ p ∈ r.primeFactors, p ∈ P)

/-- Number of representations n = m * p₁ * ⋯ * p_ℓ with m ∈ A and every p_i ∈ P. -/
def repCount (A P : Finset ℕ) (ℓ n : ℕ) : ℕ :=
  ((A ×ˢ Fintype.piFinset fun _ : Fin ℓ => P).filter (fun x => x.1 * ∏ i, x.2 i = n)).card

/-- A product of prime factors from `P` dividing `n` belongs to `restrictedDivisors P n`. -/
lemma prod_primes_mem_restrictedDivisors {P : Finset ℕ} {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p ∈ P, Nat.Prime p) {m : ℕ} {ℓ : ℕ} {p : Fin ℓ → ℕ}
    (hp : ∀ i, p i ∈ P) (hprod : m * ∏ i, p i = n) :
    (∏ i, p i) ∈ restrictedDivisors P n := by
  have hdvd : (∏ i, p i) ∣ n := ⟨m, by rw [mul_comm, hprod]⟩
  have hne : n ≠ 0 := ne_of_gt hn
  have hdiv : (∏ i, p i) ∈ n.divisors := Nat.mem_divisors.mpr ⟨hdvd, hne⟩
  rw [restrictedDivisors, Finset.mem_filter]
  refine ⟨hdiv, ?_⟩
  intro q hq
  rw [Nat.mem_primeFactors] at hq
  rcases hq with ⟨hq_prime, hq_dvd, -⟩
  rw [← List.prod_ofFn] at hq_dvd
  have h_prime_q : Prime q := Nat.Prime.prime hq_prime
  have h_all_prime : ∀ x ∈ List.ofFn p, Prime x := by
    intro x hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    exact Nat.Prime.prime (hprime (p i) (hp i))
  have hq_in : q ∈ List.ofFn p := mem_list_primes_of_dvd_prod h_prime_q h_all_prime hq_dvd
  rw [List.mem_ofFn] at hq_in
  rcases hq_in with ⟨i, rfl⟩
  exact hp i

/-- Bound on the number of representations `n = m * p₁ * ⋯ * p_ℓ` with `m ∈ A` and `p_i ∈ P`. -/
theorem repCount_le (A P : Finset ℕ) (ℓ n : ℕ) (hprime : ∀ p ∈ P, Nat.Prime p) (hn : 0 < n) :
    repCount A P ℓ n ≤ ℓ.factorial * (restrictedDivisors P n).card := by
  let S := (A ×ˢ Fintype.piFinset fun _ : Fin ℓ => P).filter (fun x => x.1 * ∏ i, x.2 i = n)
  let f : (ℕ × (Fin ℓ → ℕ)) → ℕ := fun x => ∏ i, x.2 i
  have Hf : ∀ a ∈ S, f a ∈ restrictedDivisors P n := by
    intro a ha
    rw [Finset.mem_filter] at ha
    rcases ha with ⟨ha1, ha2⟩
    rw [Finset.mem_product] at ha1
    rw [Fintype.mem_piFinset] at ha1
    exact prod_primes_mem_restrictedDivisors hn hprime (ha1.2) ha2
  have Hfib : ∀ b ∈ restrictedDivisors P n, (S.filter (fun a => f a = b)).card ≤ ℓ.factorial := by
    intro b hb
    rw [restrictedDivisors, Finset.mem_filter] at hb
    have hb_pos : 0 < b := Nat.pos_of_mem_divisors hb.1
    have hb_ne : b ≠ 0 := ne_of_gt hb_pos
    let Fb := S.filter (fun a => f a = b)
    change Fb.card ≤ ℓ.factorial
    by_cases hlen : b.primeFactorsList.length = ℓ
    · let g : (ℕ × (Fin ℓ → ℕ)) → List ℕ := fun a => List.ofFn a.2
      have hg_inj : Set.InjOn g Fb := by
        intro x hx y hy hxy
        rw [Finset.mem_coe, Finset.mem_filter] at hx hy
        have hx_f : f x = b := hx.2
        have hy_f : f y = b := hy.2
        have hx_eq : x.1 * b = n := by
          have h1 := hx.1
          rw [Finset.mem_filter] at h1
          rw [← hx_f]
          exact h1.2
        have hy_eq : y.1 * b = n := by
          have h1 := hy.1
          rw [Finset.mem_filter] at h1
          rw [← hy_f]
          exact h1.2
        have h1_eq : x.1 = y.1 := by
          apply Nat.eq_of_mul_eq_mul_right hb_pos
          rw [hx_eq, hy_eq]
        have h2_eq : x.2 = y.2 := List.ofFn_injective hxy
        exact Prod.ext h1_eq h2_eq
      have hg_maps : Set.MapsTo g Fb (b.primeFactorsList.permutations).toFinset := by
        intro a ha
        rw [Finset.mem_coe, Finset.mem_filter] at ha
        have ha_s := ha.1
        rw [Finset.mem_filter] at ha_s
        rw [Finset.mem_product] at ha_s
        rw [Fintype.mem_piFinset] at ha_s
        have ha_p : ∀ i, a.2 i ∈ P := ha_s.1.2
        have ha_prod : (List.ofFn a.2).prod = b := by
          rw [List.prod_ofFn]
          exact ha.2
        have ha_prime : ∀ q ∈ List.ofFn a.2, Nat.Prime q := by
          intro q hq
          rw [List.mem_ofFn] at hq
          rcases hq with ⟨i, rfl⟩
          exact hprime (a.2 i) (ha_p i)
        have hperm : (List.ofFn a.2).Perm b.primeFactorsList :=
          Nat.primeFactorsList_unique ha_prod ha_prime
        rw [Finset.mem_coe, List.mem_toFinset, List.mem_permutations]
        exact hperm
      have hcard_le : Fb.card ≤ ((b.primeFactorsList.permutations).toFinset).card :=
        Finset.card_le_card_of_injOn g hg_maps hg_inj
      have hcard_perm_le : ((b.primeFactorsList.permutations).toFinset).card ≤
          (b.primeFactorsList.permutations).length := List.toFinset_card_le _
      rw [List.length_permutations, hlen] at hcard_perm_le
      exact le_trans hcard_le hcard_perm_le
    · have h_not_mem : ∀ a, a ∉ Fb := by
        intro a ha
        rw [Finset.mem_filter] at ha
        have ha_s := ha.1
        rw [Finset.mem_filter] at ha_s
        rw [Finset.mem_product] at ha_s
        rw [Fintype.mem_piFinset] at ha_s
        have ha_p : ∀ i, a.2 i ∈ P := ha_s.1.2
        have ha_prod : (List.ofFn a.2).prod = b := by
          rw [List.prod_ofFn]
          exact ha.2
        have ha_prime : ∀ q ∈ List.ofFn a.2, Nat.Prime q := by
          intro q hq
          rw [List.mem_ofFn] at hq
          rcases hq with ⟨i, rfl⟩
          exact hprime (a.2 i) (ha_p i)
        have hperm : (List.ofFn a.2).Perm b.primeFactorsList :=
          Nat.primeFactorsList_unique ha_prod ha_prime
        have hlen_eq := hperm.length_eq
        rw [List.length_ofFn] at hlen_eq
        exact hlen hlen_eq.symm
      have h_empty : Fb = ∅ := by
        ext a
        simp [h_not_mem a]
      rw [h_empty, Finset.card_empty]
      exact Nat.zero_le _
  exact Finset.card_le_mul_card_image_of_maps_to Hf ℓ.factorial Hfib

/-- Upper bound on the number of multiples of `L` in an interval `(Y, 2Y]`. -/
lemma card_multiples_Ioc_le (Y : ℕ) {L : ℕ} (hL : 0 < L) :
    (((Ioc Y (2 * Y)).filter (fun n => L ∣ n)).card : ℝ) ≤ 2 * (Y : ℝ) / (L : ℝ) := by
  have hsub : ((Ioc Y (2 * Y)).filter (fun n => L ∣ n)) ⊆
      ((Ioc 0 (2 * Y)).filter (fun n => L ∣ n)) := by
    intro n hn
    simp only [mem_filter, mem_Ioc] at hn ⊢
    exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
  have hcard_le := card_le_card hsub
  have hcard_eq : ((Ioc 0 (2 * Y)).filter (fun n => L ∣ n)).card = (2 * Y) / L := by
    exact Nat.Ioc_filter_dvd_card_eq_div (2 * Y) L
  rw [hcard_eq] at hcard_le
  have h_le : ((2 * Y / L : ℕ) : ℝ) ≤ 2 * (Y : ℝ) / (L : ℝ) := by
    have h_div_le : (2 * Y / L : ℕ) * L ≤ 2 * Y := Nat.div_mul_le_self (2 * Y) L
    have h_div_le_real : ((2 * Y / L : ℕ) : ℝ) * (L : ℝ) ≤ 2 * (Y : ℝ) := by
      exact_mod_cast h_div_le
    have hL_pos : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
    exact (le_div_iff₀ hL_pos).mpr h_div_le_real
  exact (Nat.cast_le.mpr hcard_le).trans h_le

/-- Sum of reciprocals of primes in `[Y₁, 2Y₁]` is at most 2. -/
lemma sum_inv_primes_le_two (P : Finset ℕ) (Y₁ : ℕ) (hY : 2 ≤ Y₁)
    (hP : ∀ p ∈ P, Y₁ ≤ p ∧ p ≤ 2 * Y₁) :
    ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ 2 := by
  have hY_pos : 0 < (Y₁ : ℝ) := by positivity
  have hP_sub : P ⊆ Icc Y₁ (2 * Y₁) := by
    intro p hp
    rw [mem_Icc]
    exact hP p hp
  have hcard : P.card ≤ Y₁ + 1 := by
    have h1 : P.card ≤ (Icc Y₁ (2 * Y₁)).card := card_le_card hP_sub
    rw [Nat.card_Icc] at h1
    have h2 : 2 * Y₁ + 1 - Y₁ = Y₁ + 1 := by omega
    rwa [h2] at h1
  have hcard_le_two : P.card ≤ 2 * Y₁ := by omega
  have h_term_le : ∀ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ 1 / (Y₁ : ℝ) := by
    intro p hp
    have hp_ge := (hP p hp).1
    have hp_pos : 0 < (p : ℝ) := by
      have : 0 < p := by omega
      positivity
    exact one_div_le_one_div_of_le hY_pos (by exact_mod_cast hp_ge)
  have h_sum_le : ∑ p ∈ P, (1 : ℝ) / (p : ℝ) ≤ ∑ p ∈ P, (1 : ℝ) / (Y₁ : ℝ) :=
    sum_le_sum h_term_le
  rw [sum_const, nsmul_eq_mul] at h_sum_le
  have h_card_real : (P.card : ℝ) ≤ 2 * (Y₁ : ℝ) := by exact_mod_cast hcard_le_two
  have h_bound : (P.card : ℝ) * (1 / (Y₁ : ℝ)) ≤ (2 * (Y₁ : ℝ)) * (1 / (Y₁ : ℝ)) :=
    mul_le_mul_of_nonneg_right h_card_real (by positivity)
  have h_eq : (2 * (Y₁ : ℝ)) * (1 / (Y₁ : ℝ)) = 2 := by
    have : (Y₁ : ℝ) ≠ 0 := by positivity
    field_simp
  linarith

/-- Expressing the lcm of two `P`-supported numbers as a prime product with exponents `max`. -/
lemma prod_pow_max_eq_lcm (P : Finset ℕ)
    {r₁ r₂ : ℕ} (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hs₁ : r₁.primeFactors ⊆ P) (hs₂ : r₂.primeFactors ⊆ P) :
    ∏ p ∈ P, p ^ (max (r₁.factorization p) (r₂.factorization p)) = r₁.lcm r₂ := by
  have hlcm_ne : r₁.lcm r₂ ≠ 0 := Nat.lcm_ne_zero hr₁ hr₂
  have hlcm_fact := Nat.factorization_lcm hr₁ hr₂
  have hsup_sub : (r₁.lcm r₂).primeFactors ⊆ P := by
    rw [← Nat.support_factorization, hlcm_fact, Finsupp.support_sup]
    rw [Nat.support_factorization, Nat.support_factorization]
    exact union_subset hs₁ hs₂
  have hstep1 : ∏ p ∈ P, p ^ (max (r₁.factorization p) (r₂.factorization p)) =
      (r₁.lcm r₂).factorization.prod (fun x1 x2 => x1 ^ x2) := by
    rw [Finsupp.prod_of_support_subset (r₁.lcm r₂).factorization]
    · apply Finset.prod_congr rfl
      intro p _hp
      rw [hlcm_fact, Finsupp.sup_apply]
    · rw [Nat.support_factorization]
      exact hsup_sub
    · intro p _hp
      exact pow_zero p
  exact hstep1.trans (Nat.prod_factorization_pow_eq_self hlcm_ne)

/-- Closed form for the geometric-arithmetic sum `∑ (2k+1) / 2^(k-1)`. -/
lemma sum_linear_div_two_pow_eq : ∀ (K : ℕ), 1 ≤ K →
    ∑ k ∈ Ico 1 K, (2 * (k : ℝ) + 1) / (2 : ℝ) ^ (k - 1) =
    10 - (4 * (K : ℝ) + 6) / (2 : ℝ) ^ (K - 1) := by
  intro K
  induction K with
  | zero => intro h; omega
  | succ K ih =>
    intro hK
    by_cases h1 : K ≤ 1
    · interval_cases K
      · norm_num
      · have : Ico 1 2 = {1} := by decide
        rw [this, sum_singleton]
        norm_num
    · have h_prev : 1 ≤ K := by omega
      have h_insert : Ico 1 (K + 1) = insert K (Ico 1 K) := by
        exact Nat.Ico_succ_right_eq_insert_Ico h_prev
      rw [h_insert, sum_insert]
      · rw [ih h_prev]
        have hK_sub : K - 1 + 1 = K := by omega
        have hK1 : K + 1 - 1 = K := by omega
        have h2pow : (2 : ℝ) ^ K = (2 : ℝ) ^ (K - 1) * 2 := by
          have := @pow_succ ℝ _ 2 (K - 1)
          rwa [hK_sub] at this
        have h_pos : (2 : ℝ) ^ (K - 1) ≠ 0 := by positivity
        have h2 : (2 : ℝ) ≠ 0 := by norm_num
        rw [hK1, h2pow]
        field_simp
        push_cast
        ring
      · simp only [mem_Ico, lt_self_iff_false, and_false, not_false_iff]

/-- Numerical bound `∑ (2k+1) / 2^(k-1) ≤ 10`. -/
lemma sum_linear_div_two_pow_le (K : ℕ) :
    ∑ k ∈ Ico 1 K, (2 * (k : ℝ) + 1) / (2 : ℝ) ^ (k - 1) ≤ 10 := by
  by_cases hK : 1 ≤ K
  · rw [sum_linear_div_two_pow_eq K hK]
    have h_pos : 0 ≤ (4 * (K : ℝ) + 6) / (2 : ℝ) ^ (K - 1) := by positivity
    linarith
  · have : K = 0 := by omega
    subst this
    have : Ico 1 0 = ∅ := by decide
    rw [this, sum_empty]
    linarith

/-- Bounding `∑ (2k+1) / p^k ≤ exp(10 / p)` for any base `p ≥ 2`. -/
lemma sum_range_two_mul_add_one_div_pow_le (K : ℕ) {p : ℕ} (hp : 2 ≤ p) :
    ∑ k ∈ range K, (2 * (k : ℝ) + 1) / (p : ℝ) ^ k ≤ Real.exp (10 / (p : ℝ)) := by
  by_cases hK : K = 0
  · subst hK
    simp only [range_zero, sum_empty]
    positivity
  have hK_pos : 1 ≤ K := by omega
  have h_split : range K = insert 0 (Ico 1 K) := by
    ext x
    simp only [mem_range, mem_insert, mem_Ico]
    omega
  rw [h_split, sum_insert]
  · simp only [Nat.cast_zero, mul_zero, zero_add, pow_zero, div_one]
    have hp_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    have hp_pos : 0 < (p : ℝ) := by positivity
    have h_term_le : ∀ k ∈ Ico 1 K, (2 * (k : ℝ) + 1) / (p : ℝ) ^ k ≤
        (1 / (p : ℝ)) * ((2 * (k : ℝ) + 1) / (2 : ℝ) ^ (k - 1)) := by
      intro k hk
      rw [mem_Ico] at hk
      have hk1 : 1 ≤ k := hk.1
      have hpk : (p : ℝ) ^ k = (p : ℝ) * (p : ℝ) ^ (k - 1) := by
        have : k = (k - 1) + 1 := by omega
        nth_rw 1 [this]
        rw [pow_succ, mul_comm]
      have h2k : (2 : ℝ) ^ (k - 1) ≤ (p : ℝ) ^ (k - 1) := by
        exact pow_le_pow_left₀ (by norm_num) hp_real (k - 1)
      have hpos2 : 0 < (2 : ℝ) ^ (k - 1) := by positivity
      have hposp : 0 < (p : ℝ) ^ (k - 1) := by positivity
      rw [hpk]
      have : (2 * (k : ℝ) + 1) / ((p : ℝ) * (p : ℝ) ^ (k - 1)) =
          (1 / (p : ℝ)) * ((2 * (k : ℝ) + 1) / (p : ℝ) ^ (k - 1)) := by ring
      rw [this]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine div_le_div_of_nonneg_left (by positivity) hpos2 h2k
    have h_sum_le := sum_le_sum h_term_le
    rw [← mul_sum] at h_sum_le
    have h_ten := sum_linear_div_two_pow_le K
    have h_bound : (1 / (p : ℝ)) * (∑ k ∈ Ico 1 K, (2 * (k : ℝ) + 1) / (2 : ℝ) ^ (k - 1)) ≤
        (1 / (p : ℝ)) * 10 := mul_le_mul_of_nonneg_left h_ten (by positivity)
    have h_ten_div : (1 / (p : ℝ)) * 10 = 10 / (p : ℝ) := by ring
    rw [h_ten_div] at h_bound
    have h_trans := le_trans h_sum_le h_bound
    have h_exp := Real.add_one_le_exp (10 / (p : ℝ))
    linarith
  · intro h
    rw [mem_Ico] at h
    omega

/-- Size of the fiber `{ab ∈ range K × range K | max a b = k}` is `2k + 1`. -/
lemma card_fiber_max_eq (K : ℕ) {k : ℕ} (hk : k < K) :
    ({ab ∈ range K ×ˢ range K | max ab.1 ab.2 = k}).card = 2 * k + 1 := by
  have heq : {ab ∈ range K ×ˢ range K | max ab.1 ab.2 = k} =
      ({k} ×ˢ range k) ∪ (Iic k ×ˢ {k}) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product, mem_range, mem_union, mem_singleton, mem_Iic]
    constructor
    · rintro ⟨⟨ha, hb⟩, hmax⟩
      have hak : a ≤ k := by omega
      have hbk : b ≤ k := by omega
      by_cases h : b = k
      · right
        exact ⟨hak, h⟩
      · left
        have : a = k := by omega
        exact ⟨this, by omega⟩
    · rintro (⟨rfl, hb⟩ | ⟨ha, rfl⟩)
      · refine ⟨⟨by omega, by omega⟩, by omega⟩
      · refine ⟨⟨by omega, by omega⟩, by omega⟩
  rw [heq]
  have hdisj : Disjoint ({k} ×ˢ range k) (Iic k ×ˢ {k}) := by
    rw [disjoint_iff_ne]
    rintro ⟨a₁, b₁⟩ h1 ⟨a₂, b₂⟩ h2
    simp only [mem_product, mem_singleton, mem_range, mem_Iic] at h1 h2
    intro heq
    injection heq with _ hb_eq
    omega
  rw [card_union_of_disjoint hdisj]
  simp [Nat.card_Iic]
  omega

/-- Converting a double sum over `range K × range K` with `max` to a single sum weighted by `2k + 1`. -/
lemma sum_max_eq_sum_fiber (K : ℕ) (f : ℕ → ℝ) :
    ∑ ab ∈ range K ×ˢ range K, f (max ab.1 ab.2) =
    ∑ k ∈ range K, (2 * (k : ℝ) + 1) * f k := by
  have hmaps : ∀ ab ∈ range K ×ˢ range K, max ab.1 ab.2 ∈ range K := by
    intro ⟨a, b⟩ hab
    simp only [mem_product, mem_range] at hab ⊢
    exact max_lt hab.1 hab.2
  have hfib := sum_fiberwise_of_maps_to hmaps (fun ab => f (max ab.1 ab.2))
  rw [← hfib]
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have h_const : ∀ ab ∈ {ab ∈ range K ×ˢ range K | max ab.1 ab.2 = k},
      f (max ab.1 ab.2) = f k := by
    intro ab hab
    rw [mem_filter] at hab
    rw [hab.2]
  rw [sum_congr rfl h_const, sum_const, nsmul_eq_mul]
  have hcard := card_fiber_max_eq K hk
  rw [hcard]
  push_cast
  ring

/-- Numbers supported on `P` are uniquely determined by their factorization exponents on `P`. -/
lemma factorization_eq_of_support_subset {P : Finset ℕ} {r₁ r₂ : ℕ}
    (hr₁ : r₁ ≠ 0) (hr₂ : r₂ ≠ 0)
    (hs₁ : r₁.primeFactors ⊆ P) (hs₂ : r₂.primeFactors ⊆ P)
    (heq : ∀ p ∈ P, r₁.factorization p = r₂.factorization p) : r₁ = r₂ := by
  have hfact : r₁.factorization = r₂.factorization := by
    ext q
    by_cases hq : q ∈ P
    · exact heq q hq
    · have hq1 : q ∉ r₁.factorization.support := by
        rw [Nat.support_factorization]
        intro h
        exact hq (hs₁ h)
      have hq2 : q ∉ r₂.factorization.support := by
        rw [Nat.support_factorization]
        intro h
        exact hq (hs₂ h)
      have e1 : r₁.factorization q = 0 := by
        by_contra hc
        exact hq1 (Finsupp.mem_support_iff.mpr hc)
      have e2 : r₂.factorization q = 0 := by
        by_contra hc
        exact hq2 (Finsupp.mem_support_iff.mpr hc)
      rw [e1, e2]
  exact Nat.factorization_inj hr₁ hr₂ hfact

/-- The prime exponent `r.factorization p` is bounded by `r`. -/
lemma factorization_le_self {p r : ℕ} (hp : 2 ≤ p) (hr : 0 < r) :
    r.factorization p ≤ r := by
  by_cases hmem : p ∈ r.primeFactors
  · have hprod : r = ∏ q ∈ r.primeFactors, q ^ (r.factorization q) := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors]
      exact (Nat.prod_factorization_pow_eq_self (ne_of_gt hr)).symm
    have hdvd : p ^ (r.factorization p) ∣ r := by
      nth_rw 2 [hprod]
      exact Finset.dvd_prod_of_mem (fun q => q ^ (r.factorization q)) hmem
    have hle : p ^ (r.factorization p) ≤ r := Nat.le_of_dvd hr hdvd
    have h2p : 2 ^ (r.factorization p) ≤ p ^ (r.factorization p) :=
      Nat.pow_le_pow_left hp (r.factorization p)
    have hlin : r.factorization p ≤ 2 ^ (r.factorization p) :=
      Nat.le_of_lt (Nat.lt_pow_self (show 1 < 2 by omega))
    omega
  · have h0 : r.factorization p = 0 := by
      rw [← Nat.support_factorization] at hmem
      exact Finsupp.notMem_support_iff.mp hmem
    omega

/-- Expanding the square of cardinality as a double sum over pairs. -/
lemma card_sq_eq_sum_sum (s : Finset ℕ) : (s.card : ℝ) ^ 2 = ∑ _r₁ ∈ s, ∑ _r₂ ∈ s, (1 : ℝ) := by
  simp only [sum_const, nsmul_eq_mul, mul_one]
  ring

/-- Bounding the sum of squares of restricted divisor counts by an lcm reciprocal sum. -/
lemma sum_sq_card_restrictedDivisors_le_sum_lcm (P : Finset ℕ) (Y : ℕ) :
    let I := Ioc Y (2 * Y)
    let S := (Ioc 0 (2 * Y)).filter (fun r => ∀ p ∈ r.primeFactors, p ∈ P)
    (∑ n ∈ I, ((restrictedDivisors P n).card : ℝ) ^ 2) ≤
    2 * (Y : ℝ) * ∑ r₁ ∈ S, ∑ r₂ ∈ S, 1 / (r₁.lcm r₂ : ℝ) := by
  intro I S
  by_cases hY : 1 ≤ Y
  · have h_rd_eq : ∀ n ∈ I, restrictedDivisors P n = S.filter (fun r => r ∣ n) := by
      intro n hn
      rw [mem_Ioc] at hn
      ext r
      simp only [restrictedDivisors, mem_filter, Nat.mem_divisors, mem_Ioc, S]
      constructor
      · rintro ⟨⟨hr_dvd, -⟩, hr_P⟩
        have hr_pos : 0 < r := by
          have : r ≠ 0 := by rintro rfl; omega
          omega
        have hr_le : r ≤ 2 * Y := by
          have : r ≤ n := Nat.le_of_dvd (by omega) hr_dvd
          omega
        exact ⟨⟨⟨hr_pos, hr_le⟩, hr_P⟩, hr_dvd⟩
      · rintro ⟨⟨⟨_hr_pos, -⟩, hr_P⟩, hr_dvd⟩
        have hn_ne : n ≠ 0 := by omega
        exact ⟨⟨hr_dvd, hn_ne⟩, hr_P⟩
    have h_sq : ∀ n ∈ I, ((restrictedDivisors P n).card : ℝ) ^ 2 =
        ∑ r₁ ∈ S, ∑ r₂ ∈ S, if r₁ ∣ n ∧ r₂ ∣ n then (1 : ℝ) else 0 := by
      intro n hn
      rw [h_rd_eq n hn]
      rw [card_sq_eq_sum_sum]
      rw [sum_filter]
      apply sum_congr rfl
      intro r₁ _
      rw [sum_filter]
      by_cases hr₁ : r₁ ∣ n
      · simp only [hr₁, ite_true]
        apply sum_congr rfl
        intro r₂ _
        simp
      · simp only [hr₁, ite_false, false_and]
        simp
    have h_sum_interchange : (∑ n ∈ I, ((restrictedDivisors P n).card : ℝ) ^ 2) =
        ∑ r₁ ∈ S, ∑ r₂ ∈ S, ∑ n ∈ I, if r₁ ∣ n ∧ r₂ ∣ n then (1 : ℝ) else 0 := by
      calc
        (∑ n ∈ I, ((restrictedDivisors P n).card : ℝ) ^ 2) =
            ∑ n ∈ I, ∑ r₁ ∈ S, ∑ r₂ ∈ S, if r₁ ∣ n ∧ r₂ ∣ n then (1 : ℝ) else 0 := by
          apply sum_congr rfl h_sq
        _ = ∑ r₁ ∈ S, ∑ n ∈ I, ∑ r₂ ∈ S, if r₁ ∣ n ∧ r₂ ∣ n then (1 : ℝ) else 0 := sum_comm
        _ = ∑ r₁ ∈ S, ∑ r₂ ∈ S, ∑ n ∈ I, if r₁ ∣ n ∧ r₂ ∣ n then (1 : ℝ) else 0 := by
          apply sum_congr rfl
          intro r₁ _
          exact sum_comm
    rw [h_sum_interchange]
    have h_term_le : ∀ r₁ ∈ S, ∀ r₂ ∈ S,
        (∑ n ∈ I, if r₁ ∣ n ∧ r₂ ∣ n then (1 : ℝ) else 0) ≤ 2 * (Y : ℝ) * (1 / (r₁.lcm r₂ : ℝ)) := by
      intro r₁ hr₁ r₂ hr₂
      rw [mem_filter, mem_Ioc] at hr₁ hr₂
      have hr₁_pos : 0 < r₁ := hr₁.1.1
      have hlcm_pos : 0 < r₁.lcm r₂ := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (ne_of_gt hr₁_pos) (ne_of_gt hr₂.1.1))
      have h_filter : (∑ n ∈ I, if r₁ ∣ n ∧ r₂ ∣ n then (1 : ℝ) else 0) =
          (((I.filter (fun n => r₁.lcm r₂ ∣ n)).card : ℝ)) := by
        rw [← sum_filter]
        simp only [sum_const, nsmul_eq_mul, mul_one]
        have hext : (I.filter (fun n => r₁ ∣ n ∧ r₂ ∣ n)) = (I.filter (fun n => r₁.lcm r₂ ∣ n)) := by
          ext n
          simp only [mem_filter, Nat.lcm_dvd_iff]
        rw [hext]
      rw [h_filter]
      have h_bound := card_multiples_Ioc_le Y hlcm_pos
      have : 2 * (Y : ℝ) / (r₁.lcm r₂ : ℝ) = 2 * (Y : ℝ) * (1 / (r₁.lcm r₂ : ℝ)) := by ring
      rwa [this] at h_bound
    have h_sum_le1 : (∑ r₁ ∈ S, ∑ r₂ ∈ S, ∑ n ∈ I, if r₁ ∣ n ∧ r₂ ∣ n then (1 : ℝ) else 0) ≤
        ∑ r₁ ∈ S, ∑ r₂ ∈ S, 2 * (Y : ℝ) * (1 / (r₁.lcm r₂ : ℝ)) := by
      apply sum_le_sum
      intro r₁ hr₁
      apply sum_le_sum
      intro r₂ hr₂
      exact h_term_le r₁ hr₁ r₂ hr₂
    have h_factor : (∑ r₁ ∈ S, ∑ r₂ ∈ S, 2 * (Y : ℝ) * (1 / (r₁.lcm r₂ : ℝ))) =
        2 * (Y : ℝ) * ∑ r₁ ∈ S, ∑ r₂ ∈ S, 1 / (r₁.lcm r₂ : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r₁ _
      rw [mul_sum]
    rwa [h_factor] at h_sum_le1
  · have : Y = 0 := by omega
    subst this
    have : I = ∅ := by
      ext x
      simp [I]
    rw [this, sum_empty]
    simp

/-- Bounding the double sum of `1 / lcm(r₁, r₂)` over `P`-supported numbers by `exp(20)`. -/
lemma sum_lcm_inv_le_exp_twenty (P : Finset ℕ) (Y₁ : ℕ) (hY : 2 ≤ Y₁)
    (hP : ∀ p ∈ P, Y₁ ≤ p ∧ p ≤ 2 * Y₁) (Y : ℕ) :
    let S := (Ioc 0 (2 * Y)).filter (fun r => ∀ p ∈ r.primeFactors, p ∈ P)
    (∑ r₁ ∈ S, ∑ r₂ ∈ S, 1 / (r₁.lcm r₂ : ℝ)) ≤ Real.exp 20 := by
  intro S
  let K := 2 * Y + 1
  let t := Fintype.piFinset (fun (_ : P) => range K ×ˢ range K)
  let e : ℕ × ℕ → (P → ℕ × ℕ) := fun x (p : P) =>
    (x.1.factorization p.1, x.2.factorization p.1)
  let g : (P → ℕ × ℕ) → ℝ := fun w =>
    ∏ p : P, 1 / (p.1 : ℝ) ^ (max (w p).1 (w p).2)
  have he : Set.InjOn e ↑(S ×ˢ S) := by
    rintro ⟨r₁, r₂⟩ hr ⟨s₁, s₂⟩ hs heq
    rw [mem_coe, mem_product] at hr hs
    have hr₁_in := hr.1
    have hr₂_in := hr.2
    have hs₁_in := hs.1
    have hs₂_in := hs.2
    rw [mem_filter, mem_Ioc] at hr₁_in hr₂_in hs₁_in hs₂_in
    have hr₁_ne : r₁ ≠ 0 := ne_of_gt hr₁_in.1.1
    have hr₂_ne : r₂ ≠ 0 := ne_of_gt hr₂_in.1.1
    have hs₁_ne : s₁ ≠ 0 := ne_of_gt hs₁_in.1.1
    have hs₂_ne : s₂ ≠ 0 := ne_of_gt hs₂_in.1.1
    have hr₁_P : r₁.primeFactors ⊆ P := hr₁_in.2
    have hr₂_P : r₂.primeFactors ⊆ P := hr₂_in.2
    have hs₁_P : s₁.primeFactors ⊆ P := hs₁_in.2
    have hs₂_P : s₂.primeFactors ⊆ P := hs₂_in.2
    have heq1 : ∀ p ∈ P, r₁.factorization p = s₁.factorization p := by
      intro p hp
      have := congr_fun heq ⟨p, hp⟩
      exact (Prod.ext_iff.mp this).1
    have heq2 : ∀ p ∈ P, r₂.factorization p = s₂.factorization p := by
      intro p hp
      have := congr_fun heq ⟨p, hp⟩
      exact (Prod.ext_iff.mp this).2
    have e1 := factorization_eq_of_support_subset hr₁_ne hs₁_ne hr₁_P hs₁_P heq1
    have e2 := factorization_eq_of_support_subset hr₂_ne hs₂_ne hr₂_P hs₂_P heq2
    exact Prod.ext e1 e2
  have ht : image e (S ×ˢ S) ⊆ t := by
    intro w hw
    rw [mem_image] at hw
    rcases hw with ⟨⟨r₁, r₂⟩, hr, rfl⟩
    rw [mem_product] at hr
    have hr₁_in := hr.1
    have hr₂_in := hr.2
    rw [mem_filter, mem_Ioc] at hr₁_in hr₂_in
    rw [Fintype.mem_piFinset]
    intro p
    simp only [mem_product, mem_range]
    have hp_ge : 2 ≤ p.1 := by
      have := (hP p.1 p.2).1
      omega
    have hr₁_pos : 0 < r₁ := hr₁_in.1.1
    have hr₂_pos : 0 < r₂ := hr₂_in.1.1
    have h1 := factorization_le_self hp_ge hr₁_pos
    have h2 := factorization_le_self hp_ge hr₂_pos
    have hr₁_le : r₁ ≤ 2 * Y := hr₁_in.1.2
    have hr₂_le : r₂ ≤ 2 * Y := hr₂_in.1.2
    dsimp [e]
    refine ⟨by omega, by omega⟩
  have h_prod_cast : ∀ x ∈ S ×ˢ S, (x.1.lcm x.2 : ℝ) =
      ∏ p : P, (p.1 : ℝ) ^ (max (e x p).1 (e x p).2) := by
    rintro ⟨r₁, r₂⟩ hr
    rw [mem_product] at hr
    have hr₁_in := hr.1
    have hr₂_in := hr.2
    rw [mem_filter, mem_Ioc] at hr₁_in hr₂_in
    have hr₁_ne : r₁ ≠ 0 := ne_of_gt hr₁_in.1.1
    have hr₂_ne : r₂ ≠ 0 := ne_of_gt hr₂_in.1.1
    have hr₁_P : r₁.primeFactors ⊆ P := hr₁_in.2
    have hr₂_P : r₂.primeFactors ⊆ P := hr₂_in.2
    have hlcm := prod_pow_max_eq_lcm P hr₁_ne hr₂_ne hr₁_P hr₂_P
    rw [← hlcm]
    push_cast
    rw [← prod_attach]
    rfl
  have h_le_g : ∀ x ∈ S ×ˢ S, 1 / (x.1.lcm x.2 : ℝ) ≤ g (e x) := by
    intro x hx
    rw [h_prod_cast x hx]
    dsimp [g]
    rw [one_div, ← prod_inv_distrib]
    apply le_of_eq
    apply prod_congr rfl
    intro p _
    rw [one_div]
  have hg_nonneg : ∀ a ∈ t, a ∉ image e (S ×ˢ S) → 0 ≤ g a := by
    intro a _ _
    dsimp [g]
    positivity
  have h_sum_le := sum_le_sum_of_injOn e he ht h_le_g hg_nonneg
  have h_sum_prod : (∑ r₁ ∈ S, ∑ r₂ ∈ S, 1 / (r₁.lcm r₂ : ℝ)) =
      ∑ i ∈ S ×ˢ S, 1 / (i.1.lcm i.2 : ℝ) :=
    (sum_product S S (fun x : ℕ × ℕ => 1 / ((x.1.lcm x.2 : ℕ) : ℝ))).symm
  rw [h_sum_prod]
  have h_prod_sum : (∑ a ∈ t, g a) =
      ∏ p : P, ∑ ab ∈ range K ×ˢ range K, 1 / (p.1 : ℝ) ^ (max ab.1 ab.2) := by
    dsimp [g, t]
    exact (prod_univ_sum (fun (_ : P) => range K ×ˢ range K)
      (fun (p : P) ab => 1 / (p.1 : ℝ) ^ (max ab.1 ab.2))).symm
  have h_factor_le : ∀ p : P,
      (∑ ab ∈ range K ×ˢ range K, 1 / (p.1 : ℝ) ^ (max ab.1 ab.2)) ≤ Real.exp (10 / (p.1 : ℝ)) := by
    intro p
    have h_fiber := sum_max_eq_sum_fiber K (fun m => 1 / (p.1 : ℝ) ^ m)
    rw [h_fiber]
    have h_div : (∑ k ∈ range K, (2 * (k : ℝ) + 1) * (1 / (p.1 : ℝ) ^ k)) =
        ∑ k ∈ range K, (2 * (k : ℝ) + 1) / (p.1 : ℝ) ^ k := by
      apply sum_congr rfl
      intro k _
      ring
    rw [h_div]
    have hp_ge : 2 ≤ p.1 := by
      have := (hP p.1 p.2).1
      omega
    exact sum_range_two_mul_add_one_div_pow_le K hp_ge
  have h_prod_le : (∏ p : P, ∑ ab ∈ range K ×ˢ range K, 1 / (p.1 : ℝ) ^ (max ab.1 ab.2)) ≤
      ∏ p : P, Real.exp (10 / (p.1 : ℝ)) := by
    apply prod_le_prod
    · intro p _
      positivity
    · intro p _
      exact h_factor_le p
  have h_exp_prod : (∏ p : P, Real.exp (10 / (p.1 : ℝ))) = Real.exp (∑ p ∈ P, 10 / (p : ℝ)) := by
    rw [← Real.exp_sum]
    congr 1
    exact sum_coe_sort P (fun p => 10 / (p : ℝ))
  have h_exp_sum_le : Real.exp (∑ p ∈ P, 10 / (p : ℝ)) ≤ Real.exp 20 := by
    rw [Real.exp_le_exp]
    have h_factor_ten : (∑ p ∈ P, 10 / (p : ℝ)) = 10 * ∑ p ∈ P, 1 / (p : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p _
      ring
    rw [h_factor_ten]
    have h_prime_sum := sum_inv_primes_le_two P Y₁ hY hP
    linarith
  linarith [h_sum_le, h_prod_sum, h_prod_le, h_exp_prod, h_exp_sum_le]

/-- Bound on the sum of squares of restricted divisor counts over short intervals `(Y, 2Y]`. -/
theorem sum_sq_card_restrictedDivisors_le (P : Finset ℕ) (Y₁ : ℕ) (hY : 2 ≤ Y₁)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hP : ∀ p ∈ P, Y₁ ≤ p ∧ p ≤ 2 * Y₁) (Y : ℕ) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), ((restrictedDivisors P n).card : ℝ) ^ 2) ≤
    2 * Real.exp 20 * Y + Real.exp 20 := by
  have _ := hprime
  have h1 := sum_sq_card_restrictedDivisors_le_sum_lcm P Y
  have h2 := sum_lcm_inv_le_exp_twenty P Y₁ hY hP Y
  have h_nonneg : 0 ≤ 2 * (Y : ℝ) := by positivity
  have h_mul := mul_le_mul_of_nonneg_left h2 h_nonneg
  have h_exp_pos : 0 < Real.exp 20 := Real.exp_pos 20
  linarith


end Erdos1201.MR
