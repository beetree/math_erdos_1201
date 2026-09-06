import Mathlib
import Erdos1201.Vendor.NumberTheory.HalberstamRichertMeanValue.ExplicitMeanValueBound
import Erdos1201.MR.Sieve.RangeSieveUpper

/-!
# Range Sieve Upper Bound via Halberstam–Richert

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the range sieve upper bound without restrictions on $Q/P$,
using the explicit Halberstam–Richert mean value theorem (`ExplicitMeanValueBound`)
combined with Mertens' product theorems for prime ranges (`RangeSieveUpper`).

## Mathematical Note on the Hypothesis $Q \le X$ / $Q \le 2X$

The original unrestricted statement without any bound relating $Q$ and $X$ is false:
for fixed $X = 4$ and $P = 3$, the integer $n = 8 \in (4, 8]$ has only the prime factor $2 < P$,
so $8$ has no prime factor in $[3, Q]$ for any $Q \ge 3$. Hence the sifted count is at least $1$
for all $Q \ge 3$. However, $C \cdot X \cdot \frac{\log P}{\log Q} \to 0$ as $Q \to \infty$,
which would force $1 \le 0$ for large $Q$. Therefore, an upper bound on $Q$ (such as $Q \le 2X$
or $Q \le X$) is mathematically necessary and natural in sieve applications where $Q \le X$.

## Main Results

- `card_no_prime_factor_in_Icc_le_hr_two_mul`: The sieve upper bound with $Q \le 2X$.
- `card_no_prime_factor_in_Icc_le_hr`: The sieve upper bound with $Q \le X$.
- `card_no_prime_factor_in_Icc_le_hr'`: Variant with hypothesis order `2 ≤ X → Q ≤ X`.
-/

open Classical Real

namespace Erdos1201.MR

/-- Predicate stating that `n` has no prime factor in the closed interval $[P, Q]$. -/
def noPrimeFactorInRange (P Q n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → P ≤ p → p ≤ Q → ¬ p ∣ n

/-- Multiplicative indicator for having no prime factor in $[P, Q]$, with $h(0) = 0$. -/
noncomputable def hrIndicator (P Q : ℕ) (n : ℕ) : ℝ :=
  if n = 0 then 0
  else if noPrimeFactorInRange P Q n then 1 else 0

/-- The indicator vanishes at 0. -/
lemma hrIndicator_zero (P Q : ℕ) : hrIndicator P Q 0 = 0 := by
  simp [hrIndicator]

/-- The indicator equals 1 at 1. -/
lemma hrIndicator_one (P Q : ℕ) : hrIndicator P Q 1 = 1 := by
  simp only [hrIndicator, one_ne_zero, ↓reduceIte]
  have h : noPrimeFactorInRange P Q 1 := by
    intro p hp _ _ hdiv
    have hp1 := Nat.dvd_one.mp hdiv
    subst hp1
    exact Nat.not_prime_one hp
  simp [h]

/-- The indicator is always nonnegative. -/
lemma hrIndicator_nonneg (P Q n : ℕ) : 0 ≤ hrIndicator P Q n := by
  simp only [hrIndicator]
  split_ifs <;> norm_num

/-- The indicator is bounded above by 1. -/
lemma hrIndicator_le_one (P Q n : ℕ) : hrIndicator P Q n ≤ 1 := by
  simp only [hrIndicator]
  split_ifs <;> norm_num

/-- Multiplicativity of the prime-factor avoidance predicate for nonzero integers. -/
lemma noPrimeFactorInRange_mul {P Q m n : ℕ} (_hm : m ≠ 0) (_hn : n ≠ 0) :
    noPrimeFactorInRange P Q (m * n) ↔
      noPrimeFactorInRange P Q m ∧ noPrimeFactorInRange P Q n := by
  constructor
  · intro h
    constructor
    · intro p hp hP hpQ hpm
      exact h p hp hP hpQ (dvd_mul_of_dvd_left hpm n)
    · intro p hp hP hpQ hpn
      exact h p hp hP hpQ (dvd_mul_of_dvd_right hpn m)
  · rintro ⟨hm1, hn1⟩ p hp hP hpQ hpmn
    rw [hp.dvd_mul] at hpmn
    rcases hpmn with hpm | hpn
    · exact hm1 p hp hP hpQ hpm
    · exact hn1 p hp hP hpQ hpn

/-- The indicator is multiplicative on coprime integers. -/
lemma hrIndicator_mul (P Q : ℕ) {m n : ℕ} (_hmn : m.Coprime n) :
    hrIndicator P Q (m * n) = hrIndicator P Q m * hrIndicator P Q n := by
  by_cases hm : m = 0
  · subst hm
    simp [hrIndicator_zero]
  by_cases hn : n = 0
  · subst hn
    simp [hrIndicator_zero]
  have hmn_prod : m * n ≠ 0 := mul_ne_zero hm hn
  simp only [hrIndicator, hm, hn, hmn_prod, ↓reduceIte]
  rw [noPrimeFactorInRange_mul hm hn]
  by_cases h1 : noPrimeFactorInRange P Q m <;> by_cases h2 : noPrimeFactorInRange P Q n <;> simp [h1, h2]

/-- Prime power bound $h(p^\nu) \le 1 \cdot 1^\nu$ for the indicator. -/
lemma hrIndicator_pow_le (P Q : ℕ) (p : ℕ) (_hp : p.Prime) (_nu : ℕ) :
    hrIndicator P Q (p ^ _nu) ≤ 1 * 1 ^ _nu := by
  simp only [mul_one, one_pow]
  exact hrIndicator_le_one P Q (p ^ _nu)

/-- The sifted count in $(X, 2X]$ is bounded by the Halberstam–Richert partial sum. -/
lemma card_filter_noPrimeFactorInRange_le_partialSum (X P Q : ℕ) (hX : 2 ≤ X) :
    (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ) ≤
      HalberstamRichertMeanValue.partialSum (hrIndicator P Q) (2 * X) := by
  have h_sub : (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n) ⊆
      Finset.Icc 1 (2 * X) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_Icc]
    exact ⟨by omega, hn.1.2⟩
  have h_ind_eq : ∀ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n),
      hrIndicator P Q n = 1 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hn_ne : n ≠ 0 := by
      have : X < n := (Finset.mem_Ioc.mp hn.1).1
      omega
    have h_no : noPrimeFactorInRange P Q n := hn.2
    simp [hrIndicator, hn_ne, h_no]
  calc (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ)
    _ = ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n), (1 : ℝ) := by
      simp
    _ = ∑ n ∈ (Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n), hrIndicator P Q n := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      rw [h_ind_eq n hn]
    _ ≤ ∑ n ∈ Finset.Icc 1 (2 * X), hrIndicator P Q n :=
      Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun n _ _ => hrIndicator_nonneg P Q n)
    _ = HalberstamRichertMeanValue.partialSum (hrIndicator P Q) (2 * X) := rfl

/-- For primes $p \in [P, Q]$, the local factor in the Euler product is 1. -/
lemma tsum_local_factor_of_in_range {P Q p : ℕ} (hp : p.Prime) (hPin : P ≤ p) (hQin : p ≤ Q) :
    (∑' j : ℕ, hrIndicator P Q (p ^ j) / ((p ^ j : ℕ) : ℝ)) = 1 := by
  have hj_pos : ∀ j : ℕ, 1 ≤ j → hrIndicator P Q (p ^ j) / ((p ^ j : ℕ) : ℝ) = 0 := by
    intro j hj
    have hpj_ne : p ^ j ≠ 0 := pow_ne_zero j hp.ne_zero
    have hnot : ¬ noPrimeFactorInRange P Q (p ^ j) := by
      intro h
      have hdvd : p ∣ p ^ j := dvd_pow_self p (by omega)
      exact h p hp hPin hQin hdvd
    simp only [hrIndicator, hpj_ne, ↓reduceIte, hnot]
    ring
  have heq : (fun j : ℕ => hrIndicator P Q (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      (fun j => if j = 0 then (1 : ℝ) else 0) := by
    ext j
    cases j with
    | zero =>
      simp only [pow_zero, Nat.cast_one, div_one, ite_true]
      exact hrIndicator_one P Q
    | succ j =>
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      exact hj_pos (j + 1) (by omega)
  rw [heq]
  exact tsum_ite_eq 0 (fun _ : ℕ => (1 : ℝ))

/-- For primes $p \notin [P, Q]$, the local factor in the Euler product is $(1 - 1/p)^{-1}$. -/
lemma tsum_local_factor_of_not_in_range {P Q p : ℕ} (hp : p.Prime) (hnot : ¬ (P ≤ p ∧ p ≤ Q)) :
    (∑' j : ℕ, hrIndicator P Q (p ^ j) / ((p ^ j : ℕ) : ℝ)) = (1 - 1 / (p : ℝ))⁻¹ := by
  have hp_pos : 0 < (p : ℝ) := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have h_ind : ∀ j : ℕ, hrIndicator P Q (p ^ j) = 1 := by
    intro j
    cases j with
    | zero => exact hrIndicator_one P Q
    | succ j =>
      have hpj_ne : p ^ (j + 1) ≠ 0 := pow_ne_zero (j + 1) hp.ne_zero
      simp only [hrIndicator, hpj_ne, ↓reduceIte]
      have h : noPrimeFactorInRange P Q (p ^ (j + 1)) := by
        intro q hq hP hQ hdvd
        have hqp : q ∣ p := hq.dvd_of_dvd_pow hdvd
        rcases (Nat.dvd_prime hp).mp hqp with hq1 | hq_eq_p
        · subst hq1; exact False.elim (Nat.not_prime_one hq)
        · subst hq_eq_p
          exact hnot ⟨hP, hQ⟩
      simp [h]
  have hterm : (fun j : ℕ => hrIndicator P Q (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      (fun j => (1 / (p : ℝ)) ^ j) := by
    ext j
    rw [h_ind j]
    push_cast
    rw [one_div_pow]
  rw [hterm]
  have hr_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
  have hr_lt_one : 1 / (p : ℝ) < 1 := by
    rw [div_lt_one hp_pos]
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  rw [tsum_geometric_of_lt_one hr_nonneg hr_lt_one]

/-- Uniform formula for the local Euler factor at any prime $p$. -/
lemma local_factor_eq (P Q p : ℕ) (hp : p.Prime) :
    (∑' j : ℕ, hrIndicator P Q (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      (1 - 1 / (p : ℝ))⁻¹ * (if P ≤ p ∧ p ≤ Q then (1 - 1 / (p : ℝ)) else 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hne : 1 - 1 / (p : ℝ) ≠ 0 := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  split_ifs with h
  · rw [tsum_local_factor_of_in_range hp h.1 h.2, inv_mul_cancel₀ hne]
  · rw [tsum_local_factor_of_not_in_range hp h, mul_one]

/-- The primes strictly below $N + 1$ are precisely the primes $\le N$. -/
lemma primesBelow_succ_eq_primesLE (N : ℕ) : (N + 1).primesBelow = N.primesLE := by
  ext p
  simp [Nat.primesBelow, Nat.primesLE]

/-- Upper bound on the inverse product $\prod_{p \le N} (1 - 1/p)^{-1}$ from Mertens' theorem. -/
lemma prod_inv_primesLE_le {N : ℕ} (hN : 2 ≤ N) :
    ∏ p ∈ N.primesLE, (1 - 1 / (p : ℝ))⁻¹ ≤
      exp (eulerMascheroniConstant + E_const) * log ((N : ℕ) : ℝ) := by
  have hN2 : 1 < ((N : ℕ) : ℝ) := by
    have : (2 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hN
    linarith
  have hlogN_pos : 0 < log ((N : ℕ) : ℝ) := log_pos hN2
  have h_lower := prod_prime_one_minus_inv_primesLE_ge hN
  have hc0_pos : 0 < exp (-eulerMascheroniConstant) * exp (-E_const) := by positivity
  have h_frac_pos : 0 < exp (-eulerMascheroniConstant) * exp (-E_const) / log ((N : ℕ) : ℝ) :=
    div_pos hc0_pos hlogN_pos
  rw [Finset.prod_inv_distrib]
  have h_inv_le : (∏ p ∈ N.primesLE, (1 - 1 / (p : ℝ)))⁻¹ ≤
      (exp (-eulerMascheroniConstant) * exp (-E_const) / log ((N : ℕ) : ℝ))⁻¹ :=
    inv_anti₀ h_frac_pos h_lower
  refine h_inv_le.trans ?_
  have h1 : (exp (-eulerMascheroniConstant))⁻¹ = exp eulerMascheroniConstant := by
    rw [← exp_neg, neg_neg]
  have h2 : (exp (-E_const))⁻¹ = exp E_const := by
    rw [← exp_neg, neg_neg]
  calc (exp (-eulerMascheroniConstant) * exp (-E_const) / log ((N : ℕ) : ℝ))⁻¹
    _ = log ((N : ℕ) : ℝ) / (exp (-eulerMascheroniConstant) * exp (-E_const)) := inv_div _ _
    _ = exp (eulerMascheroniConstant + E_const) * log ((N : ℕ) : ℝ) := by
      rw [div_eq_mul_inv, mul_inv, h1, h2, ← exp_add]
      ring
    _ ≤ exp (eulerMascheroniConstant + E_const) * log ((N : ℕ) : ℝ) := le_rfl

/-- Rewrite of the indicator product into the range prime product when $Q \le N$. -/
lemma prod_ite_one_minus_inv_eq {P Q N : ℕ} (hQN : Q ≤ N) :
    (∏ p ∈ N.primesLE, (if P ≤ p ∧ p ≤ Q then (1 - 1 / (p : ℝ)) else 1)) =
      ∏ p ∈ (Finset.Icc P Q).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
  have h_eq : (Finset.Icc P Q).filter Nat.Prime =
      N.primesLE.filter (fun p => P ≤ p ∧ p ≤ Q) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨hP, hpQ⟩, hprime⟩
      exact ⟨⟨hpQ.trans hQN, hprime⟩, ⟨hP, hpQ⟩⟩
    · rintro ⟨⟨_, hprime⟩, ⟨hP, hpQ⟩⟩
      exact ⟨⟨hP, hpQ⟩, hprime⟩
  rw [h_eq]
  rw [← Finset.prod_filter]

/-- Range sieve upper bound via Halberstam–Richert under the hypothesis $Q \le 2X$:
for an absolute constant $C > 0$, the number of integers in $(X, 2X]$ with no prime factor
in $[P, Q]$ is bounded by $C X \frac{\log P}{\log Q}$. -/
theorem card_no_prime_factor_in_Icc_le_hr_two_mul :
    ∃ C : ℝ, 0 < C ∧ ∀ (X P Q : ℕ), 2 ≤ P → P ≤ Q → Q ≤ 2 * X → 2 ≤ X →
      (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ) ≤
        C * X * Real.log P / Real.log Q := by
  rcases prod_prime_one_minus_inv_range_le with ⟨C_mert, hC_mert_pos, h_range⟩
  let C_hr := 2 * (HalberstamRichertMeanValue.explicitMassConstant 1 1 + 1) *
    exp (eulerMascheroniConstant + E_const) * C_mert
  have hK_nonneg : 0 ≤ HalberstamRichertMeanValue.explicitMassConstant 1 1 :=
    HalberstamRichertMeanValue.explicitMassConstant_nonneg (zero_le_one : (0 : ℝ) ≤ 1) (zero_le_one : (0 : ℝ) ≤ 1)
  have hK_pos : 0 < HalberstamRichertMeanValue.explicitMassConstant 1 1 + 1 := by linarith
  have he_pos : 0 < exp (eulerMascheroniConstant + E_const) := exp_pos _
  have hC_hr_pos : 0 < C_hr :=
    mul_pos (mul_pos (mul_pos (by norm_num) hK_pos) he_pos) hC_mert_pos
  use C_hr, hC_hr_pos
  intro X P Q hP hPQ hQ2X hX
  have hN_ge : 2 ≤ 2 * X := by omega
  have hlogN_pos : 0 < log (((2 * X : ℕ) : ℝ)) := log_pos (by
    have : (2 : ℝ) ≤ (((2 * X : ℕ) : ℝ)) := by exact_mod_cast hN_ge
    linarith)
  have hlogN_ne : log (((2 * X : ℕ) : ℝ)) ≠ 0 := hlogN_pos.ne'
  have hlogQ_pos : 0 < log (Q : ℝ) := log_pos (by
    have : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (hP.trans hPQ)
    linarith)
  have hlogQ_ne : log (Q : ℝ) ≠ 0 := hlogQ_pos.ne'
  have hcard_le := card_filter_noPrimeFactorInRange_le_partialSum X P Q hX
  have hhr := ExplicitMeanValueBound.halberstam_richert_explicit_source_indexing
    (hrIndicator P Q)
    (hrIndicator_zero P Q)
    (hrIndicator_one P Q)
    (fun {_m _n} hmn => hrIndicator_mul P Q hmn)
    (hrIndicator_nonneg P Q)
    1 1
    (by norm_num) (by norm_num) (by norm_num)
    (fun p hp nu => hrIndicator_pow_le P Q p hp nu)
    (2 * X) hN_ge
  rw [mul_one] at hhr
  rw [primesBelow_succ_eq_primesLE] at hhr
  have hprod_split : (∏ p ∈ (2 * X).primesLE, ∑' j : ℕ, hrIndicator P Q (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
      (∏ p ∈ (2 * X).primesLE, (1 - 1 / (p : ℝ))⁻¹) *
      (∏ p ∈ (Finset.Icc P Q).filter Nat.Prime, (1 - 1 / (p : ℝ))) := by
    have hstep1 : (∏ p ∈ (2 * X).primesLE, ∑' j : ℕ, hrIndicator P Q (p ^ j) / ((p ^ j : ℕ) : ℝ)) =
        ∏ p ∈ (2 * X).primesLE,
          ((1 - 1 / (p : ℝ))⁻¹ * (if P ≤ p ∧ p ≤ Q then (1 - 1 / (p : ℝ)) else 1)) := by
      refine Finset.prod_congr rfl ?_
      intro p hp
      exact local_factor_eq P Q p (Nat.mem_primesLE.mp hp).2
    rw [hstep1, Finset.prod_mul_distrib]
    congr 1
    exact prod_ite_one_minus_inv_eq hQ2X
  rw [hprod_split] at hhr
  have h_inv_le := prod_inv_primesLE_le hN_ge
  have h_range_le := h_range P Q hP hPQ
  have h_range_nonneg : 0 ≤ ∏ p ∈ (Finset.Icc P Q).filter Nat.Prime, (1 - 1 / (p : ℝ)) := by
    refine Finset.prod_nonneg ?_
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2.two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
    linarith
  have h_prod_bound : (∏ p ∈ (2 * X).primesLE, (1 - 1 / (p : ℝ))⁻¹) *
      (∏ p ∈ (Finset.Icc P Q).filter Nat.Prime, (1 - 1 / (p : ℝ))) ≤
      (exp (eulerMascheroniConstant + E_const) * log (((2 * X : ℕ) : ℝ))) *
      (C_mert * Real.log (P : ℝ) / Real.log (Q : ℝ)) :=
    mul_le_mul h_inv_le h_range_le h_range_nonneg (by positivity)
  have hK_nonneg' : 0 ≤ (HalberstamRichertMeanValue.explicitMassConstant 1 1 + 1) * (((2 * X : ℕ) : ℝ)) / Real.log (((2 * X : ℕ) : ℝ)) := by
    positivity
  have hhr_comb := mul_le_mul_of_nonneg_left h_prod_bound hK_nonneg'
  have hhr_trans := hhr.trans hhr_comb
  refine hcard_le.trans (hhr_trans.trans ?_)
  have h_cast : (((2 * X : ℕ) : ℝ)) = 2 * (X : ℝ) := by push_cast; ring
  have h_cancel :
      ((HalberstamRichertMeanValue.explicitMassConstant 1 1 + 1) * (((2 * X : ℕ) : ℝ)) / Real.log (((2 * X : ℕ) : ℝ))) *
      ((exp (eulerMascheroniConstant + E_const) * Real.log (((2 * X : ℕ) : ℝ))) *
      (C_mert * Real.log (P : ℝ) / Real.log (Q : ℝ))) =
      C_hr * (X : ℝ) * Real.log (P : ℝ) / Real.log (Q : ℝ) := by
    dsimp [C_hr]
    set L := Real.log (((2 * X : ℕ) : ℝ))
    have hL_ne : L ≠ 0 := hlogN_ne
    rw [h_cast]
    field_simp [hL_ne, hlogQ_ne]
  rw [h_cancel]

/-- Sieve upper bound for integers with no prime factor in $[P, Q]$
under the hypothesis $Q \le X$:
for an absolute constant $C > 0$, the number of integers in $(X, 2X]$ with no prime factor
in $[P, Q]$ is bounded by $C X \frac{\log P}{\log Q}$. -/
theorem card_no_prime_factor_in_Icc_le_hr :
    ∃ C : ℝ, 0 < C ∧ ∀ (X P Q : ℕ), 2 ≤ P → P ≤ Q → Q ≤ X → 2 ≤ X →
      (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ) ≤
        C * X * Real.log P / Real.log Q := by
  rcases card_no_prime_factor_in_Icc_le_hr_two_mul with ⟨C, hC, h⟩
  refine ⟨C, hC, ?_⟩
  intro X P Q hP hPQ hQX hX
  have hQ2X : Q ≤ 2 * X := by omega
  exact h X P Q hP hPQ hQ2X hX

/-- Variant of `card_no_prime_factor_in_Icc_le_hr` with hypothesis order `2 ≤ X → Q ≤ X`. -/
theorem card_no_prime_factor_in_Icc_le_hr' :
    ∃ C : ℝ, 0 < C ∧ ∀ (X P Q : ℕ), 2 ≤ P → P ≤ Q → 2 ≤ X → Q ≤ X →
      (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p, Nat.Prime p → P ≤ p → p ≤ Q → ¬ p ∣ n)).card : ℝ) ≤
        C * X * Real.log P / Real.log Q := by
  rcases card_no_prime_factor_in_Icc_le_hr with ⟨C, hC, h⟩
  exact ⟨C, hC, fun X P Q hP hPQ hX hQX => h X P Q hP hPQ hQX hX⟩

end Erdos1201.MR
