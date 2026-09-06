import Mathlib

/-!
# Rankin's Upper Bound on Smooth Number Reciprocal Tails

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This file formalizes Rankin's trick for bounding the tail of the reciprocal sum of
$Q$-smooth numbers:
$$\sum_{Z < n \le N, n \text{ is } Q\text{-smooth}} \frac{1}{n} \le Z^{-\sigma} \prod_{p \le Q} (1 - p^{\sigma - 1})^{-1}$$
valid for all $Z \ge 1$, $0 < \sigma \le 1/2$, and uniformly in $N$.
It also bounds the Euler product by $\exp(4 \sum_{p \le Q} p^{\sigma - 1})$.
-/

namespace Erdos1201.MR

/-- For $Z \ge 1$, $\sigma > 0$, and $Z < n$, the reciprocal $1/n$ is bounded by $Z^{-\sigma} n^{\sigma - 1}$. -/
lemma one_div_le_rpow_tail {n : ℕ} {Z σ : ℝ} (hZ : 1 ≤ Z) (hσ0 : 0 < σ) (hn : Z < (n : ℝ)) :
    (1 : ℝ) / (n : ℝ) ≤ Z ^ (-σ) * (n : ℝ) ^ (σ - 1) := by
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hZ_pos : 0 < Z := by linarith
  have h_le : 1 ≤ ((n : ℝ) / Z) ^ σ := by
    rw [← Real.one_rpow σ]
    apply Real.rpow_le_rpow (by linarith) _ (le_of_lt hσ0)
    rw [le_div_iff₀ hZ_pos]
    linarith
  have h_eq : Z ^ (-σ) * (n : ℝ) ^ (σ - 1) = ((n : ℝ) / Z) ^ σ * (1 / (n : ℝ)) := by
    rw [Real.div_rpow (le_of_lt hn_pos) (le_of_lt hZ_pos)]
    rw [Real.rpow_neg (le_of_lt hZ_pos)]
    rw [sub_eq_add_neg, Real.rpow_add hn_pos]
    rw [Real.rpow_neg_one]
    ring
  rw [h_eq]
  have : 0 < 1 / (n : ℝ) := one_div_pos.mpr hn_pos
  nlinarith

/-- Reconstructing a $Q$-smooth integer $n$ from its prime power factorization restricted to $p \le Q$. -/
lemma prod_pow_factorization_eq_self_of_smooth {Q n : ℕ}
    (hn : n ∈ Nat.smoothNumbers (Q + 1)) :
    (∏ p ∈ Nat.primesLE Q, p ^ (n.factorization p)) = n := by
  have hn0 : n ≠ 0 := (Nat.mem_smoothNumbers.mp hn).1
  have h_supp : n.factorization.support ⊆ Nat.primesLE Q := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    have hsm := (Nat.mem_smoothNumbers.mp hn).2 p
    have hlist : p ∈ n.primeFactorsList := by
      rw [Nat.mem_primeFactorsList hn0]
      exact ⟨hp.1, hp.2.1⟩
    have hp_lt := hsm hlist
    exact ⟨by omega, hp.1⟩
  rw [← Finsupp.prod_of_support_subset n.factorization h_supp (fun p k => p ^ k) (by simp)]
  exact Nat.prod_factorization_pow_eq_self hn0

/-- Real power of a finite product of non-negative reals distributes over the product. -/
lemma prod_rpow_eq_rpow_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (z : ℝ) :
    (∏ i ∈ s, f i) ^ z = ∏ i ∈ s, (f i ^ z) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp only [Finset.mem_cons] at hf
    rw [Finset.prod_cons, Finset.prod_cons]
    have hfa : 0 ≤ f a := hf a (Or.inl rfl)
    have hfs : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => hf i (Or.inr hi))
    rw [Real.mul_rpow hfa hfs, ih (fun i hi => hf i (Or.inr hi))]

/-- Exponentiation identity $((p^k : ℝ)^z) = ((p : ℝ)^z)^k$. -/
lemma nat_cast_pow_rpow (p k : ℕ) (z : ℝ) :
    (((p ^ k : ℕ) : ℝ) ^ z) = ((p : ℝ) ^ z) ^ k := by
  rw [Nat.cast_pow]
  rw [← Real.rpow_natCast (p : ℝ) k]
  rw [← Real.rpow_mul (Nat.cast_nonneg p)]
  rw [mul_comm]
  rw [Real.rpow_mul (Nat.cast_nonneg p)]
  rw [Real.rpow_natCast]

/-- The power $n^z$ of a $Q$-smooth integer $n$ decomposes as the product of $(p^z)^{e_p}$. -/
lemma prod_rpow_factorization_eq_self_rpow {Q n : ℕ} (z : ℝ)
    (hn : n ∈ Nat.smoothNumbers (Q + 1)) :
    (∏ p ∈ Nat.primesLE Q, ((p : ℝ) ^ z) ^ (n.factorization p)) = (n : ℝ) ^ z := by
  have h_eq1 : (∏ p ∈ Nat.primesLE Q, ((p : ℝ) ^ z) ^ (n.factorization p)) =
      ∏ p ∈ Nat.primesLE Q, ((p ^ (n.factorization p) : ℕ) : ℝ) ^ z := by
    apply Finset.prod_congr rfl
    intro p hp
    rw [nat_cast_pow_rpow]
  rw [h_eq1]
  rw [← prod_rpow_eq_rpow_prod (Nat.primesLE Q) (fun p => ((p ^ (n.factorization p) : ℕ) : ℝ))
    (fun p hp => Nat.cast_nonneg _) z]
  rw [← Nat.cast_prod]
  rw [prod_pow_factorization_eq_self_of_smooth hn]

/-- For prime $p$, the $p$-adic valuation of $n \le N$ is at most $N$. -/
lemma factorization_le_of_le_of_prime {n N p : ℕ} (hn0 : n ≠ 0) (hnN : n ≤ N) (hp : Nat.Prime p) :
    n.factorization p ≤ N := by
  rw [Nat.factorization_def n hp]
  have hdvd : p ^ (padicValNat p n) ∣ n := pow_padicValNat_dvd
  have h_le : p ^ (padicValNat p n) ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have h_lt : padicValNat p n < p ^ (padicValNat p n) := Nat.lt_pow_self hp.one_lt
  omega

/-- Injectivity of prime factorization restricted to primes $p \le Q$ on $Q$-smooth integers. -/
lemma factorization_inj_on_smooth {Q : ℕ} {n m : ℕ}
    (hn : n ∈ Nat.smoothNumbers (Q + 1)) (hm : m ∈ Nat.smoothNumbers (Q + 1))
    (h_eq : ∀ p ∈ Nat.primesLE Q, n.factorization p = m.factorization p) :
    n = m := by
  have hn0 : n ≠ 0 := (Nat.mem_smoothNumbers.mp hn).1
  have hm0 : m ≠ 0 := (Nat.mem_smoothNumbers.mp hm).1
  have h_supp_n : n.factorization.support ⊆ Nat.primesLE Q := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    have hsm := (Nat.mem_smoothNumbers.mp hn).2 p
    have hlist : p ∈ n.primeFactorsList := by
      rw [Nat.mem_primeFactorsList hn0]
      exact ⟨hp.1, hp.2.1⟩
    have hp_lt := hsm hlist
    exact ⟨by omega, hp.1⟩
  have h_supp_m : m.factorization.support ⊆ Nat.primesLE Q := by
    intro p hp
    rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
    rw [Nat.mem_primesLE]
    have hsm := (Nat.mem_smoothNumbers.mp hm).2 p
    have hlist : p ∈ m.primeFactorsList := by
      rw [Nat.mem_primeFactorsList hm0]
      exact ⟨hp.1, hp.2.1⟩
    have hp_lt := hsm hlist
    exact ⟨by omega, hp.1⟩
  have h_fact_eq : n.factorization = m.factorization := by
    ext p
    by_cases hp : p ∈ Nat.primesLE Q
    · exact h_eq p hp
    · have hpn : p ∉ n.factorization.support := fun h => hp (h_supp_n h)
      have hpm : p ∉ m.factorization.support := fun h => hp (h_supp_m h)
      rw [Finsupp.mem_support_iff, not_not] at hpn hpm
      rw [hpn, hpm]
  rw [← Nat.factorization_inj hn0 hm0]
  exact h_fact_eq

/-- Finite geometric sum bound $\sum_{k=0}^N x^k \le (1 - x)^{-1}$ for $0 \le x < 1$. -/
lemma geom_sum_le_inv_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (N : ℕ) :
    (∑ k ∈ Finset.range (N + 1), x ^ k) ≤ (1 - x)⁻¹ := by
  have h_sum : (∑ k ∈ Finset.range (N + 1), x ^ k) * (1 - x) = 1 - x ^ (N + 1) :=
    geom_sum_mul_neg x (N + 1)
  have h1 : 0 < 1 - x := by linarith
  have h_le : (∑ k ∈ Finset.range (N + 1), x ^ k) * (1 - x) ≤ 1 := by
    rw [h_sum]
    have : 0 ≤ x ^ (N + 1) := by positivity
    linarith
  have h_inv : 0 < (1 - x)⁻¹ := inv_pos.mpr h1
  calc (∑ k ∈ Finset.range (N + 1), x ^ k)
    _ = ((∑ k ∈ Finset.range (N + 1), x ^ k) * (1 - x)) * (1 - x)⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt h1), mul_one]
    _ ≤ 1 * (1 - x)⁻¹ := mul_le_mul_of_nonneg_right h_le (le_of_lt h_inv)
    _ = (1 - x)⁻¹ := one_mul _

/-- The sum of $n^{\sigma - 1}$ over $Q$-smooth numbers $n \le N$ is bounded by the Euler product. -/
lemma sum_smooth_rpow_le_prod (Q N : ℕ) (σ : ℝ) (hσ : σ ≤ 1 / 2) :
    (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ Nat.smoothNumbers (Q + 1)), (n : ℝ) ^ (σ - 1)) ≤
      ∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹ := by
  let ι := { p : ℕ // p ∈ Nat.primesLE Q }
  let B := (Finset.Ioc 0 N).filter (fun n => n ∈ Nat.smoothNumbers (Q + 1))
  let T := Fintype.piFinset (fun (_ : ι) => Finset.range (N + 1))
  let F : ℕ → (ι → ℕ) := fun n => fun i => n.factorization i.val
  let term : (ι → ℕ) → ℝ := fun f => ∏ i : ι, ((i.val : ℝ) ^ (σ - 1)) ^ (f i)
  have hF_mem : ∀ n ∈ B, F n ∈ T := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ioc] at hn
    rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    dsimp [F]
    have hp : Nat.Prime i.val := (Nat.mem_primesLE.mp i.2).2
    have h_le := factorization_le_of_le_of_prime (by omega) hn.1.2 hp
    omega
  have hF_inj : Set.InjOn F ↑B := by
    intro n hn m hm h_eq
    rw [Finset.mem_coe, Finset.mem_filter] at hn hm
    apply factorization_inj_on_smooth hn.2 hm.2
    intro p hp
    have h_eval := congr_fun h_eq ⟨p, hp⟩
    exact h_eval
  have h_term_eq : ∀ n ∈ B, (n : ℝ) ^ (σ - 1) = term (F n) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    dsimp [term, F]
    rw [← prod_rpow_factorization_eq_self_rpow (σ - 1) hn.2]
    exact Finset.prod_subtype (Nat.primesLE Q) (fun x => Iff.rfl)
      (fun p => ((p : ℝ) ^ (σ - 1)) ^ (n.factorization p))
  have h_sum1 : (∑ n ∈ B, (n : ℝ) ^ (σ - 1)) = ∑ f ∈ Finset.image F B, term f := by
    rw [Finset.sum_image hF_inj]
    apply Finset.sum_congr rfl
    intro n hn
    exact h_term_eq n hn
  have h_image_sub : Finset.image F B ⊆ T := by
    intro f hf
    rw [Finset.mem_image] at hf
    rcases hf with ⟨n, hn, rfl⟩
    exact hF_mem n hn
  have h_term_nonneg : ∀ f ∈ T, 0 ≤ term f := by
    intro f hf
    dsimp [term]
    apply Finset.prod_nonneg
    intro i hi
    have hp : 0 ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have hr : 0 ≤ (i.val : ℝ) ^ (σ - 1) := Real.rpow_nonneg hp _
    exact pow_nonneg hr _
  have h_sum2 : ∑ f ∈ Finset.image F B, term f ≤ ∑ f ∈ T, term f :=
    Finset.sum_le_sum_of_subset_of_nonneg h_image_sub (fun f hf _ => h_term_nonneg f hf)
  have h_sum3 : (∑ f ∈ T, term f) =
      ∏ p ∈ Nat.primesLE Q, ∑ k ∈ Finset.range (N + 1), ((p : ℝ) ^ (σ - 1)) ^ k := by
    dsimp [T, term]
    have h := Finset.sum_prod_piFinset (Finset.range (N + 1))
      (fun (i : ι) (k : ℕ) => ((i.val : ℝ) ^ (σ - 1)) ^ k)
    rw [h]
    exact (Finset.prod_subtype (Nat.primesLE Q) (fun x => Iff.rfl)
      (fun p => ∑ k ∈ Finset.range (N + 1), ((p : ℝ) ^ (σ - 1)) ^ k)).symm
  have h_sum4 : (∏ p ∈ Nat.primesLE Q, ∑ k ∈ Finset.range (N + 1), ((p : ℝ) ^ (σ - 1)) ^ k) ≤
      ∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹ := by
    apply Finset.prod_le_prod
    · intro p hp
      apply Finset.sum_nonneg
      intro k hk
      have hp' := (Nat.mem_primesLE.mp hp).2
      have hp_pos : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
      exact pow_nonneg (Real.rpow_nonneg hp_pos _) _
    · intro p hp
      have hp' := (Nat.mem_primesLE.mp hp).2
      have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp'.pos
      have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
      have hx0 : 0 ≤ (p : ℝ) ^ (σ - 1) := Real.rpow_nonneg (le_of_lt hp_pos) _
      have hσ1 : σ - 1 ≤ 0 := by linarith
      have h_le_2 : (p : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (σ - 1) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 hσ1
      have h_two : (2 : ℝ) ^ (σ - 1) ≤ 3 / 4 := by
        have h1 : σ - 1 ≤ -(1 / 2) := by linarith
        have h2 : (2 : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
        apply le_trans h2
        rw [Real.rpow_neg (by norm_num)]
        rw [Real.rpow_div_two_eq_sqrt 1 (by norm_num)]
        rw [Real.rpow_one]
        rw [inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr (by norm_num))]
        have h_sqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
          rw [Real.le_sqrt (by norm_num) (by norm_num)]
          norm_num
        linarith
      have hx1 : (p : ℝ) ^ (σ - 1) < 1 := by linarith
      exact geom_sum_le_inv_one_sub hx0 hx1 N
  linarith

/-- Rankin's inequality: for 0 < σ ≤ 1/2 and Z ≥ 1, the reciprocal sum over Q-smooth n with Z < n ≤ N is bounded by Z^{-σ} times the Euler product ∏_{p ≤ Q} (1 - p^{σ-1})⁻¹, uniformly in N. -/
theorem sum_smooth_tail_le (Q N : ℕ) (Z σ : ℝ) (hZ : 1 ≤ Z) (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 2) :
    (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ Nat.smoothNumbers (Q + 1) ∧ Z < n), (1 : ℝ) / n) ≤
      Z ^ (-σ) * ∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹ := by
  let A := (Finset.Ioc 0 N).filter (fun n => n ∈ Nat.smoothNumbers (Q + 1) ∧ Z < n)
  let B := (Finset.Ioc 0 N).filter (fun n => n ∈ Nat.smoothNumbers (Q + 1))
  have h_le_terms : ∀ n ∈ A, (1 : ℝ) / (n : ℝ) ≤ Z ^ (-σ) * (n : ℝ) ^ (σ - 1) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    exact one_div_le_rpow_tail hZ hσ0 hn.2.2
  have h_sum_le_mul : (∑ n ∈ A, (1 : ℝ) / n) ≤ ∑ n ∈ A, (Z ^ (-σ) * (n : ℝ) ^ (σ - 1)) :=
    Finset.sum_le_sum (fun n hn => h_le_terms n hn)
  rw [← Finset.mul_sum] at h_sum_le_mul
  have hAB : A ⊆ B := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  have h_rpow_nonneg : ∀ n ∈ B, 0 ≤ (n : ℝ) ^ (σ - 1) := by
    intro n hn
    have hp : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    exact Real.rpow_nonneg hp _
  have h_sum_AB : (∑ n ∈ A, (n : ℝ) ^ (σ - 1)) ≤ ∑ n ∈ B, (n : ℝ) ^ (σ - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hAB (fun n hn _ => h_rpow_nonneg n hn)
  have hZ_nonneg : 0 ≤ Z ^ (-σ) := Real.rpow_nonneg (by linarith) _
  have h_mul_AB : Z ^ (-σ) * (∑ n ∈ A, (n : ℝ) ^ (σ - 1)) ≤ Z ^ (-σ) * ∑ n ∈ B, (n : ℝ) ^ (σ - 1) :=
    mul_le_mul_of_nonneg_left h_sum_AB hZ_nonneg
  have hB_le := sum_smooth_rpow_le_prod Q N σ hσ
  have h_mul_prod : Z ^ (-σ) * (∑ n ∈ B, (n : ℝ) ^ (σ - 1)) ≤
      Z ^ (-σ) * ∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹ :=
    mul_le_mul_of_nonneg_left hB_le hZ_nonneg
  linarith

/-- The Euler product is at most exp(4 Σ_{p ≤ Q} p^{σ-1}). -/
theorem prod_inv_one_sub_rpow_le (Q : ℕ) (σ : ℝ) (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 2) :
    (∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹) ≤ Real.exp (4 * ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1)) := by
  have h_le : ∀ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹ ≤ Real.exp (4 * (p : ℝ) ^ (σ - 1)) := by
    intro p hp
    rw [Nat.mem_primesLE] at hp
    have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr (hp.2.pos)
    have hx0 : 0 ≤ (p : ℝ) ^ (σ - 1) := Real.rpow_nonneg (le_of_lt hp_pos) _
    have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp.2.two_le
    have hσ1 : σ - 1 ≤ 0 := by linarith
    have h_le_2 : (p : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (σ - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 hσ1
    have h_two : (2 : ℝ) ^ (σ - 1) ≤ 3 / 4 := by
      have h1 : σ - 1 ≤ -(1 / 2) := by linarith
      have h2 : (2 : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      apply le_trans h2
      rw [Real.rpow_neg (by norm_num)]
      rw [Real.rpow_div_two_eq_sqrt 1 (by norm_num)]
      rw [Real.rpow_one]
      rw [inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr (by norm_num))]
      have h_sqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      linarith
    have hx : (p : ℝ) ^ (σ - 1) ≤ 3 / 4 := le_trans h_le_2 h_two
    have h1 : 0 < 1 - (p : ℝ) ^ (σ - 1) := by linarith
    have h2 : 1 ≤ (1 + 4 * (p : ℝ) ^ (σ - 1)) * (1 - (p : ℝ) ^ (σ - 1)) := by
      have : (1 + 4 * (p : ℝ) ^ (σ - 1)) * (1 - (p : ℝ) ^ (σ - 1)) - 1 =
        (p : ℝ) ^ (σ - 1) * (3 - 4 * (p : ℝ) ^ (σ - 1)) := by ring
      linarith [mul_nonneg hx0 (by linarith : 0 ≤ 3 - 4 * (p : ℝ) ^ (σ - 1))]
    have h3 : (1 - (p : ℝ) ^ (σ - 1))⁻¹ ≤ 1 + 4 * (p : ℝ) ^ (σ - 1) := by
      rw [inv_le_iff_one_le_mul₀ h1]
      exact h2
    have h4 : 1 + 4 * (p : ℝ) ^ (σ - 1) ≤ Real.exp (4 * (p : ℝ) ^ (σ - 1)) := by
      rw [add_comm]
      exact Real.add_one_le_exp (4 * (p : ℝ) ^ (σ - 1))
    exact le_trans h3 h4
  have h_prod := Finset.prod_le_prod (fun p hp => ?_) h_le
  · rw [← Real.exp_sum] at h_prod
    rw [← Finset.mul_sum] at h_prod
    exact h_prod
  · have hp' := (Nat.mem_primesLE.mp hp).2
    have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp'.pos
    have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
    have hσ1 : σ - 1 ≤ 0 := by linarith
    have h_le_2 : (p : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (σ - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 hσ1
    have h_two : (2 : ℝ) ^ (σ - 1) ≤ 3 / 4 := by
      have h1 : σ - 1 ≤ -(1 / 2) := by linarith
      have h2 : (2 : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      apply le_trans h2
      rw [Real.rpow_neg (by norm_num)]
      rw [Real.rpow_div_two_eq_sqrt 1 (by norm_num)]
      rw [Real.rpow_one]
      rw [inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr (by norm_num))]
      have h_sqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      linarith
    have hx : (p : ℝ) ^ (σ - 1) ≤ 3 / 4 := le_trans h_le_2 h_two
    have h1 : 0 < 1 - (p : ℝ) ^ (σ - 1) := by linarith
    exact le_of_lt (inv_pos.mpr h1)

end Erdos1201.MR
