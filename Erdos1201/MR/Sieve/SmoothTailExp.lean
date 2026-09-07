import Mathlib
import Erdos1201.MR.Sieve.SmoothTail
import Erdos1201.Vendor.NumberTheory.MertensTheorems

/-!
# Exponential Tail Bound for Smooth Numbers

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module provides Rankin's upper bound in the exponential form used by the
U-part of the Matomäki–Radziwiłł theorem:
$$\sum_{Z < n \le N, n \text{ is } Q\text{-smooth}} \frac{1}{n} \le C \exp\Bigl(-\frac{\log Z}{2 \log Q}\Bigr) (\log Q)^6$$
valid for all $Q \ge 2$, $Z \ge 1$, uniformly in $N \ge 1$.
-/

namespace Erdos1201.MR

/-- The constant $1 < 2 \log 2 = \log 4$. -/
lemma one_lt_two_mul_log_two : 1 < 2 * Real.log 2 := by
  have h4 : (4 : ℝ) = 2 * 2 := by norm_num
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [h4, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [← hlog4]
  rw [← Real.log_exp 1]
  apply Real.log_lt_log (Real.exp_pos 1)
  have := Real.exp_one_lt_d9
  linarith

/-- The constant $1 < \log 3$. -/
lemma one_lt_log_three : 1 < Real.log 3 := by
  rw [← Real.log_exp 1]
  apply Real.log_lt_log (Real.exp_pos 1)
  have := Real.exp_one_lt_d9
  linarith

/-- Numerical bound $\exp(1/2) \le 2$. -/
lemma exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h := Real.sqrt_le_iff.mpr (show 0 ≤ (2 : ℝ) ∧ Real.exp 1 ≤ 2 ^ 2 by
    refine ⟨by norm_num, ?_⟩
    have := Real.exp_one_lt_d9
    linarith)
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos 1)] at h
  simp only [Real.log_exp] at h
  ring_nf at h
  exact h

/-- For $0 \le x \le 2/3$, $(1 - x)^{-1} \le \exp(3x)$. -/
lemma inv_one_sub_le_exp_three_mul {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 2 / 3) :
    (1 - x)⁻¹ ≤ Real.exp (3 * x) := by
  have h1 : 0 < 1 - x := by linarith
  have h2 : 1 ≤ (1 + 3 * x) * (1 - x) := by
    have : (1 + 3 * x) * (1 - x) - 1 = x * (2 - 3 * x) := by ring
    linarith [mul_nonneg hx0 (by linarith : 0 ≤ 2 - 3 * x)]
  have h3 : (1 - x)⁻¹ ≤ 1 + 3 * x := by
    rw [inv_le_iff_one_le_mul₀ h1]
    exact h2
  have h4 : 1 + 3 * x ≤ Real.exp (3 * x) := by
    rw [add_comm]
    exact Real.add_one_le_exp (3 * x)
  exact le_trans h3 h4

/-- The Euler factor at $p = 2$ is bounded by 4 for $\sigma \le 1/2$. -/
lemma inv_one_sub_two_rpow_le_four {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    (1 - (2 : ℝ) ^ (σ - 1))⁻¹ ≤ 4 := by
  have h1 : σ - 1 ≤ -(1 / 2) := by linarith
  have h2 : (2 : ℝ) ^ (σ - 1) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  have h_two : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 3 / 4 := by
    rw [Real.rpow_neg (by norm_num)]
    rw [Real.rpow_div_two_eq_sqrt 1 (by norm_num)]
    rw [Real.rpow_one]
    rw [inv_le_iff_one_le_mul₀ (Real.sqrt_pos.mpr (by norm_num))]
    have h_sqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    linarith
  have h_le_34 : (2 : ℝ) ^ (σ - 1) ≤ 3 / 4 := le_trans h2 h_two
  have h_pos : 0 < 1 - (2 : ℝ) ^ (σ - 1) := by linarith
  rw [inv_le_iff_one_le_mul₀ h_pos]
  linarith

/-- Smooth reciprocal power sum bounded by the Euler product for any $\sigma < 1$. -/
lemma sum_smooth_rpow_le_prod_of_lt_one (Q N : ℕ) (σ : ℝ) (hσ : σ < 1) :
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
      have hx0 : 0 ≤ (p : ℝ) ^ (σ - 1) := Real.rpow_nonneg (le_of_lt hp_pos) _
      have hp1 : 1 < (p : ℝ) := by exact_mod_cast hp'.one_lt
      have hneg : σ - 1 < 0 := by linarith
      have hx1 : (p : ℝ) ^ (σ - 1) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 hneg
      exact geom_sum_le_inv_one_sub hx0 hx1 N
  linarith

/-- Tail bound for smooth numbers under $\sigma < 1$. -/
theorem sum_smooth_tail_le_of_lt_one (Q N : ℕ) (Z σ : ℝ) (hZ : 1 ≤ Z) (hσ0 : 0 < σ) (hσ : σ < 1) :
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
  have hB_le := sum_smooth_rpow_le_prod_of_lt_one Q N σ hσ
  have h_mul_prod : Z ^ (-σ) * (∑ n ∈ B, (n : ℝ) ^ (σ - 1)) ≤
      Z ^ (-σ) * ∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹ :=
    mul_le_mul_of_nonneg_left hB_le hZ_nonneg
  linarith

/-- Positivity and exponential bound for odd prime Euler factors at $\sigma = 1/(2 \log Q)$. -/
lemma inv_one_sub_rpow_props {Q p : ℕ} (hQ : 3 ≤ Q) (hp : p ∈ (Nat.primesLE Q).erase 2) :
    let σ := 1 / (2 * Real.log Q)
    0 ≤ (1 - (p : ℝ) ^ (σ - 1))⁻¹ ∧
    (1 - (p : ℝ) ^ (σ - 1))⁻¹ ≤ Real.exp (3 * (p : ℝ) ^ (σ - 1)) := by
  intro σ
  rw [Finset.mem_erase, Nat.mem_primesLE] at hp
  have hp_prime := hp.2.2
  have hp_ge3 : 3 ≤ p := by
    have := hp_prime.two_le
    have : p ≠ 2 := hp.1
    omega
  have hp_pos : 0 < (p : ℝ) := by positivity
  have hp_le_Q : (p : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hp.2.1
  have hlog_p_le : Real.log p ≤ Real.log Q := Real.log_le_log hp_pos hp_le_Q
  have hlog3 := one_lt_log_three
  have hlogQ : 1 < Real.log Q := by
    apply lt_of_lt_of_le hlog3
    apply Real.log_le_log (by norm_num) (by exact_mod_cast hQ)
  have hx0 : 0 ≤ (p : ℝ) ^ (σ - 1) := Real.rpow_nonneg (le_of_lt hp_pos) _
  have h_σ_log_p : σ * Real.log p ≤ 1 / 2 := by
    dsimp [σ]
    rw [mul_comm, ← mul_div_assoc, mul_one]
    have hpos : 0 < 2 * Real.log Q := by positivity
    rw [div_le_iff₀ hpos]
    linarith
  have hp_pow_σ : (p : ℝ) ^ σ ≤ Real.exp (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hp_pos]
    exact Real.exp_le_exp_of_le (by linarith [mul_comm σ (Real.log p)])
  have hp_pow_σ_le_2 : (p : ℝ) ^ σ ≤ 2 := le_trans hp_pow_σ exp_half_le_two
  have hp_rpow_eq : (p : ℝ) ^ (σ - 1) = (p : ℝ) ^ σ / (p : ℝ) := by
    rw [sub_eq_add_neg, Real.rpow_add hp_pos, Real.rpow_neg_one]
    ring
  have hx_le_23 : (p : ℝ) ^ (σ - 1) ≤ 2 / 3 := by
    rw [hp_rpow_eq]
    have : (p : ℝ) ^ σ / (p : ℝ) ≤ 2 / 3 := by
      rw [div_le_div_iff₀ hp_pos (by norm_num)]
      have hp_ge3_r : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_ge3
      nlinarith
    exact this
  have h1 : 0 < 1 - (p : ℝ) ^ (σ - 1) := by linarith
  have h_pos : 0 ≤ (1 - (p : ℝ) ^ (σ - 1))⁻¹ := le_of_lt (inv_pos.mpr h1)
  have h_le : (1 - (p : ℝ) ^ (σ - 1))⁻¹ ≤ Real.exp (3 * (p : ℝ) ^ (σ - 1)) :=
    inv_one_sub_le_exp_three_mul hx0 hx_le_23
  exact ⟨h_pos, h_le⟩

/-- The Euler product for $Q \ge 3$ is bounded by $4 \exp(3 \sum_{p \le Q} p^{\sigma - 1})$. -/
lemma prod_inv_one_sub_rpow_le_four_exp (Q : ℕ) (hQ : 3 ≤ Q) :
    let σ := 1 / (2 * Real.log Q)
    (∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹) ≤
      4 * Real.exp (3 * ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1)) := by
  intro σ
  have h2_mem : 2 ∈ Nat.primesLE Q := by
    rw [Nat.mem_primesLE]
    exact ⟨by omega, Nat.prime_two⟩
  have h_prod_eq : (∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹) =
      (1 - (2 : ℝ) ^ (σ - 1))⁻¹ * ∏ p ∈ (Nat.primesLE Q).erase 2, (1 - (p : ℝ) ^ (σ - 1))⁻¹ :=
    (Finset.mul_prod_erase (Nat.primesLE Q) _ h2_mem).symm
  have hlog3 := one_lt_log_three
  have hlogQ : 1 < Real.log Q := by
    apply lt_of_lt_of_le hlog3
    apply Real.log_le_log (by norm_num) (by exact_mod_cast hQ)
  have hσ_le_half : σ ≤ 1 / 2 := by
    dsimp [σ]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h2_le : (1 - (2 : ℝ) ^ (σ - 1))⁻¹ ≤ 4 := inv_one_sub_two_rpow_le_four hσ_le_half
  have h_erase_le : (∏ p ∈ (Nat.primesLE Q).erase 2, (1 - (p : ℝ) ^ (σ - 1))⁻¹) ≤
      Real.exp (3 * ∑ p ∈ (Nat.primesLE Q).erase 2, (p : ℝ) ^ (σ - 1)) := by
    have h_prod := Finset.prod_le_prod
      (fun p hp => (inv_one_sub_rpow_props hQ hp).1)
      (fun p hp => (inv_one_sub_rpow_props hQ hp).2)
    rw [← Real.exp_sum] at h_prod
    rw [← Finset.mul_sum] at h_prod
    exact h_prod
  have h_prod_nonneg : 0 ≤ ∏ p ∈ (Nat.primesLE Q).erase 2, (1 - (p : ℝ) ^ (σ - 1))⁻¹ :=
    Finset.prod_nonneg (fun p hp => (inv_one_sub_rpow_props hQ hp).1)
  have h_sum_le : ∑ p ∈ (Nat.primesLE Q).erase 2, (p : ℝ) ^ (σ - 1) ≤
      ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset 2 _)
    intro i hi _
    exact Real.rpow_nonneg (Nat.cast_nonneg i) _
  have h_exp_mono : Real.exp (3 * ∑ p ∈ (Nat.primesLE Q).erase 2, (p : ℝ) ^ (σ - 1)) ≤
      Real.exp (3 * ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1)) :=
    Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left h_sum_le (by norm_num))
  rw [h_prod_eq]
  calc (1 - (2 : ℝ) ^ (σ - 1))⁻¹ * ∏ p ∈ (Nat.primesLE Q).erase 2, (1 - (p : ℝ) ^ (σ - 1))⁻¹
    _ ≤ 4 * ∏ p ∈ (Nat.primesLE Q).erase 2, (1 - (p : ℝ) ^ (σ - 1))⁻¹ :=
        mul_le_mul_of_nonneg_right h2_le h_prod_nonneg
    _ ≤ 4 * Real.exp (3 * ∑ p ∈ (Nat.primesLE Q).erase 2, (p : ℝ) ^ (σ - 1)) :=
        mul_le_mul_of_nonneg_left h_erase_le (by norm_num)
    _ ≤ 4 * Real.exp (3 * ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1)) :=
        mul_le_mul_of_nonneg_left h_exp_mono (by norm_num)

/-- Pointwise bound $\sum_{p \le Q} p^{\sigma - 1} \le \exp(1/2) \sum_{p \le Q} 1/p$. -/
lemma sum_rpow_le_exp_half_mul_sum (Q : ℕ) (hQ : 3 ≤ Q) :
    let σ := 1 / (2 * Real.log Q)
    ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1) ≤
      Real.exp (1 / 2 : ℝ) * ∑ p ∈ Nat.primesLE Q, 1 / (p : ℝ) := by
  intro σ
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  rw [Nat.mem_primesLE] at hp
  have hp_pos : 0 < (p : ℝ) := by
    have : 2 ≤ p := hp.2.two_le
    positivity
  have hp_le_Q : (p : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hp.1
  have hlog_p_le : Real.log p ≤ Real.log Q := Real.log_le_log hp_pos hp_le_Q
  have hlog3 := one_lt_log_three
  have hlogQ : 1 < Real.log Q := by
    apply lt_of_lt_of_le hlog3
    apply Real.log_le_log (by norm_num) (by exact_mod_cast hQ)
  have h_σ_log_p : σ * Real.log p ≤ 1 / 2 := by
    dsimp [σ]
    rw [mul_comm, ← mul_div_assoc, mul_one]
    have hpos : 0 < 2 * Real.log Q := by positivity
    rw [div_le_iff₀ hpos]
    linarith
  have hp_pow_σ : (p : ℝ) ^ σ ≤ Real.exp (1 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hp_pos]
    exact Real.exp_le_exp_of_le (by linarith [mul_comm σ (Real.log p)])
  have hp_rpow_eq : (p : ℝ) ^ (σ - 1) = (p : ℝ) ^ σ * (1 / (p : ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hp_pos, Real.rpow_neg_one]
    ring
  rw [hp_rpow_eq]
  have h_inv_nonneg : 0 ≤ 1 / (p : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_right hp_pow_σ h_inv_nonneg

/-- Bounding $\exp(3 \sum_{p \le Q} p^{\sigma - 1})$ by $C (\log Q)^6$ using Mertens. -/
lemma exp_three_sum_le (Q : ℕ) (hQ : 3 ≤ Q) (C_M : ℝ)
    (h_mertens : ∑ p ∈ Nat.primesLE Q, 1 / (p : ℝ) ≤ Real.log (Real.log Q) + C_M) :
    let σ := 1 / (2 * Real.log Q)
    Real.exp (3 * ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1)) ≤
      Real.exp (3 * Real.exp (1 / 2 : ℝ) * C_M) * (Real.log Q) ^ (6 : ℝ) := by
  intro σ
  have hlog3 := one_lt_log_three
  have hlogQ : 1 < Real.log Q := by
    apply lt_of_lt_of_le hlog3
    apply Real.log_le_log (by norm_num) (by exact_mod_cast hQ)
  have h_sum := sum_rpow_le_exp_half_mul_sum Q hQ
  have h_mul_sum : 3 * ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1) ≤
      3 * Real.exp (1 / 2 : ℝ) * (Real.log (Real.log Q) + C_M) := by
    have := mul_le_mul_of_nonneg_left h_sum (by norm_num : 0 ≤ (3 : ℝ))
    have h_exp_nonneg : 0 ≤ 3 * Real.exp (1 / 2 : ℝ) := by positivity
    linarith [mul_le_mul_of_nonneg_left h_mertens h_exp_nonneg]
  have h_exp_le : Real.exp (3 * ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1)) ≤
      Real.exp (3 * Real.exp (1 / 2 : ℝ) * (Real.log (Real.log Q) + C_M)) :=
    Real.exp_le_exp_of_le h_mul_sum
  have h_split : 3 * Real.exp (1 / 2 : ℝ) * (Real.log (Real.log Q) + C_M) =
      (3 * Real.exp (1 / 2 : ℝ)) * Real.log (Real.log Q) + 3 * Real.exp (1 / 2 : ℝ) * C_M := by ring
  rw [h_split, Real.exp_add] at h_exp_le
  have h_rpow : Real.exp ((3 * Real.exp (1 / 2 : ℝ)) * Real.log (Real.log Q)) =
      (Real.log Q) ^ (3 * Real.exp (1 / 2 : ℝ)) := by
    have hpos : 0 < Real.log Q := by linarith
    rw [Real.rpow_def_of_pos hpos]
    ring_nf
  rw [h_rpow] at h_exp_le
  have h_exp_half : 3 * Real.exp (1 / 2 : ℝ) ≤ 6 := by
    have := exp_half_le_two
    linarith
  have h_rpow_le : (Real.log Q) ^ (3 * Real.exp (1 / 2 : ℝ)) ≤ (Real.log Q) ^ (6 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) h_exp_half
  have h_C_nonneg : 0 ≤ Real.exp (3 * Real.exp (1 / 2 : ℝ) * C_M) := by positivity
  calc Real.exp (3 * ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1))
    _ ≤ (Real.log Q) ^ (3 * Real.exp (1 / 2 : ℝ)) * Real.exp (3 * Real.exp (1 / 2 : ℝ) * C_M) := h_exp_le
    _ ≤ (Real.log Q) ^ (6 : ℝ) * Real.exp (3 * Real.exp (1 / 2 : ℝ) * C_M) :=
        mul_le_mul_of_nonneg_right h_rpow_le h_C_nonneg
    _ = Real.exp (3 * Real.exp (1 / 2 : ℝ) * C_M) * (Real.log Q) ^ (6 : ℝ) := by ring

/-- For $Q = 2$, the prime product consists of the single term at $p = 2$. -/
lemma prod_primesLE_two_eq (σ : ℝ) :
    (∏ p ∈ Nat.primesLE 2, (1 - (p : ℝ) ^ (σ - 1))⁻¹) = (1 - (2 : ℝ) ^ (σ - 1))⁻¹ := by
  have h : Nat.primesLE 2 = {2} := by decide
  rw [h, Finset.prod_singleton]
  norm_cast

/--
Rankin's upper bound on the reciprocal sum of $Q$-smooth numbers in exponential form.
For all $Q \ge 2$, $Z \ge 1$, and uniformly in $N$:
$$\sum_{Z < n \le N, n \text{ is } Q\text{-smooth}} \frac{1}{n} \le C \exp\Bigl(-\frac{\log Z}{2 \log Q}\Bigr) (\log Q)^6$$
-/
theorem sum_smooth_tail_le_exp : ∃ C : ℝ, 0 < C ∧ ∀ (Q N : ℕ) (Z : ℝ), 2 ≤ Q → 1 ≤ Z →
    (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ Nat.smoothNumbers (Q + 1) ∧ Z < n), (1 : ℝ) / n) ≤
      C * Real.exp (-(Real.log Z) / (2 * Real.log Q)) * (Real.log Q) ^ (6 : ℝ) := by
  rcases Mertens.exists_abs_sum_prime_inv_sub_loglog_le with ⟨C_M, _hC_M_pos, h_mertens_abs⟩
  let C_3 := 4 * Real.exp (3 * Real.exp (1 / 2 : ℝ) * C_M)
  let C_2 := (1 - (2 : ℝ) ^ (1 / (2 * Real.log 2) - 1))⁻¹ / (Real.log 2) ^ (6 : ℝ)
  let C := max C_2 C_3
  have hC_pos : 0 < C := by
    apply lt_of_lt_of_le (b := C_3)
    · dsimp [C_3]
      positivity
    · exact le_max_right C_2 C_3
  refine ⟨C, hC_pos, ?_⟩
  intro Q N Z hQ hZ
  let σ := 1 / (2 * Real.log Q)
  have hQ_real : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogQ_pos : 0 < Real.log Q := by
    have : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) hQ_real
    linarith
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    positivity
  have h_two_mul_logQ : 1 < 2 * Real.log Q := by
    have h1 := one_lt_two_mul_log_two
    have h2 : 2 * Real.log 2 ≤ 2 * Real.log Q := by
      have : Real.log 2 ≤ Real.log Q := Real.log_le_log (by norm_num) hQ_real
      linarith
    exact lt_of_lt_of_le h1 h2
  have hσ_lt1 : σ < 1 := by
    dsimp [σ]
    rw [div_lt_iff₀ (by linarith)]
    linarith
  have h_tail := sum_smooth_tail_le_of_lt_one Q N Z σ hZ hσ_pos hσ_lt1
  have hZ_pos : 0 < Z := by linarith
  have hZ_rpow : Z ^ (-σ) = Real.exp (-(Real.log Z) / (2 * Real.log Q)) := by
    rw [Real.rpow_def_of_pos hZ_pos]
    dsimp [σ]
    ring_nf
  have h_prod_le : (∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹) ≤ C * (Real.log Q) ^ (6 : ℝ) := by
    by_cases hQ3 : 3 ≤ Q
    · have h_mertens : ∑ p ∈ Nat.primesLE Q, 1 / (p : ℝ) ≤ Real.log (Real.log Q) + C_M := by
        have := (abs_le.mp (h_mertens_abs Q (by omega))).2
        linarith
      have h_four := prod_inv_one_sub_rpow_le_four_exp Q hQ3
      have h_exp := exp_three_sum_le Q hQ3 C_M h_mertens
      have h_prod_C3 : (∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹) ≤ C_3 * (Real.log Q) ^ (6 : ℝ) := by
        calc (∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹)
          _ ≤ 4 * Real.exp (3 * ∑ p ∈ Nat.primesLE Q, (p : ℝ) ^ (σ - 1)) := h_four
          _ ≤ 4 * (Real.exp (3 * Real.exp (1 / 2 : ℝ) * C_M) * (Real.log Q) ^ (6 : ℝ)) :=
              mul_le_mul_of_nonneg_left h_exp (by norm_num)
          _ = C_3 * (Real.log Q) ^ (6 : ℝ) := by
              dsimp [C_3]
              ring
      have h_C3_le : C_3 ≤ C := le_max_right C_2 C_3
      have h_rpow_nonneg : 0 ≤ (Real.log Q) ^ (6 : ℝ) := by positivity
      exact le_trans h_prod_C3 (mul_le_mul_of_nonneg_right h_C3_le h_rpow_nonneg)
    · have hQ_eq : Q = 2 := by omega
      subst hQ_eq
      have h_prod2 := prod_primesLE_two_eq σ
      rw [h_prod2]
      dsimp [σ]
      have h_log2_pow : 0 < (Real.log 2) ^ (6 : ℝ) := by positivity
      have h_eq : (1 - (2 : ℝ) ^ (1 / (2 * Real.log 2) - 1))⁻¹ =
          C_2 * (Real.log 2) ^ (6 : ℝ) := by
        dsimp [C_2]
        rw [div_mul_cancel₀ _ (ne_of_gt h_log2_pow)]
      rw [h_eq]
      have h_C2_le : C_2 ≤ C := le_max_left C_2 C_3
      exact mul_le_mul_of_nonneg_right h_C2_le (le_of_lt h_log2_pow)
  have hZ_nonneg : 0 ≤ Z ^ (-σ) := Real.rpow_nonneg (by linarith) _
  calc (∑ n ∈ (Finset.Ioc 0 N).filter (fun n => n ∈ Nat.smoothNumbers (Q + 1) ∧ Z < n), (1 : ℝ) / n)
    _ ≤ Z ^ (-σ) * ∏ p ∈ Nat.primesLE Q, (1 - (p : ℝ) ^ (σ - 1))⁻¹ := h_tail
    _ ≤ Z ^ (-σ) * (C * (Real.log Q) ^ (6 : ℝ)) :=
        mul_le_mul_of_nonneg_left h_prod_le hZ_nonneg
    _ = C * Real.exp (-(Real.log Z) / (2 * Real.log Q)) * (Real.log Q) ^ (6 : ℝ) := by
        rw [hZ_rpow]
        ring

end Erdos1201.MR
