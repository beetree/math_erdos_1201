import Mathlib
import Erdos1201.MR.Ranges
import Erdos1201.MR.Decomposition.Lemma12Assembly
import Erdos1201.MR.Decomposition.Lemma12
import Erdos1201.MR.Analysis.MeanValueTheorem


/-!
# Matomäki–Radziwiłł Proposition 1: Exceptional Set E1 Integral Bound

This module establishes the upper bound for the integral over $T_1 = \text{Tset } \langle 0, hJ \rangle$
of the Dirichlet polynomial $|F(\beta, J, \mathcal{R}, X, 1 + it)|^2$, corresponding to Section 8.1
of Matomäki–Radziwiłł (arXiv:1501.04585v4).

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.
-/

open Erdos1201.MR MeasureTheory

namespace Erdos1201.MR

lemma RangeSystem.log_Q_zero_lt_log_P {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (hη0 : 0 < η) (hη : η < 1 / 6)
    (j : Fin J) (hj : 0 < j.val) : Real.log (S.Q ⟨0, hJ⟩) < Real.log (S.P j) := by
  have hQ0_pos : 0 < Real.log (S.Q ⟨0, hJ⟩) := by
    have : (1 : ℝ) < (S.Q ⟨0, hJ⟩ : ℝ) := by
      have := (S.two_le_P ⟨0, hJ⟩).trans (S.P_le_Q ⟨0, hJ⟩)
      exact_mod_cast (by omega : 1 < S.Q ⟨0, hJ⟩)
    exact Real.log_pos this
  have h_eta_inv : 6 < 1 / η := by
    rw [lt_div_iff₀ hη0]
    linarith
  have h_ind : ∀ (k : ℕ) (hk : k < J), 0 < k → Real.log (S.Q ⟨0, hJ⟩) < Real.log (S.P ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero => intro _ hk0; omega
    | succ k ih =>
      intro hk _
      by_cases hk0 : k = 0
      · subst hk0
        have hcond := S.cond3 ⟨1, hk⟩ ⟨0, hJ⟩ rfl
        have hj_val : (((⟨1, hk⟩ : Fin J).val + 1 : ℕ) : ℝ) = 2 := rfl
        rw [hj_val] at hcond
        have h_coeff : 1 < 8 * (2 : ℝ) ^ 2 / η := by
          rw [div_eq_mul_one_div]
          calc (1 : ℝ)
            _ < 32 * 6 := by norm_num
            _ ≤ (8 * (2 : ℝ) ^ 2) * (1 / η) := mul_le_mul (by norm_num) (le_of_lt h_eta_inv) (by norm_num) (by positivity)
        have h_mul : Real.log (S.Q ⟨0, hJ⟩) < (8 * (2 : ℝ) ^ 2 / η) * Real.log (S.Q ⟨0, hJ⟩) := by
          calc Real.log (S.Q ⟨0, hJ⟩)
            _ = 1 * Real.log (S.Q ⟨0, hJ⟩) := by ring
            _ < (8 * (2 : ℝ) ^ 2 / η) * Real.log (S.Q ⟨0, hJ⟩) := mul_lt_mul_of_pos_right h_coeff hQ0_pos
        have h_pos_log : 0 ≤ 16 * Real.log (2 : ℝ) := by positivity
        linarith
      · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
        have hk_lt : k < J := by omega
        have ih_k := ih hk_lt hk_pos
        let i : Fin J := ⟨k, hk_lt⟩
        let j_cur : Fin J := ⟨k + 1, hk⟩
        have hij : i.val + 1 = j_cur.val := rfl
        have hcond := S.cond3 j_cur i hij
        have hPi_pos : (0 : ℝ) < S.P i := Nat.cast_pos.mpr (by linarith [S.two_le_P i])
        have hPi_le_Qi : (S.P i : ℝ) ≤ S.Q i := by exact_mod_cast (S.P_le_Q i)
        have h_logPi_le_logQi : Real.log (S.P i) ≤ Real.log (S.Q i) :=
          Real.log_le_log hPi_pos hPi_le_Qi
        have hj_ge : (1 : ℝ) ≤ ((j_cur.val + 1 : ℕ) : ℝ) := by
          have : 1 ≤ j_cur.val + 1 := by omega
          exact_mod_cast this
        have hj_sq : (1 : ℝ) ≤ ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
        have hj_eight : (8 : ℝ) ≤ 8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 := by linarith
        have h_coeff : 1 ≤ 8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 / η := by
          rw [div_eq_mul_one_div]
          calc (1 : ℝ)
            _ ≤ 8 * 6 := by norm_num
            _ ≤ (8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2) * (1 / η) := mul_le_mul hj_eight (le_of_lt h_eta_inv) (by norm_num) (by positivity)
        have hQi_pos : 0 < Real.log (S.Q i) := by
          calc 0 < Real.log (S.Q ⟨0, hJ⟩) := hQ0_pos
            _ < Real.log (S.P i) := ih_k
            _ ≤ Real.log (S.Q i) := h_logPi_le_logQi
        have h_bound : Real.log (S.Q i) ≤ (8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i) := by
          have : Real.log (S.Q i) = 1 * Real.log (S.Q i) := by ring
          nth_rw 1 [this]
          exact mul_le_mul_of_nonneg_right h_coeff (le_of_lt hQi_pos)
        have h_pos_log : 0 ≤ 16 * Real.log ((j_cur.val + 1 : ℕ) : ℝ) := by
          have : (1 : ℝ) ≤ ((j_cur.val + 1 : ℕ) : ℝ) := by linarith
          exact mul_nonneg (by norm_num) (Real.log_nonneg this)
        calc Real.log (S.Q ⟨0, hJ⟩)
          _ < Real.log (S.P i) := ih_k
          _ ≤ Real.log (S.Q i) := h_logPi_le_logQi
          _ ≤ (8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i) := h_bound
          _ ≤ (8 * ((j_cur.val + 1 : ℕ) : ℝ) ^ 2 / η) * Real.log (S.Q i) + 16 * Real.log ((j_cur.val + 1 : ℕ) : ℝ) := by linarith
          _ ≤ Real.log (S.P j_cur) := hcond
  exact h_ind j.val j.isLt hj

lemma RangeSystem.Q_zero_lt_P {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (hη0 : 0 < η) (hη : η < 1 / 6)
    (j : Fin J) (hj : 0 < j.val) : S.Q ⟨0, hJ⟩ < S.P j := by
  have hlog := RangeSystem.log_Q_zero_lt_log_P S hJ hη0 hη j hj
  have hQ0_pos : (0 : ℝ) < S.Q ⟨0, hJ⟩ := by
    have := (S.two_le_P ⟨0, hJ⟩).trans (S.P_le_Q ⟨0, hJ⟩)
    exact_mod_cast (by omega : 0 < S.Q ⟨0, hJ⟩)
  have h_le := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log hQ0_pos] at h_le
  have hPj_pos : (0 : ℝ) < S.P j := by
    have := S.two_le_P j
    exact_mod_cast (by omega : 0 < S.P j)
  rw [Real.exp_log hPj_pos] at h_le
  exact_mod_cast h_le

lemma RangeSystem.p_lt_q_of_mem_R {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (hη0 : 0 < η) (hη : η < 1 / 6)
    {p q : ℕ} (hp : p ∈ S.R ⟨0, hJ⟩) {j : Fin J} (hj : 0 < j.val) (hq : q ∈ S.R j) : p < q := by
  unfold RangeSystem.R primeRange at hp hq
  rw [Finset.mem_filter, Finset.mem_Icc] at hp hq
  have hp_le : p ≤ S.Q ⟨0, hJ⟩ := hp.1.2
  have hq_ge : S.P j ≤ q := hq.1.1
  have hQP := RangeSystem.Q_zero_lt_P S hJ hη0 hη j hj
  omega

def HasFactorExceptFirst (J : ℕ) (R : Fin J → Finset ℕ) (m : ℕ) : Prop :=
  ∀ j : Fin J, j.val ≠ 0 → ∃ q ∈ R j, q ∣ m

instance (J : ℕ) (R : Fin J → Finset ℕ) (m : ℕ) : Decidable (HasFactorExceptFirst J R m) := by
  unfold HasFactorExceptFirst
  infer_instance

lemma hasFactorInEach_mul_of_mem_R0 {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (hη0 : 0 < η) (hη : η < 1 / 6)
    {p m : ℕ} (hp : p ∈ S.R ⟨0, hJ⟩) :
    HasFactorInEach J S.R (p * m) ↔ HasFactorExceptFirst J S.R m := by
  constructor
  · intro h j hj
    obtain ⟨q, hq, hq_dvd⟩ := h j
    have hq_prime : q.Prime := by
      unfold RangeSystem.R primeRange at hq
      exact (Finset.mem_filter.mp hq).2
    have hp_prime : p.Prime := by
      unfold RangeSystem.R primeRange at hp
      exact (Finset.mem_filter.mp hp).2
    cases hq_prime.dvd_mul.mp hq_dvd with
    | inl hqp =>
      have hqp_eq : q = p := (Nat.dvd_prime hp_prime).mp hqp |>.resolve_left hq_prime.ne_one
      have hj_pos : 0 < j.val := Nat.pos_of_ne_zero hj
      have h_lt := RangeSystem.p_lt_q_of_mem_R S hJ hη0 hη hp hj_pos hq
      omega
    | inr hqm =>
      exact ⟨q, hq, hqm⟩
  · intro h j
    by_cases hj : j.val = 0
    · have hj_eq : j = ⟨0, hJ⟩ := by ext; exact hj
      rw [hj_eq]
      refine ⟨p, hp, dvd_mul_right p m⟩
    · obtain ⟨q, hq, hqm⟩ := h j hj
      exact ⟨q, hq, dvd_mul_of_dvd_right hqm p⟩

lemma factor_F_coeff {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (hη0 : 0 < η) (hη : η < 1 / 6)
    (β : ℝ) (X : ℕ) (hQX : (S.Q ⟨0, hJ⟩ : ℝ) ≤ (X : ℝ) ^ β)
    {p m : ℕ} (hp : p ∈ primeRange (S.P ⟨0, hJ⟩) (S.Q ⟨0, hJ⟩)) (hpm : ¬ p ∣ m) :
    (if HasFactorInEach J S.R (p * m) then fX β X (p * m) else 0) =
      (if HasFactorExceptFirst J S.R m then fX β X m else 0) * (fX β X p) := by
  have hp_prime : p.Prime := (Finset.mem_filter.mp hp).2
  have hp_le_Q : p ≤ S.Q ⟨0, hJ⟩ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
  have hp_le_X : (p : ℝ) ≤ (X : ℝ) ^ β := by
    have : (p : ℝ) ≤ (S.Q ⟨0, hJ⟩ : ℝ) := by exact_mod_cast hp_le_Q
    linarith
  have hm_pos : 0 < m := by
    by_contra hm
    have : m = 0 := by omega
    subst this
    exact hpm (dvd_zero p)
  have hfX_pm : fX β X (p * m) = fX β X m := fX_mul_of_prime_le β X p m hp_prime hm_pos hp_le_X
  have hfX_p : fX β X p = 1 := fX_prime_eq_one β X p hp_prime hp_le_X
  have hp_in_R : p ∈ S.R ⟨0, hJ⟩ := hp
  have h_has := hasFactorInEach_mul_of_mem_R0 S hJ hη0 hη hp_in_R (m := m)
  rw [hfX_pm, hfX_p, mul_one]
  by_cases h : HasFactorExceptFirst J S.R m
  · have h2 : HasFactorInEach J S.R (p * m) := h_has.mpr h
    simp [h, h2]
  · have h2 : ¬ HasFactorInEach J S.R (p * m) := fun h_in => h (h_has.mp h_in)
    simp [h, h2]

lemma dirichletPoly_coeffF_eq_F (β : ℝ) (J : ℕ) (R : Fin J → Finset ℕ) (X : ℕ) (s : ℂ) :
    dirichletPoly (fun n => if HasFactorInEach J R n then fX β X n else 0) (Finset.Ioc X (2 * X)) s =
      F β J R X s := by
  unfold F dirichletPoly coeffF siftedSet
  apply Finset.sum_congr rfl
  intro n hn
  have h_mem : (n ∈ Finset.filter (HasFactorInEach J R) (Finset.Ioc X (2 * X))) ↔ HasFactorInEach J R n := by
    rw [Finset.mem_filter]
    simp [hn]
  by_cases h : HasFactorInEach J R n
  · have h2 : n ∈ Finset.filter (HasFactorInEach J R) (Finset.Ioc X (2 * X)) := h_mem.mpr h
    simp [h, h2]
  · have h2 : n ∉ Finset.filter (HasFactorInEach J R) (Finset.Ioc X (2 * X)) := fun h_in => h (h_mem.mp h_in)
    simp [h, h2]

lemma exp_div_H_le_three_mul_Q (H : ℝ) (Q : ℕ) (v : ℕ) (hH : 1 ≤ H) (hQ : 1 ≤ Q)
    (hv : v ≤ ⌈H * Real.log Q⌉₊) :
    Real.exp (v / H) ≤ 3 * (Q : ℝ) := by
  have hH_pos : 0 < H := by linarith
  have hQ_pos : 0 < (Q : ℝ) := Nat.cast_pos.mpr hQ
  have hlogQ_nonneg : 0 ≤ Real.log (Q : ℝ) := Real.log_nonneg (by exact_mod_cast hQ)
  have hHlogQ_nonneg : 0 ≤ H * Real.log (Q : ℝ) := mul_nonneg (by linarith) hlogQ_nonneg
  have hv_le : (v : ℝ) ≤ H * Real.log (Q : ℝ) + 1 := by
    have h1 : (v : ℝ) ≤ (⌈H * Real.log (Q : ℝ)⌉₊ : ℝ) := by exact_mod_cast hv
    have h2 : (⌈H * Real.log (Q : ℝ)⌉₊ : ℝ) < H * Real.log (Q : ℝ) + 1 :=
      Nat.ceil_lt_add_one hHlogQ_nonneg
    linarith
  have h_div : (v : ℝ) / H ≤ Real.log (Q : ℝ) + 1 := by
    calc (v : ℝ) / H
      _ ≤ (H * Real.log (Q : ℝ) + 1) / H := div_le_div_of_nonneg_right hv_le (le_of_lt hH_pos)
      _ = Real.log (Q : ℝ) + 1 / H := by
        rw [add_div, mul_div_cancel_left₀ (Real.log (Q : ℝ)) hH_pos.ne']
      _ ≤ Real.log (Q : ℝ) + 1 := by
        have : 1 / H ≤ 1 := by
          rw [div_le_iff₀ hH_pos]
          linarith
        linarith
  have h_exp := Real.exp_le_exp.mpr h_div
  rw [Real.exp_add, Real.exp_log hQ_pos] at h_exp
  have h_e3 : Real.exp 1 < 3 := Real.exp_one_lt_three
  calc Real.exp (v / H)
    _ ≤ (Q : ℝ) * Real.exp 1 := h_exp
    _ ≤ (Q : ℝ) * 3 := mul_le_mul_of_nonneg_left (le_of_lt h_e3) (le_of_lt hQ_pos)
    _ = 3 * (Q : ℝ) := by ring

lemma norm_b_div_omega_le_one (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (P Q m : ℕ) :
    ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ≤ 1 := by
  rw [norm_div]
  have h_eq : (omegaIn (primeRange P Q) m : ℂ) + 1 = ((omegaIn (primeRange P Q) m + 1 : ℕ) : ℂ) := by push_cast; rfl
  rw [h_eq, Complex.norm_natCast]
  have h_den : 1 ≤ ((omegaIn (primeRange P Q) m + 1 : ℕ) : ℝ) := by
    have : 1 ≤ omegaIn (primeRange P Q) m + 1 := by omega
    exact_mod_cast this
  have h_num := hb m
  have h_den_pos : 0 < ((omegaIn (primeRange P Q) m + 1 : ℕ) : ℝ) := by linarith
  exact (div_le_iff₀ h_den_pos).mpr (by linarith)

lemma sum_norm_sq_b_div_omega_le (X : ℕ) (H : ℝ) (v : ℕ) (P Q : ℕ) (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hX : 1 ≤ X) :
    (∑ m ∈ cofactorRange X H v, ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2) ≤
      2 * Real.exp (v / H) / (X : ℝ) := by
  let S := cofactorRange X H v
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
  have hexp_pos : 0 < Real.exp (-(v / H)) := Real.exp_pos _
  have hprod_pos : 0 < (X : ℝ) * Real.exp (-(v / H)) := mul_pos hX_pos hexp_pos
  have h_bound_m : ∀ m ∈ S, ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2 ≤
      1 / (X * Real.exp (-(v / H))) ^ 2 := by
    intro m hm
    dsimp [S] at hm
    unfold cofactorRange at hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    have hm_gt : X * Real.exp (-(v / H)) < (m : ℝ) := hm.2
    have hm_sq : (X * Real.exp (-(v / H))) ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith [hm_gt, hprod_pos]
    have h_norm : ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 ≤ 1 := by
      have := norm_b_div_omega_le_one b hb P Q m
      nlinarith [norm_nonneg (b m / ((omegaIn (primeRange P Q) m : ℂ) + 1))]
    have h1 : ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right h_norm (by positivity)
    have h2 : 1 / (m : ℝ) ^ 2 ≤ 1 / (X * Real.exp (-(v / H))) ^ 2 :=
      one_div_le_one_div_of_le (by positivity) hm_sq
    exact h1.trans h2
  have h_sum := Finset.sum_le_sum h_bound_m
  have h_card_sum : (∑ _m ∈ S, 1 / (X * Real.exp (-(v / H))) ^ 2) =
      (S.card : ℝ) * (1 / (X * Real.exp (-(v / H))) ^ 2) := by
    simp [nsmul_eq_mul]
  rw [h_card_sum] at h_sum
  have hS_sub : S ⊆ Finset.Ioc 0 ⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊ := by
    intro m hm
    dsimp [S] at hm
    unfold cofactorRange at hm
    exact (Finset.mem_filter.mp hm).1
  have h_card_le : (S.card : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(v / H)) := by
    have h1 : S.card ≤ (Finset.Ioc 0 ⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊).card := Finset.card_le_card hS_sub
    rw [Nat.card_Ioc, Nat.sub_zero] at h1
    have h2 : (⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊ : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(v / H)) :=
      Nat.floor_le (by positivity)
    exact (Nat.cast_le.mpr h1).trans h2
  have h_nonneg : 0 ≤ 1 / (X * Real.exp (-(v / H))) ^ 2 := by positivity
  have h_mul_card := mul_le_mul_of_nonneg_right h_card_le h_nonneg
  have h_alg : 2 * (X : ℝ) * Real.exp (-(v / H)) * (1 / (X * Real.exp (-(v / H))) ^ 2) =
      2 * Real.exp (v / H) / (X : ℝ) := by
    have h_sq : (X * Real.exp (-(v / H))) ^ 2 = (X * Real.exp (-(v / H))) * (X * Real.exp (-(v / H))) := sq _
    rw [h_sq, div_mul_eq_div_mul_one_div, ← mul_assoc]
    have h_cancel : 2 * (X : ℝ) * Real.exp (-(v / H)) * (1 / (X * Real.exp (-(v / H)))) = 2 := by
      calc 2 * (X : ℝ) * Real.exp (-(v / H)) * (1 / (X * Real.exp (-(v / H))))
        _ = 2 * ((X : ℝ) * Real.exp (-(v / H)) * (1 / (X * Real.exp (-(v / H))))) := by ring
        _ = 2 * 1 := by rw [mul_one_div_cancel hprod_pos.ne']
        _ = 2 := by ring
    rw [h_cancel]
    have h_exp_neg : Real.exp (-(v / H)) = (Real.exp (v / H))⁻¹ := Real.exp_neg _
    rw [h_exp_neg]
    rw [div_mul_eq_div_mul_one_div]
    field_simp
  calc (∑ m ∈ S, ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2)
    _ ≤ (S.card : ℝ) * (1 / (X * Real.exp (-(v / H))) ^ 2) := h_sum
    _ ≤ 2 * (X : ℝ) * Real.exp (-(v / H)) * (1 / (X * Real.exp (-(v / H))) ^ 2) := h_mul_card
    _ = 2 * Real.exp (v / H) / (X : ℝ) := h_alg

lemma integral_norm_sq_Rv_le (X P Q : ℕ) (H : ℝ) (v : ℕ) (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (T : ℝ)
    (hT : 0 ≤ T) (hX : 1 ≤ X) (hQ : 1 ≤ Q) (hH : 1 ≤ H) (hv : v ≤ ⌈H * Real.log Q⌉₊) :
    ∫ t in (-T)..T, ‖dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1) := by
  let S := cofactorRange X H v
  let N := ⌊2 * (X : ℝ) * Real.exp (-(v / H))⌋₊
  have hS_sub : S ⊆ Finset.Ioc 0 N := by
    intro m hm
    dsimp [S] at hm
    unfold cofactorRange at hm
    exact (Finset.mem_filter.mp hm).1
  have h_mvt := integral_norm_sq_dirichletPoly_subset_le (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) S N hS_sub T hT
  have h_sum := sum_norm_sq_b_div_omega_le X H v P Q b hb hX
  have hN_le : (N : ℝ) ≤ 2 * (X : ℝ) * Real.exp (-(v / H)) := Nat.floor_le (by positivity)
  have h_factor : 2 * T + 6 * Real.pi * (N : ℝ) ≤ 2 * T + 12 * Real.pi * (X : ℝ) * Real.exp (-(v / H)) := by
    have : 6 * Real.pi * (N : ℝ) ≤ 6 * Real.pi * (2 * (X : ℝ) * Real.exp (-(v / H))) :=
      mul_le_mul_of_nonneg_left hN_le (by positivity)
    linarith
  have h_sum_nonneg : 0 ≤ ∑ m ∈ S, ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2 := by
    apply Finset.sum_nonneg
    intro i _
    positivity
  have h_prod_le := mul_le_mul h_factor h_sum h_sum_nonneg (by positivity)
  have h_exp_mul : Real.exp (-(v / H)) * Real.exp (v / H) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hX_pos : 0 < (X : ℝ) := by exact_mod_cast hX
  have h_alg : (2 * T + 12 * Real.pi * (X : ℝ) * Real.exp (-(v / H))) * (2 * Real.exp (v / H) / (X : ℝ)) =
      4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi := by
    calc (2 * T + 12 * Real.pi * (X : ℝ) * Real.exp (-(v / H))) * (2 * Real.exp (v / H) / (X : ℝ))
      _ = 2 * T * (2 * Real.exp (v / H) / (X : ℝ)) + 12 * Real.pi * (X : ℝ) * Real.exp (-(v / H)) * (2 * Real.exp (v / H) / (X : ℝ)) := by ring
      _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi * ((X : ℝ) * (Real.exp (-(v / H)) * Real.exp (v / H)) / (X : ℝ)) := by ring
      _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi * ((X : ℝ) * 1 / (X : ℝ)) := by rw [h_exp_mul]
      _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi * ((X : ℝ) / (X : ℝ)) := by ring
      _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi * 1 := by rw [div_self hX_pos.ne']
      _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi := by ring
  have h_exp_Q := exp_div_H_le_three_mul_Q H Q v hH hQ hv
  have h_term_T : 4 * T * Real.exp (v / H) / (X : ℝ) ≤ 12 * (T / ((X : ℝ) / Q)) := by
    have h_div_Q : T / ((X : ℝ) / Q) = T * (Q : ℝ) / (X : ℝ) := div_div_eq_mul_div T (X : ℝ) (Q : ℝ)
    rw [h_div_Q]
    have h1 : 4 * T * Real.exp (v / H) ≤ 4 * T * (3 * (Q : ℝ)) :=
      mul_le_mul_of_nonneg_left h_exp_Q (by positivity)
    have : 4 * T * (3 * (Q : ℝ)) = 12 * (T * (Q : ℝ)) := by ring
    rw [this] at h1
    have h2 : 4 * T * Real.exp (v / H) / (X : ℝ) ≤ 12 * (T * (Q : ℝ)) / (X : ℝ) :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have : 12 * (T * (Q : ℝ)) / (X : ℝ) = 12 * (T * (Q : ℝ) / (X : ℝ)) := by ring
    linarith
  have h_final : 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi ≤ (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1) := by
    calc 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi
      _ ≤ 12 * (T / ((X : ℝ) / Q)) + 24 * Real.pi := by linarith
      _ ≤ 12 * (T / ((X : ℝ) / Q)) + 24 * Real.pi * (T / ((X : ℝ) / Q)) + (12 + 24 * Real.pi) := by
        have : 0 ≤ 24 * Real.pi * (T / ((X : ℝ) / Q)) := by positivity
        linarith
      _ = (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1) := by ring
  calc ∫ t in (-T)..T, ‖dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) S ((1 : ℂ) + t * Complex.I)‖ ^ 2
    _ ≤ (2 * T + 6 * Real.pi * (N : ℝ)) * ∑ m ∈ S, ‖b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ^ 2 / (m : ℝ) ^ 2 := h_mvt
    _ ≤ (2 * T + 12 * Real.pi * (X : ℝ) * Real.exp (-(v / H))) * (2 * Real.exp (v / H) / (X : ℝ)) := h_prod_le
    _ = 4 * T * Real.exp (v / H) / (X : ℝ) + 24 * Real.pi := h_alg
    _ ≤ (12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1) := h_final

lemma integral_norm_sq_QR_v_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J)
    (β : ℝ) (X : ℕ) (T₀ T : ℝ) (hX : 1 ≤ X) (hT0 : 0 ≤ T₀) (hT : T₀ ≤ T)
    (hH1 : 1 ≤ S.Hj hJ ⟨0, hJ⟩) (b : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (v : ℕ) (hv : v ∈ S.Ij hJ ⟨0, hJ⟩) :
    let P := S.P ⟨0, hJ⟩
    let Q := S.Q ⟨0, hJ⟩
    let H := S.Hj hJ ⟨0, hJ⟩
    let U := S.Tset hJ β X T₀ T ⟨0, hJ⟩
    ∫ t in U, ‖dirichletPoly (fX β X) (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
        dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      Real.exp (-2 * (alpha η 1) * v / H) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) := by
  intro P Q H U
  have hT_nonneg : 0 ≤ T := hT0.trans hT
  have hU_sub : U ⊆ Set.Icc (-T) T := by
    intro t ht
    have ht_in := ht.1
    exact ⟨by linarith [hT0, ht_in.1], ht_in.2⟩
  have hU_meas : MeasurableSet U := S.measurableSet_Tset hJ β X T₀ T ⟨0, hJ⟩
  let c := fX β X
  let b_omega := fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)
  let Qv (t : ℝ) := dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I)
  let Rv (t : ℝ) := dirichletPoly b_omega (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)
  have h_pt_le : ∀ t ∈ U, ‖Qv t * Rv t‖ ^ 2 ≤ Real.exp (-2 * (alpha η 1) * v / H) * ‖Rv t‖ ^ 2 := by
    intro t ht
    dsimp [Qv, Rv]
    rw [norm_mul, mul_pow]
    have ht_good := ht.2.1
    unfold RangeSystem.Good at ht_good
    have hQ_le := ht_good v hv
    change ‖Qv t‖ ≤ Real.exp (-(alpha η 1) * v / H) at hQ_le
    have hQ_sq : ‖Qv t‖ ^ 2 ≤ Real.exp (-2 * (alpha η 1) * v / H) := by
      have h1 : ‖Qv t‖ ^ 2 ≤ (Real.exp (-(alpha η 1) * v / H)) ^ 2 := by
        nlinarith [norm_nonneg (Qv t)]
      have h2 : (Real.exp (-(alpha η 1) * v / H)) ^ 2 = Real.exp (-2 * (alpha η 1) * v / H) := by
        rw [← Real.exp_nat_mul]
        ring_nf
      rwa [h2] at h1
    exact mul_le_mul_of_nonneg_right hQ_sq (sq_nonneg _)
  have hCont_Rv : Continuous (fun t => ‖Rv t‖ ^ 2) := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_dirichletPoly_l12
    intro n hn
    unfold cofactorRange at hn
    exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  have hCont_Qv : Continuous (fun t => ‖Qv t‖ ^ 2) := by
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_dirichletPoly_l12
    intro n hn
    unfold shortPrimeRange primeRange at hn
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    have := hn.1.2.two_le
    omega
  have hCont_QR : Continuous (fun t => ‖Qv t * Rv t‖ ^ 2) := by
    have : (fun t => ‖Qv t * Rv t‖ ^ 2) = (fun t => ‖Qv t‖ ^ 2 * ‖Rv t‖ ^ 2) := by
      ext t
      rw [norm_mul, mul_pow]
    rw [this]
    exact hCont_Qv.mul hCont_Rv
  have hInt_QR : IntegrableOn (fun t => ‖Qv t * Rv t‖ ^ 2) U :=
    hCont_QR.integrableOn_Icc.mono_set hU_sub
  have hInt_Rv : IntegrableOn (fun t => ‖Rv t‖ ^ 2) U :=
    hCont_Rv.integrableOn_Icc.mono_set hU_sub
  have hInt_exp_Rv : IntegrableOn (fun t => Real.exp (-2 * (alpha η 1) * v / H) * ‖Rv t‖ ^ 2) U :=
    hInt_Rv.const_mul _
  have h_step1 : ∫ t in U, ‖Qv t * Rv t‖ ^ 2 ≤
      Real.exp (-2 * (alpha η 1) * v / H) * ∫ t in U, ‖Rv t‖ ^ 2 := by
    have h1 := setIntegral_mono_on hInt_QR hInt_exp_Rv hU_meas h_pt_le
    rw [MeasureTheory.integral_const_mul] at h1
    exact h1
  have h_step2 : ∫ t in U, ‖Rv t‖ ^ 2 ≤ ∫ t in (-T)..T, ‖Rv t‖ ^ 2 := by
    apply setIntegral_norm_sq_dirichletPoly_le b_omega (cofactorRange X H v) (by
      intro n hn
      unfold cofactorRange at hn
      exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1) T hT_nonneg U hU_meas hU_sub
  have hQ_ge1 : 1 ≤ Q := by
    have : 2 ≤ Q := (S.two_le_P ⟨0, hJ⟩).trans (S.P_le_Q ⟨0, hJ⟩)
    omega
  have hv_le : v ≤ ⌈H * Real.log Q⌉₊ := (Finset.mem_Icc.mp hv).2
  have h_step3 := integral_norm_sq_Rv_le X P Q H v b hb T hT_nonneg hX hQ_ge1 hH1 hv_le
  calc ∫ t in U, ‖Qv t * Rv t‖ ^ 2
    _ ≤ Real.exp (-2 * (alpha η 1) * v / H) * ∫ t in U, ‖Rv t‖ ^ 2 := h_step1
    _ ≤ Real.exp (-2 * (alpha η 1) * v / H) * ∫ t in (-T)..T, ‖Rv t‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h_step2 (by positivity)
    _ ≤ Real.exp (-2 * (alpha η 1) * v / H) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) :=
      mul_le_mul_of_nonneg_left h_step3 (by positivity)

theorem RangeSystem.integral_Tset_zero_le {J : ℕ} {η : ℝ} (S : RangeSystem J η) (hJ : 0 < J) (hη0 : 0 < η) (hη : η < 1 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (X : ℕ) (T₀ T : ℝ), 3 / 4 ≤ β → β < 1 → 2 ≤ X → 0 ≤ T₀ → T₀ ≤ T →
      (∀ j, (S.Q j : ℝ) ≤ (X : ℝ) ^ β) → (S.Q ⟨0, hJ⟩ : ℝ) ^ 4 ≤ X → 1 ≤ S.Hj hJ ⟨0, hJ⟩ → S.Hj hJ ⟨0, hJ⟩ ≤ Real.sqrt (S.P ⟨0, hJ⟩) →
      ∫ t in S.Tset hJ β X T₀ T ⟨0, hJ⟩, ‖F β J S.R X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (T / ((X : ℝ) / S.Q ⟨0, hJ⟩) + 1) * ((Real.log (S.Q ⟨0, hJ⟩)) ^ (1 / 3 : ℝ) / (S.P ⟨0, hJ⟩ : ℝ) ^ (1 / 6 - η))
        + C * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange (S.P ⟨0, hJ⟩) (S.Q ⟨0, hJ⟩), ¬ p ∣ n)).card : ℝ) / X := by
  obtain ⟨C_L12, hC_L12_pos, hL12⟩ := integral_norm_sq_F_le_sum_QR
  let P := S.P ⟨0, hJ⟩
  let Q := S.Q ⟨0, hJ⟩
  let H := S.Hj hJ ⟨0, hJ⟩
  let V := S.Ij hJ ⟨0, hJ⟩
  let K_sum := ∑ v ∈ V, Real.exp (-2 * (alpha η 1) * v / H)
  let K_1 := C_L12 * (H * Real.log Q) * (12 + 24 * Real.pi) * K_sum
  let K_2 := C_L12 * (1 / H + 1 / (P : ℝ))
  have hP_pos : 0 < (P : ℝ) := by
    have := S.two_le_P ⟨0, hJ⟩
    exact_mod_cast (by omega : 0 < P)
  have hQ_gt1 : (1 : ℝ) < (Q : ℝ) := by
    have := (S.two_le_P ⟨0, hJ⟩).trans (S.P_le_Q ⟨0, hJ⟩)
    exact_mod_cast (by omega : 1 < Q)
  have hlogQ_pos : 0 < Real.log (Q : ℝ) := Real.log_pos hQ_gt1
  have hW_pos : 0 < (Real.log (Q : ℝ)) ^ (1 / 3 : ℝ) / (P : ℝ) ^ (1 / 6 - η) :=
    div_pos (Real.rpow_pos_of_pos hlogQ_pos _) (Real.rpow_pos_of_pos hP_pos _)
  let W := (Real.log (Q : ℝ)) ^ (1 / 3 : ℝ) / (P : ℝ) ^ (1 / 6 - η)
  let C := max ((K_1 + K_2) / W) C_L12 + 1
  have hC_pos : 0 < C := by
    have : 0 < max ((K_1 + K_2) / W) C_L12 := lt_of_lt_of_le hC_L12_pos (le_max_right _ _)
    linarith
  use C
  refine ⟨hC_pos, ?_⟩
  intro β X T₀ T hβ hβ1 hX hT0 hT hQX_all hQ4 hH1 hHP
  have hX1 : 1 ≤ X := by omega
  have hP2 : 2 ≤ P := S.two_le_P ⟨0, hJ⟩
  have hPQ : P ≤ Q := S.P_le_Q ⟨0, hJ⟩
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
  let U := S.Tset hJ β X T₀ T ⟨0, hJ⟩
  have hU_meas : MeasurableSet U := S.measurableSet_Tset hJ β X T₀ T ⟨0, hJ⟩
  have hU_sub : U ⊆ Set.Icc (-T) T := by
    intro t ht
    have ht_in := ht.1
    exact ⟨by linarith [hT0, ht_in.1], ht_in.2⟩
  let a := fun n => if HasFactorInEach J S.R n then fX β X n else 0
  let b := fun m => if HasFactorExceptFirst J S.R m then fX β X m else 0
  let c := fX β X
  have ha : ∀ n, ‖a n‖ ≤ 1 := by
    intro n
    dsimp [a]
    split_ifs
    · exact norm_fX_le_one β X n
    · simp
  have hb : ∀ m, ‖b m‖ ≤ 1 := by
    intro m
    dsimp [b]
    split_ifs
    · exact norm_fX_le_one β X m
    · simp
  have hc : ∀ p, ‖c p‖ ≤ 1 := fun p => norm_fX_le_one β X p
  have hfactor : ∀ p m, p ∈ primeRange P Q → ¬ p ∣ m → a (p * m) = b m * c p :=
    fun p m hp hpm => factor_F_coeff S hJ hη0 hη β X (hQX_all ⟨0, hJ⟩) hp hpm
  have h_l12 := hL12 X P Q H a b c T U hX1 hP2 hPQ hQX hP4 hH1 hT_pos hU_meas hU_sub ha hb hc hfactor
  have h_poly_eq : ∀ t, ‖dirichletPoly a (Finset.Ioc X (2 * X)) ((1 : ℂ) + t * Complex.I)‖ ^ 2 =
      ‖F β J S.R X ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    intro t
    rw [dirichletPoly_coeffF_eq_F β J S.R X ((1 : ℂ) + t * Complex.I)]
  simp_rw [h_poly_eq] at h_l12
  have h_sum_QR_v : ∀ v ∈ V,
      ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        Real.exp (-2 * (alpha η 1) * v / H) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) :=
    fun v hv => integral_norm_sq_QR_v_le S hJ β X T₀ T hX1 hT0 hT hH1 b hb v hv
  have h_sum_le : (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      K_sum * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) := by
    have h_sum_ineq := Finset.sum_le_sum h_sum_QR_v
    have h_factor_sum : (∑ v ∈ V, Real.exp (-2 * (alpha η 1) * v / H) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1))) =
        (∑ v ∈ V, Real.exp (-2 * (alpha η 1) * v / H)) * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1)) := by
      rw [← Finset.sum_mul]
    rw [h_factor_sum] at h_sum_ineq
    exact h_sum_ineq
  have h_term1_le : C_L12 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      K_1 * (T / ((X : ℝ) / Q) + 1) := by
    have hH_logQ : 0 ≤ C_L12 * (H * Real.log Q) := by
      have : 0 ≤ Real.log (Q : ℝ) := le_of_lt hlogQ_pos
      positivity
    have h_mul := mul_le_mul_of_nonneg_left h_sum_le hH_logQ
    calc C_L12 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
          dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2)
      _ ≤ C_L12 * (H * Real.log Q) * (K_sum * ((12 + 24 * Real.pi) * (T / ((X : ℝ) / Q) + 1))) := h_mul
      _ = K_1 * (T / ((X : ℝ) / Q) + 1) := by
        dsimp [K_1]
        ring
  have h_X_Q : T / (X : ℝ) + 1 ≤ T / ((X : ℝ) / Q) + 1 := by
    have h1 : T / (X : ℝ) ≤ T / ((X : ℝ) / Q) := by
      have h_div_Q : T / ((X : ℝ) / Q) = T * (Q : ℝ) / (X : ℝ) := div_div_eq_mul_div T (X : ℝ) (Q : ℝ)
      rw [h_div_Q]
      have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (show 1 ≤ Q by omega)
      have : T * 1 ≤ T * (Q : ℝ) := mul_le_mul_of_nonneg_left hQ1 hT_pos
      rw [mul_one] at this
      exact div_le_div_of_nonneg_right this (by positivity)
    linarith
  have h_term2_split : C_L12 * (T / X + 1) * (1 / H + 1 / (P : ℝ) + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) =
      K_2 * (T / X + 1) + C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by
    dsimp [K_2]
    ring
  have h_term2_le : K_2 * (T / X + 1) ≤ K_2 * (T / ((X : ℝ) / Q) + 1) := by
    have hK2_pos : 0 ≤ K_2 := by
      dsimp [K_2]
      positivity
    exact mul_le_mul_of_nonneg_left h_X_Q hK2_pos
  have h_sum_main : K_1 * (T / ((X : ℝ) / Q) + 1) + K_2 * (T / ((X : ℝ) / Q) + 1) ≤
      C * (T / ((X : ℝ) / Q) + 1) * W := by
    have h_factor : K_1 * (T / ((X : ℝ) / Q) + 1) + K_2 * (T / ((X : ℝ) / Q) + 1) =
        (K_1 + K_2) * (T / ((X : ℝ) / Q) + 1) := by ring
    rw [h_factor]
    have hC_ge : (K_1 + K_2) / W ≤ C := by
      have : (K_1 + K_2) / W ≤ max ((K_1 + K_2) / W) C_L12 := le_max_left _ _
      linarith
    have h_K12 : (K_1 + K_2) ≤ C * W := by
      have := (div_le_iff₀ hW_pos).mp hC_ge
      linarith
    have h_T_nonneg : 0 ≤ T / ((X : ℝ) / Q) + 1 := by positivity
    calc (K_1 + K_2) * (T / ((X : ℝ) / Q) + 1)
      _ ≤ (C * W) * (T / ((X : ℝ) / Q) + 1) := mul_le_mul_of_nonneg_right h_K12 h_T_nonneg
      _ = C * (T / ((X : ℝ) / Q) + 1) * W := by ring
  have h_unsifted_le : C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X ≤
      C * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by
    have hC_ge_L12 : C_L12 ≤ C := by
      have : C_L12 ≤ max ((K_1 + K_2) / W) C_L12 := le_max_right _ _
      linarith
    have h_card_pos : 0 ≤ (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by positivity
    have h_TX_pos : 0 ≤ T / (X : ℝ) + 1 := by positivity
    have : 0 ≤ (T / (X : ℝ) + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by positivity
    calc C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X
      _ = C_L12 * ((T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := by ring
      _ ≤ C * ((T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) :=
        mul_le_mul_of_nonneg_right hC_ge_L12 this
      _ = C * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by ring
  have h_step_bound : ∫ t in U, ‖F β J S.R X ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      C * (T / ((X : ℝ) / Q) + 1) * W +
        C * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by
    calc ∫ t in U, ‖F β J S.R X ((1 : ℂ) + t * Complex.I)‖ ^ 2
      _ ≤ C_L12 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
          C_L12 * (T / X + 1) * (1 / H + 1 / (P : ℝ) + (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := h_l12
      _ = C_L12 * (H * Real.log Q) * (∑ v ∈ V, ∫ t in U, ‖dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
            dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2) +
          (K_2 * (T / X + 1) + C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := by rw [h_term2_split]
      _ ≤ K_1 * (T / ((X : ℝ) / Q) + 1) +
          (K_2 * (T / ((X : ℝ) / Q) + 1) + C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X) := by
        linarith [h_term1_le, h_term2_le]
      _ = (K_1 * (T / ((X : ℝ) / Q) + 1) + K_2 * (T / ((X : ℝ) / Q) + 1)) +
          C_L12 * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by ring
      _ ≤ C * (T / ((X : ℝ) / Q) + 1) * W +
          C * (T / X + 1) * (((Finset.Ioc X (2 * X)).filter (fun n => ∀ p ∈ primeRange P Q, ¬ p ∣ n)).card : ℝ) / X := by
        linarith [h_sum_main, h_unsifted_le]
  exact h_step_bound

end Erdos1201.MR
