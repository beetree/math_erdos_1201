import Mathlib
import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.MR.Ramare
import Erdos1201.MR.Arithmetic

open scoped Classical
open Erdos1201.MR

/-!
# Pointwise Bound on Dirichlet Polynomial with Ramaré Coefficients

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the pointwise bound on a Dirichlet polynomial with Ramaré-factorisable
coefficients in terms of prime sums over dyadic ranges.
-/

namespace Erdos1201.MR

lemma mem_S_iff (Z : ℝ) (hZ : 0 ≤ Z) (Y : ℕ) (p : ℕ) :
    p ∈ (Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime ↔ p.Prime ∧ Z < (p : ℝ) ∧ p ≤ 2 * Y := by
  rw [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hZ1, hpY⟩, hp⟩
    refine ⟨hp, ?_, hpY⟩
    have : (⌊Z⌋₊ : ℝ) < (p : ℝ) := by exact_mod_cast hZ1
    calc Z < (⌊Z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Z
      _ ≤ (p : ℝ) := by exact_mod_cast hZ1
  · rintro ⟨hp, hZ1, hpY⟩
    refine ⟨⟨?_, hpY⟩, hp⟩
    exact (Nat.floor_lt hZ).mpr hZ1

lemma divisorsIn_S_eq (Z : ℝ) (hZ : 0 ≤ Z) (Y : ℕ) (n : ℕ) (hn0 : n ≠ 0) (hn : n ≤ 2 * Y) :
    divisorsIn ((Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime) n =
      n.primeFactors.filter (fun (p : ℕ) => Z < (p : ℝ)) := by
  ext p
  unfold divisorsIn
  simp only [Finset.mem_filter, mem_S_iff Z hZ Y, Nat.mem_primeFactors]
  constructor
  · rintro ⟨⟨hp, hZ1, _⟩, hdvd⟩
    exact ⟨⟨hp, hdvd, hn0⟩, hZ1⟩
  · rintro ⟨⟨hp, hdvd, _⟩, hZ1⟩
    have hp_le_n : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
    exact ⟨⟨hp, hZ1, hp_le_n.trans hn⟩, hdvd⟩

lemma filter_omegaIn_zero_eq (Z : ℝ) (hZ : 0 ≤ Z) (Y : ℕ) :
    let S := (Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime
    let T := Finset.Ioc Y (2 * Y)
    T.filter (fun n => omegaIn S n = 0) =
      T.filter (fun n => ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Z) := by
  intro S T
  apply Finset.filter_congr
  intro n hn
  rw [Finset.mem_Ioc] at hn
  have hn0 : n ≠ 0 := by omega
  have hnY : n ≤ 2 * Y := hn.2
  unfold omegaIn
  rw [divisorsIn_S_eq Z hZ Y n hn0 hnY]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h p hp hdiv
    have hp_mem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hdiv, hn0⟩
    have hp_not := h hp_mem
    exact not_lt.mp hp_not
  · intro h p hp_mem
    rw [Nat.mem_primeFactors] at hp_mem
    have hp_le := h p hp_mem.1 hp_mem.2.1
    exact not_lt.mpr hp_le

lemma norm_u0_le (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (Z : ℝ) (hZ : 0 ≤ Z) (Y : ℕ) (hY : 2 ≤ Y) (t : ℝ) :
    let S := (Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime
    let T := Finset.Ioc Y (2 * Y)
    let s := (1 : ℂ) + (t : ℝ) * Complex.I
    ‖∑ n ∈ T.filter (fun n => omegaIn S n = 0), c n * (n : ℂ) ^ (-s)‖ ≤
      ∑ n ∈ T.filter (fun n => ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Z), (1 : ℝ) / n := by
  intro S T s
  have _ := hY
  rw [filter_omegaIn_zero_eq Z hZ Y]
  have h_tri := norm_sum_le (T.filter (fun n => ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Z))
    (fun n => c n * (n : ℂ) ^ (-s))
  refine h_tri.trans ?_
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Ioc] at hn
  have hn_pos : 0 < n := by omega
  rw [norm_mul, norm_natCast_cpow_neg_one_add_mul_I n hn_pos t]
  have hc_n := hc n
  have hn_r_pos : 0 ≤ 1 / (n : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_right hc_n hn_r_pos
  rw [one_mul] at h
  exact h

lemma cofactors_Ioc_eq (Y p : ℕ) (hp : 0 < p) :
    cofactors (Finset.Ioc Y (2 * Y)) p = Finset.Ioc (Y / p) (2 * Y / p) := by
  ext m
  unfold cofactors
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨n, ⟨⟨hY, h2Y⟩, hdvd⟩, rfl⟩
    refine ⟨(Nat.div_lt_iff_lt_mul hp).mpr ?_, (Nat.le_div_iff_mul_le hp).mpr ?_⟩
    · rw [Nat.div_mul_cancel hdvd]; exact hY
    · rw [Nat.div_mul_cancel hdvd]; exact h2Y
  · rintro ⟨h1, h2⟩
    refine ⟨p * m, ⟨⟨?_, ?_⟩, dvd_mul_right p m⟩, Nat.mul_div_cancel_left m hp⟩
    · have := (Nat.div_lt_iff_lt_mul hp).mp h1
      linarith [mul_comm m p]
    · have := (Nat.le_div_iff_mul_le hp).mp h2
      linarith [mul_comm m p]

noncomputable def a_m (Z : ℝ) (Y m : ℕ) : ℝ := max Z ((Y : ℝ) / (m : ℝ))
noncomputable def b_m (W : ℝ) (Y m : ℕ) : ℝ := min W ((2 * (Y : ℝ)) / (m : ℝ))

lemma a_m_ge_Z (Z : ℝ) (Y m : ℕ) : Z ≤ a_m Z Y m := le_max_left Z _

lemma b_m_le_two_a_m (Z W : ℝ) (Y m : ℕ) (hm : 0 < m) :
    b_m W Y m ≤ 2 * a_m Z Y m := by
  have _ := hm
  unfold b_m a_m
  have h1 : min W (2 * (Y : ℝ) / (m : ℝ)) ≤ 2 * (Y : ℝ) / (m : ℝ) := min_le_right _ _
  have h2 : 2 * (Y : ℝ) / (m : ℝ) = 2 * ((Y : ℝ) / (m : ℝ)) := mul_div_assoc 2 (Y : ℝ) (m : ℝ)
  have h3 : (Y : ℝ) / (m : ℝ) ≤ max Z ((Y : ℝ) / (m : ℝ)) := le_max_right _ _
  have h4 : 2 * (Y : ℝ) / (m : ℝ) ≤ 2 * max Z ((Y : ℝ) / (m : ℝ)) := by
    rw [h2]
    exact mul_le_mul_of_nonneg_left h3 (by positivity)
  exact h1.trans h4

lemma mem_prime_range_iff (Z W : ℝ) (hZ : 0 ≤ Z) (hZW : Z ≤ W) (Y m p : ℕ) (hm : 0 < m) :
    p ∈ (Finset.Ioc ⌊a_m Z Y m⌋₊ ⌊b_m W Y m⌋₊).filter Nat.Prime ↔
      p.Prime ∧ (⌊Z⌋₊ < p ∧ p ≤ 2 * Y) ∧ Y < p * m ∧ p * m ≤ 2 * Y ∧ (p : ℝ) ≤ W := by
  rw [Finset.mem_filter, Finset.mem_Ioc]
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ha_pos : 0 ≤ a_m Z Y m := by
    unfold a_m
    exact le_trans hZ (le_max_left _ _)
  constructor
  · rintro ⟨⟨hp1, hp2⟩, hp_prime⟩
    have ha_lt : a_m Z Y m < (p : ℝ) := (Nat.floor_lt ha_pos).mp hp1
    have hb_nonneg : 0 ≤ b_m W Y m := by
      unfold b_m
      refine le_min (hZ.trans hZW) ?_
      positivity
    have hp_le_b : (p : ℝ) ≤ b_m W Y m := (Nat.cast_le.mpr hp2).trans (Nat.floor_le hb_nonneg)
    unfold a_m at ha_lt
    unfold b_m at hp_le_b
    have hZ_lt : Z < (p : ℝ) := lt_of_le_of_lt (le_max_left _ _) ha_lt
    have hY_lt : (Y : ℝ) / (m : ℝ) < (p : ℝ) := lt_of_le_of_lt (le_max_right _ _) ha_lt
    have hp_le_W : (p : ℝ) ≤ W := le_trans hp_le_b (min_le_left _ _)
    have hp_le_2Y : (p : ℝ) ≤ 2 * (Y : ℝ) / (m : ℝ) := le_trans hp_le_b (min_le_right _ _)
    have h_pm1 : (Y : ℝ) < (p : ℝ) * (m : ℝ) := by
      rwa [div_lt_iff₀ hm_pos] at hY_lt
    have h_pm2 : (p : ℝ) * (m : ℝ) ≤ 2 * (Y : ℝ) := by
      rwa [le_div_iff₀ hm_pos] at hp_le_2Y
    have h_pm1_nat : Y < p * m := by exact_mod_cast h_pm1
    have h_pm2_nat : p * m ≤ 2 * Y := by exact_mod_cast h_pm2
    have hp_floor_Z : ⌊Z⌋₊ < p := (Nat.floor_lt hZ).mpr hZ_lt
    have hp_le_2Y_nat : p ≤ 2 * Y := by
      have h1 : p * 1 ≤ p * m := Nat.mul_le_mul_left p hm
      rw [mul_one] at h1
      exact h1.trans h_pm2_nat
    exact ⟨hp_prime, ⟨hp_floor_Z, hp_le_2Y_nat⟩, h_pm1_nat, h_pm2_nat, hp_le_W⟩
  · rintro ⟨hp_prime, ⟨hp_Z, _⟩, h_pm1, h_pm2, hp_W⟩
    have h_pm1_r : (Y : ℝ) < (p : ℝ) * (m : ℝ) := by exact_mod_cast h_pm1
    have h_pm2_r : (p : ℝ) * (m : ℝ) ≤ 2 * (Y : ℝ) := by exact_mod_cast h_pm2
    have hY_lt : (Y : ℝ) / (m : ℝ) < (p : ℝ) := (div_lt_iff₀ hm_pos).mpr (by linarith)
    have hp_le_2Y : (p : ℝ) ≤ 2 * (Y : ℝ) / (m : ℝ) := (le_div_iff₀ hm_pos).mpr (by linarith)
    have hZ_lt : Z < (p : ℝ) := (Nat.floor_lt hZ).mp hp_Z
    have ha_lt : a_m Z Y m < (p : ℝ) := by
      unfold a_m
      exact max_lt hZ_lt hY_lt
    have hp_le_b : (p : ℝ) ≤ b_m W Y m := by
      unfold b_m
      exact le_min hp_W hp_le_2Y
    have hp1 : ⌊a_m Z Y m⌋₊ < p := (Nat.floor_lt ha_pos).mpr ha_lt
    have hp2 : p ≤ ⌊b_m W Y m⌋₊ := Nat.le_floor hp_le_b
    exact ⟨⟨hp1, hp2⟩, hp_prime⟩

lemma prime_range_eq_filter_S (Z W : ℝ) (hZ : 0 ≤ Z) (hZW : Z ≤ W) (Y m : ℕ) (hm : 0 < m) :
    (Finset.Ioc ⌊a_m Z Y m⌋₊ ⌊b_m W Y m⌋₊).filter Nat.Prime =
      ((Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime).filter
        (fun p => Y < p * m ∧ p * m ≤ 2 * Y ∧ (p : ℝ) ≤ W) := by
  ext p
  rw [mem_prime_range_iff Z W hZ hZW Y m p hm]
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  tauto

lemma filter_M_eq_Ioc_div (Y p : ℕ) (hp : 3 ≤ p) :
    ((Finset.Ioc 0 (2 * Y)).filter (fun m => Y < p * m ∧ p * m ≤ 2 * Y)) =
      Finset.Ioc (Y / p) (2 * Y / p) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  have hp_pos : 0 < p := by omega
  constructor
  · rintro ⟨_, h1, h2⟩
    refine ⟨(Nat.div_lt_iff_lt_mul hp_pos).mpr (by linarith [mul_comm p m]),
            (Nat.le_div_iff_mul_le hp_pos).mpr (by linarith [mul_comm p m])⟩
  · rintro ⟨h1, h2⟩
    have h_pm1 : Y < p * m := by
      have := (Nat.div_lt_iff_lt_mul hp_pos).mp h1
      linarith [mul_comm m p]
    have h_pm2 : p * m ≤ 2 * Y := by
      have := (Nat.le_div_iff_mul_le hp_pos).mp h2
      linarith [mul_comm m p]
    have hm_pos : 0 < m := by
      by_contra hm0
      have : m = 0 := by omega
      subst this
      omega
    have hm_le : m ≤ 2 * Y := by
      have : 1 * m ≤ p * m := Nat.mul_le_mul_right m (by omega)
      linarith
    exact ⟨⟨hm_pos, hm_le⟩, h_pm1, h_pm2⟩

lemma sum_main_comm (Z W : ℝ) (hZ : 3 ≤ Z) (hZW : Z ≤ W) (Y : ℕ) (d : ℕ → ℂ) (s : ℂ) :
    let S := (Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime
    let M := Finset.Ioc 0 (2 * Y)
    let T := Finset.Ioc Y (2 * Y)
    (∑ m ∈ M, d m * (m : ℂ) ^ (-s) *
      ∑ p ∈ (Finset.Ioc ⌊a_m Z Y m⌋₊ ⌊b_m W Y m⌋₊).filter Nat.Prime, (p : ℂ) ^ (-s)) =
    ∑ p ∈ S, (p : ℂ) ^ (-s) *
      ∑ m ∈ cofactors T p, (if (p : ℝ) ≤ W then d m else 0) * (m : ℂ) ^ (-s) := by
  intro S M T
  have hZ0 : 0 ≤ Z := by linarith
  have h_p_ge : ∀ p ∈ S, 3 ≤ p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    have : 3 ≤ ⌊Z⌋₊ := Nat.le_floor hZ
    omega
  have h_cof : ∀ p ∈ S, cofactors T p = Finset.Ioc (Y / p) (2 * Y / p) := by
    intro p hp
    have hp3 := h_p_ge p hp
    exact cofactors_Ioc_eq Y p (by omega)
  have h1 : (∑ m ∈ M, d m * (m : ℂ) ^ (-s) *
      ∑ p ∈ (Finset.Ioc ⌊a_m Z Y m⌋₊ ⌊b_m W Y m⌋₊).filter Nat.Prime, (p : ℂ) ^ (-s)) =
    ∑ m ∈ M, ∑ p ∈ S,
      if Y < p * m ∧ p * m ≤ 2 * Y ∧ (p : ℝ) ≤ W then
        d m * (m : ℂ) ^ (-s) * (p : ℂ) ^ (-s)
      else 0 := by
    apply Finset.sum_congr rfl
    intro m hm
    have hm_pos : 0 < m := (Finset.mem_Ioc.mp hm).1
    rw [Finset.mul_sum]
    rw [prime_range_eq_filter_S Z W hZ0 hZW Y m hm_pos]
    rw [Finset.sum_filter]
  rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hp3 := h_p_ge p hp
  rw [h_cof p hp]
  rw [Finset.mul_sum]
  by_cases hpW : (p : ℝ) ≤ W
  · have h_split : (∑ m ∈ M, if Y < p * m ∧ p * m ≤ 2 * Y ∧ (p : ℝ) ≤ W then
        d m * (m : ℂ) ^ (-s) * (p : ℂ) ^ (-s) else 0) =
      ∑ m ∈ M, if Y < p * m ∧ p * m ≤ 2 * Y then
        (p : ℂ) ^ (-s) * ((if (p : ℝ) ≤ W then d m else 0) * (m : ℂ) ^ (-s)) else 0 := by
      apply Finset.sum_congr rfl
      intro m _
      have h_cond : (Y < p * m ∧ p * m ≤ 2 * Y ∧ (p : ℝ) ≤ W) ↔ (Y < p * m ∧ p * m ≤ 2 * Y) := by
        simp [hpW]
      rw [if_congr h_cond rfl rfl]
      by_cases h_if : Y < p * m ∧ p * m ≤ 2 * Y
      · simp [h_if, hpW]; ring
      · simp [h_if]
    rw [h_split, ← Finset.sum_filter]
    rw [filter_M_eq_Ioc_div Y p hp3]
  · have h_split : (∑ m ∈ M, if Y < p * m ∧ p * m ≤ 2 * Y ∧ (p : ℝ) ≤ W then
        d m * (m : ℂ) ^ (-s) * (p : ℂ) ^ (-s) else 0) =
      ∑ m ∈ Finset.Ioc (Y / p) (2 * Y / p),
        (p : ℂ) ^ (-s) * ((if (p : ℝ) ≤ W then d m else 0) * (m : ℂ) ^ (-s)) := by
      have h_lhs : (∑ m ∈ M, if Y < p * m ∧ p * m ≤ 2 * Y ∧ (p : ℝ) ≤ W then
          d m * (m : ℂ) ^ (-s) * (p : ℂ) ^ (-s) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro m _
        have hnot : ¬ (Y < p * m ∧ p * m ≤ 2 * Y ∧ (p : ℝ) ≤ W) := fun h => hpW h.2.2
        simp [hnot]
      have h_rhs : (∑ m ∈ Finset.Ioc (Y / p) (2 * Y / p),
          (p : ℂ) ^ (-s) * ((if (p : ℝ) ≤ W then d m else 0) * (m : ℂ) ^ (-s))) = 0 := by
        apply Finset.sum_eq_zero
        intro m _
        simp [hpW]
      rw [h_lhs, h_rhs]
    exact h_split

lemma prime_sum_bound (Z W : ℝ) (_hZ : 3 ≤ Z) (hZW : Z ≤ W) (Y m : ℕ) (hm : 0 < m) (t E : ℝ) (hE : 0 ≤ E)
    (hstar : ∀ (a b : ℝ), Z ≤ a → a < b → b ≤ 2 * a →
      ‖∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤ E) :
    ‖∑ p ∈ (Finset.Ioc ⌊a_m Z Y m⌋₊ ⌊b_m W Y m⌋₊).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤ E := by
  have _ := hZW
  let a := a_m Z Y m
  let b := b_m W Y m
  have haZ : Z ≤ a := a_m_ge_Z Z Y m
  have hba : b ≤ 2 * a := b_m_le_two_a_m Z W Y m hm
  by_cases hab : a < b
  · exact hstar a b haZ hab hba
  · have hba_le : b ≤ a := not_lt.mp hab
    have hfloor : ⌊b⌋₊ ≤ ⌊a⌋₊ := Nat.floor_le_floor hba_le
    have hempty : Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ = ∅ := Finset.Ioc_eq_empty_of_le hfloor
    have hempty_filter : (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime = ∅ := by
      rw [hempty, Finset.filter_empty]
    rw [hempty_filter, Finset.sum_empty, norm_zero]
    exact hE

lemma sum_Ioc_zero_inv_eq_harmonic (n : ℕ) :
    (∑ m ∈ Finset.Ioc 0 n, (1 : ℝ) / m) = (harmonic n : ℝ) := by
  have : Finset.Ioc 0 n = Finset.Icc 1 n := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [this]
  rw [harmonic_eq_sum_Icc]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  rw [one_div]

lemma sum_Ioc_zero_inv_le_log (n : ℕ) :
    (∑ m ∈ Finset.Ioc 0 n, (1 : ℝ) / m) ≤ Real.log n + 1 := by
  rw [sum_Ioc_zero_inv_eq_harmonic]
  have h := harmonic_le_one_add_log n
  linarith

lemma norm_main_le (Z W : ℝ) (hZ : 3 ≤ Z) (hZW : Z ≤ W) (Y : ℕ) (_hY : 2 ≤ Y) (t E : ℝ) (hE : 0 ≤ E)
    (d : ℕ → ℂ) (hd : ∀ m, ‖d m‖ ≤ 1)
    (hstar : ∀ (a b : ℝ), Z ≤ a → a < b → b ≤ 2 * a →
      ‖∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤ E) :
    ‖∑ m ∈ Finset.Ioc 0 (2 * Y), d m * (m : ℂ) ^ (-((1 : ℂ) + t * Complex.I)) *
      ∑ p ∈ (Finset.Ioc ⌊a_m Z Y m⌋₊ ⌊b_m W Y m⌋₊).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤
      (Real.log (2 * Y) + 1) * E := by
  let s := (1 : ℂ) + (t : ℝ) * Complex.I
  have h_tri := norm_sum_le (Finset.Ioc 0 (2 * Y))
    (fun m => d m * (m : ℂ) ^ (-s) *
      ∑ p ∈ (Finset.Ioc ⌊a_m Z Y m⌋₊ ⌊b_m W Y m⌋₊).filter Nat.Prime, (p : ℂ) ^ (-s))
  have h_term : ∀ m ∈ Finset.Ioc 0 (2 * Y),
      ‖d m * (m : ℂ) ^ (-s) * ∑ p ∈ (Finset.Ioc ⌊a_m Z Y m⌋₊ ⌊b_m W Y m⌋₊).filter Nat.Prime, (p : ℂ) ^ (-s)‖ ≤
      (1 / (m : ℝ)) * E := by
    intro m hm
    have hm_pos : 0 < m := (Finset.mem_Ioc.mp hm).1
    rw [norm_mul, norm_mul]
    have hd_m := hd m
    have h_cpow : ‖(m : ℂ) ^ (-s)‖ = 1 / (m : ℝ) :=
      norm_natCast_cpow_neg_one_add_mul_I m hm_pos t
    have h_prime := prime_sum_bound Z W hZ hZW Y m hm_pos t E hE hstar
    rw [h_cpow]
    have h_nonneg : 0 ≤ 1 / (m : ℝ) := by positivity
    have h1 : ‖d m‖ * (1 / (m : ℝ)) ≤ 1 * (1 / (m : ℝ)) :=
      mul_le_mul_of_nonneg_right hd_m h_nonneg
    rw [one_mul] at h1
    have h2 : ‖d m‖ * (1 / (m : ℝ)) * ‖∑ p ∈ (Finset.Ioc ⌊a_m Z Y m⌋₊ ⌊b_m W Y m⌋₊).filter Nat.Prime, (p : ℂ) ^ (-s)‖ ≤
        (1 / (m : ℝ)) * E :=
      mul_le_mul h1 h_prime (norm_nonneg _) h_nonneg
    exact h2
  have h_sum := Finset.sum_le_sum h_term
  have h_E_factor : (∑ m ∈ Finset.Ioc 0 (2 * Y), (1 / (m : ℝ)) * E) =
      (∑ m ∈ Finset.Ioc 0 (2 * Y), (1 : ℝ) / m) * E := by
    rw [← Finset.sum_mul]
  rw [h_E_factor] at h_sum
  have h_harm := sum_Ioc_zero_inv_le_log (2 * Y)
  push_cast at h_harm
  have h_final : (∑ m ∈ Finset.Ioc 0 (2 * Y), (1 : ℝ) / m) * E ≤ (Real.log (2 * Y) + 1) * E :=
    mul_le_mul_of_nonneg_right h_harm hE
  exact h_tri.trans (h_sum.trans h_final)

lemma sum_Ioc_inv_le_one (a b : ℕ) (hba : b ≤ 2 * a + 1) :
    (∑ k ∈ Finset.Ioc a b, (1 : ℝ) / k) ≤ 1 := by
  by_cases hab : a < b
  · have hcard : (Finset.Ioc a b).card ≤ a + 1 := by
      rw [Nat.card_Ioc]
      omega
    have hterm : ∀ k ∈ Finset.Ioc a b, (1 : ℝ) / k ≤ 1 / (a + 1 : ℝ) := by
      intro k hk
      rw [Finset.mem_Ioc] at hk
      have hk_ge : a + 1 ≤ k := hk.1
      have ha_pos : 0 < (a + 1 : ℝ) := by positivity
      exact one_div_le_one_div_of_le ha_pos (by exact_mod_cast hk_ge)
    have hsum := Finset.sum_le_sum hterm
    have hconst : (∑ _k ∈ Finset.Ioc a b, (1 : ℝ) / (a + 1 : ℝ)) = ((Finset.Ioc a b).card : ℝ) / (a + 1 : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
    rw [hconst] at hsum
    have hcard_cast : ((Finset.Ioc a b).card : ℝ) ≤ (a + 1 : ℝ) := by exact_mod_cast hcard
    have ha_pos : 0 < (a + 1 : ℝ) := by positivity
    have hdiv_le : ((Finset.Ioc a b).card : ℝ) / (a + 1 : ℝ) ≤ 1 := (div_le_one₀ ha_pos).mpr hcard_cast
    exact hsum.trans hdiv_le
  · have : Finset.Ioc a b = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    rw [this, Finset.sum_empty]
    linarith

lemma div_two_mul_le (Y d : ℕ) : (2 * Y) / d ≤ 2 * (Y / d) + 1 := by
  by_cases hd : d = 0
  · subst hd; simp
  · have hpos : 0 < d := Nat.pos_of_ne_zero hd
    have hmod : Y % d < d := Nat.mod_lt Y hpos
    have h1 : Y < d * (Y / d) + d := by
      calc Y = d * (Y / d) + Y % d := (Nat.div_add_mod Y d).symm
        _ < d * (Y / d) + d := by omega
    have h2 : 2 * Y < d * (2 * (Y / d) + 2) := by
      calc 2 * Y < 2 * (d * (Y / d) + d) := by omega
        _ = d * (2 * (Y / d) + 2) := by ring
    have h3 : (2 * Y) / d < 2 * (Y / d) + 2 := Nat.div_lt_of_lt_mul h2
    omega

lemma sum_dvd_inv_le (Y p : ℕ) (hp : 2 ≤ p) :
    (∑ m ∈ (Finset.Ioc (Y / p) (2 * Y / p)).filter (fun m => p ∣ m), (1 : ℝ) / (p * m : ℝ)) ≤
      1 / (p : ℝ) ^ 2 := by
  have hp_pos : 0 < p := by omega
  have hp2_pos : 0 < p ^ 2 := by positivity
  have h_image : ((Finset.Ioc (Y / p) (2 * Y / p)).filter (fun m => p ∣ m)) =
      (Finset.Ioc (Y / p ^ 2) (2 * Y / p ^ 2)).image (fun k => p * k) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdvd⟩
      refine ⟨m / p, ?_, Nat.mul_div_cancel' hdvd⟩
      have hpm : p * (m / p) = m := Nat.mul_div_cancel' hdvd
      refine ⟨?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hp2_pos]
        have : m / p * p ^ 2 = (p * (m / p)) * p := by ring
        rw [this, hpm]
        have := (Nat.div_lt_iff_lt_mul hp_pos).mp h1
        linarith [mul_comm p m]
      · rw [Nat.le_div_iff_mul_le hp2_pos]
        have : m / p * p ^ 2 = (p * (m / p)) * p := by ring
        rw [this, hpm]
        have := (Nat.le_div_iff_mul_le hp_pos).mp h2
        linarith [mul_comm p m]
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right p k⟩
      · rw [Nat.div_lt_iff_lt_mul hp_pos]
        have := (Nat.div_lt_iff_lt_mul hp2_pos).mp hk1
        have : k * p ^ 2 = (p * k) * p := by ring
        linarith
      · rw [Nat.le_div_iff_mul_le hp_pos]
        have := (Nat.le_div_iff_mul_le hp2_pos).mp hk2
        have : k * p ^ 2 = (p * k) * p := by ring
        linarith
  rw [h_image]
  have hinj : Set.InjOn (fun k => p * k) (Finset.Ioc (Y / p ^ 2) (2 * Y / p ^ 2)) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hp_pos hab
  rw [Finset.sum_image hinj]
  have h_term : (∑ x ∈ Finset.Ioc (Y / p ^ 2) (2 * Y / p ^ 2), (1 : ℝ) / ((p : ℝ) * ((p * x : ℕ) : ℝ))) =
      ∑ k ∈ Finset.Ioc (Y / p ^ 2) (2 * Y / p ^ 2), (1 / (p : ℝ) ^ 2) * (1 / (k : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k _
    have : ((p : ℝ) * ((p * k : ℕ) : ℝ)) = (p : ℝ) ^ 2 * (k : ℝ) := by
      push_cast; ring
    rw [this, one_div_mul_one_div]
  rw [h_term, ← Finset.mul_sum]
  have h_div_le := div_two_mul_le Y (p ^ 2)
  have h_sum_one := sum_Ioc_inv_le_one (Y / p ^ 2) (2 * Y / p ^ 2) h_div_le
  have hp_r_pos : 0 ≤ 1 / (p : ℝ) ^ 2 := by positivity
  have h_mul := mul_le_mul_of_nonneg_left h_sum_one hp_r_pos
  rw [mul_one] at h_mul
  exact h_mul

lemma inv_sq_le_inv_sub_inv {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : 0 < (n : ℝ) := by linarith
  have hn1_pos : 0 < (n : ℝ) - 1 := by linarith
  have h_eq : 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) = 1 / (((n : ℝ) - 1) * (n : ℝ)) := by
    have : (n : ℝ) - 1 ≠ 0 := by linarith
    have : (n : ℝ) ≠ 0 := by linarith
    field_simp
    ring
  rw [h_eq]
  have h_le : ((n : ℝ) - 1) * (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    calc ((n : ℝ) - 1) * (n : ℝ) = (n : ℝ) ^ 2 - (n : ℝ) := by ring
      _ ≤ (n : ℝ) ^ 2 := by linarith
  have h_prod_pos : 0 < ((n : ℝ) - 1) * (n : ℝ) := mul_pos hn1_pos hn_pos
  exact one_div_le_one_div_of_le h_prod_pos h_le

lemma sum_Ioc_telescope_eq (A B : ℕ) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ioc A B, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) =
      1 / (A : ℝ) - 1 / (B : ℝ) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hle ih =>
    rw [Finset.sum_Ioc_succ_top hle, ih]
    have : ((B + 1 : ℕ) : ℝ) - 1 = (B : ℝ) := by push_cast; ring
    rw [this]
    ring

lemma sum_Ioc_telescope_le (A B : ℕ) (hA : 1 ≤ A) :
    (∑ n ∈ Finset.Ioc A B, (1 / ((n : ℝ) - 1) - 1 / (n : ℝ))) ≤ 1 / (A : ℝ) := by
  rcases le_or_gt A B with hAB | hBA
  · rw [sum_Ioc_telescope_eq A B hAB]
    have : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast hAB
    have : 0 ≤ 1 / (B : ℝ) := by positivity
    linarith
  · have : Finset.Ioc A B = ∅ := Finset.Ioc_eq_empty_of_le (by omega)
    rw [this, Finset.sum_empty]
    have : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
    have : 0 < (A : ℝ) := by linarith
    positivity

lemma sum_inv_sq_le_four_div_Z (Z : ℝ) (hZ : 3 ≤ Z) (Y : ℕ) :
    (∑ p ∈ (Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime, 1 / (p : ℝ) ^ 2) ≤ 4 / Z := by
  have hS_sub : (Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime ⊆ Finset.Ioc ⌊Z⌋₊ (2 * Y) :=
    Finset.filter_subset _ _
  have h_sum_sub : (∑ p ∈ (Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime, 1 / (p : ℝ) ^ 2) ≤
      ∑ n ∈ Finset.Ioc ⌊Z⌋₊ (2 * Y), 1 / (n : ℝ) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hS_sub
    intro i _ _
    positivity
  have h_floor_ge3 : 3 ≤ ⌊Z⌋₊ := Nat.le_floor hZ
  have h_term_le : ∀ n ∈ Finset.Ioc ⌊Z⌋₊ (2 * Y),
      (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn_ge2 : 2 ≤ n := by omega
    exact inv_sq_le_inv_sub_inv hn_ge2
  have h_sum_le := Finset.sum_le_sum h_term_le
  have h_tel := sum_Ioc_telescope_le ⌊Z⌋₊ (2 * Y) (by omega)
  have h_step : (∑ p ∈ (Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime, 1 / (p : ℝ) ^ 2) ≤
      1 / (⌊Z⌋₊ : ℝ) :=
    h_sum_sub.trans (h_sum_le.trans h_tel)
  have hZ_pos : 0 < Z := by linarith
  have hfloor_pos : 0 < (⌊Z⌋₊ : ℝ) := by positivity
  have hZ_le_two_floor : Z ≤ 2 * (⌊Z⌋₊ : ℝ) := by
    have h1 : Z < (⌊Z⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Z
    have h2 : (⌊Z⌋₊ : ℝ) + 1 ≤ 2 * (⌊Z⌋₊ : ℝ) := by
      have : (3 : ℝ) ≤ (⌊Z⌋₊ : ℝ) := by exact_mod_cast h_floor_ge3
      linarith
    linarith
  have h_inv_le : 1 / (⌊Z⌋₊ : ℝ) ≤ 2 / Z := by
    rw [div_le_div_iff₀ hfloor_pos hZ_pos]
    linarith
  have h_two_le_four : (2 : ℝ) / Z ≤ 4 / Z := by
    exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hZ_pos)
  exact h_step.trans (h_inv_le.trans h_two_le_four)

noncomputable def diff_term (c c' : ℕ → ℂ) (S : Finset ℕ) (W : ℝ) (s : ℂ) (p m : ℕ) : ℂ :=
  (c (p * m) / (correctedCount S p m : ℂ) - (if (p : ℝ) ≤ W then c' m / ((omegaIn S m : ℂ) + 1) else 0)) *
    (p : ℂ) ^ (-s) * (m : ℂ) ^ (-s)

lemma norm_diff_term_le (c c' : ℕ → ℂ) (S : Finset ℕ) (Z W t : ℝ) (p m : ℕ)
    (hp_prime : p.Prime) (hpZ : Z < (p : ℝ)) (hm : 0 < m)
    (hc' : ∀ n, ‖c' n‖ ≤ 1) (hpS : p ∈ S)
    (hfac : ∀ p m : ℕ, p.Prime → Z < p → 0 < m → c (p * m) = if (p : ℝ) ≤ W then c' m else 0) :
    let s := (1 : ℂ) + (t : ℝ) * Complex.I
    ‖diff_term c c' S W s p m‖ ≤ if p ∣ m then 1 / (p * m : ℝ) else 0 := by
  intro s
  unfold diff_term
  have h_cpow_p : ‖(p : ℂ) ^ (-s)‖ = 1 / (p : ℝ) :=
    norm_natCast_cpow_neg_one_add_mul_I p hp_prime.pos t
  have h_cpow_m : ‖(m : ℂ) ^ (-s)‖ = 1 / (m : ℝ) :=
    norm_natCast_cpow_neg_one_add_mul_I m hm t
  have hc_pm := hfac p m hp_prime hpZ hm
  by_cases hpm : p ∣ m
  · simp only [hpm, ↓reduceIte]
    rw [norm_mul, norm_mul, h_cpow_p, h_cpow_m]
    unfold correctedCount
    simp only [hpm, ↓reduceIte, add_zero]
    by_cases hpW : (p : ℝ) ≤ W
    · simp only [hpW, ↓reduceIte]
      rw [hc_pm]
      simp only [hpW, ↓reduceIte]
      have h_factor : c' m / (omegaIn S m : ℂ) - c' m / ((omegaIn S m : ℂ) + 1) =
          c' m * (1 / (omegaIn S m : ℂ) - 1 / ((omegaIn S m : ℂ) + 1)) := by ring
      rw [h_factor, norm_mul]
      have h_omega_pos : 0 < omegaIn S m := omegaIn_pos_of_selected_dvd hpS hpm
      have h_diff_eq : (1 / (omegaIn S m : ℂ) - 1 / ((omegaIn S m : ℂ) + 1)) =
          1 / ((omegaIn S m : ℂ) * ((omegaIn S m : ℂ) + 1)) := by
        have h_omega_c : (omegaIn S m : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt h_omega_pos)
        have h_omega1_c : (omegaIn S m : ℂ) + 1 ≠ 0 := by
          have : 0 < (omegaIn S m : ℝ) + 1 := by positivity
          exact_mod_cast (ne_of_gt this)
        field_simp; ring
      rw [h_diff_eq, norm_div, norm_one]
      have h_norm_denom : ‖(omegaIn S m : ℂ) * ((omegaIn S m : ℂ) + 1)‖ =
          (omegaIn S m : ℝ) * ((omegaIn S m : ℝ) + 1) := by
        rw [norm_mul, Complex.norm_natCast]
        have : (omegaIn S m : ℂ) + 1 = ((omegaIn S m + 1 : ℕ) : ℂ) := by push_cast; rfl
        rw [this, Complex.norm_natCast]
        push_cast; rfl
      rw [h_norm_denom]
      have h_denom_ge1 : 1 ≤ (omegaIn S m : ℝ) * ((omegaIn S m : ℝ) + 1) := by
        have : (1 : ℝ) ≤ (omegaIn S m : ℝ) := by exact_mod_cast h_omega_pos
        nlinarith
      have h_frac_le1 : 1 / ((omegaIn S m : ℝ) * ((omegaIn S m : ℝ) + 1)) ≤ 1 := by
        have : 0 < (omegaIn S m : ℝ) * ((omegaIn S m : ℝ) + 1) := by linarith
        exact (div_le_one₀ this).mpr h_denom_ge1
      have hc'_m := hc' m
      have h1 : ‖c' m‖ * (1 / ((omegaIn S m : ℝ) * ((omegaIn S m : ℝ) + 1))) ≤ 1 * 1 :=
        mul_le_mul hc'_m h_frac_le1 (by positivity) (by norm_num)
      rw [one_mul] at h1
      have h_prod_le : ‖c' m‖ * (1 / ((omegaIn S m : ℝ) * ((omegaIn S m : ℝ) + 1))) * (1 / (p : ℝ)) * (1 / (m : ℝ)) ≤
          1 * (1 / (p : ℝ)) * (1 / (m : ℝ)) := by
        gcongr
      have h_alg : 1 * (1 / (p : ℝ)) * (1 / (m : ℝ)) = 1 / (p * m : ℝ) := by
        rw [one_mul, one_div_mul_one_div]
      exact h_prod_le.trans (by rw [h_alg])
    · simp only [hpW, ↓reduceIte, sub_zero]
      rw [hc_pm]
      simp only [hpW, ↓reduceIte, zero_div, norm_zero, zero_mul]
      positivity
  · simp only [hpm, ↓reduceIte]
    unfold correctedCount
    simp only [hpm, ↓reduceIte]
    rw [hc_pm]
    split_ifs <;> simp

theorem norm_dirichletPoly_le_of_prime_sums (c c' : ℕ → ℂ) (Y : ℕ) (Z W t E : ℝ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hc' : ∀ n, ‖c' n‖ ≤ 1) (hZ : 3 ≤ Z) (hZW : Z ≤ W) (hY : 2 ≤ Y) (ht : 1 ≤ |t|) (hE : 0 ≤ E)
    (hfac : ∀ p m : ℕ, p.Prime → Z < p → 0 < m → c (p * m) = if (p : ℝ) ≤ W then c' m else 0)
    (hstar : ∀ (a b : ℝ), Z ≤ a → a < b → b ≤ 2 * a →
      ‖∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (p : ℂ) ^ (-((1 : ℂ) + t * Complex.I))‖ ≤ E) :
    ‖dirichletPoly c (Finset.Ioc Y (2 * Y)) ((1 : ℂ) + t * Complex.I)‖ ≤
      (Real.log (2 * Y) + 1) * E + 4 / Z +
        ∑ n ∈ (Finset.Ioc Y (2 * Y)).filter (fun n => ∀ p : ℕ, p.Prime → p ∣ n → (p : ℝ) ≤ Z), (1 : ℝ) / n := by
  have _ := ht
  let s := (1 : ℂ) + (t : ℝ) * Complex.I
  let S := (Finset.Ioc ⌊Z⌋₊ (2 * Y)).filter Nat.Prime
  let T := Finset.Ioc Y (2 * Y)
  have hZ0 : 0 ≤ Z := by linarith
  have hS_prime : ∀ p ∈ S, Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2
  have h_ramare := ramare_cofactors T S (fun n => c n * (n : ℂ) ^ (-s)) hS_prime
  have h_poly : dirichletPoly c T s = (∑ n ∈ T, c n * (n : ℂ) ^ (-s)) := rfl
  rw [h_poly, h_ramare]
  have h_tri_ramare := norm_add_le
    (∑ p ∈ S, ∑ m ∈ cofactors T p, (c (p * m) * ((p * m : ℕ) : ℂ) ^ (-s)) / (correctedCount S p m : ℂ))
    (∑ n ∈ T.filter (fun n => omegaIn S n = 0), c n * (n : ℂ) ^ (-s))
  refine h_tri_ramare.trans ?_
  have h_u0 := norm_u0_le c hc Z hZ0 Y hY t
  let d : ℕ → ℂ := fun m => c' m / ((omegaIn S m : ℂ) + 1)
  have hd : ∀ m, ‖d m‖ ≤ 1 := by
    intro m
    dsimp [d]
    rw [norm_div]
    have h_denom : 1 ≤ ‖(omegaIn S m : ℂ) + 1‖ := by
      have : (omegaIn S m : ℂ) + 1 = ((omegaIn S m + 1 : ℕ) : ℂ) := by push_cast; rfl
      rw [this, Complex.norm_natCast]
      have : 1 ≤ omegaIn S m + 1 := by omega
      exact_mod_cast this
    have hc'_m := hc' m
    have : 0 < ‖(omegaIn S m : ℂ) + 1‖ := by positivity
    exact (div_le_one₀ this).mpr (hc'_m.trans h_denom)
  let term_Main : ℕ → ℕ → ℂ := fun p m =>
    (p : ℂ) ^ (-s) * ((if (p : ℝ) ≤ W then d m else 0) * (m : ℂ) ^ (-s))
  have h_cpow_mul (p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
      ((p * m : ℕ) : ℂ) ^ (-s) = (p : ℂ) ^ (-s) * (m : ℂ) ^ (-s) := by
    rw [natCast_cpow_neg_mul p m hp hm s]
  have h_term_split (p m : ℕ) (hp : p ∈ S) (hm : m ∈ cofactors T p) :
      (c (p * m) * ((p * m : ℕ) : ℂ) ^ (-s)) / (correctedCount S p m : ℂ) =
        term_Main p m + diff_term c c' S W s p m := by
    have hp_prime := hS_prime p hp
    have hp_pos := hp_prime.pos
    rw [cofactors_Ioc_eq Y p hp_pos] at hm
    have hm_pos : 0 < m := by
      have : Y / p < m := (Finset.mem_Ioc.mp hm).1
      have : 0 ≤ Y / p := Nat.zero_le _
      omega
    rw [h_cpow_mul p m hp_pos hm_pos]
    dsimp [term_Main, diff_term, d]
    ring
  have h_sum_split :
      (∑ p ∈ S, ∑ m ∈ cofactors T p, (c (p * m) * ((p * m : ℕ) : ℂ) ^ (-s)) / (correctedCount S p m : ℂ)) =
      (∑ p ∈ S, ∑ m ∈ cofactors T p, term_Main p m) +
        ∑ p ∈ S, ∑ m ∈ cofactors T p, diff_term c c' S W s p m := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    exact h_term_split p m hp hm
  rw [h_sum_split]
  have h_tri_split := norm_add_le
    (∑ p ∈ S, ∑ m ∈ cofactors T p, term_Main p m)
    (∑ p ∈ S, ∑ m ∈ cofactors T p, diff_term c c' S W s p m)
  have h_main_comm := sum_main_comm Z W hZ hZW Y d s
  have h_norm_main : ‖∑ p ∈ S, ∑ m ∈ cofactors T p, term_Main p m‖ ≤ (Real.log (2 * Y) + 1) * E := by
    have h_main_eq : (∑ p ∈ S, ∑ m ∈ cofactors T p, term_Main p m) =
        ∑ p ∈ S, (p : ℂ) ^ (-s) * ∑ m ∈ cofactors T p, (if (p : ℝ) ≤ W then d m else 0) * (m : ℂ) ^ (-s) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    rw [h_main_eq, ← h_main_comm]
    exact norm_main_le Z W hZ hZW Y hY t E hE d hd hstar
  have h_norm_diff : ‖∑ p ∈ S, ∑ m ∈ cofactors T p, diff_term c c' S W s p m‖ ≤ 4 / Z := by
    have h_tri1 := norm_sum_le S (fun p => ∑ m ∈ cofactors T p, diff_term c c' S W s p m)
    refine h_tri1.trans ?_
    have h_tri2 : ∀ p ∈ S, ‖∑ m ∈ cofactors T p, diff_term c c' S W s p m‖ ≤ 1 / (p : ℝ) ^ 2 := by
      intro p hp
      have hp_prime := hS_prime p hp
      have hp_pos := hp_prime.pos
      have hpZ : Z < (p : ℝ) := (mem_S_iff Z hZ0 Y p).mp hp |>.2.1
      have h_cof := cofactors_Ioc_eq Y p hp_pos
      rw [h_cof]
      have h_tri_inner := norm_sum_le (Finset.Ioc (Y / p) (2 * Y / p))
        (fun m => diff_term c c' S W s p m)
      refine h_tri_inner.trans ?_
      have h_term_diff : ∀ m ∈ Finset.Ioc (Y / p) (2 * Y / p),
          ‖diff_term c c' S W s p m‖ ≤ if p ∣ m then 1 / (p * m : ℝ) else 0 := by
        intro m hm
        have hm_pos : 0 < m := by
          have : Y / p < m := (Finset.mem_Ioc.mp hm).1
          have : 0 ≤ Y / p := Nat.zero_le _
          omega
        exact norm_diff_term_le c c' S Z W t p m hp_prime hpZ hm_pos hc' hp hfac
      have h_sum_le := Finset.sum_le_sum h_term_diff
      have h_filter : (∑ m ∈ Finset.Ioc (Y / p) (2 * Y / p), if p ∣ m then 1 / (p * m : ℝ) else 0) =
          ∑ m ∈ (Finset.Ioc (Y / p) (2 * Y / p)).filter (fun m => p ∣ m), 1 / (p * m : ℝ) := by
        rw [← Finset.sum_filter]
      rw [h_filter] at h_sum_le
      have hp2 : 2 ≤ p := hp_prime.two_le
      exact h_sum_le.trans (sum_dvd_inv_le Y p hp2)
    have h_sum_p := Finset.sum_le_sum h_tri2
    exact h_sum_p.trans (sum_inv_sq_le_four_div_Z Z hZ Y)
  linarith [h_tri_split, h_norm_main, h_norm_diff, h_u0]

end Erdos1201.MR
