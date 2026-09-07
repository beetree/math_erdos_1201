import Mathlib
import Erdos1201.Basic
import Erdos1201.MR.Setup
import Erdos1201.MR.Ramare
import Erdos1201.MR.Arithmetic
import Erdos1201.MR.Analysis.MeanValueTheorem
import Erdos1201.MR.Decomposition.Lemma12

/-!
# Lemma 12, boundary step: replacing `X < p m ≤ 2X` by short ranges

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

In Lemma 12 of the paper the main term `A₁(s) = ∑_{p ∈ [P,Q]} ∑_{X < pm ≤ 2X} b_m c_p (pm)^{-s}/(ω(m)+1)`
is replaced by `∑_v Q_{v,H}(s) R_{v,H}(s)`, where `Q_{v,H}` runs over the primes in the short
range `[e^{v/H}, e^{(v+1)/H})` and `R_{v,H}` over `m ∈ (X e^{-v/H}, 2X e^{-v/H}]`. The two
Dirichlet polynomials have the same coefficient at every `n` except on the boundary strips
`(X, X e^{1/H}] ∪ (2X, 2X e^{1/H}]`, where the difference has modulus at most `1` thanks to the
Ramaré weights `1/(ω(m)+1)`. The mean value theorem then bounds the mean square of the
difference by `C (T/X + 1) / H`.
-/

namespace Erdos1201.MR

open Finset

/-! ### Collapsing a sum over `p * m = n` -/

/-- A sum over `m` of a term supported on `p * m = n` is the single term at `m = n / p`. -/
lemma sum_ite_mul_eq_left (S : Finset ℕ) (p n : ℕ) (hp : 0 < p) (F : ℕ → ℂ) :
    (∑ m ∈ S, if p * m = n then F m else 0) = if p ∣ n ∧ n / p ∈ S then F (n / p) else 0 := by
  by_cases hdvd : p ∣ n
  · obtain ⟨k, hk⟩ := hdvd
    subst hk
    have hk : p * k / p = k := Nat.mul_div_cancel_left k hp
    rw [hk]
    have hiff : ∀ m, (p * m = p * k) ↔ (m = k) := fun m =>
      ⟨fun h => Nat.eq_of_mul_eq_mul_left hp h, fun h => by rw [h]⟩
    simp_rw [hiff]
    rw [Finset.sum_ite_eq' S k F]
    simp
  · have hz : ∀ m ∈ S, (if p * m = n then F m else 0) = 0 := by
      intro m _
      rw [ite_eq_right]
      intro h
      exact hdvd ⟨m, h.symm⟩
    rw [Finset.sum_eq_zero hz]
    simp [hdvd]

/-- Membership in `cofactors`. -/
lemma mem_cofactors_iff (T : Finset ℕ) (p m : ℕ) (hp : 0 < p) :
    m ∈ cofactors T p ↔ p * m ∈ T := by
  unfold cofactors
  rw [Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]
    exact hn.1
  · intro h
    refine ⟨p * m, ?_, Nat.mul_div_cancel_left m hp⟩
    rw [Finset.mem_filter]
    exact ⟨h, dvd_mul_right p m⟩

/-! ### The index of the short range containing a prime -/

/-- The index `v = ⌊H log p⌋` of the short range `[e^{v/H}, e^{(v+1)/H})` containing `p`. -/
noncomputable def rangeIndex (H : ℝ) (p : ℕ) : ℕ := ⌊H * Real.log p⌋₊

lemma rangeIndex_le (H : ℝ) (hH : 0 < H) (p : ℕ) (hp : 2 ≤ p) :
    Real.exp (rangeIndex H p / H) ≤ p := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  rw [← Real.le_log_iff_exp_le hp_pos, div_le_iff₀ hH, mul_comm]
  exact Nat.floor_le (by positivity)

lemma lt_rangeIndex_add_one (H : ℝ) (hH : 0 < H) (p : ℕ) (hp : 2 ≤ p) :
    (p : ℝ) < Real.exp ((rangeIndex H p + 1) / H) := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [← Real.log_lt_iff_lt_exp hp_pos, lt_div_iff₀ hH, mul_comm]
  exact Nat.lt_floor_add_one _

/-- A prime `p ≥ 2` lies in the short range `v` iff `v = rangeIndex H p`. -/
lemma range_cond_iff (H : ℝ) (hH : 0 < H) (v p : ℕ) (hp : 2 ≤ p) :
    (Real.exp (v / H) ≤ p ∧ (p : ℝ) < Real.exp ((v + 1) / H)) ↔ v = rangeIndex H p := by
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hlog : 0 ≤ H * Real.log p := by
    have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    positivity
  rw [← Real.le_log_iff_exp_le hp_pos, ← Real.log_lt_iff_lt_exp hp_pos, div_le_iff₀ hH,
    lt_div_iff₀ hH, eq_comm, rangeIndex, Nat.floor_eq_iff hlog, mul_comm (Real.log (p : ℝ)) H]

lemma rangeIndex_mem_Icc (P Q : ℕ) (H : ℝ) (hH : 0 < H) (hP : 1 ≤ P) (p : ℕ)
    (hp : p ∈ primeRange P Q) :
    rangeIndex H p ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊ := by
  unfold primeRange at hp
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨hPp, hpQ⟩, _⟩ := hp
  have hP_pos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hlogP : Real.log P ≤ Real.log p := Real.log_le_log hP_pos (by exact_mod_cast hPp)
  have hlogQ : Real.log p ≤ Real.log Q :=
    Real.log_le_log (by exact_mod_cast (show 0 < p by omega)) (by exact_mod_cast hpQ)
  rw [Finset.mem_Icc]
  constructor
  · exact Nat.floor_mono (mul_le_mul_of_nonneg_left hlogP hH.le)
  · have h1 : ((rangeIndex H p : ℕ) : ℝ) ≤ H * Real.log p := by
      have hlog : 0 ≤ H * Real.log p := by
        have : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
        positivity
      exact Nat.floor_le hlog
    have h2 : H * Real.log p ≤ H * Real.log Q := mul_le_mul_of_nonneg_left hlogQ hH.le
    have h3 : H * Real.log Q ≤ (⌈H * Real.log Q⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast h1.trans (h2.trans h3)

/-! ### Coefficients of the two Dirichlet polynomials -/

/-- Coefficient of `A₁`. -/
noncomputable def coeffA1 (P Q X : ℕ) (b c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
    if p * m = n then (b m * c p) / ((omegaIn (primeRange P Q) m : ℂ) + 1) else 0

/-- Coefficient of `∑_v Q_{v,H} R_{v,H}`. -/
noncomputable def coeffQR (P Q X : ℕ) (H : ℝ) (b c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
    ∑ p ∈ shortPrimeRange P Q H v, ∑ m ∈ cofactorRange X H v,
      if p * m = n then (b m * c p) / ((omegaIn (primeRange P Q) m : ℂ) + 1) else 0

lemma prime_of_mem_primeRange {P Q p : ℕ} (hp : p ∈ primeRange P Q) : p.Prime := by
  unfold primeRange at hp
  exact (Finset.mem_filter.mp hp).2

lemma two_le_of_mem_primeRange {P Q p : ℕ} (hp : p ∈ primeRange P Q) : 2 ≤ p :=
  (prime_of_mem_primeRange hp).two_le

lemma mul_le_of_mem_cofactorRange (X : ℕ) (H : ℝ) (v m : ℕ)
    (hm : m ∈ cofactorRange X H v) : (m : ℝ) ≤ 2 * X * Real.exp (-(v / H)) := by
  unfold cofactorRange at hm
  rw [Finset.mem_filter, Finset.mem_Ioc] at hm
  exact (Nat.le_floor_iff (by positivity)).mp hm.1.2

/-- `A₁(s)` as a Dirichlet polynomial over `(0, 6X]`. -/
theorem A1_eq_dirichletPoly (P Q X : ℕ) (b c : ℕ → ℂ) (s : ℂ) :
    (∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
      (b m * c p) * ((p * m : ℕ) : ℂ) ^ (-s) / ((omegaIn (primeRange P Q) m : ℂ) + 1)) =
    dirichletPoly (coeffA1 P Q X b c) (Finset.Ioc 0 (6 * X)) s := by
  unfold coeffA1 dirichletPoly
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hp0 : 0 < p := by have := two_le_of_mem_primeRange hp; omega
  have hpm : p * m ∈ Finset.Ioc 0 (6 * X) := by
    rw [mem_cofactors_iff _ _ _ hp0, Finset.mem_Ioc] at hm
    rw [Finset.mem_Ioc]
    omega
  rw [Finset.sum_eq_single (p * m)]
  · simp only [ite_true]
    ring
  · intro n _ hne
    rw [ite_eq_right (fun h => hne h.symm)]
  · intro h
    exact absurd hpm h

/-- `∑_v Q_{v,H}(s) R_{v,H}(s)` as a Dirichlet polynomial over `(0, 6X]`. -/
theorem QR_eq_dirichletPoly (P Q X : ℕ) (H : ℝ) (hH : 1 ≤ H) (b c : ℕ → ℂ) (s : ℂ) :
    (∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
      dirichletPoly c (shortPrimeRange P Q H v) s *
        dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1))
          (cofactorRange X H v) s) =
    dirichletPoly (coeffQR P Q X H b c) (Finset.Ioc 0 (6 * X)) s := by
  unfold coeffQR dirichletPoly
  simp_rw [Finset.sum_mul, Finset.mul_sum, ite_mul, zero_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v hv => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hp2 : 2 ≤ p := two_le_of_mem_primeRange (shortPrimeRange_subset P Q H v hp)
  have hp0 : 0 < p := by omega
  have hm_pos : 0 < m := by
    unfold cofactorRange at hm
    rw [Finset.mem_filter, Finset.mem_Ioc] at hm
    exact hm.1.1
  have hpm : p * m ∈ Finset.Ioc 0 (6 * X) := by
    rw [Finset.mem_Ioc]
    refine ⟨by positivity, ?_⟩
    have hmR := mul_le_of_mem_cofactorRange X H v m hm
    have hpR : (p : ℝ) < Real.exp ((v + 1) / H) := ((mem_shortPrimeRange P Q H v p).mp hp).2.2
    have hH0 : 0 < H := by linarith
    have hexp : Real.exp ((v + 1) / H) * Real.exp (-(v / H)) = Real.exp (1 / H) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have he : Real.exp (1 / H) ≤ 3 := by
      have h1 : (1 : ℝ) / H ≤ 1 := by rw [div_le_one hH0]; exact hH
      calc Real.exp (1 / H) ≤ Real.exp 1 := Real.exp_le_exp.mpr h1
        _ ≤ 3 := by
          have := Real.exp_one_lt_d9
          linarith
    have hprod : ((p * m : ℕ) : ℝ) ≤ 2 * X * Real.exp (1 / H) := by
      push_cast
      calc (p : ℝ) * m ≤ Real.exp ((v + 1) / H) * (2 * X * Real.exp (-(v / H))) := by
            apply mul_le_mul hpR.le hmR (by positivity) (by positivity)
        _ = 2 * X * (Real.exp ((v + 1) / H) * Real.exp (-(v / H))) := by ring
        _ = 2 * X * Real.exp (1 / H) := by rw [hexp]
    have : ((p * m : ℕ) : ℝ) ≤ 6 * X := by
      calc ((p * m : ℕ) : ℝ) ≤ 2 * X * Real.exp (1 / H) := hprod
        _ ≤ 2 * X * 3 := by gcongr
        _ = 6 * X := by ring
    exact_mod_cast this
  rw [Finset.sum_eq_single (p * m)]
  · simp only [ite_true]
    rw [natCast_cpow_neg_mul p m hp0 hm_pos s]
    ring
  · intro n _ hne
    rw [ite_eq_right (fun h => hne h.symm)]
  · intro h
    exact absurd hpm h

/-- Per-prime form of `coeffA1`. -/
lemma coeffA1_eq (P Q X : ℕ) (b c : ℕ → ℂ) (n : ℕ) :
    coeffA1 P Q X b c n = ∑ p ∈ primeRange P Q,
      if p ∣ n ∧ n ∈ Finset.Ioc X (2 * X) then
        (b (n / p) * c p) / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1) else 0 := by
  unfold coeffA1
  refine Finset.sum_congr rfl (fun p hp => ?_)
  have hp0 : 0 < p := by have := two_le_of_mem_primeRange hp; omega
  rw [sum_ite_mul_eq_left _ p n hp0]
  by_cases hdvd : p ∣ n
  · have : n / p ∈ cofactors (Finset.Ioc X (2 * X)) p ↔ n ∈ Finset.Ioc X (2 * X) := by
      rw [mem_cofactors_iff _ _ _ hp0, Nat.mul_div_cancel' hdvd]
    simp only [hdvd, true_and, this]
  · simp [hdvd]

/-- Per-prime form of `coeffQR`: every prime lies in exactly one short range. -/
lemma coeffQR_eq (P Q X : ℕ) (H : ℝ) (hH : 1 ≤ H) (hP : 1 ≤ P) (b c : ℕ → ℂ) (n : ℕ) :
    coeffQR P Q X H b c n = ∑ p ∈ primeRange P Q,
      if p ∣ n ∧ n / p ∈ cofactorRange X H (rangeIndex H p) then
        (b (n / p) * c p) / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1) else 0 := by
  have hH0 : 0 < H := by linarith
  unfold coeffQR
  -- collapse the inner sum over m
  have hinner : ∀ v p, p ∈ primeRange P Q →
      (∑ m ∈ cofactorRange X H v, if p * m = n then
        (b m * c p) / ((omegaIn (primeRange P Q) m : ℂ) + 1) else 0) =
      if p ∣ n ∧ n / p ∈ cofactorRange X H v then
        (b (n / p) * c p) / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1) else 0 := by
    intro v p hp
    have hp0 : 0 < p := by have := two_le_of_mem_primeRange hp; omega
    exact sum_ite_mul_eq_left _ p n hp0 _
  -- write the sum over the short range as a filtered sum over the prime range
  have hshort : ∀ v, (∑ p ∈ shortPrimeRange P Q H v, ∑ m ∈ cofactorRange X H v,
      if p * m = n then (b m * c p) / ((omegaIn (primeRange P Q) m : ℂ) + 1) else 0) =
      ∑ p ∈ primeRange P Q, if v = rangeIndex H p then
        (if p ∣ n ∧ n / p ∈ cofactorRange X H v then
          (b (n / p) * c p) / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1) else 0) else 0 := by
    intro v
    unfold shortPrimeRange
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    simp only [range_cond_iff H hH0 v p (two_le_of_mem_primeRange hp), hinner v p hp]
  simp_rw [hshort]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Finset.sum_ite_eq']
  rw [ite_eq_left (rangeIndex_mem_Icc P Q H hH0 hP p hp)]

/-! ### The boundary strips -/

/-- The boundary strips `(X, X e^{1/H}] ∪ (2X, 2X e^{1/H}]`, as a finset of integers. -/
noncomputable def boundaryStrip (X : ℕ) (H : ℝ) : Finset ℕ :=
  Finset.Ioc X ⌊(X : ℝ) * Real.exp (1 / H)⌋₊ ∪ Finset.Ioc (2 * X) ⌊2 * (X : ℝ) * Real.exp (1 / H)⌋₊

lemma exp_one_div_sub_one_le (H : ℝ) (hH : 1 ≤ H) : Real.exp (1 / H) - 1 ≤ 2 / H := by
  have hH0 : 0 < H := by linarith
  have hx0 : 0 ≤ 1 / H := by positivity
  have hx1 : 1 / H ≤ 1 := by rw [div_le_one hH0]; exact hH
  have h := Real.abs_exp_sub_one_sub_id_le (x := 1 / H) (by rw [abs_of_nonneg hx0]; exact hx1)
  have h1 := (abs_le.mp h).2
  have hsq : (1 / H) ^ 2 ≤ 1 / H := by
    rw [sq]
    exact mul_le_of_le_one_left hx0 hx1
  have h2 : 2 / H = 1 / H + 1 / H := by ring
  rw [h2]
  linarith

lemma card_boundaryStrip_le (X : ℕ) (H : ℝ) (hH : 1 ≤ H) :
    ((boundaryStrip X H).card : ℝ) ≤ 6 * X / H := by
  have hH0 : 0 < H := by linarith
  have hexp1 : 1 ≤ Real.exp (1 / H) := Real.one_le_exp (by positivity)
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hb1 : X ≤ ⌊(X : ℝ) * Real.exp (1 / H)⌋₊ := by
    rw [Nat.le_floor_iff (by positivity)]
    nlinarith
  have hb2 : 2 * X ≤ ⌊2 * (X : ℝ) * Real.exp (1 / H)⌋₊ := by
    rw [Nat.le_floor_iff (by positivity)]
    push_cast
    nlinarith
  have hf1 : (⌊(X : ℝ) * Real.exp (1 / H)⌋₊ : ℝ) ≤ X * Real.exp (1 / H) :=
    Nat.floor_le (by positivity)
  have hf2 : (⌊2 * (X : ℝ) * Real.exp (1 / H)⌋₊ : ℝ) ≤ 2 * X * Real.exp (1 / H) :=
    Nat.floor_le (by positivity)
  have hdiff := exp_one_div_sub_one_le H hH
  have hc1 : ((Finset.Ioc X ⌊(X : ℝ) * Real.exp (1 / H)⌋₊).card : ℝ) ≤ 2 * X / H := by
    rw [Nat.card_Ioc, Nat.cast_sub hb1]
    have : (X : ℝ) * Real.exp (1 / H) - X = X * (Real.exp (1 / H) - 1) := by ring
    calc (⌊(X : ℝ) * Real.exp (1 / H)⌋₊ : ℝ) - X ≤ X * Real.exp (1 / H) - X := by linarith
      _ = X * (Real.exp (1 / H) - 1) := this
      _ ≤ X * (2 / H) := by gcongr
      _ = 2 * X / H := by ring
  have hc2 : ((Finset.Ioc (2 * X) ⌊2 * (X : ℝ) * Real.exp (1 / H)⌋₊).card : ℝ) ≤ 4 * X / H := by
    rw [Nat.card_Ioc, Nat.cast_sub hb2]
    push_cast
    have : 2 * (X : ℝ) * Real.exp (1 / H) - 2 * X = 2 * X * (Real.exp (1 / H) - 1) := by ring
    calc (⌊2 * (X : ℝ) * Real.exp (1 / H)⌋₊ : ℝ) - 2 * X ≤ 2 * X * Real.exp (1 / H) - 2 * X := by
          linarith
      _ = 2 * X * (Real.exp (1 / H) - 1) := this
      _ ≤ 2 * X * (2 / H) := by gcongr
      _ = 4 * X / H := by ring
  have hcard : ((boundaryStrip X H).card : ℝ) ≤
      ((Finset.Ioc X ⌊(X : ℝ) * Real.exp (1 / H)⌋₊).card : ℝ) +
      ((Finset.Ioc (2 * X) ⌊2 * (X : ℝ) * Real.exp (1 / H)⌋₊).card : ℝ) := by
    unfold boundaryStrip
    exact_mod_cast Finset.card_union_le _ _
  calc ((boundaryStrip X H).card : ℝ) ≤ _ := hcard
    _ ≤ 2 * X / H + 4 * X / H := add_le_add hc1 hc2
    _ = 6 * X / H := by ring

lemma lt_of_mem_boundaryStrip {X : ℕ} {H : ℝ} {n : ℕ} (hn : n ∈ boundaryStrip X H) : X < n := by
  unfold boundaryStrip at hn
  rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc] at hn
  omega

/-- If the two indicator conditions differ, `n = p * (n/p)` lies on the boundary strips. -/
lemma mem_boundaryStrip_of_ne (X : ℕ) (H : ℝ) (hH : 1 ≤ H) (p n : ℕ) (hp : 2 ≤ p) (hpn : p ∣ n)
    (hne : ¬ (n ∈ Finset.Ioc X (2 * X) ↔ n / p ∈ cofactorRange X H (rangeIndex H p))) :
    n ∈ boundaryStrip X H := by
  have hH0 : 0 < H := by linarith
  set v := rangeIndex H p with hv
  set m := n / p with hm
  have hnm : n = p * m := (Nat.mul_div_cancel' hpn).symm
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  -- λ := p e^{-v/H} ∈ [1, e^{1/H})
  set lam : ℝ := p * Real.exp (-(v / H)) with hlam
  have hlam_pos : 0 < lam := by positivity
  have hlam1 : 1 ≤ lam := by
    have h := rangeIndex_le H hH0 p hp
    rw [hlam]
    have : Real.exp (-(v / H)) * Real.exp (v / H) = 1 := by
      rw [← Real.exp_add]; simp
    calc (1 : ℝ) = Real.exp (-(v / H)) * Real.exp (v / H) := this.symm
      _ ≤ Real.exp (-(v / H)) * p := by gcongr
      _ = p * Real.exp (-(v / H)) := by ring
  have hlam2 : lam < Real.exp (1 / H) := by
    have h := lt_rangeIndex_add_one H hH0 p hp
    rw [hlam]
    have : Real.exp ((v + 1) / H) * Real.exp (-(v / H)) = Real.exp (1 / H) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    calc (p : ℝ) * Real.exp (-(v / H)) < Real.exp ((v + 1) / H) * Real.exp (-(v / H)) := by
          gcongr
      _ = Real.exp (1 / H) := this
  -- the cofactor condition in terms of n
  have hcof : m ∈ cofactorRange X H v ↔ (X : ℝ) * lam < n ∧ (n : ℝ) ≤ 2 * X * lam := by
    unfold cofactorRange
    rw [Finset.mem_filter, Finset.mem_Ioc, Nat.le_floor_iff (by positivity)]
    have hnR : (n : ℝ) = p * m := by rw [hnm]; push_cast; ring
    have hm_pos_iff : 0 < m ↔ (0 : ℝ) < m := by exact_mod_cast Iff.rfl
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      rw [hnR, hlam]
      constructor
      · calc (X : ℝ) * (p * Real.exp (-(v / H))) = p * (X * Real.exp (-(v / H))) := by ring
          _ < p * m := by gcongr
      · calc (p : ℝ) * m ≤ p * (2 * X * Real.exp (-(v / H))) := by gcongr
          _ = 2 * X * (p * Real.exp (-(v / H))) := by ring
    · rintro ⟨h1, h2⟩
      rw [hnR, hlam] at h1 h2
      have hm1 : (X : ℝ) * Real.exp (-(v / H)) < m := by
        have := h1
        rw [show (X : ℝ) * (p * Real.exp (-(v / H))) = p * (X * Real.exp (-(v / H))) by ring] at this
        exact lt_of_mul_lt_mul_left this hp_pos.le
      have hm2 : (m : ℝ) ≤ 2 * X * Real.exp (-(v / H)) := by
        have := h2
        rw [show 2 * (X : ℝ) * (p * Real.exp (-(v / H))) = p * (2 * X * Real.exp (-(v / H))) by ring] at this
        exact le_of_mul_le_mul_left this hp_pos
      refine ⟨⟨?_, hm2⟩, hm1⟩
      have : (0 : ℝ) < m := lt_of_le_of_lt (by positivity) hm1
      exact_mod_cast this
  have hIoc : n ∈ Finset.Ioc X (2 * X) ↔ (X : ℝ) < n ∧ (n : ℝ) ≤ 2 * X := by
    rw [Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  rw [hIoc, hcof] at hne
  unfold boundaryStrip
  rw [Finset.mem_union, Finset.mem_Ioc, Finset.mem_Ioc, Nat.le_floor_iff (by positivity),
    Nat.le_floor_iff (by positivity)]
  have hX0 : (0 : ℝ) ≤ X := by positivity
  have hXlam : (X : ℝ) ≤ X * lam := le_mul_of_one_le_right hX0 hlam1
  have hXlam' : (X : ℝ) * lam ≤ X * Real.exp (1 / H) := by gcongr
  have h2Xlam : 2 * (X : ℝ) ≤ 2 * X * lam := le_mul_of_one_le_right (by positivity) hlam1
  have h2Xlam' : 2 * (X : ℝ) * lam ≤ 2 * X * Real.exp (1 / H) := by gcongr
  by_cases hA : (X : ℝ) < n ∧ (n : ℝ) ≤ 2 * X
  · have hB : ¬ ((X : ℝ) * lam < n ∧ (n : ℝ) ≤ 2 * X * lam) :=
      fun hB => hne ⟨fun _ => hB, fun _ => hA⟩
    left
    refine ⟨by exact_mod_cast hA.1, ?_⟩
    by_cases hc : (X : ℝ) * lam < n
    · have := not_le.mp (not_and.mp hB hc)
      exfalso
      linarith [hA.2]
    · have hc' := not_lt.mp hc
      linarith
  · have hB : (X : ℝ) * lam < n ∧ (n : ℝ) ≤ 2 * X * lam := by
      by_contra hB
      exact hne ⟨fun h => absurd h hA, fun h => absurd h hB⟩
    right
    have hXn : (X : ℝ) < n := lt_of_le_of_lt hXlam hB.1
    have hn2X : 2 * (X : ℝ) < n := by
      by_contra h
      exact hA ⟨hXn, not_lt.mp h⟩
    refine ⟨by exact_mod_cast hn2X, by linarith [hB.2]⟩

/-! ### Bounding the difference coefficient -/

lemma norm_weight_le (P Q : ℕ) (b c : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1)
    (p m : ℕ) :
    ‖(b m * c p) / ((omegaIn (primeRange P Q) m : ℂ) + 1)‖ ≤
      1 / ((omegaIn (primeRange P Q) m : ℝ) + 1) := by
  rw [norm_div, norm_mul]
  have hden : ‖((omegaIn (primeRange P Q) m : ℂ) + 1)‖ = (omegaIn (primeRange P Q) m : ℝ) + 1 := by
    have : ((omegaIn (primeRange P Q) m : ℂ) + 1) = ((omegaIn (primeRange P Q) m + 1 : ℕ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_natCast]
    push_cast; ring
  rw [hden]
  have hpos : (0 : ℝ) < (omegaIn (primeRange P Q) m : ℝ) + 1 := by positivity
  apply div_le_div_of_nonneg_right _ hpos.le
  calc ‖b m‖ * ‖c p‖ ≤ 1 * 1 := mul_le_mul (hb m) (hc p) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The Ramaré weights sum to at most one over the selected prime divisors. -/
lemma sum_inv_omega_div_le_one (P Q n : ℕ) :
    (∑ p ∈ (primeRange P Q).filter (fun p => p ∣ n),
      1 / ((omegaIn (primeRange P Q) (n / p) : ℝ) + 1)) ≤ 1 := by
  set S := primeRange P Q with hS
  have hSprime : ∀ q ∈ S, Nat.Prime q := fun q hq => prime_of_mem_primeRange hq
  have hfilter : S.filter (fun p => p ∣ n) = divisorsIn S n := by
    unfold divisorsIn; rfl
  rw [hfilter]
  have hω : ∀ p ∈ divisorsIn S n,
      1 / ((omegaIn S (n / p) : ℝ) + 1) ≤ 1 / (omegaIn S n : ℝ) := by
    intro p hp
    rw [mem_divisorsIn] at hp
    have hcc := correctedCount_div hSprime hp.1 hp.2
    have hle : omegaIn S n ≤ omegaIn S (n / p) + 1 := by
      rw [← hcc]
      unfold correctedCount
      split_ifs <;> omega
    have hpos : 0 < omegaIn S n := omegaIn_pos_of_selected_dvd hp.1 hp.2
    apply one_div_le_one_div_of_le (by exact_mod_cast hpos)
    exact_mod_cast hle
  calc (∑ p ∈ divisorsIn S n, 1 / ((omegaIn S (n / p) : ℝ) + 1))
      ≤ ∑ p ∈ divisorsIn S n, 1 / (omegaIn S n : ℝ) := Finset.sum_le_sum hω
    _ = (divisorsIn S n).card * (1 / (omegaIn S n : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 1 := by
        by_cases h0 : (divisorsIn S n).card = 0
        · rw [h0]; simp
        · have : (omegaIn S n : ℝ) = (divisorsIn S n).card := rfl
          rw [this, mul_one_div, div_self]
          exact_mod_cast h0

/-- The difference coefficient. -/
noncomputable def coeffDiff (P Q X : ℕ) (H : ℝ) (b c : ℕ → ℂ) (n : ℕ) : ℂ :=
  coeffA1 P Q X b c n - coeffQR P Q X H b c n

lemma coeffDiff_eq (P Q X : ℕ) (H : ℝ) (hH : 1 ≤ H) (hP : 1 ≤ P) (b c : ℕ → ℂ) (n : ℕ) :
    coeffDiff P Q X H b c n = ∑ p ∈ primeRange P Q,
      if p ∣ n then (b (n / p) * c p) / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1) *
        ((if n ∈ Finset.Ioc X (2 * X) then (1 : ℂ) else 0) -
          (if n / p ∈ cofactorRange X H (rangeIndex H p) then (1 : ℂ) else 0)) else 0 := by
  unfold coeffDiff
  rw [coeffA1_eq, coeffQR_eq P Q X H hH hP, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hd : p ∣ n
  · simp only [hd, true_and, ite_true]
    split_ifs <;> ring
  · simp [hd]

lemma norm_coeffDiff_le_one (P Q X : ℕ) (H : ℝ) (hH : 1 ≤ H) (hP : 1 ≤ P) (b c : ℕ → ℂ)
    (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) (n : ℕ) :
    ‖coeffDiff P Q X H b c n‖ ≤ 1 := by
  rw [coeffDiff_eq P Q X H hH hP]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ p ∈ primeRange P Q,
      ‖(if p ∣ n then (b (n / p) * c p) / ((omegaIn (primeRange P Q) (n / p) : ℂ) + 1) *
        ((if n ∈ Finset.Ioc X (2 * X) then (1 : ℂ) else 0) -
          (if n / p ∈ cofactorRange X H (rangeIndex H p) then (1 : ℂ) else 0)) else 0)‖ ≤
      if p ∣ n then 1 / ((omegaIn (primeRange P Q) (n / p) : ℝ) + 1) else 0 := by
    intro p _
    by_cases hd : p ∣ n
    · rw [ite_eq_left hd, ite_eq_left hd, norm_mul]
      have h1 := norm_weight_le P Q b c hb hc p (n / p)
      have h2 : ‖((if n ∈ Finset.Ioc X (2 * X) then (1 : ℂ) else 0) -
          (if n / p ∈ cofactorRange X H (rangeIndex H p) then (1 : ℂ) else 0))‖ ≤ 1 := by
        split_ifs <;> simp
      calc _ ≤ (1 / ((omegaIn (primeRange P Q) (n / p) : ℝ) + 1)) * 1 :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = _ := mul_one _
    · simp [hd]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter]
  exact sum_inv_omega_div_le_one P Q n

lemma coeffDiff_eq_zero_of_not_mem (P Q X : ℕ) (H : ℝ) (hH : 1 ≤ H) (hP : 1 ≤ P)
    (b c : ℕ → ℂ) (n : ℕ) (hn : n ∉ boundaryStrip X H) :
    coeffDiff P Q X H b c n = 0 := by
  rw [coeffDiff_eq P Q X H hH hP]
  apply Finset.sum_eq_zero
  intro p hp
  by_cases hd : p ∣ n
  · rw [ite_eq_left hd]
    have hiff : n ∈ Finset.Ioc X (2 * X) ↔ n / p ∈ cofactorRange X H (rangeIndex H p) := by
      by_contra hne
      exact hn (mem_boundaryStrip_of_ne X H hH p n (two_le_of_mem_primeRange hp) hd hne)
    have : ((if n ∈ Finset.Ioc X (2 * X) then (1 : ℂ) else 0) -
        (if n / p ∈ cofactorRange X H (rangeIndex H p) then (1 : ℂ) else 0)) = 0 := by
      by_cases h1 : n ∈ Finset.Ioc X (2 * X)
      · rw [ite_eq_left h1, ite_eq_left (hiff.mp h1)]; ring
      · rw [ite_eq_right h1, ite_eq_right (fun h2 => h1 (hiff.mpr h2))]; ring
    rw [this, mul_zero]
  · rw [ite_eq_right hd]

/-- The `ℓ²` mass of the difference coefficient is at most `6/(HX)`. -/
lemma sum_norm_sq_coeffDiff_le (P Q X : ℕ) (H : ℝ) (hH : 1 ≤ H) (hP : 1 ≤ P) (hX : 1 ≤ X)
    (b c : ℕ → ℂ) (hb : ∀ m, ‖b m‖ ≤ 1) (hc : ∀ p, ‖c p‖ ≤ 1) :
    (∑ n ∈ Finset.Ioc 0 (6 * X), ‖coeffDiff P Q X H b c n‖ ^ 2 / (n : ℝ) ^ 2) ≤
      6 / (H * X) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hH0 : 0 < H := by linarith
  set M := Finset.Ioc 0 (6 * X) with hM
  have hsupp : ∀ n ∈ M, ‖coeffDiff P Q X H b c n‖ ^ 2 / (n : ℝ) ^ 2 ≠ 0 →
      n ∈ boundaryStrip X H := by
    intro n _ hne
    by_contra hn
    apply hne
    rw [coeffDiff_eq_zero_of_not_mem P Q X H hH hP b c n hn]
    simp
  rw [← Finset.sum_filter_of_ne hsupp]
  have hterm : ∀ n ∈ M.filter (fun n => n ∈ boundaryStrip X H),
      ‖coeffDiff P Q X H b c n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / (X : ℝ) ^ 2 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    have hXn : X < n := lt_of_mem_boundaryStrip hn.2
    have hXnR : (X : ℝ) < n := by exact_mod_cast hXn
    have hnorm := norm_coeffDiff_le_one P Q X H hH hP b c hb hc n
    have hnum : ‖coeffDiff P Q X H b c n‖ ^ 2 ≤ 1 := by
      calc ‖coeffDiff P Q X H b c n‖ ^ 2 ≤ 1 ^ 2 := by gcongr
        _ = 1 := one_pow 2
    calc ‖coeffDiff P Q X H b c n‖ ^ 2 / (n : ℝ) ^ 2 ≤ 1 / (n : ℝ) ^ 2 := by
          gcongr
      _ ≤ 1 / (X : ℝ) ^ 2 := by gcongr
  calc (∑ n ∈ M.filter (fun n => n ∈ boundaryStrip X H),
        ‖coeffDiff P Q X H b c n‖ ^ 2 / (n : ℝ) ^ 2)
      ≤ ∑ _n ∈ M.filter (fun n => n ∈ boundaryStrip X H), 1 / (X : ℝ) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = ((M.filter (fun n => n ∈ boundaryStrip X H)).card : ℝ) * (1 / (X : ℝ) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((boundaryStrip X H).card : ℝ) * (1 / (X : ℝ) ^ 2) := by
        gcongr
        intro n hn
        exact (Finset.mem_filter.mp hn).2
    _ ≤ (6 * X / H) * (1 / (X : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (card_boundaryStrip_le X H hH) (by positivity)
    _ = 6 / (H * X) := by
        field_simp

/-! ### The boundary step of Lemma 12 -/

/-- Lemma 12, boundary step: replacing `X < pm ≤ 2X` by `m ∈ cofactorRange X H v` for
`p` in the short range `v` costs only `O((T/X + 1)/H)` in mean square. -/
theorem integral_norm_sq_A₁_sub_sum_QR_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (X P Q : ℕ) (H : ℝ) (b c : ℕ → ℂ) (T : ℝ) (U : Set ℝ),
      1 ≤ X → 2 ≤ P → P ≤ Q → (Q : ℝ) ≤ X → 1 ≤ H → 0 ≤ T → MeasurableSet U → U ⊆ Set.Icc (-T) T →
      (∀ m, ‖b m‖ ≤ 1) → (∀ p, ‖c p‖ ≤ 1) →
      ∫ t in U, ‖(∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
            (b m * c p) * ((p * m : ℕ) : ℂ) ^ (-((1 : ℂ) + t * Complex.I)) / ((omegaIn (primeRange P Q) m : ℂ) + 1)) -
          ∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
            dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
              dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
        C * (T / X + 1) * (1 / H + 1 / X) := by
  refine ⟨216 * Real.pi, by positivity, ?_⟩
  intro X P Q H b c T U hX hP hPQ hQX hH hT hU hUsub hb hc
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hH0 : 0 < H := by linarith
  have hP1 : 1 ≤ P := by omega
  set M := Finset.Ioc 0 (6 * X) with hM
  have hMpos : ∀ n ∈ M, 0 < n := fun n hn => (Finset.mem_Ioc.mp hn).1
  -- rewrite the integrand as a single Dirichlet polynomial
  have hpt : ∀ t : ℝ,
      ‖(∑ p ∈ primeRange P Q, ∑ m ∈ cofactors (Finset.Ioc X (2 * X)) p,
            (b m * c p) * ((p * m : ℕ) : ℂ) ^ (-((1 : ℂ) + t * Complex.I)) / ((omegaIn (primeRange P Q) m : ℂ) + 1)) -
          ∑ v ∈ Finset.Icc ⌊H * Real.log P⌋₊ ⌈H * Real.log Q⌉₊,
            dirichletPoly c (shortPrimeRange P Q H v) ((1 : ℂ) + t * Complex.I) *
              dirichletPoly (fun m => b m / ((omegaIn (primeRange P Q) m : ℂ) + 1)) (cofactorRange X H v) ((1 : ℂ) + t * Complex.I)‖ ^ 2 =
      ‖dirichletPoly (coeffDiff P Q X H b c) M ((1 : ℂ) + t * Complex.I)‖ ^ 2 := by
    intro t
    rw [A1_eq_dirichletPoly, QR_eq_dirichletPoly P Q X H hH]
    congr 2
    unfold coeffDiff dirichletPoly
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    ring
  simp_rw [hpt]
  have h1 := setIntegral_norm_sq_dirichletPoly_le (coeffDiff P Q X H b c) M hMpos T hT U hU hUsub
  have h2 := integral_norm_sq_dirichletPoly_subset_le (coeffDiff P Q X H b c) M (6 * X)
    (Finset.Subset.refl _) T hT
  have h3 := sum_norm_sq_coeffDiff_le P Q X H hH hP1 hX b c hb hc
  have hpi : 0 < Real.pi := Real.pi_pos
  calc _ ≤ _ := h1
    _ ≤ (2 * T + 6 * Real.pi * ((6 * X : ℕ) : ℝ)) *
        ∑ n ∈ M, ‖coeffDiff P Q X H b c n‖ ^ 2 / (n : ℝ) ^ 2 := h2
    _ ≤ (2 * T + 6 * Real.pi * ((6 * X : ℕ) : ℝ)) * (6 / (H * X)) := by
        gcongr
    _ = (12 * T / X + 216 * Real.pi) / H := by
        push_cast
        field_simp
        ring
    _ ≤ 216 * Real.pi * (T / X + 1) * (1 / H + 1 / X) := by
        have hTX : 0 ≤ T / X := by positivity
        have hinvX : 0 ≤ 1 / (X : ℝ) := by positivity
        have hinvH : 0 < 1 / H := by positivity
        have hpi3 : 12 ≤ 216 * Real.pi := by nlinarith [Real.pi_gt_three]
        have e : (12 * T / X + 216 * Real.pi) / H = (12 * (T / X) + 216 * Real.pi) * (1 / H) := by
          field_simp
        rw [e]
        have : 12 * (T / X) + 216 * Real.pi ≤ 216 * Real.pi * (T / X + 1) := by nlinarith
        calc (12 * (T / X) + 216 * Real.pi) * (1 / H)
            ≤ 216 * Real.pi * (T / X + 1) * (1 / H) := by gcongr
          _ ≤ 216 * Real.pi * (T / X + 1) * (1 / H + 1 / X) := by gcongr; linarith

end Erdos1201.MR
