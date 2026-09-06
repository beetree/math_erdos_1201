import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Van der Corput's Inequality (Weyl Differencing)

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes van der Corput's inequality (Weyl differencing; Tao 254A Notes 5,
Proposition 7; Graham–Kolesnik Lemma 2.5) for an arbitrary real phase on an interval of integers.
-/

open Real Complex Finset

namespace Erdos1201.MR

/-- Cauchy–Schwarz inequality for complex sums on a finite set. -/
lemma norm_sum_sq_le_card_mul_sum_norm_sq {α : Type*} (s : Finset α) (f : α → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := by
  have h1 : ‖∑ x ∈ s, f x‖ ≤ ∑ x ∈ s, ‖f x‖ := norm_sum_le _ _
  have h1_nonneg : 0 ≤ ∑ x ∈ s, ‖f x‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h2 : ‖∑ x ∈ s, f x‖ ^ 2 ≤ (∑ x ∈ s, ‖f x‖) ^ 2 :=
    sq_le_sq.mpr (by rw [abs_norm, abs_of_nonneg h1_nonneg]; exact h1)
  have hcs : (∑ x ∈ s, (1 : ℝ) * ‖f x‖) ^ 2 ≤
      (∑ x ∈ s, (1 : ℝ) ^ 2) * ∑ x ∈ s, ‖f x‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => 1) (fun x => ‖f x‖)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  exact h2.trans hcs

/-- Expansion of the squared norm `‖∑ i ∈ s, z i‖²` as `(∑ i, ∑ j, z i * star (z j)).re`. -/
lemma normSq_sum_eq {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    (‖∑ i ∈ s, z i‖ ^ 2 : ℝ) = (∑ i ∈ s, ∑ j ∈ s, z i * (starRingEnd ℂ) (z j)).re := by
  have h1 : ‖∑ i ∈ s, z i‖ ^ 2 = normSq (∑ i ∈ s, z i) := (normSq_eq_norm_sq _).symm
  have h2 : ((normSq (∑ i ∈ s, z i) : ℝ) : ℂ) = (∑ i ∈ s, z i) * (starRingEnd ℂ) (∑ i ∈ s, z i) :=
    (mul_conj (∑ i ∈ s, z i)).symm
  have h3 : (∑ i ∈ s, z i) * (starRingEnd ℂ) (∑ i ∈ s, z i) = ∑ i ∈ s, ∑ j ∈ s, z i * (starRingEnd ℂ) (z j) := by
    rw [map_sum, sum_mul_sum]
  rw [h1, ← ofReal_re (normSq (∑ i ∈ s, z i)), h2, h3]

/-- The standard phase exponential `e(x) = exp(2π i x)`. -/
noncomputable def weyl_e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))

/-- Complex conjugate of `weyl_e(x)`. -/
lemma star_weyl_e (x : ℝ) : (starRingEnd ℂ) (weyl_e x) = weyl_e (-x) := by
  simp only [weyl_e, ← exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, conj_ofReal, conj_I]
  push_cast
  ring

/-- Multiplicative property of `weyl_e`. -/
lemma weyl_e_add (x y : ℝ) : weyl_e (x + y) = weyl_e x * weyl_e y := by
  simp only [weyl_e]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Value of `weyl_e` at zero. -/
lemma weyl_e_zero : weyl_e 0 = 1 := by
  simp [weyl_e]

/-- Product of `weyl_e x` and the conjugate of `weyl_e y`. -/
lemma weyl_e_mul_star (x y : ℝ) : weyl_e x * (starRingEnd ℂ) (weyl_e y) = weyl_e (x - y) := by
  rw [star_weyl_e, ← weyl_e_add, sub_eq_add_neg]

/-- Shifted summand indicator for Weyl differencing. -/
noncomputable def weyl_term (g : ℕ → ℝ) (a b : ℕ) (m k : ℕ) : ℂ :=
  if a + k < m ∧ m ≤ b + k then weyl_e (g (m - k)) else 0

/-- Diagonal product of shifted indicators. -/
lemma weyl_term_mul_star_diag (g : ℕ → ℝ) (a b : ℕ) (k m : ℕ) :
    weyl_term g a b m k * (starRingEnd ℂ) (weyl_term g a b m k) =
      if a + k < m ∧ m ≤ b + k then 1 else 0 := by
  dsimp [weyl_term]
  split_ifs with h
  · rw [weyl_e_mul_star, sub_self, weyl_e_zero]
  · simp

/-- Off-diagonal product of shifted indicators. -/
lemma weyl_term_mul_star_offdiag (g : ℕ → ℝ) (a b : ℕ) (k1 h m : ℕ) (_hh : 0 < h) :
    weyl_term g a b m k1 * (starRingEnd ℂ) (weyl_term g a b m (k1 + h)) =
      if a + k1 + h < m ∧ m ≤ b + k1 then weyl_e (g (m - k1) - g (m - (k1 + h))) else 0 := by
  dsimp [weyl_term]
  by_cases h_in : a + k1 + h < m ∧ m ≤ b + k1
  · have h1 : a + k1 < m ∧ m ≤ b + k1 := by omega
    have h2 : a + (k1 + h) < m ∧ m ≤ b + (k1 + h) := by omega
    split_ifs
    exact weyl_e_mul_star (g (m - k1)) (g (m - (k1 + h)))
  · split_ifs with h_a h_b
    · exfalso; apply h_in; omega
    · simp
    · simp
    · simp

/-- Sum shift identity on integer intervals. -/
lemma sum_Ioc_add (f : ℕ → ℂ) (A B s : ℕ) :
    ∑ n ∈ Finset.Ioc A B, f (n + s) = ∑ m ∈ Finset.Ioc (A + s) (B + s), f m := by
  rw [← Finset.map_add_right_Ioc, Finset.sum_map]
  rfl

/-- Sum of the shifted indicator over `m` recovers the original exponential sum. -/
lemma sum_weyl_term_m (g : ℕ → ℝ) (a b H : ℕ) (k : ℕ) (hk : k < H) :
    ∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m k = ∑ n ∈ Finset.Ioc a b, weyl_e (g n) := by
  have h_sub : Finset.Ioc (a + k) (b + k) ⊆ Finset.Ioc a (b + H) := by
    intro x hx
    rw [mem_Ioc] at hx ⊢
    omega
  have h_filter : ∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m k =
      ∑ m ∈ Finset.Ioc (a + k) (b + k), weyl_e (g (m - k)) := by
    rw [← sum_subset h_sub]
    · apply sum_congr rfl
      intro x hx
      rw [mem_Ioc] at hx
      dsimp [weyl_term]
      have : a + k < x ∧ x ≤ b + k := hx
      simp [this]
    · intro x hx hnot
      rw [mem_Ioc] at hnot
      dsimp [weyl_term]
      have : ¬ (a + k < x ∧ x ≤ b + k) := hnot
      simp [this]
  rw [h_filter]
  have h_shift := (sum_Ioc_add (fun m => weyl_e (g (m - k))) a b k).symm
  rw [h_shift]
  apply sum_congr rfl
  intro n _
  simp only [Nat.add_sub_cancel]

/-- Diagonal sum over `m` equals the interval length `b - a`. -/
lemma sum_weyl_term_mul_star_diag (g : ℕ → ℝ) (a b H : ℕ) (k : ℕ) (hk : k < H) :
    ∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m k * (starRingEnd ℂ) (weyl_term g a b m k) = (b - a : ℕ) := by
  have h_sub : Finset.Ioc (a + k) (b + k) ⊆ Finset.Ioc a (b + H) := by
    intro x hx
    rw [mem_Ioc] at hx ⊢
    omega
  simp_rw [weyl_term_mul_star_diag]
  have h_filter : ∑ m ∈ Finset.Ioc a (b + H), (if a + k < m ∧ m ≤ b + k then (1 : ℂ) else 0) =
      ∑ m ∈ Finset.Ioc (a + k) (b + k), (1 : ℂ) := by
    rw [← sum_subset h_sub]
    · apply sum_congr rfl
      intro x hx
      rw [mem_Ioc] at hx
      simp [hx]
    · intro x _ hnot
      rw [mem_Ioc] at hnot
      simp [hnot]
  rw [h_filter, sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
  have : b + k - (a + k) = b - a := by omega
  rw [this]

/-- Off-diagonal sum over `m` equals the differenced sum over `Ioc a (b - h)`. -/
lemma sum_weyl_term_mul_star_offdiag (g : ℕ → ℝ) (a b H : ℕ) (k1 h : ℕ)
    (hk1 : k1 + h < H) (hh : 0 < h) :
    ∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m k1 * (starRingEnd ℂ) (weyl_term g a b m (k1 + h)) =
      ∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n) := by
  have h_prod : ∀ m, weyl_term g a b m k1 * (starRingEnd ℂ) (weyl_term g a b m (k1 + h)) =
      if a + k1 + h < m ∧ m ≤ b + k1 then weyl_e (g (m - k1) - g (m - (k1 + h))) else 0 :=
    fun m => weyl_term_mul_star_offdiag g a b k1 h m hh
  simp_rw [h_prod]
  by_cases hba : a + h ≤ b
  · have h_sub : Finset.Ioc (a + k1 + h) (b + k1) ⊆ Finset.Ioc a (b + H) := by
      intro x hx
      rw [mem_Ioc] at hx ⊢
      omega
    have h_filter : ∑ m ∈ Finset.Ioc a (b + H), (if a + k1 + h < m ∧ m ≤ b + k1 then weyl_e (g (m - k1) - g (m - (k1 + h))) else 0) =
        ∑ m ∈ Finset.Ioc (a + k1 + h) (b + k1), weyl_e (g (m - k1) - g (m - (k1 + h))) := by
      rw [← sum_subset h_sub]
      · apply sum_congr rfl
        intro x hx
        rw [mem_Ioc] at hx
        simp [hx]
      · intro x _ hnot
        rw [mem_Ioc] at hnot
        simp [hnot]
    rw [h_filter]
    have h_shift := (sum_Ioc_add (fun m => weyl_e (g (m - k1) - g (m - (k1 + h)))) a (b - h) (k1 + h)).symm
    have h_eq_interval : a + (k1 + h) = a + k1 + h ∧ b - h + (k1 + h) = b + k1 := by omega
    have h_shift' : ∑ m ∈ Finset.Ioc (a + k1 + h) (b + k1), weyl_e (g (m - k1) - g (m - (k1 + h))) =
        ∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + (k1 + h) - k1) - g (n + (k1 + h) - (k1 + h))) := by
      rw [← h_eq_interval.1, ← h_eq_interval.2]
      exact h_shift
    rw [h_shift']
    apply sum_congr rfl
    intro n _
    congr 2
    · congr 1; omega
    · congr 1; omega
  · have h_empty1 : Finset.Ioc a (b - h) = ∅ := by
      rw [Finset.Ioc_eq_empty_iff]
      omega
    rw [h_empty1, sum_empty]
    apply sum_eq_zero
    intro m _
    split_ifs with h1
    · exfalso; omega
    · rfl

/-- Symmetry of the inner product real parts under index swap. -/
lemma weyl_v_symm (g : ℕ → ℝ) (a b H : ℕ) (i j : ℕ) :
    (∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m i * (starRingEnd ℂ) (weyl_term g a b m j)).re =
    (∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m j * (starRingEnd ℂ) (weyl_term g a b m i)).re := by
  have h_conj : (starRingEnd ℂ) (∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m i * (starRingEnd ℂ) (weyl_term g a b m j)) =
      ∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m j * (starRingEnd ℂ) (weyl_term g a b m i) := by
    rw [map_sum]
    apply sum_congr rfl
    intro m _
    simp only [map_mul]
    have : (starRingEnd ℂ) ((starRingEnd ℂ) (weyl_term g a b m j)) = weyl_term g a b m j :=
      Complex.conj_conj (weyl_term g a b m j)
    rw [this, mul_comm]
  rw [← h_conj, conj_re]

/-- The open interval `Ioo 0 0` is empty. -/
lemma Ioo_zero_zero : Ioo 0 0 = (∅ : Finset ℕ) := by
  simp

/-- The open interval `Ioo 0 1` is empty. -/
lemma Ioo_zero_one : Ioo 0 1 = (∅ : Finset ℕ) := by
  ext x; simp; omega

/-- Successor decomposition of `Ioo 0 (H + 1)`. -/
lemma Ioo_zero_succ (H : ℕ) (hH : 1 ≤ H) :
    Ioo 0 (H + 1) = insert H (Ioo 0 H) := by
  ext x
  simp only [mem_Ioo, mem_insert]
  omega

/-- `H` is not in `Ioo 0 H`. -/
lemma not_mem_Ioo_self (H : ℕ) : H ∉ Ioo 0 H := by
  simp [mem_Ioo]

/-- Reindexing a sum over `range H` to `Ioo 0 (H + 1)`. -/
lemma sum_range_eq_sum_Ioo (w : ℕ → ℝ) (H : ℕ) :
    ∑ i ∈ range H, w i = ∑ h ∈ Ioo 0 (H + 1), w (H - h) := by
  refine sum_bij (fun i _ => H - i) ?_ ?_ ?_ ?_
  · intro i hi
    rw [mem_range] at hi
    rw [mem_Ioo]
    omega
  · intro i1 hi1 i2 hi2 heq
    rw [mem_range] at hi1 hi2
    omega
  · intro b hb
    rw [mem_Ioo] at hb
    refine ⟨H - b, ?_, ?_⟩
    · rw [mem_range]; omega
    · omega
  · intro i hi
    rw [mem_range] at hi
    congr 1
    omega

/-- Decomposition of a symmetric double sum over `range H` into diagonal and off-diagonal parts. -/
lemma double_sum_symmetric (v : ℕ → ℕ → ℝ) (h_symm : ∀ i j, v i j = v j i) (H : ℕ) :
    ∑ i ∈ range H, ∑ j ∈ range H, v i j =
      ∑ i ∈ range H, v i i + 2 * ∑ h ∈ Ioo 0 H, ∑ i ∈ range (H - h), v i (i + h) := by
  induction H with
  | zero => simp
  | succ H ih =>
    have h1 : ∑ i ∈ range (H + 1), ∑ j ∈ range (H + 1), v i j =
        (∑ i ∈ range H, ∑ j ∈ range H, v i j) + v H H + 2 * ∑ i ∈ range H, v i H := by
      rw [sum_range_succ]
      have hj : ∀ i, ∑ j ∈ range (H + 1), v i j = (∑ j ∈ range H, v i j) + v i H :=
        fun i => sum_range_succ (fun j => v i j) H
      simp_rw [hj]
      rw [sum_add_distrib]
      have h_symm_sum : ∑ j ∈ range H, v H j = ∑ i ∈ range H, v i H := by
        apply sum_congr rfl
        intro x _
        exact h_symm H x
      linarith [h_symm_sum]
    rw [h1, ih, sum_range_succ (fun i => v i i)]
    by_cases hH : H = 0
    · subst hH
      rw [Ioo_zero_zero, Ioo_zero_one, sum_empty, sum_empty]
      simp
    · have hH_ge : 1 ≤ H := by omega
      have h_rev : ∑ i ∈ range H, v i H = ∑ h ∈ Ioo 0 (H + 1), v (H - h) H :=
        sum_range_eq_sum_Ioo (fun i => v i H) H
      rw [h_rev]
      have h_split : Ioo 0 (H + 1) = insert H (Ioo 0 H) := Ioo_zero_succ H hH_ge
      have h_not_mem : H ∉ Ioo 0 H := not_mem_Ioo_self H
      have h_H_term : v (H - H) H = ∑ i ∈ range (H + 1 - H), v i (i + H) := by
        have : H + 1 - H = 1 := by omega
        rw [this, sum_range_one]
        have : H - H = 0 := by omega
        rw [this, zero_add]
      have h_comb : (∑ h ∈ Ioo 0 H, ∑ i ∈ range (H - h), v i (i + h)) +
          ∑ h ∈ Ioo 0 H, v (H - h) H =
          ∑ h ∈ Ioo 0 H, ∑ i ∈ range (H + 1 - h), v i (i + h) := by
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro h hh
        rw [mem_Ioo] at hh
        have h_step : H + 1 - h = (H - h) + 1 := by omega
        rw [h_step, sum_range_succ]
        have : H - h + h = H := by omega
        rw [this]
      rw [h_split, sum_insert h_not_mem, sum_insert h_not_mem]
      linarith [h_comb, h_H_term]

/-- Bound on the double sum of inner product real parts. -/
lemma sum_double_v_le (g : ℕ → ℝ) (a b H : ℕ) :
    ∑ i ∈ range H, ∑ j ∈ range H,
      (∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m i * (starRingEnd ℂ) (weyl_term g a b m j)).re ≤
    (H : ℝ) * (((b - a : ℕ) : ℝ) + 2 * ∑ h ∈ Ioo 0 H,
      ‖∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)‖) := by
  set v := fun i j => (∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m i * (starRingEnd ℂ) (weyl_term g a b m j)).re
  have h_symm : ∀ i j, v i j = v j i := fun i j => weyl_v_symm g a b H i j
  rw [double_sum_symmetric v h_symm H]
  have h_diag : ∑ i ∈ range H, v i i = (H : ℝ) * ((b - a : ℕ) : ℝ) := by
    have : ∀ i ∈ range H, v i i = ((b - a : ℕ) : ℝ) := by
      intro i hi
      dsimp [v]
      rw [sum_weyl_term_mul_star_diag g a b H i (mem_range.mp hi)]
      rfl
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]
  have h_offdiag : ∑ h ∈ Ioo 0 H, ∑ i ∈ range (H - h), v i (i + h) ≤
      (H : ℝ) * ∑ h ∈ Ioo 0 H, ‖∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)‖ := by
    have h_term_le : ∀ h ∈ Ioo 0 H,
        ∑ i ∈ range (H - h), v i (i + h) ≤ (H : ℝ) * ‖∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)‖ := by
      intro h hh
      rw [mem_Ioo] at hh
      have h_eq : ∀ i ∈ range (H - h), v i (i + h) =
          (∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)).re := by
        intro i hi
        dsimp [v]
        rw [mem_range] at hi
        have hk1 : i + h < H := by omega
        rw [sum_weyl_term_mul_star_offdiag g a b H i h hk1 hh.1]
      rw [sum_congr rfl h_eq, sum_const, card_range, nsmul_eq_mul]
      have h_re_le : (∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)).re ≤
          ‖∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)‖ :=
        Complex.re_le_norm _
      have h_card_le : ((H - h : ℕ) : ℝ) ≤ (H : ℝ) := by
        have : H - h ≤ H := by omega
        exact_mod_cast this
      have h_norm_nonneg : 0 ≤ ‖∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)‖ := norm_nonneg _
      have h_mult1 := mul_le_mul_of_nonneg_left h_re_le (Nat.cast_nonneg (H - h))
      have h_mult2 := mul_le_mul_of_nonneg_right h_card_le h_norm_nonneg
      linarith
    have h_sum_le := sum_le_sum h_term_le
    rw [mul_sum]
    exact h_sum_le
  linarith

/-- Van der Corput's inequality (Weyl differencing; Tao 254A Notes 5, Proposition 7;
Graham–Kolesnik Lemma 2.5) for an arbitrary real phase on an interval of integers. -/
theorem norm_sq_sum_exp_le_weyl (g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) (H : ℕ) (hH : 1 ≤ H) :
    ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * Complex.I * (g n : ℂ))‖ ^ 2 ≤
      (((b - a : ℕ) : ℝ) + H) / H * (((b - a : ℕ) : ℝ) + 2 * ∑ h ∈ Finset.Ioo 0 H,
        ‖∑ n ∈ Finset.Ioc a (b - h), Complex.exp (2 * Real.pi * Complex.I * ((g (n + h) - g n : ℝ) : ℂ))‖) := by
  have _ := hab
  have _ := hH
  set F : ℕ → ℂ := fun m => ∑ k ∈ range H, weyl_term g a b m k
  have h_sum_F : ∑ m ∈ Finset.Ioc a (b + H), F m = (H : ℂ) * ∑ n ∈ Finset.Ioc a b, weyl_e (g n) := by
    dsimp [F]
    rw [sum_comm]
    have h_k : ∀ k ∈ range H, ∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m k = ∑ n ∈ Finset.Ioc a b, weyl_e (g n) :=
      fun k hk => sum_weyl_term_m g a b H k (mem_range.mp hk)
    rw [sum_congr rfl h_k, sum_const, card_range, nsmul_eq_mul]
  have h_cs := norm_sum_sq_le_card_mul_sum_norm_sq (Finset.Ioc a (b + H)) F
  have h_card_Ioc : (Finset.Ioc a (b + H)).card = (b - a) + H := by
    rw [Nat.card_Ioc]
    omega
  have h_norm_sum_F : ‖∑ m ∈ Finset.Ioc a (b + H), F m‖ ^ 2 =
      (H : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ioc a b, weyl_e (g n)‖ ^ 2 := by
    rw [h_sum_F, norm_mul, Complex.norm_natCast, mul_pow]
  have h_sum_norm_sq : ∑ m ∈ Finset.Ioc a (b + H), ‖F m‖ ^ 2 =
      ∑ i ∈ range H, ∑ j ∈ range H,
        (∑ m ∈ Finset.Ioc a (b + H), weyl_term g a b m i * (starRingEnd ℂ) (weyl_term g a b m j)).re := by
    have h_ptwise : ∀ m ∈ Finset.Ioc a (b + H), ‖F m‖ ^ 2 =
        (∑ i ∈ range H, ∑ j ∈ range H, weyl_term g a b m i * (starRingEnd ℂ) (weyl_term g a b m j)).re :=
      fun m _ => normSq_sum_eq (range H) (weyl_term g a b m)
    rw [sum_congr rfl h_ptwise]
    simp_rw [re_sum]
    rw [sum_comm]
    have h_inner : ∀ i ∈ range H, ∑ m ∈ Finset.Ioc a (b + H), ∑ j ∈ range H,
        (weyl_term g a b m i * (starRingEnd ℂ) (weyl_term g a b m j)).re =
        ∑ j ∈ range H, ∑ m ∈ Finset.Ioc a (b + H),
        (weyl_term g a b m i * (starRingEnd ℂ) (weyl_term g a b m j)).re :=
      fun i _ => sum_comm
    rw [sum_congr rfl h_inner]
  have h_bound := sum_double_v_le g a b H
  rw [h_sum_norm_sq] at h_cs
  rw [h_norm_sum_F, h_card_Ioc] at h_cs
  push_cast at h_cs
  have hH_sq_pos : 0 < (H : ℝ) ^ 2 := by positivity
  have h_step : ‖∑ n ∈ Finset.Ioc a b, weyl_e (g n)‖ ^ 2 * (H : ℝ) ^ 2 ≤
      (((b - a : ℕ) : ℝ) + (H : ℝ)) * ((H : ℝ) * (((b - a : ℕ) : ℝ) + 2 * ∑ h ∈ Ioo 0 H,
        ‖∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)‖)) := by
    rw [mul_comm]
    exact h_cs.trans (mul_le_mul_of_nonneg_left h_bound (by positivity))
  have h_div : ‖∑ n ∈ Finset.Ioc a b, weyl_e (g n)‖ ^ 2 ≤
      ((((b - a : ℕ) : ℝ) + (H : ℝ)) * ((H : ℝ) * (((b - a : ℕ) : ℝ) + 2 * ∑ h ∈ Ioo 0 H,
        ‖∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)‖))) / (H : ℝ) ^ 2 :=
    (le_div_iff₀ hH_sq_pos).mpr h_step
  have h_alg : ((((b - a : ℕ) : ℝ) + (H : ℝ)) * ((H : ℝ) * (((b - a : ℕ) : ℝ) + 2 * ∑ h ∈ Ioo 0 H,
        ‖∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)‖))) / (H : ℝ) ^ 2 =
      (((b - a : ℕ) : ℝ) + (H : ℝ)) / (H : ℝ) * (((b - a : ℕ) : ℝ) + 2 * ∑ h ∈ Ioo 0 H,
        ‖∑ n ∈ Finset.Ioc a (b - h), weyl_e (g (n + h) - g n)‖) := by
    have : (H : ℝ) ^ 2 = (H : ℝ) * (H : ℝ) := by ring
    rw [this]
    field_simp
  rw [h_alg] at h_div
  exact h_div

end Erdos1201.MR
