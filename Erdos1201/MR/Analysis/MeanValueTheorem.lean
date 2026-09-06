import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.MR.Analysis.HilbertInequality

open scoped BigOperators
open intervalIntegral

/-!
# Montgomery's Mean Value Theorem for Dirichlet Polynomials

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This file formalizes Montgomery's mean value theorem for finite Dirichlet polynomials
on the line $\text{Re}(s) = 1$ over the interval $[-T, T]$ with the sharp $(2T + O(N))$ shape:
$$ \int_{-T}^T |P(1 + it)|^2 dt \le (2T + 6\pi N) \sum_{n \le N} \frac{|a_n|^2}{n^2} $$
as in Matomäki–Radziwiłł (arXiv:1501.04585v4), Lemma 6.

The proof uses the exact $L^2$ expansion from `Erdos1201.MR.Analysis.DirichletPolyBasics`
and decomposes the off-diagonal kernel into two Montgomery–Vaughan generalized Hilbert
bilinear forms from `Erdos1201.MR.Analysis.HilbertInequality`.
-/

namespace Erdos1201.MR

/-- Lower bound on $\log(1 + 1/N)$ by $(2N)^{-1}$ for $N \ge 1$. -/
lemma inv_le_log_one_add_inv (N : ℕ) (hN : 1 ≤ N) :
    (2 * (N : ℝ))⁻¹ ≤ Real.log (1 + (N : ℝ)⁻¹) := by
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hN_pos : 0 < (N : ℝ) := by linarith
  have hN1_pos : 0 < (N : ℝ) + 1 := by linarith
  have h_pos : 0 < (N : ℝ) / (N + 1) := div_pos hN_pos hN1_pos
  have h_le := Real.log_le_sub_one_of_pos h_pos
  have h_inv_eq : (1 + (N : ℝ)⁻¹)⁻¹ = (N : ℝ) / (N + 1) := by
    rw [inv_eq_one_div]
    have : 1 + (N : ℝ)⁻¹ = ((N : ℝ) + 1) / (N : ℝ) := by
      rw [inv_eq_one_div]
      field_simp
    rw [this, one_div_div]
  have h_log_eq : Real.log ((N : ℝ) / (N + 1)) = -Real.log (1 + (N : ℝ)⁻¹) := by
    rw [← h_inv_eq, Real.log_inv]
  have h_sub : (N : ℝ) / (N + 1) - 1 = - ((N : ℝ) + 1)⁻¹ := by
    rw [inv_eq_one_div]
    field_simp
    ring
  rw [h_log_eq, h_sub] at h_le
  have h1 : ((N : ℝ) + 1)⁻¹ ≤ Real.log (1 + (N : ℝ)⁻¹) := by
    linarith
  have h2 : (2 * (N : ℝ))⁻¹ ≤ ((N : ℝ) + 1)⁻¹ := by
    rw [inv_le_inv₀ (by linarith) (by linarith)]
    linarith
  exact h2.trans h1

/-- Lower bound on $\log(r/s)$ by $(2N)^{-1}$ when $0 < s < r \le N$. -/
lemma inv_le_log_div_of_lt {s r N : ℕ} (hs_pos : 0 < s) (hsr : s < r) (hrN : r ≤ N) :
    (2 * (N : ℝ))⁻¹ ≤ Real.log ((r : ℝ) / s) := by
  have hN : 1 ≤ N := by omega
  have hs_le : (s : ℝ) ≤ N := by
    have : s ≤ N := by omega
    exact_mod_cast this
  have hs_real_pos : 0 < (s : ℝ) := by
    exact_mod_cast hs_pos
  have hr_real_pos : 0 < (r : ℝ) := by
    have : 0 < r := by omega
    exact_mod_cast this
  have h_sr_le : (s : ℝ) + 1 ≤ r := by
    have : s + 1 ≤ r := by omega
    exact_mod_cast this
  have h_div_le : 1 + (N : ℝ)⁻¹ ≤ (r : ℝ) / s := by
    have h1 : 1 + ((s : ℝ))⁻¹ ≤ (r : ℝ) / s := by
      rw [inv_eq_one_div]
      have : 1 + 1 / (s : ℝ) = ((s : ℝ) + 1) / (s : ℝ) := by
        field_simp [ne_of_gt hs_real_pos]
      rw [this]
      exact div_le_div_of_nonneg_right h_sr_le (by linarith)
    have h2 : 1 + (N : ℝ)⁻¹ ≤ 1 + (s : ℝ)⁻¹ := by
      have hN_pos : 0 < (N : ℝ) := by
        have : 0 < N := by omega
        exact_mod_cast this
      have : (N : ℝ)⁻¹ ≤ (s : ℝ)⁻¹ := by
        rw [inv_le_inv₀ hN_pos hs_real_pos]
        exact hs_le
      linarith
    exact h2.trans h1
  have h_log_mono : Real.log (1 + (N : ℝ)⁻¹) ≤ Real.log ((r : ℝ) / s) := by
    apply Real.log_le_log (by positivity) h_div_le
  exact (inv_le_log_one_add_inv N hN).trans h_log_mono

/-- Separation of logarithmic points: $|\log r - \log s| \ge (2N)^{-1}$ for distinct $r, s \in (0, N]$. -/
lemma inv_le_abs_log_sub_log_of_mem_Ioc {s r N : ℕ} (hs : s ∈ Finset.Ioc 0 N) (hr : r ∈ Finset.Ioc 0 N) (hne : r ≠ s) :
    (2 * (N : ℝ))⁻¹ ≤ |Real.log (r : ℝ) - Real.log (s : ℝ)| := by
  rw [Finset.mem_Ioc] at hs hr
  rcases lt_or_gt_of_ne hne with h | h
  · have hs_pos : 0 < (s : ℝ) := by exact_mod_cast hs.1
    have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr.1
    have h_sub : Real.log (s : ℝ) - Real.log (r : ℝ) = Real.log ((s : ℝ) / r) := by
      rw [Real.log_div (ne_of_gt hs_pos) (ne_of_gt hr_pos)]
    have h_div_ge := inv_le_log_div_of_lt hr.1 h hs.2
    rw [abs_sub_comm]
    have h_ge_zero : 0 ≤ Real.log (s : ℝ) - Real.log (r : ℝ) := by
      have : (2 * (N : ℝ))⁻¹ > 0 := by
        have : 0 < (N : ℝ) := by
          have : 0 < N := by omega
          exact_mod_cast this
        positivity
      rw [h_sub]
      linarith
    rw [abs_of_nonneg h_ge_zero, h_sub]
    exact h_div_ge
  · have hs_pos : 0 < (s : ℝ) := by exact_mod_cast hs.1
    have hr_pos : 0 < (r : ℝ) := by exact_mod_cast hr.1
    have h_sub : Real.log (r : ℝ) - Real.log (s : ℝ) = Real.log ((r : ℝ) / s) := by
      rw [Real.log_div (ne_of_gt hr_pos) (ne_of_gt hs_pos)]
    have h_div_ge := inv_le_log_div_of_lt hs.1 h hr.2
    have h_ge_zero : 0 ≤ Real.log (r : ℝ) - Real.log (s : ℝ) := by
      have : (2 * (N : ℝ))⁻¹ > 0 := by
        have : 0 < (N : ℝ) := by
          have : 0 < N := by omega
          exact_mod_cast this
        positivity
      rw [h_sub]
      linarith
    rw [abs_of_nonneg h_ge_zero, h_sub]
    exact h_div_ge

/-- Equivalence of sum over erased subtype and sum over erased Finset. -/
lemma sum_erase_subtype_eq {α : Type*} [DecidableEq α] (S : Finset α) (r : {x // x ∈ S}) (h : α → ℂ) :
    (∑ s ∈ Finset.univ.erase r, h s.1) = ∑ s ∈ S.erase r.1, h s := by
  have h1 : (∑ s : {x // x ∈ S}, h s.1) = h r.1 + ∑ s ∈ Finset.univ.erase r, h s.1 := by
    exact (Finset.add_sum_erase Finset.univ (fun s => h s.1) (Finset.mem_univ r)).symm
  have h2 : (∑ s ∈ S, h s) = h r.1 + ∑ s ∈ S.erase r.1, h s := by
    exact (Finset.add_sum_erase S h r.2).symm
  have h3 : (∑ s ∈ S, h s) = (∑ s : {x // x ∈ S}, h s.1) :=
    Finset.sum_subtype S (fun x => Iff.rfl) h
  rw [h3] at h2
  rw [h1] at h2
  exact add_left_cancel h2

/-- Hilbert inequality adapted to finite sums over arbitrary `Finset`. -/
lemma norm_hilbert_form_finset_le {α : Type*} [DecidableEq α] (S : Finset α) (x : α → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |x r - x s|) (u : α → ℂ) :
    ‖∑ r ∈ S, ∑ s ∈ S.erase r, u r * (starRingEnd ℂ) (u s) / ((x r - x s : ℝ) : ℂ)‖ ≤
      Real.pi * δ⁻¹ * ∑ r ∈ S, ‖u r‖ ^ 2 := by
  let ι := {r : α // r ∈ S}
  let x_ι (r : ι) : ℝ := x r.1
  let u_ι (r : ι) : ℂ := u r.1
  have hsep_ι (r s : ι) (hrs : r ≠ s) : δ ≤ |x_ι r - x_ι s| := by
    apply hsep r.1 r.2 s.1 s.2
    intro h
    apply hrs
    exact Subtype.ext h
  have h_bound := norm_hilbert_form_le x_ι hδ hsep_ι u_ι
  have h_rhs : (∑ r : ι, ‖u_ι r‖ ^ 2) = ∑ r ∈ S, ‖u r‖ ^ 2 := by
    exact (Finset.sum_subtype S (fun x => Iff.rfl) (fun a => ‖u a‖ ^ 2)).symm
  rw [h_rhs] at h_bound
  have h_lhs : (∑ r : ι, ∑ s ∈ Finset.univ.erase r, u_ι r * (starRingEnd ℂ) (u_ι s) / ((x_ι r - x_ι s : ℝ) : ℂ)) =
      ∑ r ∈ S, ∑ s ∈ S.erase r, u r * (starRingEnd ℂ) (u s) / ((x r - x s : ℝ) : ℂ) := by
    rw [Finset.sum_subtype S (fun x => Iff.rfl) (fun r => ∑ s ∈ S.erase r, u r * (starRingEnd ℂ) (u s) / ((x r - x s : ℝ) : ℂ))]
    apply Finset.sum_congr rfl
    intro r _
    exact sum_erase_subtype_eq S r (fun s => u r.1 * (starRingEnd ℂ) (u s) / ((x r.1 - x s : ℝ) : ℂ))
  rwa [h_lhs] at h_bound

/-- Complex conjugation of $\exp(i t)$. -/
lemma starRingEnd_exp_I_mul (t : ℝ) :
    (starRingEnd ℂ) (Complex.exp (Complex.I * (t : ℂ))) = Complex.exp (-Complex.I * (t : ℂ)) := by
  rw [← Complex.exp_conj]
  simp

/-- Division by $i$ of difference of exponentials gives $2 \sin \theta$. -/
lemma exp_diff_div_I (θ : ℝ) :
    (Complex.exp (Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (θ : ℂ))) / Complex.I =
      2 * (Real.sin θ : ℂ) := by
  have hsin : (Real.sin θ : ℂ) = Complex.sin (θ : ℂ) := Complex.ofReal_sin θ
  rw [hsin]
  unfold Complex.sin
  have h1 : -Complex.I * (θ : ℂ) = -(θ : ℂ) * Complex.I := by ring
  have h2 : Complex.I * (θ : ℂ) = (θ : ℂ) * Complex.I := by ring
  rw [h1, h2]
  rw [Complex.div_I]
  ring

/-- Product $\exp(i T x_m) \overline{\exp(i T x_n)} = \exp(i T (x_m - x_n))$. -/
lemma exp_sub_eq (T xm xn : ℝ) :
    Complex.exp (Complex.I * ((T * xm : ℝ) : ℂ)) * (starRingEnd ℂ) (Complex.exp (Complex.I * ((T * xn : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((T * (xm - xn) : ℝ) : ℂ)) := by
  have h_conj : (starRingEnd ℂ) (Complex.exp (Complex.I * ((T * xn : ℝ) : ℂ))) =
      Complex.exp (-Complex.I * ((T * xn : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj]
    simp
  rw [h_conj, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Product $\exp(-i T x_m) \overline{\exp(-i T x_n)} = \exp(-i T (x_m - x_n))$. -/
lemma exp_sub_neg_eq (T xm xn : ℝ) :
    Complex.exp (-Complex.I * ((T * xm : ℝ) : ℂ)) * (starRingEnd ℂ) (Complex.exp (-Complex.I * ((T * xn : ℝ) : ℂ))) =
      Complex.exp (-Complex.I * ((T * (xm - xn) : ℝ) : ℂ)) := by
  have h_conj : (starRingEnd ℂ) (Complex.exp (-Complex.I * ((T * xn : ℝ) : ℂ))) =
      Complex.exp (Complex.I * ((T * xn : ℝ) : ℂ)) := by
    rw [← Complex.exp_conj]
    simp
  rw [h_conj, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Identity $-i \cdot (i \cdot z) = z$. -/
lemma neg_I_mul_I_mul (z : ℂ) : -Complex.I * (Complex.I * z) = z := by
  have : -Complex.I * Complex.I = 1 := by
    calc -Complex.I * Complex.I = -(Complex.I * Complex.I) := by ring
    _ = -(-1) := by rw [Complex.I_mul_I]
    _ = 1 := by ring
  rw [← mul_assoc, this, one_mul]

/-- Decomposition of an off-diagonal Dirichlet polynomial kernel term into two Hilbert terms. -/
lemma off_diag_term_decomp (a : ℕ → ℂ) (T : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    let x (k : ℕ) : ℝ := Real.log (k : ℝ)
    let u1 (k : ℕ) : ℂ := a k * Complex.exp (Complex.I * ((T * x k : ℝ) : ℂ)) / (k : ℂ)
    let u2 (k : ℕ) : ℂ := a k * Complex.exp (-Complex.I * ((T * x k : ℝ) : ℂ)) / (k : ℂ)
    (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
        (2 * Real.sin (T * Real.log ((m : ℝ) / n)) / Real.log ((m : ℝ) / n) : ℂ) =
      (-Complex.I) * ((u1 m * (starRingEnd ℂ) (u1 n) / ((x m - x n : ℝ) : ℂ)) -
        (u2 m * (starRingEnd ℂ) (u2 n) / ((x m - x n : ℝ) : ℂ))) := by
  intro x u1 u2
  have hm_pos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have h_log_div : Real.log ((m : ℝ) / n) = x m - x n :=
    Real.log_div (ne_of_gt hm_pos) (ne_of_gt hn_pos)
  have h_ne : x m - x n ≠ 0 := by
    rw [← h_log_div]
    intro h
    have h1 : (m : ℝ) / n = 1 := Real.eq_one_of_pos_of_log_eq_zero (div_pos hm_pos hn_pos) h
    have h2 : (m : ℝ) = (n : ℝ) := (div_eq_one_iff_eq (ne_of_gt hn_pos)).mp h1
    exact hmn (Nat.cast_injective h2)
  have _ : ((x m - x n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h_ne
  have h_u1 : u1 m * (starRingEnd ℂ) (u1 n) =
      (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
        Complex.exp (Complex.I * ((T * (x m - x n) : ℝ) : ℂ)) := by
    dsimp [u1]
    simp only [map_mul, map_div₀]
    have hc_n : (starRingEnd ℂ) (n : ℂ) = (n : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.conj_ofReal]
    rw [hc_n]
    have h_exp := exp_sub_eq T (x m) (x n)
    calc
      a m * Complex.exp (Complex.I * ((T * x m : ℝ) : ℂ)) / (m : ℂ) *
          ((starRingEnd ℂ) (a n) * (starRingEnd ℂ) (Complex.exp (Complex.I * ((T * x n : ℝ) : ℂ))) / (n : ℂ)) =
        (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
          (Complex.exp (Complex.I * ((T * x m : ℝ) : ℂ)) * (starRingEnd ℂ) (Complex.exp (Complex.I * ((T * x n : ℝ) : ℂ)))) := by ring
      _ = (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) * Complex.exp (Complex.I * ((T * (x m - x n) : ℝ) : ℂ)) := by rw [h_exp]
  have h_u2 : u2 m * (starRingEnd ℂ) (u2 n) =
      (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
        Complex.exp (-Complex.I * ((T * (x m - x n) : ℝ) : ℂ)) := by
    dsimp [u2]
    simp only [map_mul, map_div₀]
    have hc_n : (starRingEnd ℂ) (n : ℂ) = (n : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.conj_ofReal]
    rw [hc_n]
    have h_exp := exp_sub_neg_eq T (x m) (x n)
    calc
      a m * Complex.exp (-Complex.I * ((T * x m : ℝ) : ℂ)) / (m : ℂ) *
          ((starRingEnd ℂ) (a n) * (starRingEnd ℂ) (Complex.exp (-Complex.I * ((T * x n : ℝ) : ℂ))) / (n : ℂ)) =
        (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
          (Complex.exp (-Complex.I * ((T * x m : ℝ) : ℂ)) * (starRingEnd ℂ) (Complex.exp (-Complex.I * ((T * x n : ℝ) : ℂ)))) := by ring
      _ = (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) * Complex.exp (-Complex.I * ((T * (x m - x n) : ℝ) : ℂ)) := by rw [h_exp]
  rw [h_log_div]
  rw [h_u1, h_u2]
  have h_diff : (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
          Complex.exp (Complex.I * ((T * (x m - x n) : ℝ) : ℂ)) / ((x m - x n : ℝ) : ℂ) -
        (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
          Complex.exp (-Complex.I * ((T * (x m - x n) : ℝ) : ℂ)) / ((x m - x n : ℝ) : ℂ) =
      (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
        ((Complex.exp (Complex.I * ((T * (x m - x n) : ℝ) : ℂ)) -
          Complex.exp (-Complex.I * ((T * (x m - x n) : ℝ) : ℂ))) / ((x m - x n : ℝ) : ℂ)) := by
    ring
  rw [h_diff]
  have h_sin := exp_diff_div_I (T * (x m - x n))
  have h_sin_eq : (Complex.exp (Complex.I * ((T * (x m - x n) : ℝ) : ℂ)) -
        Complex.exp (-Complex.I * ((T * (x m - x n) : ℝ) : ℂ))) =
      Complex.I * (2 * (Real.sin (T * (x m - x n)) : ℂ)) := by
    rw [← h_sin]
    have : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp
  rw [h_sin_eq]
  have h_calc : (-Complex.I) * ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
        (Complex.I * (2 * (Real.sin (T * (x m - x n)) : ℂ)) / ((x m - x n : ℝ) : ℂ))) =
      -Complex.I * (Complex.I * ((a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
        (2 * (Real.sin (T * (x m - x n)) : ℂ) / ((x m - x n : ℝ) : ℂ)))) := by
    ring
  rw [h_calc, neg_I_mul_I_mul]

/-- Squared norm of the first twisted coefficient $u_1(m)$ is $|a_m|^2 / m^2$. -/
lemma norm_u1_sq (a : ℕ → ℂ) (T : ℝ) (m : ℕ) :
    let x (k : ℕ) : ℝ := Real.log (k : ℝ)
    let u1 (k : ℕ) : ℂ := a k * Complex.exp (Complex.I * ((T * x k : ℝ) : ℂ)) / (k : ℂ)
    ‖u1 m‖ ^ 2 = ‖a m‖ ^ 2 / (m : ℝ) ^ 2 := by
  intro x u1
  dsimp [u1]
  rw [norm_div, norm_mul]
  have h_exp : ‖Complex.exp (Complex.I * ((T * x m : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  have h_m : ‖(m : ℂ)‖ = (m : ℝ) := Complex.norm_natCast m
  rw [h_exp, h_m, mul_one, div_pow]

/-- Squared norm of the second twisted coefficient $u_2(m)$ is $|a_m|^2 / m^2$. -/
lemma norm_u2_sq (a : ℕ → ℂ) (T : ℝ) (m : ℕ) :
    let x (k : ℕ) : ℝ := Real.log (k : ℝ)
    let u2 (k : ℕ) : ℂ := a k * Complex.exp (-Complex.I * ((T * x k : ℝ) : ℂ)) / (k : ℂ)
    ‖u2 m‖ ^ 2 = ‖a m‖ ^ 2 / (m : ℝ) ^ 2 := by
  intro x u2
  dsimp [u2]
  rw [norm_div, norm_mul]
  have h_exp : ‖Complex.exp (-Complex.I * ((T * x m : ℝ) : ℂ))‖ = 1 := by
    have : -Complex.I * ((T * x m : ℝ) : ℂ) = (-(T * x m) : ℝ) * Complex.I := by
      push_cast; ring
    rw [this]
    exact Complex.norm_exp_ofReal_mul_I _
  have h_m : ‖(m : ℂ)‖ = (m : ℝ) := Complex.norm_natCast m
  rw [h_exp, h_m, mul_one, div_pow]

/-- Norm of $-i$ is 1. -/
lemma norm_neg_I : ‖(-Complex.I : ℂ)‖ = 1 := by
  rw [norm_neg, Complex.norm_I]

/-- Real part commutes with double summation over a Finset. -/
lemma sum_sum_re_eq {α : Type*} [DecidableEq α] (S : Finset α) (w : α → α → ℂ) :
    (∑ m ∈ S, ∑ n ∈ S.erase m, (w m n).re) = (∑ m ∈ S, ∑ n ∈ S.erase m, w m n).re := by
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Complex.re_sum]

/-- Linearity of double summation for decomposed off-diagonal terms. -/
lemma double_sum_decomp {α : Type*} [DecidableEq α] (S : Finset α) (w h1 h2 : α → α → ℂ)
    (h_term : ∀ m ∈ S, ∀ n ∈ S.erase m, w m n = (-Complex.I) * (h1 m n - h2 m n)) :
    (∑ m ∈ S, ∑ n ∈ S.erase m, w m n) =
      (-Complex.I) * ((∑ m ∈ S, ∑ n ∈ S.erase m, h1 m n) - (∑ m ∈ S, ∑ n ∈ S.erase m, h2 m n)) := by
  have h_inner (m : α) (hm : m ∈ S) :
      (∑ n ∈ S.erase m, w m n) = (-Complex.I) * ((∑ n ∈ S.erase m, h1 m n) - (∑ n ∈ S.erase m, h2 m n)) := by
    have : (∑ n ∈ S.erase m, w m n) = ∑ n ∈ S.erase m, (-Complex.I * (h1 m n - h2 m n)) :=
      Finset.sum_congr rfl (fun n hn => h_term m hm n hn)
    rw [this, ← Finset.mul_sum, ← Finset.sum_sub_distrib]
  have h_outer : (∑ m ∈ S, ∑ n ∈ S.erase m, w m n) =
      ∑ m ∈ S, (-Complex.I * ((∑ n ∈ S.erase m, h1 m n) - (∑ n ∈ S.erase m, h2 m n))) :=
    Finset.sum_congr rfl h_inner
  rw [h_outer, ← Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- Montgomery's mean value theorem for Dirichlet polynomials on the line Re s = 1. -/
theorem integral_norm_sq_dirichletPoly_le_mul (a : ℕ → ℂ) (N : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∫ t in (-T)..T, ‖dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I)‖ ^ 2 ≤
      (2 * T + 6 * Real.pi * N) * ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  by_cases hN0 : N = 0
  · subst hN0
    simp only [Finset.Ioc_self, dirichletPoly, Finset.sum_empty, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_const, smul_eq_mul, mul_zero,
      Nat.cast_zero, mul_zero, add_zero, le_refl]
  · have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    have _ : 0 < (N : ℝ) := Nat.cast_pos.mpr hN1
    let S := Finset.Ioc 0 N
    have hS_pos : ∀ n ∈ S, 0 < n := by
      intro n hn
      exact (Finset.mem_Ioc.mp hn).1
    have h_int := integral_norm_sq_dirichletPoly a S hS_pos T hT
    rw [h_int]
    let x (k : ℕ) : ℝ := Real.log (k : ℝ)
    let u1 (k : ℕ) : ℂ := a k * Complex.exp (Complex.I * ((T * x k : ℝ) : ℂ)) / (k : ℂ)
    let u2 (k : ℕ) : ℂ := a k * Complex.exp (-Complex.I * ((T * x k : ℝ) : ℂ)) / (k : ℂ)
    let w (m n : ℕ) : ℂ := (a m * (starRingEnd ℂ) (a n) / ((m : ℂ) * (n : ℂ))) *
        (2 * Real.sin (T * Real.log ((m : ℝ) / n)) / Real.log ((m : ℝ) / n) : ℂ)
    let h1 (m n : ℕ) : ℂ := u1 m * (starRingEnd ℂ) (u1 n) / ((x m - x n : ℝ) : ℂ)
    let h2 (m n : ℕ) : ℂ := u2 m * (starRingEnd ℂ) (u2 n) / ((x m - x n : ℝ) : ℂ)
    have hw_eq : ∀ m ∈ S, ∀ n ∈ S.erase m, w m n = (-Complex.I) * (h1 m n - h2 m n) := by
      intro m hm n hn
      have hm_pos := hS_pos m hm
      have hn_in : n ∈ S := Finset.mem_of_mem_erase hn
      have hn_pos := hS_pos n hn_in
      have hmn : m ≠ n := (Finset.ne_of_mem_erase hn).symm
      exact off_diag_term_decomp a T m n hm_pos hn_pos hmn
    have h_decomp := double_sum_decomp S w h1 h2 hw_eq
    rw [sum_sum_re_eq S w]
    have h_re_le := Complex.re_le_norm (∑ m ∈ S, ∑ n ∈ S.erase m, w m n)
    have h_norm_eq : ‖∑ m ∈ S, ∑ n ∈ S.erase m, w m n‖ =
        ‖(∑ m ∈ S, ∑ n ∈ S.erase m, h1 m n) - (∑ m ∈ S, ∑ n ∈ S.erase m, h2 m n)‖ := by
      rw [h_decomp, norm_mul, norm_neg_I, one_mul]
    have h_sub_le : ‖(∑ m ∈ S, ∑ n ∈ S.erase m, h1 m n) - (∑ m ∈ S, ∑ n ∈ S.erase m, h2 m n)‖ ≤
        ‖∑ m ∈ S, ∑ n ∈ S.erase m, h1 m n‖ + ‖∑ m ∈ S, ∑ n ∈ S.erase m, h2 m n‖ := norm_sub_le _ _
    let δ := (2 * (N : ℝ))⁻¹
    have hδ_pos : 0 < δ := by
      dsimp [δ]
      positivity
    have hsep : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → δ ≤ |x r - x s| := fun r hr s hs hrs =>
      inv_le_abs_log_sub_log_of_mem_Ioc hs hr hrs
    have h_H1 := norm_hilbert_form_finset_le S x hδ_pos hsep u1
    have h_H2 := norm_hilbert_form_finset_le S x hδ_pos hsep u2
    have hu1_norm : (∑ r ∈ S, ‖u1 r‖ ^ 2) = ∑ r ∈ S, ‖a r‖ ^ 2 / (r : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      exact norm_u1_sq a T r
    have hu2_norm : (∑ r ∈ S, ‖u2 r‖ ^ 2) = ∑ r ∈ S, ‖a r‖ ^ 2 / (r : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      exact norm_u2_sq a T r
    rw [hu1_norm] at h_H1
    rw [hu2_norm] at h_H2
    have h_inv_δ : δ⁻¹ = 2 * (N : ℝ) := by
      dsimp [δ]
      exact inv_inv (2 * (N : ℝ))
    rw [h_inv_δ] at h_H1 h_H2
    have h_sum_nonneg : 0 ≤ ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
      apply Finset.sum_nonneg
      intro i _
      positivity
    have h_offdiag_le : ‖∑ m ∈ S, ∑ n ∈ S.erase m, w m n‖ ≤
        (4 * Real.pi * N) * ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
      rw [h_norm_eq]
      refine h_sub_le.trans ?_
      have : Real.pi * (2 * (N : ℝ)) * (∑ r ∈ S, ‖a r‖ ^ 2 / (r : ℝ) ^ 2) +
          Real.pi * (2 * (N : ℝ)) * (∑ r ∈ S, ‖a r‖ ^ 2 / (r : ℝ) ^ 2) =
          (4 * Real.pi * N) * ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by ring
      rw [← this]
      exact add_le_add h_H1 h_H2
    have h_offdiag_le_6 : ‖∑ m ∈ S, ∑ n ∈ S.erase m, w m n‖ ≤
        (6 * Real.pi * N) * ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
      refine h_offdiag_le.trans ?_
      have : (4 * Real.pi * N) ≤ (6 * Real.pi * N) := by
        have : 0 ≤ Real.pi := Real.pi_pos.le
        nlinarith
      exact mul_le_mul_of_nonneg_right this h_sum_nonneg
    have h_total : (∑ m ∈ S, ∑ n ∈ S.erase m, w m n).re ≤
        (6 * Real.pi * N) * ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 :=
      h_re_le.trans h_offdiag_le_6
    calc
      2 * T * (∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2) + (∑ m ∈ S, ∑ n ∈ S.erase m, w m n).re ≤
          2 * T * (∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2) + (6 * Real.pi * N) * ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
        linarith [h_total]
      _ = (2 * T + 6 * Real.pi * N) * ∑ n ∈ S, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by ring

end Erdos1201.MR
