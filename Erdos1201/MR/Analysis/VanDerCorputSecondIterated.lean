import Mathlib
import Erdos1201.MR.Analysis.KusminLandau
import Erdos1201.MR.Analysis.LogIteratedDifferences
import Erdos1201.MR.Analysis.VanDerCorput
import Erdos1201.MR.Analysis.VanDerCorputIteratedMain

open Real Complex Finset

/-!
# Discrete Second-Derivative Test for Iterated Van der Corput Phases

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes the discrete second-derivative test (Graham–Kolesnik, Theorem 2.2)
for the $m$-fold differenced phases `vdc_phase t m h n`, uniformly in the depth $m \le K_0$.
-/

namespace Erdos1201.MR

/-- The natural size of the k-th difference of the m-fold differenced phase. -/
noncomputable def vdcLam (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (N k : ℕ) : ℝ :=
  (t / (2 * Real.pi)) * ((m + k - 1).factorial * ∏ i, (h i : ℝ)) / (N : ℝ) ^ (m + k)

/-- Step recurrence for `vdcLam`: shifting by `j` at order `k - 1` scales by `j`. -/
lemma vdcLam_snoc (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (N : ℕ) (k : ℕ) (_hk : 1 ≤ k) (j : ℕ) :
    vdcLam t (m + 1) (Fin.snoc h j) N (k - 1) = (j : ℝ) * vdcLam t m h N k := by
  dsimp [vdcLam]
  have h_fac : (m + 1 + (k - 1) - 1).factorial = (m + k - 1).factorial := by
    congr 1; omega
  have h_pow : (N : ℝ) ^ (m + 1 + (k - 1)) = (N : ℝ) ^ (m + k) := by
    congr 1; omega
  have h_prod : ∏ i : Fin (m + 1), (((Fin.snoc (α := fun _ => ℕ) h j) i : ℕ) : ℝ) =
      (∏ i : Fin m, (h i : ℝ)) * (j : ℝ) := by
    have hsnoc := Fin.prod_snoc (j : ℝ) (fun i : Fin m => (h i : ℝ))
    have heq : (fun i : Fin (m + 1) => (((Fin.snoc (α := fun _ => ℕ) h j) i : ℕ) : ℝ)) =
        Fin.snoc (α := fun _ => ℝ) (fun i : Fin m => (h i : ℝ)) (j : ℝ) := by
      ext i
      obtain ⟨i0, rfl⟩ | rfl := Fin.eq_castSucc_or_eq_last i
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      · rw [Fin.snoc_last, Fin.snoc_last]
    rw [heq, hsnoc]
  rw [h_fac, h_pow, h_prod]
  ring

/-- The signed differenced phase whose second difference is strictly positive. -/
noncomputable def vdc_F (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ m * vdc_phase t m h n

/-- First difference of the signed phase `vdc_F`. -/
noncomputable def vdc_d2 (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (n : ℕ) : ℝ :=
  vdc_F t m h (n + 1) - vdc_F t m h n

/-- Second consecutive difference identity for `vdc_phase`. -/
lemma vdc_consec_consec_diff_eq (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (n : ℕ) :
    vdc_phase t m h (n + 2) - 2 * vdc_phase t m h (n + 1) + vdc_phase t m h n =
    vdc_phase t (m + 2) (Fin.snoc (α := fun _ => ℕ) (Fin.snoc h 1) 1) n := by
  have h1 := vdc_phase_diff t m h 1 (n + 1)
  have h2 := vdc_phase_diff t m h 1 n
  have h3 := vdc_phase_diff t (m + 1) (Fin.snoc h 1) 1 n
  linarith

/-- Second difference of `vdc_F` expressed in terms of `vdc_phase` at depth `m + 2`. -/
lemma vdc_d2_diff_eq (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (n : ℕ) :
    vdc_d2 t m h (n + 1) - vdc_d2 t m h n =
    (-1 : ℝ) ^ m * vdc_phase t (m + 2) (Fin.snoc (α := fun _ => ℕ) (Fin.snoc h 1) 1) n := by
  dsimp [vdc_d2, vdc_F]
  have hdiff := vdc_consec_consec_diff_eq t m h n
  calc (-1 : ℝ) ^ m * vdc_phase t m h (n + 2) - (-1 : ℝ) ^ m * vdc_phase t m h (n + 1) -
      ((-1 : ℝ) ^ m * vdc_phase t m h (n + 1) - (-1 : ℝ) ^ m * vdc_phase t m h n)
    _ = (-1 : ℝ) ^ m * (vdc_phase t m h (n + 2) - 2 * vdc_phase t m h (n + 1) + vdc_phase t m h n) := by ring
    _ = (-1 : ℝ) ^ m * vdc_phase t (m + 2) (Fin.snoc (α := fun _ => ℕ) (Fin.snoc h 1) 1) n := by rw [hdiff]

/-- Absolute value of the second difference of `vdc_F`. -/
lemma abs_vdc_d2_diff_eq (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (n : ℕ) :
    |vdc_d2 t m h (n + 1) - vdc_d2 t m h n| =
    |vdc_phase t (m + 1) (Fin.snoc h 1) (n + 1) - vdc_phase t (m + 1) (Fin.snoc h 1) n| := by
  have h3 := vdc_phase_diff t (m + 1) (Fin.snoc h 1) 1 n
  rw [vdc_d2_diff_eq, ← h3, abs_mul]
  have : |(-1 : ℝ) ^ m| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [this, one_mul]

/-- Identity relating `vdc_d2` increment to `logIterDiff`. -/
lemma vdc_d2_diff_eq_logIterDiff (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (n : ℕ) :
    vdc_d2 t m h (n + 1) - vdc_d2 t m h n =
    (t / (2 * Real.pi)) * ((-1 : ℝ) ^ (m + 1) * logIterDiff (m + 2) (Fin.snoc (α := fun _ => ℕ) (Fin.snoc h 1) 1) (n : ℝ)) := by
  rw [vdc_d2_diff_eq]
  dsimp [vdc_phase]
  have : (-1 : ℝ) ^ m * (- (t / (2 * Real.pi)) * logIterDiff (m + 2) (Fin.snoc (α := fun _ => ℕ) (Fin.snoc h 1) 1) (n : ℝ)) =
      (t / (2 * Real.pi)) * ((- ((-1 : ℝ) ^ m)) * logIterDiff (m + 2) (Fin.snoc (α := fun _ => ℕ) (Fin.snoc h 1) 1) (n : ℝ)) := by ring
  rw [this]
  congr 2
  have hpow : (-1 : ℝ) ^ (m + 1) = - ((-1 : ℝ) ^ m) := by
    rw [pow_succ]
    ring
  rw [hpow]

/-- The difference increment of `vdc_d2` is strictly positive. -/
lemma vdc_d2_diff_pos (t : ℝ) (ht : 0 < t) (m : ℕ) (h : Fin m → ℕ) (hpos : ∀ i, 1 ≤ h i)
    (n : ℕ) (hn : 1 ≤ n) :
    0 < vdc_d2 t m h (n + 1) - vdc_d2 t m h n := by
  rw [vdc_d2_diff_eq_logIterDiff]
  have ht_div : 0 < t / (2 * Real.pi) := by positivity
  have hm2 : 1 ≤ m + 2 := by omega
  have hpos' : ∀ i : Fin (m + 2), 1 ≤ (Fin.snoc (α := fun _ => ℕ) (Fin.snoc h 1) 1) i := by
    have h1 := fin_snoc_one_ge_one m h hpos
    exact fin_snoc_one_ge_one (m + 1) (Fin.snoc h 1) h1
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hsign := sign_logIterDiff (m + 2) hm2 (Fin.snoc (α := fun _ => ℕ) (Fin.snoc h 1) 1) hpos' (n : ℝ) hn_pos
  have hsub : m + 2 - 1 = m + 1 := rfl
  rw [hsub] at hsign
  exact mul_pos ht_div hsign

/-- Sharp upper and lower bounds on the second differences of `vdc_F`. -/
lemma vdc_d2_diff_bounds (t : ℝ) (ht : 0 ≤ t) (m : ℕ) (h : Fin m → ℕ)
    (hpos : ∀ i, 1 ≤ h i) (N : ℕ) (hN : 1 ≤ N) (hh : ∀ i, h i ≤ N)
    (n : ℕ) (hn1 : N ≤ n) (hn2 : n ≤ 2 * N) :
    vdcLam t m h N 2 / (m + 4 : ℝ) ^ (m + 2) ≤
      |vdc_d2 t m h (n + 1) - vdc_d2 t m h n| ∧
    |vdc_d2 t m h (n + 1) - vdc_d2 t m h n| ≤
      vdcLam t m h N 2 := by
  have hpos' := fin_snoc_one_ge_one m h hpos
  have hh' := fin_snoc_one_le m h hh hN
  have hn2_cast : (n : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hn2
  have hbounds := abs_vdc_consec_diff_bounds t ht (m + 1) (Fin.snoc h 1) hpos' N hN hh' n hn1 hn2_cast
  rw [abs_vdc_d2_diff_eq]
  have hprod := prod_fin_snoc_one m h
  have hbase : (((m + 1 : ℕ) : ℝ) + 3) = (m + 4 : ℝ) := by push_cast; ring
  have hpow : m + 1 + 1 = m + 2 := by omega
  have hdenom : (((m + 1 : ℕ) : ℝ) + 3) ^ (m + 1 + 1) = (m + 4 : ℝ) ^ (m + 2) := by
    rw [hbase, hpow]
  have hstep : (((((m + 1 : ℕ) : ℝ) + 3) * (N : ℝ)) ^ (m + 1 + 1)) = (m + 4 : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2) := by
    rw [mul_pow, hpow, hdenom]
  have hpow_N : (N : ℝ) ^ (m + 1 + 1) = (N : ℝ) ^ (m + 2) := by
    rw [show m + 1 + 1 = m + 2 by omega]
  rw [hprod] at hbounds
  dsimp [vdcLam]
  constructor
  · have hlow := hbounds.1
    rw [hstep] at hlow
    have h_alg : (t / (2 * Real.pi)) * ((m + 1).factorial * ∏ i, (h i : ℝ)) / (N : ℝ) ^ (m + 2) / (m + 4 : ℝ) ^ (m + 2) =
        (t / (2 * Real.pi)) * (((m + 1).factorial * ∏ i, (h i : ℝ)) / ((m + 4 : ℝ) ^ (m + 2) * (N : ℝ) ^ (m + 2))) := by
      rw [div_div, mul_div_assoc, mul_comm ((N : ℝ) ^ (m + 2))]
    rw [h_alg]
    exact hlow
  · have hup := hbounds.2
    rw [hpow_N] at hup
    rw [mul_div_assoc]
    exact hup

/-- Complex conjugation of the exponential phase increment flips sign. -/
lemma star_exp_two_pi_I_mul (x : ℝ) :
    star (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) =
    Complex.exp (2 * Real.pi * Complex.I * ((-x : ℝ) : ℂ)) := by
  change (starRingEnd ℂ) (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

/-- Summing the conjugate phase gives the same norm. -/
lemma norm_sum_exp_neg (s : Finset ℕ) (f : ℕ → ℝ) :
    ‖∑ n ∈ s, Complex.exp (2 * Real.pi * Complex.I * ((- f n : ℝ) : ℂ))‖ =
    ‖∑ n ∈ s, Complex.exp (2 * Real.pi * Complex.I * ((f n : ℝ) : ℂ))‖ := by
  have heq : (∑ n ∈ s, Complex.exp (2 * Real.pi * Complex.I * ((- f n : ℝ) : ℂ))) =
      star (∑ n ∈ s, Complex.exp (2 * Real.pi * Complex.I * ((f n : ℝ) : ℂ))) := by
    rw [star_sum]
    refine sum_congr rfl fun n _ => ?_
    exact (star_exp_two_pi_I_mul (f n)).symm
  rw [heq, star_def, Complex.norm_conj]

/-- The norm of `vdc_S` equals the norm of the sum of `vdc_F`. -/
lemma norm_vdc_S_eq_norm_sum_exp_F (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (a b : ℕ) :
    ‖vdc_S t m h a b‖ =
    ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * Complex.I * ((vdc_F t m h n : ℝ) : ℂ))‖ := by
  dsimp [vdc_S, vdc_F]
  obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd m
  · have hpow : (-1 : ℝ) ^ m = 1 := Even.neg_one_pow ⟨k, hk⟩
    simp only [hpow, one_mul]
  · have hpow : (-1 : ℝ) ^ m = -1 := Odd.neg_one_pow ⟨k, hk⟩
    simp only [hpow, neg_one_mul]
    exact (norm_sum_exp_neg (Finset.Ioc a b) (fun n => vdc_phase t m h n)).symm

/-- Trivial bound on `vdc_S` by interval length. -/
lemma norm_vdc_S_le_card (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (a b : ℕ) :
    ‖vdc_S t m h a b‖ ≤ ((b - a : ℕ) : ℝ) := by
  dsimp [vdc_S]
  have h1 := norm_sum_le (Finset.Ioc a b) (fun n => Complex.exp (2 * Real.pi * Complex.I * ((vdc_phase t m h n : ℝ) : ℂ)))
  refine h1.trans ?_
  have h2 : ∀ n ∈ Finset.Ioc a b, ‖Complex.exp (2 * Real.pi * Complex.I * ((vdc_phase t m h n : ℝ) : ℂ))‖ = 1 :=
    fun n _ => norm_exp_two_pi_I_mul (vdc_phase t m h n)
  rw [sum_congr rfl h2, sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc]

/-- Lower bound on interval variation from lower bound on step sizes. -/
lemma d_sub_ge_mul_diff_gen (d : ℕ → ℝ) (s_min : ℝ) (a b : ℕ) (hab : a ≤ b)
    (hstep : ∀ m, a ≤ m → m < b → s_min ≤ d (m + 1) - d m) :
    ((b - a : ℕ) : ℝ) * s_min ≤ d b - d a := by
  have h_sum : ∑ m ∈ Finset.Ico a b, (d (m + 1) - d m) = d b - d a :=
    sum_Ico_sub d hab
  rw [← h_sum]
  have hcard : (Finset.Ico a b).card = b - a := Nat.card_Ico a b
  have h_const : ∑ m ∈ Finset.Ico a b, s_min = ((b - a : ℕ) : ℝ) * s_min := by
    rw [sum_const, hcard, nsmul_eq_mul]
  rw [← h_const]
  exact sum_le_sum fun m hm => hstep m (mem_Ico.mp hm).1 (mem_Ico.mp hm).2

/-- Upper bound on interval variation from upper bound on step sizes. -/
lemma d_sub_le_mul_diff_gen (d : ℕ → ℝ) (lam : ℝ) (a b : ℕ) (hab : a ≤ b)
    (hstep : ∀ m, a ≤ m → m < b → d (m + 1) - d m ≤ lam) :
    d b - d a ≤ ((b - a : ℕ) : ℝ) * lam := by
  have h_sum : ∑ m ∈ Finset.Ico a b, (d (m + 1) - d m) = d b - d a :=
    sum_Ico_sub d hab
  rw [← h_sum]
  have hcard : (Finset.Ico a b).card = b - a := Nat.card_Ico a b
  have h_const : ∑ m ∈ Finset.Ico a b, lam = ((b - a : ℕ) : ℝ) * lam := by
    rw [sum_const, hcard, nsmul_eq_mul]
  rw [← h_const]
  exact sum_le_sum fun m hm => hstep m (mem_Ico.mp hm).1 (mem_Ico.mp hm).2

/-- Number of points in an interval where variation is at most `2δ`. -/
lemma card_Icc_le_of_d_sub_le_gen (d : ℕ → ℝ) (s_min : ℝ) (hs_pos : 0 < s_min)
    (a b : ℕ) (hab : a ≤ b)
    (hstep : ∀ m, a ≤ m → m < b → s_min ≤ d (m + 1) - d m)
    (δ : ℝ) (hsub : d b - d a ≤ 2 * δ) :
    ((Finset.Icc a b).card : ℝ) ≤ 2 * δ / s_min + 1 := by
  have hge := d_sub_ge_mul_diff_gen d s_min a b hab hstep
  have hba : ((b - a : ℕ) : ℝ) * s_min ≤ 2 * δ := hge.trans hsub
  have hba_le : ((b - a : ℕ) : ℝ) ≤ 2 * δ / s_min := by
    rwa [le_div_iff₀ hs_pos]
  have hcard_eq : (Finset.Icc a b).card = (b - a) + 1 := by
    rw [Nat.card_Icc]
    omega
  rw [hcard_eq]
  push_cast
  linarith

/-- Bounding each fiber in the phase partition. -/
lemma norm_sum_exp_fiber_gen_le (F : ℕ → ℝ) (d : ℕ → ℝ) (hd : ∀ n, d n = F (n + 1) - F n)
    (a b : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ_half : δ < 1 / 2)
    (s_min : ℝ) (hs_pos : 0 < s_min)
    (hstep : ∀ n, a ≤ n → n < b → s_min ≤ d (n + 1) - d n)
    (k : ℤ) (tag : Fin 3) :
    let s := (Finset.Ioc a b).filter (fun n => vdc_class (d n) δ = (k, tag))
    ‖∑ n ∈ s, Complex.exp (2 * Real.pi * Complex.I * ((F n : ℝ) : ℂ))‖ ≤
      2 * δ / s_min + 1 / δ + 1 := by
  intro s
  have h_mono : ∀ x y, a ≤ x → x ≤ y → y ≤ b → d x ≤ d y := by
    intro x y hx hxy hy
    obtain ⟨l, rfl⟩ := Nat.le.dest hxy
    clear hxy
    induction l with
    | zero => rfl
    | succ l ih =>
      have h1 : a ≤ x + l := by omega
      have h2 : x + l < b := by omega
      have hs := hstep (x + l) h1 h2
      have : d (x + l) ≤ d (x + l + 1) := by linarith
      have : x + (l + 1) = x + l + 1 := by omega
      rw [this]
      exact le_trans (ih (by omega)) (by linarith)
  have h_exp_shift : ∀ n ∈ s,
      Complex.exp (2 * Real.pi * Complex.I * ((F n : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (((F n + (k : ℝ) * (n : ℝ)) : ℝ) : ℂ)) := by
    intro n _
    rw [exp_phase_shift (F n) k n]
  rw [sum_congr rfl h_exp_shift]
  by_cases hs : s.Nonempty
  · have hconv := vdc_class_convex k tag δ hδ hδ_half
    have ⟨a', b', ha', hab', hb', heq⟩ :=
      filter_Ioc_eq_Icc_of_convex_mono_on d a b h_mono
        (fun x => vdc_class x δ = (k, tag)) hconv hs
    have hs_eq : s = Finset.Icc a' b' := heq
    rw [hs_eq]
    set H := fun n => F n + (k : ℝ) * (n : ℝ)
    have h_diff_eq : ∀ n, H (n + 1) - H n = d n + (k : ℝ) := by
      intro n
      simp only [H, hd n]
      push_cast
      ring
    have h_diff_mono : ∀ n, a' ≤ n → n + 1 < b' → H (n + 1) - H n ≤ H (n + 2) - H (n + 1) := by
      intro n hn hnb
      rw [h_diff_eq n, h_diff_eq (n + 1)]
      have hna : a ≤ n := by omega
      have hnbb : n < b := by omega
      have := hstep n hna hnbb
      linarith
    fin_cases tag
    · have h_norm_le : ‖∑ m ∈ Finset.Icc a' b', Complex.exp (2 * Real.pi * Complex.I * ((H m : ℝ) : ℂ))‖ ≤
          ((Finset.Icc a' b').card : ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have : ∀ m ∈ Finset.Icc a' b', ‖Complex.exp (2 * Real.pi * Complex.I * ((H m : ℝ) : ℂ))‖ = 1 :=
          fun m _ => norm_exp_two_pi_I_mul (H m)
        rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_one]
      have ha_in : a' ∈ s := by rw [hs_eq]; exact mem_Icc.mpr ⟨le_rfl, hab'⟩
      have hb_in : b' ∈ s := by rw [hs_eq]; exact mem_Icc.mpr ⟨hab', le_rfl⟩
      have ha_class := (Finset.mem_filter.mp ha_in).2
      have hb_class := (Finset.mem_filter.mp hb_in).2
      have ha_0 := (vdc_class_zero_iff (d a') δ hδ_half k).mp ha_class
      have hb_0 := (vdc_class_zero_iff (d b') δ hδ_half k).mp hb_class
      have hsub : d b' - d a' ≤ 2 * δ := by linarith [ha_0.1, hb_0.2]
      have hstep_inner : ∀ m, a' ≤ m → m < b' → s_min ≤ d (m + 1) - d m := by
        intro m hm1 hm2
        exact hstep m (by omega) (by omega)
      have hcard := card_Icc_le_of_d_sub_le_gen d s_min hs_pos a' b' hab' hstep_inner δ hsub
      have h_card_trans := h_norm_le.trans hcard
      have : 2 * δ / s_min + 1 ≤ 2 * δ / s_min + 1 / δ + 1 := by
        have : 0 ≤ 1 / δ := by positivity
        linarith
      exact h_card_trans.trans this
    · have hKL := norm_sum_exp_le_of_monotone_diff H a' b' hab' δ hδ
      have hneg : ∀ n, a' ≤ n → n < b' → H (n + 1) - H n < 0 := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_1 := (vdc_class_one_iff (d n) δ hδ k).mp hn_class
        linarith [hn_1.2]
      have hlow : ∀ n, a' ≤ n → n < b' → δ ≤ |H (n + 1) - H n| := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_1 := (vdc_class_one_iff (d n) δ hδ k).mp hn_class
        have : d n + (k : ℝ) < 0 := by linarith [hn_1.2]
        rw [abs_of_neg this]
        linarith [hn_1.2]
      have hhalf : ∀ n, a' ≤ n → n < b' → |H (n + 1) - H n| ≤ 1 / 2 := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_1 := (vdc_class_one_iff (d n) δ hδ k).mp hn_class
        have : d n + (k : ℝ) < 0 := by linarith [hn_1.2]
        rw [abs_of_neg this]
        linarith [hn_1.1]
      have hKL_bound := hKL hneg h_diff_mono hlow hhalf
      have : 1 / δ + 1 ≤ 2 * δ / s_min + 1 / δ + 1 := by
        have : 0 ≤ 2 * δ / s_min := by positivity
        linarith
      exact hKL_bound.trans this
    · have hKL_pos := norm_sum_exp_le_of_monotone_diff_pos H a' b' hab' δ hδ
      have hpos : ∀ n, a' ≤ n → n < b' → 0 < H (n + 1) - H n := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_2 := (vdc_class_two_iff (d n) δ hδ k).mp hn_class
        linarith [hn_2.1]
      have hlow : ∀ n, a' ≤ n → n < b' → δ ≤ H (n + 1) - H n := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_2 := (vdc_class_two_iff (d n) δ hδ k).mp hn_class
        linarith [hn_2.1]
      have hhalf : ∀ n, a' ≤ n → n < b' → H (n + 1) - H n ≤ 1 / 2 := by
        intro n hn hnb
        rw [h_diff_eq n]
        have hn_in : n ∈ s := by
          rw [hs_eq]
          exact mem_Icc.mpr ⟨hn, hnb.le⟩
        have hn_class := (Finset.mem_filter.mp hn_in).2
        have hn_2 := (vdc_class_two_iff (d n) δ hδ k).mp hn_class
        linarith [hn_2.2]
      have hKL_bound := hKL_pos hpos h_diff_mono hlow hhalf
      have : 1 / δ + 1 ≤ 2 * δ / s_min + 1 / δ + 1 := by
        have : 0 ≤ 2 * δ / s_min := by positivity
        linarith
      exact hKL_bound.trans this
  · have : s = ∅ := not_nonempty_iff_eq_empty.mp hs
    rw [this, sum_empty, norm_zero]
    have : 0 ≤ 2 * δ / s_min + 1 / δ + 1 := by positivity
    linarith

/-- Integer interval cardinality bound when `a ≤ b`. -/
lemma card_Icc_int_le_of_le (a b : ℤ) (h : a ≤ b) :
    ((Finset.Icc a b).card : ℝ) ≤ (b : ℝ) - (a : ℝ) + 1 := by
  rw [Int.card_Icc]
  have hpos : 0 ≤ b + 1 - a := by omega
  have : ((b + 1 - a).toNat : ℤ) = b + 1 - a := Int.toNat_of_nonneg hpos
  have hcast : ((b + 1 - a).toNat : ℝ) = (b + 1 - a : ℤ) := by exact_mod_cast this
  rw [hcast]
  push_cast
  ring_nf
  rfl

/-- Bounding difference of floors. -/
lemma floor_sub_floor_le (x y : ℝ) :
    ((⌊x⌋ : ℤ) : ℝ) - ((⌊y⌋ : ℤ) : ℝ) ≤ x - y + 1 := by
  have h1 : ((⌊x⌋ : ℤ) : ℝ) ≤ x := Int.floor_le x
  have h2 : y - 1 < ((⌊y⌋ : ℤ) : ℝ) := Int.sub_one_lt_floor y
  linarith

/-- Algebraic reduction for the medium-phase regime. -/
lemma vdc_medium_algebra (N : ℝ) (hN : 0 ≤ N) (lam : ℝ) (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    (α : ℝ) (hα : 1 ≤ α) (s_min δ : ℝ) (hs : s_min = lam / α) (hd : δ = Real.sqrt lam / 4) :
    3 * (N * lam + 2) * (2 * δ / s_min + 1 / δ + 1) ≤
      (40 * (α + 1)) * (N * Real.sqrt lam + 1 / Real.sqrt lam) := by
  rw [hs, hd]
  have hsqrt_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam_pos
  have hsqrt_lt1 : Real.sqrt lam < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hlam_pos.le hlam_lt
  have hlam_eq : lam = Real.sqrt lam * Real.sqrt lam := (Real.mul_self_sqrt hlam_pos.le).symm
  have hlam_le_sqrt : lam ≤ Real.sqrt lam := by
    calc lam = Real.sqrt lam * Real.sqrt lam := hlam_eq
      _ ≤ Real.sqrt lam * 1 := mul_le_mul_of_nonneg_left hsqrt_lt1.le hsqrt_pos.le
      _ = Real.sqrt lam := mul_one _
  have h1_le_inv_sqrt : 1 ≤ 1 / Real.sqrt lam := by
    rw [le_div_iff₀ hsqrt_pos]
    linarith
  have hα_gt0 : 0 < α := by linarith
  have hS_ne : Real.sqrt lam ≠ 0 := hsqrt_pos.ne'
  have hα_ne : α ≠ 0 := hα_gt0.ne'
  have h_term1 : 2 * (Real.sqrt lam / 4) / (lam / α) = (α / 2) / Real.sqrt lam := by
    nth_rw 2 [hlam_eq]
    field_simp
    ring
  have h_term2 : 1 / (Real.sqrt lam / 4) = 4 / Real.sqrt lam := by
    field_simp
  have h_sum_tags : 3 * (2 * (Real.sqrt lam / 4) / (lam / α) + 1 / (Real.sqrt lam / 4) + 1) =
      (3 * α / 2 + 12) / Real.sqrt lam + 3 := by
    rw [h_term1, h_term2]
    ring
  have h_rearr : 3 * (N * lam + 2) * (2 * (Real.sqrt lam / 4) / (lam / α) + 1 / (Real.sqrt lam / 4) + 1) =
      (N * lam + 2) * (3 * (2 * (Real.sqrt lam / 4) / (lam / α) + 1 / (Real.sqrt lam / 4) + 1)) := by ring
  rw [h_rearr, h_sum_tags]
  have h_expand : (N * lam + 2) * ((3 * α / 2 + 12) / Real.sqrt lam + 3) =
      (3 * α / 2 + 12) * N * (lam / Real.sqrt lam) + 3 * N * lam + (3 * α + 24) / Real.sqrt lam + 6 := by
    have : (N * lam + 2) * ((3 * α / 2 + 12) / Real.sqrt lam + 3) =
        N * lam * ((3 * α / 2 + 12) / Real.sqrt lam) + N * lam * 3 + 2 * ((3 * α / 2 + 12) / Real.sqrt lam) + 2 * 3 := by ring
    rw [this]
    have : N * lam * ((3 * α / 2 + 12) / Real.sqrt lam) = (3 * α / 2 + 12) * N * (lam / Real.sqrt lam) := by ring
    have : 2 * ((3 * α / 2 + 12) / Real.sqrt lam) = (3 * α + 24) / Real.sqrt lam := by ring
    linarith
  rw [h_expand]
  have h_lam_div : lam / Real.sqrt lam = Real.sqrt lam := by
    rw [div_eq_iff hsqrt_pos.ne']
    exact hlam_eq
  rw [h_lam_div]
  have h1 : 3 * N * lam ≤ 3 * N * Real.sqrt lam := by
    nlinarith
  have h2 : (6 : ℝ) ≤ 6 / Real.sqrt lam := by
    calc (6 : ℝ) = 6 * 1 := by ring
      _ ≤ 6 * (1 / Real.sqrt lam) := mul_le_mul_of_nonneg_left h1_le_inv_sqrt (by norm_num)
      _ = 6 / Real.sqrt lam := by ring
  have h3 : (3 * α / 2 + 12) * N * Real.sqrt lam + 3 * N * Real.sqrt lam = (3 * α / 2 + 15) * N * Real.sqrt lam := by ring
  have h4 : (3 * α + 24) / Real.sqrt lam + 6 / Real.sqrt lam = (3 * α + 30) / Real.sqrt lam := by ring
  have h5 : (3 * α / 2 + 15) * N * Real.sqrt lam ≤ (3 * α + 30) * N * Real.sqrt lam := by
    have : 3 * α / 2 + 15 ≤ 3 * α + 30 := by linarith
    have : 0 ≤ N * Real.sqrt lam := mul_nonneg hN hsqrt_pos.le
    nlinarith
  have h6 : (3 * α + 30) * N * Real.sqrt lam + (3 * α + 30) / Real.sqrt lam = (3 * α + 30) * (N * Real.sqrt lam + 1 / Real.sqrt lam) := by ring
  have h7 : (3 * α + 30) * (N * Real.sqrt lam + 1 / Real.sqrt lam) ≤
      (40 * (α + 1)) * (N * Real.sqrt lam + 1 / Real.sqrt lam) := by
    have h_coef : 3 * α + 30 ≤ 40 * (α + 1) := by linarith
    have h_nonneg : 0 ≤ N * Real.sqrt lam + 1 / Real.sqrt lam := by positivity
    exact mul_le_mul_of_nonneg_right h_coef h_nonneg
  linarith

/-- Bound `α(m)` by `α(K₀)` for `m ≤ K₀`. -/
lemma alpha_le_alpha_max (m K₀ : ℕ) (hm : m ≤ K₀) :
    (m + 4 : ℝ) ^ (m + 2) ≤ (K₀ + 4 : ℝ) ^ (K₀ + 2) := by
  have h1 : (1 : ℝ) ≤ (m + 4 : ℝ) := by
    have : (1 : ℝ) ≤ 4 := by norm_num
    linarith
  have h2 : m + 2 ≤ K₀ + 2 := by omega
  have hstep1 := pow_le_pow_right₀ h1 h2
  have h3 : 0 ≤ (m + 4 : ℝ) := by linarith
  have h4 : (m + 4 : ℝ) ≤ (K₀ + 4 : ℝ) := by
    have : (m : ℝ) ≤ (K₀ : ℝ) := by exact_mod_cast hm
    linarith
  have hstep2 := pow_le_pow_left₀ h3 h4 (K₀ + 2)
  exact hstep1.trans hstep2

/--
The discrete second-derivative test (Graham–Kolesnik, Theorem 2.2) for the differenced phases,
uniformly in the depth `m ≤ K₀`.
-/
theorem norm_vdc_S_le_second (K₀ : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (m : ℕ) (h : Fin m → ℕ) (N a b : ℕ),
    0 < t → m ≤ K₀ → (∀ i, 1 ≤ h i) → (∀ i, h i ≤ N) → 2 ≤ N → N ≤ a → a ≤ b → b ≤ 2 * N →
    ‖vdc_S t m h a b‖ ≤ C * ((N : ℝ) * Real.sqrt (vdcLam t m h N 2) + 1 / Real.sqrt (vdcLam t m h N 2)) := by
  set α₀ := (K₀ + 4 : ℝ) ^ (K₀ + 2)
  use 40 * (α₀ + 1)
  have hα₀_pos : 0 < α₀ := by
    have : 0 < (K₀ + 4 : ℝ) := by positivity
    exact pow_pos this _
  refine ⟨by positivity, ?_⟩
  intro t m h N a b ht hm hpos hh hN hna hab hnb
  set lam := vdcLam t m h N 2
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hlam_pos : 0 < lam := by
    dsimp [vdcLam, lam]
    have ht_div : 0 < t / (2 * Real.pi) := by positivity
    have hprod_pos : 0 < ∏ i, (h i : ℝ) := prod_h_pos m h hpos
    positivity
  have hsqrt_lam_pos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam_pos
  by_cases hlam_ge : 1 ≤ lam
  · have hcard := norm_vdc_S_le_card t m h a b
    have hba : (b - a : ℕ) ≤ N := by omega
    have h_norm_le_N : ‖vdc_S t m h a b‖ ≤ (N : ℝ) := by
      refine hcard.trans ?_
      exact_mod_cast hba
    have h1_le_sqrt : 1 ≤ Real.sqrt lam := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt hlam_ge
    have hN_le : (N : ℝ) ≤ (N : ℝ) * Real.sqrt lam := by
      calc (N : ℝ) = (N : ℝ) * 1 := by ring
        _ ≤ (N : ℝ) * Real.sqrt lam := mul_le_mul_of_nonneg_left h1_le_sqrt hN_pos.le
    have h_sum_pos : (N : ℝ) * Real.sqrt lam ≤ (N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam := by
      have : 0 ≤ 1 / Real.sqrt lam := by positivity
      linarith
    have h_bracket_pos : 0 ≤ (N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam := by positivity
    have hC_ge : 1 ≤ 40 * (α₀ + 1) := by
      have : 0 ≤ α₀ := hα₀_pos.le
      linarith
    calc ‖vdc_S t m h a b‖ ≤ (N : ℝ) := h_norm_le_N
      _ ≤ (N : ℝ) * Real.sqrt lam := hN_le
      _ ≤ (N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam := h_sum_pos
      _ = 1 * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) := by ring
      _ ≤ (40 * (α₀ + 1)) * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) :=
        mul_le_mul_of_nonneg_right hC_ge h_bracket_pos
  · have hlam_lt : lam < 1 := lt_of_not_ge hlam_ge
    by_cases hab_eq : a = b
    · subst hab_eq
      dsimp [vdc_S]
      rw [Finset.Ioc_self, Finset.sum_empty, norm_zero]
      have : 0 ≤ (N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam := by positivity
      positivity
    · have hab_lt : a < b := lt_of_le_of_ne hab hab_eq
      have ha1_le_b : a + 1 ≤ b := by omega
      set F := vdc_F t m h
      set d := vdc_d2 t m h
      have hd : ∀ n, d n = F (n + 1) - F n := fun _ => rfl
      set α := (m + 4 : ℝ) ^ (m + 2)
      have hα_ge1 : 1 ≤ α := by
        have : (1 : ℝ) ≤ (m + 4 : ℝ) := by
          have : (1 : ℝ) ≤ 4 := by norm_num
          linarith
        have hstep := pow_le_pow_right₀ this (by omega : 0 ≤ m + 2)
        rw [pow_zero] at hstep
        exact hstep
      have hα_pos : 0 < α := by linarith
      set s_min := lam / α
      have hs_min_pos : 0 < s_min := div_pos hlam_pos hα_pos
      have hstep_bounds : ∀ n, a ≤ n → n < b → s_min ≤ d (n + 1) - d n ∧ d (n + 1) - d n ≤ lam := by
        intro n hn_ge_a hnb'
        have hn_ge_N : N ≤ n := le_trans hna hn_ge_a
        have hn_le_2N : n ≤ 2 * N := by omega
        have hbounds := vdc_d2_diff_bounds t ht.le m h hpos N (by omega) hh n hn_ge_N hn_le_2N
        have hdiff_pos := vdc_d2_diff_pos t ht m h hpos n (by omega)
        rw [abs_of_pos hdiff_pos] at hbounds
        exact hbounds
      have hstep_ge : ∀ n, a ≤ n → n < b → s_min ≤ d (n + 1) - d n :=
        fun n hna' hnb' => (hstep_bounds n hna' hnb').1
      have hstep_le : ∀ n, a + 1 ≤ n → n < b → d (n + 1) - d n ≤ lam :=
        fun n hna' hnb' => (hstep_bounds n (by omega) hnb').2
      have hd_mono : ∀ x y, a ≤ x → x ≤ y → y ≤ b → d x ≤ d y := by
        intro x y hx hxy hy
        obtain ⟨l, rfl⟩ := Nat.le.dest hxy
        clear hxy
        induction l with
        | zero => rfl
        | succ l ih =>
          have h1 : a ≤ x + l := by omega
          have h2 : x + l < b := by omega
          have hs := hstep_ge (x + l) h1 h2
          have : d (x + l) ≤ d (x + l + 1) := by linarith
          have : x + (l + 1) = x + l + 1 := by omega
          rw [this]
          exact le_trans (ih (by omega)) (by linarith)
      set δ := Real.sqrt lam / 4
      have hδ_pos : 0 < δ := by positivity
      have hδ_half : δ < 1 / 2 := by
        have : Real.sqrt lam < 1 := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_lt_sqrt hlam_pos.le hlam_lt
        dsimp [δ]
        linarith
      set k_min := ⌊- d b + 1 / 2⌋
      set k_max := ⌊- d (a + 1) + 1 / 2⌋
      have hk_le : k_min ≤ k_max := by
        have h_d_le := hd_mono (a + 1) b (by omega) ha1_le_b le_rfl
        have : - d b + 1 / 2 ≤ - d (a + 1) + 1 / 2 := by linarith
        exact Int.floor_le_floor this
      have h_maps : ∀ n ∈ Finset.Ioc a b, (vdc_k (d n), vdc_tag (d n) δ) ∈ (Finset.Icc k_min k_max) ×ˢ (Finset.univ : Finset (Fin 3)) := by
        intro n hn
        simp only [mem_product, mem_Icc, mem_univ, and_true]
        have hna1 : a + 1 ≤ n := (mem_Ioc.mp hn).1
        have hnb_le : n ≤ b := (mem_Ioc.mp hn).2
        have h1 : d (a + 1) ≤ d n := hd_mono (a + 1) n (by omega) hna1 (by omega)
        have h2 : d n ≤ d b := hd_mono n b (by omega) hnb_le le_rfl
        dsimp [vdc_k]
        constructor
        · apply Int.floor_le_floor; linarith
        · apply Int.floor_le_floor; linarith
      set T : Finset (ℤ × Fin 3) := (Finset.Icc k_min k_max) ×ˢ (Finset.univ : Finset (Fin 3))
      have h_fiber := Finset.sum_fiberwise_of_maps_to h_maps (fun n => Complex.exp (2 * Real.pi * Complex.I * ((F n : ℝ) : ℂ)))
      have h_norm_eq : ‖vdc_S t m h a b‖ = ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * Complex.I * ((F n : ℝ) : ℂ))‖ :=
        norm_vdc_S_eq_norm_sum_exp_F t m h a b
      have h_tri : ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * Complex.I * ((F n : ℝ) : ℂ))‖ ≤
          ∑ j ∈ T, ‖∑ n ∈ Finset.Ioc a b with (vdc_k (d n), vdc_tag (d n) δ) = j,
            Complex.exp (2 * Real.pi * Complex.I * ((F n : ℝ) : ℂ))‖ := by
        rw [← h_fiber]
        exact norm_sum_le _ _
      have h_term_bound : ∀ j ∈ T,
          ‖∑ n ∈ Finset.Ioc a b with (vdc_k (d n), vdc_tag (d n) δ) = j,
            Complex.exp (2 * Real.pi * Complex.I * ((F n : ℝ) : ℂ))‖ ≤
          2 * δ / s_min + 1 / δ + 1 := by
        intro j _
        rcases j with ⟨k, tag⟩
        exact norm_sum_exp_fiber_gen_le F d hd a b δ hδ_pos hδ_half s_min hs_min_pos hstep_ge k tag
      have h_sum_le : (∑ j ∈ T, ‖∑ n ∈ Finset.Ioc a b with (vdc_k (d n), vdc_tag (d n) δ) = j,
            Complex.exp (2 * Real.pi * Complex.I * ((F n : ℝ) : ℂ))‖) ≤
          (T.card : ℝ) * (2 * δ / s_min + 1 / δ + 1) := by
        have h_const : ∑ j ∈ T, (2 * δ / s_min + 1 / δ + 1) = (T.card : ℝ) * (2 * δ / s_min + 1 / δ + 1) := by
          simp only [sum_const, nsmul_eq_mul]
        rw [← h_const]
        exact sum_le_sum h_term_bound
      have h_card_T : (T.card : ℝ) = ((Finset.Icc k_min k_max).card : ℝ) * 3 := by
        have : T.card = (Finset.Icc k_min k_max).card * (Finset.univ : Finset (Fin 3)).card := card_product _ _
        rw [this]
        have h_univ : (Finset.univ : Finset (Fin 3)).card = 3 := Fintype.card_fin 3
        rw [h_univ]
        push_cast
        ring
      have h_card_Icc := card_Icc_int_le_of_le k_min k_max hk_le
      have h_floor_diff := floor_sub_floor_le (- d (a + 1) + 1 / 2) (- d b + 1 / 2)
      have h_d_diff := d_sub_le_mul_diff_gen d lam (a + 1) b ha1_le_b hstep_le
      have h_b_sub_a : (b - (a + 1) : ℕ) ≤ N := by omega
      have h_d_bound : d b - d (a + 1) ≤ (N : ℝ) * lam := by
        calc d b - d (a + 1) ≤ ((b - (a + 1) : ℕ) : ℝ) * lam := h_d_diff
          _ ≤ (N : ℝ) * lam := by
            have : ((b - (a + 1) : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h_b_sub_a
            exact mul_le_mul_of_nonneg_right this hlam_pos.le
      have h_k_max_sub : (k_max : ℝ) - (k_min : ℝ) ≤ (N : ℝ) * lam + 1 := by
        linarith [h_floor_diff, h_d_bound]
      have h_card_le : ((Finset.Icc k_min k_max).card : ℝ) ≤ (N : ℝ) * lam + 2 := by
        linarith [h_card_Icc, h_k_max_sub]
      have h_card_T_le : (T.card : ℝ) ≤ 3 * ((N : ℝ) * lam + 2) := by
        rw [h_card_T]
        linarith [h_card_le]
      have h_bracket_nonneg : 0 ≤ 2 * δ / s_min + 1 / δ + 1 := by positivity
      have h_mult_le : (T.card : ℝ) * (2 * δ / s_min + 1 / δ + 1) ≤
          3 * ((N : ℝ) * lam + 2) * (2 * δ / s_min + 1 / δ + 1) :=
        mul_le_mul_of_nonneg_right h_card_T_le h_bracket_nonneg
      have h_algebra := vdc_medium_algebra (N : ℝ) (by positivity) lam hlam_pos hlam_lt α hα_ge1 s_min δ rfl rfl
      have hα_le := alpha_le_alpha_max m K₀ hm
      have h_sum_le_C : 40 * (α + 1) ≤ 40 * (α₀ + 1) := by
        have : α ≤ α₀ := hα_le
        linarith
      have h_RHS_nonneg : 0 ≤ (N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam := by positivity
      have h_final_mult : (40 * (α + 1)) * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) ≤
          (40 * (α₀ + 1)) * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) :=
        mul_le_mul_of_nonneg_right h_sum_le_C h_RHS_nonneg
      calc ‖vdc_S t m h a b‖ = ‖∑ n ∈ Finset.Ioc a b, Complex.exp (2 * Real.pi * Complex.I * ((F n : ℝ) : ℂ))‖ := h_norm_eq
        _ ≤ ∑ j ∈ T, ‖∑ n ∈ Finset.Ioc a b with (vdc_k (d n), vdc_tag (d n) δ) = j, Complex.exp (2 * Real.pi * Complex.I * ((F n : ℝ) : ℂ))‖ := h_tri
        _ ≤ (T.card : ℝ) * (2 * δ / s_min + 1 / δ + 1) := h_sum_le
        _ ≤ 3 * ((N : ℝ) * lam + 2) * (2 * δ / s_min + 1 / δ + 1) := h_mult_le
        _ ≤ (40 * (α + 1)) * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) := h_algebra
        _ ≤ (40 * (α₀ + 1)) * ((N : ℝ) * Real.sqrt lam + 1 / Real.sqrt lam) := h_final_mult

end Erdos1201.MR
