import Mathlib

open intervalIntegral MeasureTheory Set

/-!
# Iterated Finite Differences of the Logarithm

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module provides explicit control of iterated finite differences of the logarithm,
as needed for the van der Corput iteration applied to the phase `f(x) = -(t/2π) log x`.
-/

namespace Erdos1201.MR

/-- The m-fold iterated difference of `Real.log` with steps `h : Fin m → ℕ`, at the point `x`:
`Δ_h f (x) = ∑_{S ⊆ [m]} (-1)^{m-|S|} f(x + ∑_{i∈S} h i)`.
Defined recursively: `iterDiff 0 h x = Real.log x`,
`iterDiff (m+1) h x = iterDiff m (fun i => h i.castSucc) (x + h (Fin.last m)) - iterDiff m (fun i => h i.castSucc) x`. -/
noncomputable def logIterDiff : (m : ℕ) → (Fin m → ℕ) → ℝ → ℝ
  | 0, _, x => Real.log x
  | m + 1, h, x =>
    logIterDiff m (fun i => h i.castSucc) (x + (h (Fin.last m) : ℝ)) -
      logIterDiff m (fun i => h i.castSucc) x

/-- The integration box `∏_{i=0}^{m-1} [0, h_i]` in `Fin m → ℝ`. -/
def box (m : ℕ) (h : Fin m → ℕ) : Set (Fin m → ℝ) :=
  Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (h i)

/-- The box is compact. -/
lemma isCompact_box (m : ℕ) (h : Fin m → ℕ) : IsCompact (box m h) := by
  rw [box, pi_univ_Icc]
  exact isCompact_Icc

/-- Sum of coordinates on the non-negative box is non-negative. -/
lemma box_sum_nonneg (m : ℕ) (h : Fin m → ℕ) {u : Fin m → ℝ} (hu : u ∈ box m h) :
    0 ≤ ∑ i, u i := by
  refine Finset.sum_nonneg fun i _ => ?_
  exact hu i (mem_univ i) |>.1

/-- The volume of the box is the product of the side lengths. -/
lemma volume_box (m : ℕ) (h : Fin m → ℕ) :
    (volume (box m h)).toReal = ∏ i, (h i : ℝ) := by
  rw [box, pi_univ_Icc]
  have h_le : (0 : Fin m → ℝ) ≤ fun i => (h i : ℝ) := fun i => Nat.cast_nonneg (h i)
  have hvol := Real.volume_Icc_pi_toReal h_le
  simp only [Pi.zero_apply, sub_zero] at hvol
  exact hvol

/-- Integrating a constant `C` over `box m h` yields `(∏ i, h i) * C`. -/
lemma integral_const_box (m : ℕ) (h : Fin m → ℕ) (C : ℝ) :
    ∫ _ in box m h, C = (∏ i, (h i : ℝ)) * C := by
  rw [setIntegral_const, smul_eq_mul, measureReal_def, volume_box]

/-- The product of positive integers is strictly positive. -/
lemma prod_h_pos (m : ℕ) (h : Fin m → ℕ) (hpos : ∀ i, 1 ≤ h i) :
    0 < ∏ i, (h i : ℝ) := by
  refine Finset.prod_pos fun i _ => ?_
  have : (1 : ℝ) ≤ (h i : ℝ) := by exact_mod_cast hpos i
  linarith

/-- Constant functions are integrable on the compact box. -/
lemma integrable_const_box (m : ℕ) (h : Fin m → ℕ) (C : ℝ) :
    IntegrableOn (fun _ : Fin m → ℝ => C) (box m h) volume :=
  continuousOn_const.integrableOn_compact (isCompact_box m h)

/-- Pointwise bound: sum of coordinates on the box is at most sum of upper bounds. -/
lemma sum_u_le_sum_h (m : ℕ) (h : Fin m → ℕ) {u : Fin m → ℝ} (hu : u ∈ box m h) :
    ∑ i, u i ≤ ∑ i, (h i : ℝ) := by
  refine Finset.sum_le_sum fun i _ => ?_
  exact hu i (mem_univ i) |>.2

/-- If all `h i ≤ N`, then `∑ i, h i ≤ m * N`. -/
lemma sum_h_le_m_mul_N (m : ℕ) (h : Fin m → ℕ) (N : ℕ) (hh : ∀ i, h i ≤ N) :
    ∑ i, (h i : ℝ) ≤ (m : ℝ) * (N : ℝ) := by
  have : ∑ i, (h i : ℝ) ≤ ∑ i : Fin m, (N : ℝ) := by
    refine Finset.sum_le_sum fun i _ => ?_
    exact_mod_cast hh i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  exact this

/-- Integrability of the signed integrand on `box m h`. -/
lemma integrable_box_integrand (m : ℕ) (h : Fin m → ℕ) (y : ℝ) (hy : 0 < y) :
    IntegrableOn (fun v => (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) / (y + ∑ j, v j) ^ m)
      (box m h) volume := by
  have hcomp : IsCompact (box m h) := isCompact_box m h
  have hcont : ContinuousOn (fun v => (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) / (y + ∑ j, v j) ^ m)
      (box m h) := by
    refine continuousOn_const.div ?_ ?_
    · refine (continuousOn_const.add ?_).pow m
      refine continuous_finsetSum Finset.univ (fun j _ => ?_) |>.continuousOn
      exact continuous_apply j
    · intro v hv
      have hv_nonneg : 0 ≤ ∑ j, v j := by
        refine Finset.sum_nonneg fun j _ => ?_
        rw [box, pi_univ_Icc] at hv
        exact hv.1 j
      have : 0 < y + ∑ j, v j := by linarith
      exact (pow_pos this m).ne'
  exact hcont.integrableOn_compact hcomp

/-- Integrability of the positive integrand on `box m h`. -/
lemma integrable_box_integrand_pos (m : ℕ) (h : Fin m → ℕ) (y : ℝ) (hy : 0 < y) :
    IntegrableOn (fun (u : Fin m → ℝ) => ((m - 1).factorial : ℝ) / (y + ∑ j, u j) ^ m)
      (box m h) volume := by
  have h_eq : (fun (u : Fin m → ℝ) => ((m - 1).factorial : ℝ) / (y + ∑ j, u j) ^ m) =
      fun (u : Fin m → ℝ) => (-1 : ℝ) ^ (m - 1) * ((-1 : ℝ) ^ (m - 1) * (m - 1).factorial / (y + ∑ j, u j) ^ m) := by
    ext u
    have h1 : (-1 : ℝ) ^ (m - 1) * ((-1 : ℝ) ^ (m - 1) * (m - 1).factorial / (y + ∑ j, u j) ^ m) =
        ((-1 : ℝ) ^ (m - 1) * (-1 : ℝ) ^ (m - 1)) * ((m - 1).factorial / (y + ∑ j, u j) ^ m) := by ring
    rw [h1, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
  rw [h_eq]
  exact (integrable_box_integrand m h y hy).const_mul _

/-- Integrability of the step integrand on `[0, b] × box m h_init`. -/
lemma integrable_step (m : ℕ) (x : ℝ) (hx : 0 < x) (b : ℝ) (_hb : 0 ≤ b) (h_init : Fin m → ℕ) :
    IntegrableOn (fun (p : ℝ × (Fin m → ℝ)) =>
      (-1 : ℝ) ^ m * (m.factorial : ℝ) / (x + p.1 + ∑ j, p.2 j) ^ (m + 1))
      (Icc 0 b ×ˢ box m h_init) volume := by
  have hcomp : IsCompact (Icc 0 b ×ˢ box m h_init) :=
    isCompact_Icc.prod (isCompact_box m h_init)
  have hcont : ContinuousOn (fun (p : ℝ × (Fin m → ℝ)) =>
      (-1 : ℝ) ^ m * (m.factorial : ℝ) / (x + p.1 + ∑ j, p.2 j) ^ (m + 1))
      (Icc 0 b ×ˢ box m h_init) := by
    refine continuousOn_const.div ?_ ?_
    · refine ((continuousOn_const.add continuous_fst.continuousOn).add ?_).pow (m + 1)
      refine continuous_finsetSum Finset.univ (fun j _ => ?_) |>.continuousOn
      exact continuous_apply j |>.comp continuous_snd
    · rintro ⟨t, v⟩ ⟨ht, hv⟩
      have ht_nonneg : 0 ≤ t := ht.1
      have hv_nonneg : 0 ≤ ∑ j, v j := by
        refine Finset.sum_nonneg fun j _ => ?_
        rw [box, pi_univ_Icc] at hv
        exact hv.1 j
      have : 0 < x + t + ∑ j, v j := by linarith
      exact (pow_pos this (m + 1)).ne'
  exact hcont.integrableOn_compact hcomp

/-- Fubini swap on the product domain `[0, b] × box m h_init`. -/
lemma fst_snd_integral_eq (m : ℕ) (x : ℝ) (hx : 0 < x) (b : ℝ) (hb : 0 ≤ b) (h_init : Fin m → ℕ) :
    ∫ p in (Icc 0 b ×ˢ box m h_init),
      (-1 : ℝ) ^ m * (m.factorial : ℝ) / (x + p.1 + ∑ j, p.2 j) ^ (m + 1) =
    ∫ v in box m h_init, ∫ t in Icc 0 b,
      (-1 : ℝ) ^ m * (m.factorial : ℝ) / (x + t + ∑ j, v j) ^ (m + 1) := by
  have hint := integrable_step m x hx b hb h_init
  rw [Measure.volume_eq_prod] at hint ⊢
  have hprod := setIntegral_prod
    (fun p : ℝ × (Fin m → ℝ) => (-1 : ℝ) ^ m * (m.factorial : ℝ) / (x + p.1 + ∑ j, p.2 j) ^ (m + 1))
    hint
  rw [hprod]
  have h_int_uncurry : Integrable (Function.uncurry fun (t : ℝ) (v : Fin m → ℝ) =>
      (-1 : ℝ) ^ m * (m.factorial : ℝ) / (x + t + ∑ j, v j) ^ (m + 1))
      ((volume.restrict (Icc 0 b)).prod (volume.restrict (box m h_init))) := by
    rw [Measure.prod_restrict]
    exact hint
  exact integral_integral_swap (μ := volume.restrict (Icc 0 b)) (ν := volume.restrict (box m h_init)) h_int_uncurry

/-- Derivative of `1 / s^m` is `-m / s^{m+1}`. -/
theorem hasDerivAt_pow_inv (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s => (1 : ℝ) / s ^ m) (-m / x ^ (m + 1)) x := by
  have hd_pow : HasDerivAt (fun s : ℝ => s ^ m) (m * x ^ (m - 1)) x := by
    have hd_id : HasDerivAt (fun s : ℝ => s) 1 x := hasDerivAt_id x
    have h := hd_id.pow m
    rw [mul_one] at h
    exact h
  have h_ne : x ^ m ≠ 0 := (pow_pos hx m).ne'
  have hd_inv := hd_pow.inv h_ne
  have h_alg : -(m * x ^ (m - 1)) / (x ^ m) ^ 2 = -m / x ^ (m + 1) := by
    have h1 : (x ^ m) ^ 2 = x ^ (m + 1) * x ^ (m - 1) := by
      rw [← pow_mul]
      have : m * 2 = m + 1 + (m - 1) := by omega
      rw [this, pow_add]
    rw [h1]
    have hx_sub : x ^ (m - 1) ≠ 0 := (pow_pos hx (m - 1)).ne'
    have : -(m * x ^ (m - 1)) = (-m) * x ^ (m - 1) := by ring
    rw [this]
    exact mul_div_mul_right (-m : ℝ) (x ^ (m + 1)) hx_sub
  have h_fun : (fun s : ℝ => s ^ m)⁻¹ = fun s => 1 / s ^ m := by
    ext s; rw [Pi.inv_apply, inv_eq_one_div]
  rw [h_fun] at hd_inv
  rw [h_alg] at hd_inv
  exact hd_inv

/-- Derivative of `(-1)^{m-1} (m-1)! / (y + s)^m` is `(-1)^m m! / (y + t)^{m+1}`. -/
theorem hasDerivAt_log_diff_integrand (m : ℕ) (hm : 1 ≤ m) (y t : ℝ) (hpos : 0 < y + t) :
    HasDerivAt (fun s => (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) / (y + s) ^ m)
      ((-1 : ℝ) ^ m * (m.factorial : ℝ) / (y + t) ^ (m + 1)) t := by
  have hd_shift : HasDerivAt (fun s => (1 : ℝ) / (y + s) ^ m) (-m / (y + t) ^ (m + 1)) t := by
    have hd1 : HasDerivAt (fun s : ℝ => (1 : ℝ) / s ^ m) (-m / (y + t) ^ (m + 1)) (y + t) :=
      hasDerivAt_pow_inv m hm (y + t) hpos
    have hd2 : HasDerivAt (fun s : ℝ => y + s) 1 t := (hasDerivAt_id t).const_add y
    have hd := hd1.comp t hd2
    rw [mul_one] at hd
    exact hd
  have hd_mul := hd_shift.const_mul ((-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ))
  have h_alg : (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) * (-m / (y + t) ^ (m + 1)) =
      (-1 : ℝ) ^ m * (m.factorial : ℝ) / (y + t) ^ (m + 1) := by
    have hm_fac : ((m - 1).factorial : ℝ) * (m : ℝ) = (m.factorial : ℝ) := by
      have hnat : (m - 1).factorial * m = m.factorial := by
        have := Nat.factorial_succ (m - 1)
        have hsub : (m - 1) + 1 = m := Nat.sub_add_cancel hm
        rw [hsub] at this
        rw [mul_comm]
        exact this.symm
      rw [← Nat.cast_mul, hnat]
    have hpow : (-1 : ℝ) ^ (m - 1) * (-1) = (-1 : ℝ) ^ m := by
      have hsub : (m - 1) + 1 = m := Nat.sub_add_cancel hm
      rw [← pow_succ, hsub]
    calc (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) * (-m / (y + t) ^ (m + 1))
      _ = ((-1 : ℝ) ^ (m - 1) * (-1)) * (((m - 1).factorial : ℝ) * m) / (y + t) ^ (m + 1) := by ring
      _ = (-1 : ℝ) ^ m * (m.factorial : ℝ) / (y + t) ^ (m + 1) := by
        rw [hpow, hm_fac]
  have h_fun : (fun s => (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) * ((1 : ℝ) / (y + s) ^ m)) =
      (fun s => (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) / (y + s) ^ m) := by
    ext s; ring
  rw [← h_fun]
  rw [← h_alg]
  exact hd_mul

/-- 1D integral step evaluating `(-1)^m m! / (y + t)^{m+1}` from `0` to `b` via FTC. -/
theorem integral_log_diff_step (m : ℕ) (hm : 1 ≤ m) (y b : ℝ) (hy : 0 < y) (hb : 0 ≤ b) :
    ∫ t in (0 : ℝ)..b, (-1 : ℝ) ^ m * (m.factorial : ℝ) / (y + t) ^ (m + 1) =
      (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) / (y + b) ^ m -
      (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) / y ^ m := by
  have h_deriv : ∀ t ∈ uIcc 0 b,
      HasDerivAt (fun s => (-1 : ℝ) ^ (m - 1) * ((m - 1).factorial : ℝ) / (y + s) ^ m)
        ((-1 : ℝ) ^ m * (m.factorial : ℝ) / (y + t) ^ (m + 1)) t := by
    intro t ht
    rw [uIcc_of_le hb] at ht
    have hpos : 0 < y + t := by linarith [ht.1]
    exact hasDerivAt_log_diff_integrand m hm y t hpos
  have h_cont : ContinuousOn (fun t => (-1 : ℝ) ^ m * (m.factorial : ℝ) / (y + t) ^ (m + 1)) (uIcc 0 b) := by
    rw [uIcc_of_le hb]
    refine continuousOn_const.div ?_ ?_
    · exact (continuousOn_const.add continuousOn_id).pow (m + 1)
    · intro t ht
      have : 0 < y + t := by linarith [ht.1]
      exact (pow_pos this (m + 1)).ne'
  have h_int : IntervalIntegrable (fun t => (-1 : ℝ) ^ m * (m.factorial : ℝ) / (y + t) ^ (m + 1)) volume 0 b :=
    h_cont.intervalIntegrable
  have h_ftc := integral_eq_sub_of_hasDerivAt h_deriv h_int
  rw [h_ftc]
  ring_nf

/-- Base case 1D integral: `∫_0^b 1 / (y + t) dt = log (y + b) - log y`. -/
theorem integral_inv_x_add_t (y b : ℝ) (hy : 0 < y) (hb : 0 ≤ b) :
    ∫ t in (0 : ℝ)..b, (1 : ℝ) / (y + t) = Real.log (y + b) - Real.log y := by
  have h_deriv : ∀ t ∈ uIcc 0 b, HasDerivAt (fun s => Real.log (y + s)) (1 / (y + t)) t := by
    intro t ht
    rw [uIcc_of_le hb] at ht
    have hpos : 0 < y + t := by linarith [ht.1]
    have hd1 : HasDerivAt (fun s => y + s) 1 t := by
      simpa using (hasDerivAt_id t).const_add y
    have hd2 := HasDerivAt.log hd1 hpos.ne'
    simpa using hd2
  have h_cont : ContinuousOn (fun t => (1 : ℝ) / (y + t)) (uIcc 0 b) := by
    rw [uIcc_of_le hb]
    refine continuousOn_const.div ?_ ?_
    · exact continuousOn_const.add continuousOn_id
    · intro t ht; linarith [ht.1]
  have h_int : IntervalIntegrable (fun t => (1 : ℝ) / (y + t)) volume 0 b :=
    h_cont.intervalIntegrable
  have h_ftc := integral_eq_sub_of_hasDerivAt h_deriv h_int
  rw [h_ftc]
  ring_nf

/-- Preimage of `box (n + 1) h` under `piFinSuccAbove.symm` decomposes as `[0, h_last] × box n h_init`. -/
theorem preimage_piFinSuccAbove_box (n : ℕ) (h : Fin (n + 1) → ℝ) :
    let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm
    e ⁻¹' (Icc 0 h) = Icc 0 (h (Fin.last n)) ×ˢ Icc 0 (fun j => h j.castSucc) := by
  intro e
  have he_iso : (e : ℝ × (Fin n → ℝ) → (Fin (n + 1) → ℝ)) =
      (Fin.insertNthOrderIso (fun _ => ℝ) (Fin.last n)) := rfl
  change (Fin.insertNthOrderIso (fun _ => ℝ) (Fin.last n)) ⁻¹' (Icc 0 h) = _
  rw [OrderIso.preimage_Icc, Icc_prod_eq]
  have hsymm (f : Fin (n + 1) → ℝ) :
      (Fin.insertNthOrderIso (fun _ => ℝ) (Fin.last n)).symm f =
        (f (Fin.last n), fun j => f j.castSucc) := by
    ext
    · change ((Fin.insertNthOrderIso (fun _ => ℝ) (Fin.last n)).toEquiv.symm f).1 = _
      rw [Fin.insertNthOrderIso_toEquiv, Fin.insertNthEquiv_symm_apply]
    · change ((Fin.insertNthOrderIso (fun _ => ℝ) (Fin.last n)).toEquiv.symm f).2 _ = _
      rw [Fin.insertNthOrderIso_toEquiv, Fin.insertNthEquiv_symm_apply]
      dsimp [Fin.removeNth]
      rw [Fin.succAbove_last]
  rw [hsymm 0, hsymm h]
  rfl

/-- Sum of coordinates splits as `t + ∑ j, v j` under `piFinSuccAbove.symm`. -/
theorem sum_piFinSuccAbove (n : ℕ) (t : ℝ) (v : Fin n → ℝ) :
    let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm
    ∑ i, e (t, v) i = t + ∑ j, v j := by
  intro e
  change ∑ i, (Fin.insertNth (Fin.last n) t v : Fin (n + 1) → ℝ) i = t + ∑ j, v j
  rw [Fin.sum_univ_castSucc]
  rw [@Fin.insertNth_apply_same n (fun _ => ℝ) (Fin.last n) t v]
  have hcast (j : Fin n) : (Fin.insertNth (Fin.last n) t v : Fin (n + 1) → ℝ) j.castSucc = v j := by
    have : j.castSucc = (Fin.last n).succAbove j := by rw [Fin.succAbove_last]
    rw [this]
    exact @Fin.insertNth_apply_succAbove n (fun _ => ℝ) (Fin.last n) t v j
  simp_rw [hcast]
  ring

/-- Integral representation: Δ_h log (x) = ∫_{[0,h₀]}⋯∫_{[0,h_{m-1}]} log^{(m)}(x + u₀ + ⋯ + u_{m-1}) du,
where log^{(m)}(y) = (-1)^{m-1} (m-1)! / y^m for m ≥ 1. -/
theorem logIterDiff_eq_integral (m : ℕ) (hm : 1 ≤ m) (h : Fin m → ℕ) (x : ℝ) (hx : 0 < x) :
    logIterDiff m h x = ∫ u in (Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (h i)),
      (-1 : ℝ) ^ (m - 1) * (m - 1).factorial / (x + ∑ i, u i) ^ m := by
  have hne : m ≠ 0 := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
  clear hm hne
  induction k generalizing x with
  | zero =>
    have h_simp : (fun u : Fin 1 → ℝ => (-1 : ℝ) ^ (1 - 1) * (1 - 1).factorial / (x + ∑ i, u i) ^ 1) =
        fun u => 1 / (x + u 0) := by
      ext u
      simp only [Nat.sub_self, pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, pow_one,
        Fin.sum_univ_one]
    rw [h_simp]
    set e := (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
    have hem : MeasurePreserving e :=
      (volume_preserving_funUnique (Fin 1) ℝ).symm _
    have hpre : e ⁻¹' (Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (h i)) = Set.Icc 0 (h 0 : ℝ) := by
      rw [pi_univ_Icc]
      have := (OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc (0 : Fin 1 → ℝ) (fun i => (h i : ℝ))
      exact this
    rw [← hem.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)]
    rw [hpre]
    have h_eval (t : ℝ) : e t 0 = t := rfl
    simp_rw [h_eval]
    rw [integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (Nat.cast_nonneg (h 0))]
    dsimp [logIterDiff]
    exact (integral_inv_x_add_t x (h 0 : ℝ) hx (Nat.cast_nonneg (h 0))).symm
  | succ k ih =>
    let n := k + 1
    have hn : 1 ≤ n := by omega
    set h_init := fun i : Fin n => h i.castSucc
    set b := (h (Fin.last n) : ℝ)
    have hb : 0 ≤ b := Nat.cast_nonneg _
    have hxb : 0 < x + b := by linarith
    have ih_xb := ih (x + b) hxb h_init
    have ih_x := ih x hx h_init
    set e := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm
    have hem : MeasurePreserving e :=
      (volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last n)).symm _
    have hpre : e ⁻¹' (box (n + 1) h) = Icc 0 b ×ˢ box n h_init := by
      rw [box, box, pi_univ_Icc, pi_univ_Icc]
      exact preimage_piFinSuccAbove_box n (fun i => (h i : ℝ))
    have hsum (p : ℝ × (Fin n → ℝ)) : ∑ i, e p i = p.1 + ∑ j, p.2 j :=
      sum_piFinSuccAbove n p.1 p.2
    have h_sub_n : (n + 1) - 1 = n := rfl
    change logIterDiff (n + 1) h x = ∫ u in box (n + 1) h, _
    rw [h_sub_n]
    rw [← hem.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)]
    rw [hpre]
    have h_sum_rewrite : (∫ p in Icc 0 b ×ˢ box n h_init,
        (-1 : ℝ) ^ n * (n.factorial : ℝ) / (x + ∑ i, e p i) ^ (n + 1)) =
        ∫ p in Icc 0 b ×ˢ box n h_init,
          (-1 : ℝ) ^ n * (n.factorial : ℝ) / (x + p.1 + ∑ j, p.2 j) ^ (n + 1) := by
      refine setIntegral_congr_fun (measurableSet_Icc.prod (isCompact_box n h_init).measurableSet) ?_
      intro p _
      dsimp only
      rw [hsum p]
      congr 2
      ring
    rw [h_sum_rewrite]
    rw [fst_snd_integral_eq n x hx b hb h_init]
    have h_inner (v : Fin n → ℝ) (hv : v ∈ box n h_init) :
        ∫ t in Icc 0 b, (-1 : ℝ) ^ n * (n.factorial : ℝ) / (x + t + ∑ j, v j) ^ (n + 1) =
          (-1 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) / ((x + b) + ∑ j, v j) ^ n -
          (-1 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) / (x + ∑ j, v j) ^ n := by
      have hv_nonneg : 0 ≤ ∑ j, v j := box_sum_nonneg n h_init hv
      have hy : 0 < x + ∑ j, v j := by linarith
      have hstep := integral_log_diff_step n hn (x + ∑ j, v j) b hy hb
      have h_rearr (t : ℝ) : x + t + ∑ j, v j = x + ∑ j, v j + t := by ring
      simp_rw [h_rearr]
      rw [integral_Icc_eq_integral_Ioc]
      rw [← intervalIntegral.integral_of_le hb]
      rw [hstep]
    have h_congr : (∫ v in box n h_init, ∫ t in Icc 0 b,
        (-1 : ℝ) ^ n * (n.factorial : ℝ) / (x + t + ∑ j, v j) ^ (n + 1)) =
        ∫ v in box n h_init,
          ((-1 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) / ((x + b) + ∑ j, v j) ^ n -
           (-1 : ℝ) ^ (n - 1) * ((n - 1).factorial : ℝ) / (x + ∑ j, v j) ^ n) := by
      refine setIntegral_congr_fun (isCompact_box n h_init).measurableSet ?_
      intro v hv
      exact h_inner v hv
    rw [h_congr]
    rw [integral_sub (integrable_box_integrand n h_init (x + b) hxb)
                     (integrable_box_integrand n h_init x hx)]
    change logIterDiff (n + 1) h x = _
    dsimp [logIterDiff]
    rw [ih_xb, ih_x]
    rfl

/-- One more difference in the base point is the (m+1)-fold difference with the extra step k. -/
theorem logIterDiff_succ_eq (m : ℕ) (h : Fin m → ℕ) (k : ℕ) (x : ℝ) :
    logIterDiff m h (x + k) - logIterDiff m h x = logIterDiff (m + 1) (Fin.snoc h k) x := by
  dsimp [logIterDiff]
  rw [Fin.snoc_last]
  congr 2 <;> {
    ext i
    rw [Fin.snoc_castSucc]
  }

/-- Expressing `(-1)^{m-1} Δ_h log(x)` as a strictly positive integral. -/
lemma sign_mul_logIterDiff_eq (m : ℕ) (hm : 1 ≤ m) (h : Fin m → ℕ) (x : ℝ) (hx : 0 < x) :
    (-1 : ℝ) ^ (m - 1) * logIterDiff m h x =
      ∫ u in (Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (h i)),
        ((m - 1).factorial : ℝ) / (x + ∑ i, u i) ^ m := by
  rw [logIterDiff_eq_integral m hm h x hx]
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun (isCompact_box m h).measurableSet ?_
  intro u _
  dsimp only
  have h1 : (-1 : ℝ) ^ (m - 1) * ((-1 : ℝ) ^ (m - 1) * (m - 1).factorial / (x + ∑ i, u i) ^ m) =
      ((-1 : ℝ) ^ (m - 1) * (-1 : ℝ) ^ (m - 1)) * ((m - 1).factorial / (x + ∑ i, u i) ^ m) := by ring
  rw [h1, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/-- Strict positivity of `(-1)^{m-1} Δ_h log(x)`. -/
theorem sign_logIterDiff (m : ℕ) (hm : 1 ≤ m) (h : Fin m → ℕ) (hpos : ∀ i, 1 ≤ h i) (x : ℝ) (hx : 0 < x) :
    0 < (-1 : ℝ) ^ (m - 1) * logIterDiff m h x := by
  rw [sign_mul_logIterDiff_eq m hm h x hx]
  have h_int_pos : 0 < (∏ i, (h i : ℝ)) * (((m - 1).factorial : ℝ) / (x + ∑ i, (h i : ℝ)) ^ m) := by
    refine mul_pos (prod_h_pos m h hpos) ?_
    refine div_pos (by positivity) ?_
    refine pow_pos ?_ m
    have : 0 ≤ ∑ i, (h i : ℝ) := Finset.sum_nonneg fun i _ => Nat.cast_nonneg (h i)
    linarith
  have h_le : (∏ i, (h i : ℝ)) * (((m - 1).factorial : ℝ) / (x + ∑ i, (h i : ℝ)) ^ m) ≤
      ∫ u in (Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (h i)),
        ((m - 1).factorial : ℝ) / (x + ∑ i, u i) ^ m := by
    rw [← integral_const_box]
    refine setIntegral_mono_on (integrable_const_box m h _) (integrable_box_integrand_pos m h x hx) (isCompact_box m h).measurableSet ?_
    intro u hu
    have hu_le : ∑ i, u i ≤ ∑ i, (h i : ℝ) := sum_u_le_sum_h m h hu
    have hu_nonneg : 0 ≤ ∑ i, u i := box_sum_nonneg m h hu
    have h_pos : 0 < x + ∑ i, u i := by linarith
    refine div_le_div_of_nonneg_left (by positivity) (pow_pos h_pos m) ?_
    refine pow_le_pow_left₀ (by linarith) (by linarith) m
  linarith

/-- Monotonicity in x: (-1)^{m-1} Δ_h log(x) is antitone in x on (0, ∞) (as the integrand (m-1)!/(x+…)^m is). -/
theorem antitone_sign_mul_logIterDiff (m : ℕ) (hm : 1 ≤ m) (h : Fin m → ℕ) (_hpos : ∀ i, 1 ≤ h i) :
    AntitoneOn (fun x : ℝ => (-1 : ℝ) ^ (m - 1) * logIterDiff m h x) (Set.Ioi 0) := by
  intro x1 hx1 x2 hx2 hle
  have hx1_pos : 0 < x1 := hx1
  have hx2_pos : 0 < x2 := hx2
  dsimp only
  rw [sign_mul_logIterDiff_eq m hm h x1 hx1_pos]
  rw [sign_mul_logIterDiff_eq m hm h x2 hx2_pos]
  have h_int1 := integrable_box_integrand_pos m h x1 hx1_pos
  have h_int2 := integrable_box_integrand_pos m h x2 hx2_pos
  refine setIntegral_mono_on h_int2 h_int1 (isCompact_box m h).measurableSet ?_
  intro u hu
  have hu_nonneg : 0 ≤ ∑ i, u i := box_sum_nonneg m h hu
  have h1 : 0 < x1 + ∑ i, u i := by linarith
  have h2 : x1 + ∑ i, u i ≤ x2 + ∑ i, u i := by linarith
  refine div_le_div_of_nonneg_left (by positivity) (pow_pos h1 m) ?_
  exact pow_le_pow_left₀ (by linarith) h2 m

/-- Absolute value equals the sign-multiplied difference when sign-multiplied difference is positive. -/
lemma abs_sign_mul (m : ℕ) (A : ℝ) (hA : 0 < (-1 : ℝ) ^ (m - 1) * A) :
    |A| = (-1 : ℝ) ^ (m - 1) * A := by
  have h1 : |(-1 : ℝ) ^ (m - 1) * A| = (-1 : ℝ) ^ (m - 1) * A := abs_of_pos hA
  have h2 : |(-1 : ℝ) ^ (m - 1) * A| = |(-1 : ℝ) ^ (m - 1)| * |A| := abs_mul _ _
  have h3 : |(-1 : ℝ) ^ (m - 1)| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  rw [h3, one_mul] at h2
  rw [← h1, h2]

/-- Sign and size: for x ≥ N ≥ 1 and all h i ≤ N, (-1)^{m-1} Δ_h log(x) is positive and
(m-1)! ∏ h i / ((m+2)N)^m ≤ |Δ_h log(x)| ≤ (m-1)! ∏ h i / N^m, when x ≤ 2N. -/
theorem abs_logIterDiff_bounds (m : ℕ) (hm : 1 ≤ m) (h : Fin m → ℕ) (hpos : ∀ i, 1 ≤ h i)
    (N : ℕ) (hN : 1 ≤ N) (hh : ∀ i, h i ≤ N) (x : ℝ) (hx : (N : ℝ) ≤ x) (hx2 : x ≤ 2 * N) :
    ((m - 1).factorial : ℝ) * (∏ i, (h i : ℝ)) / ((m + 2) * N) ^ m ≤ |logIterDiff m h x| ∧
    |logIterDiff m h x| ≤ ((m - 1).factorial : ℝ) * (∏ i, (h i : ℝ)) / (N : ℝ) ^ m := by
  have hN_pos : 0 < (N : ℝ) := by positivity
  have hx_pos : 0 < x := by linarith
  have h_sign := sign_logIterDiff m hm h hpos x hx_pos
  have h_abs : |logIterDiff m h x| = (-1 : ℝ) ^ (m - 1) * logIterDiff m h x :=
    abs_sign_mul m (logIterDiff m h x) h_sign
  rw [h_abs, sign_mul_logIterDiff_eq m hm h x hx_pos]
  have h_int := integrable_box_integrand_pos m h x hx_pos
  constructor
  · -- Lower bound
    have h_lower : (∏ i, (h i : ℝ)) * (((m - 1).factorial : ℝ) / ((m + 2 : ℝ) * N) ^ m) ≤
        ∫ u in (Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (h i)),
          ((m - 1).factorial : ℝ) / (x + ∑ i, u i) ^ m := by
      rw [← integral_const_box]
      refine setIntegral_mono_on (integrable_const_box m h _) h_int (isCompact_box m h).measurableSet ?_
      intro u hu
      have hu_le : ∑ i, u i ≤ (m : ℝ) * (N : ℝ) :=
        (sum_u_le_sum_h m h hu).trans (sum_h_le_m_mul_N m h N hh)
      have h_sum_le : x + ∑ i, u i ≤ (m + 2 : ℝ) * (N : ℝ) := by
        calc x + ∑ i, u i ≤ 2 * (N : ℝ) + (m : ℝ) * (N : ℝ) := by linarith
        _ = (m + 2 : ℝ) * (N : ℝ) := by ring
      have h_pos : 0 < x + ∑ i, u i := by linarith [box_sum_nonneg m h hu]
      refine div_le_div_of_nonneg_left (by positivity) (pow_pos h_pos m) ?_
      exact pow_le_pow_left₀ (by linarith) h_sum_le m
    have : ((m - 1).factorial : ℝ) * (∏ i, (h i : ℝ)) / ((m + 2) * N) ^ m =
        (∏ i, (h i : ℝ)) * (((m - 1).factorial : ℝ) / ((m + 2 : ℝ) * N) ^ m) := by ring
    rw [this]
    exact h_lower
  · -- Upper bound
    have h_upper : (∫ u in (Set.pi Set.univ fun i => Set.Icc (0 : ℝ) (h i)),
          ((m - 1).factorial : ℝ) / (x + ∑ i, u i) ^ m) ≤
        (∏ i, (h i : ℝ)) * (((m - 1).factorial : ℝ) / (N : ℝ) ^ m) := by
      rw [← integral_const_box]
      refine setIntegral_mono_on h_int (integrable_const_box m h _) (isCompact_box m h).measurableSet ?_
      intro u hu
      have hu_nonneg : 0 ≤ ∑ i, u i := box_sum_nonneg m h hu
      have h_le : (N : ℝ) ≤ x + ∑ i, u i := by linarith
      refine div_le_div_of_nonneg_left (by positivity) (pow_pos hN_pos m) ?_
      exact pow_le_pow_left₀ (by positivity) h_le m
    have : ((m - 1).factorial : ℝ) * (∏ i, (h i : ℝ)) / (N : ℝ) ^ m =
        (∏ i, (h i : ℝ)) * (((m - 1).factorial : ℝ) / (N : ℝ) ^ m) := by ring
    rw [this]
    exact h_upper

end Erdos1201.MR
