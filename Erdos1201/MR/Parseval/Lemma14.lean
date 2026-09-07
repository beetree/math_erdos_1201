import Mathlib
import Erdos1201.MR.Parseval.SaffariVaughan
import Erdos1201.MR.Parseval.WindowTransform
import Erdos1201.MR.Parseval.WindowKernel
import Erdos1201.MR.Parseval.HighFrequency
import Erdos1201.MR.Parseval.LowFrequency
import Erdos1201.MR.Parseval.WindowEnergy
import Erdos1201.MR.Analysis.DirichletPolyBasics

/-!
# Lemma 14 (Parseval bound) of Matomäki–Radziwiłł

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

Stage 1: the Saffari–Vaughan averaging identity for the short sums, written with the
multiplicative window function `windowFun`.
-/

namespace Erdos1201.MR

open MeasureTheory intervalIntegral Real Set Measure
open scoped FourierTransform ComplexInnerProductSpace

/-- A short sum over `(z, z(1+u)]` is `z` times the multiplicative window at `log z`. -/
lemma windowSum_eq_mul_windowFun (a : ℕ → ℂ) (N : Finset ℕ) (hsupp : ∀ n, n ∉ N → a n = 0)
    (z u : ℝ) (hz : 0 < z) :
    windowSum a z (z * (1 + u)) = (z : ℂ) * windowFun a N u (Real.log z) := by
  unfold windowSum windowFun
  rw [Real.exp_log hz, Real.exp_neg, Real.exp_log hz]
  have hz' : (z : ℂ) ≠ 0 := by exact_mod_cast hz.ne'
  have hR : ∀ n : ℕ, n ∈ (Finset.Ioc 0 ⌊z * (1 + u)⌋₊).filter (fun n : ℕ => z < n) ↔
      (z < n ∧ (n : ℝ) ≤ z * (1 + u)) := by
    intro n
    rw [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h3, ?_⟩
      have hpos : 0 < ⌊z * (1 + u)⌋₊ := lt_of_lt_of_le h1 h2
      have h1le : (1 : ℝ) ≤ z * (1 + u) := Nat.floor_pos.mp hpos
      exact (Nat.le_floor_iff (by linarith)).mp h2
    · rintro ⟨h1, h2⟩
      have hn : 0 < n := by
        have : (0 : ℝ) < n := lt_trans hz h1
        exact_mod_cast this
      exact ⟨⟨hn, Nat.le_floor h2⟩, h1⟩
  set R := (Finset.Ioc 0 ⌊z * (1 + u)⌋₊).filter (fun n : ℕ => z < n) with hRdef
  have hcond : ∀ n : ℕ, (z < n ∧ (n : ℝ) ≤ z * (1 + u)) ↔ n ∈ R := fun n => (hR n).symm
  -- both sides equal the sum over `R ∪ N` of the conditional terms
  have hL : ∑ n ∈ R, a n = ∑ n ∈ R ∪ N, if z < n ∧ (n : ℝ) ≤ z * (1 + u) then a n else 0 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext n
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · intro hn
        exact ⟨Or.inl hn, (hcond n).mpr hn⟩
      · rintro ⟨_, hn⟩
        exact (hcond n).mp hn
    · intros; rfl
  have hRn : (∑ n ∈ N, if z < n ∧ (n : ℝ) ≤ z * (1 + u) then a n else 0) =
      ∑ n ∈ R ∪ N, if z < n ∧ (n : ℝ) ≤ z * (1 + u) then a n else 0 := by
    apply Finset.sum_subset Finset.subset_union_right
    intro n _ hnN
    rw [hsupp n hnN]
    simp
  rw [hL, ← hRn]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ hz', one_mul]

/-- Saffari–Vaughan: the short sum equals the average of longer windows minus the average of
windows starting at `x + h`. -/
lemma windowSum_eq_integral_sub (a : ℕ → ℂ) (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    windowSum a x (x + h) = (1 / (2 * h : ℂ)) *
      ((∫ w in h..(3 * h), windowSum a x (x + w)) - ∫ w in h..(3 * h), windowSum a (x + h) (x + w)) := by
  have hconst : ∫ w in h..(3 * h), (windowSum a x (x + w) - windowSum a (x + h) (x + w)) =
      ∫ _w in h..(3 * h), windowSum a x (x + h) := by
    apply intervalIntegral.integral_congr
    intro w hw
    rw [Set.uIcc_of_le (by linarith)] at hw
    exact (windowSum_add_split a x h w hx hh hw.1).symm
  rw [← intervalIntegral.integral_sub (intervalIntegrable_windowSum_add a x x h hh.le)
    (intervalIntegrable_windowSum_add a (x + h) x h hh.le), hconst, intervalIntegral.integral_const]
  have h2 : (2 * h : ℂ) ≠ 0 := by
    have : (2 * h : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  rw [Complex.real_smul]
  push_cast
  field_simp
  try ring

/-- The first Saffari–Vaughan integral after the substitution `w = x u`. -/
lemma integral_windowSum_first (a : ℕ → ℂ) (x h : ℝ) (hx : 0 < x) :
    ∫ w in h..(3 * h), windowSum a x (x + w) =
      (x : ℂ) * ∫ u in (h / x)..(3 * h / x), windowSum a x (x * (1 + u)) := by
  have hx' : x ≠ 0 := hx.ne'
  have := intervalIntegral.integral_comp_mul_left (fun w => windowSum a x (x + w)) hx'
    (a := h / x) (b := 3 * h / x)
  have e1 : x * (h / x) = h := by field_simp
  have e2 : x * (3 * h / x) = 3 * h := by field_simp
  rw [e1, e2] at this
  have hfun : (fun u => windowSum a x (x * (1 + u))) = fun u => windowSum a x (x + x * u) := by
    funext u; ring_nf
  rw [hfun, this, Complex.real_smul, ← mul_assoc]
  have : (x : ℂ) * ((x⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast hx')
  rw [this, one_mul]

/-- The second Saffari–Vaughan integral after the substitution `w = h + (x + h) u`. -/
lemma integral_windowSum_second (a : ℕ → ℂ) (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    ∫ w in h..(3 * h), windowSum a (x + h) (x + w) =
      ((x + h : ℝ) : ℂ) * ∫ u in (0 : ℝ)..(2 * h / (x + h)), windowSum a (x + h) ((x + h) * (1 + u)) := by
  have hxh : x + h ≠ 0 := by positivity
  have := intervalIntegral.integral_comp_mul_add (fun w => windowSum a (x + h) (x + w)) hxh h
    (a := (0 : ℝ)) (b := 2 * h / (x + h))
  have e1 : (x + h) * 0 + h = h := by ring
  have e2 : (x + h) * (2 * h / (x + h)) + h = 3 * h := by field_simp; ring
  rw [e1, e2] at this
  have hfun : (fun u => windowSum a (x + h) ((x + h) * (1 + u))) =
      fun u => windowSum a (x + h) (x + ((x + h) * u + h)) := by
    funext u; ring_nf
  rw [hfun, this, Complex.real_smul, ← mul_assoc]
  have : ((x + h : ℝ) : ℂ) * (((x + h)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast hxh)
  rw [this, one_mul]

/-- The Saffari–Vaughan identity in terms of the multiplicative window function. -/
theorem windowSum_div_eq (a : ℕ → ℂ) (N : Finset ℕ) (hsupp : ∀ n, n ∉ N → a n = 0)
    (x h : ℝ) (hx : 0 < x) (hh : 0 < h) :
    windowSum a x (x + h) / (h : ℂ) =
      ((x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) * (∫ u in (h / x)..(3 * h / x), windowFun a N u (Real.log x)) -
      (((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) *
        (∫ u in (0 : ℝ)..(2 * h / (x + h)), windowFun a N u (Real.log (x + h))) := by
  rw [windowSum_eq_integral_sub a x h hx hh, integral_windowSum_first a x h hx,
    integral_windowSum_second a x h hx hh]
  have hxh : 0 < x + h := by linarith
  have e1 : (fun u => windowSum a x (x * (1 + u))) = fun u => (x : ℂ) * windowFun a N u (Real.log x) := by
    funext u; exact windowSum_eq_mul_windowFun a N hsupp x u hx
  have e2 : (fun u => windowSum a (x + h) ((x + h) * (1 + u))) =
      fun u => ((x + h : ℝ) : ℂ) * windowFun a N u (Real.log (x + h)) := by
    funext u; exact windowSum_eq_mul_windowFun a N hsupp (x + h) u hxh
  rw [e1, e2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  field_simp
  try ring

/-! ### Stage 3: the low-frequency part -/

lemma one_add_mul_I_ne_zero (t : ℝ) : (1 : ℂ) + (t : ℂ) * Complex.I ≠ 0 :=
  norm_pos_iff.mp (norm_one_add_mul_I_pos t)

/-- `lowPart` is continuous in the window parameter `u ∈ [0, 1]`. -/
lemma continuousOn_lowPart_param (a : ℕ → ℂ) (N : Finset ℕ) (T₀ y : ℝ) (hN : ∀ n ∈ N, 0 < n) :
    ContinuousOn (fun u : ℝ => lowPart a N u T₀ y) (Set.Icc 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hA := continuous_dirichletPoly_one_line a N hN
  let f : Set.Icc (0 : ℝ) 1 → ℝ → ℂ := fun u t =>
    dirichletPoly a N ((1 : ℂ) + t * Complex.I) * windowKernel u t * Complex.exp (t * y * Complex.I)
  have hf : Continuous f.uncurry := by
    have h1 : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
        dirichletPoly a N ((1 : ℂ) + (p.2 : ℂ) * Complex.I) := hA.comp continuous_snd
    have h2 : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
        Complex.exp ((p.2 : ℂ) * (y : ℂ) * Complex.I) := by fun_prop
    have hbase : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ => (1 + ((p.1 : ℝ) : ℂ)) := by fun_prop
    have hexp : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ => ((1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
      fun_prop
    have hpow : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ =>
        (1 + ((p.1 : ℝ) : ℂ)) ^ ((1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
      refine hbase.cpow hexp (fun p => ?_)
      have : (1 + ((p.1 : ℝ) : ℂ)) = ((1 + (p.1 : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [p.1.2.1])
    have hker : Continuous fun p : Set.Icc (0 : ℝ) 1 × ℝ => windowKernel (p.1 : ℝ) p.2 := by
      unfold windowKernel
      exact (hpow.sub continuous_const).div hexp (fun p => one_add_mul_I_ne_zero p.2)
    exact (h1.mul hker).mul h2
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hf (-T₀) T₀
  exact continuous_const.mul hcont

lemma windowKernel_zero (t : ℝ) : windowKernel 0 t = 0 := by
  unfold windowKernel
  simp

lemma lowPart_zero (a : ℕ → ℂ) (N : Finset ℕ) (T₀ y : ℝ) : lowPart a N 0 T₀ y = 0 := by
  unfold lowPart
  simp [windowKernel_zero]

lemma intervalIntegrable_lowPart_param (a : ℕ → ℂ) (N : Finset ℕ) (T₀ y : ℝ)
    (hN : ∀ n ∈ N, 0 < n) (c d : ℝ) (hc : 0 ≤ c) (hd : d ≤ 1) (hcd : c ≤ d) :
    IntervalIntegrable (fun u : ℝ => lowPart a N u T₀ y) volume c d :=
  ((continuousOn_lowPart_param a N T₀ y hN).mono (Set.Icc_subset_Icc hc hd)).intervalIntegrable_of_Icc hcd

/-- `windowFun` is measurable in the window parameter. -/
lemma measurable_windowFun_param (a : ℕ → ℂ) (N : Finset ℕ) (y : ℝ) :
    Measurable (fun u : ℝ => windowFun a N u y) := by
  unfold windowFun
  refine Measurable.const_mul ?_ _
  refine Finset.measurable_sum _ (fun n _ => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  have : {u : ℝ | Real.exp y < n ∧ (n : ℝ) ≤ Real.exp y * (1 + u)} =
      {u : ℝ | Real.exp y < n} ∩ {u : ℝ | (n : ℝ) ≤ Real.exp y * (1 + u)} := by
    ext u; simp
  rw [this]
  exact (MeasurableSet.const _).inter (measurableSet_le measurable_const (by fun_prop))

lemma norm_windowFun_le (a : ℕ → ℂ) (N : Finset ℕ) (u y : ℝ) :
    ‖windowFun a N u y‖ ≤ Real.exp (-y) * ∑ n ∈ N, ‖a n‖ := by
  unfold windowFun
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  split_ifs <;> simp

lemma intervalIntegrable_windowFun_param (a : ℕ → ℂ) (N : Finset ℕ) (y c d : ℝ) :
    IntervalIntegrable (fun u : ℝ => windowFun a N u y) volume c d :=
  intervalIntegrable_of_bounded_complex (measurable_windowFun_param a N y)
    (by positivity : 0 ≤ Real.exp (-y) * ∑ n ∈ N, ‖a n‖) (fun u _ => norm_windowFun_le a N u y)

/-- The low-frequency part of the averaged short sum. -/
noncomputable def lowAvg (a : ℕ → ℂ) (N : Finset ℕ) (T₀ x h : ℝ) : ℂ :=
  ((x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) * (∫ u in (h / x)..(3 * h / x), lowPart a N u T₀ (Real.log x)) -
    (((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) *
      (∫ u in (0 : ℝ)..(2 * h / (x + h)), lowPart a N u T₀ (Real.log (x + h)))

/-- The high-frequency part of the averaged short sum. -/
noncomputable def highAvg (a : ℕ → ℂ) (N : Finset ℕ) (T₀ x h : ℝ) : ℂ :=
  ((x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) *
      (∫ u in (h / x)..(3 * h / x), (windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x))) -
    (((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) *
      (∫ u in (0 : ℝ)..(2 * h / (x + h)),
        (windowFun a N u (Real.log (x + h)) - lowPart a N u T₀ (Real.log (x + h))))

theorem windowSum_div_eq_lowAvg_add_highAvg (a : ℕ → ℂ) (N : Finset ℕ)
    (hsupp : ∀ n, n ∉ N → a n = 0) (hN : ∀ n ∈ N, 0 < n) (T₀ x h : ℝ) (hx : 0 < x) (hh : 0 < h)
    (hhx : 3 * h ≤ x) :
    windowSum a x (x + h) / (h : ℂ) = lowAvg a N T₀ x h + highAvg a N T₀ x h := by
  rw [windowSum_div_eq a N hsupp x h hx hh]
  unfold lowAvg highAvg
  have hxh : 0 < x + h := by linarith
  have hc1 : 0 ≤ h / x := by positivity
  have hd1 : 3 * h / x ≤ 1 := by rw [div_le_one hx]; exact hhx
  have hcd1 : h / x ≤ 3 * h / x := by
    apply div_le_div_of_nonneg_right _ hx.le; linarith
  have hd2 : 2 * h / (x + h) ≤ 1 := by rw [div_le_one hxh]; linarith
  have hcd2 : (0 : ℝ) ≤ 2 * h / (x + h) := by positivity
  rw [intervalIntegral.integral_sub (intervalIntegrable_windowFun_param a N _ _ _)
      (intervalIntegrable_lowPart_param a N T₀ _ hN _ _ hc1 hd1 hcd1),
    intervalIntegral.integral_sub (intervalIntegrable_windowFun_param a N _ _ _)
      (intervalIntegrable_lowPart_param a N T₀ _ hN _ _ le_rfl hd2 hcd2)]
  ring

/-! ### Stage 3b: pointwise bound for the low-frequency part -/

/-- The normalised low parts vary little in `u` and `y`. -/
lemma norm_lowPart_sub_mul_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ y y₀ u u₀ : ℝ)
    (hu : 0 < u) (hu' : u ≤ 1 / 2) (hu₀ : 0 < u₀) (hu₀' : u₀ ≤ 1 / 2) (hT₀ : 0 < T₀)
    (hN : ∀ n ∈ N, 0 < n) :
    ‖lowPart a N u T₀ y - (u : ℂ) * (lowPart a N u₀ T₀ y₀ / u₀)‖ ≤
      u * ((8 * T₀ * (1 + T₀) / Real.pi) * (u + u₀) + (2 * T₀ ^ 2 / Real.pi) * |y - y₀|) *
        ∑ n ∈ N, ‖a n‖ / n := by
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have heq : lowPart a N u T₀ y - (u : ℂ) * (lowPart a N u₀ T₀ y₀ / u₀) =
      (u : ℂ) * ((lowPart a N u T₀ y / u - lowPart a N u₀ T₀ y / u₀) +
        (lowPart a N u₀ T₀ y / u₀ - lowPart a N u₀ T₀ y₀ / u₀)) := by
    field_simp
    try ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have h1 := norm_lowPart_div_sub_le a N u u₀ T₀ y hu hu' hu₀ hu₀' hT₀ hN
  have h2 := norm_lowPart_div_sub_shift_le a N u₀ T₀ y y₀ hu₀ hu₀' hT₀ hN
  have hM : 0 ≤ ∑ n ∈ N, ‖a n‖ / (n : ℝ) :=
    Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  calc u * ‖(lowPart a N u T₀ y / u - lowPart a N u₀ T₀ y / u₀) +
        (lowPart a N u₀ T₀ y / u₀ - lowPart a N u₀ T₀ y₀ / u₀)‖
      ≤ u * ((8 * T₀ * (1 + T₀) / Real.pi) * (u + u₀) * ∑ n ∈ N, ‖a n‖ / n +
          (2 * T₀ ^ 2 / Real.pi) * |y - y₀| * ∑ n ∈ N, ‖a n‖ / n) := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = _ := by ring

lemma integral_ofReal_id (c d : ℝ) : ∫ u in c..d, (u : ℂ) = (((d ^ 2 - c ^ 2) / 2 : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_ofReal, integral_id]

/-- The first low-frequency average equals `2 Φ₀` up to an explicit error. -/
lemma lowAvg_first_sub_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ x h u₀ : ℝ) (hx : 0 < x) (hh : 0 < h)
    (hhx : 6 * h ≤ x) (hu₀ : 0 < u₀) (hu₀' : u₀ ≤ 1 / 2) (hT₀ : 0 < T₀) (hN : ∀ n ∈ N, 0 < n) :
    ‖((x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) * (∫ u in (h / x)..(3 * h / x), lowPart a N u T₀ (Real.log x)) -
        2 * (lowPart a N u₀ T₀ (Real.log x) / u₀)‖ ≤
      3 * ((8 * T₀ * (1 + T₀) / Real.pi) * (3 * h / x + u₀)) * ∑ n ∈ N, ‖a n‖ / n := by
  set Φ₀ : ℂ := lowPart a N u₀ T₀ (Real.log x) / u₀ with hΦ₀
  have hc : 0 ≤ h / x := by positivity
  have hcd : h / x ≤ 3 * h / x := by apply div_le_div_of_nonneg_right _ hx.le; linarith
  have hd : 3 * h / x ≤ 1 := by rw [div_le_one hx]; linarith
  have hd' : 3 * h / x ≤ 1 / 2 := by rw [div_le_iff₀ hx]; linarith
  have hint : IntervalIntegrable (fun u : ℝ => lowPart a N u T₀ (Real.log x)) volume (h / x) (3 * h / x) :=
    intervalIntegrable_lowPart_param a N T₀ _ hN _ _ hc hd hcd
  have hint2 : IntervalIntegrable (fun u : ℝ => (u : ℂ) * Φ₀) volume (h / x) (3 * h / x) :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hsplit : (∫ u in (h / x)..(3 * h / x), lowPart a N u T₀ (Real.log x)) =
      (∫ u in (h / x)..(3 * h / x), (lowPart a N u T₀ (Real.log x) - (u : ℂ) * Φ₀)) +
        Φ₀ * (((( 3 * h / x) ^ 2 - (h / x) ^ 2) / 2 : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_sub hint hint2, intervalIntegral.integral_mul_const, integral_ofReal_id]
    ring
  have hM : 0 ≤ ∑ n ∈ N, ‖a n‖ / (n : ℝ) :=
    Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  -- the error integral
  have herr : ‖∫ u in (h / x)..(3 * h / x), (lowPart a N u T₀ (Real.log x) - (u : ℂ) * Φ₀)‖ ≤
      ((3 * h / x) * ((8 * T₀ * (1 + T₀) / Real.pi) * (3 * h / x + u₀)) * ∑ n ∈ N, ‖a n‖ / n) *
        |3 * h / x - h / x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le hcd, Set.mem_Ioc] at hu
    have hu0 : 0 < u := lt_of_le_of_lt hc hu.1
    have hb := norm_lowPart_sub_mul_le a N T₀ (Real.log x) (Real.log x) u u₀ hu0 (hu.2.trans hd') hu₀ hu₀' hT₀ hN
    rw [sub_self, abs_zero, mul_zero, add_zero] at hb
    refine hb.trans ?_
    have hpi : 0 < Real.pi := Real.pi_pos
    have hfac : 0 ≤ (8 * T₀ * (1 + T₀) / Real.pi) := by positivity
    gcongr
    · exact hu.2
    · exact hu.2
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hmain : ((x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) * (Φ₀ * (((( 3 * h / x) ^ 2 - (h / x) ^ 2) / 2 : ℝ) : ℂ)) = 2 * Φ₀ := by
    push_cast
    field_simp
    try ring
  rw [hsplit, mul_add, hmain, add_sub_cancel_right, norm_mul]
  have habs : |3 * h / x - h / x| = 2 * h / x := by
    rw [abs_of_nonneg (by linarith)]; ring
  rw [habs] at herr
  have hcoef : ‖(x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)‖ = x ^ 2 / (2 * h ^ 2) := by
    rw [norm_div, norm_pow, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx, abs_of_pos hh]
    norm_num
  rw [hcoef]
  calc x ^ 2 / (2 * h ^ 2) * ‖∫ u in (h / x)..(3 * h / x), (lowPart a N u T₀ (Real.log x) - (u : ℂ) * Φ₀)‖
      ≤ x ^ 2 / (2 * h ^ 2) * (((3 * h / x) * ((8 * T₀ * (1 + T₀) / Real.pi) * (3 * h / x + u₀)) *
          ∑ n ∈ N, ‖a n‖ / n) * (2 * h / x)) := by gcongr
    _ = 3 * ((8 * T₀ * (1 + T₀) / Real.pi) * (3 * h / x + u₀)) * ∑ n ∈ N, ‖a n‖ / n := by
        field_simp
        try ring

/-- The second low-frequency average equals `Φ₀` up to an explicit error. -/
lemma lowAvg_second_sub_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ x h u₀ : ℝ) (hx : 0 < x) (hh : 0 < h)
    (hhx : 6 * h ≤ x) (hu₀ : 0 < u₀) (hu₀' : u₀ ≤ 1 / 2) (hT₀ : 0 < T₀) (hN : ∀ n ∈ N, 0 < n) :
    ‖(((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) *
        (∫ u in (0 : ℝ)..(2 * h / (x + h)), lowPart a N u T₀ (Real.log (x + h))) -
        lowPart a N u₀ T₀ (Real.log x) / u₀‖ ≤
      2 * ((8 * T₀ * (1 + T₀) / Real.pi) * (2 * h / x + u₀) + (2 * T₀ ^ 2 / Real.pi) * (h / x)) *
        ∑ n ∈ N, ‖a n‖ / n := by
  set Φ₀ : ℂ := lowPart a N u₀ T₀ (Real.log x) / u₀ with hΦ₀
  have hxh : 0 < x + h := by linarith
  set c : ℝ := 2 * h / (x + h) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by rw [hcdef, div_le_one hxh]; linarith
  have hc2 : c ≤ 2 * h / x := by
    rw [hcdef]; apply div_le_div_of_nonneg_left (by positivity) hx; linarith
  have hchalf : c ≤ 1 / 2 := by
    have : 2 * h / x ≤ 1 / 2 := by rw [div_le_iff₀ hx]; linarith
    linarith
  have hint : IntervalIntegrable (fun u : ℝ => lowPart a N u T₀ (Real.log (x + h))) volume 0 c :=
    intervalIntegrable_lowPart_param a N T₀ _ hN _ _ le_rfl hc1 hc0
  have hint2 : IntervalIntegrable (fun u : ℝ => (u : ℂ) * Φ₀) volume 0 c :=
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  have hsplit : (∫ u in (0 : ℝ)..c, lowPart a N u T₀ (Real.log (x + h))) =
      (∫ u in (0 : ℝ)..c, (lowPart a N u T₀ (Real.log (x + h)) - (u : ℂ) * Φ₀)) +
        Φ₀ * (((c ^ 2 - 0 ^ 2) / 2 : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_sub hint hint2, intervalIntegral.integral_mul_const, integral_ofReal_id]
    ring
  have hM : 0 ≤ ∑ n ∈ N, ‖a n‖ / (n : ℝ) :=
    Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have hlog : |Real.log (x + h) - Real.log x| ≤ h / x := by
    rw [← Real.log_div hxh.ne' hx.ne']
    have hdiv : (x + h) / x = 1 + h / x := by field_simp
    rw [hdiv, abs_of_nonneg (Real.log_nonneg (by linarith [show 0 ≤ h / x by positivity]))]
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + h / x by positivity)]
  have herr : ‖∫ u in (0 : ℝ)..c, (lowPart a N u T₀ (Real.log (x + h)) - (u : ℂ) * Φ₀)‖ ≤
      (c * ((8 * T₀ * (1 + T₀) / Real.pi) * (2 * h / x + u₀) + (2 * T₀ ^ 2 / Real.pi) * (h / x)) *
        ∑ n ∈ N, ‖a n‖ / n) * |c - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le hc0, Set.mem_Ioc] at hu
    obtain ⟨hu1, hu2⟩ := hu
    have hb := norm_lowPart_sub_mul_le a N T₀ (Real.log (x + h)) (Real.log x) u u₀ hu1
      (hu2.trans hchalf) hu₀ hu₀' hT₀ hN
    refine hb.trans ?_
    have hpi : 0 < Real.pi := Real.pi_pos
    have hfac : 0 ≤ (8 * T₀ * (1 + T₀) / Real.pi) := by positivity
    have hfac2 : 0 ≤ (2 * T₀ ^ 2 / Real.pi) := by positivity
    have hinner : (8 * T₀ * (1 + T₀) / Real.pi) * (u + u₀) +
        (2 * T₀ ^ 2 / Real.pi) * |Real.log (x + h) - Real.log x| ≤
        (8 * T₀ * (1 + T₀) / Real.pi) * (2 * h / x + u₀) + (2 * T₀ ^ 2 / Real.pi) * (h / x) :=
      add_le_add (mul_le_mul_of_nonneg_left (by linarith [hu2, hc2]) hfac)
        (mul_le_mul_of_nonneg_left hlog hfac2)
    have hinner0 : 0 ≤ (8 * T₀ * (1 + T₀) / Real.pi) * (u + u₀) +
        (2 * T₀ ^ 2 / Real.pi) * |Real.log (x + h) - Real.log x| := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul hu2 hinner hinner0 hc0) hM
  have hxhC : ((x + h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hxh.ne'
  have hxhC' : (x : ℂ) + (h : ℂ) ≠ 0 := by exact_mod_cast hxh.ne'
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hmain : (((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) * (Φ₀ * (((c ^ 2 - 0 ^ 2) / 2 : ℝ) : ℂ)) = Φ₀ := by
    rw [hcdef]
    push_cast
    field_simp
    try ring
  rw [hsplit, mul_add, hmain, add_sub_cancel_right, norm_mul]
  have habs : |c - 0| = c := by rw [sub_zero, abs_of_nonneg hc0]
  rw [habs] at herr
  have hcoef : ‖((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)‖ = (x + h) ^ 2 / (2 * h ^ 2) := by
    rw [norm_div, norm_pow, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxh, abs_of_pos hh]
    norm_num
  rw [hcoef]
  calc (x + h) ^ 2 / (2 * h ^ 2) * ‖∫ u in (0 : ℝ)..c, (lowPart a N u T₀ (Real.log (x + h)) - (u : ℂ) * Φ₀)‖
      ≤ (x + h) ^ 2 / (2 * h ^ 2) * ((c * ((8 * T₀ * (1 + T₀) / Real.pi) * (2 * h / x + u₀) +
          (2 * T₀ ^ 2 / Real.pi) * (h / x)) * ∑ n ∈ N, ‖a n‖ / n) * c) := by gcongr
    _ = 2 * ((8 * T₀ * (1 + T₀) / Real.pi) * (2 * h / x + u₀) + (2 * T₀ ^ 2 / Real.pi) * (h / x)) *
        ∑ n ∈ N, ‖a n‖ / n := by
        rw [hcdef]
        field_simp
        try ring

/-! ### Stage 4a: `L²` facts for the high-frequency part -/

/-- `lowPart` is square integrable (it is the inverse Fourier transform of a compactly supported
bounded function). -/
lemma memLp_two_lowPart (a : ℕ → ℂ) (N : Finset ℕ) (u T₀ : ℝ) (hu : 0 < u) (hT₀ : 0 ≤ T₀)
    (hN : ∀ n ∈ N, 0 < n) : MemLp (fun y => lowPart a N u T₀ y) 2 volume := by
  set Φ : ℝ → ℂ := fun ξ => Real.fourierIntegral (windowFun a N u) ξ
  set s : Set ℝ := Icc (-T₀ / (2 * Real.pi)) (T₀ / (2 * Real.pi))
  set Φ₀ : ℝ → ℂ := s.indicator Φ
  have hG₁ : Integrable (windowFun a N u) := integrable_windowFun a N u hu hN
  have hℓ_eq : ∀ y, lowPart a N u T₀ y = 𝓕⁻ Φ₀ y := fun y =>
    lowPart_eq_fourierInv a N u T₀ hu hT₀ hN y
  have hΦ_cont : Continuous Φ :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hG₁
  have hsupp : HasCompactSupport Φ₀ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc support_indicator_subset
  have hmeas : AEStronglyMeasurable Φ₀ volume :=
    (hΦ_cont.stronglyMeasurable.indicator measurableSet_Icc).aestronglyMeasurable
  set C : ℝ := ∫ y, ‖windowFun a N u y‖
  have hC_nonneg : 0 ≤ C := integral_nonneg (fun y => norm_nonneg _)
  have hbound : ∀ᵐ ξ ∂volume, ‖Φ₀ ξ‖ ≤ C := by
    apply Filter.Eventually.of_forall
    intro ξ
    simp only [Φ₀, indicator_apply]
    split_ifs with hξ
    · exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) (windowFun a N u) ξ
    · rw [norm_zero]
      exact hC_nonneg
  have hΦ₀_mem (p : ENNReal) : MemLp Φ₀ p volume :=
    HasCompactSupport.memLp_of_bound hsupp hmeas C hbound
  have h_fourierInv := fourierInv_toLp_eq_fourierIntegralInv Φ₀
    (memLp_one_iff_integrable.mp (hΦ₀_mem 1)) (hΦ₀_mem 2)
  have hℓ_ae : (𝓕⁻ ((hΦ₀_mem 2).toLp Φ₀) : Lp ℂ 2 volume) =ᵐ[volume]
      fun y => lowPart a N u T₀ y := by
    filter_upwards [h_fourierInv] with y hy
    rw [hy, ← hℓ_eq y]
  exact (Lp.memLp _).ae_eq hℓ_ae

lemma memLp_two_high (a : ℕ → ℂ) (N : Finset ℕ) (u T₀ : ℝ) (hu : 0 < u) (hT₀ : 0 ≤ T₀)
    (hN : ∀ n ∈ N, 0 < n) :
    MemLp (fun y => windowFun a N u y - lowPart a N u T₀ y) 2 volume :=
  (memLp_two_windowFun a N u hu hN).sub (memLp_two_lowPart a N u T₀ hu hT₀ hN)

lemma integrable_norm_sq_high (a : ℕ → ℂ) (N : Finset ℕ) (u T₀ : ℝ) (hu : 0 < u) (hT₀ : 0 ≤ T₀)
    (hN : ∀ n ∈ N, 0 < n) :
    Integrable (fun y => ‖windowFun a N u y - lowPart a N u T₀ y‖ ^ 2) volume :=
  (memLp_two_iff_integrable_sq_norm (memLp_two_high a N u T₀ hu hT₀ hN).aestronglyMeasurable).mp
    (memLp_two_high a N u T₀ hu hT₀ hN)

/-- Change of variables `x = e^y`: for a nonnegative integrable `f`,
`∫_{(X, 2X]} f (log x) dx ≤ 2X ∫ f`. -/
lemma integral_comp_log_Ioc_le (f : ℝ → ℝ) (hf : Integrable f volume) (hf0 : ∀ y, 0 ≤ f y)
    (X X₂ : ℝ) (hX : 0 < X) (hX₂ : X ≤ X₂) :
    ∫ x in Ioc X X₂, f (Real.log x) ≤ X₂ * ∫ y, f y := by
  set s : Set ℝ := Ioc (Real.log X) (Real.log X₂) with hs
  have hX2 : 0 < X₂ := by linarith
  have himage : Real.exp '' s = Ioc X X₂ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hs, mem_Ioc] at hy
      refine ⟨?_, ?_⟩
      · calc X = Real.exp (Real.log X) := (Real.exp_log hX).symm
          _ < Real.exp y := Real.exp_lt_exp.mpr hy.1
      · calc Real.exp y ≤ Real.exp (Real.log X₂) := Real.exp_le_exp.mpr hy.2
          _ = X₂ := Real.exp_log hX2
    · intro hx
      rw [mem_Ioc] at hx
      have hx0 : 0 < x := lt_trans hX hx.1
      refine ⟨Real.log x, ?_, Real.exp_log hx0⟩
      rw [hs, mem_Ioc]
      exact ⟨Real.log_lt_log hX hx.1, Real.log_le_log hx0 hx.2⟩
  have hderiv : ∀ y ∈ s, HasDerivWithinAt Real.exp (Real.exp y) s y :=
    fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt
  have hinj : InjOn Real.exp s := Real.exp_injective.injOn
  have hcov := integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioc) hderiv hinj
    (fun x => f (Real.log x))
  rw [himage] at hcov
  rw [hcov]
  have hpt : ∀ y ∈ s, |Real.exp y| • f (Real.log (Real.exp y)) ≤ X₂ * f y := by
    intro y hy
    rw [hs, mem_Ioc] at hy
    rw [Real.log_exp, abs_of_pos (Real.exp_pos y), smul_eq_mul]
    have : Real.exp y ≤ X₂ := by
      calc Real.exp y ≤ Real.exp (Real.log X₂) := Real.exp_le_exp.mpr hy.2
        _ = X₂ := Real.exp_log hX2
    exact mul_le_mul_of_nonneg_right this (hf0 y)
  calc ∫ y in s, |Real.exp y| • f (Real.log (Real.exp y))
      ≤ ∫ y in s, X₂ * f y := by
        apply setIntegral_mono_on ?_ ?_ measurableSet_Ioc hpt
        · have hfun : (fun y => |Real.exp y| • f (Real.log (Real.exp y))) =
              fun y => Real.exp y * f y := by
            funext y
            rw [Real.log_exp, abs_of_pos (Real.exp_pos y), smul_eq_mul]
          rw [hfun]
          refine Integrable.mono' ((hf.const_mul X₂).integrableOn) ?_ ?_
          · exact (Real.continuous_exp.aestronglyMeasurable.restrict).mul
              hf.aestronglyMeasurable.restrict
          · filter_upwards [ae_restrict_mem (measurableSet_Ioc)] with y hy
            rw [mem_Ioc] at hy
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos y).le (hf0 y))]
            have : Real.exp y ≤ X₂ := by
              calc Real.exp y ≤ Real.exp (Real.log X₂) := Real.exp_le_exp.mpr hy.2
                _ = X₂ := Real.exp_log hX2
            exact mul_le_mul_of_nonneg_right this (hf0 y)
        · exact (hf.const_mul _).integrableOn
    _ = X₂ * ∫ y in s, f y := integral_const_mul _ _
    _ ≤ X₂ * ∫ y, f y :=
        mul_le_mul_of_nonneg_left (setIntegral_le_integral hf (Filter.Eventually.of_forall hf0))
          (by positivity)

/-! ### Stage 4b: joint measurability and Fubini for the high-frequency part -/

/-- Joint continuity of `lowPart` in `(u, y)` for `u ∈ [0, 1]`. -/
lemma continuous_lowPart_pair (a : ℕ → ℂ) (N : Finset ℕ) (T₀ : ℝ) (hN : ∀ n ∈ N, 0 < n) :
    Continuous (fun q : Set.Icc (0 : ℝ) 1 × ℝ => lowPart a N q.1 T₀ q.2) := by
  have hA := continuous_dirichletPoly_one_line a N hN
  let f : Set.Icc (0 : ℝ) 1 × ℝ → ℝ → ℂ := fun q t =>
    dirichletPoly a N ((1 : ℂ) + t * Complex.I) * windowKernel q.1 t * Complex.exp (t * q.2 * Complex.I)
  have hf : Continuous f.uncurry := by
    have h1 : Continuous fun p : (Set.Icc (0 : ℝ) 1 × ℝ) × ℝ =>
        dirichletPoly a N ((1 : ℂ) + (p.2 : ℂ) * Complex.I) := hA.comp continuous_snd
    have h2 : Continuous fun p : (Set.Icc (0 : ℝ) 1 × ℝ) × ℝ =>
        Complex.exp ((p.2 : ℂ) * (p.1.2 : ℂ) * Complex.I) := by fun_prop
    have hbase : Continuous fun p : (Set.Icc (0 : ℝ) 1 × ℝ) × ℝ => (1 + ((p.1.1 : ℝ) : ℂ)) := by
      fun_prop
    have hexp : Continuous fun p : (Set.Icc (0 : ℝ) 1 × ℝ) × ℝ =>
        ((1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
    have hpow : Continuous fun p : (Set.Icc (0 : ℝ) 1 × ℝ) × ℝ =>
        (1 + ((p.1.1 : ℝ) : ℂ)) ^ ((1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
      refine hbase.cpow hexp (fun p => ?_)
      have : (1 + ((p.1.1 : ℝ) : ℂ)) = ((1 + (p.1.1 : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [p.1.1.2.1])
    have hker : Continuous fun p : (Set.Icc (0 : ℝ) 1 × ℝ) × ℝ => windowKernel (p.1.1 : ℝ) p.2 := by
      unfold windowKernel
      exact (hpow.sub continuous_const).div hexp (fun p => one_add_mul_I_ne_zero p.2)
    exact (h1.mul hker).mul h2
  have hcont := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hf (-T₀) T₀
  exact continuous_const.mul hcont

/-- `windowFun` composed with `log` is measurable in `(x, u)`. -/
lemma measurable_windowFun_pair (a : ℕ → ℂ) (N : Finset ℕ) :
    Measurable (fun p : ℝ × ℝ => windowFun a N p.2 (Real.log p.1)) := by
  unfold windowFun
  have hg : Measurable (fun p : ℝ × ℝ => Real.exp (Real.log p.1)) :=
    Real.measurable_exp.comp (Real.measurable_log.comp measurable_fst)
  refine Measurable.mul ?_ (Finset.measurable_sum _ fun n _ => Measurable.ite ?_ measurable_const measurable_const)
  · exact Complex.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_neg.comp (Real.measurable_log.comp measurable_fst)))
  · have : {p : ℝ × ℝ | Real.exp (Real.log p.1) < n ∧ (n : ℝ) ≤ Real.exp (Real.log p.1) * (1 + p.2)} =
        {p : ℝ × ℝ | Real.exp (Real.log p.1) < n} ∩
          {p : ℝ × ℝ | (n : ℝ) ≤ Real.exp (Real.log p.1) * (1 + p.2)} := by
      ext p; simp
    rw [this]
    exact (measurableSet_lt hg measurable_const).inter
      (measurableSet_le measurable_const (hg.mul (measurable_const.add measurable_snd)))

/-- The high-frequency part is jointly bounded on the relevant product set. -/
lemma norm_high_pair_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ x u : ℝ) (hx : 1 ≤ x) (hu : 0 < u)
    (hu' : u ≤ 1 / 2) (hT₀ : 0 < T₀) (hN : ∀ n ∈ N, 0 < n) :
    ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ≤
      (∑ n ∈ N, ‖a n‖) + (T₀ / Real.pi) * ∑ n ∈ N, ‖a n‖ / n := by
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_windowFun_le a N u (Real.log x)).trans ?_
    have hx0 : 0 < x := by linarith
    rw [Real.exp_neg, Real.exp_log hx0]
    have hS : 0 ≤ ∑ n ∈ N, ‖a n‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    calc x⁻¹ * ∑ n ∈ N, ‖a n‖ ≤ 1 * ∑ n ∈ N, ‖a n‖ := by
          gcongr
          exact inv_le_one_of_one_le₀ hx
      _ = _ := one_mul _
  · refine (norm_lowPart_le a N u T₀ (Real.log x) hu hu' hT₀ hN).trans ?_
    have hM : 0 ≤ ∑ n ∈ N, ‖a n‖ / (n : ℝ) :=
      Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    have hpi : 0 < Real.pi := Real.pi_pos
    calc (2 * T₀ / Real.pi) * u * ∑ n ∈ N, ‖a n‖ / n
        ≤ (2 * T₀ / Real.pi) * (1 / 2) * ∑ n ∈ N, ‖a n‖ / n := by gcongr
      _ = (T₀ / Real.pi) * ∑ n ∈ N, ‖a n‖ / n := by ring

set_option maxHeartbeats 800000 in
/-- Integrability of `‖H_u(log x)‖²` on the product of the two ranges. -/
lemma integrable_high_pair (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X X₂ c d sh : ℝ) (hX : 1 ≤ X)
    (hsh : 0 ≤ sh) (hT₀ : 0 < T₀) (hc : 0 ≤ c) (hd : d ≤ 1 / 2) (hN : ∀ n ∈ N, 0 < n) :
    Integrable (Function.uncurry fun (x u : ℝ) =>
        ‖windowFun a N u (Real.log (x + sh)) - lowPart a N u T₀ (Real.log (x + sh))‖ ^ 2)
      ((volume.restrict (Ioc X X₂)).prod (volume.restrict (Ioc c d))) := by
  have hX0 : 0 < X := by linarith
  set B : ℝ := (∑ n ∈ N, ‖a n‖) + (T₀ / Real.pi) * ∑ n ∈ N, ‖a n‖ / n with hB
  have hB0 : 0 ≤ B := by
    have hM : 0 ≤ ∑ n ∈ N, ‖a n‖ / (n : ℝ) :=
      Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
    have hS : 0 ≤ ∑ n ∈ N, ‖a n‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  rw [Measure.prod_restrict]
  have hmeasSet : MeasurableSet (Ioc X X₂ ×ˢ Ioc c d) := measurableSet_Ioc.prod measurableSet_Ioc
  have : IsFiniteMeasure ((volume.prod volume).restrict (Ioc X X₂ ×ˢ Ioc c d)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hG : AEStronglyMeasurable (fun p : ℝ × ℝ => windowFun a N p.2 (Real.log (p.1 + sh)))
      ((volume.prod volume).restrict (Ioc X X₂ ×ˢ Ioc c d)) :=
    ((measurable_windowFun_pair a N).comp ((measurable_fst.add_const sh).prodMk measurable_snd)).aestronglyMeasurable
  have hL : AEStronglyMeasurable (fun p : ℝ × ℝ => lowPart a N p.2 T₀ (Real.log (p.1 + sh)))
      ((volume.prod volume).restrict (Ioc X X₂ ×ˢ Ioc c d)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hmeasSet
    rw [continuousOn_iff_continuous_domRestrict]
    have hcont := continuous_lowPart_pair a N T₀ hN
    have hd1 : d ≤ 1 := by linarith
    let φ : (Ioc X X₂ ×ˢ Ioc c d : Set (ℝ × ℝ)) → Set.Icc (0 : ℝ) 1 × ℝ := fun p =>
      (⟨p.1.2, ⟨hc.trans p.2.2.1.le, p.2.2.2.trans hd1⟩⟩, Real.log (p.1.1 + sh))
    have hφ : Continuous φ := by
      refine Continuous.prodMk ?_ ?_
      · exact Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _
      · exact Real.continuousOn_log.comp_continuous
          ((continuous_fst.comp continuous_subtype_val).add continuous_const)
          (fun p => ne_of_gt (by linarith [p.2.1.1]))
    have key : Continuous ((fun q : Set.Icc (0 : ℝ) 1 × ℝ => lowPart a N q.1 T₀ q.2) ∘ φ) :=
      hcont.comp hφ
    exact key.congr (fun p => rfl)
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x u : ℝ) =>
      ‖windowFun a N u (Real.log (x + sh)) - lowPart a N u T₀ (Real.log (x + sh))‖ ^ 2)
      ((volume.prod volume).restrict (Ioc X X₂ ×ˢ Ioc c d)) :=
    (continuous_pow 2).comp_aestronglyMeasurable (hG.sub hL).norm
  refine Integrable.mono' (integrable_const (B ^ 2)) hmeas ?_
  filter_upwards [ae_restrict_mem hmeasSet] with p hp
  obtain ⟨hp1, hp2⟩ := hp
  simp only [Function.uncurry]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hb := norm_high_pair_le a N T₀ (p.1 + sh) p.2 (by linarith [hp1.1]) (lt_of_le_of_lt hc hp2.1)
    (hp2.2.trans hd) hT₀ hN
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

/-- Fubini for the high-frequency part. -/
lemma integral_integral_high_swap (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X X₂ c d sh : ℝ) (hX : 1 ≤ X)
    (hsh : 0 ≤ sh) (hX₂ : X ≤ X₂) (hT₀ : 0 < T₀) (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1 / 2)
    (hN : ∀ n ∈ N, 0 < n) :
    (∫ x in X..X₂, ∫ u in c..d,
        ‖windowFun a N u (Real.log (x + sh)) - lowPart a N u T₀ (Real.log (x + sh))‖ ^ 2) =
      ∫ u in c..d, ∫ x in X..X₂,
        ‖windowFun a N u (Real.log (x + sh)) - lowPart a N u T₀ (Real.log (x + sh))‖ ^ 2 := by
  simp_rw [intervalIntegral.integral_of_le hcd, intervalIntegral.integral_of_le hX₂]
  exact MeasureTheory.integral_integral_swap
    (integrable_high_pair a N T₀ X X₂ c d sh hX hsh hT₀ hc hd hN)

/-! ### Stage 4c: the kernel weight and the Plancherel bound for each window -/

/-- The weight appearing in Lemma 14. -/
noncomputable def wgt (X h t : ℝ) : ℝ := min 1 ((X / (h * t)) ^ 2)

lemma wgt_nonneg (X h t : ℝ) : 0 ≤ wgt X h t := le_min zero_le_one (sq_nonneg _)

lemma wgt_le_one (X h t : ℝ) : wgt X h t ≤ 1 := min_le_left _ _

lemma measurable_wgt (X h : ℝ) : Measurable (wgt X h) := by
  unfold wgt
  exact measurable_const.min ((measurable_const.div (measurable_const.mul measurable_id)).pow_const 2)

/-- Pointwise bound for the window kernel in terms of the weight. -/
lemma norm_sq_windowKernel_le_weight (X h u t : ℝ) (hX : 0 < X) (hh : 0 < h) (hu : 0 < u)
    (hu3 : u ≤ 3 * h / X) (hu1 : u ≤ 1) (ht : 1 ≤ |t|) :
    ‖windowKernel u t‖ ^ 2 ≤ 36 * (h / X) ^ 2 * wgt X h t := by
  have hb1 : ‖windowKernel u t‖ ^ 2 ≤ 36 * (h / X) ^ 2 := by
    have h1 := norm_windowKernel_le_mul u t hu hu1
    have h2 : 2 * u ≤ 6 * (h / X) := by
      have : u ≤ 3 * (h / X) := by rw [mul_div_assoc] at hu3; exact hu3
      linarith
    calc ‖windowKernel u t‖ ^ 2 ≤ (6 * (h / X)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
      _ = 36 * (h / X) ^ 2 := by ring
  have ht0 : 0 < |t| := by linarith
  have ht0' : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht; linarith
  have hb2 : ‖windowKernel u t‖ ^ 2 ≤ 36 * (h / X) ^ 2 * (X / (h * t)) ^ 2 := by
    have h1 := norm_windowKernel_le_div u t hu hu1
    have hsq : |t| ≤ Real.sqrt (1 + t ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by linarith)
    have h2 : 3 / Real.sqrt (1 + t ^ 2) ≤ 3 / |t| :=
      div_le_div_of_nonneg_left (by norm_num) ht0 hsq
    have h3 : ‖windowKernel u t‖ ^ 2 ≤ (3 / |t|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
    refine h3.trans ?_
    have hX' : X ≠ 0 := hX.ne'
    have hh' : h ≠ 0 := hh.ne'
    have e : 36 * (h / X) ^ 2 * (X / (h * t)) ^ 2 = 36 / t ^ 2 := by
      field_simp
      try ring
    rw [e, div_pow, sq_abs]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hnn : 0 ≤ 36 * (h / X) ^ 2 := by positivity
  unfold wgt
  rw [mul_min_of_nonneg _ _ hnn, mul_one]
  exact le_min hb1 hb2

/-- The weighted mean square is integrable on `{|t| ≥ T₀}`. -/
lemma integrableOn_weighted_dirichletPoly (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h : ℝ)
    (hN : ∀ n ∈ N, 0 < n) (hT₀ : 1 ≤ T₀) (hX : 0 < X) (hh : 0 < h) :
    IntegrableOn (fun t : ℝ => ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 * wgt X h t)
      {t : ℝ | T₀ ≤ |t|} := by
  set M : ℝ := ∑ n ∈ N, ‖a n‖ / n with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  have hset : MeasurableSet {t : ℝ | T₀ ≤ |t|} := measurableSet_le measurable_const measurable_abs
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ => ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 * wgt X h t)
      (volume.restrict {t : ℝ | T₀ ≤ |t|}) :=
    (((continuous_dirichletPoly_one_line a N hN).norm.pow 2).measurable.mul
      (measurable_wgt X h)).aestronglyMeasurable
  have hg : IntegrableOn (fun t : ℝ => 2 * M ^ 2 * (X / h) ^ 2 * (1 + t ^ 2)⁻¹)
      {t : ℝ | T₀ ≤ |t|} := (integrable_inv_one_add_sq.const_mul _).integrableOn
  refine hg.mono' hmeas ?_
  filter_upwards [ae_restrict_mem hset] with t ht
  have ht1 : 1 ≤ |t| := hT₀.trans ht
  have ht0 : t ≠ 0 := by intro h0; rw [h0, abs_zero] at ht1; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (wgt_nonneg X h t))]
  have hA : ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 ≤ M ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_dirichletPoly_le a N hN t) 2
  have hw : wgt X h t ≤ (X / h) ^ 2 * (2 * (1 + t ^ 2)⁻¹) := by
    have h1 : wgt X h t ≤ (X / (h * t)) ^ 2 := min_le_right _ _
    have h2 : (X / (h * t)) ^ 2 = (X / h) ^ 2 * (t ^ 2)⁻¹ := by
      field_simp
    have h3 : (t ^ 2)⁻¹ ≤ 2 * (1 + t ^ 2)⁻¹ := by
      have ht2 : 1 ≤ t ^ 2 := by
        have := sq_abs t
        nlinarith [sq_nonneg t, abs_nonneg t]
      rw [show (2 : ℝ) * (1 + t ^ 2)⁻¹ = ((1 + t ^ 2) / 2)⁻¹ by rw [inv_div, div_eq_mul_inv]]
      exact inv_anti₀ (by positivity) (by nlinarith)
    calc wgt X h t ≤ (X / (h * t)) ^ 2 := h1
      _ = (X / h) ^ 2 * (t ^ 2)⁻¹ := h2
      _ ≤ (X / h) ^ 2 * (2 * (1 + t ^ 2)⁻¹) := by gcongr
  calc ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 * wgt X h t
      ≤ M ^ 2 * ((X / h) ^ 2 * (2 * (1 + t ^ 2)⁻¹)) :=
        mul_le_mul hA hw (wgt_nonneg X h t) (sq_nonneg _)
    _ = 2 * M ^ 2 * (X / h) ^ 2 * (1 + t ^ 2)⁻¹ := by ring

/-- The weighted mean square of `A` on `{|t| ≥ T₀}`. -/
noncomputable def weightedMeanSq (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h : ℝ) : ℝ :=
  ∫ (t : ℝ) in {t : ℝ | T₀ ≤ |t|}, ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 * wgt X h t

lemma weightedMeanSq_nonneg (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h : ℝ) :
    0 ≤ weightedMeanSq a N T₀ X h :=
  setIntegral_nonneg (measurableSet_le measurable_const measurable_abs)
    (fun t _ => mul_nonneg (sq_nonneg _) (wgt_nonneg X h t))

/-- Plancherel bound for the high-frequency part of one window. -/
lemma integral_norm_sq_high_le_weighted (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h u : ℝ)
    (hN : ∀ n ∈ N, 0 < n) (hT₀ : 1 ≤ T₀) (hX : 0 < X) (hh : 0 < h) (hu : 0 < u)
    (hu3 : u ≤ 3 * h / X) (hu1 : u ≤ 1) :
    (∫ y, ‖windowFun a N u y - lowPart a N u T₀ y‖ ^ 2) ≤
      (18 / Real.pi) * (h / X) ^ 2 * weightedMeanSq a N T₀ X h := by
  rw [integral_norm_sq_windowFun_sub_lowPart a N u T₀ hu (by linarith) hN]
  have hset1 : MeasurableSet {t : ℝ | T₀ < |t|} := measurableSet_lt measurable_const measurable_abs
  have hsub : {t : ℝ | T₀ < |t|} ⊆ {t : ℝ | T₀ ≤ |t|} := fun t ht => show T₀ ≤ |t| from le_of_lt ht
  have hint := integrableOn_weighted_dirichletPoly a N T₀ X h hN hT₀ hX hh
  have hpt : ∀ t ∈ {t : ℝ | T₀ < |t|},
      ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I) * windowKernel u t‖ ^ 2 ≤
        36 * (h / X) ^ 2 * (‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 * wgt X h t) := by
    intro t ht
    have ht1 : 1 ≤ |t| := hT₀.trans (le_of_lt ht)
    rw [norm_mul, mul_pow]
    have hk := norm_sq_windowKernel_le_weight X h u t hX hh hu hu3 hu1 ht1
    calc ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 * ‖windowKernel u t‖ ^ 2
        ≤ ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 * (36 * (h / X) ^ 2 * wgt X h t) := by
          gcongr
      _ = _ := by ring
  have hpi : 0 < Real.pi := Real.pi_pos
  calc (1 / (2 * Real.pi)) * ∫ t in {t : ℝ | T₀ < |t|},
        ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I) * windowKernel u t‖ ^ 2
      ≤ (1 / (2 * Real.pi)) * ∫ t in {t : ℝ | T₀ < |t|},
          36 * (h / X) ^ 2 * (‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 * wgt X h t) := by
        refine mul_le_mul_of_nonneg_left
          (setIntegral_mono_on ?_ ((hint.mono_set hsub).const_mul _) hset1 hpt) (by positivity)
        -- integrability of the left integrand: bounded by the right one
        refine ((hint.mono_set hsub).const_mul (36 * (h / X) ^ 2)).mono' ?_ ?_
        · exact ((continuous_dirichletPoly_one_line a N hN).mul
            (by
              unfold windowKernel
              exact ((continuous_const.cpow (by fun_prop) (fun _ => by
                rw [show (1 + u : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; ring]
                exact Complex.ofReal_mem_slitPlane.mpr (by linarith))).sub continuous_const).div
                (by fun_prop) (fun t => one_add_mul_I_ne_zero t))).norm.pow 2
            |>.aestronglyMeasurable
        · filter_upwards [ae_restrict_mem hset1] with t ht
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact hpt t ht
    _ = (1 / (2 * Real.pi)) * (36 * (h / X) ^ 2 * ∫ t in {t : ℝ | T₀ < |t|},
          ‖dirichletPoly a N ((1 : ℂ) + (t : ℂ) * Complex.I)‖ ^ 2 * wgt X h t) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ (1 / (2 * Real.pi)) * (36 * (h / X) ^ 2 * weightedMeanSq a N T₀ X h) := by
        gcongr
        unfold weightedMeanSq
        exact setIntegral_mono_set hint (Filter.Eventually.of_forall
          (fun t => mul_nonneg (sq_nonneg _) (wgt_nonneg X h t))) (Filter.Eventually.of_forall hsub)
    _ = (18 / Real.pi) * (h / X) ^ 2 * weightedMeanSq a N T₀ X h := by
        field_simp
        ring

/-! ### Stage 4d: mean square of the high-frequency averages -/

lemma windowFun_zero (a : ℕ → ℂ) (N : Finset ℕ) (y : ℝ) : windowFun a N 0 y = 0 := by
  unfold windowFun
  rw [mul_eq_zero]
  right
  apply Finset.sum_eq_zero
  intro n _
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  linarith [show (Real.exp y * (1 + 0) : ℝ) = Real.exp y by ring]

lemma high_zero (a : ℕ → ℂ) (N : Finset ℕ) (T₀ y : ℝ) :
    windowFun a N 0 y - lowPart a N 0 T₀ y = 0 := by
  rw [windowFun_zero, lowPart_zero, sub_zero]

/-- The high part is bounded, for `u ∈ (0, 1/2]` and `y ≥ 0`. -/
lemma norm_high_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ u y : ℝ) (hu : 0 < u) (hu' : u ≤ 1 / 2)
    (hy : 0 ≤ y) (hT₀ : 0 < T₀) (hN : ∀ n ∈ N, 0 < n) :
    ‖windowFun a N u y - lowPart a N u T₀ y‖ ≤
      (∑ n ∈ N, ‖a n‖) + (T₀ / Real.pi) * ∑ n ∈ N, ‖a n‖ / n := by
  have := norm_high_pair_le a N T₀ (Real.exp y) u (Real.one_le_exp hy) hu hu' hT₀ hN
  rwa [Real.log_exp] at this

lemma intervalIntegrable_high_param (a : ℕ → ℂ) (N : Finset ℕ) (T₀ y α β : ℝ) (hα : 0 ≤ α)
    (hαβ : α ≤ β) (hβ : β ≤ 1) (hN : ∀ n ∈ N, 0 < n) :
    IntervalIntegrable (fun u => windowFun a N u y - lowPart a N u T₀ y) volume α β :=
  (intervalIntegrable_windowFun_param a N y α β).sub
    (intervalIntegrable_lowPart_param a N T₀ y hN α β hα hβ hαβ)

lemma intervalIntegrable_norm_sq_high_param (a : ℕ → ℂ) (N : Finset ℕ) (T₀ y α β : ℝ)
    (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1 / 2) (hy : 0 ≤ y) (hT₀ : 0 < T₀)
    (hN : ∀ n ∈ N, 0 < n) :
    IntervalIntegrable (fun u => ‖windowFun a N u y - lowPart a N u T₀ y‖ ^ 2) volume α β := by
  have hg := (intervalIntegrable_high_param a N T₀ y α β hα hαβ (by linarith) hN).norm
  set B : ℝ := (∑ n ∈ N, ‖a n‖) + (T₀ / Real.pi) * ∑ n ∈ N, ‖a n‖ / n with hB
  rw [intervalIntegrable_iff] at hg ⊢
  have hfin : IsFiniteMeasure (volume.restrict (Set.uIoc α β)) :=
    isFiniteMeasure_restrict.mpr (by
      rw [Set.uIoc_of_le hαβ, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  refine (integrable_const (B ^ 2)).mono'
    ((continuous_pow 2).comp_aestronglyMeasurable hg.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  rw [Set.uIoc_of_le hαβ, mem_Ioc] at hu
  simp only [Real.norm_eq_abs, abs_pow, abs_norm]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (norm_high_le a N T₀ u y (lt_of_le_of_lt hα hu.1) (hu.2.trans hβ) hy hT₀ hN) 2

/-- Cauchy–Schwarz for one averaged window piece. -/
lemma norm_sq_piece_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ : ℝ) (hN : ∀ n ∈ N, 0 < n) (K : ℂ)
    (α β y : ℝ) (hα : 0 ≤ α) (hαβ : α ≤ β) (hβ : β ≤ 1 / 2) (hT₀ : 0 < T₀) (hy : 0 ≤ y) :
    ‖K * ∫ u in α..β, (windowFun a N u y - lowPart a N u T₀ y)‖ ^ 2 ≤
      ‖K‖ ^ 2 * ((β - α) * ∫ u in α..β, ‖windowFun a N u y - lowPart a N u T₀ y‖ ^ 2) := by
  rw [norm_mul, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have h1 : ‖∫ u in α..β, (windowFun a N u y - lowPart a N u T₀ y)‖ ≤
      ∫ u in α..β, ‖windowFun a N u y - lowPart a N u T₀ y‖ :=
    intervalIntegral.norm_integral_le_integral_norm hαβ
  have h2 := sq_integral_le_integral_sq α β hαβ (fun u => ‖windowFun a N u y - lowPart a N u T₀ y‖)
    (intervalIntegrable_high_param a N T₀ y α β hα hαβ (by linarith) hN).norm
    (intervalIntegrable_norm_sq_high_param a N T₀ y α β hα hαβ hβ hy hT₀ hN)
  calc ‖∫ u in α..β, (windowFun a N u y - lowPart a N u T₀ y)‖ ^ 2
      ≤ (∫ u in α..β, ‖windowFun a N u y - lowPart a N u T₀ y‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

/-- Pointwise domination of the first piece. -/
lemma norm_sq_first_piece_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h x : ℝ) (hN : ∀ n ∈ N, 0 < n)
    (hX : 1 ≤ X) (hh : 0 < h) (h8 : 8 * h ≤ X) (hT₀ : 0 < T₀) (hx : X ≤ x) (hx2 : x ≤ 2 * X) :
    ‖((x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) * ∫ u in (h / x)..(3 * h / x),
        (windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x))‖ ^ 2 ≤
      (4 * X ^ 3 / h ^ 3) * ∫ u in (h / (2 * X))..(3 * h / X),
        ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2 := by
  have hx0 : 0 < x := by linarith
  have hy : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hα : 0 ≤ h / x := by positivity
  have hαβ : h / x ≤ 3 * h / x := by apply div_le_div_of_nonneg_right _ hx0.le; linarith
  have hβ : 3 * h / x ≤ 1 / 2 := by
    rw [div_le_iff₀ hx0]; nlinarith
  have hc : h / (2 * X) ≤ h / x := by
    apply div_le_div_of_nonneg_left hh.le hx0 hx2
  have hd : 3 * h / x ≤ 3 * h / X := by
    apply div_le_div_of_nonneg_left (by positivity) (by linarith) hx
  have hd' : 3 * h / X ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hcs := norm_sq_piece_le a N T₀ hN ((x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) (h / x) (3 * h / x)
    (Real.log x) hα hαβ hβ hT₀ hy
  have hK : ‖(x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)‖ ^ 2 = x ^ 4 / (4 * h ^ 4) := by
    rw [norm_div, norm_pow, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, abs_of_pos hh]
    norm_num
    ring
  have hext : (∫ u in (h / x)..(3 * h / x),
        ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2) ≤
      ∫ u in (h / (2 * X))..(3 * h / X),
        ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2 := by
    apply intervalIntegral.integral_mono_interval hc hαβ hd
    · exact Filter.Eventually.of_forall (fun u => sq_nonneg _)
    · exact intervalIntegrable_norm_sq_high_param a N T₀ (Real.log x) _ _ (by positivity)
        (hc.trans (hαβ.trans hd)) hd' hy hT₀ hN
  have hint0 : 0 ≤ ∫ u in (h / (2 * X))..(3 * h / X),
      ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2 :=
    intervalIntegral.integral_nonneg (hc.trans (hαβ.trans hd)) (fun u _ => sq_nonneg _)
  have hlen : 3 * h / x - h / x = 2 * h / x := by ring
  calc _ ≤ _ := hcs
    _ = (x ^ 3 / (2 * h ^ 3)) * ∫ u in (h / x)..(3 * h / x),
        ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2 := by
        rw [hK, hlen]
        field_simp
        try ring
    _ ≤ (x ^ 3 / (2 * h ^ 3)) * ∫ u in (h / (2 * X))..(3 * h / X),
        ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2 := by
        gcongr
    _ ≤ (4 * X ^ 3 / h ^ 3) * ∫ u in (h / (2 * X))..(3 * h / X),
        ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hint0
        have : x ^ 3 ≤ 8 * X ^ 3 := by
          calc x ^ 3 ≤ (2 * X) ^ 3 := pow_le_pow_left₀ hx0.le hx2 3
            _ = 8 * X ^ 3 := by ring
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hh 3]

/-- Pointwise domination of the second piece. -/
lemma norm_sq_second_piece_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h x : ℝ) (hN : ∀ n ∈ N, 0 < n)
    (hX : 1 ≤ X) (hh : 0 < h) (h8 : 8 * h ≤ X) (hT₀ : 0 < T₀) (hx : X ≤ x) (hx2 : x ≤ 2 * X) :
    ‖(((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) * ∫ u in (0 : ℝ)..(2 * h / (x + h)),
        (windowFun a N u (Real.log (x + h)) - lowPart a N u T₀ (Real.log (x + h)))‖ ^ 2 ≤
      (27 * X ^ 3 / (2 * h ^ 3)) * ∫ u in (0 : ℝ)..(2 * h / X),
        ‖windowFun a N u (Real.log (x + h)) - lowPart a N u T₀ (Real.log (x + h))‖ ^ 2 := by
  have hxh : 0 < x + h := by linarith
  have hy : 0 ≤ Real.log (x + h) := Real.log_nonneg (by linarith)
  have hαβ : (0 : ℝ) ≤ 2 * h / (x + h) := by positivity
  have hβ : 2 * h / (x + h) ≤ 1 / 2 := by
    rw [div_le_iff₀ hxh]; nlinarith
  have hd : 2 * h / (x + h) ≤ 2 * h / X := by
    apply div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
  have hd' : 2 * h / X ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hcs := norm_sq_piece_le a N T₀ hN (((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) 0
    (2 * h / (x + h)) (Real.log (x + h)) le_rfl hαβ hβ hT₀ hy
  have hK : ‖((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)‖ ^ 2 = (x + h) ^ 4 / (4 * h ^ 4) := by
    rw [norm_div, norm_pow, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxh, abs_of_pos hh]
    norm_num
    ring
  have hext : (∫ u in (0 : ℝ)..(2 * h / (x + h)),
        ‖windowFun a N u (Real.log (x + h)) - lowPart a N u T₀ (Real.log (x + h))‖ ^ 2) ≤
      ∫ u in (0 : ℝ)..(2 * h / X),
        ‖windowFun a N u (Real.log (x + h)) - lowPart a N u T₀ (Real.log (x + h))‖ ^ 2 := by
    apply intervalIntegral.integral_mono_interval le_rfl hαβ hd
    · exact Filter.Eventually.of_forall (fun u => sq_nonneg _)
    · exact intervalIntegrable_norm_sq_high_param a N T₀ (Real.log (x + h)) _ _ le_rfl
        (by positivity) hd' hy hT₀ hN
  have hint0 : 0 ≤ ∫ u in (0 : ℝ)..(2 * h / X),
      ‖windowFun a N u (Real.log (x + h)) - lowPart a N u T₀ (Real.log (x + h))‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by positivity) (fun u _ => sq_nonneg _)
  calc _ ≤ _ := hcs
    _ = ((x + h) ^ 3 / (2 * h ^ 3)) * ∫ u in (0 : ℝ)..(2 * h / (x + h)),
        ‖windowFun a N u (Real.log (x + h)) - lowPart a N u T₀ (Real.log (x + h))‖ ^ 2 := by
        rw [hK, sub_zero]
        field_simp
        try ring
    _ ≤ ((x + h) ^ 3 / (2 * h ^ 3)) * ∫ u in (0 : ℝ)..(2 * h / X),
        ‖windowFun a N u (Real.log (x + h)) - lowPart a N u T₀ (Real.log (x + h))‖ ^ 2 := by
        gcongr
    _ ≤ (27 * X ^ 3 / (2 * h ^ 3)) * ∫ u in (0 : ℝ)..(2 * h / X),
        ‖windowFun a N u (Real.log (x + h)) - lowPart a N u T₀ (Real.log (x + h))‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hint0
        have : (x + h) ^ 3 ≤ 27 * X ^ 3 := by
          calc (x + h) ^ 3 ≤ (3 * X) ^ 3 := pow_le_pow_left₀ hxh.le (by linarith) 3
            _ = 27 * X ^ 3 := by ring
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [pow_pos hh 3]

/-! ### Stage 4e: integrating the pieces -/

/-- The inner integral of the high part over a range of windows. -/
noncomputable def innerHigh (a : ℕ → ℂ) (N : Finset ℕ) (T₀ c d : ℝ) (x : ℝ) : ℝ :=
  ∫ u in c..d, ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2

lemma innerHigh_nonneg (a : ℕ → ℂ) (N : Finset ℕ) (T₀ c d x : ℝ) (hcd : c ≤ d) :
    0 ≤ innerHigh a N T₀ c d x :=
  intervalIntegral.integral_nonneg hcd (fun _ _ => sq_nonneg _)

lemma integrableOn_innerHigh_shift (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X X₂ c d sh : ℝ) (hX : 1 ≤ X)
    (hsh : 0 ≤ sh) (hT₀ : 0 < T₀) (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 1 / 2)
    (hN : ∀ n ∈ N, 0 < n) :
    IntegrableOn (fun x => innerHigh a N T₀ c d (x + sh)) (Ioc X X₂) := by
  have := (integrable_high_pair a N T₀ X X₂ c d sh hX hsh hT₀ hc hd hN).integral_prod_left
  unfold innerHigh IntegrableOn
  simp_rw [intervalIntegral.integral_of_le hcd]
  exact this

/-- The integrated inner integral over a range of windows `u ≤ 3h/X`. -/
lemma integral_innerHigh_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X X₂ h c d sh : ℝ)
    (hN : ∀ n ∈ N, 0 < n) (hT₀ : 1 ≤ T₀) (hX : 1 ≤ X) (hX₂ : X ≤ X₂) (hsh : 0 ≤ sh) (hh : 0 < h)
    (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ 3 * h / X) (hd' : d ≤ 1 / 2) :
    ∫ x in Ioc X X₂, innerHigh a N T₀ c d (x + sh) ≤
      (d - c) * ((X₂ + sh) * ((18 / Real.pi) * (h / X) ^ 2 * weightedMeanSq a N T₀ X h)) := by
  have hT₀0 : 0 < T₀ := by linarith
  have hX0 : 0 < X := by linarith
  have hswap := integral_integral_high_swap a N T₀ X X₂ c d sh hX hsh hX₂ hT₀0 hc hcd hd' hN
  have hI0 := weightedMeanSq_nonneg a N T₀ X h
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold innerHigh
  rw [← intervalIntegral.integral_of_le hX₂, hswap]
  have hpt : ∀ u ∈ Icc c d, (∫ x in X..X₂,
      ‖windowFun a N u (Real.log (x + sh)) - lowPart a N u T₀ (Real.log (x + sh))‖ ^ 2) ≤
      (X₂ + sh) * ((18 / Real.pi) * (h / X) ^ 2 * weightedMeanSq a N T₀ X h) := by
    intro u hu
    rcases (hc.trans hu.1).eq_or_lt with h0 | hu0
    · subst h0
      simp only [high_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        intervalIntegral.integral_zero]
      exact mul_nonneg (by linarith) (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) hI0)
    · have hu3 : u ≤ 3 * h / X := hu.2.trans hd
      have hu1 : u ≤ 1 := by linarith [hu.2.trans hd']
      have hint := integrable_norm_sq_high a N u T₀ hu0 hT₀0.le hN
      calc (∫ x in X..X₂, ‖windowFun a N u (Real.log (x + sh)) -
              lowPart a N u T₀ (Real.log (x + sh))‖ ^ 2)
          = ∫ x in (X + sh)..(X₂ + sh),
              ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2 :=
            intervalIntegral.integral_comp_add_right
              (fun x => ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2) sh
        _ = ∫ x in Ioc (X + sh) (X₂ + sh),
              ‖windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x)‖ ^ 2 :=
            intervalIntegral.integral_of_le (by linarith)
        _ ≤ (X₂ + sh) * ∫ y, ‖windowFun a N u y - lowPart a N u T₀ y‖ ^ 2 :=
            integral_comp_log_Ioc_le _ hint (fun _ => sq_nonneg _) (X + sh) (X₂ + sh)
              (by linarith) (by linarith)
        _ ≤ (X₂ + sh) * ((18 / Real.pi) * (h / X) ^ 2 * weightedMeanSq a N T₀ X h) :=
            mul_le_mul_of_nonneg_left
              (integral_norm_sq_high_le_weighted a N T₀ X h u hN hT₀ hX0 hh hu0 hu3 hu1)
              (by linarith)
  have hint1 : IntervalIntegrable (fun u => ∫ x in X..X₂,
      ‖windowFun a N u (Real.log (x + sh)) - lowPart a N u T₀ (Real.log (x + sh))‖ ^ 2)
      volume c d := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcd]
    have := (integrable_high_pair a N T₀ X X₂ c d sh hX hsh hT₀0 hc hd' hN).integral_prod_right
    simp_rw [intervalIntegral.integral_of_le hX₂]
    exact this
  calc (∫ u in c..d, ∫ x in X..X₂,
        ‖windowFun a N u (Real.log (x + sh)) - lowPart a N u T₀ (Real.log (x + sh))‖ ^ 2)
      ≤ ∫ _u in c..d, (X₂ + sh) * ((18 / Real.pi) * (h / X) ^ 2 * weightedMeanSq a N T₀ X h) :=
        intervalIntegral.integral_mono_on hcd hint1 intervalIntegrable_const hpt
    _ = (d - c) * ((X₂ + sh) * ((18 / Real.pi) * (h / X) ^ 2 * weightedMeanSq a N T₀ X h)) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]

/-- The dominating function for `‖highAvg‖²`. -/
noncomputable def highDom (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h : ℝ) (x : ℝ) : ℝ :=
  2 * ((4 * X ^ 3 / h ^ 3) * innerHigh a N T₀ (h / (2 * X)) (3 * h / X) x) +
    2 * ((27 * X ^ 3 / (2 * h ^ 3)) * innerHigh a N T₀ 0 (2 * h / X) (x + h))

lemma norm_sq_highAvg_le_highDom (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h x : ℝ) (hN : ∀ n ∈ N, 0 < n)
    (hX : 1 ≤ X) (hh : 0 < h) (h8 : 8 * h ≤ X) (hT₀ : 0 < T₀) (hx : X ≤ x) (hx2 : x ≤ 2 * X) :
    ‖highAvg a N T₀ x h‖ ^ 2 ≤ highDom a N T₀ X h x := by
  unfold highAvg highDom innerHigh
  have h1 := norm_sq_first_piece_le a N T₀ X h x hN hX hh h8 hT₀ hx hx2
  have h2 := norm_sq_second_piece_le a N T₀ X h x hN hX hh h8 hT₀ hx hx2
  set P₁ := ((x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) * ∫ u in (h / x)..(3 * h / x),
    (windowFun a N u (Real.log x) - lowPart a N u T₀ (Real.log x))
  set P₂ := (((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) * ∫ u in (0 : ℝ)..(2 * h / (x + h)),
    (windowFun a N u (Real.log (x + h)) - lowPart a N u T₀ (Real.log (x + h)))
  have htri : ‖P₁ - P₂‖ ≤ ‖P₁‖ + ‖P₂‖ := norm_sub_le _ _
  calc ‖P₁ - P₂‖ ^ 2 ≤ (‖P₁‖ + ‖P₂‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ 2 * ‖P₁‖ ^ 2 + 2 * ‖P₂‖ ^ 2 := sq_add_le_two_mul_sq_add_sq _ _
    _ ≤ _ := by linarith

lemma integrableOn_highDom (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h : ℝ) (hN : ∀ n ∈ N, 0 < n)
    (hX : 1 ≤ X) (hh : 0 < h) (h8 : 8 * h ≤ X) (hT₀ : 0 < T₀) :
    IntegrableOn (highDom a N T₀ X h) (Ioc X (2 * X)) := by
  have hd1 : 3 * h / X ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hd2 : 2 * h / X ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hcd1 : h / (2 * X) ≤ 3 * h / X := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hi1 := integrableOn_innerHigh_shift a N T₀ X (2 * X) (h / (2 * X)) (3 * h / X) 0 hX le_rfl
    hT₀ (by positivity) hcd1 hd1 hN
  have hi2 := integrableOn_innerHigh_shift a N T₀ X (2 * X) 0 (2 * h / X) h hX hh.le
    hT₀ le_rfl (by positivity) hd2 hN
  simp only [add_zero] at hi1
  unfold highDom
  exact ((hi1.const_mul _).const_mul _).add ((hi2.const_mul _).const_mul _)

lemma integral_highDom_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h : ℝ) (hN : ∀ n ∈ N, 0 < n)
    (hT₀ : 1 ≤ T₀) (hX : 1 ≤ X) (hh : 0 < h) (h8 : 8 * h ≤ X) :
    ∫ x in Ioc X (2 * X), highDom a N T₀ X h x ≤ 1204 * X * weightedMeanSq a N T₀ X h := by
  have hT₀0 : 0 < T₀ := by linarith
  have hX0 : 0 < X := by linarith
  have hd1 : 3 * h / X ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hd2 : 2 * h / X ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have hcd1 : h / (2 * X) ≤ 3 * h / X := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hd2' : 2 * h / X ≤ 3 * h / X := by
    apply div_le_div_of_nonneg_right _ hX0.le; linarith
  have hi1 := integrableOn_innerHigh_shift a N T₀ X (2 * X) (h / (2 * X)) (3 * h / X) 0 hX le_rfl
    hT₀0 (by positivity) hcd1 hd1 hN
  have hi2 := integrableOn_innerHigh_shift a N T₀ X (2 * X) 0 (2 * h / X) h hX hh.le
    hT₀0 le_rfl (by positivity) hd2 hN
  simp only [add_zero] at hi1
  have hb1 := integral_innerHigh_le a N T₀ X (2 * X) h (h / (2 * X)) (3 * h / X) 0 hN hT₀ hX
    (by linarith) le_rfl hh (by positivity) hcd1 le_rfl hd1
  have hb2 := integral_innerHigh_le a N T₀ X (2 * X) h 0 (2 * h / X) h hN hT₀ hX
    (by linarith) hh.le hh le_rfl (by positivity) hd2' hd2
  simp only [add_zero] at hb1
  have hI0 := weightedMeanSq_nonneg a N T₀ X h
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  unfold highDom
  rw [integral_add ((hi1.const_mul _).const_mul _) ((hi2.const_mul _).const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  set I := weightedMeanSq a N T₀ X h
  have hK1 : 0 ≤ 4 * X ^ 3 / h ^ 3 := by positivity
  have hK2 : 0 ≤ 27 * X ^ 3 / (2 * h ^ 3) := by positivity
  have e1 : (3 * h / X - h / (2 * X)) * ((2 * X) * ((18 / Real.pi) * (h / X) ^ 2 * I)) =
      (90 / Real.pi) * (h ^ 3 / X ^ 2) * I := by
    have hX0' : X ≠ 0 := hX0.ne'
    have hpi' : Real.pi ≠ 0 := hpi.ne'
    field_simp
    ring
  have e2 : (2 * h / X - 0) * ((2 * X + h) * ((18 / Real.pi) * (h / X) ^ 2 * I)) ≤
      (108 / Real.pi) * (h ^ 3 / X ^ 2) * I := by
    have : 2 * X + h ≤ 3 * X := by linarith
    have hnn : 0 ≤ (2 * h / X) * ((18 / Real.pi) * (h / X) ^ 2 * I) := by positivity
    calc (2 * h / X - 0) * ((2 * X + h) * ((18 / Real.pi) * (h / X) ^ 2 * I))
        ≤ (2 * h / X - 0) * ((3 * X) * ((18 / Real.pi) * (h / X) ^ 2 * I)) := by
          apply mul_le_mul_of_nonneg_left _ (by rw [sub_zero]; positivity)
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ = (108 / Real.pi) * (h ^ 3 / X ^ 2) * I := by
          field_simp
          ring
  rw [e1] at hb1
  have hb2' := hb2.trans e2
  calc 2 * ((4 * X ^ 3 / h ^ 3) * ∫ x in Ioc X (2 * X), innerHigh a N T₀ (h / (2 * X)) (3 * h / X) x) +
        2 * ((27 * X ^ 3 / (2 * h ^ 3)) * ∫ x in Ioc X (2 * X), innerHigh a N T₀ 0 (2 * h / X) (x + h))
      ≤ 2 * ((4 * X ^ 3 / h ^ 3) * ((90 / Real.pi) * (h ^ 3 / X ^ 2) * I)) +
        2 * ((27 * X ^ 3 / (2 * h ^ 3)) * ((108 / Real.pi) * (h ^ 3 / X ^ 2) * I)) := by
        gcongr
    _ = (3636 / Real.pi) * X * I := by
        field_simp
        ring
    _ ≤ 1204 * X * I := by
        have : (3636 : ℝ) / Real.pi ≤ 1204 := by
          rw [div_le_iff₀ hpi]; nlinarith [Real.pi_gt_d2]
        have hXI : 0 ≤ X * I := by positivity
        calc (3636 / Real.pi) * X * I = (3636 / Real.pi) * (X * I) := by ring
          _ ≤ 1204 * (X * I) := by gcongr
          _ = 1204 * X * I := by ring

/-! ### Stage 5: the low-frequency part and the final assembly -/

/-- The low-frequency average is close to the reference value `Φ₀ = lowPart(u₀, log x)/u₀`
with `u₀ = h₁/x`, uniformly for `h ≤ h₂`. -/
lemma norm_lowAvg_sub_le (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X x h h₁ h₂ : ℝ) (hN : ∀ n ∈ N, 0 < n)
    (hT₀ : 1 ≤ T₀) (hX : 1 ≤ X) (hx : X ≤ x) (hh₁ : 0 < h₁) (h12 : h₁ ≤ h₂) (hh : 0 < h)
    (hh2 : h ≤ h₂) (h8 : 8 * h₂ ≤ X) :
    ‖lowAvg a N T₀ x h - lowPart a N (h₁ / x) T₀ (Real.log x) / ((h₁ / x : ℝ) : ℂ)‖ ≤
      94 * T₀ ^ 2 * (h₂ / X) * ∑ n ∈ N, ‖a n‖ / n := by
  have hX0 : 0 < X := by linarith
  have hx0 : 0 < x := by linarith
  have hT₀0 : 0 < T₀ := by linarith
  have hu₀ : 0 < h₁ / x := div_pos hh₁ hx0
  have hu₀' : h₁ / x ≤ 1 / 2 := by rw [div_le_iff₀ hx0]; linarith
  have hhx : 6 * h ≤ x := by linarith
  set M : ℝ := ∑ n ∈ N, ‖a n‖ / n with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  set Φ₀ : ℂ := lowPart a N (h₁ / x) T₀ (Real.log x) / ((h₁ / x : ℝ) : ℂ) with hΦ₀
  have h1 := lowAvg_first_sub_le a N T₀ x h (h₁ / x) hx0 hh hhx hu₀ hu₀' hT₀0 hN
  have h2 := lowAvg_second_sub_le a N T₀ x h (h₁ / x) hx0 hh hhx hu₀ hu₀' hT₀0 hN
  rw [← hΦ₀] at h1 h2
  rw [← hM] at h1 h2
  have hsplit : lowAvg a N T₀ x h - Φ₀ =
      (((x : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) * (∫ u in (h / x)..(3 * h / x), lowPart a N u T₀ (Real.log x)) -
        2 * Φ₀) -
      ((((x + h : ℝ) : ℂ) ^ 2 / (2 * (h : ℂ) ^ 2)) *
        (∫ u in (0 : ℝ)..(2 * h / (x + h)), lowPart a N u T₀ (Real.log (x + h))) - Φ₀) := by
    unfold lowAvg; ring
  set r : ℝ := h₂ / X with hr
  have hr0 : 0 ≤ r := div_nonneg (by linarith) hX0.le
  have hhx' : h / x ≤ r := by
    rw [hr, div_le_div_iff₀ hx0 hX0]; nlinarith
  have hh₁x : h₁ / x ≤ r := by
    rw [hr, div_le_div_iff₀ hx0 hX0]; nlinarith
  have hpi : 0 < Real.pi := Real.pi_pos
  have hA : 0 ≤ 8 * T₀ * (1 + T₀) / Real.pi := div_nonneg (by nlinarith) hpi.le
  have hB : 0 ≤ 2 * T₀ ^ 2 / Real.pi := div_nonneg (by nlinarith) hpi.le
  have e3 : 3 * h / x = 3 * (h / x) := by ring
  have e2 : 2 * h / x = 2 * (h / x) := by ring
  have hs1 : 3 * h / x + h₁ / x ≤ 4 * r := by rw [e3]; linarith
  have hs2 : 2 * h / x + h₁ / x ≤ 3 * r := by rw [e2]; linarith
  have b1 : 3 * ((8 * T₀ * (1 + T₀) / Real.pi) * (3 * h / x + h₁ / x)) * M ≤
      3 * ((8 * T₀ * (1 + T₀) / Real.pi) * (4 * r)) * M := by
    have := mul_le_mul_of_nonneg_left hs1 hA
    have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 3)
    exact mul_le_mul_of_nonneg_right this hM0
  have b2 : 2 * ((8 * T₀ * (1 + T₀) / Real.pi) * (2 * h / x + h₁ / x) + (2 * T₀ ^ 2 / Real.pi) * (h / x)) * M ≤
      2 * ((8 * T₀ * (1 + T₀) / Real.pi) * (3 * r) + (2 * T₀ ^ 2 / Real.pi) * r) * M := by
    have := add_le_add (mul_le_mul_of_nonneg_left hs2 hA) (mul_le_mul_of_nonneg_left hhx' hB)
    have := mul_le_mul_of_nonneg_left this (by norm_num : (0 : ℝ) ≤ 2)
    exact mul_le_mul_of_nonneg_right this hM0
  have hnum : 3 * ((8 * T₀ * (1 + T₀) / Real.pi) * (4 * r)) * M +
      2 * ((8 * T₀ * (1 + T₀) / Real.pi) * (3 * r) + (2 * T₀ ^ 2 / Real.pi) * r) * M ≤
      94 * T₀ ^ 2 * r * M := by
    have e : 3 * ((8 * T₀ * (1 + T₀) / Real.pi) * (4 * r)) * M +
        2 * ((8 * T₀ * (1 + T₀) / Real.pi) * (3 * r) + (2 * T₀ ^ 2 / Real.pi) * r) * M =
        ((144 * T₀ * (1 + T₀) + 4 * T₀ ^ 2) / Real.pi) * (r * M) := by
      field_simp
      ring
    rw [e]
    have hc : (144 * T₀ * (1 + T₀) + 4 * T₀ ^ 2) / Real.pi ≤ 94 * T₀ ^ 2 := by
      rw [div_le_iff₀ hpi]
      nlinarith [Real.pi_gt_d2, sq_nonneg T₀]
    have hrM : 0 ≤ r * M := mul_nonneg hr0 hM0
    calc ((144 * T₀ * (1 + T₀) + 4 * T₀ ^ 2) / Real.pi) * (r * M) ≤ 94 * T₀ ^ 2 * (r * M) :=
          mul_le_mul_of_nonneg_right hc hrM
      _ = 94 * T₀ ^ 2 * r * M := by ring
  calc ‖lowAvg a N T₀ x h - Φ₀‖ ≤ _ := by rw [hsplit]; exact norm_sub_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ ≤ _ := add_le_add b1 b2
    _ ≤ 94 * T₀ ^ 2 * r * M := hnum

/-- The weighted mean square is monotone decreasing in the window length. -/
lemma weightedMeanSq_mono (a : ℕ → ℂ) (N : Finset ℕ) (T₀ X h₁ h₂ : ℝ) (hN : ∀ n ∈ N, 0 < n)
    (hT₀ : 1 ≤ T₀) (hX : 0 < X) (hh₁ : 0 < h₁) (h12 : h₁ ≤ h₂) :
    weightedMeanSq a N T₀ X h₂ ≤ weightedMeanSq a N T₀ X h₁ := by
  unfold weightedMeanSq
  have hset : MeasurableSet {t : ℝ | T₀ ≤ |t|} := measurableSet_le measurable_const measurable_abs
  apply setIntegral_mono_on
  · exact integrableOn_weighted_dirichletPoly a N T₀ X h₂ hN hT₀ hX (by linarith)
  · exact integrableOn_weighted_dirichletPoly a N T₀ X h₁ hN hT₀ hX hh₁
  · exact hset
  · intro t ht
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    unfold wgt
    apply min_le_min_left
    have ht0 : t ≠ 0 := by
      intro h0
      simp only [Set.mem_ofPred_eq, h0, abs_zero] at ht
      linarith
    have habs : 0 < |t| := abs_pos.mpr ht0
    rw [div_pow, div_pow, mul_pow, mul_pow]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ hh₁.le h12 2

/-- **Lemma 14 (Parseval bound), real form.** -/
theorem variance_windowSum_le_real (a : ℕ → ℂ) (N : Finset ℕ) (X h₁ h₂ T₀ : ℝ)
    (hN : ∀ n ∈ N, 0 < n) (hX : 1 ≤ X) (hh₁ : 1 ≤ h₁) (h12 : h₁ ≤ h₂) (h2X : h₂ ≤ X / 8)
    (hT₀ : 1 ≤ T₀) (hsupp : ∀ n, n ∉ N → a n = 0) :
    (1 / X) * ∫ x in X..(2 * X), ‖windowSum a x (x + h₁) / (h₁ : ℂ) -
        windowSum a x (x + h₂) / (h₂ : ℂ)‖ ^ 2 ≤
      80000 * (T₀ ^ 4 * (h₂ / X) ^ 2 * (∑ n ∈ N, ‖a n‖ / (n : ℝ)) ^ 2 + weightedMeanSq a N T₀ X h₁) := by
  have hX0 : 0 < X := by linarith
  have hT₀0 : 0 < T₀ := by linarith
  have hh₁0 : 0 < h₁ := by linarith
  have hh₂0 : 0 < h₂ := by linarith
  have h8 : 8 * h₂ ≤ X := by linarith
  have h8' : 8 * h₁ ≤ X := by linarith
  set M : ℝ := ∑ n ∈ N, ‖a n‖ / n with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun n _ => div_nonneg (norm_nonneg _) (Nat.cast_nonneg _))
  set K : ℝ := 94 * T₀ ^ 2 * (h₂ / X) * M with hK
  have hK0 : 0 ≤ K := by positivity
  set I₁ := weightedMeanSq a N T₀ X h₁ with hI₁
  set I₂ := weightedMeanSq a N T₀ X h₂ with hI₂
  have hI₁0 := weightedMeanSq_nonneg a N T₀ X h₁
  have hI21 : I₂ ≤ I₁ := weightedMeanSq_mono a N T₀ X h₁ h₂ hN hT₀ hX0 hh₁0 h12
  -- the dominating function
  set G : ℝ → ℝ := fun x => 8 * K ^ 2 + 4 * highDom a N T₀ X h₁ x + 4 * highDom a N T₀ X h₂ x with hG
  have hGint : IntegrableOn G (Ioc X (2 * X)) := by
    have hc : IntegrableOn (fun _ : ℝ => 8 * K ^ 2) (Ioc X (2 * X)) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    exact (hc.add ((integrableOn_highDom a N T₀ X h₁ hN hX hh₁0 h8' hT₀0).const_mul 4)).add
      ((integrableOn_highDom a N T₀ X h₂ hN hX hh₂0 h8 hT₀0).const_mul 4)
  have hpt : ∀ x ∈ Ioc X (2 * X), ‖windowSum a x (x + h₁) / (h₁ : ℂ) -
      windowSum a x (x + h₂) / (h₂ : ℂ)‖ ^ 2 ≤ G x := by
    intro x hx
    have hx0 : 0 < x := by linarith [hx.1]
    have hxX : X ≤ x := hx.1.le
    have hx2 : x ≤ 2 * X := hx.2
    rw [windowSum_div_eq_lowAvg_add_highAvg a N hsupp hN T₀ x h₁ hx0 hh₁0 (by linarith),
      windowSum_div_eq_lowAvg_add_highAvg a N hsupp hN T₀ x h₂ hx0 hh₂0 (by linarith)]
    set Φ₀ : ℂ := lowPart a N (h₁ / x) T₀ (Real.log x) / ((h₁ / x : ℝ) : ℂ) with hΦ₀
    have hL1 := norm_lowAvg_sub_le a N T₀ X x h₁ h₁ h₂ hN hT₀ hX hxX hh₁0 h12 hh₁0 h12 h8
    have hL2 := norm_lowAvg_sub_le a N T₀ X x h₂ h₁ h₂ hN hT₀ hX hxX hh₁0 h12 hh₂0 le_rfl h8
    rw [← hΦ₀, ← hM, ← hK] at hL1 hL2
    have hH1 := norm_sq_highAvg_le_highDom a N T₀ X h₁ x hN hX hh₁0 h8' hT₀0 hxX hx2
    have hH2 := norm_sq_highAvg_le_highDom a N T₀ X h₂ x hN hX hh₂0 h8 hT₀0 hxX hx2
    have hsplit : lowAvg a N T₀ x h₁ + highAvg a N T₀ x h₁ - (lowAvg a N T₀ x h₂ + highAvg a N T₀ x h₂) =
        ((lowAvg a N T₀ x h₁ - Φ₀) - (lowAvg a N T₀ x h₂ - Φ₀)) +
          (highAvg a N T₀ x h₁ - highAvg a N T₀ x h₂) := by ring
    rw [hsplit]
    have hn : ‖((lowAvg a N T₀ x h₁ - Φ₀) - (lowAvg a N T₀ x h₂ - Φ₀)) +
        (highAvg a N T₀ x h₁ - highAvg a N T₀ x h₂)‖ ≤
        (K + K) + (‖highAvg a N T₀ x h₁‖ + ‖highAvg a N T₀ x h₂‖) := by
      calc _ ≤ ‖(lowAvg a N T₀ x h₁ - Φ₀) - (lowAvg a N T₀ x h₂ - Φ₀)‖ +
            ‖highAvg a N T₀ x h₁ - highAvg a N T₀ x h₂‖ := norm_add_le _ _
        _ ≤ (‖lowAvg a N T₀ x h₁ - Φ₀‖ + ‖lowAvg a N T₀ x h₂ - Φ₀‖) +
            (‖highAvg a N T₀ x h₁‖ + ‖highAvg a N T₀ x h₂‖) :=
            add_le_add (norm_sub_le _ _) (norm_sub_le _ _)
        _ ≤ _ := by gcongr
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hs1 := sq_add_le_two_mul_sq_add_sq (K + K) (‖highAvg a N T₀ x h₁‖ + ‖highAvg a N T₀ x h₂‖)
    have hs2 := sq_add_le_two_mul_sq_add_sq ‖highAvg a N T₀ x h₁‖ ‖highAvg a N T₀ x h₂‖
    simp only [hG]
    nlinarith
  have hnn : ∀ x ∈ Ioc X (2 * X), 0 ≤ ‖windowSum a x (x + h₁) / (h₁ : ℂ) -
      windowSum a x (x + h₂) / (h₂ : ℂ)‖ ^ 2 := fun x _ => sq_nonneg _
  have hmono : ∫ x in Ioc X (2 * X), ‖windowSum a x (x + h₁) / (h₁ : ℂ) -
      windowSum a x (x + h₂) / (h₂ : ℂ)‖ ^ 2 ≤ ∫ x in Ioc X (2 * X), G x := by
    apply integral_mono_of_nonneg
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hnn)
    · exact hGint
    · exact (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hpt)
  have hGint' : ∫ x in Ioc X (2 * X), G x = 8 * K ^ 2 * X +
      4 * (∫ x in Ioc X (2 * X), highDom a N T₀ X h₁ x) +
      4 * (∫ x in Ioc X (2 * X), highDom a N T₀ X h₂ x) := by
    have hc : IntegrableOn (fun _ : ℝ => 8 * K ^ 2) (Ioc X (2 * X)) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    have h1int : IntegrableOn (fun x => 4 * highDom a N T₀ X h₁ x) (Ioc X (2 * X)) :=
      (integrableOn_highDom a N T₀ X h₁ hN hX hh₁0 h8' hT₀0).const_mul 4
    have h2int : IntegrableOn (fun x => 4 * highDom a N T₀ X h₂ x) (Ioc X (2 * X)) :=
      (integrableOn_highDom a N T₀ X h₂ hN hX hh₂0 h8 hT₀0).const_mul 4
    have h12int : IntegrableOn (fun x => 8 * K ^ 2 + 4 * highDom a N T₀ X h₁ x) (Ioc X (2 * X)) :=
      hc.add h1int
    simp only [hG]
    rw [integral_add h12int h2int, integral_add hc h1int,
      MeasureTheory.integral_const_mul (4 : ℝ) (highDom a N T₀ X h₁),
      MeasureTheory.integral_const_mul (4 : ℝ) (highDom a N T₀ X h₂), setIntegral_const,
      Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have hD1 := integral_highDom_le a N T₀ X h₁ hN hT₀ hX hh₁0 h8'
  have hD2 := integral_highDom_le a N T₀ X h₂ hN hT₀ hX hh₂0 h8
  rw [← hI₁] at hD1
  rw [← hI₂] at hD2
  rw [intervalIntegral.integral_of_le (by linarith)]
  have hXI : 0 ≤ X := hX0.le
  have htot : ∫ x in Ioc X (2 * X), ‖windowSum a x (x + h₁) / (h₁ : ℂ) -
      windowSum a x (x + h₂) / (h₂ : ℂ)‖ ^ 2 ≤ (8 * K ^ 2 + 9632 * I₁) * X := by
    rw [hGint'] at hmono
    have : 4 * (∫ x in Ioc X (2 * X), highDom a N T₀ X h₁ x) +
        4 * (∫ x in Ioc X (2 * X), highDom a N T₀ X h₂ x) ≤ 9632 * I₁ * X := by
      have h1 : 4 * (∫ x in Ioc X (2 * X), highDom a N T₀ X h₁ x) ≤ 4 * (1204 * X * I₁) := by
        linarith
      have h2 : 4 * (∫ x in Ioc X (2 * X), highDom a N T₀ X h₂ x) ≤ 4 * (1204 * X * I₂) := by
        linarith
      have h3 : 4 * (1204 * X * I₂) ≤ 4 * (1204 * X * I₁) := by
        have := mul_le_mul_of_nonneg_left hI21 (by positivity : (0 : ℝ) ≤ 1204 * X)
        linarith
      linear_combination h1 + h2 + h3
    linear_combination hmono + this
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hX0]
  calc _ ≤ (8 * K ^ 2 + 9632 * I₁) * X := htot
    _ ≤ 80000 * (T₀ ^ 4 * (h₂ / X) ^ 2 * M ^ 2 + I₁) * X := by
        apply mul_le_mul_of_nonneg_right _ hXI
        have hK2 : K ^ 2 = 8836 * (T₀ ^ 4 * (h₂ / X) ^ 2 * M ^ 2) := by
          rw [hK]; ring
        rw [hK2]
        have : 0 ≤ T₀ ^ 4 * (h₂ / X) ^ 2 * M ^ 2 := by positivity
        nlinarith

/-- **Lemma 14 (Parseval bound).** The variance of the short window sums is controlled by the
low-frequency term and the weighted mean square of the Dirichlet polynomial. -/
theorem variance_windowSum_le : ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → ℂ) (N : Finset ℕ) (X : ℕ) (h₁ h₂ T₀ : ℝ),
    (∀ n ∈ N, 0 < n) → 1 ≤ X → 1 ≤ h₁ → h₁ ≤ h₂ → h₂ ≤ X / 8 → 1 ≤ T₀ → (∀ n, n ∉ N → a n = 0) →
    (1 / (X : ℝ)) * ∫ x in (X : ℝ)..(2 * X), ‖windowSum a x (x + h₁) / h₁ -
        windowSum a x (x + h₂) / h₂‖ ^ 2 ≤
      C * (T₀ ^ 4 * (h₂ / X) ^ 2 * (∑ n ∈ N, ‖a n‖ / (n : ℝ)) ^ 2 +
        ∫ t in {t : ℝ | T₀ ≤ |t|}, ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I)‖ ^ 2 *
          min 1 ((X / (h₁ * t)) ^ 2)) := by
  refine ⟨80000, by norm_num, ?_⟩
  intro a N X h₁ h₂ T₀ hN hX hh₁ h12 h2X hT₀ hsupp
  have hX' : (1 : ℝ) ≤ X := by exact_mod_cast hX
  exact variance_windowSum_le_real a N X h₁ h₂ T₀ hN hX' hh₁ h12 h2X hT₀ hsupp

end Erdos1201.MR
