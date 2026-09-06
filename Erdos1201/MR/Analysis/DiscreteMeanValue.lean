import Mathlib
import Erdos1201.MR.Analysis.MeanValueTheorem
import Erdos1201.MR.Analysis.WellSpaced
import Erdos1201.MR.Analysis.DirichletPolyBasics
import Erdos1201.Vendor.Analysis.GallagherSobolevPointwise

open MeasureTheory intervalIntegral Set

/-!
# Discrete Mean Value Theorem for Dirichlet Polynomials at Well-Spaced Points

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes Matomäki–Radziwiłł Lemma 7 (and Iwaniec–Kowalski Theorem 9.4), bounding
the discrete mean square of a finite Dirichlet polynomial evaluated on the line $\text{Re}(s) = 1$
at any well-spaced set of points $S \subset [-T, T]$.

The proof proceeds by:
1. Differentiating the Dirichlet polynomial $F(t) = P(1 + it)$ with respect to $t$ to obtain
   another Dirichlet polynomial $F'(t)$ whose coefficients are $-i a_n \log n$.
2. Applying Gallagher's Sobolev pointwise inequality (`GallagherSobolevPointwise.pointwise_sobolev`)
   on symmetric unit intervals $[t - 1/2, t + 1/2]$.
3. Summing over the well-spaced set $S$: since distinct points differ by at least 1, the intervals
   $(t - 1/2, t + 1/2)$ are pairwise disjoint and contained in $[-T - 1, T + 1]$.
4. Applying Montgomery's continuous mean value theorem (`integral_norm_sq_dirichletPoly_le_mul`)
   to both $F$ and $F'$.
-/

namespace Erdos1201.MR

/-- The coefficient sequence of the derivative of a Dirichlet polynomial on the line Re s = 1. -/
noncomputable def derivCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  -Complex.I * (Real.log (n : ℝ) : ℂ) * a n

/-- The squared norm of the derivative coefficient is $(\log n)^2 |a_n|^2$. -/
lemma norm_derivCoeff_sq (a : ℕ → ℂ) (n : ℕ) :
    ‖derivCoeff a n‖ ^ 2 = (Real.log (n : ℝ)) ^ 2 * ‖a n‖ ^ 2 := by
  dsimp [derivCoeff]
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul]
  rw [Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- Bound on the sum of squared derivative coefficients divided by $n^2$ in terms of $\log(2N)^2$. -/
lemma sum_derivCoeff_norm_sq_div_sq_le (a : ℕ → ℂ) (N : ℕ) (_hN : 1 ≤ N) :
    (∑ n ∈ Finset.Ioc 0 N, ‖derivCoeff a n‖ ^ 2 / (n : ℝ) ^ 2) ≤
      (Real.log (2 * (N : ℝ))) ^ 2 * (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [Finset.mem_Ioc] at hn
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn.1
  have hn_ge_1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hn_le_N : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
  have h_le_2N : (n : ℝ) ≤ 2 * (N : ℝ) := by linarith
  have h_log_le : Real.log (n : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log hn_pos h_le_2N
  have h_sq_le : (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (2 * (N : ℝ))) ^ 2 := by
    have h_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn_ge_1
    nlinarith
  rw [norm_derivCoeff_sq]
  have h_div : (Real.log (n : ℝ)) ^ 2 * ‖a n‖ ^ 2 / (n : ℝ) ^ 2 =
      (Real.log (n : ℝ)) ^ 2 * (‖a n‖ ^ 2 / (n : ℝ) ^ 2) := by ring
  rw [h_div]
  exact mul_le_mul_of_nonneg_right h_sq_le (by positivity)

/-- Termwise derivative of a Dirichlet polynomial term with respect to $t$. -/
lemma hasDerivAt_dirichletPoly_term (a : ℕ → ℂ) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    HasDerivAt (fun x : ℝ => a n * (n : ℂ) ^ (-((1 : ℂ) + (x : ℝ) * Complex.I)))
      (derivCoeff a n * (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) t := by
  let c : ℂ := -Complex.I * (Real.log (n : ℝ) : ℂ)
  have h_eq (x : ℝ) : a n * (n : ℂ) ^ (-((1 : ℂ) + (x : ℝ) * Complex.I)) =
      (a n / (n : ℂ)) * Complex.exp (c * (x : ℂ)) := by
    rw [natCast_cpow_neg_one_add_mul_I_eq_exp n hn x]
    dsimp [c]
    ring_nf
  have h_eq_t : derivCoeff a n * (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I)) =
      (a n / (n : ℂ)) * (c * Complex.exp (c * (t : ℂ))) := by
    rw [natCast_cpow_neg_one_add_mul_I_eq_exp n hn t]
    dsimp [derivCoeff, c]
    ring_nf
  simp_rw [h_eq]
  rw [h_eq_t]
  have h1 : HasDerivAt (fun w : ℂ => c * w) c (t : ℂ) := by
    simpa using (hasDerivAt_id' (t : ℂ)).const_mul c
  have h2 : HasDerivAt Complex.exp (Complex.exp (c * (t : ℂ))) (c * (t : ℂ)) :=
    Complex.hasDerivAt_exp (c * (t : ℂ))
  have h3 : HasDerivAt (fun w : ℂ => Complex.exp (c * w)) (Complex.exp (c * (t : ℂ)) * c) (t : ℂ) :=
    HasDerivAt.comp (t : ℂ) h2 h1
  have h4 := HasDerivAt.comp_ofReal h3
  rw [mul_comm] at h4
  exact h4.const_mul (a n / (n : ℂ))

/-- Differentiability and derivative of a finite Dirichlet polynomial on the line Re s = 1. -/
lemma hasDerivAt_dirichletPoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    HasDerivAt (fun x : ℝ => dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + (x : ℝ) * Complex.I))
      (dirichletPoly (derivCoeff a) (Finset.Ioc 0 N) ((1 : ℂ) + (t : ℝ) * Complex.I)) t := by
  unfold dirichletPoly
  have h_sum : HasDerivAt
      (∑ n ∈ Finset.Ioc 0 N, fun x : ℝ => a n * (n : ℂ) ^ (-((1 : ℂ) + (x : ℝ) * Complex.I)))
      (∑ n ∈ Finset.Ioc 0 N, derivCoeff a n * (n : ℂ) ^ (-((1 : ℂ) + (t : ℝ) * Complex.I))) t := by
    apply HasDerivAt.sum
    intro n hn
    have hn_pos : 0 < n := (Finset.mem_Ioc.mp hn).1
    exact hasDerivAt_dirichletPoly_term a n hn_pos t
  have h_eq : (fun x : ℝ => ∑ n ∈ Finset.Ioc 0 N, a n * (n : ℂ) ^ (-((1 : ℂ) + (x : ℝ) * Complex.I))) =
      (∑ n ∈ Finset.Ioc 0 N, fun x : ℝ => a n * (n : ℂ) ^ (-((1 : ℂ) + (x : ℝ) * Complex.I))) := by
    ext x
    simp only [Finset.sum_apply]
  rw [h_eq]
  exact h_sum

/-- Differentiability of a Dirichlet polynomial at any real height. -/
lemma differentiable_dirichletPoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    DifferentiableAt ℝ (fun x : ℝ => dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + (x : ℝ) * Complex.I)) t :=
  (hasDerivAt_dirichletPoly a N t).differentiableAt

/-- Explicit derivative of a Dirichlet polynomial as another Dirichlet polynomial. -/
lemma deriv_dirichletPoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    deriv (fun x : ℝ => dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + (x : ℝ) * Complex.I)) t =
      dirichletPoly (derivCoeff a) (Finset.Ioc 0 N) ((1 : ℂ) + (t : ℝ) * Complex.I) :=
  (hasDerivAt_dirichletPoly a N t).deriv

/-- Continuity of a Dirichlet polynomial on the line Re s = 1. -/
lemma continuous_dirichletPoly (a : ℕ → ℂ) (N : ℕ) :
    Continuous (fun x : ℝ => dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + (x : ℝ) * Complex.I)) := by
  unfold dirichletPoly
  apply continuous_finsetSum
  intro n hn
  have hn_pos : 0 < n := (Finset.mem_Ioc.mp hn).1
  have h_eq (x : ℝ) : a n * (n : ℂ) ^ (-((1 : ℂ) + (x : ℝ) * Complex.I)) =
      (a n / (n : ℂ)) * Complex.exp ((-Complex.I * (Real.log (n : ℝ) : ℂ)) * (x : ℂ)) := by
    rw [natCast_cpow_neg_one_add_mul_I_eq_exp n hn_pos x]
    ring_nf
  simp_rw [h_eq]
  fun_prop

/-- Continuity of the derivative of a Dirichlet polynomial on the line Re s = 1. -/
lemma continuous_deriv_dirichletPoly (a : ℕ → ℂ) (N : ℕ) :
    Continuous (deriv (fun x : ℝ => dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + (x : ℝ) * Complex.I))) := by
  have h_eq : (deriv (fun x : ℝ => dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + (x : ℝ) * Complex.I))) =
      (fun t : ℝ => dirichletPoly (derivCoeff a) (Finset.Ioc 0 N) ((1 : ℂ) + (t : ℝ) * Complex.I)) := by
    ext t
    exact deriv_dirichletPoly a N t
  rw [h_eq]
  exact continuous_dirichletPoly (derivCoeff a) N

/-- Quadratic inequality $2uv \le c u^2 + c^{-1} v^2$ for $c > 0$. -/
lemma two_mul_le_mul_sq_add_inv_mul_sq (u v c : ℝ) (hc : 0 < c) :
    2 * u * v ≤ c * u ^ 2 + c⁻¹ * v ^ 2 := by
  have h_sq : 0 ≤ (c * u - v) ^ 2 := sq_nonneg (c * u - v)
  have h_exp : (c * u - v) ^ 2 = c ^ 2 * u ^ 2 - 2 * c * u * v + v ^ 2 := by ring
  rw [h_exp] at h_sq
  have h_pos : 0 < c := hc
  have h_c_ne : c ≠ 0 := ne_of_gt hc
  have h_step : 2 * c * u * v ≤ c ^ 2 * u ^ 2 + v ^ 2 := by linarith
  have h_div : (2 * c * u * v) / c ≤ (c ^ 2 * u ^ 2 + v ^ 2) / c :=
    (div_le_div_iff_of_pos_right h_pos).mpr h_step
  have h_lhs : (2 * c * u * v) / c = 2 * u * v := by
    calc (2 * c * u * v) / c = (2 * u * v * c) / c := by ring
    _ = 2 * u * v := mul_div_cancel_right₀ _ h_c_ne
  have h_rhs : (c ^ 2 * u ^ 2 + v ^ 2) / c = c * u ^ 2 + c⁻¹ * v ^ 2 := by
    rw [add_div, inv_eq_one_div]
    have : c ^ 2 * u ^ 2 / c = c * u ^ 2 := by
      calc c ^ 2 * u ^ 2 / c = (c * u ^ 2 * c) / c := by ring
      _ = c * u ^ 2 := mul_div_cancel_right₀ _ h_c_ne
    rw [this]
    ring_nf
  rw [h_lhs, h_rhs] at h_div
  exact h_div

/-- Gallagher's pointwise Sobolev bound combined with a quadratic split for parameter $c > 0$. -/
lemma pointwise_bound_c (f : ℝ → ℂ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (hf' : Continuous (deriv f)) (θ : ℝ) (c : ℝ) (hc : 0 < c) :
    ‖f θ‖ ^ 2 ≤ ∫ t in Set.Ioc (θ - 1/2) (θ + 1/2), ((1 + c) * ‖f t‖ ^ 2 + c⁻¹ * ‖deriv f t‖ ^ 2) := by
  have h1 : ‖f θ‖ ^ 2 ≤ 1⁻¹ * (∫ t in (θ - 1/2)..(θ + 1/2), ‖f t‖ ^ 2) +
      2 * (∫ t in (θ - 1/2)..(θ + 1/2), ‖f t‖ * ‖deriv f t‖) :=
    GallagherSobolevPointwise.pointwise_sobolev f hf hf' θ 1 zero_lt_one
  rw [inv_one, one_mul] at h1
  have h_le : θ - 1/2 ≤ θ + 1/2 := by linarith
  rw [integral_of_le h_le] at h1
  rw [integral_of_le h_le] at h1
  rw [← MeasureTheory.integral_const_mul] at h1
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have h_int1 : IntegrableOn (fun t => ‖f t‖ ^ 2) (Set.Ioc (θ - 1/2) (θ + 1/2)) :=
    (hfc.norm.pow 2).integrableOn_Ioc
  have h_int2 : IntegrableOn (fun t => 2 * (‖f t‖ * ‖deriv f t‖)) (Set.Ioc (θ - 1/2) (θ + 1/2)) :=
    (continuous_const.mul (hfc.norm.mul hf'.norm)).integrableOn_Ioc
  rw [← integral_add h_int1 h_int2] at h1
  have h_mono : (∫ t in Set.Ioc (θ - 1/2) (θ + 1/2), (‖f t‖ ^ 2 + 2 * (‖f t‖ * ‖deriv f t‖))) ≤
      ∫ t in Set.Ioc (θ - 1/2) (θ + 1/2), ((1 + c) * ‖f t‖ ^ 2 + c⁻¹ * ‖deriv f t‖ ^ 2) := by
    apply setIntegral_mono (h_int1.add h_int2)
    · exact ((continuous_const.mul (hfc.norm.pow 2)).add (continuous_const.mul (hf'.norm.pow 2))).integrableOn_Ioc
    · intro t
      dsimp only [Pi.add_apply]
      have h_quad := two_mul_le_mul_sq_add_inv_mul_sq (‖f t‖) (‖deriv f t‖) c hc
      linarith
  exact h1.trans h_mono

/-- Half-open intervals around points separated by at least 1 are disjoint. -/
lemma disjoint_Ioc_half_of_wellSpaced {s t : ℝ} (h_dist : 1 ≤ |s - t|) :
    Disjoint (Ioc (s - 1/2) (s + 1/2)) (Ioc (t - 1/2) (t + 1/2)) := by
  rw [Set.disjoint_iff]
  intro x ⟨⟨_, hxs⟩, ⟨hxt, _⟩⟩
  have hne : s ≠ t := by
    intro h
    subst h
    rw [sub_self, abs_zero] at h_dist
    linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : 0 < t - s := sub_pos.mpr hlt
    have h2 : |s - t| = t - s := by
      rw [abs_sub_comm, abs_of_pos h1]
    have h3 : s + 1 ≤ t := by linarith
    linarith
  · have h1 : 0 < s - t := sub_pos.mpr hgt
    have h2 : |s - t| = s - t := abs_of_pos h1
    have h3 : t + 1 ≤ s := by linarith
    linarith

/-- Inclusion of the unit neighborhood of $|t| \le T$ into $(-T - 1, T + 1]$. -/
lemma subset_Ioc_of_abs_le {t T : ℝ} (ht : |t| ≤ T) :
    Ioc (t - 1/2) (t + 1/2) ⊆ Ioc (-T - 1) (T + 1) := by
  intro x ⟨hx1, hx2⟩
  have ht1 : -T ≤ t := (abs_le.mp ht).1
  have ht2 : t ≤ T := (abs_le.mp ht).2
  constructor
  · linarith
  · linarith

/-- The union of unit intervals around points of $S \subset [-T, T]$ lies in $(-T - 1, T + 1]$. -/
lemma iUnion_subset_Ioc_of_mem {S : Finset ℝ} {T : ℝ} (hST : ∀ t ∈ S, |t| ≤ T) :
    (⋃ t ∈ S, Ioc (t - 1/2) (t + 1/2)) ⊆ Ioc (-T - 1) (T + 1) := by
  intro x hx
  simp only [mem_iUnion] at hx
  obtain ⟨t, ht, hxt⟩ := hx
  exact subset_Ioc_of_abs_le (hST t ht) hxt

/-- Sum of integrals over disjoint unit intervals is bounded by the global integral. -/
lemma sum_setIntegral_Ioc_half_le {S : Finset ℝ} (hS : WellSpaced S) {T : ℝ} (_hT : 1 ≤ T)
    (hST : ∀ t ∈ S, |t| ≤ T) (g : ℝ → ℝ) (hg_nonneg : ∀ x, 0 ≤ g x)
    (hg_int : IntegrableOn g (Ioc (-T - 1) (T + 1))) :
    (∑ t ∈ S, ∫ x in Ioc (t - 1/2) (t + 1/2), g x) ≤ ∫ x in (-T - 1)..(T + 1), g x := by
  have h_meas (t : ℝ) : MeasurableSet (Ioc (t - 1/2) (t + 1/2)) := measurableSet_Ioc
  have h_disj : (↑S : Set ℝ).Pairwise (Function.onFun Disjoint (fun t => Ioc (t - 1/2) (t + 1/2))) := by
    intro s hs t ht hne
    exact disjoint_Ioc_half_of_wellSpaced (hS s hs t ht hne)
  have h_sub (t : ℝ) (ht : t ∈ S) : Ioc (t - 1/2) (t + 1/2) ⊆ Ioc (-T - 1) (T + 1) :=
    subset_Ioc_of_abs_le (hST t ht)
  have h_int (t : ℝ) (ht : t ∈ S) : IntegrableOn g (Ioc (t - 1/2) (t + 1/2)) :=
    hg_int.mono_set (h_sub t ht)
  have h_biUnion := integral_biUnion_finset S (fun t _ => h_meas t) h_disj h_int
  rw [← h_biUnion]
  have h_sub_all : (⋃ t ∈ S, Ioc (t - 1/2) (t + 1/2)) ⊆ Ioc (-T - 1) (T + 1) :=
    iUnion_subset_Ioc_of_mem hST
  have h_eventually_sub : (⋃ t ∈ S, Ioc (t - 1/2) (t + 1/2)) ≤ᵐ[volume] Ioc (-T - 1) (T + 1) :=
    Filter.Eventually.of_forall (fun x hx => h_sub_all hx)
  have h_eventually_nonneg : 0 ≤ᵐ[volume.restrict (Ioc (-T - 1) (T + 1))] g :=
    Filter.Eventually.of_forall (fun x => hg_nonneg x)
  have h_mono := setIntegral_mono_set hg_int h_eventually_nonneg h_eventually_sub
  have h_le : -T - 1 ≤ T + 1 := by linarith
  rw [integral_of_le h_le]
  exact h_mono

/-- Numerical constant bound: $(2(T + 1) + 6\pi N)(1 + 2\log(2N)) \le 100(T + N)\log(2N)$. -/
lemma constant_bound (T : ℝ) (hT : 1 ≤ T) (N : ℕ) (hN : 1 ≤ N) :
    (2 * (T + 1) + 6 * Real.pi * (N : ℝ)) * (1 + 2 * Real.log (2 * (N : ℝ))) ≤
      100 * (T + (N : ℝ)) * Real.log (2 * (N : ℝ)) := by
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hlog2 : (69 / 100 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have h2N : 2 ≤ 2 * (N : ℝ) := by
    have : 1 ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlog2_le : Real.log 2 ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_le_log (by positivity) h2N
  have hlog_pos : (69 / 100 : ℝ) < Real.log (2 * (N : ℝ)) := by linarith
  have h1 : 1 ≤ (100 / 69 : ℝ) * Real.log (2 * (N : ℝ)) := by
    calc 1 = (100 / 69 : ℝ) * (69 / 100 : ℝ) := by norm_num
    _ ≤ (100 / 69 : ℝ) * Real.log (2 * (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hlog_pos) (by norm_num)
  have h_bracket2 : 1 + 2 * Real.log (2 * (N : ℝ)) ≤ ((100 / 69 : ℝ) + 2) * Real.log (2 * (N : ℝ)) := by
    calc 1 + 2 * Real.log (2 * (N : ℝ)) ≤ (100 / 69 : ℝ) * Real.log (2 * (N : ℝ)) + 2 * Real.log (2 * (N : ℝ)) := by linarith
    _ = ((100 / 69 : ℝ) + 2) * Real.log (2 * (N : ℝ)) := by ring
  have h_bracket1 : 2 * (T + 1) + 6 * Real.pi * (N : ℝ) ≤ 28 * (T + (N : ℝ)) := by
    calc 2 * (T + 1) + 6 * Real.pi * (N : ℝ) = 2 * T + 2 + 6 * Real.pi * (N : ℝ) := by ring
    _ ≤ 2 * T + 2 * T + 6 * 4 * (N : ℝ) := by
      have : 2 ≤ 2 * T := by linarith
      have : 6 * Real.pi * (N : ℝ) ≤ 6 * 4 * (N : ℝ) := by
        have : 0 ≤ (N : ℝ) := by positivity
        nlinarith
      linarith
    _ = 4 * T + 24 * (N : ℝ) := by ring
    _ ≤ 28 * (T + (N : ℝ)) := by
      have : 4 * T ≤ 28 * T := by linarith
      have : 24 * (N : ℝ) ≤ 28 * (N : ℝ) := by
        have : 0 ≤ (N : ℝ) := by positivity
        linarith
      linarith
  have h_bracket1_nonneg : 0 ≤ 2 * (T + 1) + 6 * Real.pi * (N : ℝ) := by positivity
  have h_bracket2_nonneg : 0 ≤ 1 + 2 * Real.log (2 * (N : ℝ)) := by linarith
  have h_prod := mul_le_mul h_bracket1 h_bracket2 h_bracket2_nonneg (by positivity)
  refine h_prod.trans ?_
  have h_const : 28 * ((100 / 69 : ℝ) + 2) ≤ (100 : ℝ) := by
    norm_num
  have h_log_nonneg : 0 ≤ Real.log (2 * (N : ℝ)) := by linarith
  have h_mul_nonneg : 0 ≤ (T + (N : ℝ)) * Real.log (2 * (N : ℝ)) := by positivity
  calc 28 * (T + (N : ℝ)) * (((100 / 69 : ℝ) + 2) * Real.log (2 * (N : ℝ))) =
      (28 * ((100 / 69 : ℝ) + 2)) * ((T + (N : ℝ)) * Real.log (2 * (N : ℝ))) := by ring
  _ ≤ 100 * ((T + (N : ℝ)) * Real.log (2 * (N : ℝ))) := by
    exact mul_le_mul_of_nonneg_right h_const h_mul_nonneg
  _ = 100 * (T + (N : ℝ)) * Real.log (2 * (N : ℝ)) := by ring

/-- Matomäki–Radziwiłł Lemma 7 (Iwaniec–Kowalski Theorem 9.4):
Mean value theorem for Dirichlet polynomials at well-spaced points. -/
theorem sum_wellSpaced_norm_sq_dirichletPoly_le (a : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) (T : ℝ) (hT : 1 ≤ T)
    (S : Finset ℝ) (hS : WellSpaced S) (hST : ∀ t ∈ S, |t| ≤ T) :
    (∑ t ∈ S, ‖dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + t * Complex.I)‖ ^ 2) ≤
      100 * (T + N) * Real.log (2 * N) * ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2 := by
  let F (x : ℝ) : ℂ := dirichletPoly a (Finset.Ioc 0 N) ((1 : ℂ) + (x : ℝ) * Complex.I)
  let F' (x : ℝ) : ℂ := dirichletPoly (derivCoeff a) (Finset.Ioc 0 N) ((1 : ℂ) + (x : ℝ) * Complex.I)
  have hF_diff : ∀ x, DifferentiableAt ℝ F x := differentiable_dirichletPoly a N
  have hF'_cont : Continuous (deriv F) := continuous_deriv_dirichletPoly a N
  have h_deriv_eq (x : ℝ) : deriv F x = F' x := deriv_dirichletPoly a N x
  let c : ℝ := Real.log (2 * (N : ℝ))
  have hc_pos : 0 < c := by
    have h2N : 2 ≤ 2 * (N : ℝ) := by
      have : 1 ≤ (N : ℝ) := by exact_mod_cast hN
      linarith
    have hlog2_le : Real.log 2 ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log (by positivity) h2N
    have hlog2 : 0 < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    exact lt_of_lt_of_le hlog2 hlog2_le
  let g (x : ℝ) : ℝ := (1 + c) * ‖F x‖ ^ 2 + c⁻¹ * ‖F' x‖ ^ 2
  have hg_nonneg (x : ℝ) : 0 ≤ g x := by
    dsimp [g]
    positivity
  have hF_cont : Continuous F := continuous_dirichletPoly a N
  have hF'_cont_fn : Continuous F' := continuous_dirichletPoly (derivCoeff a) N
  have hg_cont : Continuous g := by
    dsimp [g]
    exact (continuous_const.mul (hF_cont.norm.pow 2)).add (continuous_const.mul (hF'_cont_fn.norm.pow 2))
  have hg_int : IntegrableOn g (Ioc (-T - 1) (T + 1)) := hg_cont.integrableOn_Ioc
  have h_pointwise (θ : ℝ) : ‖F θ‖ ^ 2 ≤ ∫ t in Ioc (θ - 1/2) (θ + 1/2), g t := by
    have h_bound := pointwise_bound_c F hF_diff hF'_cont θ c hc_pos
    simp_rw [h_deriv_eq] at h_bound
    exact h_bound
  have h_sum_le : (∑ t ∈ S, ‖F t‖ ^ 2) ≤ ∑ t ∈ S, ∫ x in Ioc (t - 1/2) (t + 1/2), g x :=
    Finset.sum_le_sum (fun t _ => h_pointwise t)
  have h_sum_int := sum_setIntegral_Ioc_half_le hS hT hST g hg_nonneg hg_int
  have h_total_int := h_sum_le.trans h_sum_int
  let T1 : ℝ := T + 1
  have hT1_nonneg : 0 ≤ T1 := by
    dsimp [T1]
    linarith
  have h_neg_T1 : -T - 1 = -T1 := by
    dsimp [T1]
    ring
  have h_pos_T1 : T + 1 = T1 := rfl
  have h_int_g : (∫ x in (-T - 1)..(T + 1), g x) =
      (1 + c) * (∫ x in (-T1)..T1, ‖F x‖ ^ 2) + c⁻¹ * (∫ x in (-T1)..T1, ‖F' x‖ ^ 2) := by
    dsimp [g]
    rw [h_neg_T1, h_pos_T1]
    have h_intF : IntervalIntegrable (fun x => (1 + c) * ‖F x‖ ^ 2) volume (-T1) T1 :=
      (continuous_const.mul (hF_cont.norm.pow 2)).intervalIntegrable _ _
    have h_intF' : IntervalIntegrable (fun x => c⁻¹ * ‖F' x‖ ^ 2) volume (-T1) T1 :=
      (continuous_const.mul (hF'_cont_fn.norm.pow 2)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add h_intF h_intF']
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [h_int_g] at h_total_int
  let SigmaA : ℝ := ∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2 / (n : ℝ) ^ 2
  have hSigmaA_nonneg : 0 ≤ SigmaA := by
    apply Finset.sum_nonneg
    intro i _
    positivity
  have h_mv_F := integral_norm_sq_dirichletPoly_le_mul a N T1 hT1_nonneg
  have h_mv_F' := integral_norm_sq_dirichletPoly_le_mul (derivCoeff a) N T1 hT1_nonneg
  have h_sum_F'_le := sum_derivCoeff_norm_sq_div_sq_le a N hN
  have h_c_sq : (Real.log (2 * (N : ℝ))) ^ 2 = c ^ 2 := rfl
  rw [h_c_sq] at h_sum_F'_le
  have h_F'_le : (∫ x in (-T1)..T1, ‖F' x‖ ^ 2) ≤ (2 * T1 + 6 * Real.pi * N) * (c ^ 2 * SigmaA) := by
    refine h_mv_F'.trans ?_
    exact mul_le_mul_of_nonneg_left h_sum_F'_le (by positivity)
  have h_F'_c_inv : c⁻¹ * (∫ x in (-T1)..T1, ‖F' x‖ ^ 2) ≤ c * (2 * T1 + 6 * Real.pi * N) * SigmaA := by
    have h_step : c⁻¹ * (∫ x in (-T1)..T1, ‖F' x‖ ^ 2) ≤ c⁻¹ * ((2 * T1 + 6 * Real.pi * N) * (c ^ 2 * SigmaA)) :=
      mul_le_mul_of_nonneg_left h_F'_le (by positivity)
    refine h_step.trans ?_
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    have h_cancel : c⁻¹ * ((2 * T1 + 6 * Real.pi * N) * (c ^ 2 * SigmaA)) =
        c * (2 * T1 + 6 * Real.pi * N) * SigmaA := by
      calc c⁻¹ * ((2 * T1 + 6 * Real.pi * N) * (c ^ 2 * SigmaA)) =
          (2 * T1 + 6 * Real.pi * N) * (c⁻¹ * c ^ 2) * SigmaA := by ring
      _ = (2 * T1 + 6 * Real.pi * N) * (c⁻¹ * c * c) * SigmaA := by ring
      _ = (2 * T1 + 6 * Real.pi * N) * (1 * c) * SigmaA := by rw [inv_mul_cancel₀ hc_ne]
      _ = c * (2 * T1 + 6 * Real.pi * N) * SigmaA := by ring
    rw [h_cancel]
  have h_F_c : (1 + c) * (∫ x in (-T1)..T1, ‖F x‖ ^ 2) ≤ (1 + c) * (2 * T1 + 6 * Real.pi * N) * SigmaA := by
    have : (1 + c) * (∫ x in (-T1)..T1, ‖F x‖ ^ 2) ≤ (1 + c) * ((2 * T1 + 6 * Real.pi * N) * SigmaA) :=
      mul_le_mul_of_nonneg_left h_mv_F (by positivity)
    calc (1 + c) * (∫ x in (-T1)..T1, ‖F x‖ ^ 2) ≤ (1 + c) * ((2 * T1 + 6 * Real.pi * N) * SigmaA) := this
    _ = (1 + c) * (2 * T1 + 6 * Real.pi * N) * SigmaA := by ring
  have h_add_le : (1 + c) * (∫ x in (-T1)..T1, ‖F x‖ ^ 2) + c⁻¹ * (∫ x in (-T1)..T1, ‖F' x‖ ^ 2) ≤
      (2 * T1 + 6 * Real.pi * N) * (1 + 2 * c) * SigmaA := by
    calc (1 + c) * (∫ x in (-T1)..T1, ‖F x‖ ^ 2) + c⁻¹ * (∫ x in (-T1)..T1, ‖F' x‖ ^ 2) ≤
        (1 + c) * (2 * T1 + 6 * Real.pi * N) * SigmaA + c * (2 * T1 + 6 * Real.pi * N) * SigmaA :=
      add_le_add h_F_c h_F'_c_inv
    _ = (2 * T1 + 6 * Real.pi * N) * (1 + 2 * c) * SigmaA := by ring
  have h_const := constant_bound T hT N hN
  have hT1_def : T1 = T + 1 := rfl
  rw [hT1_def] at h_add_le
  have h_const_Sigma : (2 * (T + 1) + 6 * Real.pi * (N : ℝ)) * (1 + 2 * c) * SigmaA ≤
      100 * (T + (N : ℝ)) * c * SigmaA :=
    mul_le_mul_of_nonneg_right h_const hSigmaA_nonneg
  have h_chain := h_total_int.trans (h_add_le.trans h_const_Sigma)
  dsimp [c, SigmaA] at h_chain
  exact h_chain

end Erdos1201.MR
