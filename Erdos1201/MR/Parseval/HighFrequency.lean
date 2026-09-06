import Mathlib
import Erdos1201.MR.Parseval.PlancherelL1L2
import Erdos1201.MR.Parseval.WindowTransform
import Erdos1201.MR.Parseval.WindowKernel
import Erdos1201.MR.Analysis.DirichletPolyBasics

/-!
# High-Frequency Mean Square of the Multiplicative Window Function

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5. This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) that the deduction takes as input.

This module establishes the $L^2$ Parseval identity for the high-frequency part of the
multiplicative window function $G_u(y) = \text{windowFun } a\ N\ u\ y$.

Given the low-frequency projection `lowPart a N u T₀ y`, defined as the inverse Fourier
transform restricted to $|t| \le T_0$ (where $t = 2\pi\xi$), we show that the $L^2$ norm
of the difference $G_u - \text{lowPart}$ equals the truncated integral of the Mellin-Fourier
transform over the high frequencies $|t| > T_0$:
$$ \int_{\mathbb{R}} \|G_u(y) - \text{lowPart}(y)\|^2 dy = \frac{1}{2\pi} \int_{|t| > T_0} \|A(1+it) k_u(t)\|^2 dt. $$
-/

open MeasureTheory Real SchwartzMap Set intervalIntegral Measure
open scoped FourierTransform ComplexInnerProductSpace Pointwise

namespace Erdos1201.MR

/-- Duality formula for the inverse Fourier transform on integrable functions on `ℝ`. -/
lemma fourierInv_flip_real (f : ℝ → ℂ) (g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, (𝓕⁻ f ξ) • g ξ = ∫ x, f x • 𝓕⁻ g x := by
  have hL : (-innerₗ ℝ).flip = (-innerₗ ℝ) := by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    simp only [LinearMap.flip_apply, LinearMap.neg_apply]
    congr 1
    exact real_inner_comm x y
  have h_cont : Continuous fun p : ℝ × ℝ ↦ (-innerₗ ℝ) p.1 p.2 :=
    continuous_neg.comp (innerSL ℝ).continuous₂
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (μ := volume) (ν := volume)
    (L := -innerₗ ℝ) (f := f) (g := g) continuous_fourierChar h_cont hf hg
  rw [hL] at h
  exact h

/-- For $f \in L^1 \cap L^2$, the $L^2$ inverse Fourier transform coincides a.e. with the integral inverse Fourier transform. -/
theorem fourierInv_toLp_eq_fourierIntegralInv (f : ℝ → ℂ) (hf₁ : MeasureTheory.Integrable f) (hf₂ : MeasureTheory.MemLp f 2) :
    (𝓕⁻ (hf₂.toLp f) : MeasureTheory.Lp ℂ 2 (volume : MeasureTheory.Measure ℝ)) =ᵐ[MeasureTheory.volume] fun ξ => 𝓕⁻ f ξ := by
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  set F : ℝ → ℂ := ⇑(𝓕⁻ (hf₂.toLp f) : Lp ℂ 2 volume)
  set G : ℝ → ℂ := 𝓕⁻ f
  have hF_lp : MemLp F 2 volume := Lp.memLp _
  have hF_loc : LocallyIntegrable F volume := hF_lp.locallyIntegrable (by norm_num)
  have hG_cont : Continuous G := by
    have : G = (fun ξ => 𝓕 f (-ξ)) := by
      ext ξ
      exact fourierInv_eq_fourier_neg f ξ
    rw [this]
    have hF_cont : Continuous (𝓕 f) :=
      VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf₁
    exact hF_cont.comp continuous_neg
  have hG_loc : LocallyIntegrable G volume := hG_cont.locallyIntegrable
  have hFG_loc : LocallyIntegrable (F - G) volume := hF_loc.sub hG_loc
  have h_zero : ∀ᵐ ξ ∂volume, (F - G) ξ = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hFG_loc
    intro g g_diff g_supp
    have hg₁ : HasCompactSupport (fun x => Complex.ofRealCLM (g x)) := g_supp.comp_left rfl
    have hg₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => Complex.ofRealCLM (g x)) :=
      g_diff.continuousLinearMap_comp Complex.ofRealCLM
    set φ : SchwartzMap ℝ ℂ := hg₁.toSchwartzMap hg₂
    have h_toTemp :
        Lp.toTemperedDistribution (𝓕⁻ (hf₂.toLp f) : Lp ℂ 2 volume) φ =
        Lp.toTemperedDistribution (hf₂.toLp f) (𝓕⁻ φ) := by
      have h1 : ((𝓕⁻ (hf₂.toLp f) : Lp ℂ 2 volume) : TemperedDistribution ℝ ℂ) =
          𝓕⁻ ((hf₂.toLp f : Lp ℂ 2 volume) : TemperedDistribution ℝ ℂ) :=
        (MeasureTheory.Lp.fourierInv_toTemperedDistribution_eq (hf₂.toLp f)).symm
      change ((𝓕⁻ (hf₂.toLp f) : Lp ℂ 2 volume) : TemperedDistribution ℝ ℂ) φ = _
      rw [h1]
      exact TemperedDistribution.fourierInv_apply _ _
    have h_left : Lp.toTemperedDistribution (𝓕⁻ (hf₂.toLp f) : Lp ℂ 2 volume) φ = ∫ x, φ x • F x := by
      exact Lp.toTemperedDistribution_apply _ _
    have h_right : Lp.toTemperedDistribution (hf₂.toLp f) (𝓕⁻ φ) = ∫ x, (𝓕⁻ φ) x • f x := by
      rw [Lp.toTemperedDistribution_apply]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [hx]
    have h_flip : ∫ x, (𝓕⁻ φ) x • f x = ∫ x, φ x • G x := by
      have h_comm1 : (fun x => (𝓕⁻ φ) x • f x) = (fun x => f x • 𝓕⁻ (⇑φ) x) := by
        ext x
        simp only [fourierInv_coe]
        exact mul_comm _ _
      have h_comm2 : (fun x => (G x) • φ x) = (fun x => φ x • G x) := by
        ext x; exact mul_comm _ _
      rw [h_comm1]
      have h_int_phi : Integrable (⇑φ) := φ.integrable
      have h_fl := (fourierInv_flip_real f φ hf₁ h_int_phi).symm
      rw [h_fl]
      exact congr_arg _ h_comm2
    have h_eq : ∫ x, φ x • F x = ∫ x, φ x • G x := by
      rw [← h_left, h_toTemp, h_right, h_flip]
    have h_phi_eq : (fun x => g x • (F - G) x) = (fun x => φ x • (F x - G x)) := by
      ext x
      simp only [φ, HasCompactSupport.toSchwartzMap_toFun,
        Complex.ofRealCLM_apply, Pi.sub_apply]
      rfl
    rw [h_phi_eq]
    have h_sub_smul : (fun x => φ x • (F x - G x)) = (fun x => φ x • F x - φ x • G x) := by
      ext x; exact smul_sub _ _ _
    rw [h_sub_smul]
    have h_phi_cpt : HasCompactSupport (⇑φ) := hg₁
    have h_phi_cont : Continuous (⇑φ) := φ.continuous
    have h_int_phi_F : Integrable (fun x => φ x • F x) :=
      hF_loc.integrable_smul_left_of_hasCompactSupport h_phi_cont h_phi_cpt
    have h_int_phi_G : Integrable (fun x => φ x • G x) :=
      hG_loc.integrable_smul_left_of_hasCompactSupport h_phi_cont h_phi_cpt
    rw [integral_sub h_int_phi_F h_int_phi_G, h_eq, sub_self]
  filter_upwards [h_zero] with ξ hξ
  exact sub_eq_zero.mp hξ

/-- In $L^2(\mathbb{R})$, the inner product $\langle X, X \rangle$ equals the integral of the squared pointwise norm. -/
lemma inner_self_eq_integral_norm_sq (X : Lp ℂ 2 (volume : Measure ℝ)) :
    inner ℂ X X = ((∫ x : ℝ, ‖(X : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
  rw [L2.inner_def]
  simp only [RCLike.inner_apply]
  have : (fun x : ℝ => (X : ℝ → ℂ) x * (starRingEnd ℂ) ((X : ℝ → ℂ) x)) =
      (fun x : ℝ => ((‖(X : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ)) := by
    ext x
    exact mul_starRingEnd_eq_norm_sq ((X : ℝ → ℂ) x)
  rw [this]
  have h_int : (∫ x : ℝ, ((‖(X : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ)) =
      ((∫ x : ℝ, ‖(X : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
  exact h_int

/-- For any element $X \in L^2(\mathbb{R})$, the integral of its squared norm equals that of its Fourier transform. -/
lemma integral_norm_sq_Lp_eq_integral_norm_sq_fourier (X : Lp ℂ 2 (volume : Measure ℝ)) :
    ∫ x : ℝ, ‖(X : ℝ → ℂ) x‖ ^ 2 = ∫ x : ℝ, ‖((𝓕 X : Lp ℂ 2 volume) : ℝ → ℂ) x‖ ^ 2 := by
  have h1 := inner_self_eq_integral_norm_sq X
  have h2 := inner_self_eq_integral_norm_sq (𝓕 X)
  have h_iso := Lp.inner_fourier_eq X X
  have h_eq : ((∫ x : ℝ, ‖((𝓕 X : Lp ℂ 2 volume) : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) =
      ((∫ x : ℝ, ‖(X : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h2, h_iso, h1]
  exact (Complex.ofReal_inj.mp h_eq).symm

/-- Low-frequency part: inverse transform of 𝓕 G_u restricted to |t| ≤ T₀, written in the variable t = 2πξ. -/
noncomputable def lowPart (a : ℕ → ℂ) (N : Finset ℕ) (u T₀ : ℝ) (y : ℝ) : ℂ :=
  (1 / (2 * Real.pi)) * ∫ t in (-T₀)..T₀, dirichletPoly a N ((1 : ℂ) + t * Complex.I) * windowKernel u t * Complex.exp (t * y * Complex.I)

/-- Pointwise identity identifying `lowPart` as the inverse Fourier integral of the truncated Fourier transform. -/
lemma lowPart_eq_fourierInv (a : ℕ → ℂ) (N : Finset ℕ) (u T₀ : ℝ) (hu : 0 < u) (hT₀ : 0 ≤ T₀) (hN : ∀ n ∈ N, 0 < n) (y : ℝ) :
    let Φ := fun ξ => Real.fourierIntegral (windowFun a N u) ξ
    let s := Icc (-T₀ / (2 * Real.pi)) (T₀ / (2 * Real.pi))
    let Φ₀ := s.indicator Φ
    lowPart a N u T₀ y = 𝓕⁻ Φ₀ y := by
  intro Φ s Φ₀
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpi_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hpi
  have hpi_cne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have hcast : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast]
    exact Complex.ofReal_ne_zero.mpr hpi_ne
  have h_le : -T₀ / (2 * Real.pi) ≤ T₀ / (2 * Real.pi) := by
    rw [div_le_div_iff_of_pos_right hpi]
    linarith
  set g : ℝ → ℂ := fun t => dirichletPoly a N ((1 : ℂ) + t * Complex.I) * windowKernel u t * Complex.exp (t * y * Complex.I)
  have h_comp := intervalIntegral.smul_integral_comp_mul_left g (2 * Real.pi) (a := -T₀ / (2 * Real.pi)) (b := T₀ / (2 * Real.pi))
  have h1 : 2 * Real.pi * (-T₀ / (2 * Real.pi)) = -T₀ := mul_div_cancel₀ (-T₀) hpi_ne
  have h2 : 2 * Real.pi * (T₀ / (2 * Real.pi)) = T₀ := mul_div_cancel₀ T₀ hpi_ne
  rw [h1, h2] at h_comp
  have h_low : lowPart a N u T₀ y = ∫ ξ in (-T₀ / (2 * Real.pi))..(T₀ / (2 * Real.pi)), g (2 * Real.pi * ξ) := by
    dsimp [lowPart]
    rw [← h_comp]
    simp only [Complex.real_smul]
    have : ((1 : ℂ) / (2 * Real.pi)) * (((2 * Real.pi : ℝ) : ℂ) * ∫ ξ in -T₀ / (2 * Real.pi)..T₀ / (2 * Real.pi), g (2 * Real.pi * ξ)) =
        (((1 : ℂ) / (2 * Real.pi)) * ((2 * Real.pi : ℝ) : ℂ)) * ∫ ξ in -T₀ / (2 * Real.pi)..T₀ / (2 * Real.pi), g (2 * Real.pi * ξ) := by
      ring
    rw [this]
    have hcand : ((1 : ℂ) / (2 * Real.pi)) * ((2 * Real.pi : ℝ) : ℂ) = 1 := by
      push_cast
      exact div_mul_cancel₀ 1 hpi_cne
    rw [hcand, one_mul]
  have h_g (ξ : ℝ) : g (2 * Real.pi * ξ) = Complex.exp (↑(2 * Real.pi * (ξ * y)) * Complex.I) • Φ ξ := by
    dsimp [g, Φ]
    rw [fourierIntegral_windowFun a N u hu hN ξ]
    have hcast : (1 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I = (1 : ℂ) + (2 * Real.pi * ξ) * Complex.I := by
      push_cast; ring
    rw [hcast]
    have h_exp : Complex.exp ((2 * Real.pi * ξ : ℝ) * (y : ℂ) * Complex.I) =
        Complex.exp (↑(2 * Real.pi * (ξ * y)) * Complex.I) := by
      congr 1
      push_cast
      ring
    rw [h_exp]
    ring
  simp_rw [h_g] at h_low
  have h_four : 𝓕⁻ Φ₀ y = ∫ ξ, Complex.exp ((↑(2 * Real.pi * (ξ * y)) * Complex.I)) • Φ₀ ξ := by
    have h := fourierInv_eq' Φ₀ y
    simp only [Real.inner_apply] at h
    exact h
  rw [h_four, h_low]
  have h_set : (∫ ξ in -T₀ / (2 * Real.pi)..T₀ / (2 * Real.pi),
      Complex.exp (↑(2 * Real.pi * (ξ * y)) * Complex.I) • Φ ξ) =
      ∫ ξ in Icc (-T₀ / (2 * Real.pi)) (T₀ / (2 * Real.pi)),
        Complex.exp (↑(2 * Real.pi * (ξ * y)) * Complex.I) • Φ ξ := by
    rw [intervalIntegral.integral_of_le h_le, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [h_set]
  dsimp [Φ₀, s]
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ξ
  by_cases hξ : ξ ∈ Icc (-T₀ / (2 * Real.pi)) (T₀ / (2 * Real.pi))
  · simp [hξ]
  · simp [hξ]

/-- The $L^2$ Parseval identity for the high-frequency part of the multiplicative window function. -/
theorem integral_norm_sq_windowFun_sub_lowPart (a : ℕ → ℂ) (N : Finset ℕ) (u T₀ : ℝ) (hu : 0 < u) (hT₀ : 0 ≤ T₀) (hN : ∀ n ∈ N, 0 < n) :
    ∫ y, ‖windowFun a N u y - lowPart a N u T₀ y‖ ^ 2 =
      (1 / (2 * Real.pi)) * ∫ t in {t : ℝ | T₀ < |t|}, ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I) * windowKernel u t‖ ^ 2 := by
  set G : ℝ → ℂ := windowFun a N u
  set ℓ : ℝ → ℂ := lowPart a N u T₀
  set Φ : ℝ → ℂ := fun ξ => Real.fourierIntegral (windowFun a N u) ξ
  set s : Set ℝ := Icc (-T₀ / (2 * Real.pi)) (T₀ / (2 * Real.pi))
  set Φ₀ : ℝ → ℂ := s.indicator Φ
  have hpi : 0 < 2 * Real.pi := by positivity
  have hG₁ : Integrable G := integrable_windowFun a N u hu hN
  have hG₂ : MemLp G 2 := memLp_two_windowFun a N u hu hN
  have hℓ_eq : ∀ y, ℓ y = 𝓕⁻ Φ₀ y := fun y => lowPart_eq_fourierInv a N u T₀ hu hT₀ hN y
  have hΦ_cont : Continuous Φ :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hG₁
  have hsupp : HasCompactSupport Φ₀ :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc support_indicator_subset
  have hmeas : AEStronglyMeasurable Φ₀ volume :=
    hΦ_cont.stronglyMeasurable.indicator measurableSet_Icc |>.aestronglyMeasurable
  set C : ℝ := ∫ y, ‖G y‖
  have hC_nonneg : 0 ≤ C := integral_nonneg (fun y => norm_nonneg _)
  have hbound : ∀ᵐ ξ ∂volume, ‖Φ₀ ξ‖ ≤ C := by
    apply Filter.Eventually.of_forall
    intro ξ
    dsimp [Φ₀]
    rw [indicator_apply]
    split_ifs with hξ
    · exact VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ) G ξ
    · rw [norm_zero]
      exact hC_nonneg
  have hΦ₀_mem (p : ENNReal) : MemLp Φ₀ p volume := HasCompactSupport.memLp_of_bound hsupp hmeas C hbound
  have hΦ₀₁ : Integrable Φ₀ := memLp_one_iff_integrable.mp (hΦ₀_mem 1)
  have hΦ₀₂ : MemLp Φ₀ 2 := hΦ₀_mem 2
  have h_fourierInv := fourierInv_toLp_eq_fourierIntegralInv Φ₀ hΦ₀₁ hΦ₀₂
  have hℓ_ae : (𝓕⁻ (hΦ₀₂.toLp Φ₀) : Lp ℂ 2 volume) =ᵐ[volume] ℓ := by
    filter_upwards [h_fourierInv] with y hy
    rw [hy, ← hℓ_eq y]
  have hℓ₂ : MemLp ℓ 2 := (Lp.memLp (𝓕⁻ (hΦ₀₂.toLp Φ₀))).ae_eq hℓ_ae
  have hℓ_toLp : hℓ₂.toLp ℓ = 𝓕⁻ (hΦ₀₂.toLp Φ₀) := by
    apply Lp.ext
    filter_upwards [hℓ₂.coeFn_toLp, hℓ_ae] with y h1 h2
    rw [h1, h2]
  have h_four_ℓ : 𝓕 (hℓ₂.toLp ℓ) = hΦ₀₂.toLp Φ₀ := by
    rw [hℓ_toLp]
    exact (Lp.fourierTransformₗᵢ ℝ ℂ).apply_symm_apply (hΦ₀₂.toLp Φ₀)
  have h_four_G := fourier_toLp_eq_fourierIntegral G hG₁ hG₂
  have hdiff₂ : MemLp (G - ℓ) 2 := hG₂.sub hℓ₂
  set X : Lp ℂ 2 volume := hdiff₂.toLp (G - ℓ)
  have hX_eq : X = hG₂.toLp G - hℓ₂.toLp ℓ := by
    apply Lp.ext
    filter_upwards [hdiff₂.coeFn_toLp, hG₂.coeFn_toLp, hℓ₂.coeFn_toLp,
      Lp.coeFn_sub (hG₂.toLp G) (hℓ₂.toLp ℓ)] with y h1 h2 h3 h4
    rw [h1, h4, Pi.sub_apply, Pi.sub_apply, h2, h3]
  have h_norm := integral_norm_sq_Lp_eq_integral_norm_sq_fourier X
  have h_lhs : (∫ y, ‖(X : ℝ → ℂ) y‖ ^ 2) = ∫ y, ‖G y - ℓ y‖ ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hdiff₂.coeFn_toLp] with y hy
    rw [hy, Pi.sub_apply]
  have h_four_X : (𝓕 X : Lp ℂ 2 volume) = 𝓕 (hG₂.toLp G) - hΦ₀₂.toLp Φ₀ := by
    rw [hX_eq]
    have h_sub : 𝓕 (hG₂.toLp G - hℓ₂.toLp ℓ) = 𝓕 (hG₂.toLp G) - 𝓕 (hℓ₂.toLp ℓ) :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).map_sub (hG₂.toLp G) (hℓ₂.toLp ℓ)
    rw [h_sub, h_four_ℓ]
  have h_four_X_ae : ((𝓕 X : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] fun ξ => Φ ξ - Φ₀ ξ := by
    rw [h_four_X]
    filter_upwards [Lp.coeFn_sub (𝓕 (hG₂.toLp G)) (hΦ₀₂.toLp Φ₀), h_four_G, hΦ₀₂.coeFn_toLp] with ξ h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
  have h_rhs : (∫ ξ, ‖((𝓕 X : Lp ℂ 2 volume) : ℝ → ℂ) ξ‖ ^ 2) = ∫ ξ, ‖Φ ξ - Φ₀ ξ‖ ^ 2 := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [h_four_X_ae] with ξ hξ
    rw [hξ]
  have h_mid : ∫ y, ‖G y - ℓ y‖ ^ 2 = ∫ ξ, ‖Φ ξ - Φ₀ ξ‖ ^ 2 := by
    rw [← h_lhs, h_norm, h_rhs]
  rw [h_mid]
  have hs_comp : sᶜ = {ξ : ℝ | T₀ < |2 * Real.pi * ξ|} := by
    ext ξ
    simp only [s, mem_compl_iff, mem_Icc]
    rw [neg_div, ← abs_le, not_le]
    rw [div_lt_iff₀ hpi]
    have : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
      rw [abs_mul, abs_of_pos hpi]
    rw [mul_comm, ← this]
    rfl
  have h_pw (ξ : ℝ) : ‖Φ ξ - Φ₀ ξ‖ ^ 2 = (sᶜ).indicator (fun ξ => ‖Φ ξ‖ ^ 2) ξ := by
    dsimp [Φ₀]
    by_cases hξ : ξ ∈ s
    · simp [hξ]
    · simp [hξ]
  simp_rw [h_pw]
  have hmeas_s : MeasurableSet sᶜ := measurableSet_Icc.compl
  rw [MeasureTheory.integral_indicator hmeas_s, hs_comp]
  set S : Set ℝ := {t : ℝ | T₀ < |t|}
  set f_t : ℝ → ℝ := fun t => ‖dirichletPoly a N ((1 : ℂ) + t * Complex.I) * windowKernel u t‖ ^ 2
  have h_comp_f : (fun ξ => ‖Φ ξ‖ ^ 2) = (fun ξ => f_t (2 * Real.pi * ξ)) := by
    ext ξ
    dsimp [Φ, f_t]
    rw [fourierIntegral_windowFun a N u hu hN ξ]
    have hcast : (1 : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I = (1 : ℂ) + (2 * Real.pi * ξ) * Complex.I := by
      push_cast; ring
    rw [hcast]
  rw [h_comp_f]
  have h_subst := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure ℝ)) (f := f_t) (R := 2 * Real.pi) {ξ : ℝ | T₀ < |2 * Real.pi * ξ|} hpi
  simp only [smul_eq_mul] at h_subst
  have h_fin : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
  rw [h_fin, pow_one] at h_subst
  have h_smul_s : (2 * Real.pi) • {ξ : ℝ | T₀ < |2 * Real.pi * ξ|} = S := by
    ext t
    simp only [mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hpi), smul_eq_mul]
    dsimp [S]
    have : 2 * Real.pi * ((2 * Real.pi)⁻¹ * t) = t := mul_inv_cancel_left₀ (ne_of_gt hpi) t
    rw [this]
  rw [h_smul_s] at h_subst
  rw [h_subst, one_div]

end Erdos1201.MR
