import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Erdos1201.MR.Parseval.FourierAlias

/-!
# Plancherel's Theorem for L¹ ∩ L² Functions on ℝ

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

This module formalizes Plancherel's theorem for functions in L¹ ∩ L² on ℝ, derived from
Mathlib's L² Fourier isometry (`MeasureTheory.Lp.fourierTransformₗᵢ`).

The key steps are:
1. Identify the L² Fourier transform with the integral Fourier transform almost everywhere
   via tempered distributions and testing against compactly supported smooth functions.
2. Deduce the polarised Parseval identity for two functions in L¹ ∩ L².
3. Specialize to the L² isometry (Plancherel's formula) in integral form.
-/

open MeasureTheory Real SchwartzMap
open scoped FourierTransform ComplexInnerProductSpace


namespace Erdos1201.MR

/-- Duality (flip) formula for the Fourier transform of integrable functions on `ℝ`. -/
lemma fourier_flip_real (f : ℝ → ℂ) (g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, (𝓕 f ξ) • g ξ = ∫ x, f x • 𝓕 g x := by
  have hL : (innerₗ ℝ).flip = (innerₗ ℝ) := by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    simp only [LinearMap.flip_apply]
    exact real_inner_comm x y
  have h_cont : Continuous fun p : ℝ × ℝ ↦ innerₗ ℝ p.1 p.2 := (innerSL ℝ).continuous₂
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (μ := volume) (ν := volume)
    (L := innerₗ ℝ) (f := f) (g := g) continuous_fourierChar h_cont hf hg
  rw [hL] at h
  exact h

/-- For f ∈ L¹ ∩ L², the L² Fourier transform of (the class of) f is a.e. the integral Fourier transform. -/
theorem fourier_toLp_eq_fourierIntegral (f : ℝ → ℂ) (hf₁ : MeasureTheory.Integrable f) (hf₂ : MeasureTheory.MemLp f 2) :
    (𝓕 (hf₂.toLp f) : MeasureTheory.Lp ℂ 2 (volume : MeasureTheory.Measure ℝ)) =ᵐ[MeasureTheory.volume] fun ξ => Real.fourierIntegral f ξ := by
  have : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  set F : ℝ → ℂ := ⇑(𝓕 (hf₂.toLp f) : Lp ℂ 2 volume)
  set G : ℝ → ℂ := Real.fourierIntegral f
  have hF_lp : MemLp F 2 volume := Lp.memLp _
  have hF_loc : LocallyIntegrable F volume := hF_lp.locallyIntegrable (by norm_num)
  have hG_cont : Continuous G := by
    change Continuous (𝓕 f)
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf₁
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
        Lp.toTemperedDistribution (𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) φ =
        Lp.toTemperedDistribution (hf₂.toLp f) (𝓕 φ) := by
      have h1 : ((𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) : TemperedDistribution ℝ ℂ) =
          𝓕 ((hf₂.toLp f : Lp ℂ 2 volume) : TemperedDistribution ℝ ℂ) :=
        (MeasureTheory.Lp.fourier_toTemperedDistribution_eq (hf₂.toLp f)).symm
      change ((𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) : TemperedDistribution ℝ ℂ) φ = _
      rw [h1]
      exact TemperedDistribution.fourier_apply _ _
    have h_left : Lp.toTemperedDistribution (𝓕 (hf₂.toLp f) : Lp ℂ 2 volume) φ = ∫ x, φ x • F x := by
      exact Lp.toTemperedDistribution_apply _ _
    have h_right : Lp.toTemperedDistribution (hf₂.toLp f) (𝓕 φ) = ∫ x, (𝓕 φ) x • f x := by
      rw [Lp.toTemperedDistribution_apply]
      apply integral_congr_ae
      filter_upwards [hf₂.coeFn_toLp] with x hx
      rw [hx]
    have h_flip : ∫ x, (𝓕 φ) x • f x = ∫ x, φ x • G x := by
      have h_comm1 : (fun x => (𝓕 φ) x • f x) = (fun x => f x • 𝓕 (⇑φ) x) := by
        ext x
        simp only [fourier_coe]
        exact mul_comm _ _
      have h_comm2 : (fun x => (G x) • φ x) = (fun x => φ x • G x) := by
        ext x; exact mul_comm _ _
      rw [h_comm1]
      have h_int_phi : Integrable (⇑φ) := φ.integrable
      have h_fl := (fourier_flip_real f φ hf₁ h_int_phi).symm
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

/-- Polarised form for two functions in L¹ ∩ L². -/
theorem integral_fourierIntegral_mul_conj (f g : ℝ → ℂ) (hf₁ : MeasureTheory.Integrable f) (hf₂ : MeasureTheory.MemLp f 2)
    (hg₁ : MeasureTheory.Integrable g) (hg₂ : MeasureTheory.MemLp g 2) :
    ∫ ξ, Real.fourierIntegral f ξ * (starRingEnd ℂ) (Real.fourierIntegral g ξ) = ∫ x, f x * (starRingEnd ℂ) (g x) := by
  set F : Lp ℂ 2 volume := hf₂.toLp f
  set G : Lp ℂ 2 volume := hg₂.toLp g
  have h_inner : inner ℂ G F = inner ℂ (𝓕 G) (𝓕 F) := (Lp.inner_fourier_eq G F).symm
  have hGF : inner ℂ G F = ∫ x, f x * (starRingEnd ℂ) (g x) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply]
    apply integral_congr_ae
    filter_upwards [hf₂.coeFn_toLp, hg₂.coeFn_toLp] with x hx hy
    rw [hx, hy]
  have hFG_four : inner ℂ (𝓕 G) (𝓕 F) =
      ∫ ξ, Real.fourierIntegral f ξ * (starRingEnd ℂ) (Real.fourierIntegral g ξ) := by
    rw [L2.inner_def]
    simp only [RCLike.inner_apply]
    apply integral_congr_ae
    filter_upwards [fourier_toLp_eq_fourierIntegral f hf₁ hf₂,
                    fourier_toLp_eq_fourierIntegral g hg₁ hg₂] with ξ hξ hη
    rw [hξ, hη]
  rw [← hGF, h_inner, hFG_four]

/-- The product of a complex number with its complex conjugate equals the square of its norm. -/
lemma mul_starRingEnd_eq_norm_sq (z : ℂ) : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Plancherel for L¹ ∩ L²: ∫ ‖𝓕 f‖² = ∫ ‖f‖². -/
theorem integral_norm_sq_fourierIntegral (f : ℝ → ℂ) (hf₁ : MeasureTheory.Integrable f) (hf₂ : MeasureTheory.MemLp f 2) :
    ∫ ξ, ‖Real.fourierIntegral f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have h := integral_fourierIntegral_mul_conj f f hf₁ hf₂ hf₁ hf₂
  have h_left : (fun ξ => Real.fourierIntegral f ξ * (starRingEnd ℂ) (Real.fourierIntegral f ξ)) =
      (fun ξ => ((‖Real.fourierIntegral f ξ‖ ^ 2 : ℝ) : ℂ)) := by
    ext ξ; exact mul_starRingEnd_eq_norm_sq _
  have h_right : (fun x => f x * (starRingEnd ℂ) (f x)) =
      (fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ)) := by
    ext x; exact mul_starRingEnd_eq_norm_sq _
  rw [h_left, h_right] at h
  have h_int_left : (∫ ξ, ((‖Real.fourierIntegral f ξ‖ ^ 2 : ℝ) : ℂ)) =
      ((∫ ξ, ‖Real.fourierIntegral f ξ‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
  have h_int_right : (∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ)) =
      ((∫ x, ‖f x‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
  rw [h_int_left, h_int_right] at h
  exact Complex.ofReal_inj.mp h

end Erdos1201.MR
