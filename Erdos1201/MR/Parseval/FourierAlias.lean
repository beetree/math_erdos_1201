import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Notation for the integral Fourier transform on `ℝ`

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

The Parseval modules share the abbreviation `Real.fourierIntegral f ξ = 𝓕 f ξ`.
-/

open scoped FourierTransform

/-- Integral Fourier transform of a complex-valued function on `ℝ`: `Real.fourierIntegral f ξ = 𝓕 f ξ`. -/
noncomputable abbrev Real.fourierIntegral (f : ℝ → ℂ) (ξ : ℝ) : ℂ := 𝓕 f ξ
