module

public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp

@[expose] public section

set_option linter.style.setOption false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.flexible false


open scoped Complex ComplexConjugate


theorem deriv_riemannZeta_conj (s : ℂ) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  have h := congrFun (deriv_conj_conj (f := riemannZeta)) (conj s)
  rw [show conj ∘ riemannZeta ∘ conj = riemannZeta by
    ext z
    simp only [Function.comp_apply, riemannZeta_conj, Complex.conj_conj]] at h
  simpa only [Function.comp_apply, Complex.conj_conj] using h

theorem logDerivZeta_conj (s : ℂ) :
    (deriv riemannZeta / riemannZeta) (conj s) = conj ((deriv riemannZeta / riemannZeta) s) := by
  simp [deriv_riemannZeta_conj, riemannZeta_conj]
