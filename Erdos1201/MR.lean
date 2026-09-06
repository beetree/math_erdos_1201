import Erdos1201.MR.Arithmetic
import Erdos1201.MR.Ramare
import Erdos1201.MR.Exceptional
import Erdos1201.MR.SupportReduction

/-!
# Matomäki–Radziwiłł Auxiliary Modules

## Attribution

* **Original Erdős #1201 Paper & Proof**: The original paper and mathematical proof
  for Erdős Problem #1201 are by **Przemek Chojecki together with ChatGPT 5.5** (`erdos1201.pdf`).
* **Matomäki–Radziwiłł Auxiliary Lemmas**: Finite reductions and auxiliary infrastructure supporting
  the Matomäki–Radziwiłł framework, based on Section 5, equation (16) of the authors' corrected
  version of the Matomäki–Radziwiłł paper (arXiv:1501.04585v4, 15 Oct 2017).

## Analytic Trust Boundary

**These auxiliary lemmas DO NOT prove `QuantitativeShortIntervalInput`** (or the qualitative
`ShortIntervalInput`), nor do they constitute a completed formalization of the
Matomäki–Radziwiłł theorem.

They provide strictly finite combinatorial and algebraic infrastructure:
1. `Erdos1201.MR.Arithmetic`: Finite divisor-count arithmetic, the corrected denominator
   $\text{correctedCount}(S, p, m) = \omega_S(m) + \mathbf{1}_{p \nmid m}$, and prime-square
   support detection.
2. `Erdos1201.MR.Ramare`: Exact finite partition of unity over char-0 fields, cofactor
   reindexing, and three-part decomposition separating the factorized main term, the explicit
   prime-square correction, and unsifted residue.
3. `Erdos1201.MR.Exceptional`: Finite Chebyshev inequality and two-energy exceptional-set reduction.
4. `Erdos1201.MR.SupportReduction`: Support-set removal, transport of missing mass, and discrepancy
   bounds with exact endpoint error $|(\#I)/h - (\#J)/X|$.

The deep analytical components of the Matomäki–Radziwiłł theorem—including continuous
Dirichlet polynomial $L^2$ mean-value theorems, Halász pretentious large-value analysis,
Parseval/Perron contour integrals, and sieve optimization—remain unformalized.
`QuantitativeShortIntervalInput` and `SmoothCountingInput` remain explicit `Prop` hypotheses
in the top-level Erdős #1201 theorems.
-/
