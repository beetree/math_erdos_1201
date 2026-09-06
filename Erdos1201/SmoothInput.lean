import Erdos1201.PrimeSums
import Erdos1201.SmoothBound

/-!
# The smooth-number input, proved

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.

The paper takes the Dickman–de Bruijn asymptotic for `Ψ(X, X^β)` as an input. The deduction
only uses the consequence that the density of `X^β`-smooth integers in `[X, 2X)` stays
bounded away from one. That consequence is proved here from Chebyshev's elementary prime
bounds: `Erdos1201.PrimeSums` gives a Mertens-type lower bound for the reciprocal sum of
primes in `(X^γ, X]`, and `Erdos1201.SmoothBound` turns it into the block-mean bound.
No analytic hypothesis remains on the smooth-number side.
-/

namespace Erdos1201

/-- The smooth-number input holds unconditionally. -/
theorem smoothUpperInput : SmoothUpperInput :=
  smoothUpperInput_of_primeSums fun _ hγ0 hγ1 => exists_sum_inv_primes_lower hγ0 hγ1

end Erdos1201
