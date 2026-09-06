import Erdos1201.Density

/-!
# Explicit analytic hypotheses

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.

These propositions are interfaces, NOT proved theorems or new axioms. The final
results take proofs of them as arguments. They isolate qualitative consequences
of the two analytic results cited in the paper; those consequences, and the
underlying analytic results, are not yet formalized in this repository.
-/

open Filter
open scoped Topology

namespace Erdos1201

/-- Qualitative uniform consequence of Matomäki–Radziwiłł, Theorem 1.

The thresholds for `h` and `X` are independent of `f`. This permits `f = f_X`.
The restriction to completely multiplicative functions is sufficient here.
The exceptional interval is `(X, 2X]`; changing the endpoints costs at most two
points in the quantitative theorem. -/
def ShortIntervalInput : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
    ∀ᶠ h : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      ∀ f : ℕ → ℝ, CompletelyMultiplicative f → (∀ n, f n ∈ Set.Icc (-1 : ℝ) 1) →
        (intervalCount {n | δ < |shortMean f h n - blockMean f X|} X (2 * X) : ℝ)
          ≤ η * X

/-- Consequence of the Dickman–de Bruijn estimate for each fixed `0 < β < 1`.

Only the existence of a limiting mean strictly below one is needed. This avoids
introducing an unformalized definition of the Dickman function. All sums use
`[X, 2X)` consistently; the endpoint corrections are absorbed in convergence. -/
def SmoothMeanInput : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 → ∃ r : ℝ, r < 1 ∧
    Tendsto (fun X : ℕ => blockMean (smoothIndicator ((X : ℝ) ^ β)) X) atTop (𝓝 r)

end Erdos1201
