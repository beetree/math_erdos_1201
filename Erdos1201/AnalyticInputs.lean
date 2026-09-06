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

/-- Upper-bound form of the smooth-number input: for each fixed `0 < β < 1` the block mean
of the `X^β`-smooth indicator over `[X, 2X)` is eventually at most some constant `c < 1`.

This is all the deduction uses. It is weaker than `SmoothMeanInput` (no limit is required)
and is proved unconditionally in `Erdos1201.SmoothBound` from Chebyshev-type prime bounds. -/
def SmoothUpperInput : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 → ∃ c : ℝ, c < 1 ∧
    ∀ᶠ X : ℕ in atTop, blockMean (smoothIndicator ((X : ℝ) ^ β)) X ≤ c

/-- A limiting mean strictly below one gives an eventual upper bound strictly below one. -/
theorem SmoothMeanInput.to_smoothUpperInput (H : SmoothMeanInput) : SmoothUpperInput := by
  intro β hβ0 hβ1
  obtain ⟨r, hr, hlim⟩ := H β hβ0 hβ1
  refine ⟨(r + 1) / 2, by linarith, ?_⟩
  exact (hlim.eventually (gt_mem_nhds (by linarith : r < (r + 1) / 2))).mono fun _ h => h.le

end Erdos1201
