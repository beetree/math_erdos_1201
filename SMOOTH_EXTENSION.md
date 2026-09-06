# Smooth-side assumption elimination for Erdős #1201

## Exact status

This extension proves `Erdos1201.smoothMeanGapInput` with no analytic theorem parameters. It uses only proved mathlib results and finite counting. It then supplies that theorem to the density deduction, obtaining:

```lean
theorem erdos_problem_1201_of_MR
    (hMR : QuantitativeShortIntervalInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k)
```

Thus **the smooth-number assumption is unnecessary in the new final API**. This is not a proof of the stronger `SmoothCountingInput` asymptotic; that proposition remains unproved. `QuantitativeShortIntervalInput` also remains unproved. The repository does **not** yet contain an unconditional proof of Erdős #1201.

The original two-input theorem in `Erdos1201/Main.lean` is retained unchanged for compatibility. No assumption has been silently converted into an axiom, hidden instance, or proof placeholder.

## Attribution

The original Erdős #1201 paper and deduction are by Przemek Chojecki together with ChatGPT 5.5. This extension gives an alternative formalized smooth-number estimate sufficient for their density argument. No novelty claim is made for the underlying elementary counting argument.

## What was actually proved

`SmoothMeanGapInput` states that, for each fixed `0 < β < 1`, some `r < 1` is an eventual upper bound for the block mean of the `X^β`-smoothness indicator on `[X, 2X)`.

Unlike `SmoothMeanInput`, it does not ask that the block mean converge. Unlike `SmoothCountingInput`, it does not ask for the two Dickman counting limits. The main density proof uses only this eventual upper bound.

The six new modules are:

| File | Content |
| --- | --- |
| `Erdos1201/Smooth/MeanGap.lean` | Weakened interface, bridges from the original interfaces, and the full density deduction from the weakened interface. |
| `Erdos1201/Smooth/PrimeBand.lean` | Positive linear Chebyshev lower bound, exact Abel summation, and a reciprocal-prime mass estimate. |
| `Erdos1201/Smooth/PowerBand.lean` | Positive reciprocal mass between two fixed powers; the vanishing boundary error; the square-root-scale separation. |
| `Erdos1201/Smooth/PrimeMultiples.lean` | Exact count of multiples, at-most-one large prime divisor, finite double counting, and the exact endpoint correction. |
| `Erdos1201/Smooth/Unconditional.lean` | Unconditional mean-gap theorem and final wrappers requiring only MR. The word “Unconditional” refers to the smooth-number result, not to the final Erdős conclusion. |
| `Erdos1201/Smooth/Audit.lean` | Enforced `#guard_msgs` checks of axiom dependencies for the new main results. |

## Mathematical proof

Fix `0 < β < 1`. Choose

    α = (β + 1) / 2,  γ = (α + 1) / 2.

Then `β < α < γ < 1` and `α > 1/2`. Put `Y = X^α` and `B = X^γ`.

1. The proved Chebyshev bounds imply `θ(t) ≥ c t` eventually, for some `c > 0`.
2. Abel summation gives

       sum_(Y < p ≤ B) log(p)/p
       = θ(B)/B - θ(Y)/Y + integral_Y^B θ(t)/t² dt.

   Combining the eventual lower bound with `θ(Y) ≤ log(4) Y` yields

       log(B) sum_(Y < p ≤ B) 1/p ≥ c (log(B) - log(Y)) - log(4).

   Since `α < γ`, the prime reciprocal sum is eventually at least some fixed `d > 0`.
3. For large `X`, `Y² > 2X`. An integer in `(X, 2X]` cannot have two distinct prime divisors exceeding `Y`.
4. Each prime `p` in `(Y, B]` divides exactly `floor(2X/p) - floor(X/p)` integers in `(X, 2X]`, which is at least `X/p - 1`.
5. Double counting therefore gives a deficit of smooth integers. Converting from `(X, 2X]` to the required `[X, 2X)` yields the proved finite estimate

       blockMean(smoothIndicator(Y), X)
       ≤ 1 - sum_(Y < p ≤ B) 1/p + (B + 1)/X.

   The `+1` is the explicit endpoint correction, not a discarded term.
6. As `γ < 1`, `(X^γ + 1)/X → 0`. The smooth mean is eventually at most `1 - d/2 < 1`.
7. Since `X^β ≤ X^α`, monotonicity gives the same upper bound for the original cutoff `X^β`.

Every step above is represented by a Lean proof in the new modules. In particular, the proof does not assume an independent distribution of prime divisibility events.

## Verification

Toolchain: Lean `leanprover/lean4:v4.34.0-rc2`.
Mathlib commit: `85e3a25e006c35636f0e53b0e9296caca2685bc0`.

The new modules were checked by the actual pinned Lean executable against the pinned compiled dependencies. The audit reports exactly:

    [propext, Classical.choice, Quot.sound]

for `smoothMeanGapInput`, `erdos_problem_1201_of_MR`, `theorem1_of_MR`, and the two main prime-counting estimates. The new audit uses `#guard_msgs`, so an unexpected axiom report is a compilation failure, rather than merely printed output.

Reproduce from the repository root:

```sh
lake exe cache get
lake build
lake env lean Erdos1201/Smooth/Audit.lean
```

## Remaining obligation

An unconditional Erdős theorem still requires a proved MR input. In the original quantitative route, the exact remaining target is a theorem of type

    QuantitativeShortIntervalInput

with no additional analytic assumptions. The finite auxiliary MR modules already in the repository do not prove that target. This extension does not change their status.

The full `SmoothCountingInput` theorem also remains unformalized, but is no longer needed by the new route to the Erdős conclusion.
