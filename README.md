# math_erdos_1201

A Lean 4 development of the deduction in *A note on Erdős Problem #1201*, with an additional elementary smooth-number route. The original paper is included as [erdos1201.pdf](erdos1201.pdf).

## Attribution

The original Erdős #1201 paper and mathematical deduction are by **Przemek Chojecki together with ChatGPT 5.5**. This repository is an independent Lean formalization. The finite MR auxiliary modules are based on the corrected Matomäki–Radziwiłł framework, arXiv:1501.04585v4, Section 5, equation (16).

## Current proof boundary

**The smooth-number premise has been eliminated from the new final theorem. The MR premise has not.**

```lean
theorem erdos_problem_1201_of_MR
    (hMR : QuantitativeShortIntervalInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k)
```

This theorem is in `Erdos1201/Smooth/Unconditional.lean`. That module name refers to its **smooth-number theorem**, not to the final Erdős conclusion.

The extension proves

```lean
theorem smoothMeanGapInput : SmoothMeanGapInput
```

without analytic assumptions. Its proof uses mathlib’s Chebyshev bounds and Abel summation, followed by exact finite counting of large-prime multiples. The original density deduction is proved using this one-sided estimate instead of a full smooth-number asymptotic.

**Neither `QuantitativeShortIntervalInput` nor the stronger `SmoothCountingInput` has been proved in this repository.** The latter is no longer needed by the new route. The overall Erdős theorem remains conditional on MR.

See [SMOOTH_EXTENSION.md](SMOOTH_EXTENSION.md) for the elementary proof, module map, exact verification scope, and remaining obligation.

## Original API

The original wrappers in `Erdos1201/Main.lean` are preserved unchanged:

- `Erdos1201.theorem1` takes `QuantitativeShortIntervalInput` and `SmoothCountingInput` and proves that the bad-set upper density tends to zero with block length.
- `Erdos1201.erdos_problem_1201` takes the same two inputs and proves the lower-density conclusion.

The bridges from the quantitative estimate to `ShortIntervalInput` and from the smooth counting limits to `SmoothMeanInput` remain proved. Defining an analytic input as a `Prop` is not a proof of that input.

## New API

The extension exports:

- `Erdos1201.smoothMeanGapInput`: an unconditional eventual upper bound strictly below one for the smooth-number block mean.
- `Erdos1201.erdos_problem_1201_of_MR` and `Erdos1201.theorem1_of_MR`: the density conclusions with only the quantitative MR hypothesis.
- `Erdos1201.erdos_problem_1201_of_shortInterval` and `Erdos1201.theorem1_of_shortInterval`: corresponding versions with the qualitative MR hypothesis.

## Mathematical conventions

`consecutiveProduct n h` is the product of the `h` integers `n, ..., n+h-1`. The problem parameter `k` corresponds to `h = k+1`, giving `n(n+1)...(n+k)`.

The largest-prime-factor conventions are `P⁺(1)=1` and `P⁺(0)=1`; zero is excluded from both good and bad sets. Good means `P⁺(n(n+1)...(n+k)) > n^(1-ε)`.

Counting for density is on positive integers `[1,N]`. Upper and lower density are the real limsup and liminf of normalized counts. The conclusion is a **lower-density** statement, not a claim that ordinary natural density exists.

Block averages use `[X,2X)`, whereas dyadic counting shells use `(X,2X]`. The conversion is proved with its exact endpoint correction. In the new smooth-number estimate the resulting error is `(B+1)/X`.

## Verification

The toolchain is pinned to:

- Lean `leanprover/lean4:v4.34.0-rc2`.
- Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`.

From the repository root:

```sh
lake exe cache get
lake build
lake env lean Erdos1201/Smooth/Audit.lean
```

The new modules and the root import were checked with the pinned Lean compiler. The new audit uses **`#guard_msgs`**, not just `#print axioms`: it fails if the expected axiom report changes. The audited new results depend only on `propext`, `Classical.choice`, and `Quot.sound`.

There are no new `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` constructs in the extension. A clean axiom audit checks foundational dependencies; it does not remove hypotheses explicitly present in a theorem’s type.

The original `Erdos1201/Audit.lean` remains a printed report for the original final theorem. The separate new audit is the enforcing check.

## Modules

The original `Basic`, `PrimeFactor`, `Density`, `AnalyticInputs`, `Proof`, `Quantitative`, `SmoothAsymptotics`, and `Main` modules are retained. The additional files under `Erdos1201/Smooth/` are:

| Module | Role |
| --- | --- |
| `MeanGap` | One-sided interface and deduction of the density conclusions from it. |
| `PrimeBand` | Chebyshev lower bound, Abel identity, and reciprocal-prime inequality. |
| `PowerBand` | Prime reciprocal mass between powers and asymptotic error bounds. |
| `PrimeMultiples` | Exact finite multiple counts and smooth-number deficit estimate. |
| `Unconditional` | Proved mean-gap input and the one-MR-input final wrappers. |
| `Audit` | Enforced axiom checks for the main new results. |

The `Erdos1201/MR/` modules prove finite divisor arithmetic, Ramaré decompositions, Chebyshev exceptional-set bounds, and support-removal estimates. **They do not prove the MR short-interval theorem.** No continuous mean-value, large-value, or sieve analysis needed for that theorem is claimed complete here.

## References

- K. Matomäki and M. Radziwiłł, *Multiplicative functions in short intervals*, Annals of Mathematics **183** (2016), 1015–1056; corrected arXiv:1501.04585v4.
- G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Cambridge Studies in Advanced Mathematics **46** (1995), Chapter III.5 (for the original smooth-number input, bypassed in the new route).
- Pinned mathlib files `Mathlib/NumberTheory/Chebyshev.lean` and `Mathlib/NumberTheory/AbelSummation.lean` (used in the new route).
