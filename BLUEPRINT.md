# Blueprint: making the Erdős #1201 proof unconditional

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5. The
deduction is formalized in `Erdos1201/`. The only remaining hypothesis is
`QuantitativeShortIntervalInput` (their Theorem 2, the Matomäki–Radziwiłł short-interval
theorem). This document is the plan of record for proving what the deduction needs.

## Target

The deduction (`Erdos1201/Proof.lean`) applies the short-interval input only to the
completely multiplicative function `f_X = smoothIndicator (X^β)` with `3/4 ≤ β < 1`, and
only in the qualitative form `ShortIntervalInput` (for every `δ, η > 0`, for all large `h`,
for all large `X`, the number of `n ∈ (X, 2X]` with
`|shortMean f_X h n − blockMean f_X X| > δ` is at most `η X`). We prove exactly that:

```
theorem smoothShortIntervalInput : SmoothShortIntervalInput     -- stated in MR/Target.lean, not yet proved
```

and then `Proof.lean` needs no analytic hypothesis at all. We do not prove the general
Matomäki–Radziwiłł theorem or its quantitative rates.

## Mathematical route (Matomäki–Radziwiłł, arXiv:1501.04585v4, specialised)

Write `F(s) = Σ_{X ≤ n ≤ 2X, n ∈ S} f_X(n) n^{-s}` with `S` the sifted set of Section 2 of the
paper (integers with a prime factor in every range `[P_j, Q_j]`, `j ≤ J`).

1. **Parseval (Lemma 14).** Variance of short averages ≪ `∫_{T₀}^{X/h} |F(1+it)|² dt` +
   tail + `(log X)^{-2/15}`. Proved via the Saffari–Vaughan averaging and an L² identity
   for finite sums of scaled interval indicators (no Perron formula: Plancherel for pairs
   of L¹∩L² step functions, obtained by approximation from Mathlib's Schwartz-space
   Plancherel).
2. **Medium vs long averages (Lemma 4, elementary for `f_X`).** For `y = X/(log X)^{1/5}`
   the average over `(x, x+y]` equals the block mean up to `O(π(2X)/y)`, because
   `1 − f_X` is the indicator of "has a prime factor > X^β" and each such prime is the
   unique one (β > 1/2). Sieve upper bounds handle the restriction to `S`.
3. **Proposition 1** (`∫_{T₀}^{T} |F(1+it)|² dt` small): the paper's argument verbatim, with
   the Ramaré identity (already in `Erdos1201/MR/Ramare.lean`), Lemma 12 (decomposition
   `F ≈ Σ_v Q_{v,H} R_{v,H}`), Lemma 13 (moments, with an elementary divisor bound in
   place of Shiu), Lemma 8 (moments of prime polynomials) and the sets `T_j`, `U`.
4. **Mean value theorems.** Lemma 6 (Montgomery, `T + O(N)`) from the vendored
   Montgomery–Vaughan Hilbert inequality; Lemma 7 (well-spaced points) from Lemma 6 and a
   Sobolev inequality; Lemma 9 (Halász–Montgomery for integers) from duality and the
   van der Corput bound for `Σ n^{it}`.
5. **Pointwise bounds on `R` (Lemma 3, specialised).** For `f_X` no Halász theorem is
   needed: the "1" part of `f_X` gives sifted sums of `n^{-1-it}` (Möbius over the sifting
   primes, van der Corput, Rankin for smooth tails); the "prime factor > X^β" part
   gives prime sums `Σ_{p ~ P} p^{-1-it}` with `P ≥ X^{3/4}` at heights up to `X`, which need
   the zero-free region below.
6. **Halász inequality for primes (Lemma 11)** and **Lemma 2**: both need a zero-free
   region `ζ(σ+it) ≠ 0` for `σ ≥ 1 − c/(log t)^θ` with some `θ < 1`, and the matching bound
   for `ζ'/ζ`. Any `θ < 1` suffices after re-tuning the parameters `P, Q, H` of Section 8.3
   (take `P = exp((log X)^{1−κ})` with `κ < (1−θ)/2`). The classical region (`θ = 1`) does
   not suffice: at heights comparable to a power of `X` it saves only a constant factor.
7. **Sieve.** Upper bound for integers with no prime factor in `[P, Q]` (Selberg sieve,
   vendored) and the fundamental-lemma-free inclusion–exclusion (Lemma 5).

## The critical path: a Vinogradov-type zero-free region

Neither Mathlib nor solve-math has a region with `θ < 1`. Plan (Vaughan, *The
Hardy–Littlewood method*, Ch. 5; Ivić, *The Riemann zeta-function*, Ch. 6):

- V1. Vinogradov's mean value theorem, weak form: `J_{s,k}(P) ≪ P^{2s − k(k+1)/2 + η_s}`
  with `η_s → 0` polynomially in `s/k²` (Vaughan Thm 5.1).
- V2. Weyl-sum bound: `|Σ_{n ~ N} n^{it}| ≪ N^{1 − c/k²}` for `N^k ≍ t` (Vaughan Thm 5.3 /
  Ivić Thm 6.2).
- V3. `|ζ(σ+it)| ≪ t^{A(1−σ)^{3/2}} (log t)^{2/3}` near `σ = 1` (Ivić Thm 6.3).
- V4. Zero-free region `σ ≥ 1 − c/(log t)^{2/3} (log log t)^{1/3}` and `ζ'/ζ` bounds, by
  re-running the vendored classical argument (`Erdos1201/Vendor/.../ZetaZeroFreeRegion`)
  with the bound V3 in place of `|ζ| ≪ log t`.
- V5. Prime sums at large heights: `Σ_{p ~ P} p^{-it} ≪ P exp(−c (log P)^{1/3−ε})` for
  `|t| ≤ P^A`, via the vendored truncated Perron formula and the region V4.

## Revised route for the smooth indicator (2026-09-06, evening)

Only `f_X = smoothIndicator (X^β)`, `3/4 ≤ β < 1`, matters. Write `f_X = 1 − 1_{P⁺(n) > X^β}`;
since `(X^β)^2 > 2X` every `n ≤ 2X` has at most one prime factor above `X^β`.

- Halász's theorem (paper Lemmas 2–4) is NOT needed. The pointwise bounds on the
  `R_{v,H}` polynomials in the U-part reduce, after the Ramaré identity on a large prime
  factor and Rankin's bound for smooth numbers, to one analytic input:

  (★) twisted prime sums: for `A ≥ exp((log X)^{3/4})`, `A < B ≤ 2A`, `1 ≤ |u| ≤ X^2`,
      `∑_{A<p≤B} p^{-1-iu} = O(1/(|u| log A)) + O(exp(−(log X)^{1/20}))`.

  (★) also gives Lemma 11 (Halász for primes) by the duality argument of the paper, with
  the main terms `P/|t−t'|` summed over well-spaced points (a `log T` loss that the
  parameters absorb). Lemma 9 (Halász–Montgomery for integers) is `HalaszMontgomery`.
- (★) comes from the vendored smoothed-Chebyshev contour argument (`Vendor/.../PNT/MediumPNT.lean`)
  re-run for `∑ Λ(n) n^{-iu} Smooth1(n/A)`: same contour, the Mellin factor evaluated at
  `s − iu`, residue `A^{1−iu} 𝓜(Smooth1)(1−iu)`, and the ζ'/ζ bound in the
  Vinogradov–Korobov region (width `c/((log t)^{2/3} log log t)`) in place of the
  vendored `(log t)^{-9}` region.
- Everything else follows the paper: Proposition 1 with the sets `T_j` (E_1, E_j bounds,
  Lemma 12 = Boundary + Square + assembly, Lemma 13 moments, Lemma 8 large values), the
  U-part with `T_S`/`T_L` and Lemma 11, Lemma 14 (Parseval; `WindowEnergy` gives the
  exact two-window identity), the elementary Lipschitz step `MediumAverage`, the sieve
  removal of `S`, and the Chebyshev-count reduction `ShortIntervalAssembly`
  (`smoothShortIntervalInput_of_restricted_shortMeanEnergies`).

## Infrastructure

- `Erdos1201/Vendor/`: 135 modules copied from solve-math (same toolchain and Mathlib),
  module paths renamed; no dependency on solve-math.
- `Erdos1201/MR/`: new modules, one per task; each task owns exactly one file.
- Swarm (local, not committed): `tmp/agy/mr/scheduler2.py` keeps up to ten `agy` workers running from
  `tmp/agy/mr/tasks.json` (dependency-ordered). Reports: `tmp/agy/reports/mr_*.md`.

## Status

See the README section "Work in Progress" for the list of verified building blocks; `Erdos1201/MR/All.lean` aggregates every verified module. Nothing in this
plan is claimed as proved until it builds without `sorry` and passes the axiom audit.
