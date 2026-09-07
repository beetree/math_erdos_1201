# math_erdos_1201

A Lean 4.34.0-rc2 formal reproduction of the proof in [A note on Erdős Problem #1201](https://www.ulam.ai/research/erdos1201.pdf), available locally as [erdos1201.pdf](erdos1201.pdf).

## Attribution

* **Original Paper and Deduction**: **The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.** Credit for the mathematical argument and proof strategy belongs entirely to them. This repository is an independent formalization in Lean 4 verifying their deduction.
* **Matomäki–Radziwiłł Auxiliary Lemmas**: The auxiliary modules under [`Erdos1201/MR/`](Erdos1201/MR.lean) formalize finite reductions supporting the Matomäki–Radziwiłł framework (based on Section 5, equation 16 of arXiv:1501.04585v4).

Preserve this attribution prominently throughout the repository, including in all documentation, module docstrings, and derived artifacts. See [AGENTS.md](AGENTS.md) for contributor and agent workflow guidelines.

## Formalization Status & Analytic Trust Boundary

The formalization now verifies the paper's deduction **unconditionally**. The one analytic input the deduction needs, the Matomäki–Radziwiłł short-interval theorem (arXiv:1501.04585v4) applied to the $X^\beta$-smooth indicator with $3/4 \le \beta < 1$, is stated as `SmoothShortIntervalInput` in [`Erdos1201/MR/Target.lean`](Erdos1201/MR/Target.lean) and proved in [`Erdos1201/MR/FinalAssembly.lean`](Erdos1201/MR/FinalAssembly.lean) (`Erdos1201.MR.smoothShortIntervalInput_holds`). The final theorems in [`Erdos1201/Final.lean`](Erdos1201/Final.lean) carry no hypothesis beyond the positivity of the parameters, and the axiom audit shows they depend only on `propext`, `Classical.choice`, and `Quot.sound`.

### The Short-Interval Input, Proved
- **Matomäki–Radziwiłł for the smooth indicator** (`SmoothShortIntervalInput`): for every $3/4 \le \beta < 1$, $\delta > 0$, $\eta > 0$, for all large $h$ and then all large $X$, the number of $n \in (X, 2X]$ at which the mean of the $X^\beta$-smooth indicator over $[n, n+h)$ differs from its mean over $[X, 2X)$ by more than $\delta$ is at most $\eta X$. The proof follows arXiv:1501.04585v4 with two changes recorded in [`BLUEPRINT.md`](BLUEPRINT.md): the polynomial is not sieved (Lemma 12 carries the unsifted count as an error term), and Halász's theorem is replaced by a twisted prime-number theorem in short ranges obtained from a Vinogradov–Korobov zero-free region, itself proved from a weak Vinogradov mean value theorem.
- The earlier conditional statements (`Erdos1201.erdos_problem_1201` with hypothesis `QuantitativeShortIntervalInput`) are kept as corollaries of the same deduction.

### Smooth-Number Analytic Input Proved Unconditionally
The paper's second external input (Dickman–de Bruijn smooth-number asymptotics) is **not needed in full**. The core deduction only requires that for each fixed $0 < \beta < 1$, the dyadic block mean of the $X^\beta$-smooth indicator over $[X, 2X)$ stays bounded away from $1$ for all large $X$ (`SmoothUpperInput`). Rather than being assumed, this upper bound is now **proved unconditionally** from Chebyshev-type elementary prime bounds across three new modules:
1. [`Erdos1201/PrimeSums.lean`](Erdos1201/PrimeSums.lean) (theorem `exists_sum_inv_primes_lower`): Proves that for any $0 < \gamma < 1$, there exists $c > 0$ such that $\sum_{X^\gamma < p \le X \text{ prime}} 1/p \ge c$ for all sufficiently large $X$. This Mertens-type lower bound is proved unconditionally from Mathlib's Chebyshev bounds `Chebyshev.theta_ge'` and `Chebyshev.theta_le_log4_mul_x` by summing over dyadic blocks $(4^k, 4^{k+1}]$.
2. [`Erdos1201/SmoothBound.lean`](Erdos1201/SmoothBound.lean) (theorem `smoothUpperInput_of_primeSums`): Proves that counting multiples of the large primes in $(X^\gamma, X]$ (at most one of which can divide any $n < 2X$ when $\gamma \ge 3/4$) shows the block mean of the $X^\beta$-smooth indicator over $[X, 2X)$ is eventually $\le 1 - c/2 < 1$.
3. [`Erdos1201/SmoothInput.lean`](Erdos1201/SmoothInput.lean) (theorem `smoothUpperInput : SmoothUpperInput`): Combines the prime-sum lower bound and the multiples-counting reduction to establish `SmoothUpperInput` unconditionally.

The original Dickman-based formulations—`SmoothCountingInput`, `SmoothMeanInput`, `SmoothCountingInput.to_smoothMeanInput` in [`Erdos1201/SmoothAsymptotics.lean`](Erdos1201/SmoothAsymptotics.lean), and `erdos1201_of_quantitative` in [`Erdos1201/Quantitative.lean`](Erdos1201/Quantitative.lean)—are retained for reference and faithfulness to the paper's original exposition, but are no longer needed by the main theorems.

### Checked Matomäki–Radziwiłł Auxiliary Lemmas (`Erdos1201.MR`)

To substantiate the mathematical foundations underlying the Matomäki–Radziwiłł theorem, four self-contained auxiliary modules have been formalized and fully verified under `Erdos1201.MR`:
- [`Erdos1201/MR/Arithmetic.lean`](Erdos1201/MR/Arithmetic.lean): Finite prime-divisor counting functions (`divisorsIn`, `omegaIn`), the corrected divisor count denominator $\text{correctedCount}(S, p, m) = \omega_S(m) + \mathbf{1}_{p \nmid m}$ from arXiv:1501.04585v4, and prime-square divisor detection.
- [`Erdos1201/MR/Ramare.lean`](Erdos1201/MR/Ramare.lean): Exact finite partition-of-unity identity over fields of characteristic zero, prime/cofactor reindexing via `cofactors`, and the three-part Ramaré decomposition separating the factorized coprime main term, the explicit prime-square correction, and the unsifted residual.
- [`Erdos1201/MR/Exceptional.lean`](Erdos1201/MR/Exceptional.lean): Finite Chebyshev inequality (`exceptional_card_le_energy`) bounding exceptional set cardinality by explicit $L^2$ energy, and the two-energy exceptional reduction (`exceptional_card_le_two_energies`).
- [`Erdos1201/MR/SupportReduction.lean`](Erdos1201/MR/SupportReduction.lean): Support-set removal (`average_restriction_error`), missing mass transport (`missingAverage_le`), and the finite discrepancy reduction (`average_discrepancy_bound` and `exceptional_card_le_restricted_energies`) with exact endpoint mass error $\bigl\lvert \lvert I\rvert/h - \lvert J\rvert/X \bigr\rvert$.
- [`Erdos1201/MR.lean`](Erdos1201/MR.lean): Aggregator module importing and re-exporting all four verified MR auxiliary modules.

> [!NOTE]
> These four modules are finite reduction scaffolding; the analytic proof of the short-interval input lives in the subdirectories described next.

### The Proof of the Short-Interval Input (`Erdos1201.MR.*`, `Erdos1201.Vendor.*`)

The plan for removing the last hypothesis is recorded in [`BLUEPRINT.md`](BLUEPRINT.md). The deduction only ever applies the short-interval input to the $X^\beta$-smooth indicator with $3/4 \le \beta < 1$, in the qualitative form stated as `SmoothShortIntervalInput` in [`Erdos1201/MR/Target.lean`](Erdos1201/MR/Target.lean); that module already proves `erdos_problem_1201_of_smoothShortInterval` and `theorem1_of_smoothShortInterval`, so the remaining task is exactly `SmoothShortIntervalInput`, a specialisation of the Matomäki–Radziwiłł theorem to this one function.

Towards it, the subdirectories `Erdos1201/MR/{Analysis,Parseval,Polynomials,Sieve,Decomposition,Vinogradov,Prop1}` (aggregated in [`Erdos1201/MR/All.lean`](Erdos1201/MR/All.lean)) contain verified building blocks following arXiv:1501.04585v4 and, for the zero-free region it needs, Vinogradov's mean value theorem after T. Tao's *254A, Notes 5*: mean value theorems for Dirichlet polynomials (Lemmas 6–7), Kusmin–Landau and van der Corput bounds, the prime-polynomial moment bounds (Lemma 8 with an elementary divisor bound in place of Shiu's theorem), the Saffari–Vaughan averaging and an $L^1 \cap L^2$ Plancherel identity for Lemma 14, Halberstam–Richert sieve upper bounds for the sifted set, the parameter system of Proposition 1, and parts of the Vinogradov–Korobov argument (curve counts, Linnik's lemma, the Hölder and Taylor reductions, the ζ bound from exponential sums, and a general zero-free-region theorem). Some of these modules prove only part of the corresponding lemma (their docstrings say which part); several statements in the Vinogradov chain are still stated relative to an explicit intermediate hypothesis (`BilinearEstimate`, the 3-4-1 inequality) that is being proved in later modules. `Erdos1201/Vendor/` holds modules copied verbatim (module paths renamed) from a separate formalization corpus with the same toolchain and Mathlib commit; they are compiled as part of this library and carry no external dependency.

> [!NOTE]
> The chain ends in [`Erdos1201/MR/FinalAssembly.lean`](Erdos1201/MR/FinalAssembly.lean) (`smoothShortIntervalInput_holds`), which [`Erdos1201/Final.lean`](Erdos1201/Final.lean) feeds into the deduction. Everything committed builds without `sorry`.

### Trust Boundary and Axiom Audit Validation
- **Lake Build Passed**: The entire repository builds cleanly with exit code 0 (`lake build` completed successfully).
- **Standard Foundation**: The verified proofs in this project use only standard Lean 4 core axioms: `propext` (propositional extensionality), `Classical.choice` (axiom of choice), and `Quot.sound` (quotient soundness).
- **No Unchecked Substitutes**: The final theorem audit (`lake env lean Erdos1201/Audit.lean`) checks the single final unconditional theorem `Erdos1201.erdos_problem_1201_unconditional`, listing only standard Lean axioms and no `sorryAx`. Auxiliary theorems and modules are compiled and verified as dependencies within the library build, but are not claimed to be individually axiom-audited by this one check. Across the codebase, there are strictly zero `sorry`, zero `admit`, zero custom `axiom` declarations, and zero `unsafe` constructs.
- **No Analytic Hypothesis Remains**: `SmoothShortIntervalInput` is proved, so the final theorems are unconditional; the conditional forms with `QuantitativeShortIntervalInput` are retained only as corollaries.

### Final Verified Theorems
The unconditional theorems, exported in [`Erdos1201/Final.lean`](Erdos1201/Final.lean) (with `erdos_problem_1201_unconditional` axiom-audited in [`Erdos1201/Audit.lean`](Erdos1201/Audit.lean)), are:
- `Erdos1201.theorem1_unconditional`:
  ```lean
  theorem theorem1_unconditional {ε : ℝ} (hε : 0 < ε) :
      Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0)
  ```
- `Erdos1201.erdos_problem_1201_unconditional`:
  ```lean
  theorem erdos_problem_1201_unconditional {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
      ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k)
  ```

The conditional wrappers in [`Erdos1201/Main.lean`](Erdos1201/Main.lean), retained as corollaries, are:
- `Erdos1201.theorem1`:
  ```lean
  theorem theorem1
      (hMR : QuantitativeShortIntervalInput)
      {ε : ℝ} (hε : 0 < ε) :
      Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0)
  ```
- `Erdos1201.erdos_problem_1201`:
  ```lean
  theorem erdos_problem_1201
      (hMR : QuantitativeShortIntervalInput)
      {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
      ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k)
  ```

Supporting bridge theorems connecting the external hypotheses to the core proof:
- [`Erdos1201.QuantitativeShortIntervalInput.to_shortIntervalInput`](Erdos1201/Quantitative.lean): Bridges `QuantitativeShortIntervalInput` to `ShortIntervalInput`.
- [`Erdos1201.smoothUpperInput`](Erdos1201/SmoothInput.lean): Unconditional proof of `SmoothUpperInput`, combining Chebyshev prime reciprocal sums and the block-mean reduction.
- [`Erdos1201.exists_sum_inv_primes_lower`](Erdos1201/PrimeSums.lean): Proves for $0 < \gamma < 1$ that $\sum_{X^\gamma < p \le X \text{ prime}} 1/p \ge c > 0$ eventually, by summing over blocks $(4^k, 4^{k+1}]$ via Chebyshev estimates.
- [`Erdos1201.smoothUpperInput_of_primeSums`](Erdos1201/SmoothBound.lean): Deduces `SmoothUpperInput` from prime reciprocal sums by counting multiples of large primes in $(X^\gamma, X]$.
- [`Erdos1201.SmoothCountingInput.to_smoothMeanInput`](Erdos1201/SmoothAsymptotics.lean): Bridges `SmoothCountingInput` to `SmoothMeanInput` (retained reference bridge).
- [`Erdos1201.SmoothMeanInput.to_smoothUpperInput`](Erdos1201/AnalyticInputs.lean): Bridges `SmoothMeanInput` to `SmoothUpperInput`.
- [`Erdos1201.erdos1201_of_quantitative`](Erdos1201/Quantitative.lean): Bridges `QuantitativeShortIntervalInput` and `SmoothMeanInput` directly (retained reference bridge).
- [`Erdos1201.bad_upperDensity_tendsto_zero`](Erdos1201/Proof.lean) and [`Erdos1201.erdos1201`](Erdos1201/Proof.lean): The core deductions from `ShortIntervalInput` and `SmoothUpperInput`.

## Mathematical Formulations and Conventions

The formalization defines:
- **Consecutive Product**: $\Pi(n, h) = \prod_{j=0}^{h-1} (n + j) = n(n+1)\dotsm(n+h-1)$, containing $h$ factors.
- **Block Length Correspondence**: The problem's $k$ consecutive integers correspond to block length $h = k + 1$ (the product $\prod_{j=0}^k (n+j)$).
- **Largest Prime Factor**: $P^+(n)$ denotes the largest prime factor of $n$, with conventions $P^+(1) = 1$ and $P^+(0) = 1$ (extended to zero by the value 1; zero is excluded from both the good and bad sets by $n \ge 1$). In [`Erdos1201/PrimeFactor.lean`](Erdos1201/PrimeFactor.lean), we formally verify semantic equivalence between $P^+(n) \le Y$ and the prime-divisor smoothness predicate `Smooth Y n` for $n \ge 1$ and $Y \ge 1$.
- **Bad and Good Sets**:
  - Bad set: $\text{badSet}(\varepsilon, h) = \{n \in \mathbb{N}_{\ge 1} \mid P^+(\Pi(n, h)) \le n^{1 - \varepsilon}\}$.
  - Good set: $\text{goodSet}(\varepsilon, k) = \{n \in \mathbb{N}_{\ge 1} \mid P^+(\Pi(n, k + 1)) > n^{1 - \varepsilon}\}$.
  - Zero is excluded from both sets.
- **Asymptotic Density**: Defined on positive integers using `limsup` (upper density $\overline{d}$) and `liminf` (lower density $\underline{d}$) of normalized counting measures in $[1, N]$. Complementation gives $\underline{d}(\text{goodSet}(\varepsilon, k)) = 1 - \overline{d}(\text{badSet}(\varepsilon, k + 1))$.
- **Dyadic Decompositions and Intervals**: Dyadic block averages use half-open intervals $[X, 2X)$; counting shells use $(X, 2X]$. Endpoint corrections between inclusive smooth counts and half-open averages are bounded and proven to vanish asymptotically.

## Reproducible Build

### Prerequisites
Install [elan](https://github.com/leanprover/elan) (Lean version manager).

The toolchain is strictly pinned to:
- Lean: `leanprover/lean4:v4.34.0-rc2` (in [`lean-toolchain`](lean-toolchain))
- Mathlib: `85e3a25e006c35636f0e53b0e9296caca2685bc0` (in [`lakefile.toml`](lakefile.toml) and [`lake-manifest.json`](lake-manifest.json))

### Build and Audit Commands
From the repository root:
```sh
# Fetch precompiled Mathlib build artifacts
lake exe cache get

# Compile the project
lake build

# Verify axiom dependencies of the final unconditional theorem
lake env lean Erdos1201/Audit.lean
```

Individual modules can also be compiled and checked directly:
```sh
lake env lean Erdos1201/Proof.lean
```

## Module Structure

| Module | Role | Status |
| --- | --- | --- |
| [`Erdos1201/Basic.lean`](Erdos1201/Basic.lean) | Largest prime factors, consecutive products, smooth indicators, complete multiplicativity, divisor bound, and the mean-gap contradiction. | Verified |
| [`Erdos1201/Density.lean`](Erdos1201/Density.lean) | Counting on positive integers, upper/lower density, dyadic partition bounds, and set complementation. | Verified |
| [`Erdos1201/AnalyticInputs.lean`](Erdos1201/AnalyticInputs.lean) | Explicit analytic interfaces (`ShortIntervalInput`, `SmoothMeanInput`, `SmoothUpperInput`) and bridge `SmoothMeanInput.to_smoothUpperInput`. | Verified |
| [`Erdos1201/PrimeSums.lean`](Erdos1201/PrimeSums.lean) | Elementary Chebyshev-based lower bounds for prime reciprocal sums $\sum_{X^\gamma < p \le X} 1/p$ across dyadic blocks (`exists_sum_inv_primes_lower`). | Verified |
| [`Erdos1201/SmoothBound.lean`](Erdos1201/SmoothBound.lean) | Multiples of large primes bound showing block mean of $X^\beta$-smooth indicator is eventually bounded below 1 (`smoothUpperInput_of_primeSums`). | Verified |
| [`Erdos1201/SmoothInput.lean`](Erdos1201/SmoothInput.lean) | Unconditional proof of `smoothUpperInput : SmoothUpperInput` combining `PrimeSums` and `SmoothBound`. | Verified |
| [`Erdos1201/Proof.lean`](Erdos1201/Proof.lean) | Scale separation, inclusion in the exceptional set, upper density limit, and the fixed-$k$ conclusion from `ShortIntervalInput` and `SmoothUpperInput`. | Verified |
| [`Erdos1201/Quantitative.lean`](Erdos1201/Quantitative.lean) | The quantitative short-interval hypothesis (`QuantitativeShortIntervalInput`) and proof of `to_shortIntervalInput`. | Verified |
| [`Erdos1201/SmoothAsymptotics.lean`](Erdos1201/SmoothAsymptotics.lean) | Smooth count $\Psi(X, X^\beta)$ definition, endpoint corrections, and proof that `SmoothCountingInput` implies `SmoothMeanInput` (retained reference bridge from the paper's Dickman input, no longer on the main path). | Verified |
| [`Erdos1201/PrimeFactor.lean`](Erdos1201/PrimeFactor.lean) | Semantic bridges relating the prime-divisor smoothness predicate (`Smooth`) to the largest-prime-factor convention (`largestPrimeFactor` / $P^+$), verifying $P^+(1) = 1$, $P^+(p) = p$, and `Smooth Y n ↔ P⁺(n) ≤ Y`. | Verified |
| [`Erdos1201/Main.lean`](Erdos1201/Main.lean) | Final wrappers `Erdos1201.theorem1` and `Erdos1201.erdos_problem_1201` taking only `QuantitativeShortIntervalInput`. | Verified |
| [`Erdos1201/MR/Arithmetic.lean`](Erdos1201/MR/Arithmetic.lean) | Finite prime-divisor counting functions (`divisorsIn`, `omegaIn`) and corrected denominator count $\omega_S(m) + \mathbf{1}_{p \nmid m}$. | Verified |
| [`Erdos1201/MR/Ramare.lean`](Erdos1201/MR/Ramare.lean) | Exact finite Ramaré partition of unity, prime/cofactor reindexing, and three-part decomposition with prime-square correction. | Verified |
| [`Erdos1201/MR/Exceptional.lean`](Erdos1201/MR/Exceptional.lean) | Finite Chebyshev $L^2$ cardinality inequality and two-energy exceptional reduction. | Verified |
| [`Erdos1201/MR/SupportReduction.lean`](Erdos1201/MR/SupportReduction.lean) | Finite support removal, triangle-inequality bounds, missing mass transport, and discrepancy reduction with endpoint error. | Verified |
| [`Erdos1201/MR.lean`](Erdos1201/MR.lean) | Aggregator module re-exporting the four Matomäki–Radziwiłł auxiliary modules under `Erdos1201.MR`. | Verified |
| [`Erdos1201/Audit.lean`](Erdos1201/Audit.lean) | Automated `#print axioms` audit asserting absence of `sorryAx` for the final conditional theorem `Erdos1201.erdos_problem_1201`. | Verified |
| [`Erdos1201.lean`](Erdos1201.lean) | Root library module re-exporting the audit, main verification results, prime-factor bridges, and MR auxiliary modules. | Verified |

> [!NOTE]
> All modules are fully verified and compile cleanly under Lean 4.34.0-rc2. Full repository verification is automated via `lake build` and `lake env lean Erdos1201/Audit.lean`.

## Analytic References

These are the external results utilized in the original paper by Przemek Chojecki together with ChatGPT 5.5:

- K. Matomäki and M. Radziwiłł, *Multiplicative functions in short intervals*, Annals of Mathematics (2) **183** (2016), 1015–1056, Theorem 1 (and corrected arXiv:1501.04585v4, 2017).
- G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Cambridge Studies in Advanced Mathematics **46** (1995), Chapter III.5.
