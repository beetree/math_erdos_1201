# math_erdos_1201

A Lean 4.34.0-rc2 formal reproduction of the proof in [A note on Erdős Problem #1201](https://www.ulam.ai/research/erdos1201.pdf), available locally as [erdos1201.pdf](erdos1201.pdf).

## Attribution

* **Original Paper and Deduction**: **The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.** Credit for the mathematical argument and proof strategy belongs entirely to them. This repository is an independent formalization in Lean 4 verifying their deduction.
* **Matomäki–Radziwiłł Auxiliary Lemmas**: The auxiliary modules under [`Erdos1201/MR/`](Erdos1201/MR.lean) formalize finite reductions supporting the Matomäki–Radziwiłł framework (based on Section 5, equation 16 of arXiv:1501.04585v4).

Preserve this attribution prominently throughout the repository, including in all documentation, module docstrings, and derived artifacts. See [AGENTS.md](AGENTS.md) for contributor and agent workflow guidelines.

## Formalization Status & Analytic Trust Boundary

The formalization verifies the paper's deduction **conditional on two explicit analytic hypotheses**. It does **not** provide an unconditional proof of Erdős Problem #1201.

The two external inputs are deep number-theoretic results that are isolated as explicit hypothesis propositions (`Prop`), **never** introduced as Lean `axiom` declarations:
1. **Quantitative Matomäki–Radziwiłł Short-Interval Theorem** (`QuantitativeShortIntervalInput`): An explicit quantitative short-interval variance estimate for completely multiplicative functions with values in $[-1, 1]$. In [`Erdos1201/Quantitative.lean`](Erdos1201/Quantitative.lean), we formally prove that this implies the qualitative uniform interface `ShortIntervalInput` (`QuantitativeShortIntervalInput.to_shortIntervalInput`).
2. **Dickman–de Bruijn Smooth-Number Asymptotics** (`SmoothCountingInput`): The asymptotic density of smooth numbers $\Psi(X, X^\beta)/X \to r < 1$ and $\Psi(2X, X^\beta)/X \to 2r$ as natural $X \to \infty$ for fixed $0 < \beta < 1$. In [`Erdos1201/SmoothAsymptotics.lean`](Erdos1201/SmoothAsymptotics.lean), we formally prove that this implies the block-mean interface `SmoothMeanInput` (`SmoothCountingInput.to_smoothMeanInput`).

### Checked Matomäki–Radziwiłł Auxiliary Lemmas (`Erdos1201.MR`)

To substantiate the mathematical foundations underlying the Matomäki–Radziwiłł theorem, four self-contained auxiliary modules have been formalized and fully verified under `Erdos1201.MR`:
- [`Erdos1201/MR/Arithmetic.lean`](Erdos1201/MR/Arithmetic.lean): Finite prime-divisor counting functions (`divisorsIn`, `omegaIn`), the corrected divisor count denominator $\text{correctedCount}(S, p, m) = \omega_S(m) + \mathbf{1}_{p \nmid m}$ from arXiv:1501.04585v4, and prime-square divisor detection.
- [`Erdos1201/MR/Ramare.lean`](Erdos1201/MR/Ramare.lean): Exact finite partition-of-unity identity over fields of characteristic zero, prime/cofactor reindexing via `cofactors`, and the three-part Ramaré decomposition separating the factorized coprime main term, the explicit prime-square correction, and the unsifted residual.
- [`Erdos1201/MR/Exceptional.lean`](Erdos1201/MR/Exceptional.lean): Finite Chebyshev inequality (`exceptional_card_le_energy`) bounding exceptional set cardinality by explicit $L^2$ energy, and the two-energy exceptional reduction (`exceptional_card_le_two_energies`).
- [`Erdos1201/MR/SupportReduction.lean`](Erdos1201/MR/SupportReduction.lean): Support-set removal (`average_restriction_error`), missing mass transport (`missingAverage_le`), and the finite discrepancy reduction (`average_discrepancy_bound` and `exceptional_card_le_restricted_energies`) with exact endpoint mass error $|\lvert I\rvert/h - \lvert J\rvert/X|$.
- [`Erdos1201/MR.lean`](Erdos1201/MR.lean): Aggregator module importing and re-exporting all four verified MR auxiliary modules.

### Remaining Analytical Proof Gaps

> [!IMPORTANT]
> **These auxiliary lemmas DO NOT prove `QuantitativeShortIntervalInput` (or `ShortIntervalInput`), nor do they discharge the Matomäki–Radziwiłł theorem.**
> They supply only finite combinatorial, algebraic, and Chebyshev reduction scaffolding.

The remaining analytical gaps required for an unconditional proof of the Matomäki–Radziwiłł theorem comprise:
1. **Continuous Dirichlet Polynomial $L^2$ Mean-Value Theorem**: The continuous mean-square estimate along the critical line $\int_{-T}^T |\sum_{n \le N} a_n n^{-it}|^2 dt \ll (T + N) \sum_{n \le N} |a_n|^2$ (Montgomery–Vaughan large sieve inequality).
2. **Halász Pretentious Distance & Large-Value Analysis**: Pretentious distance bounds $\mathbb{D}(f, n^{it}; X)$ and frequency estimates controlling the Dirichlet polynomials on resonant frequencies.
3. **Parseval / Perron Contour Transfer**: Relaying continuous frequency integrals back to physical short spatial averages $\int_X^{2X} |\frac{1}{h} \int_0^h f(x+y) dy|^2 dx$.
4. **Fundamental Lemma of the Sieve & Parameter Optimization**: Bounding the missing mass $\rho \ll \frac{\log w}{\log z}$ and optimizing sieve scales $(w, z)$ and frequency cutoff $T = X/h$.

Because these deep analytic components are outside the formal scope, `QuantitativeShortIntervalInput` and `SmoothCountingInput` remain strictly explicit `Prop` hypotheses in the top-level theorems.

### Trust Boundary and Axiom Audit Validation
- **Lake Build Passed**: The entire repository builds cleanly with exit code 0 (`lake build` completed successfully across all 3055 jobs).
- **Standard Foundation**: The verified proofs in this project use only standard Lean 4 core axioms: `propext` (propositional extensionality), `Classical.choice` (axiom of choice), and `Quot.sound` (quotient soundness).
- **No Unchecked Substitutes**: The final theorem audit (`lake env lean Erdos1201/Audit.lean`) checks the single final conditional theorem `Erdos1201.erdos_problem_1201`, listing only standard Lean axioms and no `sorryAx`. Auxiliary theorems and modules are compiled and verified as dependencies within the library build, but are not claimed to be individually axiom-audited by this one check. Across the codebase, there are strictly zero `sorry`, zero `admit`, zero custom `axiom` declarations, and zero `unsafe` constructs.
- **Two Analytic Results Remain Explicit Hypotheses**: The results `QuantitativeShortIntervalInput` and `SmoothCountingInput` remain explicit `Prop` hypotheses in the final theorems. A clean build verifies the implication from these two analytic hypotheses to the Erdős problem conclusions, rather than an unconditional proof.

### Final Verified Wrapper Theorems
The top-level theorems, exported in [`Erdos1201/Main.lean`](Erdos1201/Main.lean) (with the final theorem `erdos_problem_1201` axiom-audited in [`Erdos1201/Audit.lean`](Erdos1201/Audit.lean)), are:
- `Erdos1201.theorem1`:
  ```lean
  theorem theorem1
      (hMR : QuantitativeShortIntervalInput) (hSmooth : SmoothCountingInput)
      {ε : ℝ} (hε : 0 < ε) :
      Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0)
  ```
- `Erdos1201.erdos_problem_1201`:
  ```lean
  theorem erdos_problem_1201
      (hMR : QuantitativeShortIntervalInput) (hSmooth : SmoothCountingInput)
      {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
      ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k)
  ```

Supporting bridge theorems connecting the external hypotheses to the core proof:
- [`Erdos1201.QuantitativeShortIntervalInput.to_shortIntervalInput`](Erdos1201/Quantitative.lean): Bridges `QuantitativeShortIntervalInput` to `ShortIntervalInput`.
- [`Erdos1201.SmoothCountingInput.to_smoothMeanInput`](Erdos1201/SmoothAsymptotics.lean): Bridges `SmoothCountingInput` to `SmoothMeanInput`.
- [`Erdos1201.bad_upperDensity_tendsto_zero`](Erdos1201/Proof.lean) and [`Erdos1201.erdos1201`](Erdos1201/Proof.lean): The core deductions from the qualitative interfaces.

## Mathematical Formulations and Conventions

The formalization defines:
- **Consecutive Product**: $\Pi(n, h) = \prod_{j=1}^h (n + j)$, containing $h$ factors.
- **Block Length Correspondence**: The problem's $k$ consecutive integers correspond to block length $h = k + 1$ (the product $\prod_{j=1}^{k+1}(n+j)$).
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

# Verify axiom dependencies of the final conditional theorem
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
| [`Erdos1201/AnalyticInputs.lean`](Erdos1201/AnalyticInputs.lean) | Explicit qualitative analytic interfaces (`ShortIntervalInput`, `SmoothMeanInput`). | Verified |
| [`Erdos1201/Proof.lean`](Erdos1201/Proof.lean) | Scale separation, inclusion in the exceptional set, upper density limit, and the fixed-$k$ conclusion. | Verified |
| [`Erdos1201/Quantitative.lean`](Erdos1201/Quantitative.lean) | The quantitative short-interval hypothesis (`QuantitativeShortIntervalInput`) and proof of `to_shortIntervalInput`. | Verified |
| [`Erdos1201/SmoothAsymptotics.lean`](Erdos1201/SmoothAsymptotics.lean) | Smooth count $\Psi(X, X^\beta)$ definition, endpoint corrections, and proof that `SmoothCountingInput` implies `SmoothMeanInput`. | Verified |
| [`Erdos1201/PrimeFactor.lean`](Erdos1201/PrimeFactor.lean) | Semantic bridges relating the prime-divisor smoothness predicate (`Smooth`) to the largest-prime-factor convention (`largestPrimeFactor` / $P^+$), verifying $P^+(1) = 1$, $P^+(p) = p$, and `Smooth Y n ↔ P⁺(n) ≤ Y`. | Verified |
| [`Erdos1201/Main.lean`](Erdos1201/Main.lean) | Final wrappers `Erdos1201.theorem1` and `Erdos1201.erdos_problem_1201` connecting quantitative and smooth inputs. | Verified |
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
