# Contributor and Agent Instructions

## Attribution

The original paper and proof are by **Przemek Chojecki together with ChatGPT 5.5**.
This repository formalizes their work in Lean 4. Preserve this credit prominently
in `README.md`, in module docstrings for every proof file, and in all derived
explanations or reports. Never present the original mathematical argument as our own.
The source paper is `erdos1201.pdf`, downloaded from
https://www.ulam.ai/research/erdos1201.pdf.

Matomäki–Radziwiłł (MR) auxiliary code needs no provenance attribution to the
user or private `expert_advice` materials; describe these neutrally as
Matomäki–Radziwiłł auxiliary lemmas or finite reductions. Mathematical citations
to Matomäki and Radziwiłł (and arXiv:1501.04585v4) and original-paper attribution
to Przemek Chojecki together with ChatGPT 5.5 must remain.

## Lean Workflow and Environment

- **Pinned toolchain**: Lean `leanprover/lean4:v4.34.0-rc2` (specified in `lean-toolchain`).
- **Pinned dependencies**: Mathlib git commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`
  (locked in `lakefile.toml` and `lake-manifest.json`).
- **Reproducible build commands**:
  - `lake exe cache get` (fetches precompiled Mathlib oleans)
  - `lake build` (compiles the project)
  - `lake env lean <file>` (verifies individual Lean source files)
- **Axiom audit**: The default build and audit verify that no axioms beyond standard
  Lean foundation (`propext`, `Classical.choice`, `Quot.sound`) are introduced.

## Concurrency, Worker Roles, and Swarm Orchestration

- **Worker pool**: Up to 10 concurrent Gemini workers (`gemini-3.8-flash-high`), explicitly
  requested by the user.
- **Role separation**:
  - Use `agy` with model `gemini-3.8-flash-high` for all heavy Lean implementation,
    routine proof repairs, error resolution, and compilation iterations.
  - The primary agent focuses on orchestration, dependency scheduling, queue management,
    and very selective blocker assistance on the hardest mathematical issues.
- **Replenishment from queue**: As active workers complete tasks, replenish the worker pool
  from useful queued work in `tasks.json` / the dependency graph, maintaining high throughput
  without exceeding the 10-worker concurrency limit.
- **Strict file ownership**: Obey file ownership strictly. Each worker is assigned specific
  files; never edit files owned by concurrent workers. Avoid overlapping ownership.
- **Conflict avoidance via scratch dirs**: Use isolated scratch directories under
  `tmp/agy/<task_name>/` for intermediate files, scratch Lean experiments, and temporary logs.
- **Compiler check discipline**: Always run compiler commands (e.g. `lake env lean <file>`
  or `lake build`) and wait/poll until an actual exit code is obtained. Never end a turn
  or report merely that a check was launched.
- **Reporting**: On task completion or when documenting a concrete blocker, write a concise,
  structured markdown report to `tmp/agy/reports/<task_name>.md`.

## Analytic Trust Boundary and Conditional Formalization

- **No axioms, no sorry**: Never introduce `sorry`, `admit`, new Lean `axiom` declarations,
  or unchecked proof substitutes.
- **Explicit analytic hypotheses**: The two external analytic inputs from the paper:
  1. The quantitative Matomäki–Radziwiłł short-interval theorem (`QuantitativeShortIntervalInput`,
     which implies `ShortIntervalInput`).
  2. The Dickman–de Bruijn smooth-number asymptotic (`SmoothCountingInput`, which implies
     `SmoothMeanInput`).
  These are NOT formalized in Lean. They MUST remain explicit theorem parameters (`Prop`
  hypotheses) rather than added Lean axioms.
- **Conditional nature**: Results are conditional deductions: a clean build verifies the
  implication from the analytic hypotheses to the Erdős problem conclusions, NOT an
  unconditional proof of Erdős Problem #1201.
- **Expected final wrappers**:
  - `Erdos1201.theorem1`
  - `Erdos1201.erdos_problem_1201`
  Both take `QuantitativeShortIntervalInput` and `SmoothCountingInput` as explicit hypotheses.

## Mathematical Conventions

- **Block length and problem parameter**: The consecutive product $\prod_{j=1}^h (n+j)$ has
  $h$ factors, corresponding to the paper's $k = h - 1$ consecutive integers.
- **Positive integer domain**: Counting is performed on positive integers $n \ge 1$;
  zero is excluded from both the good and bad sets. Largest prime factors satisfy
  $P^+(1) = 1$ and $P^+(0) = 0$.
- **Interval endpoints**: Dyadic averaging intervals use $[X, 2X)$; counting shells use
  $(X, 2X]$. Endpoint corrections between inclusive counts and half-open averages must be
  bounded and proved to vanish asymptotically.
