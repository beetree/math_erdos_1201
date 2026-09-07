# Erdős Problem 1201: Lean 4 formalization

**Paper:** [*A note on Erdős Problem #1201*](erdos1201.pdf) (30 April 2026, downloaded from
[ulam.ai](https://www.ulam.ai/research/erdos1201.pdf)). **The original paper and proof are by
Przemek Chojecki together with ChatGPT 5.5.** It proves that for every $\varepsilon,\eta>0$ there is
$k$ such that the set of integers $n$ with $P^+(n(n+1)\cdots(n+k))>n^{1-\varepsilon}$ has lower
asymptotic density at least $1-\eta$, and in fact that the exceptional upper density tends to $0$
as $k\to\infty$, using the Matomäki–Radziwiłł theorem on multiplicative functions in short
intervals. This repository holds the Lean 4 formalization of that deduction, together with a
Lean proof of the short-interval input it uses (specialised to the one function the deduction
applies it to), so that the final theorem is unconditional. Credit for the mathematical argument
belongs entirely to the authors of the paper.

## Verification transcript

`lake build` on `main` produces no errors and no warnings; the single info line is the axiom
report of the terminal theorem, printed by `Erdos1201/Audit.lean`:

```console
$ cat lean-toolchain
leanprover/lean4:v4.34.0-rc2
$ lake exe cache get
$ lake build
ℹ [8944/8947] Replayed Erdos1201.Audit
info: Erdos1201/Audit.lean:25:0: 'Erdos1201.erdos_problem_1201_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
Build completed successfully (8947 jobs).
$
```

`propext`, `Classical.choice`, and `Quot.sound` are Lean's standard foundational axioms.
No `sorryAx`, no `Lean.ofReduceBool`, and no project-declared axiom appears: the theorem
`Erdos1201.erdos_problem_1201_unconditional` is proved using Mathlib (`v4.34.0-rc2`, revision
`85e3a25e`, pinned in `lake-manifest.json`) and the vendored proved lemmas under
`Erdos1201/Vendor/`, with only the stated standard foundational axioms. The transcript above was
recorded on 7 September 2026 at commit `d039570` of `main` (the last commit touching Lean
sources; clean working tree). No independent third party has yet reproduced it.

## How to read this repository

The trust chain has two links, plus the integrity of the checking environment.

1. **The statement of faithfulness** (next section). It is the human-checked claim that the
   formal proposition proved by `Erdos1201.erdos_problem_1201_unconditional`, with the
   definitions in `Erdos1201/Basic.lean` and `Erdos1201/Density.lean`, is a faithful
   formulation of Erdős Problem 1201. This is the one thing a reader must examine and believe;
   no machine can check it.
2. **The Lean kernel.** Once the terminal theorem is checked and
   `#print axioms Erdos1201.erdos_problem_1201_unconditional` reports only `propext`,
   `Classical.choice`, and `Quot.sound`, the paper's analytic arguments, the Matomäki–Radziwiłł
   paper, the tactics, and the AI systems that wrote the proof scripts need not be trusted as
   independent authorities: the proof terms and their dependencies supply the justification.

The remaining trust is in this correspondence, in Lean's logical foundations and checker, and
in the integrity of the checking environment and of the source revision. A transcript does not
authenticate itself: reproduce the check from a fresh checkout of the pinned revision (see
"Terminal theorem and verification procedure").

The files holding the audited definitions and the terminal theorem have these SHA-256 values at
the recorded revision:

```text
d2cc1022dc116780b96661d9d1dea1e1a3e6204c6e4142d437958be8e4c22876  Erdos1201/Basic.lean
6f38fb3f7869e689a3ac6dbd99c403d6b3fe87bed3f3bc25fc84a3071649856f  Erdos1201/Density.lean
c185e11d802a3ec9969bea80065c705eb1216059242a82f18ce3305216b3a465  Erdos1201/Final.lean
```

Any change to them requires the correspondence below to be checked again.

## Statement of faithfulness

### Statement of faithfulness: Erdős Problem 1201

**Version: 7 September 2026. Status: statement audit; formal proof complete, kernel-checked (see the verification transcript above).**

This statement identifies the mathematical assertion that the Lean project proves and explains
why that assertion answers Erdős Problem 1201. It distinguishes the human task of checking that
the formal statement captures the problem from the kernel's task of checking a proof of that
statement.

The problem, as stated on the [Erdős Problems website](https://www.erdosproblems.com/1201)
(#1201, from [Er80, p. 107]), asks: is it true that for every $\varepsilon,\eta>0$ there exists
$k$ such that the density of $n$ for which

$$
P(n(n+1)\cdots(n+k))>n^{1-\varepsilon}
$$

is at least $1-\eta$, where $P(m)$ is the greatest prime divisor of $m$? The paper (Section 1)
reads "density" as lower asymptotic density,
$\underline d(A)=\liminf_{N\to\infty}|A\cap[1,N]|/N$, with $P^+(1)=1$, and proves the stronger
Theorem 1: for every $\varepsilon>0$,

$$
\lim_{h\to\infty}\ \overline d\Bigl\{n\in\mathbb N : P^+\Bigl(\prod_{j=0}^{h-1}(n+j)\Bigr)\le n^{1-\varepsilon}\Bigr\}=0,
$$

from which the requested statement follows with $k+1$ factors.

The terminal theorems, in `Erdos1201/Final.lean` (namespace `Erdos1201`), are

```lean
theorem erdos_problem_1201_unconditional {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k)

theorem theorem1_unconditional {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0)
```

with the definitions (`Erdos1201/Basic.lean`, `Erdos1201/Density.lean`)

```lean
def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)
def consecutiveProduct (n h : ℕ) : ℕ := ∏ j ∈ range h, (n + j)
def badSet (ε : ℝ) (h : ℕ) : Set ℕ :=
  {n | 0 < n ∧ (largestPrimeFactor (consecutiveProduct n h) : ℝ) ≤ (n : ℝ) ^ (1 - ε)}
def goodSet (ε : ℝ) (k : ℕ) : Set ℕ :=
  {n | 0 < n ∧ (n : ℝ) ^ (1 - ε) < largestPrimeFactor (consecutiveProduct n (k + 1))}
noncomputable def intervalCount (A : Set ℕ) (a b : ℕ) : ℕ := ((Ioc a b).filter (· ∈ A)).card
noncomputable def density (A : Set ℕ) (N : ℕ) : ℝ := (intervalCount A 0 N : ℝ) / N
noncomputable def upperDensity (A : Set ℕ) : ℝ := limsup (density A) atTop
noncomputable def lowerDensity (A : Set ℕ) : ℝ := liminf (density A) atTop
```

| Formal expression | Mathematical meaning |
| --- | --- |
| `largestPrimeFactor n` | $P^+(n)$: the largest prime divisor of $n$, with $P^+(1)=1$ (and value $1$ at $n=0$, which is excluded below). |
| `consecutiveProduct n h` | $n(n+1)\cdots(n+h-1)$, a product of $h$ consecutive integers. |
| `goodSet ε k` | $\{n\ge1 : P^+(n(n+1)\cdots(n+k))>n^{1-\varepsilon}\}$, the set $\mathcal G_{\varepsilon,k}$ of the paper; the product has $k+1$ factors. |
| `badSet ε h` | $\{n\ge1 : P^+(\prod_{j<h}(n+j))\le n^{1-\varepsilon}\}$, the set $\mathcal B_{\varepsilon,h}$ of the paper. |
| `density A N` | $\lvert A\cap[1,N]\rvert/N$ (`Ioc 0 N` is $\{1,\dots,N\}$). |
| `lowerDensity A`, `upperDensity A` | $\underline d(A)$ and $\overline d(A)$, as `liminf`/`limsup` in $\mathbb R$ of the density sequence, which lies in $[0,1]$. |
| `(n : ℝ) ^ (1 - ε)` | the real power $n^{1-\varepsilon}$; `ε` is any positive real, so $\varepsilon\ge1$ is allowed (the conclusion is then trivial, as in the paper). |

These definitions address the relevant conventions explicitly. The condition `0 < n` excludes
$n=0$, where the product is $0$ and every prime divides it; a single point does not affect any
density. `largestPrimeFactor` is a total function with `max 1`, which realises $P^+(1)=1$ and
agrees with the greatest prime divisor for every $n\ge2$ (`Erdos1201/PrimeFactor.lean` proves
these bridges). The count uses the integers $1,\dots,N$, matching $|A\cap[1,N]|$. The
`liminf`/`limsup` are taken in $\mathbb R$; since every value `density A N` lies in $[0,1]$, these
coincide with the extended-real limits, so `1 - η ≤ lowerDensity (goodSet ε k)` says exactly that
$\underline d(\mathcal G_{\varepsilon,k})\ge1-\eta$. The quantifier order in
`erdos_problem_1201_unconditional` is the problem's: for every $\varepsilon>0$ and $\eta>0$ a
single $k$ works for all large $N$.

For comparison, the [Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/1201.lean)
(inspected 7 September 2026) defines the set with `sSup {p : ℕ | p.Prime ∧ p ∣ ∏ i ∈ range (k+1), (n+i)}`,
counts $n<x$ with `Nat.count`, and takes the `liminf` in `EReal`. For $n\ge1$ its set and
`goodSet ε k` coincide (`sSup` of the finite nonempty set of prime divisors is $P^+$); the two
formulations differ at $n=0$ only, and their density sequences differ by a bounded shift, so their
`liminf`s agree. The theorem proved here is therefore the affirmative answer to that statement as
well, and `theorem1_unconditional` is the stronger form of the paper.

Both terminal theorems are **unconditional**: their only hypotheses are `0 < ε` and `0 < η`.
The analytic input of the paper, the Matomäki–Radziwiłł short-interval theorem, is not assumed;
it is proved in this repository in the form the deduction uses (`SmoothShortIntervalInput` in
`Erdos1201/MR/Target.lean`, proved by `Erdos1201.MR.smoothShortIntervalInput_holds` in
`Erdos1201/MR/FinalAssembly.lean`), and the paper's smooth-number input is proved by
`Erdos1201.smoothUpperInput` in `Erdos1201/SmoothInput.lean`. Wrapper theorems with an explicit
`QuantitativeShortIntervalInput` hypothesis (`Erdos1201/Main.lean`) are corollaries of the same
deduction and are not part of the certificate.

The final theorem's complete dependency chain is checked by the kernel. The permitted
foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx`,
problem-specific axiom, or additional computational trust axiom occurs. These foundations and the
role of kernel checking are described in
[Lean's account of axioms](https://lean-lang.org/theorem_proving_in_lean4/Axioms-and-Computation/)
and its [description of the kernel](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/#the-kernel).
The kernel cannot itself establish that a formal proposition is the problem Erdős intended; that
is the content of this statement.

**This certificate: commit `d039570` of `main`; terminal theorem
`Erdos1201.erdos_problem_1201_unconditional`; axiom report `[propext, Classical.choice, Quot.sound]`.**

---

## Terminal theorem and verification procedure

The terminal theorem is

```lean
theorem Erdos1201.erdos_problem_1201_unconditional {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k)
```

with the definitions exactly as in `Erdos1201/Basic.lean` and `Erdos1201/Density.lean`. To verify:

```sh
lake exe cache get   # precompiled Mathlib
lake build           # must succeed with no errors; the axiom report is printed by Erdos1201/Audit.lean
```

or, after the build, with a check file `AxiomCheck.lean` containing

```lean
import Erdos1201.Final

#check @Erdos1201.erdos_problem_1201_unconditional
#print axioms Erdos1201.erdos_problem_1201_unconditional
#print axioms Erdos1201.theorem1_unconditional
#print axioms Erdos1201.MR.smoothShortIntervalInput_holds
```

run `lake env lean AxiomCheck.lean`; each line should report exactly
`[propext, Classical.choice, Quot.sound]`. The first report is the essential check; the other two
are diagnostics for Theorem 1 of the paper and for the short-interval input.

## Status

Complete, according to the certificate recorded above. The deduction follows the paper; the
short-interval input is proved following K. Matomäki and M. Radziwiłł, *Multiplicative functions
in short intervals*, Ann. of Math. **183** (2016), in the corrected version
[arXiv:1501.04585v4](https://arxiv.org/abs/1501.04585v4), with two departures recorded in
[`BLUEPRINT.md`](BLUEPRINT.md): the Dirichlet polynomial is not restricted to a sifted set (the
decomposition lemma carries the unsifted count as an explicit error term), and Halász's theorem is
replaced by a twisted prime-number theorem in short ranges, obtained from a Vinogradov–Korobov
zero-free region that is itself proved from a weak form of Vinogradov's mean value theorem
(after T. Tao, *254A, Notes 5*). Paper component → Lean files:

| Paper component | Section | Principal Lean files |
|---|---:|---|
| Definitions: $P^+$, densities, $\mathcal G_{\varepsilon,k}$, $\mathcal B_{\varepsilon,h}$ | 1 | `Basic.lean`, `Density.lean`, `PrimeFactor.lean` |
| Deduction of Theorem 1 and of the problem from the two inputs | 3 | `Proof.lean`, `AnalyticInputs.lean`, `Quantitative.lean`, `Main.lean`, `Final.lean` |
| Smooth-number input (block mean of the $X^\beta$-smooth indicator bounded away from $1$) | 2, 3 | `PrimeSums.lean`, `SmoothBound.lean`, `SmoothInput.lean`, `SmoothAsymptotics.lean` (reference bridge) |
| Short-interval input for the smooth indicator: statement and its use | 2 | `MR/Target.lean`, `MR/ShortIntervalAssembly.lean` |
| MR Lemma 12 (Ramaré decomposition) and Lemma 13 (moments) | MR §5–7 | `MR/Decomposition/`, `MR/Polynomials/`, `MR/Arithmetic.lean`, `MR/Ramare.lean` |
| MR Lemma 14 (Parseval), Saffari–Vaughan averaging, Plancherel | MR §6 | `MR/Parseval/` |
| MR Proposition 1: range system, $E_1$, $E_j$, exceptional set | MR §8 | `MR/Ranges.lean`, `MR/Prop1/` |
| Mean value theorems, Halász–Montgomery, Halász for primes, large values | MR §4 | `MR/Analysis/` |
| Twisted prime sums via the smoothed Chebyshev contour | — | `MR/Twisted/` |
| Vinogradov mean value theorem, bilinear estimate, ζ bound, zero-free region | — | `MR/Vinogradov/` |
| Sieve bounds and Rankin's smooth-number tail | MR §8 | `MR/Sieve/` |
| Final assembly of the short-interval input | — | `MR/FrequencyIntegral.lean`, `MR/FinalAssembly.lean` |
| Axiom audit | — | `Audit.lean` |

The modules `MR/Exceptional.lean` and `MR/SupportReduction.lean` are finite reduction lemmas
(Chebyshev counting, support removal) used by `MR/ShortIntervalAssembly.lean`; the modules
`Quantitative.lean`, `SmoothAsymptotics.lean`, and the wrappers in `Main.lean` are reference
bridges that follow the paper's exposition and are not on the terminal theorem's path.

## Vendored proofs

`Erdos1201/Vendor/` holds 139 modules (about 58,500 lines) copied from the `solve-math` corpus
with the same toolchain and Mathlib commit, with module paths renamed and no other changes:
analytic-number-theory libraries (the prime number theorem with the smoothed Chebyshev contour,
Mertens' theorems, the classical zero-free region, Halberstam–Richert and Selberg sieve bounds,
friable integers, and supporting analysis). They are compiled as part of this library; no
dependency on the `solve-math` repository exists. The only entry points from `Erdos1201/MR/` are
explicit imports of the theorems used (the contour machinery in `MR/Twisted/`, the Mertens and
sieve bounds in `MR/Sieve/`, the classical zero-free-region argument generalised in
`MR/Vinogradov/ZeroFreeGeneral.lean`). The formal statements proved from them are audited as
part of the terminal theorem's dependency chain.

## Layout

- `erdos1201.pdf`: the paper by Przemek Chojecki together with ChatGPT 5.5.
- `BLUEPRINT.md`: the route of the short-interval proof and the two departures from
  arXiv:1501.04585v4.
- `Erdos1201/`: the Lean sources; `Erdos1201/Final.lean` holds the terminal theorems and
  `Erdos1201/Audit.lean` prints their axioms. `Erdos1201/MR/` is the proof of the short-interval
  input (aggregated by `Erdos1201/MR/All.lean`); `Erdos1201/Vendor/` the vendored libraries.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: pins to Lean and Mathlib `v4.34.0-rc2`.
- `AGENTS.md`: contributor and agent instructions, including the attribution requirements.

## Authorship and use of AI

The original paper and proof are by **Przemek Chojecki together with ChatGPT 5.5**; the
mathematical argument and proof strategy are theirs. The short-interval theorem is due to
Matomäki and Radziwiłł, and the Vinogradov mean value route follows Tao's notes.

The Lean formalization was produced by Johan Land, 7 September 2026, with extensive use of large
language models: Codex (OpenAI), Claude Fable 5.1 (Anthropic), and Gemini 3.8 Flash (Google)
wrote the proof scripts under human direction and review. The formalization builds on Mathlib and
on the vendored libraries described above. The certificate is the kernel check reported in the
verification transcript; no independent third party has yet reproduced it.
