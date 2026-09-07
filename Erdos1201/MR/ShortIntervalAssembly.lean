import Erdos1201.MR.SupportReduction
import Erdos1201.MR.Target

/-!
# From restricted dyadic energies to the smooth short-interval target

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
These are Matomäki–Radziwiłł auxiliary reductions for arXiv:1501.04585v4.

This file connects the generic finite-set support-removal lemma to the actual
`shortMean`, `blockMean`, `intervalCount`, and `SmoothShortIntervalInput` definitions.
The short windows are `[n,n+h)`, the long mean is on `[X,2X)`, and the starting points
are counted in `(X,2X]`.  The short and long averaging sets have exactly `h` and `X`
elements, respectively: the **cardinality normalization error** is exactly zero.
This does not identify `[X,2X)` with `(X,2X]` or remove errors caused by truncating
coefficient support. Such changes still need their own estimates.

The final assembly theorem takes the restricted energy estimates as explicit hypotheses.
It does not establish those estimates or remove the analytic hypothesis from the existing
final Erdős theorems. In particular, the order `∀ᶠ h, ∀ᶠ X` is preserved.

Validation status: candidate continuation, not compiler-checked in the delivery environment.
See `MR_CONTINUATION.md` and `scripts/check_mr_continuation.sh`.
-/

open Filter Finset
open scoped BigOperators Topology

namespace Erdos1201.MR

/-- The finite set underlying the existing short mean. -/
def shortWindow (h n : ℕ) : Finset ℕ :=
  (Finset.range h).image (fun j => n + j)

lemma shortWindow_eq_Ico (h n : ℕ) : shortWindow h n = Finset.Ico n (n + h) := by
  ext m
  simp only [shortWindow, Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨j, hj, rfl⟩
    omega
  · rintro ⟨hnm, hmh⟩
    exact ⟨m - n, by omega, by omega⟩

@[simp] lemma card_shortWindow (h n : ℕ) : (shortWindow h n).card = h := by
  unfold shortWindow
  rw [Finset.card_image_of_injective (Finset.range h) (by
    intro i j hij
    exact Nat.add_left_cancel hij)]
  exact Finset.card_range h

lemma finiteAverage_shortWindow (f : ℕ → ℝ) (h n : ℕ) :
    finiteAverage (shortWindow h n) f (h : ℝ) = shortMean f h n := by
  unfold finiteAverage shortWindow shortMean
  rw [Finset.sum_image]
  intro i _ j _ hij
  exact Nat.add_left_cancel hij

lemma finiteAverage_dyadic (f : ℕ → ℝ) (X : ℕ) :
    finiteAverage (Finset.Ico X (2 * X)) f (X : ℝ) = blockMean f X := rfl

lemma discrepancy_shortWindow (f : ℕ → ℝ) (h X n : ℕ) :
    discrepancy (shortWindow h) (Finset.Ico X (2 * X)) f (h : ℝ) (X : ℝ) n =
      shortMean f h n - blockMean f X := by
  simp only [discrepancy, finiteAverage_shortWindow, finiteAverage_dyadic]

/-- No cardinality-normalization error occurs for these exact half-open averages. -/
lemma shortWindow_endpoint_mass_eq_zero (h X n : ℕ) (hh : 0 < h) (hX : 0 < X) :
    |((shortWindow h n).card : ℝ) / (h : ℝ) -
        ((Finset.Ico X (2 * X)).card : ℝ) / (X : ℝ)| = 0 := by
  have hcard : (Finset.Ico X (2 * X)).card = X := by
    rw [Nat.card_Ico]
    omega
  rw [card_shortWindow, hcard]
  have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hh)
  have hXR : (X : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hX)
  simp [hhR, hXR]

/-- The actual dyadic second moment, before division by `X`. -/
noncomputable def shortMeanEnergy (f : ℕ → ℝ) (h X : ℕ) : ℝ :=
  energy (Finset.Ioc X (2 * X)) (fun n => shortMean f h n - blockMean f X)

lemma shortMeanEnergy_nonneg (f : ℕ → ℝ) (h X : ℕ) : 0 ≤ shortMeanEnergy f h X :=
  energy_nonneg _ _

/-- The existing counting convention agrees exactly with the finite exceptional set. -/
lemma intervalCount_eq_exceptional_card (f : ℕ → ℝ) (h X : ℕ) (δ : ℝ) :
    intervalCount {n | δ < |shortMean f h n - blockMean f X|} X (2 * X) =
      (exceptional (Finset.Ioc X (2 * X))
        (discrepancy (shortWindow h) (Finset.Ico X (2 * X)) f (h : ℝ) (X : ℝ)) δ).card := by
  classical
  simp only [intervalCount, exceptional, discrepancy_shortWindow, Set.mem_setOf_eq]

/-- Exact finite support-removal estimate for the means used by the Erdős deduction. -/
theorem intervalCount_le_restricted_shortMeanEnergies
    (S : Set ℕ) (f : ℕ → ℝ) (h X : ℕ) (t ρ : ℝ)
    (hh : 0 < h) (hX : 0 < X) (ht : 0 < t) (hf : ∀ n, |f n| ≤ 1)
    (hmissing : blockMean (missingIndicator S) X ≤ ρ) :
    (intervalCount {n | 2 * t + 2 * ρ < |shortMean f h n - blockMean f X|}
      X (2 * X) : ℝ) ≤
      (shortMeanEnergy (supportedPart S f) h X +
        shortMeanEnergy (supportIndicator S) h X) / t ^ 2 := by
  have hhR : 0 < (h : ℝ) := by exact_mod_cast hh
  have hXR : 0 < (X : ℝ) := by exact_mod_cast hX
  have hmissing' :
      finiteAverage (Finset.Ico X (2 * X)) (missingIndicator S) (X : ℝ) ≤ ρ := hmissing
  have hend : ∀ n ∈ Finset.Ioc X (2 * X),
      |((shortWindow h n).card : ℝ) / (h : ℝ) -
        ((Finset.Ico X (2 * X)).card : ℝ) / (X : ℝ)| ≤ (0 : ℝ) := by
    intro n _
    exact le_of_eq (shortWindow_endpoint_mass_eq_zero h X n hh hX)
  have hfinite := exceptional_card_le_restricted_energies
    (Finset.Ioc X (2 * X)) (shortWindow h) (Finset.Ico X (2 * X)) S f
    (h : ℝ) (X : ℝ) t ρ 0 hhR hXR ht
    (fun _ _ n _ => hf n) (fun n _ => hf n) hmissing' hend
  rw [intervalCount_eq_exceptional_card]
  have hd : ∀ g : ℕ → ℝ, discrepancy (shortWindow h) (Finset.Ico X (2 * X)) g (h : ℝ) (X : ℝ) =
      fun n => shortMean g h n - blockMean g X :=
    fun g => funext (fun n => discrepancy_shortWindow g h X n)
  simp only [hd, add_zero] at hfinite ⊢
  simpa only [shortMeanEnergy] using hfinite

/-- Convenient budget form: missing mean at most `δ/4` and total restricted energy at
most `η (δ/4)² X` imply at most `η X` exceptions at threshold `δ`. -/
theorem intervalCount_le_of_restricted_shortMeanEnergy_budget
    (S : Set ℕ) (f : ℕ → ℝ) (h X : ℕ) (δ η : ℝ)
    (hh : 0 < h) (hX : 0 < X) (hδ : 0 < δ) (hf : ∀ n, |f n| ≤ 1)
    (hmissing : blockMean (missingIndicator S) X ≤ δ / 4)
    (henergy : shortMeanEnergy (supportedPart S f) h X +
        shortMeanEnergy (supportIndicator S) h X ≤ η * (δ / 4) ^ 2 * (X : ℝ)) :
    (intervalCount {n | δ < |shortMean f h n - blockMean f X|} X (2 * X) : ℝ) ≤
      η * (X : ℝ) := by
  have ht : 0 < δ / 4 := by positivity
  have hbound := intervalCount_le_restricted_shortMeanEnergies S f h X
    (δ / 4) (δ / 4) hh hX ht hf hmissing
  have hthreshold : 2 * (δ / 4) + 2 * (δ / 4) = δ := by ring
  rw [hthreshold] at hbound
  refine hbound.trans ?_
  have hsq : (δ / 4) ^ 2 ≠ 0 := ne_of_gt (pow_pos ht 2)
  calc
    (shortMeanEnergy (supportedPart S f) h X +
        shortMeanEnergy (supportIndicator S) h X) / (δ / 4) ^ 2
        ≤ (η * (δ / 4) ^ 2 * (X : ℝ)) / (δ / 4) ^ 2 :=
          div_le_div_of_nonneg_right henergy (sq_nonneg _)
    _ = (η * (X : ℝ)) * (δ / 4) ^ 2 / (δ / 4) ^ 2 := by ring
    _ = η * (X : ℝ) := mul_div_cancel_right₀ _ hsq

/-- Assembly into the precise smooth short-interval target.

`H` is the remaining mathematical obligation, not a new axiom or a claimed proof:
for every positive missing-mass budget and positive energy budget, after choosing
`h` large and then `X` large, choose one support satisfying both bounds.
The support may depend on `β`, the budgets, `h`, and `X`.

Both restricted energies must be controlled for that **same support**. -/
theorem smoothShortIntervalInput_of_restricted_shortMeanEnergies
    (H : ∀ β : ℝ, 3 / 4 ≤ β → β < 1 →
      ∀ ρ : ℝ, 0 < ρ → ∀ V : ℝ, 0 < V →
        ∀ᶠ h : ℕ in atTop, ∀ᶠ X : ℕ in atTop, ∃ S : Set ℕ,
          blockMean (missingIndicator S) X ≤ ρ ∧
          shortMeanEnergy (supportedPart S (smoothIndicator ((X : ℝ) ^ β))) h X +
            shortMeanEnergy (supportIndicator S) h X ≤ V * (X : ℝ)) :
    SmoothShortIntervalInput := by
  intro β hβ hβ1 δ hδ η hη
  have hρ : 0 < δ / 4 := by positivity
  have hV : 0 < η * (δ / 4) ^ 2 := by positivity
  filter_upwards [H β hβ hβ1 (δ / 4) hρ (η * (δ / 4) ^ 2) hV,
    eventually_gt_atTop 0] with h hH hh
  filter_upwards [hH, eventually_gt_atTop 0] with X hHX hX
  obtain ⟨S, hmissing, henergy⟩ := hHX
  have hf : ∀ n, |smoothIndicator ((X : ℝ) ^ β) n| ≤ 1 := by
    intro n
    exact abs_le.mpr (smoothIndicator_mem_Icc _ n)
  exact intervalCount_le_of_restricted_shortMeanEnergy_budget
    S (smoothIndicator ((X : ℝ) ^ β)) h X δ η hh hX hδ hf hmissing henergy

end Erdos1201.MR
