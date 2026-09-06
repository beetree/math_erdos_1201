import Erdos1201.Main

/-!
# A one-sided smooth-number input

The original Erdős #1201 deduction is by Przemek Chojecki together with
ChatGPT 5.5. This module isolates the strictly weaker smooth-number estimate
actually needed by that deduction. It does not assert that estimate as an axiom
or as a proved theorem: `SmoothMeanGapInput` is an explicit proposition.

The bridge and density deductions below have proof terms. A proof of
`SmoothMeanGapInput` would eliminate the need to formalize the entire Dickman
asymptotic in an alternative proof of the Erdős conclusion.
-/

open Filter
open scoped Topology

namespace Erdos1201

/-- An eventual upper bound strictly below one suffices; convergence is unnecessary. -/
def SmoothMeanGapInput : Prop :=
  ∀ β : ℝ, 0 < β → β < 1 → ∃ r : ℝ, r < 1 ∧
    ∀ᶠ X : ℕ in atTop, blockMean (smoothIndicator ((X : ℝ) ^ β)) X ≤ r

/-- The existing limiting-mean interface implies the weaker one-sided interface. -/
theorem SmoothMeanInput.to_smoothMeanGapInput (H : SmoothMeanInput) :
    SmoothMeanGapInput := by
  intro β hβ0 hβ1
  obtain ⟨r, hr, ht⟩ := H β hβ0 hβ1
  refine ⟨(r + 1) / 2, by linarith, ?_⟩
  exact (ht.eventually (gt_mem_nhds (by linarith : r < (r + 1) / 2))).mono
    (fun _ hx => hx.le)

/-- The counting asymptotic also implies the one-sided input. -/
theorem SmoothCountingInput.to_smoothMeanGapInput (H : SmoothCountingInput) :
    SmoothMeanGapInput :=
  H.to_smoothMeanInput.to_smoothMeanGapInput

/-- The main dyadic estimate uses only the eventual mean gap. -/
theorem eventually_upperDensity_bad_le_of_meanGap_of_lt_one
    (hMR : ShortIntervalInput) (hGap : SmoothMeanGapInput)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) :
    ∀ᶠ h : ℕ in atTop, upperDensity (badSet ε h) ≤ η := by
  let β : ℝ := 1 - ε / 2
  obtain ⟨r, hr, hmean⟩ := hGap β (by dsimp [β]; linarith)
    (by dsimp [β]; linarith)
  let δ : ℝ := (1 - r) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hscale := eventually_scale_separation (a := 1 - ε) (β := β)
    (by linarith) (by dsimp [β]; linarith)
  filter_upwards [hMR δ hδ (η / 2) (by positivity), eventually_gt_atTop 0]
    with h hmr hh
  have hb : ∀ᶠ X : ℕ in atTop,
      (intervalCount (badSet ε h) X (2 * X) : ℝ) ≤ (η / 2) * X := by
    filter_upwards [hmr, hmean, hscale] with X hX hm hs
    apply bad_block_bound hh hr (show δ = (1 - r) / 4 from rfl)
      (show blockMean (smoothIndicator ((X : ℝ) ^ β)) X ≤ r + δ by linarith) hs
    exact hX _ (smoothIndicator_completelyMultiplicative _) (smoothIndicator_mem_Icc _)
  have hd := upperDensity_le_of_dyadic (badSet ε h) (by positivity : 0 ≤ η / 2) hb
  linarith

/-- All positive epsilon values, with only the one-sided mean gap. -/
theorem eventually_upperDensity_bad_le_of_meanGap
    (hMR : ShortIntervalInput) (hGap : SmoothMeanGapInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ h : ℕ in atTop, upperDensity (badSet ε h) ≤ η := by
  let ε' : ℝ := min ε (1 / 2)
  have hp : 0 < ε' := lt_min hε (by norm_num)
  have h1 : ε' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  filter_upwards [eventually_upperDensity_bad_le_of_meanGap_of_lt_one hMR hGap hp h1 hη]
    with h hh
  exact (upperDensity_mono (badSet_antitone (min_le_left ε (1 / 2)) h)).trans hh

/-- The stronger bad-density limit, still conditional on the displayed inputs. -/
theorem bad_upperDensity_tendsto_zero_of_meanGap
    (hMR : ShortIntervalInput) (hGap : SmoothMeanGapInput)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun h => ha.trans_le (upperDensity_nonneg _))
  · intro a ha
    filter_upwards [eventually_upperDensity_bad_le_of_meanGap hMR hGap hε
      (show 0 < a / 2 by positivity)] with h hh
    linarith

/-- The Erdős conclusion needs no full smooth-counting asymptotic. -/
theorem erdos1201_of_meanGap
    (hMR : ShortIntervalInput) (hGap : SmoothMeanGapInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k) := by
  obtain ⟨h, hh, hpos⟩ := ((eventually_upperDensity_bad_le_of_meanGap hMR hGap hε hη).and
    (eventually_gt_atTop 0)).exists
  refine ⟨h - 1, ?_⟩
  rw [good_lowerDensity_eq, Nat.sub_add_cancel hpos]
  linarith

/-- Quantitative-MR wrapper for the one-sided smooth-number route. -/
theorem erdos1201_of_quantitative_meanGap
    (hMR : QuantitativeShortIntervalInput) (hGap : SmoothMeanGapInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k) :=
  erdos1201_of_meanGap hMR.to_shortIntervalInput hGap hε hη

end Erdos1201
