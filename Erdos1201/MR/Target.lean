import Erdos1201.Proof
import Erdos1201.SmoothInput

/-!
# The exact short-interval statement needed for Erdős #1201

The original Erdős #1201 paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
This module is part of the formalization of the Matomäki–Radziwiłł short-interval theorem
(arXiv:1501.04585v4) that the deduction takes as input.

The deduction in `Erdos1201/Proof.lean` applies the short-interval input only to the smooth
indicator `f_X = smoothIndicator (X^β)` with `3/4 ≤ β < 1`. `SmoothShortIntervalInput` is that
special case. Proving it unconditionally makes `erdos_problem_1201` unconditional.
-/

open Filter Finset
open scoped Topology

namespace Erdos1201

/-- The short-interval input specialised to the smooth indicator with `3/4 ≤ β < 1`. -/
def SmoothShortIntervalInput : Prop :=
  ∀ β : ℝ, 3 / 4 ≤ β → β < 1 → ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
    ∀ᶠ h : ℕ in atTop, ∀ᶠ X : ℕ in atTop,
      (intervalCount {n | δ < |shortMean (smoothIndicator ((X : ℝ) ^ β)) h n -
          blockMean (smoothIndicator ((X : ℝ) ^ β)) X|} X (2 * X) : ℝ) ≤ η * X

/-- The general qualitative input implies the specialised one. -/
theorem ShortIntervalInput.to_smoothShortIntervalInput (H : ShortIntervalInput) :
    SmoothShortIntervalInput := by
  intro β _ _ δ hδ η hη
  filter_upwards [H δ hδ η hη] with h hh
  filter_upwards [hh] with X hX
  exact hX _ (smoothIndicator_completelyMultiplicative _) (smoothIndicator_mem_Icc _)

/-- The bad upper density is eventually small, from the specialised input. -/
theorem eventually_upperDensity_bad_le_of_smooth
    (hMR : SmoothShortIntervalInput) (hSmooth : SmoothUpperInput)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hη : 0 < η) :
    ∀ᶠ h : ℕ in atTop, upperDensity (badSet ε h) ≤ η := by
  let β : ℝ := 1 - ε / 2
  have hβ : 3 / 4 ≤ β := by dsimp [β]; linarith
  obtain ⟨r, hr, hmean⟩ := hSmooth β (by dsimp [β]; linarith) (by dsimp [β]; linarith)
  let δ : ℝ := (1 - r) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hmean' : ∀ᶠ X : ℕ in atTop,
      blockMean (smoothIndicator ((X : ℝ) ^ β)) X ≤ r + δ :=
    hmean.mono (fun _ h => h.trans (by linarith))
  have hscale := eventually_scale_separation (a := 1 - ε) (β := β)
    (by linarith) (by dsimp [β]; linarith)
  filter_upwards [hMR β hβ (by dsimp [β]; linarith) δ hδ (η / 2) (by positivity),
    eventually_gt_atTop 0] with h hmr hh
  have hb : ∀ᶠ X : ℕ in atTop,
      (intervalCount (badSet ε h) X (2 * X) : ℝ) ≤ (η / 2) * X := by
    filter_upwards [hmr, hmean', hscale] with X hX hm hs
    exact bad_block_bound hh hr rfl hm hs hX
  have := upperDensity_le_of_dyadic (badSet ε h) (by positivity : 0 ≤ η / 2) hb
  linarith

/-- Erdős problem #1201, conditional only on the specialised short-interval input. -/
theorem erdos_problem_1201_of_smoothShortInterval (hMR : SmoothShortIntervalInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k) := by
  let ε' : ℝ := min ε (1 / 2)
  have hp : 0 < ε' := lt_min hε (by norm_num)
  have h1 : ε' ≤ 1 / 2 := min_le_right _ _
  obtain ⟨h, hh, hpos⟩ := ((eventually_upperDensity_bad_le_of_smooth hMR smoothUpperInput hp h1 hη).and
    (eventually_gt_atTop 0)).exists
  refine ⟨h - 1, ?_⟩
  rw [good_lowerDensity_eq, Nat.sub_add_cancel hpos]
  have := upperDensity_mono (badSet_antitone (min_le_left ε (1 / 2)) h)
  linarith

/-- Theorem 1 of the paper, conditional only on the specialised short-interval input. -/
theorem theorem1_of_smoothShortInterval (hMR : SmoothShortIntervalInput)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun h => ha.trans_le (upperDensity_nonneg _))
  · intro a ha
    let ε' : ℝ := min ε (1 / 2)
    have hp : 0 < ε' := lt_min hε (by norm_num)
    have h1 : ε' ≤ 1 / 2 := min_le_right _ _
    filter_upwards [eventually_upperDensity_bad_le_of_smooth hMR smoothUpperInput hp h1
      (show 0 < a / 2 by positivity)] with h hh
    have := upperDensity_mono (badSet_antitone (min_le_left ε (1 / 2)) h)
    linarith

end Erdos1201
