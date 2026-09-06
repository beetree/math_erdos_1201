import Erdos1201.Proof

/-!
# Quantitative short-interval input and its qualitative consequence

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
The analytic theorem below is an explicit proposition parameter, not an axiom.
The passage from its quantitative estimate to `ShortIntervalInput` is proved.
-/

open Filter Finset
open scoped Topology

namespace Erdos1201
open Classical

noncomputable def shortError (h : ℕ) : ℝ := Real.log (Real.log h) / Real.log h
noncomputable def lengthError (δ : ℝ) (h : ℕ) : ℝ :=
  (Real.log h) ^ (1 / 3 : ℝ) / (δ ^ 2 * (h : ℝ) ^ (δ / 25))
noncomputable def scaleError (δ : ℝ) (X : ℕ) : ℝ :=
  1 / (δ ^ 2 * (Real.log X) ^ (1 / 50 : ℝ))

/-- Theorem 2 of the paper, restricted to completely multiplicative functions.

The endpoint convention is `(X, 2X]`, a subset of the paper's exceptional domain
`[X, 2X]`. The averaging intervals are unchanged. -/
def QuantitativeShortIntervalInput : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ f : ℕ → ℝ, CompletelyMultiplicative f → (∀ n, f n ∈ Set.Icc (-1 : ℝ) 1) →
    ∀ h X : ℕ, 2 ≤ h → h ≤ X → ∀ δ : ℝ, 0 < δ →
      (intervalCount {n | δ + C₀ * shortError h < |shortMean f h n - blockMean f X|}
        X (2 * X) : ℝ) ≤ C * X * (lengthError δ h + scaleError δ X)

theorem shortError_tendsto_zero : Tendsto shortError atTop (𝓝 0) := by
  exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem lengthError_tendsto_zero {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (lengthError δ) atTop (𝓝 0) := by
  have ht := (isLittleO_log_rpow_rpow_atTop (1 / 3 : ℝ)
    (show 0 < δ / 25 by positivity)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hd := ht.div_const (δ ^ 2)
  change Tendsto (fun h => lengthError δ h) atTop (𝓝 0)
  simpa only [Function.comp_apply, zero_div, lengthError, div_div, mul_comm] using hd

theorem scaleError_tendsto_zero {δ : ℝ} (_hδ : 0 < δ) :
    Tendsto (scaleError δ) atTop (𝓝 0) := by
  have ht := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 50 by norm_num)).comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hd := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop ht
  have hd' := hd.div_const (δ ^ 2)
  change Tendsto (fun X => scaleError δ X) atTop (𝓝 0)
  simpa only [Function.comp_apply, zero_div, scaleError, div_div, mul_comm] using hd'

/-- All limit estimates needed to deduce the uniform qualitative input are checked here. -/
theorem QuantitativeShortIntervalInput.to_shortIntervalInput
    (H : QuantitativeShortIntervalInput) : ShortIntervalInput := by
  obtain ⟨C, hC, C₀, hC₀, H⟩ := H
  intro δ hδ η hη
  have hd : 0 < δ / 2 := by positivity
  have herr := by simpa using shortError_tendsto_zero.const_mul C₀
  have hlen := by simpa using (lengthError_tendsto_zero hd).const_mul C
  have hscale := by simpa using (scaleError_tendsto_zero hd).const_mul C
  filter_upwards [herr.eventually (gt_mem_nhds hd),
    hlen.eventually (gt_mem_nhds (show 0 < η / 2 by positivity)),
    eventually_ge_atTop 2] with h hh hl hh2
  filter_upwards [hscale.eventually (gt_mem_nhds (show 0 < η / 2 by positivity)),
    eventually_ge_atTop h] with X hX hhX
  intro f hf hbound
  have hinc : intervalCount {n | δ < |shortMean f h n - blockMean f X|} X (2 * X) ≤
      intervalCount {n | δ / 2 + C₀ * shortError h < |shortMean f h n - blockMean f X|}
        X (2 * X) := by
    apply card_le_card
    intro n hn
    simp only [mem_filter, mem_Ioc, Set.mem_ofPred_eq] at hn ⊢
    refine ⟨hn.1, ?_⟩
    have : C₀ * shortError h < δ / 2 := by simpa using hh
    linarith [hn.2]
  have hquant := H f hf hbound h X hh2 hhX (δ / 2) hd
  have hl' : C * lengthError (δ / 2) h < η / 2 := by simpa using hl
  have hs' : C * scaleError (δ / 2) X < η / 2 := by simpa using hX
  have hxpos : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  calc
    _ ≤ (intervalCount {n | δ / 2 + C₀ * shortError h <
        |shortMean f h n - blockMean f X|} X (2 * X) : ℝ) := Nat.cast_le.mpr hinc
    _ ≤ C * X * (lengthError (δ / 2) h + scaleError (δ / 2) X) := hquant
    _ ≤ η * X := by nlinarith [mul_nonneg hxpos (le_of_lt (show
        0 < η - (C * lengthError (δ / 2) h + C * scaleError (δ / 2) X) by linarith))]

/-- The problem's conclusion, using the quantitative short-interval theorem directly. -/
theorem erdos1201_of_quantitative
    (hMR : QuantitativeShortIntervalInput) (hSmooth : SmoothMeanInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k) :=
  erdos1201 hMR.to_shortIntervalInput hSmooth hε hη

end Erdos1201
