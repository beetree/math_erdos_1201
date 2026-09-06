import Erdos1201.AnalyticInputs

/-!
# The deduction in the paper, conditional on explicit analytic inputs

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
-/

open Finset Filter
open scoped Topology

namespace Erdos1201
open Classical

/-- The small increase in exponent absorbs the factor two in a dyadic interval. -/
theorem eventually_scale_separation {a β : ℝ} (ha : 0 ≤ a) (hab : a < β) :
    ∀ᶠ X : ℕ in atTop, ∀ n : ℕ, n ≤ 2 * X → (n : ℝ) ^ a ≤ (X : ℝ) ^ β := by
  have ht := (tendsto_rpow_atTop (sub_pos.mpr hab)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [ht.eventually (eventually_ge_atTop ((2 : ℝ) ^ a)),
    eventually_gt_atTop 0] with X hX hpos
  intro n hn
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hpos
  calc
    (n : ℝ) ^ a ≤ (2 * (X : ℝ)) ^ a :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) ha
    _ = (2 : ℝ) ^ a * (X : ℝ) ^ a := Real.mul_rpow (by norm_num) hXpos.le
    _ ≤ (X : ℝ) ^ (β - a) * (X : ℝ) ^ a :=
      mul_le_mul_of_nonneg_right hX (Real.rpow_nonneg hXpos.le _)
    _ = (X : ℝ) ^ β := by rw [← Real.rpow_add hXpos]; congr 1; ring

/-- Every bad point is exceptional for the short-interval estimate. -/
theorem bad_is_exceptional {ε β r δ : ℝ} {h X : ℕ}
    (hh : 0 < h) (hr : r < 1) (hδ : δ = (1 - r) / 4)
    (hmean : blockMean (smoothIndicator ((X : ℝ) ^ β)) X ≤ r + δ)
    (hscale : ∀ n : ℕ, n ≤ 2 * X → (n : ℝ) ^ (1 - ε) ≤ (X : ℝ) ^ β) :
    ∀ n ∈ badSet ε h, n ≤ 2 * X →
      δ < |shortMean (smoothIndicator ((X : ℝ) ^ β)) h n -
        blockMean (smoothIndicator ((X : ℝ) ^ β)) X| := by
  intro n hn hnX
  have hone : shortMean (smoothIndicator ((X : ℝ) ^ β)) h n = 1 := by
    apply shortMean_eq_one hh
    intro j hj
    simp [smoothIndicator, badSet_smooth_factors hn (hscale n hnX) hj]
  by_contra hc
  have hδpos : 0 < δ := by linarith
  have hgap := mean_gap hr hδ hmean ((le_of_not_gt hc).trans (by linarith : δ ≤ 2 * δ))
  rw [hone] at hgap
  exact (lt_irrefl 1) hgap

/-- The finite counting step: inclusion in the exceptional set transfers its bound. -/
theorem bad_block_bound {ε β r δ η : ℝ} {h X : ℕ}
    (hh : 0 < h) (hr : r < 1) (hδ : δ = (1 - r) / 4)
    (hmean : blockMean (smoothIndicator ((X : ℝ) ^ β)) X ≤ r + δ)
    (hscale : ∀ n : ℕ, n ≤ 2 * X → (n : ℝ) ^ (1 - ε) ≤ (X : ℝ) ^ β)
    (hex : (intervalCount {n | δ < |shortMean (smoothIndicator ((X : ℝ) ^ β)) h n -
        blockMean (smoothIndicator ((X : ℝ) ^ β)) X|} X (2 * X) : ℝ) ≤ η * X) :
    (intervalCount (badSet ε h) X (2 * X) : ℝ) ≤ η * X := by
  apply le_trans _ hex
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  simp only [mem_filter, mem_Ioc] at hn ⊢
  exact ⟨hn.1, bad_is_exceptional hh hr hδ hmean hscale n hn.2 hn.1.2⟩

/-- For `0 < ε < 1`, all sufficiently long blocks have arbitrarily small bad upper density. -/
theorem eventually_upperDensity_bad_le_of_lt_one
    (hMR : ShortIntervalInput) (hSmooth : SmoothMeanInput)
    {ε η : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hη : 0 < η) :
    ∀ᶠ h : ℕ in atTop, upperDensity (badSet ε h) ≤ η := by
  let β : ℝ := 1 - ε / 2
  obtain ⟨r, hr, hmean⟩ := hSmooth β (by dsimp [β]; linarith) (by dsimp [β]; linarith)
  let δ : ℝ := (1 - r) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hmean' : ∀ᶠ X : ℕ in atTop,
      blockMean (smoothIndicator ((X : ℝ) ^ β)) X ≤ r + δ :=
    (hmean.eventually (gt_mem_nhds (by linarith : r < r + δ))).mono (fun _ h => h.le)
  have hscale := eventually_scale_separation (a := 1 - ε) (β := β)
    (by linarith) (by dsimp [β]; linarith)
  filter_upwards [hMR δ hδ (η / 2) (by positivity), eventually_gt_atTop 0] with h hmr hh
  have hb : ∀ᶠ X : ℕ in atTop,
      (intervalCount (badSet ε h) X (2 * X) : ℝ) ≤ (η / 2) * X := by
    filter_upwards [hmr, hmean', hscale] with X hX hm hs
    exact bad_block_bound hh hr rfl hm hs
      (hX _ (smoothIndicator_completelyMultiplicative _) (smoothIndicator_mem_Icc _))
  have := upperDensity_le_of_dyadic (badSet ε h) (by positivity : 0 ≤ η / 2) hb
  linarith

/-- Increasing epsilon only shrinks the exceptional set. -/
theorem badSet_antitone {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (h : ℕ) :
    badSet ε₂ h ⊆ badSet ε₁ h := by
  intro n hn
  refine ⟨hn.1, hn.2.trans ?_⟩
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast hn.1
  · linarith

/-- The eventual bound, for every positive epsilon (including epsilon at least one). -/
theorem eventually_upperDensity_bad_le
    (hMR : ShortIntervalInput) (hSmooth : SmoothMeanInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∀ᶠ h : ℕ in atTop, upperDensity (badSet ε h) ≤ η := by
  let ε' : ℝ := min ε (1 / 2)
  have hp : 0 < ε' := lt_min hε (by norm_num)
  have h1 : ε' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  filter_upwards [eventually_upperDensity_bad_le_of_lt_one hMR hSmooth hp h1 hη] with h hh
  exact (upperDensity_mono (badSet_antitone (min_le_left ε (1 / 2)) h)).trans hh

/-- Theorem 1 in the original paper, conditional on the two analytic input propositions. -/
theorem bad_upperDensity_tendsto_zero
    (hMR : ShortIntervalInput) (hSmooth : SmoothMeanInput)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun h : ℕ => upperDensity (badSet ε h)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun h => ha.trans_le (upperDensity_nonneg _))
  · intro a ha
    filter_upwards [eventually_upperDensity_bad_le hMR hSmooth hε
      (show 0 < a / 2 by positivity)] with h hh
    linarith

/-- The good-set lower density is exactly the complement of the bad upper density. -/
theorem good_lowerDensity_eq (ε : ℝ) (k : ℕ) :
    lowerDensity (goodSet ε k) = 1 - upperDensity (badSet ε (k + 1)) := by
  apply lowerDensity_eq_one_sub_upperDensity
  intro n hn
  simp [goodSet, badSet, hn, not_le]

/-- Erdős problem #1201 as stated in the paper, conditional on the cited analytic inputs. -/
theorem erdos1201
    (hMR : ShortIntervalInput) (hSmooth : SmoothMeanInput)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ k : ℕ, 1 - η ≤ lowerDensity (goodSet ε k) := by
  obtain ⟨h, hh, hpos⟩ := ((eventually_upperDensity_bad_le hMR hSmooth hε hη).and
    (eventually_gt_atTop 0)).exists
  refine ⟨h - 1, ?_⟩
  rw [good_lowerDensity_eq, Nat.sub_add_cancel hpos]
  linarith

end Erdos1201
