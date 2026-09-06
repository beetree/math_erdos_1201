module

public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.Analysis.RCLike.TangentCone
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic.FunProp
public import Erdos1201.Vendor.Analysis.DiskAnalyticBounds.RectangleContourConstruction

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Complex MeasureTheory intervalIntegral
open scoped Interval

/-!
Bounds the rectangle-contour error term `Err` (via `S_horiz`/`S_vert`/`S_max`),
shows `Err(z,h)/h → 0` as `h → 0`, extends `I_f` to all of `ℂ`, and concludes
`I_f` is differentiable on the closed disk with `derivWithin I_f z = f z` —
i.e. `I_f` is a primitive of `f`.
-/

public section

namespace DiskAnalyticBounds

noncomputable def S_horiz (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
        r = ‖f (t + Complex.I * z.im) - f z‖}

noncomputable def S_vert (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  sSup {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
        r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}

noncomputable def S_max (z h : ℂ) (f : ℂ → ℂ) : ℝ :=
  max (S_horiz z h f) (S_vert z h f)

lemma bound_on_Err
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
  (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1) :
  ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖
      ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := by
  -- Unfold the error term and prepare to bound each piece
  unfold Err
  -- Triangle inequality for the sum
  have hsplit :
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
      ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
        + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ :=
    norm_add_le _ _

  -- Pull out the factor ‖I‖ = 1 on the vertical term
  have hI : ‖Complex.I‖ = (1 : ℝ) := by simp
  have hvertnorm :
      ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
        = ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by
    simp [norm_mul, hI, one_mul]

  -- Show the sets defining S_horiz/S_vert are bounded above via compactness of images
  set SH : Set ℝ := {r | ∃ t ∈ Set.uIcc z.re (z + h).re,
      r = ‖f (t + Complex.I * z.im) - f z‖}
  have hbdd_SH : BddAbove SH := by
    classical
    -- continuous map r(t) on a compact interval
    have hK : IsCompact (Set.uIcc z.re (z + h).re) := isCompact_uIcc
    -- path into the closed ball R
    let γ : ℝ → ℂ := fun t => (t : ℂ) + Complex.I * z.im
    have hγ_cont : Continuous γ := by
      show Continuous (fun t : ℝ => (t : ℂ) + Complex.I * z.im)
      fun_prop
    have hz_mem : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show (z.re : ℂ) + Complex.I * z.im = z.re + z.im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hz
    have hw_mem : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hw
    have hseg_subset :
        (γ '' Set.uIcc z.re (z + h).re) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim
      rcases hwim with ⟨t, ht, rfl⟩
      -- point on the horizontal segment between the two endpoints
      have hseg : ((t : ℂ) + Complex.I * z.im)
          ∈ segment ℝ ((z.re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * z.im) := by
        -- reparametrize uIcc as a segment in ℝ, then map affinely (inlined former
        -- horizontal_line_in_segment, specialized a:=z.im, b₁:=z.re, b₂:=(z+h).re)
        obtain ⟨lam, h_lam_nonneg, h_lam_le_one, h_t_eq⟩ :=
          real_between_as_convex_combination z.re (z + h).re t (by simpa [Set.mem_uIcc] using ht)
        have h_convex : (t : ℂ) + Complex.I * z.im
            = (1 - lam) • ((z.re : ℂ) + Complex.I * z.im) + lam • (((z + h).re : ℂ) + Complex.I * z.im) := by
          simp only [Complex.real_smul]
          rw [h_t_eq]
          simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
          ring
        rw [h_convex, ← AffineMap.lineMap_apply_module]
        exact lineMap_mem_segment ℝ ((z.re : ℂ) + Complex.I * z.im) (((z + h).re : ℂ) + Complex.I * z.im)
          ⟨h_lam_nonneg, h_lam_le_one⟩
      have hz_in : ((z.re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hz_mem
      have hw_in : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := hw_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simpa [Metric.mem_closedBall, dist_zero_right] using hw'
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
    -- compose with continuous path (restricted to uIcc)
    have hmaps : Set.MapsTo γ (Set.uIcc z.re (z + h).re) (Metric.closedBall (0 : ℂ) R) := by
      intro t ht
      have himg_r1 : γ t ∈ Metric.closedBall (0 : ℂ) r1 := by
        exact hseg_subset (Set.mem_image_of_mem _ ht)
      exact (Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_R)) himg_r1
    have hcont_on : ContinuousOn (fun t => f (γ t)) (Set.uIcc z.re (z + h).re) :=
      hf_cont.comp hγ_cont.continuousOn hmaps
    -- real-valued continuous map r(t) := ‖f (γ t) - f z‖
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun t => ‖f (γ t) - f z‖) (Set.uIcc z.re (z + h).re) := by
      -- first get continuity of f (γ t) - f z
      have h_cont_sub : ContinuousOn (fun t => f (γ t) - f z) (Set.uIcc z.re (z + h).re) :=
        hcont_on.sub continuousOn_const
      -- then apply norm
      exact h_cont_sub.norm
    -- image is compact, hence bounded above
    have himage_compact : IsCompact ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      IsCompact.image_of_continuousOn hK hR_cont
    -- Now, SH equals this image set
    have hSH_eq : SH = (fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re := by
      ext r; constructor
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
      · intro hr; rcases hr with ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
    -- Compact subset of ℝ is bounded above
    have : BddAbove ((fun t => ‖f (γ t) - f z‖) '' Set.uIcc z.re (z + h).re) :=
      himage_compact.bddAbove
    simpa [hSH_eq] using this

  set SV : Set ℝ := {r | ∃ τ ∈ Set.uIcc z.im (z + h).im,
      r = ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖}
  have hbdd_SV : BddAbove SV := by
    classical
    -- compactness of the vertical segment
    have hK : IsCompact (Set.uIcc z.im (z + h).im) := isCompact_uIcc
    let γv : ℝ → ℂ := fun τ => ((z + h).re : ℂ) + Complex.I * τ
    have hγv_cont : Continuous γv := by
      have hmul : Continuous (fun τ : ℝ => Complex.I * (τ : ℂ)) := by
        exact continuous_const.mul Complex.continuous_ofReal
      simp only [γv]
      exact continuous_const.add hmul
    have hw_mem' : (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hw
    have hzh_mem : (((z + h).re : ℂ) + Complex.I * (z + h).im) ∈ Metric.closedBall (0 : ℂ) r1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      rw [show ((z + h).re : ℂ) + Complex.I * (z + h).im = (z + h).re + (z + h).im * Complex.I by ring]
      rw [Complex.re_add_im]
      rwa [Metric.mem_closedBall, dist_zero_right] at hzh
    have hseg_subset :
        (γv '' Set.uIcc z.im (z + h).im) ⊆ Metric.closedBall (0 : ℂ) r1 := by
      intro w hwim; rcases hwim with ⟨τ, hτ, rfl⟩
      have hseg : (((z + h).re : ℂ) + Complex.I * τ)
          ∈ segment ℝ (((z + h).re : ℂ) + Complex.I * z.im)
                          (((z + h).re : ℂ) + Complex.I * (z + h).im) := by
        have := vertical_line_in_segment (((z + h).re : ℂ)) (b₁ := z.im) (b₂ := (z + h).im) (t := τ)
          (by simpa [Set.mem_uIcc] using hτ)
        simpa using this
      have hz_in := hw_mem'
      have hw_in := hzh_mem
      have hsubset := (convex_closedBall (0 : ℂ) r1).segment_subset hz_in hw_in
      have hw' := hsubset hseg
      simp only [γv, Metric.mem_closedBall, dist_zero_right] at hw'
      rwa [Metric.mem_closedBall, dist_zero_right]
    have hmaps : Set.MapsTo γv (Set.uIcc z.im (z + h).im) (Metric.closedBall (0 : ℂ) R) := by
      intro τ hτ; have : γv τ ∈ Metric.closedBall (0 : ℂ) r1 := hseg_subset (Set.mem_image_of_mem _ hτ)
      exact (Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_R)) this
    have hf_cont : ContinuousOn f (Metric.closedBall (0 : ℂ) R) := hf.continuousOn
    have hcont_on : ContinuousOn (fun τ => f (γv τ)) (Set.uIcc z.im (z + h).im) :=
      hf_cont.comp hγv_cont.continuousOn hmaps
    have hψ : Continuous (fun w : ℂ => ‖w - f z‖) :=
      (continuous_id.sub continuous_const).norm
    have hR_cont : ContinuousOn (fun τ => ‖f (γv τ) - f z‖) (Set.uIcc z.im (z + h).im) := by
      have h1 : ContinuousOn (fun τ => f (γv τ) - f z) (Set.uIcc z.im (z + h).im) := by
        exact hcont_on.sub continuousOn_const
      exact h1.norm
    have himage_compact : IsCompact ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      IsCompact.image_of_continuousOn hK hR_cont
    have hSV_eq : SV = (fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im := by
      ext r; constructor
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
      · intro hr; rcases hr with ⟨τ, hτ, rfl⟩; exact ⟨τ, hτ, rfl⟩
    have : BddAbove ((fun τ => ‖f (γv τ) - f z‖) '' Set.uIcc z.im (z + h).im) :=
      himage_compact.bddAbove
    simpa [hSV_eq] using this

  -- Pointwise bounds via membership in the sup-sets
  have hC_horiz : ∀ t ∈ Set.uIcc z.re (z + h).re,
      ‖(f (t + Complex.I * z.im) - f z)‖ ≤ S_horiz z h f := by
    intro t ht
    have hx : ‖f (t + Complex.I * z.im) - f z‖ ∈ SH := ⟨t, ht, rfl⟩
    -- S_horiz is the sSup of SH by definition
    have : S_horiz z h f = sSup SH := rfl
    simpa [this] using (le_csSup hbdd_SH hx)

  have hC_vert : ∀ τ ∈ Set.uIcc z.im (z + h).im,
      ‖(f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ S_vert z h f := by
    intro τ hτ
    have hx : ‖f (((z + h).re : ℂ) + Complex.I * τ) - f z‖ ∈ SV := ⟨τ, hτ, rfl⟩
    have : S_vert z h f = sSup SV := rfl
    simpa [this] using (le_csSup hbdd_SV hx)

  -- Apply ML-type bounds on both integrals
  have hH : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            ≤ |(z + h).re - z.re| * S_horiz z h f := by
    -- Convert from uIcc to interval bounds
    have h_bound : ∀ t, t ∈ [[z.re, (z + h).re]] → ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht; exact hC_horiz t ht
    have h_int : ∀ t ∈ Ι z.re (z + h).re, ‖f (↑t + Complex.I * ↑z.im) - f z‖ ≤ S_horiz z h f := by
      intro t ht
      have ht_uIcc : t ∈ Set.uIcc z.re (z + h).re := by
        -- uIoc_subset_uIcc: Ι a b ⊆ uIcc a b
        exact Set.uIoc_subset_uIcc ht
      exact h_bound t ht_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    convert this using 1
    ring

  have hV : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
            ≤ |(z + h).im - z.im| * S_vert z h f := by
    have h_bound : ∀ τ, τ ∈ [[z.im, (z + h).im]] → ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ; exact hC_vert τ hτ
    have h_int : ∀ τ ∈ Ι z.im (z + h).im, ‖f (↑(z + h).re + Complex.I * ↑τ) - f z‖ ≤ S_vert z h f := by
      intro τ hτ
      have hτ_uIcc : τ ∈ Set.uIcc z.im (z + h).im := by
        -- uIoc_subset_uIcc: Ι a b ⊆ uIcc a b
        exact Set.uIoc_subset_uIcc hτ
      exact h_bound τ hτ_uIcc
    have := intervalIntegral.norm_integral_le_of_norm_le_const h_int
    rwa [mul_comm] at this

  -- Simplify the interval lengths
  have hre' : (z + h).re - z.re = h.re := by
    simp [Complex.add_re, add_comm, add_left_comm, add_assoc, add_sub_cancel]
  have him' : (z + h).im - z.im = h.im := by
    simp [Complex.add_im, add_comm, add_left_comm, add_assoc, add_sub_cancel]
  have hre : |(z + h).re - z.re| = |h.re| := by simp [hre']
  have him : |(z + h).im - z.im| = |h.im| := by simp [him']

  -- Compare with S_max
  have hH' : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
                ≤ |h.re| * S_max z h f := by
    have : S_horiz z h f ≤ S_max z h f := by exact le_max_left _ _
    -- First rewrite hH using hre
    have hH_rewritten : ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖ ≤ |h.re| * S_horiz z h f := by
      rwa [hre] at hH
    -- Then apply the bound
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.re))
    exact le_trans hH_rewritten h_bound

  have hV' : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖
                ≤ |h.im| * S_max z h f := by
    have : S_vert z h f ≤ S_max z h f := by exact le_max_right _ _
    -- First rewrite hV using him
    have hV_rewritten : ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ ≤ |h.im| * S_vert z h f := by
      rwa [him] at hV
    -- Then apply the bound
    have h_bound := mul_le_mul_of_nonneg_left this (abs_nonneg (h.im))
    exact le_trans hV_rewritten h_bound

  -- Final combination
  have :=
    calc
      ‖(∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z))
        + Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖
          ≤ ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖Complex.I * (∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z))‖ := hsplit
      _ = ‖∫ t in z.re..(z + h).re, (f (t + Complex.I * z.im) - f z)‖
            + ‖∫ τ in z.im..(z + h).im, (f (((z + h).re : ℂ) + Complex.I * τ) - f z)‖ := by simp [hvertnorm]
      _ ≤ |h.re| * S_max z h f + |h.im| * S_max z h f := add_le_add hH' hV'

  simpa [Err] using this

lemma S_horiz_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_horiz z h f := by
  -- All elements of the set are norms, hence nonnegative
  unfold S_horiz
  apply Real.sSup_nonneg
  intro r hr; rcases hr with ⟨t, ht, rfl⟩; exact norm_nonneg _

lemma S_max_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_max z h f := by
  unfold S_max
  have h1 : 0 ≤ S_horiz z h f := S_horiz_nonneg z h f
  exact le_trans h1 (le_max_left _ _)

lemma bound_on_Err_ratio
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z h : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1)
    (hzh : z + h ∈ Metric.closedBall (0 : ℂ) r1)
    (hw : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) r1)
    (hh : h ≠ 0) :
    ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤ 2 * S_max z h f := by
  -- Since norm z = ‖z‖, rewrite goal using norm
  -- change norm to norm
  have h_abs_eq : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ = ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ := rfl

  -- Start with the inequality from bound_on_Err (as mentioned in informal proof)
  have h1 := bound_on_Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz hzh hw
  -- Factor out S_max: |h.re| * S_max + |h.im| * S_max = (|h.re| + |h.im|) * S_max
  rw [← add_mul] at h1
  -- Now h1: ‖Err‖ ≤ (|h.re| + |h.im|) * S_max

  -- Since h ≠ 0, we have ‖h‖ > 0 (as mentioned in informal proof)
  have h_norm_pos : 0 < ‖h‖ := norm_pos_iff.mpr hh

  -- Divide the inequality by |h| (as mentioned in informal proof)
  have h2 : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h‖ / ‖h‖ ≤
            (|h.re| + |h.im|) * S_max z h f / ‖h‖ := by
    exact div_le_div_of_nonneg_right h1 (le_of_lt h_norm_pos)

  -- Use the property |A/B| = |A|/|B| (as mentioned in informal proof)
  -- The left side becomes ‖Err/h‖
  rw [← norm_div] at h2

  -- Rearrange the right side to get (|h.re| + |h.im|) / ‖h‖ * S_max
  -- We need: (a * b) / c = (a / c) * b
  have h2' : ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖ ≤
             (|h.re| + |h.im|) / ‖h‖ * S_max z h f := by
    rw [← div_mul_eq_mul_div] at h2
    exact h2

  -- Use the bound |h.re| + |h.im| ≤ 2‖h‖ (as mentioned in informal proof)
  have h3 : |h.re| + |h.im| ≤ 2 * ‖h‖ := by
    -- "For any complex number h, |h.re| ≤ |h| and |h.im| ≤ |h|"
    calc |h.re| + |h.im|
      ≤ ‖h‖ + ‖h‖ := add_le_add (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
      _ = 2 * ‖h‖ := by ring

  -- Therefore (|h.re| + |h.im|) / ‖h‖ ≤ 2 (as mentioned in informal proof)
  have h4 : (|h.re| + |h.im|) / ‖h‖ ≤ 2 := by
    -- "This gives us a bound for the fraction: (|h.re| + |h.im|) / |h| ≤ 2|h| / |h| = 2"
    rw [div_le_iff₀ h_norm_pos]
    exact h3

  -- Final step: combine everything (as mentioned in informal proof)
  calc ‖Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h‖
    ≤ (|h.re| + |h.im|) / ‖h‖ * S_max z h f := h2'
    _ ≤ 2 * S_max z h f := mul_le_mul_of_nonneg_right h4 (S_max_nonneg z h f)
open Filter Topology

lemma abs_horizontal_diff_eq_abs_real (z : ℂ) (t : ℝ) : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := by
  have h : (t : ℂ) + Complex.I * z.im - z = ((t - z.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [h, Complex.norm_real, Real.norm_eq_abs]

lemma abs_sub_le_of_mem_uIcc (a b t : ℝ) (ht : t ∈ Set.uIcc a b) : |t - a| ≤ |b - a| ∧ |b - t| ≤ |b - a| := by
  -- Reduce to cases using uIcc and abs_sub_le_iff
  have h1 : a ≤ b ∨ b ≤ a := le_total a b
  rcases h1 with hle | hle
  · -- a ≤ b: uIcc a b = Icc a b
    have ht' : t ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : a ≤ t ∧ t ≤ b := by simpa using ht'
    constructor
    · have h_ta : |t - a| = t - a := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.left)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_right h_bounds.right a
    · have h_bt : |b - t| = b - t := by simp [abs_of_nonneg (sub_nonneg.mpr h_bounds.right)]
      have h_ba : |b - a| = b - a := by simp [abs_of_nonneg (sub_nonneg.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_left h_bounds.left b
  · -- b ≤ a: symmetric case
    have ht' : t ∈ Set.Icc b a := by
      rw [Set.uIcc_comm] at ht
      simpa [Set.uIcc_of_le hle] using ht
    have h_bounds : b ≤ t ∧ t ≤ a := by simpa using ht'
    constructor
    · have h_ta : |t - a| = a - t := by simp [abs_of_nonpos (sub_nonpos.mpr h_bounds.right)]
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_ta, h_ba]
      exact sub_le_sub_left h_bounds.left a
    · have h_bt : |b - t| = t - b := by
        rw [abs_of_nonpos (sub_nonpos.mpr h_bounds.left)]
        ring
      have h_ba : |b - a| = a - b := by simp [abs_of_nonpos (sub_nonpos.mpr hle)]
      rw [h_bt, h_ba]
      exact sub_le_sub_right h_bounds.right b

lemma sub_ofReal_add_I (a b c d : ℝ) : ((a : ℂ) + Complex.I * b) - ((c : ℂ) + Complex.I * d) = ((a - c : ℝ) : ℂ) + Complex.I * (b - d) := by
  apply Complex.ext
  · -- Real part
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.I_mul_re, Complex.ofReal_im, neg_zero, add_zero, sub_zero]
    -- Now need to show: a - c = a - c + -(↑b - ↑d).im
    -- Use that ↑b - ↑d = ↑(b - d) and then (↑(b - d)).im = 0
    rw [← Complex.ofReal_sub, Complex.ofReal_im, neg_zero, add_zero]
  · -- Imaginary part
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re, zero_add, zero_sub]
    -- Now need to show: b - d = (↑b - ↑d).re
    -- Use that ↑b - ↑d = ↑(b - d) and then (↑(b - d)).re = b - d
    rw [← Complex.ofReal_sub, Complex.ofReal_re]

lemma norm_I_mul_ofReal (b : ℝ) : ‖Complex.I * (b : ℂ)‖ = |b| := by
  simp [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]

lemma S_vert_nonneg (z h : ℂ) (f : ℂ → ℂ) : 0 ≤ S_vert z h f := by
  unfold S_vert
  apply Real.sSup_nonneg
  intro r hr; rcases hr with ⟨τ, hτ, rfl⟩; exact norm_nonneg _

lemma limit_of_S_is_zero
    {r1 R R0 : ℝ}
  (_hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (_hR_lt_R0 : R < R0) (_hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) := by
  -- Use the continuity of f at z (which follows from analyticity)
  have f_cont_at_z : ContinuousAt f z := by
    -- z is in the closed ball r1 which is contained in closed ball R
    have hz_in_R : z ∈ Metric.closedBall (0 : ℂ) R :=
      Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_R) hz
    -- Analytic functions are continuous
    exact (hf z hz_in_R).continuousAt

  -- Inline of the deleted tendsto_of_nonneg_local_bound, specialized to g := fun h => S_max z h f
  have local_tendsto : ∀ {g : ℂ → ℝ}, (∀ h, 0 ≤ g h) →
      (∀ ε > 0, ∃ δ > 0, ∀ h, ‖h‖ < δ → g h ≤ ε) → Tendsto g (𝓝 (0:ℂ)) (𝓝 (0:ℝ)) := by
    intro g h_nonneg h_loc
    rw [Metric.tendsto_nhds_nhds]
    intro ε hε
    have hε_half : (0 : ℝ) < ε / 2 := by linarith
    obtain ⟨δ, hδ_pos, hδ⟩ := h_loc (ε / 2) hε_half
    use δ
    exact ⟨hδ_pos, fun h hh_dist => by
      rw [Real.dist_eq, sub_zero]
      rw [abs_of_nonneg (h_nonneg h)]
      have : g h ≤ ε / 2 := hδ h (by rwa [Complex.dist_eq, sub_zero] at hh_dist)
      linarith⟩
  apply local_tendsto
  · -- Show S_max z h f ≥ 0 for all h
    exact fun h => S_max_nonneg z h f
  · -- Show local bound: for ε > 0, ∃ δ > 0, ‖h‖ < δ → S_max z h f ≤ ε
    intro ε hε_pos
    -- Use continuity of f at z to get δ
    rw [Metric.continuousAt_iff] at f_cont_at_z
    obtain ⟨δ₁, hδ₁_pos, hf_bound⟩ := f_cont_at_z ε hε_pos

    -- Choose δ = δ₁ / 2 (to handle the factor of 2 in the vertical case)
    use δ₁ / 2
    constructor
    · exact half_pos hδ₁_pos
    · intro h hh_norm
      -- Need to show S_max z h f ≤ ε
      -- S_max = max of S_horiz and S_vert, so bound both
      unfold S_max
      apply max_le

      -- Bound S_horiz following the informal proof
      · unfold S_horiz
        -- Use Real.sSup_le to bound the supremum
        apply Real.sSup_le
        · -- Show all elements in the set are ≤ ε
          intro r hr
          obtain ⟨t, ht, rfl⟩ := hr
          -- Show norm (f(t + I*z.im) - f z) ≤ ε
          -- Key insight: show dist ((t : ℂ) + Complex.I * z.im) z < δ₁
          have key_dist : dist ((t : ℂ) + Complex.I * z.im) z < δ₁ := by
            -- Use the horizontal distance lemma and bound |t - z.re|
            rw [dist_eq]
            -- Since norm = ‖·‖, we can use the horizontal distance lemma
            have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| := abs_horizontal_diff_eq_abs_real z t
            simp [eq_transform]
            -- Bound |t - z.re| by |(z+h).re - z.re| then by ‖h‖
            have t_bound : |t - z.re| ≤ |(z + h).re - z.re| := (abs_sub_le_of_mem_uIcc z.re (z + h).re t ht).1
            have re_diff_le : |(z + h).re - z.re| ≤ ‖h‖ := by
              -- (z+h).re - z.re = h.re
              simpa [Complex.add_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (Complex.abs_re_le_norm h)
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            calc |t - z.re|
              _ ≤ |(z + h).re - z.re| := t_bound
              _ ≤ ‖h‖ := re_diff_le
              _ < δ₁ / 2 := h_bound
              _ < δ₁ := by linarith
          -- Apply continuity to get the bound
          have f_dist := hf_bound key_dist
          -- Convert dist back to norm for the conclusion
          rw [dist_eq] at f_dist
          -- Already in norm form
          exact le_of_lt f_dist
        · -- Show 0 ≤ ε
          exact le_of_lt hε_pos

      -- Bound S_vert following the informal proof
      · unfold S_vert
        apply Real.sSup_le
        · -- Show all elements in the set are ≤ ε
          intro r hr
          obtain ⟨τ, hτ, rfl⟩ := hr
          -- Show norm (f((z+h).re + I*τ) - f z) ≤ ε
          have key_dist : dist (((z + h).re : ℂ) + Complex.I * τ) z < δ₁ := by
            rw [dist_eq]
            -- The key insight: ‖w_τ - z‖ ≤ |h.re| + |τ - z.im| ≤ |h.re| + |h.im| ≤ 2‖h‖
            -- First, express the difference in terms of h.re and (τ - z.im)
            have h_eq : (((z + h).re : ℂ) + Complex.I * τ - z) = (h.re : ℝ) + Complex.I * (τ - z.im) := by
              apply Complex.ext_iff.mpr
              constructor
              · simp [Complex.add_re, Complex.sub_re]
              · simp [Complex.add_im, Complex.sub_im]
            rw [h_eq]
            -- Bound |τ - z.im| by |(z+h).im - z.im| = |h.im|
            have τ_bound0 : |τ - z.im| ≤ |(z + h).im - z.im| := (abs_sub_le_of_mem_uIcc z.im (z + h).im τ hτ).1
            have im_diff_eq : |(z + h).im - z.im| = |h.im| := by
              simp [Complex.add_im, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            have τ_bound : |τ - z.im| ≤ |h.im| := by simpa [im_diff_eq] using τ_bound0
            -- Use the triangle inequality bound from the context
            have vertical_bound : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |h.re| + |τ - z.im| := by
              have h1 : ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖ ≤ |((h.re : ℝ) + Complex.I * (τ - z.im)).re| + |((h.re : ℝ) + Complex.I * (τ - z.im)).im| :=
                Complex.norm_le_abs_re_add_abs_im _
              have h2 : ((h.re : ℝ) + Complex.I * (τ - z.im)).re = h.re := by simp
              have h3 : ((h.re : ℝ) + Complex.I * (τ - z.im)).im = τ - z.im := by simp
              rwa [h2, h3] at h1
            have sum_bound : |h.re| + |τ - z.im| ≤ |h.re| + |h.im| := by
              linarith [τ_bound]
            have norm_bound : |h.re| + |h.im| ≤ (2:ℝ) * ‖h‖ := by
              have := add_le_add (Complex.abs_re_le_norm h) (Complex.abs_im_le_norm h)
              simpa [two_mul] using this
            have h_bound : ‖h‖ < δ₁ / 2 := hh_norm
            have final_bound : (2:ℝ) * ‖h‖ < δ₁ := by
              have := mul_lt_mul_of_pos_left h_bound (by norm_num : (0:ℝ) < 2)
              simpa [two_mul, add_halves] using this
            calc ‖(h.re : ℝ) + Complex.I * (τ - z.im)‖
              _ ≤ |h.re| + |τ - z.im| := vertical_bound
              _ ≤ |h.re| + |h.im| := sum_bound
              _ ≤ (2 : ℝ) * ‖h‖ := norm_bound
              _ < δ₁ := final_bound
          -- Apply continuity to get the bound
          have f_dist := hf_bound key_dist
          rw [dist_eq] at f_dist
          -- Already in norm form
          exact le_of_lt f_dist
        · -- Show 0 ≤ ε
          exact le_of_lt hε_pos

lemma eventually_corner_and_sum_in_closedBall {z : ℂ} {R' : ℝ}
  (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    (z + h) ∈ Metric.closedBall (0 : ℂ) R' ∧
    (((z + h).re : ℂ) + Complex.I * z.im) ∈ Metric.closedBall (0 : ℂ) R' := by
  -- Let ρ = R' - ‖z‖ > 0
  have hρ_pos : 0 < R' - ‖z‖ := sub_pos.mpr hz
  have h_small : ∀ᶠ h in 𝓝 (0:ℂ), h ∈ Metric.ball (0 : ℂ) (R' - ‖z‖) :=
    Metric.ball_mem_nhds (0 : ℂ) hρ_pos
  refine h_small.mono ?_
  intro h hhball
  have hnorm_lt : ‖h‖ < R' - ‖z‖ := by
    simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hhball
  -- First membership: z + h ∈ closedBall 0 R'
  have hsum_lt : ‖z‖ + ‖h‖ < R' := by
    have htemp : ‖z‖ + ‖h‖ < ‖z‖ + (R' - ‖z‖) := by linarith [hnorm_lt]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htemp
  have hzph_le : ‖z + h‖ ≤ R' :=
    le_of_lt (lt_of_le_of_lt (norm_add_le _ _) hsum_lt)
  have hzph_mem : (z + h) ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hzph_le
  -- Second membership: w ∈ closedBall 0 R' for w = ((z+h).re) + I z.im
  let w : ℂ := ((z + h).re : ℂ) + Complex.I * z.im
  -- Triangle inequality relative to z: ‖w‖ ≤ ‖w - z‖ + ‖z‖
  have tri : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
    have := norm_add_le (w - z) z
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- Compute and bound ‖w - z‖ ≤ ‖h‖ via horizontal distance
  let t : ℝ := (z + h).re
  have hwz_eq : w - z = (t : ℂ) + Complex.I * z.im - z := by
    simp [w, t, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have eq_transform : ‖(t : ℂ) + Complex.I * z.im - z‖ = |t - z.re| :=
    abs_horizontal_diff_eq_abs_real z t
  have t_sub_re : t - z.re = h.re := by
    simp [t, Complex.add_re, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hwz_abs2 : ‖w - z‖ = |h.re| := by
    simpa [hwz_eq, t_sub_re] using eq_transform
  have hwz_le : ‖w - z‖ ≤ ‖h‖ := by
    simpa [hwz_abs2] using (Complex.abs_re_le_norm h)
  have hw_le'' : ‖w‖ ≤ ‖h‖ + ‖z‖ := by
    exact le_trans tri (by linarith [hwz_le])
  have hw_lt : ‖w‖ < R' := by
    have : ‖h‖ + ‖z‖ < R' := by simpa [add_comm] using hsum_lt
    exact lt_of_le_of_lt hw_le'' this
  have hw_mem : w ∈ Metric.closedBall (0 : ℂ) R' := by
    simpa [w, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using (le_of_lt hw_lt)
  exact And.intro hzph_mem hw_mem


lemma limit_of_Err_ratio_is_zero
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r1) :
    Tendsto (fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
  -- Define the target function g(h) = Err(z,h)/h
  set g : ℂ → ℂ := fun h => Err hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf z h / h
  -- S_max → 0 as h → 0 (given)
  have hS : Tendsto (fun h => S_max z h f) (𝓝 0) (𝓝 0) :=
    limit_of_S_is_zero (r1:=r1) (R:=R) (R0:=R0) hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hf hz
  -- Hence |2 * S_max| → 0 by continuity
  have h_upper : Tendsto (fun h => |(2 : ℝ) * S_max z h f|) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous fun x : ℝ => |(2 : ℝ) * x| :=
      (continuous_const.mul continuous_id).abs
    have h0 := hcont.tendsto (0 : ℝ)
    have hcomp := h0.comp hS
    unfold Function.comp at hcomp
    simpa using hcomp
  -- Lower bound: 0 ≤ ‖g h‖ holds everywhere
  have h_lower_nonneg : ∀ᶠ h in 𝓝 0, 0 ≤ ‖g h‖ :=
    Filter.Eventually.of_forall (fun _ => by simpa [g] using (norm_nonneg (g _)))
  -- Choose δ = (R - r1)/2 > 0 and set R' = r1 + δ so that r1 < R' < R
  let δ : ℝ := (R - r1) / 2
  have hδ_pos : 0 < δ := by
    have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
    simpa [δ] using half_pos this
  let R' : ℝ := r1 + δ
  have hR'_pos : 0 < R' := by
    have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
    simpa [R'] using this
  have hR'_lt_R : R' < R := by
    have hδlt : δ < R - r1 := by
      simpa [δ] using (half_lt_self (sub_pos.mpr hr1_lt_R))
    have : r1 + δ < r1 + (R - r1) := by linarith [hδlt]
    simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  -- z lies in the R'-closed ball
  have hz_le_r1 : ‖z‖ ≤ r1 := by
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have hr1_le_R' : r1 ≤ R' := by
      have : 0 ≤ δ := le_of_lt hδ_pos
      simpa [R'] using (le_add_of_nonneg_right this : r1 ≤ r1 + δ)
    have : ‖z‖ ≤ R' := le_trans hz_le_r1 hr1_le_R'
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
  -- Eventual upper bound: for small h, z + h ∈ closedBall 0 R', then apply bound_on_Err_ratio with R'
  have h_event : ∀ᶠ h in 𝓝 0, ‖g h‖ ≤ |(2 : ℝ) * S_max z h f| := by
    -- Use the event that ensures both z+h and the mixed corner lie in the smaller ball R'
    have hcorner := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') (hz := by
      -- from ‖z‖ ≤ r1 and r1 < R', we have ‖z‖ < R'
      have : ‖z‖ ≤ r1 := hz_le_r1
      exact lt_of_le_of_lt this (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos)))
    refine hcorner.mono ?_
    intro h hh
    have hzh' : z + h ∈ Metric.closedBall (0 : ℂ) R' := hh.1
    have hw' : ((z + h).re : ℂ) + Complex.I * z.im ∈ Metric.closedBall (0 : ℂ) R' := hh.2
    by_cases hh0 : h = 0
    · have : 0 ≤ |(2 : ℝ) * S_max z h f| := abs_nonneg _
      simp [g, hh0, div_zero, norm_zero]
    · -- apply the ratio bound with radius R'
      have hb :=
        bound_on_Err_ratio (r1:=R') (R:=R) (R0:=R0)
          hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (h:=h) hz' hzh' hw' hh0
      have hb' : ‖g h‖ ≤ 2 * S_max z h f := by
        simpa [g, norm, Err] using hb
      exact le_trans hb' (le_abs_self ((2 : ℝ) * S_max z h f))
  -- Apply squeeze theorem to the norm
  have h_norm_tendsto : Tendsto (fun h => ‖g h‖) (𝓝 0) (𝓝 0) := by
    refine Filter.Tendsto.squeeze' tendsto_const_nhds h_upper h_lower_nonneg h_event
  -- Convert from norm convergence to complex convergence
  have h_dist_tendsto : Tendsto (fun h => dist (g h) 0) (𝓝 0) (𝓝 0) := by
    simpa [dist_eq_norm] using h_norm_tendsto
  simpa [g] using (tendsto_iff_dist_tendsto_zero).2 h_dist_tendsto

open Classical
/-- Extend `If_taxicab` to a total function on `ℂ` by zero outside the closed ball. -/
@[expose] noncomputable def If_ext
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) : ℂ → ℂ :=
  fun w =>
    if h : w ∈ Metric.closedBall (0 : ℂ) r1 then
      If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, h⟩
    else
      0

lemma If_ext_eq_taxicab_of_mem {r1 R R0 : ℝ} (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ} (hw : w ∈ Metric.closedBall (0 : ℂ) r1) :
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
      = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
  classical
  simp [If_ext, hw]

lemma If_taxicab_param_invariance {r1₁ r1₂ R R0 : ℝ}
    (hr1₁_pos : 0 < r1₁) (hr1₁_lt_R : r1₁ < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    (hr1₂_pos : 0 < r1₂) (hr1₂_lt_R : r1₂ < R)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
    {w : ℂ}
    (hw₁ : w ∈ Metric.closedBall (0 : ℂ) r1₁)
    (hw₂ : w ∈ Metric.closedBall (0 : ℂ) r1₂) :
    If_taxicab hr1₁_pos hr1₁_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₁⟩
    = If_taxicab hr1₂_pos hr1₂_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw₂⟩ := by
  -- The definition of If_taxicab depends only on the underlying complex number w
  -- and not on the radius parameter; unfolding both sides gives identical expressions.
  simp [If_taxicab]


lemma eventually_decomposition_for_ext
  {R' R R0 : ℝ} (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  (z : ℂ) (hz : ‖z‖ < R') :
  ∀ᶠ h in 𝓝 (0:ℂ),
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
    g (z + h) - g z = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
  -- Eventually, both z+h and the corner lie in the closed ball of radius R'.
  have h_event := eventually_corner_and_sum_in_closedBall (z:=z) (R':=R') hz
  refine h_event.mono ?_
  intro h hh
  -- Define g
  let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
  -- z is in the closed ball of radius R' since ‖z‖ < R'
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
  -- Rewrite g at the two points using the definition of If_ext on the ball
  have hgzh : g (z + h)
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z + h) hh.1
  have hgz : g z
      = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
    simpa [g] using
      If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=z) hz'
  -- Apply the decomposition lemma for If_taxicab on radius R'
  have H :=
    If_diff_decomposition_final (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one (f:=f) (hf:=hf)
      (z:=z) (h:=h)
      (hz:=hz') (hzh:=hh.1) (hw:=hh.2)
  -- Conclude by rewriting g using hgzh and hgz
  calc
    g (z + h) - g z
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hh.1⟩
          - If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz'⟩ := by
            simp [hgzh, hgz]
    _ = f z * h + Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h := by
      simpa using H

lemma tendsto_Err_ratio_radius (R' R R0 : ℝ) (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z : ℂ} (hz : ‖z‖ < R') :
  Tendsto (fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h / h) (𝓝 0) (𝓝 0) := by
  -- From ‖z‖ < R', we have z ∈ closedBall 0 R'
  have hz' : z ∈ Metric.closedBall (0 : ℂ) R' := by
    have : ‖z‖ ≤ R' := le_of_lt hz
    simpa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] using this
  -- Apply the general limit lemma with radius R'
  simpa using
    (limit_of_Err_ratio_is_zero (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf (z:=z) (hz:=hz'))

lemma If_ext_eq_taxicab_at_sum {R' R R0 : ℝ} (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z h : ℂ}
  (hzh : z + h ∈ Metric.closedBall (0 : ℂ) R') :
  If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (z + h)
  = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z + h, hzh⟩ := by
  simpa using
    (If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one (f:=f) (hf:=hf) (w:=z + h) hzh)

lemma If_ext_eq_taxicab_at_point {R' R R0 : ℝ} (hR'_pos : 0 < R') (hR'_lt_R : R' < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R))
  {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) R') :
  If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z
  = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨z, hz⟩ := by
  simpa using
    (If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0)
      hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one (f:=f) (hf:=hf) (w:=z) hz)

lemma differentiableOn_of_hasDerivWithinAt {f : ℂ → ℂ} {s : Set ℂ} {F : ℂ → ℂ}
  (h : ∀ z ∈ s, HasDerivWithinAt f (F z) s z) : DifferentiableOn ℂ f s := by
  intro z hz
  exact (h z hz).differentiableWithinAt

lemma If_ext_agree_on_smallBall {r1 R' R R0 : ℝ}
  (hr1_pos : 0 < r1) (hR'_pos : 0 < R') (hr1_lt_R : r1 < R) (hR'_lt_R : R' < R) (hr1_lt_R' : r1 < R') (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
  {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
  Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
           (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
           (Metric.closedBall (0 : ℂ) r1) := by
  intro w hw
  -- From hw : w ∈ closedBall 0 r1 and r1 < R', we also have w ∈ closedBall 0 R'
  have hw' : w ∈ Metric.closedBall (0 : ℂ) R' :=
    Metric.closedBall_subset_closedBall (le_of_lt hr1_lt_R') hw
  -- Rewrite both sides using the definition of If_ext on the ball
  have hleft :
      If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=r1) (R:=R) (R0:=R0)
        hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw)
  have hright :
      If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := by
    simpa using
      (If_ext_eq_taxicab_of_mem (r1:=R') (R:=R) (R0:=R0)
        hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf (w:=w) hw')
  -- Use parameter invariance of If_taxicab
  have hparam :=
    If_taxicab_param_invariance (r1₁:=r1) (r1₂:=R') (R:=R) (R0:=R0)
      hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one hR'_pos hR'_lt_R hf (w:=w) hw hw'
  -- Chain equalities
  calc
    If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf w
        = If_taxicab hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw⟩ := hleft
    _ = If_taxicab hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf ⟨w, hw'⟩ := hparam
    _ = If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf w := by
          simpa using hright.symm

lemma hasDerivAt_of_local_decomposition' (g : ℂ → ℂ) (z F : ℂ)
  (Err_func : ℂ → ℂ)
  (hdecomp : ∀ᶠ h in 𝓝 (0:ℂ), g (z + h) - g z = F * h + Err_func h)
  (hErr : Tendsto (fun h => Err_func h / h) (𝓝 (0:ℂ)) (𝓝 (0:ℂ))) :
  HasDerivAt g F z := by
  -- Restrict the decomposition to the punctured neighborhood
  have hdecomp_within : ∀ᶠ h in 𝓝[≠] (0:ℂ), g (z + h) - g z = F * h + Err_func h :=
    (hdecomp.filter_mono (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ)))
  -- On the punctured neighborhood, we also have eventually h ≠ 0
  have h_ne0 : ∀ᶠ h in 𝓝[≠] (0:ℂ), h ≠ 0 :=
    Filter.eventually_iff.mpr self_mem_nhdsWithin
  -- On (nhds[≠] 0), the slope equals F + Err h / h
  have h_eq_slope : ∀ᶠ h in 𝓝[≠] (0:ℂ),
      h⁻¹ • (g (z + h) - g z) = F + Err_func h / h := by
    refine (hdecomp_within.and h_ne0).mono ?_
    intro h hh
    rcases hh with ⟨hEq, hne⟩
    -- Start from the decomposition and divide by h
    have H0 : h⁻¹ • (g (z + h) - g z) = h⁻¹ • (F * h + Err_func h) := by
      simpa using congrArg (fun x => h⁻¹ • x) hEq
    -- Simplify the RHS algebraically
    have h1 : h⁻¹ * (F * h) = F := by
      have hne' : h ≠ 0 := hne
      calc
        h⁻¹ * (F * h) = F * (h⁻¹ * h) := by
          ac_rfl
        _ = F * 1 := by simp [hne']
        _ = F := by simp
    have h2 : h⁻¹ * Err_func h = Err_func h / h := by
      simp [div_eq_mul_inv, mul_comm]
    calc
      h⁻¹ • (g (z + h) - g z)
          = h⁻¹ • (F * h + Err_func h) := H0
      _ = h⁻¹ * (F * h + Err_func h) := by simp [smul_eq_mul]
      _ = h⁻¹ * (F * h) + h⁻¹ * (Err_func h) := by simp [mul_add]
      _ = F + Err_func h / h := by simp [h1, h2]
  -- Limit of the RHS: F + Err h / h → F
  have hErr_within : Tendsto (fun h => Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (0:ℂ)) :=
    hErr.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
  have h_const : Tendsto (fun _ : ℂ => F) (𝓝[≠] (0:ℂ)) (𝓝 F) := tendsto_const_nhds
  have h_sum : Tendsto (fun h => F + Err_func h / h) (𝓝[≠] (0:ℂ)) (𝓝 (F + 0)) :=
    h_const.add hErr_within
  have h_target : Tendsto (fun h => h⁻¹ • (g (z + h) - g z)) (𝓝[≠] (0:ℂ)) (𝓝 F) := by
    have := (Filter.tendsto_congr' h_eq_slope).2 h_sum
    simpa [zero_add] using this
  -- Conclude by the slope characterization of the derivative
  exact (hasDerivAt_iff_tendsto_slope_zero).2 h_target

lemma If_is_differentiable_on
    {r1 R R0 : ℝ}
    (hr1_pos : 0 < r1) (hr1_lt_R : r1 < R) (hR_lt_R0 : R < R0) (hR0_lt_one : R0 < 1)
    {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) R)) :
    DifferentiableOn ℂ (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1)
    ∧
    ∀ z ∈ Metric.closedBall (0 : ℂ) r1,
      derivWithin (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (Metric.closedBall (0 : ℂ) r1) z = f z := by
  set s : Set ℂ := Metric.closedBall (0 : ℂ) r1
  have hHasDerivWithinAt : ∀ z ∈ s,
      HasDerivWithinAt (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf) (f z) s z := by
    intro z hz
    -- Choose an intermediate radius R' with r1 < R' < R
    let δ : ℝ := (R - r1) / 2
    have hδ_pos : 0 < δ := by
      have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
      simpa [δ] using half_pos this
    let R' : ℝ := r1 + δ
    have hR'_pos : 0 < R' := by
      have : 0 < r1 + δ := add_pos_of_pos_of_nonneg hr1_pos (le_of_lt hδ_pos)
      simpa [R'] using this
    have hR'_lt_R : R' < R := by
      have hδlt : δ < R - r1 := by
        have : 0 < R - r1 := sub_pos.mpr hr1_lt_R
        simpa [δ] using (half_lt_self this)
      have : r1 + δ < r1 + (R - r1) := by linarith [hδlt]
      simpa [R', sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hr1_lt_R' : r1 < R' := by
      have : r1 < r1 + δ := by simpa [add_comm, add_left_comm, add_assoc, R', δ] using (lt_of_le_of_lt (le_of_eq rfl) (add_lt_add_left hδ_pos r1))
      simpa [R'] using this
    -- z is strictly inside the R'-ball
    have hz_le_r1 : ‖z‖ ≤ r1 := by
      simpa [s, Metric.mem_closedBall, Complex.dist_eq, sub_zero] using hz
    have hz_lt_R' : ‖z‖ < R' := lt_of_le_of_lt hz_le_r1 (by simpa [R'] using (lt_add_of_pos_right r1 hδ_pos))
    -- Define g as the extension at radius R'
    let g := If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf
    -- Local decomposition for g around z
    have hdecomp := eventually_decomposition_for_ext (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf z hz_lt_R'
    -- Error ratio tends to zero
    have hErr := tendsto_Err_ratio_radius (R':=R') (R:=R) (R0:=R0) hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one hf hz_lt_R'
    -- Conclude derivative exists for g at z with derivative f z
    have hDerivAt_g : HasDerivAt g (f z) z :=
      hasDerivAt_of_local_decomposition' (g := g) (z := z) (F := f z)
        (Err_func := fun h => Err hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf z h)
        (hdecomp := by
          -- adjust the eventual decomposition to match hasDerivAt_of_local_decomposition'
          simpa [g] using hdecomp)
        (hErr := by
          -- convert real-valued limit to complex-valued (same statement)
          simpa using hErr)
    -- Turn into a within-derivative on s for g
    have hWithin_g : HasDerivWithinAt g (f z) s z := hDerivAt_g.hasDerivWithinAt
    -- Use equality of If_ext on s for radii r1 and R'
    have hEq : Set.EqOn (If_ext hr1_pos hr1_lt_R hR_lt_R0 hR0_lt_one f hf)
                        (If_ext hR'_pos hR'_lt_R hR_lt_R0 hR0_lt_one f hf)
                        s :=
      If_ext_agree_on_smallBall (r1:=r1) (R':=R') (R:=R) (R0:=R0)
        hr1_pos hR'_pos hr1_lt_R hR'_lt_R hr1_lt_R' hR_lt_R0 hR0_lt_one hf
    -- Transfer the derivative along equality on s
    exact HasDerivWithinAt.congr_of_mem hWithin_g (fun x hx => hEq hx) hz
  -- First goal: DifferentiableOn
  refine And.intro ?hdiff ?hderiv
  · -- differentiability on s from existence of derivative within at each point
    apply differentiableOn_of_hasDerivWithinAt
    intro z hz
    exact hHasDerivWithinAt z hz
  · -- compute the derivative within s
    intro z hz
    have hUD : UniqueDiffWithinAt ℂ s z := by
      have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) r1) := convex_closedBall (0 : ℂ) r1
      have hnonempty : (interior (Metric.closedBall (0 : ℂ) r1)).Nonempty := by
        have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r1 := by
          simpa [Metric.mem_ball, Complex.dist_eq, sub_zero] using hr1_pos
        exact ⟨0, Metric.ball_subset_interior_closedBall h0mem⟩
      have hz_cl : z ∈ closure (Metric.closedBall (0 : ℂ) r1) := subset_closure (by simpa [s] using hz)
      exact uniqueDiffWithinAt_convex_of_isRCLikeNormedField hconv hnonempty hz_cl
    have hD := hHasDerivWithinAt z hz
    simpa using hD.derivWithin hUD


open scoped Topology


end DiskAnalyticBounds
