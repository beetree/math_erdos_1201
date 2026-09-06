module

public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.flexible false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
Generic complex-analysis infrastructure over the closed unit-ish disk: norm and
trigonometric algebra, analytic-continuation-to-closed-ball lemmas, the extreme
value theorem on a closed disk, and the maximum-modulus principle.
-/

public section

namespace DiskAnalyticBounds

lemma lem_log2tlogt2 (t : ℝ) (ht : t ≥ 2) : Real.log (2 * t) ≤ Real.log (t ^ 2) := by
  apply Real.log_le_log (by linarith)
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ t) (by linarith : (0:ℝ) ≤ t - 2)]

lemma lem_log22log (t : ℝ) (ht : t ≥ 2) : Real.log (2 * t) ≤ 2 * Real.log t := by
  have hlog : Real.log (t ^ 2) = 2 * Real.log t := by exact_mod_cast Real.log_pow t 2
  rw [← hlog]
  exact lem_log2tlogt2 t ht

lemma lem_niyelog (n : ℕ) (hn : n ≥ 1) (y : ℝ) : (n : ℂ) ^ (-y * Complex.I) = Complex.exp (-y * Complex.I * Real.log (n : ℝ)) := by
  have h1 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp hn)
  rw [Complex.cpow_def_of_ne_zero h1, ← Complex.natCast_log]
  ring_nf

lemma lem_eacosalog (n : ℕ) (_hn : n ≥ 1) (y : ℝ) : (Complex.exp (-y * Complex.I * Real.log (n : ℝ))).re = Real.cos (-y * Real.log (n : ℝ)) := by
  have h : -y * Complex.I * Real.log (n : ℝ) = (↑(-y * Real.log (n : ℝ)) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h]
  exact Complex.exp_ofReal_mul_I_re _

lemma lem_eacosalog2 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (-y * Real.log (n : ℝ)) := by
  rw [lem_niyelog n hn y]
  exact lem_eacosalog n hn y

lemma lem_eacosalog3 (n : ℕ) (hn : n ≥ 1) (y : ℝ) : ((n : ℂ) ^ (-y * Complex.I)).re = Real.cos (y * Real.log (n : ℝ)) := by
  rw [lem_eacosalog2 n hn y]
  rw [neg_mul]
  exact Real.cos_neg (y * Real.log (n : ℝ))

lemma lem_cos2t2 (θ : ℝ) : 2 * Real.cos θ ^ 2 = 1 + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  ring

lemma lem_cosSquare (θ : ℝ) : 2 * (1 + Real.cos θ)^2 = 2 + 4 * Real.cos θ + 2 * Real.cos θ^2 := by
  ring

lemma lem_cos2cos341 (θ : ℝ) : 2 * (1 + Real.cos θ) ^ 2 = 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]; ring

lemma lem_SquarePos2 (y : ℝ) : 0 ≤ 2 * y ^ 2 := mul_nonneg (by norm_num) (sq_nonneg y)

lemma lem_SquarePoscos (θ : ℝ) : 0 ≤ 2 * (1 + Real.cos θ) ^ 2 := by
  exact lem_SquarePos2 (1 + Real.cos θ)

lemma lem_postrig (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [← lem_cos2cos341]
  exact lem_SquarePoscos θ

lemma lem_postriglogn (n : ℕ) (_hn : n ≥ 1) (t : ℝ) : 0 ≤ 3 + 4 * Real.cos (t * Real.log (n : ℝ)) + Real.cos (2 * t * Real.log (n : ℝ)) := by
  rw [mul_assoc]
  exact lem_postrig (t * Real.log (n : ℝ))

lemma lem_seriesPos {r_n : ℕ+ → ℝ} {r : ℝ} (h_hasSum : HasSum r_n r) (h_nonneg : ∀ n : ℕ+, r_n n ≥ 0) : r ≥ 0 := by
  -- HasSum r_n r means ∑' n, r_n n = r
  have h_eq : ∑' n, r_n n = r := HasSum.tsum_eq h_hasSum
  -- Use tsum_nonneg to show ∑' n, r_n n ≥ 0
  have h_tsum_nonneg : ∑' n, r_n n ≥ 0 := tsum_nonneg h_nonneg
  -- Combine the two results
  rw [← h_eq]
  exact h_tsum_nonneg

lemma real_part_of_diff (M : ℝ) (w : ℂ) : (2 * M - w).re = 2 * M - w.re := by
  simp [Complex.sub_re]

lemma real_part_of_diffz (M : ℝ) (f_z : ℂ) : (2 * M - f_z).re = 2 * M - f_z.re := real_part_of_diff M f_z

lemma inequality_reversal (x M : ℝ) (hxM : x ≤ M) : 2 * M - x ≥ M := by linarith

lemma real_part_lower_bound (w : ℂ) (M : ℝ) (_hM : M > 0) (h : w.re ≤ M) : 2 * M - w.re ≥ M := by apply inequality_reversal w.re M h

lemma real_part_lower_bound2 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w).re ≥ M := by rw [real_part_of_diffz]; exact real_part_lower_bound w M hM h

lemma real_part_lower_bound3 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w).re > 0 := by
  rw [real_part_of_diffz]
  apply lt_of_le_of_lt'
  apply real_part_lower_bound
  exact hM
  exact h
  exact hM

lemma nonzero_if_real_part_positive (w : ℂ) (hw_re_pos : w.re > 0) : w ≠ 0 := by
  by_contra h
  rw [h] at hw_re_pos
  exact lt_irrefl 0 hw_re_pos

lemma lem_real_part_lower_bound4 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : (2 * M - w) ≠ 0 := by
  apply nonzero_if_real_part_positive
  exact real_part_lower_bound3 w M hM h

lemma lem_abspos (z : ℂ) : z ≠ 0 → norm z > 0 := by
  intro h_ne_zero
  exact norm_pos_iff.mpr h_ne_zero

lemma lem_real_part_lower_bound5 (w : ℂ) (M : ℝ) (hM : M > 0) (h : w.re ≤ M) : norm (2 * M - w) > 0 :=
  norm_pos_iff.mpr (lem_real_part_lower_bound4 w M hM h)

lemma lem_modaib (a b : ℝ) : norm (a + Complex.I * b) ^ 2 = a ^ 2 + b ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring

lemma lem_modcaib (a b c : ℝ) : norm (c - a - Complex.I * b) ^ 2 = (c - a) ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

lemma lem_diffmods (a b c : ℝ) :
norm (c - a - Complex.I * b) ^ 2 - norm (a + Complex.I * b) ^ 2 = (c - a) ^ 2 - a ^ 2 := by
  rw [lem_modcaib, lem_modaib]
  ring

lemma lem_casq (a c : ℝ) : (c - a) ^ 2 = a ^ 2 - 2 * a * c + c ^ 2 := by linarith

lemma lem_casq2 (a c : ℝ) : (c - a) ^ 2 - a ^ 2 = c * (c - 2 * a) := by
  ring

lemma lem_diffmods2 (a b c : ℝ) : norm (c - a - Complex.I * b) ^ 2 - norm (a + Complex.I * b) ^ 2 =  c * (c - 2 * a) := by
  rw [lem_diffmods]
  rw [lem_casq2]

lemma lem_modulus_sq_ReImw (M : ℝ) (w : ℂ) : norm (2 * M - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := by
  simp_rw [Complex.sq_norm]
  simp_rw [Complex.normSq_apply]
  simp [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

lemma lem_modulus_sq_identity (M : ℝ) (w : ℂ) : norm (2 * M - w) ^ 2 - norm w ^ 2 = 4 * M * (M - w.re) := lem_modulus_sq_ReImw M w

lemma lem_nonnegative_product (M x : ℝ) (hM : M > 0) (hxM : x ≤ M) : 4 * M * (M - x) ≥ 0 :=
  mul_nonneg (by linarith) (by linarith)

lemma lem_nonnegative_product2 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : 4 * M * (M - w.re) ≥ 0 :=
  lem_nonnegative_product M w.re hM hw_re_le_M

lemma lem_nonnegative_product3 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ^ 2 - norm w ^ 2 ≥ 0 := by
  rw [lem_modulus_sq_identity]; exact lem_nonnegative_product2 M w hM hw_re_le_M

lemma lem_nonnegative_product4 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ^ 2 ≥ norm w ^ 2 := by
  have h := lem_nonnegative_product3 M w hM hw_re_le_M
  linarith

lemma lem_nonnegative_product5 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm (2 * M - w) ≥ norm w :=
  (sq_le_sq₀ (norm_nonneg w) (norm_nonneg (2 * M - w))).mp (lem_nonnegative_product4 M w hM hw_re_le_M)

lemma lem_nonnegative_product6 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm w ≤ norm (2 * M - w) := by apply lem_nonnegative_product5 M w hM hw_re_le_M

lemma lem_ineqmultrbb (a b : ℝ) (hb : b > 0) (ha : 0 ≤ a) (hab : a ≤ b) : a / b ≤ 1 := by
  simpa [div_self (ne_of_gt hb)] using div_le_div_of_nonneg_right hab hb.le

lemma lem_nonnegative_product7 (M : ℝ) (w : ℂ) (hM : M > 0) (h_abs_diff_pos : norm (2 * M - w) > 0) (h_abs_le_abs_diff : norm w ≤ norm (2 * M - w)) : norm w / norm (2 * M - w) ≤ 1 :=
  lem_ineqmultrbb (norm w) (norm (2 * M - w)) h_abs_diff_pos (norm_nonneg w) h_abs_le_abs_diff

lemma lem_nonnegative_product8 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) (h_abs_le_abs_diff : norm w ≤
norm (2 * M - w)) : norm w / norm (2 * M - w) ≤ 1 :=
  lem_nonnegative_product7 M w hM (lem_real_part_lower_bound5 w M hM hw_re_le_M) h_abs_le_abs_diff

lemma lem_nonnegative_product9 (M : ℝ) (w : ℂ) (hM : M > 0) (hw_re_le_M : w.re ≤ M) : norm w / norm (2 * M - w) ≤ 1 :=
  lem_nonnegative_product8 M w hM hw_re_le_M (lem_nonnegative_product6 M w hM hw_re_le_M)

lemma lem_triangle_ineq (N G : ℂ) : norm (N + G) ≤ norm N + norm G := by
  exact norm_add_le N G

lemma lem_triangleineqminus (N F : ℂ) : norm (N - F) ≤ norm N + norm F := by
  rw [sub_eq_add_neg]
  calc
    ‖N + (-F)‖ ≤ ‖N‖ + ‖-F‖ := by apply lem_triangle_ineq
    _ = ‖N‖ + ‖F‖ := by rw [norm_neg]

lemma lem_rtriangle (r : ℝ) (N F : ℂ) (hr : r > 0) : r * norm (N - F) ≤ r * (norm N + norm F) :=
  mul_le_mul_of_nonneg_left (lem_triangleineqminus N F) hr.le

lemma rtriangle2 (r : ℝ) (N F : ℂ) (hr : r > 0) : r * norm (N - F) ≤ r * norm N + r * norm F := by
  linarith [lem_rtriangle r N F hr]

lemma lem_rtriangle3 (r R : ℝ) (N F : ℂ) (hr : r > 0) (hR : r < R) (h : R * norm F ≤ r * norm (N - F)) : R * norm F ≤ r * norm N + r * norm F :=
  h.trans (rtriangle2 r N F hr)

lemma lem_rtriangle4 (r R : ℝ) (N F : ℂ) (hr : 0 < r) (hR : r < R) (h_hyp : R * norm F ≤ r * norm (N - F)) : (R - r) * norm F ≤ r * norm N := by
  linarith [lem_rtriangle3 r R N F hr hR h_hyp]

lemma lem_absposeq (a : ℝ) (ha : a > 0) : |a| = a := by
  apply Real.norm_of_nonneg
  linarith [ha]

lemma lem_a2a (a : ℝ) (ha : a > 0) : 2 * a > 0 := by linarith

lemma lem_absposeq2 (a : ℝ) (ha : a > 0) : |2 * a| = 2 * a := by
  apply lem_absposeq
  apply lem_a2a
  exact ha

lemma lem_rtriangle5 (r R M : ℝ) (F : ℂ) (hr : 0 < r) (hrR : r < R) (hM : M > 0)
    (h_hyp : R * norm F ≤ r * norm (2 * M - F)) :
(R - r) * norm F ≤ 2 * M * r := by
  have h1 : (R - r) * norm F ≤ r * norm (2 * M : ℂ) :=
    lem_rtriangle4 r R (2 * M : ℂ) F hr hrR h_hyp
  have h2 : norm (2 * M : ℂ) = 2 * M := by
    convert Complex.norm_of_nonneg (by linarith : (0:ℝ) ≤ 2 * M) using 1
    norm_cast
  rw [h2, mul_comm r (2 * M)] at h1
  exact h1

lemma lem_RrFpos (r R : ℝ) (F : ℂ) (hr : 0 < r) (hrR : r < R) : (R - r) * norm F ≥ 0 :=
  mul_nonneg (by linarith) (norm_nonneg F)

lemma lem_rtriangle6 (r R M : ℝ) (F : ℂ) (hr : 0 < r) (hrR : r < R) (hM : M > 0)
    (h_hyp : (R - r) * norm F ≤ 2 * M * r) :
norm F ≤ (2 * M * r) / (R - r) := by
  have hpos : R - r > 0 := by linarith
  have h := div_le_div_of_nonneg_right h_hyp hpos.le
  rwa [mul_div_cancel_left₀ (‖F‖) (ne_of_gt hpos)] at h

lemma lem_rtriangle7 (r R M : ℝ) (F : ℂ)
    (hr : 0 < r) (hrR : r < R) (hM : M > 0)
    (h_hyp : R * norm F ≤ r * norm (2 * M - F)) :
norm F ≤ (2 * M * r) / (R - r) :=
  lem_rtriangle6 r R M F hr hrR hM (lem_rtriangle5 r R M F hr hrR hM h_hyp)


theorem analyticWithinAt_to_analyticAt_aux {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ} (hS : S ∈ nhds z)
  (p : FormalMultilinearSeries ℂ ℂ ℂ) (r : ENNReal) (h_conv_on_inter : r ≤ p.radius) (hr_pos : 0 < r)
  (hasSumt : ∀ {y : ℂ}, z + y ∈ insert z S → y ∈ Metric.eball 0 r → HasSum (fun n => (p n) fun x => y) (f (z + y)))
  (ε : ℝ) (hε_pos : ε > 0) (h_ball_subset_S : Metric.ball z ε ⊆ S) :
  let r' := min r (ENNReal.ofReal ε);
  ∀ {y : ℂ}, y ∈ Metric.eball 0 r' → HasSum (fun n => (p n) fun x => y) (f (z + y)) := by
  intro r' y hy
  apply hasSumt
  · -- Prove z + y ∈ insert z S
    -- Since y ∈ Metric.eball 0 r', we have ‖y‖ < r'
    -- Since r' ≤ ENNReal.ofReal ε, we have ‖y‖ < ε
    -- Therefore z + y ∈ Metric.ball z ε ⊆ S
    right  -- Choose to prove z + y ∈ S (not z + y = z)
    apply h_ball_subset_S
    rw [Metric.mem_ball]
    -- Need to show dist z (z + y) < ε
    simp [dist_self_add_right]
    -- Now need to show ‖y‖ < ε
    have : y ∈ Metric.eball 0 (ENNReal.ofReal ε) := by
      apply Metric.eball_subset_eball (min_le_right r (ENNReal.ofReal ε)) hy

    have hedist : edist y 0 < ENNReal.ofReal ε := Metric.mem_eball.mp this
    have hdist : dist y 0 < ε := edist_lt_ofReal.mp hedist
    simpa using hdist

  · -- Prove y ∈ Metric.eball 0 r
    exact Metric.eball_subset_eball (min_le_left r (ENNReal.ofReal ε)) hy


theorem analyticWithinAt_to_analyticAt {f : ℂ → ℂ} {S : Set ℂ} {z : ℂ}
    (hS : S ∈ nhds z) (h : AnalyticWithinAt ℂ f S z) : AnalyticAt ℂ f z :=
  analyticWithinAt_univ.mp (h.mono_of_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hS))


-- First, the easy auxiliary lemmas:

lemma lem_not0mono (R : ℝ) (hR_pos : 0 < R) (hR_lt_one : R < 1) :
    {z : ℂ | norm z ≤ R ∧ z ≠ 0} ⊆ {z : ℂ | z ≠ 0} := by
  intro z hz
  exact hz.2

lemma lem_1zanalDR (R : ℝ) (hR_pos : 0 < R) :
    AnalyticOn ℂ (fun z ↦ z⁻¹) {z : ℂ | norm z ≤ R ∧ z ≠ 0} :=
  AnalyticOn.mono analyticOn_inv (fun _ hz => hz.2)

lemma lem_analprodST {T S : Set ℂ} {f1 f2 : ℂ → ℂ} (hTS : T ⊆ S) (hf1 : AnalyticOn ℂ f1 T) (hf2 : AnalyticOn ℂ f2 S) :
    AnalyticOn ℂ (f1 * f2) T := by
  exact hf1.mul (hf2.mono hTS)

lemma lem_analprodTDR (R : ℝ) (f1 f2 : ℂ → ℂ) :
    (AnalyticOn ℂ f1 {z : ℂ | norm z ≤ R ∧ z ≠ 0}) →
    (AnalyticOn ℂ f2 (Metric.closedBall 0 R)) →
    AnalyticOn ℂ (f1 * f2) {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
  intro hf1 hf2
  -- Let T be the punctured disk.
  let T := {z : ℂ | norm z ≤ R ∧ z ≠ 0}
  -- The product is analytic on T if both functions are analytic on T.
  -- We have hf1 : AnalyticOn ℂ f1 T.
  -- We need to show f2 is analytic on T.
  have hf2_on_T : AnalyticOn ℂ f2 T := by
    -- f2 is analytic on the whole closed ball.
    -- The punctured disk T is a subset of the closed ball.
    apply hf2.mono
    intro z hz
    -- Goal: z ∈ Metric.closedBall 0 R
    simp [Metric.closedBall, dist_zero_right]
    -- From hz : |z| ≤ R ∧ z ≠ 0, we need to prove |z| ≤ R.
    exact hz.1
  -- Now apply the theorem for multiplication of analytic functions.
  exact hf1.mul hf2_on_T

lemma lem_fzzTanal {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ)
    (hf : AnalyticOn ℂ f (Metric.closedBall 0 R)) :
    AnalyticOn ℂ (fun z ↦ f z / z) {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
  have hsub : {z : ℂ | norm z ≤ R ∧ z ≠ 0} ⊆ Metric.closedBall (0 : ℂ) R := fun z hz => by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz.1
  have h : AnalyticOn ℂ (fun z ↦ f z * z⁻¹) {z : ℂ | norm z ≤ R ∧ z ≠ 0} :=
    (hf.mono hsub).mul (lem_1zanalDR R hR_pos)
  simpa [div_eq_mul_inv] using h

lemma lem_DR0T {R : ℝ} (hR : 0 < R) :
    Metric.closedBall 0 R = {0} ∪ {z : ℂ | norm z ≤ R ∧ z ≠ 0} := by
  ext z
  simp [Metric.closedBall, dist_zero_right]
  by_cases hz : z = 0
  · simp [hz, hR.le]
  · simp [hz]

lemma lem_analWWWithin {R : ℝ} (hR_pos : 0 < R) (h : ℂ → ℂ) :
    (AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0) →
    (∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) →
    (∀ z ∈ Metric.closedBall 0 R, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) := by
  intro h0 hT z hz
  rw [lem_DR0T hR_pos] at hz
  rcases hz with hz | hz
  · simp at hz
    rw [hz]
    exact h0
  · exact hT z hz

lemma lem_analWWithinAtOn (R : ℝ) (hR_pos : 0 < R) (h : ℂ → ℂ)
    (h_at_0 : AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0)
    (h_at_T : ∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z) :
    AnalyticOn ℂ h (Metric.closedBall 0 R) := by
  exact lem_analWWWithin hR_pos h h_at_0 h_at_T

lemma analyticWithinAt_punctured_to_closedBall {R : ℝ} (hR : 0 < R) {h : ℂ → ℂ} {z : ℂ} (hz : z ∈ {w : ℂ | norm w ≤ R ∧ w ≠ 0}) (h_within : AnalyticWithinAt ℂ h {w : ℂ | norm w ≤ R ∧ w ≠ 0} z) : AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z := by
  apply h_within.mono_of_mem_nhdsWithin
  have hU : {w : ℂ | w ≠ 0} ∈ nhdsWithin z (Metric.closedBall (0 : ℂ) R) :=
    mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hz.2)
  refine Filter.mem_of_superset (Filter.inter_mem self_mem_nhdsWithin hU) ?_
  rintro w ⟨hwT, hwU⟩
  exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hwT, hwU⟩

lemma lem_analAtOnOn {R : ℝ} (hR_pos : 0 < R) (h : ℂ → ℂ) :
    AnalyticAt ℂ h 0 →
    AnalyticOn ℂ h {z : ℂ | norm z ≤ R ∧ z ≠ 0} →
    AnalyticOn ℂ h (Metric.closedBall 0 R) := by
  intro h_at_0 h_on_punctured

  -- Use lem_analWWithinAtOn to show AnalyticOn from AnalyticWithinAt conditions
  apply lem_analWWithinAtOn R hR_pos h

  -- First goal: AnalyticWithinAt ℂ h (Metric.closedBall 0 R) 0
  · exact h_at_0.analyticWithinAt

  -- Second goal: ∀ z ∈ {z : ℂ | norm z ≤ R ∧ z ≠ 0}, AnalyticWithinAt ℂ h (Metric.closedBall 0 R) z
  · intro z hz
    -- First get AnalyticWithinAt on the punctured ball
    have h_within_punctured : AnalyticWithinAt ℂ h {w : ℂ | norm w ≤ R ∧ w ≠ 0} z :=
      h_on_punctured z hz
    -- Then extend to the closed ball
    exact analyticWithinAt_punctured_to_closedBall hR_pos hz h_within_punctured

lemma lem_ordernatcast1 (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (n : ℕ) (hn : analyticOrderAt f 0 = n) (hn_ne_zero : n ≠ 0) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h 0 ∧ ∀ᶠ z in nhds 0, f z = z * h z := by
  obtain ⟨g, hg_analytic, _, hf_eq_g⟩ :
      ∃ (g : ℂ → ℂ), AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧ ∀ᶠ (z : ℂ) in nhds 0, f z = z ^ n * g z := by
    rw [AnalyticAt.analyticOrderAt_eq_natCast] at hn
    · convert hn
      aesop
    · exact hf
  refine ⟨fun z ↦ z ^ (n - 1) * g z, (analyticAt_id.pow (n - 1)).mul hg_analytic, ?_⟩
  filter_upwards [hf_eq_g] with z h_eq
  rw [h_eq]
  ring_nf
  rw [← pow_succ' z (n - 1), Nat.sub_add_cancel (Nat.pos_of_ne_zero hn_ne_zero)]

-- Now, the proof of your sorried lemma, exactly as you designed it.
lemma lem_ordernatcast2_old (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (h_not_eventually_zero : ¬ (∀ᶠ z in nhds 0, f z = 0)) :
    ∃ (h : ℂ → ℂ), AnalyticAt ℂ h 0 ∧ ∀ᶠ z in nhds 0, f z = z * h z := by
  -- Let n₀ be the analytic order
  let n₀ := analyticOrderAt f 0
  -- Apply lem:ordernetop: since f is not eventually zero, n₀ is finite.
  have hn_ne_top : n₀ ≠ ⊤ := by
    intro h
    rw [analyticOrderAt_eq_top] at h
    exact h_not_eventually_zero h
  -- So we can lift n₀ to a natural number n.
  lift n₀ to ℕ using hn_ne_top with n hn_eq
  -- Apply lem:orderne0: since f(0)=0, n is not 0.
  have hn_ne_zero : n ≠ 0 := by
    intro hn_zero
    rw [hn_zero] at hn_eq

    have t := (AnalyticAt.analyticOrderAt_ne_zero hf).mpr hf0
    have : n₀ = analyticOrderAt f 0 := rfl
    rw [←this] at t
    exact t (id (Eq.symm hn_eq))
  -- Apply lem:ordernatcast1: since n ∈ ℕ and n ≠ 0, we get our result.
  exact lem_ordernatcast1 f hf n (by aesop) hn_ne_zero

lemma lem_ordernatcast2 {R : ℝ} (hR_pos : 0 < R) (f : ℂ → ℂ) (hf0 : f 0 = 0)
    (hf : AnalyticOn ℂ f (Metric.closedBall 0 R)) :
    AnalyticAt ℂ (fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z) 0 := by
  -- First, extract AnalyticAt for f at 0 from AnalyticOn on a neighborhood.
  have hS : Metric.closedBall 0 R ∈ nhds (0 : ℂ) := by
    -- Any open ball around 0 is contained in the closed ball.
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hR_pos) ?subset
    exact Metric.ball_subset_closedBall
  have hf_within : AnalyticWithinAt ℂ f (Metric.closedBall 0 R) 0 := hf 0 (by
    simp [Metric.mem_closedBall, dist_zero_right, hR_pos.le])
  have hf_at0 : AnalyticAt ℂ f 0 := analyticWithinAt_to_analyticAt hS hf_within

  -- Define the target function g
  let g : ℂ → ℂ := fun z ↦ if z = 0 then (fderiv ℂ f 0) 1 else f z / z

  -- Case split on whether f is eventually zero near 0
  by_cases hEZ : (∀ᶠ z in nhds (0 : ℂ), f z = 0)
  · -- If f is eventually zero, then (fderiv f 0) 1 = 0 and g is 0 on a nbhd; hence analytic.
    -- The zero set is a neighborhood of 0
    have hU : {z : ℂ | f z = 0} ∈ nhds (0 : ℂ) := Filter.eventually_iff.mp hEZ
    -- Turn it into an eventual equality
    have hf_eq_zero : f =ᶠ[nhds (0 : ℂ)] (fun _ : ℂ => 0) := by
      refine (Filter.eventuallyEq_iff_exists_mem).2 ?_
      exact ⟨{z | f z = 0}, hU, by intro z hz; simpa [Set.mem_ofPred_eq] using hz⟩
    -- Derivative at 0 equals derivative of the constant-0 function.
    have h_fderiv_zero : (fderiv ℂ f 0) = 0 := by
      simpa using (Filter.EventuallyEq.fderiv_eq hf_eq_zero)
    -- From this, g equals 0 on the same neighborhood U = {z | f z = 0}
    -- Show g is identically 0 on U
    have h_g_zero_on_U : ∀ z ∈ {z : ℂ | f z = 0}, g z = 0 := by
      intro z hzU
      by_cases hz0 : z = 0
      · -- At 0, g 0 = (fderiv f 0) 1 = 0
        simp [g, hz0, h_fderiv_zero]
      · -- Away from 0, g z = f z / z = 0
        have : f z = 0 := by simpa [Set.mem_ofPred_eq] using hzU
        simp [g, hz0, this]
    -- Conclude AnalyticAt at 0 via AnalyticWithinAt on U and neighborhood lifting
    have h_const0_within : AnalyticWithinAt ℂ (fun _ : ℂ => (0 : ℂ)) {z : ℂ | f z = 0} 0 :=
      analyticAt_const.analyticWithinAt
    have h_g_within : AnalyticWithinAt ℂ g {z : ℂ | f z = 0} 0 := by
      -- equal to constant 0 on this set
      apply h_const0_within.congr
      intro z hz
      by_cases hz0 : z = 0
      · -- At 0
        simp [g, hz0, h_fderiv_zero]
      · -- For z ≠ 0
        have : f z = 0 := by simpa [Set.mem_ofPred_eq] using hz
        simp [g, hz0, this]
      -- Show equality at 0
      simp [g, h_fderiv_zero]
    exact analyticWithinAt_to_analyticAt hU h_g_within

  · -- Otherwise, use the local factorization f z = z * h0 z near 0
    have h_notEZ : ¬ (∀ᶠ z in nhds (0 : ℂ), f z = 0) := hEZ
    -- Obtain a local factorization from the order lemma
    rcases lem_ordernatcast2_old f hf_at0 hf0 h_notEZ with ⟨h0, h0_at0, hfac_ev⟩
    -- Turn eventual equality into EventuallyEq for derivatives
    have hV : {z : ℂ | f z = z * h0 z} ∈ nhds (0 : ℂ) := Filter.eventually_iff.mp hfac_ev
    have h_eq_nhds : f =ᶠ[nhds (0 : ℂ)] (fun z => z * h0 z) :=
      (Filter.eventuallyEq_iff_exists_mem).2 ⟨{z : ℂ | f z = z * h0 z}, hV, by
        intro z hz; simpa [Set.mem_ofPred_eq] using hz⟩
    -- Equality of fderiv at 0
    have h_fderiv_prod : fderiv ℂ f 0 = fderiv ℂ (fun z => z * h0 z) 0 :=
      Filter.EventuallyEq.fderiv_eq h_eq_nhds
    -- Compute (fderiv f 0) 1 using the product rule to identify g 0 with h0 0
    have h_diff_id : DifferentiableAt ℂ (fun z : ℂ => z) 0 := differentiableAt_id
    have h_diff_h0 : DifferentiableAt ℂ h0 0 := h0_at0.differentiableAt
    -- fderiv of product at 0
    have h_val0 : (fderiv ℂ f 0) 1 = h0 0 := by
      -- Rewrite fderiv using the product rule and simplify
      rw [h_fderiv_prod]
      rw [fderiv_fun_mul' h_diff_id h_diff_h0]
      simp only [add_apply, smul_apply]
      rw [fderiv_fun_id]
      simp only [ContinuousLinearMap.id_apply]
      simp only [zero_smul, zero_add]
      simp
    -- Build a neighborhood where equality g = h0 holds everywhere
    -- On V = {z | f z = z * h0 z}, for z ≠ 0 we have f z = z * h0 z; at 0, we showed g 0 = h0 0
    have h_geq_h0_on_V : ∀ z ∈ {z : ℂ | f z = z * h0 z}, g z = h0 z := by
      intro z hzU
      by_cases hz0 : z = 0
      · -- At 0
        simpa [g, hz0] using h_val0
      · -- For z ≠ 0, use the factorization
        have : f z = z * h0 z := by simpa [Set.mem_ofPred_eq] using hzU
        simp only [g, ite_eq_right hz0, this]
        exact mul_div_cancel_left₀ (h0 z) hz0
    -- Conclude AnalyticAt at 0 via AnalyticWithinAt congruence on V
    have h0_within : AnalyticWithinAt ℂ h0 {z : ℂ | f z = z * h0 z} 0 := h0_at0.analyticWithinAt
    have hg_within : AnalyticWithinAt ℂ g {z : ℂ | f z = z * h0 z} 0 := by
      -- Use the fact that h0 is analytic within the set and g = h0 on the set
      -- Show g equals h0 on a neighborhood within the set
      apply AnalyticWithinAt.congr h0_within
      -- Show equality on the set
      intro z hz
      exact h_geq_h0_on_V z hz
      -- Show equality at 0 - need to prove 0 ∈ {z | f z = z * h0 z}
      -- From f 0 = 0 and 0 * h0 0 = 0, we get f 0 = 0 * h0 0
      have h_0_in_V : (0 : ℂ) ∈ {z : ℂ | f z = z * h0 z} := by
        simp [Set.mem_ofPred_eq, hf0]
      exact h_geq_h0_on_V 0 h_0_in_V
    exact analyticWithinAt_to_analyticAt hV hg_within


lemma lem_inDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw : w ∈ closure (Metric.ball (0 : ℂ) R)) : norm w ≤ R := by
  rw [closure_ball (0 : ℂ) (ne_of_gt hR), Metric.mem_closedBall, Complex.dist_eq] at hw
  simpa using hw

lemma lem_notinDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw : w ∉ Metric.ball (0 : ℂ) R) : norm w ≥ R := by
  simpa [Metric.mem_ball, Complex.dist_eq, not_lt] using hw

lemma lem_circleDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw1 : w ∈ closure (Metric.ball (0 : ℂ) R)) (hw2 : w ∉ Metric.ball (0 : ℂ) R) : norm w = R := by
  have h1 : norm w ≤ R := lem_inDR R hR w hw1
  have h2 : norm w ≥ R := lem_notinDR R hR w hw2
  exact le_antisymm h1 h2

lemma lem_Rself (R : ℝ) (hR : R > 0) : |R| = R := by
  rw [abs_eq_self]
  linarith

lemma lem_Rself2 (R : ℝ) (hR : R > 0) : |R| ≤ R := by
  rw [lem_Rself R hR]

lemma lem_Rself3 (R : ℝ) (hR : R > 0) : (R : ℂ) ∈ closure (Metric.ball (0 : ℂ) R) := by
  rw [closure_ball (0 : ℂ) (ne_of_gt hR), Metric.mem_closedBall]
  simpa [Complex.dist_eq] using lem_Rself2 R hR

lemma lem_ExtrValThm {K : Set ℂ} (hK : IsCompact K) (hK_nonempty : K.Nonempty) (g : K → ℂ) (hg : Continuous g) :
∃ v : K, ∀ z : K, norm (g z) ≤ norm (g v) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : Nonempty K := hK_nonempty.to_subtype
  obtain ⟨v, _, hv_max⟩ := IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty
    (continuous_norm.comp hg).continuousOn
  exact ⟨v, fun z => hv_max (Set.mem_univ z)⟩

lemma lem_ExtrValThmDR (R : ℝ) (hR : R > 0) (g : closure (Metric.ball (0 : ℂ) R) → ℂ) (hg : Continuous g) :
∃ v : closure (Metric.ball (0 : ℂ) R), ∀ z : closure (Metric.ball (0 : ℂ) R), norm (g z) ≤ norm (g v) :=
  lem_ExtrValThm
    (by rw [closure_ball (0 : ℂ) (ne_of_gt hR)]
        exact Metric.isCompact_of_isClosed_isBounded Metric.isClosed_closedBall Metric.isBounded_closedBall)
    (by rw [closure_ball (0 : ℂ) (ne_of_gt hR), Metric.nonempty_closedBall]; linarith) g hg

lemma lem_AnalCont {R : ℝ} (hR : R > 0) (H : ℂ → ℂ) (h_analytic : AnalyticOn ℂ H (closure (Metric.ball (0 : ℂ) R))) :
Continuous (H ∘ (Subtype.val : closure (Metric.ball (0 : ℂ) R) → ℂ)) :=
  h_analytic.continuousOn.comp_continuous continuous_subtype_val (fun _ => Subtype.mem _)

lemma lem_ExtrValThmh {R : ℝ} (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (Metric.ball (0 : ℂ) R))) :
∃ u : closure (Metric.ball (0 : ℂ) R), ∀ z : closure (Metric.ball (0 : ℂ) R), norm (h u) ≥ norm (h z) := by
  obtain ⟨v, hv⟩ := lem_ExtrValThmDR R hR (h ∘ Subtype.val) (lem_AnalCont hR h h_analytic)
  exact ⟨v, fun z => hv z⟩

lemma lem_MaxModP (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (Metric.ball (0 : ℂ) R))) (w : ℂ) (hw_in_DR : w ∈ Metric.ball (0 : ℂ) R) (hw_max : ∀ z ∈ Metric.ball (0 : ℂ) R, norm (h z) ≤ norm (h w)) : ∀ z ∈ closure (Metric.ball (0 : ℂ) R), norm (h z) = norm (h w) := by
  have h_preconnected : IsPreconnected (Metric.ball (0 : ℂ) R) := (convex_ball (0 : ℂ) R).isPreconnected
  have h_open : IsOpen (Metric.ball (0 : ℂ) R) := Metric.isOpen_ball
  have h_diff_cont : DiffContOnCl ℂ h (Metric.ball (0 : ℂ) R) :=
    ⟨(h_analytic.mono subset_closure).differentiableOn, h_analytic.continuousOn⟩
  have h_max_on : IsMaxOn (norm ∘ h) (Metric.ball (0 : ℂ) R) w := fun z hz => hw_max z hz
  intro z hz
  exact Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn h_preconnected h_open h_diff_cont hw_in_DR h_max_on hz

lemma lem_MaxModR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (Metric.ball (0 : ℂ) R))) (w : ℂ) (hw_in_DR : w ∈ Metric.ball (0 : ℂ) R) (hw_max : ∀ z ∈ Metric.ball (0 : ℂ) R, norm (h z) ≤ norm (h w)) : norm (h R) = norm (h w) :=
  lem_MaxModP R hR h h_analytic w hw_in_DR hw_max (R : ℂ) (lem_Rself3 R hR)

lemma lem_MaxModRR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (Metric.ball (0 : ℂ) R)))
  (w : ℂ) (hw_in_DR : w ∈ Metric.ball (0 : ℂ) R) (hw_max : ∀ z ∈ Metric.ball (0 : ℂ) R, norm (h z) ≤ norm (h w)) :
∀ z ∈ closure (Metric.ball (0 : ℂ) R), norm (h R) ≥ norm (h z) := fun z hz => by
  rw [lem_MaxModR R hR h h_analytic w hw_in_DR hw_max, lem_MaxModP R hR h h_analytic w hw_in_DR hw_max z hz]

theorem lem_MaxModv2 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (Metric.ball (0 : ℂ) R))) :
∃ v : closure (Metric.ball (0 : ℂ) R), norm (v : ℂ) = R ∧ ∀ z : closure (Metric.ball (0 : ℂ) R), norm (h (v : ℂ)) ≥ norm (h (z : ℂ)) := by
  obtain ⟨u, hu⟩ := lem_ExtrValThmh hR h h_analytic
  by_cases h_case : (u : ℂ) ∈ Metric.ball (0 : ℂ) R
  · refine ⟨⟨(R : ℂ), lem_Rself3 R hR⟩, ?_, ?_⟩
    · simpa [Complex.norm_real] using lem_Rself R hR
    · have hw_max : ∀ w ∈ Metric.ball (0 : ℂ) R, norm (h w) ≤ norm (h (u : ℂ)) := fun w hw =>
        hu ⟨w, subset_closure hw⟩
      exact fun z => lem_MaxModRR R hR h h_analytic (u : ℂ) h_case hw_max (z : ℂ) (Subtype.mem z)
  · exact ⟨u, lem_circleDR R hR (u : ℂ) (Subtype.mem u) h_case, hu⟩

theorem lem_MaxModv3 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (Metric.ball (0 : ℂ) R))) :
∃ v : ℂ, norm v = R ∧ ∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → norm (h v) ≥ norm (h z) := by
  obtain ⟨v, hv_front, hv_max⟩ := Complex.exists_mem_frontier_isMaxOn_norm (f := h) (U := Metric.ball (0 : ℂ) R)
    Metric.isBounded_ball (Metric.nonempty_ball.mpr hR)
    ⟨(h_analytic.mono subset_closure).differentiableOn, h_analytic.continuousOn⟩
  refine ⟨v, ?_, fun z hz => hv_max hz⟩
  have hfr : frontier (Metric.ball (0 : ℂ) R) = Metric.sphere (0 : ℂ) R := frontier_ball 0 (ne_of_gt hR)
  rw [hfr] at hv_front
  simpa [Metric.mem_sphere, Complex.dist_eq] using hv_front

lemma lem_MaxModv4 (R B : ℝ) (hR : R > 0) (hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (Metric.ball (0 : ℂ) R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∃ v : ℂ, norm v = R ∧ (∀ w : ℂ, w ∈ closure (Metric.ball (0 : ℂ) R) → norm (h v) ≥ norm (h w)) ∧ norm (h v) ≤ B := by
  obtain ⟨v, hv_abs, hv_max⟩ := lem_MaxModv3 R hR h h_analytic
  exact ⟨v, hv_abs, hv_max, h_boundary_bound v hv_abs⟩

lemma lem_HardMMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (Metric.ball (0 : ℂ) R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∀ w : ℂ, w ∈ closure (Metric.ball (0 : ℂ) R) → norm (h w) ≤ B := by
  obtain ⟨v, _, hv_max, hv_bound⟩ := lem_MaxModv4 R B hR hB h h_analytic h_boundary_bound
  exact fun w hw => (hv_max w hw).trans hv_bound

lemma lem_EasyMMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (Metric.ball (0 : ℂ) R)))
  (h_closure_bound : ∀ w : ℂ, w ∈ closure (Metric.ball (0 : ℂ) R) → norm (h w) ≤ B) :
∀ z : ℂ, norm z = R → norm (h z) ≤ B := fun z hz =>
  h_closure_bound z (by rw [closure_ball (0 : ℂ) (ne_of_gt hR), Metric.mem_closedBall, Complex.dist_eq]; simp [hz])

theorem lem_MMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (Metric.ball (0 : ℂ) R))) :
(∀ z : ℂ, z ∈ closure (Metric.ball (0 : ℂ) R) → norm (h z) ≤ B) ↔ (∀ z : ℂ, norm z = R → norm (h z) ≤ B) :=
  ⟨lem_EasyMMP R B hR hB h h_analytic, lem_HardMMP R B hR hB h h_analytic⟩


end DiskAnalyticBounds
