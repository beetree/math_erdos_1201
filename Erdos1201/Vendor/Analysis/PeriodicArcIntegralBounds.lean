module

public import Mathlib.Algebra.Order.Round
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Erdos1201.Vendor.Analysis.AdditiveCharacterGeometricSums

@[expose] public section

/-!
# Periodic disjoint-arc integral bounds

This module bounds the sum of symmetric interval integrals about separated
points for a nonnegative periodic integrable function.
-/

namespace PeriodicArcIntegralBounds

open scoped BigOperators
open Real MeasureTheory intervalIntegral
open AdditiveCharacterGeometricSums

set_option maxHeartbeats 1600000 in
-- Lean 4.34: `if_pos`/`if_neg` on `Int.fract y < δ`-guarded `ite`s need `Int.fract y` unfolded to
-- `y - ⌊y⌋` to unify `Decidable` instances, at a transparency now excluded by
-- `backward.isDefEq.respectTransparency.types`.
set_option backward.isDefEq.respectTransparency.types false in
/-- Disjoint arcs around points separated modulo one have total integral at
most one full period of a nonnegative periodic function. -/
lemma sum_symmetricIntervalIntegral_le_period (g : ℝ → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hper : Function.Periodic g 1) (hgi : ∀ a b : ℝ, IntervalIntegrable g volume a b)
    (R : ℕ) (θ : Fin R → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : ∀ r s, r ≠ s → δ ≤ nearestIntegerDistance (θ r - θ s)) :
    (∑ r, ∫ t in (θ r - δ/2)..(θ r + δ/2), g t) ≤ ∫ t in (0:ℝ)..1, g t := by
  have h_integral_rewrite : ∫ t in (0 : ℝ)..1, ∑ r : Fin R,
      (if (t - (θ r - δ / 2)) - ⌊t - (θ r - δ / 2)⌋ < δ then g t else 0) ≤
      ∫ t in (0 : ℝ)..1, g t := by
    have h_integral_rewrite : ∀ t ∈ Set.Ioo (0 : ℝ) 1, ∑ r : Fin R,
        (if (t - (θ r - δ / 2)) - ⌊t - (θ r - δ / 2)⌋ < δ then 1 else 0) ≤ 1 := by
      intro t ht
      have h_unique : ∀ r s : Fin R, r ≠ s →
          ¬ ((t - (θ r - δ / 2)) - ⌊t - (θ r - δ / 2)⌋ < δ ∧
            (t - (θ s - δ / 2)) - ⌊t - (θ s - δ / 2)⌋ < δ) := by
        intros r s hrs h
        specialize hsp r s hrs
        simp_all +decide [nearestIntegerDistance]
        have h_abs : ∀ k : ℤ, |θ r - θ s - k| ≥ δ := by
          intro k
          exact le_trans hsp (by
            convert round_le (θ r - θ s) k using 1)
        contrapose! h_abs
        use ⌊t - (θ s - δ / 2)⌋ - ⌊t - (θ r - δ / 2)⌋
        rw [abs_lt]
        constructor <;> push_cast <;>
          linarith [Int.fract_add_floor (t - (θ r - δ / 2)),
            Int.fract_add_floor (t - (θ s - δ / 2)),
            Int.fract_nonneg (t - (θ r - δ / 2)),
            Int.fract_lt_one (t - (θ r - δ / 2)),
            Int.fract_nonneg (t - (θ s - δ / 2)),
            Int.fract_lt_one (t - (θ s - δ / 2))]
      let S : Finset (Fin R) := Finset.univ.filter fun r =>
        Int.fract (t - (θ r - δ / 2)) < δ
      have hcard : S.card ≤ 1 := by
        refine Finset.card_le_one.mpr fun r hr s hs => Classical.not_not.1 fun h => by
          have hr' : t - (θ r - δ / 2) - ⌊t - (θ r - δ / 2)⌋ < δ :=
            Finset.mem_filter.mp hr |>.2
          have hs' : t - (θ s - δ / 2) - ⌊t - (θ s - δ / 2)⌋ < δ :=
            Finset.mem_filter.mp hs |>.2
          exact False.elim (h_unique r s h ⟨hr', hs'⟩)
      rw [Finset.sum_boole]
      change S.card ≤ 1
      exact hcard
    rw [intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one]
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun _ _ =>
        by split_ifs <;> linarith [hg x]
    · exact (hgi 0 1).1
    · rw [Filter.EventuallyLE, MeasureTheory.ae_restrict_iff'] <;> norm_num
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
        (MeasureTheory.measure_singleton 1)] with x hx₁ hx₂ hx₃
      simp_all +decide
      have hcount : (∑ r : Fin R,
          if Int.fract (x - (θ r - δ / 2)) < δ then (1 : ℝ) else 0) ≤ 1 := by
        exact_mod_cast h_integral_rewrite x hx₂ (lt_of_le_of_ne hx₃ hx₁)
      calc
        (∑ r : Fin R, if Int.fract (x - (θ r - δ / 2)) < δ then g x else 0) =
            (∑ r : Fin R,
              if Int.fract (x - (θ r - δ / 2)) < δ then (1 : ℝ) else 0) * g x := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => by split_ifs <;> ring
        _ ≤ 1 * g x := mul_le_mul_of_nonneg_right hcount (hg x)
        _ = g x := one_mul _
  have h_fubini : ∫ t in (0 : ℝ)..1, ∑ r : Fin R,
      (if (t - (θ r - δ / 2)) - ⌊t - (θ r - δ / 2)⌋ < δ then g t else 0) =
      ∑ r : Fin R, ∫ t in (0 : ℝ)..1,
        (if (t - (θ r - δ / 2)) - ⌊t - (θ r - δ / 2)⌋ < δ then g t else 0) := by
    rw [intervalIntegral.integral_finsetSum]
    intro r _
    specialize hgi 0 1
    simp_all +decide [intervalIntegrable_iff]
    refine hgi.mono' ?_ ?_
    · exact MeasureTheory.AEStronglyMeasurable.indicator hgi.aestronglyMeasurable
        (measurableSet_lt (measurable_fract.comp (measurable_id.sub measurable_const))
          measurable_const)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx using by
        split_ifs <;> simp +decide [*, abs_of_nonneg]
  have h_periodic_integral : ∀ r : Fin R, ∫ t in (0 : ℝ)..1,
      (if (t - (θ r - δ / 2)) - ⌊t - (θ r - δ / 2)⌋ < δ then g t else 0) =
      ∫ t in (θ r - δ / 2)..(θ r + δ / 2), g t := by
    intro r
    have h_periodic_integral : ∫ t in (0 : ℝ)..1,
        (if (t - (θ r - δ / 2)) - ⌊t - (θ r - δ / 2)⌋ < δ then g t else 0) =
        ∫ t in (θ r - δ / 2)..(θ r - δ / 2 + 1),
          (if (t - (θ r - δ / 2)) - ⌊t - (θ r - δ / 2)⌋ < δ then g t else 0) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals]
      rw [intervalIntegral.integral_symm]
      rw [neg_add_eq_sub, sub_eq_iff_eq_add]
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · convert intervalIntegral.integral_comp_sub_right _ 1 using 2 <;> norm_num
        ext x
        simp +decide [sub_sub]
        rw [show x - (1 + (θ r - δ / 2)) = x - (θ r - δ / 2) - 1 by ring,
          Int.fract_sub_one]
        rw [← hper (x - 1)]
        ring_nf
      · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le]
        · refine MeasureTheory.Integrable.mono'
            (g := g)
            (f := fun t => if (t - (θ r - δ / 2)) -
              ⌊t - (θ r - δ / 2)⌋ < δ then g t else 0)
            ?_ ?_ ?_
          · exact (hgi _ _).1.mono_set Set.Ioo_subset_Ioc_self
          · exact MeasureTheory.AEStronglyMeasurable.indicator
              ((hgi _ _).1.aestronglyMeasurable.mono_set Set.Ioo_subset_Ioc_self)
              (measurableSet_lt (measurable_id.sub measurable_const |>.sub
                (Measurable.comp (by measurability)
                  (measurable_id.sub measurable_const |>.floor))) measurable_const)
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx using by
              split_ifs <;> rw [Real.norm_of_nonneg] <;> linarith [hg x]
        · linarith
      · rw [intervalIntegrable_iff]
        refine MeasureTheory.Integrable.indicator (hgi _ _).1
          (measurableSet_lt (measurable_id.sub measurable_const |>.sub
            (Measurable.comp (by measurability)
              (measurable_id.sub measurable_const |>.floor))) measurable_const)
      · rw [intervalIntegrable_iff]
        refine MeasureTheory.Integrable.indicator (hgi _ _).1
          (measurableSet_lt (measurable_id.sub measurable_const |>.sub
            (Measurable.comp (by measurability)
              (measurable_id.sub measurable_const |>.floor))) measurable_const)
      · rw [intervalIntegrable_iff]
        refine MeasureTheory.Integrable.indicator (hgi _ _).1
          (measurableSet_lt (measurable_id.sub measurable_const |>.sub
            (Measurable.comp (by measurability)
              (measurable_id.sub measurable_const |>.floor))) measurable_const)
    rw [h_periodic_integral, intervalIntegral.integral_of_le,
      intervalIntegral.integral_of_le] <;> try linarith
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator] <;>
      norm_num [Set.indicator]
    congr with x
    by_cases ha : θ r - δ / 2 < x ∧ x < θ r - δ / 2 + 1
    · obtain ⟨ha1, ha2⟩ := ha
      have hfract : Int.fract (x - (θ r - δ / 2)) = x - (θ r - δ / 2) :=
        Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      rw [ite_eq_left ⟨ha1, ha2⟩]
      by_cases hb : Int.fract (x - (θ r - δ / 2)) < δ
      · have hc : θ r - δ / 2 < x ∧ x < θ r + δ / 2 :=
          ⟨ha1, by rw [hfract] at hb; linarith⟩
        rw [ite_eq_left hb, ite_eq_left hc]
      · have hc : ¬(θ r - δ / 2 < x ∧ x < θ r + δ / 2) := by
          rintro ⟨_, h2⟩; exact hb (by rw [hfract]; linarith)
        rw [ite_eq_right hb, ite_eq_right hc]
    · rw [ite_eq_right ha]
      have hc : ¬(θ r - δ / 2 < x ∧ x < θ r + δ / 2) := by
        rintro ⟨h1, h2⟩; exact ha ⟨h1, by linarith⟩
      rw [ite_eq_right hc]
  aesop

end PeriodicArcIntegralBounds
