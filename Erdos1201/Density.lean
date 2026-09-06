import Erdos1201.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Asymptotic density and dyadic bookkeeping

The original paper and proof are by Przemek Chojecki together with ChatGPT 5.5.
We use a factor-two dyadic bound, which suffices for the zero-density limit.
-/

open Finset Filter
open scoped Topology

namespace Erdos1201
open Classical

noncomputable def intervalCount (A : Set ℕ) (a b : ℕ) : ℕ :=
  ((Ioc a b).filter (· ∈ A)).card

noncomputable def density (A : Set ℕ) (N : ℕ) : ℝ :=
  (intervalCount A 0 N : ℝ) / N

noncomputable def upperDensity (A : Set ℕ) : ℝ := limsup (density A) atTop
noncomputable def lowerDensity (A : Set ℕ) : ℝ := liminf (density A) atTop

theorem intervalCount_le (A : Set ℕ) (a b : ℕ) : intervalCount A a b ≤ b - a := by
  simpa [intervalCount] using card_filter_le (s := Ioc a b) (p := (· ∈ A))

theorem intervalCount_mono_right (A : Set ℕ) {a b c : ℕ} (h : b ≤ c) :
    intervalCount A a b ≤ intervalCount A a c := by
  apply card_le_card
  intro n hn
  simp only [mem_filter, mem_Ioc] at hn ⊢
  exact ⟨⟨hn.1.1, hn.1.2.trans h⟩, hn.2⟩

theorem intervalCount_add (A : Set ℕ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    intervalCount A a c = intervalCount A a b + intervalCount A b c := by
  unfold intervalCount
  rw [← Ioc_union_Ioc_eq_Ioc hab hbc, filter_union, card_union_of_disjoint]
  exact (Ioc_disjoint_Ioc_of_le (le_refl b)).mono (filter_subset _ _) (filter_subset _ _)

theorem density_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ density A N := by
  unfold density
  positivity

theorem density_le_one (A : Set ℕ) (N : ℕ) : density A N ≤ 1 := by
  by_cases hN : N = 0
  · simp [density, hN]
  · apply (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hN)).mpr
    exact_mod_cast (intervalCount_le A 0 N)

theorem upperDensity_nonneg (A : Set ℕ) : 0 ≤ upperDensity A := by
  apply le_limsup_of_le
  · exact isBoundedUnder_of ⟨1, density_le_one A⟩
  · intro b hb
    obtain ⟨N, hN⟩ := hb.exists
    exact (density_nonneg A N).trans hN

theorem upperDensity_le_one (A : Set ℕ) : upperDensity A ≤ 1 := by
  apply limsup_le_of_le
  · exact (isBoundedUnder_of ⟨0, density_nonneg A⟩).isCoboundedUnder_le
  · exact Eventually.of_forall (density_le_one A)

/-- An eventual bound on every dyadic shell gives a global bound, up to a constant. -/
theorem prefix_bound_of_dyadic (A : Set ℕ) {b : ℝ} (hb : 0 ≤ b) {X₀ : ℕ}
    (hX₀ : 1 ≤ X₀)
    (hblock : ∀ X ≥ X₀, (intervalCount A X (2 * X) : ℝ) ≤ b * X) :
    ∀ N : ℕ, (intervalCount A 0 N : ℝ) ≤ 2 * b * N + 2 * X₀ := by
  have hpow : ∀ k : ℕ, (intervalCount A 0 (2 ^ k) : ℝ) ≤ b * (2 ^ k : ℕ) + 2 * X₀ := by
    intro k
    induction k with
    | zero =>
      have hc : (intervalCount A 0 1 : ℝ) ≤ 1 := by exact_mod_cast intervalCount_le A 0 1
      have hx : (1 : ℝ) ≤ X₀ := by exact_mod_cast hX₀
      simp only [pow_zero, Nat.cast_one]
      linarith
    | succ k ih =>
      by_cases hk : X₀ ≤ 2 ^ k
      · have hs := intervalCount_add A (a := 0) (b := 2 ^ k) (c := 2 * 2 ^ k)
          (Nat.zero_le _) (by omega)
        have he := hblock (2 ^ k) hk
        rw [pow_succ, Nat.mul_comm, hs, Nat.cast_add]
        push_cast at ih he ⊢
        nlinarith
      · have hc := intervalCount_le A 0 (2 ^ (k + 1))
        have hp : (0 : ℝ) ≤ b * (2 ^ (k + 1) : ℕ) := mul_nonneg hb (Nat.cast_nonneg _)
        have hn : 2 ^ (k + 1) ≤ 2 * X₀ := by rw [pow_succ]; omega
        have : (intervalCount A 0 (2 ^ (k + 1)) : ℝ) ≤ 2 * X₀ := by
          exact_mod_cast (hc.trans (by omega))
        linarith
  intro N
  by_cases hN : N = 0
  · simp [hN, intervalCount]
  have hlow := Nat.pow_log_le_self 2 hN
  have hupp := Nat.lt_pow_succ_log_self (by omega : 1 < 2) N
  have hc := intervalCount_mono_right A (a := 0) hupp.le
  have hp := hpow (Nat.log 2 N + 1)
  have hm : (2 ^ (Nat.log 2 N + 1) : ℕ) ≤ 2 * N := by rw [pow_succ]; omega
  have hmr : ((2 ^ (Nat.log 2 N + 1) : ℕ) : ℝ) ≤ 2 * N := by exact_mod_cast hm
  have hcr : (intervalCount A 0 N : ℝ) ≤ intervalCount A 0 (2 ^ (Nat.log 2 N + 1)) := by
    exact_mod_cast hc
  nlinarith [mul_le_mul_of_nonneg_left hmr hb]

/-- Factor two is sufficient because the shell bounds can be made arbitrarily small. -/
theorem upperDensity_le_of_dyadic (A : Set ℕ) {b : ℝ} (hb : 0 ≤ b)
    (hblock : ∀ᶠ X : ℕ in atTop, (intervalCount A X (2 * X) : ℝ) ≤ b * X) :
    upperDensity A ≤ 2 * b := by
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hblock
  have hp := prefix_bound_of_dyadic A hb (X₀ := max X₀ 1) (le_max_right _ _)
    (fun X hX => hX₀ X ((le_max_left _ _).trans hX))
  have ht : Tendsto (fun N : ℕ => 2 * b + (2 * (max X₀ 1 : ℕ) : ℝ) / N)
      atTop (𝓝 (2 * b)) := by
    have hzero : Tendsto (fun N : ℕ => (2 * (max X₀ 1 : ℕ) : ℝ) / (N : ℝ))
        atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa using (tendsto_const_nhds (x := 2 * b)).add hzero
  apply le_of_forall_pos_le_add
  intro η hη
  apply limsup_le_of_le
  · exact (isBoundedUnder_of ⟨0, density_nonneg A⟩).isCoboundedUnder_le
  · filter_upwards [ht.eventually (gt_mem_nhds (by linarith : 2 * b < 2 * b + η)),
      eventually_gt_atTop 0] with N hlim hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hdiv := (div_le_div_of_nonneg_right (hp N) hNr.le)
    rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hNr)] at hdiv
    exact hdiv.trans hlim.le

theorem upperDensity_mono {A B : Set ℕ} (hAB : A ⊆ B) :
    upperDensity A ≤ upperDensity B := by
  apply limsup_le_limsup
  · apply Eventually.of_forall
    intro N
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
    apply Nat.cast_le.mpr
    apply card_le_card
    intro n hn
    simp only [mem_filter] at hn ⊢
    exact ⟨hn.1, hAB hn.2⟩
  · exact (isBoundedUnder_of ⟨0, density_nonneg A⟩).isCoboundedUnder_le
  · exact isBoundedUnder_of ⟨1, density_le_one B⟩

/-- Complementation on positive integers, with exactly the paper's `[1, N]` convention. -/
theorem lowerDensity_eq_one_sub_upperDensity {A B : Set ℕ}
    (hAB : ∀ n : ℕ, 0 < n → (n ∈ B ↔ n ∉ A)) :
    lowerDensity B = 1 - upperDensity A := by
  have hd : ∀ᶠ N : ℕ in atTop, density B N = 1 - density A N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hc : intervalCount B 0 N + intervalCount A 0 N = N := by
      unfold intervalCount
      have hf : (Ioc 0 N).filter (· ∈ B) = (Ioc 0 N).filter (fun n => n ∉ A) := by
        apply filter_congr
        intro n hn
        exact hAB n (mem_Ioc.mp hn).1
      rw [hf, add_comm, card_filter_add_card_filter_not, Nat.card_Ioc, Nat.sub_zero]
    have hcr : (intervalCount B 0 N : ℝ) + intervalCount A 0 N = N := by
      exact_mod_cast hc
    unfold density
    have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
    apply (eq_sub_iff_add_eq).mpr
    rw [← add_div, hcr, div_self hNr]
  exact (liminf_congr hd).trans (liminf_const_sub atTop (density A) 1
    (isBoundedUnder_of ⟨1, density_le_one A⟩)
    (isBoundedUnder_of ⟨0, density_nonneg A⟩).isCoboundedUnder_le)

end Erdos1201
