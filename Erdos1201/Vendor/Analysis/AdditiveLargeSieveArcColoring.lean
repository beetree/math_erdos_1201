/-
Source repository and pin: https://github.com/ericlisg/erdos731 @
cb1b58c88bf639bb87664dd96ffc327c305e160e.
Pinned source: RequestProject/Erdos731/StripLargeSieveArc.lean.
Formal-proof author: Aristotle, Harmonic's automated theorem prover.
Informal attribution: Erdős, Graham, Ruzsa, and Straus, per
erdosproblems.com/731. License: Apache-2.0.

Local changes ledger:
- None of this file's three declarations (`exists_coloring_of_window_bound`,
  `nid_eq_abs_of_lt`, `largeSieve_mult_arc`) mentions any problem-specific
  object; the whole file is a generic interval-graph coloring argument plus
  its large-sieve consequence, so it moves to the corpus intact under an
  honest name.
- Source `nid` -> the already-landed corpus
  `AdditiveCharacterGeometricSums.nearestIntegerDistance`.
- `nid_eq_abs_of_lt` -> `nearestIntegerDistance_eq_abs_of_lt` (honest name,
  matching the corpus's `nearestIntegerDistance`).
- `largeSieve_mult_arc` -> `additiveLargeSieve_arc_multiplicity` (parallels
  the already-landed `AdditiveLargeSieveMultiplicity.additiveLargeSieve_
  multiplicity` it specializes to an arc-window multiplicity hypothesis).
- Proofs ported verbatim modulo the renames above; no mathematical change.
-/
module

public import Mathlib.Tactic.Positivity
public import Erdos1201.Vendor.Analysis.AdditiveLargeSieveMultiplicity

/-!
# Arc-multiplicity form of the additive large sieve

The packet-incidence estimates elsewhere in this corpus produce their
multiplicity bound in the geometric form "every arc of length `X⁻¹` contains
at most `R` indexed frequencies". This module converts that hypothesis into
the coloring hypothesis of `AdditiveLargeSieveMultiplicity.
additiveLargeSieve_multiplicity` and states the resulting arc-multiplicity
large sieve.

* `exists_coloring_of_window_bound` — an interval-graph coloring: if every
  half-open window `[a, a+δ)` contains at most `R` of the points, they can be
  `R`-colored with each color class `δ`-separated.
* `additiveLargeSieve_arc_multiplicity` — the large sieve for frequencies
  lying in a common window of width `< 1/2` (so nearest-integer distance
  equals ordinary distance) with an arc-multiplicity bound `R`.
-/

@[expose] public section

namespace AdditiveLargeSieveArcColoring

open scoped BigOperators
open Real Complex
open AdditiveCharacterGeometricSums
open AdditiveLargeSieveMultiplicity

/-- **Interval-graph coloring.** If every half-open window `[a, a+δ)`
contains at most `R` of the points `x i` (`R ≥ 1`, `δ > 0`), then there is an
`R`-coloring `col` such that any two distinct points of the same color are at
distance `≥ δ`. -/
lemma exists_coloring_of_window_bound {ι : Type*} [Fintype ι] (x : ι → ℝ) (δ : ℝ)
    (_hδ : 0 < δ) (R : ℕ) (hR : 1 ≤ R)
    (hwin : ∀ a : ℝ, (Finset.univ.filter (fun i => a ≤ x i ∧ x i < a + δ)).card ≤ R) :
    ∃ col : ι → Fin R, ∀ i j, col i = col j → i ≠ j → δ ≤ |x i - x j| := by
  set e0 : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set rank : ι → ℕ := fun i => (Finset.univ.filter (fun j => x j < x i ∨ (x j = x i ∧ e0 j < e0 i))).card
  have h_rank_inj : Function.Injective rank := by
    intro i j hij
    by_contra h_neq
    have h_lt : x i < x j ∨ (x i = x j ∧ e0 i < e0 j) ∨ (x j < x i ∨ (x j = x i ∧ e0 j < e0 i)) := by
      cases lt_trichotomy (x i) (x j) <;> cases lt_trichotomy (e0 i) (e0 j) <;> aesop
    have h_lt_rank : ∀ i j, x i < x j ∨ (x i = x j ∧ e0 i < e0 j) → rank i < rank j := by
      intro i j hij
      have h_subset : Finset.filter (fun k => x k < x i ∨ (x k = x i ∧ e0 k < e0 i)) Finset.univ
          ⊂ Finset.filter (fun k => x k < x j ∨ (x k = x j ∧ e0 k < e0 j)) Finset.univ := by
        simp_all +decide [Finset.ssubset_def, Finset.subset_iff]
        grind
      exact Finset.card_lt_card h_subset
    grind +ring
  have h_rank_lt : ∀ i, rank i < Fintype.card ι :=
    fun i => lt_of_lt_of_le (Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨i, by aesop⟩))
      (by simp +decide)
  have h_monotone : ∀ i j, rank i ≤ rank j → x i ≤ x j := by
    intro i j hij
    by_contra h_contra
    push Not at h_contra
    have h_rank_gt : rank j < rank i := by
      refine Finset.card_lt_card ?_
      simp +decide [Finset.ssubset_def, Finset.subset_iff]
      exact ⟨fun k hk => Or.inl <| hk.elim (fun hk => hk.trans h_contra) fun hk => hk.1.symm ▸ h_contra,
        j, Or.inl h_contra, le_rfl, fun _ => le_rfl⟩
    linarith [hij]
  set col : ι → Fin R := fun i => ⟨rank i % R, Nat.mod_lt _ hR⟩
  use col
  intro i j hcol hij
  have h_diff : |(rank i : ℤ) - rank j| ≥ R := by
    simp_all +decide [Fin.ext_iff]
    exact Int.le_of_dvd (abs_pos.mpr (sub_ne_zero.mpr (mod_cast h_rank_inj.ne hij)))
      (by simpa using Int.ModEq.dvd (Int.ModEq.symm (Int.natCast_modEq_iff.mpr hcol)))
  have h_dist : δ ≤ |x i - x j| := by
    by_cases h_case : rank i < rank j
    · set T := Finset.univ.filter (fun k => rank i ≤ rank k ∧ rank k ≤ rank j) with hT_def
      have hT_card : T.card ≥ R + 1 := by
        have hT_card : T.card = Finset.card (Finset.Icc (rank i) (rank j)) := by
          refine Finset.card_bij (fun k hk => rank k) ?_ ?_ ?_ <;> simp +decide [h_rank_inj.eq_iff]
          · exact fun k hk => Finset.mem_filter.mp hk |>.2
          · intro b hb₁ hb₂
            obtain ⟨a, ha⟩ : ∃ a, rank a = b := by
              have h_rank_surj : Finset.image rank Finset.univ = Finset.range (Fintype.card ι) :=
                Finset.eq_of_subset_of_card_le
                  (Finset.image_subset_iff.mpr fun i _ => Finset.mem_range.mpr (h_rank_lt i))
                  (by rw [Finset.card_image_of_injective _ h_rank_inj, Finset.card_range,
                    Finset.card_univ])
              exact Finset.mem_image.mp
                (h_rank_surj.symm ▸ Finset.mem_range.mpr (by linarith [h_rank_lt j]))
                |> Exists.imp fun x hx => hx.2
            use a
            aesop
        simp_all +decide [abs_of_neg]
        exact lt_tsub_iff_left.mpr (by linarith)
      have hT_subset : T ⊆ Finset.univ.filter (fun k => x i ≤ x k ∧ x k < x i + δ) → False :=
        fun h => by have := Finset.card_le_card h; linarith [hwin (x i)]
      contrapose! hT_subset
      simp_all +decide [Finset.subset_iff]
      exact fun k hk₁ hk₂ => by
        linarith [abs_lt.mp hT_subset, h_monotone i k hk₁, h_monotone k j hk₂]
    · have h_dist : δ ≤ |x j - x i| := by
        have h_card : (Finset.univ.filter (fun k => rank j ≤ rank k ∧ rank k ≤ rank i)).card ≥ R + 1 := by
          have h_card : (Finset.image rank (Finset.univ.filter
              (fun k => rank j ≤ rank k ∧ rank k ≤ rank i))).card ≥ R + 1 := by
            rw [show (Finset.image rank {k | rank j ≤ rank k ∧ rank k ≤ rank i})
                = Finset.Icc (rank j) (rank i) from ?_]
            · simp +zetaDelta at *
              exact Nat.lt_sub_of_add_lt (by
                cases abs_cases
                  ((Finset.card (Finset.filter (fun k => x k < x i ∨ x k = x i ∧ e0 k < e0 i)
                    Finset.univ) : ℤ)
                    - Finset.card (Finset.filter (fun k => x k < x j ∨ x k = x j ∧ e0 k < e0 j)
                      Finset.univ)) <;>
                  linarith)
            · ext k
              simp [Finset.mem_image, Finset.mem_Icc]
              constructor <;> intro hk
              · grind
              · have h_card : Finset.image rank Finset.univ = Finset.range (Fintype.card ι) :=
                  Finset.eq_of_subset_of_card_le
                    (Finset.image_subset_iff.mpr fun i _ => Finset.mem_range.mpr (h_rank_lt i))
                    (by rw [Finset.card_image_of_injective _ h_rank_inj, Finset.card_range,
                      Finset.card_univ])
                exact Exists.elim
                  (Finset.mem_image.mp
                    (h_card.symm ▸ Finset.mem_range.mpr (by linarith [h_rank_lt i, h_rank_lt j])))
                  fun x hx => ⟨x, ⟨by linarith, by linarith⟩, hx.2⟩
          rwa [Finset.card_image_of_injective _ h_rank_inj] at h_card
        contrapose! h_card
        refine lt_of_le_of_lt (Finset.card_le_card ?_) (Nat.lt_succ_of_le (hwin (x j)))
        intro k hk
        simp_all +decide [abs_lt]
        linarith [h_monotone _ _ hk.1, h_monotone _ _ hk.2]
      exact h_dist.trans (by rw [abs_sub_comm])
  exact h_dist

/-- `nearestIntegerDistance` equals the ordinary absolute value on
differences of size `< 1/2`. -/
lemma nearestIntegerDistance_eq_abs_of_lt {y : ℝ} (h : |y| < 1 / 2) :
    nearestIntegerDistance y = |y| := by
  unfold nearestIntegerDistance
  norm_num [show round y = 0 by
    rw [round_eq]
    norm_num [show ⌊y + 1 / 2⌋ = 0 from
      Int.floor_eq_iff.mpr ⟨by norm_num; linarith [abs_lt.mp h], by norm_num; linarith [abs_lt.mp h]⟩]]

/-- **Arc-multiplicity large sieve.** If all frequencies lie in a common
window `[c, c + w)` of width `w < 1/2` and every window of length `δ`
contains at most `R` of them, then
`∑_{M ≤ n < M+N} |∑_i c_i e(n θ_i)|² ≤ R (δ⁻¹ + 2π N) ∑_i |c_i|²`. -/
theorem additiveLargeSieve_arc_multiplicity (M N : ℕ) {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (cc : ι → ℂ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (R : ℕ) (hR : 1 ≤ R)
    (c w : ℝ) (hw : w < 1 / 2) (hmem : ∀ i, c ≤ θ i ∧ θ i < c + w)
    (harc : ∀ a : ℝ, (Finset.univ.filter (fun i => a ≤ θ i ∧ θ i < a + δ)).card ≤ R) :
    (∑ n ∈ Finset.Ico M (M + N), ‖∑ i, cc i * additiveCharacter (n * θ i)‖ ^ 2)
      ≤ (R : ℝ) * (δ⁻¹ + 2 * Real.pi * N) * ∑ i, ‖cc i‖ ^ 2 := by
  obtain ⟨col, hcol⟩ := exists_coloring_of_window_bound θ δ hδ R hR harc
  apply additiveLargeSieve_multiplicity M N θ cc δ hδ hδ1 R col
  intro i j hij hne
  rw [nearestIntegerDistance_eq_abs_of_lt]
  · exact hcol i j hij hne
  · grind +splitImp

end AdditiveLargeSieveArcColoring
