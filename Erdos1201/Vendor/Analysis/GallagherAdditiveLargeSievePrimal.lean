module

public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Erdos1201.Vendor.Analysis.GallagherAdditiveLargeSieveWindow
public import Erdos1201.Vendor.Analysis.AdditiveLargeSieveDuality

@[expose] public section

/-!
# The primal additive large sieve over an arbitrary finite index type

This module generalizes the windowed additive large-sieve bound
(`GallagherAdditiveLargeSieveWindow.finite_additiveLargeSieve_window`, indexed
over `Fin R`) to an arbitrary finite frequency index type and a natural-number
block `[M, M+N)`, then dualizes it (via
`AdditiveLargeSieveDuality.sq_sum_transpose_le`) from the dual quadratic form
(sum over frequencies of squared exponential sums) to the primal form (sum
over the block of squared exponential sums). Source provenance is recorded in
the campaign report.
-/

namespace GallagherAdditiveLargeSievePrimal

open scoped BigOperators
open Real Complex
open AdditiveCharacterGeometricSums

/-- Reindex a sum over an integer block `[M, M+N)` as a sum over the
corresponding natural-number block, given the two summands agree under
`Int.toNat`. -/
theorem sumIco_int_eq_sumIco_nat {γ : Type*} [AddCommMonoid γ] (M N : ℕ)
    (f : ℤ → γ) (g : ℕ → γ)
    (hfg : ∀ n : ℤ, (M : ℤ) ≤ n → n < (M : ℤ) + N → f n = g n.toNat) :
    ∑ n ∈ Finset.Ico (M : ℤ) ((M : ℤ) + N), f n = ∑ n ∈ Finset.Ico M (M + N), g n := by
  refine Finset.sum_bij (fun n _ => n.toNat) ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_Ico] at hn ⊢
    omega
  · intro n hn m hm h
    simp only [Finset.mem_Ico] at hn hm
    omega
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    exact ⟨(n : ℤ), by simp only [Finset.mem_Ico]; omega, by omega⟩
  · intro n hn
    simp only [Finset.mem_Ico] at hn
    exact hfg n (by omega) (by omega)

/-- The windowed additive large-sieve bound, generalized from `Fin R` to an
arbitrary finite frequency index type and from an integer block to a
natural-number block `[M, M+N)`. -/
theorem finite_additiveLargeSievePrimal_window (M N : ℕ) {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : ∀ i j, i ≠ j → δ ≤ nearestIntegerDistance (θ i - θ j)) (b : ℕ → ℂ) :
    (∑ i, ‖∑ n ∈ Finset.Ico M (M + N), b n * additiveCharacter ((n : ℝ) * θ i)‖ ^ 2)
      ≤ (δ⁻¹ + 2 * Real.pi * N) * ∑ n ∈ Finset.Ico M (M + N), ‖b n‖ ^ 2 := by
  set e0 : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set b' : ℤ → ℂ := fun n => if n < 0 then 0 else b n.toNat with hb'_def
  have hbase := GallagherAdditiveLargeSieveWindow.finite_additiveLargeSieve_window
    (M : ℤ) N b' (Fintype.card ι) (fun k => θ (e0.symm k)) δ hδ hδ1
    (fun k l hkl => hsp (e0.symm k) (e0.symm l) (fun h => hkl (e0.symm.injective h)))
  have hsum_eq : ∀ k : Fin (Fintype.card ι),
      ∑ n ∈ Finset.Ico (M : ℤ) ((M : ℤ) + N), b' n * additiveCharacter ((n : ℝ) * θ (e0.symm k))
        = ∑ n ∈ Finset.Ico M (M + N), b n * additiveCharacter ((n : ℝ) * θ (e0.symm k)) := by
    intro k
    refine sumIco_int_eq_sumIco_nat M N _ _ fun n hn1 hn2 => ?_
    rw [hb'_def]
    simp only [ite_eq_right (by omega : ¬ n < 0)]
    have hcast : (n.toNat : ℝ) = (n : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ n)
    rw [hcast]
  have hnorm_eq : ∑ n ∈ Finset.Ico (M : ℤ) ((M : ℤ) + N), ‖b' n‖ ^ 2
      = ∑ n ∈ Finset.Ico M (M + N), ‖b n‖ ^ 2 :=
    sumIco_int_eq_sumIco_nat M N _ _ fun n hn1 hn2 => by
      rw [hb'_def]; simp only [ite_eq_right (by omega : ¬ n < 0)]
  calc ∑ i, ‖∑ n ∈ Finset.Ico M (M + N), b n * additiveCharacter ((n : ℝ) * θ i)‖ ^ 2
      = ∑ k : Fin (Fintype.card ι),
          ‖∑ n ∈ Finset.Ico M (M + N), b n * additiveCharacter ((n : ℝ) * θ (e0.symm k))‖ ^ 2 := by
        refine Finset.sum_bij (fun i _ => e0 i) (fun i _ => Finset.mem_univ _)
          (fun i _ j _ h => e0.injective h)
          (fun k _ => ⟨e0.symm k, Finset.mem_univ _, e0.apply_symm_apply k⟩)
          (fun i _ => by rw [e0.symm_apply_apply])
    _ = ∑ k : Fin (Fintype.card ι),
          ‖∑ n ∈ Finset.Ico (M : ℤ) ((M : ℤ) + N), b' n *
            additiveCharacter ((n : ℝ) * θ (e0.symm k))‖ ^ 2 :=
        Finset.sum_congr rfl fun k _ => by rw [hsum_eq]
    _ ≤ (δ⁻¹ + 2 * Real.pi * N) * ∑ n ∈ Finset.Ico (M : ℤ) ((M : ℤ) + N), ‖b' n‖ ^ 2 := hbase
    _ = (δ⁻¹ + 2 * Real.pi * N) * ∑ n ∈ Finset.Ico M (M + N), ‖b n‖ ^ 2 := by rw [hnorm_eq]

/-- The log-free primal additive large sieve (arbitrary finite index).  For
`δ`-spaced real points `θ : ι → ℝ` (`0 < δ ≤ 1`) and complex coefficients,
`∑_{M ≤ n < M+N} |∑_i c_i e(n θ_i)|² ≤ (δ⁻¹ + 2π N) ∑_i |c_i|²`. -/
theorem finite_additiveLargeSievePrimal (M N : ℕ) {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (cc : ι → ℂ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsp : ∀ i j, i ≠ j → δ ≤ nearestIntegerDistance (θ i - θ j)) :
    (∑ n ∈ Finset.Ico M (M + N), ‖∑ i, cc i * additiveCharacter ((n : ℝ) * θ i)‖ ^ 2)
      ≤ (δ⁻¹ + 2 * Real.pi * N) * ∑ i, ‖cc i‖ ^ 2 := by
  set ρ := Finset.Ico M (M + N) with hρ_def
  set Mmat : ρ → ι → ℂ := fun p i => additiveCharacter ((p.val : ℝ) * θ i) with hMmat_def
  set C := δ⁻¹ + 2 * Real.pi * N with hC_def
  have hC_nonneg : 0 ≤ C := by positivity
  have h_transpose : ∀ (b : ρ → ℂ),
      ∑ i, ‖∑ p : ρ, Mmat p i * b p‖ ^ 2 ≤ C * ∑ p : ρ, ‖b p‖ ^ 2 := by
    intro b
    set b' : ℕ → ℂ := fun n => if h : n ∈ ρ then b ⟨n, h⟩ else 0 with hb'_def
    have hb'_sum : ∀ i, ∑ p : ρ, Mmat p i * b p
        = ∑ n ∈ ρ, b' n * additiveCharacter ((n : ℝ) * θ i) := by
      intro i
      refine Finset.sum_bij (fun p (_ : p ∈ (Finset.univ : Finset ρ)) => (p : ℕ))
        (fun p _ => p.2) (fun p _ q _ h => Subtype.ext h)
        (fun n hn => ⟨⟨n, hn⟩, Finset.mem_univ _, rfl⟩) (fun p _ => ?_)
      simp only [hMmat_def, hb'_def, dite_eq_left p.2, Subtype.coe_eta]
      ring
    have hb'_norm : ∑ p : ρ, ‖b p‖ ^ 2 = ∑ n ∈ ρ, ‖b' n‖ ^ 2 := by
      refine Finset.sum_bij (fun p (_ : p ∈ (Finset.univ : Finset ρ)) => (p : ℕ))
        (fun p _ => p.2) (fun p _ q _ h => Subtype.ext h)
        (fun n hn => ⟨⟨n, hn⟩, Finset.mem_univ _, rfl⟩) (fun p _ => ?_)
      simp only [hb'_def, dite_eq_left p.2]
    simp only [hb'_sum, hb'_norm]
    exact finite_additiveLargeSievePrimal_window M N θ δ hδ hδ1 hsp b'
  have hdual := AdditiveLargeSieveDuality.sq_sum_transpose_le Mmat C hC_nonneg h_transpose cc
  have heq : ∑ p : ρ, ‖∑ i, Mmat p i * cc i‖ ^ 2
      = ∑ n ∈ Finset.Ico M (M + N), ‖∑ i, cc i * additiveCharacter ((n : ℝ) * θ i)‖ ^ 2 := by
    refine Finset.sum_bij (fun p (_ : p ∈ (Finset.univ : Finset ρ)) => (p : ℕ))
      (fun p _ => p.2) (fun p _ q _ h => Subtype.ext h)
      (fun n hn => ⟨⟨n, hn⟩, Finset.mem_univ _, rfl⟩) (fun p _ => ?_)
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hMmat_def]
    ring
  rwa [heq] at hdual

end GallagherAdditiveLargeSievePrimal
