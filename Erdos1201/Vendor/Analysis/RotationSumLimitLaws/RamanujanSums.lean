module

public import Erdos1201.Vendor.Analysis.RotationSumLimitLaws.Foundations
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Data.Nat.Totient

@[expose] public section

namespace RotationSumLimitLaws

open scoped BigOperators ComplexConjugate FourierTransform

noncomputable section

def reducedResidues (q : ℕ) : Finset ℕ :=
  (Finset.range q).filter fun a ↦ Nat.Coprime a q

def ramanujanPhase (q a : ℕ) (n : ℤ) : ℂ :=
  (Real.fourierChar (((a : ℤ) * n : ℤ) / (q : ℝ)) : ℂ)

def ramanujanSum (q : ℕ) (n : ℤ) : ℂ :=
  ∑ a ∈ reducedResidues q, ramanujanPhase q a n

@[simp]
theorem reducedResidues_zero : reducedResidues 0 = ∅ := by
  simp [reducedResidues]

@[simp]
theorem reducedResidues_one : reducedResidues 1 = {0} := by
  ext a
  simp [reducedResidues]

@[simp]
theorem ramanujanSum_zero (n : ℤ) : ramanujanSum 0 n = 0 := by
  simp [ramanujanSum]

@[simp]
theorem ramanujanPhase_zero_index (q a : ℕ) : ramanujanPhase q a 0 = 1 := by
  simp [ramanujanPhase]

@[simp]
theorem ramanujanSum_one (n : ℤ) : ramanujanSum 1 n = 1 := by
  simp [ramanujanSum, ramanujanPhase]


@[simp]
theorem fourierChar_int (z : ℤ) :
    (Real.fourierChar (z : ℝ) : ℂ) = 1 := by
  rw [Real.fourierChar_apply]
  convert Complex.exp_int_mul_two_pi_mul_I z using 2
  push_cast
  ring

@[simp]
theorem fourierChar_int_circle (z : ℤ) :
    Real.fourierChar (z : ℝ) = 1 := by
  apply Subtype.ext
  exact fourierChar_int z

theorem ramanujanPhase_add_modulus {q a : ℕ} (n : ℤ) (hq : q ≠ 0) :
    ramanujanPhase q a (n + q) = ramanujanPhase q a n := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have harg :
      ((((a : ℤ) * (n + q) : ℤ) : ℝ) / (q : ℝ)) =
        (((((a : ℤ) * n : ℤ) : ℝ) / (q : ℝ)) + (a : ℝ)) := by
    push_cast
    field_simp
  rw [ramanujanPhase, harg, AddChar.map_add_eq_mul]
  simp [ramanujanPhase]
  exact_mod_cast fourierChar_int (a : ℤ)

theorem ramanujanPhase_complement {q a : ℕ} (ha : a ≤ q) (n : ℤ) :
    ramanujanPhase q (q - a) n = ramanujanPhase q a (-n) := by
  by_cases hq : q = 0
  · subst q
    have : a = 0 := by omega
    subst a
    simp [ramanujanPhase]
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have harg :
      ((((q - a : ℕ) : ℤ) * n : ℤ) : ℝ) / (q : ℝ) =
        (n : ℝ) + ((((a : ℤ) * (-n) : ℤ) : ℝ) / (q : ℝ)) := by
    push_cast [Nat.cast_sub ha]
    field_simp
    ring
  rw [ramanujanPhase, harg, AddChar.map_add_eq_mul]
  simp [ramanujanPhase]

private theorem complement_mem_reducedResidues {q a : ℕ} (hq : 2 ≤ q)
    (ha : a ∈ reducedResidues q) : q - a ∈ reducedResidues q := by
  rw [reducedResidues, Finset.mem_filter] at ha ⊢
  rcases ha with ⟨haRange, haCoprime⟩
  rw [Finset.mem_range] at haRange ⊢
  have haPos : 0 < a := by
    by_contra h
    have haZero : a = 0 := Nat.eq_zero_of_not_pos h
    subst a
    have hqOne : q = 1 := by simpa using haCoprime
    omega
  refine ⟨by omega, ?_⟩
  exact (Nat.coprime_self_sub_left haRange.le).2 haCoprime

theorem ramanujanSum_add_modulus {q : ℕ} (n : ℤ) (hq : q ≠ 0) :
    ramanujanSum q (n + q) = ramanujanSum q n := by
  simp_rw [ramanujanSum, ramanujanPhase_add_modulus n hq]

theorem ramanujanSum_periodic (q : ℕ) :
    Function.Periodic (ramanujanSum q) (q : ℤ) := by
  by_cases hq : q = 0
  · subst q
    intro n
    simp
  · exact fun n ↦ ramanujanSum_add_modulus n hq


theorem ramanujanPhase_neg (q a : ℕ) (n : ℤ) :
    ramanujanPhase q a (-n) = conj (ramanujanPhase q a n) := by
  have harg :
      ((((a : ℤ) * (-n) : ℤ) : ℝ) / (q : ℝ)) =
        -((((a : ℤ) * n : ℤ) : ℝ) / (q : ℝ)) := by
    push_cast
    ring
  rw [ramanujanPhase, harg, Real.fourierChar.map_neg_eq_inv]
  exact Circle.coe_inv_eq_conj _

theorem ramanujanSum_neg (q : ℕ) (n : ℤ) :
    ramanujanSum q (-n) = conj (ramanujanSum q n) := by
  simp_rw [ramanujanSum, ramanujanPhase_neg, map_sum]

theorem ramanujanSum_even (q : ℕ) (n : ℤ) :
    ramanujanSum q (-n) = ramanujanSum q n := by
  by_cases hq : q ≤ 1
  · interval_cases q <;> simp
  have hqTwo : 2 ≤ q := by omega
  unfold ramanujanSum
  refine Finset.sum_bij'
    (fun a _ ↦ q - a) (fun a _ ↦ q - a)
    (fun a ha ↦ complement_mem_reducedResidues hqTwo ha)
    (fun a ha ↦ complement_mem_reducedResidues hqTwo ha) ?_ ?_ ?_
  · intro a ha
    have haLt : a < q := (Finset.mem_filter.mp ha).1 |> Finset.mem_range.mp
    change q - (q - a) = a
    exact Nat.sub_sub_self haLt.le
  · intro a ha
    have haLt : a < q := (Finset.mem_filter.mp ha).1 |> Finset.mem_range.mp
    change q - (q - a) = a
    exact Nat.sub_sub_self haLt.le
  · intro a ha
    exact (ramanujanPhase_complement
      (Finset.mem_range.mp (Finset.mem_filter.mp ha).1).le n).symm

theorem conj_ramanujanSum (q : ℕ) (n : ℤ) :
    conj (ramanujanSum q n) = ramanujanSum q n := by
  rw [← ramanujanSum_neg, ramanujanSum_even]

theorem ofReal_re_ramanujanSum (q : ℕ) (n : ℤ) :
    ((ramanujanSum q n).re : ℂ) = ramanujanSum q n :=
  Complex.conj_eq_iff_re.mp (conj_ramanujanSum q n)

@[simp]
theorem ramanujanSum_im (q : ℕ) (n : ℤ) : (ramanujanSum q n).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  exact conj_ramanujanSum q n

theorem norm_ramanujanSum_le_totient (q : ℕ) (n : ℤ) :
    ‖ramanujanSum q n‖ ≤ (Nat.totient q : ℝ) := by
  calc
    ‖ramanujanSum q n‖ = ‖∑ a ∈ reducedResidues q, ramanujanPhase q a n‖ := rfl
    _ ≤ ∑ a ∈ reducedResidues q, ‖ramanujanPhase q a n‖ := norm_sum_le _ _
    _ = ((reducedResidues q).card : ℝ) := by
      simp [ramanujanPhase, Circle.norm_coe]
    _ = (Nat.totient q : ℝ) := by
      congr 1
      simpa [reducedResidues, Nat.coprime_comm] using
        (Nat.totient_eq_card_coprime q).symm

end

end RotationSumLimitLaws
